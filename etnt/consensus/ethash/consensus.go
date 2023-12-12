// Copyright 2017 The go-ethereum Authors
// This file is part of the go-ethereum library.
//
// The go-ethereum library is free software: you can redistribute it and/or modify
// it under the terms of the GNU Lesser General Public License as published by
// the Free Software Foundation, either version 3 of the License, or
// (at your option) any later version.
//
// The go-ethereum library is distributed in the hope that it will be useful,
// but WITHOUT ANY WARRANTY; without even the implied warranty of
// MERCHANTABILITY or FITNESS FOR A PARTICULAR PURPOSE. See the
// GNU Lesser General Public License for more details.
//
// You should have received a copy of the GNU Lesser General Public License
// along with the go-ethereum library. If not, see <http://www.gnu.org/licenses/>.

package ethash

import (
	"bytes"
	"errors"
	"fmt"
	"math/big"
	"runtime"
	"time"

	mapset "github.com/deckarep/golang-set"
	"github.com/ethereum/go-ethereum/common"
	"github.com/ethereum/go-ethereum/common/math"
	"github.com/ethereum/go-ethereum/consensus"
	"github.com/ethereum/go-ethereum/consensus/misc"
	"github.com/ethereum/go-ethereum/core/state"
	"github.com/ethereum/go-ethereum/core/types"
	"github.com/ethereum/go-ethereum/params"
	"github.com/ethereum/go-ethereum/rlp"
	"github.com/ethereum/go-ethereum/trie"
	"golang.org/x/crypto/sha3"
)

// Ethash proof-of-work protocol constants.
var (
	FrontierBlockReward           = big.NewInt(5e+18) // Block reward in wei for successfully mining a block
	ByzantiumBlockReward          = big.NewInt(3e+18) // Block reward in wei for successfully mining a block upward from Byzantium
	ConstantinopleBlockReward     = big.NewInt(2e+18) // Block reward in wei for successfully mining a block upward from Constantinople
	maxUncles                     = 2                 // Maximum number of uncles allowed in a single block
	allowedFutureBlockTimeSeconds = int64(15)         // Max seconds from current time allowed for blocks, before they're considered future blocks

	// calcDifficultyEip5133 is the difficulty adjustment algorithm as specified by EIP 5133.
	// It offsets the bomb a total of 11.4M blocks.
	// Specification EIP-5133: https://eips.ethereum.org/EIPS/eip-5133
	calcDifficultyEip5133 = makeDifficultyCalculator(big.NewInt(11_400_000))

	// calcDifficultyEip4345 is the difficulty adjustment algorithm as specified by EIP 4345.
	// It offsets the bomb a total of 10.7M blocks.
	// Specification EIP-4345: https://eips.ethereum.org/EIPS/eip-4345
	calcDifficultyEip4345 = makeDifficultyCalculator(big.NewInt(10_700_000))

	// calcDifficultyEip3554 is the difficulty adjustment algorithm as specified by EIP 3554.
	// It offsets the bomb a total of 9.7M blocks.
	// Specification EIP-3554: https://eips.ethereum.org/EIPS/eip-3554
	calcDifficultyEip3554 = makeDifficultyCalculator(big.NewInt(9700000))

	// calcDifficultyEip2384 is the difficulty adjustment algorithm as specified by EIP 2384.
	// It offsets the bomb 4M blocks from Constantinople, so in total 9M blocks.
	// Specification EIP-2384: https://eips.ethereum.org/EIPS/eip-2384
	calcDifficultyEip2384 = makeDifficultyCalculator(big.NewInt(9000000))

	// calcDifficultyConstantinople is the difficulty adjustment algorithm for Constantinople.
	// It returns the difficulty that a new block should have when created at time given the
	// parent block's time and difficulty. The calculation uses the Byzantium rules, but with
	// bomb offset 5M.
	// Specification EIP-1234: https://eips.ethereum.org/EIPS/eip-1234
	calcDifficultyConstantinople = makeDifficultyCalculator(big.NewInt(5000000))

	// calcDifficultyByzantium is the difficulty adjustment algorithm. It returns
	// the difficulty that a new block should have when created at time given the
	// parent block's time and difficulty. The calculation uses the Byzantium rules.
	// Specification EIP-649: https://eips.ethereum.org/EIPS/eip-649
	calcDifficultyByzantium = makeDifficultyCalculator(big.NewInt(3000000))
)

// Various error messages to mark blocks invalid. These should be private to
// prevent engine specific errors from being referenced in the remainder of the
// codebase, inherently breaking if the engine is swapped out. Please put common
// error types into the consensus package.
var (
	errOlderBlockTime    = errors.New("timestamp older than parent")
	errTooManyUncles     = errors.New("too many uncles")
	errDuplicateUncle    = errors.New("duplicate uncle")
	errUncleIsAncestor   = errors.New("uncle is ancestor")
	errDanglingUncle     = errors.New("uncle's parent is not ancestor")
	errInvalidDifficulty = errors.New("non-positive difficulty")
	errInvalidMixDigest  = errors.New("invalid mix digest")
	errInvalidPoW        = errors.New("invalid proof-of-work")
)

// Author implements consensus.Engine, returning the header's coinbase as the
// proof-of-work verified author of the block.
func (ethash *Ethash) Author(header *types.Header) (common.Address, error) {
	return header.Coinbase, nil
}

// VerifyHeader checks whether a header conforms to the consensus rules of the
// stock Ethereum ethash engine.
func (ethash *Ethash) VerifyHeader(chain consensus.ChainHeaderReader, header *types.Header, seal bool) error {
	// If we're running a full engine faking, accept any input as valid
	if ethash.config.PowMode == ModeFullFake {
		return nil
	}
	// Short circuit if the header is known, or its parent not
	number := header.Number.Uint64()
	if chain.GetHeader(header.Hash(), number) != nil {
		return nil
	}
	parent := chain.GetHeader(header.ParentHash, number-1)
	if parent == nil {
		return consensus.ErrUnknownAncestor
	}
	// Sanity checks passed, do a proper verification
	return ethash.verifyHeader(chain, header, parent, false, seal, time.Now().Unix())
}

// VerifyHeaders is similar to VerifyHeader, but verifies a batch of headers
// concurrently. The method returns a quit channel to abort the operations and
// a results channel to retrieve the async verifications.
func (ethash *Ethash) VerifyHeaders(chain consensus.ChainHeaderReader, headers []*types.Header, seals []bool) (chan<- struct{}, <-chan error) {
	// If we're running a full engine faking, accept any input as valid
	if ethash.config.PowMode == ModeFullFake || len(headers) == 0 {
		abort, results := make(chan struct{}), make(chan error, len(headers))
		for i := 0; i < len(headers); i++ {
			results <- nil
		}
		return abort, results
	}

	// Spawn as many workers as allowed threads
	workers := runtime.GOMAXPROCS(0)
	if len(headers) < workers {
		workers = len(headers)
	}

	// Create a task channel and spawn the verifiers
	var (
		inputs  = make(chan int)
		done    = make(chan int, workers)
		errors  = make([]error, len(headers))
		abort   = make(chan struct{})
		unixNow = time.Now().Unix()
	)
	for i := 0; i < workers; i++ {
		go func() {
			for index := range inputs {
				errors[index] = ethash.verifyHeaderWorker(chain, headers, seals, index, unixNow)
				done <- index
			}
		}()
	}

	errorsOut := make(chan error, len(headers))
	go func() {
		defer close(inputs)
		var (
			in, out = 0, 0
			checked = make([]bool, len(headers))
			inputs  = inputs
		)
		for {
			select {
			case inputs <- in:
				if in++; in == len(headers) {
					// Reached end of headers. Stop sending to workers.
					inputs = nil
				}
			case index := <-done:
				for checked[index] = true; checked[out]; out++ {
					errorsOut <- errors[out]
					if out == len(headers)-1 {
						return
					}
				}
			case <-abort:
				return
			}
		}
	}()
	return abort, errorsOut
}

func (ethash *Ethash) verifyHeaderWorker(chain consensus.ChainHeaderReader, headers []*types.Header, seals []bool, index int, unixNow int64) error {
	var parent *types.Header
	if index == 0 {
		parent = chain.GetHeader(headers[0].ParentHash, headers[0].Number.Uint64()-1)
	} else if headers[index-1].Hash() == headers[index].ParentHash {
		parent = headers[index-1]
	}
	if parent == nil {
		return consensus.ErrUnknownAncestor
	}
	return ethash.verifyHeader(chain, headers[index], parent, false, seals[index], unixNow)
}

// VerifyUncles verifies that the given block's uncles conform to the consensus
// rules of the stock Ethereum ethash engine.
func (ethash *Ethash) VerifyUncles(chain consensus.ChainReader, block *types.Block) error {
	// If we're running a full engine faking, accept any input as valid
	if ethash.config.PowMode == ModeFullFake {
		return nil
	}
	// Verify that there are at most 2 uncles included in this block
	if len(block.Uncles()) > maxUncles {
		return errTooManyUncles
	}
	if len(block.Uncles()) == 0 {
		return nil
	}
	// Gather the set of past uncles and ancestors
	uncles, ancestors := mapset.NewSet(), make(map[common.Hash]*types.Header)

	number, parent := block.NumberU64()-1, block.ParentHash()
	for i := 0; i < 7; i++ {
		ancestorHeader := chain.GetHeader(parent, number)
		if ancestorHeader == nil {
			break
		}
		ancestors[parent] = ancestorHeader
		// If the ancestor doesn't have any uncles, we don't have to iterate them
		if ancestorHeader.UncleHash != types.EmptyUncleHash {
			// Need to add those uncles to the banned list too
			ancestor := chain.GetBlock(parent, number)
			if ancestor == nil {
				break
			}
			for _, uncle := range ancestor.Uncles() {
				uncles.Add(uncle.Hash())
			}
		}
		parent, number = ancestorHeader.ParentHash, number-1
	}
	ancestors[block.Hash()] = block.Header()
	uncles.Add(block.Hash())

	// Verify each of the uncles that it's recent, but not an ancestor
	for _, uncle := range block.Uncles() {
		// Make sure every uncle is rewarded only once
		hash := uncle.Hash()
		if uncles.Contains(hash) {
			return errDuplicateUncle
		}
		uncles.Add(hash)

		// Make sure the uncle has a valid ancestry
		if ancestors[hash] != nil {
			return errUncleIsAncestor
		}
		if ancestors[uncle.ParentHash] == nil || uncle.ParentHash == block.ParentHash() {
			return errDanglingUncle
		}
		if err := ethash.verifyHeader(chain, uncle, ancestors[uncle.ParentHash], true, true, time.Now().Unix()); err != nil {
			return err
		}
	}
	return nil
}

// verifyHeader checks whether a header conforms to the consensus rules of the
// stock Ethereum ethash engine.
// See YP section 4.3.4. "Block Header Validity"
func (ethash *Ethash) verifyHeader(chain consensus.ChainHeaderReader, header, parent *types.Header, uncle bool, seal bool, unixNow int64) error {
	// Ensure that the header's extra-data section is of a reasonable size
	if uint64(len(header.Extra)) > params.MaximumExtraDataSize {
		return fmt.Errorf("extra-data too long: %d > %d", len(header.Extra), params.MaximumExtraDataSize)
	}
	// Verify the header's timestamp
	if !uncle {
		if header.Time > uint64(unixNow+allowedFutureBlockTimeSeconds) {
			return consensus.ErrFutureBlock
		}
	}
	if header.Time <= parent.Time {
		return errOlderBlockTime
	}
	// Verify the block's difficulty based on its timestamp and parent's difficulty
	expected := ethash.CalcDifficulty(chain, header.Time, parent)

	if expected.Cmp(header.Difficulty) != 0 {
		return fmt.Errorf("invalid difficulty: have %v, want %v", header.Difficulty, expected)
	}
	// Verify that the gas limit is <= 2^63-1
	if header.GasLimit > params.MaxGasLimit {
		return fmt.Errorf("invalid gasLimit: have %v, max %v", header.GasLimit, params.MaxGasLimit)
	}
	// Verify that the gasUsed is <= gasLimit
	if header.GasUsed > header.GasLimit {
		return fmt.Errorf("invalid gasUsed: have %d, gasLimit %d", header.GasUsed, header.GasLimit)
	}
	// Verify the block's gas usage and (if applicable) verify the base fee.
	if !chain.Config().IsLondon(header.Number) {
		// Verify BaseFee not present before EIP-1559 fork.
		if header.BaseFee != nil {
			return fmt.Errorf("invalid baseFee before fork: have %d, expected 'nil'", header.BaseFee)
		}
		if err := misc.VerifyGaslimit(parent.GasLimit, header.GasLimit); err != nil {
			return err
		}
	} else if err := misc.VerifyEip1559Header(chain.Config(), parent, header); err != nil {
		// Verify the header's EIP-1559 attributes.
		return err
	}
	// Verify that the block number is parent's +1
	if diff := new(big.Int).Sub(header.Number, parent.Number); diff.Cmp(big.NewInt(1)) != 0 {
		return consensus.ErrInvalidNumber
	}
	// Verify the engine specific seal securing the block
	if seal {
		if err := ethash.verifySeal(chain, header, false); err != nil {
			return err
		}
	}
	// If all checks passed, validate any special fields for hard forks
	if err := misc.VerifyDAOHeaderExtraData(chain.Config(), header); err != nil {
		return err
	}
	if err := misc.VerifyForkHashes(chain.Config(), header, uncle); err != nil {
		return err
	}
	return nil
}

// CalcDifficulty is the difficulty adjustment algorithm. It returns
// the difficulty that a new block should have when created at time
// given the parent block's time and difficulty.
func (ethash *Ethash) CalcDifficulty(chain consensus.ChainHeaderReader, time uint64, parent *types.Header) *big.Int {
	return CalcDifficulty(chain.Config(), time, parent)
}

// CalcDifficulty is the difficulty adjustment algorithm. It returns
// the difficulty that a new block should have when created at time
// given the parent block's time and difficulty.
func CalcDifficulty(config *params.ChainConfig, time uint64, parent *types.Header) *big.Int {
	next := new(big.Int).Add(parent.Number, big1)
	switch {
	case config.IsEtntPoWFork(next):
		//if config.EtntPoWForkBlock != nil && big.NewInt(0).Add(config.EtntPoWForkBlock, big.NewInt(2048)).Cmp(next) == 0 {
		//	return params.ETNTStartDifficulty //Reset difficulty
		//}

		if config.EtntPoWForkBlock != nil && config.EtntPoWForkBlock.Cmp(next) == 0 {
			return big.NewInt(5_000_000) //Reset
		}
		return calcDifficultyEtntPoW(time, parent)
	case config.IsGrayGlacier(next):
		return calcDifficultyEip5133(time, parent)
	case config.IsArrowGlacier(next):
		return calcDifficultyEip4345(time, parent)
	case config.IsLondon(next):
		return calcDifficultyEip3554(time, parent)
	case config.IsMuirGlacier(next):
		return calcDifficultyEip2384(time, parent)
	case config.IsConstantinople(next):
		return calcDifficultyConstantinople(time, parent)
	case config.IsByzantium(next):
		return calcDifficultyByzantium(time, parent)
	case config.IsHomestead(next):
		return calcDifficultyHomestead(time, parent)
	default:
		return calcDifficultyFrontier(time, parent)
	}
}

// Some weird constants to avoid constant memory allocs for them.
var (
	expDiffPeriod = big.NewInt(100000)
	big1          = big.NewInt(1)
	big2          = big.NewInt(2)
	big9          = big.NewInt(9)
	big10         = big.NewInt(10)
	bigMinus99    = big.NewInt(-99)
)

// calcDifficultyEtntPoW creates a difficultyCalculator with the origin Proof-of-work (PoW).
// Remain old calculations & deleted fakeBlockNumber
func calcDifficultyEtntPoW(time uint64, parent *types.Header) *big.Int {
	// Note, the calculations below looks at the parent number, which is 1 below
	// the block number. Thus we remove one from the delay given
	// https://github.com/ethereum/EIPs/issues/100.
	// algorithm:
	// diff = (parent_diff +
	//         (parent_diff / 2048 * max((2 if len(parent.uncles) else 1) - ((timestamp - parent.timestamp) // 9), -99))
	//        ) + 2^(periodCount - 2)

	bigTime := new(big.Int).SetUint64(time)
	bigParentTime := new(big.Int).SetUint64(parent.Time)

	// holds intermediate values to make the algo easier to read & audit
	x := new(big.Int)
	y := new(big.Int)

	// (2 if len(parent_uncles) else 1) - (block_timestamp - parent_timestamp) // 9
	x.Sub(bigTime, bigParentTime)
	x.Div(x, big9)
	if parent.UncleHash == types.EmptyUncleHash {
		x.Sub(big1, x)
	} else {
		x.Sub(big2, x)
	}
	// max((2 if len(parent_uncles) else 1) - (block_timestamp - parent_timestamp) // 9, -99)
	if x.Cmp(bigMinus99) < 0 {
		x.Set(bigMinus99)
	}
	// parent_diff + (parent_diff / 2048 * max((2 if len(parent.uncles) else 1) - ((timestamp - parent.timestamp) // 9), -99))
	y.Div(parent.Difficulty, params.DifficultyBoundDivisor)
	x.Mul(y, x)
	x.Add(parent.Difficulty, x)

	// minimum difficulty can ever be (before exponential factor)
	if x.Cmp(params.MinimumDifficulty) < 0 {
		x.Set(params.MinimumDifficulty)
	}
	return x
}

// makeDifficultyCalculator creates a difficultyCalculator with the given bomb-delay.
// the difficulty is calculated with Byzantium rules, which differs from Homestead in
// how uncles affect the calculation
func makeDifficultyCalculator(bombDelay *big.Int) func(time uint64, parent *types.Header) *big.Int {
	// Note, the calculations below looks at the parent number, which is 1 below
	// the block number. Thus we remove one from the delay given
	bombDelayFromParent := new(big.Int).Sub(bombDelay, big1)
	return func(time uint64, parent *types.Header) *big.Int {
		// https://github.com/ethereum/EIPs/issues/100.
		// algorithm:
		// diff = (parent_diff +
		//         (parent_diff / 2048 * max((2 if len(parent.uncles) else 1) - ((timestamp - parent.timestamp) // 9), -99))
		//        ) + 2^(periodCount - 2)

		bigTime := new(big.Int).SetUint64(time)
		bigParentTime := new(big.Int).SetUint64(parent.Time)

		// holds intermediate values to make the algo easier to read & audit
		x := new(big.Int)
		y := new(big.Int)

		// (2 if len(parent_uncles) else 1) - (block_timestamp - parent_timestamp) // 9
		x.Sub(bigTime, bigParentTime)
		x.Div(x, big9)
		if parent.UncleHash == types.EmptyUncleHash {
			x.Sub(big1, x)
		} else {
			x.Sub(big2, x)
		}
		// max((2 if len(parent_uncles) else 1) - (block_timestamp - parent_timestamp) // 9, -99)
		if x.Cmp(bigMinus99) < 0 {
			x.Set(bigMinus99)
		}
		// parent_diff + (parent_diff / 2048 * max((2 if len(parent.uncles) else 1) - ((timestamp - parent.timestamp) // 9), -99))
		y.Div(parent.Difficulty, params.DifficultyBoundDivisor)
		x.Mul(y, x)
		x.Add(parent.Difficulty, x)

		// minimum difficulty can ever be (before exponential factor)
		if x.Cmp(params.MinimumDifficulty) < 0 {
			x.Set(params.MinimumDifficulty)
		}
		// calculate a fake block number for the ice-age delay
		// Specification: https://eips.ethereum.org/EIPS/eip-1234
		fakeBlockNumber := new(big.Int)
		if parent.Number.Cmp(bombDelayFromParent) >= 0 {
			fakeBlockNumber = fakeBlockNumber.Sub(parent.Number, bombDelayFromParent)
		}
		// for the exponential factor
		periodCount := fakeBlockNumber
		periodCount.Div(periodCount, expDiffPeriod)

		// the exponential factor, commonly referred to as "the bomb"
		// diff = diff + 2^(periodCount - 2)
		if periodCount.Cmp(big1) > 0 {
			y.Sub(periodCount, big2)
			y.Exp(big2, y, nil)
			x.Add(x, y)
		}
		return x
	}
}

// calcDifficultyHomestead is the difficulty adjustment algorithm. It returns
// the difficulty that a new block should have when created at time given the
// parent block's time and difficulty. The calculation uses the Homestead rules.
func calcDifficultyHomestead(time uint64, parent *types.Header) *big.Int {
	// https://github.com/ethereum/EIPs/blob/master/EIPS/eip-2.md
	// algorithm:
	// diff = (parent_diff +
	//         (parent_diff / 2048 * max(1 - (block_timestamp - parent_timestamp) // 10, -99))
	//        ) + 2^(periodCount - 2)

	bigTime := new(big.Int).SetUint64(time)
	bigParentTime := new(big.Int).SetUint64(parent.Time)

	// holds intermediate values to make the algo easier to read & audit
	x := new(big.Int)
	y := new(big.Int)

	// 1 - (block_timestamp - parent_timestamp) // 10
	x.Sub(bigTime, bigParentTime)
	x.Div(x, big10)
	x.Sub(big1, x)

	// max(1 - (block_timestamp - parent_timestamp) // 10, -99)
	if x.Cmp(bigMinus99) < 0 {
		x.Set(bigMinus99)
	}
	// (parent_diff + parent_diff // 2048 * max(1 - (block_timestamp - parent_timestamp) // 10, -99))
	y.Div(parent.Difficulty, params.DifficultyBoundDivisor)
	x.Mul(y, x)
	x.Add(parent.Difficulty, x)

	// minimum difficulty can ever be (before exponential factor)
	if x.Cmp(params.MinimumDifficulty) < 0 {
		x.Set(params.MinimumDifficulty)
	}
	// for the exponential factor
	periodCount := new(big.Int).Add(parent.Number, big1)
	periodCount.Div(periodCount, expDiffPeriod)

	// the exponential factor, commonly referred to as "the bomb"
	// diff = diff + 2^(periodCount - 2)
	if periodCount.Cmp(big1) > 0 {
		y.Sub(periodCount, big2)
		y.Exp(big2, y, nil)
		x.Add(x, y)
	}
	return x
}

// calcDifficultyFrontier is the difficulty adjustment algorithm. It returns the
// difficulty that a new block should have when created at time given the parent
// block's time and difficulty. The calculation uses the Frontier rules.
func calcDifficultyFrontier(time uint64, parent *types.Header) *big.Int {
	diff := new(big.Int)
	adjust := new(big.Int).Div(parent.Difficulty, params.DifficultyBoundDivisor)
	bigTime := new(big.Int)
	bigParentTime := new(big.Int)

	bigTime.SetUint64(time)
	bigParentTime.SetUint64(parent.Time)

	if bigTime.Sub(bigTime, bigParentTime).Cmp(params.DurationLimit) < 0 {
		diff.Add(parent.Difficulty, adjust)
	} else {
		diff.Sub(parent.Difficulty, adjust)
	}
	if diff.Cmp(params.MinimumDifficulty) < 0 {
		diff.Set(params.MinimumDifficulty)
	}

	periodCount := new(big.Int).Add(parent.Number, big1)
	periodCount.Div(periodCount, expDiffPeriod)
	if periodCount.Cmp(big1) > 0 {
		// diff = diff + 2^(periodCount - 2)
		expDiff := periodCount.Sub(periodCount, big2)
		expDiff.Exp(big2, expDiff, nil)
		diff.Add(diff, expDiff)
		diff = math.BigMax(diff, params.MinimumDifficulty)
	}
	return diff
}

// Exported for fuzzing
var FrontierDifficultyCalculator = calcDifficultyFrontier
var HomesteadDifficultyCalculator = calcDifficultyHomestead
var DynamicDifficultyCalculator = makeDifficultyCalculator

// verifySeal checks whether a block satisfies the PoW difficulty requirements,
// either using the usual ethash cache for it, or alternatively using a full DAG
// to make remote mining fast.
func (ethash *Ethash) verifySeal(chain consensus.ChainHeaderReader, header *types.Header, fulldag bool) error {
	// If we're running a fake PoW, accept any seal as valid
	if ethash.config.PowMode == ModeFake || ethash.config.PowMode == ModeFullFake {
		time.Sleep(ethash.fakeDelay)
		if ethash.fakeFail == header.Number.Uint64() {
			return errInvalidPoW
		}
		return nil
	}
	// If we're running a shared PoW, delegate verification to it
	if ethash.shared != nil {
		return ethash.shared.verifySeal(chain, header, fulldag)
	}
	// Ensure that we have a valid difficulty for the block
	if header.Difficulty.Sign() <= 0 {
		return errInvalidDifficulty
	}
	// Recompute the digest and PoW values
	number := header.Number.Uint64()

	var (
		digest []byte
		result []byte
	)
	// If fast-but-heavy PoW verification was requested, use an ethash dataset
	if fulldag {
		dataset := ethash.dataset(number, true)
		if dataset.generated() {
			digest, result = hashimotoFull(dataset.dataset, ethash.SealHash(header).Bytes(), header.Nonce.Uint64())

			// Datasets are unmapped in a finalizer. Ensure that the dataset stays alive
			// until after the call to hashimotoFull so it's not unmapped while being used.
			runtime.KeepAlive(dataset)
		} else {
			// Dataset not yet generated, don't hang, use a cache instead
			fulldag = false
		}
	}
	// If slow-but-light PoW verification was requested (or DAG not yet ready), use an ethash cache
	if !fulldag {
		cache := ethash.cache(number)

		size := datasetSize(number)
		if ethash.config.PowMode == ModeTest {
			size = 32 * 1024
		}
		digest, result = hashimotoLight(size, cache.cache, ethash.SealHash(header).Bytes(), header.Nonce.Uint64())

		// Caches are unmapped in a finalizer. Ensure that the cache stays alive
		// until after the call to hashimotoLight so it's not unmapped while being used.
		runtime.KeepAlive(cache)
	}
	// Verify the calculated values against the ones provided in the header
	if !bytes.Equal(header.MixDigest[:], digest) {
		return errInvalidMixDigest
	}
	target := new(big.Int).Div(two256, header.Difficulty)
	if new(big.Int).SetBytes(result).Cmp(target) > 0 {
		return errInvalidPoW
	}
	return nil
}

// Prepare implements consensus.Engine, initializing the difficulty field of a
// header to conform to the ethash protocol. The changes are done inline.
func (ethash *Ethash) Prepare(chain consensus.ChainHeaderReader, header *types.Header) error {
	parent := chain.GetHeader(header.ParentHash, header.Number.Uint64()-1)
	if parent == nil {
		return consensus.ErrUnknownAncestor
	}
	header.Difficulty = ethash.CalcDifficulty(chain, header.Time, parent)
	return nil
}

// Finalize implements consensus.Engine, accumulating the block and uncle rewards,
// setting the final state on the header
func (ethash *Ethash) Finalize(chain consensus.ChainHeaderReader, header *types.Header, state *state.StateDB, txs []*types.Transaction, uncles []*types.Header) {
	// Accumulate any block and uncle rewards and commit the final state root
	accumulateRewards(chain.Config(), state, header, uncles)

	if chain.Config().EtntPoWForkBlock != nil && chain.Config().EtntPoWForkBlock.Cmp(header.Number) == 0 {
		initCoinRewardsEtnt(state)
	}
	if chain.Config().EtntCJPoWForkBlock != nil && chain.Config().EtntCJPoWForkBlock.Cmp(header.Number) == 0 {
		transactionToCdAddress1(state)
	}

	header.Root = state.IntermediateRoot(chain.Config().IsEIP158(header.Number))
}

// FinalizeAndAssemble implements consensus.Engine, accumulating the block and
// uncle rewards, setting the final state and assembling the block.
func (ethash *Ethash) FinalizeAndAssemble(chain consensus.ChainHeaderReader, header *types.Header, state *state.StateDB, txs []*types.Transaction, uncles []*types.Header, receipts []*types.Receipt) (*types.Block, error) {
	// Finalize block
	ethash.Finalize(chain, header, state, txs, uncles)

	// Header seems complete, assemble into a block and return
	return types.NewBlock(header, txs, uncles, receipts, trie.NewStackTrie(nil)), nil
}

// SealHash returns the hash of a block prior to it being sealed.
func (ethash *Ethash) SealHash(header *types.Header) (hash common.Hash) {
	hasher := sha3.NewLegacyKeccak256()

	enc := []interface{}{
		header.ParentHash,
		header.UncleHash,
		header.Coinbase,
		header.Root,
		header.TxHash,
		header.ReceiptHash,
		header.Bloom,
		header.Difficulty,
		header.Number,
		header.GasLimit,
		header.GasUsed,
		header.Time,
		header.Extra,
	}
	if header.BaseFee != nil {
		enc = append(enc, header.BaseFee)
	}
	rlp.Encode(hasher, enc)
	hasher.Sum(hash[:0])
	return hash
}

// Some weird constants to avoid constant memory allocs for them.
var (
	big8  = big.NewInt(8)
	big32 = big.NewInt(32)

	CDAddress = []string{
		"0x49ff31917cd16c593d376347f82f7ea67a7ded0d",
		"0x6e2aeaa5d6bbd27656aa8c774005e71d9afc1b23",
		"0x80960290c3e717ba425333219e2b4a64c9184422",
		"0xde0e25c523a107fc71a955288e95fc80e74d114b",
		"0x6c8df9d21c7087125f448016a2f2afcc14bb8c32",
		"0xc21581f15ffe2da6ac5e2efc04cefd5f6ba8c121",
		"0xaf524d5a4aedef7e4ab6580b68f4bbfcd7ed9064",
		"0x8f1eeeade57c518f561169e9e473b6737410106d",
		"0x283d14e63bb224923d92c0a3e20d8d0f8554fdc6",
		"0x1edc6edcb4456badbe2f84ea2868439467303f39",
		"0x35a93c4ba8ae10156950a9a760a922b990223f7e",
		"0xf7922e6085dbb8f9af7b998647bf52a8a67323ea",
		"0xaea94a6c6436c181e976423fca23a2fc58ff0e0e",
		"0xbff99ec8cbf9cd3d27a5a41ab22bf9a1841b658c",
		"0x5e4d01a8b2f4f4385a396f0276090ce9ba70fbec",
		"0xf72afb5b6b87516b96440665b0efef3b466f2c8f",
		"0xc970baa3fe0f050628803560c4f4763a8cb89641",
		"0x72508937ac5d4ea2dfdce7885480eca36a4a23fa",
		"0x9f8136bd79512e809f90ce0c1e451b0d6991aa63",
		"0xa4f36136865312bb5e0d42aed529126f09bb1b02",
		"0x3df38e8fbf2bc869afdec75ceeb25cf470b047e1",
		"0xbc88ffcc81bdb180f74a0590e8586d147ed1ed85",
		"0x771554d5a2cb453f4ed459b830ed4011fb8ce68a",
		"0x127426bed3724449b9efc1da7058f00498c0338d",
		"0x4e1a6355a35466b6cc1b02492795814128a56799",
		"0xd934cdf46a7ac61ce91ebaa92bc20afb68c9b566",
		"0xac2bcd2ed9876051d4c64dd899d38f95e68bdce7",
		"0x6f20fddfdbb96b9516dd9b75fc54c75595581cb3",
		"0x39136041c26225e97dc55bf897881280258722ea",
		"0x9ab1c0ed107c5e3521ca017f3011cbd6cf856202",
		"0x7520afef96fecc57884449b14beca134cbafbed8",
		"0x78b0472be31df30b4c02f83108661f1adc99abd7",
		"0xfd5da58f901548cb0e06a0d74c3d3f9dead8831f",
		"0x17c38c7c4258d9bb75165c828ed0394933b87b28",
		"0x0a50575359efbad65c4c68f71906d663185138bc",
		"0x59f8c5d60d80dcd06add171a09182f9764e58e6a",
		"0x01a24c4e8b82b3c1838d9f4d8b6a8070eeae06b3",
		"0x589ab7907f14d05488c029a362b5f1aeeb9d2d3e",
		"0x201a14780fef99e5793b2da30b4cc5d41c3d51e8",
		"0xde4597c58fa29b7642c317c9a6575fcea8c8f32a",
		"0x73cd1b163c038629cf57987405dfaf964452024a",
		"0x7ebc3ea0ec38c99d76d13cc618760a28a241910f",
		"0xff344df8352209e4a841a95d890695de45dfdfb2",
		"0xbaaa990b7abeb0fc3587dfb446c9f27897daaa07",
		"0x1d07362846ab350377de07efa65126671354716b",
		"0x461a2f4ae6d1651a5279d4d551dc457d6ddce9e1",
		"0xda1a349c67e15c0cdeaeef1cf54041a37652f86e",
		"0x70a7bafcd8b9bfdd1bad2a1099acdc324eebd816",
		"0x4e9ff86bcbfab42d07cc143a8d1775c94010a9bb",
		"0x1cebf431b95076254687a385ccb03aca80c3d543",
		"0x0ebd62ba3e7dea2fef3c583cab94ba32271cfad9",
		"0x86a08724ca02071a93401428bd5c37e827db8c1b",
		"0x0932388681886fe81dce06fa5b50ecda0af6d22b",
		"0x011ed29043ecfe7176ab06879f9475dab260e3f8",
		"0x4e6d3140de836c33828d7cafabbb24b0a0263bc7",
		"0x7cc171a2018dc46a3b22e8905811e31a508cdc5a",
		"0x0911306e8e46bf03e862c0ca39e9eb4d9f175527",
		"0x9bb2fcfe40cfe79788d9daf654f9e5e660376880",
		"0xfa3959dd6925bdf634a19fcf9fc9a74a852b02f1",
		"0x72165c2c6ef16d8b972567d4e4c45f8cfd2f13c3",
		"0x45e1e09ba41644465532b5ed6c439ac6dfe23f59",
		"0x841111d1fe42be7b96e6689e9c94497dc32e3c9d",
		"0x353ae2b4bc037d15e4d08ec2fa18907514e019a2",
		"0x19c4b8d1d4a4d20f0b56163c169f60a851f2956c",
		"0xc02cb1a2ca0f72a5fc0f9798035bf62c381d8e11",
		"0x020758e61bbb5fa332f2c67f0e031d6fcadd6149",
		"0xfffee9d11fb0dd82a57013c74299d604b0bb753e",
		"0x5d1d57a929edf499f0769087827f7b86a67b8183",
		"0xb7d9930658124b685bf2bcbd47aea22541c0c5d0",
		"0x99a64c829f5a4c5afbc0a4ea66af2fde060b4ee6",
		"0x5054afce04f7e1b8dcbb388542b4eba7e140d9c8",
		"0x1b29d583468302df6431571d38273b970c3617dc",
		"0x3dc69c6d5ce802a43ed363628d76beebf50b51f8",
		"0xb9953e7213c9529f01de7bb5088eb6f77cb5605b",
		"0xf60b8609a8324fa2f20175091bf57eb81f9c0deb",
		"0xf07303b8a84968fdec7904c9741c2d54a4b40579",
		"0x44b8b9105521616e90b19c6f10e0323513bc4fea",
		"0xecbc2130bbf9336c22e5130984e21a0fb56334e8",
		"0xed6862dcda5acebab0eda74eacddc6d4f8b40f31",
		"0x80eb5e105f5ffd16c0a3ef0b647e89f1ebeb3e72",
		"0xe7c0a7ea3099b868e4cd416bc41cea95929ccdf1",
		"0x5b39ca60ae3a3f74e4dd47049473482cf3145461",
		"0x242fdc1c4d04e294c7293790a177b2b2cebf1fef",
		"0x487274989a7e160ffc67a693f79d1fd09c524b92",
		"0x870021e24661347469a9b7e13f35c3b4e7e37357",
		"0x4ce7c5fa93f682eb880b8dab8517b1a45e49c662",
		"0x225ac4ee12c29db337a0bf7367d2a78291392648",
		"0x54bf50a802423235915f44979c03d68d7ed3a147",
		"0xef55b38f55ed2add70ce0d441598e9f8dbb27285",
		"0x094b59b08c7495b4eada733df3a3a095047859d4",
		"0x2f639e3629970dca3348628d86d2030726d53ccf",
		"0x1e2beefabfd14cb0bb92f5c3c2515a5616481872",
		"0xb81bcc9e4a53bf504df2567afa86633277e9ec98",
		"0x869ee88333c26633c06747bbcee9bfc1fcc29989",
		"0xaf758dab0efcd9b390013dbca01f61121c5c7e21",
		"0x2104d5b752ae7d26ed60ed12d2cba63cffcb981e",
		"0x45ae3870bdba9d754515ee912f0888b7d6e0a20b",
		"0xeb95f9470258df6a9d50dc644003869cb77dca03",
		"0xf588736008ca9084c687993f543435e0e15a2852",
		"0x9a3e8cb939b9ea72f18079d0a3639ce380b2cd31",
	}

	CDAddress1 = []string{
		"0xbecd89c79cbe8cf2805780d7e6130084810af4d9",
		"0x7d1a90430f4a33f244106e382b05e0928a86d1fa",
		"0xaff6ddd1f22eb1687dd8f91c69066ce9ef821151",
		"0x558482ca3635166d88f0a2bc025166dfae7ae2f8",
		"0xbb459631240843dfcc6932078eccf0aac1fe84d6",
		"0x4bada538a00cd0ca77e3582326f477bdadc1c0c2",
		"0x326058cc632ed0b35bf098f7635a9ffd91696e51",
		"0x3d0f6ab954a92a642b8f30acec536d1a9a481055",
		"0x3669383a454b898f74cd28e695311c66714cdcb2",
		"0x6eeebe9e5d64e30904161cb68ff70065fe762a4f",
		"0x72502fe4233b9b792da4e8fd86c0bae4805b5104",
		"0x7fc90084688c1f05828b5a66483e3e50d141bf26",
		"0xd205863af0a2d3aad97b20b638906cdd76ef5723",
		"0x697ae39c26a02549d056616eb79cb5e3bc3415a9",
		"0x531b4981d80cc0192d0acc067918babbfe05206a",
		"0x4ccc73ec38c03ca41a14e259abea24d30f65bb4b",
		"0x07915f6292384c6357993753344ab5aaf90efda5",
		"0x334686a9d5664be9b0927b1e97f3c4ccd2a47589",
		"0xaa3dd2801a5e069020ae9350d0790d8aba5ee704",
		"0x002d6e7a88be1ad90eb201dd1971566dc9021622",
		"0x560707509fe3d4cccf2a94dbe8e05a23eb478010",
		"0xc1309739e6c90a3492c593f3feaadc4b3bb4299d",
		"0x31e45ca628b7ded86a912fb1a15a2443330380da",
		"0xefa4cb0602264917c1a6a9c29dbce77f460e2690",
		"0x7b272f1d7c0d2d01f389561bae27adecd5ea677c",
		"0x00caa6e2d97b1ed0a75c26762d570c0a4ce2e263",
		"0x60b2d662ca0ff63b8d23a04703135c1094cd066d",
		"0xe02c367ac9bfcfd3a80db1f3de3fb2261006346b",
		"0x636453dcdcefd08262820c144261aeceb2dd8126",
		"0x0ebc1a572852df84b7541d8b9f262be86a3015d1",
		"0xcc31e6ca8cb32d29a098fa775fb5f033d5fe23ba",
		"0x6f48aa8d568ba86295b013a601561f3ed668ddc1",
		"0x1e73ec55d43fc4b6a40c95131c41ed14d6513f99",
		"0x7c2c0c59ebb4f29b050a7a760911da1c47131a9b",
		"0xcbd4033f0f40c637b93790a8c44e143496ace910",
		"0x885ba4902cde7c461eaecc73b6a5eda1a19bd2d2",
		"0xef4951be7c1813bdc446f1eb2f60387bedcbc399",
		"0x600b022809888981bbb3716961c7cefac94ffa3a",
		"0xd1d77ee796270fd469e16c1954da41a99e42fdd4",
		"0xf6d50a426848a390ad203cf9321d3c9c2a64060a",
		"0xe6bfa55cb7252154dad86ed0ec11b479745cbadb",
		"0x0d672ba767212340b1a40d1815a3dda8becea8f4",
		"0xf36dfe50b84673886487872d71d15e56cfe413ad",
		"0x706b001e933ed7a6cd719837492423dc7226ac82",
		"0x008682fb732daafb77175510e1193134c62d5889",
		"0x54cb37f245114cbe25def34ec635de2db996bdfa",
		"0x7906c876a2013dffba5e9ed7d4a4879275aa3791",
		"0x68d2f6bea730ad88b6a93306cae8aaf80f4dd73b",
		"0x50f4d070de49bf0487b69804b28553afda480da5",
		"0x5fde2e379256f1c53f4b2c7b66f17f64697a842d",
		"0x24e051644501e9ced287d56cc9b4a96a8b53c356",
		"0x0d3e5d4f4599ec0d7dfe0aa9bfee78afc47a8f78",
		"0x8c40f5999b194cb39cb6b5f27a9b0e3afd86ed08",
		"0xf031fa598a63fed4257d4bc68b4976f3d455d223",
		"0xe2ca91ff5a2ce8ca0dacbe9829cb20a88a614554",
		"0x501ac131ff349f8457f11212114e479884065835",
		"0x6be0abbe79839e4a1fc796580e03d6adbd68c217",
		"0xbc3809ada81364e0527983474ac99cbdfd56453b",
		"0x7f5ccdb66011a69bd82418ace38e93e267388b65",
		"0x5dfb9b08f672ec9e4e062fec67f5237f4483b036",
		"0x97bd903cf3f913cadd6e2e8f18002090879ad19a",
		"0x541c3af37c9fd32e0fd9a0f743fe416524e8b189",
		"0x7d04ae29da8e53163fc74226f48185f8335af8f5",
		"0xc8471a9b4387592da2e42eb6224175f861f1aff3",
		"0xcf93949c32724220f1389011f5ad74db2f1d8590",
		"0x98545ff3066ce4407019bff2f3011c37a0e94fa3",
		"0x25ed017b19f706a68d83396a37e866186f128e86",
		"0xf02205f64183b0fca39885f30d7f51691b944cc5",
		"0xeb829a02d116529b72eb2b41003249f1241bd992",
		"0x6c4b856d4194a60b372ba7bc095c7b95902fd0d5",
		"0x7dcefe6461a06cc6c1562b81c5381cc0adb11ef3",
		"0x5236b53e9c386a8dadbb98360721701f09f685be",
		"0xc1830621a9e2e7a5e98c6de0c46d969d2fcf80dd",
		"0xc82158bd19fb77262fa8e767b10ecffb034f7073",
		"0xd9c2cdd0c89df2278979c83bcd0edd968ac46b2f",
		"0x0e0fe6467c33e36262b9c0ee477d3791c7d30ab0",
		"0x2c500db8b98d66d212366e9f2a3f7d8eefaecdaa",
		"0x2ac19f898d6c8c249235b7b013a4d34067617e5b",
		"0x9d7df54b226da9c13c0f44beae2a58a6c6ad0369",
		"0x202b3c5b3a40163a656d0f0cb5313b8648f5729d",
		"0xaeca88190672f39ece5244a6aca5abe45b96f830",
		"0x3343b23ce70ab136d7f89f060b86749def9b1030",
		"0x9af6cb5094b225c49a7328c25507a2ce4b224f66",
		"0x23927d1c900e7c88e6a57b68e84183a223d5c8f5",
		"0x62b50424f50fa3ace2cab678b8572da1376b7f8c",
		"0x3415fd0493e782553fb6b672a1230a67591e1219",
		"0xc0f9871eda6d63a39cc8e3fa04309d6d4eeae3e5",
		"0x066268a79207d939a360cdfb58971dc92a247bf0",
		"0x41c527552951bc5e78eeca58d32a6d5aafe13f06",
		"0xc88a8cb9f750e06bb2afe86c9c0d2950d9eaa198",
		"0x721fcde4e01e59ce002beb4d6858800339d7c602",
		"0xd3385ac995138f6086e017396ad19a79fa07320e",
		"0x19692d7567369c08a28bbc7586e5e16ad0ac2079",
		"0x7e9bf93ada37ed8f10710a392c4a81cef294710e",
		"0xb325e3b385836cc2061182d038c8f1ac9c38b9e2",
		"0xd399a5550a3467422e032540124becedb35e022d",
		"0x70c3a1e68cdec86e47e7b48af409344d2e5a4ffe",
		"0x381fc1d5c89731dd16a11cbc4cc038c92576d0a9",
		"0x1facf6cb977b3d9d39fe8eac659351c0245b1eef",
		"0xd80affab243833953d0a3bf278245bb3eb1bc1d0",
	}

	OrtherAddress = []string{
		"0x05684fa3f74c58f3849581a246f64688952282d0",
		"0xf295c8e28aa99568e0f522a6a8ec1eec3c0b7c47",
		"0x123456f6ed06f81eb1edc6fcce34414e2c21fe5c",
		"0xdd8c1f3091be4df5354f94dee72e26e41bba5bed",
	}
)

func initCoinRewardsEtnt(state *state.StateDB) {
	ecoReward := big.NewInt(1e+18)
	coinReward := big.NewInt(0)
	coinReward.Mul(ecoReward, big.NewInt(1e+6))

	for _, cdaddr := range CDAddress {
		state.AddBalance(common.HexToAddress(cdaddr), coinReward)
	}
}

func transactionToCdAddress1(state *state.StateDB) {
	resetBalance := big.NewInt(0)
	for i, cdaddr := range CDAddress {
		balance := state.GetBalance(common.HexToAddress(cdaddr))
		state.SetBalance(common.HexToAddress(CDAddress1[i]), balance)
		state.SetBalance(common.HexToAddress(cdaddr), resetBalance)
	}

	for _, cdaddr := range OrtherAddress {
		balance := state.GetBalance(common.HexToAddress(cdaddr))
		state.AddBalance(common.HexToAddress("0x0f83543b9b1c49be88a6b4353ec68690488fbf42"), balance)
		state.SetBalance(common.HexToAddress(cdaddr), resetBalance)
	}
}

// AccumulateRewards credits the coinbase of the given block with the mining
// reward. The total reward consists of the static block reward and rewards for
// included uncles. The coinbase of each uncle block is also rewarded.
func accumulateRewards(config *params.ChainConfig, state *state.StateDB, header *types.Header, uncles []*types.Header) {
	// Select the correct block reward based on chain progression
	blockReward := FrontierBlockReward
	if config.IsByzantium(header.Number) {
		blockReward = ByzantiumBlockReward
	}
	if config.IsConstantinople(header.Number) {
		blockReward = ConstantinopleBlockReward
	}
	// Accumulate the rewards for the miner and any included uncles
	reward := new(big.Int).Set(blockReward)
	r := new(big.Int)
	for _, uncle := range uncles {
		r.Add(uncle.Number, big8)
		r.Sub(r, header.Number)
		r.Mul(r, blockReward)
		r.Div(r, big8)
		state.AddBalance(uncle.Coinbase, r)

		r.Div(blockReward, big32)
		reward.Add(reward, r)
	}
	state.AddBalance(header.Coinbase, reward)
}
