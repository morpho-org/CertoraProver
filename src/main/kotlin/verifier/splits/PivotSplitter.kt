/*
 *     The Certora Prover
 *     Copyright (C) 2025  Certora Ltd.
 *
 *     This program is free software: you can redistribute it and/or modify
 *     it under the terms of the GNU General Public License as published by
 *     the Free Software Foundation, version 3 of the License.
 *
 *     This program is distributed in the hope that it will be useful,
 *     but WITHOUT ANY WARRANTY; without even the implied warranty of
 *     MERCHANTABILITY or FITNESS FOR A PARTICULAR PURPOSE.  See the
 *     GNU General Public License for more details.
 *
 *     You should have received a copy of the GNU General Public License
 *     along with this program.  If not, see <https://www.gnu.org/licenses/>.
 */

package verifier.splits

import cli.SplitHeuristicEnum
import config.Config
import datastructures.stdcollections.*
import log.*
import utils.Color.Companion.blue
import utils.Color.Companion.red
import utils.Color.Companion.yellow
import vc.data.CoreTACProgram
import verifier.splits.SplitAddress.Block
import java.util.Objects
import kotlin.random.Random

private val logger = Logger(LoggerTypes.SPLIT)

/**
 * Uses [DAGSplitter] to split the [node].
 */
class PivotSplitter(private val node: SplitTree.Node) : Splitter {
    private val lazySub get() = node.lazySub

    private fun graphSplitter(actualTAC: CoreTACProgram) =
        DAGSplitter(actualTAC.analysisCache.graph.blockSucc, lazySub.assertBlocks)

    override fun splittable(actualTAC: CoreTACProgram) =
        graphSplitter(actualTAC).isSplittable()

    override fun split(actualTAC: CoreTACProgram) =
        with(node) {
            require(splittable) { "Can only split a splittable split" }

            val splitter = graphSplitter(actualTAC)
            val scorer = when (Config.SplitHeuristic.get()) {
                SplitHeuristicEnum.NON_LINEAR -> NLScorer(actualTAC)
                SplitHeuristicEnum.SIZE_ONLY -> SizeScorer
            }
            val (pivotResults, globalScore) = splitter.bestPivots(scorer)
            val pivotResult = chooseAmongTied(pivotResults, Config.SplitTieBreakSeed.get(), address)
            logger.info {
                "${address.red}[global=${globalScore.yellow}] --- ${pivotResult.blue} (of ${pivotResults.size} tied)"
            }
            with(pivotResult) {
                setChildren(
                    listOf(
                        Block.MustPass(address, pivot) to scoreIfPassing,
                        Block.DontPass(address, pivot) to scoreIfNotPassing
                    )
                )
            }
        }

}

/**
 * Picks one of the equally scored [tied] pivots of the split at [address]. With a negative [seed], the one with the
 * greatest block name, so the result is consistent across runs. Otherwise a random one, seeded by [seed] and [address],
 * so the split tree varies with the seed.
 */
internal fun <T : DAGSplitter.Result<*, *>> chooseAmongTied(tied: List<T>, seed: Int, address: SplitAddress): T {
    val byName = tied.sortedBy { it.pivot.toString() }
    return if (seed < 0) {
        byName.last()
    } else {
        byName.random(Random(Objects.hash(seed, address.name())))
    }
}
