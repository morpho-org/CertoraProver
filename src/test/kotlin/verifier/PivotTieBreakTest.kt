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

package verifier

import org.junit.jupiter.api.Assertions.*
import org.junit.jupiter.api.Test
import verifier.splits.DAGSplitter
import verifier.splits.SplitAddress
import verifier.splits.chooseAmongTied

class PivotTieBreakTest {
    private val tied = listOf("b", "d", "a", "c").map { DAGSplitter.Result(it, 0, 0) }

    /** Without a seed, the pivot with the greatest name wins, whatever the order of the candidates. */
    @Test
    fun noSeedPicksGreatestName() {
        assertEquals("d", chooseAmongTied(tied, -1, SplitAddress.Root).pivot)
        assertEquals("d", chooseAmongTied(tied.reversed(), -1, SplitAddress.Root).pivot)
    }

    /** A seed gives the same choice on every run and for any order of the candidates, and different seeds reach
     * every candidate. */
    @Test
    fun seedIsDeterministicAndVaries() {
        val choices = (0 until 50).map { seed ->
            val choice = chooseAmongTied(tied, seed, SplitAddress.Root).pivot
            assertEquals(choice, chooseAmongTied(tied.reversed(), seed, SplitAddress.Root).pivot)
            choice
        }
        assertEquals(setOf("a", "b", "c", "d"), choices.toSet())
    }
}
