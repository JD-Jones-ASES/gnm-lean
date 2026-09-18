# The proof

The mathematics of the development, with the Lean name carrying each step, in the order a reader
follows the Lean. Everything lives in the namespace `GNM`; the modules are under `GNM/`. The
namespace `GN` is the copied development, whose account is its own `PROOF.md`.

## Notation

Blocks are finite sets of integers. `GNM.IsGoodPartition n bs` says that the blocks of `bs` cover
exactly the integers from `1` to `n`, are pairwise disjoint, and are nonempty with at most three
elements and a sum that is a power of three; `GNM.count n` is the number of such `bs`. The two
exceptional sets are `GNM.Nu` and `GNM.E2`, written with sums (`n + 4 = 3 ^ t`) rather than
subtractions. These four definitions are pinned in `Challenge.lean` and copied verbatim into
`GNM/Defs.lean`.

`GNM.isGoodPartition_iff` identifies the predicate with `GN.GoodOn (GN.interval n)`, so every
theorem of the copied development applies. `GNM.goodPartitions n` is the good partitions as a
`Finset` and `GNM.count_eq_card` its cardinality; `GNM.count_zero` is `count 0 = 1` and
`GNM.one_le_count` is the existence theorem `GN.gurvich_naumova`. The counting steps are
`GNM.three_le_count` (three pairwise distinct partitions), `GNM.count_eq_one_of`,
`GNM.count_eq_two_of`, `GNM.count_le_of_injOn` and `GNM.count_le_of_leftInverse`.

The arithmetic of the two sets is also in `GNM/Basic.lean`: they are disjoint
(`GNM.not_e2_of_nu`); below `250` they are explicit lists (`GNM.nu_iff_of_le`, `GNM.e2_iff_of_le`);
powers of three are separated (`GNM.pow_three_eq_of_lt`); above the fourth power membership is
decided by the offset alone (`GNM.nu_add_iff`, `GNM.not_e2_add`, `GNM.nu_sub_iff`,
`GNM.e2_sub_iff`); and a member at least `33` is `3^s − e` with `e ∈ {1, 2, 3, 4, 6}` or `3^s + c`
with `c ∈ {0, 1, 2, 3, 5}`, `s ≥ 4` (`GNM.exceptional_form`).

Throughout, `P` and `Q` are powers of three, `r` is an offset, and an interval `{1, …, n}` is placed
by the power below it: either `n = P + r` with `2r < P`, or `n = Q − r` with `2r < Q`.

## The finite base

`GNM/SearchDefs.lean` imports nothing and holds the functions the kernel evaluates: `GNM.goodBlock`
and `GNM.checkPartition` decide whether a list of lists of numbers is a good partition of
`{1, …, n}`; `GNM.differ` decides whether two such lists have different block sets; `GNM.framesOK`
and `GNM.differZ` do the same for partitions of a finite set of integers into zero-sum triples; and
`GNM.search` is an exhaustive depth-first search that repeatedly takes the largest uncovered element
and tries every good block containing it, returning `true` exactly when every partition it reaches
is one of a prescribed list. Every recursion is an explicit recursor, and the candidate generator
`GNM.candidates` prunes hard: for a block `{x, a, b}` with `1 ≤ b < a < x` the sum lies strictly
between `x + a` and `x + 2a`, so with the power of three fixed and `a` chosen, `b` is determined.

`GNM/Witness.lean` restates each of those functions in the language of lists and bridges them to the
Finset statements: `GNM.isGoodPartition_of_checkPartition`, `GNM.toBlocks_ne_of_differ`,
`GNM.three_le_count_of_witnesses`, and, for frames, `GNM.zeroPartition_of_framesOK` and
`GNM.toBlocksZ_ne_of_differZ`.

`GNM/Search.lean` proves the search complete. `GNM.mem_candidates_of` says that every good block
containing the head of the list, drawn from the list, is one of the generated candidates, which is
where the bound on the entries enters (the power-of-three test covers the powers below `3^7`, so the
statements assume three times the largest entry is below `729`). `GNM.searchAll_complete` is the
induction on the supply of steps: the block of the largest element is a candidate, erasing it leaves
a good partition of the rest (`GN.GoodOn.erase`), and the recursive call's verdict applies.
`GNM.complete_of_search` is the conclusion for `{1, …, n}`, and
`GNM.count_eq_one_of_search`, `GNM.count_eq_two_of_search` turn an accepting search with one or two
listed partitions into the exact count.

The tables are `GNM/Data/BaseWitnesses.lean`: `GNM.baseWitnesses n` for `n ≤ 86`, three partitions
at every `n ≤ 80` outside the exceptional sets and the complete list at every exceptional `n`.
`GNM/SearchFacts.lean` imports no library and holds the kernel facts, each by `decide +kernel`:
`GNM.allWitnessesOK_true` (every tabulated partition passes the checker), one `GNM.three_ok_n` per
non-exceptional `n ≤ 80` (three of them good and pairwise different), and, at the twenty values
`1, …, 14, 21, 23, 30, 32, 75, 86`, one `GNM.search_n` saying that the search accepts the tabulated
list there.

`GNM/Base.lean` reads those facts off through the bridges and evaluates nothing:
`GNM.three_le_count_of_le_80` (three good partitions at every `n ≤ 80` outside the two sets, taken
in blocks of ten), `GNM.count_eq_one_small` at the sixteen values where the count is one, and
`GNM.count_eq_two_small` at `6`, `13`, `21`, `75`.

## Three distinct frames

`GNM/Distinct.lean` fixes the distinctness predicates. `GNM.ThreePWD S D` is three pairwise distinct
permutations of `S` whose displacements are exactly `D`; `GNM.ThreeDisp k j` reads it on the centred
interval `[−k, k]` with the hole `j` (`GNM.displacementPermutation_iff` identifies the two forms),
`GNM.ThreeM q` on `[1, 2q]` with no hole, and `GNM.ThreeA k H` on `[1, 2k + 1]` with the position
`H` removed. The dictionary between the three coordinate systems is `GNM.threeM_iff_threeA`,
`GNM.threeA_of_threeDisp`, `GNM.threeDisp_of_threeA` and `GNM.ThreeDisp.neg`, with
`GNM.ThreePWD.translate`, `GNM.ThreePWD.negate` and `GNM.ThreePWD.reflect` moving a triple of
permutations. `GNM.ThreeZero s` is three pairwise distinct partitions of `s` into zero-sum triples;
`GNM.ThreeFrames r a` reads it on the signed vertex set `GN.signedVertices r a` and
`GNM.ThreeFrameA r` on `GNM.frameSet r`, the centred interval `[−r, r]` with its centre removed when
three divides `r`.

`GNM/Perms.lean` supplies the small radii. `GNM.witnessPerm` reads a row of the positional tables of
`GNM/Data/Perms.lean` back as a function; `GNM.PermCertificate k i` states the two image equalities
that characterise a displacement permutation at every hole, and `GNM.DistinctCertificate k` that the
three rows differ at every hole. Both are finite and checked by evaluation, one statement per `k`
and per row, giving `GNM.threeDisp_of_le_21` for `4 ≤ k ≤ 21` and every hole.

`GNM/Prefix.lean` removes the bound. The gluing theorem of the copied development fills the small
displacements with one fixed prefix; nothing about that prefix is used beyond its being a
permutation of the initial interval with the small displacements, so `GNM.with_prefix` glues an
arbitrary prefix and records that the result agrees with the prefix on the prefix positions. Hence
three prefixes give three permutations (`GNM.threeA_of_pairing`), and with the six Langford families
of `GN.Universal` the upper-half holes are covered (`GNM.threeA_high`), reflection covers the lower
half (`GNM.threeA_reflect`), and a strong induction on the length gives `GNM.threeM_all` for every
`q ≥ 5`, then `GNM.threeA_all` and `GNM.threeDisp_all` for every `k ≥ 4` and every hole.

`GNM/Frames.lean` turns permutations into frames, in two supplies.

*Signed frames.* `GNM.signedFrame k j a σ` is the set of residue triples
`{3u + 1, −(3σ(u) + 1), 3(σ(u) − u)}` of a displacement permutation together with the outer triple
`{a, 3k + 2, −(3k + 2 + a)}`. It partitions the signed vertex set into zero-sum triples
(`GNM.signedFrame_zeroPartition`), and it is injective in the permutation, because the triple of a
domain point carries the only entry of residue one that it can (`GNM.signedFrame_ne`). So three
permutations give three frames (`GNM.threeFrames_of_threeDisp`), and with the tabulated frames at
radius eleven (`GNM.threeFrames_eleven`) and `GN.exists_residue_hole` one gets
`GNM.threeFrames_of_mod`: three frames for every partner not divisible by three at every offset
`r ≥ 11` with `r ≡ 2 (mod 3)`. `GNM.threeFrames_eight_one` is the tabulated case used at offset
eight.

*Symmetric frames.* `GNM.symFamily k` is the pair of explicit triple families of the copied
development read at the centre zero; it partitions `GNM.symInterval k`, the centred interval of
radius `3k` without zero (`GNM.symFamily_zeroPartition`). Negating every entry gives a second
partition of the same set (`GNM.ZeroPartition.negBlocks`, `GNM.symInterval_neg`), different from the
first because the block of `−3k` differs (`GNM.symFamily_ne_neg`). A third comes from one of three
trades, which replace three triples of the family by three others according to `k mod 3`:
`GNM.tradeI`, `GNM.tradeII`, `GNM.tradeIII`, each with its coverage and its two distinctness
statements. The exception `k = 5` is tabulated. This is `GNM.threeZero_sym` for every `k ≥ 3`, and
`GNM.threeFrameA_of_threeZero_sym` transports it to the offsets `3k` and `3k + 1`, the second by
adjoining the central triple `{−(3k + 1), 0, 3k + 1}`. With the tabulated frame at offset seven
(`GNM.threeFrameA_seven`) this is `GNM.threeFrameA_of_mod`: three frames at every offset `r ≥ 7`
with `r ≡ 0, 1 (mod 3)`.

## The positive offsets

Let `n = P + r` with `2r < P`. In `GNM/Positive.lean` a partition of `{1, …, n}` is assembled from a
partition of a smaller interval and a frame shifted to sit around `P`, where a zero-sum triple
becomes a triple of sum `3P` (`GNM.shiftBlocks`, `GNM.sum_shift_of_zero`).

*Lemma A.* `GNM.targetA P src zs c` is a partition `src` of `{1, …, P − r − 1}`, the shifted frame,
and the singleton `{P}` when three divides `r`. It is a good partition of `{1, …, P + r}`
(`GNM.targetA_goodOn`), the blocks of sum `3P` are exactly the shifted frame
(`GNM.targetA_frame`), and the blocks lying below `P − r` are exactly `src` (`GNM.targetA_src`), so
different frames and different sources give different targets (`GNM.targetA_ne_of_frame_ne`,
`GNM.targetA_ne_of_src_ne`). With `GNM.threeFrameA_of_mod` this is
`GNM.three_le_count_add_of_threeFrameA` at every offset `r ≡ 0, 1 (mod 3)`.

*Lemma B.* For `r ≡ 2 (mod 3)` the source is a partition of `{1, …, r}`; its block containing `r`
has a partner `a` not divisible by three (`GN.GoodOn.maximum_partner`), and contracting that block
at the partner (`GN.contractBlock`) frees the signed vertex set on which the frame lives.
`GNM.targetB` is the contracted source, the singleton `{P}`, the shifted signed frame, and the
complement pairs `{x, P − x}` over the elements below `P` not yet covered (`GNM.contractedSource`,
`GNM.uncovered`); it is good (`GNM.targetB_goodOn`) and again its blocks of sum `3P` are exactly the
frame (`GNM.targetB_frame`). So three signed frames give three partitions
(`GNM.three_le_count_add_of_source`), and with `GNM.threeFrames_of_mod` this is
`GNM.three_le_count_add_of_threeFrames` for `r ≥ 11`, `r ≡ 2 (mod 3)`.

Three small offsets are outside both supplies and are treated explicitly, for `P ≥ 27`: offset four
(`GNM.three_le_count_add_four`), where all three partitions share the canonical pairs on
`[6, P − 6]` and combine two frames covering `[P − 4, P + 4]` with two ways of covering `{1, …, 5}`
and the deficit five; offset six (`GNM.three_le_count_add_six`), where the two good partitions of
`{1, …, 6}` extended by complement pairs meet the symmetric family at `k = 2` and its negation; and
offset eight (`GNM.three_le_count_add_eight`), where the source is the good partition of
`{1, …, 8}`, whose partner is `1`, and the three frames are the tabulated ones on the signed vertex
set of that partner.

## Forced blocks, the lift, and stabilization

`GNM/Forced.lean` bounds what a good partition can do near the top of the interval. Below a power,
a block containing an element above `(Q − 1)/2` sums to `Q` and its other elements are small
(`GNM.high_block_sub`). Just above a power, with `P > r(r + 1)`, such a block is `{P}`, or sums to
`P` with one high element, or sums to `3P` with three high elements (`GNM.high_block_add`).

Counting mass then forces large deficits. For each deficit `d`, the low part of the block of `Q − d`
sums to `d`; summing over `d` and comparing with the total mass of the low elements shows that the
blocks with no high element carry at most `r(r − 1)/2`. A descent on the largest non-canonical
deficit removes the rest: if the low part of the block of `Q − d` is not the singleton `{d}`, then
`d` itself sits in a low-only block, too light, or in the block of a larger non-canonical deficit.
This is `GNM.canonical_sub`; `GNM.canonical_add` is the same with the extra step that the elements
above `P` lie in `3P`-blocks whose offsets cancel, so the deficits those blocks use also sum to
`r(r + 1)/2`.

`GNM/Lift.lean` builds the bijection between two powers. `GNM.canonicalPairs Q lo hi` is the pairs
`{d, Q − d}` for `d` in a range, a good partition of the range and its complement
(`GNM.canonicalPairs_goodOn`). `GNM.liftBlocks Q Q'` relabels every element above `(Q − 1)/2` by the
gap `Q' − Q` and adds the canonical pairs for the deficits in between; it carries good partitions
upwards at a negative offset (`GNM.liftBlocks_goodOn_sub`) and at a positive one
(`GNM.liftBlocks_goodOn_add`). `GNM.truncBlocks Q Q'` drops those pairs and relabels back; it
inverts the lift unconditionally (`GNM.truncBlocks_liftBlocks_sub`,
`GNM.truncBlocks_liftBlocks_add`) and, above the threshold, is inverted by it
(`GNM.liftBlocks_truncBlocks_sub`, `GNM.liftBlocks_truncBlocks_add`) — precisely because the pairs
to be dropped have large deficits, hence are canonical, hence are present in every good partition of
the larger interval. One direction alone already gives monotonicity
(`GNM.count_sub_le_count_sub`), and both directions give equality in `GNM/Stabilize.lean`:
`GNM.count_sub_eq` and `GNM.count_add_eq`, the counts along one family of offsets are the same at
every admissible power.

## The negative offsets

Let `n = Q − r` with `2r < Q`. In `GNM/Negative.lean`, `GNM.targetC Q r src` is a good partition
`src` of `{1, …, r − 1}` together with the canonical pairs `{d, Q − d}` for `r ≤ d ≤ (Q − 1)/2`
(`GNM.targetC_goodOn`). The source is recovered as the blocks lying below `r`
(`GNM.targetC_src`), so distinct sources give distinct targets and
`GNM.count_pred_le_count_sub` reads `count (r − 1) ≤ count (Q − r)`.

That route is closed when `r − 1` is itself exceptional, and two gadgets replace it, for `3R ≤ Q`.
When `r − 1 = R − e` with `e ∈ {1, 2, 3, 4, 6}` and `R = 3^s ≥ 27`, the source is a partition of
`{1, …, e − 1}` with the pairs `{j, R − j}`, and the three targets are its canonical extension and
the two single merges `{j, R − j, Q − R}` together with `{R}`, at `j = e` and at `j = e + 1`; the
block containing `Q − R` separates them (`GNM.three_le_count_sub_below`). When `r = R + δ` with
`δ ∈ {1, 2, 3, 4, 6}` and `R = 3^s ≥ 81`, the source is the tabulated partition of `{1, …, R + δ − 1}`
and the three targets differ by a three-pair merge at two places, separated by the smallest
non-canonical deficit (`GNM.three_le_count_sub_above`).

## The assembly

`GNM/Assembly.lean` puts the regimes together. `GNM.three_le_count_of_not_exceptional` is a strong
induction on `n`: at `n ≤ 80` it is the finite base; above, `P = 3 ^ Nat.log 3 n` is at least `81`.
In the positive regime the offset is not in `{0, 1, 2, 3, 5}` (`GNM.nu_add_iff`), so it is four, six,
eight, or at least seven with a residue the frames cover. In the negative regime the offset is at
least `5` (`GNM.nu_sub_iff`, `GNM.e2_sub_iff`); if `r − 1` is not exceptional the induction
hypothesis and `GNM.count_pred_le_count_sub` finish; if it is exceptional and `r ≤ 33`, then
`81 − r` is not exceptional and `GNM.count_sub_le_count_sub` carries the base's three partitions up
from `3^4`; and if `r − 1 ≥ 33`, `GNM.exceptional_form` puts `r` in the range of one of the two
gadgets. `GNM.count_eq_one_of_nu` and `GNM.count_eq_two_of_e2` case on the members of the two sets:
the finite ones come from `GNM.count_eq_one_small` and `GNM.count_eq_two_small`, and each family
from its first admissible power by `GNM.count_add_eq` or `GNM.count_sub_eq`.

`GNM/Main.lean` reads the three assembly theorems as equivalences, since they are mutually exclusive
and cover every `n ≥ 1`: `GNM.count_eq_one_iff_internal`, `GNM.count_eq_two_iff_internal`,
`GNM.three_le_count_iff_internal`, and `GNM.count_eq_two_of_add_six_internal` for the family six
below a power. `Solution.lean` restates the four verbatim.

## References

- Vladimir Gurvich and Mariya Naumova, *Partitioning set [n] = {1, …, n} into subsets of size at
  most m such that all sums are powers of m*, arXiv:2508.00946v3.
- S. Mor and V. Linek, *Hooked extended Langford sequences of small and large defects*, Mathematica
  Slovaca 64 (2014) 819–842, doi:10.2478/s12175-014-0242-6 — the Langford formulas adapted inside
  `GN/`.
- Diane M. Donovan and Michael J. Grannell, *On the number of additive permutations and Skolem-type
  sequences*, Ars Mathematica Contemporanea 14 (2018) 415–432, doi:10.26493/1855-3974.1098.ca0 —
  lower bounds for the number of additive permutations of a centred interval. Deleting the fixed
  point of such a permutation leaves a displacement permutation with one hole, so that count is the
  count used here summed over the hole. Nothing from it is used.
