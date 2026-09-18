# Verification

All four statements of Challenge.lean have proofs. The local build, the axiom audit, the source
guard and the standard-library cross-check pass.

## Formal scope

| Statement | Proved in |
| --- | --- |
| `GNM.count_eq_one_iff` — `count n = 1` exactly on `N_u` | GNM/Main.lean |
| `GNM.count_eq_two_iff` — `count n = 2` exactly on `E_2` | GNM/Main.lean |
| `GNM.three_le_count_iff` — `count n ≥ 3` off both sets | GNM/Main.lean |
| `GNM.count_eq_two_of_add_six` — `count (3^t − 6) = 2` for `t ≥ 3` | GNM/Main.lean |

Each is restated verbatim in Solution.lean. The layers behind them: the count and its toolkit in
GNM/Basic.lean; the kernel-evaluated checkers and the exhaustive search in GNM/SearchDefs.lean,
GNM/SearchFacts.lean, GNM/Witness.lean and GNM/Search.lean, with the tables in GNM/Data/; the finite
base in GNM/Base.lean; the frames in GNM/Distinct.lean, GNM/Perms.lean, GNM/Prefix.lean and
GNM/Frames.lean; the transports in GNM/Positive.lean, GNM/Negative.lean, GNM/Forced.lean,
GNM/Lift.lean and GNM/Stabilize.lean; the assembly in GNM/Assembly.lean. PROOF.md names the lemma
behind each step. The directory GN/ is an unchanged copy of the gn-lean development at commit
`73bb87b16da8c053fd07e0d4dc43732b74335a3b`; it is rebuilt and audited here with everything else.

## Local checks

```sh
lake build
python scripts/check-source.py
python scripts/check_counts.py
```

The `Test` target audits every constant whose name begins with `GN.`, `GNM.` or the private
auxiliaries Lean generates for them and for Solution (DESK_FILLS at the time of writing, floor
1600), permits only `propext`, `Classical.choice` and `Quot.sound`, and fails if any of the four
compared theorems is missing. A placeholder in a proof compiles with a warning; this audit is what
fails the build. Challenge.lean intentionally contains four proof placeholders; Solution.lean and
the modules it imports contain none, and Solution.lean does not import Challenge.lean. The source
guard rejects `sorry`, `admit`, `axiom`, `unsafe`, `partial`, `native_decide`, `implemented_by`,
`extern`, `Lean.ofReduceBool` and the kernel-bypass options in `GN/`, `GNM/`, Solution.lean and
`Test/`, the same tokens except `sorry` in Challenge.lean, and any `debug.` option in lakefile.toml.

Lean 4.33.0 and Mathlib v4.33.0 (commit `db584cd6d46c92f209a44c0f1c829460d327499d`) are pinned by
the committed manifest; `lake update` is never run.

## The finite computations

There is no `native_decide`. Every finite fact is evaluated by Lean's kernel, and the modules the
kernel works hardest in import no library at all, so that the memory a computation needs is not
added to a Mathlib-loaded process.

| Computation | Where | Size |
| --- | --- | --- |
| The exhaustive search at `n = 86`, `search 86 (baseWitnesses 86) = true` | GNM/SearchFacts.lean | the largest single computation: DESK_FILLS s, DESK_FILLS GB peak |
| The searches at the other nineteen values `1, …, 14, 21, 23, 30, 32, 75` | GNM/SearchFacts.lean | one `decide +kernel` each, DESK_FILLS s in total |
| The checker facts for the tabulated partitions, and their pairwise differences | GNM/SearchFacts.lean | one batch over every tabulated partition at every `n ≤ 86`, DESK_FILLS s, DESK_FILLS GB peak |
| The permutation certificates, `4 ≤ k ≤ 21` | GNM/Perms.lean | three image-equality statements and one distinctness statement per radius, 72 `decide` calls, DESK_FILLS s in total |
| The frame tables at radius eleven, at offset seven and the two tabulated exceptions | GNM/Frames.lean, GNM/Data/Frames.lean | one `decide` per table and per pair of tables, DESK_FILLS s in total |

`scripts/check_counts.py` recomputes the finite content with the standard library and exact
integers: the exact number of good partitions at the twenty values whose count the classification
consumes, three good partitions at each of the 51 values at most eighty outside the two exceptional
sets, a displacement permutation at every hole of every centred interval of radius four to eight,
and two controls. It ends:

```text
ok    control: the blocks {6, 2}, {5, 4}, {3, 1} of sums 8, 9, 4 are not a good partition of {1, ..., 6}, as they must not be
ok    control: at radius 4 no permutation has displacements omitting 1 instead of 0, as there must not be

ALL CHECKS PASSED
```

## Not checked here

- Other bases: nothing is claimed for parts of size at most `m` and sums powers of `m` with
  `m ≠ 3`, which is the source's general question.
- Growth: no asymptotics for `count n` and no closed form are proved; only the values `1` and `2`
  and the bound `3 ≤ count n` are.
- The source's arguments: its Theorem 3 is re-proved here by this development's own route, and no
  proof of the source is formalized.
- The tabulated partitions and permutations are witnesses, not claimed to be canonical or minimal
  in any sense.
- The Python script is a cross-check of finite instances, not a premise of any Lean proof.
