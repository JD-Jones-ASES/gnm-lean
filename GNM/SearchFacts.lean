import GNM.SearchDefs
import GNM.Data.BaseWitnesses

/-!
# The kernel-checked finite facts

This module imports nothing from Mathlib. Each theorem is a closed computation, checked by Lean's
kernel: the exhaustive search of `GNM.SearchDefs` accepts the listed partitions of `{1, …, n}` as
the only good partitions at the twenty values of `n` the classification consumes, and the listed
partitions pass the checker. The modules that import this one turn these facts into statements
about `IsGoodPartition` and `count`.
-/

namespace GNM

/-- Every good partition of `{1, …, 1}` is among the listed ones. -/
theorem search_1 : search 1 (baseWitnesses 1) = true := by decide +kernel
/-- Every good partition of `{1, …, 2}` is among the listed ones. -/
theorem search_2 : search 2 (baseWitnesses 2) = true := by decide +kernel
/-- Every good partition of `{1, …, 3}` is among the listed ones. -/
theorem search_3 : search 3 (baseWitnesses 3) = true := by decide +kernel
/-- Every good partition of `{1, …, 4}` is among the listed ones. -/
theorem search_4 : search 4 (baseWitnesses 4) = true := by decide +kernel
/-- Every good partition of `{1, …, 5}` is among the listed ones. -/
theorem search_5 : search 5 (baseWitnesses 5) = true := by decide +kernel
/-- Every good partition of `{1, …, 6}` is among the listed ones. -/
theorem search_6 : search 6 (baseWitnesses 6) = true := by decide +kernel
/-- Every good partition of `{1, …, 7}` is among the listed ones. -/
theorem search_7 : search 7 (baseWitnesses 7) = true := by decide +kernel
/-- Every good partition of `{1, …, 8}` is among the listed ones. -/
theorem search_8 : search 8 (baseWitnesses 8) = true := by decide +kernel
/-- Every good partition of `{1, …, 9}` is among the listed ones. -/
theorem search_9 : search 9 (baseWitnesses 9) = true := by decide +kernel
/-- Every good partition of `{1, …, 10}` is among the listed ones. -/
theorem search_10 : search 10 (baseWitnesses 10) = true := by decide +kernel
/-- Every good partition of `{1, …, 11}` is among the listed ones. -/
theorem search_11 : search 11 (baseWitnesses 11) = true := by decide +kernel
/-- Every good partition of `{1, …, 12}` is among the listed ones. -/
theorem search_12 : search 12 (baseWitnesses 12) = true := by decide +kernel
/-- Every good partition of `{1, …, 13}` is among the listed ones. -/
theorem search_13 : search 13 (baseWitnesses 13) = true := by decide +kernel
/-- Every good partition of `{1, …, 14}` is among the listed ones. -/
theorem search_14 : search 14 (baseWitnesses 14) = true := by decide +kernel
/-- Every good partition of `{1, …, 21}` is among the listed ones. -/
theorem search_21 : search 21 (baseWitnesses 21) = true := by decide +kernel
/-- Every good partition of `{1, …, 23}` is among the listed ones. -/
theorem search_23 : search 23 (baseWitnesses 23) = true := by decide +kernel
/-- Every good partition of `{1, …, 30}` is among the listed ones. -/
theorem search_30 : search 30 (baseWitnesses 30) = true := by decide +kernel
/-- Every good partition of `{1, …, 32}` is among the listed ones. -/
theorem search_32 : search 32 (baseWitnesses 32) = true := by decide +kernel
/-- Every good partition of `{1, …, 75}` is among the listed ones. -/
theorem search_75 : search 75 (baseWitnesses 75) = true := by decide +kernel
/-- Every good partition of `{1, …, 86}` is among the listed ones. -/
theorem search_86 : search 86 (baseWitnesses 86) = true := by decide +kernel

end GNM
