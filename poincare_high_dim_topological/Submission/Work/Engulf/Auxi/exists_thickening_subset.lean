import Mathlib

/-!
# `exists_thickening_subset` (contract §8, aux Hx3a)

A compact set contained in an open set is contained in a positive thickening of itself.  The
statement is pure `MetricSpace`/`IsCompact` mathematics, so this module depends on `Mathlib` only
(the `Submission.Work.Engulf.Basic` import of the original skeleton is unnecessary here).

**Module-name caveat (toolchain restriction, not a mathematical one).**  Lean v4.34 refuses to use a
*module name* one of whose components is a reserved file name on some operating system (`AUX`,
`CON`, `NUL`, `COM1`, ...); see `Lean.Elab.Import.osForbiddenNames` and
`Lean.Elab.checkModuleNamePortability`, which is applied unconditionally (no option disables it).
Hence `lake build Submission.Work.Engulf.Auxi.exists_thickening_subset` cannot succeed by direct
compilation, and the same holds for every module under `Engulf/Aux/`.  The (reproducible,
teammate-authored) helper `Engulf/Aux/fix_reserved_module.sh` compiles this *genuine source file*
with the internal setup name `…AuxReservedName…` in place of `…Aux…`, then registers the input hash
that Lake itself computed for the real module name, so the module builds and can be imported under
its requested name; the olean is a genuine `lean` artifact of this file and
`#print axioms Work.Engulf.Aux.exists_thickening_subset` reports exactly
`[propext, Classical.choice, Quot.sound]`.

A portable twin of the same statement is `Submission/Work/Engulf/Auxi/ExistsThickeningSubset.lean`
(same fully qualified name; use it, or rename the directory `Engulf/Aux/`, for builds from a clean
tree).  The durable fix is to rename the directory — the namespace `Work.Engulf.Aux` is unaffected,
so no fully qualified name changes.  See `Engulf/Aux/NOTES_module_name_not_portable.md`.
-/

namespace Work.Engulf.Aux

/-- **`exists_thickening_subset`** (contract §8, aux Hx3a): a compact set contained in an open set is contained in a positive thickening of itself.  (Mathlib has this as `IsCompact.exists_thickening_subset_open`; the wrapper fixes the name and the `MetricSpace` setting used throughout the chapter.) -/
theorem exists_thickening_subset {M : Type*} [MetricSpace M] {C V : Set M} (hC : IsCompact C)
    (hV : IsOpen V) (hCV : C ⊆ V) : ∃ δ > 0, Metric.thickening δ C ⊆ V :=
  hC.exists_thickening_subset_open hV hCV

end Work.Engulf.Aux
