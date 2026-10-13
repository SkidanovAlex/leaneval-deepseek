import Mathlib
import Submission.Work.WilC4.Defs
import Submission.Work.WilC4.sup_exists_dcl
import Submission.Work.WilC2.finite_definable_singleton

namespace Work.WilC4g

/-- `DefinableElt T ∅ x` is exactly "the singleton `{x}` is `T`-definable in one variable".
The two formulations differ only in how the one-element set is written: `DefinableElt` uses
the set of the *constant function* `fun _ : Fin 1 => x`, while `Definable₁` uses the set of
one-tuples whose coordinate lies in `{x}`.  Since `Fin 1` is a subsingleton, these two sets
of functions `Fin 1 → M` coincide. -/
lemma definableElt_empty_iff_singleton {M : Type} [Field M] [LinearOrder M]
    [IsStrictOrderedRing M] [FirstOrder.Ring.CompatibleRing M]
    [WilkiesDesign.CG.rexpL.Structure M] [(FirstOrder.Language.constantsOn ℝ).Structure M]
    {T : Set M} {x : M} :
    Work.WilC4.DefinableElt T ∅ x ↔ T.Definable₁ WilkiesDesign.CG.LRc ({x} : Set M) := by
  have hset : {v : Fin 1 → M | v 0 ∈ ({x} : Set M)} = {fun _ : Fin 1 => x} := by
    ext v
    simp only [Set.mem_ofPred_eq, Set.mem_singleton_iff]
    constructor
    · intro hv
      funext i
      fin_cases i
      exact hv
    · intro hv
      rw [hv]
  unfold Work.WilC4.DefinableElt Set.Definable₁
  rw [Set.union_empty, hset]

theorem finiteDefinable_subset_T {M : Type} [Field M] [LinearOrder M] [IsStrictOrderedRing M] [FirstOrder.Ring.CompatibleRing M] [WilkiesDesign.CG.rexpL.Structure M] [(FirstOrder.Language.constantsOn ℝ).Structure M] (hM : M ⊨ WilkiesDesign.CG.TR) {T : Set M} (hTdcl : ∀ x : M, Work.WilC4.DefinableElt T ∅ x ↔ x ∈ T) {D : Set M} (hDdef : T.Definable₁ WilkiesDesign.CG.LRc D) (hfin : D.Finite) : D ⊆ T := by
  intro d hd
  -- every element of a finite `T`-definable set is `T`-definable
  have hsing : T.Definable₁ WilkiesDesign.CG.LRc ({d} : Set M) :=
    Work.WilC2.finite_definable_singleton hM hDdef hfin d hd
  -- and `T` is `dcl`-closed, so it belongs to `T`
  exact (hTdcl d).mp ((definableElt_empty_iff_singleton (T := T) (x := d)).mpr hsing)

end Work.WilC4g
