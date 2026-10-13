import Submission.Work.Wilkies.CG.Spec

/-!
LEAD-OWNED (curric-46, 2026-10-11; ruling cbc/wilkies_c5c4_ruling.md). Do not edit.

`ValProp` — the valuation property for `TR` (vdDMM (3.7), containment half), stated with the
same binders as the frozen `WilkiesDesign.CG.ValIneq`. It is true for `TR` but NOT derivable from
`hMCr`, `hOM`, `hVI`; C5 takes it as the explicit hypothesis `hVP`, and it is discharged by the
separate node `ValProp_TR` at the final wire.
-/

open Classical
open WilkiesConjecture WilkiesDesign FirstOrder Language WilkiesDesign.CG

namespace Work.WilC5

/-- Valuation property for TR: if some element definable from `S ∪ {z}` has a value outside
`v(S^×)`, then so does some translate `z − a`, `a ∈ S`. -/
def ValProp : Prop :=
  ∀ (M : Type) [Field M] [LinearOrder M] [IsStrictOrderedRing M] [Ring.CompatibleRing M]
    [rexpL.Structure M] [(constantsOn ℝ).Structure M] [M ⊨ TR]
    (S : LRc.ElementarySubstructure M) (z w : M), w ≠ 0 →
    ((S : Set M) ∪ {z}).Definable LRc {fun _ : Fin 1 => w} →
    (∀ c ∈ (S : Set M), ¬ IsUnitVal (c * w)) →
    ∃ a ∈ (S : Set M), z - a ≠ 0 ∧ ∀ c ∈ (S : Set M), ¬ IsUnitVal (c * (z - a))

end Work.WilC5
