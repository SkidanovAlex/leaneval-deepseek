import Mathlib
import Submission.Work.Serre.relCohMV_les_rat
import Submission.Work.Serre.MVShift.ShQ
import Submission.Work.Cohomology.mixedRelCupH
import Submission.Work.Cohomology.relCupHNatural

/-!
# The honest (cochain-level) cup product with a relative cocycle

For a space `Y` and a subset `B ⊆ Y`, a cocycle `t ∈ C^{n₀}(Y,B)` gives a chain map
`ψ ↦ ψ ⌣ t` from the absolute cochain complex of `Y` to the relative complex of `(Y,B)`, shifted
by `n₀`.  Applying this to the four pairs of an open cover (`X`, `A`), (`U`,`U∩A`), (`V`,`V∩A`)
and (`U∩V`,`U∩V∩A`) and combining, one gets the "honest" cup morphism
`C^*(X,∅) → C^*(U) ⊞ C^*(V) → C^*(U∩V)` ⟶ its shift, whose components are the cup products with
the restrictions of `t`.

These are the chain-level cup maps that the Mayer–Vietoris `δ`-derivation
(`Work.Serre.mvDelta_cup_mixed`) is built from.
-/

set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 4000000

open CategoryTheory CategoryTheory.Limits
open scoped Simplicial

namespace Work.Serre

noncomputable section

variable (X : TopCat) (A U V : Set X) (n₀ : ℕ)

/-! ## The generic construction -/

/-- The linear map `ψ ↦ ψ ⌣ t` on the absolute cochains of `Y`, with values in the relative
cochains of `(Y,B)`, in the degree shifted by `n₀`. -/
noncomputable def cupRelLM (Y : TopCat) (B : Set Y) (n₀ : ℕ)
    (t : Work.Cohomology.relKern ℚ Y B n₀) (k : ℕ) :
    ↥(Work.Cohomology.relKern ℚ Y (∅ : Set Y) k) →ₗ[ℚ]
      ↥(Work.Cohomology.relKern ℚ Y B (k + n₀)) where
  toFun x := (Work.Cohomology.mixedRelStar ℚ Y B k n₀)
    (show Work.Cohomology.Cochain ℚ (TopCat.toSSet.obj Y) k from x.1) t
  map_add' x y := by
    have hx : (show Work.Cohomology.Cochain ℚ (TopCat.toSSet.obj Y) k from (x + y).1)
        = (show Work.Cohomology.Cochain ℚ (TopCat.toSSet.obj Y) k from x.1)
          + (show Work.Cohomology.Cochain ℚ (TopCat.toSSet.obj Y) k from y.1) := rfl
    rw [hx, map_add]
    rfl
  map_smul' c x := by
    have hx : (show Work.Cohomology.Cochain ℚ (TopCat.toSSet.obj Y) k from (c • x).1)
        = c • (show Work.Cohomology.Cochain ℚ (TopCat.toSSet.obj Y) k from x.1) := rfl
    rw [hx, map_smul]
    rfl

/-- **The honest cup product with a relative cocycle**: `ψ ↦ ψ ⌣ t`, as a morphism of cochain
complexes `C^*(Y,∅) ⟶ C^*(Y,B)[n₀]`. -/
noncomputable def cupRelChain (Y : TopCat) (B : Set Y) (n₀ : ℕ)
    (t : Work.Cohomology.relKern ℚ Y B n₀)
    (ht : Work.Cohomology.relDiffLM ℚ Y B n₀ t = 0) :
    Work.Cohomology.relComplex ℚ Y (∅ : Set Y) ⟶
      MVShift.shK (Work.Cohomology.relComplex ℚ Y B) n₀ :=
  CochainComplex.ofHom (fun k => ModuleCat.ofHom (cupRelLM Y B n₀ t k)) (fun k => by
    have ht' : (ModuleCat.Hom.hom ((Work.Cohomology.relComplex ℚ Y B).d n₀ (n₀+1))) t = 0 := by
      rw [Work.Cohomology.relComplex_d]; exact ht
    apply ModuleCat.hom_ext
    apply LinearMap.ext
    intro x
    show (ModuleCat.Hom.hom ((Work.Cohomology.relComplex ℚ Y B).d (k+n₀) ((k+1)+n₀)))
        ((Work.Cohomology.mixedRelStar ℚ Y B k n₀)
          (show Work.Cohomology.Cochain ℚ (TopCat.toSSet.obj Y) k from x.1) t)
      = (Work.Cohomology.mixedRelStar ℚ Y B (k+1) n₀)
          (show Work.Cohomology.Cochain ℚ (TopCat.toSSet.obj Y) (k+1) from
            ((ModuleCat.Hom.hom ((Work.Cohomology.relComplex ℚ Y (∅ : Set Y)).d k (k+1))) x).1) t
    have h := Work.Cohomology.mstar_leibniz_left
      (Work.Cohomology.mixedLeibniz_mixedRelStar ℚ Y B) k n₀
      (show Work.Cohomology.Cochain ℚ (TopCat.toSSet.obj Y) k from x.1) t ht'
    refine h.trans ?_
    rw [Work.Cohomology.relComplex_d]
    rfl)

/-- The degree-`k` component of `cupRelChain` is `cupRelLM`. -/
@[simp] theorem cupRelChain_f (Y : TopCat) (B : Set Y) (n₀ : ℕ)
    (t : Work.Cohomology.relKern ℚ Y B n₀)
    (ht : Work.Cohomology.relDiffLM ℚ Y B n₀ t = 0) (k : ℕ) :
    (cupRelChain Y B n₀ t ht).f k = ModuleCat.ofHom (cupRelLM Y B n₀ t k) := rfl

end

end Work.Serre
