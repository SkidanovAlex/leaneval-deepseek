import Mathlib
import Submission.Work.Serre.relCohMV_les_rat
import Submission.Work.Serre.MVCohRatDefs
import Submission.Work.Serre.MVShift.ShQ
import Submission.Work.Cohomology.cappedPairDefs

/-!
# The "honest" Mayer–Vietoris short complex `Smv` and its comparison with the small model

`Work.Serre.mvDelta` is the connecting map of the rational relative Mayer–Vietoris sequence, defined
in `Submission/Work/Serre/relCohMV_les_rat.lean` by conjugating the connecting map of the *small*
model `Work.Serre.dqShort` along the comparison morphisms `zetaTop, zetaMid, zetaW`.

This file introduces

* `Smv`: the **honest** short complex `C^*(X,A) → C^*(U,A∩U) ⊞ C^*(V,A∩V) → C^*(U∩V,A∩U∩V)`
  (it is *not* short exact — that is exactly why the small model is needed);
* `zetaSmv : Smv ⟶ dqShort`: the comparison morphism, whose three components are quasi-isomorphisms.

The point of `Smv` is that the *chain-level* cup product with a global cocycle is a morphism of short
complexes `Smv_{∅} ⟶ shS Smv_A n`, so that a chain-level inverse of the comparison transports this
to a `δ`-square for the small model.
-/

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
set_option maxHeartbeats 1600000

namespace Work.Serre.MVGlue

open CategoryTheory CategoryTheory.Limits

noncomputable section

variable (X : TopCat) (A U V : Set X)

/-! ## The two restrictions to the overlap agree -/

/-- `relComplexMap` does not depend on the proof that the first set is carried into the second
(over `ℚ`). -/
theorem relComplexMap_hcongrQ {Y Z : TopCat} (A₁ : Set Y) (A₂ : Set Z) (f : Y ⟶ Z)
    (h h' : ∀ x ∈ A₁, f x ∈ A₂) :
    Work.Cohomology.relComplexMap ℚ A₁ A₂ f h = Work.Cohomology.relComplexMap ℚ A₁ A₂ f h' := by
  apply HomologicalComplex.hom_ext
  intro n
  apply ModuleCat.hom_ext
  apply LinearMap.ext
  intro x
  apply Subtype.ext
  simp only [ModuleCat.hom_ofHom, Work.Cohomology.relMapLM_coe]

/-- `relComplexMap` does not depend on the chosen spelling of the map (over `ℚ`). -/
theorem relComplexMap_congr_mapQ {Y Z : TopCat} (A₁ : Set Y) (A₂ : Set Z) {f g : Y ⟶ Z}
    (hfg : f = g) (h : ∀ x ∈ A₁, f x ∈ A₂) (h' : ∀ x ∈ A₁, g x ∈ A₂) :
    Work.Cohomology.relComplexMap ℚ A₁ A₂ f h = Work.Cohomology.relComplexMap ℚ A₁ A₂ g h' := by
  subst hfg
  exact relComplexMap_hcongrQ A₁ A₂ _ h h'

/-- **The two spellings of the restriction of a relative class to the overlap agree** (chain level):
this is the chain-level form of `Work.Serre.mvRestrVU_eq`. -/
theorem mvFU_comp_mvGWU :
    Work.Serre.mvFU X A U ≫ Work.Serre.mvGWU X A U V
      = Work.Serre.mvFU X A V ≫ Work.Serre.mvGWV X A U V := by
  have hUV : (Work.Cohomology.pdIncl U (U ∩ V) Set.inter_subset_left) ≫
        (Work.Cohomology.subtypeIncl X U)
      = (Work.Cohomology.pdIncl V (U ∩ V) Set.inter_subset_right) ≫
        (Work.Cohomology.subtypeIncl X V) := by
    ext x
    rfl
  simp only [Work.Serre.mvFU, Work.Serre.mvGWU, Work.Serre.mvGWV]
  rw [← Work.Cohomology.relComplexMap_comp ℚ (Work.Cohomology.interAU A (U ∩ V))
      (Work.Cohomology.interAU A U) A (Work.Cohomology.pdIncl U (U ∩ V) Set.inter_subset_left)
      (Work.Cohomology.subtypeIncl X U) (Work.Cohomology.interAU_incl_pdIncl_U X A U V)
      (Work.Cohomology.interAU_incl_subtypeIncl X A U)]
  rw [← Work.Cohomology.relComplexMap_comp ℚ (Work.Cohomology.interAU A (U ∩ V))
      (Work.Cohomology.interAU A V) A (Work.Cohomology.pdIncl V (U ∩ V) Set.inter_subset_right)
      (Work.Cohomology.subtypeIncl X V) (Work.Cohomology.interAU_incl_pdIncl_V X A U V)
      (Work.Cohomology.interAU_incl_subtypeIncl_V X A V)]
  exact relComplexMap_congr_mapQ (Work.Cohomology.interAU A (U ∩ V)) A hUV
    (fun x hx => Work.Cohomology.interAU_incl_subtypeIncl X A U
      ((Work.Cohomology.pdIncl U (U ∩ V) Set.inter_subset_left) x)
      (Work.Cohomology.interAU_incl_pdIncl_U X A U V x hx))
    (fun x hx => Work.Cohomology.interAU_incl_subtypeIncl_V X A V
      ((Work.Cohomology.pdIncl V (U ∩ V) Set.inter_subset_right) x)
      (Work.Cohomology.interAU_incl_pdIncl_V X A U V x hx))

/-- The two composites of the `F`- and `G`-maps vanish (chain level). -/
theorem mvF_comp_mvG :
    Work.Serre.mvFChain X A U V ≫ Work.Serre.mvGChain X A U V = 0 := by
  rw [Work.Serre.mvFChain, Work.Serre.mvGChain, biprod.lift_desc, Preadditive.comp_neg]
  rw [show (Work.Serre.mvFU X A U ≫ Work.Serre.mvGWU X A U V)
      + -(Work.Serre.mvFU X A V ≫ Work.Serre.mvGWV X A U V)
      = (Work.Serre.mvFU X A U ≫ Work.Serre.mvGWU X A U V)
        - (Work.Serre.mvFU X A V ≫ Work.Serre.mvGWV X A U V) from (sub_eq_add_neg _ _).symm]
  exact sub_eq_zero.mpr (mvFU_comp_mvGWU X A U V)

/-! ## The honest Mayer–Vietoris short complex -/

/-- **The honest Mayer–Vietoris short complex** `C^*(X,A) → C^*(U,A∩U) ⊞ C^*(V,A∩V) →
C^*(U∩V,A∩U∩V)` in honest rational cochains.  It is *not* short exact; the small model
`Work.Serre.dqShort` is the short exact model of the same sequence. -/
noncomputable def Smv : ShortComplex (CochainComplex (ModuleCat ℚ) ℕ) :=
  ShortComplex.mk (Work.Serre.mvFChain X A U V) (Work.Serre.mvGChain X A U V)
    (mvF_comp_mvG X A U V)

@[simp] theorem Smv_f : (Smv X A U V).f = Work.Serre.mvFChain X A U V := rfl
@[simp] theorem Smv_g : (Smv X A U V).g = Work.Serre.mvGChain X A U V := rfl

/-! ## The comparison morphism -/

/-- **The comparison `Smv ⟶ dqShort`**: its three components are `zetaTop, zetaMid, zetaW`, the
comparisons of the honest cochain complexes with the `ℚ`-duals of the small chains. -/
noncomputable def zetaSmv : Smv X A U V ⟶ Work.Serre.dqShort X A U V where
  τ₁ := Work.Serre.zetaTop X A U V
  τ₂ := Work.Serre.zetaMid X A U V
  τ₃ := Work.Serre.zetaW X A U V
  comm₁₂ := Work.Serre.natA X A U V
  comm₂₃ := Work.Serre.natB X A U V

@[simp] theorem zetaSmv_τ₁ : (zetaSmv X A U V).τ₁ = Work.Serre.zetaTop X A U V := rfl
@[simp] theorem zetaSmv_τ₂ : (zetaSmv X A U V).τ₂ = Work.Serre.zetaMid X A U V := rfl
@[simp] theorem zetaSmv_τ₃ : (zetaSmv X A U V).τ₃ = Work.Serre.zetaW X A U V := rfl

/-- The comparison is a quasi-isomorphism on the first component. -/
theorem isIso_zetaSmv_τ₁ (hU : IsOpen U) (hV : IsOpen V) (hcov : U ∪ V = Set.univ) (k : ℕ) :
    IsIso (HomologicalComplex.homologyMap (zetaSmv X A U V).τ₁ k) := by
  rw [zetaSmv_τ₁]
  exact Work.Serre.isIso_homologyMap_zetaTop X A U V hU hV hcov k

/-- The comparison is a quasi-isomorphism on the third component. -/
theorem isIso_zetaSmv_τ₃ (k : ℕ) :
    IsIso (HomologicalComplex.homologyMap (zetaSmv X A U V).τ₃ k) := by
  rw [zetaSmv_τ₃]
  exact Work.Serre.isIso_homologyMap_zetaW X A U V k


/-- The overlap `U ∩ V` as a space, as a *named* abbreviation, so that statements can mention it
without the `↥` coercion. -/
abbrev ovl (X : TopCat) (U V : Set X) : Type := ↥(U ∩ V)

/-! ## The cup map with a fixed relative class -/

/-- The cup map with a fixed relative class `z`, as a `ℚ`-linear map. -/
noncomputable def cupWith (B : Type) [TopologicalSpace B] (A : Set B) (m n : ℕ)
    (z : Work.Thom.RelCoh ℚ n B A) :
    Work.Thom.Coh ℚ m B →ₗ[ℚ] Work.Thom.RelCoh ℚ (m + n) B A where
  toFun y := (Work.Thom.mixedCupC ℚ A m n) y z
  map_add' y y' := by simp
  map_smul' c y := by simp

end

end Work.Serre.MVGlue
