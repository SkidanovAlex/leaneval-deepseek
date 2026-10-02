import Mathlib
import Submission.Work.LerayHirsch.LhTwoCoverDefs
import Submission.Work.LerayHirsch.MvAux.BiprodElem

-- Lean v4.35.0-rc3: restore v4.34 instance-unification transparency (port).
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
set_option synthInstance.maxHeartbeats 400000

set_option autoImplicit false
set_option maxHeartbeats 1600000
set_option linter.unusedVariables false
set_option linter.unusedSectionVars false

/-!
# The honest Mayer–Vietoris maps in the `pdCoh` model: elementwise form

The three maps of the honest relative Mayer–Vietoris sequence of the cover `U ∪ V` of `B`
(`Work.Cohomology.honestF`, `honestG`, `honestDelta`) are bundled as `ShortComplex` morphisms; for
the ladder of `Submission/Work/LerayHirsch/Mv_exact.lean` their *elementwise* behaviour is needed:

* `honestF_apply_pair`: `honestF` evaluated at a class is the pair of its two restrictions;
* `honestG_apply_pair`: `honestG` evaluated at a pair is the difference of the two restrictions to
  the overlap;
* `honestF_ker_zero`: at degree `0` the first map is injective (so its kernel is `⊥`);
* `mem_ker_honestF`: membership in `ker honestF` is the pair of memberships in the two kernels;
* `honestDelta_comp_pdCohRes`: `δ` followed by either restriction is `0`;
* `pdCast_comp_pdCast_symm`: the degree cast and its inverse compose to the identity.
-/

namespace Work.LerayHirsch.MvAux

open CategoryTheory CategoryTheory.Limits
open Work.Cohomology

variable {B : Type} [TopologicalSpace B] {U V : Set B}

/-- `honestF` on an element: the pair of the two restrictions. -/
theorem honestF_apply_pair (d : ℕ) (z : ↑(pdCoh (TopCat.of B) (∅ : Set B) d)) :
    ModuleCat.Hom.hom (honestF (TopCat.of B) (∅ : Set B) U V d) z
      = biprodPair
          (ModuleCat.Hom.hom (pdCohRes (TopCat.of B) (∅ : Set B) U d) z)
          (ModuleCat.Hom.hom (pdCohRes (TopCat.of B) (∅ : Set B) V d) z) := by
  unfold Work.Cohomology.honestF
  exact biprod_lift_apply _ _ z

/-- Membership in the kernel of `honestF` is membership in the kernels of the two restrictions. -/
theorem mem_ker_honestF (d : ℕ) (z : ↑(pdCoh (TopCat.of B) (∅ : Set B) d)) :
    z ∈ (ModuleCat.Hom.hom (honestF (TopCat.of B) (∅ : Set B) U V d)).ker
      ↔ (ModuleCat.Hom.hom (pdCohRes (TopCat.of B) (∅ : Set B) U d) z = 0
        ∧ ModuleCat.Hom.hom (pdCohRes (TopCat.of B) (∅ : Set B) V d) z = 0) := by
  rw [LinearMap.mem_ker, honestF_apply_pair, biprodPair_eq_zero]

/-- At degree `0`, `honestF` is injective; its kernel is `⊥`. -/
theorem honestF_ker_eq_bot (hU : IsOpen U) (hV : IsOpen V) (hcov : U ∪ V = Set.univ) :
    (ModuleCat.Hom.hom (honestF (TopCat.of B) (∅ : Set B) U V 0)).ker = ⊥ :=
  LinearMap.ker_eq_bot.mpr
    (Work.Thom.honestF_injective_zero (TopCat.of B) (∅ : Set B) U V hU hV hcov)

/-- `honestG` on a pair: the difference of the two restrictions to the overlap. -/
theorem honestG_apply_pair (d : ℕ) (u : ↑(pdCohSub (TopCat.of B) (∅ : Set B) U d))
    (v : ↑(pdCohSub (TopCat.of B) (∅ : Set B) V d)) :
    ModuleCat.Hom.hom (honestG (TopCat.of B) (∅ : Set B) U V d) (biprodPair u v)
      = ModuleCat.Hom.hom
            (pdCohMap (TopCat.of B) (∅ : Set B) U (U ∩ V) Set.inter_subset_left d) u
        - ModuleCat.Hom.hom
            (pdCohMap (TopCat.of B) (∅ : Set B) V (U ∩ V) Set.inter_subset_right d) v := by
  unfold Work.Cohomology.honestG
  rw [biprod_desc_apply, biprodPair_fst, biprodPair_snd, ModuleCat.hom_neg, LinearMap.neg_apply,
    sub_eq_add_neg]

/-- `honestDelta` followed by either restriction to a piece is `0`. -/
theorem honestDelta_comp_pdCohRes (hU : IsOpen U) (hV : IsOpen V) (hcov : U ∪ V = Set.univ)
    (d : ℕ) :
    honestDelta (TopCat.of B) (∅ : Set B) U V hU hV hcov d
        ≫ pdCohRes (TopCat.of B) (∅ : Set B) U (d + 1) = 0
      ∧ honestDelta (TopCat.of B) (∅ : Set B) U V hU hV hcov d
        ≫ pdCohRes (TopCat.of B) (∅ : Set B) V (d + 1) = 0 := by
  constructor
  · rw [← honestF_fst (TopCat.of B) (∅ : Set B) U V (d + 1), ← Category.assoc, honestδF,
      zero_comp]
  · rw [← honestF_snd (TopCat.of B) (∅ : Set B) U V (d + 1), ← Category.assoc, honestδF,
      zero_comp]

/-- The degree cast and its inverse compose to the identity. -/
theorem pdCast_comp_pdCast_symm (X : TopCat) (A : Set X) {k l : ℕ} (h : k = l) :
    pdCast X A h ≫ pdCast X A h.symm = 𝟙 (pdCoh X A k) := by
  simp only [pdCast, eqToHom_trans, eqToHom_refl]

/-- The degree cast composed with its inverse, on elements. -/
theorem pdCast_pdCast_symm_apply (X : TopCat) (A : Set X) {k l : ℕ} (h : k = l)
    (x : ↑(pdCoh X A k)) :
    ModuleCat.Hom.hom (pdCast X A h.symm) (ModuleCat.Hom.hom (pdCast X A h) x) = x := by
  have h1 := congrArg (fun (φ : pdCoh X A k ⟶ pdCoh X A k) => ModuleCat.Hom.hom φ x)
    (pdCast_comp_pdCast_symm X A h)
  rwa [ModuleCat.hom_comp, ModuleCat.hom_id, LinearMap.comp_apply, LinearMap.id_apply] at h1

end Work.LerayHirsch.MvAux
