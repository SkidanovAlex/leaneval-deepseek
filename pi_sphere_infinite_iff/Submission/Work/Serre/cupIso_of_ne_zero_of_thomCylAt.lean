import Mathlib
import Submission.Work.Serre.ThomCylDefs
import Submission.Work.Serre.exists_smul_oneH_rat
import Submission.Work.Serre.cohMap_oneH
import Submission.Work.StemsB.Rat.collarSuspClassAuxRat

/-!
# Any nonzero relative class is a Thom class (over a base where `ThomCylAt` holds)

`Work.Serre.ThomCylAt r N p` says that *some* class `U₀ ∈ H^{r+1}(cyl p, range (cylIncl p))` has the
cup isomorphism in the range `m + r + 1 ≤ N + 1`.  This module shows that in fact **every** nonzero
class does: the degree-`0` clause of `ThomCylAt` (available because `r ≤ N`) exhibits
`H^{r+1}(cyl p, range (cylIncl p)) ≅ ℚ` — a *line* — so every nonzero class is a nonzero multiple of
`U₀`, and the cup maps with two proportional classes are proportional.

This is the step that turns the local `ThomCylAt` statements over the pieces of a cover into the
*local bijectivity* hypotheses of the Mayer–Vietoris gluing
`Work.Serre.MVGlue.glueCupIso` for a *specific* class (see `thomCylCellStepAlt_NOTES4.md` §2).
-/

namespace Work.Serre

open CategoryTheory CategoryTheory.Limits

noncomputable section

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false

/-- Scalar multiplication commutes with a degree transport (local copy of
`Work.StemsB.Rat.relCoh_cast_smulQ` for the `RelCoh` abbreviation). -/
theorem alt_relCoh_cast_smulQ {Z : Type} [TopologicalSpace Z] (A : Set Z) {p q : ℕ} (h : p = q)
    (c : ℚ) (x : Work.Thom.RelCoh ℚ q Z A) :
    (h.symm ▸ (c • x) : Work.Thom.RelCoh ℚ p Z A) = c • (h.symm ▸ x) := by
  subst h
  rfl

/-- **Every nonzero relative class has the cup isomorphism in the range.** -/
theorem cupIso_of_ne_zero_of_thomCylAt (r N : ℕ) (hr : 1 ≤ r) (hN : r ≤ N)
    {B : Type} [TopologicalSpace B] [PathConnectedSpace B]
    {X : Type} [TopologicalSpace X] (p : C(X, B))
    (h : Work.Serre.ThomCylAt r N p)
    (U : Work.Thom.RelCoh ℚ (r + 1) (Work.Serre.cyl p) (Set.range (Work.Serre.cylIncl p)))
    (hU : U ≠ 0) (m : ℕ) (hm : m + r + 1 ≤ N + 1) :
    CategoryTheory.IsIso (ModuleCat.ofHom
      (((Work.Thom.mixedCupC ℚ (Set.range (Work.Serre.cylIncl p)) m (r + 1))).flip U ∘ₗ
        (Work.Thom.CohMap (Work.Serre.cylRetract p) ℚ m).hom)) := by
  classical
  obtain ⟨U₀, hU₀⟩ := h
  -- the cup map with `U₀` at degree `0`
  haveI h0 : CategoryTheory.IsIso (ModuleCat.ofHom
      (((Work.Thom.mixedCupC ℚ (Set.range (Work.Serre.cylIncl p)) 0 (r + 1))).flip U₀ ∘ₗ
        (Work.Thom.CohMap (Work.Serre.cylRetract p) ℚ 0).hom)) := hU₀ 0 (by omega)
  have hbij0 : Function.Bijective ((((Work.Thom.mixedCupC ℚ (Set.range (Work.Serre.cylIncl p)) 0 (r + 1))).flip U₀) ∘ₗ
      (Work.Thom.CohMap (Work.Serre.cylRetract p) ℚ 0).hom) :=
    (CategoryTheory.ConcreteCategory.isIso_iff_bijective (ModuleCat.ofHom _)).mp h0
  -- `U` and `U₀` span the same line
  obtain ⟨x, hx⟩ := hbij0.2 ((Nat.zero_add (r + 1)).symm ▸ U)
  have hx' : (((Work.Thom.mixedCupC ℚ (Set.range (Work.Serre.cylIncl p)) 0 (r + 1))).flip U₀)
      ((Work.Thom.CohMap (Work.Serre.cylRetract p) ℚ 0).hom x)
      = (Nat.zero_add (r + 1)).symm ▸ U := by
    simpa only [ModuleCat.hom_ofHom, LinearMap.comp_apply] using hx
  obtain ⟨c, hc⟩ := Work.Serre.exists_smul_oneH_rat (TopCat.of B) x
  have h1 : (Work.Thom.CohMap (Work.Serre.cylRetract p) ℚ 0).hom x
      = c • Work.Cohomology.oneH ℚ (TopCat.toSSet.obj (TopCat.of (Work.Serre.cyl p))) := by
    rw [hc]
    simp only [map_smul, Work.Serre.cohMap_oneH]
  have hunit : (((Work.Thom.mixedCupC ℚ (Set.range (Work.Serre.cylIncl p)) 0 (r + 1))).flip U₀)
      (Work.Cohomology.oneH ℚ (TopCat.toSSet.obj (TopCat.of (Work.Serre.cyl p))))
      = (Nat.zero_add (r + 1)).symm ▸ U₀ := by
    rw [show (((Work.Thom.mixedCupC ℚ (Set.range (Work.Serre.cylIncl p)) 0 (r + 1))).flip U₀)
          (Work.Cohomology.oneH ℚ (TopCat.toSSet.obj (TopCat.of (Work.Serre.cyl p))))
        = (Work.Thom.mixedCupC ℚ (Set.range (Work.Serre.cylIncl p)) 0 (r + 1))
            (Work.Cohomology.oneH ℚ (TopCat.toSSet.obj (TopCat.of (Work.Serre.cyl p)))) U₀
        from rfl]
    exact Work.StemsB.Rat.mixedCupC_oneH_zeroQ (Set.range (Work.Serre.cylIncl p)) (r + 1) U₀
  have hkey : (((Work.Thom.mixedCupC ℚ (Set.range (Work.Serre.cylIncl p)) 0 (r + 1))).flip U₀)
      ((Work.Thom.CohMap (Work.Serre.cylRetract p) ℚ 0).hom x)
      = (Nat.zero_add (r + 1)).symm ▸ (c • U₀) := by
    rw [h1, LinearMap.map_smul, hunit,
      (alt_relCoh_cast_smulQ (Set.range (Work.Serre.cylIncl p)) (Nat.zero_add (r + 1)) c U₀).symm]
  have hUc : U = c • U₀ := by
    have heq : ((Nat.zero_add (r + 1)).symm ▸ U : Work.Thom.RelCoh ℚ (0 + (r + 1))
        (Work.Serre.cyl p) (Set.range (Work.Serre.cylIncl p))) = (Nat.zero_add (r + 1)).symm ▸ (c • U₀) := by
      rw [← hx', hkey]
    have h2 := congrArg (fun z => (Nat.zero_add (r + 1)) ▸ z) heq
    simpa only [Work.StemsB.Rat.relCoh_symm_cast_castQ (X := TopCat.of (Work.Serre.cyl p))
      (Set.range (Work.Serre.cylIncl p)) (Nat.zero_add (r + 1)).symm _] using h2
  have hcne : c ≠ 0 := by
    intro hc0
    exact hU (by rw [hUc, hc0, zero_smul])
  -- proportional cup maps
  have hline : (((Work.Thom.mixedCupC ℚ (Set.range (Work.Serre.cylIncl p)) m (r + 1))).flip U)
      = c • (((Work.Thom.mixedCupC ℚ (Set.range (Work.Serre.cylIncl p)) m (r + 1))).flip U₀) := by
    rw [hUc, LinearMap.map_smul]
  have hbij : Function.Bijective ((((Work.Thom.mixedCupC ℚ (Set.range (Work.Serre.cylIncl p)) m (r + 1))).flip U₀) ∘ₗ
      (Work.Thom.CohMap (Work.Serre.cylRetract p) ℚ m).hom) :=
    (CategoryTheory.ConcreteCategory.isIso_iff_bijective (ModuleCat.ofHom _)).mp (hU₀ m hm)
  refine (CategoryTheory.ConcreteCategory.isIso_iff_bijective (ModuleCat.ofHom _)).mpr ?_
  rw [hline, LinearMap.smul_comp]
  simp only [ModuleCat.hom_ofHom]
  refine ⟨fun x y hxy => ?_, fun y => ?_⟩
  · rw [LinearMap.smul_apply, LinearMap.smul_apply] at hxy
    have h2 := congrArg (fun z => c⁻¹ • z) hxy
    simp only [smul_smul, inv_mul_cancel₀ hcne, one_smul] at h2
    exact hbij.1 h2
  · obtain ⟨x, hx⟩ := hbij.2 (c⁻¹ • y)
    refine ⟨x, ?_⟩
    rw [LinearMap.smul_apply, hx]
    simp only [smul_smul, mul_inv_cancel₀ hcne, one_smul]

end

end Work.Serre
