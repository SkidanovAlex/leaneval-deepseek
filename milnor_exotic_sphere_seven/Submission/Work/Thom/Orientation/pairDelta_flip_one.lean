import Mathlib
import Submission.Work.Thom.Orientation.Reflection
import Submission.Work.Cohomology.SphZeroBase
import Submission.Work.Thom.disjointCoverA
import Submission.Work.Thom.Orientation.ReflSections

-- Lean v4.35.0-rc3: restore v4.34 instance-unification transparency (port).
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
set_option synthInstance.maxHeartbeats 400000

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option linter.unusedSimpArgs false

/-!
# The connecting homomorphism of `(Y × ℝ¹, Y × S⁰)` kills `u + f^*u`

For the rank-one sphere bundle `Sph Y 1 = Y × S⁰ ⊆ Y × ℝ¹` of the trivial line bundle over a space
`Y`, the reflection `f = fibSph = id × (-1)` is a self-homeomorphism of the pair
`(Y × ℝ¹, Y × S⁰)`; its induced map on `H⁰(Sph Y 1)` is the involution `f^*` exchanging the two
components of every fibre.

**`Work.Thom.Orientation.pairDelta_flip_one`** states that the connecting homomorphism

  `δ = pairδC (Sph Y 1) 0 : H⁰(Sph Y 1) → H¹(Y × ℝ¹, Sph Y 1)`

kills `u + f^*u`, for every `u ∈ H⁰(Sph Y 1)`.  This is the rank-one case of the statement that
the reflection acts on `H¹(Y × ℝ¹, Y × S⁰) = (suspension) H⁰(Y)` by `-1`.

The proof does not compute `H¹` of the pair.  Instead:

* `u + f^*u = foldPos^* u + foldNeg^* u`, where `foldPos`, `foldNeg : Sph Y 1 → Sph Y 1` are the
  two "fold" maps collapsing the fibres onto their positive resp. negative point.  The identity
  follows from the fact that the two constant sections `sigPos`, `sigNeg` of the fibre
  (`y ↦ (y,±1)`) jointly detect `H⁰(Sph Y 1)`:
  `Work.Thom.Orientation.eq_zero_of_sigPos_sigNeg_eq_zero`;
* each of `foldPos^* u`, `foldNeg^* u` is the restriction of a class of `H⁰(Y × ℝ¹)`
  (`f = sigPos ∘ proj ∘ incl`), and the composite `restriction ≫ δ` is zero.

The accompanying file `Submission/Work/Thom/Orientation/ReflSections.lean` contains the two points
of `S⁰`, the two sections, the projection, the reflection and the two halves `Upos`, `Uneg`.
-/

namespace Work.Thom.Orientation

open Work.Thom
open CategoryTheory

noncomputable section

variable {Y : Type} [TopologicalSpace Y]

/-! ## The pullback along a composite -/

/-- The value of the pullback of a class along a composite `g ∘ f`. -/
theorem CohMap_comp_apply_gen {A B Cc : Type} [TopologicalSpace A] [TopologicalSpace B]
    [TopologicalSpace Cc] (f : C(A, B)) (g : C(B, Cc)) (u : Coh ℤ 0 Cc) :
    (CohMap (g.comp f) ℤ 0).hom u = (CohMap f ℤ 0).hom ((CohMap g ℤ 0).hom u) := by
  have h := CohMap_comp (f) (g) ℤ 0
  have h2 := congrArg (fun (k : Coh ℤ 0 Cc ⟶ Coh ℤ 0 A) => k.hom u) h
  simpa only [ModuleCat.hom_comp, LinearMap.comp_apply] using h2

/-! ## The two sections detect `H⁰` -/

/-- **The two constant sections of the rank-one sphere bundle jointly detect `H⁰`**: a class of
`H⁰(Sph Y 1)` whose pullbacks along both `y ↦ (y,±1)` vanish is zero.

The two halves `Upos`, `Uneg` of `Sph Y 1` form a disjoint open cover, and each section is a
homeomorphism onto its half, so the hypotheses say that the class restricts to zero on both open
sets of the cover; `Work.Thom.disjointCoverA` then gives the conclusion. -/
theorem eq_zero_of_sigPos_sigNeg_eq_zero
    (α : Coh ℤ 0 (↥(Sph Y 1)))
    (hP : (CohMap (sigPos (Y := Y)) ℤ 0).hom α = 0)
    (hN : (CohMap (sigNeg (Y := Y)) ℤ 0).hom α = 0) : α = 0 := by
  have hU0 : (CohMap (Work.Thom.subtypeMap (Upos (Y := Y))) ℤ 0).hom α = 0 := by
    have hcomp : CohMap (sigPos (Y := Y)) ℤ 0
        = CohMap (Work.Thom.subtypeMap (Upos (Y := Y))) ℤ 0
          ≫ CohMap (sigPosU (Y := Y)) ℤ 0 := by
      have h := CohMap_comp (sigPosU (Y := Y)) (Work.Thom.subtypeMap (Upos (Y := Y))) ℤ 0
      rwa [← sigPos_eq_subtypeMap_comp_sigPosU] at h
    have hsplit : CohMap (sigPosU (Y := Y)) ℤ 0 ≫ CohMap (sigPosUinv (Y := Y)) ℤ 0
        = 𝟙 (Coh ℤ 0 (↥(Upos (Y := Y)))) := by
      have h := CohMap_comp (sigPosUinv (Y := Y)) (sigPosU (Y := Y)) ℤ 0
      rw [sigPosU_comp_sigPosUinv, CohMap_id] at h
      exact h.symm
    have h1 : (CohMap (sigPosU (Y := Y)) ℤ 0).hom
        ((CohMap (Work.Thom.subtypeMap (Upos (Y := Y))) ℤ 0).hom α) = 0 := by
      have h := hP
      rw [hcomp] at h
      simpa only [ModuleCat.hom_comp, LinearMap.comp_apply] using h
    have h2 : (CohMap (sigPosUinv (Y := Y)) ℤ 0).hom
        ((CohMap (sigPosU (Y := Y)) ℤ 0).hom
          ((CohMap (Work.Thom.subtypeMap (Upos (Y := Y))) ℤ 0).hom α)) = 0 := by
      rw [h1, map_zero]
    have h3 := congrArg (fun (g : Coh ℤ 0 (↥(Upos (Y := Y))) ⟶ Coh ℤ 0 (↥(Upos (Y := Y)))) =>
      g.hom ((CohMap (Work.Thom.subtypeMap (Upos (Y := Y))) ℤ 0).hom α)) hsplit
    simp only [ModuleCat.hom_comp, LinearMap.comp_apply, ModuleCat.hom_id, LinearMap.id_apply]
      at h3
    rw [← h3]
    exact h2
  have hV0 : (CohMap (Work.Thom.subtypeMap (Uneg (Y := Y))) ℤ 0).hom α = 0 := by
    have hcomp : CohMap (sigNeg (Y := Y)) ℤ 0
        = CohMap (Work.Thom.subtypeMap (Uneg (Y := Y))) ℤ 0
          ≫ CohMap (sigNegU (Y := Y)) ℤ 0 := by
      have h := CohMap_comp (sigNegU (Y := Y)) (Work.Thom.subtypeMap (Uneg (Y := Y))) ℤ 0
      rwa [← sigNeg_eq_subtypeMap_comp_sigNegU] at h
    have hsplit : CohMap (sigNegU (Y := Y)) ℤ 0 ≫ CohMap (sigNegUinv (Y := Y)) ℤ 0
        = 𝟙 (Coh ℤ 0 (↥(Uneg (Y := Y)))) := by
      have h := CohMap_comp (sigNegUinv (Y := Y)) (sigNegU (Y := Y)) ℤ 0
      rw [sigNegU_comp_sigNegUinv, CohMap_id] at h
      exact h.symm
    have h1 : (CohMap (sigNegU (Y := Y)) ℤ 0).hom
        ((CohMap (Work.Thom.subtypeMap (Uneg (Y := Y))) ℤ 0).hom α) = 0 := by
      have h := hN
      rw [hcomp] at h
      simpa only [ModuleCat.hom_comp, LinearMap.comp_apply] using h
    have h2 : (CohMap (sigNegUinv (Y := Y)) ℤ 0).hom
        ((CohMap (sigNegU (Y := Y)) ℤ 0).hom
          ((CohMap (Work.Thom.subtypeMap (Uneg (Y := Y))) ℤ 0).hom α)) = 0 := by
      rw [h1, map_zero]
    have h3 := congrArg (fun (g : Coh ℤ 0 (↥(Uneg (Y := Y))) ⟶ Coh ℤ 0 (↥(Uneg (Y := Y)))) =>
      g.hom ((CohMap (Work.Thom.subtypeMap (Uneg (Y := Y))) ℤ 0).hom α)) hsplit
    simp only [ModuleCat.hom_comp, LinearMap.comp_apply, ModuleCat.hom_id, LinearMap.id_apply]
      at h3
    rw [← h3]
    exact h2
  exact disjointCoverA (X := TopCat.of ↥(Sph Y 1)) (Upos (Y := Y)) (Uneg (Y := Y))
    isOpen_Upos isOpen_Uneg disjoint_Upos_Uneg union_Upos_Uneg 0 α hU0 hV0

/-! ## The pullbacks of the six maps involved -/

theorem CohMap_sigPos_fibSph (u : Coh ℤ 0 (↥(Sph Y 1))) :
    (CohMap (sigPos (Y := Y)) ℤ 0).hom ((CohMap (fibSph (Y := Y)) ℤ 0).hom u)
      = (CohMap (sigNeg (Y := Y)) ℤ 0).hom u := by
  rw [← CohMap_comp_apply_gen (sigPos (Y := Y)) (fibSph (Y := Y)) u, fibSph_comp_sigPos]

theorem CohMap_sigPos_foldPos (u : Coh ℤ 0 (↥(Sph Y 1))) :
    (CohMap (sigPos (Y := Y)) ℤ 0).hom ((CohMap (foldPos (Y := Y)) ℤ 0).hom u)
      = (CohMap (sigPos (Y := Y)) ℤ 0).hom u := by
  rw [← CohMap_comp_apply_gen (sigPos (Y := Y)) (foldPos (Y := Y)) u, foldPos_comp_sigPos]

theorem CohMap_sigPos_foldNeg (u : Coh ℤ 0 (↥(Sph Y 1))) :
    (CohMap (sigPos (Y := Y)) ℤ 0).hom ((CohMap (foldNeg (Y := Y)) ℤ 0).hom u)
      = (CohMap (sigNeg (Y := Y)) ℤ 0).hom u := by
  rw [← CohMap_comp_apply_gen (sigPos (Y := Y)) (foldNeg (Y := Y)) u, foldNeg_comp_sigPos]

theorem CohMap_sigNeg_fibSph (u : Coh ℤ 0 (↥(Sph Y 1))) :
    (CohMap (sigNeg (Y := Y)) ℤ 0).hom ((CohMap (fibSph (Y := Y)) ℤ 0).hom u)
      = (CohMap (sigPos (Y := Y)) ℤ 0).hom u := by
  rw [← CohMap_comp_apply_gen (sigNeg (Y := Y)) (fibSph (Y := Y)) u, fibSph_comp_sigNeg]

theorem CohMap_sigNeg_foldPos (u : Coh ℤ 0 (↥(Sph Y 1))) :
    (CohMap (sigNeg (Y := Y)) ℤ 0).hom ((CohMap (foldPos (Y := Y)) ℤ 0).hom u)
      = (CohMap (sigPos (Y := Y)) ℤ 0).hom u := by
  rw [← CohMap_comp_apply_gen (sigNeg (Y := Y)) (foldPos (Y := Y)) u, foldPos_comp_sigNeg]

theorem CohMap_sigNeg_foldNeg (u : Coh ℤ 0 (↥(Sph Y 1))) :
    (CohMap (sigNeg (Y := Y)) ℤ 0).hom ((CohMap (foldNeg (Y := Y)) ℤ 0).hom u)
      = (CohMap (sigNeg (Y := Y)) ℤ 0).hom u := by
  rw [← CohMap_comp_apply_gen (sigNeg (Y := Y)) (foldNeg (Y := Y)) u, foldNeg_comp_sigNeg]

/-! ## `u + f^*u` is a sum of two restrictions -/

/-- **The reflected sum is the sum of the two folded classes.** -/
theorem fibSph_add_eq_fold (u : Coh ℤ 0 (↥(Sph Y 1))) :
    (CohMap (fibSph (Y := Y)) ℤ 0).hom u + u
      = (CohMap (foldPos (Y := Y)) ℤ 0).hom u + (CohMap (foldNeg (Y := Y)) ℤ 0).hom u := by
  have hz : (CohMap (fibSph (Y := Y)) ℤ 0).hom u + u
      - ((CohMap (foldPos (Y := Y)) ℤ 0).hom u + (CohMap (foldNeg (Y := Y)) ℤ 0).hom u)
      = 0 := by
    apply eq_zero_of_sigPos_sigNeg_eq_zero
    · simp only [map_sub, map_add]
      rw [CohMap_sigPos_fibSph, CohMap_sigPos_foldPos, CohMap_sigPos_foldNeg]
      abel
    · simp only [map_sub, map_add]
      rw [CohMap_sigNeg_fibSph, CohMap_sigNeg_foldPos, CohMap_sigNeg_foldNeg]
      abel
  exact sub_eq_zero.mp hz

/-! ## The connecting homomorphism kills each folded class -/

/-- The connecting homomorphism kills the restriction of a class of `H⁰(Y × ℝ¹)`. -/
theorem pairδC_apply_restrCoh (w : Coh ℤ 0 (Y × EuclideanSpace ℝ (Fin 1))) :
    (pairδC (Sph Y 1) 0).hom ((restrCoh (Sph Y 1) ℤ 0).hom w) = 0 := by
  have h := congrArg ModuleCat.Hom.hom (restrCoh_comp_pairδC (Sph Y 1) 0)
  simp only [ModuleCat.hom_comp, ModuleCat.hom_zero] at h
  exact LinearMap.congr_fun h w

/-- `CohMap foldPos`, expanded through the composite `sigPos ∘ proj ∘ incl`. -/
theorem CohMap_foldPos :
    CohMap (foldPos (Y := Y)) ℤ 0
      = CohMap (sigPos (Y := Y)) ℤ 0
        ≫ (CohMap (sphProj (Y := Y)) ℤ 0 ≫ CohMap (sphIncl (Y := Y)) ℤ 0) := by
  have h := CohMap_comp ((sphProj (Y := Y)).comp (sphIncl (Y := Y))) (sigPos (Y := Y)) ℤ 0
  rw [show (sigPos (Y := Y)).comp ((sphProj (Y := Y)).comp (sphIncl (Y := Y)))
      = foldPos (Y := Y) from rfl] at h
  rw [h]
  rw [CohMap_comp (sphIncl (Y := Y)) (sphProj (Y := Y)) ℤ 0]

/-- `CohMap foldNeg`, expanded through the composite `sigNeg ∘ proj ∘ incl`. -/
theorem CohMap_foldNeg :
    CohMap (foldNeg (Y := Y)) ℤ 0
      = CohMap (sigNeg (Y := Y)) ℤ 0
        ≫ (CohMap (sphProj (Y := Y)) ℤ 0 ≫ CohMap (sphIncl (Y := Y)) ℤ 0) := by
  have h := CohMap_comp ((sphProj (Y := Y)).comp (sphIncl (Y := Y))) (sigNeg (Y := Y)) ℤ 0
  rw [show (sigNeg (Y := Y)).comp ((sphProj (Y := Y)).comp (sphIncl (Y := Y)))
      = foldNeg (Y := Y) from rfl] at h
  rw [h]
  rw [CohMap_comp (sphIncl (Y := Y)) (sphProj (Y := Y)) ℤ 0]

theorem pairδC_foldPos (u : Coh ℤ 0 (↥(Sph Y 1))) :
    (pairδC (Sph Y 1) 0).hom ((CohMap (foldPos (Y := Y)) ℤ 0).hom u) = 0 := by
  rw [CohMap_foldPos]
  simp only [ModuleCat.hom_comp, LinearMap.comp_apply]
  exact pairδC_apply_restrCoh _

theorem pairδC_foldNeg (u : Coh ℤ 0 (↥(Sph Y 1))) :
    (pairδC (Sph Y 1) 0).hom ((CohMap (foldNeg (Y := Y)) ℤ 0).hom u) = 0 := by
  rw [CohMap_foldNeg]
  simp only [ModuleCat.hom_comp, LinearMap.comp_apply]
  exact pairδC_apply_restrCoh _

/-! ## The theorem -/

theorem pairDelta_flip_one {Y : Type} [TopologicalSpace Y] (u : Work.Thom.Coh ℤ 0 (↥(Work.Thom.Sph Y 1))) :
    (Work.Thom.pairδC (Work.Thom.Sph Y 1) 0).hom
      (((Work.Thom.CohMap (Work.Thom.restrictMap (fibRefl 1 Y) (Work.Thom.Sph Y 1)
          (Work.Thom.Sph Y 1) (fibRefl_mem_sph 1 Y)) ℤ 0).hom u) + u) = 0 := by
  change (pairδC (Sph Y 1) 0).hom ((CohMap (fibSph (Y := Y)) ℤ 0).hom u + u) = 0
  rw [fibSph_add_eq_fold, map_add, pairδC_foldPos, pairδC_foldNeg, add_zero]

end

end Work.Thom.Orientation
