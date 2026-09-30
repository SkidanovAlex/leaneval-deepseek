import Mathlib

set_option synthInstance.maxHeartbeats 400000

/-!
# Coning a homeomorphism of the sphere to the ball

Every homeomorphism `δ` of the unit sphere `S^{n-1} ⊆ ℝⁿ` extends to a homeomorphism of the
closed unit ball `Dⁿ` by "coning":
`y ↦ ‖y‖ • δ(y/‖y‖)` for `y ≠ 0`, and `0 ↦ 0`. This extension preserves the norm.
-/

namespace Work.Morse

open Metric
open scoped Topology

variable {n : ℕ}

/-- The point `y/‖y‖ = ‖y‖⁻¹ • y` of the unit sphere, for `y ≠ 0`. -/
noncomputable def sphPt (y : EuclideanSpace ℝ (Fin n)) (hy : y ≠ 0) :
    Metric.sphere (0 : EuclideanSpace ℝ (Fin n)) 1 :=
  ⟨(‖y‖)⁻¹ • y, by
    rw [Metric.mem_sphere, dist_eq_norm, sub_zero, norm_smul, Real.norm_eq_abs,
      abs_of_nonneg (inv_nonneg.mpr (norm_nonneg y)), inv_mul_cancel₀ (norm_ne_zero_iff.mpr hy)]⟩

@[simp] lemma sphPt_coe (y : EuclideanSpace ℝ (Fin n)) (hy : y ≠ 0) :
    ((sphPt y hy : Metric.sphere (0 : EuclideanSpace ℝ (Fin n)) 1) :
      EuclideanSpace ℝ (Fin n)) = (‖y‖)⁻¹ • y := rfl

/-- The coning of a self-homeomorphism `δ` of the sphere to the ambient space: it is
`y ↦ ‖y‖ • δ(y/‖y‖)` away from the origin, and `0` at the origin. -/
noncomputable def coneMap
    (δ : Metric.sphere (0 : EuclideanSpace ℝ (Fin n)) 1 ≃ₜ
         Metric.sphere (0 : EuclideanSpace ℝ (Fin n)) 1)
    (y : EuclideanSpace ℝ (Fin n)) : EuclideanSpace ℝ (Fin n) :=
  if hy : y = 0 then 0 else ‖y‖ • ((δ (sphPt y hy)) : EuclideanSpace ℝ (Fin n))

@[simp] lemma coneMap_zero
    (δ : Metric.sphere (0 : EuclideanSpace ℝ (Fin n)) 1 ≃ₜ
         Metric.sphere (0 : EuclideanSpace ℝ (Fin n)) 1) : coneMap δ 0 = 0 := by
  rw [coneMap, dif_pos rfl]

lemma norm_coneMap
    (δ : Metric.sphere (0 : EuclideanSpace ℝ (Fin n)) 1 ≃ₜ
         Metric.sphere (0 : EuclideanSpace ℝ (Fin n)) 1)
    (y : EuclideanSpace ℝ (Fin n)) : ‖coneMap δ y‖ = ‖y‖ := by
  rw [coneMap]
  split_ifs with hy
  · rw [norm_zero, hy, norm_zero]
  · rw [norm_smul, mem_sphere_zero_iff_norm.mp (δ (sphPt y hy)).2, mul_one, norm_norm]

lemma coneMap_ne_zero
    (δ : Metric.sphere (0 : EuclideanSpace ℝ (Fin n)) 1 ≃ₜ
         Metric.sphere (0 : EuclideanSpace ℝ (Fin n)) 1)
    {y : EuclideanSpace ℝ (Fin n)} (hy : y ≠ 0) : coneMap δ y ≠ 0 := by
  intro h
  have h1 := norm_coneMap δ y
  rw [h, norm_zero] at h1
  exact hy (norm_eq_zero.mp h1.symm)

/-- The sphere point of a nonzero vector, as a continuous function of the vector, using the
polar-coordinate homeomorphism `homeomorphUnitSphereProd`. -/
noncomputable def sphProj (y : ({0}ᶜ : Set (EuclideanSpace ℝ (Fin n)))) :
    Metric.sphere (0 : EuclideanSpace ℝ (Fin n)) 1 :=
  (homeomorphUnitSphereProd (EuclideanSpace ℝ (Fin n)) y).1

lemma continuous_sphProj : Continuous (sphProj (n := n)) :=
  (homeomorphUnitSphereProd (EuclideanSpace ℝ (Fin n))).continuous.fst

lemma sphProj_coe (y : ({0}ᶜ : Set (EuclideanSpace ℝ (Fin n)))) :
    (sphProj y : EuclideanSpace ℝ (Fin n)) =
      (‖(y : EuclideanSpace ℝ (Fin n))‖)⁻¹ • (y : EuclideanSpace ℝ (Fin n)) :=
  homeomorphUnitSphereProd_apply_fst_coe _ y

noncomputable def coneMapP
    (δ : Metric.sphere (0 : EuclideanSpace ℝ (Fin n)) 1 ≃ₜ
         Metric.sphere (0 : EuclideanSpace ℝ (Fin n)) 1) :
    ({0}ᶜ : Set (EuclideanSpace ℝ (Fin n))) → ({0}ᶜ : Set (EuclideanSpace ℝ (Fin n))) :=
  fun y => ⟨coneMap δ (y : EuclideanSpace ℝ (Fin n)),
    coneMap_ne_zero δ (Set.mem_compl_singleton_iff.mp y.2)⟩

lemma continuous_coneMapP
    (δ : Metric.sphere (0 : EuclideanSpace ℝ (Fin n)) 1 ≃ₜ
         Metric.sphere (0 : EuclideanSpace ℝ (Fin n)) 1) :
    Continuous (coneMapP δ) := by
  let f : ({0}ᶜ : Set (EuclideanSpace ℝ (Fin n))) → EuclideanSpace ℝ (Fin n) :=
    fun y => ‖(y : EuclideanSpace ℝ (Fin n))‖ •
      ((δ (sphProj y)) : EuclideanSpace ℝ (Fin n))
  have hfcont : Continuous f :=
    (continuous_norm.comp continuous_subtype_val).smul
      (continuous_subtype_val.comp (δ.continuous.comp continuous_sphProj))
  have hfmem : ∀ y, f y ∈ ({0}ᶜ : Set (EuclideanSpace ℝ (Fin n))) := by
    intro y
    have hy : (y : EuclideanSpace ℝ (Fin n)) ≠ 0 := Set.mem_compl_singleton_iff.mp y.2
    intro h
    have h1 : ‖f y‖ = ‖(y : EuclideanSpace ℝ (Fin n))‖ := by
      change ‖‖(y : EuclideanSpace ℝ (Fin n))‖ •
        ((δ (sphProj y)) : EuclideanSpace ℝ (Fin n))‖ = _
      rw [norm_smul, mem_sphere_zero_iff_norm.mp (δ (sphProj y)).2, mul_one, norm_norm]
    rw [h, norm_zero] at h1
    exact hy (norm_eq_zero.mp h1.symm)
  have hfun : coneMapP δ = fun y => ⟨f y, hfmem y⟩ := by
    funext y
    apply Subtype.ext
    have hne : (y : EuclideanSpace ℝ (Fin n)) ≠ 0 := Set.mem_compl_singleton_iff.mp y.2
    change coneMap δ (y : EuclideanSpace ℝ (Fin n)) = f y
    rw [show coneMap δ (y : EuclideanSpace ℝ (Fin n)) =
        ‖(y : EuclideanSpace ℝ (Fin n))‖ •
          ((δ (sphPt (y : EuclideanSpace ℝ (Fin n)) hne)) : EuclideanSpace ℝ (Fin n)) by
        rw [coneMap, dif_neg hne],
      show sphPt (y : EuclideanSpace ℝ (Fin n)) hne = sphProj y from
        Subtype.ext (by rw [sphPt_coe, sphProj_coe])]
  rw [hfun]
  exact Continuous.subtype_mk hfcont hfmem

lemma continuous_coneMap
    (δ : Metric.sphere (0 : EuclideanSpace ℝ (Fin n)) 1 ≃ₜ
         Metric.sphere (0 : EuclideanSpace ℝ (Fin n)) 1) : Continuous (coneMap δ) := by
  have hOn : ContinuousOn (coneMap δ) ({0}ᶜ : Set (EuclideanSpace ℝ (Fin n))) := by
    rw [continuousOn_iff_continuous_domRestrict]
    change Continuous (fun y : ({0}ᶜ : Set (EuclideanSpace ℝ (Fin n))) =>
      (coneMapP δ y : EuclideanSpace ℝ (Fin n)))
    exact continuous_subtype_val.comp (continuous_coneMapP δ)
  rw [continuous_iff_continuousAt]
  intro y
  by_cases hy : y = 0
  · subst hy
    rw [ContinuousAt, coneMap_zero, tendsto_zero_iff_norm_tendsto_zero]
    have hfun : (fun z : EuclideanSpace ℝ (Fin n) => ‖coneMap δ z‖) =
        fun z : EuclideanSpace ℝ (Fin n) => ‖z‖ := funext (norm_coneMap δ)
    rw [hfun]
    simpa using (continuous_norm.continuousAt (x := (0 : EuclideanSpace ℝ (Fin n)))).tendsto
  · exact hOn.continuousAt (IsOpen.mem_nhds isOpen_compl_singleton
      (Set.mem_compl_singleton_iff.mpr hy))

lemma coneMap_injective
    (δ : Metric.sphere (0 : EuclideanSpace ℝ (Fin n)) 1 ≃ₜ
         Metric.sphere (0 : EuclideanSpace ℝ (Fin n)) 1) :
    Function.Injective (coneMap δ) := by
  intro y z h
  have hnorm : ‖y‖ = ‖z‖ := by rw [← norm_coneMap δ y, h, norm_coneMap δ z]
  by_cases hy : y = 0
  · have hz : z = 0 := by
      have h1 : ‖z‖ = 0 := by rw [← hnorm, hy, norm_zero]
      exact norm_eq_zero.mp h1
    rw [hy, hz]
  · have hz : z ≠ 0 := by
      intro hz0
      have h1 : ‖y‖ = 0 := by rw [hnorm, hz0, norm_zero]
      exact hy (norm_eq_zero.mp h1)
    have hr : ‖y‖ ≠ 0 := norm_ne_zero_iff.mpr hy
    have h' : ‖y‖ • ((δ (sphPt y hy)) : EuclideanSpace ℝ (Fin n)) =
        ‖z‖ • ((δ (sphPt z hz)) : EuclideanSpace ℝ (Fin n)) := by
      simpa only [coneMap, dif_neg hy, dif_neg hz] using h
    rw [← hnorm] at h'
    have h2 : (δ (sphPt y hy) : EuclideanSpace ℝ (Fin n)) =
        (δ (sphPt z hz) : EuclideanSpace ℝ (Fin n)) := by
      have h3 := congrArg (fun v : EuclideanSpace ℝ (Fin n) => (‖y‖)⁻¹ • v) h'
      simpa [smul_smul, inv_mul_cancel₀ hr, one_smul] using h3
    have h4 : sphPt y hy = sphPt z hz := δ.injective (Subtype.ext h2)
    have h5 : (‖y‖)⁻¹ • y = (‖z‖)⁻¹ • z := by
      have h6 := congrArg (fun w : Metric.sphere (0 : EuclideanSpace ℝ (Fin n)) 1 =>
        (w : EuclideanSpace ℝ (Fin n))) h4
      simpa only [sphPt_coe] using h6
    calc y = ‖y‖ • ((‖y‖)⁻¹ • y) := by rw [smul_smul, mul_inv_cancel₀ hr, one_smul]
      _ = ‖y‖ • ((‖z‖)⁻¹ • z) := by rw [h5]
      _ = z := by rw [smul_smul, ← hnorm, mul_inv_cancel₀ hr, one_smul]

lemma coneMap_surjective
    (δ : Metric.sphere (0 : EuclideanSpace ℝ (Fin n)) 1 ≃ₜ
         Metric.sphere (0 : EuclideanSpace ℝ (Fin n)) 1) :
    Function.Surjective (coneMap δ) := by
  intro w
  by_cases hw : w = 0
  · exact ⟨0, by rw [coneMap_zero, hw]⟩
  · have hr : 0 < ‖w‖ := norm_pos_iff.mpr hw
    obtain ⟨v, hv⟩ := δ.surjective (sphPt w hw)
    refine ⟨‖w‖ • (v : EuclideanSpace ℝ (Fin n)), ?_⟩
    have hy : ‖w‖ • (v : EuclideanSpace ℝ (Fin n)) ≠ 0 := by
      intro h0
      have h1 : ‖‖w‖ • (v : EuclideanSpace ℝ (Fin n))‖ = 0 := by rw [h0, norm_zero]
      rw [norm_smul, mem_sphere_zero_iff_norm.mp v.2, mul_one, norm_norm] at h1
      exact hr.ne' h1
    rw [coneMap, dif_neg hy]
    have hnorm : ‖‖w‖ • (v : EuclideanSpace ℝ (Fin n))‖ = ‖w‖ := by
      rw [norm_smul, mem_sphere_zero_iff_norm.mp v.2, mul_one, norm_norm]
    have hsp : sphPt (‖w‖ • (v : EuclideanSpace ℝ (Fin n))) hy = v := by
      apply Subtype.ext
      rw [sphPt_coe, hnorm, smul_smul, inv_mul_cancel₀ hr.ne', one_smul]
    rw [hnorm, hsp, hv, sphPt_coe, smul_smul, mul_inv_cancel₀ hr.ne', one_smul]

lemma coneMap_mem_closedBall
    (δ : Metric.sphere (0 : EuclideanSpace ℝ (Fin n)) 1 ≃ₜ
         Metric.sphere (0 : EuclideanSpace ℝ (Fin n)) 1)
    {y : EuclideanSpace ℝ (Fin n)} (hy : y ∈ Metric.closedBall (0 : EuclideanSpace ℝ (Fin n)) 1) :
    coneMap δ y ∈ Metric.closedBall (0 : EuclideanSpace ℝ (Fin n)) 1 := by
  have h := mem_closedBall.mp hy
  rw [dist_zero_right] at h
  rw [mem_closedBall, dist_zero_right, norm_coneMap]
  exact h

/-- The coning map, as a self-map of the closed unit ball. -/
noncomputable def ballMap
    (δ : Metric.sphere (0 : EuclideanSpace ℝ (Fin n)) 1 ≃ₜ
         Metric.sphere (0 : EuclideanSpace ℝ (Fin n)) 1) :
    Metric.closedBall (0 : EuclideanSpace ℝ (Fin n)) 1 →
    Metric.closedBall (0 : EuclideanSpace ℝ (Fin n)) 1 :=
  fun y => ⟨coneMap δ (y : EuclideanSpace ℝ (Fin n)), coneMap_mem_closedBall δ y.2⟩

lemma continuous_ballMap
    (δ : Metric.sphere (0 : EuclideanSpace ℝ (Fin n)) 1 ≃ₜ
         Metric.sphere (0 : EuclideanSpace ℝ (Fin n)) 1) : Continuous (ballMap δ) :=
  Continuous.subtype_mk ((continuous_coneMap δ).comp continuous_subtype_val)
    (fun y => coneMap_mem_closedBall δ y.2)

lemma ballMap_injective
    (δ : Metric.sphere (0 : EuclideanSpace ℝ (Fin n)) 1 ≃ₜ
         Metric.sphere (0 : EuclideanSpace ℝ (Fin n)) 1) :
    Function.Injective (ballMap δ) := by
  intro y z h
  apply Subtype.ext
  exact coneMap_injective δ (by simpa only [ballMap] using Subtype.ext_iff.mp h)

lemma ballMap_surjective
    (δ : Metric.sphere (0 : EuclideanSpace ℝ (Fin n)) 1 ≃ₜ
         Metric.sphere (0 : EuclideanSpace ℝ (Fin n)) 1) :
    Function.Surjective (ballMap δ) := by
  intro w
  obtain ⟨y, hy⟩ := coneMap_surjective δ (w : EuclideanSpace ℝ (Fin n))
  have hyD : y ∈ Metric.closedBall (0 : EuclideanSpace ℝ (Fin n)) 1 := by
    have hw : ‖(w : EuclideanSpace ℝ (Fin n))‖ ≤ 1 := by
      have h := mem_closedBall.mp w.2
      rwa [dist_zero_right] at h
    rw [mem_closedBall, dist_zero_right, ← norm_coneMap δ y, hy]
    exact hw
  exact ⟨⟨y, hyD⟩, by apply Subtype.ext; simpa only [ballMap] using hy⟩

/-- Every homeomorphism of the unit sphere `S^{n-1} ⊆ ℝⁿ` extends to a homeomorphism of the
closed unit ball `Dⁿ`, by "coning": `y ↦ ‖y‖ • δ(y/‖y‖)`.  We also record that the extension
preserves the norm. -/
theorem coning_extension {n : ℕ}
    (δ : Metric.sphere (0 : EuclideanSpace ℝ (Fin n)) 1 ≃ₜ
         Metric.sphere (0 : EuclideanSpace ℝ (Fin n)) 1) :
    ∃ C : Metric.closedBall (0 : EuclideanSpace ℝ (Fin n)) 1 ≃ₜ
          Metric.closedBall (0 : EuclideanSpace ℝ (Fin n)) 1,
      (∀ u : Metric.sphere (0 : EuclideanSpace ℝ (Fin n)) 1,
        (C ⟨(u : EuclideanSpace ℝ (Fin n)),
            Metric.sphere_subset_closedBall u.2⟩ : EuclideanSpace ℝ (Fin n))
          = (δ u : EuclideanSpace ℝ (Fin n))) ∧
      (∀ y : Metric.closedBall (0 : EuclideanSpace ℝ (Fin n)) 1,
        ‖(C y : EuclideanSpace ℝ (Fin n))‖ = ‖(y : EuclideanSpace ℝ (Fin n))‖) := by
  have hiso : IsHomeomorph (ballMap δ) :=
    isHomeomorph_iff_continuous_bijective.mpr
      ⟨continuous_ballMap δ, ballMap_injective δ, ballMap_surjective δ⟩
  refine ⟨IsHomeomorph.homeomorph (ballMap δ) hiso, ?_, ?_⟩
  · intro u
    rw [IsHomeomorph.homeomorph_apply]
    have hu : (u : EuclideanSpace ℝ (Fin n)) ≠ 0 := by
      intro h
      have h1 := mem_sphere_zero_iff_norm.mp u.2
      rw [h, norm_zero] at h1
      norm_num at h1
    change coneMap δ (u : EuclideanSpace ℝ (Fin n)) = (δ u : EuclideanSpace ℝ (Fin n))
    rw [show coneMap δ (u : EuclideanSpace ℝ (Fin n)) =
          ‖(u : EuclideanSpace ℝ (Fin n))‖ •
            ((δ (sphPt (u : EuclideanSpace ℝ (Fin n)) hu)) : EuclideanSpace ℝ (Fin n)) by
        rw [coneMap, dif_neg hu],
      show sphPt (u : EuclideanSpace ℝ (Fin n)) hu = u from Subtype.ext (by
        rw [sphPt_coe, mem_sphere_zero_iff_norm.mp u.2, inv_one, one_smul]),
      mem_sphere_zero_iff_norm.mp u.2, one_smul]
  · intro y
    rw [IsHomeomorph.homeomorph_apply]
    change ‖coneMap δ (y : EuclideanSpace ℝ (Fin n))‖ = ‖(y : EuclideanSpace ℝ (Fin n))‖
    exact norm_coneMap δ (y : EuclideanSpace ℝ (Fin n))

end Work.Morse
