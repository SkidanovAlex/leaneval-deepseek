import Submission.Work.OddRadon.Core

/-!
# The spherical Radon transform — the one-variable reduction (`Work.OddRadon`, part 2)

For a rotation-invariant integrand `g w = γ (w 0)` the spherical Radon transform at a unit
vector `ξ` depends only on `|ξ 0|` (`= |sin α|` for the paper's `ξ(α)`) and equals the explicit
one-variable integral `radonProfile d γ (cos α)` with the Abel-type kernel
`(1 - s ^ 2) ^ (d/2 - 2)`.

## Main results

* `sphereArea_sub_three`
* `sphericalRadon_rotationInvariant`
* `sphericalRadon_rotationInvariant_factor`
* `radonProfile_neg`, `radonProfile_odd`

(The companion results `radonXi_norm`, `radonXi_zero_coord`, `sphericalRadon_radonXi` — the same
reduction written in the paper's angular parametrisation `ξ(α) = (sin α, 0, …, 0, -cos α)` — are
in `Submission/Work/OddRadon/RadonXi.lean`.)
-/

noncomputable section

set_option linter.style.haveILetI false

open MeasureTheory
open scoped RealInnerProductSpace Pointwise Interval Topology

namespace Work.OddRadon

/-- The surface area of `S^{d-3}` (the constant of the reduction) written as the total mass of
the sphere measure of `ℝ^{d-2}`. -/
lemma sphereArea_sub_three (d : ℕ) (hd : 3 ≤ d) :
    sphereArea (d - 3)
      = (((MeasureTheory.Measure.toSphere
          (volume : Measure (EuclideanSpace ℝ (Fin (d - 2))))) Set.univ).toReal) := by
  haveI : Nonempty (Fin (d - 2)) := ⟨⟨0, by omega⟩⟩
  rw [sphereArea]
  exact Commons.Analysis.Radon.toSphere_real_univ_eq_of_finrank_eq
    (E := EuclideanSpace ℝ (Fin (d - 3 + 1))) (F := EuclideanSpace ℝ (Fin (d - 2))) (by
      rw [finrank_euclideanSpace, finrank_euclideanSpace, Fintype.card_fin, Fintype.card_fin]
      omega)

/-- **The reduction of the spherical Radon transform to one variable.**
For `g w = γ (w 0)` with `γ` continuous and `ξ` a unit vector,

  `𝓡 g ξ = radonProfile d γ (√(1 - (ξ 0)^2))`. -/
theorem sphericalRadon_rotationInvariant (d : ℕ) [NeZero d] (hd : 3 ≤ d) {γ : ℝ → ℝ}
    (hγ : Continuous γ) {ξ : EuclideanSpace ℝ (Fin d)} (hξ : ‖ξ‖ = 1) :
    sphericalRadon d (fun w => γ (w 0)) ξ = radonProfile d γ (Real.sqrt (1 - (ξ 0) ^ 2)) := by
  have hred := Commons.Analysis.Radon.radial_reduction_of_radonOver (d := d) hd γ hγ
    (e0 d) ξ (e0_norm d) hξ
  have hσ := sphereArea_sub_three d hd
  have hfun : ∀ ω : Metric.sphere (0 : (ℝ ∙ ξ)ᗮ) 1,
      γ (((ω : (ℝ ∙ ξ)ᗮ) : EuclideanSpace ℝ (Fin d)) 0)
        = γ ⟪((ω : (ℝ ∙ ξ)ᗮ) : EuclideanSpace ℝ (Fin d)), e0 d⟫ :=
    fun ω => by rw [inner_e0]
  simp only [sphericalRadon, radonProfile]
  rw [show (∫ ω : Metric.sphere (0 : (ℝ ∙ ξ)ᗮ) 1,
        γ (((ω : (ℝ ∙ ξ)ᗮ) : EuclideanSpace ℝ (Fin d)) 0)
          ∂MeasureTheory.Measure.toSphere (volume : Measure (ℝ ∙ ξ)ᗮ))
      = ∫ ω : Metric.sphere (0 : (ℝ ∙ ξ)ᗮ) 1,
        γ ⟪((ω : (ℝ ∙ ξ)ᗮ) : EuclideanSpace ℝ (Fin d)), e0 d⟫
          ∂MeasureTheory.Measure.toSphere (volume : Measure (ℝ ∙ ξ)ᗮ) from
    integral_congr_ae (Filter.Eventually.of_forall hfun)]
  rw [hred, ← hσ, inner_e0]
  congr 1
  apply intervalIntegral.integral_congr
  intro s _
  ring

/-- The Radon transform of a rotation-invariant integrand depends only on `|ξ 0|`. -/
theorem sphericalRadon_rotationInvariant_factor (d : ℕ) [NeZero d] (hd : 3 ≤ d) {γ : ℝ → ℝ}
    (hγ : Continuous γ) {ξ η : EuclideanSpace ℝ (Fin d)} (hξ : ‖ξ‖ = 1) (hη : ‖η‖ = 1)
    (h : (ξ 0) ^ 2 = (η 0) ^ 2) :
    sphericalRadon d (fun w => γ (w 0)) ξ = sphericalRadon d (fun w => γ (w 0)) η := by
  rw [sphericalRadon_rotationInvariant d hd hγ hξ,
    sphericalRadon_rotationInvariant d hd hγ hη, h]

/-! ### Symmetries of the profile form -/

/-- `radonProfile` only sees `|c|`. -/
lemma radonProfile_neg (d : ℕ) (γ : ℝ → ℝ) (c : ℝ) :
    radonProfile d γ (-c) = radonProfile d γ c := by
  have key : (∫ s in (-1 : ℝ)..1, (1 - s ^ 2) ^ ((d : ℝ) / 2 - 2) * γ ((-c) * s))
      = ∫ s in (-1 : ℝ)..1, (1 - s ^ 2) ^ ((d : ℝ) / 2 - 2) * γ (c * (-s)) := by
    apply intervalIntegral.integral_congr
    intro s _
    change (1 - s ^ 2) ^ ((d : ℝ) / 2 - 2) * γ ((-c) * s)
      = (1 - s ^ 2) ^ ((d : ℝ) / 2 - 2) * γ (c * (-s))
    rw [neg_mul, mul_neg]
  have h2 : (∫ s in (-1 : ℝ)..1, (1 - s ^ 2) ^ ((d : ℝ) / 2 - 2) * γ (c * (-s)))
      = ∫ s in (-1 : ℝ)..1, (1 - s ^ 2) ^ ((d : ℝ) / 2 - 2) * γ (c * s) := by
    have h := intervalIntegral.integral_comp_neg (a := (-1 : ℝ)) (b := 1)
      (f := fun s : ℝ => (1 - s ^ 2) ^ ((d : ℝ) / 2 - 2) * γ (c * s))
    simpa only [neg_sq, neg_neg] using h
  simp only [radonProfile]
  rw [key, h2]

/-- For an odd profile the transform vanishes. -/
lemma radonProfile_odd (d : ℕ) {γ : ℝ → ℝ} (hγ : ∀ t, γ (-t) = - γ t) (c : ℝ) :
    radonProfile d γ c = 0 := by
  have hneg : radonProfile d γ (-c) = - radonProfile d γ c := by
    have key : (∫ s in (-1 : ℝ)..1, (1 - s ^ 2) ^ ((d : ℝ) / 2 - 2) * γ ((-c) * s))
        = ∫ s in (-1 : ℝ)..1, -((1 - s ^ 2) ^ ((d : ℝ) / 2 - 2) * γ (c * s)) := by
      apply intervalIntegral.integral_congr
      intro s _
      change (1 - s ^ 2) ^ ((d : ℝ) / 2 - 2) * γ ((-c) * s)
        = -((1 - s ^ 2) ^ ((d : ℝ) / 2 - 2) * γ (c * s))
      rw [neg_mul, hγ (c * s), mul_neg]
    simp only [radonProfile]
    rw [key, intervalIntegral.integral_neg, mul_neg]
  rw [radonProfile_neg] at hneg
  linarith

end Work.OddRadon
