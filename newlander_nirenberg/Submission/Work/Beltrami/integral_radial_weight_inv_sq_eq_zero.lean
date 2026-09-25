import Mathlib

set_option linter.unusedVariables false

namespace Work.Beltrami

/-- The kernel `w ↦ w⁻²` has vanishing integral against a radial weight over any set that is
invariant under all rotations `w ↦ c * w` (`‖c‖ = 1`): the rotation by `I` preserves both `S` and
Lebesgue measure, while `(I*w)⁻² = -w⁻²`, so the integral equals its own negative. -/
theorem integral_radial_weight_inv_sq_eq_zero (g : ℝ → ℝ) {S : Set ℂ}
    (hS : ∀ c : Circle, ∀ w : ℂ, w ∈ S ↔ (c : ℂ) * w ∈ S)
    (hg : MeasureTheory.IntegrableOn (fun w : ℂ => (g ‖w‖ : ℂ) * (w ^ 2)⁻¹) S MeasureTheory.volume) :
    ∫ w in S, (g ‖w‖ : ℂ) * (w ^ 2)⁻¹ = 0 := by
  -- The rotation by `I`: an element of the unit circle whose square is `-1`.
  set c : Circle := ⟨Complex.I, by simp [Submonoid.unitSphere]⟩ with hc
  have hcI : (c : ℂ) = Complex.I := by rw [hc]
  have hc2 : (c : ℂ) ^ 2 = -1 := by rw [hcI, pow_two, Complex.I_mul_I]
  have hcne : (c : ℂ) ≠ 0 := by rw [hcI]; exact Complex.I_ne_zero
  -- Multiplication by `c` is measure-preserving and a measurable embedding.
  have hMP : MeasureTheory.MeasurePreserving (fun w : ℂ => (c:ℂ) * w)
      MeasureTheory.volume MeasureTheory.volume := by
    have h := LinearIsometryEquiv.measurePreserving (rotation c)
    convert h using 1
    ext w
    simp [rotation_apply]
  have hEmb : MeasurableEmbedding (fun w : ℂ => (c:ℂ) * w) := by
    have h : MeasurableEmbedding (⇑(rotation c).toContinuousLinearEquiv.toHomeomorph) :=
      (rotation c).toContinuousLinearEquiv.toHomeomorph.measurableEmbedding
    convert h using 1
    ext w
    simp [rotation_apply]
  -- Invariance of `S` under the rotation, as an equality of sets.
  have hTimg : (fun w : ℂ => (c:ℂ) * w) '' S = S := by
    ext y
    constructor
    · rintro ⟨x, hx, hxy⟩
      rw [← hxy]
      exact (hS c x).mp hx
    · intro hy
      refine ⟨(c:ℂ)⁻¹ * y, ?_, ?_⟩
      · refine (hS c ((c:ℂ)⁻¹ * y)).mpr ?_
        rw [show (c:ℂ) * ((c:ℂ)⁻¹ * y) = y by
          rw [← mul_assoc, mul_inv_cancel₀ hcne, one_mul]]
        exact hy
      · show (c:ℂ) * ((c:ℂ)⁻¹ * y) = y
        rw [← mul_assoc, mul_inv_cancel₀ hcne, one_mul]
  -- Vanishing of the integral of any function that is anti-invariant under the rotation.
  have key : ∀ (f : ℂ → ℂ), (∀ x, f ((c:ℂ) * x) = -f x) → ∫ x in S, f x = 0 := by
    intro f hf
    have hstep1 : ∫ y in S, f y = ∫ x in S, f ((c:ℂ) * x) := by
      have h := hMP.setIntegral_image_emb hEmb f S
      rwa [hTimg] at h
    have hstep2 : ∫ x in S, f ((c:ℂ) * x) = - ∫ x in S, f x := by
      rw [show (fun x => f ((c:ℂ) * x)) = (fun x => - f x) from funext hf]
      exact MeasureTheory.integral_neg f
    have hmain : ∫ x in S, f x = - ∫ x in S, f x :=
      calc ∫ x in S, f x = ∫ x in S, f ((c:ℂ) * x) := hstep1
        _ = - ∫ x in S, f x := hstep2
    have hsum : (∫ x in S, f x) + (∫ x in S, f x) = 0 := by
      have h' := congrArg (· + ∫ x in S, f x) hmain
      simpa using h'
    exact add_self_eq_zero.mp hsum
  refine key (fun w => (g ‖w‖ : ℂ) * (w ^ 2)⁻¹) ?_
  intro x
  have hnorm : ‖(c:ℂ) * x‖ = ‖x‖ := by rw [norm_mul, hcI, Complex.norm_I, one_mul]
  have hsq : ((c:ℂ) * x) ^ 2 = -(x ^ 2) := by rw [mul_pow, hc2, neg_one_mul]
  simp only [hnorm, hsq, inv_neg]
  ring

end Work.Beltrami
