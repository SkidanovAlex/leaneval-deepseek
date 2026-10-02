import Mathlib
import Submission.Work.MRMT.Found.Defs
import Submission.Work.MRMT.Wirtinger.dz_comp
import Submission.Work.MRMT.Wirtinger.dzbar_comp

-- Lean v4.35.0-rc3 / Mathlib 5e0c4e5 made `isDefEq` respect transparency when unifying instances; with it,
-- `ZMod.instField` and `ZMod.commRing` (and `Neg (ZMod p)` via `SubtractionMonoid`) no longer unify, which
-- breaks `ring`/`rw`/module-instance search on `ZMod p`. Restore the v4.34 behaviour for this file.
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false


namespace Work.MRMT.Found

open Complex

/-- **Inverse-matrix relation for the Wirtinger coefficients of a `C¹` homeomorphism.**

For a homeomorphism `F : ℂ ≃ₜ ℂ` that is `C¹` together with its inverse, and every `z`,
writing `a = ∂F(z)`, `b = ∂̄F(z)`, `A = ∂(F⁻¹)(F z)`, `B = ∂̄(F⁻¹)(F z)`, one has

`A * a + B * conj b = 1`   and   `A * b + B * conj a = 0`.

Indeed these are the two Wirtinger components of the chain rule for `F⁻¹ ∘ F = id`:
`∂(F⁻¹ ∘ F) = 1` and `∂̄(F⁻¹ ∘ F) = 0`. -/
theorem symm_coeff {F : ℂ ≃ₜ ℂ}
    (hF : ContDiff ℝ 1 (F : ℂ → ℂ)) (hGs : ContDiff ℝ 1 ((F.symm : ℂ → ℂ))) (z : ℂ) :
    Work.MRMT.dz (F.symm : ℂ → ℂ) (F z) * Work.MRMT.dz (F : ℂ → ℂ) z
        + Work.MRMT.dzbar (F.symm : ℂ → ℂ) (F z)
            * star (Work.MRMT.dzbar (F : ℂ → ℂ) z) = 1 ∧
    Work.MRMT.dz (F.symm : ℂ → ℂ) (F z) * Work.MRMT.dzbar (F : ℂ → ℂ) z
        + Work.MRMT.dzbar (F.symm : ℂ → ℂ) (F z)
            * star (Work.MRMT.dz (F : ℂ → ℂ) z) = 0 := by
  have hg : DifferentiableAt ℝ (F.symm : ℂ → ℂ) (F z) :=
    hGs.contDiffAt.differentiableAt (by norm_num)
  have hf : DifferentiableAt ℝ (F : ℂ → ℂ) z :=
    hF.contDiffAt.differentiableAt (by norm_num)
  have hgf : ((F.symm : ℂ → ℂ) ∘ (F : ℂ → ℂ)) = id := funext (fun x => F.symm_apply_apply x)
  constructor
  · have h := Work.MRMT.Wirtinger.dz_comp (f := (F : ℂ → ℂ)) (g := (F.symm : ℂ → ℂ))
      (z := z) hg hf
    rw [hgf, Work.MRMT.dz_id] at h
    exact h.symm
  · have h := Work.MRMT.Wirtinger.dzbar_comp (f := (F : ℂ → ℂ)) (g := (F.symm : ℂ → ℂ))
      (z := z) hg hf
    rw [hgf, Work.MRMT.dzbar_id] at h
    exact h.symm

theorem dzbar_symm_le (F : ℂ ≃ₜ ℂ) (μ : ℂ → ℂ) (k : ℝ)
    (hF : ContDiff ℝ 1 (F : ℂ → ℂ)) (hFs : ContDiff ℝ 1 ((F.symm : ℂ → ℂ)))
    (hrel : ∀ z : ℂ, Work.MRMT.dzbar (F : ℂ → ℂ) z = μ z * Work.MRMT.dz (F : ℂ → ℂ) z)
    (hb : ∀ z : ℂ, ‖μ z‖ ≤ k) :
    (∀ w : ℂ, ‖Work.MRMT.dzbar ((F.symm : ℂ → ℂ)) w‖ ≤ k * ‖Work.MRMT.dz ((F.symm : ℂ → ℂ)) w‖) ∧
    (∀ w : ℂ, Work.MRMT.dzbar ((F.symm : ℂ → ℂ)) w ≠ 0 → μ (F.symm w) ≠ 0) := by
  -- Pointwise statement at `F z` for every `z`.
  have key : ∀ z : ℂ,
      ‖Work.MRMT.dzbar (F.symm : ℂ → ℂ) (F z)‖
          ≤ k * ‖Work.MRMT.dz (F.symm : ℂ → ℂ) (F z)‖ ∧
      (Work.MRMT.dzbar (F.symm : ℂ → ℂ) (F z) ≠ 0 → μ z ≠ 0) := by
    intro z
    obtain ⟨h1, h2⟩ := symm_coeff hF hFs z
    set a : ℂ := Work.MRMT.dz (F : ℂ → ℂ) z with ha
    set b : ℂ := Work.MRMT.dzbar (F : ℂ → ℂ) z with hbdef
    set A : ℂ := Work.MRMT.dz (F.symm : ℂ → ℂ) (F z) with hA
    set B : ℂ := Work.MRMT.dzbar (F.symm : ℂ → ℂ) (F z) with hB
    -- h1 : A * a + B * star b = 1,  h2 : A * b + B * star a = 0
    have hrel_z : b = μ z * a := hrel z
    have ha_ne : a ≠ 0 := by
      intro ha0
      have hb0 : b = 0 := by rw [hrel_z, ha0, mul_zero]
      have hone : (1 : ℂ) = 0 := by
        rw [ha0, hb0] at h1
        simpa using h1.symm
      exact one_ne_zero hone
    have hB_le : ‖B‖ ≤ k * ‖A‖ := by
      have hAb : A * b = -(B * star a) := by linear_combination h2
      have hnorm : ‖A‖ * ‖b‖ = ‖B‖ * ‖a‖ := by
        calc ‖A‖ * ‖b‖ = ‖A * b‖ := (norm_mul A b).symm
          _ = ‖-(B * star a)‖ := by rw [hAb]
          _ = ‖B * star a‖ := norm_neg _
          _ = ‖B‖ * ‖star a‖ := norm_mul B (star a)
          _ = ‖B‖ * ‖a‖ := by rw [norm_star]
      have hbnb : ‖b‖ = ‖μ z‖ * ‖a‖ := by rw [hrel_z, norm_mul]
      have hcancel : ‖B‖ = ‖A‖ * ‖μ z‖ := by
        have h := hnorm
        rw [hbnb, ← mul_assoc] at h
        exact (mul_right_cancel₀ (by simpa [norm_eq_zero] using ha_ne) h).symm
      calc ‖B‖ = ‖A‖ * ‖μ z‖ := hcancel
        _ ≤ ‖A‖ * k := mul_le_mul_of_nonneg_left (hb z) (norm_nonneg A)
        _ = k * ‖A‖ := by ring
    refine ⟨hB_le, ?_⟩
    intro hB0 hmu
    have hb0 : b = 0 := by rw [hrel_z, hmu, zero_mul]
    have hBa : B * star a = 0 := by
      have h := h2
      rw [hb0] at h
      simpa using h
    rcases mul_eq_zero.mp hBa with h | h
    · exact hB0 h
    · exact ha_ne (by have := congrArg star h; simpa using this)
  constructor
  · intro w
    have h := (key (F.symm w)).1
    rwa [F.apply_symm_apply w] at h
  · intro w hB
    have h := (key (F.symm w)).2
    rw [F.apply_symm_apply w] at h
    exact h hB

end Work.MRMT.Found
