import Mathlib.Algebra.Ring.IsFormallyReal
import Mathlib.Analysis.CStarAlgebra.Classes
import Mathlib.MeasureTheory.Measure.Haar.NormedSpace
import Submission.Work.BoseFixB3.Scaling.chiU_sq_indicator
import Submission.Work.BoseFixB3.Scaling.kinFT_scaled_phi
-- PORT435-BEGIN (v4.35 isDefEq respectTransparency compat)
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- PORT435-END

/-!
# `Submission/Work/BoseFixB3/Conv/Scale/multOn_scale_phi`

The Fourier multiplier `Work.BoseFixB3.multOn` is *covariant* under dilating the box and
the profile: on the window profile `φ = χ²` (`Work.BoseFixB3.Scaling.phi`) of FS `sec:3Q`,

`multOn F ℓ (φ(ℓ⁻¹•·)) x = multOn (F(ℓ⁻¹·)) 1 φ (ℓ⁻¹•x)`.

Both sides are `(2π)⁻³∫_p e^{i⟪p,·⟫}·(symbol)·φ̂(p) dp`, and the identity is exactly the
change of variables `p ↦ ℓ⁻¹p` in the `p`-integral, using

* `Scaling.chiU_sq_indicator` to drop the box truncation `1_{acube ℓ}` (the profile already
  vanishes outside the box), and `1_{acube 1} φ = φ` at `ℓ = 1`;
* `Scaling.kinFT_scaled_phi`, i.e. `kinFT (φ(ℓ⁻¹•·)) p = ℓ³ · kinFT φ (ℓ·p)`;
* `Measure.integral_comp_smul_of_nonneg` (`∫ f (ℓ • p) dp = (ℓ³)⁻¹ ∫ f`).
-/

noncomputable section

open MeasureTheory

namespace Work.BoseFixB3.Conv.Scale

local notation "E3" => EuclideanSpace ℝ (Fin 3)

theorem multOn_scale_phi (F : ℝ → ℝ) (ℓ : ℝ) (hℓ : 0 < ℓ) (x : EuclideanSpace ℝ (Fin 3)) :
    Work.BoseFixB3.multOn F ℓ (fun z => Work.BoseFixB3.Scaling.phi (ℓ⁻¹ • z)) x
      = Work.BoseFixB3.multOn (fun r => F (ℓ⁻¹ * r)) 1
          Work.BoseFixB3.Scaling.phi (ℓ⁻¹ • x) := by
  have hℓne : ℓ ≠ 0 := ne_of_gt hℓ
  have hfin : Module.finrank ℝ E3 = 3 := by simp
  -- ## 1. The box truncations are redundant
  have hchi : (fun z : E3 => Submission.BoseGases.chiU ℓ 0 z ^ 2)
      = fun z => Work.BoseFixB3.Scaling.phi (ℓ⁻¹ • z) := by
    funext z
    simp [Submission.BoseGases.chiU, Work.BoseFixB3.Scaling.phi, sub_zero]
  have h1 : ∀ z : E3,
      (Submission.BoseGases.acube ℓ).indicator (fun z => Work.BoseFixB3.Scaling.phi (ℓ⁻¹ • z)) z
        = Work.BoseFixB3.Scaling.phi (ℓ⁻¹ • z) := by
    intro z
    rw [← hchi]
    exact Work.BoseFixB3.Scaling.chiU_sq_indicator ℓ hℓ z
  have key_ind : (fun z : E3 => (((Submission.BoseGases.acube ℓ).indicator
        (fun z => Work.BoseFixB3.Scaling.phi (ℓ⁻¹ • z)) z : ℝ) : ℂ))
      = (fun z => (Work.BoseFixB3.Scaling.phi (ℓ⁻¹ • z) : ℂ)) := by
    funext z
    rw [h1 z]
  have hchi1 : (fun z : E3 => Submission.BoseGases.chiU 1 0 z ^ 2)
      = Work.BoseFixB3.Scaling.phi := by
    funext z
    simp [Submission.BoseGases.chiU, Work.BoseFixB3.Scaling.phi, sub_zero, inv_one, one_smul]
  have h2 : ∀ z : E3,
      (Submission.BoseGases.acube 1).indicator Work.BoseFixB3.Scaling.phi z
        = Work.BoseFixB3.Scaling.phi z := by
    intro z
    have h := Work.BoseFixB3.Scaling.chiU_sq_indicator 1 one_pos z
    simp only [inv_one, one_smul] at h
    rwa [hchi1] at h
  have key_ind1 : (fun z : E3 => (((Submission.BoseGases.acube 1).indicator
        Work.BoseFixB3.Scaling.phi z : ℝ) : ℂ)) = Work.BoseFixB3.Scaling.phiC := by
    funext z
    rw [h2 z]
    rfl
  -- ## 2. The change of variables `p ↦ ℓ⁻¹ • p` in the `p`-integral
  have hInt :
      (∫ p : E3, Complex.exp (Complex.I * (inner ℝ p x : ℂ)) * ((F ‖p‖ : ℝ) : ℂ) *
          Submission.BoseGases.kinFT (fun z : E3 =>
            (Work.BoseFixB3.Scaling.phi (ℓ⁻¹ • z) : ℂ)) p)
        = ∫ p : E3, Complex.exp (Complex.I * (inner ℝ p (ℓ⁻¹ • x) : ℂ)) *
            ((F (ℓ⁻¹ * ‖p‖) : ℝ) : ℂ) *
              Submission.BoseGases.kinFT Work.BoseFixB3.Scaling.phiC p := by
    set H : E3 → ℂ := fun q => Complex.exp (Complex.I * (inner ℝ q (ℓ⁻¹ • x) : ℂ)) *
        ((F (ℓ⁻¹ * ‖q‖) : ℝ) : ℂ) * Submission.BoseGases.kinFT Work.BoseFixB3.Scaling.phiC q
      with hH
    have hpt : ∀ p : E3,
        (Complex.exp (Complex.I * (inner ℝ p x : ℂ)) * ((F ‖p‖ : ℝ) : ℂ) *
          Submission.BoseGases.kinFT (fun z : E3 =>
            (Work.BoseFixB3.Scaling.phi (ℓ⁻¹ • z) : ℂ)) p)
          = (ℓ ^ 3 : ℝ) • H (ℓ • p) := by
      intro p
      have hk := Work.BoseFixB3.Scaling.kinFT_scaled_phi ℓ hℓ p
      have hin : inner ℝ (ℓ • p) (ℓ⁻¹ • x) = inner ℝ p x := by
        rw [real_inner_smul_left, real_inner_smul_right, ← mul_assoc,
          mul_inv_cancel₀ hℓne, one_mul]
      have hn : ℓ⁻¹ * ‖ℓ • p‖ = ‖p‖ := by
        rw [norm_smul, Real.norm_eq_abs, abs_of_pos hℓ, ← mul_assoc,
          inv_mul_cancel₀ hℓne, one_mul]
      simp only [hH]
      rw [hk, hin, hn]
      rw [Complex.real_smul, Complex.real_smul]
      ring
    rw [show (∫ p : E3, Complex.exp (Complex.I * (inner ℝ p x : ℂ)) * ((F ‖p‖ : ℝ) : ℂ) *
          Submission.BoseGases.kinFT (fun z : E3 =>
            (Work.BoseFixB3.Scaling.phi (ℓ⁻¹ • z) : ℂ)) p)
        = ∫ p : E3, (ℓ ^ 3 : ℝ) • H (ℓ • p) from by
          apply integral_congr_ae
          filter_upwards with p
          exact hpt p]
    rw [integral_smul]
    have hI2 : (∫ p : E3, H (ℓ • p)) = ((ℓ ^ 3)⁻¹ : ℝ) • ∫ p : E3, H p := by
      have hsub := Measure.integral_comp_smul_of_nonneg volume H ℓ (hR := hℓ.le)
      simpa [hfin] using hsub
    rw [hI2]
    rw [smul_smul, mul_inv_cancel₀ (pow_ne_zero 3 hℓne), one_smul]
  -- ## 3. Assemble
  unfold Work.BoseFixB3.multOn
  rw [key_ind, key_ind1, hInt]

end Work.BoseFixB3.Conv.Scale
