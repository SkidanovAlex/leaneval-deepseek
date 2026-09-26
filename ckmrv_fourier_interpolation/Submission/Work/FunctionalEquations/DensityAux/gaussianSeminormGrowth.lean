import Mathlib
import Submission.Work.Core.Basic
import Submission.Work.Radial.exp_iteratedFDeriv_bound
import Submission.Work.Radial.quad_iteratedFDeriv_bound
import Submission.Work.Radial.poly_mul_exp_neg_sq_bounded

/-!
# Polynomial growth of the Schwartz seminorms of the complex Gaussian

For fixed `y > 0` and any `k, l : ℕ`, the `(k,l)`-th Schwartz seminorm of the Gaussian
`x ↦ exp (π i τ ‖x‖²)` at `τ = u + i y` grows at most like `(1 + |u|)^{2l+2}` in the real
part `u`.  The decay rate `exp (-π y ‖x‖²)` is independent of `u`, while the derivatives
bring in powers of `c = π i τ`, whence the polynomial growth in `|u|`.
-/

open scoped SchwartzMap ContDiff

namespace Work.FunctionalEquations.DensityAux

set_option maxHeartbeats 1000000 in
/-- The `(k,l)`-th Schwartz seminorm of the complex Gaussian `x ↦ exp (π i (u + i y) ‖x‖²)`
is at most `C * (1 + |u|)^(2l+2)`, with `C` independent of `u`. -/
theorem gaussianSeminormGrowth (n : ℕ) [NeZero n] {y : ℝ} (hy : 0 < y) (k l : ℕ) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ (u : ℝ) (G : SchwartzMap (EuclideanSpace ℝ (Fin n)) ℂ),
      (∀ x, G x = Work.Core.gaussianFun n ((u : ℂ) + (y : ℂ) * Complex.I) x) →
      (SchwartzMap.seminorm ℂ k l) G ≤ C * (1 + |u|) ^ (2 * l + 2) := by
  have ha : 0 < Real.pi * y := by positivity
  obtain ⟨B, hB⟩ := Work.Radial.poly_mul_exp_neg_sq_bounded (Real.pi * y) ha k l
  have hB0 : 0 ≤ B := by
    have h := hB 0 (le_refl 0)
    have h0 : (0:ℝ) ≤ 0 ^ k * (1 + 0) ^ (2 * l) * Real.exp (-(Real.pi * y) * 0 ^ 2) := by positivity
    linarith
  refine ⟨(Nat.factorial l : ℝ) * (2 * (Real.pi * (y + 1) + 1) + 1) ^ l * B, by positivity, ?_⟩
  intro u G hG
  refine SchwartzMap.seminorm_le_bound ℂ k l G (by positivity) (fun x => ?_)
  set c : ℂ := ↑Real.pi * Complex.I * ((u : ℂ) + ↑y * Complex.I) with hc
  have hfun : (⇑G : EuclideanSpace ℝ (Fin n) → ℂ)
      = fun x => Complex.exp (c * (↑(‖x‖ ^ 2) : ℂ)) := by
    funext x
    rw [hG x, Work.Core.gaussianFun, hc]
  rw [hfun]
  have hcre : c.re = -(Real.pi * y) := by
    rw [hc]
    simp only [Complex.mul_re, Complex.mul_im, Complex.add_re, Complex.add_im, Complex.ofReal_re,
      Complex.ofReal_im, Complex.I_re, Complex.I_im, mul_zero, mul_one, add_zero]
    ring
  have hf : ContDiff ℝ ∞ (fun x : EuclideanSpace ℝ (Fin n) => c * (↑(‖x‖ ^ 2) : ℂ)) := by
    have h2 : ContDiff ℝ ∞ (fun x : EuclideanSpace ℝ (Fin n) => (‖x‖ ^ 2 : ℝ)) :=
      (Function.hasTemperateGrowth_norm_sq (H := EuclideanSpace ℝ (Fin n))).1
    have h3 : ContDiff ℝ ∞ (fun x : EuclideanSpace ℝ (Fin n) => ((‖x‖ ^ 2 : ℝ) : ℂ)) :=
      Complex.ofRealCLM.contDiff.comp h2
    exact contDiff_const.mul h3
  have hcomp := norm_iteratedFDeriv_comp_le (𝕜 := ℝ) (n := l) (N := ∞) (g := Complex.exp)
      (f := fun x : EuclideanSpace ℝ (Fin n) => c * (↑(‖x‖ ^ 2) : ℂ))
      Complex.contDiff_exp hf (by
        rw [show (∞ : ℕ∞ω) = ((⊤ : ℕ∞) : ℕ∞ω) from rfl]
        exact WithTop.coe_le_coe.mpr le_top) x
      (C := Real.exp (-(Real.pi * y) * ‖x‖ ^ 2))
      (D := (2 * (‖c‖ + 1) + 1) * (1 + ‖x‖) ^ 2) ?_ ?_
  rw [Function.comp_def] at hcomp
  · have hcn : Real.pi * ‖(u : ℂ) + ↑y * Complex.I‖ ≤ Real.pi * (|u| + y) := by
      have hnorm_u : ‖((u : ℝ) : ℂ)‖ = |u| := RCLike.norm_ofReal u
      have hnorm_y : ‖((y : ℝ) * Complex.I : ℂ)‖ = y := by
        rw [Complex.norm_mul]
        have h1 : ‖((y : ℝ) : ℂ)‖ = |y| := RCLike.norm_ofReal y
        rw [h1, Complex.norm_I, mul_one, abs_of_pos hy]
      have h1 : ‖(u : ℂ) + ↑y * Complex.I‖ ≤ |u| + y := by
        calc ‖(u : ℂ) + ↑y * Complex.I‖ ≤ ‖(u : ℂ)‖ + ‖(↑y * Complex.I : ℂ)‖ := norm_add_le _ _
          _ = |u| + y := by rw [hnorm_u, hnorm_y]
      exact mul_le_mul_of_nonneg_left h1 Real.pi_pos.le
    have hcU : ‖c‖ ≤ Real.pi * (|u| + y) := by
      have h1 : ‖((Real.pi : ℝ) : ℂ)‖ = Real.pi :=
        (RCLike.norm_ofReal Real.pi).trans (abs_of_pos Real.pi_pos)
      calc ‖c‖ = ‖((Real.pi : ℝ) : ℂ)‖ * ‖Complex.I * ((u : ℂ) + ↑y * Complex.I)‖ := by
            rw [hc, show (↑Real.pi : ℂ) * Complex.I * ((u : ℂ) + ↑y * Complex.I)
                = ((Real.pi : ℝ) : ℂ) * (Complex.I * ((u : ℂ) + ↑y * Complex.I)) by ring, norm_mul]
        _ = Real.pi * ‖(u : ℂ) + ↑y * Complex.I‖ := by
            rw [h1, norm_mul, Complex.norm_I, one_mul]
        _ ≤ Real.pi * (|u| + y) := hcn
    calc ‖x‖ ^ k * ‖iteratedFDeriv ℝ l
            (fun x : EuclideanSpace ℝ (Fin n) => Complex.exp (c * (↑(‖x‖ ^ 2) : ℂ))) x‖
        ≤ ‖x‖ ^ k * ((Nat.factorial l : ℝ) * Real.exp (-(Real.pi * y) * ‖x‖ ^ 2)
            * ((2 * (‖c‖ + 1) + 1) * (1 + ‖x‖) ^ 2) ^ l) := by gcongr
      _ = (Nat.factorial l : ℝ) * (2 * (‖c‖ + 1) + 1) ^ l
            * (‖x‖ ^ k * (1 + ‖x‖) ^ (2 * l) * Real.exp (-(Real.pi * y) * ‖x‖ ^ 2)) := by
          rw [mul_pow, pow_mul]; ring
      _ ≤ (Nat.factorial l : ℝ) * (2 * (‖c‖ + 1) + 1) ^ l * B := by
          gcongr
          exact hB ‖x‖ (norm_nonneg x)
      _ ≤ (Nat.factorial l : ℝ) * (2 * (Real.pi * (y + 1) + 1) + 1) ^ l * B
            * (1 + |u|) ^ (2 * l + 2) := by
          have h1 : (2 * (‖c‖ + 1) + 1) ≤ (2 * (Real.pi * (y + 1) + 1) + 1) * (1 + |u|) := by
            have habs : (0:ℝ) ≤ |u| := abs_nonneg u
            have hC : 2 * (‖c‖ + 1) + 1 ≤ 2 * (Real.pi * (|u| + y) + 1) + 1 := by linarith [hcU]
            have hD : 2 * (Real.pi * (|u| + y) + 1) + 1 ≤
                (2 * (Real.pi * (y + 1) + 1) + 1) * (1 + |u|) := by
              nlinarith [habs, Real.pi_pos, hy]
            linarith [hC, hD]
          have h2 : (2 * (‖c‖ + 1) + 1) ^ l
              ≤ ((2 * (Real.pi * (y + 1) + 1) + 1) * (1 + |u|)) ^ l :=
            pow_le_pow_left₀ (by positivity) h1 l
          have h3 : ((2 * (Real.pi * (y + 1) + 1) + 1) * (1 + |u|)) ^ l
              = (2 * (Real.pi * (y + 1) + 1) + 1) ^ l * (1 + |u|) ^ l := mul_pow _ _ _
          have h4 : (1 + |u|) ^ l ≤ (1 + |u|) ^ (2 * l + 2) :=
            pow_le_pow_right₀ (by linarith [abs_nonneg u]) (by omega)
          rw [h3] at h2
          calc (Nat.factorial l : ℝ) * (2 * (‖c‖ + 1) + 1) ^ l * B
              ≤ (Nat.factorial l : ℝ) * ((2 * (Real.pi * (y + 1) + 1) + 1) ^ l * (1 + |u|) ^ l) * B := by
                have h5 : (0:ℝ) ≤ (Nat.factorial l : ℝ) := by positivity
                calc (Nat.factorial l : ℝ) * (2 * (‖c‖ + 1) + 1) ^ l * B
                    = (Nat.factorial l : ℝ) * B * (2 * (‖c‖ + 1) + 1) ^ l := by ring
                  _ ≤ (Nat.factorial l : ℝ) * B *
                        ((2 * (Real.pi * (y + 1) + 1) + 1) ^ l * (1 + |u|) ^ l) :=
                      mul_le_mul_of_nonneg_left h2 (by positivity)
                  _ = (Nat.factorial l : ℝ) * ((2 * (Real.pi * (y + 1) + 1) + 1) ^ l * (1 + |u|) ^ l) * B := by ring
            _ = (Nat.factorial l : ℝ) * (2 * (Real.pi * (y + 1) + 1) + 1) ^ l * B
                  * (1 + |u|) ^ l := by ring
            _ ≤ (Nat.factorial l : ℝ) * (2 * (Real.pi * (y + 1) + 1) + 1) ^ l * B
                  * (1 + |u|) ^ (2 * l + 2) := by
                apply mul_le_mul_of_nonneg_left h4
                positivity
      _ = (Nat.factorial l : ℝ) * (2 * (Real.pi * (y + 1) + 1) + 1) ^ l * B
            * (1 + |u|) ^ (2 * l + 2) := rfl
  · intro i hi
    have h := Work.Radial.exp_iteratedFDeriv_bound i (c * (↑(‖x‖ ^ 2) : ℂ))
    have hxre : (c * (↑(‖x‖ ^ 2) : ℂ)).re = -(Real.pi * y) * ‖x‖ ^ 2 := by
      rw [Complex.mul_re, hcre, Complex.ofReal_im, Complex.ofReal_re]
      ring
    rwa [hxre] at h
  · intro i hi1 him
    have h := Work.Radial.quad_iteratedFDeriv_bound c i x
    refine h.trans ?_
    have hK1 : 1 ≤ 2 * (‖c‖ + 1) + 1 := by have := norm_nonneg c; linarith
    have hx1 : 1 ≤ 1 + ‖x‖ := by have := norm_nonneg x; linarith
    have h1 : 2 * (‖c‖ + 1) ≤ (2 * (‖c‖ + 1) + 1) ^ i := by
      calc 2 * (‖c‖ + 1) ≤ 2 * (‖c‖ + 1) + 1 := by linarith
        _ ≤ (2 * (‖c‖ + 1) + 1) ^ i := by
            simpa using pow_le_pow_right₀ hK1 (show 1 ≤ i by omega)
    have h2 : (1 + ‖x‖) ^ 2 ≤ (1 + ‖x‖) ^ (2 * i) :=
      pow_le_pow_right₀ hx1 (by omega)
    calc 2 * (‖c‖ + 1) * (1 + ‖x‖) ^ 2
        ≤ (2 * (‖c‖ + 1) + 1) ^ i * (1 + ‖x‖) ^ (2 * i) :=
          mul_le_mul h1 h2 (by positivity) (by positivity)
      _ = (((2 * (‖c‖ + 1) + 1) * (1 + ‖x‖) ^ 2)) ^ i := by
          rw [mul_pow, pow_mul]

end Work.FunctionalEquations.DensityAux
