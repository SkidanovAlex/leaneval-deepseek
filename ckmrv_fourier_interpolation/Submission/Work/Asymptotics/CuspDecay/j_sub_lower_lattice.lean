import Mathlib
import Submission.Work.Kernels.Kernels
import Submission.Work.Asymptotics.CuspDecay.PsiDefs
import Submission.Work.Asymptotics.CuspDecay.PsiBounds
import Submission.Work.Asymptotics.CuspDecay.PsiLipschitz
import Submission.Work.Asymptotics.CuspDecay.norm_one_sub_expm_ge_third

namespace Work.Asymptotics.CuspDecay

open UpperHalfPlane
open scoped Manifold

/-- **The `j`-difference dominates the lattice distance divided by `‖q σ‖`.**

With `σ` on the imaginary axis (in the application `σ = S•z = -1/z` for `z = it`, so
`σ.im = 1/t ≥ 1`) and `k : ℤ` the nearest integer to `τ.re`, the difference `j τ - j σ`
dominates `‖τ - (σ+k)‖ / ‖q σ‖`, where `q u = Work.Kernels.qParamFun u = e^{2πiu}`.
Equivalently `‖D₁(τ,z)‖ ≥ c·ε·‖τ - (σ+k)‖` for `D₁ = Δ(τ)Δ(σ)(j τ - j z)` (`DOne_eq'`), which
is what makes the vanishing of the numerator `N₁` cancel the vanishing of `D₁` at the
coincidence lattice `σ + ℤ` (the only lattice points that can approach the region
`{|Re τ| < 1, 2 ≤ Im τ}`).

Route.  Put `Ψ u := Work.Kernels.qParamFun u * Work.Kernels.jInvariantFun u` (so
`j u = Ψ u / q u`), `w := τ - σ - k` and `c := σ + k ∈ ℍ`.  Since `j` and `q` are
`T`-periodic, `Ψ c = Ψ σ` and `j σ = j c`, and the exact identity
  `q σ · (j τ - j σ) = Ψ τ · (e^{-2πiw} - 1) + (Ψ τ - Ψ c)`
holds (the `q`-ratio `q σ / q τ = e^{-2πiw}` because `k ∈ ℤ`).  Then
* `‖Ψ τ - Ψ c‖ ≤ (1/8)‖w‖` (`Psi_lipschitz_eighth`, from `D Ψ = E₄²(q/Δ)(E₄ - E₆) = O(q)`);
* `‖Ψ τ‖ ≥ 3/4` (`Psi_sub_one_le_quarter`);
* `‖e^{-2πiw} - 1‖ ≥ (1/3)‖w‖` (`norm_one_sub_expm_ge_third`);
so `‖q σ‖ ‖j τ - j σ‖ ≥ (3/4)(1/3)‖w‖ - (1/8)‖w‖ = (1/8)‖w‖`, which is the claim with
`c = 1/8`. -/
theorem j_sub_lower_lattice :
    ∃ c : ℝ, 0 < c ∧ ∀ (τ σ : UpperHalfPlane) (k : ℤ), σ.re = 0 → 2 ≤ σ.im → 2 ≤ τ.im →
      |τ.re - (k : ℝ)| ≤ 1 / 2 → ‖(τ : ℂ) - (σ : ℂ) - (k : ℂ)‖ ≤ 2 →
      c * (‖(τ : ℂ) - (σ : ℂ) - (k : ℂ)‖ / ‖Work.Kernels.qParamFun σ‖)
        ≤ ‖Work.Kernels.jInvariantFun τ - Work.Kernels.jInvariantFun σ‖ := by
  refine ⟨1 / 8, by norm_num, ?_⟩
  intro τ σ k hσre hσim hτim hkre hkn
  set w : ℂ := (τ : ℂ) - (σ : ℂ) - (k : ℂ) with hw
  set c0 : UpperHalfPlane := (k : ℝ) +ᵥ σ with hc0
  have hc0coe : (c0 : ℂ) = (σ : ℂ) + (k : ℂ) := by
    rw [hc0, UpperHalfPlane.coe_vadd]; push_cast; ring
  have hc0im : 2 ≤ c0.im := by
    have hk0 : ((k : ℂ)).im = 0 := by simp
    rw [← UpperHalfPlane.coe_im, hc0coe, Complex.add_im, UpperHalfPlane.coe_im, hk0]
    simpa using hσim
  have hwr : |w.re| ≤ 1 / 2 := by
    have hrek : ((k : ℂ)).re = (k : ℝ) := by simp
    rw [hw]
    simp only [Complex.sub_re, UpperHalfPlane.coe_re, hrek, hσre, sub_zero]
    exact hkre
  have hwn : ‖w‖ ≤ 2 := by rw [hw]; exact hkn
  have hq_c0 : Work.Kernels.qParamFun c0 = Work.Kernels.qParamFun σ :=
    qParamFun_vadd_int k σ
  have hj_c0 : Work.Kernels.jInvariantFun c0 = Work.Kernels.jInvariantFun σ :=
    jInvariantFun_vadd_int k σ
  -- the `q`-ratio
  have hqratio : Work.Kernels.qParamFun σ / Work.Kernels.qParamFun τ
      = Complex.exp (-(2 * (Real.pi : ℂ) * Complex.I * w)) := by
    have hτ : (τ : ℂ) = (σ : ℂ) + (k : ℂ) + w := by rw [hw]; ring
    have h1 : Work.Kernels.qParamFun σ / Work.Kernels.qParamFun τ
        = Complex.exp (2 * (Real.pi : ℂ) * Complex.I * (σ : ℂ)
            - 2 * (Real.pi : ℂ) * Complex.I * (τ : ℂ)) := by
      rw [qParamFun_eq_exp, qParamFun_eq_exp, Complex.exp_sub]
    rw [h1, hτ]
    have harg : 2 * (Real.pi : ℂ) * Complex.I * (σ : ℂ)
        - 2 * (Real.pi : ℂ) * Complex.I * ((σ : ℂ) + (k : ℂ) + w)
        = -(2 * (Real.pi : ℂ) * Complex.I * w)
          + (((-k : ℤ)) : ℂ) * (2 * (Real.pi : ℂ) * Complex.I) := by
      push_cast
      ring
    rw [harg, Complex.exp_add, Complex.exp_int_mul_two_pi_mul_I, mul_one]
  -- the exact identity
  have hident : Work.Kernels.qParamFun σ
        * (Work.Kernels.jInvariantFun τ - Work.Kernels.jInvariantFun σ)
      = Psi τ * (Complex.exp (-(2 * (Real.pi : ℂ) * Complex.I * w)) - 1)
        + (Psi τ - Psi c0) := by
    have h1 : Work.Kernels.qParamFun σ * Work.Kernels.jInvariantFun τ
        = (Work.Kernels.qParamFun σ / Work.Kernels.qParamFun τ) * Psi τ := by
      rw [Psi_apply]; field_simp
    have h2 : Work.Kernels.qParamFun σ * Work.Kernels.jInvariantFun σ = Psi c0 := by
      rw [Psi_apply, hq_c0, hj_c0]
    rw [mul_sub, h1, h2, hqratio]
    ring
  -- the three estimates
  have hlip : ‖Psi τ - Psi c0‖ ≤ (1 / 8) * ‖w‖ := by
    have h := Psi_lipschitz_eighth τ c0 hτim hc0im
    have hdist : ‖(τ : ℂ) - (c0 : ℂ)‖ = ‖w‖ := by
      rw [hc0coe, hw]; congr 1; ring
    rwa [hdist] at h
  have hPsi_lb : (3 / 4 : ℝ) ≤ ‖Psi τ‖ := by
    have h := Psi_sub_one_le_quarter τ hτim
    have h2 := abs_norm_sub_norm_le (Psi τ) (1 : ℂ)
    rw [norm_one, abs_le] at h2
    linarith [h2.1]
  have hexp : (1 / 3) * ‖w‖
      ≤ ‖Complex.exp (-(2 * (Real.pi : ℂ) * Complex.I * w)) - 1‖ := by
    have h := norm_one_sub_expm_ge_third w hwr hwn
    have hrev : ‖Complex.exp (-(2 * (Real.pi : ℂ) * Complex.I * w)) - 1‖
        = ‖1 - Complex.exp (-(2 * (Real.pi : ℂ) * Complex.I * w))‖ := norm_sub_rev _ _
    rw [hrev]
    exact h
  -- assembly
  have hmain : (1 / 8) * ‖w‖
      ≤ ‖Work.Kernels.qParamFun σ‖ * ‖Work.Kernels.jInvariantFun τ
          - Work.Kernels.jInvariantFun σ‖ := by
    have hnorm : ‖Work.Kernels.qParamFun σ‖
          * ‖Work.Kernels.jInvariantFun τ - Work.Kernels.jInvariantFun σ‖
        = ‖Work.Kernels.qParamFun σ
            * (Work.Kernels.jInvariantFun τ - Work.Kernels.jInvariantFun σ)‖ := by
      rw [norm_mul]
    rw [hnorm]
    have hlt : ‖Psi τ * (Complex.exp (-(2 * (Real.pi : ℂ) * Complex.I * w)) - 1)‖
        = ‖Psi τ‖ * ‖Complex.exp (-(2 * (Real.pi : ℂ) * Complex.I * w)) - 1‖ := by
      rw [norm_mul]
    have hprodb : (3 / 4) * ((1 / 3) * ‖w‖)
        ≤ ‖Psi τ‖ * ‖Complex.exp (-(2 * (Real.pi : ℂ) * Complex.I * w)) - 1‖ :=
      mul_le_mul hPsi_lb hexp (by positivity) (by positivity)
    have hsplit : ‖Psi τ * (Complex.exp (-(2 * (Real.pi : ℂ) * Complex.I * w)) - 1)‖
          - ‖Psi τ - Psi c0‖
        ≤ ‖Psi τ * (Complex.exp (-(2 * (Real.pi : ℂ) * Complex.I * w)) - 1)
            + (Psi τ - Psi c0)‖ := by
      have h2 := norm_add_le
        (Psi τ * (Complex.exp (-(2 * (Real.pi : ℂ) * Complex.I * w)) - 1)
          + (Psi τ - Psi c0)) (-(Psi τ - Psi c0))
      have h3 : (Psi τ * (Complex.exp (-(2 * (Real.pi : ℂ) * Complex.I * w)) - 1)
          + (Psi τ - Psi c0)) + -(Psi τ - Psi c0)
          = Psi τ * (Complex.exp (-(2 * (Real.pi : ℂ) * Complex.I * w)) - 1) := by ring
      rw [h3, norm_neg] at h2
      linarith
    rw [hident]
    calc (1 / 8) * ‖w‖
        = (3 / 4) * ((1 / 3) * ‖w‖) - (1 / 8) * ‖w‖ := by ring
      _ ≤ ‖Psi τ‖ * ‖Complex.exp (-(2 * (Real.pi : ℂ) * Complex.I * w)) - 1‖
            - ‖Psi τ - Psi c0‖ := by linarith
      _ = ‖Psi τ * (Complex.exp (-(2 * (Real.pi : ℂ) * Complex.I * w)) - 1)‖
            - ‖Psi τ - Psi c0‖ := by rw [hlt]
      _ ≤ _ := hsplit
  have hpos : 0 < ‖Work.Kernels.qParamFun σ‖ := by
    rw [norm_qParamFun_eq_exp]; exact Real.exp_pos _
  have hgoal : (1 / 8) * (‖w‖ / ‖Work.Kernels.qParamFun σ‖)
      ≤ ‖Work.Kernels.jInvariantFun τ - Work.Kernels.jInvariantFun σ‖ := by
    rw [← mul_div_assoc, div_le_iff₀ hpos]
    simpa [mul_comm] using hmain
  simpa [hw] using hgoal

end Work.Asymptotics.CuspDecay
