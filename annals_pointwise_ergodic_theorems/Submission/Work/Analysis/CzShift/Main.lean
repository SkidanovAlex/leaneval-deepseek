/-
Copyright (c) 2026. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import Mathlib
import Submission.Work.Analysis.CzShift.cz_shift_lp_of_l2
import Submission.Work.Analysis.CzShift.l2_bound_shiftKernelFam
import Submission.Commons.Analysis.Walsh.exists_khintchine_hilbert

/-!
# Shifted Calderón–Zygmund estimates (Theorem `cz-shift` of Krause–Mirek–Tao, Appendix B)

The main results of this chapter are, for a finite `λ`-lacunary family of scales `σ i` with
shifts `|t i| ≤ 2^K` and a rescaled kernel `Ψ` (`IsCZSeed Ψ Ψ' B`):

* `Work.Analysis.CzShift.cz_shift_lp` : for `1 < p < ∞` the convolution operators
  `T_ε = ∑_{i ∈ D} ε i • (K_i ⋆ ·)` (the operator with symbol `∑ ε_i φ_i`) satisfy
  `‖T_ε f‖_{L^p} ≲ K ‖f‖_{L^p}`, uniformly over `‖ε i‖ ≤ 1`;
* `Work.Analysis.CzShift.cz_shift_square_function` : the square function
  `x ↦ (∑_{i ∈ D} ‖K_i ⋆ f (x)‖²)^{1/2}` satisfies the same estimate.

Both are proved conditionally on the analytic content of the paper's hypotheses on the symbol
`ψ = 𝓕Ψ`: support in `[-C,C]` and `‖ψ ξ‖ ≤ C min 1 |ξ|` (the latter is what the paper's bounds
`|ψ^{(j)}| ≤ C` together with `ψ(0) = 0` give, see
`Work.Analysis.CzShift.multiplier_bound_of_deriv`).  Constants are uniform in the lacunary
family, the shifts and `ε`, and depend only on `λ`, `B`, `C`, `p`.
-/

namespace Work.Analysis.CzShift

open MeasureTheory
open scoped ENNReal

set_option autoImplicit false

variable {ι : Type*}

/-- **The shifted Calderón–Zygmund `L^p` estimate** (Theorem `cz-shift` (i) of
Krause–Mirek–Tao, Appendix B), with the paper's hypotheses on the symbol `ψ = 𝓕Ψ` of the
rescaled kernel: `ψ` is supported in `[-C,C]` and satisfies `‖ψ ξ‖ ≤ C min 1 |ξ|` (in particular
`ψ 0 = 0`).

For every `1 < p < ∞`, `‖∑_{i ∈ D} ε i • (K_i ⋆ f)‖_{L^p} ≲ K ‖f‖_{L^p}` uniformly over the
signs `‖ε i‖ ≤ 1`, the lacunary family `σ` and the shifts `|t i| ≤ 2^K`; the constant is
`C₀ (B (1+K) + 1)` with `C₀` depending only on `λ`, `C`, `B`, `p`. -/
theorem cz_shift_lp (lam B C : ℝ) (hlam : 1 < lam) (hB : 1 ≤ B) (hC : 0 < C)
    {p : ℝ} (hp : 1 < p) :
    ∃ C₀ : ℝ, 0 < C₀ ∧ ∀ {ι : Type} {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H]
      [CompleteSpace H] (D : Finset ι) (σ t : ι → ℝ) (Ψ Ψ' : ℝ → ℝ) (K : ℝ)
      (hlac : LacunaryFam lam D σ) (hseed : IsCZSeed Ψ Ψ' B) (hK : 1 ≤ K)
      (ht : ∀ i ∈ D, |t i| ≤ 2 ^ K)
      (hψsupp : ∀ ξ : ℝ, C < |ξ| →
        FourierTransform.fourier (fun u => (Ψ u : ℂ)) ξ = 0)
      (hψbd : ∀ ξ : ℝ,
        ‖FourierTransform.fourier (fun u => (Ψ u : ℂ)) ξ‖ ≤ C * min 1 |ξ|),
      ∀ (ε : ι → ℂ), (∀ i ∈ D, ‖ε i‖ ≤ 1) → ∀ f : ℝ → H, MeasureTheory.Integrable f →
        MeasureTheory.MemLp f (ENNReal.ofReal p) MeasureTheory.volume →
        MeasureTheory.eLpNorm (czOp D (shiftKernelFam Ψ σ t) ε f) (ENNReal.ofReal p)
            MeasureTheory.volume
          ≤ ENNReal.ofReal (C₀ * (B * (1 + K) + 1))
              * MeasureTheory.eLpNorm f (ENNReal.ofReal p) MeasureTheory.volume := by
  obtain ⟨Cm, hCmpos, hCm⟩ := l2_bound_shiftKernelFam lam C hlam hC
  obtain ⟨C₁, hC₁pos, hC₁⟩ := cz_shift_lp_of_l2 lam B Cm hlam hB hCmpos.le hp
  refine ⟨C₁, hC₁pos, ?_⟩
  intro ι H _ _ _ D σ t Ψ Ψ' K hlac hseed hK ht hψsupp hψbd ε hε f hfint hfLp
  exact hC₁ D σ t Ψ Ψ' K hlac hseed hK ht
    (fun ε' hε' g hg hg2 => hCm D σ t Ψ Ψ' B ε' hlac hseed hε' hψsupp hψbd g hg hg2)
    ε hε f hfint hfLp

end Work.Analysis.CzShift
