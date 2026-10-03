import Mathlib
import Submission.Work.FIArea6T.Defs
import Submission.Work.FIArea6T.Support
import Submission.Work.FIArea6.pair_phi_helpers

namespace Work.FIArea6T

/-!
# `Work.FIArea6T.InnerSum_le` — the triangle bound for the inner `d`-sum of (10.13)

The inner sum of the (10.13) form `TcutBil`,

`Σ_{d ∈ Sset z₁ z₂} (φ(d)/d)·cut z₁ z₂ d·(z₂/z₁|d)·logFac6 z₁ z₂`,

is bounded in modulus by `PhiLocC z₁ z₂ · 4 log(2+N)` on the polar box.  This is completely
elementary: `Sset z₁ z₂` is exactly the index set of `PhiLocC` (the `(8.16)` range
`1 ≤ d ≤ |Δ|/4+1` cut by `4d ∣ |Δ|`), and each summand contributes at most
`(φ(d)/d)·1·1·4log(2+N)`, because

* `|cut z₁ z₂ d| ≤ 1` is the hypothesis `hcut`;
* `|(z₂/z₁|d)| ≤ 1` is `ratioSym_abs_le_one` (a Jacobi symbol);
* `|logFac6 z₁ z₂| ≤ 4 log(2+N)` is `logFac6_abs_le` ((7.10) on the box, where
  `|z₁|², |z₂|² ≤ (1+θ)N ≤ 2N`).

The bound is what makes `PhiLocC` the natural weight of the pair, balancing the trilinear
trilogy `(φ(d)/d)·(z₂/z₁|d)·logFac6` of (10.13); the sum over `z₁` is controlled separately.
-/

/-- The triangle bound for the inner `d`-sum of (10.13): each term carries at most the weight
`φ(d)/d` times the two unit bounds `|cut| ≤ 1`, `|(z₂/z₁|d)| ≤ 1` and the log factor
`4 log(2+N)`. -/
theorem InnerSum_le (Pa : Work.FITop.Params) (φ : ℝ)
    (cut : GaussianInt → GaussianInt → ℕ → ℝ)
    (hcut : ∀ z1 z2 d, |cut z1 z2 d| ≤ 1) (hθ : Pa.θ ≤ 1) (hN : 1 ≤ Pa.N)
    {z1 z2 : GaussianInt} (h1 : Work.FITop4.InPolarBox Pa φ z1)
    (h2 : Work.FITop4.InPolarBox Pa φ z2) :
    ‖(∑ d ∈ Work.FITop4.Sset z1 z2,
        ((Nat.totient d : ℝ) / (d : ℝ)) * cut z1 z2 d
          * (Work.FIArea7.ratioSym z1 z2 d : ℝ) * Work.FITop4.logFac6 z1 z2 : ℂ)‖
      ≤ Work.FIArea6.PhiLocC z1 z2 * (4 * Real.log (2 + Pa.N)) := by
  -- the `|z_i|²`-bounds of the polar box, at `2N` rather than `(1+θ)N`
  have hgn1 : ((Work.FIPlan.gnorm z1 : ℕ) : ℝ) ≤ 2 * (Pa.N : ℝ) := by
    have h := h1.2.2.1
    nlinarith [hθ]
  have hgn2 : ((Work.FIPlan.gnorm z2 : ℕ) : ℝ) ≤ 2 * (Pa.N : ℝ) := by
    have h := h2.2.2.1
    nlinarith [hθ]
  -- (7.10) on the polar box
  have hlog : |Work.FITop4.logFac6 z1 z2| ≤ 4 * Real.log (2 + (Pa.N : ℝ)) :=
    Work.FIArea6T.logFac6_abs_le Pa hN hgn1 hgn2
  -- `Sset` *is* the index set of `PhiLocC`
  have hphi : Work.FIArea6.PhiLocC z1 z2
      = ∑ d ∈ Work.FITop4.Sset z1 z2, ((Nat.totient d : ℝ) / (d : ℝ)) := rfl
  -- the pointwise triangle bound
  have hkey : ∀ d ∈ Work.FITop4.Sset z1 z2,
      ‖(((Nat.totient d : ℝ) / (d : ℝ)) * cut z1 z2 d
        * (Work.FIArea7.ratioSym z1 z2 d : ℝ) * Work.FITop4.logFac6 z1 z2 : ℂ)‖
      ≤ ((Nat.totient d : ℝ) / (d : ℝ)) * (4 * Real.log (2 + Pa.N)) := by
    intro d _
    have hA : 0 ≤ (Nat.totient d : ℝ) / (d : ℝ) :=
      div_nonneg (Nat.cast_nonneg _) (Nat.cast_nonneg _)
    have hB : |cut z1 z2 d| ≤ 1 := hcut z1 z2 d
    have hC : |(Work.FIArea7.ratioSym z1 z2 d : ℝ)| ≤ 1 :=
      Work.FIArea6T.ratioSym_abs_le_one z1 z2 d
    have hcast : (((Nat.totient d : ℝ) / (d : ℝ)) * cut z1 z2 d
        * (Work.FIArea7.ratioSym z1 z2 d : ℝ) * Work.FITop4.logFac6 z1 z2 : ℂ)
        = ((((Nat.totient d : ℝ) / (d : ℝ)) * cut z1 z2 d
        * (Work.FIArea7.ratioSym z1 z2 d : ℝ) * Work.FITop4.logFac6 z1 z2 : ℝ) : ℂ) := by
      push_cast; ring
    rw [hcast, Complex.norm_real, Real.norm_eq_abs]
    have hBC : |cut z1 z2 d| * |(Work.FIArea7.ratioSym z1 z2 d : ℝ)| ≤ 1 := by
      calc |cut z1 z2 d| * |(Work.FIArea7.ratioSym z1 z2 d : ℝ)| ≤ 1 * 1 :=
            mul_le_mul hB hC (abs_nonneg _) (by norm_num)
        _ = 1 := by ring
    rw [abs_mul, abs_mul, abs_mul, abs_of_nonneg hA]
    calc (Nat.totient d : ℝ) / (d : ℝ) * |cut z1 z2 d|
            * |(Work.FIArea7.ratioSym z1 z2 d : ℝ)| * |Work.FITop4.logFac6 z1 z2|
        = (Nat.totient d : ℝ) / (d : ℝ)
            * (|cut z1 z2 d| * |(Work.FIArea7.ratioSym z1 z2 d : ℝ)|)
            * |Work.FITop4.logFac6 z1 z2| := by ring
      _ ≤ (Nat.totient d : ℝ) / (d : ℝ) * 1 * (4 * Real.log (2 + Pa.N)) := by
          apply mul_le_mul
          · exact mul_le_mul_of_nonneg_left hBC hA
          · exact hlog
          · exact abs_nonneg _
          · exact mul_nonneg hA zero_le_one
      _ = (Nat.totient d : ℝ) / (d : ℝ) * (4 * Real.log (2 + Pa.N)) := by ring
  -- triangle inequality, then factor `PhiLocC` out of the sum
  calc ‖∑ d ∈ Work.FITop4.Sset z1 z2,
        (((Nat.totient d : ℝ) / (d : ℝ)) * cut z1 z2 d
          * (Work.FIArea7.ratioSym z1 z2 d : ℝ) * Work.FITop4.logFac6 z1 z2 : ℂ)‖
      ≤ ∑ d ∈ Work.FITop4.Sset z1 z2,
        ‖(((Nat.totient d : ℝ) / (d : ℝ)) * cut z1 z2 d
          * (Work.FIArea7.ratioSym z1 z2 d : ℝ) * Work.FITop4.logFac6 z1 z2 : ℂ)‖ :=
        norm_sum_le _ _
    _ ≤ ∑ d ∈ Work.FITop4.Sset z1 z2,
        ((Nat.totient d : ℝ) / (d : ℝ)) * (4 * Real.log (2 + Pa.N)) := Finset.sum_le_sum hkey
    _ = (∑ d ∈ Work.FITop4.Sset z1 z2, ((Nat.totient d : ℝ) / (d : ℝ)))
        * (4 * Real.log (2 + Pa.N)) := (Finset.sum_mul _ _ _).symm
    _ = Work.FIArea6.PhiLocC z1 z2 * (4 * Real.log (2 + Pa.N)) := by rw [hphi]

end Work.FIArea6T
