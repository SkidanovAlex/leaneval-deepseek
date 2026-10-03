import Mathlib
import Submission.Work.FIArea6Hecke.R.ConductorThetaDefs
import Submission.Work.FIArea5.S16.summable_int_prod_exp_neg_sq_add

namespace Work.FIArea6Hecke

/-- Norm of one factor `n^a · e^{-πu n²}` of the all-`z` theta summand, as a real number:
`‖(n:ℂ)^a · exp(-πu n²)‖ = |n|^a · exp(-(πu) n²)`. -/
private lemma norm_pow_mul_exp_neg_sq (u : ℝ) (a : ℕ) (n : ℤ) :
    ‖((n : ℂ) ^ a) * Complex.exp (-Real.pi * u * ((n : ℂ) ^ 2))‖
      = |(n : ℝ)| ^ a * Real.exp (-(Real.pi * u) * (n : ℝ) ^ 2) := by
  rw [norm_mul, Complex.norm_exp, norm_pow, Complex.norm_intCast]
  have h : (-Real.pi * u * ((n : ℂ) ^ 2)) = (((-(Real.pi * u) * (n : ℝ) ^ 2) : ℝ) : ℂ) := by
    push_cast; ring
  rw [h, Complex.ofReal_re]

theorem allZSummable (M : GaussianInt) (chi₀ : GaussianInt → ℂ)
    (hchi : Work.FIArea6Hecke.R.IsCharModStrict M chi₀) {u : ℝ} (hu : 0 < u) (a b : ℕ) :
    Summable (fun p : ℤ × ℤ => chi₀ (⟨p.1, p.2⟩ : GaussianInt) *
      ((((p.1 : ℂ) ^ a) * Complex.exp (-Real.pi * u * ((p.1 : ℂ) ^ 2)))
        * (((p.2 : ℂ) ^ b) * Complex.exp (-Real.pi * u * ((p.2 : ℂ) ^ 2))))) := by
  have hpu : 0 < Real.pi * u := by positivity
  -- The two one-dimensional Gaussian majorants are summable.
  have hg : Summable (fun n : ℤ => |(n : ℝ)| ^ a * Real.exp (-(Real.pi * u) * (n : ℝ) ^ 2)) :=
    Work.FIArea5.S16.summable_int_abs_pow_mul_exp_neg_sq hpu a
  have hg2 : Summable (fun n : ℤ => |(n : ℝ)| ^ b * Real.exp (-(Real.pi * u) * (n : ℝ) ^ 2)) :=
    Work.FIArea5.S16.summable_int_abs_pow_mul_exp_neg_sq hpu b
  -- Their outer product over `ℤ × ℤ` is summable.
  refine Summable.of_norm_bounded
    (hg.mul_of_nonneg hg2 (fun _ => by positivity) (fun _ => by positivity)) (fun p => ?_)
  have hz : ‖chi₀ (⟨p.1, p.2⟩ : GaussianInt)‖ ≤ 1 := hchi.2.2.1 _
  rw [norm_mul, norm_mul, norm_pow_mul_exp_neg_sq, norm_pow_mul_exp_neg_sq]
  calc ‖chi₀ (⟨p.1, p.2⟩ : GaussianInt)‖ *
        (|(p.1 : ℝ)| ^ a * Real.exp (-(Real.pi * u) * (p.1 : ℝ) ^ 2) *
          (|(p.2 : ℝ)| ^ b * Real.exp (-(Real.pi * u) * (p.2 : ℝ) ^ 2)))
      ≤ 1 * (|(p.1 : ℝ)| ^ a * Real.exp (-(Real.pi * u) * (p.1 : ℝ) ^ 2) *
          (|(p.2 : ℝ)| ^ b * Real.exp (-(Real.pi * u) * (p.2 : ℝ) ^ 2))) := by
        apply mul_le_mul_of_nonneg_right hz; positivity
    _ = _ := one_mul _

end Work.FIArea6Hecke
