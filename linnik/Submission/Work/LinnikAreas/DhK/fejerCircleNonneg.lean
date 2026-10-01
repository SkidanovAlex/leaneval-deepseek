import Mathlib
import Submission.Work.LinnikAreas.DhK.TuranDefs
import Submission.Work.LinnikAreas.fejerSq

/-!
# Non-negativity of the Fejér kernel on the unit circle

The Fejér polynomial `Q J z = Σ_{j=1}^{J} (1 - j/(J+1)) Re(z^j)` satisfies
`1 + 2 Q J ζ ≥ 0` for every `ζ` on the unit circle `‖ζ‖ = 1`.  Indeed, writing
`ζ = exp (arg ζ · I)` (here `‖ζ‖ = 1`), we get `Re (ζ^j) = cos (j · arg ζ)`, so that
`1 + 2 Q J ζ = Kfun 1 (arg ζ) (J+1)`, the Fejér kernel at `r = 1`, which is `1/N` times a sum
of two squares and hence non-negative (`Work.LinnikAreas.fejerSq`).
-/

namespace Work.LinnikAreas.DhK

open scoped BigOperators

/-- On the unit circle, `Re (ζ ^ j) = cos (j * arg ζ)`; this is the polar decomposition
`ζ = exp (arg ζ * I)` together with `‖ζ‖ = 1`. -/
lemma re_pow_eq_cos_arg {ζ : ℂ} (hζ : ‖ζ‖ = 1) (j : ℕ) :
    (ζ ^ j).re = Real.cos ((j : ℝ) * Complex.arg ζ) := by
  have hE : (Complex.exp ((Complex.arg ζ : ℂ) * Complex.I)) ^ j
      = Complex.exp (((j : ℝ) * Complex.arg ζ : ℝ) * Complex.I) := by
    rw [← Complex.exp_nat_mul]; congr 1; push_cast; ring
  conv_lhs => rw [← Complex.norm_mul_exp_arg_mul_I ζ]
  rw [hζ, Complex.ofReal_one, one_mul, hE, Complex.exp_ofReal_mul_I_re]

/-- `fejerQ` on the unit circle, expressed through cosines of multiples of the argument. -/
lemma fejerQ_eq_cos_sum (J : ℕ) {ζ : ℂ} (hζ : ‖ζ‖ = 1) :
    fejerQ J ζ = ∑ j ∈ Finset.Icc 1 J,
      (1 - (j : ℝ) / ((J : ℝ) + 1)) * Real.cos ((j : ℝ) * Complex.arg ζ) := by
  unfold fejerQ fejerW
  refine Finset.sum_congr rfl fun j _ => ?_
  rw [re_pow_eq_cos_arg hζ j]

/-- The real Fejér kernel at `r = 1` and length `J + 1` is `1 + 2 Q J`. -/
lemma Kfun_one_eq (J : ℕ) (θ : ℝ) :
    Work.LinnikAreas.Kfun 1 θ (J + 1)
      = 1 + 2 * ∑ j ∈ Finset.Icc 1 J,
          (1 - (j : ℝ) / ((J : ℝ) + 1)) * Real.cos ((j : ℝ) * θ) := by
  have hden : ((J + 1 : ℕ) : ℝ) = (J : ℝ) + 1 := by push_cast; ring
  have hsum : (∑ x ∈ Finset.Icc 1 J, (1 - (x : ℝ) / ((J + 1 : ℕ) : ℝ))
        * Real.cos ((x : ℝ) * θ))
      = ∑ j ∈ Finset.Icc 1 J,
          (1 - (j : ℝ) / ((J : ℝ) + 1)) * Real.cos ((j : ℝ) * θ) := by
    refine Finset.sum_congr rfl fun j _ => ?_
    rw [hden]
  unfold Work.LinnikAreas.Kfun
  rw [Nat.add_sub_cancel]
  simp only [one_pow, mul_one]
  rw [hsum]

theorem fejerCircleNonneg (J : ℕ) (ζ : ℂ) (hζ : ‖ζ‖ = 1) :
    0 ≤ 1 + 2 * fejerQ J ζ := by
  have h := Work.LinnikAreas.fejerSq (J + 1) (by omega) (Complex.arg ζ)
  have hK : Work.LinnikAreas.Kfun 1 (Complex.arg ζ) (J + 1) = 1 + 2 * fejerQ J ζ := by
    rw [Kfun_one_eq J (Complex.arg ζ), fejerQ_eq_cos_sum J hζ]
  rwa [hK] at h

end Work.LinnikAreas.DhK
