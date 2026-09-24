import Mathlib
import Submission.Work.GM.S3.Base

open Complex Finset
open scoped BigOperators

namespace Work.GM.S3

/-- The exponential `e^{iτt}` appearing in the statement: `efun τ t = exp(I * (t*τ))`. -/
private noncomputable def efun (τ t : ℝ) : ℂ := Complex.exp (Complex.I * ((t * τ : ℝ) : ℂ))

private lemma efun_add (τ : ℝ) (x y : ℝ) : efun τ x * efun τ y = efun τ (x + y) := by
  unfold efun
  rw [← Complex.exp_add]; congr 1; push_cast; ring

private lemma efun_star (τ : ℝ) (x : ℝ) : star (efun τ x) = efun τ (-x) := by
  unfold efun
  rw [Complex.star_def, ← Complex.exp_conj]; congr 1
  rw [map_mul, Complex.conj_I, Complex.conj_ofReal]; push_cast; ring

/-- The per-term identity `e^{iτa} e^{iτb} conj(e^{iτc}) conj(e^{iτd}) = e^{iτ(a+b-c-d)}`. -/
private lemma efun_quad (τ : ℝ) (a b c d : ℝ) :
    efun τ a * efun τ b * star (efun τ c) * star (efun τ d) = efun τ (a + b - c - d) := by
  rw [efun_star, efun_star, efun_add, efun_add, efun_add]
  congr 1

/-- The same identity, in the parenthesisation produced by expanding a product of two
double sums: `e^{iτ(a+b-c-d)} = (e^{iτa} e^{iτb}) (conj(e^{iτc}) conj(e^{iτd}))`. -/
private lemma efun_quad' (τ : ℝ) (a b c d : ℝ) :
    efun τ (a + b - c - d) = (efun τ a * efun τ b) * (star (efun τ c) * star (efun τ d)) := by
  rw [← efun_quad]; ring

/-- Bridge between the coercion form appearing in the statement and `efun`. -/
private lemma exp_I_mul_eq (τ x : ℝ) :
    Complex.exp (Complex.I * ((x : ℂ) * (τ : ℂ))) = efun τ x := by
  rw [efun, Complex.ofReal_mul]

/-- Expansion of the product of two double sums as a four-fold sum. -/
private lemma sum2_mul_sum2 (W : Finset ℝ) (X Y : ℝ → ℝ → ℂ) :
    (∑ a ∈ W, ∑ b ∈ W, X a b) * (∑ c ∈ W, ∑ d ∈ W, Y c d)
      = ∑ a ∈ W, ∑ b ∈ W, ∑ c ∈ W, ∑ d ∈ W, X a b * Y c d := by
  rw [Finset.sum_mul]
  refine Finset.sum_congr rfl fun a ha => ?_
  rw [Finset.sum_mul_sum]
  exact Finset.sum_congr rfl (fun b hb => Finset.sum_congr rfl (fun c hc =>
    Finset.mul_sum W (fun d => Y c d) (X a b)))

/-- The exact expansion of `‖Σ_{t∈W} e^{iτt}‖^4` as the sum of `e^{iτ(t₁+t₂-t₃-t₄)}` over
quadruples, stated as an identity in `ℂ` (it also shows the left side is a nonnegative real). -/
theorem l4_expansion (W : Finset ℝ) (τ : ℝ) :
    ((‖∑ t ∈ W, Complex.exp (Complex.I * ((t * τ : ℝ) : ℂ))‖ ^ 4 : ℝ) : ℂ)
      = ∑ q ∈ W ×ˢ W ×ˢ W ×ˢ W,
          Complex.exp (Complex.I * ((q.1 + q.2.1 - q.2.2.1 - q.2.2.2 : ℝ) * τ)) := by
  change ((‖∑ t ∈ W, efun τ t‖ ^ 4 : ℝ) : ℂ)
      = ∑ q ∈ W ×ˢ W ×ˢ W ×ˢ W,
          Complex.exp (Complex.I * ((q.1 + q.2.1 - q.2.2.1 - q.2.2.2 : ℝ) * τ))
  have hcongr : ∀ q ∈ W ×ˢ W ×ˢ W ×ˢ W,
      Complex.exp (Complex.I * ((q.1 + q.2.1 - q.2.2.1 - q.2.2.2 : ℝ) * τ))
        = (efun τ q.1 * efun τ q.2.1) * (star (efun τ q.2.2.1) * star (efun τ q.2.2.2)) := by
    intro q hq
    rw [exp_I_mul_eq τ]
    exact efun_quad' τ q.1 q.2.1 q.2.2.1 q.2.2.2
  have hRHS : (∑ q ∈ W ×ˢ W ×ˢ W ×ˢ W,
        Complex.exp (Complex.I * ((q.1 + q.2.1 - q.2.2.1 - q.2.2.2 : ℝ) * τ)))
      = ∑ a ∈ W, ∑ b ∈ W, ∑ c ∈ W, ∑ d ∈ W,
          (efun τ a * efun τ b) * (star (efun τ c) * star (efun τ d)) := by
    rw [Finset.sum_congr rfl hcongr]
    simp only [Finset.sum_product]
  have hS : (∑ t ∈ W, efun τ t) * (∑ t ∈ W, efun τ t)
      = ∑ a ∈ W, ∑ b ∈ W, efun τ a * efun τ b := by
    rw [Finset.sum_mul_sum]
  have hT : star (∑ t ∈ W, efun τ t) * star (∑ t ∈ W, efun τ t)
      = ∑ c ∈ W, ∑ d ∈ W, star (efun τ c) * star (efun τ d) := by
    rw [star_sum, Finset.sum_mul_sum]
  have hL : ((‖∑ t ∈ W, efun τ t‖ ^ 4 : ℝ) : ℂ)
      = ((∑ t ∈ W, efun τ t) * star (∑ t ∈ W, efun τ t)) ^ 2 := by
    have hcast : ((‖∑ t ∈ W, efun τ t‖ ^ 2 : ℝ) : ℂ)
        = (∑ t ∈ W, efun τ t) * star (∑ t ∈ W, efun τ t) := by
      rw [Complex.star_def, ← Complex.normSq_eq_norm_sq, ← Complex.mul_conj]
    rw [show ‖∑ t ∈ W, efun τ t‖ ^ 4 = (‖∑ t ∈ W, efun τ t‖ ^ 2) ^ 2 by ring,
      Complex.ofReal_pow, hcast]
  have hSS : ((∑ t ∈ W, efun τ t) * star (∑ t ∈ W, efun τ t)) ^ 2
      = ∑ a ∈ W, ∑ b ∈ W, ∑ c ∈ W, ∑ d ∈ W,
          (efun τ a * efun τ b) * (star (efun τ c) * star (efun τ d)) := by
    calc ((∑ t ∈ W, efun τ t) * star (∑ t ∈ W, efun τ t)) ^ 2
        = ((∑ t ∈ W, efun τ t) * (∑ t ∈ W, efun τ t))
          * (star (∑ t ∈ W, efun τ t) * star (∑ t ∈ W, efun τ t)) := by ring
      _ = (∑ a ∈ W, ∑ b ∈ W, efun τ a * efun τ b)
          * (∑ c ∈ W, ∑ d ∈ W, star (efun τ c) * star (efun τ d)) := by rw [hS, hT]
      _ = ∑ a ∈ W, ∑ b ∈ W, ∑ c ∈ W, ∑ d ∈ W,
            (efun τ a * efun τ b) * (star (efun τ c) * star (efun τ d)) := by
            rw [sum2_mul_sum2]
  rw [hL, hSS, ← hRHS]

end Work.GM.S3
