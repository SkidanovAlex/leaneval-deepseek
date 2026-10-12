import Mathlib.Analysis.InnerProductSpace.PiL2
import Mathlib.Algebra.Order.Star.Real
import Submission.Work.BoseB7AK.K15R.card_le_of_vec_norm_le
-- PORT435-BEGIN (v4.35 isDefEq respectTransparency compat)
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- PORT435-END

/-!
# `Work.BoseB7AK.K15R.annulus_sum_bound` — one dyadic annulus of the momentum sum

The lattice sum `∑_{n ∈ S} (1 + ‖vec n‖²)^{-s}` is estimated by counting: inside
the annulus `(2^k)R ≤ ‖vec n‖ ≤ 2^{k+1}R` there are at most `(2^{k+1}R/π + 1)³`
indices (`card_le_of_vec_norm_le`), and each term is at most
`(((2^k)R)²)^{-s}`, because on the annulus `1 + ‖vec n‖² ≥ ‖vec n‖² ≥ ((2^k)R)²`
and `x ↦ (x^s)^{-1}` is antitone on the positive reals.  Multiplying the two
bounds gives the claim.  This is the per-annulus step of the dyadic
decomposition of the box's momentum sums (FS §10), and it is where the
`(ρ/π+1)³` volume factor meets the `R^{-2s}` decay.
-/

noncomputable section

open scoped BigOperators

namespace Work.BoseB7AK.K15R

theorem annulus_sum_bound (s k : ℕ) (R : ℝ) (S : Finset (Fin 3 → ℤ)) (hR : 1 ≤ R)
    (hlo : ∀ n ∈ S, (2:ℝ)^k * R ≤ ‖Work.BoseB4.vec n‖)
    (hhi : ∀ n ∈ S, ‖Work.BoseB4.vec n‖ ≤ (2:ℝ)^(k+1) * R) :
    (∑ n ∈ S, (((1 : ℝ) + ‖Work.BoseB4.vec n‖ ^ 2) ^ s)⁻¹)
      ≤ (((2:ℝ)^(k+1) * R / Real.pi + 1) ^ 3) * ((((2:ℝ)^k * R) ^ 2) ^ s)⁻¹ := by
  have hRpos : 0 < R := lt_of_lt_of_le one_pos hR
  have hb : 0 < (2:ℝ)^k * R := by positivity
  have hb2 : 0 < ((2:ℝ)^k * R) ^ 2 := by positivity
  have hρ : 0 ≤ (2:ℝ)^(k+1) * R := by positivity
  -- the annulus contains at most `(ρ/π+1)³` lattice points
  have hcard := card_le_of_vec_norm_le S ((2:ℝ)^(k+1) * R) hρ hhi
  -- each summand is at most the value at the inner radius
  have hterm : ∀ n ∈ S, (((1:ℝ) + ‖Work.BoseB4.vec n‖ ^ 2) ^ s)⁻¹
      ≤ ((((2:ℝ)^k * R) ^ 2) ^ s)⁻¹ := by
    intro n hn
    have h1 : (2:ℝ)^k * R ≤ ‖Work.BoseB4.vec n‖ := hlo n hn
    have hsq : (((2:ℝ)^k * R) ^ 2) ≤ (1:ℝ) + ‖Work.BoseB4.vec n‖ ^ 2 := by
      have h := pow_le_pow_left₀ (le_of_lt hb) h1 2
      have hnn := sq_nonneg ‖Work.BoseB4.vec n‖
      linarith
    have hpow : ((((2:ℝ)^k * R) ^ 2) ^ s) ≤ (((1:ℝ) + ‖Work.BoseB4.vec n‖ ^ 2) ^ s) :=
      pow_le_pow_left₀ (le_of_lt hb2) hsq s
    calc (((1:ℝ) + ‖Work.BoseB4.vec n‖ ^ 2) ^ s)⁻¹
        = 1 / ((1:ℝ) + ‖Work.BoseB4.vec n‖ ^ 2) ^ s := by rw [one_div]
      _ ≤ 1 / ((((2:ℝ)^k * R) ^ 2) ^ s) :=
          one_div_le_one_div_of_le (pow_pos hb2 s) hpow
      _ = ((((2:ℝ)^k * R) ^ 2) ^ s)⁻¹ := by rw [one_div]
  calc (∑ n ∈ S, (((1:ℝ) + ‖Work.BoseB4.vec n‖ ^ 2) ^ s)⁻¹)
      ≤ ∑ n ∈ S, ((((2:ℝ)^k * R) ^ 2) ^ s)⁻¹ := Finset.sum_le_sum hterm
    _ = (S.card : ℝ) * ((((2:ℝ)^k * R) ^ 2) ^ s)⁻¹ := by
        rw [Finset.sum_const, nsmul_eq_mul]
    _ ≤ (((2:ℝ)^(k+1) * R / Real.pi + 1) ^ 3) * ((((2:ℝ)^k * R) ^ 2) ^ s)⁻¹ :=
        mul_le_mul_of_nonneg_right hcard (by positivity)

end Work.BoseB7AK.K15R
