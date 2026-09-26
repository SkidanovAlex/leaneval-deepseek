import Mathlib

/-!
# The ratio estimate for `θ(z/2, z) / 2`

For `z` in the upper half plane we show that

`jacobiTheta₂ (z / 2) z / 2 = ∑_{n ∈ ℤ} exp (π i z (n ^ 2 + n)) / 2`

and that the two halves of this series over `ℤ` (the nonnegative and the strictly negative
integers) are *equal*, both being `∑_{k ≥ 0} exp (π i z (k ^ 2 + k))`.  Hence

`jacobiTheta₂ (z / 2) z / 2 - 1 = ∑_{k ≥ 1} exp (π i z (k ^ 2 + k))`.

Taking norms and comparing with the geometric series `∑_{k ≥ 1} r ^ k`, `r = exp (-2 π Im z)`
(note `k ^ 2 + k ≥ 2 k` for `k ≥ 1`) yields

`‖jacobiTheta₂ (z / 2) z / 2 - 1‖ ≤ r / (1 - r)`,
-/

open Complex Real
open scoped Topology

namespace Work.Kernels.LogLambda.ThetaLower

noncomputable section

/-- The `n`-th summand of the series `∑_{n ∈ ℤ} exp (π i z (n ^ 2 + n))`. -/
def thetaSummand (z : ℂ) (n : ℤ) : ℂ :=
  Complex.exp ((π : ℂ) * Complex.I * z * ((n : ℂ) ^ 2 + (n : ℂ)))

/-- The `k`-th summand of the series `∑_{k ≥ 0} exp (π i z (k ^ 2 + k))`. -/
def thetaPairSummand (z : ℂ) (k : ℕ) : ℂ :=
  Complex.exp ((π : ℂ) * Complex.I * z * ((k : ℂ) ^ 2 + (k : ℂ)))

lemma thetaSummand_ofNat (z : ℂ) (k : ℕ) : thetaSummand z (k : ℤ) = thetaPairSummand z k := by
  simp only [thetaSummand, thetaPairSummand, Int.cast_natCast]

lemma thetaSummand_negSucc (z : ℂ) (m : ℕ) :
    thetaSummand z (-((m : ℤ) + 1)) = thetaPairSummand z m := by
  simp only [thetaSummand, thetaPairSummand]
  congr 1
  push_cast
  ring

/-- The summand of `jacobiTheta₂ (z/2) z` is the summand of `∑ exp (π i z (n ^ 2 + n))`. -/
lemma jacobiTheta₂_term_half (z : ℂ) (n : ℤ) :
    jacobiTheta₂_term n (z / 2) z = thetaSummand z n := by
  rw [jacobiTheta₂_term, thetaSummand]
  congr 1
  ring

lemma norm_thetaPairSummand (z : ℂ) (k : ℕ) :
    ‖thetaPairSummand z k‖ = Real.exp (-(π * z.im * ((k : ℝ) ^ 2 + (k : ℝ)))) := by
  rw [thetaPairSummand, Complex.norm_exp]
  congr 1
  rw [show (π : ℂ) * Complex.I * z * ((k : ℂ) ^ 2 + (k : ℂ)) =
      (((π * ((k : ℝ) ^ 2 + (k : ℝ))) : ℝ) : ℂ) * (Complex.I * z) by push_cast; ring]
  rw [Complex.re_ofReal_mul, Complex.I_mul_re]
  ring

/-- The main estimate. -/
theorem ratio_estimate (z : ℂ) (hz : 0 < z.im) :
    ‖jacobiTheta₂ (z / 2) z / 2 - 1‖
      ≤ Real.exp (-(2 * Real.pi * z.im)) / (1 - Real.exp (-(2 * Real.pi * z.im))) := by
  -- Summability of the theta series, and of the "pair" series `∑_k exp (π i z (k² + k))`.
  have hjac : Summable (fun n : ℤ => jacobiTheta₂_term n (z / 2) z) :=
    (summable_jacobiTheta₂_term_iff (z / 2) z).mpr hz
  have hu : Summable (thetaSummand z) := hjac.congr (fun n => jacobiTheta₂_term_half z n)
  have hw : Summable (thetaPairSummand z) :=
    (hu.comp_injective Nat.cast_injective).congr (fun k => thetaSummand_ofNat z k)
  have h1 : HasSum (fun k : ℕ => thetaSummand z (k : ℤ)) (∑' k : ℕ, thetaPairSummand z k) :=
    hw.hasSum.congr_fun (fun k => thetaSummand_ofNat z k)
  have h2 : HasSum (fun m : ℕ => thetaSummand z (-((m : ℤ) + 1))) (∑' k : ℕ, thetaPairSummand z k) :=
    hw.hasSum.congr_fun (fun m => thetaSummand_negSucc z m)
  have hsum_u : HasSum (thetaSummand z)
      ((∑' k : ℕ, thetaPairSummand z k) + (∑' k : ℕ, thetaPairSummand z k)) :=
    HasSum.of_nat_of_neg_add_one h1 h2
  have hU : (∑' n : ℤ, thetaSummand z n)
      = (∑' k : ℕ, thetaPairSummand z k) + (∑' k : ℕ, thetaPairSummand z k) := hsum_u.tsum_eq
  have hS : jacobiTheta₂ (z / 2) z / 2 = (∑' n : ℤ, thetaSummand z n) / 2 := by
    rw [jacobiTheta₂]
    congr 1
    exact tsum_congr (fun n => jacobiTheta₂_term_half z n)
  have hS2 : jacobiTheta₂ (z / 2) z / 2 = ∑' k : ℕ, thetaPairSummand z k := by
    rw [hS, hU]; ring
  have hpair_zero : thetaPairSummand z 0 = 1 := by simp [thetaPairSummand]
  have hsplit : (∑' k : ℕ, thetaPairSummand z k) = 1 + ∑' k : ℕ, thetaPairSummand z (k + 1) := by
    rw [hw.tsum_eq_zero_add, hpair_zero]
  have hkey : jacobiTheta₂ (z / 2) z / 2 - 1 = ∑' k : ℕ, thetaPairSummand z (k + 1) := by
    rw [hS2, hsplit]; ring
  -- The geometric comparison series.
  set r : ℝ := Real.exp (-(2 * Real.pi * z.im)) with hrdef
  have hr1 : r < 1 := by
    rw [hrdef, Real.exp_lt_one_iff]
    nlinarith [Real.pi_pos, hz]
  have hr0 : (0 : ℝ) ≤ r := le_of_lt (by rw [hrdef]; positivity)
  have hgeom : Summable (fun k : ℕ => r ^ (k + 1)) :=
    (summable_geometric_of_lt_one hr0 hr1).comp_injective Nat.succ_injective
  have hpt_eq : ∀ k : ℕ, ‖thetaPairSummand z (k + 1)‖
      = Real.exp (-(π * z.im * (((k : ℝ) + 1) ^ 2 + ((k : ℝ) + 1)))) := by
    intro k
    rw [norm_thetaPairSummand]
    congr 1
    push_cast
    ring
  have hbound : ∀ k : ℕ,
      Real.exp (-(π * z.im * (((k : ℝ) + 1) ^ 2 + ((k : ℝ) + 1)))) ≤ r ^ (k + 1) := by
    intro k
    rw [show ((k : ℝ) + 1) = ((k + 1 : ℕ) : ℝ) by push_cast; ring]
    set a : ℝ := ((k + 1 : ℕ) : ℝ) with hadef
    have ha1 : (1 : ℝ) ≤ a := by
      rw [hadef]
      exact_mod_cast Nat.succ_le_succ (Nat.zero_le k)
    have ha0 : (0 : ℝ) ≤ a := by linarith
    have hineq : 2 * a ≤ a ^ 2 + a := by
      nlinarith [mul_nonneg ha0 (by linarith : (0 : ℝ) ≤ a - 1)]
    have hpt : (0 : ℝ) ≤ π * z.im := by positivity
    rw [hrdef, ← Real.exp_nat_mul]
    apply Real.exp_le_exp.mpr
    nlinarith [hineq, hpt]
  have hsumm_exp : Summable (fun k : ℕ =>
      Real.exp (-(π * z.im * (((k : ℝ) + 1) ^ 2 + ((k : ℝ) + 1))))) :=
    Summable.of_nonneg_of_le (fun k => Real.exp_nonneg _) hbound hgeom
  have hnorm_summ : Summable (fun k : ℕ => ‖thetaPairSummand z (k + 1)‖) :=
    hsumm_exp.congr (fun k => (hpt_eq k).symm)
  have htsum_geom : (∑' k : ℕ, r ^ (k + 1)) = r / (1 - r) := by
    have h : HasSum (fun k : ℕ => r ^ (k + 1)) (r * (1 - r)⁻¹) :=
      (hasSum_geometric_of_lt_one hr0 hr1).mul_left r |>.congr_fun (fun k => by rw [pow_succ'])
    rw [div_eq_mul_inv]
    exact h.tsum_eq
  calc ‖jacobiTheta₂ (z / 2) z / 2 - 1‖
      = ‖∑' k : ℕ, thetaPairSummand z (k + 1)‖ := by rw [hkey]
    _ ≤ ∑' k : ℕ, ‖thetaPairSummand z (k + 1)‖ := norm_tsum_le_tsum_norm hnorm_summ
    _ = ∑' k : ℕ, Real.exp (-(π * z.im * (((k : ℝ) + 1) ^ 2 + ((k : ℝ) + 1)))) :=
        tsum_congr hpt_eq
    _ ≤ ∑' k : ℕ, r ^ (k + 1) := Summable.tsum_le_tsum hbound hsumm_exp hgeom
    _ = r / (1 - r) := htsum_geom
    _ = Real.exp (-(2 * Real.pi * z.im)) / (1 - Real.exp (-(2 * Real.pi * z.im))) := by
        rw [hrdef]

end

end Work.Kernels.LogLambda.ThetaLower
