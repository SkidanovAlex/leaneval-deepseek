/-
# `FIArea2/R6/Area6eDefs.lean` — the §9 error sum of the round-6 area-2 assembly

This tiny module names the intermediate quantity of `area2_6e_A`: the per-pair (9.1) right-hand
side summed over the coprime pairs of the box, with the (9.2) weight `Haver` kept, the round-6
coefficient bound `‖β z‖ ≤ Pa.τ`, and the prefactor `√M` of Lemma 7.1 pulled out:

  `sec9ErrSum6 Pa β
     = √M · Σ_{(z₁,z₂) ∈ B²} ‖β_{z₁}β_{z₂}‖·|z₁z₂|^{-1/2}·τ(Δ)³|Δ|^{-1}·log(2+1/(1-γ²))·H(z₁,z₂)`.

It is the round-6 analogue of `Work.FIArea2.sec9ErrSum` (with the *sector-scale* axis threshold
`Work.FITop4.IsAxisFree`, the general derivative constant `Cder6` of the round-6 majorant and the
extra `τ(Δ)³` weight already sitting inside `sec9Core6`).  The §9 aggregate
(`sec9Psum_le_of_Lsum_six`) bounds it by `Cb·ϑ⁻¹τ²N²(log N)^{bFun η}`.

The auxiliary `bFun_ge_5000` records that the exponent `bFun η` of (9.10) dominates the
`log`-power produced by the §9 aggregation, for every `η ∈ (0,3/32)`.
-/
import Mathlib
import Submission.Work.FIArea2.R6.SixDefs
import Submission.Work.FITop4.Defs6

set_option autoImplicit false

namespace Work.FIArea2.R6

open Finset
open scoped BigOperators

attribute [local instance] Classical.propDecidable

noncomputable section

/-- The §9 corrector sum of the round-6 area-2 assembly: the per-pair (9.1) right-hand side,
summed over the coprime pairs of the box, with `√M` pulled out.

`Haver` is the (9.2) weight, `τ(Δ)³|Δ|^{-1}` the §9 pair weight, `log(2+1/(1-γ²))` the (7.1)
logarithmic factor and `|z₁z₂|^{-1/2} = gnorm(z₁z₂)^{-1/4}`. -/
def sec9ErrSum6 (Pa : Work.FITop.Params) (β : GaussianInt → ℂ) : ℝ :=
  Real.sqrt Pa.M *
    ∑ z1 ∈ Work.FITop.boxN Pa, ∑ z2 ∈ Work.FITop.boxN Pa,
      (if Work.FIPlan.GaussCoprime z1 z2 then
        ‖β z1‖ * ‖β z2‖ * (((Work.FIPlan.gnorm (z1 * z2) : ℕ) : ℝ) ^ (-(1 : ℝ) / 4))
          * ((((Work.FIPlan.absDelta z1 z2).divisors.card : ℝ) ^ 3)
              / ((Work.FIPlan.absDelta z1 z2 : ℕ) : ℝ)
              * Real.log (2 + 1 / (1 - (Work.FIArea2.gamOf z1 z2) ^ 2))
              * Work.FIArea2.Haver Pa z1 z2)
      else 0)

/-- For `η ∈ (0, 3/32)`, `bFun η ≥ 5000` — comfortably above the log-power produced by the §9
aggregation.  (`η⁻¹ > 32/3 > 10`, so `η⁻¹ log η⁻¹ > 10·2 = 20` and
`bFun η ≥ 2^{η⁻¹log η⁻¹+4} ≥ 2^{13} = 8192`.) -/
lemma bFun_ge_5000 (η : ℝ) (h0 : 0 < η) (h1 : η < 3 / 32) : 5000 ≤ Work.FITop4.bFun η := by
  have hη32 : (32 / 3 : ℝ) < η⁻¹ := by
    rw [inv_eq_one_div, lt_div_iff₀ h0]
    nlinarith [h1]
  have ht10 : (10 : ℝ) < η⁻¹ := by linarith
  have htpos : 0 < η⁻¹ := by linarith
  have hlog10 : (2 : ℝ) < Real.log 10 := by
    rw [Real.lt_log_iff_exp_lt (by norm_num)]
    have h3 : Real.exp 2 = Real.exp 1 * Real.exp 1 := by rw [← Real.exp_add]; norm_num
    have h1' : Real.exp 1 < 3 := Real.exp_one_lt_three
    have h10 : Real.exp 2 < 10 := by rw [h3]; nlinarith [Real.exp_pos 1]
    exact h10
  have hlogt : Real.log 10 ≤ Real.log η⁻¹ := Real.log_le_log (by norm_num) ht10.le
  have hlogt2 : (2 : ℝ) ≤ Real.log η⁻¹ := le_of_lt (lt_of_lt_of_le hlog10 hlogt)
  have hprod : (20 : ℝ) < η⁻¹ * Real.log η⁻¹ := by
    have h1'' : (10 : ℝ) * 2 < η⁻¹ * Real.log η⁻¹ :=
      mul_lt_mul ht10 hlogt2 (by norm_num) htpos.le
    linarith
  have hexp : (13 : ℝ) ≤ η⁻¹ * Real.log η⁻¹ + 4 := by linarith
  have hpow : (2 : ℝ) ^ (13 : ℕ) ≤ (2 : ℝ) ^ (η⁻¹ * Real.log η⁻¹ + 4) := by
    rw [← Real.rpow_natCast]
    exact Real.rpow_le_rpow_of_exponent_le (by norm_num) hexp
  have h2t : (0 : ℝ) < (2 : ℝ) ^ (η⁻¹ * Real.log η⁻¹ + 1) := Real.rpow_pos_of_pos (by norm_num) _
  have hb : Work.FITop4.bFun η
      = (2 : ℝ) ^ (η⁻¹ * Real.log η⁻¹ + 4)
        + (2 : ℝ) ^ (η⁻¹ * Real.log η⁻¹ + 1) + 4 := rfl
  rw [hb]
  have h8192 : (2 : ℝ) ^ (13 : ℕ) = 8192 := by norm_num
  nlinarith [hpow, h2t, h8192]

end

end Work.FIArea2.R6
