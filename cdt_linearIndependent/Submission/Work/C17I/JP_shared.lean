import Mathlib

/-!
# Shared helpers for the `J_package` argument (area C17I)

Two small lemmas used both by the assembly of `Work.C17I.J_package` and by the lemmas proving the
value of `yQ^k · dyQ` at points of a set avoiding `0` and `1`:

* `Work.C17I.ratFunc_eval_eq_div`: if `r : RatFunc ℚ` is presented as `P/Q` (with `Q ≠ 0`) and
  `Q` does not vanish at `z : ℂ`, then the numerator-over-denominator expression defining
  `RatFunc.eval` equals `P(z)/Q(z)`;
* `Work.C17I.differentiableOn_eval₂`: `z ↦ p.eval₂ (algebraMap ℚ ℂ) z` is complex differentiable.
-/

namespace Work.C17I

open Polynomial

noncomputable section

/-- `num/denom` of a rational function evaluated at `z` against any quotient presentation `P/Q`
for which `Q` does not vanish at `z`. -/
theorem ratFunc_eval_eq_div {r : RatFunc ℚ} {P Q : Polynomial ℚ} (hQ : Q ≠ 0)
    (hr : r = algebraMap (Polynomial ℚ) (RatFunc ℚ) P / algebraMap (Polynomial ℚ) (RatFunc ℚ) Q)
    {z : ℂ} (hQz : Q.eval₂ (algebraMap ℚ ℂ) z ≠ 0) :
    RatFunc.eval (algebraMap ℚ ℂ) z r = P.eval₂ (algebraMap ℚ ℂ) z / Q.eval₂ (algebraMap ℚ ℂ) z := by
  have hnum : r.num * Q = P * r.denom := (RatFunc.num_mul_eq_mul_denom_iff hQ).mpr hr
  have hden : r.denom ∣ Q := (RatFunc.denom_dvd hQ).mpr ⟨P, hr⟩
  obtain ⟨c, hc⟩ := hden
  have hdz : r.denom.eval₂ (algebraMap ℚ ℂ) z ≠ 0 := by
    intro h
    refine hQz ?_
    rw [hc, Polynomial.eval₂_mul, h, zero_mul]
  rw [RatFunc.eval, div_eq_div_iff hdz hQz]
  rw [← Polynomial.eval₂_mul, ← Polynomial.eval₂_mul, hnum]

/-- `z ↦ p.eval₂ (algebraMap ℚ ℂ) z` is complex differentiable. -/
theorem differentiableOn_eval₂ (P : Polynomial ℚ) (U : Set ℂ) :
    DifferentiableOn ℂ (fun z => P.eval₂ (algebraMap ℚ ℂ) z) U := by
  apply DifferentiableOn.congr (Polynomial.differentiable (P.map (algebraMap ℚ ℂ))).differentiableOn
  intro z _
  exact Polynomial.eval₂_eq_eval_map (algebraMap ℚ ℂ) (x := z) (p := P)

end

end Work.C17I
