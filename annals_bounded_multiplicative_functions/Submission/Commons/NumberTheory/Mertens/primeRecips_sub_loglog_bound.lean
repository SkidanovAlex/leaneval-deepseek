import Mathlib
import Submission.Commons.NumberTheory.Mertens.primeRecips_sub_loglog_eventually_bounded
import Submission.Commons.NumberTheory.Mertens.mertens_lower

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false

open Finset Real

namespace Commons.NumberTheory.Mertens

/-!
# `∑_{p ≤ x} 1/p − log log x` is bounded for all `x ≥ 11`

`primeRecips_sub_loglog_eventually_bounded` gives a constant `C₀` and a threshold
`X₀ ≥ 3` with `|primeRecips x − log log x| ≤ C₀` for `x ≥ X₀`.  To extend the bound
down to `x = 11` we control the compact range `[11, X₁]`, `X₁ := max X₀ 11`:
`primeRecips` is monotone and nonnegative, so it is `≤ primeRecips X₁` there, while
`log log x` is monotone on `[11, X₁]` (whose arguments exceed `1`), hence
`|log log x| ≤ |log log 11| + |log log X₁|`.  Adding `C₀` and this finite constant
gives the desired uniform bound.
-/

/-- `primeRecips` is nonnegative. -/
private lemma primeRecips_nonneg (x : ℝ) : 0 ≤ primeRecips x :=
  Finset.sum_nonneg (fun p _ => div_nonneg zero_le_one (Nat.cast_nonneg p))

theorem primeRecips_sub_loglog_bound :
    ∃ C : ℝ, 0 < C ∧ ∀ x : ℝ, 11 ≤ x →
      |(∑ p ∈ (⌊x⌋₊).primesLE, (1 : ℝ) / p) - Real.log (Real.log x)| ≤ C := by
  obtain ⟨C₀, hC₀pos, X₀, _hX₀3, hC₀⟩ := primeRecips_sub_loglog_eventually_bounded
  set X₁ : ℝ := max X₀ 11 with hX₁
  have hX₁11 : 11 ≤ X₁ := le_max_right _ _
  have hX₀X₁ : X₀ ≤ X₁ := le_max_left _ _
  set C₁ : ℝ := primeRecips X₁ + |Real.log (Real.log 11)| + |Real.log (Real.log X₁)| with hC₁
  have hC₁nonneg : 0 ≤ C₁ := by
    rw [hC₁]
    nlinarith [abs_nonneg (Real.log (Real.log 11)), abs_nonneg (Real.log (Real.log X₁)),
      primeRecips_nonneg X₁]
  refine ⟨C₀ + C₁, by linarith, ?_⟩
  intro x hx
  have hsum : (∑ p ∈ (⌊x⌋₊).primesLE, (1 : ℝ) / p) = primeRecips x := rfl
  rw [hsum]
  by_cases hX₀x : X₀ ≤ x
  · have h := hC₀ x hX₀x
    linarith
  · have hlt : x < X₀ := not_le.mp hX₀x
    have hxX₁ : x ≤ X₁ := le_trans (le_of_lt hlt) hX₀X₁
    have hmono : primeRecips x ≤ primeRecips X₁ :=
      primeRecips_mono (le_trans (le_of_lt hlt) hX₀X₁)
    have hlog11pos : 0 < Real.log (11 : ℝ) := Real.log_pos (by norm_num)
    have hlogxpos : 0 < Real.log x := Real.log_pos (by linarith : (1 : ℝ) < x)
    have hlower : Real.log (Real.log 11) ≤ Real.log (Real.log x) :=
      Real.log_le_log hlog11pos (Real.log_le_log (by norm_num : (0 : ℝ) < 11) hx)
    have hupper : Real.log (Real.log x) ≤ Real.log (Real.log X₁) :=
      Real.log_le_log hlogxpos (Real.log_le_log (by linarith : (0 : ℝ) < x) hxX₁)
    have hloglog_abs : |Real.log (Real.log x)| ≤
        |Real.log (Real.log 11)| + |Real.log (Real.log X₁)| := by
      refine abs_le.mpr ⟨?_, ?_⟩
      · calc -(|Real.log (Real.log 11)| + |Real.log (Real.log X₁)|)
            ≤ Real.log (Real.log 11) := by
              have h1 := neg_abs_le (Real.log (Real.log 11))
              have h2 := abs_nonneg (Real.log (Real.log X₁))
              linarith
        _ ≤ Real.log (Real.log x) := hlower
      · calc Real.log (Real.log x) ≤ Real.log (Real.log X₁) := hupper
          _ ≤ |Real.log (Real.log X₁)| := le_abs_self _
          _ ≤ |Real.log (Real.log 11)| + |Real.log (Real.log X₁)| := by
              have h1 := abs_nonneg (Real.log (Real.log 11))
              linarith
    have htri : |primeRecips x - Real.log (Real.log x)| ≤
        primeRecips x + |Real.log (Real.log x)| := by
      calc |primeRecips x - Real.log (Real.log x)|
            = |primeRecips x + (- Real.log (Real.log x))| := by ring_nf
        _ ≤ |primeRecips x| + |(- Real.log (Real.log x))| := abs_add_le _ _
        _ = primeRecips x + |Real.log (Real.log x)| := by
              rw [abs_neg, abs_of_nonneg (primeRecips_nonneg x)]
    calc |primeRecips x - Real.log (Real.log x)|
          ≤ primeRecips x + |Real.log (Real.log x)| := htri
      _ ≤ primeRecips X₁ + (|Real.log (Real.log 11)| + |Real.log (Real.log X₁)|) := by
            linarith
      _ = C₁ := by rw [hC₁]; ring
      _ ≤ C₀ + C₁ := by linarith

end Commons.NumberTheory.Mertens
