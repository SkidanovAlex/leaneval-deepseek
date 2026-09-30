import Mathlib
import Submission.Commons.NumberTheory.Mertens.primeRecips_sub_loglog_bound

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false

namespace Work.BMF.liouville

open Polynomial Finset Real

/-- Mertens' upper bound for reciprocal primes in the form needed downstream:
`Σ_{p ≤ X} 1/p ≤ log log X + C` for all real `X ≥ 3` (where the sum is over `⌊X⌋₊.primesLE`).
Route: import `Submission.Commons.NumberTheory.Mertens.primeRecips_sub_loglog_bound`, which gives
(`∃ C > 0, ∀ x ≥ 11, |Σ_{p ≤ ⌊x⌋₊} 1/p − log log x| ≤ C`); this gives the bound for `X ≥ 11`, and
for `3 ≤ X < 11` the left side is at most `Σ_{p ≤ 7} 1/p ≤ 1.6` while `log log X ≥ 0`, so enlarging
the constant handles the compact range. -/
theorem mertens_recip_le :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ X : ℝ, 3 ≤ X →
      (∑ p ∈ ⌊X⌋₊.primesLE, (1 : ℝ) / p) ≤ Real.log (Real.log X) + C := by
  obtain ⟨C₀, hC₀pos, hC₀bound⟩ :=
    Commons.NumberTheory.Mertens.primeRecips_sub_loglog_bound
  have hPnonneg : 0 ≤ Commons.NumberTheory.Mertens.primeRecips 11 := by
    unfold Commons.NumberTheory.Mertens.primeRecips
    exact sum_nonneg (fun p _ => div_nonneg zero_le_one (Nat.cast_nonneg p))
  refine ⟨C₀ + Commons.NumberTheory.Mertens.primeRecips 11, by linarith, ?_⟩
  intro X hX
  by_cases h : 11 ≤ X
  · -- large range: use the imported bound directly
    have h2 := (abs_le.mp (hC₀bound X h)).2
    linarith
  · -- compact range `3 ≤ X < 11`: bound by `primeRecips 11`, and `log log X ≥ 0`
    have hX11 : X ≤ 11 := le_of_lt (not_le.mp h)
    have hmono' : Commons.NumberTheory.Mertens.primeRecips X ≤
        Commons.NumberTheory.Mertens.primeRecips 11 :=
      Commons.NumberTheory.Mertens.primeRecips_mono hX11
    have hsumX : (∑ p ∈ ⌊X⌋₊.primesLE, (1 : ℝ) / p) =
        Commons.NumberTheory.Mertens.primeRecips X := rfl
    rw [hsumX]
    have hexp : Real.exp 1 ≤ (3 : ℝ) := le_of_lt Real.exp_one_lt_three
    have hlog := Real.log_le_log (Real.exp_pos 1) (le_trans hexp hX)
    rw [Real.log_exp] at hlog
    have hloglogX : 0 ≤ Real.log (Real.log X) := Real.log_nonneg hlog
    linarith

end Work.BMF.liouville
