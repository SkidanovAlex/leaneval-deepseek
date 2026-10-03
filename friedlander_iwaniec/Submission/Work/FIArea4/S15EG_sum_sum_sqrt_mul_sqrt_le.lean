import Mathlib

namespace Work.FIArea4

theorem S15EG_sum_sum_sqrt_mul_sqrt_le (s : Finset ℕ) (t : ℕ → Finset ℕ) (U V : ℕ → ℕ → ℝ)
    (hU : ∀ e ∈ s, ∀ d' ∈ t e, 0 ≤ U e d') (hV : ∀ e ∈ s, ∀ d' ∈ t e, 0 ≤ V e d') :
    (∑ e ∈ s, ∑ d' ∈ t e, Real.sqrt (U e d') * Real.sqrt (V e d'))
      ≤ (1 / 2) * ((∑ e ∈ s, ∑ d' ∈ t e, U e d') + (∑ e ∈ s, ∑ d' ∈ t e, V e d')) := by
  -- Pointwise AM-GM: √U * √V ≤ (U + V) / 2, from (√U - √V)^2 ≥ 0.
  have hterm : ∀ e ∈ s, ∀ d' ∈ t e,
      Real.sqrt (U e d') * Real.sqrt (V e d') ≤ (U e d' + V e d') / 2 := by
    intro e he d' hd
    have hu := hU e he d' hd
    have hv := hV e he d' hd
    nlinarith [sq_nonneg (Real.sqrt (U e d') - Real.sqrt (V e d')),
      Real.sq_sqrt hu, Real.sq_sqrt hv]
  have hstep : (∑ e ∈ s, ∑ d' ∈ t e, Real.sqrt (U e d') * Real.sqrt (V e d'))
      ≤ ∑ e ∈ s, ∑ d' ∈ t e, (U e d' + V e d') / 2 :=
    Finset.sum_le_sum (fun e he => Finset.sum_le_sum (fun d' hd => hterm e he d' hd))
  have hsplit : ∑ e ∈ s, ∑ d' ∈ t e, (U e d' + V e d') / 2
      = (1 / 2) * ((∑ e ∈ s, ∑ d' ∈ t e, U e d') + (∑ e ∈ s, ∑ d' ∈ t e, V e d')) := by
    have hinner : ∀ e ∈ s,
        (∑ d' ∈ t e, (U e d' + V e d') / 2) = (∑ d' ∈ t e, (U e d' + V e d')) / 2 :=
      fun e _ => (Finset.sum_div (t e) (fun d' => U e d' + V e d') 2).symm
    rw [Finset.sum_congr rfl hinner]
    rw [(Finset.sum_div s (fun e => ∑ d' ∈ t e, (U e d' + V e d')) 2).symm]
    simp_rw [Finset.sum_add_distrib]
    ring
  exact hstep.trans hsplit.le

end Work.FIArea4
