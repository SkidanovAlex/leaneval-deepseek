import Mathlib

namespace Work.TMC7Core.Scale

open GenContFract

/-- For a real number `v` whose continued fraction expansion never terminates at any stage
(in particular `v` is irrational), the sequence `n ↦ Bₙ₊₁` of denominators of the convergents of
`GenContFract.of v`, shifted by one, is strictly increasing.

Indeed, writing `g = of v`, every partial quotient exists, so for every `n` we have
`g.s.get? (n+1) = some ⟨1, b⟩` with `b ≥ 1`.  The denominator recurrence
`Bₙ₊₂ = b · Bₙ₊₁ + 1 · Bₙ` then gives `Bₙ₊₂ ≥ Bₙ₊₁ + Bₙ > Bₙ₊₁`, since all denominators are
positive (they dominate the Fibonacci numbers). -/
theorem dens_succ_strictMono (v : ℝ) (hv : ∀ n, ¬ (GenContFract.of v).TerminatedAt n) :
    StrictMono (fun n => (GenContFract.of v).dens (n + 1)) := by
  -- every partial quotient of `of v` exists
  have hget : ∀ m, ∃ gp : GenContFract.Pair ℝ, (GenContFract.of v).s.get? m = some gp :=
    fun m => Option.ne_none_iff_exists'.mp fun h =>
      hv m (GenContFract.terminatedAt_iff_s_none.mpr h)
  have hstep : ∀ n, (GenContFract.of v).dens (n + 1) < (GenContFract.of v).dens (n + 2) := by
    intro n
    obtain ⟨gp, hgp⟩ := hget (n + 1)
    -- the partial numerator at that index is `1`
    have ha : gp.a = 1 :=
      (GenContFract.of_partNum_eq_one_and_exists_int_partDen_eq hgp).1
    -- the partial denominator is at least `1`
    have hb1 : (1 : ℝ) ≤ gp.b :=
      GenContFract.of_one_le_get?_partDen (GenContFract.partDen_eq_s_b hgp)
    -- the denominator recurrence
    have hrec := GenContFract.dens_recurrence (g := GenContFract.of v) (n := n) hgp rfl rfl
    rw [ha, one_mul] at hrec
    -- all denominators are positive: they dominate the Fibonacci numbers
    have hdenpos : 0 < (GenContFract.of v).dens n := by
      have hfib :=
        GenContFract.succ_nth_fib_le_of_nth_den (v := v) (n := n) (Or.inr (hv (n - 1)))
      have hpos : (0 : ℝ) < (Nat.fib (n + 1) : ℝ) := by
        exact_mod_cast (Nat.fib_pos.mpr (Nat.succ_pos n))
      linarith
    have hge : (0 : ℝ) ≤ (GenContFract.of v).dens (n + 1) := GenContFract.zero_le_of_den
    have hmul : (GenContFract.of v).dens (n + 1) ≤ gp.b * (GenContFract.of v).dens (n + 1) := by
      calc (GenContFract.of v).dens (n + 1)
          = 1 * (GenContFract.of v).dens (n + 1) := (one_mul _).symm
        _ ≤ gp.b * (GenContFract.of v).dens (n + 1) := mul_le_mul_of_nonneg_right hb1 hge
    rw [hrec]
    linarith
  exact strictMono_nat_of_lt_succ hstep

end Work.TMC7Core.Scale
