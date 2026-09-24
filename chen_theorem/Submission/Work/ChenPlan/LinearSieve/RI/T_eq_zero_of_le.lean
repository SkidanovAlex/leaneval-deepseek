import Mathlib
import Submission.Work.ChenPlan.LinearSieve.RI.basic

/-!
# Vanishing of the Rosser–Iwaniec layer sums `T_n(D,z)` for `z^{n+2} ≤ D`

The recursion `T_{n+1}(D,z) = Σ_{p < z, cond} ν(p) · T_n(D/p, p)` loses one prime at a time:
each step replaces `D` by `D/p` and `z` by `p`, so the exponent threshold `z^{k+2} ≤ D`
is preserved exactly when `p < z`.  Hence `T_n(D,z) = 0` as soon as `z^{n+2} ≤ D`:
the sieve problem has become empty.  This is the "the support is exhausted" input used to
terminate the Rosser–Iwaniec iteration.
-/

open Finset
open scoped BigOperators

set_option autoImplicit false

namespace Work.ChenPlan.LinearSieve.RI

open Classical

/-- If `z ^ (n + 2) ≤ D` and `n ≥ 1`, the `n`-th Rosser–Iwaniec layer sum vanishes.

The proof is an induction on `n`.  For `n = 1` the outer condition `Tcond 1 D p` requires
`D < p³`, while `p < z` gives `p³ < z³ ≤ D`: the sum is empty.  For the step, `T_{n+1}(D,z)`
sums `T_n(D/p, p)` over `p < z`, and `p < z` gives `p^{n+3} ≤ z^{n+3} ≤ D`, i.e.
`p^{n+2} ≤ D/p`, so the inner sum vanishes by the inductive hypothesis. -/
theorem T_eq_zero_of_le {A : BoundingSieve} {D z : ℝ} {n : ℕ} (hn : 1 ≤ n)
    (h : z ^ (n + 2) ≤ D) : T A n D z = 0 := by
  have main : ∀ n : ℕ, 1 ≤ n → ∀ D z : ℝ, z ^ (n + 2) ≤ D → T A n D z = 0 := by
    intro k
    induction k using Nat.strong_induction_on with
    | h n ih =>
      intro hn D z h
      rcases n with _ | n'
      · omega
      · rcases n' with _ | m
        · -- `n = 1`: the outer condition `Tcond 1 D p` contradicts `p < z` and `z³ ≤ D`.
          rw [T.eq_2 A D z 0]
          apply Finset.sum_eq_zero
          intro p hp
          rw [Finset.mem_filter] at hp
          obtain ⟨hpmem, hpz, hTcond⟩ := hp
          exfalso
          have hpprime : p.Prime := (Nat.mem_primeFactors.mp hpmem).1
          have hppos : (0 : ℝ) < (p : ℝ) := by exact_mod_cast hpprime.pos
          have hh : z ^ 3 ≤ D := by simpa using h
          have hp3 : (p : ℝ) ^ 3 ≤ z ^ 3 :=
            pow_le_pow_left₀ (le_of_lt hppos) (le_of_lt hpz) 3
          have hDlt : D < (p : ℝ) ^ 3 := hTcond.1 rfl
          linarith
        · -- `n = m + 2`: each summand `T_{m+1}(D/p, p)` vanishes, since `p < z` gives
          -- `p^{m+3} ≤ z^{m+3} ≤ D`, i.e. `p^{(m+1)+2} ≤ D/p`.
          rw [T.eq_2 A D z (m + 1)]
          apply Finset.sum_eq_zero
          intro p hp
          rw [Finset.mem_filter] at hp
          obtain ⟨hpmem, hpz, hTcond⟩ := hp
          have hpprime : p.Prime := (Nat.mem_primeFactors.mp hpmem).1
          have hppos : (0 : ℝ) < (p : ℝ) := by exact_mod_cast hpprime.pos
          have hD : z ^ (m + 4) ≤ D := by
            have hh : Nat.succ (Nat.succ m) + 2 = m + 4 := by omega
            simpa [hh] using h
          have hp_pow : (p : ℝ) ^ (m + 4) ≤ z ^ (m + 4) :=
            pow_le_pow_left₀ (le_of_lt hppos) (le_of_lt hpz) (m + 4)
          have hlt : (p : ℝ) ^ (m + 4) ≤ D := le_trans hp_pow hD
          have hkey : (p : ℝ) ^ ((m + 1) + 2) ≤ D / (p : ℝ) := by
            rw [le_div_iff₀ hppos]
            have : (p : ℝ) ^ ((m + 1) + 2) * (p : ℝ) = (p : ℝ) ^ (m + 4) := by
              rw [← pow_succ]
            rw [this]
            exact hlt
          rw [ih (m + 1) (by omega) (by omega) (D / (p : ℝ)) (p : ℝ) hkey, mul_zero]
  exact main n hn D z h

end Work.ChenPlan.LinearSieve.RI
