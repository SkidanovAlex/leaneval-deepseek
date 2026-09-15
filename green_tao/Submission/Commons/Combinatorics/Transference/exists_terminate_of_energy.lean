import Mathlib

set_option linter.unusedVariables false

namespace Commons.Combinatorics.Transference

open Finset
open scoped BigOperators

/-- **Energy argument of the Furstenberg tower** (Green–Tao §7).  Let `E : ℕ → ℝ` be an "energy"
which is bounded by `B` on `{0, …, K₀}` and increases by at least `c > 0` at every step at which
the algorithm does not terminate (`P K`).  If `B < K₀ · c` and `E 0 ≥ 0`, then the algorithm
terminates at some step `K < K₀`. -/
theorem exists_terminate_of_energy {E : ℕ → ℝ} {P : ℕ → Prop} {c B : ℝ} (hc : 0 < c)
    {K₀ : ℕ} (hK₀ : B < (K₀ : ℝ) * c)
    (hstep : ∀ K, K < K₀ → ¬ P K → E (K + 1) ≥ E K + c)
    (hbound : ∀ K, K ≤ K₀ → E K ≤ B) (hzero : 0 ≤ E 0) :
    ∃ K < K₀, P K := by
  by_contra h
  push Not at h
  -- h : ∀ K, K < K₀ → ¬ P K
  have hmono : ∀ K, K ≤ K₀ → E 0 + (K : ℝ) * c ≤ E K := by
    intro K hK
    induction K with
    | zero => simp
    | succ n ih =>
      have hn : n < K₀ := Nat.lt_of_succ_le hK
      have hprev := ih (le_of_lt hn)
      have hstepn := hstep n hn (h n hn)
      have : E 0 + ((n : ℝ) + 1) * c ≤ E (n + 1) := by
        have : E 0 + (n : ℝ) * c + c ≤ E n + c := by linarith
        linarith
      simpa [Nat.cast_succ] using this
  have hK0 : E 0 + (K₀ : ℝ) * c ≤ E K₀ := hmono K₀ le_rfl
  have hb := hbound K₀ le_rfl
  nlinarith [hzero, hK₀, hK0, hb]

end Commons.Combinatorics.Transference
