import Mathlib
import Submission.Work.TMComp.RealCartanDefs

namespace Work.TMComp.RealCartan

open Filter

theorem rcAall_eq_iUnion {U : Set ℂ} {f : ℕ → ℂ → ℂ} {w s : ℕ → ℝ}
    (hw : ∀ k, 0 < w k) (hs : ∀ k, 0 < s k) :
    Work.TMComp.RC.Aall U f w s = ⋃ m, ⋃ n, Work.TMComp.RC.Amn U f w s m n := by
  ext x
  simp only [Work.TMComp.RC.Aall, Work.TMComp.RC.Amn, Set.mem_ofPred_eq, Set.mem_iUnion]
  constructor
  · rintro ⟨hxU, η, hη, hev⟩
    obtain ⟨N, hN⟩ := Filter.eventually_atTop.mp hev
    obtain ⟨m, hm⟩ := exists_nat_one_div_lt hη
    refine ⟨m, N, hxU, fun k hk => ?_⟩
    have h1 : (1 : ℝ) / (m + 1) ≤ η := le_of_lt hm
    have h2 : s k / (m + 1 : ℝ) ≤ η * s k := by
      have h2' : s k * (1 / (m + 1 : ℝ)) ≤ s k * η :=
        mul_le_mul_of_nonneg_left h1 (le_of_lt (hs k))
      rw [div_eq_mul_inv, ← one_div, mul_comm η (s k)]
      exact h2'
    calc ‖f k x‖ ≤ w k * Real.exp (-(η * s k)) := hN k hk
      _ ≤ w k * Real.exp (-(s k / (m + 1))) :=
          mul_le_mul_of_nonneg_left (Real.exp_le_exp.mpr (neg_le_neg h2)) (le_of_lt (hw k))
  · rintro ⟨m, n, hxU, h⟩
    refine ⟨hxU, 1 / (m + 1), by positivity, ?_⟩
    filter_upwards [Filter.eventually_ge_atTop n] with k hk
    have hthis := h k hk
    have key : (1 / (m + 1 : ℝ)) * s k = s k / (m + 1) := by
      rw [one_div, div_eq_mul_inv, mul_comm]
    rw [key]
    exact hthis

end Work.TMComp.RealCartan
