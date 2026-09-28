import Mathlib
import Submission.Work.HP.Defs
import Submission.Work.HP.DyadicDefs
import Submission.Work.HP.dyadic.reindex
import Submission.Work.HP.dyadic.sum_bound
import Submission.Work.HP.dyadic.L_arith

namespace Work.HP

open Finset

theorem dyadic_sum_ge3 (N r : ℕ) (hr : 3 ≤ r) (hrN : r ≤ N) :
    ∃ C : ℝ, 0 < C ∧ ∀ (L : ℝ), 0 ≤ L →
      (∑ k ∈ Fintype.piFinset (fun _ : Fin r => Finset.range (⌈L⌉₊ + 1)),
        (if Monotone k ∧ (∑ j, k j) ≤ ⌈L⌉₊ then
          (2 : ℝ) ^ (∑ j : Fin r, k j * (if (j.1 : ℕ) < 2 then N - 2 else N + r - 1 - 2 * j.1))
        else 0))
      ≤ C * 2 ^ ((N - 2) * L) * (1 + L) ^ 2 := by
  obtain ⟨C1, hC1pos, hC1⟩ := dyadic.sum_bound N r hr hrN
  obtain ⟨C2, hC2pos, hC2⟩ := dyadic.L_arith N (by omega)
  refine ⟨C1 * C2 + 1, by positivity, ?_⟩
  intro L hL
  have hif : (∑ k ∈ Fintype.piFinset (fun _ : Fin r => Finset.range (⌈L⌉₊ + 1)),
        (if Monotone k ∧ (∑ j, k j) ≤ ⌈L⌉₊ then
          (2 : ℝ) ^ (∑ j : Fin r, k j * (if (j.1 : ℕ) < 2 then N - 2 else N + r - 1 - 2 * j.1))
        else 0)) = ∑ k ∈ Kset r ⌈L⌉₊, (2:ℝ) ^ (bigE N r k) := by
    rw [Kset, piBox, Finset.sum_filter]
    apply Finset.sum_congr rfl
    intro k _
    simp only [bigE, cval]
  rw [hif, dyadic.reindex N r hrN ⌈L⌉₊]
  have hb := hC1 ⌈L⌉₊
  have hl := hC2 L hL
  have hpow_nonneg : (0:ℝ) ≤ 2 ^ ((N-2)*L) * (1+L)^2 := by positivity
  calc (∑ n ∈ Nset N r ⌈L⌉₊, (2:ℝ) ^ (bigE' N r n))
      ≤ C1 * 2 ^ ((N-2)*⌈L⌉₊) * (⌈L⌉₊+1)^2 := hb
    _ = C1 * (2 ^ ((N-2)*⌈L⌉₊) * (⌈L⌉₊+1)^2) := by ring
    _ ≤ C1 * (C2 * 2 ^ ((N-2)*L) * (1+L)^2) :=
        mul_le_mul_of_nonneg_left hl (le_of_lt hC1pos)
    _ = C1 * C2 * (2 ^ ((N-2)*L) * (1+L)^2) := by ring
    _ ≤ (C1 * C2 + 1) * (2 ^ ((N-2)*L) * (1+L)^2) :=
        mul_le_mul_of_nonneg_right (by linarith) hpow_nonneg
    _ = (C1 * C2 + 1) * 2 ^ ((N-2)*L) * (1+L)^2 := by ring

end Work.HP
