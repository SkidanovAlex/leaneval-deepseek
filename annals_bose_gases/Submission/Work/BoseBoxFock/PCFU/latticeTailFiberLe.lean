import Mathlib.Algebra.Order.Ring.Star
import Mathlib.Algebra.Order.Archimedean.Real.Basic
import Mathlib.Algebra.Order.BigOperators.Group.Finset
import Submission.Work.BoseBoxFock.ShellCard
import Submission.Work.BoseBoxFock.farK0_defs
-- PORT435-BEGIN (v4.35 isDefEq respectTransparency compat)
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- PORT435-END

namespace Work.BoseBoxFock.PCFU

open Finset

/-- The sup-norm achieves its value: if `K d = j` then some coordinate of `d` has absolute
value `j`.  Consequently `j ^ 2 ≤ nSq d`. -/
lemma sq_le_nSq_of_K_eq {d : Fin 3 → ℤ} {j : ℕ} (h : Work.BoseBoxFock.K d = j) :
    j ^ 2 ≤ Work.BoseBoxFock.nSq d := by
  obtain ⟨i, -, hi⟩ := Finset.exists_mem_eq_sup (Finset.univ : Finset (Fin 3))
    Finset.univ_nonempty (fun i => (d i).natAbs)
  have hKi : Work.BoseBoxFock.K d = (d i).natAbs := hi
  have hj_eq : j = (d i).natAbs := by rw [← h, hKi]
  rw [hj_eq]
  exact Work.BoseBoxFock.coord_sq_le_nSq d i

theorem latticeTailFiberLe (N M j : ℕ) (hN : 2 ≤ N) (hj : 1 ≤ j) :
    ∑ d ∈ (Work.BoseBoxFock.box M).filter (fun d => Work.BoseBoxFock.K d = j),
        ((Work.BoseBoxFock.nSq d : ℝ) ^ N)⁻¹
      ≤ (24 * (j : ℝ) ^ 2 + 2) * ((j : ℝ) ^ (2 * N))⁻¹ := by
  classical
  have hsub : (Work.BoseBoxFock.box M).filter (fun d => Work.BoseBoxFock.K d = j)
      ⊆ Work.BoseBoxFock.shell j := by
    intro d hd
    rw [Finset.mem_filter] at hd
    obtain ⟨-, hK⟩ := hd
    rw [Work.BoseBoxFock.shell, Finset.mem_sdiff]
    exact ⟨Work.BoseBoxFock.mem_box_of_K_eq d j hK,
      Work.BoseBoxFock.not_mem_box_pred_of_K_eq hj hK⟩
  have hcard : ((Work.BoseBoxFock.box M).filter (fun d => Work.BoseBoxFock.K d = j)).card
      ≤ 24 * j ^ 2 + 2 := le_trans (Finset.card_le_card hsub) (Work.BoseBoxFock.ShellCard hj)
  have hjpos : (0 : ℝ) < (j : ℝ) := by exact_mod_cast (by omega : 0 < j)
  have hterm : ∀ d ∈ (Work.BoseBoxFock.box M).filter (fun d => Work.BoseBoxFock.K d = j),
      ((Work.BoseBoxFock.nSq d : ℝ) ^ N)⁻¹ ≤ ((j : ℝ) ^ (2 * N))⁻¹ := by
    intro d hd
    have hK : Work.BoseBoxFock.K d = j := (Finset.mem_filter.mp hd).2
    have hle : (j : ℝ) ^ 2 ≤ (Work.BoseBoxFock.nSq d : ℝ) := by
      exact_mod_cast sq_le_nSq_of_K_eq hK
    have hpow : (j : ℝ) ^ (2 * N) ≤ (Work.BoseBoxFock.nSq d : ℝ) ^ N := by
      rw [pow_mul]
      exact pow_le_pow_left₀ (by positivity) hle N
    exact (inv_le_inv₀ (pow_pos (lt_of_lt_of_le (by positivity : (0 : ℝ) < (j : ℝ) ^ 2) hle) N)
      (pow_pos hjpos (2 * N))).mpr hpow
  calc ∑ d ∈ (Work.BoseBoxFock.box M).filter (fun d => Work.BoseBoxFock.K d = j),
        ((Work.BoseBoxFock.nSq d : ℝ) ^ N)⁻¹
      ≤ ∑ _d ∈ (Work.BoseBoxFock.box M).filter (fun d => Work.BoseBoxFock.K d = j),
        ((j : ℝ) ^ (2 * N))⁻¹ := Finset.sum_le_sum hterm
    _ = (((Work.BoseBoxFock.box M).filter (fun d => Work.BoseBoxFock.K d = j)).card : ℝ)
        * ((j : ℝ) ^ (2 * N))⁻¹ := by rw [Finset.sum_const, nsmul_eq_mul]
    _ ≤ ((24 * j ^ 2 + 2 : ℕ) : ℝ) * ((j : ℝ) ^ (2 * N))⁻¹ := by
        refine mul_le_mul_of_nonneg_right ?_ ?_
        · exact_mod_cast hcard
        · positivity
    _ = (24 * (j : ℝ) ^ 2 + 2) * ((j : ℝ) ^ (2 * N))⁻¹ := by push_cast; ring

end Work.BoseBoxFock.PCFU
