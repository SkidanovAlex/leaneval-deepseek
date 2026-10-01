import Mathlib
import Submission.Work.ZeroFreeTables.HBTable7_of_count
import Submission.Work.ZeroFreeTables.lam0_rows_fmethod
import Submission.Work.ZeroFreeTables.HBTable4_proof
import Submission.Work.ZeroFreeTables.Lam0Table7_of_table2and3

open DirichletCharacter Complex
open Work.LinnikContract
open scoped Classical BigOperators
noncomputable section

namespace Work.ZeroFreeTables

/-- The rows of Table 7 with `b ≤ 2/5` are exactly the rows of `fmRows`. -/
lemma mem_fmRows_of_mem_tableR {p : ℝ × ℝ} (hp : p ∈ tableR hbTable7) (h : p.1 ≤ 2 / 5) :
    p ∈ fmRows := by
  simp only [tableR, hbTable7, List.map_cons, List.map_nil, List.mem_cons, List.mem_nil_iff,
    or_false] at hp
  rcases hp with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl |
    rfl | rfl | rfl | rfl
  all_goals (norm_num [fmRows] <;> norm_num at h)

theorem Lam0Table7_of_wide : Work.ZeroFreeTables.Lam0Table7 := by
  obtain ⟨qF, hF⟩ := lam0_rows_fmethod
  obtain ⟨q4, h4⟩ := HBTable4_proof
  refine ⟨max qF q4, ?_⟩
  intro q hq _ χ₁ ρ₁ hw hsq him p hp hlam u hzu himu hne
  have hχ1 : χ₁ ≠ 1 := hw.1.1.1
  have hsq' : χ₁ ^ 2 = 1 := by rw [pow_two]; exact hsq
  have hZu : IsZ χ₁ u := ⟨hχ1, hzu, himu⟩
  have hconj : u ≠ starRingEnd ℂ ρ₁ := by
    rw [conj_eq_self_of_im_zero_lam0 him]; exact hne
  by_cases hsmall : p.1 ≤ 2 / 5
  · have hmem : p ∈ fmRows := mem_fmRows_of_mem_tableR hp hsmall
    exact (hF q (le_trans (le_max_left _ _) hq) χ₁ ρ₁ hw hsq' him p hmem hlam).2 u hZu hne
      (fun _ => hconj)
  · have hb := (h4 q (le_trans (le_max_right _ _) hq) χ₁ ρ₁ hw hsq' him
        ((1294 / 1000 : ℝ), (1294 / 1000 : ℝ)) (by simp [tableR, hbTable4])
        (by linarith [tableR_hbTable7_fst_le hp])).2 u hZu hne (fun _ => hconj)
    have hp2 : p.2 ≤ 1294 / 1000 := table7_row_bound_big hp (le_of_lt (not_le.mp hsmall))
    linarith

end Work.ZeroFreeTables
