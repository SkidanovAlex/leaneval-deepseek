import Mathlib
import Submission.Work.WilG4b.pullback_mem
import Submission.Work.WilG5.Basic

set_option autoImplicit false
noncomputable section
open Classical

namespace Work.WilG4b

open WilkiesDesign WilkiesConjecture
open Work.WilG5

theorem uniform_pullback_mem (S : WilkiesDesign.SOMin) (m N : ℕ) :
    ∃ (K : ℕ) (p : Polynomial ℕ), ∀ (e : Fin m → Fin N) (F D : ℕ) (X : Set (Fin m → ℝ)),
      X ∈ S.Ω F D m → {z : Fin N → ℝ | z ∘ e ∈ X} ∈ S.Ω (F + K) (p.eval D) N := by
  refine ⟨max N (4 * (m + N) + 8) + 1 + m, Polynomial.X + Polynomial.C (2 * m + 4), ?_⟩
  intro e F D X hX
  have hLift : liftLastM m N X ∈ S.Ω (F + N) D (N + m) := liftLastM_mem hX
  have hRel : relSetSwap e ∈ S.Ω (4 * (m + N) + 8) (2 * m + 4) (N + m) := relSetSwap_mem e
  have hJ : liftLastM m N X ∩ relSetSwap e ∈
      S.Ω (max (F + N) (4 * (m + N) + 8) + 1) (D + (2 * m + 4)) (N + m) := by
    have h2 := S.inter (F := max (F + N) (4 * (m + N) + 8)) (n := N + m) (k := 2)
      (fun i : Fin 2 => if i = 0 then D else 2 * m + 4)
      (fun i : Fin 2 => if i = 0 then liftLastM m N X else relSetSwap e)
      (by intro i
          fin_cases i
          · simpa using (mem_mono hLift (max (F + N) (4 * (m + N) + 8)) D (le_max_left _ _) le_rfl)
          · simpa using (mem_mono hRel (max (F + N) (4 * (m + N) + 8)) (2 * m + 4) (le_max_right _ _) le_rfl))
    rw [show (∑ i : Fin 2, (if i = 0 then D else 2 * m + 4)) = D + (2 * m + 4) from by
      simp [Fin.sum_univ_two]] at h2
    rwa [Work.WilG1.Omega.iInter_fin_two] at h2
  have hproj := projN_mem (S := S) (n := N) m (max (F + N) (4 * (m + N) + 8) + 1) (D + (2 * m + 4)) hJ
  rw [projN_liftLastM_relSetSwap e X] at hproj
  refine mem_mono hproj (F + (max N (4 * (m + N) + 8) + 1 + m))
    ((Polynomial.X + Polynomial.C (2 * m + 4)).eval D) ?_ ?_
  · omega
  · simp [Polynomial.eval_add]

end Work.WilG4b
