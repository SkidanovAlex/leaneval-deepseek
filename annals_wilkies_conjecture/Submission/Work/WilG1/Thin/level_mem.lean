import Mathlib
import Submission.Work.WilG1.OneDim.Defs
import Submission.Work.WilG1.Basic
import Submission.Work.WilG0.Main
import Submission.Work.WilG1.Choice.Helpers

set_option autoImplicit false

namespace Work.WilG1.Thin

open WilkiesDesign

/-- The graph of `x ↦ g (x 0)`, cut by the half-space `r < z 1` and projected back to
`Fin 1 → ℝ`, is the lifted superlevel set `{x | g x > r}`. -/
theorem projLast_graph_gt (g : ℝ → ℝ) (r : ℝ) :
    WilkiesDesign.projLast (WilkiesDesign.graphOf (fun x : Fin 1 → ℝ => g (x 0)) ∩
        {z : Fin 2 → ℝ | r < z (Fin.last 1)})
      = Work.WilG1.liftR {x : ℝ | g x > r} := by
  ext x
  simp only [WilkiesDesign.projLast, WilkiesDesign.graphOf, Set.mem_ofPred_eq,
    Set.mem_inter_iff, Work.WilG1.liftR, Fin.snoc_last, Fin.init_snoc]
  constructor
  · rintro ⟨t, h1, h2⟩
    rw [h1] at h2
    exact h2
  · intro hx
    exact ⟨g (x 0), rfl, hx⟩

/-- The graph of `x ↦ g (x 0)`, cut by the half-space `r ≤ z 1` and projected back to
`Fin 1 → ℝ`, is the lifted sublevel set `{x | g x ≥ r}`. -/
theorem projLast_graph_ge (g : ℝ → ℝ) (r : ℝ) :
    WilkiesDesign.projLast (WilkiesDesign.graphOf (fun x : Fin 1 → ℝ => g (x 0)) ∩
        {z : Fin 2 → ℝ | r ≤ z (Fin.last 1)})
      = Work.WilG1.liftR {x : ℝ | g x ≥ r} := by
  ext x
  simp only [WilkiesDesign.projLast, WilkiesDesign.graphOf, Set.mem_ofPred_eq,
    Set.mem_inter_iff, Work.WilG1.liftR, Fin.snoc_last, Fin.init_snoc]
  constructor
  · rintro ⟨t, h1, h2⟩
    rw [h1] at h2
    exact h2
  · intro hx
    exact ⟨g (x 0), rfl, hx⟩

/-- Format bookkeeping: the format `max F c + 2` of a graph-inter-halfspace-projection stays
below `F + 20` for the two constants `c = 4`, `c = 5` that occur below. -/
theorem max_add_le (F c : ℕ) (hc : c ≤ 5) : max F c + 1 + 1 ≤ F + 20 := by
  have h : max F c ≤ F + c := max_le (by omega) (by omega)
  have h2 : max F c + 1 + 1 ≤ (F + c) + 1 + 1 := by omega
  have h3 : (F + c) + 1 + 1 ≤ F + 20 := by omega
  exact le_trans h2 h3

/-- Degree bookkeeping: `D + 3 ≤ 20 * (D + 1)`. -/
theorem deg_le (D : ℕ) : D + 3 ≤ (Polynomial.C 20 * (Polynomial.X + Polynomial.C 1)).eval D := by
  simp only [Polynomial.eval_mul, Polynomial.eval_add, Polynomial.eval_C, Polynomial.eval_X]
  omega

theorem level_mem {S : WilkiesDesign.SOMin} {F D : ℕ} (g : ℝ → ℝ)
    (hg : WilkiesDesign.graphOf (fun x : Fin 1 → ℝ => g (x 0)) ∈ S.Ω F D 2) (r : ℝ) :
    (Work.WilG1.liftR {x : ℝ | g x > r} ∈
        S.Ω (F + 20) ((Polynomial.C 20 * (Polynomial.X + Polynomial.C 1)).eval D) 1) ∧
    (Work.WilG1.liftR {x : ℝ | g x ≥ r} ∈
        S.Ω (F + 20) ((Polynomial.C 20 * (Polynomial.X + Polynomial.C 1)).eval D) 1) := by
  constructor
  · -- the strict superlevel set
    have hB : {z : Fin 2 → ℝ | r < z (Fin.last 1)} ∈ S.Ω 4 3 2 :=
      Work.WilG1.Choice.gtConst_mem (S := S) (i := Fin.last 1) (c := r)
    have hI := Work.WilG1.Choice.inter2_mem (S := S) (n := 2) hg hB
    have hP := S.proj hI
    rw [projLast_graph_gt] at hP
    exact Omega.mono hP (max_add_le F 4 (by norm_num)) (deg_le D)
  · -- the closed superlevel set
    have hB : {z : Fin 2 → ℝ | r ≤ z (Fin.last 1)} ∈ S.Ω 5 3 2 :=
      Work.WilG1.Choice.geConst_mem (S := S) (i := Fin.last 1) (c := r)
    have hI := Work.WilG1.Choice.inter2_mem (S := S) (n := 2) hg hB
    have hP := S.proj hI
    rw [projLast_graph_ge] at hP
    exact Omega.mono hP (max_add_le F 5 (by norm_num)) (deg_le D)

end Work.WilG1.Thin
