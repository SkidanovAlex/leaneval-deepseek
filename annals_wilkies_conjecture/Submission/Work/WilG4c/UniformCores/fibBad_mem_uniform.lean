import Mathlib
import Submission.Work.WilG1.Cell.Junk.fibBad_mem
import Submission.Work.WilG4a.diffLocus_mem

namespace Work.WilG4c.UniformCores

theorem fibBad_mem_uniform (S : WilkiesDesign.SOMin) (n F : ℕ) (i : Fin n) :
    ∃ (a : ℕ) (b : Polynomial ℕ), ∀ (D : ℕ) (h : (Fin n → ℝ) → ℝ),
      WilkiesDesign.graphOf h ∈ S.Ω F D (n + 1) →
      Work.WilG1.Cell.fibBad h i ∈ S.Ω a (b.eval D) n := by
  rcases n with _ | k
  · exact i.elim0
  · obtain ⟨a, b, hS⟩ := Work.WilG4a.Sset_omega_uniform (S := S) (N := k + 1) (F := F) i
    refine ⟨a + 1 + 1, b, ?_⟩
    intro D h hh
    have hs : Work.WilG1.Plumb.Sset (k + 1) i h ∈ S.Ω a (b.eval D) (k + 1 + 1) := hS D h hh
    have hset : Work.WilG1.Cell.fibBad h i =
        (WilkiesDesign.projLast (Work.WilG1.Plumb.Sset (k + 1) i h))ᶜ := by
      ext x
      simp only [Work.WilG1.Cell.fibBad, Set.mem_ofPred_eq, Set.mem_compl_iff]
      rw [Work.WilG1.Cell.Junk.mem_projLast_Sset_iff]
    rw [hset]
    exact S.compl (S.proj hs)

end Work.WilG4c.UniformCores
