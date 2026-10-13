import Mathlib
import Submission.Work.Wilkies.Defs
import Submission.Work.WilG1.Basic
import Submission.Work.WilG1.Calc.lt_mem
import Submission.Work.WilG4b.posPoly_mem
import Submission.Work.WilG4a.diffLocus_mem

namespace Work.WilG4a

open WilkiesDesign

/-- The cylinder over the differentiability locus of `g`, in the coordinates
`Fin 2 → ℝ` (first coordinate `x`, second coordinate the value). -/
lemma init_mem_liftR_iff (g : ℝ → ℝ) (z : Fin 2 → ℝ) :
    Fin.init z ∈ Work.WilG1.liftR {x : ℝ | DifferentiableAt ℝ g x}
      ↔ DifferentiableAt ℝ g (z 0) := by
  have h : (Fin.init z) 0 = z 0 := rfl
  simp only [Work.WilG1.liftR, Set.mem_ofPred_eq, h]

theorem extDeriv_graph_mem (S : WilkiesDesign.SOMin) (F : ℕ) :
    ∃ (a : ℕ) (b : Polynomial ℕ), ∀ (D : ℕ) (g : ℝ → ℝ),
      WilkiesDesign.graphOf (fun x : Fin 1 → ℝ => g (x 0)) ∈ S.Ω F D 2 →
      ({z : Fin 2 → ℝ | DifferentiableAt ℝ g (z 0) ∧ z 1 = deriv g (z 0)} ∪
        {z : Fin 2 → ℝ | ¬ DifferentiableAt ℝ g (z 0) ∧ z 1 = 0}) ∈ S.Ω a (b.eval D) 2 := by
  classical
  obtain ⟨a₀, b₀, hdl⟩ := diffLocus_mem S F
  refine ⟨max a₀ (max (a₀ + 2) 2 + 1), b₀ + (b₀ + Polynomial.C 1), ?_⟩
  intro D g hg
  obtain ⟨hloc, hB1⟩ := hdl D g hg
  -- The differentiability locus, as a subset of `ℝ²` (a cylinder over the locus in `ℝ`).
  have hCyg : {z : Fin 2 → ℝ | Fin.init z ∈ Work.WilG1.liftR {x : ℝ | DifferentiableAt ℝ g x}}
      ∈ S.Ω (a₀ + 1) (b₀.eval D) 2 :=
    Work.WilG1.Omega.prodRight_mem (S := S) hloc
  have hCset : {z : Fin 2 → ℝ |
        Fin.init z ∈ Work.WilG1.liftR {x : ℝ | DifferentiableAt ℝ g x}}
      = {z : Fin 2 → ℝ | DifferentiableAt ℝ g (z 0)} := by
    ext z
    exact init_mem_liftR_iff g z
  rw [hCset] at hCyg
  -- The hyperplane `{z 1 = 0}`.
  have hHmem : {z : Fin 2 → ℝ | z 1 = 0} ∈ S.Ω 2 ((Polynomial.C 1).eval D) 2 := by
    have h := Work.WilG1.Omega.hyp_mem (S := S) D
      (MvPolynomial.X (1 : Fin 2) : MvPolynomial (Fin 2) ℝ)
    have hX : (MvPolynomial.X (1 : Fin 2) : MvPolynomial (Fin 2) ℝ).totalDegree = 1 :=
      MvPolynomial.totalDegree_X (1 : Fin 2)
    rw [hX] at h
    simpa [MvPolynomial.eval_X] using h
  -- The "non-differentiable" part: complement of the locus, on the hyperplane.
  have hB2 : {z : Fin 2 → ℝ | ¬ DifferentiableAt ℝ g (z 0) ∧ z 1 = 0}
      ∈ S.Ω (max (a₀ + 2) 2 + 1) ((b₀ + Polynomial.C 1).eval D) 2 := by
    have hc : ({z : Fin 2 → ℝ | DifferentiableAt ℝ g (z 0)})ᶜ
        ∈ S.Ω (a₀ + 2) (b₀.eval D) 2 :=
      Work.WilG1.Omega.compl_mem (S := S) hCyg
    have hint := Work.WilG1.Omega.inter₂ (S := S) hc hHmem
    have hset : ({z : Fin 2 → ℝ | DifferentiableAt ℝ g (z 0)})ᶜ ∩ {z : Fin 2 → ℝ | z 1 = 0}
        = {z : Fin 2 → ℝ | ¬ DifferentiableAt ℝ g (z 0) ∧ z 1 = 0} := by
      ext z
      simp only [Set.mem_inter_iff, Set.mem_compl_iff, Set.mem_ofPred_eq]
    rwa [hset] at hint
  exact Work.WilG1.Omega.union₂ (S := S) hB1 hB2

end Work.WilG4a
