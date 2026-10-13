import Mathlib
import Submission.Work.WilG1.Cell.JunkDefs
import Submission.Work.WilG1.Plumb.junkPartial_mem
import Submission.Work.WilG4a.diffLocus_mem

namespace Work.WilG4c.UniformCores

open WilkiesDesign

/-- The junk partial `JunkDefs.junkP` of the cell package is the `Plumb.junkPartial` used by
the plumbing construction of the proof that the graph of the partial derivative is `Ω`-definable.
Both differentiate the fibre `t ↦ h (update y i t)` at `y i`. -/
theorem junkP_eq_junkPartial {N : ℕ} (g : (Fin (N + 1) → ℝ) → ℝ) (i : Fin (N + 1)) :
    Work.WilG1.Cell.junkP g i = Work.WilG1.junkPartial i g := by
  funext z
  simp only [Work.WilG1.Cell.junkP, Work.WilG1.junkPartial]
  congr 1
  funext x
  rw [Fin.insertNth_removeNth]
  rfl

/-- **Uniformity in the degree parameter of `junkPartial_mem`.**  For a fixed input format `F`
and dimension `m`, the format and the degree-polynomial witnessing `Ω`-membership of
`graphOf (junkP h i)` can be chosen independently of the degree parameter `D` and of `h`.

The proof combines the uniform `Sset`-membership `Sset_omega_uniform` (from area G4a) with the
explicit description `graph_eq` of the graph of `junkPartial`:

`graphOf (junkP h i) = Sset m i h ∪ (lift of (projLast (Sset m i h))ᶜ) ∩ {last = 0}`,

each piece of which is an `Ω`-set with format and degree depending on `m`, `F` and `D` only
through the polynomial `b₀` produced by `Sset_omega_uniform`. -/
theorem junkP_mem_uniform (S : WilkiesDesign.SOMin) (m F : ℕ) (i : Fin m) :
    ∃ (a : ℕ) (b : Polynomial ℕ), ∀ (D : ℕ) (h : (Fin m → ℝ) → ℝ),
      WilkiesDesign.graphOf h ∈ S.Ω F D (m + 1) →
      WilkiesDesign.graphOf (Work.WilG1.Cell.junkP h i) ∈ S.Ω a (b.eval D) (m + 1) := by
  rcases m with _ | k
  · exact Fin.elim0 i
  obtain ⟨a₀, b₀, hS⟩ := Work.WilG4a.Sset_omega_uniform (S := S) (N := k + 1) (F := F) i
  refine ⟨max a₀ (max (a₀ + 3) (k + 1 + 1) + 1), b₀ + (b₀ + Polynomial.C 1), ?_⟩
  intro D h hf
  have hs : Work.WilG1.Plumb.Sset (k + 1) i h ∈ S.Ω a₀ (b₀.eval D) (k + 1 + 1) := hS D h hf
  have hproj : projLast (Work.WilG1.Plumb.Sset (k + 1) i h) ∈
      S.Ω (a₀ + 1) (b₀.eval D) (k + 1) := S.proj hs
  have hnot : (projLast (Work.WilG1.Plumb.Sset (k + 1) i h))ᶜ ∈
      S.Ω (a₀ + 2) (b₀.eval D) (k + 1) := S.compl hproj
  have hlift : {v : Fin (k + 1 + 1) → ℝ | Fin.init v ∉ projLast (Work.WilG1.Plumb.Sset (k + 1) i h)} ∈
      S.Ω (a₀ + 3) (b₀.eval D) (k + 1 + 1) := S.prod_right hnot
  have hzero : {v : Fin (k + 1 + 1) → ℝ | v (Fin.last (k + 1)) = 0} ∈
      S.Ω (k + 1 + 1) ((Polynomial.C 1 : Polynomial ℕ).eval D) (k + 1 + 1) := by
    have h := S.hyp (k + 1 + 1)
      (MvPolynomial.X (Fin.last (k + 1)) : MvPolynomial (Fin (k + 1 + 1)) ℝ)
    rw [MvPolynomial.totalDegree_X] at h
    simpa using h
  have hinter : ({v : Fin (k + 1 + 1) → ℝ |
        Fin.init v ∉ projLast (Work.WilG1.Plumb.Sset (k + 1) i h)} ∩
      {v : Fin (k + 1 + 1) → ℝ | v (Fin.last (k + 1)) = 0}) ∈
      S.Ω (max (a₀ + 3) (k + 1 + 1) + 1) ((b₀ + Polynomial.C 1).eval D) (k + 1 + 1) :=
    Work.WilG1.Omega.inter₂ hlift hzero
  have hunion : (Work.WilG1.Plumb.Sset (k + 1) i h ∪
      ({v : Fin (k + 1 + 1) → ℝ | Fin.init v ∉ projLast (Work.WilG1.Plumb.Sset (k + 1) i h)} ∩
       {v : Fin (k + 1 + 1) → ℝ | v (Fin.last (k + 1)) = 0})) ∈
      S.Ω (max a₀ (max (a₀ + 3) (k + 1 + 1) + 1))
        ((b₀ + (b₀ + Polynomial.C 1)).eval D) (k + 1 + 1) :=
    Work.WilG1.Omega.union₂ hs hinter
  rw [junkP_eq_junkPartial h i, Work.WilG1.Plumb.graph_eq (n := k) i h]
  exact hunion

end Work.WilG4c.UniformCores
