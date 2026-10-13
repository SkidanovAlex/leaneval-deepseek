/-
  WilG5.Interior — `famGraph` of a parameter-independent family, with bounds uniform in the
  format and degree of the input.

  `famGraph_param_mem` (in `Submission.Work.WilG5.Interior.famGraph_param_mem`) proves that the
  `famGraph` of the constant family `(l, u) ↦ g u` is `Ω`-definable as soon as `graphOf g` is,
  but its existential bound is quantified *after* the format, degree and the function `g`; the
  constants it produces do not depend on them, but that is not visible from the statement.

  `cell_charts` must choose the format argument of the F-lemma *before* the cell `κ` and the
  degree `D₀` are known (the polynomial bound of the F-lemma depends on that format), so it
  needs the uniform form: one pair `(A, L)` working for every `g`, `F` and `D`.  That is what
  `famGraph_param_mem_uniform` provides, with the same explicit constants.
-/
import Mathlib
import Submission.Work.Wilkies.CG.Spec
import Submission.Work.WilG5.Defs

set_option autoImplicit false
set_option maxHeartbeats 1000000
noncomputable section
open Classical

namespace Work.WilG5.Interior

open WilkiesDesign WilkiesConjecture

/-- The `famGraph` of the family `(l, u) ↦ g u` is the preimage of `graphOf g` under the
"drop the first coordinate" map `Fin (n+1) → Fin (1+n+1)`, so `coordPre_mem` gives the
`Ω`-membership with bounds independent of the format and degree of `graphOf g`. -/
theorem famGraph_param_mem_uniform (S : WilkiesDesign.SOMin) (n : ℕ) :
    ∃ A L : ℕ, ∀ (g : (Fin n → ℝ) → ℝ) (F D : ℕ),
      WilkiesDesign.graphOf g ∈ S.Ω F D (n + 1) →
      WilkiesDesign.CG.famGraph (fun (_ : Fin 1 → ℝ) (u : Fin n → ℝ) => g u) ∈
        S.Ω (A + F) (D + L) (1 + n + 1) := by
  refine ⟨64 * ((1 + n + 1) + (n + 1)) + 64, 32 * ((1 + n + 1) + (n + 1)) + 32, ?_⟩
  intro g F D hg
  set I : Fin (n + 1) → Fin (1 + n + 1) :=
    fun i => ⟨i.val + 1, by have := i.isLt; omega⟩ with hI
  have hlast : I (Fin.last n) = Fin.last (1 + n) := by
    rw [hI]; apply Fin.ext
    simp only [Fin.val_last]
    omega
  have hcast : ∀ j : Fin n, I (Fin.castSucc j) = Fin.castSucc (Fin.natAdd 1 j) := by
    intro j
    rw [hI]; apply Fin.ext
    simp only [Fin.val_castSucc, Fin.val_natAdd]
    omega
  have hmem1 : ∀ z : Fin (1 + n + 1) → ℝ,
      z ∈ Work.WilG5.coordPre I (WilkiesDesign.graphOf g) ↔
        z (Fin.last (1 + n)) = g (fun j : Fin n => z (Fin.castSucc (Fin.natAdd 1 j))) := by
    intro z
    rw [Work.WilG5.coordPre, Set.mem_ofPred_eq]
    show z (I (Fin.last n)) = g (Fin.init (fun i => z (I i))) ↔
      z (Fin.last (1 + n)) = g (fun j : Fin n => z (Fin.castSucc (Fin.natAdd 1 j)))
    rw [hlast]
    have hinit : Fin.init (fun i => z (I i)) =
        (fun j : Fin n => z (Fin.castSucc (Fin.natAdd 1 j))) := by
      funext j
      exact congrArg z (hcast j)
    rw [hinit]
  have hmem2 : ∀ z : Fin (1 + n + 1) → ℝ,
      z ∈ WilkiesDesign.CG.famGraph (fun (_ : Fin 1 → ℝ) (u : Fin n → ℝ) => g u) ↔
        z (Fin.last (1 + n)) = g (fun j : Fin n => z (Fin.castSucc (Fin.natAdd 1 j))) := by
    intro z
    have hcomp : (Fin.init z ∘ Fin.natAdd 1) =
        (fun j : Fin n => z (Fin.castSucc (Fin.natAdd 1 j))) := by
      funext j; rfl
    show z (Fin.last (1 + n)) = g (Fin.init z ∘ Fin.natAdd 1) ↔
      z (Fin.last (1 + n)) = g (fun j : Fin n => z (Fin.castSucc (Fin.natAdd 1 j)))
    rw [hcomp]
  have hset : Work.WilG5.coordPre I (WilkiesDesign.graphOf g) =
      WilkiesDesign.CG.famGraph (fun (_ : Fin 1 → ℝ) (u : Fin n → ℝ) => g u) := by
    ext z
    rw [hmem1 z, hmem2 z]
  rw [← hset]
  refine Work.WilG5.mem_mono
    (Work.WilG5.coordPre_mem (S := S) (ι := I) (A := WilkiesDesign.graphOf g) hg)
    (64 * ((1 + n + 1) + (n + 1)) + 64 + F) (D + (32 * ((1 + n + 1) + (n + 1)) + 32)) ?_ ?_
  · omega
  · omega

end Work.WilG5.Interior
