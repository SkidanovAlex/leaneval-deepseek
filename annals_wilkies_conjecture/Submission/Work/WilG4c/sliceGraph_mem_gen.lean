/-
  WilG4c — the general slice lemma: fixing `p` of the variables of an `Ω`-definable function.

  `Work.WilG1.Thin.sliceGraph_mem` treats the case `m = 1`: from
  `graphOf G ∈ S.Ω F D (p+2)` and `x : ℝ^p` it produces the sliced graph
  `graphOf (fun u : ℝ^1 → ℝ => G (Fin.snoc x (u 0)))` in `S.Ω a (b.eval D) 2`, where the
  format `a` depends on `p` and the degree is a *polynomial* in `D`.

  Here we need the uniform statement that the lead consumes: the slice keeps `m` free
  variables, and both the format and the degree grow by a *constant* `K` independent of
  `F`, `D`, `G` and `x` (`D + K`, not `b.eval D`).

  Proof.  Write `φ x := fun u : ℝ^m => Fin.append x₀ u : ℝ^{p+m}`; the sliced function is
  `G ∘ φ x₀`, so the rectangular composition lemma `Work.WilG4c.graphOfCompGen` (proved in
  the sibling module `graphOfCompGen`) applies as soon as the `p + m` coordinate graphs of
  `φ x₀` are `Ω`-definable with *constant* format and degree.  Each coordinate of `φ x₀` is
  either the constant `x₀ i` (`i < p`) or the projection `u ↦ u i` (`i ≥ p`); both graphs are
  hypersurfaces of a linear polynomial (`X (last m) - C c`, resp. `X (last m) - X i`), hence
  live in `S.Ω (m+1) 1 (m+1)`.  Feeding `F₂ = m+1`, `D₂ = 1` into `graphOfCompGen` gives
  format `F + (m+1) + C₁` and degree `D + (p+m) + C₂`, i.e. both are shifts by constants.

  This is the route with constant (not `D`-dependent) degree shift, which is exactly what the
  format/degree bookkeeping downstream requires.
-/
import Mathlib
import Submission.Work.Wilkies.Defs
import Submission.Work.WilG1.Basic
import Submission.Work.WilG5.Basic
import Submission.Work.WilG5.Reindex3
import Submission.Work.WilG1.Thin.sliceGraph_mem
import Submission.Work.WilG0.API
import Submission.Work.WilG4c.graphOfCompGen

set_option autoImplicit false

namespace Work.WilG4c

open WilkiesDesign

/-! ## The two coordinate graphs of the slice map -/

/-- The graph of a constant function `ℝ^m → ℝ` is a hyperplane, `Ω`-definable at format
`m+1` and degree `1`. -/
theorem graphOf_const_mem {S : SOMin} {m : ℕ} (c : ℝ) :
    graphOf (fun _ : Fin m → ℝ => c) ∈ S.Ω (m + 1) 1 (m + 1) := by
  have h := S.hyp (m + 1) ((MvPolynomial.X (Fin.last m) : MvPolynomial (Fin (m + 1)) ℝ) -
    MvPolynomial.C c)
  have hset : {z : Fin (m + 1) → ℝ | MvPolynomial.eval z
      ((MvPolynomial.X (Fin.last m) : MvPolynomial (Fin (m + 1)) ℝ) - MvPolynomial.C c) = 0}
      = graphOf (fun _ : Fin m → ℝ => c) := by
    ext z
    simp only [Set.mem_ofPred_eq, MvPolynomial.eval_sub, MvPolynomial.eval_X,
      MvPolynomial.eval_C, graphOf, sub_eq_zero]
  rw [hset] at h
  refine Work.WilG1.Omega.mono h le_rfl ?_
  simpa using Work.WilG5.td_X_sub_C_le (N := m) (Fin.last m) c

/-- The graph of a coordinate projection `u ↦ u i` on `ℝ^m` is a hyperplane, `Ω`-definable
at format `m+1` and degree `1`. -/
theorem graphOf_coord_mem {S : SOMin} {m : ℕ} (i : Fin m) :
    graphOf (fun u : Fin m → ℝ => u i) ∈ S.Ω (m + 1) 1 (m + 1) := by
  have h := S.hyp (m + 1) ((MvPolynomial.X (Fin.last m) : MvPolynomial (Fin (m + 1)) ℝ) -
    MvPolynomial.X (Fin.castSucc i))
  have hset : {z : Fin (m + 1) → ℝ | MvPolynomial.eval z
      ((MvPolynomial.X (Fin.last m) : MvPolynomial (Fin (m + 1)) ℝ) -
        MvPolynomial.X (Fin.castSucc i)) = 0}
      = graphOf (fun u : Fin m → ℝ => u i) := by
    ext z
    simp only [Set.mem_ofPred_eq, MvPolynomial.eval_sub, MvPolynomial.eval_X, graphOf]
    rw [Fin.init]
    simp only [sub_eq_zero]
  rw [hset] at h
  refine Work.WilG1.Omega.mono h le_rfl ?_
  refine le_trans (Work.WilG5.td_sub_le _ _) (max_le (Work.WilG5.td_X_le _) (Work.WilG5.td_X_le _))

/-! ## The slice lemma -/

theorem sliceGraph_mem_gen (S : WilkiesDesign.SOMin) (p m : ℕ) :
    ∃ K : ℕ, ∀ (F D : ℕ) (G : (Fin (p + m) → ℝ) → ℝ) (x : Fin p → ℝ),
      WilkiesDesign.graphOf G ∈ S.Ω F D (p + m + 1) →
      WilkiesDesign.graphOf (fun u : Fin m → ℝ => G (Fin.append x u)) ∈
        S.Ω (F + K) (D + K) (m + 1) := by
  obtain ⟨C₁, C₂, hC⟩ := Work.WilG4c.graphOfCompGen S (p + m) m
  refine ⟨((m + 1) + C₁) + ((p + m) + C₂), ?_⟩
  intro F D G x hG
  -- every coordinate of `u ↦ Fin.append x u` has a graph in `S.Ω (m+1) 1 (m+1)`
  have hcoord : ∀ j : Fin (p + m),
      WilkiesDesign.graphOf (fun u : Fin m → ℝ => (Fin.append x u : Fin (p + m) → ℝ) j) ∈
        S.Ω (m + 1) 1 (m + 1) := by
    intro j
    refine Fin.addCases (m := p) (n := m) (motive := fun j => WilkiesDesign.graphOf
      (fun u : Fin m → ℝ => (Fin.append x u : Fin (p + m) → ℝ) j) ∈ S.Ω (m + 1) 1 (m + 1))
      ?_ ?_ j
    · intro i
      rw [show (fun u : Fin m → ℝ => (Fin.append x u : Fin (p + m) → ℝ) (Fin.castAdd m i))
          = (fun _ : Fin m → ℝ => x i) from by
        funext u; exact Fin.append_left x u i]
      exact graphOf_const_mem (S := S) (x i)
    · intro i
      rw [show (fun u : Fin m → ℝ => (Fin.append x u : Fin (p + m) → ℝ) (Fin.natAdd p i))
          = (fun u : Fin m → ℝ => u i) from by
        funext u; exact Fin.append_right x u i]
      exact graphOf_coord_mem (S := S) i
  -- the rectangular composition lemma, with the slice map `u ↦ Fin.append x u` as `φ`
  have h := hC F (m + 1) D 1 G (fun u : Fin m → ℝ => Fin.append x u) hG hcoord
  have hmono := Work.WilG1.Omega.mono h
    (show F + (m + 1) + C₁ ≤ F + (((m + 1) + C₁) + ((p + m) + C₂)) by omega)
    (show D + (p + m) * 1 + C₂ ≤ D + (((m + 1) + C₁) + ((p + m) + C₂)) by omega)
  simpa [Function.comp_def, Nat.mul_one] using hmono

end Work.WilG4c
