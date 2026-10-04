import Mathlib
import Submission.Work.Diff.EXT.splice_defs
import Submission.Work.Diff.EXT.ricJetDefs

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false

/-!
# Smoothness of the coordinate expression `ricPhi`

`Work.Diff.EXT.ricPhi` is the explicit coordinate (Christoffel) formula for the chart Ricci matrix
of a metric, read off from the `2`-jet of the chart matrix: it is a polynomial expression in the
entries of `L` and `B` (the first and second spatial jets of the chart matrix, evaluated on the
canonical basis of the model space) together with the entries of the inverse Gram matrix
`(Matrix.of A)⁻¹`.

On the open set `{A | (Matrix.of A).det ≠ 0}` where the Gram matrix is nondegenerate, the inverse
is smooth (it is `(det)⁻¹` times the adjugate, both of which are polynomial in the entries, and
`x ↦ x⁻¹` is smooth away from `0`), and the jet entries are (continuous linear, hence) smooth
functions of the jet, so `ricPhi` is `C^∞` there.  This file proves exactly that.
-/

set_option linter.unusedSectionVars false

open scoped Manifold ContDiff Bundle Topology BigOperators
open Bundle ContDiff Set VectorField CovariantDerivative Metric

namespace Work.Diff.EXT

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]
  [CompleteSpace E]

noncomputable section

/-- The type of the jet variable of `ricPhi`: the Gram matrix, its first spatial jet and its
second spatial jet. -/
abbrev JetT := (MatE (E := E) × (E →L[ℝ] MatE (E := E)) × (E →L[ℝ] E →L[ℝ] MatE (E := E)))

/-- The type of the argument of `ricPhi`. -/
abbrev Zt := E × JetT (E := E)

/-- The set of jets with nondegenerate Gram matrix, on which the inverse Gram matrix is
differentiable. -/
abbrev goodSet : Set (Zt (E := E)) := {z | (Matrix.of z.2.1).det ≠ 0}

/-- A finite product of `C^n` `ℝ`-valued functions is `C^n`. -/
lemma contDiff_finset_prod {ι X : Type*} [NormedAddCommGroup X] [NormedSpace ℝ X]
    (u : Finset ι) {n : WithTop ℕ∞} {f : ι → X → ℝ}
    (h : ∀ i ∈ u, ContDiff ℝ n (f i)) :
    ContDiff ℝ n (fun x => ∏ i ∈ u, f i x) := by
  classical
  induction u using Finset.induction with
  | empty => simp only [Finset.prod_empty]; exact contDiff_const
  | insert a u ha ih =>
      have hstep : (fun x => ∏ i ∈ insert a u, f i x) = (fun x => f a x * ∏ i ∈ u, f i x) := by
        funext x; rw [Finset.prod_insert ha]
      rw [hstep]
      exact (h a (Finset.mem_insert_self a u)).mul
        (ih fun i hi => h i (Finset.mem_insert_of_mem hi))

/-- The determinant of the Gram matrix, as a function of the Gram matrix, is `C^∞`: it is a
polynomial in the entries. -/
lemma contDiff_det_MatE :
    ContDiff ℝ (⊤ : ℕ∞) (fun A : MatE (E := E) => (Matrix.of A).det) := by
  have key : (fun A : MatE (E := E) => (Matrix.of A).det)
      = fun A => ∑ σ : Equiv.Perm (Fin (Module.finrank ℝ E)),
          Equiv.Perm.sign σ • ∏ i, (Matrix.of A) (σ i) i := by
    funext A; rw [Matrix.det_apply]
  rw [key]
  refine ContDiff.sum (fun σ _ => ?_)
  refine ContDiff.const_smul (Equiv.Perm.sign σ) ?_
  refine contDiff_finset_prod Finset.univ (fun i _ => ?_)
  have h : (fun A : MatE (E := E) => (Matrix.of A) (σ i) i) = fun A => A (σ i) i := by
    funext A; rw [Matrix.of_apply]
  rw [h]
  fun_prop

/-- Every entry of the adjugate of the Gram matrix, as a function of the Gram matrix, is `C^∞`:
it is a determinant of a matrix obtained by replacing one row of `A` by a fixed vector, hence
again a polynomial in the entries. -/
lemma contDiff_adjugate_MatE (r s : Fin (Module.finrank ℝ E)) :
    ContDiff ℝ (⊤ : ℕ∞) (fun A : MatE (E := E) => (Matrix.of A).adjugate r s) := by
  have key : (fun A : MatE (E := E) => (Matrix.of A).adjugate r s)
      = fun A => ((Matrix.of A).updateRow s (Pi.single r (1:ℝ))).det := by
    funext A; rw [Matrix.adjugate_apply]
  rw [key]
  have key2 : (fun A : MatE (E := E) => ((Matrix.of A).updateRow s (Pi.single r (1:ℝ))).det)
      = fun A => ∑ σ : Equiv.Perm (Fin (Module.finrank ℝ E)), Equiv.Perm.sign σ •
          ∏ i, ((Matrix.of A).updateRow s (Pi.single r (1:ℝ))) (σ i) i := by
    funext A; rw [Matrix.det_apply]
  rw [key2]
  refine ContDiff.sum (fun σ _ => ?_)
  refine ContDiff.const_smul (Equiv.Perm.sign σ) ?_
  refine contDiff_finset_prod Finset.univ (fun i _ => ?_)
  by_cases h : σ i = s
  · simp only [← h, Matrix.updateRow_self]
    exact contDiff_const
  · simp only [Matrix.updateRow_ne h, Matrix.of_apply]
    fun_prop

/-- The `(r,s)` entry of the inverse Gram matrix is smooth, as a function of the jet, on the set
where the Gram matrix is nondegenerate. -/
lemma contDiffOn_invComp (r s : Fin (Module.finrank ℝ E)) :
    ContDiffOn ℝ (⊤ : ℕ∞) (fun z : Zt (E := E) => (Matrix.of z.2.1)⁻¹ r s) (goodSet (E := E)) := by
  have hproj : ContDiffOn ℝ (⊤ : ℕ∞) (fun z : Zt (E := E) => z.2.1) (goodSet (E := E)) := by
    fun_prop
  have hdet : ContDiffOn ℝ (⊤ : ℕ∞) (fun z : Zt (E := E) => (Matrix.of z.2.1).det)
      (goodSet (E := E)) := contDiff_det_MatE.comp_contDiffOn hproj
  have hinv : ContDiffOn ℝ (⊤ : ℕ∞) (fun z : Zt (E := E) => ((Matrix.of z.2.1).det)⁻¹)
      (goodSet (E := E)) := hdet.inv (fun z hz => hz)
  have hadj : ContDiffOn ℝ (⊤ : ℕ∞) (fun z : Zt (E := E) => (Matrix.of z.2.1).adjugate r s)
      (goodSet (E := E)) := (contDiff_adjugate_MatE r s).comp_contDiffOn hproj
  have hmul := hinv.mul hadj
  convert hmul using 1
  funext z
  rw [Matrix.inv_def, Matrix.smul_apply, Ring.inverse_eq_inv, smul_eq_mul]

/-- The Koszul Christoffel pairing read off from the first spatial jet is smooth as a function of
the jet (it is linear in the jet). -/
lemma contDiff_jKz (a b c : Fin (Module.finrank ℝ E)) :
    ContDiff ℝ (⊤ : ℕ∞) (fun z : Zt (E := E) => jKz z.2.2.1 a b c) := by
  unfold jKz
  fun_prop

/-- The derivative of the Koszul Christoffel pairing read off from the second spatial jet is smooth
as a function of the jet (it is linear in the jet). -/
lemma contDiff_jKzD (m a b c : Fin (Module.finrank ℝ E)) :
    ContDiff ℝ (⊤ : ℕ∞) (fun z : Zt (E := E) => jKzD z.2.2.2 m a b c) := by
  unfold jKzD
  fun_prop

/-- **Smoothness of the explicit coordinate expression for the chart Ricci matrix**: away from the
degenerate matrices the expression `ricPhi` (a polynomial expression in the entries of the inverse
Gram matrix `(Matrix.of A)⁻¹` and in the jet variables) is `C^∞`. -/
theorem ricPhi_contDiffOn
    {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E] [CompleteSpace E] :
    ContDiffOn ℝ (⊤ : ℕ∞)
      (fun z : E × (Work.Diff.EXT.MatE (E := E) × (E →L[ℝ] Work.Diff.EXT.MatE (E := E)) ×
          (E →L[ℝ] E →L[ℝ] Work.Diff.EXT.MatE (E := E))) => Work.Diff.EXT.ricPhi z)
      {z | (Matrix.of z.2.1).det ≠ 0} := by
  unfold ricPhi jRic jRm jInv
  apply contDiffOn_pi.mpr; intro i
  apply contDiffOn_pi.mpr; intro j
  apply ContDiffOn.sum; intro k _
  apply ContDiffOn.sum; intro l _
  apply ContDiffOn.mul (contDiffOn_invComp k l)
  apply ContDiffOn.add
  · apply ContDiffOn.sub
    · apply ContDiffOn.sub
      · exact (contDiff_jKzD k j i l).contDiffOn
      · exact (contDiff_jKzD i j k l).contDiffOn
    · apply ContDiffOn.sum; intro r _
      apply ContDiffOn.sum; intro s _
      exact ((contDiffOn_invComp r s).mul (contDiff_jKz j i r).contDiffOn).mul
        (contDiff_jKz k l s).contDiffOn
  · apply ContDiffOn.sum; intro r _
    apply ContDiffOn.sum; intro s _
    exact ((contDiffOn_invComp r s).mul (contDiff_jKz j k r).contDiffOn).mul
      (contDiff_jKz i l s).contDiffOn

end

end Work.Diff.EXT
