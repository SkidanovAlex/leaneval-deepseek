import Mathlib
import Submission.Work.Diff.GE.deps
import Submission.Work.Diff.GE.norms_defs
import Submission.Work.Diff.GE.curvbasic
import Submission.Work.Diff.GE.NablaRm
import Submission.Work.Diff.GE.frobSq5_rot
import Submission.Work.Diff.GE.N5_eq_QQ2
import Submission.Work.Diff.GE.frobSq5_eq_sum
import Submission.Work.Diff.GE.rot5_eq_rotA
import Submission.Work.Diff.GE.covRm_eq_rot5

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false

/-!
# `|∇Rm|²` in a general basis

The frozen `Submission.Diff.dRmNormSq g x` is `|∇Rm|²` computed in the chosen orthonormal frame
`Submission.Diff.onFrame g x`.  For an arbitrary basis `e` of the tangent space at `x` with Gram
matrix `Γ i j = g.inner x (e i) (e j)`, the same number is the full contraction `N5 Γ S` of the
components `S m i j k l = covRm g x (e m) (e i) (e j) (e k) (e l)` of `∇Rm` in `e` with `Γ⁻¹` in
every slot.

The proof: let `f = onFrame g x` be the orthonormal frame and `A` the matrix of `e` in `f`
(`e i = ∑ j, A i j • f j`).  Then `Γ = A * Aᵀ` (the Gram matrix, `mul_transpose_eq_gram`), `A` is
invertible (`e` is a basis, `isUnit_det_basis_repr`), the components of `∇Rm` in `e` are the
`rot5 A`-rotation of its components in `f` (`Work.Diff.GE.covRm_eq_rot5`), and
`N5 (A * Aᵀ) (rot5 A S) = frobSq5 S` (`Work.Diff.GE.frobSq5_rot`); the right-hand side is
`dRmNormSq g x` by definition.
-/

set_option linter.style.haveILetI false
set_option linter.unusedSectionVars false

namespace Work.Diff.GE

open LeanEval.Geometry.SphereTheorem Submission.Diff Submission.Diff.Alg
open scoped Manifold ContDiff Bundle Topology Matrix
open Bundle ContDiff Set VectorField CovariantDerivative Metric

variable
  {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E] [CompleteSpace E]
  {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
  {M : Type*} [TopologicalSpace M] [T2Space M] [ChartedSpace H M] [IsManifold I ∞ M]

/-- The Gram matrix of a frame `e'` expanded in an orthonormal frame `f` as `e' i = ∑ j, A i j • f j`
is `A * Aᵀ`. -/
theorem mul_transpose_eq_gram {g : SMet I M} (x : M)
    (f e' : Fin (Module.finrank ℝ E) → TangentSpace I x)
    (hf : IsONFrame g x f)
    (A : Matrix (Fin (Module.finrank ℝ E)) (Fin (Module.finrank ℝ E)) ℝ)
    (hA : ∀ i, e' i = ∑ j, A i j • f j) :
    A * Matrix.transpose A = fun i j => g.inner x (e' i) (e' j) := by
  funext i j
  simp only [Matrix.mul_apply, Matrix.transpose_apply]
  rw [hA i, hA j]
  simp only [map_sum, sum_apply, map_smul, smul_apply, smul_eq_mul]
  have hf2 : ∀ i j, g.inner x (f i) (f j) = if i = j then (1 : ℝ) else 0 := fun i j => hf i j
  simp only [hf2]
  have hinner : ∀ x_1 : Fin (Module.finrank ℝ E),
      (∑ x_2, A i x_2 * (if x_2 = x_1 then (1 : ℝ) else 0)) = A i x_1 := by
    intro x_1
    rw [Finset.sum_eq_single x_1]
    · simp
    · intro b _ hb; simp [hb]
    · intro h; exact absurd (Finset.mem_univ x_1) h
  simp only [hinner]
  refine Finset.sum_congr rfl fun k _ => ?_
  ring

/-- If `e` spans `V` and `b` is a basis of `V` indexed by the same finite type, then the matrix of
coordinates of `e` in `b` is invertible. -/
theorem isUnit_det_basis_repr {ι : Type*} [Fintype ι] [DecidableEq ι]
    {V : Type*} [AddCommGroup V] [Module ℝ V]
    (b : Module.Basis ι ℝ V) (e : ι → V)
    (hb : Submodule.span ℝ (Set.range e) = ⊤) :
    IsUnit (Matrix.det (fun i j => b.repr (e i) j)) := by
  have hli : LinearIndependent ℝ e :=
    linearIndependent_of_top_le_span_of_card_eq_finrank (le_of_eq hb.symm)
      (Module.finrank_eq_card_basis b).symm
  let be : Module.Basis ι ℝ V := Module.Basis.mk hli (le_of_eq hb.symm)
  have hcoe : (be : ι → V) = e := Module.Basis.coe_mk hli (le_of_eq hb.symm)
  have hM : (fun i j => b.repr (e i) j) = (b.toMatrix (⇑be))ᵀ := by
    ext i j
    rw [Matrix.transpose_apply, Module.Basis.toMatrix_apply, hcoe]
  rw [hM, Matrix.det_transpose]
  haveI := Module.Basis.invertibleToMatrix b be
  exact (Matrix.isUnit_iff_isUnit_det _).mp (isUnit_of_invertible _)

theorem dRmNormSq_eq_N5_of_basis
    {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E] [CompleteSpace E]
    {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
    {M : Type*} [TopologicalSpace M] [T2Space M] [ChartedSpace H M] [IsManifold I ∞ M]
    [I.Boundaryless] (hLC : LCSmooth I M) {g : SMet I M} (x : M)
    (e : Fin (Module.finrank ℝ E) → TangentSpace I x)
    (Γ : Matrix (Fin (Module.finrank ℝ E)) (Fin (Module.finrank ℝ E)) ℝ)
    (hΓ : ∀ i j, Γ i j = g.inner x (e i) (e j))
    (hb : Submodule.span ℝ (Set.range e) = ⊤) :
    dRmNormSq g x
      = N5 Γ (fun m i j k l => covRm g x (e m) (e i) (e j) (e k) (e l)) := by
  rcases Nat.eq_zero_or_pos (Module.finrank ℝ E) with h0 | hpos
  · -- degenerate case: there are no indices at all
    haveI : IsEmpty (Fin (Module.finrank ℝ E)) := by rw [h0]; infer_instance
    simp only [dRmNormSq, N5, Finset.univ_eq_empty, Finset.sum_empty]
  · haveI : Nonempty (Fin (Module.finrank ℝ E)) := Fin.pos_iff_nonempty.mp hpos
    letI : RiemannianBundle (fun x : M ↦ TangentSpace I x) := ⟨g.toRiemannianMetric⟩
    haveI : IsContMDiffRiemannianBundle I ∞ E (fun x : M ↦ TangentSpace I x) := inferInstance
    haveI : FiniteDimensional ℝ (TangentSpace I x) := inferInstanceAs (FiniteDimensional ℝ E)
    let f : Fin (Module.finrank ℝ E) → TangentSpace I x := onFrame g x
    have hf : IsONFrame g x f := isONFrame_onFrame g x
    have hone : Orthonormal ℝ f := by
      rw [orthonormal_iff_ite]
      intro i j
      rw [show inner ℝ (f i) (f j) = g.inner x (f i) (f j) from rfl]
      exact hf i j
    have hcard : Fintype.card (Fin (Module.finrank ℝ E))
        = Module.finrank ℝ (TangentSpace I x) := by
      rw [Fintype.card_fin]; rfl
    let bf : Module.Basis (Fin (Module.finrank ℝ E)) ℝ (TangentSpace I x) :=
      basisOfOrthonormalOfCardEqFinrank hone hcard
    have hbf : (bf : Fin (Module.finrank ℝ E) → TangentSpace I x) = f :=
      coe_basisOfOrthonormalOfCardEqFinrank hone hcard
    let A : Matrix (Fin (Module.finrank ℝ E)) (Fin (Module.finrank ℝ E)) ℝ :=
      fun i j => bf.repr (e i) j
    have hAexp : ∀ i, e i = ∑ j, A i j • f j := by
      intro i
      have h := bf.sum_repr (e i)
      rw [hbf] at h
      exact h.symm
    have hdet : IsUnit A.det := isUnit_det_basis_repr bf e hb
    have hGram : A * Matrix.transpose A = Γ := by
      rw [mul_transpose_eq_gram x f e hf A hAexp]
      ext i j
      exact (hΓ i j).symm
    have hrot := covRm_eq_rot5 hLC g x f e A hAexp
    have hfrob : frobSq5 (fun m i j k l => covRm g x (f m) (f i) (f j) (f k) (f l))
        = dRmNormSq g x := rfl
    calc dRmNormSq g x
        = frobSq5 (fun m i j k l => covRm g x (f m) (f i) (f j) (f k) (f l)) :=
          hfrob.symm
      _ = N5 (A * Matrix.transpose A)
            (rot5 A (fun m i j k l => covRm g x (f m) (f i) (f j) (f k) (f l))) :=
          (frobSq5_rot A hdet _).symm
      _ = N5 Γ (fun m i j k l => covRm g x (e m) (e i) (e j) (e k) (e l)) := by
          rw [hGram, ← hrot]

end Work.Diff.GE
