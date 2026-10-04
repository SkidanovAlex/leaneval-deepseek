import Mathlib
import Submission.Work.Diff.GE.deps
import Submission.Work.Diff.GE.frobSq5_rot
import Submission.Work.Diff.GE.rmFrame_eq_rot
import Submission.Work.Diff.GE.covRm_linear
import Submission.Work.Diff.GE.dRmNormSq_eq_N5_of_basis

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false

/-!
# `|∇Rm|²` in the coordinate frame of a chart

The frozen `Submission.Diff.dRmNormSq g y` is `|∇Rm|²` computed in the `Classical.epsilon`-chosen
orthonormal frame `onFrame g y`.  For the analytic applications (regularity of the curvature
quantities along a Ricci flow) one needs instead the *explicit* chart expression: the same number is
the full contraction `N5 Γ S` of the `∇Rm`-components `S m i j k l` in the coordinate frame
`cFrame x₀ ·` of the chart at `x₀` with the inverse Gram matrix `Γ = GramM` of that frame.

The general basis statement (an arbitrary spanning family `e` with Gram matrix `Γ`) is
`Work.Diff.GE.dRmNormSq_eq_N5_of_basis`; its proof, however, carries a spurious `[I.Boundaryless]`
hypothesis (nothing in the argument uses boundarylessness — the frame `onFrame g y`, its
orthonormality, the multilinearity `covRm_eq_rot5` and the algebra `frobSq5_rot` all need only
smoothness).  Since the request here is stated without `[I.Boundaryless]`, the general statement is
re-proved below (`dRmNormSq_eq_N5_of_basis_nb`) with the hypothesis dropped, and then specialised to
the coordinate frame.  The argument is the classical one:

* write `e i = ∑ j, A i j • f j` in the orthonormal frame `f = onFrame g y`; `A` is invertible
  because `e` spans (`isUnit_det_basis_repr`),
* `Γ = A * Aᵀ` (`mul_transpose_eq_gram`, the Parseval identity for an orthonormal frame),
* the `∇Rm`-components rotate by `A` (`covRm_eq_rot5`),
* and `N5 (A * Aᵀ) (rot5 A S) = frobSq5 S` (`frobSq5_rot`), whose right-hand side is `dRmNormSq`.

For the coordinate frame the spanning hypothesis is `cFrame_span_of_chartSource`: at every point of the chart at
`x₀` the fields `cFrame x₀ i` are `frameVector`-images of the canonical basis of the model space,
and any tangent vector is the sum of its canonical-coordinate components in that frame
(`Commons.Geometry.Manifold.Tangent.eqOn_sum_frameSection_of_basis`).
-/

set_option linter.style.haveILetI false
set_option linter.unusedSectionVars false

open LeanEval.Geometry.SphereTheorem Submission.Diff Submission.Diff.Alg
open scoped Manifold ContDiff Bundle Topology BigOperators Matrix
open Bundle ContDiff Set VectorField CovariantDerivative Metric

namespace Work.Diff.GE

variable
  {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E] [CompleteSpace E]
  {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
  {M : Type*} [TopologicalSpace M] [T2Space M] [ChartedSpace H M] [IsManifold I ∞ M]

/-! ## The coordinate frame spans the tangent space -/

/-- At every point of the chart at `x₀`, the coordinate frame `cFrame x₀ ·` spans the tangent
space: any tangent vector is the sum of its canonical-coordinate components in that frame. -/
theorem cFrame_span_of_chartSource (x₀ : M) {p : M} (hp : p ∈ (chartAt H x₀).source) :
    Submodule.span ℝ (Set.range (fun i : Fin (Module.finrank ℝ E) ↦ cFrame (I := I) x₀ i p))
      = ⊤ := by
  refine Submodule.eq_top_iff'.2 fun w => ?_
  have hb : p ∈ (trivializationAt E (TangentSpace I) x₀).baseSet := by
    rw [TangentBundle.trivializationAt_baseSet]; exact hp
  set c := (trivializationAt E (TangentSpace I) x₀).continuousLinearMapAt ℝ p w with hc
  have hspec : Submission.Geodesic.frameSection (I := I) x₀ c p
      = ∑ i : Fin (Module.finrank ℝ E), ((Module.finBasis ℝ E).coord i) c
          • cFrame (I := I) x₀ i p := by
    have h1 := Commons.Geometry.Manifold.Tangent.eqOn_sum_frameSection_of_basis (I := I)
      (b := Module.finBasis ℝ E) x₀ (Submission.Geodesic.frameSection (I := I) x₀ c) hp
    have h2 : (trivializationAt E (TangentSpace I) x₀).continuousLinearMapAt ℝ p
        (Submission.Geodesic.frameSection (I := I) x₀ c p) = c := by
      show (trivializationAt E (TangentSpace I) x₀).continuousLinearMapAt ℝ p
        ((trivializationAt E (TangentSpace I) x₀).symmL ℝ p c) = c
      exact Trivialization.continuousLinearMapAt_symmL _ hb c
    have h3 := h1
    simp only [] at h3
    rw [h3, h2]
    rfl
  have hlhs : Submission.Geodesic.frameSection (I := I) x₀ c p = w :=
    (trivializationAt E (TangentSpace I) x₀).symmL_continuousLinearMapAt hb w
  rw [← hlhs, hspec]
  refine Submodule.sum_mem _ fun i _ => Submodule.smul_mem _ _ ?_
  exact Submodule.subset_span (Set.mem_range_self i)

/-! ## `|∇Rm|²` in a general basis (without `I.Boundaryless`) -/

/-- **`|∇Rm|²` in a general basis.**  This is `Work.Diff.GE.dRmNormSq_eq_N5_of_basis` with the
spurious `[I.Boundaryless]` hypothesis removed (the argument below does not use it). -/
theorem dRmNormSq_eq_N5_of_basis_nb
    (hLC : LCSmooth I M) {g : SMet I M} (x : M)
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

/-! ## The requested statement -/

theorem dRmNormSq_eq_N5
    {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E] [CompleteSpace E]
    {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
    {M : Type*} [TopologicalSpace M] [T2Space M] [ChartedSpace H M] [IsManifold I ∞ M]
    (hLC : LCSmooth I M) (G : ℝ → SMet I M) {x₀ : M} (t : ℝ) {y : M}
    (hy : y ∈ (chartAt H x₀).source) :
    dRmNormSq (G t) y
      = N5 (GramM (I := I) G x₀ t y) (covRmC5 (I := I) G x₀ t y) := by
  have h := dRmNormSq_eq_N5_of_basis_nb (I := I) (M := M) hLC (g := G t) (x := y)
    (fun i => cFrame (I := I) x₀ i y) (GramM (I := I) G x₀ t y)
    (fun i j => rfl) (cFrame_span_of_chartSource (I := I) (M := M) x₀ hy)
  have h' : covRmC5 (I := I) G x₀ t y
      = fun m i j k l => covRm (G t) y (cFrame (I := I) x₀ m y) (cFrame (I := I) x₀ i y)
          (cFrame (I := I) x₀ j y) (cFrame (I := I) x₀ k y) (cFrame (I := I) x₀ l y) := rfl
  rw [h']
  exact h

end Work.Diff.GE
