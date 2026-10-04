import Mathlib
import Submission.Work.Diff.EXT.Basic
import Submission.Work.Diff.GE.curvbasic

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false

/-!
# The Ricci trace in an orthonormal frame

`Submission.Diff.ricAt` defines the Ricci tensor of a connection `cov` at a point `x` as the trace
of the endomorphism `w ↦ R(w,u)v` computed in the canonical basis `Module.finBasis ℝ E` of the
model space:

`ricAt cov x u v = ∑ i, (Module.finBasis ℝ E).coord i (rmVec cov x (finBasis i) u v)`.

This file computes the same trace in an *orthonormal* frame `e` of `(TₓM, g)`, which is the form
used everywhere in the curvature-evolution and maximum-principle arguments:

`ricAt (lcOf g) x u v = ∑ j, g(R(e_j,u)v, e_j)`.

The proof has three ingredients, all already available:

* `rmVec` is `ℝ`-linear in its first slot for a smooth connection
  (`Work.Diff.GE.rmVec_add_left`, `rmVec_smul_left`), so `w ↦ rmVec (lcOf g) x w u v` is a
  `LinearMap`;
* the trace of a linear endomorphism is independent of the basis
  (`LinearMap.trace_eq_matrix_trace`) so it may be read off in the canonical basis, giving `ricAt`;
* for an orthonormal basis `B`, `LinearMap.trace_eq_sum_inner` gives
  `trace T = ∑ i, ⟪B i, T (B i)⟫`, and `⟪a, b⟫ = ⟪b, a⟫` over `ℝ` turns this into
  `∑ i, g(T (e i), e i)`.

The only degenerate case is `finrank ℝ E = 0`, where `Fin (finrank ℝ E)` is empty and both sides
are the empty sum.
-/

open Bundle

namespace Work.EXT

theorem ricAt_eq_sum_frame
    {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E] [CompleteSpace E]
    {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
    {M : Type*} [TopologicalSpace M] [ChartedSpace H M] [IsManifold I (⊤ : ℕ∞) M] [T2Space M]
    (g : Submission.Diff.SMet I M)
    (hcov : CovariantDerivative.ContMDiffCovariantDerivative (Submission.Diff.lcOf g) (⊤ : ℕ∞))
    (x : M) (e : Fin (Module.finrank ℝ E) → TangentSpace I x)
    (he : Submission.Diff.IsONFrame g x e) (u v : TangentSpace I x) :
    Submission.Diff.ricAt (Submission.Diff.lcOf g) x u v =
      Finset.univ.sum (fun j => g.inner x (Submission.Diff.rmVec (Submission.Diff.lcOf g) x (e j) u v) (e j)) := by
  classical
  letI : RiemannianBundle (fun x : M ↦ TangentSpace I x) := ⟨g.toRiemannianMetric⟩
  haveI : IsContMDiffRiemannianBundle I (⊤ : ℕ∞) E (fun x : M ↦ TangentSpace I x) := inferInstance
  by_cases h0 : Module.finrank ℝ E = 0
  · -- no tangent vectors: both sums are empty
    haveI : IsEmpty (Fin (Module.finrank ℝ E)) := by rw [h0]; infer_instance
    simp [Submission.Diff.ricAt, Finset.univ_eq_empty]
  · haveI : Nonempty (Fin (Module.finrank ℝ E)) :=
      Fin.pos_iff_nonempty.mp (Nat.pos_of_ne_zero h0)
    -- the endomorphism `w ↦ R(w,u)v`, whose trace is `ricAt`
    let T : TangentSpace I x →ₗ[ℝ] TangentSpace I x :=
      { toFun := fun w => Submission.Diff.rmVec (Submission.Diff.lcOf g) x w u v
        map_add' := fun a b => Work.Diff.GE.rmVec_add_left (Submission.Diff.lcOf g) hcov x a b u v
        map_smul' := fun c a => Work.Diff.GE.rmVec_smul_left (Submission.Diff.lcOf g) hcov x c a u v }
    have hT : ∀ w : TangentSpace I x,
        T w = Submission.Diff.rmVec (Submission.Diff.lcOf g) x w u v := fun _ => rfl
    -- `ricAt` is the trace of `T`, computed in the canonical basis
    have htrace : Submission.Diff.ricAt (Submission.Diff.lcOf g) x u v
        = T.trace ℝ (TangentSpace I x) := by
      rw [LinearMap.trace_eq_matrix_trace ℝ (Module.finBasis ℝ (TangentSpace I x)) T]
      simp only [Submission.Diff.ricAt, Matrix.trace, Matrix.diag_apply, LinearMap.toMatrix_apply]
      apply Finset.sum_congr rfl
      intro i _
      rw [hT]
      rfl
    -- ... and, for an orthonormal frame, its diagonal entries are `g(T e_j, e_j)`
    have hsum : T.trace ℝ (TangentSpace I x) = ∑ j, g.inner x (T (e j)) (e j) := by
      have hon : Orthonormal ℝ e := by
        rw [orthonormal_iff_ite]
        intro i j
        rw [show Inner.inner ℝ (e i) (e j) = g.inner x (e i) (e j) from rfl]
        exact he i j
      let bb : Module.Basis (Fin (Module.finrank ℝ E)) ℝ (TangentSpace I x) :=
        basisOfOrthonormalOfCardEqFinrank hon (by rw [Fintype.card_fin]; rfl)
      have hb : (bb : Fin (Module.finrank ℝ E) → TangentSpace I x) = e :=
        coe_basisOfOrthonormalOfCardEqFinrank hon _
      have honb : Orthonormal ℝ (bb : Fin (Module.finrank ℝ E) → TangentSpace I x) := by
        rw [hb]; exact hon
      let B : OrthonormalBasis (Fin (Module.finrank ℝ E)) ℝ (TangentSpace I x) :=
        bb.toOrthonormalBasis honb
      have hB : ⇑B = e := by
        rw [Module.Basis.coe_toOrthonormalBasis]; exact hb
      rw [LinearMap.trace_eq_sum_inner T B]
      apply Finset.sum_congr rfl
      intro j _
      rw [hB, real_inner_comm (T (e j)) (e j)]
      rfl
    rw [htrace, hsum]
    apply Finset.sum_congr rfl
    intro j _
    rw [hT]

end Work.EXT
