import Mathlib
import Submission.Work.Diff.GE.Frame
import Submission.Work.Diff.GE.curvbasic

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false

/-!
# Two orthonormal frames at a point differ by an orthogonal matrix

The frozen interface `Submission.Diff.IsONFrame g x e` says that `e : Fin (finrank ℝ E) → TₓM` is
`g`-orthonormal at `x`. This file records the standard fact that any two such frames are related by
an orthogonal matrix: if `e` and `e'` are both `g`-orthonormal at `x`, then there is
`A ∈ Matrix.orthogonalGroup (Fin (finrank ℝ E)) ℝ` with `e' i = ∑ j, A i j • e j`.

This is what lets one transfer frame-dependent computations (curvature components `rmFrame`,
norms `|Rm|²`, ...) between the different orthonormal frames used in the gradient-estimate area.

The proof is elementary linear algebra. Installing `⟨g.toRiemannianMetric⟩` as the
`RiemannianBundle` instance on the tangent bundle turns `TₓM` into a real inner product space for
which `⟪·,·⟫` *is* `g.inner x` (definitionally, see `inner_eq_metric` in
`Submission/Work/Diff/GE/Frame.lean`), and turns `IsONFrame g x e` into `Orthonormal ℝ e`. An
orthonormal family of the right cardinality is then an orthonormal basis
(`basisOfOrthonormalOfCardEqFinrank`), and we take `A i j` to be the `j`-th coordinate of `e' i` in
that basis. The expansion `e' i = ∑ j, A i j • e j` is `OrthonormalBasis.sum_repr`; the orthogonality
`A * Aᵀ = 1` follows from Parseval, `OrthonormalBasis.sum_inner_mul_inner`
(`∑ j ⟪u, e j⟫ ⟪e j, w⟫ = ⟪u, w⟫`), together with `OrthonormalBasis.repr_apply_apply`, which says
that the coefficients are exactly the inner products with the basis vectors.

The degenerate case `finrank ℝ E = 0` is vacuous (`Fin 0` has no elements) and `A = 1` works.
-/

set_option linter.style.haveILetI false

open scoped Manifold ContDiff Bundle Topology
open Bundle

namespace Work.Diff.GE

theorem onFrame_orthogonal_change
    {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E] [CompleteSpace E]
    {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
    {M : Type*} [TopologicalSpace M] [ChartedSpace H M] [IsManifold I ((⊤ : ENat) : WithTop ENat) M] [T2Space M]
    (g : Submission.Diff.SMet I M) (x : M) (e e' : Fin (Module.finrank ℝ E) → TangentSpace I x)
    (he : Submission.Diff.IsONFrame g x e) (he' : Submission.Diff.IsONFrame g x e') :
    ∃ A : Matrix (Fin (Module.finrank ℝ E)) (Fin (Module.finrank ℝ E)) ℝ,
      A ∈ Matrix.orthogonalGroup (Fin (Module.finrank ℝ E)) ℝ ∧
        ∀ i, e' i = ∑ j, A i j • e j := by
  classical
  by_cases hn : 0 < Module.finrank ℝ E
  · -- the interesting case: `Fin (finrank ℝ E)` is nonempty
    letI : RiemannianBundle (fun x : M ↦ TangentSpace I x) := ⟨g.toRiemannianMetric⟩
    haveI : IsContMDiffRiemannianBundle I ∞ E (fun x : M ↦ TangentSpace I x) := inferInstance
    haveI : FiniteDimensional ℝ (TangentSpace I x) := inferInstanceAs (FiniteDimensional ℝ E)
    haveI : Nonempty (Fin (Module.finrank ℝ E)) := Fin.pos_iff_nonempty.mp hn
    -- the two frames are orthonormal for the instance inner product
    have hone : Orthonormal ℝ e := by
      rw [orthonormal_iff_ite]
      intro i j
      rw [show inner ℝ (e i) (e j) = g.inner x (e i) (e j) from rfl]
      exact he i j
    have hone' : Orthonormal ℝ e' := by
      rw [orthonormal_iff_ite]
      intro i j
      rw [show inner ℝ (e' i) (e' j) = g.inner x (e' i) (e' j) from rfl]
      exact he' i j
    -- `e` is an orthonormal basis of `TₓM`
    have hcard : Fintype.card (Fin (Module.finrank ℝ E)) = Module.finrank ℝ (TangentSpace I x) := by
      rw [Fintype.card_fin]; rfl
    let b₀ : Module.Basis (Fin (Module.finrank ℝ E)) ℝ (TangentSpace I x) :=
      basisOfOrthonormalOfCardEqFinrank hone hcard
    have hb₀ : (b₀ : Fin (Module.finrank ℝ E) → TangentSpace I x) = e :=
      coe_basisOfOrthonormalOfCardEqFinrank hone hcard
    have honb₀ : Orthonormal ℝ (b₀ : Fin (Module.finrank ℝ E) → TangentSpace I x) := by
      rw [hb₀]; exact hone
    let b : OrthonormalBasis (Fin (Module.finrank ℝ E)) ℝ (TangentSpace I x) :=
      b₀.toOrthonormalBasis honb₀
    have hb : (b : Fin (Module.finrank ℝ E) → TangentSpace I x) = e := by
      rw [Module.Basis.coe_toOrthonormalBasis, hb₀]
    -- the change-of-basis matrix: `A i j` is the `j`-th coordinate of `e' i` in the basis `e`
    let A : Matrix (Fin (Module.finrank ℝ E)) (Fin (Module.finrank ℝ E)) ℝ :=
      fun i j => b.repr (e' i) j
    refine ⟨A, ?_, ?_⟩
    · -- `A` is orthogonal: `A * Aᵀ = 1`
      rw [Matrix.mem_orthogonalGroup_iff]
      ext i k
      simp only [Matrix.mul_apply, Matrix.transpose_apply, Matrix.one_apply]
      dsimp only [A]
      -- Parseval: the entries evaluate to `⟪e' i, e' k⟫`
      have h1 : (∑ j, b.repr (e' i) j * b.repr (e' k) j) = inner ℝ (e' i) (e' k) := by
        rw [← b.sum_inner_mul_inner (e' i) (e' k)]
        refine Finset.sum_congr rfl fun j _ => ?_
        rw [b.repr_apply_apply, b.repr_apply_apply, real_inner_comm (e' i) (b j)]
      rw [h1, (orthonormal_iff_ite.mp hone') i k]
    · -- expansion of `e' i` in the basis `e`
      intro i
      dsimp only [A]
      have h := b.sum_repr (e' i)
      rw [hb] at h
      exact h.symm
  · -- degenerate case: there are no indices at all
    refine ⟨1, one_mem _, ?_⟩
    intro i
    exact absurd i.isLt (by omega)

end Work.Diff.GE
