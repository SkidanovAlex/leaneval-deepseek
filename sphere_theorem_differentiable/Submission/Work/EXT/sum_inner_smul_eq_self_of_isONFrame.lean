import Mathlib
import Submission.Work.Diff.EXT.Basic
import Submission.Work.Diff.GE.linearIndependent_of_isONFrame

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false

namespace Work.EXT

open scoped Manifold ContDiff Bundle Topology
open Bundle ContDiff Set

set_option linter.style.haveILetI false in
/-- Expansion of a tangent vector in an orthonormal frame: if `e : Fin (finrank ℝ E) → T_xM` satisfies `IsONFrame g x e` (i.e. `g.inner x (e i) (e j) = if i = j then 1 else 0`), so that it is an orthonormal basis of `T_xM`, then `∑ i, g.inner x v (e i) • e i = v` for every `v : T_xM`.  The degenerate case `finrank ℝ E = 0` must be handled (empty sum, `v = 0`); the related lemma `Work.Diff.GE.sum_smul_inner_eq_self` assumes `0 < finrank ℝ E`, which is not available here. -/
theorem sum_inner_smul_eq_self_of_isONFrame
    {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E] [CompleteSpace E]
    {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
    {M : Type*} [TopologicalSpace M] [ChartedSpace H M] [IsManifold I (⊤ : ℕ∞) M]
    (g : Submission.Diff.SMet I M) (x : M)
    (e : Fin (Module.finrank ℝ E) → TangentSpace I x)
    (he : Submission.Diff.IsONFrame g x e) (v : TangentSpace I x) :
    ∑ i, g.inner x v (e i) • e i = v := by
  -- Work with the inner product space structure on the tangent space induced by `g`.
  classical
  letI : RiemannianBundle (fun x : M ↦ TangentSpace I x) := ⟨g.toRiemannianMetric⟩
  haveI : IsContMDiffRiemannianBundle I (⊤ : ℕ∞) E (fun x : M ↦ TangentSpace I x) := inferInstance
  haveI : FiniteDimensional ℝ (TangentSpace I x) := inferInstanceAs (FiniteDimensional ℝ E)
  -- `e` is orthonormal for that inner product (`Inner.inner ℝ` is `g.inner x` by definition).
  have hon : Orthonormal ℝ e := by
    rw [orthonormal_iff_ite]
    intro i j
    rw [show Inner.inner ℝ (e i) (e j) = g.inner x (e i) (e j) from rfl]
    exact he i j
  have hli : LinearIndependent ℝ e := hon.linearIndependent
  have hcard : Fintype.card (Fin (Module.finrank ℝ E)) = Module.finrank ℝ (TangentSpace I x) := by
    rw [Fintype.card_fin]; rfl
  -- A linearly independent family of `finrank` vectors is a basis.  The primed version of the
  -- Mathlib constructor needs no `Nonempty ι`, which is exactly what is required for the degenerate
  -- case `finrank ℝ E = 0` (there the empty family *is* a basis of the trivial space).
  let bb : Module.Basis (Fin (Module.finrank ℝ E)) ℝ (TangentSpace I x) :=
    basisOfLinearIndependentOfCardEqFinrank' e hli hcard
  have hb : (bb : Fin (Module.finrank ℝ E) → TangentSpace I x) = e :=
    coe_basisOfLinearIndependentOfCardEqFinrank' e hli hcard
  have honb : Orthonormal ℝ (bb : Fin (Module.finrank ℝ E) → TangentSpace I x) := by
    rw [hb]; exact hon
  let B : OrthonormalBasis (Fin (Module.finrank ℝ E)) ℝ (TangentSpace I x) := bb.toOrthonormalBasis honb
  have hB : (B : Fin (Module.finrank ℝ E) → TangentSpace I x) = e := by
    rw [Module.Basis.coe_toOrthonormalBasis]; exact hb
  -- `OrthonormalBasis.sum_repr'` is the expansion in the orthonormal basis `B`, which is `e`.
  refine Eq.trans ?_ (B.sum_repr' v)
  apply Finset.sum_congr rfl
  intro i _
  rw [hB]
  congr 1
  exact (g.symm x v (e i)).trans rfl

end Work.EXT
