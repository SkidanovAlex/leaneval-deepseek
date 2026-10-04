import Mathlib
import Submission.Work.Diff.GE.kato_deps

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false

namespace Work.Diff.GE

open LeanEval.Geometry.SphereTheorem Submission.Diff Submission.Diff.Alg
open scoped Manifold ContDiff Bundle Topology
open Bundle ContDiff Set VectorField CovariantDerivative Metric

/-- **The Levi-Civita connection is additive over a finite sum of scaled smooth fields.**

For a metric `g`, a point `x`, a finite family of smooth functions `f i` and a finite family of
smooth vector fields `Y i`, the covariant derivative of `∑ i, f i • Y i` in the direction
`v ∈ TₓM` is `∑ i, (f i x • ∇_v Y i + (d f i)ₓ(v) • Y i x)`.  This is exactly the combination of
the two structural properties of a covariant derivative, `IsCovariantDerivativeOn.add` and
`IsCovariantDerivativeOn.leibniz`, applied by induction on the finite set: additivity in the field
argument and the Leibniz rule in each coefficient. -/
theorem kato_lcOf_sum_apply
    {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E] [CompleteSpace E]
    {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
    {M : Type*} [TopologicalSpace M] [T2Space M] [ChartedSpace H M] [IsManifold I ∞ M]
    (g : SMet I M) (x : M) {ι : Type*} (s : Finset ι) (f : ι → M → ℝ)
    (Y : ι → Π y : M, TangentSpace I y) (hf : ∀ i ∈ s, CMDiff ∞ (f i))
    (hY : ∀ i ∈ s, CMDiff ∞ (T% (Y i))) (v : TangentSpace I x) :
    lcOf g (∑ i ∈ s, f i • Y i) x v
      = ∑ i ∈ s, (f i x • lcOf g (Y i) x v + mvfderiv I (f i) x v • Y i x) := by
  classical
  -- The statement for an arbitrary finite set `t ⊆ s` (so that it can be proved by induction),
  -- with the smoothness hypotheses relativised to `t`.
  have key : ∀ t : Finset ι,
      (∀ i ∈ t, CMDiff ∞ (f i)) → (∀ i ∈ t, CMDiff ∞ (T% (Y i))) →
      ∀ v : TangentSpace I x,
        lcOf g (∑ i ∈ t, f i • Y i) x v
          = ∑ i ∈ t, (f i x • lcOf g (Y i) x v + mvfderiv I (f i) x v • Y i x) := by
    intro t
    induction t using Finset.induction with
    | empty =>
      -- `∇ 0 = 0` for the zero section (`CovariantDerivative.zero`), and the empty sum vanishes.
      intro _ _ v
      simp
    | insert a t ha ih =>
      intro hft hYt v
      have hfa : CMDiff ∞ (f a) := hft a (Finset.mem_insert_self a t)
      have hYa : CMDiff ∞ (T% (Y a)) := hYt a (Finset.mem_insert_self a t)
      have hft' : ∀ i ∈ t, CMDiff ∞ (f i) := fun i hi => hft i (Finset.mem_insert_of_mem hi)
      have hYt' : ∀ i ∈ t, CMDiff ∞ (T% (Y i)) := fun i hi => hYt i (Finset.mem_insert_of_mem hi)
      rw [Finset.sum_insert ha, Finset.sum_insert ha]
      -- Differentiability at `x` of the two pieces, as required by additivity.
      have h1 : MDiffAt (T% (f a • Y a)) x := (hfa.smul_section hYa).mdifferentiableAt (by simp)
      have h2 : MDiffAt (T% (∑ i ∈ t, f i • Y i)) x := by
        simpa only [Finset.sum_apply] using
          ((ContMDiff.sum_section (fun i hi => (hft' i hi).smul_section (hYt' i hi))).mdifferentiableAt
            (by simp) : MDiffAt (T% (fun y : M => ∑ i ∈ t, (f i • Y i) y)) x)
      -- Additivity of `∇` in the field argument ...
      rw [congrArg (fun L : TangentSpace I x →L[ℝ] TangentSpace I x => L v)
        ((lcOf g).isCovariantDerivativeOn.add h1 h2), add_apply]
      -- ... the Leibniz rule for the new term ...
      have hlei : (lcOf g) (f a • Y a) x
          = f a x • (lcOf g) (Y a) x + (mvfderiv I (f a) x).smulRight (Y a x) :=
        (lcOf g).isCovariantDerivativeOn.leibniz (σ := Y a) (g := f a)
          (hYa.mdifferentiableAt (by simp)) (hfa.mdifferentiableAt (by simp))
      -- ... and the induction hypothesis for the remaining sum.
      rw [congrArg (fun L : TangentSpace I x →L[ℝ] TangentSpace I x => L v) hlei,
        ih hft' hYt' v]
      simp only [add_apply, smul_apply, ContinuousLinearMap.smulRight_apply]
  exact key s hf hY v

end Work.Diff.GE
