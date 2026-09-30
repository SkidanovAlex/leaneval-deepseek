import Mathlib

-- Lean v4.35.0-rc3 / Mathlib 5e0c4e5 made `isDefEq` respect transparency when unifying instances; with it,
-- `ZMod.instField` and `ZMod.commRing` (and `Neg (ZMod p)` via `SubtractionMonoid`) no longer unify, which
-- breaks `ring`/`rw`/module-instance search on `ZMod p`. Restore the v4.34 behaviour for this file.
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false


namespace Commons.Geometry.Manifold.VectorBundle.CovariantDerivative

open scoped _root_.Manifold _root_.ContDiff
open _root_.VectorField Filter

/-- **Covariant derivative of a section given as a finite sum, pointwise version.**
Same as `Commons.Geometry.Manifold.VectorBundle.CovariantDerivative.cov_eq_sum_of_eventuallyEq`
but with the smoothness hypotheses only at the point `x` (this is the form in which the
constant-coordinate frame sections of a chart, which are smooth only on the chart, can be
used). -/
theorem cov_eq_sum_of_eventuallyEq_pointwise
    {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
    {M : Type*} [TopologicalSpace M] [ChartedSpace H M] [IsManifold I ∞ M]
    {cov : CovariantDerivative I E (TangentSpace I (M := M))}
    {ι : Type*} (s : Finset ι) (f : ι → M → ℝ) (σ : ι → Π x : M, TangentSpace I x)
    {Z : Π x : M, TangentSpace I x} {x : M} {v : TangentSpace I x}
    (hZ : CMDiffAt ∞ (T% Z) x) (hσ : ∀ i, CMDiffAt ∞ (T% (σ i)) x)
    (hf : ∀ i, CMDiffAt ∞ (f i) x)
    (heq : Z =ᶠ[nhds x] fun y => ∑ i ∈ s, f i y • σ i y) :
    cov Z x v = ∑ i ∈ s, f i x • cov (σ i) x v
      + ∑ i ∈ s, mvfderiv I (f i) x v • σ i x := by
  classical
  -- smoothness (at `x`) of the partial sums
  have hsum_diff : ∀ t : Finset ι,
      MDiffAt (T% (fun y : M => ∑ i ∈ t, f i y • σ i y)) x := by
    intro t
    exact MDifferentiableAt.sum_section
      (fun i _ => ((hf i).mdifferentiableAt (by simp)).smul_section
        ((hσ i).mdifferentiableAt (by simp)))
  -- germ reduction: replace `Z` by the sum
  have hcongr : cov Z x = cov (fun y : M => ∑ i ∈ s, f i y • σ i y) x :=
    cov.isCovariantDerivativeOn.congr_of_eventuallyEq
      ((hZ).mdifferentiableAt (by simp))
      (hsum_diff s)
      Filter.univ_mem heq
  rw [hcongr]
  -- the finite-sum Leibniz computation
  have key : ∀ t : Finset ι,
      cov (fun y : M => ∑ i ∈ t, f i y • σ i y) x v
        = ∑ i ∈ t, f i x • cov (σ i) x v + ∑ i ∈ t, mvfderiv I (f i) x v • σ i x := by
    intro t
    induction t using Finset.induction_on with
    | empty =>
      have hzero : (fun y : M => ∑ i ∈ (∅ : Finset ι), f i y • σ i y) = 0 := by
        funext y
        simp
      rw [hzero]
      simp [CovariantDerivative.zero]
    | insert a t ha ih =>
      have hfa : MDiffAt (T% (f a • σ a)) x :=
        ((hf a).mdifferentiableAt (by simp)).smul_section
          ((hσ a).mdifferentiableAt (by simp))
      have hsumt : MDiffAt (T% (fun y : M => ∑ i ∈ t, f i y • σ i y)) x := hsum_diff t
      have hfun : (fun y : M => ∑ i ∈ insert a t, f i y • σ i y)
          = (f a • σ a) + (fun y : M => ∑ i ∈ t, f i y • σ i y) := by
        funext y
        simp [Finset.sum_insert ha]
      rw [hfun]
      have hadd := cov.isCovariantDerivativeOn.add hfa hsumt
      have haddv : cov ((f a • σ a) + (fun y : M => ∑ i ∈ t, f i y • σ i y)) x v
          = cov (f a • σ a) x v + cov (fun y : M => ∑ i ∈ t, f i y • σ i y) x v := by
        rw [congrArg (fun L : TangentSpace I x →L[ℝ] TangentSpace I x => L v) hadd, add_apply]
      rw [haddv]
      have hleibv : cov (f a • σ a) x v
          = f a x • cov (σ a) x v + mvfderiv I (f a) x v • σ a x := by
        have hL := cov.isCovariantDerivativeOn.leibniz (σ := σ a) (g := f a)
          ((hσ a).mdifferentiableAt (by simp)) ((hf a).mdifferentiableAt (by simp))
        rw [congrArg (fun L : TangentSpace I x →L[ℝ] TangentSpace I x => L v) hL,
          add_apply, smul_apply, ContinuousLinearMap.smulRight_apply]
      rw [hleibv, ih]
      rw [Finset.sum_insert ha, Finset.sum_insert ha]
      abel
  exact key s

end Commons.Geometry.Manifold.VectorBundle.CovariantDerivative
