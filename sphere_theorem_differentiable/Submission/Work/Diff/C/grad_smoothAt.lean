import Mathlib
import Submission.Work.Diff.C.Defs
import Submission.Work.Diff.C.mvfderiv_contMDiffAt
import Submission.Work.Diff.GE.smooth_onframe
import Submission.Work.Diff.L.Defs

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false

/-!
# Smoothness of the gradient at a point (`Work.Diff.C.grad_smoothAt`)

`Work.Diff.C.rgrad F` is the gradient of a real function on a Riemannian manifold with respect to
the ambient (`RiemannianBundle`) metric: the Riesz representative of `mfderiv F`.

The point of this file is the **pointwise** statement

`CMDiffAt ∞ F x → CMDiffAt ∞ (T% (rgrad F)) x`,

in which the hypothesis is the *weak* `C^∞`-at-a-point notion of Mathlib: for every `m` there is a
neighbourhood (depending on `m`) on which `F` is `C^m`.  This is exactly the hypothesis that the
argument needs, and the reason the proof goes through is a separation of the neighbourhoods:

* `CMDiffAt ∞ F x` unpacks, for the order `m+1`, to `F` being `C^{m+1}` on a neighbourhood `U_m`;
* on `U_m` the gradient is expanded in a smooth local orthonormal frame,
  `rgrad F = ∑ᵢ (dF(eᵢ)) eᵢ` (no inverse of the Gram matrix is needed because the frame is
  orthonormal);
* `Work.Diff.C.mvfderiv_contMDiffAt` is itself stated with the weak hypothesis `CMDiffAt ∞ F x`
  and re-derives `U_m` inside, so it applies verbatim;
* smooth sections are closed under finite sums and scalar multiplication
  (`ContMDiffAt.sum_section`, `ContMDiffAt.smul_section`), so `rgrad F` is `C^m` on `U_m`, and
  `CMDiffAt ∞` at `x` only asks for this for every `m`.

The only genuinely new ingredients are the three elementary lemmas below (an orthonormal family
whose index type has cardinality `finrank` expands every vector in a finite-dimensional real inner
product space, the defining property of `rgrad` against `mvfderiv`, and the translation of
`IsONFrame` for `Work.Diff.L.initSMet` into `Orthonormal` for the ambient inner product).
-/

namespace Work.Diff.C

open scoped Manifold ContDiff Bundle Topology BigOperators
open Bundle Set VectorField CovariantDerivative Metric Filter
open LeanEval.Geometry.SphereTheorem Submission.Diff Submission.Diff.Alg

set_option linter.unusedSectionVars false

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]
  [CompleteSpace E]
  {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
  {M : Type*} [TopologicalSpace M] [T2Space M] [ChartedSpace H M] [IsManifold I ∞ M]
  [RiemannianBundle (fun x : M ↦ TangentSpace I x)]
  [IsContMDiffRiemannianBundle I ∞ E (fun x : M ↦ TangentSpace I x)]

/-! ## Elementary Hilbert-space and gradient lemmas -/

/-- In a finite-dimensional real inner product space, an orthonormal family whose index type has
cardinality `finrank` expands every vector. -/
lemma sum_inner_smul_eq_of_orthonormal {V : Type*} [NormedAddCommGroup V] [InnerProductSpace ℝ V]
    [FiniteDimensional ℝ V] {ι : Type*} [Fintype ι] {f : ι → V}
    (hf : Orthonormal ℝ f) (hcard : Fintype.card ι = Module.finrank ℝ V) (v : V) :
    ∑ i, Inner.inner ℝ v (f i) • f i = v := by
  classical
  rcases isEmpty_or_nonempty ι with hι | hι
  · haveI := hι
    have hfin : Module.finrank ℝ V = 0 := by
      rw [← hcard]
      exact Fintype.card_eq_zero
    have hsub : Subsingleton V := Module.finrank_zero_iff.mp hfin
    simp [Subsingleton.elim v 0]
  · haveI := hι
    let b : Module.Basis ι ℝ V := basisOfLinearIndependentOfCardEqFinrank hf.linearIndependent hcard
    have hb : (b : ι → V) = f := coe_basisOfLinearIndependentOfCardEqFinrank _ _
    have hcoeff : ∀ i, Inner.inner ℝ v (f i) = b.repr v i := by
      intro i
      rw [← hb]
      conv_lhs => rw [← b.sum_repr v]
      rw [sum_inner, Finset.sum_eq_single i]
      · rw [inner_smul_left, hb, real_inner_self_eq_norm_sq, hf.1 i]
        simp
      · intro j _ hj
        rw [inner_smul_left, hb, hf.2 hj, mul_zero]
      · intro hi
        exact absurd (Finset.mem_univ i) hi
    calc ∑ i, Inner.inner ℝ v (f i) • f i = ∑ i, b.repr v i • b i := by simp [hcoeff, hb]
      _ = v := b.sum_repr v

/-- The defining property of `rgrad`, in terms of `mvfderiv`. -/
lemma inner_rgrad_mvfderiv (F : M → ℝ) (x : M) (v : TangentSpace I x) :
    Inner.inner ℝ (rgrad (I := I) F x) v = mvfderiv I F x v := by
  rw [inner_rgrad]
  simp only [mvfderiv]
  rfl

/-- `IsONFrame` for the ambient metric (`Work.Diff.L.initSMet`), read with the instance inner
product, is Mathlib's `Orthonormal`. -/
lemma orthonormal_of_initSMet_isONFrame {x : M}
    {f : Fin (Module.finrank ℝ E) → TangentSpace I x}
    (h : IsONFrame (Work.Diff.L.initSMet (I := I) (M := M)) x f) :
    Orthonormal ℝ f := by
  constructor
  · intro i
    have h1 : Inner.inner ℝ (f i) (f i) = 1 := by
      rw [← Work.Diff.L.initSMet_inner, h i i, if_pos rfl]
    rw [norm_eq_sqrt_real_inner, h1, Real.sqrt_one]
  · intro i j hij
    rw [← Work.Diff.L.initSMet_inner, h i j, if_neg hij]

/-! ## The main theorem -/

open scoped Manifold ContDiff Bundle Topology in
theorem grad_smoothAt
    {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E] [CompleteSpace E]
    {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
    {M : Type*} [TopologicalSpace M] [T2Space M] [ChartedSpace H M] [IsManifold I ∞ M]
    [Bundle.RiemannianBundle (fun x : M ↦ TangentSpace I x)]
    [IsContMDiffRiemannianBundle I ∞ E (fun x : M ↦ TangentSpace I x)]
    {F : M → ℝ} {x : M} (hF : CMDiffAt ∞ F x) :
    CMDiffAt ∞ (T% (Work.Diff.C.rgrad (I := I) F)) x := by
  obtain ⟨f, hON, hfsm⟩ :=
    Work.Diff.GE.smooth_onframe (I := I) (M := M) (Work.Diff.L.initSMet (I := I) (M := M)) x
  -- the scalar coefficients `y ↦ dF_y (eᵢ(y))` are smooth at `x`, from the weak hypothesis
  have hscalar : ∀ i, CMDiffAt ∞ (fun y : M ↦ mvfderiv I F y (f y i)) x := fun i =>
    mvfderiv_contMDiffAt hF (hfsm i)
  have hterm : ∀ i, CMDiffAt ∞ (T% (fun y : M ↦ mvfderiv I F y (f y i) • f y i)) x := fun i =>
    (hscalar i).smul_section (hfsm i)
  have hsum : CMDiffAt ∞ (T% (fun y : M ↦ ∑ i, mvfderiv I F y (f y i) • f y i)) x :=
    ContMDiffAt.sum_section (fun i _ => hterm i)
  refine hsum.congr_of_eventuallyEq ?_
  filter_upwards [hON] with y hy
  have horth : Orthonormal ℝ (fun i => f y i) := orthonormal_of_initSMet_isONFrame hy
  have hvec : rgrad (I := I) F y = ∑ i, mvfderiv I F y (f y i) • f y i := by
    rw [← sum_inner_smul_eq_of_orthonormal horth (by rw [Fintype.card_fin]; rfl)
      (rgrad (I := I) F y)]
    exact Finset.sum_congr rfl (fun i _ => by rw [inner_rgrad_mvfderiv])
  show (⟨y, rgrad (I := I) F y⟩ : TotalSpace E (TangentSpace I))
      = ⟨y, ∑ i, mvfderiv I F y (f y i) • f y i⟩
  rw [hvec]

end Work.Diff.C
