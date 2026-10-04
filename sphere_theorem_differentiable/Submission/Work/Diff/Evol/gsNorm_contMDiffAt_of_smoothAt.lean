import Mathlib
import Submission.Work.Diff.GE.onFrameONfield

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false

/-!
# Smoothness of the pointwise Gram–Schmidt orthonormalisation from *pointwise* smoothness

`Work.Diff.Evol.gsNorm_contMDiffAt_of_smoothAt` : if the sections `F i` are `C^∞` **at** `y` (not
on all of `M`) and the family `F · y` is linearly independent at `y`, then the pointwise
Gram–Schmidt orthonormalisation `Work.Diff.GE.gsNorm g F i` is `C^∞` at `y`.

This is the local form of `Work.Diff.GE.gsNorm_contMDiffAt_of_linearIndependent` (which assumes
`∀ i, CMDiff ∞ (T% (F i))`, i.e. global smoothness, and carries a `[T2Space M]` assumption).  That
proof is built from the four local ingredients

* `metric_pairingAt` — the metric pairing of two sections smooth at `x` is smooth at `x`,
* `sqrt_inner_inv_contMDiffAt` — the reciprocal of the length of such a section is smooth,
* `gs_step` — one Gram–Schmidt projection step, and
* the `Nat.strong_induction_on` over the Gram–Schmidt index,

none of which uses anything global; the `[T2Space M]` in `Work.Diff.GE` merely rode along from the
variable block of that file (it is used there only for `SmoothBumpFunction` in the *globalisation*
lemma `exists_smooth_section_eq_nhds`).  Hence the same proof goes through verbatim with pointwise
hypotheses, which is what is needed e.g. for the coordinate frame of a chart, which is smooth only
on the chart source.
-/

set_option maxHeartbeats 1000000
set_option linter.unusedSectionVars false
set_option linter.style.haveILetI false

open LeanEval.Geometry.SphereTheorem Submission.Diff Submission.Diff.Alg
open scoped Manifold ContDiff Bundle Topology BigOperators
open Bundle ContDiff Set VectorField CovariantDerivative Metric Filter

namespace Work.Diff.Evol

/-! ## The elementary smoothness ingredients (pointwise form) -/

/-- The metric pairing `y ↦ g.inner y (X y) (Y y)` of two sections that are smooth at `x` is
smooth at `x`.  (Pointwise form of `Work.Diff.GE.metric_pairing`.) -/
theorem metric_pairingAt
    {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E] [CompleteSpace E]
    {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
    {M : Type*} [TopologicalSpace M] [ChartedSpace H M]
    [IsManifold I (((⊤ : ℕ∞) : WithTop ℕ∞)) M]
    (g : Submission.Diff.SMet I M) (x : M) {X Y : Π y : M, TangentSpace I y}
    (hX : CMDiffAt ∞ (T% X) x) (hY : CMDiffAt ∞ (T% Y) x) :
    CMDiffAt ∞ (fun y : M => g.inner y (X y) (Y y)) x := by
  letI : RiemannianBundle (fun x : M ↦ TangentSpace I x) := ⟨g.toRiemannianMetric⟩
  haveI : IsContMDiffRiemannianBundle I ∞ E (fun x : M ↦ TangentSpace I x) := inferInstance
  exact ContMDiffAt.inner_bundle (F := E) (E := fun x : M ↦ TangentSpace I x) (b := id) hX hY

/-- The reciprocal square root of the squared length of a section that is smooth and non-zero at
`x` is smooth at `x`.  (Pointwise form of `Work.Diff.GE.sqrt_inner_inv_contMDiffAt`.) -/
theorem sqrt_inner_inv_contMDiffAt
    {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E] [CompleteSpace E]
    {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
    {M : Type*} [TopologicalSpace M] [ChartedSpace H M]
    [IsManifold I (((⊤ : ℕ∞) : WithTop ℕ∞)) M]
    (g : Submission.Diff.SMet I M) (x : M) {X : Π y : M, TangentSpace I y}
    (hX : CMDiffAt ∞ (T% X) x) (hXx : X x ≠ 0) :
    CMDiffAt ∞ (fun y : M => (Real.sqrt (g.inner y (X y) (X y)))⁻¹) x := by
  letI : RiemannianBundle (fun x : M ↦ TangentSpace I x) := ⟨g.toRiemannianMetric⟩
  haveI : IsContMDiffRiemannianBundle I ∞ E (fun x : M ↦ TangentSpace I x) := inferInstance
  have hS : CMDiffAt ∞ (fun y : M => g.inner y (X y) (X y)) x := metric_pairingAt g x hX hX
  have hpos : 0 < g.inner x (X x) (X x) := g.pos x (X x) hXx
  have h1 : CMDiffAt ∞ (fun y : M => Real.sqrt (g.inner y (X y) (X y))) x :=
    ContMDiffAt.comp x (contMDiffAt_iff_contDiffAt.mpr (Real.contDiffAt_sqrt hpos.ne')) hS
  exact ContMDiffAt.inv₀ h1 (Real.sqrt_pos.mpr hpos).ne'

/-- One Gram–Schmidt subtraction step: subtracting from a section `X` smooth at `x` its orthogonal
projections onto the sections `A i` (smooth at `x`, with lengths non-zero at `x`) is smooth at `x`.
(Pointwise form of `Work.Diff.GE.gs_step`.) -/
theorem gs_step
    {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E] [CompleteSpace E]
    {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
    {M : Type*} [TopologicalSpace M] [ChartedSpace H M]
    [IsManifold I (((⊤ : ℕ∞) : WithTop ℕ∞)) M]
    (g : Submission.Diff.SMet I M) (x : M) {ι : Type*} (s : Finset ι)
    {A : ι → Π y : M, TangentSpace I y} {X : Π y : M, TangentSpace I y}
    (hA : ∀ i ∈ s, CMDiffAt ∞ (T% (A i)) x)
    (hX : CMDiffAt ∞ (T% X) x)
    (hne : ∀ i ∈ s, g.inner x (A i x) (A i x) ≠ 0) :
    CMDiffAt ∞ (T% (fun y : M => X y - ∑ i ∈ s,
      ((g.inner y (A i y) (X y)) * (g.inner y (A i y) (A i y))⁻¹) • A i y)) x := by
  letI : RiemannianBundle (fun x : M ↦ TangentSpace I x) := ⟨g.toRiemannianMetric⟩
  haveI : IsContMDiffRiemannianBundle I ∞ E (fun x : M ↦ TangentSpace I x) := inferInstance
  have hterm : ∀ i ∈ s, CMDiffAt ∞ (T% (fun y : M =>
      ((g.inner y (A i y) (X y)) * (g.inner y (A i y) (A i y))⁻¹) • A i y)) x := by
    intro i hi
    have h1 : CMDiffAt ∞ (fun y : M => g.inner y (A i y) (X y)) x :=
      metric_pairingAt g x (hA i hi) hX
    have h2 : CMDiffAt ∞ (fun y : M => g.inner y (A i y) (A i y)) x :=
      metric_pairingAt g x (hA i hi) (hA i hi)
    have h3 : CMDiffAt ∞ (fun y : M => (g.inner y (A i y) (A i y))⁻¹) x :=
      h2.inv₀ (hne i hi)
    exact (h1.mul h3).smul_section (hA i hi)
  exact hX.sub_section (ContMDiffAt.sum_section (s := s) hterm)

/-! ## The main statement -/

/-- **Smoothness of the pointwise Gram–Schmidt orthonormalisation, from pointwise smoothness.**
If the family of sections `F` is smooth at `y` and pointwise linearly independent at `y`, then its
pointwise Gram–Schmidt orthonormalisation is smooth at `y`. -/
theorem gsNorm_contMDiffAt_of_smoothAt
    {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E] [CompleteSpace E]
    {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
    {M : Type*} [TopologicalSpace M] [ChartedSpace H M] [IsManifold I (⊤ : ℕ∞) M]
    (g : Submission.Diff.SMet I M)
    (F : Fin (Module.finrank ℝ E) → Π y : M, TangentSpace I y) (y : M)
    (hF : ∀ i, ContMDiffAt I I.tangent (((⊤ : ℕ∞) : WithTop ℕ∞))
            (fun z : M => Bundle.TotalSpace.mk' E z (F i z)) y)
    (i : Fin (Module.finrank ℝ E))
    (hy : LinearIndependent ℝ (fun j : Fin (Module.finrank ℝ E) => F j y)) :
    ContMDiffAt I I.tangent (((⊤ : ℕ∞) : WithTop ℕ∞))
      (fun z : M => Bundle.TotalSpace.mk' E z (Work.Diff.GE.gsNorm g F i z)) y := by
  classical
  letI : RiemannianBundle (fun y : M ↦ TangentSpace I y) := ⟨g.toRiemannianMetric⟩
  haveI : IsContMDiffRiemannianBundle I ∞ E (fun y : M ↦ TangentSpace I y) := inferInstance
  let U : Fin (Module.finrank ℝ E) → (Π z : M, TangentSpace I z) :=
    fun i z => InnerProductSpace.gramSchmidt ℝ
      (fun j : Fin (Module.finrank ℝ E) => F j z) i
  have hGS : ∀ (m : ℕ) (hm : m < Module.finrank ℝ E), CMDiffAt ∞ (T% (U ⟨m, hm⟩)) y := by
    intro m
    refine Nat.strong_induction_on m (fun m ih hm => ?_)
    have hpt : ∀ z : M, U ⟨m, hm⟩ z =
        F ⟨m, hm⟩ z - ∑ i ∈ Finset.Iio (⟨m, hm⟩ : Fin (Module.finrank ℝ E)),
          ((g.inner z (U i z) (F ⟨m, hm⟩ z)) *
            (g.inner z (U i z) (U i z))⁻¹) • U i z := by
      intro z
      change InnerProductSpace.gramSchmidt ℝ (fun j : Fin (Module.finrank ℝ E) => F j z)
          (⟨m, hm⟩ : Fin (Module.finrank ℝ E)) =
        F ⟨m, hm⟩ z - ∑ i ∈ Finset.Iio (⟨m, hm⟩ : Fin (Module.finrank ℝ E)),
          ((g.inner z (U i z) (F ⟨m, hm⟩ z)) *
            (g.inner z (U i z) (U i z))⁻¹) • U i z
      rw [InnerProductSpace.gramSchmidt_def]
      simp only [Submodule.starProjection_singleton]
      congr 1
      refine Finset.sum_congr rfl (fun i hi => ?_)
      congr 1
      rw [← real_inner_self_eq_norm_sq, div_eq_mul_inv]
      rfl
    have hA : ∀ i ∈ Finset.Iio (⟨m, hm⟩ : Fin (Module.finrank ℝ E)),
        CMDiffAt ∞ (T% (U i)) y := by
      intro i hi
      have hi' : i < (⟨m, hm⟩ : Fin (Module.finrank ℝ E)) := Finset.mem_Iio.mp hi
      exact ih i.val hi' i.isLt
    have hne : ∀ i ∈ Finset.Iio (⟨m, hm⟩ : Fin (Module.finrank ℝ E)),
        g.inner y (U i y) (U i y) ≠ 0 := by
      intro i hi
      have hne0 : U i y ≠ 0 := by
        show InnerProductSpace.gramSchmidt ℝ
          (fun j : Fin (Module.finrank ℝ E) => F j y) i ≠ 0
        exact InnerProductSpace.gramSchmidt_ne_zero i hy
      exact (g.pos y (U i y) hne0).ne'
    have hstep := gs_step (I := I) (M := M) g y (Finset.Iio (⟨m, hm⟩ : Fin (Module.finrank ℝ E)))
      (A := U) (X := F ⟨m, hm⟩) hA (hF ⟨m, hm⟩) hne
    simpa only [hpt] using hstep
  have hUy : U i y ≠ 0 := by
    show InnerProductSpace.gramSchmidt ℝ (fun j : Fin (Module.finrank ℝ E) => F j y) i ≠ 0
    exact InnerProductSpace.gramSchmidt_ne_zero i hy
  have h1 : CMDiffAt ∞ (fun z : M => (Real.sqrt (g.inner z (U i z) (U i z)))⁻¹) y :=
    sqrt_inner_inv_contMDiffAt (I := I) (M := M) g y (hGS i.val i.isLt) hUy
  have h2 : CMDiffAt ∞ (T% (fun z : M =>
      (Real.sqrt (g.inner z (U i z) (U i z)))⁻¹ • U i z)) y :=
    h1.smul_section (hGS i.val i.isLt)
  refine h2.congr_of_eventuallyEq (Filter.Eventually.of_forall (fun z => ?_))
  show Bundle.TotalSpace.mk' E z (Work.Diff.GE.gsNorm g F i z) = Bundle.TotalSpace.mk' E z
    ((Real.sqrt (g.inner z (U i z) (U i z)))⁻¹ • U i z)
  congr 1

end Work.Diff.Evol
