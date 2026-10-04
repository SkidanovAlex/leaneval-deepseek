import Mathlib
import Submission.Work.Diff.GE.CurvDerivDefs
import Submission.Work.Diff.GE.linearIndependent_of_isONFrame
import Submission.Work.Diff.GE.exists_smooth_section_eq_nhds
import Submission.Work.Diff.GE.eventually_linearIndependent

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false

/-!
# Globally defined smooth fields forming an `onFrame`-frame near a point

`Work.Diff.GE.onFrameONfield`: given a smooth metric `g` and a point `x` of `M`, there is a family
of globally `C^∞` vector fields `E' i` which is a `g`-orthonormal frame near `x` and whose value at
`x` is the `Classical.epsilon`-chosen orthonormal frame `onFrame g x`.

The construction: the vectors `onFrame g x i` are extended to globally smooth fields
`F i := smoothExt x (onFrame g x i)` (Mathlib's `exists_contMDiff_section_apply_eq`, used through
`Submission.Diff.smoothExt`).  Since `F · x` is orthonormal, the family `F · y` stays linearly
independent for `y` near `x`, and on that set the pointwise Gram-Schmidt orthonormalisation
`gsNorm g F i` is `C^∞` (the key lemma `gsNorm_contMDiffAt_of_linearIndependent` below) and is
`g`-orthonormal.  Finally the Gram-Schmidt fields are globalised with a smooth bump function
(`Work.Diff.GE.exists_smooth_section_eq_nhds`).
-/

set_option autoImplicit false
set_option linter.unusedSectionVars false
set_option maxHeartbeats 1000000

open LeanEval.Geometry.SphereTheorem Submission.Diff Submission.Diff.Alg
open scoped Manifold ContDiff Bundle Topology BigOperators
open Bundle ContDiff Set VectorField CovariantDerivative Metric Filter

namespace Work.Diff.GE

variable
  {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E] [CompleteSpace E]
  {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
  {M : Type*} [TopologicalSpace M] [ChartedSpace H M]
    [IsManifold I ((⊤ : ENat) : WithTop ENat) M] [T2Space M]

/-! ## The elementary smoothness ingredients of Gram–Schmidt -/

/-- The metric pairing `y ↦ g.inner y (X y) (Y y)` of two sections that are smooth at `x` is
smooth at `x`. -/
theorem metric_pairing (g : SMet I M) (x : M) {X Y : Π y : M, TangentSpace I y}
    (hX : CMDiffAt ∞ (T% X) x) (hY : CMDiffAt ∞ (T% Y) x) :
    CMDiffAt ∞ (fun y : M => g.inner y (X y) (Y y)) x := by
  letI : RiemannianBundle (fun x : M ↦ TangentSpace I x) := ⟨g.toRiemannianMetric⟩
  haveI : IsContMDiffRiemannianBundle I ∞ E (fun x : M ↦ TangentSpace I x) := inferInstance
  exact ContMDiffAt.inner_bundle (F := E) (E := fun x : M ↦ TangentSpace I x) (b := id) hX hY

/-- The reciprocal square root of the squared length of a section that is smooth and non-zero at
`x` is smooth at `x`. -/
theorem sqrt_inner_inv_contMDiffAt (g : SMet I M) (x : M) {X : Π y : M, TangentSpace I y}
    (hX : CMDiffAt ∞ (T% X) x) (hXx : X x ≠ 0) :
    CMDiffAt ∞ (fun y : M => (Real.sqrt (g.inner y (X y) (X y)))⁻¹) x := by
  letI : RiemannianBundle (fun x : M ↦ TangentSpace I x) := ⟨g.toRiemannianMetric⟩
  haveI : IsContMDiffRiemannianBundle I ∞ E (fun x : M ↦ TangentSpace I x) := inferInstance
  have hS : CMDiffAt ∞ (fun y : M => g.inner y (X y) (X y)) x := metric_pairing g x hX hX
  have hpos : 0 < g.inner x (X x) (X x) := g.pos x (X x) hXx
  have h1 : CMDiffAt ∞ (fun y : M => Real.sqrt (g.inner y (X y) (X y))) x :=
    ContMDiffAt.comp x (contMDiffAt_iff_contDiffAt.mpr (Real.contDiffAt_sqrt hpos.ne')) hS
  exact ContMDiffAt.inv₀ h1 (Real.sqrt_pos.mpr hpos).ne'

/-- One Gram–Schmidt subtraction step: subtracting from a smooth section `X` its orthogonal
projections onto the smooth sections `A i` (whose lengths are non-zero at `x`) is smooth at `x`. -/
theorem gs_step (g : SMet I M) (x : M) {ι : Type*} (s : Finset ι)
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
      metric_pairing g x (hA i hi) hX
    have h2 : CMDiffAt ∞ (fun y : M => g.inner y (A i y) (A i y)) x :=
      metric_pairing g x (hA i hi) (hA i hi)
    have h3 : CMDiffAt ∞ (fun y : M => (g.inner y (A i y) (A i y))⁻¹) x :=
      h2.inv₀ (hne i hi)
    exact (h1.mul h3).smul_section (hA i hi)
  exact hX.sub_section (ContMDiffAt.sum_section (s := s) hterm)

/-! ## Pointwise Gram–Schmidt orthonormalisation of a family of sections -/

/-- The pointwise Gram–Schmidt orthonormalisation (with respect to the metric `g`) of a family of
sections `F i`, as a family of sections. -/
noncomputable def gsNorm (g : SMet I M)
    (F : Fin (Module.finrank ℝ E) → (Π y : M, TangentSpace I y))
    (i : Fin (Module.finrank ℝ E)) : Π y : M, TangentSpace I y :=
  letI : RiemannianBundle (fun y : M ↦ TangentSpace I y) := ⟨g.toRiemannianMetric⟩
  fun y => InnerProductSpace.gramSchmidtNormed ℝ
    (fun j : Fin (Module.finrank ℝ E) => F j y) i

/-- **Gram–Schmidt of an orthonormal family is the family itself.** -/
theorem gsNorm_apply_of_isONFrame (g : SMet I M) (x : M)
    {F : Fin (Module.finrank ℝ E) → (Π y : M, TangentSpace I y)}
    (h : IsONFrame g x (fun i => F i x)) (i : Fin (Module.finrank ℝ E)) :
    gsNorm g F i x = F i x := by
  letI : RiemannianBundle (fun y : M ↦ TangentSpace I y) := ⟨g.toRiemannianMetric⟩
  have hon : Orthonormal ℝ (fun i : Fin (Module.finrank ℝ E) => F i x) := by
    rw [orthonormal_iff_ite]
    intro i j
    exact h i j
  have hgs : ∀ j, InnerProductSpace.gramSchmidt ℝ
      (fun i : Fin (Module.finrank ℝ E) => F i x) j = F j x :=
    fun j => congrFun (InnerProductSpace.gramSchmidt_of_orthogonal ℝ hon.2) j
  rw [show gsNorm g F i x = InnerProductSpace.gramSchmidtNormed ℝ
      (fun j : Fin (Module.finrank ℝ E) => F j x) i from rfl]
  rw [InnerProductSpace.gramSchmidtNormed, hgs i, hon.1 i]
  simp

/-- **The key smoothness lemma.**  If the family of globally smooth sections `F i` is pointwise
linearly independent at `y`, then the pointwise Gram–Schmidt orthonormalisation of `F` is smooth
at `y`. -/
theorem gsNorm_contMDiffAt_of_linearIndependent (g : SMet I M)
    (F : Fin (Module.finrank ℝ E) → (Π y : M, TangentSpace I y))
    (hF : ∀ i, CMDiff ∞ (T% (F i))) :
    ∀ (i : Fin (Module.finrank ℝ E)) (y : M),
      LinearIndependent ℝ (fun j : Fin (Module.finrank ℝ E) => F j y) →
      CMDiffAt ∞ (T% (gsNorm g F i)) y := by
  intro i y hy
  letI : RiemannianBundle (fun y : M ↦ TangentSpace I y) := ⟨g.toRiemannianMetric⟩
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
      (A := U) (X := F ⟨m, hm⟩) hA (hF ⟨m, hm⟩ y) hne
    simpa only [hpt] using hstep
  have hUy : U i y ≠ 0 := by
    show InnerProductSpace.gramSchmidt ℝ (fun j : Fin (Module.finrank ℝ E) => F j y) i ≠ 0
    exact InnerProductSpace.gramSchmidt_ne_zero i hy
  have h1 : CMDiffAt ∞ (fun z : M => (Real.sqrt (g.inner z (U i z) (U i z)))⁻¹) y :=
    sqrt_inner_inv_contMDiffAt g y (hGS i.val i.isLt) hUy
  have h2 : CMDiffAt ∞ (T% (fun z : M =>
      (Real.sqrt (g.inner z (U i z) (U i z)))⁻¹ • U i z)) y :=
    h1.smul_section (hGS i.val i.isLt)
  refine h2.congr_of_eventuallyEq (Filter.Eventually.of_forall (fun z => ?_))
  show Bundle.TotalSpace.mk' E z (gsNorm g F i z) = Bundle.TotalSpace.mk' E z
    ((Real.sqrt (g.inner z (U i z) (U i z)))⁻¹ • U i z)
  congr 1

/-- Where the family `F` is pointwise linearly independent, its Gram–Schmidt orthonormalisation is
a `g`-orthonormal frame. -/
theorem isONFrame_gsNorm {g : SMet I M}
    {F : Fin (Module.finrank ℝ E) → (Π y : M, TangentSpace I y)} {y : M}
    (hy : LinearIndependent ℝ (fun j : Fin (Module.finrank ℝ E) => F j y)) :
    IsONFrame g y (fun i => gsNorm g F i y) := by
  letI : RiemannianBundle (fun y : M ↦ TangentSpace I y) := ⟨g.toRiemannianMetric⟩
  have hon : Orthonormal ℝ (fun i : Fin (Module.finrank ℝ E) =>
      InnerProductSpace.gramSchmidtNormed ℝ
        (fun j : Fin (Module.finrank ℝ E) => F j y) i) :=
    InnerProductSpace.gramSchmidtNormed_orthonormal hy
  intro i j
  show g.inner y (gsNorm g F i y) (gsNorm g F j y) = if i = j then (1 : ℝ) else 0
  exact orthonormal_iff_ite.mp hon i j

/-! ## The main statement -/

theorem onFrameONfield
    {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E] [CompleteSpace E]
    {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
    {M : Type*} [TopologicalSpace M] [ChartedSpace H M] [IsManifold I ((⊤ : ENat) : WithTop ENat) M]
    [T2Space M]
    (hLC : Submission.Diff.LCSmooth I M) (g : Submission.Diff.SMet I M) (x : M) :
    ∃ (E' : Fin (Module.finrank ℝ E) → (Π y : M, TangentSpace I y)),
      (∀ i, Work.Diff.GE.SmoothField M (E' i)) ∧
      Work.Diff.GE.OnFrameNear g x E' ∧
      (∀ i, E' i x = Submission.Diff.onFrame g x i) := by
  classical
  -- the `onFrame` vectors, extended to globally smooth fields
  let F : Fin (Module.finrank ℝ E) → (Π y : M, TangentSpace I y) :=
    fun i => smoothExt x (Submission.Diff.onFrame g x i)
  have hF : ∀ i, CMDiff ∞ (T% (F i)) := fun i => smoothExt_cmdiff x _
  have hFx : ∀ i, F i x = Submission.Diff.onFrame g x i := fun i => smoothExt_apply x _
  have hONF : IsONFrame g x (fun i => F i x) := by
    intro i j
    change g.inner x (F i x) (F j x) = if i = j then (1 : ℝ) else 0
    rw [hFx i, hFx j]
    exact isONFrame_onFrame g x i j
  -- the family stays linearly independent near `x`
  have hli : ∀ᶠ y in 𝓝 x,
      LinearIndependent ℝ (fun i : Fin (Module.finrank ℝ E) => F i y) :=
    eventually_linearIndependent F (fun i => hF i x)
      (linearIndependent_of_isONFrame g x (fun i => F i x) hONF)
  -- the Gram–Schmidt fields are smooth and orthonormal near `x`, and match `onFrame` at `x`
  have hsm : ∀ i, ∀ᶠ y in 𝓝 x, CMDiffAt ∞ (T% (gsNorm g F i)) y := fun i =>
    hli.mono (fun y hy => gsNorm_contMDiffAt_of_linearIndependent g F hF i y hy)
  have hONnear : ∀ᶠ y in 𝓝 x, IsONFrame g y (fun i => gsNorm g F i y) :=
    hli.mono (fun y hy => isONFrame_gsNorm (g := g) (F := F) hy)
  have hxval : ∀ i, gsNorm g F i x = Submission.Diff.onFrame g x i := by
    intro i
    rw [← hFx i]
    exact gsNorm_apply_of_isONFrame g x hONF i
  -- globalise the Gram–Schmidt fields
  let E' : Fin (Module.finrank ℝ E) → (Π y : M, TangentSpace I y) :=
    fun i => Classical.choose (Work.Diff.GE.exists_smooth_section_eq_nhds (gsNorm g F i) (hsm i))
  have hE'sm : ∀ i, CMDiff ∞ (T% (E' i)) := fun i =>
    (Classical.choose_spec
      (Work.Diff.GE.exists_smooth_section_eq_nhds (gsNorm g F i) (hsm i))).1
  have hE'x : ∀ i, E' i x = gsNorm g F i x := fun i =>
    (Classical.choose_spec
      (Work.Diff.GE.exists_smooth_section_eq_nhds (gsNorm g F i) (hsm i))).2.1
  have hE'eq : ∀ i, E' i =ᶠ[𝓝 x] gsNorm g F i := fun i =>
    (Classical.choose_spec
      (Work.Diff.GE.exists_smooth_section_eq_nhds (gsNorm g F i) (hsm i))).2.2
  refine ⟨E', hE'sm, ?_, fun i => by rw [hE'x i, hxval i]⟩
  filter_upwards [hONnear, Filter.eventually_all.mpr (fun i => hE'eq i)] with y hONy heq
  intro i j
  change g.inner y (E' i y) (E' j y) = if i = j then (1 : ℝ) else 0
  rw [heq i, heq j]
  exact hONy i j

end Work.Diff.GE
