import Mathlib
import Submission.Work.Diff.GE.scal_lapl_defs
import Submission.Work.Diff.GE.exists_global_ON_frame
import Submission.Work.Diff.GE.onFrame_orthogonal_change

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false

/-!
# A globally smooth orthonormal frame field with prescribed value at a point

`Work.Diff.GE.exists_ON_frame_field_eq`: given a smooth Riemannian metric `g` on a smooth manifold
`M`, a point `x : M` and a `g`-orthonormal frame `e` of `TₓM`, there is a family `Ef i` of
*globally* `C^∞` vector fields which is a `g`-orthonormal frame near `x` and whose value at `x` is
prescribed: `Ef i x = e i`.

This is the "prescribed value at `x`" refinement of `Work.Diff.GE.exists_global_ON_frame`, and the
first three clauses of the frozen contract `Submission.Diff.LapRmFrameParallel`.

## Why not the obvious two-line proof?

The natural route is: take a globally smooth ON frame `W` near `x`
(`Work.Diff.GE.exists_global_ON_frame`), use `Work.Diff.GE.onFrame_orthogonal_change` to write
`e i = ∑ j A i j • W j x` with `A ∈ O(n)`, and set `Ef k := ∑ i A k i • W i`; smoothness of the
finite sum is `ContMDiff.sum_section` with `ContMDiff.const_smul_section`, and orthonormality of
the rotated family is the standard computation with `A * Aᵀ = 1`
(`Matrix.mem_orthogonalGroup_iff`), done with the `RiemannianBundle` instance `⟨g.toRiemannianMetric⟩`
under which `inner ℝ` at a fibre is literally `g.inner`.

That route does **not** apply here, for a formalisation reason worth recording: the proved
`Work.Diff.GE.exists_global_ON_frame` is stated with the hypothesis
`[IsManifold I ((⊤ : ENat) : WithTop ENat) M]`, which in Mathlib's `ContDiff` scope is `IsManifold I ω M`,
i.e. an **analytic** manifold (`ω = (⊤ : WithTop ℕ∞)`), whereas this theorem (and all of
`Submission.Diff.SMet`, `Submission.Diff.IsONFrame`, `Work.Diff.GE.SmoothSect`) only assumes the
weaker `IsManifold I ∞ M` (`∞ = ((⊤ : ℕ∞) : WithTop ℕ∞)`, smooth).  Analyticity is *not* derivable
from smoothness, so `exists_global_ON_frame` cannot be invoked; the analytic hypothesis there comes
from its use of the coordinate frame of the chart (`Work.Diff.T.exists_global_eventuallyEq_symmL`).

## The proof used instead

Everything is done with smooth data only, by pointwise Gram–Schmidt:

* `F i := Submission.Diff.smoothExt x (e i)` is a globally `C^∞` extension of `e i`
  (`Work.Diff.GE.smoothExt_cmdiff`, `Work.Diff.GE.smoothExt_apply`); its value at `x` is the
  orthonormal frame `e`, hence it is pointwise linearly independent near `x`
  (`Work.Diff.GE.linearIndependent_of_isONFrame`, `Work.Diff.GE.eventually_linearIndependent`);
* where the family is linearly independent, its pointwise Gram–Schmidt normalisation
  `Work.Diff.GE.gsNorm g F` is `C^∞` (`Work.Diff.GE.gsNorm_contMDiffAt_of_linearIndependent`) and
  orthonormal (`Work.Diff.GE.isONFrame_gsNorm`), and at `x` it is the family itself, since
  Gram–Schmidt of an already orthonormal family is the identity
  (`Work.Diff.GE.gsNorm_apply_of_isONFrame`);
* finally each `gsNorm g F i` is cut off by a smooth bump function to a *global* `C^∞` field
  agreeing with it near `x` (`Work.Diff.GE.exists_smooth_section_eq_nhds`).
-/

set_option linter.style.haveILetI false

open scoped Manifold ContDiff Bundle Topology
open Bundle ContDiff Set VectorField CovariantDerivative Metric Filter

namespace Work.Diff.GE

theorem exists_ON_frame_field_eq
    {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E] [CompleteSpace E]
    {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
    {M : Type*} [TopologicalSpace M] [ChartedSpace H M]
    [IsManifold I (((⊤ : ℕ∞) : WithTop ℕ∞)) M] [I.Boundaryless] [T2Space M]
    (g : Submission.Diff.SMet I M) (x : M)
    (e : Fin (Module.finrank ℝ E) → TangentSpace I x) (he : Submission.Diff.IsONFrame g x e) :
    ∃ Ef : Fin (Module.finrank ℝ E) → Π y : M, TangentSpace I y,
      (∀ i, Ef i x = e i) ∧ (∀ i, Work.Diff.GE.SmoothSect (I := I) (M := M) (Ef i)) ∧
        (Filter.Eventually (fun y : M ↦ Submission.Diff.IsONFrame g y (fun i ↦ Ef i y))
          (nhds x)) := by
  classical
  -- globally smooth extensions of the prescribed frame `e`
  let F : Fin (Module.finrank ℝ E) → Π y : M, TangentSpace I y :=
    fun i => Submission.Diff.smoothExt x (e i)
  have hF : ∀ i, CMDiff ∞ (T% (F i)) := fun i => Work.Diff.GE.smoothExt_cmdiff x (e i)
  have hFx : ∀ i, F i x = e i := fun i => Work.Diff.GE.smoothExt_apply x (e i)
  have hONx : Submission.Diff.IsONFrame g x (fun i => F i x) := by
    intro i j
    show g.inner x (F i x) (F j x) = if i = j then 1 else 0
    rw [hFx i, hFx j]
    exact he i j
  -- the family stays pointwise linearly independent near `x`
  have hli : ∀ᶠ y in 𝓝 x, LinearIndependent ℝ (fun i : Fin (Module.finrank ℝ E) => F i y) :=
    Work.Diff.GE.eventually_linearIndependent F (fun i => (hF i).contMDiffAt)
      (Work.Diff.GE.linearIndependent_of_isONFrame g x (fun i => F i x) hONx)
  -- its Gram-Schmidt normalisation is smooth and orthonormal near `x`
  have hsm : ∀ i, ∀ᶠ y in 𝓝 x, CMDiffAt ∞ (T% (Work.Diff.GE.gsNorm g F i)) y := fun i =>
    hli.mono (fun y hy => Work.Diff.GE.gsNorm_contMDiffAt_of_linearIndependent g F hF i y hy)
  have hONnear : ∀ᶠ y in 𝓝 x,
      Submission.Diff.IsONFrame g y (fun i => Work.Diff.GE.gsNorm g F i y) :=
    hli.mono (fun y hy => Work.Diff.GE.isONFrame_gsNorm (g := g) hy)
  -- globalise, one field at a time
  choose Ef hEfsm hEfx hEfeq using fun i =>
    Work.Diff.GE.exists_smooth_section_eq_nhds (Work.Diff.GE.gsNorm g F i) (hsm i)
  refine ⟨Ef, ?_, ?_, ?_⟩
  · -- the prescribed value at `x`
    intro i
    rw [hEfx i, Work.Diff.GE.gsNorm_apply_of_isONFrame g x hONx i, hFx i]
  · -- global smoothness
    intro i
    exact hEfsm i
  · -- orthonormality near `x`
    filter_upwards [hONnear, Filter.eventually_all.mpr hEfeq] with y h1 h2
    have hfun : (fun i => Ef i y) = fun i => Work.Diff.GE.gsNorm g F i y :=
      funext fun i => h2 i
    rw [hfun]
    exact h1

/-- **A globally smooth field of orthonormal frames near a point — smooth-manifold version.**

The proved `Work.Diff.GE.exists_global_ON_frame` carries the hypothesis
`[IsManifold I ((⊤ : ENat) : WithTop ENat) M]`, which in Mathlib's `ContDiff` scope is `IsManifold I ω M` — an
*analytic* manifold (`ω = (⊤ : WithTop ℕ∞)` is the top of the smoothness lattice).  That hypothesis
is strictly stronger than the `IsManifold I ∞ M` used throughout this workspace (by
`Submission.Diff.SMet`, `Submission.Diff.IsONFrame`, `Work.Diff.GE.SmoothSect`, ...), and is not
derivable from it, so `exists_global_ON_frame` cannot be applied on a merely smooth manifold (this
is why the proof of `exists_ON_frame_field_eq` above avoids it).

This corollary supplies the missing smooth-manifold version; it is an immediate consequence of
`exists_ON_frame_field_eq` applied to the chosen frame `Submission.Diff.onFrame g x`.

This matters beyond bookkeeping: the ambient hypothesis of the challenge
(`Challenge.lean`, `Submission.lean`, and `Submission.Diff.*`) is `IsManifold I ∞ M`, i.e. *smooth*,
so an analytic hypothesis can never be supplied in the endgame and any result depending on
`exists_global_ON_frame` as stated is unusable there. -/
theorem exists_global_ON_frame_smooth
    {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E] [CompleteSpace E]
    {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
    {M : Type*} [TopologicalSpace M] [ChartedSpace H M]
    [IsManifold I (((⊤ : ℕ∞) : WithTop ℕ∞)) M] [I.Boundaryless] [T2Space M]
    (g : Submission.Diff.SMet I M) (x : M) :
    ∃ W : Fin (Module.finrank ℝ E) → Π y : M, TangentSpace I y,
      (∀ i, Work.Diff.GE.SmoothSect (I := I) (M := M) (W i)) ∧
      Filter.Eventually (fun y : M ↦ Submission.Diff.IsONFrame g y (fun i ↦ W i y)) (nhds x) := by
  obtain ⟨W, -, hsm, hON⟩ := exists_ON_frame_field_eq (I := I) (M := M) g x
    (Submission.Diff.onFrame g x) (Work.Diff.GE.isONFrame_onFrame g x)
  exact ⟨W, hsm, hON⟩

end Work.Diff.GE
