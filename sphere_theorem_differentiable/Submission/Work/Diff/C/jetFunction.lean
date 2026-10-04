import Mathlib
import Submission.Work.Diff.C.Setup

set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
set_option backward.isDefEq.respectTransparency false
set_option linter.unusedSectionVars false

/-!
# A smooth function with prescribed first derivative (the "jet function")

For a point `x` of a `C^∞` manifold and a nonzero tangent vector `v ∈ T_xM` there is a **globally
`C^∞`** function `f : M → ℝ` with `f x = 0` and `mvfderiv I f x v = 1`.

This is the analytic input for the proof that a connection which is compatible with the metric
(`IsMetricCompatible`) forces the metric to be *continuous*: if `Y` is a smooth field with `Y x ≠ 0`
and `f x = 0`, `mvfderiv I f x (Y x) = 1`, then the function `p ↦ ⟪f p • Y p, Y p⟫` has
`mvfderiv` at `x` in direction `Y x` equal to `⟪Y x, Y x⟫ ≠ 0` (by `hmet` + the Leibniz rule), so it
is `MDifferentiableAt` at `x` (else `mfderiv = 0`), hence continuous; dividing by `f` — which is
nonzero off a hypersurface through `x` — and iterating gives continuity of `⟪Y,Y⟫` at `x`.

The construction: with the local chart `χ = extChartAt I x`, the function
`y ↦ ℓ (χ y - χ x)` (for a linear functional `ℓ` with `ℓ (dχ_x v) = 1`) is smooth on the chart
source with derivative `ℓ ∘ dχ_x` at `x`; multiplying by a smooth bump `≡ 1` near `x` and supported
in the chart source globalises it.

Nothing here is a `sorry`.
-/

open scoped Manifold ContDiff Bundle Topology ENNReal
open Bundle ContDiff Set VectorField CovariantDerivative Metric Filter

namespace Work.Diff.C

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]
  [CompleteSpace E]
  {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
  {M : Type*} [TopologicalSpace M] [T2Space M] [ChartedSpace H M] [IsManifold I ∞ M]

/-- A continuous linear functional on `E` taking the value `1` at a nonzero vector. -/
theorem exists_clm_eq_one (c : E) (hc : c ≠ 0) : ∃ ℓ : E →L[ℝ] ℝ, ℓ c = 1 := by
  classical
  set b := Module.finBasis ℝ E with hb
  have hrep : b.repr c ≠ 0 := by
    intro h
    have h1 : c = 0 := by
      have := b.sum_repr c
      rw [h] at this
      simpa using this.symm
    exact hc h1
  have hex : ∃ i, b.repr c i ≠ 0 := by
    by_contra h
    push Not at h
    exact hrep (by ext i; simpa using h i)
  obtain ⟨i, hi⟩ := hex
  refine ⟨((b.repr c i)⁻¹) • (LinearMap.toContinuousLinearMap (b.coord i)), ?_⟩
  rw [smul_apply, smul_eq_mul, LinearMap.coe_toContinuousLinearMap', Module.Basis.coord_apply]
  exact inv_mul_cancel₀ hi

/-- The derivative at `x` of the chart map is injective: its value on a nonzero tangent vector is
nonzero. -/
theorem mvfderiv_extChartAt_ne (x : M) (v : TangentSpace I x) (hv : v ≠ 0) :
    mvfderiv I (extChartAt I x) x v ≠ 0 := by
  intro h0
  apply hv
  have hinj : Function.Injective (mvfderiv I (extChartAt I x) x) := by
    intro a b hab
    have h2 : (mfderiv I 𝓘(ℝ,E) (extChartAt I x) x) a
        = (mfderiv I 𝓘(ℝ,E) (extChartAt I x) x) b := by
      have h3 := congrArg
        ((NormedSpace.fromTangentSpace (𝕜 := ℝ) (E := E) ((extChartAt I x) x)).symm) hab
      simpa [mvfderiv, ContinuousLinearMap.comp_apply] using h3
    exact (isInvertible_mfderiv_extChartAt (mem_extChartAt_source x)).injective h2
  exact hinj (by rw [h0]; simp)

/-- The manifold derivative of the affine chart-coordinate function `y ↦ ℓ (χ y - χ x)`. -/
theorem mvfderiv_affine_chart (x : M) (ℓ : E →L[ℝ] ℝ) :
    mvfderiv I (fun y : M => ℓ ((extChartAt I x) y - (extChartAt I x) x)) x
      = ℓ.comp (mfderiv I 𝓘(ℝ,E) (extChartAt I x) x) := by
  have hχ : MDifferentiableAt I 𝓘(ℝ,E) (extChartAt I x) x :=
    mdifferentiableAt_extChartAt (mem_chart_source H x)
  set c : E := (extChartAt I x) x with hc
  have hphi : (fun w : E => ℓ (w - c)) = ((fun w : E => ℓ w) - fun _ : E => ℓ c) := by
    ext w; rw [Pi.sub_apply, map_sub]
  have hsplit : (fun y : M => ℓ ((extChartAt I x) y - (extChartAt I x) x))
      = (fun w : E => ℓ (w - c)) ∘ (extChartAt I x) := rfl
  have hdphi : MDifferentiableAt (modelWithCornersSelf ℝ E) (modelWithCornersSelf ℝ ℝ)
      (fun w : E => ℓ (w - c)) c := by
    rw [hphi]
    exact ((ContinuousLinearMap.contMDiff (n := ⊤) ℓ).sub contMDiff_const).mdifferentiableAt
      (by simp)
  rw [hsplit, mvfderiv_comp x hdphi hχ]
  have hclm : mvfderiv (modelWithCornersSelf ℝ E) (fun w : E => ℓ (w - c)) c = ℓ := by
    rw [hphi]
    have hd1 : MDifferentiableAt (modelWithCornersSelf ℝ E) (modelWithCornersSelf ℝ ℝ)
        (fun w : E => ℓ w) c :=
      (ContinuousLinearMap.contMDiff (n := ⊤) ℓ).mdifferentiableAt (by simp)
    have hd2 : MDifferentiableAt (modelWithCornersSelf ℝ E) (modelWithCornersSelf ℝ ℝ)
        (fun _ : E => ℓ c) c := mdifferentiableAt_const (c := ℓ c)
    rw [mvfderiv_sub hd1 hd2, mvfderiv_const, sub_zero]
    rw [mvfderiv_eq_fderiv]
    exact (ContinuousLinearMap.hasFDerivAt ℓ).fderiv
  rw [hclm]

/-- **Jet function.**  For `v ≠ 0` there is a globally `C^∞` function `f` with `f x = 0` and
`mvfderiv I f x v = 1`. -/
theorem jetFunction (x : M) (v : TangentSpace I x) (hv : v ≠ 0) :
    ∃ f : M → ℝ, CMDiff ∞ f ∧ f x = 0 ∧ mvfderiv I f x v = 1 := by
  obtain ⟨ℓ, hℓ⟩ := exists_clm_eq_one (mvfderiv I (extChartAt I x) x v)
    (mvfderiv_extChartAt_ne x v hv)
  obtain ⟨ψ, -, hψsupp⟩ : ∃ ψ : SmoothBumpFunction I x,
      True ∧ tsupport (ψ : M → ℝ) ⊆ (chartAt H x).source :=
    (SmoothBumpFunction.nhds_basis_tsupport (I := I) x).mem_iff.mp
      ((chartAt H x).open_source.mem_nhds (mem_chart_source H x))
  set g : M → ℝ := fun y => ℓ ((extChartAt I x) y - (extChartAt I x) x) with hg
  have hgOn : ContMDiffOn I 𝓘(ℝ,ℝ) ∞ g (chartAt H x).source := by
    have h1 : ContMDiffOn I 𝓘(ℝ,E) ∞ (fun y : M => (extChartAt I x) y - (extChartAt I x) x)
        (chartAt H x).source :=
      (contMDiffOn_extChartAt (I := I) (x := x)).sub_const _
    exact (ℓ.contMDiff).comp_contMDiffOn h1
  have hgcd : CMDiff ∞ (fun y : M => (ψ : M → ℝ) y • g y) := ψ.contMDiff_smul hgOn
  have hgd : MDifferentiableAt I 𝓘(ℝ,ℝ) g x :=
    ((hgOn x (mem_chart_source H x)).contMDiffAt
      ((chartAt H x).open_source.mem_nhds (mem_chart_source H x))).mdifferentiableAt (by simp)
  have hψd : MDifferentiableAt I 𝓘(ℝ,ℝ) (fun y : M => (ψ : M → ℝ) y) x :=
    ψ.contMDiff.mdifferentiableAt (by simp)
  refine ⟨fun y => (ψ : M → ℝ) y * g y, ?_, ?_, ?_⟩
  · simpa only [smul_eq_mul] using hgcd
  · simp only [hg, SmoothBumpFunction.eq_one, sub_self, map_zero, mul_zero]
  · have hmul := mvfderiv_fun_mul hψd hgd
    rw [hmul]
    simp only [add_apply, smul_apply, smul_eq_mul]
    have hgv : mvfderiv I g x v = 1 := by
      rw [hg, mvfderiv_affine_chart]
      simp only [ContinuousLinearMap.comp_apply]
      exact hℓ
    have hg0 : g x = 0 := by simp [hg, map_sub]
    have hψx : (ψ : M → ℝ) x = 1 := SmoothBumpFunction.eq_one ψ
    rw [hgv, hg0, hψx]
    ring

end Work.Diff.C
