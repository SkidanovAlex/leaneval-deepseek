/-
# Layer C2: the metric product rule along a **within-`J`** curve

The sealed library's `Submission.ChartConnection.hasDerivAt_chartGram` differentiates the chart
metric `chartGram x₀ (γ ·) (h₁ ·) (h₂ ·)` for a curve `γ` that is differentiable *two-sidedly* at
`t`, with direction `curveVelocity γ t`.  The DeTurck pull-back computation only has the
**within-`J`** differentiability of the curve, and the metric is an *arbitrary* smooth metric `g`
(not the ambient instance metric), with `cov` metric compatible for `g` (hypothesis `hmet`).

This file redoes that computation in the within-`J` setting:

* `hasDerivWithinAt_inner_sections_wj` — the within-`J` product rule for the pairing of two globally
  smooth sections, the exact analogue of `Submission.Variation.hasDerivAt_inner_sections`;
* `hasDerivWithinAt_chartGram_const_wj` — the constant-coordinate case (both coordinate vectors
  fixed), obtained from the previous one by extending the frame sections to globally smooth sections
  with a bump function (`exists_contMDiff_section_eventuallyEq_frameSection`);
* `hasDerivWithinAt_chartGram_const_fst_wj`, `hasDerivWithinAt_chartGram_wj` — the cases with one
  resp. both coordinate fields varying, by expansion in a basis (`Module.finBasis`), exactly as in
  `Submission.ChartConnection`.

The target `withinJChartGram` is the statement for an arbitrary `g : SMet I M`: writing
`letI : RiemannianBundle _ := ⟨g.toRiemannianMetric⟩`, the ambient inner product *is* `g.inner`
(definitionally), so the chart-metric lemmas above apply verbatim.  This is the bridge that lets the
DeTurck computation use the chart-form metric compatibility for a moving metric.
-/
import Mathlib
import Submission.Work.Diff.STE.C2.ChartKit
import Submission.Work.Diff.STE.C2.WithinJKit

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false

set_option linter.unusedSectionVars false
set_option linter.style.haveILetI false

open scoped Manifold ContDiff Bundle Topology
open Bundle ContDiff Set VectorField CovariantDerivative Metric Filter
open LeanEval.Geometry.SphereTheorem
open Submission.Geodesic
open Submission.ChartConnection

namespace Work.Diff.STE.C2

noncomputable section

section Instances

variable
  {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    [FiniteDimensional ℝ E] [CompleteSpace E]
  {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
  {M : Type*} [TopologicalSpace M] [T2Space M] [ChartedSpace H M]
    [IsManifold I ∞ M]
  [RiemannianBundle (fun (x : M) ↦ TangentSpace I x)]
  [IsContMDiffRiemannianBundle I ∞ E (fun (x : M) ↦ TangentSpace I x)]

/-- **Metric compatibility along a curve, within-`J` form.**  For globally smooth sections `Y`, `Z`
and a curve `γ` whose within-`J` velocity at `t` is `v`, the function `s ↦ ⟪Y (γ s), Z (γ s)⟫` has
within-`J` derivative `⟪∇_v Y, Z⟫ + ⟪Y, ∇_v Z⟫` at `t`.

This is `Work.Diff.STE.C2.hasDerivWithinAt_inner_sections` with the two-sided differentiability of
the curve weakened to a `HasMFDerivWithinAt` hypothesis (the proof is the within-`J` chain rule
`Work.Diff.STE.C2.hasDerivWithinAt_comp_curve` plus `IsMetricCompatible`). -/
theorem hasDerivWithinAt_inner_sections_wj
    (cov : CovariantDerivative I E (TangentSpace I (M := M)))
    (hmet : IsMetricCompatible cov)
    {Y Z : Π x : M, TangentSpace I x}
    (hY : ContMDiff I I.tangent ∞ (fun y : M ↦ (⟨y, Y y⟩ : TangentBundle I M)))
    (hZ : ContMDiff I I.tangent ∞ (fun y : M ↦ (⟨y, Z y⟩ : TangentBundle I M)))
    {γ : ℝ → M} {J : Set ℝ} {t : ℝ} {v : TangentSpace I (γ t)}
    (hγ : HasMFDerivWithinAt (modelWithCornersSelf ℝ ℝ) I γ J t
      ((1 : ℝ →L[ℝ] ℝ).smulRight v)) :
    HasDerivWithinAt (fun s ↦ inner ℝ (Y (γ s)) (Z (γ s)))
      (inner ℝ (cov Y (γ t) v) (Z (γ t)) + inner ℝ (Y (γ t)) (cov Z (γ t) v)) J t := by
  have hinner : MDifferentiableAt I 𝓘(ℝ, ℝ) (fun y : M ↦ inner ℝ (Y y) (Z y)) (γ t) :=
    Submission.Variation.mdifferentiableAt_inner_sections hY hZ (γ t)
  have h := hasDerivWithinAt_comp_curve (I := I) (M := M) (F := ℝ)
    (ψ := fun y : M ↦ inner ℝ (Y y) (Z y)) hγ hinner
  rwa [hmet Y Z hY hZ (γ t) v] at h

/-- **The chart-metric product rule for constant coordinate vectors, within-`J` form.**

For a curve `γ` whose within-`J` velocity at `t` is `v` and with `γ t` in the chart at `x₀`, the
derivative of `s ↦ ⟪a, b⟫_{γ s}` (the metric on the constant-coordinate frame vectors `a`, `b`) is
`⟪Γ(a)(v), b⟫ + ⟪a, Γ(b)(v)⟫`.

This is the within-`J` analogue of `Submission.ChartConnection.hasDerivAt_chartGram_const`; the
metric compatibility `hmet` is applied to the frame sections made globally smooth by a bump
function. -/
theorem hasDerivWithinAt_chartGram_const_wj
    (cov : CovariantDerivative I E (TangentSpace I (M := M)))
    (hmet : IsMetricCompatible cov) (x₀ : M) (a b : E)
    {γ : ℝ → M} {J : Set ℝ} {t : ℝ} {v : TangentSpace I (γ t)}
    (hγ : HasMFDerivWithinAt (modelWithCornersSelf ℝ ℝ) I γ J t
      ((1 : ℝ →L[ℝ] ℝ).smulRight v))
    (hsrc : γ t ∈ (chartAt H x₀).source) :
    HasDerivWithinAt (fun s => chartGram (I := I) x₀ (γ s) a b)
      (chartGram (I := I) x₀ (γ t)
          (christoffelEval cov x₀ (γ t) a v) b
       + chartGram (I := I) x₀ (γ t) a
          (christoffelEval cov x₀ (γ t) b v)) J t := by
  obtain ⟨Y, hYsm, hYeq⟩ :=
    exists_contMDiff_section_eventuallyEq_frameSection (I := I) x₀ a hsrc
  obtain ⟨Z, hZsm, hZeq⟩ :=
    exists_contMDiff_section_eventuallyEq_frameSection (I := I) x₀ b hsrc
  have hbase : HasDerivWithinAt (fun s => inner ℝ (Y (γ s)) (Z (γ s)))
      (inner ℝ (cov Y (γ t) v) (Z (γ t))
        + inner ℝ (Y (γ t)) (cov Z (γ t) v)) J t :=
    hasDerivWithinAt_inner_sections_wj (I := I) cov hmet hYsm hZsm hγ
  have heq : (fun s => inner ℝ (Y (γ s)) (Z (γ s)))
      =ᶠ[𝓝[J] t] (fun s => chartGram (I := I) x₀ (γ s) a b) := by
    filter_upwards [hγ.continuousWithinAt.eventually hYeq,
      hγ.continuousWithinAt.eventually hZeq] with s hs hs'
    have hs1 : Y (γ s) = frameVector (I := I) x₀ (γ s) a := hs
    have hs2 : Z (γ s) = frameVector (I := I) x₀ (γ s) b := hs'
    rw [hs1, hs2, chartGram_apply]
  have hcovY : cov Y (γ t) = cov (frameSection (I := I) x₀ a) (γ t) :=
    cov.isCovariantDerivativeOn.congr_of_eventuallyEq
      ((hYsm (γ t)).mdifferentiableAt (by simp))
      (mdiffAt_frameSection (I := I) x₀ a hsrc) Filter.univ_mem hYeq
  have hcovZ : cov Z (γ t) = cov (frameSection (I := I) x₀ b) (γ t) :=
    cov.isCovariantDerivativeOn.congr_of_eventuallyEq
      ((hZsm (γ t)).mdifferentiableAt (by simp))
      (mdiffAt_frameSection (I := I) x₀ b hsrc) Filter.univ_mem hZeq
  have hYt : Y (γ t) = frameVector (I := I) x₀ (γ t) a := by
    rw [hYeq.eq_of_nhds]; rfl
  have hZt : Z (γ t) = frameVector (I := I) x₀ (γ t) b := by
    rw [hZeq.eq_of_nhds]; rfl
  have hcovYe : cov Y (γ t) v
      = frameVector (I := I) x₀ (γ t)
          (christoffelEval cov x₀ (γ t) a v) := by
    rw [hcovY, cov_frameSection_eq cov x₀ (γ t) a v hsrc]
    rfl
  have hcovZe : cov Z (γ t) v
      = frameVector (I := I) x₀ (γ t)
          (christoffelEval cov x₀ (γ t) b v) := by
    rw [hcovZ, cov_frameSection_eq cov x₀ (γ t) b v hsrc]
    rfl
  have hmain : HasDerivWithinAt (fun s => chartGram (I := I) x₀ (γ s) a b)
      (inner ℝ (cov Y (γ t) v) (Z (γ t))
        + inner ℝ (Y (γ t)) (cov Z (γ t) v)) J t :=
    hbase.congr_of_eventuallyEq heq.symm (by rw [chartGram_apply, hYt, hZt])
  have hval : inner ℝ (cov Y (γ t) v) (Z (γ t))
      + inner ℝ (Y (γ t)) (cov Z (γ t) v)
      = chartGram (I := I) x₀ (γ t)
          (christoffelEval cov x₀ (γ t) a v) b
        + chartGram (I := I) x₀ (γ t) a
          (christoffelEval cov x₀ (γ t) b v) := by
    rw [hcovYe, hYt, hcovZe, hZt]
    rfl
  rwa [hval] at hmain

/-- Product rule for functions `ℝ → ℝ`, stated with the pointwise product as an explicit lambda
(within-`J` version of `Submission.ChartConnection.hasDerivAt_mul_fun`). -/
theorem hasDerivWithinAt_mul_fun_wj {f g : ℝ → ℝ} {f' g' : ℝ} {x : ℝ} {s : Set ℝ}
    (hf : HasDerivWithinAt f f' s x) (hg : HasDerivWithinAt g g' s x) :
    HasDerivWithinAt (fun t => f t * g t) (f' * g x + f x * g') s x := by
  have h := hf.mul hg
  rwa [show (f * g) = fun t => f t * g t from by funext t; exact Pi.mul_apply f g t] at h

/-- **The chart-metric product rule, first argument constant, within-`J` form.**

For a curve `γ` with within-`J` velocity `v` at `t`, and a field `h` along it with within-`J`
derivative `h'`,
`d/dt ⟪a, h(t)⟫ = ⟪a, h'(t)⟫ + ⟪Γ(a)(v), h(t)⟫ + ⟪a, Γ(h t)(v)⟫`.

This is the within-`J` analogue of `Submission.ChartConnection.hasDerivAt_chartGram_const_fst`; the
proof expands `h` in the basis `Module.finBasis` and applies the constant-coordinate case. -/
theorem hasDerivWithinAt_chartGram_const_fst_wj
    (cov : CovariantDerivative I E (TangentSpace I (M := M)))
    (hmet : IsMetricCompatible cov) (x₀ : M) (a : E)
    {γ : ℝ → M} {J : Set ℝ} {t : ℝ} {v : TangentSpace I (γ t)}
    (hγ : HasMFDerivWithinAt (modelWithCornersSelf ℝ ℝ) I γ J t
      ((1 : ℝ →L[ℝ] ℝ).smulRight v))
    (hsrc : γ t ∈ (chartAt H x₀).source)
    {h : ℝ → E} {h' : E} (hh : HasDerivWithinAt h h' J t) :
    HasDerivWithinAt (fun s => chartGram (I := I) x₀ (γ s) a (h s))
      (chartGram (I := I) x₀ (γ t) a h'
       + chartGram (I := I) x₀ (γ t)
          (christoffelEval cov x₀ (γ t) a v) (h t)
       + chartGram (I := I) x₀ (γ t) a
          (christoffelEval cov x₀ (γ t) (h t) v)) J t := by
  classical
  let bb : Module.Basis (Fin (Module.finrank ℝ E)) ℝ E := Module.finBasis ℝ E
  have hsum : (fun s => chartGram (I := I) x₀ (γ s) a (h s))
      = fun s => ∑ j, (bb.repr (h s) j) * chartGram (I := I) x₀ (γ s) a (bb j) := by
    funext s
    conv_lhs => rw [← bb.sum_repr (h s)]
    rw [chartGram_sum_snd (I := I) (x₀ := x₀) (p := γ s) (s := Finset.univ)
      (c := fun j => bb.repr (h s) j) (v := fun j => bb j) (a := a)]
  have hcoord : ∀ j, HasDerivWithinAt (fun s => bb.repr (h s) j) (bb.repr h' j) J t := by
    intro j
    exact (((bb.coord j : E →ₗ[ℝ] ℝ).toContinuousLinearMap).hasFDerivAt.comp_hasDerivWithinAt t hh)
  have hsingle : ∀ j, HasDerivWithinAt (fun s => chartGram (I := I) x₀ (γ s) a (bb j))
      (chartGram (I := I) x₀ (γ t)
          (christoffelEval cov x₀ (γ t) a v) (bb j)
        + chartGram (I := I) x₀ (γ t) a
          (christoffelEval cov x₀ (γ t) (bb j) v)) J t :=
    fun j => hasDerivWithinAt_chartGram_const_wj cov hmet x₀ a (bb j) hγ hsrc
  have hderivF : HasDerivWithinAt
      (fun s => ∑ j, (bb.repr (h s) j) * chartGram (I := I) x₀ (γ s) a (bb j))
      (∑ j, (bb.repr h' j * chartGram (I := I) x₀ (γ t) a (bb j)
        + bb.repr (h t) j * (chartGram (I := I) x₀ (γ t)
              (christoffelEval cov x₀ (γ t) a v) (bb j)
            + chartGram (I := I) x₀ (γ t) a
              (christoffelEval cov x₀ (γ t) (bb j) v)))) J t := by
    have h1 : HasDerivWithinAt
        (∑ j ∈ Finset.univ, ((fun s => bb.repr (h s) j) *
          (fun s => chartGram (I := I) x₀ (γ s) a (bb j))))
        (∑ j ∈ Finset.univ, (bb.repr h' j * chartGram (I := I) x₀ (γ t) a (bb j)
          + bb.repr (h t) j * (chartGram (I := I) x₀ (γ t)
                (christoffelEval cov x₀ (γ t) a v) (bb j)
              + chartGram (I := I) x₀ (γ t) a
                (christoffelEval cov x₀ (γ t) (bb j) v)))) J t := by
      refine HasDerivWithinAt.sum fun j _ => ?_
      exact hasDerivWithinAt_mul_fun_wj (hcoord j) (hsingle j)
    refine h1.congr_of_eventuallyEq (Filter.EventuallyEq.of_eq ?_) ?_
    · funext s
      simp only [Finset.sum_apply, Pi.mul_apply]
    · simp only [Finset.sum_apply, Pi.mul_apply]
  have hval : (∑ j, (bb.repr h' j * chartGram (I := I) x₀ (γ t) a (bb j)
        + bb.repr (h t) j * (chartGram (I := I) x₀ (γ t)
              (christoffelEval cov x₀ (γ t) a v) (bb j)
            + chartGram (I := I) x₀ (γ t) a
              (christoffelEval cov x₀ (γ t) (bb j) v))))
      = chartGram (I := I) x₀ (γ t) a h'
       + chartGram (I := I) x₀ (γ t)
          (christoffelEval cov x₀ (γ t) a v) (h t)
       + chartGram (I := I) x₀ (γ t) a
          (christoffelEval cov x₀ (γ t) (h t) v) := by
    simp_rw [mul_add, Finset.sum_add_distrib]
    have hA : (∑ j, bb.repr h' j * chartGram (I := I) x₀ (γ t) a (bb j))
        = chartGram (I := I) x₀ (γ t) a h' :=
      (chartGram_eq_sum_snd_repr (I := I) bb x₀ (γ t) a h').symm
    have hB : (∑ j, bb.repr (h t) j * chartGram (I := I) x₀ (γ t)
          (christoffelEval cov x₀ (γ t) a v) (bb j))
        = chartGram (I := I) x₀ (γ t)
          (christoffelEval cov x₀ (γ t) a v) (h t) :=
      (chartGram_eq_sum_snd_repr (I := I) bb x₀ (γ t)
        (christoffelEval cov x₀ (γ t) a v) (h t)).symm
    have hG : christoffelEval cov x₀ (γ t) (h t) v
        = ∑ j, (bb.repr (h t) j) •
            christoffelEval cov x₀ (γ t) (bb j) v := by
      conv_lhs => rw [← bb.sum_repr (h t)]
      exact christoffelEval_sum_left Finset.univ cov x₀ (γ t) (fun j => bb.repr (h t) j)
        (fun j => bb j) v hsrc
    have hC : (∑ j, bb.repr (h t) j * chartGram (I := I) x₀ (γ t) a
          (christoffelEval cov x₀ (γ t) (bb j) v))
        = chartGram (I := I) x₀ (γ t) a
          (christoffelEval cov x₀ (γ t) (h t) v) := by
      rw [hG, chartGram_sum_snd (I := I) (x₀ := x₀) (p := γ t) (s := Finset.univ)
        (c := fun j => bb.repr (h t) j)
        (v := fun j => christoffelEval cov x₀ (γ t) (bb j) v)
        (a := a)]
    rw [hA, hB, hC]
    ring
  rw [hval] at hderivF
  exact hderivF.congr_of_eventuallyEq (Filter.EventuallyEq.of_eq hsum) (congrFun hsum t)

/-- **The chart-metric product rule, within-`J` form.**  For a curve `γ` with within-`J` velocity
`v` at `t`, `γ t` in the chart at `x₀`, and fields `h₁`, `h₂` along it with within-`J` derivatives
`h₁'`, `h₂'`,

`d/dt ⟪h₁(t), h₂(t)⟫ = ⟪h₁'(t) + Γ(h₁ t)(v), h₂(t)⟫ + ⟪h₁(t), h₂'(t) + Γ(h₂ t)(v)⟫`.

This is the within-`J` analogue of `Submission.ChartConnection.hasDerivAt_chartGram` (there the
direction is `curveVelocity γ t`); it is what the DeTurck pull-back computation needs for the
metric along the flow curve. -/
theorem hasDerivWithinAt_chartGram_wj
    (cov : CovariantDerivative I E (TangentSpace I (M := M)))
    (hmet : IsMetricCompatible cov) (x₀ : M)
    {γ : ℝ → M} {J : Set ℝ} {t : ℝ} {v : TangentSpace I (γ t)}
    (hγ : HasMFDerivWithinAt (modelWithCornersSelf ℝ ℝ) I γ J t
      ((1 : ℝ →L[ℝ] ℝ).smulRight v))
    (hsrc : γ t ∈ (chartAt H x₀).source)
    {h₁ h₂ : ℝ → E} {h₁' h₂' : E}
    (hh₁ : HasDerivWithinAt h₁ h₁' J t) (hh₂ : HasDerivWithinAt h₂ h₂' J t) :
    HasDerivWithinAt (fun s => chartGram (I := I) x₀ (γ s) (h₁ s) (h₂ s))
      (chartGram (I := I) x₀ (γ t)
          (h₁' + christoffelEval cov x₀ (γ t) (h₁ t) v) (h₂ t)
       + chartGram (I := I) x₀ (γ t) (h₁ t)
          (h₂' + christoffelEval cov x₀ (γ t) (h₂ t) v)) J t := by
  classical
  let bb : Module.Basis (Fin (Module.finrank ℝ E)) ℝ E := Module.finBasis ℝ E
  have hsum : (fun s => chartGram (I := I) x₀ (γ s) (h₁ s) (h₂ s))
      = fun s => ∑ j, (bb.repr (h₁ s) j) * chartGram (I := I) x₀ (γ s) (bb j) (h₂ s) := by
    funext s
    exact chartGram_eq_sum_fst_repr (I := I) bb x₀ (γ s) (h₁ s) (h₂ s)
  have hcoord : ∀ j, HasDerivWithinAt (fun s => bb.repr (h₁ s) j) (bb.repr h₁' j) J t := by
    intro j
    exact (((bb.coord j : E →ₗ[ℝ] ℝ).toContinuousLinearMap).hasFDerivAt.comp_hasDerivWithinAt t hh₁)
  have hsingle : ∀ j, HasDerivWithinAt (fun s => chartGram (I := I) x₀ (γ s) (bb j) (h₂ s))
      (chartGram (I := I) x₀ (γ t) (bb j) h₂'
       + chartGram (I := I) x₀ (γ t)
          (christoffelEval cov x₀ (γ t) (bb j) v) (h₂ t)
       + chartGram (I := I) x₀ (γ t) (bb j)
          (christoffelEval cov x₀ (γ t) (h₂ t) v)) J t :=
    fun j => hasDerivWithinAt_chartGram_const_fst_wj cov hmet x₀ (bb j) hγ hsrc hh₂
  have hderivF : HasDerivWithinAt
      (fun s => ∑ j, (bb.repr (h₁ s) j) * chartGram (I := I) x₀ (γ s) (bb j) (h₂ s))
      (∑ j, (bb.repr h₁' j * chartGram (I := I) x₀ (γ t) (bb j) (h₂ t)
        + bb.repr (h₁ t) j * (chartGram (I := I) x₀ (γ t) (bb j) h₂'
          + chartGram (I := I) x₀ (γ t)
              (christoffelEval cov x₀ (γ t) (bb j) v) (h₂ t)
          + chartGram (I := I) x₀ (γ t) (bb j)
              (christoffelEval cov x₀ (γ t) (h₂ t) v)))) J t := by
    have h1 : HasDerivWithinAt
        (∑ j ∈ Finset.univ, ((fun s => bb.repr (h₁ s) j) *
          (fun s => chartGram (I := I) x₀ (γ s) (bb j) (h₂ s))))
        (∑ j ∈ Finset.univ, (bb.repr h₁' j * chartGram (I := I) x₀ (γ t) (bb j) (h₂ t)
          + bb.repr (h₁ t) j * (chartGram (I := I) x₀ (γ t) (bb j) h₂'
            + chartGram (I := I) x₀ (γ t)
                (christoffelEval cov x₀ (γ t) (bb j) v) (h₂ t)
            + chartGram (I := I) x₀ (γ t) (bb j)
                (christoffelEval cov x₀ (γ t) (h₂ t) v)))) J t := by
      refine HasDerivWithinAt.sum fun j _ => ?_
      exact hasDerivWithinAt_mul_fun_wj (hcoord j) (hsingle j)
    refine h1.congr_of_eventuallyEq (Filter.EventuallyEq.of_eq ?_) ?_
    · funext s
      simp only [Finset.sum_apply, Pi.mul_apply]
    · simp only [Finset.sum_apply, Pi.mul_apply]
  have hval : (∑ j, (bb.repr h₁' j * chartGram (I := I) x₀ (γ t) (bb j) (h₂ t)
        + bb.repr (h₁ t) j * (chartGram (I := I) x₀ (γ t) (bb j) h₂'
          + chartGram (I := I) x₀ (γ t)
              (christoffelEval cov x₀ (γ t) (bb j) v) (h₂ t)
          + chartGram (I := I) x₀ (γ t) (bb j)
              (christoffelEval cov x₀ (γ t) (h₂ t) v))))
      = chartGram (I := I) x₀ (γ t)
          (h₁' + christoffelEval cov x₀ (γ t) (h₁ t) v) (h₂ t)
       + chartGram (I := I) x₀ (γ t) (h₁ t)
          (h₂' + christoffelEval cov x₀ (γ t) (h₂ t) v) := by
    simp_rw [mul_add, Finset.sum_add_distrib]
    have hA : (∑ j, bb.repr h₁' j * chartGram (I := I) x₀ (γ t) (bb j) (h₂ t))
        = chartGram (I := I) x₀ (γ t) h₁' (h₂ t) :=
      (chartGram_eq_sum_fst_repr (I := I) bb x₀ (γ t) h₁' (h₂ t)).symm
    have hB : (∑ j, bb.repr (h₁ t) j * chartGram (I := I) x₀ (γ t) (bb j) h₂')
        = chartGram (I := I) x₀ (γ t) (h₁ t) h₂' :=
      (chartGram_eq_sum_fst_repr (I := I) bb x₀ (γ t) (h₁ t) h₂').symm
    have hΓ₁ : christoffelEval cov x₀ (γ t) (h₁ t) v
        = ∑ j, (bb.repr (h₁ t) j) •
            christoffelEval cov x₀ (γ t) (bb j) v := by
      conv_lhs => rw [← bb.sum_repr (h₁ t)]
      exact christoffelEval_sum_left Finset.univ cov x₀ (γ t) (fun j => bb.repr (h₁ t) j)
        (fun j => bb j) v hsrc
    have hC : (∑ j, bb.repr (h₁ t) j * chartGram (I := I) x₀ (γ t)
          (christoffelEval cov x₀ (γ t) (bb j) v) (h₂ t))
        = chartGram (I := I) x₀ (γ t)
          (christoffelEval cov x₀ (γ t) (h₁ t) v) (h₂ t) := by
      rw [hΓ₁, chartGram_sum_fst (I := I) (x₀ := x₀) (p := γ t) (s := Finset.univ)
        (c := fun j => bb.repr (h₁ t) j)
        (v := fun j => christoffelEval cov x₀ (γ t) (bb j) v)
        (b := h₂ t)]
    have hD : (∑ j, bb.repr (h₁ t) j * chartGram (I := I) x₀ (γ t) (bb j)
          (christoffelEval cov x₀ (γ t) (h₂ t) v))
        = chartGram (I := I) x₀ (γ t) (h₁ t)
          (christoffelEval cov x₀ (γ t) (h₂ t) v) :=
      (chartGram_eq_sum_fst_repr (I := I) bb x₀ (γ t) (h₁ t)
        (christoffelEval cov x₀ (γ t) (h₂ t) v)).symm
    rw [hA, hB, hC, hD, chartGram_add_fst, chartGram_add_snd]
    ring_nf
  rw [hval] at hderivF
  exact hderivF.congr_of_eventuallyEq (Filter.EventuallyEq.of_eq hsum) (congrFun hsum t)

end Instances

theorem withinJChartGram
    {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E] [CompleteSpace E]
    {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
    {M : Type*} [TopologicalSpace M] [T2Space M] [ChartedSpace H M] [IsManifold I (⊤ : ℕ∞) M]
    (g : Submission.Diff.SMet I M)
    (cov : CovariantDerivative I E (TangentSpace I (M := M)))
    (hmet : ∀ (Y Z : Π x : M, TangentSpace I x),
      ContMDiff I I.tangent (⊤ : ℕ∞) (fun y : M ↦ (⟨y, Y y⟩ : TangentBundle I M)) →
      ContMDiff I I.tangent (⊤ : ℕ∞) (fun y : M ↦ (⟨y, Z y⟩ : TangentBundle I M)) →
      ∀ (x : M) (v : TangentSpace I x),
        mvfderiv I (fun y : M ↦ g.inner y (Y y) (Z y)) x v =
          g.inner x (cov Y x v) (Z x) + g.inner x (Y x) (cov Z x v))
    (x₀ : M) {γ : ℝ → M} {J : Set ℝ} {t : ℝ} {v : TangentSpace I (γ t)}
    (hγ : HasMFDerivWithinAt (modelWithCornersSelf ℝ ℝ) I γ J t
      ((1 : ℝ →L[ℝ] ℝ).smulRight v))
    (hsrc : γ t ∈ (chartAt H x₀).source)
    {h₁ h₂ : ℝ → E} {h₁' h₂' : E}
    (hh₁ : HasDerivWithinAt h₁ h₁' J t) (hh₂ : HasDerivWithinAt h₂ h₂' J t) :
    HasDerivWithinAt
      (fun s ↦ g.inner (γ s)
        (Submission.Geodesic.frameVector x₀ (γ s) (h₁ s))
        (Submission.Geodesic.frameVector x₀ (γ s) (h₂ s)))
      (g.inner (γ t)
          (Submission.Geodesic.frameVector x₀ (γ t)
            (h₁' + Submission.Geodesic.christoffelEval cov x₀ (γ t) (h₁ t) v))
          (Submission.Geodesic.frameVector x₀ (γ t) (h₂ t))
        + g.inner (γ t)
          (Submission.Geodesic.frameVector x₀ (γ t) (h₁ t))
          (Submission.Geodesic.frameVector x₀ (γ t)
            (h₂' + Submission.Geodesic.christoffelEval cov x₀ (γ t) (h₂ t) v))) J t := by
  -- For the metric `g` we use the Riemannian-bundle structure it induces: then the ambient inner
  -- product on the tangent spaces *is* `g.inner` by definition, so the chart-metric product rule
  -- `hasDerivWithinAt_chartGram_wj` applies verbatim.
  letI : RiemannianBundle (fun x : M ↦ TangentSpace I x) := ⟨g.toRiemannianMetric⟩
  haveI : IsContMDiffRiemannianBundle I ∞ E (fun x : M ↦ TangentSpace I x) := inferInstance
  have hmc : IsMetricCompatible cov := hmet
  exact hasDerivWithinAt_chartGram_wj (I := I) cov hmc x₀ hγ hsrc hh₁ hh₂

end

end Work.Diff.STE.C2
