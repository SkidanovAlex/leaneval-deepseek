import Submission.Geodesic
import Submission.Variation
import Submission.Commons.Geometry.Manifold.Tangent.mfderiv_extChartAt_comp
import Submission.Commons.Geometry.Manifold.Tangent.hasMFDerivAt_extChartAt_symm_comp

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false

/-!
# The Riemannian metric in a chart, and the product rule along a curve

`Submission/Geodesic.lean` develops the local theory of geodesics through the chart at a point
`x₀`: the Christoffel symbol `christoffelEval` and the coordinate frame `frameSection`/`frameVector`.
This module adds the *metric* in the same chart,

`chartGram x₀ p a b = ⟪frameVector x₀ p a, frameVector x₀ p b⟫`

(as a bilinear form on the coordinate vectors `a b : E`), proves its local section extension, and
establishes the **product rule along a chart curve**: for a curve `γ` (differentiable at `t`, with
`γ t` in the chart at `x₀`) and fields `h₁`, `h₂` along it,

`d/dt ⟪h₁(t), h₂(t)⟫ = ⟪h₁'(t) + Γ(h₁ t)(γ'(t)), h₂(t)⟫ + ⟪h₁(t), h₂'(t) + Γ(h₂ t)(γ'(t))⟫`

which is the chart form of metric compatibility.  This is the tool that lets us differentiate the
metric along *arbitrary* smooth fields along a curve (which need not come from global sections of
the tangent bundle — those do not always exist, see the docstring of `Submission/Geodesic.lean`).

## Main results

* `exists_contMDiff_section_eventuallyEq_frameSection`: every constant-coordinate frame section can
  be modified near a point to be a *globally* smooth section (multiplying by a bump function), so
  that the challenge's `IsMetricCompatible` (which quantifies over globally smooth sections) can be
  applied to it.
* `hasDerivAt_chartGram_const`: the constant-coordinate case of the product rule.
* `hasDerivAt_chartGram_const_fst` and `hasDerivAt_chartGram`: the product rule with one resp. both
  arguments varying.
-/

set_option linter.unusedSectionVars false

open LeanEval.Geometry.SphereTheorem
open scoped Manifold ContDiff Bundle Topology
open Bundle ContDiff Set VectorField CovariantDerivative Metric
open Submission.Geodesic
open Submission.Variation

variable
  {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    [FiniteDimensional ℝ E] [CompleteSpace E]
  {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
  {M : Type*} [TopologicalSpace M] [T2Space M] [ChartedSpace H M]
    [IsManifold I ∞ M]
  [RiemannianBundle (fun (x : M) ↦ TangentSpace I x)]
  [IsContMDiffRiemannianBundle I ∞ E (fun (x : M) ↦ TangentSpace I x)]

namespace Submission.ChartConnection

noncomputable section

/-! ## Extending a frame section to a globally smooth section -/

/-- A globally smooth section of the tangent bundle which agrees with the constant-coordinate
frame section `frameSection x₀ v` near a point `p` of the chart at `x₀`.  The proof multiplies
`frameSection x₀ v` (which is smooth on the chart) by a smooth bump function supported in the
chart. -/
theorem exists_contMDiff_section_eventuallyEq_frameSection
    (x₀ : M) (v : E) {p : M} (hp : p ∈ (chartAt H x₀).source) :
    ∃ Y : Π x : M, TangentSpace I x, ContMDiff I I.tangent ∞ (T% Y) ∧
      Y =ᶠ[𝓝 p] frameSection (I := I) x₀ v := by
  obtain ⟨ψ, -, hψts⟩ := (SmoothBumpFunction.nhds_basis_tsupport (I := I) p).mem_iff.mp
    ((chartAt H x₀).open_source.mem_nhds hp)
  refine ⟨fun y => ψ y • frameSection (I := I) x₀ v y, ?_, ?_⟩
  · refine ContMDiffOn.smul_section_of_tsupport
      (u := (chartAt H x₀).source)
      (ψ := (ψ : M → ℝ)) (s := frameSection (I := I) x₀ v) ?_ ?_ hψts ?_
    · exact ψ.contMDiff.contMDiffOn
    · exact (chartAt H x₀).open_source
    · exact fun y hy => (contMDiffAt_frameSection (I := I) x₀ v hy).contMDiffWithinAt
  · filter_upwards [ψ.eventuallyEq_one] with y hy
    rw [hy]
    simp only [Pi.one_apply, one_smul]
    try rfl

/-! ## The metric in a chart -/

/-- **The Riemannian metric in the chart at `x₀`**, expressed on the coordinate vectors: the scalar
product of the frame vectors with coordinates `a` and `b` at the point `p`. -/
def chartGram (x₀ p : M) (a b : E) : ℝ :=
  inner ℝ (frameVector (I := I) x₀ p a) (frameVector (I := I) x₀ p b)

lemma chartGram_apply (x₀ p : M) (a b : E) :
    chartGram (I := I) x₀ p a b
      = inner ℝ (frameVector (I := I) x₀ p a) (frameVector (I := I) x₀ p b) := rfl

lemma chartGram_comm (x₀ p : M) (a b : E) :
    chartGram (I := I) x₀ p a b = chartGram (I := I) x₀ p b a := by
  rw [chartGram_apply, chartGram_apply, real_inner_comm]

lemma chartGram_add_fst (x₀ p : M) (a₁ a₂ b : E) :
    chartGram (I := I) x₀ p (a₁ + a₂) b
      = chartGram (I := I) x₀ p a₁ b + chartGram (I := I) x₀ p a₂ b := by
  rw [chartGram_apply, chartGram_apply, chartGram_apply, frameVector_add, inner_add_left]

lemma chartGram_add_snd (x₀ p : M) (a b₁ b₂ : E) :
    chartGram (I := I) x₀ p a (b₁ + b₂)
      = chartGram (I := I) x₀ p a b₁ + chartGram (I := I) x₀ p a b₂ := by
  rw [chartGram_apply, chartGram_apply, chartGram_apply, frameVector_add, inner_add_right]

lemma chartGram_smul_fst (x₀ p : M) (c : ℝ) (a b : E) :
    chartGram (I := I) x₀ p (c • a) b = c * chartGram (I := I) x₀ p a b := by
  rw [chartGram_apply, chartGram_apply, frameVector_smul, inner_smul_left, starRingEnd_apply,
    star_trivial]

lemma chartGram_smul_snd (x₀ p : M) (c : ℝ) (a b : E) :
    chartGram (I := I) x₀ p a (c • b) = c * chartGram (I := I) x₀ p a b := by
  rw [chartGram_apply, chartGram_apply, frameVector_smul, inner_smul_right]

lemma chartGram_sum_fst {ι : Type*} (s : Finset ι) (x₀ p : M) (c : ι → ℝ) (v : ι → E) (b : E) :
    chartGram (I := I) x₀ p (∑ i ∈ s, c i • v i) b
      = ∑ i ∈ s, c i * chartGram (I := I) x₀ p (v i) b := by
  rw [chartGram_apply, frameVector_sum]
  rw [sum_inner]
  refine Finset.sum_congr rfl fun i _ => ?_
  rw [chartGram_apply, inner_smul_left, starRingEnd_apply, star_trivial]

lemma chartGram_sum_snd {ι : Type*} (s : Finset ι) (x₀ p : M) (c : ι → ℝ) (v : ι → E) (a : E) :
    chartGram (I := I) x₀ p a (∑ i ∈ s, c i • v i)
      = ∑ i ∈ s, c i * chartGram (I := I) x₀ p a (v i) := by
  rw [chartGram_apply, frameVector_sum]
  rw [inner_sum]
  refine Finset.sum_congr rfl fun i _ => ?_
  rw [chartGram_apply, inner_smul_right]

/-! ## The product rule along a chart curve -/

/-- Expansion of the chart metric in a basis, in the second argument. -/
lemma chartGram_eq_sum_snd_repr {ι : Type*} [Fintype ι] (bb : Module.Basis ι ℝ E)
    (x₀ p : M) (a b : E) :
    chartGram (I := I) x₀ p a b
      = ∑ i, (bb.repr b i) * chartGram (I := I) x₀ p a (bb i) := by
  conv_lhs => rw [← bb.sum_repr b]
  rw [chartGram_sum_snd (I := I) (x₀ := x₀) (p := p) (s := Finset.univ)
    (c := fun i => bb.repr b i) (v := fun i => bb i) (a := a)]

/-- Expansion of the chart metric in a basis, in the first argument. -/
lemma chartGram_eq_sum_fst_repr {ι : Type*} [Fintype ι] (bb : Module.Basis ι ℝ E)
    (x₀ p : M) (a b : E) :
    chartGram (I := I) x₀ p a b
      = ∑ i, (bb.repr a i) * chartGram (I := I) x₀ p (bb i) b := by
  conv_lhs => rw [← bb.sum_repr a]
  rw [chartGram_sum_fst (I := I) (x₀ := x₀) (p := p) (s := Finset.univ)
    (c := fun i => bb.repr a i) (v := fun i => bb i) (b := b)]

/-- Product rule for functions `ℝ → ℝ`, stated with the pointwise product as an explicit lambda
(the pointwise product of functions is not definitionally the lambda). -/
theorem hasDerivAt_mul_fun {f g : ℝ → ℝ} {f' g' : ℝ} {x : ℝ}
    (hf : HasDerivAt f f' x) (hg : HasDerivAt g g' x) :
    HasDerivAt (fun s => f s * g s) (f' * g x + f x * g') x := by
  have h := hf.mul hg
  rwa [show (f * g) = fun s => f s * g s from by funext s; exact Pi.mul_apply f g s] at h

/-- **The product rule for the chart metric, constant coordinate vectors.**  For a curve `γ`
differentiable at `t` with `γ t` in the chart at `x₀`, the derivative of `s ↦ ⟪a, b⟫_{γ s}` (the
metric evaluated on the coordinate vectors `a`, `b`) is
`⟪Γ(a)(γ'(t)), b⟫ + ⟪a, Γ(b)(γ'(t))⟫`.  This is metric compatibility applied to the (locally
defined) frame sections, which are extended to globally smooth sections by a bump function. -/
theorem hasDerivAt_chartGram_const (cov : CovariantDerivative I E (TangentSpace I (M := M)))
    (hmet : IsMetricCompatible cov) (x₀ : M) (a b : E)
    {γ : ℝ → M} {t : ℝ} (hγ : MDifferentiableAt 𝓘(ℝ) I γ t)
    (hsrc : γ t ∈ (chartAt H x₀).source) :
    HasDerivAt (fun s => chartGram (I := I) x₀ (γ s) a b)
      (chartGram (I := I) x₀ (γ t)
          (christoffelEval cov x₀ (γ t) a (curveVelocity (I := I) γ t)) b
       + chartGram (I := I) x₀ (γ t) a
          (christoffelEval cov x₀ (γ t) b (curveVelocity (I := I) γ t))) t := by
  obtain ⟨Y, hYsm, hYeq⟩ :=
    exists_contMDiff_section_eventuallyEq_frameSection (I := I) x₀ a hsrc
  obtain ⟨Z, hZsm, hZeq⟩ :=
    exists_contMDiff_section_eventuallyEq_frameSection (I := I) x₀ b hsrc
  have hbase : HasDerivAt (fun s => inner ℝ (Y (γ s)) (Z (γ s)))
      (inner ℝ (cov Y (γ t) (curveVelocity (I := I) γ t)) (Z (γ t))
        + inner ℝ (Y (γ t)) (cov Z (γ t) (curveVelocity (I := I) γ t))) t :=
    hasDerivAt_inner_sections cov hmet hYsm hZsm hγ
  have heq : (fun s => inner ℝ (Y (γ s)) (Z (γ s)))
      =ᶠ[𝓝 t] (fun s => chartGram (I := I) x₀ (γ s) a b) := by
    filter_upwards [hγ.continuousAt.preimage_mem_nhds hYeq,
      hγ.continuousAt.preimage_mem_nhds hZeq] with s hs hs'
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
  have hcovYe : cov Y (γ t) (curveVelocity (I := I) γ t)
      = frameVector (I := I) x₀ (γ t)
          (christoffelEval cov x₀ (γ t) a (curveVelocity (I := I) γ t)) := by
    rw [hcovY, cov_frameSection_eq cov x₀ (γ t) a (curveVelocity (I := I) γ t) hsrc]
    rfl
  have hcovZe : cov Z (γ t) (curveVelocity (I := I) γ t)
      = frameVector (I := I) x₀ (γ t)
          (christoffelEval cov x₀ (γ t) b (curveVelocity (I := I) γ t)) := by
    rw [hcovZ, cov_frameSection_eq cov x₀ (γ t) b (curveVelocity (I := I) γ t) hsrc]
    rfl
  have hmain : HasDerivAt (fun s => chartGram (I := I) x₀ (γ s) a b)
      (inner ℝ (cov Y (γ t) (curveVelocity (I := I) γ t)) (Z (γ t))
        + inner ℝ (Y (γ t)) (cov Z (γ t) (curveVelocity (I := I) γ t))) t :=
    hbase.congr_of_eventuallyEq heq.symm
  have hval : inner ℝ (cov Y (γ t) (curveVelocity (I := I) γ t)) (Z (γ t))
      + inner ℝ (Y (γ t)) (cov Z (γ t) (curveVelocity (I := I) γ t))
      = chartGram (I := I) x₀ (γ t)
          (christoffelEval cov x₀ (γ t) a (curveVelocity (I := I) γ t)) b
        + chartGram (I := I) x₀ (γ t) a
          (christoffelEval cov x₀ (γ t) b (curveVelocity (I := I) γ t)) := by
    rw [hcovYe, hYt, hcovZe, hZt]
    rfl
  rwa [hval] at hmain

/-- **The product rule for the chart metric, first argument constant.**  For a curve `γ`
differentiable at `t` with `γ t` in the chart at `x₀` and a differentiable field `h` along it,
`d/dt ⟪a, h(t)⟫ = ⟪a, h'(t)⟫ + ⟪Γ(a)(γ'), h(t)⟫ + ⟪a, Γ(h t)(γ')⟫`. -/
theorem hasDerivAt_chartGram_const_fst (cov : CovariantDerivative I E (TangentSpace I (M := M)))
    (hmet : IsMetricCompatible cov) (x₀ : M) (a : E)
    {γ : ℝ → M} {t : ℝ} (hγ : MDifferentiableAt 𝓘(ℝ) I γ t)
    (hsrc : γ t ∈ (chartAt H x₀).source)
    {h : ℝ → E} {h' : E} (hh : HasDerivAt h h' t) :
    HasDerivAt (fun s => chartGram (I := I) x₀ (γ s) a (h s))
      (chartGram (I := I) x₀ (γ t) a h'
       + chartGram (I := I) x₀ (γ t)
          (christoffelEval cov x₀ (γ t) a (curveVelocity (I := I) γ t)) (h t)
       + chartGram (I := I) x₀ (γ t) a
          (christoffelEval cov x₀ (γ t) (h t) (curveVelocity (I := I) γ t))) t := by
  classical
  let bb : Module.Basis (Fin (Module.finrank ℝ E)) ℝ E := Module.finBasis ℝ E
  -- the expansion of the metric in the basis
  have hsum : (fun s => chartGram (I := I) x₀ (γ s) a (h s))
      = fun s => ∑ j, (bb.repr (h s) j) * chartGram (I := I) x₀ (γ s) a (bb j) := by
    funext s
    conv_lhs => rw [← bb.sum_repr (h s)]
    rw [chartGram_sum_snd (I := I) (x₀ := x₀) (p := γ s) (s := Finset.univ)
      (c := fun j => bb.repr (h s) j) (v := fun j => bb j) (a := a)]
  -- the derivatives of the factors
  have hcoord : ∀ j, HasDerivAt (fun s => bb.repr (h s) j) (bb.repr h' j) t := by
    intro j
    exact (((bb.coord j : E →ₗ[ℝ] ℝ).toContinuousLinearMap).hasFDerivAt.comp_hasDerivAt t hh)
  have hsingle : ∀ j, HasDerivAt (fun s => chartGram (I := I) x₀ (γ s) a (bb j))
      (chartGram (I := I) x₀ (γ t)
          (christoffelEval cov x₀ (γ t) a (curveVelocity (I := I) γ t)) (bb j)
        + chartGram (I := I) x₀ (γ t) a
          (christoffelEval cov x₀ (γ t) (bb j) (curveVelocity (I := I) γ t))) t :=
    fun j => hasDerivAt_chartGram_const cov hmet x₀ a (bb j) hγ hsrc
  have hderivF : HasDerivAt
      (fun s => ∑ j, (bb.repr (h s) j) * chartGram (I := I) x₀ (γ s) a (bb j))
      (∑ j, (bb.repr h' j * chartGram (I := I) x₀ (γ t) a (bb j)
        + bb.repr (h t) j * (chartGram (I := I) x₀ (γ t)
              (christoffelEval cov x₀ (γ t) a (curveVelocity (I := I) γ t)) (bb j)
            + chartGram (I := I) x₀ (γ t) a
              (christoffelEval cov x₀ (γ t) (bb j) (curveVelocity (I := I) γ t))))) t := by
    have h1 : HasDerivAt
        (∑ j ∈ Finset.univ, ((fun s => bb.repr (h s) j) *
          (fun s => chartGram (I := I) x₀ (γ s) a (bb j))))
        (∑ j ∈ Finset.univ, (bb.repr h' j * chartGram (I := I) x₀ (γ t) a (bb j)
          + bb.repr (h t) j * (chartGram (I := I) x₀ (γ t)
                (christoffelEval cov x₀ (γ t) a (curveVelocity (I := I) γ t)) (bb j)
              + chartGram (I := I) x₀ (γ t) a
                (christoffelEval cov x₀ (γ t) (bb j) (curveVelocity (I := I) γ t))))) t := by
      refine HasDerivAt.sum fun j _ => ?_
      exact hasDerivAt_mul_fun (hcoord j) (hsingle j)
    refine h1.congr_of_eventuallyEq (Filter.EventuallyEq.of_eq ?_)
    funext s
    simp only [Finset.sum_apply, Pi.mul_apply]
  have hval : (∑ j, (bb.repr h' j * chartGram (I := I) x₀ (γ t) a (bb j)
        + bb.repr (h t) j * (chartGram (I := I) x₀ (γ t)
              (christoffelEval cov x₀ (γ t) a (curveVelocity (I := I) γ t)) (bb j)
            + chartGram (I := I) x₀ (γ t) a
              (christoffelEval cov x₀ (γ t) (bb j) (curveVelocity (I := I) γ t)))))
      = chartGram (I := I) x₀ (γ t) a h'
       + chartGram (I := I) x₀ (γ t)
          (christoffelEval cov x₀ (γ t) a (curveVelocity (I := I) γ t)) (h t)
       + chartGram (I := I) x₀ (γ t) a
          (christoffelEval cov x₀ (γ t) (h t) (curveVelocity (I := I) γ t)) := by
    simp_rw [mul_add, Finset.sum_add_distrib]
    have hA : (∑ j, bb.repr h' j * chartGram (I := I) x₀ (γ t) a (bb j))
        = chartGram (I := I) x₀ (γ t) a h' :=
      (chartGram_eq_sum_snd_repr (I := I) bb x₀ (γ t) a h').symm
    have hB : (∑ j, bb.repr (h t) j * chartGram (I := I) x₀ (γ t)
          (christoffelEval cov x₀ (γ t) a (curveVelocity (I := I) γ t)) (bb j))
        = chartGram (I := I) x₀ (γ t)
          (christoffelEval cov x₀ (γ t) a (curveVelocity (I := I) γ t)) (h t) :=
      (chartGram_eq_sum_snd_repr (I := I) bb x₀ (γ t)
        (christoffelEval cov x₀ (γ t) a (curveVelocity (I := I) γ t)) (h t)).symm
    have hG : christoffelEval cov x₀ (γ t) (h t) (curveVelocity (I := I) γ t)
        = ∑ j, (bb.repr (h t) j) •
            christoffelEval cov x₀ (γ t) (bb j) (curveVelocity (I := I) γ t) := by
      conv_lhs => rw [← bb.sum_repr (h t)]
      exact christoffelEval_sum_left Finset.univ cov x₀ (γ t) (fun j => bb.repr (h t) j)
        (fun j => bb j) (curveVelocity (I := I) γ t) hsrc
    have hC : (∑ j, bb.repr (h t) j * chartGram (I := I) x₀ (γ t) a
          (christoffelEval cov x₀ (γ t) (bb j) (curveVelocity (I := I) γ t)))
        = chartGram (I := I) x₀ (γ t) a
          (christoffelEval cov x₀ (γ t) (h t) (curveVelocity (I := I) γ t)) := by
      rw [hG, chartGram_sum_snd (I := I) (x₀ := x₀) (p := γ t) (s := Finset.univ)
        (c := fun j => bb.repr (h t) j)
        (v := fun j => christoffelEval cov x₀ (γ t) (bb j) (curveVelocity (I := I) γ t))
        (a := a)]
    rw [hA, hB, hC]
    ring
  rw [hval] at hderivF
  exact hderivF.congr_of_eventuallyEq (Filter.EventuallyEq.of_eq hsum)


/-- **The product rule for the chart metric.**  For a curve `γ` differentiable at `t` with `γ t` in
the chart at `x₀`, and differentiable fields `h₁`, `h₂` along it,
`d/dt ⟪h₁(t), h₂(t)⟫ = ⟪h₁'(t) + Γ(h₁ t)(γ'), h₂(t)⟫ + ⟪h₁(t), h₂'(t) + Γ(h₂ t)(γ')⟫`.
This is the chart form of metric compatibility; it does not require the fields to come from global
sections of the tangent bundle. -/
theorem hasDerivAt_chartGram (cov : CovariantDerivative I E (TangentSpace I (M := M)))
    (hmet : IsMetricCompatible cov) (x₀ : M)
    {γ : ℝ → M} {t : ℝ} (hγ : MDifferentiableAt 𝓘(ℝ) I γ t)
    (hsrc : γ t ∈ (chartAt H x₀).source)
    {h₁ h₂ : ℝ → E} {h₁' h₂' : E}
    (hh₁ : HasDerivAt h₁ h₁' t) (hh₂ : HasDerivAt h₂ h₂' t) :
    HasDerivAt (fun s => chartGram (I := I) x₀ (γ s) (h₁ s) (h₂ s))
      (chartGram (I := I) x₀ (γ t)
          (h₁' + christoffelEval cov x₀ (γ t) (h₁ t) (curveVelocity (I := I) γ t)) (h₂ t)
       + chartGram (I := I) x₀ (γ t) (h₁ t)
          (h₂' + christoffelEval cov x₀ (γ t) (h₂ t) (curveVelocity (I := I) γ t))) t := by
  classical
  let bb : Module.Basis (Fin (Module.finrank ℝ E)) ℝ E := Module.finBasis ℝ E
  have hsum : (fun s => chartGram (I := I) x₀ (γ s) (h₁ s) (h₂ s))
      = fun s => ∑ j, (bb.repr (h₁ s) j) * chartGram (I := I) x₀ (γ s) (bb j) (h₂ s) := by
    funext s
    exact chartGram_eq_sum_fst_repr (I := I) bb x₀ (γ s) (h₁ s) (h₂ s)
  have hcoord : ∀ j, HasDerivAt (fun s => bb.repr (h₁ s) j) (bb.repr h₁' j) t := by
    intro j
    exact (((bb.coord j : E →ₗ[ℝ] ℝ).toContinuousLinearMap).hasFDerivAt.comp_hasDerivAt t hh₁)
  have hsingle : ∀ j, HasDerivAt (fun s => chartGram (I := I) x₀ (γ s) (bb j) (h₂ s))
      (chartGram (I := I) x₀ (γ t) (bb j) h₂'
       + chartGram (I := I) x₀ (γ t)
          (christoffelEval cov x₀ (γ t) (bb j) (curveVelocity (I := I) γ t)) (h₂ t)
       + chartGram (I := I) x₀ (γ t) (bb j)
          (christoffelEval cov x₀ (γ t) (h₂ t) (curveVelocity (I := I) γ t))) t :=
    fun j => hasDerivAt_chartGram_const_fst cov hmet x₀ (bb j) hγ hsrc hh₂
  have hderivF : HasDerivAt
      (fun s => ∑ j, (bb.repr (h₁ s) j) * chartGram (I := I) x₀ (γ s) (bb j) (h₂ s))
      (∑ j, (bb.repr h₁' j * chartGram (I := I) x₀ (γ t) (bb j) (h₂ t)
        + bb.repr (h₁ t) j * (chartGram (I := I) x₀ (γ t) (bb j) h₂'
          + chartGram (I := I) x₀ (γ t)
              (christoffelEval cov x₀ (γ t) (bb j) (curveVelocity (I := I) γ t)) (h₂ t)
          + chartGram (I := I) x₀ (γ t) (bb j)
              (christoffelEval cov x₀ (γ t) (h₂ t) (curveVelocity (I := I) γ t))))) t := by
    have h1 : HasDerivAt
        (∑ j ∈ Finset.univ, ((fun s => bb.repr (h₁ s) j) *
          (fun s => chartGram (I := I) x₀ (γ s) (bb j) (h₂ s))))
        (∑ j ∈ Finset.univ, (bb.repr h₁' j * chartGram (I := I) x₀ (γ t) (bb j) (h₂ t)
          + bb.repr (h₁ t) j * (chartGram (I := I) x₀ (γ t) (bb j) h₂'
            + chartGram (I := I) x₀ (γ t)
                (christoffelEval cov x₀ (γ t) (bb j) (curveVelocity (I := I) γ t)) (h₂ t)
            + chartGram (I := I) x₀ (γ t) (bb j)
                (christoffelEval cov x₀ (γ t) (h₂ t) (curveVelocity (I := I) γ t))))) t := by
      refine HasDerivAt.sum fun j _ => ?_
      refine (hasDerivAt_mul_fun (hcoord j) (hsingle j)).congr_of_eventuallyEq ?_
      exact Filter.EventuallyEq.of_eq (by
        funext s
        exact (Pi.mul_apply (fun s => bb.repr (h₁ s) j)
          (fun s => chartGram (I := I) x₀ (γ s) (bb j) (h₂ s)) s).symm)
    refine h1.congr_of_eventuallyEq (Filter.EventuallyEq.of_eq ?_)
    funext s
    simp only [Finset.sum_apply, Pi.mul_apply]
  have hval : (∑ j, (bb.repr h₁' j * chartGram (I := I) x₀ (γ t) (bb j) (h₂ t)
        + bb.repr (h₁ t) j * (chartGram (I := I) x₀ (γ t) (bb j) h₂'
          + chartGram (I := I) x₀ (γ t)
              (christoffelEval cov x₀ (γ t) (bb j) (curveVelocity (I := I) γ t)) (h₂ t)
          + chartGram (I := I) x₀ (γ t) (bb j)
              (christoffelEval cov x₀ (γ t) (h₂ t) (curveVelocity (I := I) γ t)))))
      = chartGram (I := I) x₀ (γ t)
          (h₁' + christoffelEval cov x₀ (γ t) (h₁ t) (curveVelocity (I := I) γ t)) (h₂ t)
       + chartGram (I := I) x₀ (γ t) (h₁ t)
          (h₂' + christoffelEval cov x₀ (γ t) (h₂ t) (curveVelocity (I := I) γ t)) := by
    simp_rw [mul_add, Finset.sum_add_distrib]
    have hA : (∑ j, bb.repr h₁' j * chartGram (I := I) x₀ (γ t) (bb j) (h₂ t))
        = chartGram (I := I) x₀ (γ t) h₁' (h₂ t) :=
      (chartGram_eq_sum_fst_repr (I := I) bb x₀ (γ t) h₁' (h₂ t)).symm
    have hB : (∑ j, bb.repr (h₁ t) j * chartGram (I := I) x₀ (γ t) (bb j) h₂')
        = chartGram (I := I) x₀ (γ t) (h₁ t) h₂' :=
      (chartGram_eq_sum_fst_repr (I := I) bb x₀ (γ t) (h₁ t) h₂').symm
    have hΓ₁ : christoffelEval cov x₀ (γ t) (h₁ t) (curveVelocity (I := I) γ t)
        = ∑ j, (bb.repr (h₁ t) j) •
            christoffelEval cov x₀ (γ t) (bb j) (curveVelocity (I := I) γ t) := by
      conv_lhs => rw [← bb.sum_repr (h₁ t)]
      exact christoffelEval_sum_left Finset.univ cov x₀ (γ t) (fun j => bb.repr (h₁ t) j)
        (fun j => bb j) (curveVelocity (I := I) γ t) hsrc
    have hC : (∑ j, bb.repr (h₁ t) j * chartGram (I := I) x₀ (γ t)
          (christoffelEval cov x₀ (γ t) (bb j) (curveVelocity (I := I) γ t)) (h₂ t))
        = chartGram (I := I) x₀ (γ t)
          (christoffelEval cov x₀ (γ t) (h₁ t) (curveVelocity (I := I) γ t)) (h₂ t) := by
      rw [hΓ₁, chartGram_sum_fst (I := I) (x₀ := x₀) (p := γ t) (s := Finset.univ)
        (c := fun j => bb.repr (h₁ t) j)
        (v := fun j => christoffelEval cov x₀ (γ t) (bb j) (curveVelocity (I := I) γ t))
        (b := h₂ t)]
    have hD : (∑ j, bb.repr (h₁ t) j * chartGram (I := I) x₀ (γ t) (bb j)
          (christoffelEval cov x₀ (γ t) (h₂ t) (curveVelocity (I := I) γ t)))
        = chartGram (I := I) x₀ (γ t) (h₁ t)
          (christoffelEval cov x₀ (γ t) (h₂ t) (curveVelocity (I := I) γ t)) :=
      (chartGram_eq_sum_fst_repr (I := I) bb x₀ (γ t) (h₁ t)
        (christoffelEval cov x₀ (γ t) (h₂ t) (curveVelocity (I := I) γ t))).symm
    rw [hA, hB, hC, hD, chartGram_add_fst, chartGram_add_snd]
    ring_nf
  rw [hval] at hderivF
  exact hderivF.congr_of_eventuallyEq (Filter.EventuallyEq.of_eq hsum)

/-- The chart curve attached to a coordinate curve `u`, together with the identification of its
velocity.  Helper for the following corollaries. -/
lemma curveVelocity_chartCurve {x₀ : M} {u : ℝ → E} {v : E} {t : ℝ}
    (hu : HasDerivAt u v t) (htgt : u t ∈ (extChartAt I x₀).target)
    (hstay : ∀ᶠ s in 𝓝 t, u s ∈ (extChartAt I x₀).target) :
    curveVelocity (I := I) (fun s => (extChartAt I x₀).symm (u s)) t
      = frameVector (I := I) x₀ ((extChartAt I x₀).symm (u t)) v := by
  rw [curveVelocity_extChartAt_symm (I := I) (x₀ := x₀) hu htgt hstay]
  rfl

/-- The chart curve attached to a coordinate curve is differentiable. -/
lemma mdifferentiableAt_chartCurve {x₀ : M} {u : ℝ → E} {v : E} {t : ℝ}
    (hu : HasDerivAt u v t) (htgt : u t ∈ (extChartAt I x₀).target)
    (hstay : ∀ᶠ s in 𝓝 t, u s ∈ (extChartAt I x₀).target) :
    MDifferentiableAt 𝓘(ℝ) I (fun s => (extChartAt I x₀).symm (u s)) t :=
  (Commons.Geometry.Manifold.Tangent.hasMFDerivAt_extChartAt_symm_comp (I := I)
    hu htgt hstay).mdifferentiableAt

/-- The chart curve attached to a coordinate curve stays in the chart source. -/
lemma mem_source_chartCurve {x₀ : M} {u : ℝ → E} {t : ℝ}
    (htgt : u t ∈ (extChartAt I x₀).target) :
    (extChartAt I x₀).symm (u t) ∈ (chartAt H x₀).source := by
  have h1 := PartialEquiv.target_subset_preimage_source (extChartAt I x₀) htgt
  rwa [extChartAt_source] at h1

/-- **The product rule for the chart metric, constant coordinate vectors**, in the form of a
coordinate curve `u` with velocity `v`. -/
theorem hasDerivAt_chartGram_const_curve (cov : CovariantDerivative I E (TangentSpace I (M := M)))
    (hmet : IsMetricCompatible cov) (x₀ : M) (a b : E)
    {u : ℝ → E} {v : E} {t : ℝ} (hu : HasDerivAt u v t)
    (htgt : u t ∈ (extChartAt I x₀).target)
    (hstay : ∀ᶠ s in 𝓝 t, u s ∈ (extChartAt I x₀).target) :
    HasDerivAt (fun s => chartGram (I := I) x₀ ((extChartAt I x₀).symm (u s)) a b)
      (chartGram (I := I) x₀ ((extChartAt I x₀).symm (u t))
          (christoffelEval cov x₀ ((extChartAt I x₀).symm (u t)) a
            (frameVector (I := I) x₀ ((extChartAt I x₀).symm (u t)) v)) b
       + chartGram (I := I) x₀ ((extChartAt I x₀).symm (u t)) a
          (christoffelEval cov x₀ ((extChartAt I x₀).symm (u t)) b
            (frameVector (I := I) x₀ ((extChartAt I x₀).symm (u t)) v))) t := by
  have hγ := mdifferentiableAt_chartCurve (I := I) hu htgt hstay
  have hsrc := mem_source_chartCurve (I := I) (x₀ := x₀) htgt
  have h := hasDerivAt_chartGram_const cov hmet x₀ a b hγ hsrc
  rwa [curveVelocity_chartCurve (I := I) hu htgt hstay] at h

/-- **The product rule for the chart metric**, in the form of a coordinate curve `u` with velocity
`v` and two differentiable fields `h₁`, `h₂`. -/
theorem hasDerivAt_chartGram_curve (cov : CovariantDerivative I E (TangentSpace I (M := M)))
    (hmet : IsMetricCompatible cov) (x₀ : M)
    {u : ℝ → E} {v : E} {t : ℝ} (hu : HasDerivAt u v t)
    (htgt : u t ∈ (extChartAt I x₀).target)
    (hstay : ∀ᶠ s in 𝓝 t, u s ∈ (extChartAt I x₀).target)
    {h₁ h₂ : ℝ → E} {h₁' h₂' : E}
    (hh₁ : HasDerivAt h₁ h₁' t) (hh₂ : HasDerivAt h₂ h₂' t) :
    HasDerivAt (fun s => chartGram (I := I) x₀ ((extChartAt I x₀).symm (u s)) (h₁ s) (h₂ s))
      (chartGram (I := I) x₀ ((extChartAt I x₀).symm (u t))
          (h₁' + christoffelEval cov x₀ ((extChartAt I x₀).symm (u t)) (h₁ t)
            (frameVector (I := I) x₀ ((extChartAt I x₀).symm (u t)) v)) (h₂ t)
       + chartGram (I := I) x₀ ((extChartAt I x₀).symm (u t)) (h₁ t)
          (h₂' + christoffelEval cov x₀ ((extChartAt I x₀).symm (u t)) (h₂ t)
            (frameVector (I := I) x₀ ((extChartAt I x₀).symm (u t)) v))) t := by
  have hγ := mdifferentiableAt_chartCurve (I := I) hu htgt hstay
  have hsrc := mem_source_chartCurve (I := I) (x₀ := x₀) htgt
  have h := hasDerivAt_chartGram cov hmet x₀ hγ hsrc hh₁ hh₂
  rwa [curveVelocity_chartCurve (I := I) hu htgt hstay] at h

end

end Submission.ChartConnection
