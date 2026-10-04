/-
# From local chart data to a global smooth metric

Given a family of positive definite bilinear forms `h x` on the tangent spaces `TₓM`, whose
*chart matrix* in the coordinate frame of every chart of `M`,

  `y ↦ (i j ↦ h ((extChartAt I x₀).symm y) (frameVector x₀ _ (bB i)) (frameVector x₀ _ (bB j)))`,

is `C^∞` on the chart target, we build a global smooth Riemannian metric
`g : Submission.Diff.SMet I M` with `g.inner x = h x` for every `x`.

This is the "manifold packaging" step of the geometric layer of the short-time existence proof:
the analytic core produces the chart matrices of a metric, and this lemma assembles them into the
global object `SMet I M` (`ContMDiffRiemannianMetric`) on which the rest of the development
(Levi-Civita connection, curvature, Ricci flow) is stated.

## Contents

* `Work.Diff.STE.Man.isVonNBounded_quadForm` — a positive definite continuous bilinear form on a
  finite dimensional real normed space has bounded sublevel sets of its quadratic form.  (The
  minimum of the quadratic form on the unit sphere is positive, so the form dominates
  `c ‖v‖²`.)
* `Work.Diff.STE.Man.isVonNBounded_quadForm_of_equiv` — the same statement on a fiber of a vector
  bundle, transported along a continuous linear equivalence with a normed space.
* `Work.Diff.STE.Man.isVonNBounded_of_posDef` — the `isVonNBounded` field of the metric, on the
  tangent spaces of `M`.
* `Work.Diff.STE.Man.section_contMDiffAt_of_frameMat` — smoothness of the section
  `x ↦ ⟨x, h x⟩` of the bundle of bilinear forms, from the smoothness of its frame matrix
  (the time-independent version of `Work.Diff.EXT.section_of_frameMat`).
* `Work.Diff.STE.Man.exists_sMet_of_chartData` — the target.
-/

import Mathlib
import Submission.Work.Diff.STE.Man.Defs
import Submission.Work.Diff.EXT.glueDefs
import Submission.Work.Diff.EXT.inCoordinates_tangent_bilin

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false

set_option autoImplicit false
set_option synthInstance.maxHeartbeats 1000000
set_option maxHeartbeats 1000000
set_option linter.unusedSectionVars false

open scoped Manifold ContDiff Bundle Topology BigOperators
open Bundle ContDiff Set VectorField CovariantDerivative Metric Bornology

namespace Work.Diff.STE.Man

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]
  [CompleteSpace E]
  {H' : Type*} [TopologicalSpace H'] {I : ModelWithCorners ℝ E H'}
  {M : Type*} [TopologicalSpace M] [ChartedSpace H' M] [IsManifold I (⊤ : ℕ∞) M]

noncomputable section

/-! ## Boundedness of the sublevel sets of a positive definite quadratic form -/

/-- **A positive definite continuous bilinear form on a finite dimensional real normed space has
bounded sublevel sets.**  Equivalently: the quadratic form `v ↦ B v v` dominates `c ‖v‖²` for some
`c > 0`, since its minimum on the (compact, nonempty) unit sphere is positive. -/
lemma isVonNBounded_quadForm
    {F : Type*} [NormedAddCommGroup F] [NormedSpace ℝ F] [FiniteDimensional ℝ F]
    (B : F →L[ℝ] F →L[ℝ] ℝ) (hpos : ∀ v, v ≠ 0 → 0 < B v v) :
    Bornology.IsVonNBounded ℝ {v : F | B v v < 1} := by
  have hcont : Continuous fun v : F => B v v := by
    have hp : Continuous fun v : F => (v, v) := continuous_id.prodMk continuous_id
    exact (ContinuousLinearMap.continuous₂ B).comp hp
  rcases subsingleton_or_nontrivial F with hs | hn
  · haveI := hs
    exact Bornology.IsVonNBounded.of_subsingleton
  · haveI := hn
    -- the unit sphere is nonempty and compact; the minimum of the quadratic form there is positive
    have hne : (Metric.sphere (0 : F) 1).Nonempty := NormedSpace.sphere_nonempty.mpr (by norm_num)
    obtain ⟨w₀, hw₀mem, hw₀min⟩ := (isCompact_sphere (0 : F) 1).exists_isMinOn hne
      hcont.continuousOn
    have hw₀n : ‖w₀‖ = 1 := by
      rw [Metric.mem_sphere, dist_eq_norm, sub_zero] at hw₀mem; exact hw₀mem
    have hw₀ne : w₀ ≠ 0 := by intro h; rw [h, norm_zero] at hw₀n; norm_num at hw₀n
    set c : ℝ := B w₀ w₀ with hcdef
    have hc : 0 < c := hpos w₀ hw₀ne
    -- the form dominates `c ‖v‖²`
    have hbound : ∀ v : F, c * ‖v‖ ^ 2 ≤ B v v := by
      intro v
      rw [hcdef]
      rcases eq_or_ne v 0 with rfl | hv
      · simp
      · have hvn : (0 : ℝ) < ‖v‖ := norm_pos_iff.mpr hv
        have hunit : (‖v‖⁻¹ : ℝ) • v ∈ Metric.sphere (0 : F) 1 := by
          rw [Metric.mem_sphere, dist_eq_norm, sub_zero, norm_smul, Real.norm_eq_abs, abs_inv,
            abs_of_nonneg (le_of_lt hvn), inv_mul_cancel₀ (ne_of_gt hvn)]
        have hmin := hw₀min hunit
        simp only [Set.mem_ofPred_eq] at hmin
        have hexp : B ((‖v‖⁻¹ : ℝ) • v) ((‖v‖⁻¹ : ℝ) • v)
            = (‖v‖⁻¹) ^ 2 * B v v := by
          simp only [map_smul, smul_apply, smul_eq_mul]
          ring
        rw [hexp] at hmin
        have h2 : (‖v‖⁻¹) ^ 2 * ‖v‖ ^ 2 = 1 := by
          rw [← mul_pow, inv_mul_cancel₀ (ne_of_gt hvn), one_pow]
        have h4 : c * ‖v‖ ^ 2 ≤ ((‖v‖⁻¹) ^ 2 * B v v) * ‖v‖ ^ 2 :=
          mul_le_mul_of_nonneg_right hmin (by positivity)
        refine le_of_le_of_eq h4 ?_
        calc ((‖v‖⁻¹) ^ 2 * B v v) * ‖v‖ ^ 2
            = ((‖v‖⁻¹) ^ 2 * ‖v‖ ^ 2) * B v v := by ring
          _ = 1 * B v v := by rw [h2]
          _ = B v v := one_mul _
    rw [NormedSpace.isVonNBounded_iff']
    refine ⟨max (1 / c) 1 + 1, fun v hv => ?_⟩
    simp only [Set.mem_ofPred_eq] at hv
    by_contra hcon
    push Not at hcon
    have hlt : 1 / c < ‖v‖ := by have := le_max_left (1 / c) 1; linarith
    have hlt1 : 1 < ‖v‖ := by have := le_max_right (1 / c) 1; linarith
    have h1 : 1 < c * ‖v‖ ^ 2 := by
      have hn0 : (0 : ℝ) ≤ ‖v‖ := norm_nonneg v
      have hdiv : 1 < c * ‖v‖ := by rw [div_lt_iff₀ hc] at hlt; linarith
      nlinarith
    linarith [hbound v, hv]

/-- **Boundedness of the sublevel sets, transported along a linear isomorphism.**  If `A` is the
fiber of a vector bundle, `e : A ≃L[ℝ] F` a continuous linear equivalence with a finite dimensional
normed space, and `B` a positive definite continuous bilinear form on `A`, then the sublevel set of
`v ↦ B v v` is von Neumann bounded for the topology of `A`. -/
lemma isVonNBounded_quadForm_of_equiv
    {A : Type*} [TopologicalSpace A] [AddCommGroup A] [Module ℝ A]
    {F : Type*} [NormedAddCommGroup F] [NormedSpace ℝ F] [FiniteDimensional ℝ F]
    (e : A ≃L[ℝ] F) (B : A →L[ℝ] A →L[ℝ] ℝ) (hpos : ∀ v, v ≠ 0 → 0 < B v v) :
    Bornology.IsVonNBounded ℝ {v : A | B v v < 1} := by
  have hsymm : ∀ w : F, e.symm w = 0 ↔ w = 0 := by
    intro w
    constructor
    · intro h
      have := congrArg e h
      rwa [ContinuousLinearEquiv.apply_symm_apply, map_zero] at this
    · intro h; rw [h, map_zero]
  -- transport `B` to `F`: `B' w w' = B (e.symm w) (e.symm w')`
  set B' : F →L[ℝ] F →L[ℝ] ℝ :=
    (ContinuousLinearEquiv.arrowCongr e
      (ContinuousLinearEquiv.arrowCongr e (ContinuousLinearEquiv.refl ℝ ℝ))) B with hB'def
  have hB'w : ∀ w : F, B' w w = B (e.symm w) (e.symm w) := fun w => rfl
  have hpos' : ∀ w : F, w ≠ 0 → 0 < B' w w := by
    intro w hw
    rw [hB'w w]
    exact hpos _ (fun h => hw ((hsymm w).mp h))
  have hT : Bornology.IsVonNBounded ℝ {w : F | B' w w < 1} :=
    isVonNBounded_quadForm B' hpos'
  have hT' : Bornology.IsVonNBounded ℝ {w : F | B (e.symm w) (e.symm w) < 1} := by
    simpa only [hB'w] using hT
  -- push forward along `e.symm`
  have himg := hT'.image (e.symm : F →L[ℝ] A)
  have hset : (e.symm : F →L[ℝ] A) '' {w : F | B (e.symm w) (e.symm w) < 1}
      = {v : A | B v v < 1} := by
    ext v
    simp only [Set.mem_image, Set.mem_ofPred_eq]
    constructor
    · rintro ⟨w, hw, rfl⟩; exact hw
    · intro hv
      refine ⟨e v, ?_, ?_⟩
      · rw [show e.symm (e v) = v from ContinuousLinearEquiv.symm_apply_apply e v]; exact hv
      · exact ContinuousLinearEquiv.symm_apply_apply e v
  rwa [hset] at himg

/-- **The `isVonNBounded` field of the metric on the tangent spaces of `M`**: for a pointwise
positive definite family `h` of bilinear forms, the set `{v : TₓM | h x v v < 1}` is von Neumann
bounded for the topology of the fiber `TₓM` (which is the topology of the model space `E` read
through the chart trivialisation at `x`). -/
lemma isVonNBounded_of_posDef
    (h : (x : M) → TangentSpace I x →L[ℝ] TangentSpace I x →L[ℝ] ℝ)
    (hpos : ∀ x v, v ≠ 0 → 0 < h x v v) (x : M) :
    Bornology.IsVonNBounded ℝ {v : TangentSpace I x | h x v v < 1} :=
  isVonNBounded_quadForm_of_equiv
    (Trivialization.continuousLinearEquivAt ℝ (trivializationAt E (TangentSpace I) x) x
      (FiberBundle.mem_baseSet_trivializationAt' x)) (h x) (fun v hv => hpos x v hv)

/-! ## Smoothness of the section from the smoothness of its frame matrix -/

/-- **From the frame matrix of a family of forms to the section itself.**  If the matrix of a family
`γ` of bilinear forms in the coordinate frame of the chart at `x₀` is `C^∞` at `x₀` as an
`MatE`-valued map, then the section `x ↦ ⟨x, γ x⟩` of the bundle of bilinear forms is `C^∞` at
`x₀`.

This is the time-independent version of `Work.Diff.EXT.section_of_frameMat`; the reduction uses
Mathlib's `contMDiffAt_hom_bundle` and, on the chart at `x₀`, the identification
`inCoordinates_tangent_bilin` of the trivialised form with the reconstruction of its frame
matrix. -/
theorem section_contMDiffAt_of_frameMat
    {γ : (x : M) → TangentSpace I x →L[ℝ] TangentSpace I x →L[ℝ] ℝ} {x₀ : M}
    (h : ContMDiffAt I (𝓘(ℝ, Work.Diff.EXT.MatE (E := E))) (⊤ : ℕ∞)
        (fun x : M => Work.Diff.EXT.frameMat (I := I) x₀ x (γ x)) x₀) :
    ContMDiffAt I (I.prod 𝓘(ℝ, E →L[ℝ] E →L[ℝ] ℝ)) (⊤ : ℕ∞)
      (fun x : M => TotalSpace.mk' (E →L[ℝ] E →L[ℝ] ℝ)
        (E := fun x : M => TangentSpace I x →L[ℝ] TangentSpace I x →L[ℝ] ℝ) x (γ x)) x₀ := by
  -- the chart at `x₀` contains `x₀`, so it is a neighbourhood of `x₀`
  have hb : ∀ᶠ x : M in 𝓝 x₀, x ∈ (chartAt H' x₀).source :=
    IsOpen.mem_nhds (chartAt H' x₀).open_source (mem_chart_source H' x₀)
  -- the section is a map into a hom bundle: reduce to base + trivialised component
  refine (contMDiffAt_hom_bundle (𝕜 := ℝ) (F₁ := E) (F₂ := E →L[ℝ] ℝ)
    (E₁ := fun x : M => TangentSpace I x) (E₂ := fun x : M => TangentSpace I x →L[ℝ] ℝ)
    (B := M) (M := M) (IB := I) (IM := I)
    (f := fun x : M => Bundle.TotalSpace.mk' (E →L[ℝ] E →L[ℝ] ℝ)
      (E := fun x : M => TangentSpace I x →L[ℝ] TangentSpace I x →L[ℝ] ℝ) x (γ x))
    (x₀ := x₀)).mpr ?_
  refine ⟨contMDiffAt_id, ?_⟩
  -- the trivialised component is the composition of the frame matrix with the linear map
  -- `matToBilin`, which is `C^∞`
  have hlift : ContDiff ℝ (⊤ : ℕ∞)
      (fun A : Work.Diff.EXT.MatE (E := E) => Work.Diff.EXT.matToBilin (E := E) A) :=
    ContinuousLinearMap.contDiff (𝕜 := ℝ) (E := Work.Diff.EXT.MatE (E := E))
      (F := (E →L[ℝ] E →L[ℝ] ℝ)) (n := (⊤ : ℕ∞)) (Work.Diff.EXT.matToBilin (E := E))
  have hmat : ContMDiffAt I (𝓘(ℝ, E →L[ℝ] E →L[ℝ] ℝ)) (⊤ : ℕ∞)
      (fun x : M => Work.Diff.EXT.matToBilin (E := E)
        (Work.Diff.EXT.frameMat (I := I) x₀ x (γ x))) x₀ :=
    hlift.contDiffAt.comp_contMDiffAt h
  refine hmat.congr_of_eventuallyEq ?_
  filter_upwards [hb] with x hx
  -- on the chart at `x₀`, the trivialised form is the reconstruction of its frame matrix
  exact Work.Diff.EXT.inCoordinates_tangent_bilin (I := I) (x₀ := x₀) (x := x) hx (φ := γ x)

/-! ## The target -/

theorem exists_sMet_of_chartData
    {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E] [CompleteSpace E]
    {H' : Type*} [TopologicalSpace H'] {I : ModelWithCorners ℝ E H'}
    {M : Type*} [TopologicalSpace M] [ChartedSpace H' M] [IsManifold I (⊤ : ℕ∞) M]
    [I.Boundaryless] [T2Space M]
    (h : (x : M) → TangentSpace I x →L[ℝ] TangentSpace I x →L[ℝ] ℝ)
    (hsym : ∀ x u v, h x u v = h x v u)
    (hpos : ∀ x v, v ≠ 0 → 0 < h x v v)
    (hsmooth : ∀ x₀ : M, ContDiffOn ℝ (⊤ : ℕ∞)
      (fun y : E => fun i j : Fin (Module.finrank ℝ E) =>
        h ((extChartAt I x₀).symm y)
          (Submission.Geodesic.frameVector (I := I) x₀ ((extChartAt I x₀).symm y)
            (Work.Diff.EXT.bB (E := E) i))
          (Submission.Geodesic.frameVector (I := I) x₀ ((extChartAt I x₀).symm y)
            (Work.Diff.EXT.bB (E := E) j)))
      (extChartAt I x₀).target) :
    ∃ g : Submission.Diff.SMet I M, ∀ x u v, g.inner x u v = h x u v := by
  -- smoothness of the frame matrix in the chart at each centre
  have hframe : ∀ x₀ : M, ContMDiffAt I (𝓘(ℝ, Work.Diff.EXT.MatE (E := E))) (⊤ : ℕ∞)
      (fun x : M => Work.Diff.EXT.frameMat (I := I) x₀ x (h x)) x₀ := by
    intro x₀
    have h1 : ContDiffAt ℝ (⊤ : ℕ∞)
        (fun y : E => Work.Diff.EXT.frameMat (I := I) x₀ ((extChartAt I x₀).symm y)
          (h ((extChartAt I x₀).symm y))) ((extChartAt I x₀) x₀) :=
      (hsmooth x₀).contDiffAt (extChartAt_target_mem_nhds x₀)
    have h2 : ContMDiffAt (𝓘(ℝ, E)) (𝓘(ℝ, Work.Diff.EXT.MatE (E := E))) (⊤ : ℕ∞)
        (fun y : E => Work.Diff.EXT.frameMat (I := I) x₀ ((extChartAt I x₀).symm y)
          (h ((extChartAt I x₀).symm y))) ((extChartAt I x₀) x₀) := h1.contMDiffAt
    have h3 := h2.comp x₀ (contMDiffAt_extChartAt (I := I) (x := x₀))
    refine h3.congr_of_eventuallyEq ?_
    filter_upwards [IsOpen.mem_nhds (chartAt H' x₀).open_source (mem_chart_source H' x₀)]
      with x hx
    have hx' : x ∈ (extChartAt I x₀).source := by rwa [extChartAt_source]
    simp only [Function.comp_apply]
    rw [show (extChartAt I x₀).symm ((extChartAt I x₀) x) = x from (extChartAt I x₀).left_inv hx']
  -- smoothness of the section of the bundle of bilinear forms
  have hsec : ∀ x₀ : M, ContMDiffAt I (I.prod 𝓘(ℝ, E →L[ℝ] E →L[ℝ] ℝ)) (⊤ : ℕ∞)
      (fun x : M => TotalSpace.mk' (E →L[ℝ] E →L[ℝ] ℝ)
        (E := fun x : M => TangentSpace I x →L[ℝ] TangentSpace I x →L[ℝ] ℝ) x (h x)) x₀ :=
    fun x₀ => section_contMDiffAt_of_frameMat (I := I) (x₀ := x₀) (γ := h) (hframe x₀)
  refine ⟨{ inner := h
            symm := hsym
            pos := hpos
            isVonNBounded := fun x => isVonNBounded_of_posDef (I := I) h hpos x
            contMDiff := hsec }, ?_⟩
  intro x u v
  rfl

end

end Work.Diff.STE.Man
