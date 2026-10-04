import Mathlib
import Submission.Work.Diff.EXT.ricCore

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false

/-!
# Smoothness of the spatial derivative of a jointly smooth family along a smooth field

`Work.Diff.EXT.mvfderiv_eq_fderivWithin_target` is the *pointwise chart formula* for `mvfderiv`
along a field: if `y` lies in the extended chart at `x`, then the derivative of `f` at `y` in the
direction of the tangent vector `A y` is the ordinary Fréchet derivative of the chart-written
function `f ∘ (extChartAt I x).symm`, taken within the chart target.  It is the replacement, for a
general `F`, of `Submission.ChartCurvCont.mvfderiv_frameVector_eq_fderiv` (which is stated for
`F = E` and needs `[I.Boundaryless]`); the proof uses the *within*-set chain rule
`Commons.Geometry.Manifold.VectorField.mvfderivWithin_comp_apply_vec`, so no boundary hypothesis is
needed, not even in intermediate goals.

The main theorem `Work.Diff.EXT.contMDiffAt_mvfderiv_along_field` is the joint smoothness of
`(t, y) ↦ d_y Φ(t, ·)(A y)`.  Both hypotheses and the conclusion are local, so the proof reduces to
the chart at `x`; there the mixture of the two variables becomes a parametric Fréchet derivative
and is handled by Mathlib's `ContDiffWithinAt.fderivWithin_apply`.
-/

set_option linter.unusedSectionVars false
set_option maxHeartbeats 1000000

open scoped Manifold ContDiff Bundle Topology
open Bundle ContDiff Set VectorField CovariantDerivative Metric Filter
open Commons.Geometry.Manifold.VectorField

namespace Work.Diff.EXT

noncomputable section

variable
  {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E] [CompleteSpace E]
  {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
  {M : Type*} [TopologicalSpace M] [ChartedSpace H M] [IsManifold I (⊤ : ℕ∞) M]

/-- **Pointwise chart formula for `mvfderiv` along a field.**  If `y` lies in the extended chart at
`x` and `f : M → F` is differentiable at `y`, then the derivative of `f` at `y` in the direction of
the tangent vector `A y` is the Fréchet derivative, within the chart target, of the chart-written
function `f ∘ (extChartAt I x).symm`, applied to the coordinates of `A y` in the chart at `x`. -/
lemma mvfderiv_eq_fderivWithin_target {F : Type*} [NormedAddCommGroup F] [NormedSpace ℝ F]
    {x y : M} (hy : y ∈ (extChartAt I x).source) {f : M → F}
    (hf : MDifferentiableAt I 𝓘(ℝ,F) f y) (A : Π y : M, TangentSpace I y) :
    mvfderiv I f y (A y) =
      fderivWithin ℝ (f ∘ (extChartAt I x).symm) (extChartAt I x).target ((extChartAt I x) y)
        (VectorField.mpullbackWithin 𝓘(ℝ,E) I (extChartAt I x).symm A (Set.range I)
          ((extChartAt I x) y)) := by
  have hys : y ∈ (chartAt H x).source := by simpa only [extChartAt_source] using hy
  have hleft : (extChartAt I x).symm ((extChartAt I x) y) = y := (extChartAt I x).left_inv hy
  have hsy : (extChartAt I x).source ∈ 𝓝 y := (isOpen_extChartAt_source (I := I) x).mem_nhds hy
  have huniq : UniqueMDiffAt[(extChartAt I x).source] y := by
    have h := UniqueMDiffWithinAt.inter (s := (univ : Set M)) (t := (extChartAt I x).source)
      (uniqueMDiffWithinAt_univ (I := I)) hsy
    rwa [univ_inter] at h
  have hstep1 : mvfderiv I f y = mvfderivWithin I f (extChartAt I x).source y := by
    rw [← mvfderivWithin_univ (f := f)]
    rw [← mvfderivWithin_inter (f := f) (s := (univ : Set M)) (t := (extChartAt I x).source)
      (x := y) hsy, univ_inter]
  rw [hstep1]
  have hev : ((f ∘ (extChartAt I x).symm) ∘ (extChartAt I x))
      =ᶠ[𝓝[(extChartAt I x).source] y] f := by
    filter_upwards [self_mem_nhdsWithin] with z hz
    show f ((extChartAt I x).symm ((extChartAt I x) z)) = f z
    rw [(extChartAt I x).left_inv hz]
  rw [← mvfderivWithin_congr_eventually_of_mem (s := (extChartAt I x).source) (x := y) (g := f)
    (g₁ := (f ∘ (extChartAt I x).symm) ∘ (extChartAt I x)) hev hy]
  have hg : MDiffAt[(extChartAt I x).target] (f ∘ (extChartAt I x).symm) ((extChartAt I x) y) := by
    have h2 : MDiffAt[(extChartAt I x).target] (extChartAt I x).symm ((extChartAt I x) y) :=
      (mdifferentiableWithinAt_extChartAt_symm (I := I) (x := x)
        ((extChartAt I x).map_source hy)).mono (extChartAt_target_subset_range x)
    have h1 : MDiffAt[(univ : Set M)] f ((extChartAt I x).symm ((extChartAt I x) y)) := by
      rw [hleft]; exact mdifferentiableWithinAt_univ.2 hf
    exact MDifferentiableWithinAt.comp (I := 𝓘(ℝ,E)) (I' := I) (I'' := 𝓘(ℝ,F))
      (M := E) (M' := M) (M'' := F) (f := (extChartAt I x).symm) (g := f)
      (s := (extChartAt I x).target) (u := (univ : Set M)) ((extChartAt I x) y) h1 h2
      (fun z _ => trivial)
  have hmap : (extChartAt I x).source ⊆ (extChartAt I x) ⁻¹' (extChartAt I x).target :=
    fun z hz => (extChartAt I x).map_source hz
  have hcomp : mvfderivWithin I ((f ∘ (extChartAt I x).symm) ∘ (extChartAt I x))
        (extChartAt I x).source y (A y)
      = (mvfderivWithin 𝓘(ℝ,E) (f ∘ (extChartAt I x).symm) (extChartAt I x).target
          ((extChartAt I x) y)) ((mfderiv[(extChartAt I x).source] (extChartAt I x) y) (A y)) :=
    mvfderivWithin_comp_apply_vec (f := (extChartAt I x)) (g := f ∘ (extChartAt I x).symm)
      (s := (extChartAt I x).source) (u := (extChartAt I x).target) (x := y) hg
      (mdifferentiableAt_extChartAt hys).mdifferentiableWithinAt hmap huniq (A y)
  rw [hcomp]
  have hL : (mfderiv[(extChartAt I x).source] (extChartAt I x) y) (A y)
      = (mfderiv[Set.range I] (extChartAt I x).symm ((extChartAt I x) y)).inverse (A y) := by
    rw [mfderivWithin_extChartAt_eq_inverse (I := I) (x := x) hy
      (s' := (extChartAt I x).source) huniq]
    rfl
  have hV : VectorField.mpullbackWithin 𝓘(ℝ,E) I (extChartAt I x).symm A (Set.range I)
        ((extChartAt I x) y)
      = (mfderiv[Set.range I] (extChartAt I x).symm ((extChartAt I x) y)).inverse
          (A ((extChartAt I x).symm ((extChartAt I x) y))) :=
    mpullbackWithin_apply
  rw [hL, hV, hleft]
  exact congrArg (fun (L : TangentSpace 𝓘(ℝ,E) ((extChartAt I x) y) →L[ℝ] F) => L
      ((mfderiv[Set.range I] (extChartAt I x).symm ((extChartAt I x) y)).inverse (A y)))
    (mvfderivWithin_model_eq_fderivWithin (t := (extChartAt I x).target)
      (g := f ∘ (extChartAt I x).symm) (p := (extChartAt I x) y) hg)

/-- The target of the extended chart at `x` is unique-differentiable. -/
lemma uniqueDiffOn_extChartAt_target (x : M) : UniqueDiffOn ℝ (extChartAt I x).target := by
  have h := ModelWithCorners.uniqueDiffOn_preimage I (H := H) (chartAt H x).open_target
  rwa [← OpenPartialHomeomorph.extend_target (chartAt H x) (I := I)] at h

/-- The pullback of a smooth field along the inverse of the extended chart is `C^k` within the
chart target. -/
lemma contDiffWithinAt_mpullbackWithin_field {A : Π y : M, TangentSpace I y}
    (hA : CMDiff ∞ (T% A)) (k : ℕ) (x : M) :
    ContDiffWithinAt ℝ (k : ℕ∞ω)
      (fun ξ : E => VectorField.mpullbackWithin 𝓘(ℝ,E) I (extChartAt I x).symm A (Set.range I) ξ)
      (extChartAt I x).target ((extChartAt I x) x) := by
  have hle : (k : ℕ∞ω) ≤ ∞ := by exact_mod_cast le_top
  have h : ContMDiffWithinAt 𝓘(ℝ, E) 𝓘(ℝ, E).tangent (k : ℕ∞ω)
      (fun ξ : E => (⟨ξ, VectorField.mpullbackWithin 𝓘(ℝ,E) I (extChartAt I x).symm A
        (Set.range I) ξ⟩ : TangentBundle 𝓘(ℝ,E) E))
      (extChartAt I x).target ((extChartAt I x) x) := by
    simpa only [preimage_univ, inter_univ] using
      (VectorField.contMDiffWithinAt_mpullbackWithin_extChartAt_symm
        (I := I) (M := M) (s := Set.univ) (x := x) (V := A) (m := (k : ℕ∞ω)) (n := ∞)
        ((hA x).of_le hle) (fun _ _ => uniqueMDiffWithinAt_univ (I := I)) (mem_univ x)
        (by simpa using Nat.cast_le.mpr (Nat.le_succ k)))
  exact (contMDiffWithinAt_vectorSpace_iff_contDiffWithinAt (𝕜 := ℝ) (E := E) (n := (k : ℕ∞ω))
    (V := fun ξ : E => VectorField.mpullbackWithin 𝓘(ℝ,E) I (extChartAt I x).symm A (Set.range I) ξ)
    (s := (extChartAt I x).target) (x := (extChartAt I x) x)).1 (by simpa using h)

/-- The inverse of the extended chart of the product manifold `ℝ × M`, as a total function. -/
lemma extChartAt_prod_symm (t₀ : ℝ) (x : M) :
    (extChartAt (𝓘(ℝ,ℝ).prod I) (t₀,x)).symm
      = (fun p : ℝ × E => (p.1, (extChartAt I x).symm p.2)) := by
  funext p
  rw [extChartAt_prod, PartialEquiv.prod_symm, extChartAt_model_space_eq_id,
    PartialEquiv.refl_symm, PartialEquiv.prod_coe]
  rfl

/-- The extended chart of the product manifold `ℝ × M`, evaluated at `(t₀, x)`. -/
lemma extChartAt_prod_apply (t₀ : ℝ) (x : M) :
    (extChartAt (𝓘(ℝ,ℝ).prod I) (t₀,x)) (t₀,x) = (t₀, (extChartAt I x) x) := by
  rw [extChartAt_prod, extChartAt_model_space_eq_id]
  rfl

/-- The range of the product model with corners (of the source of the joint family). -/
lemma range_prod_modelWithCorners :
    Set.range (𝓘(ℝ,ℝ).prod I) = (univ : Set ℝ) ×ˢ Set.range I := by
  rw [ModelWithCorners.range_prod, ModelWithCorners.Boundaryless.range_eq_univ]

/-- **The jointly smooth family in the chart at `x`.**  If `Φ` is jointly `C^∞` at `(t₀, x)` then
the chart-written family `(t, ξ) ↦ Φ (t, (extChartAt I x).symm ξ)` is `C^k` within
`univ ×ˢ (extChartAt I x).target` at `(t₀, (extChartAt I x) x)`. -/
lemma contDiffWithinAt_chart_family {F : Type*} [NormedAddCommGroup F] [NormedSpace ℝ F]
    {Φ : ℝ × M → F} {t₀ : ℝ} {x : M} (k : ℕ) (hΦ : JointSmoothAt I M Φ t₀ x) :
    ContDiffWithinAt ℝ (k : ℕ∞ω) (fun p : ℝ × E => Φ (p.1, (extChartAt I x).symm p.2))
      (univ ×ˢ (extChartAt I x).target) (t₀, (extChartAt I x) x) := by
  have hle : (k : ℕ∞ω) ≤ ∞ := by exact_mod_cast le_top
  have h1 : ContMDiffWithinAt 𝓘(ℝ, ℝ × E) 𝓘(ℝ,F) (k : ℕ∞ω)
      (Φ ∘ (extChartAt (𝓘(ℝ,ℝ).prod I) (t₀,x)).symm) (Set.range (𝓘(ℝ,ℝ).prod I))
      ((extChartAt (𝓘(ℝ,ℝ).prod I) (t₀,x)) (t₀,x)) :=
    (contMDiffAt_iff_source).1 (hΦ.of_le hle)
  have h2 := (contMDiffWithinAt_iff_contDiffWithinAt).1 h1
  rw [extChartAt_prod_symm t₀ x, extChartAt_prod_apply t₀ x, range_prod_modelWithCorners] at h2
  exact h2.mono (Set.prod_mono_right (extChartAt_target_subset_range x))


/-- **The spatial derivative of a jointly smooth family, along a fixed smooth field, is jointly
smooth.**  If `Φ : ℝ × M → F` is jointly `C^∞` near `(t₀, x)` and `A` is a smooth vector field,
then `(t, y) ↦ d_y Φ(t, ·)(A y)` is jointly `C^∞` near `(t₀, x)`. -/
theorem contMDiffAt_mvfderiv_along_field
    {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E] [CompleteSpace E]
    {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
    {M : Type*} [TopologicalSpace M] [ChartedSpace H M] [IsManifold I (⊤ : ℕ∞) M]
    {F : Type*} [NormedAddCommGroup F] [NormedSpace ℝ F]
    {Φ : ℝ × M → F} {A : Π y : M, TangentSpace I y} {t₀ : ℝ} {x : M}
    (hΦ : JointSmoothAt I M Φ t₀ x) (hA : SmoothField I M A) :
    JointSmoothAt I M (fun p : ℝ × M => mvfderiv I (fun y : M => Φ (p.1, y)) p.2 (A p.2)) t₀ x := by
  set G : ℝ × M → F := fun p : ℝ × M => mvfderiv I (fun y : M => Φ (p.1, y)) p.2 (A p.2)
    with hGdef
  set V : E → E := fun ξ : E =>
    VectorField.mpullbackWithin 𝓘(ℝ,E) I (extChartAt I x).symm A (Set.range I) ξ with hVdef
  set Hfun : ℝ × E → F := fun p : ℝ × E =>
    fderivWithin ℝ (fun ξ' : E => Φ (p.1, (extChartAt I x).symm ξ')) (extChartAt I x).target
      p.2 (V p.2) with hHdef
  change ContMDiffAt (𝓘(ℝ,ℝ).prod I) 𝓘(ℝ,F) ∞ G (t₀, x)
  rw [contMDiffAt_infty]
  intro n
  -- ### smoothness of the model-space representative
  have hu : ContDiffWithinAt ℝ ((n + 1 : ℕ) : ℕ∞ω)
      (fun p : ℝ × E => Φ (p.1, (extChartAt I x).symm p.2))
      (univ ×ˢ (extChartAt I x).target) (t₀, (extChartAt I x) x) :=
    contDiffWithinAt_chart_family (n + 1) hΦ
  have hVsm : ContDiffWithinAt ℝ (n : ℕ∞ω) V (extChartAt I x).target ((extChartAt I x) x) :=
    contDiffWithinAt_mpullbackWithin_field hA n x
  have hHsm : ContDiffWithinAt ℝ (n : ℕ∞ω) Hfun (univ ×ˢ (extChartAt I x).target)
      (t₀, (extChartAt I x) x) := by
    have hf : ContDiffWithinAt ℝ ((n + 1 : ℕ) : ℕ∞ω)
        (Function.uncurry (fun p : ℝ × E => fun ξ' : E => Φ (p.1, (extChartAt I x).symm ξ')))
        (((univ : Set ℝ) ×ˢ (extChartAt I x).target) ×ˢ (extChartAt I x).target)
        (((t₀, (extChartAt I x) x)), (extChartAt I x) x) := by
      have hmap : ContDiffWithinAt ℝ ((n + 1 : ℕ) : ℕ∞ω)
          (fun q : (ℝ × E) × E => (q.1.1, q.2))
          (((univ : Set ℝ) ×ˢ (extChartAt I x).target) ×ˢ (extChartAt I x).target)
          (((t₀, (extChartAt I x) x)), (extChartAt I x) x) :=
        (((ContinuousLinearMap.fst ℝ ℝ E).comp
            (ContinuousLinearMap.fst ℝ (ℝ × E) E)).prod
          (ContinuousLinearMap.snd ℝ (ℝ × E) E)).contDiff.contDiffWithinAt
      refine ContDiffWithinAt.comp (x := (((t₀, (extChartAt I x) x)), (extChartAt I x) x))
        (g := fun p : ℝ × E => Φ (p.1, (extChartAt I x).symm p.2))
        (f := fun q : (ℝ × E) × E => (q.1.1, q.2))
        (s := ((univ : Set ℝ) ×ˢ (extChartAt I x).target) ×ˢ (extChartAt I x).target)
        (t := (univ : Set ℝ) ×ˢ (extChartAt I x).target)
        ?_ hmap (fun q hq => ⟨trivial, hq.2⟩)
      exact hu
    have hg : ContDiffWithinAt ℝ (n : ℕ∞ω) (fun p : ℝ × E => p.2)
        ((univ : Set ℝ) ×ˢ (extChartAt I x).target) (t₀, (extChartAt I x) x) :=
      (ContinuousLinearMap.snd ℝ ℝ E).contDiff.contDiffWithinAt
    have hk : ContDiffWithinAt ℝ (n : ℕ∞ω) (fun p : ℝ × E => V p.2)
        ((univ : Set ℝ) ×ˢ (extChartAt I x).target) (t₀, (extChartAt I x) x) := by
      refine ContDiffWithinAt.comp (x := (t₀, (extChartAt I x) x)) (g := V)
        (f := fun p : ℝ × E => p.2) (s := (univ : Set ℝ) ×ˢ (extChartAt I x).target)
        (t := (extChartAt I x).target) ?_ hg (fun z hz => hz.2)
      exact hVsm
    exact ContDiffWithinAt.fderivWithin_apply
      (f := fun p : ℝ × E => fun ξ' : E => Φ (p.1, (extChartAt I x).symm ξ'))
      (g := fun p : ℝ × E => p.2) (k := fun p : ℝ × E => V p.2)
      (t := (extChartAt I x).target) (s := (univ : Set ℝ) ×ˢ (extChartAt I x).target)
      (x₀ := (t₀, (extChartAt I x) x)) (ht := uniqueDiffOn_extChartAt_target x)
      (hmn := by norm_num) (hx₀ := ⟨mem_univ _, mem_extChartAt_target x⟩)
      (hst := fun z hz => hz.2) hf hg hk
  -- ### the slices are differentiable near `(t₀, x)`
  have hsliceEv : ∀ᶠ q : ℝ × M in 𝓝 (t₀, x),
      MDifferentiableAt I 𝓘(ℝ,F) (fun z : M => Φ (q.1, z)) q.2 := by
    have h1 : ∀ᶠ q : ℝ × M in 𝓝 (t₀, x),
        ContMDiffAt (𝓘(ℝ,ℝ).prod I) 𝓘(ℝ,F) (1 : ℕ∞ω) Φ q :=
      (contMDiffAt_iff_contMDiffAt_nhds (by norm_num)).1
        (hΦ.of_le (by exact_mod_cast le_top))
    filter_upwards [h1] with q hq
    exact (hq.comp q.2 ((contMDiffAt_const (c := q.1)).prodMk contMDiffAt_id)).mdifferentiableAt
      (by norm_num)
  have hslice0 : MDifferentiableAt I 𝓘(ℝ,F) (fun z : M => Φ (t₀, z)) x :=
    ((hΦ.of_le (by exact_mod_cast le_top : (1 : ℕ∞ω) ≤ ∞)).comp x
      ((contMDiffAt_const (c := t₀)).prodMk contMDiffAt_id)).mdifferentiableAt (by norm_num)
  -- ### the set on which the chart formula can be applied
  set W : Set (ℝ × M) := {q : ℝ × M | MDifferentiableAt I 𝓘(ℝ,F) (fun z : M => Φ (q.1, z)) q.2}
      ∩ (univ ×ˢ (extChartAt I x).source) with hWdef
  have hWmem : W ∈ 𝓝 (t₀, x) := by
    have hs : (univ ×ˢ (extChartAt I x).source) ∈ 𝓝 (t₀, x) :=
      prod_mem_nhds univ_mem
        ((isOpen_extChartAt_source (I := I) x).mem_nhds (mem_extChartAt_source x))
    show ∀ᶠ q : ℝ × M in 𝓝 (t₀, x), q ∈ W
    filter_upwards [hsliceEv, hs] with q h1 h2
    exact ⟨h1, h2⟩
  have hcont1 : ContinuousAt (fun p : ℝ × E => (extChartAt I x).symm p.2)
      (t₀, (extChartAt I x) x) :=
    ContinuousAt.comp (f := fun p : ℝ × E => p.2) (g := (extChartAt I x).symm)
      (x := (t₀, (extChartAt I x) x)) (continuousAt_extChartAt_symm (I := I) x)
      continuousAt_snd
  have hcont : ContinuousAt (fun p : ℝ × E => (p.1, (extChartAt I x).symm p.2))
      (t₀, (extChartAt I x) x) :=
    continuousAt_fst.prodMk hcont1
  -- ### the chart formula identifies `G` with the model representative
  have hEq : (fun p : ℝ × E => G (p.1, (extChartAt I x).symm p.2))
      =ᶠ[𝓝[univ ×ˢ (extChartAt I x).target] (t₀, (extChartAt I x) x)] Hfun := by
    have hWmem' : W ∈ 𝓝 (t₀, (extChartAt I x).symm ((extChartAt I x) x)) := by
      rwa [(extChartAt I x).left_inv (mem_extChartAt_source x)]
    have hpre : (fun p : ℝ × E => (p.1, (extChartAt I x).symm p.2)) ⁻¹' W
        ∈ 𝓝 (t₀, (extChartAt I x) x) :=
      hcont.preimage_mem_nhds (by simpa using hWmem')
    filter_upwards [(nhdsWithin_le_nhds (s := (univ : Set ℝ) ×ˢ (extChartAt I x).target)
      (a := (t₀, (extChartAt I x) x))) hpre, self_mem_nhdsWithin] with p hpW hpT
    have hpd := hpW.1
    have hpsrc : (extChartAt I x).symm p.2 ∈ (extChartAt I x).source := hpW.2.2
    change MDifferentiableAt I 𝓘(ℝ,F) (fun z : M => Φ (p.1, z)) ((extChartAt I x).symm p.2)
      at hpd
    have hright : (extChartAt I x) ((extChartAt I x).symm p.2) = p.2 :=
      (extChartAt I x).right_inv hpT.2
    have hA' := mvfderiv_eq_fderivWithin_target (I := I) (x := x) hpsrc hpd A
    simp only [Function.comp_def] at hA'
    rw [hright] at hA'
    simpa only [hGdef, hHdef, hVdef] using hA'
  have hEq0 : (fun p : ℝ × E => G (p.1, (extChartAt I x).symm p.2))
      (t₀, (extChartAt I x) x) = Hfun (t₀, (extChartAt I x) x) := by
    have hleft : (extChartAt I x).symm ((extChartAt I x) x) = x :=
      (extChartAt I x).left_inv (mem_extChartAt_source x)
    have hA' := mvfderiv_eq_fderivWithin_target (I := I) (x := x)
      (mem_extChartAt_source x) hslice0 A
    simpa only [Function.comp_def, hGdef, hHdef, hVdef, hleft] using hA'
  -- ### conclusion: transfer along the chart
  have hHcmd : ContMDiffWithinAt 𝓘(ℝ, ℝ × E) 𝓘(ℝ,F) (n : ℕ∞ω) Hfun
      (univ ×ˢ (extChartAt I x).target) (t₀, (extChartAt I x) x) :=
    hHsm.contMDiffWithinAt
  have hGcmd : ContMDiffWithinAt 𝓘(ℝ, ℝ × E) 𝓘(ℝ,F) (n : ℕ∞ω)
      (fun p : ℝ × E => G (p.1, (extChartAt I x).symm p.2))
      (univ ×ˢ (extChartAt I x).target) (t₀, (extChartAt I x) x) :=
    hHcmd.congr_of_eventuallyEq hEq hEq0
  have hTev : (univ ×ˢ (extChartAt I x).target)
      =ᶠ[𝓝 (t₀, (extChartAt I x) x)] (univ ×ˢ Set.range I) := by
    obtain ⟨u, hu, huT⟩ := (mem_nhdsWithin_iff_exists_mem_nhds_inter).1
      (extChartAt_target_mem_nhdsWithin (I := I) x)
    filter_upwards [prod_mem_nhds univ_mem hu] with p hp
    exact propext ⟨fun h => ⟨h.1, extChartAt_target_subset_range x h.2⟩,
      fun h => ⟨h.1, huT ⟨hp.2, h.2⟩⟩⟩
  have hGbig : ContMDiffWithinAt 𝓘(ℝ, ℝ × E) 𝓘(ℝ,F) (n : ℕ∞ω)
      (fun p : ℝ × E => G (p.1, (extChartAt I x).symm p.2)) (univ ×ˢ Set.range I)
      (t₀, (extChartAt I x) x) :=
    (contMDiffWithinAt_congr_set hTev).1 hGcmd
  refine (contMDiffAt_iff_source (I := (𝓘(ℝ,ℝ)).prod I) (I' := 𝓘(ℝ,F))
    (x := (t₀, x))).2 ?_
  rw [show (G ∘ (extChartAt (𝓘(ℝ,ℝ).prod I) (t₀,x)).symm)
        = (fun p : ℝ × E => G (p.1, (extChartAt I x).symm p.2)) from by
      rw [extChartAt_prod_symm t₀ x]; rfl,
    extChartAt_prod_apply t₀ x, range_prod_modelWithCorners]
  exact hGbig

end

end Work.Diff.EXT
