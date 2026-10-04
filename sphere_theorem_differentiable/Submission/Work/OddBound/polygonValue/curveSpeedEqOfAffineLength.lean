import Mathlib
import Submission.Work.OddBound.LiftKit
import Submission.Work.OddBound.longHomotopy.curveLength_toolkit

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false

namespace Work.OddBound.polygonValue

open scoped Manifold ContDiff Bundle Topology ENNReal
open Bundle ContDiff Set VectorField CovariantDerivative Metric Filter
open MeasureTheory
open scoped MeasureTheory Interval

set_option linter.unusedSectionVars false

/-- **The Riemannian speed of a curve that is `C¹` on `[0,1]` is continuous at every interior
point.**  The hypothesis bounds `h` only on the closed interval, so the *unrestricted* derivative
`mfderiv` used in `curveSpeed` may be junk at the two endpoints; at an interior point `x`, however,
`curveSpeed h` agrees with the continuous "within-interval" speed built from `mfderivWithin` on
`Icc 0 1` (compare `Work.OddBound.longHomotopy.curveLength_toolkit`). -/
lemma continuousAt_curveSpeed_of_contMDiffOn_one
    {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E] [CompleteSpace E]
    {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
    {M : Type*} [TopologicalSpace M] [T2Space M] [ChartedSpace H M] [IsManifold I ∞ M]
    [RiemannianBundle (fun x : M ↦ TangentSpace I x)]
    [IsContMDiffRiemannianBundle I ∞ E (fun x : M ↦ TangentSpace I x)]
    [I.Boundaryless] [Nontrivial E]
    {h : ℝ → M} (hc : ContMDiffOn 𝓘(ℝ) I 1 h (Set.Icc (0 : ℝ) 1)) {r : ℝ}
    (hr : r ∈ Set.Ioo (0 : ℝ) 1) :
    ContinuousAt (fun t : ℝ => Submission.Length.curveSpeed (I := I) h t) r := by
  haveI : IsContinuousRiemannianBundle E (fun x : M ↦ TangentSpace I x) := by
    obtain ⟨Φ, hΦsm, hΦ⟩ :=
      (inferInstance : IsContMDiffRiemannianBundle I ∞ E
        (fun x : M ↦ TangentSpace I x)).exists_contMDiff
    exact ⟨Φ, hΦsm.continuous, hΦ⟩
  set s : Set ℝ := Set.Icc (0 : ℝ) 1
  have hs_umd : UniqueMDiff[s] :=
    UniqueDiffOn.uniqueMDiffOn (uniqueDiffOn_Icc (by norm_num : (0 : ℝ) < 1))
  -- The tangent map of `h` within `[0,1]` is continuous.
  have htan : ContinuousOn (tangentMapWithin 𝓘(ℝ) I h s) (Bundle.TotalSpace.proj ⁻¹' s) :=
    hc.continuousOn_tangentMapWithin le_rfl hs_umd
  -- The constant unit section of the tangent bundle of the model space `ℝ`.
  have hκ : ContinuousOn (fun t : ℝ => (Bundle.TotalSpace.mk' ℝ t (1 : TangentSpace 𝓘(ℝ) t) :
      TangentBundle 𝓘(ℝ) ℝ)) s :=
    ((contMDiff_vectorSpace_iff_contDiff (𝕜 := ℝ) (n := ∞) (E := ℝ)
      (V := fun t : ℝ => (1 : TangentSpace 𝓘(ℝ) t))).mpr contDiff_const).continuous.continuousOn
  have hcomp : ContinuousOn (fun t : ℝ =>
      (⟨h t, (mfderivWithin 𝓘(ℝ) I h s t) (1 : ℝ)⟩ : TangentBundle I M)) s :=
    htan.comp hκ (fun t ht => by simpa using ht)
  -- The "within-interval" speed.
  set g : ℝ → ℝ := fun t => Real.sqrt
    (inner ℝ ((mfderivWithin 𝓘(ℝ) I h s t) (1 : ℝ))
      ((mfderivWithin 𝓘(ℝ) I h s t) (1 : ℝ)))
  have hgcont : ContinuousOn g s := (ContinuousOn.inner_bundle (b := h) hcomp hcomp).sqrt
  have hgAt : ContinuousAt g r := hgcont.continuousAt (Icc_mem_nhds hr.1 hr.2)
  -- It agrees with `curveSpeed` on the interior of `[0,1]`.
  refine hgAt.congr ?_
  filter_upwards [Ioo_mem_nhds hr.1 hr.2] with t ht
  show g t = Submission.Length.curveSpeed (I := I) h t
  have hmem : s ∈ 𝓝 t := Icc_mem_nhds ht.1 ht.2
  show Real.sqrt (inner ℝ ((mfderivWithin 𝓘(ℝ) I h s t) (1 : ℝ))
    ((mfderivWithin 𝓘(ℝ) I h s t) (1 : ℝ))) = Submission.Length.curveSpeed (I := I) h t
  rw [mfderivWithin_of_mem_nhds hmem, Submission.Length.curveSpeed_def,
    Submission.Geodesic.curveVelocity_apply]

/-- **A `C¹` curve on `[0,1]` whose length is affine in the interval has constant speed.**
If `curveLength h a b = (b - a) * L` for all `0 ≤ a ≤ b ≤ 1`, then the Riemannian speed of `h` at
every *interior* point `r ∈ (0,1)` is `L`.

Proof plan: fix `r ∈ (0,1)`. The curve `h` is `C¹` near `r`, so `curveSpeed h` is continuous at `r`
(compare `Work.OddBound.polygon.continuous_curveSpeed`, or use the `mfderivWithin` trick of
`curveLength_toolkit`), hence `F(x) := ∫_r^x curveSpeed h` has derivative `curveSpeed h r` at `r`
(`intervalIntegral.integral_hasDerivAt_right`). On the other hand, for `x ∈ [0,1]`, `F x` equals
`curveLength h r x` (definition) which by hypothesis is `(x - r) * L` for `r ≤ x ≤ 1` and also for
`0 ≤ x ≤ r` (by `curveLength_neg`). So `F` agrees with the affine function `x ↦ (x - r) * L` near
`r`, hence has derivative `L` there; uniqueness of the derivative gives `curveSpeed h r = L`. -/
theorem curveSpeedEqOfAffineLength
    {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E] [CompleteSpace E]
    {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
    {M : Type*} [TopologicalSpace M] [T2Space M] [ChartedSpace H M] [IsManifold I ∞ M]
    [RiemannianBundle (fun x : M ↦ TangentSpace I x)]
    [IsContMDiffRiemannianBundle I ∞ E (fun x : M ↦ TangentSpace I x)]
    [I.Boundaryless] [Nontrivial E] [CompactSpace M] [PathConnectedSpace M] [RegularSpace M]
    {h : ℝ → M} (hc : ContMDiffOn 𝓘(ℝ) I 1 h (Set.Icc (0:ℝ) 1)) {L : ℝ}
    (hlen : ∀ a b : ℝ, 0 ≤ a → a ≤ b → b ≤ 1 →
      Submission.Length.curveLength (I := I) h a b = (b - a) * L) :
    ∀ r : ℝ, 0 < r → r < 1 → Submission.Length.curveSpeed (I := I) h r = L := by
  intro r hr0 hr1
  have hr : r ∈ Set.Ioo (0 : ℝ) 1 := ⟨hr0, hr1⟩
  -- The length toolkit: integrability of the speed on `[0,r]`.
  have hint : IntervalIntegrable (fun t : ℝ => Submission.Length.curveSpeed (I := I) h t)
      MeasureTheory.volume 0 r :=
    (Work.OddBound.longHomotopy.curveLength_toolkit (I := I) (h := h) (S := 1) hc).1
      0 r le_rfl hr0.le hr1.le
  -- The speed is continuous (and hence measurable) at `r` and near it.
  have hcontOn : ∀ x ∈ Set.Ioo (0 : ℝ) 1,
      ContinuousAt (fun t : ℝ => Submission.Length.curveSpeed (I := I) h t) x :=
    fun x hx => continuousAt_curveSpeed_of_contMDiffOn_one (I := I) hc hx
  have hmeas : StronglyMeasurableAtFilter
      (fun t : ℝ => Submission.Length.curveSpeed (I := I) h t) (𝓝 r) MeasureTheory.volume :=
    ContinuousAt.stronglyMeasurableAtFilter isOpen_Ioo hcontOn r hr
  -- The fundamental theorem of calculus at `r`.
  have hFTC : HasDerivAt
      (fun u : ℝ => ∫ x in (0 : ℝ)..u, Submission.Length.curveSpeed (I := I) h x)
      (Submission.Length.curveSpeed (I := I) h r) r :=
    intervalIntegral.integral_hasDerivAt_right hint hmeas (hcontOn r hr)
  -- Near `r`, that function is the affine function `u ↦ u * L`.
  have hEq : (fun u : ℝ => ∫ x in (0 : ℝ)..u, Submission.Length.curveSpeed (I := I) h x)
      =ᶠ[𝓝 r] (fun u : ℝ => u * L) := by
    filter_upwards [Ioo_mem_nhds hr0 hr1] with u hu
    have h1 : (∫ x in (0 : ℝ)..u, Submission.Length.curveSpeed (I := I) h x)
        = Submission.Length.curveLength (I := I) h 0 u := rfl
    rw [h1, hlen 0 u le_rfl hu.1.le hu.2.le]
    ring
  have hA : HasDerivAt (fun u : ℝ => u * L) L r := by
    simpa using (hasDerivAt_id r).mul_const L
  have hFTC' : HasDerivAt
      (fun u : ℝ => ∫ x in (0 : ℝ)..u, Submission.Length.curveSpeed (I := I) h x) L r :=
    hEq.hasDerivAt_iff.mpr hA
  exact hFTC.unique hFTC'

end Work.OddBound.polygonValue
