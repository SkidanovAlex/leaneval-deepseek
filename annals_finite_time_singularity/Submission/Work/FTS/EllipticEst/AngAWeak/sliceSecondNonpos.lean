/-
Copyright: work module for the Elgindi finite-time singularity project.

# The 1-D slice dichotomy `∫ sin(2θ)^{-η} · f · f'' ≤ 0`

For `η = Work.Spaces.eta = 99/100` and `σ θ = sin(2θ)^{-η}`, every `f` of class `C²` on
`(0, π/2)` vanishing at both endpoints with `σ · f · f''` integrable satisfies

  `∫_0^{π/2} σ θ · f θ · f'' θ  ≤  0`.

The proof splits the interval at `π/4`.  The left half

  `Phi f θ₀ - ∫_0^{θ₀} σ f f'' ≥ 0`

is `Work.FTS.EllipticEst.Cores.AeStep2Aux.slice_left_integral_nonneg` (whose engine is the
endpoint dichotomy `slice_left_bad_case`).  The right half

  `Phi f θ₀ + ∫_{θ₀}^{π/2} σ f f'' ≤ 0`

is proved here (`slice_right_integral_nonpos_fts`): it is the left half applied to the
*reflection* `θ ↦ f (π/2 - θ)`, using that `σ` is reflection invariant and that `Phi` changes
sign under the reflection (`Work.FTS.EllipticEst.AngAWeak.SliceSecondReflect`), together with
the mirror change of variables for the integral.

Since `∫_0^{π/2} = ∫_0^{θ₀} + ∫_{θ₀}^{π/2}` (the point `θ₀` is null), adding the two halves
gives `∫_0^{π/2} σ f f'' ≤ 0`.
-/
import Mathlib.Analysis.Calculus.ContDiff.Defs
import Mathlib.MeasureTheory.Integral.IntervalIntegral.Basic
import Submission.Work.Spaces.Defs
import Submission.Work.FTS.EllipticEst.AngSecond.Defs
import Submission.Work.FTS.EllipticEst.Cores.AeStep2Aux.slice_left_integral_nonneg
import Submission.Work.FTS.EllipticEst.AngAWeak.SliceSecondReflect
import Submission.Work.FTS.EllipticEst.Dispatch.flux_mirror_symmetry

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

noncomputable section

open scoped Real Topology
open MeasureTheory Set Filter

namespace Work.FTS.EllipticEst.AngAWeak

set_option autoImplicit false
set_option maxHeartbeats 1600000

/-! ## The mirror change of variables -/

/-- **Mirror substitution.**  The reflection `θ ↦ π/2 - θ` maps `(0, π/2 - θ₀)` onto
`(θ₀, π/2)`, so the corresponding set integrals agree. -/
theorem setIntegral_Ioo_mirror (F : ℝ → ℝ) {θ₀ : ℝ} (hθ₀ : θ₀ ∈ Set.Ioo 0 (Real.pi / 2)) :
    (∫ θ in Set.Ioo 0 (Real.pi / 2 - θ₀), F (Real.pi / 2 - θ))
      = ∫ u in Set.Ioo θ₀ (Real.pi / 2), F u := by
  have h0 : (0 : ℝ) ≤ Real.pi / 2 - θ₀ := by linarith [hθ₀.2]
  have h1 : (∫ θ in Set.Ioo 0 (Real.pi / 2 - θ₀), F (Real.pi / 2 - θ))
      = ∫ θ in (0 : ℝ)..(Real.pi / 2 - θ₀), F (Real.pi / 2 - θ) := by
    rw [setIntegral_congr_set (Ioo_ae_eq_Ioc (μ := volume) (a := (0 : ℝ))
      (b := Real.pi / 2 - θ₀))]
    exact (intervalIntegral.integral_of_le h0 (f := fun θ => F (Real.pi / 2 - θ))).symm
  have h2 : (∫ θ in (0 : ℝ)..(Real.pi / 2 - θ₀), F (Real.pi / 2 - θ))
      = ∫ u in (Real.pi / 2 - (Real.pi / 2 - θ₀))..(Real.pi / 2 - 0), F u :=
    intervalIntegral.integral_comp_sub_left F (Real.pi / 2)
  have h3 : (Real.pi / 2 - (Real.pi / 2 - θ₀)) = θ₀ := by ring
  have h4 : (Real.pi / 2 - 0 : ℝ) = Real.pi / 2 := by ring
  have h5 : (∫ u in θ₀..(Real.pi / 2), F u) = ∫ u in Set.Ioo θ₀ (Real.pi / 2), F u := by
    rw [intervalIntegral.integral_of_le (le_of_lt hθ₀.2) (f := F)]
    exact (setIntegral_congr_set (Ioo_ae_eq_Ioc (μ := volume) (a := θ₀)
      (b := Real.pi / 2))).symm
  rw [h1, h2, h3, h4, h5]

/-- The interval `(0, π/2)` splits at an interior point. -/
theorem Ioo_split_setIntegral {θ₀ : ℝ} (hθ₀ : θ₀ ∈ Set.Ioo 0 (Real.pi / 2))
    {F : ℝ → ℝ} (hF : IntegrableOn F (Set.Ioo 0 (Real.pi / 2))) :
    (∫ θ in Set.Ioo 0 (Real.pi / 2), F θ)
      = (∫ θ in Set.Ioo 0 θ₀, F θ) + ∫ θ in Set.Ioo θ₀ (Real.pi / 2), F θ := by
  have hA : IntegrableOn F (Ioc (0 : ℝ) θ₀) :=
    hF.mono_set (fun x hx => ⟨hx.1, lt_of_le_of_lt hx.2 hθ₀.2⟩)
  have hB : IntegrableOn F (Ioc θ₀ (Real.pi / 2)) := by
    have hB0 : IntegrableOn F (Ioo θ₀ (Real.pi / 2)) :=
      hF.mono_set (fun x hx => ⟨lt_trans hθ₀.1 hx.1, hx.2⟩)
    rw [IntegrableOn, ← Measure.restrict_congr_set
      (Ioo_ae_eq_Ioc (μ := volume) (a := θ₀) (b := Real.pi / 2))]
    exact hB0
  have hIooIoc : ∀ a : ℝ, (∫ θ in Ioo 0 a, F θ) = ∫ θ in Ioc 0 a, F θ :=
    fun a => setIntegral_congr_set (Ioo_ae_eq_Ioc (μ := volume) (a := (0 : ℝ)) (b := a))
  rw [hIooIoc (Real.pi / 2), hIooIoc θ₀,
    setIntegral_congr_set (Ioo_ae_eq_Ioc (μ := volume) (a := θ₀) (b := Real.pi / 2))]
  have hunion : Ioc (0 : ℝ) (Real.pi / 2) = Ioc 0 θ₀ ∪ Ioc θ₀ (Real.pi / 2) := by
    ext x
    constructor
    · intro hx
      by_cases h : x ≤ θ₀
      · exact Or.inl ⟨hx.1, h⟩
      · exact Or.inr ⟨lt_of_not_ge h, hx.2⟩
    · intro hx
      rcases hx with ⟨h1, h2⟩ | ⟨h1, h2⟩
      · exact ⟨h1, le_trans h2 (le_of_lt hθ₀.2)⟩
      · exact ⟨lt_trans hθ₀.1 h1, h2⟩
  rw [hunion, setIntegral_union (disjoint_left.mpr (fun x hx1 hx2 =>
      absurd hx2.1 (not_lt.mpr hx1.2))) measurableSet_Ioc hA hB]

/-! ## The right half, by reflection -/

/-- **Right half of the slice dichotomy.**  `Phi f θ₀ + ∫_{θ₀}^{π/2} σ f f'' ≤ 0`. -/
theorem slice_right_integral_nonpos_fts {f : ℝ → ℝ}
    (hf : ContDiffOn ℝ 2 f (Set.Ioo 0 (Real.pi / 2)))
    (hπ : Filter.Tendsto f (nhdsWithin (Real.pi / 2) (Set.Iio (Real.pi / 2))) (nhds 0))
    (hint : MeasureTheory.IntegrableOn
      (Work.FTS.EllipticEst.Cores.AeStep2Aux.sliceIntegrand f) (Set.Ioo 0 (Real.pi / 2)))
    {θ₀ : ℝ} (hθ₀ : θ₀ ∈ Set.Ioo 0 (Real.pi / 2)) :
    Work.FTS.EllipticEst.Cores.AeStep2Aux.Phi f θ₀
      + ∫ θ in Set.Ioo θ₀ (Real.pi / 2),
          Work.FTS.EllipticEst.Cores.AeStep2Aux.sliceIntegrand f θ ≤ 0 := by
  obtain ⟨hcd, hPhi, hSlic⟩ :=
    Work.FTS.EllipticEst.AngAWeak.SliceSecondReflect hf
  -- the mirror of `f`
  set g : ℝ → ℝ := fun θ => f (Real.pi / 2 - θ) with hgdef
  have hgcd : ContDiffOn ℝ 2 g (Set.Ioo 0 (Real.pi / 2)) := hcd
  -- the reflection carries the left filtration at `0` to the right filtration at `π/2`
  have hφ : Tendsto (fun θ : ℝ => Real.pi / 2 - θ) (nhdsWithin 0 (Ioi 0))
      (nhdsWithin (Real.pi / 2) (Iio (Real.pi / 2))) := by
    rw [tendsto_nhdsWithin_iff]
    refine ⟨?_, ?_⟩
    · have hcont : Continuous fun θ : ℝ => Real.pi / 2 - θ := continuous_const.sub continuous_id
      simpa using (hcont.tendsto 0).mono_left (nhdsWithin_le_nhds (s := Ioi 0))
    · filter_upwards [self_mem_nhdsWithin] with θ hθ
      exact sub_lt_self _ (Set.mem_Ioi.mp hθ)
  have hg0 : Tendsto g (nhdsWithin 0 (Ioi 0)) (nhds 0) := by
    simpa only [hgdef, Function.comp_def] using hπ.comp hφ
  -- integrability transfers across the reflection
  have hgint : MeasureTheory.IntegrableOn
      (Work.FTS.EllipticEst.Cores.AeStep2Aux.sliceIntegrand g) (Set.Ioo 0 (Real.pi / 2)) := by
    have h := (Work.FTS.EllipticEst.Dispatch.integrableOn_mirror
      (F := Work.FTS.EllipticEst.Cores.AeStep2Aux.sliceIntegrand f)).mpr hint
    refine h.congr_fun (fun θ hθ => ?_) measurableSet_Ioo
    exact (hSlic θ hθ).symm
  have hθ₀' : Real.pi / 2 - θ₀ ∈ Set.Ioo 0 (Real.pi / 2) :=
    ⟨by linarith [hθ₀.2], by linarith [hθ₀.1]⟩
  -- the left half applied to the reflection
  have hL := Work.FTS.EllipticEst.Cores.AeStep2Aux.slice_left_integral_nonneg
    hgcd hg0 hgint hθ₀'
  -- rewrite the two mirror ingredients
  have hPhi' : Work.FTS.EllipticEst.Cores.AeStep2Aux.Phi g (Real.pi / 2 - θ₀)
      = - Work.FTS.EllipticEst.Cores.AeStep2Aux.Phi f θ₀ := by
    have h := hPhi (Real.pi / 2 - θ₀) hθ₀'
    rw [show Real.pi / 2 - (Real.pi / 2 - θ₀) = θ₀ by ring] at h
    exact h
  have hInt' : (∫ θ in Set.Ioo 0 (Real.pi / 2 - θ₀),
        Work.FTS.EllipticEst.Cores.AeStep2Aux.sliceIntegrand g θ)
      = ∫ u in Set.Ioo θ₀ (Real.pi / 2),
          Work.FTS.EllipticEst.Cores.AeStep2Aux.sliceIntegrand f u := by
    have hcongr : (∫ θ in Set.Ioo 0 (Real.pi / 2 - θ₀),
          Work.FTS.EllipticEst.Cores.AeStep2Aux.sliceIntegrand g θ)
        = ∫ θ in Set.Ioo 0 (Real.pi / 2 - θ₀),
            Work.FTS.EllipticEst.Cores.AeStep2Aux.sliceIntegrand f (Real.pi / 2 - θ) :=
      setIntegral_congr_fun measurableSet_Ioo
        (fun θ hθ => hSlic θ ⟨hθ.1, by linarith [hθ.2, hθ₀.1]⟩)
    rw [hcongr, setIntegral_Ioo_mirror
      (Work.FTS.EllipticEst.Cores.AeStep2Aux.sliceIntegrand f) hθ₀]
  rw [hPhi', hInt'] at hL
  linarith

/-! ## The dichotomy -/

/-- **The 1-D slice dichotomy.**  `∫_0^{π/2} sin(2θ)^{-η} f θ f'' θ ≤ 0`. -/
theorem sliceSecondNonpos {f : ℝ → ℝ}
    (hf : ContDiffOn ℝ 2 f (Set.Ioo 0 (Real.pi / 2)))
    (h0 : Filter.Tendsto f (nhdsWithin (0 : ℝ) (Set.Ioi 0)) (nhds 0))
    (hπ : Filter.Tendsto f (nhdsWithin (Real.pi / 2) (Set.Iio (Real.pi / 2))) (nhds 0))
    (hint : MeasureTheory.IntegrableOn
      (fun θ => Work.FTS.EllipticEst.AngSecond.sig θ * (f θ * deriv (deriv f) θ))
      (Set.Ioo 0 (Real.pi / 2))) :
    (∫ θ in Set.Ioo 0 (Real.pi / 2),
        Work.FTS.EllipticEst.AngSecond.sig θ * (f θ * deriv (deriv f) θ)) ≤ 0 := by
  have hfun : (fun θ => Work.FTS.EllipticEst.AngSecond.sig θ * (f θ * deriv (deriv f) θ))
      = Work.FTS.EllipticEst.Cores.AeStep2Aux.sliceIntegrand f := by
    funext θ
    simp only [Work.FTS.EllipticEst.Cores.AeStep2Aux.sliceIntegrand,
      Work.FTS.EllipticEst.Cores.AeStep2Aux.sig, Work.FTS.EllipticEst.AngSecond.sig]
  rw [hfun] at hint ⊢
  have hθ₀ : Real.pi / 4 ∈ Set.Ioo 0 (Real.pi / 2) :=
    ⟨by linarith [Real.pi_pos], by linarith [Real.pi_pos]⟩
  have hL := Work.FTS.EllipticEst.Cores.AeStep2Aux.slice_left_integral_nonneg
    hf h0 hint hθ₀
  have hR := slice_right_integral_nonpos_fts hf hπ hint hθ₀
  rw [Ioo_split_setIntegral hθ₀ hint]
  linarith

end Work.FTS.EllipticEst.AngAWeak
