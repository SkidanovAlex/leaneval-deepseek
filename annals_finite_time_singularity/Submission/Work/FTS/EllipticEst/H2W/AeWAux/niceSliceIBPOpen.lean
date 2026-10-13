/-
Copyright: work module for the Elgindi finite-time singularity project.

# The `z`-integration by parts of `nice`, for data smooth on the *open* quadrant

This module proves `niceSliceIBPOpen`: the identity

  `∫_z nice n u (z,θ) = - ∫_z ∂_z²u(z,θ) · (z² ∂_θ²u(z,θ) · cut n z · w²(z))`

for a datum `u` which is `C^∞` on the *open* quadrant `(0,∞) × (0,π/2)` and an interior angle
`θ ∈ (0,π/2)`.

It is the open-quadrant (non-analytic) form of `Work.FTS.EllipticEst.AngSecond.slice_nice_ibp`,
whose hypothesis `Work.Spaces.SmoothNbhd u` asks for analyticity on a neighbourhood of the
*closed* quadrant — far too strong for the cut-off data of the truncation argument.  The
hypothesis here is exactly the class `Work.FTS.EllipticEst.SmoothOpen` of
`Submission/Work/FTS/EllipticEst/OpenQDefs.lean`, and the proof is the same two-step argument:

* the pointwise identity `nice n u z θ = pz u z θ · Dv n u z θ` of `AngSecond.pz_mul_Dv_eq_nice`
  (`pz * (z² ∂_θ²u · cut · w²)'` expanded with the product rule and `(w²)' = -4w²/((1+z)z)`),
  which only needs the *open*-quadrant smoothness of the `z`-slices;
* the half-line integration by parts `MeasureTheory.integral_Ioi_mul_deriv_eq_deriv_mul` on
  `(0,∞)`, where every integrand is supported on the compact slab
  `[1/(2(n+1)), 4(n+1)]` on which `cut n` is a genuine cut-off, so that both boundary terms
  vanish (the `z = 0` one because `cut n` vanishes near `0`).

Everything here is `sorry`-free and rests on `[propext, Classical.choice, Quot.sound]`.
-/
import Mathlib.Analysis.LocallyConvex.AbsConvexOpen
import Mathlib.MeasureTheory.Integral.IntegralEqImproper
import Submission.Work.FTS.EllipticEst.AngSecond.I1_defs
import Submission.Work.FTS.EllipticEst.AngSecond.Defs
import Submission.Work.FTS.EllipticEst.OpenQDefs

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

noncomputable section

open scoped Real Topology ContDiff
open MeasureTheory Set Filter

namespace Work.FTS.EllipticEst.H2W.AeWAux

set_option autoImplicit false
set_option linter.unusedVariables false
set_option maxHeartbeats 800000

/-! ## Two elementary bookkeeping facts -/

/-- The half-line set integrals over `Iz = [0,∞)` and over `Ioi 0 = (0,∞)` agree: the two
measures differ only at the null point `0`. -/
private theorem setIntegral_Iz_eq_setIntegral_Ioi (f : ℝ → ℝ) :
    (∫ z in Work.Spaces.Iz, f z) = ∫ z in Set.Ioi (0 : ℝ), f z := by
  rw [Work.Spaces.Iz, MeasureTheory.integral_Ici_eq_integral_Ioi]

/-- A function continuous on `[a,b]` (`0 < a ≤ b`) and vanishing outside `[a,b]` is integrable
on `(0,∞)`; its support is the compact subset `[a,b] ⊆ (0,∞)`. -/
private theorem integrableOn_Ioi_of_Icc_support {f : ℝ → ℝ} {a b : ℝ} (ha : 0 < a)
    (hab : a ≤ b) (hcont : ContinuousOn f (Set.Icc a b))
    (hzero : ∀ z, z ∉ Set.Icc a b → f z = 0) :
    MeasureTheory.IntegrableOn f (Set.Ioi 0) := by
  have hInd : MeasureTheory.Integrable ((Set.Icc a b).indicator f) volume :=
    (MeasureTheory.integrable_indicator_iff measurableSet_Icc).mpr
      (hcont.integrableOn_compact isCompact_Icc)
  have hfun : f = (Set.Icc a b).indicator f := by
    funext z
    by_cases hz : z ∈ Set.Icc a b
    · rw [Set.indicator_of_mem hz]
    · rw [Set.indicator_of_notMem hz, hzero z hz]
  rw [hfun]
  refine ⟨hInd.aestronglyMeasurable.mono_measure Measure.restrict_le_self, ?_⟩
  calc ∫⁻ z, ‖(Set.Icc a b).indicator f z‖₊ ∂(volume.restrict (Set.Ioi 0))
      ≤ ∫⁻ z, ‖(Set.Icc a b).indicator f z‖₊ ∂(volume : MeasureTheory.Measure ℝ) :=
        lintegral_mono' Measure.restrict_le_self le_rfl
    _ < ⊤ := hInd.hasFiniteIntegral

/-! ## The pointwise identity `nice = ∂_z u · Dv`, in the open class -/

/-- The `z`-derivative of `z ↦ z² · ∂_θ²u(z,θ) · cut n z · w²(z)`, in raw expanded form.
The open-quadrant analogue of `Work.FTS.EllipticEst.AngSecond.hasDerivAt_z2_phi_chi_w2`. -/
theorem hasDerivAt_z2_phi_chi_w2_open (n : ℕ) (u : ℝ → ℝ → ℝ)
    (hu : Work.FTS.EllipticEst.SmoothOpen u) {z : ℝ} (hz : 0 < z) {θ : ℝ}
    (hθ : θ ∈ Set.Ioo 0 (Real.pi / 2)) :
    HasDerivAt (fun z' => z' ^ 2 * Work.Spaces.pthIter 2 u z' θ
        * Work.FTS.EllipticEst.cut n z' * Work.FTS.EllipticEst.AngSecond.w2 z')
      (2 * z * Work.Spaces.pthIter 2 u z θ * Work.FTS.EllipticEst.cut n z
          * Work.FTS.EllipticEst.AngSecond.w2 z
        + z ^ 2 * Work.Spaces.pz (Work.Spaces.pthIter 2 u) z θ
          * Work.FTS.EllipticEst.cut n z * Work.FTS.EllipticEst.AngSecond.w2 z
        + z ^ 2 * Work.Spaces.pthIter 2 u z θ * deriv (Work.FTS.EllipticEst.cut n) z
          * Work.FTS.EllipticEst.AngSecond.w2 z
        + z ^ 2 * Work.Spaces.pthIter 2 u z θ * Work.FTS.EllipticEst.cut n z
          * deriv Work.FTS.EllipticEst.AngSecond.w2 z) z := by
  have h1 : HasDerivAt (fun z' : ℝ => z' ^ 2) (2 * z) z := by
    have h := (hasDerivAt_id z).pow 2
    have h2 : ((2 : ℕ) : ℝ) * z ^ (2 - 1) * (1 : ℝ) = 2 * z := by norm_num
    exact h.congr_deriv h2
  have hP : Work.FTS.EllipticEst.SmoothOpen (Work.Spaces.pthIter 2 u) := by
    have h := hu.pth.pth
    simpa only [Work.Spaces.pthIter_succ, Work.Spaces.pthIter_zero] using h
  have h2 : HasDerivAt (fun z' : ℝ => Work.Spaces.pthIter 2 u z' θ)
      (Work.Spaces.pz (Work.Spaces.pthIter 2 u) z θ) z := hP.hasDerivAt_slice hθ hz
  have h3 : HasDerivAt (fun z' : ℝ => Work.FTS.EllipticEst.cut n z')
      (deriv (Work.FTS.EllipticEst.cut n) z) z :=
    ((Work.FTS.EllipticEst.cut_contDiff n).differentiable (by simp)).differentiableAt.hasDerivAt
  have h4 : HasDerivAt Work.FTS.EllipticEst.AngSecond.w2
      (deriv Work.FTS.EllipticEst.AngSecond.w2 z) z :=
    (Work.FTS.EllipticEst.AngSecond.hasDerivAt_w2 hz).differentiableAt.hasDerivAt
  have htot := ((h1.mul h2).mul h3).mul h4
  refine htot.congr_deriv ?_
  simp only [Pi.mul_apply]
  ring

/-- The same derivative, in the bundled form `Dv n u z θ`. -/
theorem hasDerivAt_v_eq_Dv_open (n : ℕ) (u : ℝ → ℝ → ℝ)
    (hu : Work.FTS.EllipticEst.SmoothOpen u) {z : ℝ} (hz : 0 < z) {θ : ℝ}
    (hθ : θ ∈ Set.Ioo 0 (Real.pi / 2)) :
    HasDerivAt (fun z' => z' ^ 2 * Work.Spaces.pthIter 2 u z' θ
        * Work.FTS.EllipticEst.cut n z' * Work.FTS.EllipticEst.AngSecond.w2 z')
      (Work.FTS.EllipticEst.AngSecond.Dv n u z θ) z :=
  hasDerivAt_z2_phi_chi_w2_open n u hu hz hθ

/-- The pointwise expansion of the `z`-derivative, i.e. the right-hand side of the definition
of `nice`. -/
theorem pz_mul_deriv_expansion_open (n : ℕ) (u : ℝ → ℝ → ℝ)
    (hu : Work.FTS.EllipticEst.SmoothOpen u) {z : ℝ} (hz : 0 < z) {θ : ℝ}
    (hθ : θ ∈ Set.Ioo 0 (Real.pi / 2)) :
    Work.Spaces.pz u z θ
        * deriv (fun z' => z' ^ 2 * Work.Spaces.pthIter 2 u z' θ
            * Work.FTS.EllipticEst.cut n z' * Work.FTS.EllipticEst.AngSecond.w2 z') z
      = Work.FTS.EllipticEst.cut n z * Work.FTS.EllipticEst.AngSecond.w2 z
          * (2 * (z * Work.Spaces.pz u z θ) * (Work.Spaces.pthIter 2 u z θ)
              + (z * Work.Spaces.pz u z θ)
                  * (z * Work.Spaces.pz (Work.Spaces.pthIter 2 u) z θ)
              - 4 * (z * Work.Spaces.pz u z θ) * (Work.Spaces.pthIter 2 u z θ) / (1 + z))
        + Work.FTS.EllipticEst.AngSecond.w2 z
            * ((z * Work.Spaces.pz u z θ) * (Work.Spaces.pthIter 2 u z θ))
            * (z * deriv (Work.FTS.EllipticEst.cut n) z) := by
  rw [(hasDerivAt_z2_phi_chi_w2_open n u hu hz hθ).deriv]
  rw [Work.FTS.EllipticEst.AngSecond.deriv_w2_eq' hz]
  have hz0 : z ≠ 0 := ne_of_gt hz
  have h1z : (1 : ℝ) + z ≠ 0 := by linarith
  field_simp
  ring

/-- **The pointwise form of the cut-off identity, in the open class.**
`∂_z u(z,θ) · Dv n u z θ = nice n u z θ` for every `z > 0` and every interior angle. -/
theorem pz_mul_Dv_eq_nice_open (n : ℕ) (u : ℝ → ℝ → ℝ)
    (hu : Work.FTS.EllipticEst.SmoothOpen u) {z : ℝ} (hz : 0 < z) {θ : ℝ}
    (hθ : θ ∈ Set.Ioo 0 (Real.pi / 2)) :
    Work.Spaces.pz u z θ * Work.FTS.EllipticEst.AngSecond.Dv n u z θ
      = Work.FTS.EllipticEst.AngSecond.nice n u z θ := by
  have h := pz_mul_deriv_expansion_open n u hu hz hθ
  have hd : deriv (fun z' => z' ^ 2 * Work.Spaces.pthIter 2 u z' θ
      * Work.FTS.EllipticEst.cut n z' * Work.FTS.EllipticEst.AngSecond.w2 z') z
      = Work.FTS.EllipticEst.AngSecond.Dv n u z θ := (hasDerivAt_v_eq_Dv_open n u hu hz hθ).deriv
  rw [hd] at h
  rw [h]
  simp only [Work.FTS.EllipticEst.AngSecond.nice, Work.FTS.EllipticEst.AngSecond.G,
    Work.FTS.EllipticEst.AngSecond.Phi, Work.FTS.EllipticEst.AngSecond.H]

/-! ## The per-angle integration by parts on the half-line -/

/-- **The slice form of the `z`-integration by parts**, for data which are `C^∞` only on the
open quadrant.  Same statement as `Work.FTS.EllipticEst.AngSecond.slice_ibp_halfline`, with
`Work.Spaces.SmoothNbhd u` replaced by `Work.FTS.EllipticEst.SmoothOpen u` and a closed angle
by an interior one. -/
theorem slice_ibp_halfline_open (n : ℕ) (u : ℝ → ℝ → ℝ)
    (hu : Work.FTS.EllipticEst.SmoothOpen u) {θ : ℝ} (hθ : θ ∈ Set.Ioo 0 (Real.pi / 2)) :
    (∫ z in Set.Ioi (0 : ℝ), Work.Spaces.pz u z θ
        * Work.FTS.EllipticEst.AngSecond.Dv n u z θ)
      = -∫ z in Set.Ioi (0 : ℝ), Work.Spaces.pzIter 2 u z θ
          * (z ^ 2 * Work.Spaces.pthIter 2 u z θ * Work.FTS.EllipticEst.cut n z
              * Work.FTS.EllipticEst.AngSecond.w2 z) := by
  have ha : (0 : ℝ) < 1 / (2 * (n + 1 : ℝ)) := by positivity
  have hab : 1 / (2 * (n + 1 : ℝ)) ≤ 4 * (n + 1 : ℝ) := by
    have h1 : 1 / (2 * (n + 1 : ℝ)) ≤ 1 := by
      rw [div_le_one (by positivity)]
      linarith
    have h2 : (1 : ℝ) ≤ 4 * (n + 1 : ℝ) := by
      have : (0 : ℝ) < (n + 1 : ℝ) := by positivity
      linarith
    linarith
  have hsub : Set.Icc (1 / (2 * (n + 1 : ℝ))) (4 * (n + 1 : ℝ)) ⊆ Set.Ioi (0 : ℝ) :=
    fun z hz => lt_of_lt_of_le ha hz.1
  have hP : Work.FTS.EllipticEst.SmoothOpen (Work.Spaces.pthIter 2 u) := by
    have h := hu.pth.pth
    simpa only [Work.Spaces.pthIter_succ, Work.Spaces.pthIter_zero] using h
  have hQ : Work.FTS.EllipticEst.SmoothOpen (Work.Spaces.pz (Work.Spaces.pthIter 2 u)) := hP.pz
  have hR : Work.FTS.EllipticEst.SmoothOpen (Work.Spaces.pzIter 2 u) := hu.pzIter 2
  have hcont_pth : ContinuousOn (fun z : ℝ => Work.Spaces.pthIter 2 u z θ)
      (Set.Icc (1 / (2 * (n + 1 : ℝ))) (4 * (n + 1 : ℝ))) :=
    (hP.curry_z hθ).continuousOn.mono hsub
  have hcont_pzpth : ContinuousOn (fun z : ℝ => Work.Spaces.pz (Work.Spaces.pthIter 2 u) z θ)
      (Set.Icc (1 / (2 * (n + 1 : ℝ))) (4 * (n + 1 : ℝ))) :=
    (hQ.curry_z hθ).continuousOn.mono hsub
  have hcont_pz : ContinuousOn (fun z : ℝ => Work.Spaces.pz u z θ)
      (Set.Icc (1 / (2 * (n + 1 : ℝ))) (4 * (n + 1 : ℝ))) :=
    ((hu.pz).curry_z hθ).continuousOn.mono hsub
  have hcont_pzIter : ContinuousOn (fun z : ℝ => Work.Spaces.pzIter 2 u z θ)
      (Set.Icc (1 / (2 * (n + 1 : ℝ))) (4 * (n + 1 : ℝ))) :=
    (hR.curry_z hθ).continuousOn.mono hsub
  have hcont_cut : ContinuousOn (fun z : ℝ => Work.FTS.EllipticEst.cut n z)
      (Set.Icc (1 / (2 * (n + 1 : ℝ))) (4 * (n + 1 : ℝ))) :=
    (Work.FTS.EllipticEst.cut_contDiff n).continuous.continuousOn
  have hDv : ContinuousOn (fun z : ℝ => Work.FTS.EllipticEst.AngSecond.Dv n u z θ)
      (Set.Icc (1 / (2 * (n + 1 : ℝ))) (4 * (n + 1 : ℝ))) := by
    have hφ := hcont_pth
    have hφ' := hcont_pzpth
    have hχ := hcont_cut
    have hχ' : ContinuousOn (fun z : ℝ => deriv (Work.FTS.EllipticEst.cut n) z)
        (Set.Icc (1 / (2 * (n + 1 : ℝ))) (4 * (n + 1 : ℝ))) :=
      (Work.FTS.EllipticEst.AngSecond.continuous_deriv_cut n).continuousOn
    have hw : ContinuousOn (fun z : ℝ => Work.FTS.EllipticEst.AngSecond.w2 z)
        (Set.Icc (1 / (2 * (n + 1 : ℝ))) (4 * (n + 1 : ℝ))) :=
      Work.FTS.EllipticEst.AngSecond.continuousOn_w2' ha
    have hw' : ContinuousOn (fun z : ℝ => deriv Work.FTS.EllipticEst.AngSecond.w2 z)
        (Set.Icc (1 / (2 * (n + 1 : ℝ))) (4 * (n + 1 : ℝ))) :=
      Work.FTS.EllipticEst.AngSecond.continuousOn_deriv_w2' ha
    simp only [Work.FTS.EllipticEst.AngSecond.Dv]
    fun_prop
  have hu' : ∀ x ∈ Set.Ioi (0 : ℝ), HasDerivAt (fun z => Work.Spaces.pz u z θ)
      (Work.Spaces.pzIter 2 u x θ) x := by
    intro x hx
    have h := (hu.pz).hasDerivAt_slice hθ hx
    simpa only [Work.Spaces.pzIter_succ, Work.Spaces.pzIter_zero] using h
  have hv' : ∀ x ∈ Set.Ioi (0 : ℝ),
      HasDerivAt (fun z => z ^ 2 * Work.Spaces.pthIter 2 u z θ * Work.FTS.EllipticEst.cut n z
        * Work.FTS.EllipticEst.AngSecond.w2 z) (Work.FTS.EllipticEst.AngSecond.Dv n u x θ) x :=
    fun x hx => hasDerivAt_v_eq_Dv_open n u hu hx hθ
  have hI1 : MeasureTheory.IntegrableOn (fun z => Work.Spaces.pz u z θ
      * Work.FTS.EllipticEst.AngSecond.Dv n u z θ) (Set.Ioi 0) := by
    refine integrableOn_Ioi_of_Icc_support (f := fun z => Work.Spaces.pz u z θ
      * Work.FTS.EllipticEst.AngSecond.Dv n u z θ) ha hab ?_ ?_
    · exact hcont_pz.mul hDv
    · intro z hz
      rw [Work.FTS.EllipticEst.AngSecond.Dv_eq_zero_of_notMem n u hz, mul_zero]
  have hI2 : MeasureTheory.IntegrableOn (fun z => Work.Spaces.pzIter 2 u z θ
      * (z ^ 2 * Work.Spaces.pthIter 2 u z θ * Work.FTS.EllipticEst.cut n z
          * Work.FTS.EllipticEst.AngSecond.w2 z)) (Set.Ioi 0) := by
    refine integrableOn_Ioi_of_Icc_support (f := fun z => Work.Spaces.pzIter 2 u z θ
      * (z ^ 2 * Work.Spaces.pthIter 2 u z θ * Work.FTS.EllipticEst.cut n z
          * Work.FTS.EllipticEst.AngSecond.w2 z)) ha hab ?_ ?_
    · have hz2χφ : ContinuousOn (fun z : ℝ => z ^ 2 * Work.Spaces.pthIter 2 u z θ
          * Work.FTS.EllipticEst.cut n z * Work.FTS.EllipticEst.AngSecond.w2 z)
          (Set.Icc (1 / (2 * (n + 1 : ℝ))) (4 * (n + 1 : ℝ))) :=
        (((continuousOn_id.pow 2).mul hcont_pth).mul hcont_cut).mul
          (Work.FTS.EllipticEst.AngSecond.continuousOn_w2' ha)
      exact hcont_pzIter.mul hz2χφ
    · intro z hz
      have hn : (0 : ℝ) < (n + 1 : ℝ) := by positivity
      have ha' : 1 / (2 * (n + 1 : ℝ)) ≤ 1 / (n + 1 : ℝ) :=
        one_div_le_one_div_of_le hn (by linarith)
      simp only [Set.mem_Icc, not_and_or, not_le] at hz
      rcases hz with hzlt | hzgt
      · have h1 : z ≤ 1 / (n + 1 : ℝ) := by linarith
        simp [Work.FTS.EllipticEst.cut_apply_zero_of_le n h1]
      · have h1 : 3 * (n + 1 : ℝ) ≤ z := by linarith
        simp [Work.FTS.EllipticEst.cut_apply_zero_of_ge n h1]
  have hmem0 : ∀ᶠ z in 𝓝[>] (0 : ℝ), z < 1 / (n + 1 : ℝ) := by
    have hpos : (0 : ℝ) < 1 / (n + 1 : ℝ) := by positivity
    have hmem : Set.Iio (1 / (n + 1 : ℝ)) ∈ 𝓝 (0 : ℝ) :=
      isOpen_Iio.mem_nhds (show (0 : ℝ) ∈ Set.Iio (1 / (n + 1 : ℝ)) from hpos)
    exact nhdsWithin_le_nhds hmem
  have hbnd0 : Filter.Tendsto (fun z => Work.Spaces.pz u z θ
      * (z ^ 2 * Work.Spaces.pthIter 2 u z θ * Work.FTS.EllipticEst.cut n z
          * Work.FTS.EllipticEst.AngSecond.w2 z)) (𝓝[>] (0 : ℝ)) (nhds 0) := by
    refine Filter.Tendsto.congr' ?_ tendsto_const_nhds
    filter_upwards [hmem0] with z hz
    simp [Work.FTS.EllipticEst.cut_apply_zero_of_le n hz.le]
  have hbndT : Filter.Tendsto (fun z => Work.Spaces.pz u z θ
      * (z ^ 2 * Work.Spaces.pthIter 2 u z θ * Work.FTS.EllipticEst.cut n z
          * Work.FTS.EllipticEst.AngSecond.w2 z)) Filter.atTop (nhds 0) := by
    refine Filter.Tendsto.congr' ?_ tendsto_const_nhds
    filter_upwards [eventually_ge_atTop (3 * (n + 1 : ℝ))] with z hz
    simp [Work.FTS.EllipticEst.cut_apply_zero_of_ge n hz]
  have hIBP := MeasureTheory.integral_Ioi_mul_deriv_eq_deriv_mul (a := (0 : ℝ)) (a' := (0 : ℝ))
    (b' := (0 : ℝ))
    (u := fun z => Work.Spaces.pz u z θ) (u' := fun z => Work.Spaces.pzIter 2 u z θ)
    (v := fun z => z ^ 2 * Work.Spaces.pthIter 2 u z θ * Work.FTS.EllipticEst.cut n z
      * Work.FTS.EllipticEst.AngSecond.w2 z)
    (v' := fun z => Work.FTS.EllipticEst.AngSecond.Dv n u z θ)
    hu' hv' hI1 hI2 hbnd0 hbndT
  simpa using hIBP

/-! ## The target -/

theorem niceSliceIBPOpen (n : ℕ) (u : ℝ → ℝ → ℝ)
    (hsm : ∀ k : ℕ, ContDiffOn ℝ k (Function.uncurry u)
      (Set.Ioi 0 ×ˢ Set.Ioo 0 (Real.pi / 2)))
    {θ : ℝ} (hθ : θ ∈ Set.Ioo 0 (Real.pi / 2)) :
    (∫ z in Work.Spaces.Iz, Work.FTS.EllipticEst.AngSecond.nice n u z θ)
      = -∫ z in Work.Spaces.Iz, Work.Spaces.pzIter 2 u z θ
          * (z ^ 2 * Work.Spaces.pthIter 2 u z θ * Work.FTS.EllipticEst.cut n z
              * Work.FTS.EllipticEst.AngSecond.w2 z) := by
  have hu : Work.FTS.EllipticEst.SmoothOpen u :=
    Work.FTS.EllipticEst.smoothOpen_of_forall hsm
  have hmul : (fun z => Work.FTS.EllipticEst.AngSecond.nice n u z θ)
      =ᵐ[volume.restrict Work.Spaces.Iz]
      (fun z => Work.Spaces.pz u z θ * Work.FTS.EllipticEst.AngSecond.Dv n u z θ) := by
    rw [Work.Spaces.Iz, ← MeasureTheory.restrict_Ioi_eq_restrict_Ici]
    filter_upwards [MeasureTheory.ae_restrict_mem measurableSet_Ioi] with z hz
    exact (pz_mul_Dv_eq_nice_open n u hu hz hθ).symm
  calc (∫ z in Work.Spaces.Iz, Work.FTS.EllipticEst.AngSecond.nice n u z θ)
      = ∫ z in Work.Spaces.Iz, Work.Spaces.pz u z θ
          * Work.FTS.EllipticEst.AngSecond.Dv n u z θ :=
        MeasureTheory.integral_congr_ae hmul
    _ = ∫ z in Set.Ioi (0 : ℝ), Work.Spaces.pz u z θ
          * Work.FTS.EllipticEst.AngSecond.Dv n u z θ :=
        setIntegral_Iz_eq_setIntegral_Ioi _
    _ = -∫ z in Set.Ioi (0 : ℝ), Work.Spaces.pzIter 2 u z θ
          * (z ^ 2 * Work.Spaces.pthIter 2 u z θ * Work.FTS.EllipticEst.cut n z
              * Work.FTS.EllipticEst.AngSecond.w2 z) :=
        slice_ibp_halfline_open n u hu hθ
    _ = -∫ z in Work.Spaces.Iz, Work.Spaces.pzIter 2 u z θ
          * (z ^ 2 * Work.Spaces.pthIter 2 u z θ * Work.FTS.EllipticEst.cut n z
              * Work.FTS.EllipticEst.AngSecond.w2 z) := by
        rw [setIntegral_Iz_eq_setIntegral_Ioi]

end Work.FTS.EllipticEst.H2W.AeWAux
