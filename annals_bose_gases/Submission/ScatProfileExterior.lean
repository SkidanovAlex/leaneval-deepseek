import ChallengeDeps
import Mathlib.Order.Interval.Basic
import Mathlib.Analysis.Calculus.Deriv.Slope
import Mathlib.MeasureTheory.Integral.IntervalIntegral.Basic
import Submission.ScatChosen
import Submission.ScatProfileReg
-- PORT435-BEGIN (v4.35 isDefEq respectTransparency compat)
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- PORT435-END

/-!
# Exterior consistency of the regular profile (Layer 3)

`ScatProfileReg.scat_profile_reg_Ioi` / `ScatProfileODE.scat_profile_ODE_ae`
give, for a radial scattering solution `w` of a radial `v` (`tsupport v ⊆
ball 0 R`), for every `a > 0`, a differentiable function `U` on `(a,∞)` equal
a.e. to the profile `u(r) := r·radialProfile w r`.  For the *chosen*
scattering solution `w₀` of the `a v ≠ 0` branch, the exterior form is
`w₀ x = a v / ‖x‖` a.e. for `‖x‖ ≥ R` (`ScatChosen.chosen_scattering_av_exterior`),
so `u ≡ a v` a.e. on `(R,∞)`.  Since `U` agrees with `u` a.e. and is
continuous, `U` is *constantly* `a v` on `(R,∞)`; in particular
`U R = a v` and the two-sided derivative of `U` at `R` vanishes
(`HasDerivAt U 0 R` — forced by the right-hand constancy).  These are the
right-endpoint boundary data the maximum-principle bounds need.
-/

noncomputable section

open _root_.BoseGases
set_option autoImplicit false

namespace Submission.BoseGases

open Filter Metric MeasureTheory
open scoped ContDiff Topology Real Interval

local notation "ℝ³" => EuclideanSpace ℝ (Fin 3)

/-- If a 1D set of radii is null (Lebesgue) then its preimage under the norm
has zero volume in `ℝ³`.  (Works for possibly non-measurable `S` by passing
to the measurable hull; `volume_preimage_norm_null_r3` is the measurable
case.) -/
lemma volume_preimage_norm_null {S : Set ℝ}
    (hSvol : (volume : Measure ℝ) S = 0) :
    (volume : Measure ℝ³) {x : ℝ³ | ‖x‖ ∈ S} = 0 := by
  let N : Set ℝ := toMeasurable (volume : Measure ℝ) S
  have hNmeas : MeasurableSet N := measurableSet_toMeasurable (volume : Measure ℝ) S
  have hSsub : S ⊆ N := subset_toMeasurable (volume : Measure ℝ) S
  have hNvol : (volume : Measure ℝ) N = 0 := by
    rw [measure_toMeasurable]
    exact hSvol
  have hNpre : (volume : Measure ℝ³) {x : ℝ³ | ‖x‖ ∈ N} = 0 := by
    exact volume_preimage_norm_null_r3 hNmeas hNvol
  refine measure_mono_null (s := {x : ℝ³ | ‖x‖ ∈ S}) (t := {x : ℝ³ | ‖x‖ ∈ N}) ?_ hNpre
  intro x hx
  exact hSsub hx

/-- **Exterior consistency for the chosen scattering solution.**  In the
`a v ≠ 0` branch (`h : ∃ w, IsRadial w ∧ IsScatteringSolution w v`), for any
`0 < a₀ < R`, there is a function `U` on `(a,∞)` that is differentiable
everywhere, agrees a.e. with the profile `r ↦ r·radialProfile w₀ r` of the
chosen solution, is constantly `a v` on `[R,∞)`, and has zero derivative at
`R`. -/
theorem scat_profile_exterior_chosen {v : ℝ³ → ℝ} {R a₀ : ℝ} (hR : 0 < R) (ha₀ : 0 < a₀)
    (ha₀R : a₀ < R) (hvrad : IsRadial v) (hv_supp : tsupport v ⊆ ball (0 : ℝ³) R)
    (h : ∃ w : ℝ³ → ℝ, IsRadial w ∧ IsScatteringSolution w v) :
    let w₀ : ℝ³ → ℝ := Classical.choose h
    ∃ U : ℝ → ℝ,
      (∀ r : ℝ, a₀ < r → DifferentiableAt ℝ U r) ∧
      (∀ᵐ r : ℝ, a₀ < r → U r = r * radialProfile w₀ r) ∧
      (∀ r : ℝ, R ≤ r → U r = a v) ∧
      HasDerivAt U 0 R := by
  intro w₀
  have hspec := Classical.choose_spec h
  have hrad₀ : IsRadial w₀ := hspec.1
  have hw₀ : IsScatteringSolution w₀ v := hspec.2
  let u : ℝ → ℝ := fun r => r * radialProfile w₀ r
  -- regularity of the profile on (a₀, ∞)
  rcases scat_profile_reg_Ioi (v := v) (w := w₀) (R := R) (a := a₀) hR ha₀ hvrad hrad₀ hw₀ hv_supp
    with ⟨A, B, hEqRaw, hDiffRaw, _hDT⟩
  let U₀ : ℝ → ℝ := fun r => A + B * r + scatProfileP v w₀ a₀ r
  have hEq : ∀ᵐ r : ℝ, a₀ < r → u r = U₀ r := by
    filter_upwards [hEqRaw] with r hr hra
    simpa [u, U₀] using hr hra
  have hU₀ae : ∀ᵐ r : ℝ, a₀ < r → U₀ r = u r := by
    filter_upwards [hEq] with r hr hra
    exact (hr hra).symm
  have hU₀diff : ∀ r : ℝ, a₀ < r → DifferentiableAt ℝ U₀ r := by
    intro r hr
    exact (hDiffRaw r hr).differentiableAt
  -- null set where U₀ disagrees with the profile u above a₀
  have hB₁vol : (volume : Measure ℝ) {r : ℝ | a₀ < r ∧ U₀ r ≠ u r} = 0 := by
    have h := MeasureTheory.ae_iff.mp hU₀ae
    simpa using h
  -- the chosen exterior form (3D, a.e.)
  have h3d : ∀ᵐ x : ℝ³, R ≤ ‖x‖ → w₀ x = a v / ‖x‖ := by
    simpa [w₀] using (chosen_scattering_av_exterior (v := v) (R := R) hR hv_supp h)
  have hbadvol : (volume : Measure ℝ³) {x : ℝ³ | R ≤ ‖x‖ ∧ w₀ x ≠ a v / ‖x‖} = 0 := by
    have h := MeasureTheory.ae_iff.mp h3d
    simpa using h
  -- the exterior set E := {R < r ∧ U₀ r ≠ a v} has null norm-preimage:
  let E : Set ℝ := {r : ℝ | R < r ∧ U₀ r ≠ a v}
  let E₃ : Set ℝ := {r : ℝ | R < r ∧ u r ≠ a v}
  have hE₃pre_sub : {x : ℝ³ | ‖x‖ ∈ E₃} ⊆ {x : ℝ³ | R ≤ ‖x‖ ∧ w₀ x ≠ a v / ‖x‖} := by
    intro x hx
    have hRlt : R < ‖x‖ := hx.1
    have hu : u ‖x‖ ≠ a v := hx.2
    constructor
    · exact le_of_lt hRlt
    · have hwprof : w₀ x = radialProfile w₀ ‖x‖ := radial_eq_profile hrad₀ x
      intro hwEq
      have hf : radialProfile w₀ ‖x‖ = a v / ‖x‖ := by rwa [hwprof] at hwEq
      have huEq : u ‖x‖ = a v := by
        dsimp [u]
        have hne : ‖x‖ ≠ 0 := ne_of_gt (lt_trans hR hRlt)
        rw [hf]
        field_simp [hne]
      exact hu huEq
  have hE₃pre_null : (volume : Measure ℝ³) {x : ℝ³ | ‖x‖ ∈ E₃} = 0 := by
    exact measure_mono_null hE₃pre_sub hbadvol
  have hB₁pre_null : (volume : Measure ℝ³) {x : ℝ³ | ‖x‖ ∈ {r : ℝ | a₀ < r ∧ U₀ r ≠ u r}} = 0 := by
    exact volume_preimage_norm_null hB₁vol
  have hEpre_sub : {x : ℝ³ | ‖x‖ ∈ E} ⊆
      {x : ℝ³ | ‖x‖ ∈ {r : ℝ | a₀ < r ∧ U₀ r ≠ u r}} ∪ {x : ℝ³ | ‖x‖ ∈ E₃} := by
    intro x hx
    have hxE : ‖x‖ ∈ E := hx
    by_cases hcase : U₀ ‖x‖ = u ‖x‖
    · right
      exact ⟨hxE.1, by simpa [hcase] using hxE.2⟩
    · left
      exact ⟨lt_trans ha₀R hxE.1, hcase⟩
  have hEpre_null : (volume : Measure ℝ³) {x : ℝ³ | ‖x‖ ∈ E} = 0 := by
    refine measure_mono_null hEpre_sub ?_
    exact measure_union_null hB₁pre_null hE₃pre_null
  -- U₀ is constant a v on [R, ∞): any deviation forces an open shell of
  -- positive volume inside the (null) norm-preimage of E
  have hU₀const : ∀ r : ℝ, R ≤ r → U₀ r = a v := by
    intro r₀ hr₀
    by_contra hne
    have ha₀r₀ : a₀ < r₀ := lt_of_lt_of_le ha₀R hr₀
    have hr₀pos : 0 < r₀ := lt_of_lt_of_le hR hr₀
    have hcont : ContinuousAt U₀ r₀ := (hU₀diff r₀ ha₀r₀).continuousAt
    have hεpos : (0 : ℝ) < |U₀ r₀ - a v| := abs_pos.mpr (sub_ne_zero.mpr hne)
    rcases Metric.tendsto_nhds_nhds.mp hcont.tendsto |U₀ r₀ - a v| hεpos with ⟨δ, hδpos, hδ⟩
    have hδne : ∀ y : ℝ, dist y r₀ < δ → U₀ y ≠ a v := by
      intro y hy
      have hd := hδ hy
      intro hyEq
      have : |U₀ r₀ - a v| < |U₀ r₀ - a v| := by
        simp [Real.dist_eq, hyEq, abs_sub_comm] at hd ⊢
      exact (lt_irrefl _) this
    let I : Set ℝ := Set.Ioo r₀ (r₀ + δ)
    have hI_sub_E : I ⊆ E := by
      intro y hy
      have hy1 : r₀ < y := hy.1
      have hy2 : y < r₀ + δ := hy.2
      have hdist : dist y r₀ < δ := by
        rw [Real.dist_eq]
        rw [abs_of_nonneg (sub_nonneg.mpr (le_of_lt hy1))]
        linarith
      exact ⟨lt_of_le_of_lt hr₀ hy1, hδne y hdist⟩
    have hpreI_null : (volume : Measure ℝ³) {x : ℝ³ | ‖x‖ ∈ I} = 0 := by
      exact measure_mono_null (by intro x hx; exact hI_sub_E hx) hEpre_null
    let A : ℝ := r₀ + δ / 4
    let B : ℝ := r₀ + δ / 2
    have hA0 : 0 ≤ A := by dsimp [A]; linarith
    have hAB : A ≤ B := by dsimp [A, B]; linarith
    have hABlt : A < B := by dsimp [A, B]; linarith
    have hann_sub : {x : ℝ³ | A ≤ ‖x‖ ∧ ‖x‖ ≤ B} ⊆ {x : ℝ³ | ‖x‖ ∈ I} := by
      intro x hx
      dsimp [I]
      exact ⟨lt_of_lt_of_le (by dsimp [A]; linarith) hx.1,
        lt_of_le_of_lt hx.2 (by dsimp [B]; linarith)⟩
    have hann_pos : 0 < (volume : Measure ℝ³) {x : ℝ³ | A ≤ ‖x‖ ∧ ‖x‖ ≤ B} := by
      rw [volume_annulus_r3 A B hA0 hAB]
      refine ENNReal.ofReal_pos.mpr ?_
      have hAB3 : A ^ 3 < B ^ 3 := pow_lt_pow_left₀ (n := 3) hABlt hA0 (by norm_num)
      have hcube : 0 < B ^ 3 - A ^ 3 := sub_pos.mpr hAB3
      positivity
    have hpreI_pos : 0 < (volume : Measure ℝ³) {x : ℝ³ | ‖x‖ ∈ I} := by
      exact lt_of_lt_of_le hann_pos (measure_mono hann_sub)
    exact (ne_of_gt hpreI_pos) hpreI_null
  -- two-sided derivative of U₀ at R is zero
  have hdiffR : DifferentiableAt ℝ U₀ R := hU₀diff R ha₀R
  have hderR : HasDerivAt U₀ (deriv U₀ R) R := hdiffR.hasDerivAt
  let S : ℝ → ℝ := fun t : ℝ => t⁻¹ • (U₀ (R + t) - U₀ R)
  have hSzero : ∀ t : ℝ, 0 < t → S t = 0 := by
    intro t ht
    have hval : U₀ (R + t) = a v := hU₀const (R + t) (le_of_lt (by linarith))
    have hvalR : U₀ R = a v := hU₀const R (le_rfl)
    simp [S, hval, hvalR]
  have hStend0 : Tendsto S (𝓝[>] (0 : ℝ)) (𝓝 (0 : ℝ)) := by
    refine tendsto_const_nhds.congr' ?_
    refine Filter.eventually_of_mem (U := Set.Ioi (0 : ℝ)) ?_ ?_
    · simpa using (self_mem_nhdsWithin : Set.Ioi (0 : ℝ) ∈ 𝓝[Set.Ioi (0 : ℝ)] (0 : ℝ))
    · intro t ht
      exact (hSzero t ht).symm
  have hStendc : Tendsto S (𝓝[>] (0 : ℝ)) (𝓝 (deriv U₀ R)) := hderR.tendsto_slope_zero_right
  have hderiv0 : deriv U₀ R = 0 := tendsto_nhds_unique hStendc hStend0
  have hU₀derivR : HasDerivAt U₀ 0 R := by
    simpa [hderiv0] using hderR
  -- assemble the final U: U₀ on (a₀, ∞), a v elsewhere
  let U : ℝ → ℝ := fun r => if a₀ < r then U₀ r else a v
  refine ⟨U, ?_, ?_, ?_, ?_⟩
  · intro r hr
    have hU₀d : DifferentiableAt ℝ U₀ r := hU₀diff r hr
    refine hU₀d.congr_of_eventuallyEq ?_
    filter_upwards [(isOpen_Ioi : IsOpen (Set.Ioi a₀)).mem_nhds hr] with y hy
    have hya : a₀ < y := hy
    simp [U, hya]
  · filter_upwards [hU₀ae] with r hr hra
    have heq : U₀ r = u r := hr hra
    simp [U, hra, u, heq]
  · intro r hr
    have hcon : U₀ r = a v := hU₀const r hr
    have hra : a₀ < r := lt_of_lt_of_le ha₀R hr
    simp [U, hra, hcon]
  · refine HasDerivAt.congr_of_eventuallyEq hU₀derivR ?_
    filter_upwards [(isOpen_Ioi : IsOpen (Set.Ioi a₀)).mem_nhds ha₀R] with y hy
    have hya : a₀ < y := hy
    simp [U, hya]

end Submission.BoseGases
