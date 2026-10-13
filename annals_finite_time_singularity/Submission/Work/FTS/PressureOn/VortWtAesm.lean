/-
# `Work.FTS.PressureOn.VortWtAesm` — measurability of the angular derivative of the profile

`Work.Spaces.pth (gSlice g τ)` — the angular derivative of the perturbation slice — is needed
inside the majorant `vBound` of the spatial derivative of the vorticity.  This module proves that
`(z,θ) ↦ |∂_θ g(z,|θ|,τ)|` is a.e. strongly measurable on the half-strip
`(0,∞) × (-π/2,π/2)`:

* `Jet` (the joint `α`-Hölder bound on `z ≥ 0`, `θ ∈ Iθ`) makes `(z,θ) ↦ g z θ τ` continuous on
  the closed quadrant (`continuousOn_uncurry_gSlice`);
* the clamped extension `z ↦ max z 0`, `θ ↦ min |θ| (π/2)` of that slice is therefore a
  *continuous* two-variable family, so Mathlib's `measurable_deriv_with_param` gives joint
  measurability of `(z,θ) ↦ ∂_θ (clamped slice)(θ)`;
* that function agrees with `|∂_θ g(z,|θ|,τ)|` on the half-strip off the null angular line
  `θ = 0`, because the clamped slice agrees with `θ' ↦ g z θ' τ` resp. with
  `θ' ↦ g z (-θ') τ` on a neighbourhood of `θ ≠ 0`.
-/
import Mathlib.Algebra.Order.Star.Real
import Mathlib.Analysis.Calculus.Deriv.Shift
import Mathlib.Analysis.Calculus.FDeriv.Measurable
import Mathlib.MeasureTheory.Measure.Lebesgue.Basic
import Submission.Work.FTS.Regularity.Defs

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

noncomputable section

open FiniteTimeSingularity Set MeasureTheory Filter Topology
open scoped Topology NNReal ENNReal

namespace Work.FTS.PressureOn

local notation "R3" => EuclideanSpace ℝ (Fin 3)

/-- **The perturbation slice is continuous on the closed quadrant.**  This is the Hölder estimate
of the `Jet` field of `RegPkg`, read as an `ε`-`δ` continuity statement. -/
theorem continuousOn_uncurry_gSlice {α S Ng : ℝ} {g : ℝ → ℝ → ℝ → ℝ} (hα : 0 < α)
    (hJet : Work.FTS.Regularity.Jet α S Ng g) {τ : ℝ} (hτ : τ ∈ Set.Icc 0 S) :
    ContinuousOn (fun p : ℝ × ℝ => g p.1 p.2 τ) (Set.Ici 0 ×ˢ Work.Spaces.Iθ) := by
  have hN0 : 0 ≤ Ng := hJet.1
  rw [Metric.continuousOn_iff]
  intro p hp ε hε
  by_cases hN : Ng = 0
  · refine ⟨1, one_pos, fun q hq _ => ?_⟩
    have hle := hJet.2.2 q.1 p.1 q.2 p.2 τ τ hq.1 hp.1 hq.2 hp.2 hτ hτ
    rw [hN, zero_mul] at hle
    have h0 : 0 ≤ g q.1 q.2 τ - g p.1 p.2 τ := by
      linarith [neg_abs_le (g q.1 q.2 τ - g p.1 p.2 τ), hle]
    rw [Real.dist_eq, abs_of_nonneg h0]
    linarith [le_abs_self (g q.1 q.2 τ - g p.1 p.2 τ), hle, hε]
  · have hNpos : 0 < Ng := lt_of_le_of_ne hN0 (Ne.symm hN)
    have h2α : 0 < (2 : ℝ) ^ α := Real.rpow_pos_of_pos (by norm_num) _
    have hcoef : 0 < Ng * 2 ^ α := mul_pos hNpos h2α
    refine ⟨min 1 (((ε / (Ng * 2 ^ α)) ^ (1 / α)) / 2), lt_min one_pos
      (div_pos (Real.rpow_pos_of_pos (div_pos hε hcoef) _) (by norm_num)), fun q hq hpq => ?_⟩
    have hmax : max |q.1 - p.1| |q.2 - p.2| <
        min 1 (((ε / (Ng * 2 ^ α)) ^ (1 / α)) / 2) := by
      simpa only [Real.dist_eq, Prod.dist_eq] using hpq
    have hd1 : |q.1 - p.1| < min 1 (((ε / (Ng * 2 ^ α)) ^ (1 / α)) / 2) :=
      lt_of_le_of_lt (le_max_left _ _) hmax
    have hd2 : |q.2 - p.2| < min 1 (((ε / (Ng * 2 ^ α)) ^ (1 / α)) / 2) :=
      lt_of_le_of_lt (le_max_right _ _) hmax
    have hsum : |q.1 - p.1| + |q.2 - p.2| ≤ (ε / (Ng * 2 ^ α)) ^ (1 / α) := by
      have h1 : |q.1 - p.1| ≤ ((ε / (Ng * 2 ^ α)) ^ (1 / α)) / 2 :=
        le_of_lt (lt_of_lt_of_le hd1 (min_le_right _ _))
      have h2 : |q.2 - p.2| ≤ ((ε / (Ng * 2 ^ α)) ^ (1 / α)) / 2 :=
        le_of_lt (lt_of_lt_of_le hd2 (min_le_right _ _))
      linarith
    have hle := hJet.2.2 q.1 p.1 q.2 p.2 τ τ hq.1 hp.1 hq.2 hp.2 hτ hτ
    have hle0 : |g q.1 q.2 τ - g p.1 p.2 τ| ≤ Ng * (|q.1 - p.1| + |q.2 - p.2|) ^ α := by
      simpa using hle
    have hpow : (|q.1 - p.1| + |q.2 - p.2|) ^ α ≤ ε / (Ng * 2 ^ α) := by
      have h1 : ((ε / (Ng * 2 ^ α)) ^ (1 / α)) ^ α = ε / (Ng * 2 ^ α) := by
        rw [← Real.rpow_mul (le_of_lt (div_pos hε hcoef)), one_div, inv_mul_cancel₀,
          Real.rpow_one]
        positivity
      rw [← h1]
      exact Real.rpow_le_rpow (by positivity) hsum (le_of_lt hα)
    rw [Real.dist_eq]
    calc |g q.1 q.2 τ - g p.1 p.2 τ|
        ≤ Ng * (|q.1 - p.1| + |q.2 - p.2|) ^ α := hle0
      _ ≤ Ng * (ε / (Ng * 2 ^ α)) := by
          exact mul_le_mul_of_nonneg_left hpow hN0
      _ = ε / 2 ^ α := by field_simp
      _ < ε := by
          rw [div_lt_iff₀ h2α]
          have h2 : (1 : ℝ) < 2 ^ α := Real.one_lt_rpow one_lt_two hα
          nlinarith

/-- The clamped slice of the perturbation: extending the angular variable by `θ ↦ min |θ| (π/2)`
and the radial variable by `z ↦ max z 0`, which is continuous on the whole plane. -/
noncomputable def clampSlice (g : ℝ → ℝ → ℝ → ℝ) (τ : ℝ) (z θ : ℝ) : ℝ :=
  g (max z 0) (min |θ| (Real.pi / 2)) τ

/-- The clamped slice is continuous. -/
theorem continuous_clampSlice {α S Ng : ℝ} {g : ℝ → ℝ → ℝ → ℝ} (hα : 0 < α)
    (hJet : Work.FTS.Regularity.Jet α S Ng g) {τ : ℝ} (hτ : τ ∈ Set.Icc 0 S) :
    Continuous (fun p : ℝ × ℝ => clampSlice g τ p.1 p.2) := by
  have hcont := continuousOn_uncurry_gSlice hα hJet hτ
  have hmap : Continuous (fun p : ℝ × ℝ =>
      (max p.1 0, min |p.2| (Real.pi / 2))) := by fun_prop
  have hmem : ∀ p : ℝ × ℝ, (max p.1 0, min |p.2| (Real.pi / 2)) ∈ Set.Ici 0 ×ˢ Work.Spaces.Iθ := by
    rintro ⟨z, θ⟩
    exact ⟨le_max_right z 0, le_min (abs_nonneg θ) (by linarith [Real.pi_pos]),
      min_le_right _ _⟩
  have h := hcont.comp_continuous hmap hmem
  simpa [clampSlice, Function.comp_def] using h

/-- **The measurable parametrised `θ`-derivative of the clamped slice.** -/
theorem measurable_deriv_clampSlice {α S Ng : ℝ} {g : ℝ → ℝ → ℝ → ℝ} (hα : 0 < α)
    (hJet : Work.FTS.Regularity.Jet α S Ng g) {τ : ℝ} (hτ : τ ∈ Set.Icc 0 S) :
    Measurable (fun p : ℝ × ℝ =>
      deriv (fun θ' => clampSlice g τ p.1 θ') p.2) := by
  have hcont := continuous_clampSlice hα hJet hτ
  have h := measurable_deriv_with_param (𝕜 := ℝ) (f := fun z : ℝ => fun θ : ℝ =>
      clampSlice g τ z θ) (by simpa [Function.uncurry_def] using hcont)
  simpa using h

/-- Off the angular line `θ = 0` and for `z > 0`, the derivative of the clamped slice is the
angular derivative of the perturbation (up to the reflection of a negative angle). -/
theorem deriv_clampSlice_eq {g : ℝ → ℝ → ℝ → ℝ} {τ z θ : ℝ} (hz : 0 < z)
    (hθ1 : θ ≠ 0) (hθ2 : |θ| < Real.pi / 2) :
    |deriv (fun θ' => clampSlice g τ z θ') θ|
      = |Work.Spaces.pth (Work.FTS.Regularity.gSlice g τ) z (|θ| : ℝ)| := by
  have hmaxz : max z 0 = z := max_eq_left hz.le
  have habs : 0 < |θ| := abs_pos.mpr hθ1
  have hmem : ∀ᶠ θ' in 𝓝 θ, 0 < |θ'| ∧ |θ'| < Real.pi / 2 := by
    have h1 : {θ' : ℝ | θ' ≠ 0} ∈ 𝓝 θ := isOpen_ne.mem_nhds hθ1
    have h2 : {θ' : ℝ | |θ'| < Real.pi / 2} ∈ 𝓝 θ :=
      (isOpen_lt continuous_abs continuous_const).mem_nhds hθ2
    filter_upwards [h1, h2] with θ' h1' h2'
    exact ⟨abs_pos.mpr h1', h2'⟩
  by_cases hpos : 0 < θ
  · -- for positive angles the clamped slice is the slice itself near `θ`
    have heq : (fun θ' => clampSlice g τ z θ') =ᶠ[𝓝 θ]
        (fun θ' => g z θ' τ) := by
      filter_upwards [hmem, isOpen_Ioi.mem_nhds hpos] with θ' hlt hθ'
      have hθ'pos : (0 : ℝ) < θ' := hθ'
      have hmin : min θ' (Real.pi / 2) = θ' :=
        min_eq_left (le_of_lt (abs_lt.mp hlt.2).2)
      simp only [clampSlice, hmaxz, abs_of_pos hθ'pos, hmin]
    rw [Filter.EventuallyEq.deriv_eq heq, abs_of_pos hpos]
    rfl
  · have hneg : θ < 0 := lt_of_le_of_ne (not_lt.mp hpos) hθ1
    have heq : (fun θ' => clampSlice g τ z θ') =ᶠ[𝓝 θ]
        (fun θ' => g z (-θ') τ) := by
      filter_upwards [hmem, IsOpen.mem_nhds isOpen_Iio hneg] with θ' hlt hθ'
      have hneg' : θ' < 0 := hθ'
      have hmin : min (-θ') (Real.pi / 2) = -θ' :=
        min_eq_left (le_of_lt (by linarith [(abs_lt.mp hlt.2).1]))
      simp only [clampSlice, hmaxz, abs_of_neg hneg', hmin]
    rw [Filter.EventuallyEq.deriv_eq heq, abs_of_neg hneg]
    have hcomp : deriv (fun θ' => g z (-θ') τ) θ
        = -deriv (fun θ' => g z θ' τ) (-θ) :=
      deriv_comp_neg (fun θ' => g z θ' τ) θ
    rw [hcomp, abs_neg]
    rfl

/-- **`(z,θ) ↦ |∂_θ g(z,|θ|,τ)|` is a.e. strongly measurable on the half-strip.** -/
theorem aestronglyMeasurable_abs_pth_gSlice {α S Ng : ℝ} {g : ℝ → ℝ → ℝ → ℝ} (hα : 0 < α)
    (hJet : Work.FTS.Regularity.Jet α S Ng g) {τ : ℝ} (hτ : τ ∈ Set.Icc 0 S) :
    AEStronglyMeasurable (fun p : ℝ × ℝ =>
        |Work.Spaces.pth (Work.FTS.Regularity.gSlice g τ) p.1 (|p.2| : ℝ)|)
      (MeasureTheory.volume.restrict (Set.Ioi 0 ×ˢ Set.Ioo (-(Real.pi / 2)) (Real.pi / 2))) := by
  have hSmeas : MeasurableSet (Set.Ioi (0 : ℝ) ×ˢ Set.Ioo (-(Real.pi / 2)) (Real.pi / 2)) :=
    measurableSet_Ioi.prod measurableSet_Ioo
  have hmeas : Measurable (fun p : ℝ × ℝ =>
      |deriv (fun θ' => clampSlice g τ p.1 θ') p.2|) :=
    (measurable_deriv_clampSlice hα hJet hτ).norm
  refine hmeas.aestronglyMeasurable.congr ?_
  have hnull : (MeasureTheory.volume : MeasureTheory.Measure (ℝ × ℝ))
      ({p : ℝ × ℝ | p.2 = 0}
        ∩ (Set.Ioi 0 ×ˢ Set.Ioo (-(Real.pi / 2)) (Real.pi / 2))) = 0 := by
    have hsub : ({p : ℝ × ℝ | p.2 = 0}
        ∩ (Set.Ioi 0 ×ˢ Set.Ioo (-(Real.pi / 2)) (Real.pi / 2)))
        ⊆ (Set.univ : Set ℝ) ×ˢ ({0} : Set ℝ) := by
      rintro ⟨z, θ⟩ ⟨hθ, _⟩
      exact ⟨trivial, hθ⟩
    refine measure_mono_null hsub ?_
    change ((MeasureTheory.volume : MeasureTheory.Measure ℝ).prod MeasureTheory.volume)
      ((Set.univ : Set ℝ) ×ˢ ({0} : Set ℝ)) = 0
    rw [Measure.prod_prod, measure_singleton, mul_zero]
  change ∀ᵐ p ∂(MeasureTheory.volume.restrict
      (Set.Ioi 0 ×ˢ Set.Ioo (-(Real.pi / 2)) (Real.pi / 2))),
    |deriv (fun θ' => clampSlice g τ p.1 θ') p.2|
      = |Work.Spaces.pth (Work.FTS.Regularity.gSlice g τ) p.1 (|p.2| : ℝ)|
  rw [MeasureTheory.ae_restrict_iff' hSmeas, MeasureTheory.ae_iff]
  refine measure_mono_null ?_ hnull
  intro p hp
  simp only [Set.mem_setOf_eq, not_imp, Set.mem_inter_iff] at hp
  obtain ⟨hpS, hpne⟩ := hp
  refine ⟨?_, hpS⟩
  by_contra hθ0
  exact hpne (deriv_clampSlice_eq hpS.1 hθ0 (abs_lt.mpr hpS.2))

end Work.FTS.PressureOn
