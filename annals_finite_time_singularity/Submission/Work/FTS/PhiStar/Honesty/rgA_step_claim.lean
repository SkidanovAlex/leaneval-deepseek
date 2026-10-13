/-
# `Work.FTS.PhiStar.Honesty.rgA_step_claim`

The forward primitive `rgA α m c z = ∫_0^z c t · t^{q-1} dt` (with `q = rgQ α m = (2m+5)/α > 0`)
of the radial Green function, under the *pointwise* hypothesis

  `|c t| ≤ ε · t^{3/2}`  for `0 < t ≤ δ`      (`hvy`)

satisfies, for every `z > 0` with `2z ≤ δ`, a right-hand "step" statement: there is a number
`cA` with `|cA| ≤ ε·z^{q+3/2}/(q+3/2)` which approximates `rgA α m c (z+h)` to first order in
`h`:

  `|rgA α m c (z+h) - cA| ≤ h · ε · (2z)^{q+1/2}`   for `0 < h ≤ h₀`.

The natural candidate `cA = rgA α m c z` works whenever the integrand `rgF1 = c·t^{q-1}` is
integrable on a right-neighbourhood `(0, z+h₁]` of `0`: then the difference is the integral of
`rgF1` over `(z, z+h]`, dominated by `ε·t^{q+1/2} ≤ ε·(2z)^{q+1/2}`, and the value of `rgA z` is
bounded by the corresponding majorant integral `ε·z^{q+3/2}/(q+3/2)`.

The only subtlety of the *honest* (measurability-free) formulation is that `c` carries **no**
measurability hypothesis, so `rgF1` may fail to be a.e. strongly measurable near `0`; then
`rgA α m c (z+h) = 0` (the Bochner integral of a non-integrable function vanishes) for every
`h > 0`, and the claim holds with `cA = 0`.  The dichotomy used below is therefore on
`IntegrableOn (rgF1) (Ioc 0 (z+h₁))` for some `h₁ > 0`, not on measurability of `c`.
-/
import Mathlib.Analysis.SpecialFunctions.Integrals.Basic
import Submission.Work.FTS.EllExist.RadGreenDefs

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

noncomputable section
open scoped Real Topology
open MeasureTheory Set Filter

namespace Work.FTS.PhiStar.Honesty

set_option autoImplicit false
set_option linter.unusedVariables false

/-- The pointwise bound for the integrand `rgF1 α m c t = c t · t^{q-1}` on `(0, δ]`: the
hypothesis `|c t| ≤ ε t^{3/2}` upgrades to `|rgF1 t| ≤ ε t^{q+1/2}` because the exponents add. -/
private lemma rgF1_norm_le {α : ℝ} {m : ℕ} {c : ℝ → ℝ} {ε δ : ℝ}
    (hvy : ∀ t : ℝ, 0 < t → t ≤ δ → |c t| ≤ ε * t ^ ((3 : ℝ) / 2))
    {t : ℝ} (ht0 : 0 < t) (htδ : t ≤ δ) :
    ‖Work.FTS.EllExist.rgF1 α m c t‖ ≤ ε * t ^ (Work.FTS.EllExist.rgQ α m + 1 / 2) := by
  rw [Real.norm_eq_abs, Work.FTS.EllExist.rgF1, abs_mul, abs_of_pos (Real.rpow_pos_of_pos ht0 _)]
  calc |c t| * t ^ (Work.FTS.EllExist.rgQ α m - 1)
      ≤ (ε * t ^ ((3 : ℝ) / 2)) * t ^ (Work.FTS.EllExist.rgQ α m - 1) :=
        mul_le_mul_of_nonneg_right (hvy t ht0 htδ)
          (le_of_lt (Real.rpow_pos_of_pos ht0 _))
    _ = ε * t ^ (Work.FTS.EllExist.rgQ α m + 1 / 2) := by
        rw [mul_assoc, ← Real.rpow_add ht0,
          show (3 : ℝ) / 2 + (Work.FTS.EllExist.rgQ α m - 1) = Work.FTS.EllExist.rgQ α m + 1 / 2
            from by ring]

/-- The value bound for the forward primitive: on `(0, δ]` it is dominated by the integral of
its majorant, `ε z^{q+3/2}/(q+3/2)`.  No integrability of `rgF1` is needed:
`intervalIntegral.norm_integral_le_of_norm_le` only wants an interval-integrable majorant. -/
private lemma rgA_norm_le {α : ℝ} {m : ℕ} {c : ℝ → ℝ} {ε δ : ℝ}
    (hα : 0 < α)
    (hvy : ∀ t : ℝ, 0 < t → t ≤ δ → |c t| ≤ ε * t ^ ((3 : ℝ) / 2))
    {z : ℝ} (hz : 0 < z) (hzδ : z ≤ δ) :
    ‖Work.FTS.EllExist.rgA α m c z‖
      ≤ ε * z ^ (Work.FTS.EllExist.rgQ α m + 3 / 2) / (Work.FTS.EllExist.rgQ α m + 3 / 2) := by
  rw [Work.FTS.EllExist.rgA, Real.norm_eq_abs]
  have hq : 0 < Work.FTS.EllExist.rgQ α m := Work.FTS.EllExist.rgQ_pos hα m
  have hr : (-1 : ℝ) < Work.FTS.EllExist.rgQ α m + 1 / 2 := by linarith
  have hII : IntervalIntegrable (fun t : ℝ => ε * t ^ (Work.FTS.EllExist.rgQ α m + 1 / 2))
      volume (0:ℝ) z := (intervalIntegral.intervalIntegrable_rpow' hr).const_mul ε
  have hbound := intervalIntegral.norm_integral_le_of_norm_le (le_of_lt hz)
    (Filter.Eventually.of_forall fun t ht => rgF1_norm_le hvy ht.1 (le_trans ht.2 hzδ)) hII
  have hval : ∫ t in (0:ℝ)..z, ε * t ^ (Work.FTS.EllExist.rgQ α m + 1 / 2)
      = ε * z ^ (Work.FTS.EllExist.rgQ α m + 3 / 2) / (Work.FTS.EllExist.rgQ α m + 3 / 2) := by
    rw [intervalIntegral.integral_const_mul,
      integral_rpow (a := (0:ℝ)) (b := z) (r := Work.FTS.EllExist.rgQ α m + 1 / 2) (Or.inl hr),
      Real.zero_rpow (by linarith : Work.FTS.EllExist.rgQ α m + 1 / 2 + 1 ≠ 0),
      show Work.FTS.EllExist.rgQ α m + 1 / 2 + 1 = Work.FTS.EllExist.rgQ α m + 3 / 2 from by ring]
    ring
  rw [hval] at hbound
  simpa [Real.norm_eq_abs] using hbound

theorem rgA_step_claim {α : ℝ} {m : ℕ} {c : ℝ → ℝ} {ε δ : ℝ}
    (hα : 0 < α) (hδ : 0 < δ) (hε : 0 ≤ ε)
    (hvy : ∀ t : ℝ, 0 < t → t ≤ δ → |c t| ≤ ε * t ^ ((3 : ℝ) / 2)) :
    ∀ z : ℝ, 0 < z → 2 * z ≤ δ →
      ∃ cA : ℝ,
        |cA| ≤ ε * z ^ (Work.FTS.EllExist.rgQ α m + 3 / 2) / (Work.FTS.EllExist.rgQ α m + 3 / 2)
        ∧ ∃ h₀ : ℝ, 0 < h₀ ∧ ∀ h : ℝ, 0 < h → h ≤ h₀ →
            |Work.FTS.EllExist.rgA α m c (z + h) - cA|
              ≤ h * (ε * (2 * z) ^ (Work.FTS.EllExist.rgQ α m + 1 / 2)) := by
  intro z hz h2z
  have hzδ : z ≤ δ := by linarith
  have hq : 0 < Work.FTS.EllExist.rgQ α m := Work.FTS.EllExist.rgQ_pos hα m
  by_cases hcase : ∃ h₁ : ℝ, 0 < h₁ ∧
      MeasureTheory.IntegrableOn (Work.FTS.EllExist.rgF1 α m c) (Set.Ioc 0 (z + h₁))
  · -- the integrand is integrable on a right-neighbourhood of `0`: use `cA = rgA z` and the FTC
    obtain ⟨h₁, hh₁, hInt₁⟩ := hcase
    refine ⟨Work.FTS.EllExist.rgA α m c z, ?_, min h₁ z, lt_min hh₁ hz, ?_⟩
    · exact rgA_norm_le hα hvy hz hzδ
    · intro h hh0 hhle
      have hle₁ : h ≤ h₁ := le_trans hhle (min_le_left _ _)
      have hlez : h ≤ z := le_trans hhle (min_le_right _ _)
      have hInt : MeasureTheory.IntegrableOn (Work.FTS.EllExist.rgF1 α m c) (Set.Ioc 0 (z + h)) :=
        hInt₁.mono_set (Set.Ioc_subset_Ioc_right (by linarith : z + h ≤ z + h₁))
      have hII1 : IntervalIntegrable (Work.FTS.EllExist.rgF1 α m c) volume (0:ℝ) (z + h) :=
        (intervalIntegrable_iff_integrableOn_Ioc_of_le (by linarith : (0:ℝ) ≤ z + h)).mpr hInt
      have hII2 : IntervalIntegrable (Work.FTS.EllExist.rgF1 α m c) volume (0:ℝ) z :=
        (intervalIntegrable_iff_integrableOn_Ioc_of_le (le_of_lt hz)).mpr
          (hInt.mono_set (Set.Ioc_subset_Ioc_right (by linarith : z ≤ z + h)))
      have hsub := intervalIntegral.integral_interval_sub_left hII1 hII2
      have hconstII : IntervalIntegrable
          (fun _ : ℝ => ε * (2 * z) ^ (Work.FTS.EllExist.rgQ α m + 1 / 2)) volume z (z + h) :=
        intervalIntegrable_const
      have hpt : ∀ t ∈ Set.Ioc z (z + h),
          ‖Work.FTS.EllExist.rgF1 α m c t‖
            ≤ ε * (2 * z) ^ (Work.FTS.EllExist.rgQ α m + 1 / 2) := by
        intro t ht
        have ht0 : 0 < t := lt_trans hz ht.1
        have htδ : t ≤ δ := by linarith [ht.2, hlez, h2z]
        have htz : t ≤ 2 * z := by linarith [ht.2, hlez]
        calc ‖Work.FTS.EllExist.rgF1 α m c t‖
            ≤ ε * t ^ (Work.FTS.EllExist.rgQ α m + 1 / 2) := rgF1_norm_le hvy ht0 htδ
          _ ≤ ε * (2 * z) ^ (Work.FTS.EllExist.rgQ α m + 1 / 2) :=
              mul_le_mul_of_nonneg_left
                (Real.rpow_le_rpow (le_of_lt ht0) htz
                  (by linarith : (0:ℝ) ≤ Work.FTS.EllExist.rgQ α m + 1 / 2))
                hε
      have hbound := intervalIntegral.norm_integral_le_of_norm_le (by linarith : z ≤ z + h)
        (Filter.Eventually.of_forall fun t ht => hpt t ht) hconstII
      have hval : ∫ t in z..(z + h), ε * (2 * z) ^ (Work.FTS.EllExist.rgQ α m + 1 / 2)
          = h * (ε * (2 * z) ^ (Work.FTS.EllExist.rgQ α m + 1 / 2)) := by
        rw [intervalIntegral.integral_const, smul_eq_mul]
        ring
      have hmain : ‖Work.FTS.EllExist.rgA α m c (z + h) - Work.FTS.EllExist.rgA α m c z‖
          ≤ h * (ε * (2 * z) ^ (Work.FTS.EllExist.rgQ α m + 1 / 2)) := by
        rw [show Work.FTS.EllExist.rgA α m c (z + h)
              = ∫ t in (0:ℝ)..(z + h), Work.FTS.EllExist.rgF1 α m c t from rfl,
            show Work.FTS.EllExist.rgA α m c z
              = ∫ t in (0:ℝ)..z, Work.FTS.EllExist.rgF1 α m c t from rfl,
            hsub, Real.norm_eq_abs]
        calc |∫ t in z..(z + h), Work.FTS.EllExist.rgF1 α m c t|
            ≤ ∫ t in z..(z + h), ε * (2 * z) ^ (Work.FTS.EllExist.rgQ α m + 1 / 2) := by
              simpa [Real.norm_eq_abs] using hbound
          _ = h * (ε * (2 * z) ^ (Work.FTS.EllExist.rgQ α m + 1 / 2)) := hval
      rwa [Real.norm_eq_abs] at hmain
  · -- `rgF1` is not integrable on any right-neighbourhood of `0`: all the integrals vanish and
    -- `cA = 0` works
    refine ⟨0, ?_, z, hz, ?_⟩
    · rw [abs_zero]
      exact div_nonneg (mul_nonneg hε (Real.rpow_nonneg (le_of_lt hz) _)) (by linarith)
    · intro h hh0 _
      have hnotint : ¬ MeasureTheory.IntegrableOn (Work.FTS.EllExist.rgF1 α m c) (Set.Ioc 0 (z + h)) :=
        fun hp => hcase ⟨h, hh0, hp⟩
      have hzero : Work.FTS.EllExist.rgA α m c (z + h) = 0 := by
        rw [Work.FTS.EllExist.rgA, intervalIntegral.integral_of_le (by linarith : (0:ℝ) ≤ z + h)]
        exact MeasureTheory.integral_undef hnotint
      rw [hzero, sub_zero, abs_zero]
      exact mul_nonneg (le_of_lt hh0)
        (mul_nonneg hε (Real.rpow_nonneg (by linarith : (0:ℝ) ≤ 2 * z) _))

end Work.FTS.PhiStar.Honesty
