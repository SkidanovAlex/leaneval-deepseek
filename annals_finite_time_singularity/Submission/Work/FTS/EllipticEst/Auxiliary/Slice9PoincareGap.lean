import Mathlib.Analysis.Calculus.ContDiff.Defs
import Mathlib.Analysis.LocallyConvex.AbsConvexOpen
import Mathlib.MeasureTheory.Integral.IntervalIntegral.FundThmCalculus
import Submission.Work.Spaces.Defs
import Submission.Work.FTS.EllipticEst.AngGap.Defs
import Submission.Work.FTS.EllipticEst.AngGap.HardySetup
import Submission.Work.FTS.EllipticEst.AngGap.hBounds
import Submission.Work.FTS.EllipticEst.AngGap.stepD
import Submission.Work.FTS.EllipticEst.AngGap.ibp
import Submission.Work.FTS.EllipticEst.AngGap.assembly
import Submission.Work.FTS.EllipticEst.AngGap.int_sinSq_le_cube
import Submission.Work.FTS.EllipticEst.AngGap.int_sinSq_shift
import Submission.Work.FTS.EllipticEst.AngGap.PhiHCalc.deriv_angPhiH
import Submission.Work.FTS.EllipticEst.AngGap.PhiHCalc.tendsto_angPhiH_left
import Submission.Work.FTS.EllipticEst.AngGap.PhiHCalc.tendsto_angPhiH_right
import Submission.Work.FTS.EllipticEst.AngGap.PhiHCalc.integrable_pieces
import Submission.Work.FTS.EllipticEst.Auxiliary.Slice9PoincareDefs
import Submission.Work.FTS.EllipticEst.Auxiliary.Slice9PoincareMain

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

noncomputable section

open scoped Real Topology
open MeasureTheory Set Filter
open Work.FTS.EllipticEst.AngGap

namespace Work.FTS.EllipticEst.P9

set_option autoImplicit false

/-! ## The angular gap-Wirtinger inequality, around the shared `AngGap` development

The sibling development `Submission/Work/FTS/EllipticEst/AngGap/` proves the pieces of the
sharp gap inequality on the orthogonal complement of `sin 2θ`:

* `AngGap.hBounds`: `|h θ| ≤ C sin 2θ` and `|deriv h θ| ≤ C` on `[0,π/2]`;
* `AngGap.stepD`: `∫ Q² = ∫ h'² - 4 ∫ h²` for `Q = h' - 2 cot(2θ) h`;
* `AngGap.ibp`: `∫ h² = -∫ V Q` for `V = angG h / sin 2θ`;
* `AngGap.assembly`: the final Cauchy–Schwarz + arithmetic step, given `12 ∫ V² ≤ ∫ h²`;
* `AngGap.PhiHCalc.*`: the weighted Hardy inequality `12 ∫ V² ≤ ∫ h²` (the pointwise
  derivative of the antiderivative `6 V² cot 2θ`, its vanishing at both endpoints and the
  interval-integrability of the three pieces) — everything except the final assembly;
* `AngGap.primProps`: the primitive facts about `angG h` (the other half of the route), whose
  proof is complete except for two elementary integral estimates that are proved separately
  in `AngGap.int_sinSq_le_cube` and `AngGap.int_sinSq_shift`.

This file re-does those last two assembly steps *here* (so that this development does not
depend on the two in-flight files, whose proofs are not yet finished) and derives the gap
inequality. -/

/-- The primitive facts about `G = angG h`: its derivative is `h · sin 2θ` on `(0,π/2)`, it
vanishes at both endpoints (the mean-zero condition), and it is `O((sin 2θ)³)`.  The two
elementary integral estimates are taken from the proved siblings
`AngGap.int_sinSq_le_cube` and `AngGap.int_sinSq_shift`. -/
theorem primPropsP9 (h : ℝ → ℝ) (hh : ContDiffOn ℝ 2 h (Set.Icc 0 (π / 2)))
    (hme : ∫ θ in Work.Spaces.Iθ, h θ * Real.sin (2 * θ) = 0)
    (C : ℝ) (hC : 0 < C) (hbdd : ∀ θ ∈ Set.Icc 0 (π / 2), |h θ| ≤ C * Real.sin (2 * θ)) :
    (∀ θ ∈ Set.Ioo 0 (π / 2), HasDerivAt (angG h) (h θ * Real.sin (2 * θ)) θ)
      ∧ angG h 0 = 0 ∧ angG h (π / 2) = 0
      ∧ (∃ C' : ℝ, 0 < C' ∧ ∀ θ ∈ Set.Icc 0 (π / 2),
            |angG h θ| ≤ C' * (Real.sin (2 * θ)) ^ 3) := by
  have int_sinSq_le_cube : ∀ v ∈ Set.Icc (0 : ℝ) (π / 4),
      ∫ t in (0 : ℝ)..v, (Real.sin (2 * t)) ^ 2
        ≤ 4 * (π / 4) ^ 3 * (Real.sin (2 * v)) ^ 3 :=
    fun v hv => Work.FTS.EllipticEst.AngGap.int_sinSq_le_cube v hv
  have int_sinSq_shift : ∀ θ : ℝ, ∫ s in θ..(π / 2), (Real.sin (2 * s)) ^ 2
      = ∫ t in (0 : ℝ)..(π / 2 - θ), (Real.sin (2 * t)) ^ 2 :=
    fun θ => Work.FTS.EllipticEst.AngGap.int_sinSq_shift θ
  -- the integrand and its continuity
  have hcont : ContinuousOn (fun s : ℝ => h s * Real.sin (2 * s)) (Set.Icc 0 (π / 2)) := by
    refine hh.continuousOn.mul ?_
    fun_prop
  -- the mean-zero condition as an interval integral
  have hzero : ∫ s in (0 : ℝ)..(π / 2), h s * Real.sin (2 * s) = 0 := by
    rw [intervalIntegral.integral_of_le (by positivity : (0 : ℝ) ≤ π / 2),
      ← MeasureTheory.integral_Icc_eq_integral_Ioc]
    have : Work.Spaces.Iθ = Set.Icc (0 : ℝ) (π / 2) := rfl
    rw [← this]
    exact hme
  have hπ : angG h (π / 2) = 0 := hzero
  refine ⟨?_, by simp [angG], hπ, ?_⟩
  · -- the derivative
    intro θ hθ
    have hsub : Set.uIcc (0 : ℝ) θ ⊆ Set.Icc 0 (π / 2) := by
      rw [Set.uIcc_of_le (le_of_lt hθ.1)]
      exact Set.Icc_subset_Icc le_rfl hθ.2.le
    have hint : IntervalIntegrable (fun s : ℝ => h s * Real.sin (2 * s)) volume 0 θ :=
      (hcont.mono hsub).intervalIntegrable
    have hmem : Set.Icc (0 : ℝ) (π / 2) ∈ 𝓝 θ :=
      Filter.mem_of_superset (Ioo_mem_nhds hθ.1 hθ.2) Set.Ioo_subset_Icc_self
    have hcontAt : ContinuousAt (fun s : ℝ => h s * Real.sin (2 * s)) θ :=
      hcont.continuousAt hmem
    have hmeas : StronglyMeasurableAtFilter (fun s : ℝ => h s * Real.sin (2 * s)) (𝓝 θ) volume :=
      ContinuousOn.stronglyMeasurableAtFilter isOpen_interior (hcont.mono interior_subset) θ
        (by simpa [interior_Icc] using hθ)
    exact intervalIntegral.integral_hasDerivAt_right hint hmeas hcontAt
  · -- the bound
    refine ⟨C * (4 * (π / 4) ^ 3), by positivity, fun θ hθ => ?_⟩
    have hsubI : Set.uIcc (0 : ℝ) θ ⊆ Set.Icc 0 (π / 2) := by
      rw [Set.uIcc_of_le hθ.1]
      exact Set.Icc_subset_Icc le_rfl hθ.2
    have hsubJ : Set.uIcc θ (π / 2) ⊆ Set.Icc 0 (π / 2) := by
      rw [Set.uIcc_of_le hθ.2]
      exact Set.Icc_subset_Icc hθ.1 le_rfl
    -- pointwise domination of the integrand by `C sin²2s`
    have hpt : ∀ s ∈ Set.Icc (0 : ℝ) (π / 2),
        |h s * Real.sin (2 * s)| ≤ C * (Real.sin (2 * s)) ^ 2 := by
      intro s hs
      have hsin_nonneg : 0 ≤ Real.sin (2 * s) :=
        Real.sin_nonneg_of_mem_Icc ⟨by linarith [hs.1], by linarith [hs.2, Real.pi_pos]⟩
      rw [abs_mul, abs_of_nonneg hsin_nonneg]
      calc |h s| * Real.sin (2 * s) ≤ (C * Real.sin (2 * s)) * Real.sin (2 * s) :=
            mul_le_mul_of_nonneg_right (hbdd s hs) hsin_nonneg
        _ = C * (Real.sin (2 * s)) ^ 2 := by ring
    have hstepA : |angG h θ| ≤ C * ∫ s in (0)..θ, (Real.sin (2 * s)) ^ 2 := by
      have hfi : IntervalIntegrable (fun s : ℝ => |h s * Real.sin (2 * s)|) volume 0 θ :=
        (hcont.abs.mono hsubI).intervalIntegrable
      have hgi : IntervalIntegrable (fun s : ℝ => C * (Real.sin (2 * s)) ^ 2) volume 0 θ := by
        have hc : ContinuousOn (fun s : ℝ => C * (Real.sin (2 * s)) ^ 2) (Set.Icc 0 (π / 2)) := by
          fun_prop
        exact (hc.mono hsubI).intervalIntegrable
      have h1 : |∫ s in (0)..θ, h s * Real.sin (2 * s)|
          ≤ ∫ s in (0)..θ, |h s * Real.sin (2 * s)| :=
        intervalIntegral.abs_integral_le_integral_abs hθ.1
      have h2 : ∫ s in (0)..θ, |h s * Real.sin (2 * s)|
          ≤ ∫ s in (0)..θ, C * (Real.sin (2 * s)) ^ 2 :=
        intervalIntegral.integral_mono_on hθ.1 hfi hgi
          (fun s hs => hpt s ⟨hs.1, le_trans hs.2 hθ.2⟩)
      have h3 : ∫ s in (0)..θ, C * (Real.sin (2 * s)) ^ 2
          = C * ∫ s in (0)..θ, (Real.sin (2 * s)) ^ 2 :=
        intervalIntegral.integral_const_mul C _
      simp only [angG]
      rw [h3] at h2
      exact le_trans h1 h2
    have hstepB : |angG h θ| ≤ C * ∫ s in θ..(π / 2), (Real.sin (2 * s)) ^ 2 := by
      have hfi : IntervalIntegrable (fun s : ℝ => |h s * Real.sin (2 * s)|) volume θ (π / 2) :=
        (hcont.abs.mono hsubJ).intervalIntegrable
      have hgi : IntervalIntegrable (fun s : ℝ => C * (Real.sin (2 * s)) ^ 2) volume θ (π / 2) := by
        have hc : ContinuousOn (fun s : ℝ => C * (Real.sin (2 * s)) ^ 2) (Set.Icc 0 (π / 2)) := by
          fun_prop
        exact (hc.mono hsubJ).intervalIntegrable
      have hfi0 : IntervalIntegrable (fun s : ℝ => h s * Real.sin (2 * s)) volume θ (π / 2) :=
        (hcont.mono hsubJ).intervalIntegrable
      have hsplt : (∫ s in (0)..θ, h s * Real.sin (2 * s))
          + ∫ s in θ..(π / 2), h s * Real.sin (2 * s) = 0 := by
        rw [intervalIntegral.integral_add_adjacent_intervals
          ((hcont.mono hsubI).intervalIntegrable) hfi0, hzero]
      have heq : angG h θ = - ∫ s in θ..(π / 2), h s * Real.sin (2 * s) := by
        show (∫ s in (0)..θ, h s * Real.sin (2 * s)) = _
        linarith
      rw [heq, abs_neg]
      have h1 : |∫ s in θ..(π / 2), h s * Real.sin (2 * s)|
          ≤ ∫ s in θ..(π / 2), |h s * Real.sin (2 * s)| :=
        intervalIntegral.abs_integral_le_integral_abs hθ.2
      have h2 : ∫ s in θ..(π / 2), |h s * Real.sin (2 * s)|
          ≤ ∫ s in θ..(π / 2), C * (Real.sin (2 * s)) ^ 2 :=
        intervalIntegral.integral_mono_on hθ.2 hfi hgi
          (fun s hs => hpt s ⟨le_trans hθ.1 hs.1, hs.2⟩)
      have h3 : ∫ s in θ..(π / 2), C * (Real.sin (2 * s)) ^ 2
          = C * ∫ s in θ..(π / 2), (Real.sin (2 * s)) ^ 2 :=
        intervalIntegral.integral_const_mul C _
      rw [h3] at h2
      exact le_trans h1 h2
    by_cases hcase : θ ≤ π / 4
    · -- left half
      have hA : θ ∈ Set.Icc (0 : ℝ) (π / 4) := ⟨hθ.1, hcase⟩
      calc |angG h θ| ≤ C * ∫ s in (0)..θ, (Real.sin (2 * s)) ^ 2 := hstepA
        _ ≤ C * (4 * (π / 4) ^ 3 * (Real.sin (2 * θ)) ^ 3) :=
            mul_le_mul_of_nonneg_left (int_sinSq_le_cube θ hA) hC.le
        _ = (C * (4 * (π / 4) ^ 3)) * (Real.sin (2 * θ)) ^ 3 := by ring
    · -- right half: reflect in `π/4`
      have hcase' : π / 4 < θ := not_le.mp hcase
      have hu : π / 2 - θ ∈ Set.Icc (0 : ℝ) (π / 4) :=
        ⟨by linarith [hθ.2], by linarith [hcase']⟩
      have hcube := int_sinSq_le_cube (π / 2 - θ) hu
      have hsin_eq : Real.sin (2 * (π / 2 - θ)) = Real.sin (2 * θ) := by
        rw [show 2 * (π / 2 - θ) = π - 2 * θ by ring, Real.sin_pi_sub]
      rw [hsin_eq] at hcube
      calc |angG h θ| ≤ C * ∫ s in θ..(π / 2), (Real.sin (2 * s)) ^ 2 := hstepB
        _ = C * ∫ t in (0)..(π / 2 - θ), (Real.sin (2 * t)) ^ 2 := by rw [int_sinSq_shift θ]
        _ ≤ C * (4 * (π / 4) ^ 3 * (Real.sin (2 * θ)) ^ 3) :=
            mul_le_mul_of_nonneg_left hcube hC.le
        _ = (C * (4 * (π / 4) ^ 3)) * (Real.sin (2 * θ)) ^ 3 := by ring

/-- **The weighted Hardy inequality** `12 ∫ V² ≤ ∫ h²` for `V = angG h / sin 2θ`.

The exact identity `h² - 12 V² - (h - 6 cot(2θ) V)² = (6 V² cot(2θ))'` on `(0,π/2)` is
integrated over `[0,π/2]`: the antiderivative `angPhiH h = 6 V² cot 2θ` vanishes at both
endpoints and the integrand `angF h` is interval-integrable, so
`∫ (h² - 12 V²) = ∫ (h - 6 cot 2θ V)² ≥ 0`. -/
theorem hardyP9 (h : ℝ → ℝ) (hh : ContDiffOn ℝ 2 h (Set.Icc 0 (π / 2)))
    (hg : ∀ θ ∈ Set.Ioo 0 (π / 2), HasDerivAt (angG h) (h θ * Real.sin (2 * θ)) θ)
    (C : ℝ) (hC : 0 < C)
    (hbdd : ∀ θ ∈ Set.Icc 0 (π / 2), |h θ| ≤ C * Real.sin (2 * θ))
    (hCg : ∀ θ ∈ Set.Icc 0 (π / 2), |angG h θ| ≤ C * (Real.sin (2 * θ)) ^ 3) :
    12 * (∫ θ in Work.Spaces.Iθ, (angV h θ) ^ 2) ≤ ∫ θ in Work.Spaces.Iθ, (h θ) ^ 2 := by
  have hlt : (0 : ℝ) < π / 2 := by positivity
  -- the pointwise derivative identity
  have hΦderiv : ∀ θ ∈ Set.Ioo 0 (π / 2), HasDerivAt (angPhiH h) (angF h θ) θ :=
    fun θ hθ => (Work.FTS.EllipticEst.AngGap.PhiHCalc.deriv_angPhiH h hg θ hθ).2
  -- integrability of the pieces, and of `angF h`
  obtain ⟨hInt1, hInt2, hInt3⟩ :=
    Work.FTS.EllipticEst.AngGap.PhiHCalc.integrable_pieces h hh hg C hC hbdd hCg
  have hInt12 : IntervalIntegrable (fun y : ℝ => (h y) ^ 2 - 12 * (angV h y) ^ 2)
      volume 0 (π / 2) := IntervalIntegrable.sub hInt1 (IntervalIntegrable.const_mul hInt2 12)
  have hIntF : IntervalIntegrable (angF h) volume 0 (π / 2) :=
    IntervalIntegrable.sub hInt12 hInt3
  -- the fundamental theorem of calculus for `angPhiH h`
  have hFTC : (∫ y in (0 : ℝ)..(π / 2), angF h y) = 0 := by
    have h := intervalIntegral.integral_eq_sub_of_hasDerivAt_of_tendsto (a := (0 : ℝ))
      (b := π / 2) (f := angPhiH h) (f' := angF h) (fa := 0) (fb := 0) hlt hΦderiv hIntF
      (Work.FTS.EllipticEst.AngGap.PhiHCalc.tendsto_angPhiH_right h C hC hCg)
      (Work.FTS.EllipticEst.AngGap.PhiHCalc.tendsto_angPhiH_left h C hC hCg)
    simpa using h
  -- splitting the integral
  have hconv : (∫ y in (0 : ℝ)..(π / 2), angF h y)
      = ∫ y in (0 : ℝ)..(π / 2), ((h y) ^ 2 - 12 * (angV h y) ^ 2) - angFt h y :=
    intervalIntegral.integral_congr (fun y _ => angF_eq_sub h y)
  have hs1 : (∫ y in (0 : ℝ)..(π / 2), ((h y) ^ 2 - 12 * (angV h y) ^ 2) - angFt h y)
      = (∫ y in (0 : ℝ)..(π / 2), ((h y) ^ 2 - 12 * (angV h y) ^ 2))
        - ∫ y in (0 : ℝ)..(π / 2), angFt h y :=
    intervalIntegral.integral_sub (f := fun y : ℝ => (h y) ^ 2 - 12 * (angV h y) ^ 2)
      (g := angFt h) hInt12 hInt3
  have hs2 : (∫ y in (0 : ℝ)..(π / 2), ((h y) ^ 2 - 12 * (angV h y) ^ 2))
      = (∫ y in (0 : ℝ)..(π / 2), (h y) ^ 2)
        - 12 * (∫ y in (0 : ℝ)..(π / 2), (angV h y) ^ 2) := by
    rw [intervalIntegral.integral_sub (f := fun y : ℝ => (h y) ^ 2)
        (g := fun y : ℝ => 12 * (angV h y) ^ 2) hInt1
        (IntervalIntegrable.const_mul hInt2 12),
      intervalIntegral.integral_const_mul]
  have hFt_nonneg : 0 ≤ ∫ y in (0 : ℝ)..(π / 2), angFt h y :=
    intervalIntegral.integral_nonneg hlt.le (fun y _ => angFt_nonneg h y)
  rw [Iθ_eq_interval (fun θ => (angV h θ) ^ 2), Iθ_eq_interval (fun θ => (h θ) ^ 2)]
  linarith [hFTC, hconv, hs1, hs2, hFt_nonneg]

/-- **The angular gap-Wirtinger inequality**: a `C²` function on `[0,π/2]` vanishing at both
endpoints whose first sine mode vanishes satisfies `16 ∫ h² ≤ ∫ (h')²`. -/
theorem gapP9 (h : ℝ → ℝ) (hh : ContDiffOn ℝ 2 h (Set.Icc 0 (π / 2))) (h0 : h 0 = 0)
    (h1 : h (π / 2) = 0) (hmean : (∫ θ in Work.Spaces.Iθ, h θ * Real.sin (2 * θ)) = 0) :
    16 * (∫ θ in Work.Spaces.Iθ, (h θ) ^ 2) ≤ ∫ θ in Work.Spaces.Iθ, (deriv h θ) ^ 2 := by
  obtain ⟨C, hCpos, hbdd, hbdd'⟩ := hBounds h hh h0 h1
  obtain ⟨hg, -, -, hRest⟩ := primPropsP9 h hh hmean C hCpos hbdd
  obtain ⟨Cg, hCgpos, hCg⟩ := hRest
  -- a single constant dominating both `C` and the constant of the cubic bound of `angG h`
  set Cm : ℝ := max C Cg with hCmdef
  have hCm : 0 < Cm := by rw [hCmdef]; exact lt_of_lt_of_le hCpos (le_max_left C Cg)
  have hCCm : C ≤ Cm := by rw [hCmdef]; exact le_max_left C Cg
  have hCgCm : Cg ≤ Cm := by rw [hCmdef]; exact le_max_right C Cg
  have hbddC : ∀ θ ∈ Set.Icc 0 (π / 2), |h θ| ≤ Cm * Real.sin (2 * θ) := by
    intro θ hθ
    have hs : 0 ≤ Real.sin (2 * θ) := Real.sin_nonneg_of_mem_Icc
      ⟨by linarith [hθ.1], by linarith [hθ.2, Real.pi_pos]⟩
    exact le_trans (hbdd θ hθ) (mul_le_mul_of_nonneg_right hCCm hs)
  have hbdd'C : ∀ θ ∈ Set.Ioo 0 (π / 2), |deriv h θ| ≤ Cm :=
    fun θ hθ => le_trans (hbdd' θ hθ) hCCm
  have hCgC : ∀ θ ∈ Set.Icc 0 (π / 2), |angG h θ| ≤ Cm * (Real.sin (2 * θ)) ^ 3 := by
    intro θ hθ
    have hs : 0 ≤ (Real.sin (2 * θ)) ^ 3 := pow_nonneg (Real.sin_nonneg_of_mem_Icc
      ⟨by linarith [hθ.1], by linarith [hθ.2, Real.pi_pos]⟩) 3
    exact le_trans (hCg θ hθ) (mul_le_mul_of_nonneg_right hCgCm hs)
  exact assembly h hh Cm hCm hbddC hbdd'C hg Cm hCm hCgC
    (stepD h hh h0 h1 Cm hCm hbddC hbdd'C)
    (hardyP9 h hh hg Cm hCm hbddC hCgC)
    (ibp h hh hg Cm hCm hbddC hbdd'C hCgC)

/-- **The constrained slice Poincaré inequality, constant `9`** (Elgindi, Annals 194 (3)
2021): for `f` of class `C²` on `[0,π/2]` with `f 0 = f (π/2) = 0` and
`∫_{Iθ} f θ · sinθcos²θ dθ = 0`, one has `9 ∫_{Iθ} f² ≤ ∫_{Iθ} (f')²`. -/
theorem slicePoincare9_fts : ∀ f : ℝ → ℝ, ContDiffOn ℝ 2 f (Set.Icc 0 (π / 2)) → f 0 = 0 →
    f (π / 2) = 0 → (∫ θ in Work.Spaces.Iθ, f θ * Work.Elliptic.sinCos2 θ) = 0 →
    9 * (∫ θ in Work.Spaces.Iθ, (f θ) ^ 2) ≤ ∫ θ in Work.Spaces.Iθ, (deriv f θ) ^ 2 :=
  fun f hf h0 h1 horth => slicePoincare9_of_gap gapP9 f hf h0 h1 horth

end Work.FTS.EllipticEst.P9
