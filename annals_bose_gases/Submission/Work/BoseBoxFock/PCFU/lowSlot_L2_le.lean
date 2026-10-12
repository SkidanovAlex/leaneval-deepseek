import Mathlib.MeasureTheory.Function.L2Space
import Mathlib.Analysis.Normed.Lp.MeasurableSpace
import Mathlib.MeasureTheory.Measure.Haar.OfBasis
import Submission.Work.BoseBoxFock.PCFU.lowSlotMeasurableOfMeasurable
import Submission.Work.BoseFixB3.Conv.stronglyMeasurable_lowMult
import Submission.Work.BoseFixB3.HighMass.highSlot_sq_integral_le
import Submission.Work.BoseFixB3.Split.lowSlotBound
-- PORT435-BEGIN (v4.35 isDefEq respectTransparency compat)
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- PORT435-END

/-!
# `Work.BoseBoxFock.PCFU.lowSlot_L2_le` — the low-momentum slot is an `L²`-contraction

FS's low-momentum localisation on the box is `Q_L = P_Λ · m(√−Δ) · E_Λ`, where `E_Λ` is the
extension by zero off the box `Λ = acube ℓ`, `m(p) = f(‖p‖/κ)` is FS's cut-off (`LowCut`), and
`P_Λ` is the restriction to `Λ`.  With `0 ≤ m ≤ 1`, this is a *compression of a contraction*:
`‖P_Λ m E_Λ Ψ‖₂ ≤ ‖m E_Λ Ψ‖₂ ≤ ‖E_Λ Ψ‖₂ = ‖Ψ‖₂`, i.e.

    ∫_Λ (lowMult fc κ ℓ Ψ)² ≤ ∫_Λ Ψ² .

Since `lowSlot` applies this to the slot-`j` fibre `z ↦ Ψ(x[j↦z])` and the `n`-particle box is a
product measure, the inequality tensorises (Fubini over the slots), giving

    ∫_{abox n ℓ} (lowSlot fc κ ℓ j Ψ)² ≤ ∫_{abox n ℓ} Ψ²

for **every measurable, box-bounded `Ψ`** — with no continuity assumption on `Ψ`.

The proof is written in the same style as the already-proved companion
`Work.BoseFixB3.HighMass.highSlot_sq_integral_le` (which handles the complementary `1 − f_L` slot):
with `H = 1_Λ·Ψ`, `c = m·kinFT H`, `T = lowMult fc κ ℓ Ψ` and `U = 1_Λ·T`, the Fubini pairing
`Work.BoseFixB3.HighMass.kinPair` gives

    (2π)³ ∫_Λ T² = ∫_p m(p)·ℜ(conj(kinFT U p)·kinFT H p) dp ,

and AM–GM (`2ab ≤ a² + b²`) together with Plancherel (`∫_p ‖kinFT F p‖² = (2π)³∫‖F‖²`,
`kinFT_l1l2_plancherel`) for `U` and for `H`, and `0 ≤ m ≤ 1`, yields

    (2π)³ ∫_Λ T² ≤ ½ ((2π)³ ∫_Λ T² + (2π)³ ∫_Λ Ψ²) ,

hence `∫_Λ T² ≤ ∫_Λ Ψ²`.

The one-slot statement is then put into `∫⁻`-form and assembled over the slots with the
measure-preserving `piFinSuccAbove` slicing lemma
`Work.BoseFixB3.HighMass.abox_succ_lintegral_slice`.
-/

noncomputable section

set_option maxHeartbeats 1600000
set_option linter.style.haveILetI false
set_option linter.unusedSimpArgs false
set_option linter.unusedVariables false

open MeasureTheory Filter
open scoped Real Topology BigOperators ENNReal

/-- In this Mathlib the notion `Measurable` is a *root-level* declaration; the frozen target
statement writes it qualified as `MeasureTheory.Measurable`.  This notation makes that spelling
elaborate (to `_root_.Measurable`) so that the frozen statement text is reproduced **verbatim**.
It adds no mathematical content and -- unlike a `MeasureTheory.Measurable` abbreviation -- does not
introduce a second candidate for the unqualified name `Measurable`. -/
notation "MeasureTheory.Measurable" => _root_.Measurable

namespace Work.BoseBoxFock.PCFU

open Submission.BoseGases
open Work.BoseFixB3.HighMass
open Work.BoseBoxFix (LowCut lowMult lowSlot)

local notation "E3" => EuclideanSpace ℝ (Fin 3)

/-! ## 1. The one-slot inequality in Bochner form -/

/-- **The one-slot low-momentum contraction.**  For `κ > 0` and a measurable `ψ` bounded by `C ≥ 0`
on the cube `acube ℓ`,

    ∫_{acube ℓ} (lowMult fc κ ℓ ψ)² ≤ ∫_{acube ℓ} ψ² .

This is `P_Λ · m · E_Λ` being a compression of the contraction `m` (`0 ≤ m ≤ 1`), proved through
the momentum-space pairing `kinPair` and Plancherel; see the module docstring. -/
theorem oneSlot_lowMult_sq_integral_le {fc : LowCut} {κ ℓ C : ℝ} (hκ : 0 < κ) (hℓ : 0 < ℓ)
    (hC : 0 ≤ C) {ψ : E3 → ℝ} (hψm : _root_.Measurable ψ) (hψb : ∀ b ∈ acube ℓ, |ψ b| ≤ C) :
    ∫ b in acube ℓ, (lowMult fc κ ℓ ψ b) ^ 2 ≤ ∫ b in acube ℓ, (ψ b) ^ 2 := by
  classical
  haveI : IsFiniteMeasure ((volume : Measure E3).restrict (acube ℓ)) :=
    ⟨by rw [Measure.restrict_apply_univ]; exact acube_lt_top ℓ hℓ.le⟩
  have hα : ((2 * π) ^ 3 : ℝ) ≠ 0 := by positivity
  set Ψ : E3 → ℝ := (acube ℓ).indicator ψ with hΨ
  set H : E3 → ℂ := fun z => (Ψ z : ℂ) with hH
  have hHind : H = fun z => ((((acube ℓ).indicator ψ z : ℝ)) : ℂ) := by rw [hH, hΨ]
  set c : E3 → ℂ := fun p => ((gsym fc κ p : ℝ) : ℂ) * kinFT H p with hcdef
  set T : E3 → ℝ := fun x => (kinMult fc κ H x).re with hTdef
  set U : E3 → ℝ := (acube ℓ).indicator T with hUdef
  have hΨmeas : _root_.Measurable Ψ := by rw [hΨ]; exact hψm.indicator (acube_measurable ℓ)
  have hΨint : Integrable Ψ volume := by
    rw [hΨ, integrable_indicator_iff (acube_measurable ℓ)]
    refine IntegrableOn.of_bound (acube_lt_top ℓ hℓ.le) hψm.aestronglyMeasurable C ?_
    filter_upwards [MeasureTheory.ae_restrict_mem (acube_measurable ℓ)] with b hb
    rw [Real.norm_eq_abs]
    exact hψb b hb
  have hHint : Integrable H volume := hΨint.ofReal
  have hFh_bound : ∀ p : E3, ‖kinFT H p‖ ≤ ∫ z, ‖H z‖ := by
    intro p
    rw [show kinFT H p
        = ∫ z : E3, Complex.exp (-(Complex.I * (inner ℝ p z : ℂ))) * H z from rfl]
    refine le_trans (norm_integral_le_integral_norm
      (fun z : E3 => Complex.exp (-(Complex.I * (inner ℝ p z : ℂ))) * H z)) (le_of_eq ?_)
    apply integral_congr_ae
    filter_upwards with z
    rw [norm_mul, Complex.norm_exp]
    have hz : (-(Complex.I * (inner ℝ p z : ℂ))).re = 0 := by simp
    rw [hz, Real.exp_zero, one_mul]
  have hc : Integrable c volume := by
    rw [hcdef]
    exact integrable_gsym_mul (fc := fc) (κ := κ) hκ
      (v := kinFT H)
      (stronglyMeasurable_kinFT hHint.aestronglyMeasurable)
      ⟨∫ z, ‖H z‖, integral_nonneg (fun z => norm_nonneg _), hFh_bound⟩
  have hlow : ∀ x : E3, lowMult fc κ ℓ ψ x = T x := fun x => by
    rw [lowMult_eq_re_kinMult, ← hHind, hTdef]
  -- the inverse-transform identity
  have hZ : ∀ x : E3, (∫ p : E3, c p * Complex.exp (Complex.I * (inner ℝ p x : ℂ)))
      = (((2 * π) ^ 3 : ℝ) : ℂ) * kinMult fc κ H x := by
    intro x
    have h := kinMult_eq_invFT fc κ H x
    rw [show (∫ p : E3, c p * Complex.exp (Complex.I * (inner ℝ p x : ℂ)))
        = ∫ p : E3, (((gsym fc κ p : ℝ) : ℂ) * kinFT H p) *
            Complex.exp (Complex.I * (inner ℝ p x : ℂ)) from by
      apply integral_congr_ae
      filter_upwards with p
      rw [hcdef]]
    have hcc : ((2 * π) ^ 3 : ℝ) * ((2 * π) ^ 3)⁻¹ = (1 : ℝ) := mul_inv_cancel₀ hα
    rw [h, ← mul_assoc, ← Complex.ofReal_mul, hcc, Complex.ofReal_one, one_mul]
  have hZT : ∀ x : E3, (∫ p : E3, c p * Complex.exp (Complex.I * (inner ℝ p x : ℂ))).re
      = ((2 * π) ^ 3) * T x := fun x => by rw [hZ x, Complex.re_ofReal_mul, hTdef]
  have hTmeas : _root_.Measurable T := by
    have h1 : (fun x : E3 => (kinMult fc κ H x).re)
        = fun x : E3 => (((((2 * π) ^ 3)⁻¹ : ℝ) : ℂ) *
            (∫ p : E3, c p * Complex.exp (Complex.I * (inner ℝ p x : ℂ)))).re := by
      funext x
      rw [hZ x]
      congr 1
      have hcc : ((2 * π) ^ 3)⁻¹ * ((2 * π) ^ 3) = (1 : ℝ) := inv_mul_cancel₀ hα
      rw [← mul_assoc, ← Complex.ofReal_mul, hcc, Complex.ofReal_one, one_mul]
    rw [hTdef, h1]
    exact Complex.continuous_re.measurable.comp (measurable_const.mul
      (stronglyMeasurable_invFT hc.aestronglyMeasurable).measurable)
  have hTcont : Continuous (kinFT H) :=
    Work.BoseKinLoc.Momentum.continuous_kinFT_of_integrable hHint
  have hTn : ∀ x : E3, ‖kinMult fc κ H x‖ ≤ ((2 * π) ^ 3)⁻¹ * ∫ p, ‖c p‖ := by
    intro x; rw [hcdef]; exact kinMult_norm_le hc x
  have hTb : ∀ x : E3, |T x| ≤ ((2 * π) ^ 3)⁻¹ * ∫ p, ‖c p‖ := fun x =>
    le_trans (Complex.abs_re_le_norm _) (hTn x)
  have hCnonneg : 0 ≤ ((2 * π) ^ 3)⁻¹ * ∫ p, ‖c p‖ :=
    mul_nonneg (by positivity) (integral_nonneg fun p => norm_nonneg _)
  have hUint : Integrable U volume := by
    rw [hUdef, integrable_indicator_iff (acube_measurable ℓ)]
    exact IntegrableOn.of_bound (acube_lt_top ℓ hℓ.le) hTmeas.aestronglyMeasurable _
      (Filter.Eventually.of_forall hTb)
  have hUmemLp : MemLp (fun z : E3 => (U z : ℂ)) 2 volume := by
    have hind : (fun z : E3 => (((acube ℓ).indicator T) z : ℂ))
        = (acube ℓ).indicator (fun z : E3 => (T z : ℂ)) := by
      funext z
      rw [Set.indicator_apply, Set.indicator_apply]
      by_cases hz : z ∈ acube ℓ <;> simp [hz]
    rw [hUdef, hind]
    refine (memLp_indicator_iff_restrict (acube_measurable ℓ)).mpr ?_
    refine MemLp.of_bound
      ((Complex.continuous_ofReal.measurable.comp hTmeas).stronglyMeasurable.aestronglyMeasurable)
      (((2 * π) ^ 3)⁻¹ * ∫ p, ‖c p‖) (Filter.Eventually.of_forall fun z => ?_)
    rw [Complex.norm_real, Real.norm_eq_abs]; exact hTb z
  have hUc_int : Integrable (fun z : E3 => (U z : ℂ)) volume := hUint.ofReal
  have hUc_sm : StronglyMeasurable (kinFT (fun z : E3 => (U z : ℂ))) :=
    stronglyMeasurable_kinFT hUc_int.aestronglyMeasurable
  have hUc_cont : Continuous (kinFT (fun z : E3 => (U z : ℂ))) :=
    Work.BoseKinLoc.Momentum.continuous_kinFT_of_integrable hUc_int
  -- Plancherel for `U`
  have hUplan : ∫ p : E3, ‖kinFT (fun z => (U z : ℂ)) p‖ ^ 2
      = (2 * π) ^ 3 * ∫ x in acube ℓ, T x ^ 2 := by
    rw [Work.BoseKinLoc.Momentum.kinFT_l1l2_plancherel hUc_int hUmemLp]
    congr 1
    rw [show (∫ x : E3, ‖(fun z : E3 => (U z : ℂ)) x‖ ^ 2)
        = ∫ x : E3, (acube ℓ).indicator (fun y : E3 => T y ^ 2) x from by
      apply integral_congr_ae
      filter_upwards with x
      rw [hUdef, Set.indicator_apply]
      by_cases hx : x ∈ acube ℓ <;> simp [hx]]
    rw [MeasureTheory.integral_indicator (acube_measurable ℓ)]
  -- the `L²`-membership and Plancherel for `H`
  have hHmemLp : MemLp H 2 volume := by
    have hind : H = (acube ℓ).indicator (fun z : E3 => (ψ z : ℂ)) := by
      funext z
      rw [hHind]
      by_cases hz : z ∈ acube ℓ <;> simp [Set.indicator_of_mem, Set.indicator_of_notMem, hz]
    rw [hind]
    refine (memLp_indicator_iff_restrict (acube_measurable ℓ)).mpr ?_
    refine MemLp.of_bound
      ((Complex.continuous_ofReal.measurable.comp hψm).stronglyMeasurable.aestronglyMeasurable)
      C ?_
    filter_upwards [MeasureTheory.ae_restrict_mem (acube_measurable ℓ)] with z hz
    rw [Complex.norm_real, Real.norm_eq_abs]
    exact hψb z hz
  have hHplan : ∫ p : E3, ‖kinFT H p‖ ^ 2 = (2 * π) ^ 3 * ∫ b in acube ℓ, (ψ b) ^ 2 := by
    rw [Work.BoseKinLoc.Momentum.kinFT_l1l2_plancherel hHint hHmemLp]
    congr 1
    rw [show (∫ x : E3, ‖H x‖ ^ 2)
        = ∫ x : E3, (acube ℓ).indicator (fun y : E3 => ψ y ^ 2) x from by
      apply integral_congr_ae
      filter_upwards with x
      rw [hHind, Set.indicator_apply]
      by_cases hx : x ∈ acube ℓ <;> simp [hx]]
    rw [MeasureTheory.integral_indicator (acube_measurable ℓ)]
  -- the pairing identity for `T²` (Fubini, `kinPair` with `u = U`)
  have hAid : (2 * π) ^ 3 * ∫ b in acube ℓ, T b ^ 2
      = ∫ p : E3, (gsym fc κ p) * ((starRingEnd ℂ) (kinFT (fun z => (U z : ℂ)) p) *
            kinFT H p).re := by
    have hp := kinPair (c := c) hUint hc
    have h1 : (∫ x : E3, U x *
          (∫ p : E3, c p * Complex.exp (Complex.I * (inner ℝ p x : ℂ))).re)
        = (2 * π) ^ 3 * ∫ x : E3, U x * T x := by
      rw [show (∫ x : E3, U x *
            (∫ p : E3, c p * Complex.exp (Complex.I * (inner ℝ p x : ℂ))).re)
          = ∫ x : E3, U x * (((2 * π) ^ 3) * T x) from by
        apply integral_congr_ae; filter_upwards with x; rw [hZT x]]
      rw [show (∫ x : E3, U x * (((2 * π) ^ 3) * T x))
          = ∫ x : E3, ((2 * π) ^ 3) * (U x * T x) from by
        apply integral_congr_ae; filter_upwards with x; ring]
      rw [MeasureTheory.integral_const_mul]
    have h2 : (∫ x : E3, U x * T x) = ∫ x in acube ℓ, T x ^ 2 := by
      rw [hUdef, ← MeasureTheory.integral_indicator (acube_measurable ℓ)
        (f := fun x => T x ^ 2)]
      apply integral_congr_ae; filter_upwards with x
      rw [Set.indicator_apply, Set.indicator_apply]
      by_cases hx : x ∈ acube ℓ <;>
        simp [Set.indicator_of_mem, Set.indicator_of_notMem, hx, pow_two]
    have h3 : (∫ p : E3, ((starRingEnd ℂ) (kinFT (fun z => (U z : ℂ)) p) * c p).re)
        = ∫ p : E3, (gsym fc κ p) * ((starRingEnd ℂ)
            (kinFT (fun z => (U z : ℂ)) p) * kinFT H p).re := by
      apply integral_congr_ae
      filter_upwards with p
      rw [hcdef]
      rw [show ((starRingEnd ℂ) (kinFT (fun z => (U z : ℂ)) p) *
            (((gsym fc κ p : ℝ) : ℂ) * kinFT H p)).re
          = (gsym fc κ p) * ((starRingEnd ℂ)
              (kinFT (fun z => (U z : ℂ)) p) * kinFT H p).re from by
        rw [show (starRingEnd ℂ) (kinFT (fun z => (U z : ℂ)) p) *
              (((gsym fc κ p : ℝ) : ℂ) * kinFT H p)
            = (((gsym fc κ p : ℝ) : ℂ)) * ((starRingEnd ℂ)
                (kinFT (fun z : E3 => (U z : ℂ)) p) * kinFT H p) from by ring,
          Complex.re_ofReal_mul]]
    rw [h1, h2, h3] at hp
    exact hp
  -- integrability of the momentum-space integrands
  have hFhmem : MemLp (kinFT H) 2 volume :=
    Work.BoseKinLoc.Momentum.memLp_kinFT hHint hHmemLp
  have hFUmem : MemLp (kinFT (fun z : E3 => (U z : ℂ))) 2 volume :=
    Work.BoseKinLoc.Momentum.memLp_kinFT hUc_int hUmemLp
  have hH2int : Integrable (fun p : E3 => ‖kinFT H p‖ ^ 2) :=
    (memLp_two_iff_integrable_sq hFhmem.aestronglyMeasurable.norm).mp hFhmem.norm
  have hU2int : Integrable (fun p : E3 =>
      ‖kinFT (fun z : E3 => (U z : ℂ)) p‖ ^ 2) :=
    (memLp_two_iff_integrable_sq hFUmem.aestronglyMeasurable.norm).mp hFUmem.norm
  have hProdint : Integrable (fun p : E3 =>
      ‖kinFT (fun z : E3 => (U z : ℂ)) p‖ * ‖kinFT H p‖) := by
    refine (hU2int.add hH2int).mono' ?_ ?_
    · exact ((hUc_cont.norm.measurable.mul hTcont.norm.measurable)).stronglyMeasurable
        |>.aestronglyMeasurable
    · filter_upwards with p
      simp only [Pi.add_apply]
      have h2 : 2 * (‖kinFT (fun z : E3 => (U z : ℂ)) p‖ * ‖kinFT H p‖)
          ≤ ‖kinFT (fun z : E3 => (U z : ℂ)) p‖ ^ 2 + ‖kinFT H p‖ ^ 2 := by
        nlinarith [sq_nonneg (‖kinFT (fun z : E3 => (U z : ℂ)) p‖ - ‖kinFT H p‖)]
      have hab : (0 : ℝ) ≤ ‖kinFT (fun z : E3 => (U z : ℂ)) p‖ * ‖kinFT H p‖ :=
        mul_nonneg (norm_nonneg _) (norm_nonneg _)
      rw [Real.norm_of_nonneg hab]
      linarith
  -- the AM–GM chain
  have hGL : Integrable (fun p : E3 => (gsym fc κ p) *
      ‖kinFT (fun z : E3 => (U z : ℂ)) p‖ ^ 2) := by
    refine hU2int.mono' ?_ ?_
    · exact ((gsym_continuous fc κ).measurable.mul
        (hUc_cont.norm.measurable.pow_const 2)).stronglyMeasurable.aestronglyMeasurable
    · filter_upwards with p
      rw [Real.norm_eq_abs]
      exact le_trans (gsym_abs_mul_le fc κ p _) (le_of_eq (abs_of_nonneg (sq_nonneg _)))
  have hGR : Integrable (fun p : E3 => (gsym fc κ p) * ‖kinFT H p‖ ^ 2) := by
    refine hH2int.mono' ?_ ?_
    · exact ((gsym_continuous fc κ).measurable.mul
        (hTcont.norm.measurable.pow_const 2)).stronglyMeasurable.aestronglyMeasurable
    · filter_upwards with p
      rw [Real.norm_eq_abs]
      exact le_trans (gsym_abs_mul_le fc κ p _) (le_of_eq (abs_of_nonneg (sq_nonneg _)))
  have hRe : ∫ p : E3, (gsym fc κ p) * ((starRingEnd ℂ)
        (kinFT (fun z => (U z : ℂ)) p) * kinFT H p).re
      ≤ ∫ p : E3, (gsym fc κ p) *
          (‖kinFT (fun z => (U z : ℂ)) p‖ * ‖kinFT H p‖) := by
    have hHl : ∀ p : E3, |((starRingEnd ℂ)
          (kinFT (fun z : E3 => (U z : ℂ)) p) * kinFT H p).re|
        ≤ ‖kinFT (fun z : E3 => (U z : ℂ)) p‖ * ‖kinFT H p‖ :=
      fun p => le_trans (Complex.abs_re_le_norm _) (le_of_eq (by rw [norm_mul, Complex.norm_conj]))
    refine integral_mono ?_ ?_ (fun p => ?_)
    · refine hProdint.mono' ?_ ?_
      · refine AEStronglyMeasurable.mul (gsym_continuous fc κ).aestronglyMeasurable ?_
        exact (Complex.continuous_re.measurable.comp
          ((Complex.continuous_conj.comp hUc_cont).mul hTcont).measurable).aestronglyMeasurable
      · filter_upwards with p
        calc ‖(gsym fc κ p) * ((starRingEnd ℂ)
              (kinFT (fun z : E3 => (U z : ℂ)) p) * kinFT H p).re‖
            = |gsym fc κ p * ((starRingEnd ℂ)
                (kinFT (fun z : E3 => (U z : ℂ)) p) * kinFT H p).re| := Real.norm_eq_abs _
          _ ≤ |((starRingEnd ℂ)
                (kinFT (fun z : E3 => (U z : ℂ)) p) * kinFT H p).re| :=
              gsym_abs_mul_le fc κ p _
          _ ≤ _ := hHl p
    · refine hProdint.mono' ?_ ?_
      · refine AEStronglyMeasurable.mul (gsym_continuous fc κ).aestronglyMeasurable ?_
        exact (hUc_cont.norm.measurable.mul hTcont.norm.measurable).aestronglyMeasurable
      · filter_upwards with p
        calc ‖gsym fc κ p * (‖kinFT (fun z : E3 => (U z : ℂ)) p‖ * ‖kinFT H p‖)‖
            = |gsym fc κ p * (‖kinFT (fun z : E3 => (U z : ℂ)) p‖ * ‖kinFT H p‖)| :=
              Real.norm_eq_abs _
          _ ≤ |‖kinFT (fun z : E3 => (U z : ℂ)) p‖ * ‖kinFT H p‖| := gsym_abs_mul_le fc κ p _
          _ = _ := abs_of_nonneg (mul_nonneg (norm_nonneg _) (norm_nonneg _))
    · exact mul_le_mul_of_nonneg_left (le_trans (le_abs_self _) (hHl p)) (gsym_nonneg fc κ p)
  have hAMGM : ∫ p : E3, (gsym fc κ p) *
        (‖kinFT (fun z => (U z : ℂ)) p‖ * ‖kinFT H p‖)
      ≤ (1 / 2) * ((∫ p : E3, (gsym fc κ p) *
            ‖kinFT (fun z : E3 => (U z : ℂ)) p‖ ^ 2) +
          (∫ p : E3, (gsym fc κ p) * ‖kinFT H p‖ ^ 2)) := by
    have h1 : ∫ p : E3, (gsym fc κ p) *
          (‖kinFT (fun z : E3 => (U z : ℂ)) p‖ * ‖kinFT H p‖)
        ≤ ∫ p : E3, (1 / 2) * ((gsym fc κ p) *
              ‖kinFT (fun z : E3 => (U z : ℂ)) p‖ ^ 2 +
            (gsym fc κ p) * ‖kinFT H p‖ ^ 2) := by
      refine integral_mono ?_ ?_ (fun p => ?_)
      · refine hProdint.mono' ?_ ?_
        · refine AEStronglyMeasurable.mul (gsym_continuous fc κ).aestronglyMeasurable ?_
          exact (hUc_cont.norm.measurable.mul hTcont.norm.measurable).aestronglyMeasurable
        · filter_upwards with p
          calc ‖gsym fc κ p * (‖kinFT (fun z : E3 => (U z : ℂ)) p‖ * ‖kinFT H p‖)‖
              = |gsym fc κ p * (‖kinFT (fun z : E3 => (U z : ℂ)) p‖ * ‖kinFT H p‖)| :=
                Real.norm_eq_abs _
            _ ≤ |‖kinFT (fun z : E3 => (U z : ℂ)) p‖ * ‖kinFT H p‖| := gsym_abs_mul_le fc κ p _
            _ = _ := abs_of_nonneg (mul_nonneg (norm_nonneg _) (norm_nonneg _))
      · exact (hGL.add hGR).const_mul _
      · have h2 : 2 * (‖kinFT (fun z : E3 => (U z : ℂ)) p‖ * ‖kinFT H p‖)
            ≤ ‖kinFT (fun z : E3 => (U z : ℂ)) p‖ ^ 2 + ‖kinFT H p‖ ^ 2 := by
          nlinarith [sq_nonneg (‖kinFT (fun z : E3 => (U z : ℂ)) p‖ - ‖kinFT H p‖)]
        have hgl := gsym_nonneg fc κ p
        nlinarith [mul_le_mul_of_nonneg_left h2 hgl]
    simpa only [MeasureTheory.integral_const_mul, MeasureTheory.integral_add hGL hGR] using h1
  -- the two Plancherel comparisons
  have hUsq_le : (∫ p : E3, (gsym fc κ p) *
        ‖kinFT (fun z => (U z : ℂ)) p‖ ^ 2)
      ≤ (2 * π) ^ 3 * (∫ x in acube ℓ, T x ^ 2) := by
    refine le_trans ?_ (le_of_eq hUplan)
    exact integral_mono hGL hU2int
      (fun p => mul_le_of_le_one_left (sq_nonneg _) (gsym_le_one fc κ p))
  have hHsq_le : (∫ p : E3, (gsym fc κ p) * ‖kinFT H p‖ ^ 2)
      ≤ (2 * π) ^ 3 * (∫ x in acube ℓ, (ψ x) ^ 2) := by
    refine le_trans ?_ (le_of_eq hHplan)
    exact integral_mono hGR hH2int
      (fun p => mul_le_of_le_one_left (sq_nonneg _) (gsym_le_one fc κ p))
  -- the final chain
  calc ∫ b in acube ℓ, (lowMult fc κ ℓ ψ b) ^ 2
      = ∫ b in acube ℓ, (T b) ^ 2 := by
        apply integral_congr_ae; filter_upwards with b; rw [hlow b]
    _ ≤ ∫ b in acube ℓ, (ψ b) ^ 2 := by
        have hchain : (2 * π) ^ 3 * (∫ b in acube ℓ, T b ^ 2)
            ≤ (2 * π) ^ 3 * (∫ b in acube ℓ, (ψ b) ^ 2) := by
          rw [hAid]
          linarith [hRe, hAMGM, hUsq_le, hHsq_le]
        exact le_of_mul_le_mul_left hchain (by positivity)

/-! ## 2. The one-slot inequality in `∫⁻` form -/

/-- **The one-slot low-momentum contraction, `∫⁻`-version**, for measurable `ψ` bounded on the
cube.  This is the form used to assemble the `n`-particle statement by slicing. -/
theorem oneSlot_lintegral_le_lowMult {fc : LowCut} {κ ℓ C : ℝ} (hκ : 0 < κ) (hℓ : 0 < ℓ)
    (hC : 0 ≤ C) {ψ : E3 → ℝ} (hψm : _root_.Measurable ψ) (hψb : ∀ b ∈ acube ℓ, |ψ b| ≤ C) :
    ∫⁻ b in acube ℓ, ENNReal.ofReal ((lowMult fc κ ℓ ψ b) ^ 2)
      ≤ ∫⁻ b in acube ℓ, ENNReal.ofReal ((ψ b) ^ 2) := by
  have hD0 : 0 ≤ C * ℓ ^ 3 := mul_nonneg hC (by positivity)
  have hmass : ∫ z, ‖(((acube ℓ).indicator ψ z : ℝ) : ℂ)‖ ≤ C * ℓ ^ 3 :=
    Work.BoseFixB3.Split.integral_indicator_norm_le hℓ hC hψb
  set B : ℝ := ((2 * π) ^ 3)⁻¹ * (C * ℓ ^ 3)
      * (volume (Metric.closedBall (0 : E3) (2 * κ))).toReal with hBdef
  have hB0 : 0 ≤ B := by
    rw [hBdef]
    exact mul_nonneg (mul_nonneg (by positivity) hD0) ENNReal.toReal_nonneg
  have hlowb : ∀ y : E3, |lowMult fc κ ℓ ψ y| ≤ B := by
    intro y
    rw [hBdef]
    exact Work.BoseFixB3.Split.lowMult_abs_le (fc := fc) (κ := κ) (ℓ := ℓ)
      (D := C * ℓ ^ 3) hκ hD0 hmass y
  have hFm : _root_.Measurable (fun b : E3 => (lowMult fc κ ℓ ψ b) ^ 2) :=
    (Work.BoseFixB3.Conv.stronglyMeasurable_lowMult (fc := fc) (κ := κ) (ℓ := ℓ)
      hψm).measurable.pow_const 2
  have hFint : IntegrableOn (fun b : E3 => (lowMult fc κ ℓ ψ b) ^ 2) (acube ℓ) := by
    refine IntegrableOn.of_bound (acube_lt_top ℓ hℓ.le) hFm.aestronglyMeasurable (B ^ 2) ?_
    filter_upwards with b
    rw [Real.norm_eq_abs, abs_of_nonneg (sq_nonneg _)]
    nlinarith [hlowb b, hB0, abs_nonneg (lowMult fc κ ℓ ψ b), sq_abs (lowMult fc κ ℓ ψ b)]
  have hGint : IntegrableOn (fun b : E3 => (ψ b) ^ 2) (acube ℓ) := by
    refine IntegrableOn.of_bound (acube_lt_top ℓ hℓ.le)
      ((hψm.pow_const 2).aestronglyMeasurable) (C ^ 2) ?_
    filter_upwards [MeasureTheory.ae_restrict_mem (acube_measurable ℓ)] with b hb
    rw [Real.norm_eq_abs, abs_of_nonneg (sq_nonneg _)]
    nlinarith [hψb b hb, hC, abs_nonneg (ψ b), sq_abs (ψ b)]
  have hreal := oneSlot_lowMult_sq_integral_le (fc := fc) hκ hℓ hC hψm hψb
  have e1 := MeasureTheory.ofReal_integral_eq_lintegral_ofReal hFint
    (Filter.Eventually.of_forall fun b => sq_nonneg _)
  have e2 := MeasureTheory.ofReal_integral_eq_lintegral_ofReal hGint
    (Filter.Eventually.of_forall fun b => sq_nonneg _)
  rw [← e1, ← e2]
  exact ENNReal.ofReal_le_ofReal hreal

/-! ## 3. The target: the slot-`j` low-momentum lift is an `L²`-contraction on the box -/

theorem lowSlot_L2_le {n : ℕ} (j : Fin n) (fc : Work.BoseBoxFix.LowCut) {κ ℓ C : ℝ}
    (hκ : 0 < κ) (hℓ : 0 < ℓ) (hC : 0 ≤ C) {Ψ : Submission.BoseGases.X n → ℝ}
    (hΨm : MeasureTheory.Measurable Ψ)
    (hΨb : ∀ x ∈ Submission.BoseGases.abox n ℓ, |Ψ x| ≤ C) :
    ∫ x in Submission.BoseGases.abox n ℓ, (Work.BoseBoxFix.lowSlot fc κ ℓ j Ψ x) ^ 2
      ≤ ∫ x in Submission.BoseGases.abox n ℓ, (Ψ x) ^ 2 := by
  rcases n with _ | m
  · exact (Fin.elim0 j)
  · set e : X (m + 1) ≃ᵐ (E3 × X m) :=
      MeasurableEquiv.piFinSuccAbove (fun _ : Fin (m + 1) => E3) j with he
    -- the box is measurable (it is compact)
    have habox : MeasurableSet (abox (m + 1) ℓ) :=
      (Work.UBBInputs9.B.abox_isCompact (m + 1) ℓ).isClosed.measurableSet
    have haboxm : MeasurableSet (abox m ℓ) :=
      (Work.UBBInputs9.B.abox_isCompact m ℓ).isClosed.measurableSet
    have hesymm : ∀ (b : E3) (a : X m), e.symm (b, a) = j.insertNth b a := by
      intro b a
      rw [he, MeasurableEquiv.piFinSuccAbove_symm_apply]
      rfl
    -- the pointwise identification of the slot-`j` split
    have hpt : ∀ (b : E3) (a : X m),
        Work.BoseBoxFix.lowSlot fc κ ℓ j Ψ (e.symm (b, a))
          = lowMult fc κ ℓ (fun z : E3 => Ψ (e.symm (z, a))) b := by
      intro b a
      have hupd : ∀ z : E3, Function.update (e.symm (b, a)) j z = e.symm (z, a) := by
        intro z
        rw [hesymm b a, hesymm z a]
        ext k
        rw [Function.update_apply]
        by_cases hk : k = j
        · subst hk
          rw [if_pos rfl, Fin.insertNth_apply_same]
        · obtain ⟨k', rfl⟩ := Fin.exists_succAbove_eq hk
          rw [if_neg (Fin.succAbove_ne _ _), Fin.insertNth_apply_succAbove,
            Fin.insertNth_apply_succAbove]
      have hxj : (e.symm (b, a)) j = b := by
        rw [hesymm b a, Fin.insertNth_apply_same]
      simp only [Work.BoseBoxFix.lowSlot, hxj]
      rw [show (fun z : E3 => Ψ (Function.update (e.symm (b, a)) j z))
          = fun z : E3 => Ψ (e.symm (z, a)) from funext fun z => by rw [hupd z]]
    -- the `∫⁻` slicing
    have hslice (F : X (m + 1) → ENNReal)
        (hF : AEMeasurable F ((volume : Measure (X (m + 1))).restrict (abox (m + 1) ℓ))) :
        ∫⁻ x in abox (m + 1) ℓ, F x
          = ∫⁻ a in abox m ℓ, ∫⁻ b in acube ℓ, F (e.symm (b, a)) :=
      abox_succ_lintegral_slice j F hF
    have hL := hslice (fun x => ENNReal.ofReal ((Work.BoseBoxFix.lowSlot fc κ ℓ j Ψ x) ^ 2))
      (ENNReal.measurable_ofReal.comp
        ((lowSlotMeasurableOfMeasurable fc j hΨm).pow_const 2)).aemeasurable
    have hR := hslice (fun x => ENNReal.ofReal ((Ψ x) ^ 2))
      (ENNReal.measurable_ofReal.comp (hΨm.pow_const 2)).aemeasurable
    have hmain : ∫⁻ x in abox (m + 1) ℓ,
          ENNReal.ofReal ((Work.BoseBoxFix.lowSlot fc κ ℓ j Ψ x) ^ 2)
        ≤ ∫⁻ x in abox (m + 1) ℓ, ENNReal.ofReal ((Ψ x) ^ 2) := by
      rw [hL, hR]
      refine lintegral_mono_ae ?_
      filter_upwards [MeasureTheory.ae_restrict_mem haboxm] with a ha
      -- the slice at `a` is measurable and bounded on the cube
      have hsliceMeas : _root_.Measurable (fun z : E3 => Ψ (e.symm (z, a))) := by
        have hcont : Continuous (fun z : E3 => e.symm (z, a)) := by
          rw [continuous_pi_iff]
          intro k
          rw [he]
          by_cases hk : k = j
          · subst hk
            simp only [MeasurableEquiv.piFinSuccAbove_symm_apply, Fin.insertNthEquiv_apply,
              Fin.insertNth_apply_same]
            exact continuous_id
          · obtain ⟨k', rfl⟩ := Fin.exists_succAbove_eq hk
            simp only [MeasurableEquiv.piFinSuccAbove_symm_apply, Fin.insertNthEquiv_apply,
              Fin.insertNth_apply_succAbove]
            exact continuous_const
        exact hΨm.comp hcont.measurable
      have hsliceBdd : ∀ z ∈ acube ℓ, |Ψ (e.symm (z, a))| ≤ C := by
        intro z hz
        refine hΨb _ ?_
        rw [hesymm z a]
        intro i
        by_cases hi : i = j
        · subst hi
          rw [Fin.insertNth_apply_same]; exact hz
        · obtain ⟨k', rfl⟩ := Fin.exists_succAbove_eq hi
          rw [Fin.insertNth_apply_succAbove]
          exact ha k'
      have hcong : ∫⁻ b in acube ℓ,
            ENNReal.ofReal ((Work.BoseBoxFix.lowSlot fc κ ℓ j Ψ (e.symm (b, a))) ^ 2)
          = ∫⁻ b in acube ℓ,
            ENNReal.ofReal ((lowMult fc κ ℓ (fun z : E3 => Ψ (e.symm (z, a))) b) ^ 2) := by
        apply lintegral_congr
        intro b
        rw [hpt b a]
      rw [hcong]
      exact oneSlot_lintegral_le_lowMult hκ hℓ hC hsliceMeas hsliceBdd
    -- conversion back to Bochner integrals
    have hΨ2int : Integrable (fun x : X (m + 1) => (Ψ x) ^ 2)
        ((volume : Measure (X (m + 1))).restrict (abox (m + 1) ℓ)) := by
      refine IntegrableOn.of_bound
        ((Work.UBBInputs9.B.abox_isCompact (m + 1) ℓ).measure_lt_top)
        ((hΨm.pow_const 2).aestronglyMeasurable) (C ^ 2) ?_
      filter_upwards [MeasureTheory.ae_restrict_mem habox] with x hx
      rw [Real.norm_eq_abs, abs_of_nonneg (sq_nonneg _)]
      nlinarith [hΨb x hx, hC, abs_nonneg (Ψ x), sq_abs (Ψ x)]
    have hfin : (∫⁻ x in abox (m + 1) ℓ, ENNReal.ofReal ((Ψ x) ^ 2))
        = ENNReal.ofReal (∫ x in abox (m + 1) ℓ, (Ψ x) ^ 2) :=
      (MeasureTheory.ofReal_integral_eq_lintegral_ofReal hΨ2int
        (Filter.Eventually.of_forall fun x => sq_nonneg _)).symm
    have hle : ∫ x in abox (m + 1) ℓ, (Work.BoseBoxFix.lowSlot fc κ ℓ j Ψ x) ^ 2
        ≤ (∫⁻ x in abox (m + 1) ℓ,
            ENNReal.ofReal ((Work.BoseBoxFix.lowSlot fc κ ℓ j Ψ x) ^ 2)).toReal :=
      integral_le_toReal_lintegral_ofReal (fun x => sq_nonneg _)
    calc ∫ x in abox (m + 1) ℓ, (Work.BoseBoxFix.lowSlot fc κ ℓ j Ψ x) ^ 2
        ≤ (∫⁻ x in abox (m + 1) ℓ,
            ENNReal.ofReal ((Work.BoseBoxFix.lowSlot fc κ ℓ j Ψ x) ^ 2)).toReal := hle
      _ ≤ (ENNReal.ofReal (∫ x in abox (m + 1) ℓ, (Ψ x) ^ 2)).toReal :=
          ENNReal.toReal_mono ENNReal.ofReal_ne_top (hfin ▸ hmain)
      _ = ∫ x in abox (m + 1) ℓ, (Ψ x) ^ 2 :=
          ENNReal.toReal_ofReal (integral_nonneg fun x => sq_nonneg _)

end Work.BoseBoxFock.PCFU
