/-
Copyright: work module for the Elgindi finite-time singularity project.

# The weighted slice interpolation inequality for the angular weight `σ θ = sin(2θ)^{-η}`

`sliceInterp` is the one-dimensional weighted `L²` interpolation inequality

  `∫_{Iθ} (u')² σ ≤ 10000 (∫_{Iθ} u² σ + ∫_{Iθ} (u'')² σ)`,

`σ θ = sin(2θ)^{-η}`, `η = 99/100`, `Iθ = [0, π/2]`, for a function `u` of class `C²` on the
*open* interval `(0, π/2)` whose weighted `L²`-norms of `u` and `u''` are finite.

## Structure of the proof

Write `c = u'(π/4)`, `A = ∫_{Iθ} |u''|`, `E = ∫_{Iθ} (u'')² σ` and `P = ∫_{Iθ} u² σ`.

* `A² ≤ (π/2) E` (weighted Cauchy–Schwarz, `abs_setIntegral_le_sqrt_mul_sqrt`);
* `|u'(θ) - c| ≤ A` for every `θ ∈ (0, π/2)` (fundamental theorem of calculus for `u'`);
* **the pivot bound** `c² ≤ 12 A² + P`: the second-order Taylor identity centred at `π/4`
  relates `c (φ - θ)` to `u φ - u θ` and to `∫_θ^φ (u' - c)`; integrating the resulting
  pointwise inequality twice — over `φ ∈ [3π/8, π/2]` and then over `θ ∈ [0, π/8]` — and using
  that the weight has mass `≥ 25` on each of these two extreme quarters removes the pivot;
* finally `(u')² ≤ 2(u' - c)² + 2c² ≤ 2A² + 2c²` pointwise, so integrating against `σ`
  (`∫_{Iθ} σ ≤ 200`) and inserting the three bounds above gives the result with a constant
  below `10⁴`.
-/
import Mathlib.Algebra.Order.Star.Real
import Mathlib.Analysis.Real.Pi.Bounds
import Mathlib.Analysis.SpecialFunctions.Integrals.Basic
import Mathlib.MeasureTheory.Integral.IntervalIntegral.ContDiff
import Mathlib.Order.CompletePartialOrder
import Submission.Work.FTS.EllipticEst.Honest.Basic
import Submission.Work.FTS.EllipticEst.StraightDefs
import Submission.Work.FTS.EllipticEst.integrableAbsOfSqSeta
import Submission.Work.FTS.EllipticEst.AngSecond.abs_setIntegral_le_sqrt_mul_sqrt
import Submission.Work.FTS.EllipticEst.ThetaPoincareDefs

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

namespace Work.FTS.EllipticEst.Honest

open scoped Real Topology
open MeasureTheory Set Filter

set_option autoImplicit false
set_option maxHeartbeats 1000000

noncomputable section

local notation "σ" => Work.FTS.EllipticEst.AngSecond.sig

/-! ## 1. Elementary facts about the weight `σ θ = sin(2θ)^{-η}` -/

private lemma sig_nonneg_of_mem {θ : ℝ} (hθ : θ ∈ Work.Spaces.Iθ) : 0 ≤ σ θ :=
  Work.FTS.EllipticEst.AngSecond.sig_nonneg hθ

private lemma sig_eq_thEta : σ = Work.FTS.EllipticEst.thEta := rfl

private lemma integrableOn_sig : IntegrableOn σ Work.Spaces.Iθ := by
  rw [sig_eq_thEta]
  exact Work.FTS.EllipticEst.integrableOn_thEta.1

private lemma sig_zero_left : σ 0 = 0 := by
  rw [Work.FTS.EllipticEst.AngSecond.sig, show (2 : ℝ) * 0 = 0 by ring, Real.sin_zero]
  exact Real.zero_rpow (by rw [Work.Spaces.eta]; norm_num)

private lemma sig_zero_right : σ (Real.pi / 2) = 0 := by
  rw [Work.FTS.EllipticEst.AngSecond.sig,
    show 2 * (Real.pi / 2) = Real.pi by ring, Real.sin_pi]
  exact Real.zero_rpow (by rw [Work.Spaces.eta]; norm_num)

/-- Set integral over `[a,b]` is the interval integral. -/
private lemma setIntegral_Icc_eq_intervalIntegral {f : ℝ → ℝ} {a b : ℝ} (h : a ≤ b) :
    (∫ x in Set.Icc a b, f x) = ∫ x in a..b, f x := by
  rw [MeasureTheory.integral_Icc_eq_integral_Ioc, ← intervalIntegral.integral_of_le h]

/-- The weight is invariant under the reflection `θ ↦ π/2 - θ` of `Iθ`. -/
private lemma sig_pi_div_two_sub (θ : ℝ) : σ (Real.pi / 2 - θ) = σ θ := by
  rw [Work.FTS.EllipticEst.AngSecond.sig, Work.FTS.EllipticEst.AngSecond.sig,
    show 2 * (Real.pi / 2 - θ) = Real.pi - 2 * θ by ring, Real.sin_pi_sub]

/-- `[a,b]` and the open interval agree almost everywhere. -/
private lemma Icc_ae_eq_Ioo (a b : ℝ) : Set.Icc a b =ᵐ[volume] Set.Ioo a b := by
  have hpair : volume ({a, b} : Set ℝ) = 0 :=
    Set.Finite.measure_zero (by simp) volume
  have hpairab : ∀ᵐ x : ℝ, x ∉ ({a, b} : Set ℝ) := by
    rw [MeasureTheory.ae_iff]
    simpa only [not_not, Set.ofPred_mem_eq] using hpair
  filter_upwards [hpairab] with x hx
  refine propext ⟨?_, ?_⟩
  · intro h
    rw [Set.mem_Icc] at h
    rw [Set.mem_Ioo]
    exact ⟨lt_of_le_of_ne h.1 (fun hc => hx (Or.inl hc.symm)),
      lt_of_le_of_ne h.2 (fun hc => hx (Or.inr hc))⟩
  · intro h
    rw [Set.mem_Ioo] at h
    rw [Set.mem_Icc]
    exact ⟨le_of_lt h.1, le_of_lt h.2⟩

private lemma Iθ_ae_eq_Ioo :
    Work.Spaces.Iθ =ᵐ[volume] Set.Ioo (0 : ℝ) (Real.pi / 2) := by
  simpa only [Work.Spaces.Iθ] using Icc_ae_eq_Ioo 0 (Real.pi / 2)

private lemma Ioo_subset_Iθ : Set.Ioo (0 : ℝ) (Real.pi / 2) ⊆ Work.Spaces.Iθ :=
  fun x hx => ⟨le_of_lt hx.1, le_of_lt hx.2⟩

private lemma abs_sub_le_abs_add_abs (a b : ℝ) : |a - b| ≤ |a| + |b| := by
  rw [abs_sub_le_iff]
  constructor <;> linarith [le_abs_self a, neg_le_abs a, le_abs_self b, neg_le_abs b]

/-- On the left quarter `(0, π/4]` the weight is dominated by the power `(4θ/π)^{-η}`
(Jordan's inequality). -/
private lemma sig_le_pow_left {θ : ℝ} (hθ0 : 0 < θ) (hθ1 : θ ≤ Real.pi / 4) :
    σ θ ≤ ((4 / Real.pi) * θ) ^ (-(Work.Spaces.eta)) := by
  have hs : (4 / Real.pi) * θ ≤ Real.sin (2 * θ) := by
    have h := Real.mul_le_sin (x := 2 * θ) (by linarith) (by linarith [hθ1, Real.pi_pos])
    calc (4 / Real.pi) * θ = 2 / Real.pi * (2 * θ) := by ring
      _ ≤ Real.sin (2 * θ) := h
  have hpos : 0 < (4 / Real.pi) * θ := by positivity
  have hz : (-(Work.Spaces.eta)) ≤ 0 := by rw [Work.Spaces.eta]; norm_num
  rw [Work.FTS.EllipticEst.AngSecond.sig]
  exact Real.rpow_le_rpow_of_nonpos hpos hs hz

/-! ## 2. The mass of the weight on `Iθ` and on its two extreme quarters -/

/-- `∫_0^{π/4} (4θ/π)^{-η} dθ = 25π` (in the factored form). -/
private lemma integral_majorant_left :
    (∫ θ in (0 : ℝ)..(Real.pi / 4),
        (4 / Real.pi) ^ (-(Work.Spaces.eta)) * θ ^ (-(Work.Spaces.eta)))
      = 25 * Real.pi := by
  have hlt : (-1 : ℝ) < -(Work.Spaces.eta) := by rw [Work.Spaces.eta]; norm_num
  rw [intervalIntegral.integral_const_mul, integral_rpow (Or.inl hlt)]
  have hzero : (0 : ℝ) ^ (1 - Work.Spaces.eta) = 0 := by
    refine Real.zero_rpow ?_
    rw [Work.Spaces.eta]; norm_num
  rw [show -(Work.Spaces.eta) + 1 = 1 - Work.Spaces.eta by ring, hzero, sub_zero]
  have hcoef : (4 / Real.pi) ^ (-(Work.Spaces.eta)) = (Real.pi / 4) ^ (Work.Spaces.eta) := by
    rw [Real.rpow_neg (by positivity : (0 : ℝ) ≤ 4 / Real.pi),
      ← Real.inv_rpow (by positivity : (0 : ℝ) ≤ 4 / Real.pi) Work.Spaces.eta, inv_div]
  rw [hcoef]
  have hcomb : (Real.pi / 4) ^ (Work.Spaces.eta)
      * ((Real.pi / 4) ^ (1 - Work.Spaces.eta) / (1 - Work.Spaces.eta))
      = (Real.pi / 4) / (1 - Work.Spaces.eta) := by
    rw [mul_div_assoc', ← Real.rpow_add (by positivity : (0 : ℝ) < Real.pi / 4),
      show Work.Spaces.eta + (1 - Work.Spaces.eta) = 1 by ring, Real.rpow_one]
  rw [hcomb]
  have hden : (1 : ℝ) - Work.Spaces.eta = 1 / 100 := by rw [Work.Spaces.eta]; norm_num
  rw [hden]
  ring

/-- `∫_0^{π/4} σ ≤ 25π`. -/
private lemma integral_left_le :
    (∫ θ in (0 : ℝ)..(Real.pi / 4), σ θ) ≤ 25 * Real.pi := by
  have h44 : (0 : ℝ) ≤ Real.pi / 4 := by positivity
  have hσi : IntervalIntegrable σ volume 0 (Real.pi / 4) := by
    rw [intervalIntegrable_iff_integrableOn_Icc_of_le h44]
    refine integrableOn_sig.mono_set ?_
    intro x hx
    exact ⟨hx.1, by linarith [hx.2, Real.pi_pos]⟩
  have hmi : IntervalIntegrable
      (fun θ : ℝ => (4 / Real.pi) ^ (-(Work.Spaces.eta)) * θ ^ (-(Work.Spaces.eta)))
      volume 0 (Real.pi / 4) :=
    (intervalIntegral.intervalIntegrable_rpow'
      (by rw [Work.Spaces.eta]; norm_num : (-1 : ℝ) < -(Work.Spaces.eta))).const_mul _
  have hmono := intervalIntegral.integral_mono_on_of_le_Ioo h44 hσi hmi
    (fun x hx => by
      have h1 := sig_le_pow_left hx.1 (le_of_lt hx.2)
      rwa [Real.mul_rpow (by positivity : (0 : ℝ) ≤ 4 / Real.pi) (le_of_lt hx.1)] at h1)
  rwa [integral_majorant_left] at hmono

/-- The two halves of `∫_{Iθ} σ` are equal (reflection symmetry of the weight). -/
private lemma integral_right_eq_left :
    (∫ θ in (Real.pi / 4)..(Real.pi / 2), σ θ) = ∫ θ in (0 : ℝ)..(Real.pi / 4), σ θ := by
  have h := intervalIntegral.integral_comp_sub_left (a := 0) (b := Real.pi / 4) σ (Real.pi / 2)
  rw [show Real.pi / 2 - Real.pi / 4 = Real.pi / 4 by ring, sub_zero] at h
  rw [← h]
  exact intervalIntegral.integral_congr (fun x _ => sig_pi_div_two_sub x)

/-- **The total mass of the weight**: `∫_{Iθ} σ ≤ 200`. -/
private lemma sig_integral_Iθ_le_200 :
    (∫ θ in Work.Spaces.Iθ, σ θ) ≤ 200 := by
  have h2 : (∫ θ in Work.Spaces.Iθ, σ θ) = ∫ θ in (0 : ℝ)..(Real.pi / 2), σ θ :=
    setIntegral_Icc_eq_intervalIntegral (a := 0) (b := Real.pi / 2) (by positivity)
  rw [h2]
  have hπ4 : (0 : ℝ) ≤ Real.pi / 4 := by positivity
  have hσ1 : IntervalIntegrable σ volume 0 (Real.pi / 4) := by
    rw [intervalIntegrable_iff_integrableOn_Icc_of_le hπ4]
    refine integrableOn_sig.mono_set ?_
    intro x hx
    exact ⟨hx.1, by linarith [hx.2, Real.pi_pos]⟩
  have hσ2 : IntervalIntegrable σ volume (Real.pi / 4) (Real.pi / 2) := by
    rw [intervalIntegrable_iff_integrableOn_Icc_of_le (by linarith [Real.pi_pos])]
    refine integrableOn_sig.mono_set ?_
    intro x hx
    exact ⟨by linarith [hx.1, Real.pi_pos], hx.2⟩
  rw [← intervalIntegral.integral_add_adjacent_intervals hσ1 hσ2, integral_right_eq_left]
  have := integral_left_le
  linarith [this, Real.pi_le_four]

/-- **The mass of the weight on the left quarter**: `25 ≤ ∫_{[0,π/8]} σ`. -/
private lemma sig_integral_left_ge_25 :
    25 ≤ ∫ θ in Set.Icc (0 : ℝ) (Real.pi / 8), σ θ := by
  have hsub : Set.Icc (0 : ℝ) (Real.pi / 8) ⊆ Work.Spaces.Iθ := by
    intro x hx
    exact ⟨hx.1, by linarith [hx.2, Real.pi_pos]⟩
  have hstep : (∫ θ in Set.Icc (0 : ℝ) (Real.pi / 8), (2 * θ) ^ (-(Work.Spaces.eta)))
      ≤ ∫ θ in Set.Icc (0 : ℝ) (Real.pi / 8), σ θ := by
    refine MeasureTheory.integral_mono_of_nonneg ?_ (integrableOn_sig.mono_set hsub) ?_
    · filter_upwards [ae_restrict_mem measurableSet_Icc] with θ hθ
      exact Real.rpow_nonneg (by linarith [hθ.1]) _
    · filter_upwards [ae_restrict_mem measurableSet_Icc] with θ hθ
      have hs : Real.sin (2 * θ) ≤ 2 * θ := Real.sin_le (by linarith [hθ.1])
      rcases eq_or_lt_of_le hθ.1 with h | h
      · subst h
        rw [mul_zero, Real.zero_rpow (by rw [Work.Spaces.eta]; norm_num)]
        exact sig_nonneg_of_mem (hsub ⟨le_refl 0, by linarith [Real.pi_pos]⟩)
      · rw [Work.FTS.EllipticEst.AngSecond.sig]
        exact Real.rpow_le_rpow_of_nonpos
          (Real.sin_pos_of_pos_of_lt_pi (by linarith) (by linarith [hθ.2, Real.pi_pos])) hs
          (by rw [Work.Spaces.eta]; norm_num)
  have hval : (∫ θ in Set.Icc (0 : ℝ) (Real.pi / 8), (2 * θ) ^ (-(Work.Spaces.eta)))
      = 100 * (2 : ℝ) ^ (-(Work.Spaces.eta)) * (Real.pi / 8) ^ (1 - Work.Spaces.eta) := by
    have hred : (∫ θ in (0 : ℝ)..(Real.pi / 8), (2 * θ) ^ (-(Work.Spaces.eta)))
        = ∫ θ in (0 : ℝ)..(Real.pi / 8),
            (2 : ℝ) ^ (-(Work.Spaces.eta)) * θ ^ (-(Work.Spaces.eta)) := by
      have hae : (fun θ : ℝ => (2 * θ) ^ (-(Work.Spaces.eta)))
          =ᵐ[volume.restrict (Set.Ioc (0 : ℝ) (Real.pi / 8))]
          (fun θ : ℝ => (2 : ℝ) ^ (-(Work.Spaces.eta)) * θ ^ (-(Work.Spaces.eta))) := by
        filter_upwards [MeasureTheory.self_mem_ae_restrict measurableSet_Ioc] with θ hθ
        exact Real.mul_rpow (by norm_num : (0 : ℝ) ≤ 2) (le_of_lt hθ.1)
      rw [intervalIntegral.integral_of_le (by positivity), intervalIntegral.integral_of_le (by positivity)]
      exact MeasureTheory.integral_congr_ae hae
    rw [setIntegral_Icc_eq_intervalIntegral (a := 0) (b := Real.pi / 8) (by positivity), hred,
      intervalIntegral.integral_const_mul,
      integral_rpow (Or.inl (by rw [Work.Spaces.eta]; norm_num : (-1 : ℝ) < -(Work.Spaces.eta)))]
    have hzero : (0 : ℝ) ^ (1 - Work.Spaces.eta) = 0 := by
      refine Real.zero_rpow ?_
      rw [Work.Spaces.eta]; norm_num
    rw [show -(Work.Spaces.eta) + 1 = 1 - Work.Spaces.eta by ring, hzero, sub_zero]
    have hden : (1 : ℝ) - Work.Spaces.eta = 1 / 100 := by rw [Work.Spaces.eta]; norm_num
    rw [hden]
    field_simp
  rw [hval] at hstep
  have h2η : (1 / 2 : ℝ) ≤ (2 : ℝ) ^ (-(Work.Spaces.eta)) := by
    have h1 : (2 : ℝ) ^ (-(1 : ℝ)) ≤ (2 : ℝ) ^ (-(Work.Spaces.eta)) :=
      Real.rpow_le_rpow_of_exponent_le (by norm_num) (by rw [Work.Spaces.eta]; norm_num)
    rw [Real.rpow_neg_one] at h1
    simpa only [one_div] using h1
  have hπ8 : (1 / 2 : ℝ) ≤ (Real.pi / 8) ^ (1 - Work.Spaces.eta) := by
    have hpos : (0 : ℝ) < Real.pi / 8 := by positivity
    have hle1 : Real.pi / 8 ≤ 1 := by have := Real.pi_lt_four; linarith
    have hexp : (1 : ℝ) - Work.Spaces.eta ≤ (1 : ℝ) / 2 := by
      rw [Work.Spaces.eta]; norm_num
    have h1 := Real.rpow_le_rpow_of_exponent_ge hpos hle1 hexp
    have h2 : (1 / 2 : ℝ) ≤ (Real.pi / 8) ^ ((1 : ℝ) / 2) := by
      rw [← Real.sqrt_eq_rpow]
      rw [Real.le_sqrt (by norm_num) (by positivity)]
      nlinarith [Real.pi_gt_three]
    linarith [h1, h2]
  nlinarith [hstep, h2η, hπ8]

/-- **The mass of the weight on the right quarter**: `25 ≤ ∫_{[3π/8,π/2]} σ`. -/
private lemma sig_integral_right_ge_25 :
    25 ≤ ∫ θ in Set.Icc (3 * Real.pi / 8) (Real.pi / 2), σ θ := by
  have hsym : (∫ θ in Set.Icc (3 * Real.pi / 8) (Real.pi / 2), σ θ)
      = ∫ θ in Set.Icc (0 : ℝ) (Real.pi / 8), σ θ := by
    rw [setIntegral_Icc_eq_intervalIntegral (a := 3 * Real.pi / 8) (b := Real.pi / 2)
        (by linarith [Real.pi_pos]),
      setIntegral_Icc_eq_intervalIntegral (a := 0) (b := Real.pi / 8) (by positivity)]
    have h := intervalIntegral.integral_comp_sub_left (a := 3 * Real.pi / 8)
      (b := Real.pi / 2) σ (Real.pi / 2)
    rw [show Real.pi / 2 - Real.pi / 2 = 0 by ring,
      show Real.pi / 2 - 3 * Real.pi / 8 = Real.pi / 8 by ring] at h
    have h2 : (∫ x in (3 * Real.pi / 8)..(Real.pi / 2), σ x)
        = ∫ x in (3 * Real.pi / 8)..(Real.pi / 2), σ (Real.pi / 2 - x) :=
      intervalIntegral.integral_congr (fun x _ => (sig_pi_div_two_sub x).symm)
    rw [h2, h]
  rw [hsym]
  exact sig_integral_left_ge_25

/-! ## 3. Two fundamental-theorem-of-calculus facts for a `C²` slice -/

/-- The oscillation of `u'` about its value at `π/4` is bounded by the total variation of `u''`. -/
private lemma abs_deriv_sub_center_le (u : ℝ → ℝ)
    (hu : ContDiffOn ℝ 2 u (Set.Ioo 0 (Real.pi / 2)))
    (hint : IntegrableOn (fun θ => |deriv (fun t => deriv u t) θ|) Work.Spaces.Iθ) :
    ∀ θ ∈ Set.Ioo (0 : ℝ) (Real.pi / 2),
      |deriv u θ - deriv u (Real.pi / 4)|
        ≤ ∫ θ in Work.Spaces.Iθ, |deriv (fun t => deriv u t) θ| := by
  have hIoo : IsOpen (Set.Ioo (0 : ℝ) (Real.pi / 2)) := isOpen_Ioo
  have hd1 : ContDiffOn ℝ 1 (deriv u) (Set.Ioo (0 : ℝ) (Real.pi / 2)) :=
    hu.deriv_of_isOpen hIoo (m := 1) (by norm_num)
  have hle : (0 : ℝ) ≤ Real.pi / 2 := by positivity
  have hgi : IntervalIntegrable (fun x => |deriv (fun t => deriv u t) x|) volume 0 (Real.pi / 2) :=
    (intervalIntegrable_iff_integrableOn_Icc_of_le hle).mpr (by simpa [Work.Spaces.Iθ] using hint)
  have hIeq : (∫ x in (0 : ℝ)..(Real.pi / 2), |deriv (fun t => deriv u t) x|)
      = ∫ x in Work.Spaces.Iθ, |deriv (fun t => deriv u t) x| := by
    rw [intervalIntegral.integral_of_le hle, ← MeasureTheory.integral_Icc_eq_integral_Ioc]
    rfl
  intro θ hθ
  have h4 : Real.pi / 4 ∈ Set.Ioo (0 : ℝ) (Real.pi / 2) :=
    ⟨by linarith [Real.pi_pos], by linarith [Real.pi_pos]⟩
  have huIcc : Set.uIcc (Real.pi / 4) θ ⊆ Set.Ioo (0 : ℝ) (Real.pi / 2) := by
    intro x hx
    rw [Set.mem_uIcc] at hx
    rcases hx with ⟨h1, h2⟩ | ⟨h1, h2⟩
    · exact ⟨by linarith [h4.1, h1], by linarith [h2, hθ.2]⟩
    · exact ⟨by linarith [hθ.1, h1], by linarith [h2, h4.2]⟩
  have hFTC : (∫ x in (Real.pi / 4)..θ, deriv (fun t => deriv u t) x)
      = deriv u θ - deriv u (Real.pi / 4) :=
    intervalIntegral.integral_deriv_of_contDiffOn_uIcc (hd1.mono huIcc)
  have hkey : ∀ {a b : ℝ}, a ∈ Set.Ioo (0 : ℝ) (Real.pi / 2) →
      b ∈ Set.Ioo (0 : ℝ) (Real.pi / 2) → a ≤ b →
      |∫ x in a..b, deriv (fun t => deriv u t) x|
        ≤ ∫ x in Work.Spaces.Iθ, |deriv (fun t => deriv u t) x| := by
    intro a b ha hb hab
    calc |∫ x in a..b, deriv (fun t => deriv u t) x|
        ≤ ∫ x in a..b, |deriv (fun t => deriv u t) x| :=
          intervalIntegral.abs_integral_le_integral_abs hab
      _ ≤ ∫ x in (0 : ℝ)..(Real.pi / 2), |deriv (fun t => deriv u t) x| :=
          intervalIntegral.integral_mono_interval ha.1.le hab hb.2.le
            (Filter.Eventually.of_forall
              (fun x => abs_nonneg (deriv (fun t => deriv u t) x))) hgi
      _ = ∫ x in Work.Spaces.Iθ, |deriv (fun t => deriv u t) x| := hIeq
  rcases le_total (Real.pi / 4) θ with hlt | hlt
  · rw [← hFTC]; exact hkey h4 hθ hlt
  · have h2 : deriv u θ - deriv u (Real.pi / 4)
        = -(∫ x in θ..(Real.pi / 4), deriv (fun t => deriv u t) x) := by
      rw [← hFTC, intervalIntegral.integral_symm (a := θ) (b := Real.pi / 4)]
    rw [h2, abs_neg]
    exact hkey hθ h4 hlt

/-- The second-order Taylor identity with remainder, centred at `π/4`. -/
private lemma taylor_identity_center (u : ℝ → ℝ)
    (hu : ContDiffOn ℝ 2 u (Set.Ioo 0 (Real.pi / 2))) :
    ∀ θ ∈ Set.Ioo (0 : ℝ) (Real.pi / 2), ∀ φ ∈ Set.Ioo (0 : ℝ) (Real.pi / 2),
      deriv u (Real.pi / 4) * (φ - θ)
        = (u φ - u θ) - ∫ s in θ..φ, (deriv u s - deriv u (Real.pi / 4)) := by
  have hIoo : IsOpen (Set.Ioo (0 : ℝ) (Real.pi / 2)) := isOpen_Ioo
  have hu1 : ContDiffOn ℝ 1 u (Set.Ioo (0 : ℝ) (Real.pi / 2)) := hu.of_le (by norm_num)
  intro θ hθ φ hφ
  have huIcc : Set.uIcc θ φ ⊆ Set.Ioo (0 : ℝ) (Real.pi / 2) := by
    intro x hx
    rw [Set.mem_uIcc] at hx
    rcases hx with ⟨h1, h2⟩ | ⟨h1, h2⟩
    · exact ⟨by linarith [hθ.1, h1], by linarith [h2, hφ.2]⟩
    · exact ⟨by linarith [hφ.1, h1], by linarith [h2, hθ.2]⟩
  have hFTC : (∫ s in θ..φ, deriv u s) = u φ - u θ :=
    intervalIntegral.integral_deriv_of_contDiffOn_uIcc (hu1.mono huIcc)
  have hc : ContinuousOn (deriv u) (Set.uIcc θ φ) :=
    (hu.continuousOn_deriv_of_isOpen hIoo (by norm_num)).mono huIcc
  have hii : IntervalIntegrable (deriv u) volume θ φ := hc.intervalIntegrable
  have hic : IntervalIntegrable (fun _ : ℝ => deriv u (Real.pi / 4)) volume θ φ :=
    intervalIntegrable_const
  have hsub : IntervalIntegrable (fun s : ℝ => deriv u s - deriv u (Real.pi / 4)) volume θ φ :=
    hii.sub hic
  have hsplit : (∫ s in θ..φ, deriv u s)
      = (∫ s in θ..φ, deriv u (Real.pi / 4))
        + ∫ s in θ..φ, (deriv u s - deriv u (Real.pi / 4)) := by
    rw [← intervalIntegral.integral_add hic hsub]
    exact intervalIntegral.integral_congr (fun s _ => by ring)
  rw [hsplit, intervalIntegral.integral_const] at hFTC
  simp only [smul_eq_mul] at hFTC
  linarith [hFTC]

/-! ## 4. The pivot bound -/

/-- **The pivot bound.**  Given the pointwise Taylor inequality relating `c (φ - θ)` to
`u φ - u θ`, the total-variation bound `A` for `u' - c` on the two extreme quarters of `Iθ`
and the mass lower bounds `≥ 25` on those quarters, the pivot satisfies `c² ≤ 12 A² + P`. -/
private lemma pivot_bound (u : ℝ → ℝ) (c A : ℝ) (hA0 : 0 ≤ A)
    (hkey : ∀ θ ∈ Set.Ioo (0 : ℝ) (Real.pi / 8), ∀ φ ∈ Set.Ioo (3 * Real.pi / 8) (Real.pi / 2),
      c ^ 2 * (Real.pi / 4) ^ 2 ≤ 3 * (u φ) ^ 2
        + (3 * (u θ) ^ 2 + 3 * (Real.pi / 2) ^ 2 * A ^ 2))
    (h0int : IntegrableOn (fun θ => (u θ) ^ 2 * σ θ) Work.Spaces.Iθ)
    (hQ1 : 25 ≤ ∫ θ in Set.Icc (0 : ℝ) (Real.pi / 8), σ θ)
    (hQ2 : 25 ≤ ∫ θ in Set.Icc (3 * Real.pi / 8) (Real.pi / 2), σ θ)
    (hP : 0 ≤ ∫ θ in Work.Spaces.Iθ, (u θ) ^ 2 * σ θ) :
    c ^ 2 ≤ 12 * A ^ 2 + ∫ θ in Work.Spaces.Iθ, (u θ) ^ 2 * σ θ := by
  have hsub1 : Set.Icc (0 : ℝ) (Real.pi / 8) ⊆ Work.Spaces.Iθ := by
    intro x hx
    rw [Set.mem_Icc] at hx
    exact ⟨hx.1, by linarith [hx.2, Real.pi_pos]⟩
  have hsub2 : Set.Icc (3 * Real.pi / 8) (Real.pi / 2) ⊆ Work.Spaces.Iθ := by
    intro x hx
    rw [Set.mem_Icc] at hx
    exact ⟨by linarith [hx.1, Real.pi_pos], hx.2⟩
  set Q1 : ℝ := ∫ θ in Set.Icc (0 : ℝ) (Real.pi / 8), σ θ with hQ1def
  set Q2 : ℝ := ∫ θ in Set.Icc (3 * Real.pi / 8) (Real.pi / 2), σ θ with hQ2def
  set J1 : ℝ := ∫ θ in Set.Icc (0 : ℝ) (Real.pi / 8), (u θ) ^ 2 * σ θ with hJ1def
  set J2 : ℝ := ∫ θ in Set.Icc (3 * Real.pi / 8) (Real.pi / 2), (u θ) ^ 2 * σ θ with hJ2def
  set P : ℝ := ∫ θ in Work.Spaces.Iθ, (u θ) ^ 2 * σ θ with hPdef
  have hQ1pos : 0 < Q1 := by linarith
  have hQ2pos : 0 < Q2 := by linarith
  -- ## Step A: integrate the pointwise inequality over the right quarter in `φ`
  have hstepA : ∀ θ ∈ Set.Ioo (0 : ℝ) (Real.pi / 8),
      (c ^ 2 * (Real.pi / 4) ^ 2) * Q2 ≤ 3 * J2
        + (3 * (u θ) ^ 2 + 3 * (Real.pi / 2) ^ 2 * A ^ 2) * Q2 := by
    intro θ hθ
    have hbase : Integrable (fun φ => 3 * ((u φ) ^ 2 * σ φ))
        (volume.restrict (Set.Icc (3 * Real.pi / 8) (Real.pi / 2))) :=
      (h0int.mono_set hsub2).const_mul 3
    have hKK : Integrable (fun φ => (3 * (u θ) ^ 2 + 3 * (Real.pi / 2) ^ 2 * A ^ 2) * σ φ)
        (volume.restrict (Set.Icc (3 * Real.pi / 8) (Real.pi / 2))) :=
      (integrableOn_sig.mono_set hsub2).const_mul _
    have hsum : Integrable (fun φ => (3 * (u φ) ^ 2
        + (3 * (u θ) ^ 2 + 3 * (Real.pi / 2) ^ 2 * A ^ 2)) * σ φ)
        (volume.restrict (Set.Icc (3 * Real.pi / 8) (Real.pi / 2))) :=
      (hbase.add hKK).congr (by
        filter_upwards with φ
        simp only [Pi.add_apply]
        ring)
    have hσi : Integrable (fun φ => (c ^ 2 * (Real.pi / 4) ^ 2) * σ φ)
        (volume.restrict (Set.Icc (3 * Real.pi / 8) (Real.pi / 2))) :=
      (integrableOn_sig.mono_set hsub2).const_mul _
    have hle : (fun φ => (c ^ 2 * (Real.pi / 4) ^ 2) * σ φ)
        ≤ᵐ[volume.restrict (Set.Icc (3 * Real.pi / 8) (Real.pi / 2))]
        (fun φ => (3 * (u φ) ^ 2
          + (3 * (u θ) ^ 2 + 3 * (Real.pi / 2) ^ 2 * A ^ 2)) * σ φ) := by
      rw [Measure.restrict_congr_set (Icc_ae_eq_Ioo (3 * Real.pi / 8) (Real.pi / 2))]
      refine ae_restrict_of_forall_mem measurableSet_Ioo (fun φ hφ => ?_)
      exact mul_le_mul_of_nonneg_right (hkey θ hθ φ hφ)
        (sig_nonneg_of_mem (hsub2 ⟨le_of_lt hφ.1, le_of_lt hφ.2⟩))
    have h := integral_mono_ae hσi hsum hle
    have hIntL : (∫ φ in Set.Icc (3 * Real.pi / 8) (Real.pi / 2),
        (c ^ 2 * (Real.pi / 4) ^ 2) * σ φ) = (c ^ 2 * (Real.pi / 4) ^ 2) * Q2 := by
      rw [MeasureTheory.integral_const_mul, hQ2def]
    have hEq : (∫ φ in Set.Icc (3 * Real.pi / 8) (Real.pi / 2),
          (3 * (u φ) ^ 2 + (3 * (u θ) ^ 2 + 3 * (Real.pi / 2) ^ 2 * A ^ 2)) * σ φ)
        = (∫ φ in Set.Icc (3 * Real.pi / 8) (Real.pi / 2),
          3 * ((u φ) ^ 2 * σ φ)
            + (3 * (u θ) ^ 2 + 3 * (Real.pi / 2) ^ 2 * A ^ 2) * σ φ) := by
      refine MeasureTheory.setIntegral_congr_fun measurableSet_Icc (fun φ _ => ?_)
      ring
    have hIntR : (∫ φ in Set.Icc (3 * Real.pi / 8) (Real.pi / 2),
          3 * ((u φ) ^ 2 * σ φ)
            + (3 * (u θ) ^ 2 + 3 * (Real.pi / 2) ^ 2 * A ^ 2) * σ φ)
        = 3 * J2 + (3 * (u θ) ^ 2 + 3 * (Real.pi / 2) ^ 2 * A ^ 2) * Q2 := by
      rw [MeasureTheory.integral_add hbase hKK, MeasureTheory.integral_const_mul,
        MeasureTheory.integral_const_mul, ← hJ2def, ← hQ2def]
    rw [hIntL, hEq, hIntR] at h
    exact h
  -- ## Step B: integrate the result over the left quarter in `θ`
  have hstepB : ((c ^ 2 * (Real.pi / 4) ^ 2) * Q2) * Q1 ≤ 3 * J2 * Q1 + 3 * Q2 * J1
      + (3 * (Real.pi / 2) ^ 2 * A ^ 2) * (Q1 * Q2) := by
    have hbase : Integrable (fun θ => (3 * J2) * σ θ)
        (volume.restrict (Set.Icc (0 : ℝ) (Real.pi / 8))) :=
      (integrableOn_sig.mono_set hsub1).const_mul _
    have hIi : Integrable (fun θ => (3 * Q2) * ((u θ) ^ 2 * σ θ))
        (volume.restrict (Set.Icc (0 : ℝ) (Real.pi / 8))) :=
      (h0int.mono_set hsub1).const_mul _
    have hBi : Integrable (fun θ => ((3 * (Real.pi / 2) ^ 2 * A ^ 2) * Q2) * σ θ)
        (volume.restrict (Set.Icc (0 : ℝ) (Real.pi / 8))) :=
      (integrableOn_sig.mono_set hsub1).const_mul _
    have hsum : Integrable (fun θ => (3 * J2
        + (3 * (u θ) ^ 2 + 3 * (Real.pi / 2) ^ 2 * A ^ 2) * Q2) * σ θ)
        (volume.restrict (Set.Icc (0 : ℝ) (Real.pi / 8))) :=
      (hbase.add (hIi.add hBi)).congr (by
        filter_upwards with θ
        simp only [Pi.add_apply]
        ring)
    have hσi : Integrable (fun θ => ((c ^ 2 * (Real.pi / 4) ^ 2) * Q2) * σ θ)
        (volume.restrict (Set.Icc (0 : ℝ) (Real.pi / 8))) :=
      (integrableOn_sig.mono_set hsub1).const_mul _
    have hle : (fun θ => ((c ^ 2 * (Real.pi / 4) ^ 2) * Q2) * σ θ)
        ≤ᵐ[volume.restrict (Set.Icc (0 : ℝ) (Real.pi / 8))]
        (fun θ => (3 * J2 + (3 * (u θ) ^ 2 + 3 * (Real.pi / 2) ^ 2 * A ^ 2) * Q2) * σ θ) := by
      rw [Measure.restrict_congr_set (Icc_ae_eq_Ioo 0 (Real.pi / 8))]
      refine ae_restrict_of_forall_mem measurableSet_Ioo (fun θ hθ => ?_)
      exact mul_le_mul_of_nonneg_right (hstepA θ hθ)
        (sig_nonneg_of_mem (hsub1 ⟨le_of_lt hθ.1, le_of_lt hθ.2⟩))
    have h := integral_mono_ae hσi hsum hle
    have hIntL : (∫ θ in Set.Icc (0 : ℝ) (Real.pi / 8),
        ((c ^ 2 * (Real.pi / 4) ^ 2) * Q2) * σ θ)
        = ((c ^ 2 * (Real.pi / 4) ^ 2) * Q2) * Q1 := by
      rw [MeasureTheory.integral_const_mul, hQ1def]
    have hbase2 : Integrable (fun θ => 3 * ((u θ) ^ 2 * σ θ))
        (volume.restrict (Set.Icc (0 : ℝ) (Real.pi / 8))) :=
      (h0int.mono_set hsub1).const_mul 3
    have hc2 : Integrable (fun θ => (3 * (Real.pi / 2) ^ 2 * A ^ 2) * σ θ)
        (volume.restrict (Set.Icc (0 : ℝ) (Real.pi / 8))) :=
      (integrableOn_sig.mono_set hsub1).const_mul _
    have hKy : Integrable (fun θ => (3 * (u θ) ^ 2 + 3 * (Real.pi / 2) ^ 2 * A ^ 2) * σ θ)
        (volume.restrict (Set.Icc (0 : ℝ) (Real.pi / 8))) :=
      (hbase2.add hc2).congr (by
        filter_upwards with θ
        simp only [Pi.add_apply]
        ring)
    have hKK : Integrable (fun θ =>
        ((3 * (u θ) ^ 2 + 3 * (Real.pi / 2) ^ 2 * A ^ 2) * Q2) * σ θ)
        (volume.restrict (Set.Icc (0 : ℝ) (Real.pi / 8))) :=
      hKy.const_mul Q2 |>.congr (by
        filter_upwards with θ
        ring)
    have hE1 : (∫ θ in Set.Icc (0 : ℝ) (Real.pi / 8),
          (3 * J2 + (3 * (u θ) ^ 2 + 3 * (Real.pi / 2) ^ 2 * A ^ 2) * Q2) * σ θ)
        = (∫ θ in Set.Icc (0 : ℝ) (Real.pi / 8),
            (3 * J2) * σ θ
              + ((3 * (u θ) ^ 2 + 3 * (Real.pi / 2) ^ 2 * A ^ 2) * Q2) * σ θ) := by
      refine MeasureTheory.setIntegral_congr_fun measurableSet_Icc (fun θ _ => ?_)
      ring
    have hE2 : (∫ θ in Set.Icc (0 : ℝ) (Real.pi / 8),
            (3 * J2) * σ θ
              + ((3 * (u θ) ^ 2 + 3 * (Real.pi / 2) ^ 2 * A ^ 2) * Q2) * σ θ)
        = 3 * J2 * Q1 + (∫ θ in Set.Icc (0 : ℝ) (Real.pi / 8),
            ((3 * (u θ) ^ 2 + 3 * (Real.pi / 2) ^ 2 * A ^ 2) * Q2) * σ θ) := by
      rw [MeasureTheory.integral_add hbase hKK, MeasureTheory.integral_const_mul, ← hQ1def]
    have hE3 : (∫ θ in Set.Icc (0 : ℝ) (Real.pi / 8),
            ((3 * (u θ) ^ 2 + 3 * (Real.pi / 2) ^ 2 * A ^ 2) * Q2) * σ θ)
        = Q2 * (∫ θ in Set.Icc (0 : ℝ) (Real.pi / 8),
            (3 * (u θ) ^ 2 + 3 * (Real.pi / 2) ^ 2 * A ^ 2) * σ θ) := by
      have heq : (fun θ : ℝ => ((3 * (u θ) ^ 2 + 3 * (Real.pi / 2) ^ 2 * A ^ 2) * Q2) * σ θ)
          = fun θ : ℝ => Q2 * ((3 * (u θ) ^ 2 + 3 * (Real.pi / 2) ^ 2 * A ^ 2) * σ θ) := by
        funext θ
        ring
      rw [heq, MeasureTheory.integral_const_mul]
    have hE4 : (∫ θ in Set.Icc (0 : ℝ) (Real.pi / 8),
            (3 * (u θ) ^ 2 + 3 * (Real.pi / 2) ^ 2 * A ^ 2) * σ θ)
        = (∫ θ in Set.Icc (0 : ℝ) (Real.pi / 8),
            3 * ((u θ) ^ 2 * σ θ) + (3 * (Real.pi / 2) ^ 2 * A ^ 2) * σ θ) := by
      refine MeasureTheory.setIntegral_congr_fun measurableSet_Icc (fun θ _ => ?_)
      ring
    have hE5 : (∫ θ in Set.Icc (0 : ℝ) (Real.pi / 8),
            3 * ((u θ) ^ 2 * σ θ) + (3 * (Real.pi / 2) ^ 2 * A ^ 2) * σ θ)
        = 3 * J1 + 3 * (Real.pi / 2) ^ 2 * A ^ 2 * Q1 := by
      rw [MeasureTheory.integral_add hbase2 hc2, MeasureTheory.integral_const_mul,
        MeasureTheory.integral_const_mul, ← hJ1def, ← hQ1def]
    have hE6 : (∫ θ in Set.Icc (0 : ℝ) (Real.pi / 8),
          (3 * J2 + (3 * (u θ) ^ 2 + 3 * (Real.pi / 2) ^ 2 * A ^ 2) * Q2) * σ θ)
        = 3 * J2 * Q1 + 3 * Q2 * J1 + (3 * (Real.pi / 2) ^ 2 * A ^ 2) * (Q1 * Q2) := by
      rw [hE1, hE2, hE3, hE4, hE5]
      ring
    rw [hIntL, hE6] at h
    exact h
  -- ## Step C: divide by `Q1 Q2 ≥ 625` and use `J1, J2 ≤ P`
  have hJ1le : J1 ≤ P := by
    rw [hJ1def, hPdef]
    refine MeasureTheory.setIntegral_mono_set h0int ?_ ?_
    · filter_upwards [ae_restrict_mem measurableSet_Icc] with x hx
      exact mul_nonneg (sq_nonneg _) (sig_nonneg_of_mem hx)
    · filter_upwards with x hx
      rw [Set.mem_Icc] at hx
      exact ⟨hx.1, by linarith [hx.2, Real.pi_pos]⟩
  have hJ2le : J2 ≤ P := by
    rw [hJ2def, hPdef]
    refine MeasureTheory.setIntegral_mono_set h0int ?_ ?_
    · filter_upwards [ae_restrict_mem measurableSet_Icc] with x hx
      exact mul_nonneg (sq_nonneg _) (sig_nonneg_of_mem hx)
    · filter_upwards with x hx
      rw [Set.mem_Icc] at hx
      exact ⟨by linarith [hx.1, Real.pi_pos], hx.2⟩
  have hdiv : c ^ 2 * (Real.pi / 4) ^ 2 ≤ 6 * P / 25 + 3 * (Real.pi / 2) ^ 2 * A ^ 2 := by
    have hQpos : 0 < Q1 * Q2 := mul_pos hQ1pos hQ2pos
    have hb1 : 3 * J2 * Q1 ≤ (3 * P / 25) * (Q1 * Q2) := by
      have h25 : J2 * 25 ≤ P * Q2 := mul_le_mul hJ2le hQ2 (by norm_num) hP
      nlinarith [h25, hQ1pos.le]
    have hb2 : 3 * Q2 * J1 ≤ (3 * P / 25) * (Q1 * Q2) := by
      have h25 : J1 * 25 ≤ P * Q1 := mul_le_mul hJ1le hQ1 (by norm_num) hP
      nlinarith [h25, hQ2pos.le]
    have hmain : ((c ^ 2 * (Real.pi / 4) ^ 2) * Q2) * Q1
        ≤ (6 * P / 25 + 3 * (Real.pi / 2) ^ 2 * A ^ 2) * (Q1 * Q2) := by
      nlinarith [hstepB, hb1, hb2]
    refine le_of_mul_le_mul_right ?_ hQpos
    nlinarith [hmain]
  -- ## Step D: `(π/4)²` to `π²/16`, using `π² ≥ 4`
  have hPI : c ^ 2 ≤ 12 * A ^ 2 + P := by
    have hpi2 : (4 : ℝ) ≤ Real.pi ^ 2 := by nlinarith [Real.pi_gt_three]
    have hπ : Real.pi ≠ 0 := ne_of_gt Real.pi_pos
    have hL : (c ^ 2 * (Real.pi / 4) ^ 2) * (16 / Real.pi ^ 2) = c ^ 2 := by
      field_simp
      ring
    have hmul := mul_le_mul_of_nonneg_right hdiv (by positivity : (0 : ℝ) ≤ 16 / Real.pi ^ 2)
    rw [hL] at hmul
    have hR : (6 * P / 25 + 3 * (Real.pi / 2) ^ 2 * A ^ 2) * (16 / Real.pi ^ 2)
        ≤ P + 12 * A ^ 2 := by
      have h1 : (3 * (Real.pi / 2) ^ 2 * A ^ 2) * (16 / Real.pi ^ 2) = 12 * A ^ 2 := by
        field_simp
        ring
      have h2 : (6 * P / 25) * (16 / Real.pi ^ 2) ≤ P := by
        have heq : (6 * P / 25) * (16 / Real.pi ^ 2) = 96 * P / (25 * Real.pi ^ 2) := by
          field_simp
          ring
        rw [heq, div_le_iff₀ (by positivity : (0 : ℝ) < 25 * Real.pi ^ 2)]
        nlinarith [hpi2, hP]
      nlinarith [h1, h2]
    linarith [hmul, hR]
  linarith [hPI]

/-! ## 5. The main theorem -/

theorem sliceInterp (u : ℝ → ℝ)
    (hu : ContDiffOn ℝ 2 u (Set.Ioo 0 (Real.pi / 2)))
    (h0 : MeasureTheory.IntegrableOn
      (fun θ => (u θ) ^ 2 * Work.FTS.EllipticEst.AngSecond.sig θ) Work.Spaces.Iθ)
    (h2 : MeasureTheory.IntegrableOn
      (fun θ => (deriv (fun t => deriv u t) θ) ^ 2
        * Work.FTS.EllipticEst.AngSecond.sig θ) Work.Spaces.Iθ) :
    MeasureTheory.IntegrableOn
      (fun θ => (deriv u θ) ^ 2 * Work.FTS.EllipticEst.AngSecond.sig θ) Work.Spaces.Iθ ∧
    (∫ θ in Work.Spaces.Iθ, (deriv u θ) ^ 2 * Work.FTS.EllipticEst.AngSecond.sig θ)
      ≤ 10000 * ((∫ θ in Work.Spaces.Iθ,
            (u θ) ^ 2 * Work.FTS.EllipticEst.AngSecond.sig θ)
        + (∫ θ in Work.Spaces.Iθ, (deriv (fun t => deriv u t) θ) ^ 2
            * Work.FTS.EllipticEst.AngSecond.sig θ)) := by
  have hIoo : IsOpen (Set.Ioo (0 : ℝ) (Real.pi / 2)) := isOpen_Ioo
  have hcont : ContinuousOn (deriv u) (Set.Ioo (0 : ℝ) (Real.pi / 2)) :=
    hu.continuousOn_deriv_of_isOpen hIoo (by norm_num)
  have hd1 : ContDiffOn ℝ 1 (deriv u) (Set.Ioo (0 : ℝ) (Real.pi / 2)) :=
    hu.deriv_of_isOpen hIoo (m := 1) (by norm_num)
  have hd2cont : ContinuousOn (deriv (fun t => deriv u t)) (Set.Ioo (0 : ℝ) (Real.pi / 2)) :=
    contDiffOn_zero.1 (hd1.deriv_of_isOpen hIoo (m := 0) (by norm_num))
  have hAbs : IntegrableOn (fun θ => |deriv (fun t => deriv u t) θ|) Work.Spaces.Iθ :=
    Work.FTS.EllipticEst.integrableAbsOfSqSeta hd2cont
      (by simpa [Work.FTS.EllipticEst.AngSecond.sig, Work.FTS.EllipticEst.sEta] using h2)
  set A : ℝ := ∫ θ in Work.Spaces.Iθ, |deriv (fun t => deriv u t) θ| with hAdef
  set E : ℝ := ∫ θ in Work.Spaces.Iθ, (deriv (fun t => deriv u t) θ) ^ 2 * σ θ with hEdef
  set P : ℝ := ∫ θ in Work.Spaces.Iθ, (u θ) ^ 2 * σ θ with hPdef
  set c : ℝ := deriv u (Real.pi / 4) with hcdef
  have hAnn : 0 ≤ A :=
    MeasureTheory.setIntegral_nonneg measurableSet_Icc
      (fun x _ => abs_nonneg (deriv (fun t => deriv u t) x))
  have hEnn : 0 ≤ E :=
    MeasureTheory.setIntegral_nonneg measurableSet_Icc
      (fun x hx => mul_nonneg (sq_nonneg _) (sig_nonneg_of_mem hx))
  have hPnn : 0 ≤ P :=
    MeasureTheory.setIntegral_nonneg measurableSet_Icc
      (fun x hx => mul_nonneg (sq_nonneg _) (sig_nonneg_of_mem hx))
  have hWnn : 0 ≤ ∫ θ in Work.Spaces.Iθ, σ θ :=
    MeasureTheory.setIntegral_nonneg measurableSet_Icc (fun x hx => sig_nonneg_of_mem hx)
  -- ## the pointwise and Taylor facts
  have hpt : ∀ θ ∈ Set.Ioo (0 : ℝ) (Real.pi / 2), |deriv u θ - c| ≤ A := by
    intro θ hθ
    simpa only [hcdef, hAdef] using abs_deriv_sub_center_le u hu hAbs θ hθ
  have hty := taylor_identity_center u hu
  -- ## Cauchy–Schwarz: `A² ≤ (π/2) E`
  have hA2 : A ^ 2 ≤ (Real.pi / 2) * E := by
    have hst := Iθ_ae_eq_Ioo
    have hAint : IntegrableOn (fun θ => (deriv (fun t => deriv u t) θ) ^ 2 * σ θ)
        (Set.Ioo (0 : ℝ) (Real.pi / 2)) := h2.mono_set Ioo_subset_Iθ
    have hint1 : IntegrableOn (fun _ : ℝ => (1 : ℝ)) (Set.Ioo (0 : ℝ) (Real.pi / 2)) :=
      integrableOn_const (by rw [Real.volume_Ioo]; exact ENNReal.ofReal_ne_top)
    have hCint : IntegrableOn (fun θ => |deriv (fun t => deriv u t) θ|)
        (Set.Ioo (0 : ℝ) (Real.pi / 2)) := hAbs.mono_set Ioo_subset_Iθ
    have hdom : ∀ z ∈ Set.Ioo (0 : ℝ) (Real.pi / 2),
        abs (|deriv (fun t => deriv u t) z|) ≤
          Real.sqrt ((deriv (fun t => deriv u t) z) ^ 2 * σ z)
            * Real.sqrt ((fun _ : ℝ => (1 : ℝ)) z) := by
      intro z hz
      have hσ1 : 1 ≤ σ z := Work.FTS.EllipticEst.AngSecond.one_le_sig hz
      have hsq : (0 : ℝ) ≤ (deriv (fun t => deriv u t) z) ^ 2 := sq_nonneg _
      have h1 : Real.sqrt ((deriv (fun t => deriv u t) z) ^ 2 * σ z)
          = |deriv (fun t => deriv u t) z| * Real.sqrt (σ z) := by
        rw [Real.sqrt_mul hsq, Real.sqrt_sq_eq_abs]
      have h2 : (1 : ℝ) ≤ Real.sqrt (σ z) :=
        (Real.le_sqrt (by norm_num) (by positivity)).mpr (by simpa using hσ1)
      have h3 : abs (|deriv (fun t => deriv u t) z|) = |deriv (fun t => deriv u t) z| :=
        abs_of_nonneg (abs_nonneg _)
      simp only [Real.sqrt_one, mul_one]
      rw [h3, h1]
      nlinarith [abs_nonneg (deriv (fun t => deriv u t) z)]
    have hcs := Work.FTS.EllipticEst.AngSecond.abs_setIntegral_le_sqrt_mul_sqrt
      (s := Set.Ioo (0 : ℝ) (Real.pi / 2))
      (A := fun z => (deriv (fun t => deriv u t) z) ^ 2 * σ z)
      (B := fun _ : ℝ => (1 : ℝ))
      (C := fun z => |deriv (fun t => deriv u t) z|)
      hAint hint1 hCint
      (fun z hz => mul_nonneg (sq_nonneg _) (sig_nonneg_of_mem (Ioo_subset_Iθ hz)))
      (fun z hz => zero_le_one) hdom
    have hL : abs (∫ z in Set.Ioo (0 : ℝ) (Real.pi / 2), |deriv (fun t => deriv u t) z|) = A := by
      rw [abs_of_nonneg (MeasureTheory.setIntegral_nonneg measurableSet_Ioo
        (fun x _ => abs_nonneg _)), hAdef]
      exact MeasureTheory.setIntegral_congr_set hst.symm
    have hR1 : (∫ z in Set.Ioo (0 : ℝ) (Real.pi / 2),
        (deriv (fun t => deriv u t) z) ^ 2 * σ z) = E := by
      rw [hEdef]
      exact MeasureTheory.setIntegral_congr_set hst.symm
    have hR2 : (∫ z in Set.Ioo (0 : ℝ) (Real.pi / 2), (1 : ℝ)) = Real.pi / 2 := by
      rw [MeasureTheory.setIntegral_const, MeasureTheory.measureReal_def, Real.volume_Ioo,
        ENNReal.toReal_ofReal (by linarith [Real.pi_pos])]
      simp
    rw [hL, hR1, hR2] at hcs
    have hsq : (Real.sqrt E * Real.sqrt (Real.pi / 2)) ^ 2 = E * (Real.pi / 2) := by
      rw [mul_pow, Real.sq_sqrt hEnn, Real.sq_sqrt (by positivity)]
    calc A ^ 2 ≤ (Real.sqrt E * Real.sqrt (Real.pi / 2)) ^ 2 :=
          pow_le_pow_left₀ hAnn hcs 2
      _ = E * (Real.pi / 2) := hsq
      _ = (Real.pi / 2) * E := by ring
  -- ## the pointwise Taylor inequality on the two extreme quarters
  have hkey : ∀ θ ∈ Set.Ioo (0 : ℝ) (Real.pi / 8),
      ∀ φ ∈ Set.Ioo (3 * Real.pi / 8) (Real.pi / 2),
      c ^ 2 * (Real.pi / 4) ^ 2 ≤ 3 * (u φ) ^ 2
        + (3 * (u θ) ^ 2 + 3 * (Real.pi / 2) ^ 2 * A ^ 2) := by
    intro θ hθ φ hφ
    have hθI : θ ∈ Set.Ioo (0 : ℝ) (Real.pi / 2) :=
      ⟨hθ.1, by linarith [hθ.2, Real.pi_pos]⟩
    have hφI : φ ∈ Set.Ioo (0 : ℝ) (Real.pi / 2) :=
      ⟨by linarith [hφ.1, Real.pi_pos], hφ.2⟩
    have hle : θ ≤ φ := by linarith [hθ.2, hφ.1, Real.pi_pos]
    have ht : c * (φ - θ) = (u φ - u θ) - ∫ s in θ..φ, (deriv u s - c) := by
      rw [hcdef]
      exact hty θ hθI φ hφI
    have huIcc : Set.uIcc θ φ ⊆ Set.Ioo (0 : ℝ) (Real.pi / 2) := by
      intro x hx
      rw [Set.mem_uIcc] at hx
      rcases hx with ⟨h1, h2⟩ | ⟨h1, h2⟩
      · exact ⟨by linarith [hθI.1, h1], by linarith [h2, hφI.2]⟩
      · exact ⟨by linarith [hφI.1, h1], by linarith [h2, hθI.2]⟩
    have hcont1 : ContinuousOn (fun s => deriv u s - c) (Set.uIcc θ φ) :=
      (hcont.mono huIcc).sub continuousOn_const
    have hii : IntervalIntegrable (fun s => deriv u s - c) volume θ φ :=
      hcont1.intervalIntegrable
    have hInt : |∫ s in θ..φ, (deriv u s - c)| ≤ (φ - θ) * A := by
      have hmono : (∫ s in θ..φ, |deriv u s - c|) ≤ ∫ s in θ..φ, A := by
        refine intervalIntegral.integral_mono_on_of_le_Ioo hle hii.abs intervalIntegrable_const ?_
        intro s hs
        exact hpt s ⟨by linarith [hθI.1, hs.1], by linarith [hs.2, hφI.2]⟩
      rw [intervalIntegral.integral_const, smul_eq_mul] at hmono
      exact (intervalIntegral.abs_integral_le_integral_abs hle).trans hmono
    have hφθpos : 0 < φ - θ := by linarith [hθ.2, hφ.1, Real.pi_pos]
    have h1 : |c| * (φ - θ) ≤ |u φ| + |u θ| + (φ - θ) * A := by
      have h3 : |c * (φ - θ)| ≤ |u φ - u θ| + |∫ s in θ..φ, (deriv u s - c)| := by
        rw [ht]
        exact abs_sub_le_abs_add_abs _ _
      rw [abs_mul, abs_of_pos hφθpos] at h3
      have h4 : |u φ - u θ| ≤ |u φ| + |u θ| := abs_sub_le_abs_add_abs _ _
      linarith [h3, h4, hInt]
    have hπ4 : Real.pi / 4 ≤ φ - θ := by linarith [hθ.2, hφ.1, Real.pi_pos]
    have h5 : |c| * (Real.pi / 4) ≤ |u φ| + |u θ| + (Real.pi / 2) * A := by
      have h6 : |c| * (Real.pi / 4) ≤ |c| * (φ - θ) :=
        mul_le_mul_of_nonneg_left hπ4 (abs_nonneg c)
      have h7 : (φ - θ) * A ≤ (Real.pi / 2) * A := by
        have h8 : φ - θ ≤ Real.pi / 2 := by linarith [hθI.1, hφI.2]
        exact mul_le_mul_of_nonneg_right h8 hAnn
      linarith [h1, h6, h7]
    have hsq1 : (|c| * (Real.pi / 4)) ^ 2 ≤ (|u φ| + |u θ| + (Real.pi / 2) * A) ^ 2 :=
      pow_le_pow_left₀ (by positivity) h5 2
    have hsq2 : (|u φ| + |u θ| + (Real.pi / 2) * A) ^ 2
        ≤ 3 * (u φ) ^ 2 + 3 * (u θ) ^ 2 + 3 * (Real.pi / 2) ^ 2 * A ^ 2 := by
      have h8 : (|u φ| + |u θ| + (Real.pi / 2) * A) ^ 2
          ≤ 3 * ((u φ) ^ 2 + (u θ) ^ 2 + ((Real.pi / 2) * A) ^ 2) := by
        nlinarith [sq_nonneg (|u φ| - |u θ|), sq_nonneg (|u θ| - (Real.pi / 2) * A),
          sq_nonneg (|u φ| - (Real.pi / 2) * A), sq_abs (u φ), sq_abs (u θ)]
      nlinarith [h8]
    have hlhs : (|c| * (Real.pi / 4)) ^ 2 = c ^ 2 * (Real.pi / 4) ^ 2 := by
      rw [mul_pow, sq_abs]
    linarith [hsq1, hsq2, hlhs]
  -- ## the pivot bound
  have hpiv : c ^ 2 ≤ 12 * A ^ 2 + P := by
    have h := pivot_bound u c A hAnn hkey h0 sig_integral_left_ge_25
      sig_integral_right_ge_25 hPnn
    rw [← hPdef] at h
    exact h
  -- ## the pointwise domination of `(u')²`
  have hσmeas : Measurable σ :=
    Measurable.pow_const (Real.measurable_sin.comp (measurable_const.mul measurable_id)) _
  have hms : volume.restrict Work.Spaces.Iθ
      = volume.restrict (Set.Ioo (0 : ℝ) (Real.pi / 2)) :=
    Measure.restrict_congr_set Iθ_ae_eq_Ioo
  have haesm1 : AEStronglyMeasurable (deriv u) (volume.restrict Work.Spaces.Iθ) := by
    rw [hms]
    exact hcont.aestronglyMeasurable measurableSet_Ioo
  have haesm : AEStronglyMeasurable (fun θ => (deriv u θ) ^ 2 * σ θ)
      (volume.restrict Work.Spaces.Iθ) := (haesm1.pow 2).mul hσmeas.aestronglyMeasurable
  have hbdae : ∀ᵐ θ ∂(volume.restrict Work.Spaces.Iθ),
      (deriv u θ) ^ 2 * σ θ ≤ (2 * A ^ 2 + 2 * c ^ 2) * σ θ := by
    filter_upwards [ae_restrict_mem measurableSet_Icc] with θ hθ
    have hσnn : 0 ≤ σ θ := sig_nonneg_of_mem hθ
    rcases eq_or_lt_of_le hθ.1 with h | h
    · subst h
      simp only [sig_zero_left, mul_zero, le_refl]
    · rcases eq_or_lt_of_le hθ.2 with h2 | h2
      · subst h2
        simp only [sig_zero_right, mul_zero, le_refl]
      · have hp := hpt θ ⟨h, h2⟩
        have hx : (deriv u θ - c) ^ 2 ≤ A ^ 2 := by
          nlinarith [hp, sq_abs (deriv u θ - c), abs_nonneg (deriv u θ - c), hAnn]
        have hbd : (deriv u θ) ^ 2 ≤ 2 * A ^ 2 + 2 * c ^ 2 := by
          nlinarith [hx, sq_nonneg (deriv u θ - c - c)]
        exact mul_le_mul_of_nonneg_right hbd hσnn
  have hbdint : IntegrableOn (fun θ => (2 * A ^ 2 + 2 * c ^ 2) * σ θ) Work.Spaces.Iθ :=
    integrableOn_sig.const_mul _
  have habs : IntegrableOn (fun θ => (deriv u θ) ^ 2 * σ θ) Work.Spaces.Iθ := by
    refine hbdint.mono' haesm ?_
    filter_upwards [hbdae, ae_restrict_mem measurableSet_Icc] with θ h1 h2
    rwa [Real.norm_of_nonneg (mul_nonneg (sq_nonneg _) (sig_nonneg_of_mem h2))]
  -- ## assembly
  have hint_le : (∫ θ in Work.Spaces.Iθ, (deriv u θ) ^ 2 * σ θ)
      ≤ (2 * A ^ 2 + 2 * c ^ 2) * (∫ θ in Work.Spaces.Iθ, σ θ) := by
    have h := integral_mono_ae habs hbdint hbdae
    rwa [MeasureTheory.integral_const_mul] at h
  have hfin : (∫ θ in Work.Spaces.Iθ, (deriv u θ) ^ 2 * σ θ) ≤ 10000 * (P + E) := by
    have hW : (∫ θ in Work.Spaces.Iθ, σ θ) ≤ 200 := sig_integral_Iθ_le_200
    have hpiv' : c ^ 2 + A ^ 2 ≤ 13 * A ^ 2 + P := by linarith [hpiv]
    have h3 : 2 * (∫ θ in Work.Spaces.Iθ, σ θ) * (c ^ 2 + A ^ 2)
        ≤ 2 * 200 * (13 * A ^ 2 + P) := by
      nlinarith [hW, hpiv', hWnn, sq_nonneg c, sq_nonneg A]
    have h4 : 2 * 200 * (13 * A ^ 2 + P) ≤ 2 * 200 * (13 * ((Real.pi / 2) * E) + P) := by
      nlinarith [hA2, hEnn, hPnn, hAnn]
    have h5 : 2 * 200 * (13 * ((Real.pi / 2) * E) + P) ≤ 10000 * (P + E) := by
      have hπ : Real.pi ≤ 3.15 := Real.pi_lt_d2.le
      nlinarith [hπ, hEnn, hPnn, Real.pi_pos]
    linarith [hint_le, h3, h4, h5]
  exact ⟨habs, hfin⟩

end

end Work.FTS.EllipticEst.Honest
