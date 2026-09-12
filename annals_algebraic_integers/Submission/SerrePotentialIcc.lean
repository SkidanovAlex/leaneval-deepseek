import Submission.Serre
import Submission.SerreExample
import Submission.SerreConstantNeg
import Submission.PotentialDefs
import Submission.SerreLogMoment
import Submission.BalayOnIcc
import Submission.EquilibriumPotentialIcc
import Submission.LogSingularIntegral
import Submission.PotentialContinuity
import Submission.WeightedNorm
import Mathlib.Analysis.SpecialFunctions.Exp
import Mathlib.Analysis.SpecialFunctions.Pow.Real

/-!
# The explicit Serre potential on `[aSerre, bSerre]`

Serre's measure `μ = γ·ν + (1−γ)·μ_[a,b]` is tuned so that its logarithmic
potential is affine in `log x` on the interval:

    U^μ(x) = serreConstant − γ·log x        for x ∈ [aSerre, bSerre]

(`serreConstant < 0` is tiny, ≈ −1.3·10⁻⁷.)  Consequences:

* the weight is explicit: `w_μ(x) = e^{serreConstant}·x^{−γ}` on the interval;
* `log w_μ` is bounded on the interval;
* the potential is Lipschitz (hence 1/2-Hölder) on the interval with
  constant `γ / aSerre`  —  the paper's `lem:pot_Hold` specialised.
-/

noncomputable section

open MeasureTheory
open Filter
open ComplexOrder
open scoped Real ENNReal

namespace Submission.SerrePotentialIcc

open Submission.PotentialDefs
open Submission.Serre
open Submission.SerreExample
open Submission.Equilibrium
open Submission.WeightedNorm

/-- The log-potential integrand (at a complex point). -/
def integrand (z : ℂ) (t : ℝ) : ℝ := -Real.log ‖z - (t : ℂ)‖

/-- Integrability of the log-potential integrand against `ν` at real `x` in
the interval. -/
lemma integrable_integrand_nu {x : ℝ} (hx : x ∈ Set.Icc aSerre bSerre) :
    Integrable (integrand (x : ℂ)) (nu aSerre bSerre) := by
  have h1 : Integrable (fun t : ℝ => Real.log ‖(t : ℂ) - (x : ℂ)‖) (nu aSerre bSerre) :=
    Submission.LogSingularIntegral.nu_log_sub_integrable (a := aSerre) (b := bSerre)
      aSerre_pos (by norm_num [aSerre, bSerre]) hx
  have hEq : (fun t : ℝ => -Real.log ‖(t : ℂ) - (x : ℂ)‖) =ᵐ[nu aSerre bSerre]
      integrand (x : ℂ) := by
    apply Eventually.of_forall
    intro t
    unfold integrand
    change -Real.log ‖(t : ℂ) - (x : ℂ)‖ = -Real.log ‖(x : ℂ) - (t : ℂ)‖
    congr 1
    exact congrArg Real.log (norm_sub_rev (t : ℂ) (x : ℂ))
  exact h1.neg.congr hEq

/-- Integrability of the log-potential integrand against the equilibrium
measure at real `x` in the interval. -/
lemma integrable_integrand_eq {x : ℝ} (hx : x ∈ Set.Icc aSerre bSerre) :
    Integrable (integrand (x : ℂ)) (equilibrium aSerre bSerre) := by
  have h1 : Integrable (fun t : ℝ => Real.log ‖(t : ℂ) - (x : ℂ)‖) (equilibrium aSerre bSerre) :=
    Submission.LogSingularIntegral.equilibrium_log_sub_integrable (a := aSerre) (b := bSerre)
      (by norm_num [aSerre, bSerre]) hx
  have hEq : (fun t : ℝ => -Real.log ‖(t : ℂ) - (x : ℂ)‖) =ᵐ[equilibrium aSerre bSerre]
      integrand (x : ℂ) := by
    apply Eventually.of_forall
    intro t
    unfold integrand
    change -Real.log ‖(t : ℂ) - (x : ℂ)‖ = -Real.log ‖(x : ℂ) - (t : ℂ)‖
    congr 1
    exact congrArg Real.log (norm_sub_rev (t : ℂ) (x : ℂ))
  exact h1.neg.congr hEq

/-- Linearity of the potential in the convex combination, at real `x` in the
interval:  `U^μ(x) = γ·U^ν(x) + (1−γ)·U^{μ_[a,b]}(x)`. -/
theorem logPotential_serre_real {x : ℝ} (hx : x ∈ Set.Icc aSerre bSerre) :
    logPotential (serreMeasure gSerre aSerre bSerre) (x : ℂ) =
      gSerre * logPotential (nu aSerre bSerre) (x : ℂ) +
        (1 - gSerre) * logPotential (equilibrium aSerre bSerre) (x : ℂ) := by
  have hInt_nu : Integrable (integrand (x : ℂ)) (nu aSerre bSerre) := integrable_integrand_nu hx
  have hInt_eq : Integrable (integrand (x : ℂ)) (equilibrium aSerre bSerre) :=
    integrable_integrand_eq hx
  have hInt_nu_s : Integrable (integrand (x : ℂ)) (ENNReal.ofReal gSerre • nu aSerre bSerre) :=
    hInt_nu.smul_measure ENNReal.ofReal_ne_top
  have hInt_eq_s : Integrable (integrand (x : ℂ))
      (ENNReal.ofReal (1 - gSerre) • equilibrium aSerre bSerre) :=
    hInt_eq.smul_measure ENNReal.ofReal_ne_top
  unfold logPotential serreMeasure
  change (∫ t : ℝ, integrand (x : ℂ) t ∂
      (ENNReal.ofReal gSerre • nu aSerre bSerre + ENNReal.ofReal (1 - gSerre) • equilibrium aSerre bSerre)) =
      gSerre * (∫ t : ℝ, integrand (x : ℂ) t ∂nu aSerre bSerre) +
        (1 - gSerre) * (∫ t : ℝ, integrand (x : ℂ) t ∂equilibrium aSerre bSerre)
  rw [MeasureTheory.integral_add_measure hInt_nu_s hInt_eq_s]
  rw [MeasureTheory.integral_smul_measure, MeasureTheory.integral_smul_measure]
  rw [ENNReal.toReal_ofReal gSerre_pos.le, ENNReal.toReal_ofReal (sub_nonneg.mpr gSerre_le_one)]
  ring

/-- `U^ν(x) = log(A/(b−a)) − log x` for `x ∈ [aSerre,bSerre]` (from the
machine-verified balayage identity). -/
theorem nu_potential_on_Icc {x : ℝ} (hx : x ∈ Set.Icc aSerre bSerre) :
    logPotential (nu aSerre bSerre) (x : ℂ) =
      Real.log ((aSerre + 2 * Real.sqrt (aSerre * bSerre) + bSerre) / (bSerre - aSerre)) - Real.log x := by
  have hxpos : 0 < x := lt_of_lt_of_le aSerre_pos hx.1
  have hbal := Submission.BalayOnIcc.balay_potential_on_Icc (a := aSerre) (b := bSerre)
    aSerre_pos (by norm_num [aSerre, bSerre]) hx
  have hlog : Real.log ‖(x : ℂ)‖ = Real.log x := Submission.SerreLogMoment.log_norm_ofReal_pos hxpos
  linarith

/-- `U^{μ_[a,b]}(x) = −log((b−a)/4)` for `x ∈ [aSerre,bSerre]`. -/
theorem equilibrium_potential_on_serre {x : ℝ} (hx : x ∈ Set.Icc aSerre bSerre) :
    logPotential (equilibrium aSerre bSerre) (x : ℂ) =
      -Real.log ((bSerre - aSerre) / 4) := by
  have h1 := Submission.EquilibriumPotentialIcc.equilibrium_potential_on_Icc
    (c := aSerre) (d := bSerre) (by norm_num [aSerre, bSerre]) hx
  unfold logCap at h1
  exact h1

/-- Pure log identity used below:
`log(A/(b−a)) + log((b−a)/4) = log(A/4)` with `A = a + 2√(ab) + b`. -/
lemma serre_log_identity :
    Real.log ((aSerre + 2 * Real.sqrt (aSerre * bSerre) + bSerre) / (bSerre - aSerre)) +
      Real.log ((bSerre - aSerre) / 4)
    = Real.log ((aSerre + 2 * Real.sqrt (aSerre * bSerre) + bSerre) / 4) := by
  have hApos : 0 < (aSerre + 2 * Real.sqrt (aSerre * bSerre) + bSerre) := by
    have ha : 0 < aSerre := aSerre_pos
    have hb : 0 < bSerre := bSerre_pos
    have hs : 0 ≤ Real.sqrt (aSerre * bSerre) := Real.sqrt_nonneg _
    nlinarith
  have hbma : 0 < bSerre - aSerre := by norm_num [aSerre, bSerre]
  have hbm4 : 0 < (bSerre - aSerre) / 4 := by positivity
  have hprod : ((aSerre + 2 * Real.sqrt (aSerre * bSerre) + bSerre) / (bSerre - aSerre)) *
      ((bSerre - aSerre) / 4) = (aSerre + 2 * Real.sqrt (aSerre * bSerre) + bSerre) / 4 := by
    field_simp [ne_of_gt hbma]
  have hX0 : (aSerre + 2 * Real.sqrt (aSerre * bSerre) + bSerre) / (bSerre - aSerre) ≠ 0 :=
    ne_of_gt (div_pos hApos hbma)
  calc
    Real.log ((aSerre + 2 * Real.sqrt (aSerre * bSerre) + bSerre) / (bSerre - aSerre)) +
        Real.log ((bSerre - aSerre) / 4)
        = Real.log (((aSerre + 2 * Real.sqrt (aSerre * bSerre) + bSerre) / (bSerre - aSerre)) *
            ((bSerre - aSerre) / 4)) := by
          rw [← Real.log_mul hX0 (ne_of_gt hbm4)]
    _ = Real.log ((aSerre + 2 * Real.sqrt (aSerre * bSerre) + bSerre) / 4) := by
          rw [hprod]

/-- The `γ`-combination of the two interval potentials equals `serreConstant`. -/
lemma serre_constant_log_eq :
    gSerre * Real.log ((aSerre + 2 * Real.sqrt (aSerre * bSerre) + bSerre) / (bSerre - aSerre)) +
        (1 - gSerre) * -Real.log ((bSerre - aSerre) / 4) = serreConstant := by
  unfold serreConstant
  calc
    gSerre * Real.log ((aSerre + 2 * Real.sqrt (aSerre * bSerre) + bSerre) / (bSerre - aSerre)) +
        (1 - gSerre) * -Real.log ((bSerre - aSerre) / 4)
        = -Real.log ((bSerre - aSerre) / 4) + gSerre *
          (Real.log ((aSerre + 2 * Real.sqrt (aSerre * bSerre) + bSerre) / (bSerre - aSerre)) +
            Real.log ((bSerre - aSerre) / 4)) := by ring
    _ = -Real.log ((bSerre - aSerre) / 4) + gSerre *
          Real.log ((aSerre + 2 * Real.sqrt (aSerre * bSerre) + bSerre) / 4) := by
      rw [serre_log_identity]
    _ = -Real.log ((bSerre - aSerre) / 4) + gSerre *
          Real.log ((aSerre + 2 * Real.sqrt (aSerre * bSerre) + bSerre) / 4) := by rfl

/-- **The explicit Serre potential on the interval:**
`U^μ(x) = serreConstant − γ·log x` for `x ∈ [aSerre,bSerre]`. -/
theorem serre_potential_on_Icc {x : ℝ} (hx : x ∈ Set.Icc aSerre bSerre) :
    logPotential (serreMeasure gSerre aSerre bSerre) (x : ℂ) =
      serreConstant - gSerre * Real.log x := by
  rw [logPotential_serre_real hx]
  rw [nu_potential_on_Icc hx, equilibrium_potential_on_serre hx]
  calc
    gSerre * (Real.log ((aSerre + 2 * Real.sqrt (aSerre * bSerre) + bSerre) / (bSerre - aSerre)) -
        Real.log x) + (1 - gSerre) * -Real.log ((bSerre - aSerre) / 4)
        = (gSerre * Real.log ((aSerre + 2 * Real.sqrt (aSerre * bSerre) + bSerre) / (bSerre - aSerre)) +
            (1 - gSerre) * -Real.log ((bSerre - aSerre) / 4)) - gSerre * Real.log x := by ring
    _ = serreConstant - gSerre * Real.log x := by rw [serre_constant_log_eq]

/-- **The weight is explicit on the interval:**
`w_μ(x) = e^{serreConstant}·x^{−γ}` for `x ∈ [aSerre,bSerre]`. -/
theorem weight_serre_on_Icc {x : ℝ} (hx : x ∈ Set.Icc aSerre bSerre) :
    weight (serreMeasure gSerre aSerre bSerre) x =
      Real.exp serreConstant * x ^ (-gSerre) := by
  unfold weight
  rw [serre_potential_on_Icc hx]
  have hxpos : 0 < x := lt_of_lt_of_le aSerre_pos hx.1
  have hrpow : Real.exp (gSerre * Real.log x) = x ^ gSerre := by
    calc
      Real.exp (gSerre * Real.log x) = Real.exp (Real.log x * gSerre) := by congr 1; ring
      _ = x ^ gSerre := (Real.rpow_def_of_pos hxpos gSerre).symm
  have hneg : x ^ (-gSerre) = (x ^ gSerre)⁻¹ := by
    rw [Real.rpow_neg hxpos.le gSerre]
  calc
    Real.exp (serreConstant - gSerre * Real.log x)
        = Real.exp serreConstant / Real.exp (gSerre * Real.log x) := by rw [Real.exp_sub]
    _ = Real.exp serreConstant / x ^ gSerre := by rw [hrpow]
    _ = Real.exp serreConstant * (x ^ gSerre)⁻¹ := by rw [div_eq_mul_inv]
    _ = Real.exp serreConstant * x ^ (-gSerre) := by rw [← hneg]

/-- Bound on `|log x|` for `x ∈ [aSerre,bSerre]` in terms of the endpoints. -/
lemma log_abs_le_max {x : ℝ} (hx : x ∈ Set.Icc aSerre bSerre) :
    |Real.log x| ≤ max |Real.log aSerre| |Real.log bSerre| := by
  have hxpos : 0 < x := lt_of_lt_of_le aSerre_pos hx.1
  have hloga_lt : Real.log aSerre < 0 := by
    have h1 : aSerre < 1 := by norm_num [aSerre]
    have h2 : Real.log aSerre < Real.log 1 := Real.log_lt_log aSerre_pos h1
    simpa using h2
  have hlogb_pos : 0 < Real.log bSerre := by
    have h1 : 1 < bSerre := by norm_num [bSerre]
    have h2 : Real.log 1 < Real.log bSerre := Real.log_lt_log (by norm_num) h1
    simpa using h2
  have hloga_le : Real.log aSerre ≤ Real.log x := Real.log_le_log aSerre_pos hx.1
  have hlogx_le : Real.log x ≤ Real.log bSerre := Real.log_le_log hxpos hx.2
  rw [abs_of_neg hloga_lt, abs_of_pos hlogb_pos]
  rw [abs_le]
  constructor
  · calc
      -max (-Real.log aSerre) (Real.log bSerre) ≤ Real.log aSerre := by
        simpa using (neg_le_neg (le_max_left (-Real.log aSerre) (Real.log bSerre)))
      _ ≤ Real.log x := hloga_le
  · calc
      Real.log x ≤ Real.log bSerre := hlogx_le
      _ ≤ max (-Real.log aSerre) (Real.log bSerre) := le_max_right _ _

/-- Bound on the log-weight on the interval. -/
lemma log_weight_bound {x : ℝ} (hx : x ∈ Set.Icc aSerre bSerre) :
    |Real.log (weight (serreMeasure gSerre aSerre bSerre) x)| ≤
      |serreConstant| + gSerre * (max |Real.log aSerre| |Real.log bSerre|) := by
  have hxpos : 0 < x := lt_of_lt_of_le aSerre_pos hx.1
  have hlogw : Real.log (weight (serreMeasure gSerre aSerre bSerre) x)
      = serreConstant - gSerre * Real.log x := by
    rw [weight_serre_on_Icc hx]
    rw [Real.log_mul (ne_of_gt (Real.exp_pos serreConstant))
      (ne_of_gt (Real.rpow_pos_of_pos hxpos (-gSerre)))]
    rw [Real.log_exp, Real.log_rpow hxpos (-gSerre)]
    ring
  have hlogx : |Real.log x| ≤ max |Real.log aSerre| |Real.log bSerre| := log_abs_le_max hx
  rw [hlogw]
  have h1 : |gSerre * Real.log x| ≤ gSerre * |Real.log x| := by
    rw [abs_mul, abs_of_pos gSerre_pos]
  have h2 : |serreConstant - gSerre * Real.log x| ≤ |serreConstant| + |gSerre * Real.log x| := by
    rw [abs_sub_le_iff]
    constructor
    · nlinarith [le_abs_self serreConstant, neg_le_abs (gSerre * Real.log x)]
    · nlinarith [le_abs_self (gSerre * Real.log x), neg_le_abs serreConstant]
  have h3 : |serreConstant| + |gSerre * Real.log x| ≤
      |serreConstant| + gSerre * |Real.log x| := by
    exact add_le_add_right h1 |serreConstant|
  have h4 : |serreConstant| + gSerre * |Real.log x| ≤
      |serreConstant| + gSerre * (max |Real.log aSerre| |Real.log bSerre|) := by
    exact add_le_add_right (mul_le_mul_of_nonneg_left hlogx gSerre_pos.le) |serreConstant|
  exact le_trans (le_trans h2 h3) h4

/-- Global bound on the log-weight (existential form). -/
theorem exists_log_weight_bound :
    ∃ K : ℝ, 0 ≤ K ∧
      ∀ x : ℝ, x ∈ Set.Icc aSerre bSerre →
        |Real.log (weight (serreMeasure gSerre aSerre bSerre) x)| ≤ K := by
  refine ⟨|serreConstant| + gSerre * (max |Real.log aSerre| |Real.log bSerre|), ?_, ?_⟩
  · have h1 : 0 ≤ |serreConstant| := abs_nonneg _
    have h2 : 0 ≤ max |Real.log aSerre| |Real.log bSerre| :=
      le_trans (abs_nonneg (Real.log aSerre)) (le_max_left _ _)
    exact add_nonneg h1 (mul_nonneg gSerre_pos.le h2)
  · intro x hx
    exact log_weight_bound hx

/-- The potential is Lipschitz on the interval:
`|U^μ(x) − U^μ(y)| ≤ (γ/aSerre)·|x−y|` for `x,y ∈ [aSerre,bSerre]`. -/
theorem potential_lipschitz_on_Icc {x y : ℝ} (hx : x ∈ Set.Icc aSerre bSerre)
    (hy : y ∈ Set.Icc aSerre bSerre) :
    |logPotential (serreMeasure gSerre aSerre bSerre) (x : ℂ) -
      logPotential (serreMeasure gSerre aSerre bSerre) (y : ℂ)|
        ≤ (gSerre / aSerre) * |x - y| := by
  have hxpos : 0 < x := lt_of_lt_of_le aSerre_pos hx.1
  have hypos : 0 < y := lt_of_lt_of_le aSerre_pos hy.1
  have hlogd : |Real.log x - Real.log y| ≤ |x - y| / min x y :=
    Submission.PotentialContinuity.abs_log_sub_le_div_min hxpos hypos
  have hmin : aSerre ≤ min x y := le_min hx.1 hy.1
  have hminpos : 0 < min x y := lt_of_lt_of_le aSerre_pos hmin
  have hdiv : |x - y| / min x y ≤ |x - y| / aSerre := by
    rw [div_eq_mul_inv, div_eq_mul_inv]
    apply mul_le_mul_of_nonneg_left _ (abs_nonneg _)
    exact (inv_le_inv₀ hminpos aSerre_pos).mpr hmin
  rw [serre_potential_on_Icc hx, serre_potential_on_Icc hy]
  have hmain : |(serreConstant - gSerre * Real.log x) - (serreConstant - gSerre * Real.log y)|
      ≤ (gSerre / aSerre) * |x - y| := by
    have hsub : (serreConstant - gSerre * Real.log x) - (serreConstant - gSerre * Real.log y)
        = -(gSerre * (Real.log x - Real.log y)) := by ring
    rw [hsub]
    rw [abs_neg]
    calc
      |gSerre * (Real.log x - Real.log y)| = gSerre * |Real.log x - Real.log y| := by
        rw [abs_mul, abs_of_pos gSerre_pos]
      _ ≤ gSerre * (|x - y| / min x y) := by
        exact mul_le_mul_of_nonneg_left hlogd gSerre_pos.le
      _ ≤ gSerre * (|x - y| / aSerre) := by
        exact mul_le_mul_of_nonneg_left hdiv gSerre_pos.le
      _ = (gSerre / aSerre) * |x - y| := by ring
  simpa using hmain

/-- The potential is `1/2`-Hölder on the interval (∃ form, used as the
paper's `lem:pot_Hold` at the Serre data): there is `H` with
`|U^μ(x) − U^μ(y)| ≤ H·√|x−y|` for `x,y` in the interval. -/
theorem exists_potential_half_holder :
    ∃ H : ℝ, 0 ≤ H ∧ ∀ x y : ℝ, x ∈ Set.Icc aSerre bSerre → y ∈ Set.Icc aSerre bSerre →
      |logPotential (serreMeasure gSerre aSerre bSerre) (x : ℂ) -
        logPotential (serreMeasure gSerre aSerre bSerre) (y : ℂ)|
          ≤ H * Real.sqrt |x - y| := by
  let d : ℝ := bSerre - aSerre
  refine ⟨(gSerre / aSerre) * Real.sqrt d, ?_, ?_⟩
  · have hg : 0 ≤ gSerre / aSerre := div_nonneg gSerre_pos.le aSerre_pos.le
    exact mul_nonneg hg (Real.sqrt_nonneg d)
  · intro x y hx hy
    have hdiam : |x - y| ≤ d := by
      unfold d
      rw [abs_le]
      constructor <;> nlinarith [hx.1, hx.2, hy.1, hy.2]
    have hxy0 : 0 ≤ |x - y| := abs_nonneg _
    have hsqrt : |x - y| ≤ Real.sqrt d * Real.sqrt |x - y| := by
      by_cases h0 : |x - y| = 0
      · simp [h0]
      · have hpos : 0 < |x - y| := lt_of_le_of_ne hxy0 (Ne.symm h0)
        have hd0 : 0 ≤ d := by unfold d; nlinarith [hx.1, hy.2]
        have hle : Real.sqrt |x - y| ≤ Real.sqrt d := by
          exact Real.sqrt_le_sqrt (by simpa [d] using hdiam)
        have hsq : Real.sqrt |x - y| * Real.sqrt |x - y| = |x - y| := by
          rw [← pow_two]
          exact Real.sq_sqrt hxy0
        calc
          |x - y| = Real.sqrt |x - y| * Real.sqrt |x - y| := hsq.symm
          _ ≤ Real.sqrt d * Real.sqrt |x - y| := by
            exact mul_le_mul_of_nonneg_right hle (Real.sqrt_nonneg _)
    calc
      |logPotential (serreMeasure gSerre aSerre bSerre) (x : ℂ) -
          logPotential (serreMeasure gSerre aSerre bSerre) (y : ℂ)|
          ≤ (gSerre / aSerre) * |x - y| := potential_lipschitz_on_Icc hx hy
      _ ≤ (gSerre / aSerre) * (Real.sqrt d * Real.sqrt |x - y|) := by
        have hg : 0 ≤ gSerre / aSerre := div_nonneg gSerre_pos.le aSerre_pos.le
        exact mul_le_mul_of_nonneg_left hsqrt hg
      _ = ((gSerre / aSerre) * Real.sqrt d) * Real.sqrt |x - y| := by ring

end Submission.SerrePotentialIcc
