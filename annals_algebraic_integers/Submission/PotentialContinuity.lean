import Submission.PotentialDefs
import Submission.Serre
import Submission.SerreExample
import Submission.SerreMean
import Submission.EquilibriumHolder
import Submission.SupportConcentration
import Mathlib.MeasureTheory.Integral.Bochner.Basic
import Mathlib.Analysis.SpecialFunctions.Log.Basic
import Mathlib.Analysis.SpecialFunctions.Log.Deriv
import Mathlib.Analysis.SpecialFunctions.Log.NegMulLog
import Mathlib.MeasureTheory.Integral.Layercake
import Submission.GenericLocalLog

/-!
# Continuity of the Serre potential on the real axis (contract W2)

Proves (for later splicing into `Submission.WeightedNorm.logPotential_continuous_real`):

    Continuous (fun x : ℝ => logPotential (serreMeasure gSerre aSerre bSerre) (x : ℂ))

## Route

Let `μ := serreMeasure gSerre aSerre bSerre` and `U(x) := logPotential μ (x:ℂ)`.

1. **Hölder control of the measures.**  The three measures `equilibrium a b`,
   `nu a b` (image of `equilibrium (1/b) (1/a)` under inversion) and `μ` are
   supported on `[a,b] ⊂ (0,∞)` and are `1/2`-Hölder:
       ∀ a ≤ u ≤ v ≤ b : measure (Icc u v) ≤ C·√(v−u)
   * for `equilibrium a b`: `Submission.EquilibriumHolder.equilibrium_holder`;
   * for `nu a b`: its preimage under `t ↦ t⁻¹` is an interval of length
     `1/u − 1/v = (v−u)/(uv) ≤ (v−u)/a²`, so it follows from the same lemma
     applied to `equilibrium (1/b) (1/a)`;
   * for the convex combination: additivity (`Measure.add_apply`,
     `Measure.smul_apply`), constants add.

2. **Log-kernel estimate.**  For fixed `x₀ ∈ ℝ`, with `ε := |x − x₀|` small
   (say `ε ≤ 1`), split `t ∈ [a,b]` into
     (i) the ε-neighbourhood of `x₀` inside `[a,b]` (μ-measure ≤ C·√ε by
         Hölder; there `|log|x−t| − log|x₀−t|| ≤ 2·max(−log ε, 0) + O(1)`,
         whose product with `√ε` tends to 0 since `√ε·log(1/ε) → 0`);
     (ii) the rest: both `|x−t|,|x₀−t| ≥ ε/2`, where `log` is Lipschitz with
         constant `2/ε`, giving an integral `≤ (2/ε)·ε·μ(rest) = O(1)·ε`.
   Then `|U(x) − U(x₀)| → 0` as `x → x₀` (`tendsto`/`ContinuousAt`).

3. Assemble continuity on ℝ (`continuous_iff_continuousAt`).
-/

noncomputable section

set_option maxHeartbeats 1000000

open MeasureTheory
open Filter
open scoped Real ENNReal Topology

namespace Submission.PotentialContinuity

open Submission.PotentialDefs
open Submission.Serre
open Submission.SerreExample
open Submission.EquilibriumHolder
open Submission.Equilibrium

/-! ## The measure and its constants -/

/-- The Serre measure on `[aSerre, bSerre]`. -/
abbrev muS : Measure ℝ := serreMeasure gSerre aSerre bSerre

/-- Hölder constant for the equilibrium part `4/√(b−a)`. -/
abbrev Ceq : ℝ := 4 / Real.sqrt (bSerre - aSerre)

/-- Hölder constant for the inversion image part. -/
abbrev Cnu : ℝ := 4 / (aSerre * Real.sqrt ((aSerre)⁻¹ - (bSerre)⁻¹))

/-- Hölder constant for the full Serre measure. -/
abbrev Cmu : ℝ := Ceq + Cnu

/-- The constant in the local log-kernel bounds. -/
abbrev Kloc : ℝ := (Cmu + 1) * 4096

lemma aSerre_inv_gt_bSerre_inv : (bSerre)⁻¹ < (aSerre)⁻¹ := by
  have h := one_div_lt_one_div_of_lt aSerre_pos a_lt_b
  simpa [one_div] using h

lemma Ceq_pos : 0 < Ceq := by
  dsimp [Ceq]
  have hb : 0 < bSerre - aSerre := sub_pos.mpr a_lt_b
  exact div_pos (by norm_num) (Real.sqrt_pos.mpr hb)

lemma Cnu_pos : 0 < Cnu := by
  dsimp [Cnu]
  have harg : 0 < (aSerre)⁻¹ - (bSerre)⁻¹ := sub_pos.mpr aSerre_inv_gt_bSerre_inv
  have hs : 0 < Real.sqrt ((aSerre)⁻¹ - (bSerre)⁻¹) := Real.sqrt_pos.mpr harg
  exact div_pos (by norm_num) (mul_pos aSerre_pos hs)

lemma Cmu_pos : 0 < Cmu := by
  dsimp [Cmu]
  exact add_pos Ceq_pos Cnu_pos

/-- μ has no mass outside `[a,b]`. -/
lemma muS_compl_Icc : muS (Set.Icc aSerre bSerre)ᶜ = 0 := by
  unfold muS
  exact Submission.SupportConcentration.serre_compl_Icc (a := aSerre) (b := bSerre) (γ := gSerre)
    aSerre_pos a_le_b (le_of_lt gSerre_pos) gSerre_le_one

/-- μ is a probability measure. -/
lemma muS_univ : muS Set.univ = 1 := by
  unfold muS
  exact serre_univ (γ := gSerre) (a := aSerre) (b := bSerre) (le_of_lt gSerre_pos) gSerre_le_one

instance muS_isProb : IsProbabilityMeasure muS := ⟨muS_univ⟩

instance muS_isFinite : IsFiniteMeasure muS where
  measure_univ_lt_top := by
    rw [muS_univ]
    exact (ENNReal.coe_lt_top : (1 : ℝ≥0∞) < ∞)

/-- mass of `[a,b]` itself is 1 -/
lemma muS_Icc : muS (Set.Icc aSerre bSerre) = 1 := by
  have hsum := MeasureTheory.measure_add_measure_compl (μ := muS)
    (isClosed_Icc.measurableSet : MeasurableSet (Set.Icc aSerre bSerre))
  rw [muS_compl_Icc, muS_univ] at hsum
  simpa using hsum

/-! ## 1/2-Hölder estimates for ν and μ -/

/-- inversion preimage of `Icc u v` is `Icc v⁻¹ u⁻¹` (for `0 < u ≤ v`). -/
lemma inv_preimage_Icc {u v : ℝ} (hu0 : 0 < u) (huv : u ≤ v) :
    invMap ⁻¹' (Set.Icc u v) = Set.Icc (v⁻¹) (u⁻¹) := by
  have hv0 : 0 < v := lt_of_lt_of_le hu0 huv
  ext t
  constructor
  · intro ht
    have ht1 : u ≤ t⁻¹ := ht.1
    have ht2 : t⁻¹ ≤ v := ht.2
    have htpos : 0 < t⁻¹ := lt_of_lt_of_le hu0 ht1
    have ht0 : 0 < t := inv_pos.mp htpos
    constructor
    · -- v⁻¹ ≤ t : from 1 ≤ v·t
      have hmult : 1 ≤ v * t := by
        have h := mul_le_mul_of_nonneg_right ht2 (le_of_lt ht0)
        have hc : t⁻¹ * t = 1 := by field_simp [ht0.ne']
        rwa [hc] at h
      calc
        v⁻¹ = (1 : ℝ) * v⁻¹ := by ring
        _ ≤ (v * t) * v⁻¹ := by
          exact mul_le_mul_of_nonneg_right hmult (inv_nonneg.mpr (le_of_lt hv0))
        _ = t := by field_simp [hv0.ne']
    · -- t ≤ u⁻¹ : from u·t ≤ 1
      have hmult : u * t ≤ 1 := by
        have h := mul_le_mul_of_nonneg_right ht1 (le_of_lt ht0)
        have hc : t⁻¹ * t = 1 := by field_simp [ht0.ne']
        rwa [hc] at h
      calc
        t = (u * t) * u⁻¹ := by field_simp [hu0.ne']
        _ ≤ u⁻¹ := by
          calc
            (u * t) * u⁻¹ ≤ (1 : ℝ) * u⁻¹ := by
              exact mul_le_mul_of_nonneg_right hmult (inv_nonneg.mpr (le_of_lt hu0))
            _ = u⁻¹ := by ring
  · intro ht
    have ht1' : v⁻¹ ≤ t := ht.1
    have ht2' : t ≤ u⁻¹ := ht.2
    have ht0 : 0 < t := lt_of_lt_of_le (inv_pos.mpr hv0) ht1'
    constructor
    · -- u ≤ t⁻¹ : from u·t ≤ 1
      have hmult : u * t ≤ 1 := by
        have h := mul_le_mul_of_nonneg_right ht2' (le_of_lt hu0)
        have hc : u⁻¹ * u = 1 := by field_simp [hu0.ne']
        rw [hc] at h
        simpa [mul_comm] using h
      calc
        u = (u * t) * t⁻¹ := by field_simp [ht0.ne']
        _ ≤ t⁻¹ := by
          calc
            (u * t) * t⁻¹ ≤ (1 : ℝ) * t⁻¹ := by
              exact mul_le_mul_of_nonneg_right hmult (inv_nonneg.mpr (le_of_lt ht0))
            _ = t⁻¹ := by ring
    · -- t⁻¹ ≤ v : from 1 ≤ v·t
      have hmult : 1 ≤ v * t := by
        have h := mul_le_mul_of_nonneg_right ht1' (le_of_lt hv0)
        have hc : v⁻¹ * v = 1 := by field_simp [hv0.ne']
        rw [hc] at h
        simpa [mul_comm] using h
      calc
        t⁻¹ = t⁻¹ * (1 : ℝ) := by ring
        _ ≤ t⁻¹ * (v * t) := by
          exact mul_le_mul_of_nonneg_left hmult (inv_nonneg.mpr (le_of_lt ht0))
        _ = v := by field_simp [ht0.ne']

/-- Hölder bound for `ν = image of equilibrium under inversion`. -/
lemma nu_holder {u v : ℝ} (hu : aSerre ≤ u) (huv : u ≤ v) (hv : v ≤ bSerre) :
    nu aSerre bSerre (Set.Icc u v) ≤ ENNReal.ofReal (Cnu * Real.sqrt (v - u)) := by
  have hu0 : 0 < u := lt_of_lt_of_le aSerre_pos hu
  have hb0 : 0 < bSerre := bSerre_pos
  have hv0 : 0 < v := lt_of_lt_of_le hu0 huv
  unfold nu
  rw [Measure.map_apply invMap_measurable isClosed_Icc.measurableSet]
  rw [inv_preimage_Icc hu0 huv]
  have h := equilibrium_holder (a := (bSerre)⁻¹) (b := (aSerre)⁻¹)
    (x := v⁻¹) (y := u⁻¹) aSerre_inv_gt_bSerre_inv
    (by simpa [one_div] using (one_div_le_one_div_of_le hv0 hv))
    (by simpa [one_div] using (one_div_le_one_div_of_le hu0 huv))
    (by simpa [one_div] using (one_div_le_one_div_of_le aSerre_pos hu))
  have hmain : equilibrium (bSerre)⁻¹ (aSerre)⁻¹ (Set.Icc v⁻¹ u⁻¹) ≤
      ENNReal.ofReal (4 / Real.sqrt ((aSerre)⁻¹ - (bSerre)⁻¹) * Real.sqrt (u⁻¹ - v⁻¹)) := by
    simpa using h
  have harg : 0 < (aSerre)⁻¹ - (bSerre)⁻¹ := sub_pos.mpr aSerre_inv_gt_bSerre_inv
  have hsqrt_le : Real.sqrt (u⁻¹ - v⁻¹) ≤ Real.sqrt (v - u) / aSerre := by
    have hsub : u⁻¹ - v⁻¹ = (v - u) / (u * v) := by
      field_simp [ne_of_gt hu0, ne_of_gt hv0]
    rw [hsub]
    rw [Real.sqrt_div (sub_nonneg.mpr huv)]
    apply div_le_div_of_nonneg_left (Real.sqrt_nonneg (v - u)) aSerre_pos
    have h1 : aSerre * aSerre ≤ u * aSerre :=
      mul_le_mul_of_nonneg_right hu (le_of_lt aSerre_pos)
    have h2 : u * aSerre ≤ u * v :=
      mul_le_mul_of_nonneg_left (le_trans hu huv) (le_of_lt hu0)
    have hsq : aSerre ^ 2 ≤ u * v := by
      calc
        aSerre ^ 2 = aSerre * aSerre := by ring
        _ ≤ u * aSerre := h1
        _ ≤ u * v := h2
    exact (Real.le_sqrt (le_of_lt aSerre_pos)
      (mul_nonneg (le_of_lt hu0) (le_of_lt hv0))).mpr hsq
  have hreal : 4 / Real.sqrt ((aSerre)⁻¹ - (bSerre)⁻¹) * Real.sqrt (u⁻¹ - v⁻¹)
      ≤ Cnu * Real.sqrt (v - u) := by
    calc
      4 / Real.sqrt ((aSerre)⁻¹ - (bSerre)⁻¹) * Real.sqrt (u⁻¹ - v⁻¹)
          ≤ 4 / Real.sqrt ((aSerre)⁻¹ - (bSerre)⁻¹) * (Real.sqrt (v - u) / aSerre) := by
            exact mul_le_mul_of_nonneg_left hsqrt_le
              (div_nonneg (by norm_num) (Real.sqrt_nonneg ((aSerre)⁻¹ - (bSerre)⁻¹)))
      _ = Cnu * Real.sqrt (v - u) := by
            dsimp [Cnu]
            field_simp [ne_of_gt (Real.sqrt_pos.mpr harg), ne_of_gt aSerre_pos]
  exact le_trans hmain (ENNReal.ofReal_le_ofReal hreal)

/-- Hölder bound for the full Serre measure `μ` on `[a,b]`. -/
lemma muS_holder {u v : ℝ} (hu : aSerre ≤ u) (huv : u ≤ v) (hv : v ≤ bSerre) :
    muS (Set.Icc u v) ≤ ENNReal.ofReal (Cmu * Real.sqrt (v - u)) := by
  unfold muS serreMeasure
  rw [Measure.add_apply, Measure.smul_apply, Measure.smul_apply]
  have heq_bnd : equilibrium aSerre bSerre (Set.Icc u v) ≤ ENNReal.ofReal (Ceq * Real.sqrt (v - u)) := by
    exact equilibrium_holder (a := aSerre) (b := bSerre) (x := u) (y := v) a_lt_b hu huv hv
  have hnu_bnd : nu aSerre bSerre (Set.Icc u v) ≤ ENNReal.ofReal (Cnu * Real.sqrt (v - u)) :=
    nu_holder hu huv hv
  have hg : ENNReal.ofReal gSerre ≤ 1 := by
    rw [← ENNReal.ofReal_one]
    exact ENNReal.ofReal_le_ofReal (by linarith [gSerre_le_one, gSerre_pos])
  have hg2 : ENNReal.ofReal (1 - gSerre) ≤ 1 := by
    rw [← ENNReal.ofReal_one]
    exact ENNReal.ofReal_le_ofReal (by linarith [gSerre_le_one, gSerre_pos])
  set nu_mass : ℝ≥0∞ := nu aSerre bSerre (Set.Icc u v)
  set eq_mass : ℝ≥0∞ := equilibrium aSerre bSerre (Set.Icc u v)
  have h1 : ENNReal.ofReal gSerre * nu_mass ≤ nu_mass := by
    simpa [mul_comm] using (mul_le_of_le_one_right (a := nu_mass) (b := ENNReal.ofReal gSerre) (by positivity) hg)
  have h2 : ENNReal.ofReal (1 - gSerre) * eq_mass ≤ eq_mass := by
    simpa [mul_comm] using (mul_le_of_le_one_right (a := eq_mass) (b := ENNReal.ofReal (1 - gSerre)) (by positivity) hg2)
  have hsgn : 0 ≤ Real.sqrt (v - u) := Real.sqrt_nonneg (v - u)
  calc
    ENNReal.ofReal gSerre * nu_mass + ENNReal.ofReal (1 - gSerre) * eq_mass
        ≤ nu_mass + ENNReal.ofReal (1 - gSerre) * eq_mass := by
          exact add_le_add_left h1 _
    _ ≤ nu_mass + eq_mass := by
          simpa [add_comm, add_left_comm, add_assoc] using add_le_add_left h2 nu_mass
    _ ≤ ENNReal.ofReal (Cnu * Real.sqrt (v - u)) + ENNReal.ofReal (Ceq * Real.sqrt (v - u)) := by
          exact add_le_add hnu_bnd heq_bnd
    _ = ENNReal.ofReal (Cmu * Real.sqrt (v - u)) := by
          rw [← ENNReal.ofReal_add (mul_nonneg (le_of_lt Cnu_pos) hsgn) (mul_nonneg (le_of_lt Ceq_pos) hsgn)]
          congr 1
          dsimp [Cmu]
          ring

/-- mass of a (possibly external) ball: `μ {t | |t−c| ≤ R} ≤ Cmu·√(2R)` -/
lemma muS_ball_mass (c : ℝ) {R : ℝ} (hR : 0 ≤ R) :
    muS {t : ℝ | |t - c| ≤ R} ≤ ENNReal.ofReal (Cmu * Real.sqrt (2 * R)) := by
  have hball : {t : ℝ | |t - c| ≤ R} = Set.Icc (c - R) (c + R) := by
    ext t
    constructor
    · intro ht
      change |t - c| ≤ R at ht
      rw [abs_le] at ht
      exact ⟨by linarith, by linarith⟩
    · intro ht
      rw [Set.mem_Icc] at ht
      change |t - c| ≤ R
      rw [abs_le]
      exact ⟨by linarith, by linarith⟩
  rw [hball]
  let J : Set ℝ := Set.Icc (c - R) (c + R) ∩ Set.Icc aSerre bSerre
  let K : Set ℝ := Set.Icc (c - R) (c + R) ∩ (Set.Icc aSerre bSerre)ᶜ
  let u' : ℝ := max (c - R) aSerre
  let v' : ℝ := min (c + R) bSerre
  have hcomp : muS (Set.Icc (c - R) (c + R)) = muS J := by
    have hJmeas : MeasurableSet J :=
      isClosed_Icc.measurableSet.inter isClosed_Icc.measurableSet
    have hKmeas : MeasurableSet K :=
      isClosed_Icc.measurableSet.inter (isClosed_Icc.measurableSet.compl)
    have hdecomp : Set.Icc (c - R) (c + R) = J ∪ K := by
      ext t
      constructor
      · intro ht
        by_cases hmem : t ∈ Set.Icc aSerre bSerre
        · left
          exact ⟨ht, hmem⟩
        · right
          exact ⟨ht, hmem⟩
      · intro ht
        rcases ht with htJ | htK
        · exact htJ.1
        · exact htK.1
    have hdisj : Disjoint J K := by
      rw [Set.disjoint_left]
      intro t htJ htK
      dsimp [J, K] at htJ htK
      rw [Set.mem_inter_iff] at htJ htK
      exact htK.2 htJ.2
    have hz : muS K = 0 := by
      unfold K
      exact measure_inter_null_of_null_right (Set.Icc (c - R) (c + R)) muS_compl_Icc
    calc
      muS (Set.Icc (c - R) (c + R)) = muS (J ∪ K) := by rw [hdecomp]
      _ = muS J + muS K := MeasureTheory.measure_union (μ := muS) (s₁ := J) (s₂ := K) hdisj hKmeas
      _ = muS J := by rw [hz]; simp
  have hJsub : J ⊆ Set.Icc u' v' := by
    intro t ht
    have htI : t ∈ Set.Icc (c - R) (c + R) := ht.1
    have htA : t ∈ Set.Icc aSerre bSerre := ht.2
    dsimp [u', v']
    exact ⟨max_le htI.1 htA.1, le_min htI.2 htA.2⟩
  by_cases hle : u' ≤ v'
  · -- interval Icc u' v' nonempty: apply Holder
    have hua : aSerre ≤ u' := by dsimp [u']; exact le_max_right _ _
    have hvb : v' ≤ bSerre := by dsimp [v']; exact min_le_right _ _
    have hlen : v' - u' ≤ 2 * R := by
      have hv1 : v' ≤ c + R := by dsimp [v']; exact min_le_left _ _
      have hu1 : c - R ≤ u' := by dsimp [u']; exact le_max_left _ _
      nlinarith
    have hmass : muS (Set.Icc u' v') ≤ ENNReal.ofReal (Cmu * Real.sqrt (v' - u')) :=
      muS_holder hua hle hvb
    have hsq : Cmu * Real.sqrt (v' - u') ≤ Cmu * Real.sqrt (2 * R) := by
      exact mul_le_mul_of_nonneg_left (Real.sqrt_le_sqrt hlen) (le_of_lt Cmu_pos)
    calc
      muS (Set.Icc (c - R) (c + R)) = muS J := hcomp
      _ ≤ muS (Set.Icc u' v') := measure_mono hJsub
      _ ≤ ENNReal.ofReal (Cmu * Real.sqrt (v' - u')) := hmass
      _ ≤ ENNReal.ofReal (Cmu * Real.sqrt (2 * R)) := ENNReal.ofReal_le_ofReal hsq
  · -- J is empty
    have hJempty : J = ∅ := by
      apply Set.eq_empty_iff_forall_notMem.mpr
      intro t ht
      have htu : t ∈ Set.Icc u' v' := hJsub ht
      exact hle (htu.1.trans htu.2)
    have hm : muS J = 0 := by rw [hJempty]; simp
    rw [hcomp]
    rw [hm]
    exact zero_le

/-- Local log-kernel mass bound (layer-cake / dyadic), instance of the generic
estimate `GenericLocalLog.local_log_bound`. -/
lemma local_log_bound (c : ℝ) {r : ℝ} (hr0 : 0 < r) (hr1 : r ≤ 1) :
    (∫ t : ℝ, Set.indicator {t : ℝ | |t - c| ≤ r} (fun t : ℝ => |Real.log (|t - c|)|) t ∂muS)
        ≤ Kloc * (Real.sqrt r * (2 + |Real.log r|)) := by
  dsimp [Kloc]
  exact GenericLocalLog.local_log_bound (μ := muS) (C := Cmu) Cmu_pos.le muS_ball_mass c r hr0 hr1

/-- `√r·(2+|log r|) → 0` as `r → 0⁺`. -/
lemma sqrt_log2_tendsto_zero :
    Tendsto (fun r : ℝ => Real.sqrt r * (2 + |Real.log r|)) (𝓝[>] (0 : ℝ)) (𝓝 0) := by
  have hsqrt0 : Tendsto Real.sqrt (𝓝[>] (0 : ℝ)) (𝓝 (0 : ℝ)) := by
    simpa using ((Real.continuous_sqrt.tendsto (0 : ℝ)).mono_left nhdsWithin_le_nhds)
  have hmain : Tendsto (fun r : ℝ => Real.sqrt r * Real.log r) (𝓝[>] (0 : ℝ)) (𝓝 0) := by
    have h := tendsto_log_mul_rpow_nhdsGT_zero (r := (1 / 2 : ℝ)) (by norm_num)
    simpa [Real.sqrt_eq_rpow, mul_comm, mul_left_comm, mul_assoc] using h
  have habs : Tendsto (fun r : ℝ => Real.sqrt r * |Real.log r|) (𝓝[>] (0 : ℝ)) (𝓝 0) := by
    have hc := (continuous_abs.tendsto (0 : ℝ)).comp hmain
    have hc' : Tendsto (fun r : ℝ => |Real.sqrt r * Real.log r|) (𝓝[>] (0 : ℝ)) (𝓝 (0 : ℝ)) := by
      simpa [Function.comp_def] using hc
    refine hc'.congr' ?_
    exact Eventually.of_forall (fun r => by simp [abs_mul, abs_of_nonneg (Real.sqrt_nonneg r)])
  have h2 : Tendsto (fun r : ℝ => Real.sqrt r * 2) (𝓝[>] (0 : ℝ)) (𝓝 0) := by
    simpa [mul_comm] using hsqrt0.const_mul 2
  have hsum : Tendsto (fun r : ℝ => Real.sqrt r * 2 + Real.sqrt r * |Real.log r|)
      (𝓝[>] (0 : ℝ)) (𝓝 0) := by
    simpa using h2.add habs
  refine hsum.congr' ?_
  exact Eventually.of_forall (fun r => by ring)

/-! ## Kernel bounds -/

/-- For `0 < p,q`, `|log p − log q| ≤ |p−q|/min p q`. -/
lemma abs_log_sub_le_div_min {p q : ℝ} (hp : 0 < p) (hq : 0 < q) :
    |Real.log p - Real.log q| ≤ |p - q| / min p q := by
  have hpqcase : ∀ {p q : ℝ}, 0 < p → 0 < q → p ≤ q →
      |Real.log p - Real.log q| ≤ |p - q| / min p q := by
    intro p q hp hq hpq
    have hlogmono : Real.log p ≤ Real.log q := Real.log_le_log hp hpq
    calc
      |Real.log p - Real.log q| = Real.log (q / p) := by
        rw [abs_of_nonpos (sub_nonpos.mpr hlogmono)]
        rw [Real.log_div (ne_of_gt hq) (ne_of_gt hp)]
        ring
      _ ≤ q / p - 1 := Real.log_le_sub_one_of_pos (div_pos hq hp)
      _ = |p - q| / min p q := by
        rw [min_eq_left hpq, abs_of_nonpos (sub_nonpos.mpr hpq)]
        field_simp [ne_of_gt hp]
        ring
  by_cases hpq : p ≤ q
  · exact hpqcase hp hq hpq
  · have hqp : q ≤ p := le_of_not_ge hpq
    simpa [abs_sub_comm, min_comm] using (hpqcase hq hp hqp)

/-- `|x−t| ≤ |x|+|a|+|b|` for `t ∈ [a,b]`. -/
lemma abs_sub_le_of_mem_Icc (x t : ℝ) (ht : t ∈ Set.Icc aSerre bSerre) :
    |x - t| ≤ |x| + |aSerre| + |bSerre| := by
  have h1 : x - t ≤ |x| + |t| := by
    nlinarith [le_abs_self x, neg_le_abs t]
  have h2 : t - x ≤ |x| + |t| := by
    nlinarith [neg_le_abs x, le_abs_self t]
  have habs : |x - t| ≤ |x| + |t| := (abs_sub_le_iff.mpr ⟨h1, h2⟩)
  have htle : |t| ≤ |bSerre| := by
    calc
      |t| = t := abs_of_pos (lt_of_lt_of_le aSerre_pos ht.1)
      _ ≤ bSerre := ht.2
      _ = |bSerre| := (abs_of_pos bSerre_pos).symm
  nlinarith [habs, htle, abs_nonneg aSerre]

/-- away from the singularity (`|x−t| ≥ 1`), on `[a,b]`, `|log|x−t||` is bounded. -/
lemma logAbs_bound_far (x t : ℝ) (ht : t ∈ Set.Icc aSerre bSerre) (hfar : 1 ≤ |x - t|) :
    |Real.log (|x - t|)| ≤ |x| + |aSerre| + |bSerre| + 1 := by
  have hu0 : 0 < |x - t| := lt_of_lt_of_le zero_lt_one hfar
  have hlog_nonneg : 0 ≤ Real.log (|x - t|) := Real.log_nonneg hfar
  have hlog_le : Real.log (|x - t|) ≤ |x - t| - 1 := Real.log_le_sub_one_of_pos hu0
  have hu : |x - t| ≤ |x| + |aSerre| + |bSerre| := abs_sub_le_of_mem_Icc x t ht
  calc
    |Real.log (|x - t|)| = Real.log (|x - t|) := abs_of_nonneg hlog_nonneg
    _ ≤ |x - t| - 1 := hlog_le
    _ ≤ |x| + |aSerre| + |bSerre| := by linarith
    _ ≤ |x| + |aSerre| + |bSerre| + 1 := by linarith

/-- integrability of the (absolute) log kernel against μ, for every real centre. -/
lemma logAbs_integrable (x : ℝ) : Integrable (fun t : ℝ => |Real.log (|x - t|)|) muS := by
  let f : ℝ → ℝ := fun t => |Real.log (|t - x|)|
  let g : ℝ → ℝ := fun t => (Set.Icc aSerre bSerre).indicator f t
  let Cx : ℝ := |x| + |aSerre| + |bSerre| + 1
  have hCx0 : 0 ≤ Cx := by dsimp [Cx]; positivity
  have hfmeas : Measurable f := by
    dsimp [f]
    exact GenericLocalLog.log_kernel_measurable x
  have hgm : Measurable g := by
    dsimp [g]
    exact hfmeas.indicator isClosed_Icc.measurableSet
  have hfnn : ∀ t : ℝ, 0 ≤ f t := by
    intro t; dsimp [f]; exact abs_nonneg _
  have hgnn : ∀ t : ℝ, 0 ≤ g t := by
    intro t; dsimp [g]
    by_cases ht : t ∈ Set.Icc aSerre bSerre
    · simp [ht]; positivity
    · simp [ht]
  -- g = f a.e. (outside [a,b] carries no mass); f itself is what we want (up to |t−x|=|x−t|)
  have hfg_ae : f =ᵐ[muS] g := by
    apply MeasureTheory.mem_ae_iff.mpr
    have hsubset : {t : ℝ | f t ≠ g t} ⊆ (Set.Icc aSerre bSerre)ᶜ := by
      intro t ht
      rw [Set.mem_compl_iff]
      intro htc
      exact ht (by simp [g, Set.indicator_of_mem htc])
    have hle : muS {t : ℝ | f t ≠ g t} ≤ 0 := by
      calc
        muS {t : ℝ | f t ≠ g t} ≤ muS (Set.Icc aSerre bSerre)ᶜ := measure_mono hsubset
        _ = 0 := muS_compl_Icc
    have hz : muS {t : ℝ | f t ≠ g t} = 0 := le_antisymm hle (zero_le : (0 : ℝ≥0∞) ≤ muS {t : ℝ | f t ≠ g t})
    have hcompl : ({t : ℝ | f t = g t})ᶜ = {t : ℝ | f t ≠ g t} := by
      ext t
      simp
    rw [hcompl]
    exact hz
  -- integrability of the truncated-at-1 kernel (ENNReal bound from the generic lemma)
  let trunc : ℝ → ℝ := fun t =>
    Set.indicator {t : ℝ | |t - x| ≤ 1} (fun t : ℝ => |Real.log (|t - x|)|) t
  have htrunc_int : Integrable trunc muS := by
    constructor
    · exact (GenericLocalLog.log_kernel_trunc_measurable x 1).aestronglyMeasurable
    · rw [MeasureTheory.hasFiniteIntegral_iff_ofReal
        (Eventually.of_forall (GenericLocalLog.log_kernel_trunc_nonneg x 1))]
      have hb := GenericLocalLog.log_kernel_ennreal_bound (μ := muS) (C := Cmu) (c := x) (r := 1)
        Cmu_pos.le muS_ball_mass zero_lt_one le_rfl
      have htop : ENNReal.ofReal ((Cmu + 1) * 4096 * (Real.sqrt 1 * (2 + |Real.log 1|))) < ∞ := by
        exact ENNReal.ofReal_lt_top
      exact lt_of_le_of_lt (by simpa [trunc] using hb) htop
  -- bounded far piece is integrable (bounded on the finite measure)
  let farB : ℝ → ℝ := fun t => Cx * (Set.Icc aSerre bSerre).indicator (fun _ : ℝ => (1 : ℝ)) t
  have hfar_int : Integrable farB muS := by
    apply Integrable.mono' (g := fun _ : ℝ => (Cx : ℝ))
    · exact MeasureTheory.integrable_const Cx
    · apply Measurable.aestronglyMeasurable
      dsimp [farB]
      have hind : Measurable ((Set.Icc aSerre bSerre).indicator (fun _ : ℝ => (1 : ℝ))) :=
        (measurable_const : Measurable (fun _ : ℝ => (1 : ℝ))).indicator isClosed_Icc.measurableSet
      exact (measurable_const : Measurable (fun _ : ℝ => (Cx : ℝ))).mul hind
    · refine Eventually.of_forall (fun t => ?_)
      by_cases ht : t ∈ Set.Icc aSerre bSerre
      · simp [farB, ht, abs_of_nonneg hCx0]
      · simp [farB, ht, hCx0]
  -- pointwise majorant on g: |g| ≤ trunc + farB
  have htrunc_nn : ∀ t : ℝ, 0 ≤ trunc t := by
    intro t
    dsimp [trunc]
    by_cases hb : |t - x| ≤ 1
    · simp [hb]
    · simp [hb]
  have hg_le_norm : ∀ t : ℝ, ‖g t‖ ≤ trunc t + farB t := by
    intro t
    by_cases htc : t ∈ Set.Icc aSerre bSerre
    · by_cases hsmall : |t - x| ≤ 1
      · calc
          ‖g t‖ = g t := by rw [Real.norm_eq_abs, abs_of_nonneg (hgnn t)]
          _ = f t := by dsimp [g]; rw [Set.indicator_of_mem htc]
          _ = trunc t := by dsimp [trunc]; simp [f, hsmall]
          _ ≤ trunc t + farB t := le_add_of_nonneg_right (by dsimp [farB]; simp [htc, hCx0])
      · calc
          ‖g t‖ = g t := by rw [Real.norm_eq_abs, abs_of_nonneg (hgnn t)]
          _ = f t := by dsimp [g]; rw [Set.indicator_of_mem htc]
          _ = |Real.log (|x - t|)| := by dsimp [f]; rw [abs_sub_comm]
          _ ≤ Cx := by
            have hfar : 1 ≤ |x - t| := by
              have h := le_of_not_ge hsmall
              simpa [abs_sub_comm] using h
            have hb := logAbs_bound_far x t htc hfar
            simpa [Cx] using hb
          _ = farB t := by dsimp [farB]; simp [htc]
          _ ≤ trunc t + farB t := le_add_of_nonneg_left (htrunc_nn t)
    · have hg0 : g t = 0 := by simp [g, htc]
      have hB0 : farB t = 0 := by dsimp [farB]; simp [htc]
      rw [hg0, hB0]
      simpa using htrunc_nn t

  have hg_int : Integrable g muS := by
    refine Integrable.mono' (htrunc_int.add hfar_int) ?_ ?_
    · exact hgm.aestronglyMeasurable
    · exact Eventually.of_forall hg_le_norm
  have hf_int : Integrable f muS := hg_int.congr hfg_ae.symm
  -- |log|x−t|| = |log|t−x||, so transfer
  refine Integrable.congr hf_int ?_
  rw [Filter.EventuallyEq]
  exact Eventually.of_forall (fun t => by congr 1; rw [abs_sub_comm])

/-- the log kernel itself is integrable (abs one bounds it) -/
lemma log_integrable (x : ℝ) : Integrable (fun t : ℝ => Real.log (|x - t|)) muS := by
  have habs := logAbs_integrable x
  refine Integrable.mono' habs ?_ ?_
  · apply Measurable.aestronglyMeasurable
    exact Real.measurable_log.comp (by fun_prop : Measurable fun t : ℝ => |x - t|)
  · refine Eventually.of_forall (fun t => ?_)
    simpa [Real.norm_eq_abs]

/-- kernel difference is integrable -/
lemma logDiff_integrable (x x₀ : ℝ) : Integrable (fun t : ℝ => Real.log (|x₀ - t|) - Real.log (|x - t|)) muS := by
  exact (log_integrable x₀).sub (log_integrable x)

/-! ## Potential difference decomposition -/

/-- Potential difference formula with real distance kernel. -/
lemma potential_diff_formula (x x₀ : ℝ) :
    logPotential muS (x : ℂ) - logPotential muS (x₀ : ℂ) =
      (∫ t : ℝ, Real.log |x₀ - t| - Real.log |x - t| ∂muS) := by
  have h1 (z : ℝ) : logPotential muS (z : ℂ) = (∫ t : ℝ, -Real.log (|z - t|) ∂muS) := by
    unfold logPotential
    apply MeasureTheory.integral_congr_ae
    exact Eventually.of_forall (fun t : ℝ => log_norm_sub_ofReal z t)
  rw [h1 x, h1 x₀]
  have hx : Integrable (fun t : ℝ => -Real.log (|x - t|)) muS := (log_integrable x).neg
  have hx0 : Integrable (fun t : ℝ => -Real.log (|x₀ - t|)) muS := (log_integrable x₀).neg
  rw [← MeasureTheory.integral_sub hx hx0]
  congr 1
  funext t
  ring

/-- indicator-restricted bounded integral estimate: if `|f| ≤ M` on `S`, then
`|∫ 1_S · f dμ| ≤ M · μ(S)`. -/
lemma integral_indicator_le {S : Set ℝ} (hS : MeasurableSet S) {M : ℝ} (hM : 0 ≤ M)
    {f : ℝ → ℝ} (hfmeas : Measurable f) (hf : ∀ t ∈ S, |f t| ≤ M) :
    |∫ t : ℝ, Set.indicator S f t ∂muS| ≤ M * (muS S).toReal := by
  have hconst_int : Integrable (fun _ : ℝ => (M : ℝ)) muS := by
    exact MeasureTheory.integrable_const M
  have hfS_int : Integrable (fun t : ℝ => Set.indicator S f t) muS := by
    refine MeasureTheory.Integrable.mono' hconst_int (by fun_prop) ?_
    refine Eventually.of_forall (fun t => ?_)
    by_cases ht : t ∈ S
    · simpa [ht] using hf t ht
    · simp [ht, hM]
  have hfSabs_int : Integrable (fun t : ℝ => |Set.indicator S f t|) muS := hfS_int.abs
  have hMS_int : Integrable (fun t : ℝ => M * Set.indicator S (fun _ : ℝ => (1 : ℝ)) t) muS := by
    refine MeasureTheory.Integrable.mono' hconst_int (by fun_prop) ?_
    refine Eventually.of_forall (fun t => ?_)
    by_cases ht : t ∈ S
    · simp [ht, abs_of_nonneg hM]
    · simp [ht, hM]
  calc
    |∫ t : ℝ, Set.indicator S f t ∂muS| ≤ ∫ t : ℝ, |Set.indicator S f t| ∂muS :=
      MeasureTheory.abs_integral_le_integral_abs
    _ ≤ ∫ t : ℝ, M * Set.indicator S (fun _ : ℝ => (1 : ℝ)) t ∂muS := by
      refine MeasureTheory.integral_mono_ae hfSabs_int hMS_int ?_
      refine Eventually.of_forall (fun t => ?_)
      by_cases ht : t ∈ S
      · simpa [ht] using hf t ht
      · simp [ht, hM]
    _ = M * (muS S).toReal := by
      rw [MeasureTheory.integral_const_mul]
      rw [MeasureTheory.integral_indicator hS]
      rw [MeasureTheory.setIntegral_const]
      simp [MeasureTheory.measureReal_def]

/-! ## Auxiliary lemmas for the continuity proof -/

/-- `μ(S).toReal ≤ 1` for every set (μ is a probability measure). -/
lemma muS_toReal_le_one (S : Set ℝ) : (muS S).toReal ≤ 1 := by
  have hle : muS S ≤ 1 := by
    calc
      muS S ≤ muS Set.univ := measure_mono (Set.subset_univ S)
      _ = 1 := muS_univ
  have hfin : muS S ≠ ∞ := ne_of_lt (lt_of_le_of_lt hle (by norm_num : (1 : ℝ≥0∞) < ∞))
  have hfin1 : (1 : ℝ≥0∞) ≠ ∞ := by norm_num
  exact (ENNReal.toReal_le_toReal hfin hfin1).2 hle

/-- log is `2δ/ρ`-Lipschitz away from the singularities: for `p,q ≥ ρ/2` and
`|p−q| ≤ δ`, `|log p − log q| ≤ 2δ/ρ`. -/
lemma log_diff_bound_away {p q δ ρ : ℝ} (hp0 : 0 < p) (hq0 : 0 < q)
    (hδ : |p - q| ≤ δ) (hmin : ρ / 2 ≤ min p q) (hρ0 : 0 < ρ) (hδ0 : 0 ≤ δ) :
    |Real.log p - Real.log q| ≤ 2 * δ / ρ := by
  have hstep1 : |Real.log p - Real.log q| ≤ |p - q| / min p q := abs_log_sub_le_div_min hp0 hq0
  have hρ20 : 0 < ρ / 2 := by positivity
  have hmin0 : 0 < min p q := lt_of_lt_of_le hρ20 hmin
  have hminpos : 0 ≤ min p q := le_of_lt hmin0
  have h2 : |p - q| / min p q ≤ δ / min p q := by
    exact div_le_div_of_nonneg_right hδ hminpos
  have h3 : δ / min p q ≤ δ / (ρ / 2) := by
    exact div_le_div_of_nonneg_left hδ0 hρ20 hmin
  have h4 : δ / (ρ / 2) = 2 * δ / ρ := by ring
  calc
    |Real.log p - Real.log q| ≤ |p - q| / min p q := hstep1
    _ ≤ δ / min p q := h2
    _ ≤ δ / (ρ / 2) := h3
    _ = 2 * δ / ρ := h4

/-! ## The main continuity theorem -/

/-- (W2) Continuity of the Serre potential on the real axis. -/
theorem logPotential_continuous_real :
    Continuous (fun x : ℝ => logPotential (serreMeasure gSerre aSerre bSerre) (x : ℂ)) := by
  change Continuous (fun x : ℝ => logPotential muS (x : ℂ))
  rw [continuous_iff_continuousAt]
  intro x₀
  rw [Metric.continuousAt_iff]
  intro η hη
  let F : ℝ → ℝ := fun x => logPotential muS (x : ℂ)
  let Φ : ℝ → ℝ := fun r => Kloc * (Real.sqrt r * (2 + |Real.log r|))
  have hΦ0 : Tendsto Φ (𝓝[>] (0 : ℝ)) (𝓝 0) := by
    simpa [Φ] using sqrt_log2_tendsto_zero.const_mul Kloc
  have hEv : ∀ᶠ r in 𝓝[>] (0 : ℝ), Φ r < η / 4 :=
    hΦ0.eventually ((isOpen_Iio.mem_nhds (by linarith : (0 : ℝ) < η / 4)))
  have hlim : ∃ δ > 0, ∀ r : ℝ, 0 < r → r < δ → Φ r < η / 4 := by
    rw [eventually_nhdsWithin_iff] at hEv
    rw [Metric.eventually_nhds_iff] at hEv
    rcases hEv with ⟨δ, hδ0, hδ⟩
    refine ⟨δ, hδ0, ?_⟩
    intro r hr0 hlr
    have hdist : dist r 0 < δ := by
      simpa [Real.dist_eq, sub_zero, abs_of_pos hr0] using hlr
    exact (hδ hdist) hr0
  rcases hlim with ⟨δ₁, hδ₁0, hδ₁⟩
  let ρ : ℝ := min (δ₁ / 3) (1 / 4)
  have hρ0 : 0 < ρ := by
    dsimp [ρ]
    positivity
  have hρ_le_d : ρ ≤ δ₁ / 3 := min_le_left _ _
  have hρ_lt_d : ρ < δ₁ := lt_of_le_of_lt hρ_le_d (by linarith)
  have h2ρ_lt_d : 2 * ρ < δ₁ := by
    have h : 2 * ρ ≤ 2 * (δ₁ / 3) := by nlinarith [hρ_le_d]
    nlinarith
  have hρ14 : ρ ≤ 1 / 4 := min_le_right _ _
  have h2ρ_pos : 0 < 2 * ρ := by positivity
  have h2ρ_le1 : 2 * ρ ≤ 1 := by nlinarith [hρ14]
  have hΦρ : Φ ρ < η / 4 := hδ₁ ρ hρ0 hρ_lt_d
  have hΦ2ρ : Φ (2 * ρ) < η / 4 := hδ₁ (2 * ρ) h2ρ_pos h2ρ_lt_d
  let eps₀ : ℝ := min (ρ / 2) (η * ρ / 8)
  have heps0 : 0 < eps₀ := by
    dsimp [eps₀]
    positivity
  refine ⟨eps₀, heps0, ?_⟩
  intro x hx
  have hδ : |x - x₀| < eps₀ := by simpa [Real.dist_eq] using hx
  have hδ_ρ2 : |x - x₀| < ρ / 2 := by
    have : eps₀ ≤ ρ / 2 := min_le_left _ _
    linarith
  have hδ_η : |x - x₀| < η * ρ / 8 := by
    have : eps₀ ≤ η * ρ / 8 := min_le_right _ _
    linarith
  have hδ_le_ρ : |x - x₀| ≤ ρ := by
    have : |x - x₀| < ρ / 2 := hδ_ρ2
    nlinarith [hρ0]
  -- local kernels g₀ (radius ρ around x₀), g₁ (radius 2ρ around x) and P,Q,R
  let D : ℝ → ℝ := fun t => Real.log (|x₀ - t|) - Real.log (|x - t|)
  let g₀ : ℝ → ℝ := fun t =>
    Set.indicator {t : ℝ | |t - x₀| ≤ ρ} (fun t : ℝ => |Real.log (|t - x₀|)|) t
  let g₁ : ℝ → ℝ := fun t =>
    Set.indicator {t : ℝ | |t - x| ≤ 2 * ρ} (fun t : ℝ => |Real.log (|t - x|)|) t
  let P : ℝ → ℝ := fun t =>
    Set.indicator {t : ℝ | |x₀ - t| ≤ ρ} (fun t : ℝ => |Real.log (|x₀ - t|)|) t
  let Q : ℝ → ℝ := fun t =>
    Set.indicator {t : ℝ | |x - t| ≤ 2 * ρ} (fun t : ℝ => |Real.log (|x - t|)|) t
  let c : ℝ := 2 * |x - x₀| / ρ
  let R : ℝ → ℝ := fun t =>
    c * Set.indicator {t : ℝ | ρ < |t - x₀|} (fun _ : ℝ => (1 : ℝ)) t
  have hc0 : 0 ≤ c := by dsimp [c]; positivity
  -- pointwise value equations (no simplification of the log!)
  have hP_of (t : ℝ) (ht : |x₀ - t| ≤ ρ) : P t = |Real.log (|x₀ - t|)| := by
    dsimp [P]
    simp [ht]
  have hQ_of (t : ℝ) (ht : |x - t| ≤ 2 * ρ) : Q t = |Real.log (|x - t|)| := by
    dsimp [Q]
    simp [ht]
  have hR_of (t : ℝ) (ht : ρ < |t - x₀|) : R t = c := by
    dsimp [R]
    simp [ht]
  have hPg0 : P = g₀ := by
    funext t
    by_cases ht : |x₀ - t| ≤ ρ
    · have ht0 : |t - x₀| ≤ ρ := by simpa [abs_sub_comm] using ht
      simp [P, g₀, ht, ht0]
      rw [show x₀ - t = -(t - x₀) by ring, Real.log_neg_eq_log (t - x₀)]
    · have ht0 : ¬ |t - x₀| ≤ ρ := by simpa [abs_sub_comm] using ht
      simp [P, g₀, ht, ht0]
  have hQg1 : Q = g₁ := by
    funext t
    by_cases ht : |x - t| ≤ 2 * ρ
    · have ht0 : |t - x| ≤ 2 * ρ := by simpa [abs_sub_comm] using ht
      simp [Q, g₁, ht, ht0]
      rw [show x - t = -(t - x) by ring, Real.log_neg_eq_log (t - x)]
    · have ht0 : ¬ |t - x| ≤ 2 * ρ := by simpa [abs_sub_comm] using ht
      simp [Q, g₁, ht, ht0]
  have hP_nonneg (t : ℝ) : 0 ≤ P t := by
    by_cases h : |x₀ - t| ≤ ρ
    · rw [hP_of t h]; exact abs_nonneg _
    · dsimp [P]; simp [h]
  have hQ_nonneg (t : ℝ) : 0 ≤ Q t := by
    by_cases h : |x - t| ≤ 2 * ρ
    · rw [hQ_of t h]; exact abs_nonneg _
    · dsimp [Q]; simp [h]
  have hR_nonneg (t : ℝ) : 0 ≤ R t := by
    dsimp [R]
    by_cases h : ρ < |t - x₀|
    · simp [h, hc0]
    · simp [h, hc0]
  -- integrability of D and the kernels
  have hDmeas : Measurable D := by
    dsimp [D]
    have h1 : Measurable fun t : ℝ => Real.log (|x₀ - t|) := by
      refine Real.measurable_log.comp ?_
      exact (continuous_const.sub continuous_id).abs.measurable
    have h2 : Measurable fun t : ℝ => Real.log (|x - t|) := by
      refine Real.measurable_log.comp ?_
      exact (continuous_const.sub continuous_id).abs.measurable
    exact h1.sub h2
  have hDint : Integrable D muS := by
    dsimp [D]
    exact logDiff_integrable x x₀
  have htrunc_int (c' : ℝ) (r : ℝ) (hr0 : 0 < r) (hr1 : r ≤ 1) :
      Integrable (fun t : ℝ =>
        Set.indicator {t : ℝ | |t - c'| ≤ r} (fun t : ℝ => |Real.log (|t - c'|)|) t) muS := by
    constructor
    · exact (GenericLocalLog.log_kernel_trunc_measurable c' r).aestronglyMeasurable
    · rw [MeasureTheory.hasFiniteIntegral_iff_ofReal
        (Eventually.of_forall (GenericLocalLog.log_kernel_trunc_nonneg c' r))]
      have hb := GenericLocalLog.log_kernel_ennreal_bound (μ := muS) (C := Cmu) (c := c') (r := r)
        Cmu_pos.le muS_ball_mass hr0 hr1
      exact lt_of_le_of_lt (by simpa using hb) (ENNReal.ofReal_lt_top)
  have hg0_int : Integrable g₀ muS := htrunc_int x₀ ρ hρ0 (by nlinarith [hρ14])
  have hg1_int : Integrable g₁ muS := htrunc_int x (2 * ρ) h2ρ_pos h2ρ_le1
  have hP_int : Integrable P muS := by
    rw [hPg0]
    exact hg0_int
  have hQ_int : Integrable Q muS := by
    rw [hQg1]
    exact hg1_int
  have hRmeas : Measurable R := by
    dsimp [R]
    have hS : MeasurableSet {t : ℝ | ρ < |t - x₀|} := by
      have hg : Continuous fun t : ℝ => |t - x₀| := by fun_prop
      exact (isOpen_lt continuous_const hg).measurableSet
    have hind : Measurable ({t : ℝ | ρ < |t - x₀|}.indicator (fun _ : ℝ => (1 : ℝ))) :=
      (measurable_const : Measurable (fun _ : ℝ => (1 : ℝ))).indicator hS
    exact (measurable_const : Measurable (fun _ : ℝ => (c : ℝ))).mul hind
  have hR_int : Integrable R muS := by
    refine Integrable.mono' (MeasureTheory.integrable_const c) hRmeas.aestronglyMeasurable ?_
    refine Eventually.of_forall (fun t => ?_)
    by_cases ht : ρ < |t - x₀|
    · dsimp [R]
      simp [ht, Real.norm_eq_abs, abs_of_nonneg hc0]
    · dsimp [R]
      simp [ht, hc0]
  -- triangle and Lipschitz pointwise bounds
  have hD_tri (t : ℝ) : |D t| ≤ |Real.log (|x₀ - t|)| + |Real.log (|x - t|)| := by
    dsimp [D]
    have ha : Real.log (|x₀ - t|) - Real.log (|x - t|) ≤
        |Real.log (|x₀ - t|)| + |Real.log (|x - t|)| := by
      nlinarith [le_abs_self (Real.log (|x₀ - t|)), neg_le_abs (Real.log (|x - t|))]
    have hb : Real.log (|x - t|) - Real.log (|x₀ - t|) ≤
        |Real.log (|x₀ - t|)| + |Real.log (|x - t|)| := by
      nlinarith [neg_le_abs (Real.log (|x₀ - t|)), le_abs_self (Real.log (|x - t|))]
    exact (abs_sub_le_iff.mpr ⟨ha, hb⟩)
  have hFarLog (t : ℝ) (ht : ρ < |t - x₀|) : |D t| ≤ c := by
    dsimp [c]
    dsimp [D]
    let p : ℝ := |x - t|
    let q : ℝ := |x₀ - t|
    have ht' : ρ < |x₀ - t| := by simpa [abs_sub_comm] using ht
    have htri (a b c : ℝ) : |a - c| ≤ |a - b| + |b - c| := by
      simpa [Real.dist_eq] using (dist_triangle a b c)
    have htri1 : q ≤ p + |x - x₀| := by
      have hsum : |x₀ - t| ≤ |x - t| + |x - x₀| := by
        simpa [abs_sub_comm, add_comm, add_left_comm, add_assoc] using (htri x₀ x t)
      simpa [p, q] using hsum
    have hp_ge : ρ / 2 ≤ p := by
      have hδle : |x - x₀| ≤ ρ / 2 := le_of_lt hδ_ρ2
      dsimp [p, q]
      nlinarith [ht', htri1, hδle, hρ0]
    have hq_ge : ρ / 2 ≤ q := by
      dsimp [q]
      nlinarith [ht', hρ0]
    have hpq : |p - q| ≤ |x - x₀| := by
      have h1 : |x - t| - |x₀ - t| ≤ |x - x₀| := by
        have hx : |x - t| ≤ |x - x₀| + |x₀ - t| := htri x x₀ t
        nlinarith
      have h2 : |x₀ - t| - |x - t| ≤ |x - x₀| := by
        have hx : |x₀ - t| ≤ |x - x₀| + |x - t| := by
          simpa [abs_sub_comm] using (htri x₀ x t)
        nlinarith
      dsimp [p, q]
      exact (abs_sub_le_iff.mpr ⟨h1, h2⟩)
    have hp0 : 0 < p := lt_of_lt_of_le (by positivity) hp_ge
    have hq0 : 0 < q := lt_of_lt_of_le (by positivity) hq_ge
    have hmin : ρ / 2 ≤ min p q := le_min hp_ge hq_ge
    have hδ0 : 0 ≤ |x - x₀| := abs_nonneg (x - x₀)
    have hbnd := log_diff_bound_away (p := p) (q := q) (δ := |x - x₀|) (ρ := ρ)
      hp0 hq0 hpq hmin hρ0 hδ0
    calc
      |D t| = |Real.log q - Real.log p| := by
        dsimp [D, p, q]
      _ = |Real.log p - Real.log q| := by
        rw [abs_sub_comm (Real.log q) (Real.log p)]
      _ ≤ 2 * |x - x₀| / ρ := by simpa [p, q] using hbnd
  -- global pointwise bound |D t| ≤ P t + Q t + R t
  have hglobal (t : ℝ) : |D t| ≤ P t + Q t + R t := by
    by_cases htn : |t - x₀| ≤ ρ
    · have htn' : |x₀ - t| ≤ ρ := by simpa [abs_sub_comm] using htn
      have hdtri : |D t| ≤ |Real.log (|x₀ - t|)| + |Real.log (|x - t|)| := hD_tri t
      have hcloset : |x - t| ≤ 2 * ρ := by
        have htri (a b c : ℝ) : |a - c| ≤ |a - b| + |b - c| := by
          simpa [Real.dist_eq] using (dist_triangle a b c)
        have h1 : |x - t| ≤ |x - x₀| + |x₀ - t| := htri x x₀ t
        have h2 : |x - x₀| + |x₀ - t| ≤ 2 * ρ := by
          have hx0 : |x₀ - t| = |t - x₀| := abs_sub_comm x₀ t
          rw [hx0]
          nlinarith [hδ_le_ρ, htn]
        exact le_trans h1 h2
      calc
        |D t| ≤ |Real.log (|x₀ - t|)| + |Real.log (|x - t|)| := hdtri
        _ = P t + Q t := by rw [hP_of t htn', hQ_of t hcloset]
        _ ≤ P t + Q t + R t := le_add_of_nonneg_right (hR_nonneg t)
    · have hfar_t : ρ < |t - x₀| := lt_of_not_ge htn
      have hlog_far : |D t| ≤ c := hFarLog t hfar_t
      have hRof : R t = c := hR_of t hfar_t
      calc
        |D t| ≤ c := hlog_far
        _ = R t := hRof.symm
        _ ≤ P t + Q t + R t := by
          exact le_add_of_nonneg_left (add_nonneg (hP_nonneg t) (hQ_nonneg t))
  -- local-bound integrals
  have hloc₀ : (∫ t : ℝ, g₀ t ∂muS) ≤ Φ ρ := by
    have h := local_log_bound x₀ hρ0 (by nlinarith [hρ14])
    dsimp [g₀, Φ]
    simpa using h
  have hloc₁ : (∫ t : ℝ, g₁ t ∂muS) ≤ Φ (2 * ρ) := by
    have h := local_log_bound x h2ρ_pos h2ρ_le1
    dsimp [g₁, Φ]
    simpa using h
  have hIntP : (∫ t : ℝ, P t ∂muS) ≤ Φ ρ := by
    calc
      (∫ t : ℝ, P t ∂muS) = (∫ t : ℝ, g₀ t ∂muS) := by rw [hPg0]
      _ ≤ Φ ρ := hloc₀
  have hIntQ : (∫ t : ℝ, Q t ∂muS) ≤ Φ (2 * ρ) := by
    calc
      (∫ t : ℝ, Q t ∂muS) = (∫ t : ℝ, g₁ t ∂muS) := by rw [hQg1]
      _ ≤ Φ (2 * ρ) := hloc₁
  have hIntR : (∫ t : ℝ, R t ∂muS) ≤ c := by
    have hRle_c : ∀ t : ℝ, R t ≤ c := by
      intro t
      by_cases ht : ρ < |t - x₀|
      · rw [hR_of t ht]
      · have : R t = 0 := by dsimp [R]; simp [ht]
        rw [this]
        exact hc0
    calc
      (∫ t : ℝ, R t ∂muS) ≤ (∫ t : ℝ, c ∂muS) :=
        MeasureTheory.integral_mono hR_int (MeasureTheory.integrable_const c) hRle_c
      _ = c := by
        rw [MeasureTheory.integral_const]
        simp [muS_univ]
  -- assemble
  have hDabs_le : (∫ t : ℝ, |D t| ∂muS) ≤
      (∫ t : ℝ, P t ∂muS) + (∫ t : ℝ, Q t ∂muS) + (∫ t : ℝ, R t ∂muS) := by
    calc
      (∫ t : ℝ, |D t| ∂muS) ≤ (∫ t : ℝ, P t + Q t + R t ∂muS) :=
        MeasureTheory.integral_mono hDint.abs ((hP_int.add hQ_int).add hR_int) hglobal
      _ = (∫ t : ℝ, P t ∂muS) + (∫ t : ℝ, Q t ∂muS) + (∫ t : ℝ, R t ∂muS) := by
        have h1 : (∫ t : ℝ, P t + Q t + R t ∂muS) =
            (∫ t : ℝ, P t + Q t ∂muS) + (∫ t : ℝ, R t ∂muS) :=
          MeasureTheory.integral_add (hP_int.add hQ_int) hR_int
        have h2 : (∫ t : ℝ, P t + Q t ∂muS) =
            (∫ t : ℝ, P t ∂muS) + (∫ t : ℝ, Q t ∂muS) :=
          MeasureTheory.integral_add hP_int hQ_int
        rw [h1, h2]
  have hmain : |F x - F x₀| ≤ Φ ρ + Φ (2 * ρ) + c := by
    have hF : F x - F x₀ = (∫ t : ℝ, D t ∂muS) := by
      dsimp [F, D]
      exact potential_diff_formula x x₀
    have h1 : |∫ t : ℝ, D t ∂muS| ≤ (∫ t : ℝ, |D t| ∂muS) := MeasureTheory.abs_integral_le_integral_abs
    calc
      |F x - F x₀| = |∫ t : ℝ, D t ∂muS| := by rw [hF]
      _ ≤ (∫ t : ℝ, |D t| ∂muS) := h1
      _ ≤ (∫ t : ℝ, P t ∂muS) + (∫ t : ℝ, Q t ∂muS) + (∫ t : ℝ, R t ∂muS) := hDabs_le
      _ ≤ Φ ρ + Φ (2 * ρ) + c := by
        dsimp [c]
        nlinarith [hIntP, hIntQ, hIntR]
  have hq3 : c < η / 4 := by
    dsimp [c]
    have hprod : 2 * |x - x₀| < η * ρ / 4 := by nlinarith [hδ_η]
    rw [div_lt_iff₀ hρ0]
    nlinarith
  have htot : Φ ρ + Φ (2 * ρ) + c < η := by
    nlinarith [hΦρ, hΦ2ρ, hq3]
  have hnorm : |F x - F x₀| < η := lt_of_le_of_lt hmain htot
  simpa [Real.dist_eq] using hnorm

end Submission.PotentialContinuity
