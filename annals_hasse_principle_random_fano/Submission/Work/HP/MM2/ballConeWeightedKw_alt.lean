import Mathlib
import Submission.Work.HP.MM2.Defs
import Submission.Work.HP.BallConeK.Defs
import Submission.Work.HP.BallVolIntrinsic
import Submission.Work.HP.lam_basic
import Submission.Work.HP.rk_le_card
import Submission.Work.HP.BCS.Setup
import Submission.Work.HP.BCS.count_from_layer
import Submission.Work.HP.BCS.coneTube_bound
import Submission.Work.HP.BCS.small_basis_clean
import Submission.Work.HP.Lat.detL_basis_gram
import Submission.Work.HP.BallConeK.layerCake
import Submission.Work.HP.BallConeK.mainTermIdent
import Submission.Work.HP.BallConeK.coneCountSub
import Submission.Work.HP.BallConeK.largeFilterCard
import Submission.Work.HP.BallConeK.integralDivPow
import Submission.Work.HP.Lat.detL_ge_one
import Submission.Work.HP.BCS.BallConeCountPub
import Submission.Work.HP.MM2.ConeSliceVolBound

/-!
# `Work.HP.MM2.ballConeWeightedKw_alt`

Weighted Abel summation for the two-cone lattice count, with the *weighted* short-vector term.

The proof splits the weighted sum `S = S_Y + S_{>Y}` at radius `Y`, computes `S_{>Y}` exactly by
partial summation against the counting function `coneCount` (the Abel step for the main term is
`BallConeK.mainTermIdent`), and bounds the resulting boundary/integral errors using the uniform
cone-count estimate `BCS.BallConeCountPub`.  The extra term `q * (r/(r-k)) * Y^{r-k}` produced by
the split is killed by the dimension-uniform bound `ConeSliceVolBound` on `coneSliceVol`
(`Y^{r-k} <= T^{r-k-1} * Y`, `rk L <= Fintype.card iota`).
-/

set_option autoImplicit false
noncomputable section
set_option maxHeartbeats 4000000
set_option linter.unusedSectionVars false

open Finset MeasureTheory

namespace Work.HP.MM2

/-- `1 ≤ lam L (rk L)` for a lattice of positive rank. -/
private lemma one_le_lam_rk {ι : Type*} [Fintype ι] (L : Submodule ℤ (ι → ℤ)) (hr : 1 ≤ rk L) :
    1 ≤ lam L (rk L) := by
  rw [lam_eq_sInf]
  refine le_csInf (lamSet_nonempty L le_rfl) ?_
  rintro r ⟨_, f, hfL, hfind, hfr⟩
  exact le_trans (one_le_eNorm (hfind.ne_zero ⟨0, hr⟩)) (hfr ⟨0, hr⟩)

/-- `∫_Y^T (k/t^{k+1}) (t^r - Y^r) dt` in closed form. -/
private lemma integral_model {k r : ℕ} {Y T : ℝ} (hkr : k + 1 < r) (hY : 0 < Y) (hYT : Y ≤ T) :
    ∫ t in Y..T, ((k : ℝ) / t ^ (k + 1)) * (t ^ r - Y ^ r)
      = (k : ℝ) * (T ^ (r - k) - Y ^ (r - k)) / ((r - k : ℕ) : ℝ)
        - Y ^ r * (1 / Y ^ k - 1 / T ^ k) := by
  have hpt : ∀ t ∈ Set.uIcc Y T, ((k : ℝ) / t ^ (k + 1)) * (t ^ r - Y ^ r)
      = (k : ℝ) * t ^ (r - k - 1) - Y ^ r * ((k : ℝ) / t ^ (k + 1)) := by
    intro t ht
    rw [Set.uIcc_of_le hYT] at ht
    have ht0 : t ≠ 0 := ne_of_gt (lt_of_lt_of_le hY ht.1)
    have h1 : t ^ r = t ^ (k + 1) * t ^ (r - k - 1) := by
      rw [← pow_add]
      congr 1
      omega
    rw [h1, mul_sub]
    have h2 : (k : ℝ) / t ^ (k + 1) * (t ^ (k + 1) * t ^ (r - k - 1))
        = (k : ℝ) * t ^ (r - k - 1) := by
      field_simp
    rw [h2]
    ring
  have hcont1 : ContinuousOn (fun t : ℝ => (k : ℝ) * t ^ (r - k - 1)) (Set.Icc Y T) :=
    (continuous_const.mul (continuous_pow _)).continuousOn
  have hcont2 : ContinuousOn (fun t : ℝ => Y ^ r * ((k : ℝ) / t ^ (k + 1))) (Set.Icc Y T) :=
    continuousOn_const.mul (ContinuousOn.div continuousOn_const (continuousOn_pow _)
      (fun t ht => pow_ne_zero _ (ne_of_gt (lt_of_lt_of_le hY ht.1))))
  rw [intervalIntegral.integral_congr hpt,
    intervalIntegral.integral_sub (hcont1.intervalIntegrable_of_Icc hYT)
      (hcont2.intervalIntegrable_of_Icc hYT),
    intervalIntegral.integral_const_mul, integral_pow,
    intervalIntegral.integral_const_mul, BallConeK.integralDivPow k hY hYT]
  have hsucc : (r - k - 1) + 1 = r - k := by omega
  have hden : ((r - k - 1 : ℕ) : ℝ) + 1 = ((r - k : ℕ) : ℝ) := by
    have h2 : ((r - k - 1 : ℕ) + 1 : ℕ) = (r - k : ℕ) := hsucc
    calc ((r - k - 1 : ℕ) : ℝ) + 1 = ((r - k - 1 : ℕ) : ℝ) + ((1 : ℕ) : ℝ) := by norm_num
      _ = (((r - k - 1 : ℕ) + 1 : ℕ) : ℝ) := by rw [Nat.cast_add]
      _ = ((r - k : ℕ) : ℝ) := by rw [h2]
  rw [hsucc, hden]
  ring

/-- `|a + b + c - d| ≤ |a| + |b| + |c| + |d|`. -/
private lemma abs_add_add_sub_le (a b c d : ℝ) : |a + b + c - d| ≤ |a| + |b| + |c| + |d| := by
  calc |a + b + c - d| ≤ |a + b + c| + |d| := by simpa using abs_sub_le (a + b + c) 0 d
    _ ≤ (|a + b| + |c|) + |d| := by linarith [abs_add_le (a + b) c]
    _ ≤ ((|a| + |b|) + |c|) + |d| := by linarith [abs_add_le a b]
    _ = |a| + |b| + |c| + |d| := by ring

/-- The "error integral" bound: a pointwise bound `|e t| ≤ C₀ t^{r-1} Y / d` on `[Y,T]` gives
`|∫_Y^T (k/t^{k+1})(e t - e Y) dt| ≤ C₀(k+1) T^{r-k-1} Y / d`. -/
private lemma errIntegralBound (k r : ℕ) {Y T C₀ d : ℝ}
    (hk : 1 ≤ k) (hkr : k + 1 < r) (hY : 0 < Y) (hYT : Y ≤ T) (hd : 0 < d) (hC₀ : 0 ≤ C₀)
    (e : ℝ → ℝ) (he : ∀ t ∈ Set.Icc Y T, |e t| ≤ C₀ * t ^ (r - 1) * Y / d)
    (hi : IntervalIntegrable (fun t => (k : ℝ) / t ^ (k + 1) * (e t - e Y)) volume Y T) :
    |∫ t in Y..T, (k : ℝ) / t ^ (k + 1) * (e t - e Y)|
      ≤ (C₀ * (k + 1)) * (T ^ (r - k - 1) * Y / d) := by
  have hTpos : 0 < T := lt_of_lt_of_le hY hYT
  have hYmem : Y ∈ Set.Icc Y T := ⟨le_rfl, hYT⟩
  have hCYnn : 0 ≤ C₀ * Y / d := div_nonneg (mul_nonneg hC₀ (le_of_lt hY)) (le_of_lt hd)
  have hstep1 : |∫ t in Y..T, (k : ℝ) / t ^ (k + 1) * (e t - e Y)|
      ≤ ∫ t in Y..T, |(k : ℝ) / t ^ (k + 1) * (e t - e Y)| :=
    intervalIntegral.abs_integral_le_integral_abs hYT
  have hpt1 : ∀ t ∈ Set.Icc Y T, |(k : ℝ) / t ^ (k + 1) * (e t - e Y)|
      ≤ C₀ * Y / d * (k * t ^ (r - k - 2)) + C₀ * Y ^ r / d * ((k : ℝ) / t ^ (k + 1)) := by
    intro t ht
    have htpos : 0 < t := lt_of_lt_of_le hY ht.1
    have ht0 : t ≠ 0 := ne_of_gt htpos
    have h1 : |(k : ℝ) / t ^ (k + 1) * (e t - e Y)|
        = (k : ℝ) / t ^ (k + 1) * |e t - e Y| := by
      rw [abs_mul, abs_of_nonneg (by positivity)]
    have h2 : |e t - e Y| ≤ C₀ * t ^ (r - 1) * Y / d + C₀ * Y ^ (r - 1) * Y / d := by
      have h3 : |e t - e Y| ≤ |e t| + |e Y| := by simpa using abs_sub_le (e t) 0 (e Y)
      have h4 := he t ht
      have h5 := he Y hYmem
      linarith
    have hp1 : t ^ (r - 1) / t ^ (k + 1) = t ^ (r - k - 2) := by
      rw [div_eq_mul_inv]
      have h6 : r - k - 2 = r - 1 - (k + 1) := by omega
      rw [h6]
      simpa using (pow_sub₀ t ht0 (by omega : k + 1 ≤ r - 1)).symm
    have hp2 : Y ^ (r - 1) * Y = Y ^ r := by
      rw [← pow_succ, Nat.sub_add_cancel (by omega : 1 ≤ r)]
    have e1 : (k : ℝ) / t ^ (k + 1) * (C₀ * t ^ (r - 1) * Y / d)
        = C₀ * Y / d * (k * (t ^ (r - 1) / t ^ (k + 1))) := by ring
    have e2 : (k : ℝ) / t ^ (k + 1) * (C₀ * Y ^ (r - 1) * Y / d)
        = C₀ * Y ^ r / d * ((k : ℝ) / t ^ (k + 1)) := by
      rw [← hp2]; ring
    calc |(k : ℝ) / t ^ (k + 1) * (e t - e Y)|
        = (k : ℝ) / t ^ (k + 1) * |e t - e Y| := h1
      _ ≤ (k : ℝ) / t ^ (k + 1) * (C₀ * t ^ (r - 1) * Y / d + C₀ * Y ^ (r - 1) * Y / d) :=
          mul_le_mul_of_nonneg_left h2 (by positivity)
      _ = (k : ℝ) / t ^ (k + 1) * (C₀ * t ^ (r - 1) * Y / d)
            + (k : ℝ) / t ^ (k + 1) * (C₀ * Y ^ (r - 1) * Y / d) := by ring
      _ = C₀ * Y / d * (k * t ^ (r - k - 2)) + C₀ * Y ^ r / d * ((k : ℝ) / t ^ (k + 1)) := by
          rw [e1, e2, hp1]
  have hcont1 : ContinuousOn (fun t : ℝ => C₀ * Y / d * (k * t ^ (r - k - 2))
      + C₀ * Y ^ r / d * ((k : ℝ) / t ^ (k + 1))) (Set.Icc Y T) := by
    refine ContinuousOn.add ?_ ?_
    · exact continuousOn_const.mul (continuousOn_const.mul (continuousOn_pow _))
    · refine continuousOn_const.mul ?_
      exact ContinuousOn.div continuousOn_const (continuousOn_pow _)
        (fun t ht => pow_ne_zero _ (ne_of_gt (lt_of_lt_of_le hY ht.1)))
  have hint1 : IntervalIntegrable (fun t : ℝ => C₀ * Y / d * (k * t ^ (r - k - 2))
      + C₀ * Y ^ r / d * ((k : ℝ) / t ^ (k + 1))) volume Y T :=
    hcont1.intervalIntegrable_of_Icc hYT
  have hstep2 : ∫ t in Y..T, |(k : ℝ) / t ^ (k + 1) * (e t - e Y)|
      ≤ ∫ t in Y..T, (C₀ * Y / d * (k * t ^ (r - k - 2))
          + C₀ * Y ^ r / d * ((k : ℝ) / t ^ (k + 1))) :=
    intervalIntegral.integral_mono_on hYT hi.abs hint1 hpt1
  have hpt2 : ∀ t ∈ Set.Icc Y T, C₀ * Y / d * (k * t ^ (r - k - 2))
      + C₀ * Y ^ r / d * ((k : ℝ) / t ^ (k + 1))
      ≤ C₀ * Y / d * (k * T ^ (r - k - 2)) + C₀ * Y ^ r / d * ((k : ℝ) / t ^ (k + 1)) := by
    intro t ht
    have h1 : t ^ (r - k - 2) ≤ T ^ (r - k - 2) :=
      pow_le_pow_left₀ (le_of_lt (lt_of_lt_of_le hY ht.1)) ht.2 _
    have h2 := mul_le_mul_of_nonneg_left h1 (Nat.cast_nonneg k)
    have h3 := mul_le_mul_of_nonneg_left h2 hCYnn
    linarith [h3]
  have hcont2 : ContinuousOn (fun t : ℝ => C₀ * Y / d * (k * T ^ (r - k - 2))
      + C₀ * Y ^ r / d * ((k : ℝ) / t ^ (k + 1))) (Set.Icc Y T) := by
    refine ContinuousOn.add continuousOn_const ?_
    refine continuousOn_const.mul ?_
    exact ContinuousOn.div continuousOn_const (continuousOn_pow _)
      (fun t ht => pow_ne_zero _ (ne_of_gt (lt_of_lt_of_le hY ht.1)))
  have hint2 : IntervalIntegrable (fun t : ℝ => C₀ * Y / d * (k * T ^ (r - k - 2))
      + C₀ * Y ^ r / d * ((k : ℝ) / t ^ (k + 1))) volume Y T :=
    hcont2.intervalIntegrable_of_Icc hYT
  have hstep3 : ∫ t in Y..T, (C₀ * Y / d * (k * t ^ (r - k - 2))
      + C₀ * Y ^ r / d * ((k : ℝ) / t ^ (k + 1)))
      ≤ ∫ t in Y..T, (C₀ * Y / d * (k * T ^ (r - k - 2))
          + C₀ * Y ^ r / d * ((k : ℝ) / t ^ (k + 1))) :=
    intervalIntegral.integral_mono_on hYT hint1 hint2 hpt2
  have hintc : IntervalIntegrable (fun t : ℝ => C₀ * Y / d * (k * T ^ (r - k - 2)))
      volume Y T := (continuousOn_const).intervalIntegrable_of_Icc hYT
  have hintd : IntervalIntegrable (fun t : ℝ => C₀ * Y ^ r / d * ((k : ℝ) / t ^ (k + 1)))
      volume Y T :=
    (continuousOn_const.mul (ContinuousOn.div continuousOn_const (continuousOn_pow _)
      (fun t ht => pow_ne_zero _ (ne_of_gt (lt_of_lt_of_le hY ht.1))))).intervalIntegrable_of_Icc hYT
  have hval : ∫ t in Y..T, (C₀ * Y / d * (k * T ^ (r - k - 2))
      + C₀ * Y ^ r / d * ((k : ℝ) / t ^ (k + 1)))
      = C₀ * Y / d * (k * T ^ (r - k - 2)) * (T - Y)
        + C₀ * Y ^ r / d * (1 / Y ^ k - 1 / T ^ k) := by
    rw [intervalIntegral.integral_add hintc hintd, intervalIntegral.integral_const,
      intervalIntegral.integral_const_mul, BallConeK.integralDivPow k hY hYT]
    simp only [smul_eq_mul]
    ring
  have hstep4 : C₀ * Y / d * (k * T ^ (r - k - 2)) * (T - Y)
      + C₀ * Y ^ r / d * (1 / Y ^ k - 1 / T ^ k)
      ≤ C₀ * k * T ^ (r - k - 1) * Y / d + C₀ * Y ^ (r - k) / d := by
    have hTY : T - Y ≤ T := by linarith [le_of_lt hY]
    have hpow : T ^ (r - k - 2) * T = T ^ (r - k - 1) := by
      rw [← pow_succ]
      congr 1
      omega
    have hA : C₀ * Y / d * (k * T ^ (r - k - 2)) * (T - Y)
        ≤ C₀ * k * T ^ (r - k - 1) * Y / d := by
      have h1 : 0 ≤ (k:ℝ) * T ^ (r - k - 2) := by positivity
      have h2 : 0 ≤ C₀ * Y / d := hCYnn
      calc C₀ * Y / d * (k * T ^ (r - k - 2)) * (T - Y)
          ≤ C₀ * Y / d * (k * T ^ (r - k - 2)) * T :=
            mul_le_mul_of_nonneg_left hTY (mul_nonneg h2 h1)
        _ = C₀ * k * (T ^ (r - k - 2) * T) * Y / d := by ring
        _ = C₀ * k * T ^ (r - k - 1) * Y / d := by rw [hpow]
    have hB : C₀ * Y ^ r / d * (1 / Y ^ k - 1 / T ^ k) ≤ C₀ * Y ^ (r - k) / d := by
      have h1 : 1 / Y ^ k - 1 / T ^ k ≤ 1 / Y ^ k := by
        have h2 : 0 ≤ 1 / T ^ k := by positivity
        linarith
      have h2 : 0 ≤ C₀ * Y ^ r / d :=
        div_nonneg (mul_nonneg hC₀ (by positivity)) (le_of_lt hd)
      have h3 : C₀ * Y ^ r / d * (1 / Y ^ k) = C₀ * Y ^ (r - k) / d := by
        have h4 : Y ^ r / Y ^ k = Y ^ (r - k) := by
          rw [div_eq_mul_inv]
          simpa using (pow_sub₀ Y (ne_of_gt hY) (by omega : k ≤ r)).symm
        have h5 : C₀ * Y ^ r / d * (1 / Y ^ k) = C₀ * (Y ^ r / Y ^ k) / d := by ring
        rw [h5, h4]
      calc C₀ * Y ^ r / d * (1 / Y ^ k - 1 / T ^ k)
          ≤ C₀ * Y ^ r / d * (1 / Y ^ k) := mul_le_mul_of_nonneg_left h1 h2
        _ = C₀ * Y ^ (r - k) / d := h3
    linarith [hA, hB]
  have hstep5 : C₀ * k * T ^ (r - k - 1) * Y / d + C₀ * Y ^ (r - k) / d
      ≤ (C₀ * (k + 1)) * (T ^ (r - k - 1) * Y / d) := by
    have hYZ : Y ^ (r - k) ≤ T ^ (r - k - 1) * Y := by
      calc Y ^ (r - k) = Y ^ (r - k - 1) * Y := by
            have h1 : Y ^ (r - k) = Y ^ ((r - k - 1) + 1) := by
              congr 1
              omega
            rw [h1, pow_succ]
        _ ≤ T ^ (r - k - 1) * Y :=
            mul_le_mul_of_nonneg_right
              (pow_le_pow_left₀ (le_of_lt hY) hYT (r - k - 1)) (le_of_lt hY)
    have h1 : C₀ * Y ^ (r - k) / d ≤ C₀ * (T ^ (r - k - 1) * Y) / d :=
      div_le_div_of_nonneg_right (mul_le_mul_of_nonneg_left hYZ hC₀) (le_of_lt hd)
    have h2 : C₀ * k * T ^ (r - k - 1) * Y / d + C₀ * (T ^ (r - k - 1) * Y) / d
        = (C₀ * (k + 1)) * (T ^ (r - k - 1) * Y / d) := by ring
    linarith [h1, h2]
  calc |∫ t in Y..T, (k : ℝ) / t ^ (k + 1) * (e t - e Y)|
      ≤ ∫ t in Y..T, |(k : ℝ) / t ^ (k + 1) * (e t - e Y)| := hstep1
    _ ≤ ∫ t in Y..T, (C₀ * Y / d * (k * t ^ (r - k - 2))
          + C₀ * Y ^ r / d * ((k : ℝ) / t ^ (k + 1))) := hstep2
    _ ≤ ∫ t in Y..T, (C₀ * Y / d * (k * T ^ (r - k - 2))
          + C₀ * Y ^ r / d * ((k : ℝ) / t ^ (k + 1))) := hstep3
    _ = C₀ * Y / d * (k * T ^ (r - k - 2)) * (T - Y)
          + C₀ * Y ^ r / d * (1 / Y ^ k - 1 / T ^ k) := hval
    _ ≤ C₀ * k * T ^ (r - k - 1) * Y / d + C₀ * Y ^ (r - k) / d := hstep4
    _ ≤ (C₀ * (k + 1)) * (T ^ (r - k - 1) * Y / d) := hstep5

/-! ## The weighted cone sum -/

theorem ballConeWeightedKw_alt {ι : Type} [Fintype ι] [DecidableEq ι] (k : ℕ) :
    ∃ C : ℝ, 0 < C ∧ ∀ (L : Submodule ℤ (ι → ℤ)) (v w : ι → ℝ) (γ T Y : ℝ),
      1 ≤ k → k + 1 < rk L → 0 < γ → 1 ≤ Y → lam L (rk L) ≤ Y → Y ≤ T →
      |(∑ᶠ a ∈ {a : ι → ℤ | a ∈ L ∧ a ≠ 0 ∧ eNorm a ≤ T ∧ toR a ∈ Cgam v γ ∧
            toR a ∈ Cgam w γ}, 1 / eNorm a ^ k) -
        ((rk L : ℝ) / ((rk L : ℝ) - (k : ℝ))) * T ^ (rk L - k) / detL L *
          coneSliceVol L v w γ|
        ≤ C * T ^ (rk L - k - 1) * Y / detL L
          + ∑ᶠ a ∈ {a : ι → ℤ | a ∈ L ∧ a ≠ 0 ∧ eNorm a ≤ Y ∧ toR a ∈ Cgam v γ ∧
              toR a ∈ Cgam w γ}, 1 / eNorm a ^ k := by
  obtain ⟨C₀, hC₀pos, hC₀⟩ := BCS.BallConeCountPub (ι := ι)
  obtain ⟨K, hKpos, hKcone⟩ := ConeSliceVolBound (ι := ι)
  set C : ℝ := 2 * C₀ + C₀ * ((k : ℝ) + 1) + (Fintype.card ι : ℝ) * K with hCdef
  have hCpos : 0 < C := by
    rw [hCdef]
    have h1 : 0 < C₀ * ((k : ℝ) + 1) := mul_pos hC₀pos (by positivity)
    have h2 : 0 ≤ (Fintype.card ι : ℝ) * K := mul_nonneg (Nat.cast_nonneg _) hKpos.le
    linarith
  refine ⟨C, hCpos, ?_⟩
  intro L v w γ T Y hk hkr hγ hY1 hlam hYT
  classical
  have hrk1 : 1 ≤ rk L := by omega
  have hT1 : 1 ≤ T := le_trans hY1 hYT
  have hYpos : 0 < Y := lt_of_lt_of_le one_pos hY1
  have hTpos : 0 < T := lt_of_lt_of_le one_pos hT1
  have hdet1 : 1 ≤ detL L := Lat.detL_ge_one L
  have hdetpos : 0 < detL L := lt_of_lt_of_le zero_lt_one hdet1
  have hrkcard : (rk L : ℝ) ≤ (Fintype.card ι : ℝ) := by exact_mod_cast rk_le_card L
  have hCnn : 0 ≤ C₀ := le_of_lt hC₀pos
  have hCVle : coneSliceVol L v w γ ≤ K := hKcone L v w γ
  have hCVnn : 0 ≤ coneSliceVol L v w γ := by
    rw [coneSliceVol, subVol]; exact ENNReal.toReal_nonneg
  set q : ℝ := coneSliceVol L v w γ / detL L with hq
  set G : ℝ → ℝ := fun t => (k : ℝ) / t ^ (k + 1) with hG
  set ee : ℝ → ℝ := fun t => coneCount L v w γ t - q * t ^ (rk L) with hee
  set Dv : ℝ := T ^ (rk L - k - 1) * Y / detL L with hDv
  have hqnn : 0 ≤ q := by
    rw [hq]
    exact div_nonneg hCVnn (le_of_lt hdetpos)
  have hGcont : ContinuousOn G (Set.Icc Y T) := by
    rw [hG]
    refine ContinuousOn.div continuousOn_const (continuousOn_pow _) ?_
    intro t ht
    exact pow_ne_zero _ (ne_of_gt (lt_of_lt_of_le hYpos ht.1))
  -- ============ (1) the uniform count estimate ============
  have hcnt : ∀ t : ℝ, 1 ≤ t → Y ≤ t → |ee t| ≤ C₀ * t ^ (rk L - 1) * Y / detL L := by
    intro t ht1 hYt
    have ht0 : t ≠ 0 := ne_of_gt (lt_of_lt_of_le one_pos ht1)
    have h := hC₀ L v w γ t Y hγ hrk1 ht1 hlam hYt
    have heq : coneCount L v w γ t - t ^ (rk L) / detL L * coneSliceVol L v w γ = ee t := by
      rw [hee, hq]; ring
    have hconv : C₀ * t ^ (rk L) / detL L * (Y / t) = C₀ * t ^ (rk L - 1) * Y / detL L := by
      have h1 : C₀ * t ^ (rk L) / detL L * (Y / t)
          = C₀ * (t ^ (rk L) / t) * (Y / detL L) := by ring
      have h2 : t ^ (rk L) / t = t ^ (rk L - 1) := by
        rw [div_eq_mul_inv]
        simpa using (pow_sub₀ t ht0 hrk1).symm
      rw [h1, h2]; ring
    have h' : |coneCount L v w γ t - t ^ (rk L) / detL L * coneSliceVol L v w γ|
        ≤ C₀ * t ^ (rk L) / detL L * (Y / t) := h
    rw [heq, hconv] at h'
    exact h'
  -- ============ (2) splitting the sum ============
  have hfinS : (smallSet L v w γ Y).Finite := finite_smallSet L v w γ Y
  have hfinL : (largeSet L v w γ Y T).Finite := finite_largeSet L v w γ Y T
  have hsplitS : (∑ᶠ a ∈ fullSet L v w γ T, 1 / eNorm a ^ k)
      = (∑ᶠ a ∈ smallSet L v w γ Y, 1 / eNorm a ^ k)
        + (∑ᶠ a ∈ largeSet L v w γ Y T, 1 / eNorm a ^ k) := by
    rw [fullSet_eq_union L v w γ Y T hYT,
      finsum_mem_union (disjoint_small_large L v w γ Y T) hfinS hfinL]
  -- ============ (3) layer cake for the large part ============
  have hYle : ∀ a ∈ hfinL.toFinset, Y ≤ eNorm a := by
    intro a ha
    exact le_of_lt (((Set.Finite.mem_toFinset hfinL).mp ha :
      a ∈ largeSet L v w γ Y T).2.2.1)
  have hTle : ∀ a ∈ hfinL.toFinset, eNorm a ≤ T := by
    intro a ha
    exact ((Set.Finite.mem_toFinset hfinL).mp ha : a ∈ largeSet L v w γ Y T).2.2.2.1
  have hpoint : ∀ a ∈ hfinL.toFinset, (1:ℝ) / eNorm a ^ k
      = 1 / T ^ k + ∫ t in (eNorm a)..T, G t := by
    intro a ha
    have ha' : a ∈ largeSet L v w γ Y T := (Set.Finite.mem_toFinset hfinL).mp ha
    have hpos : 0 < eNorm a := lt_of_lt_of_le hYpos (le_of_lt ha'.2.2.1)
    have hle : eNorm a ≤ T := ha'.2.2.2.1
    have h := BallConeK.integralDivPow k hpos hle
    rw [hG]
    linarith [h]
  have hlc : ∑ a ∈ hfinL.toFinset, ∫ t in (eNorm a)..T, G t
      = ∫ t in Y..T, G t * ((hfinL.toFinset.filter (fun a => eNorm a ≤ t)).card : ℝ) :=
    BallConeK.layerCake hfinL.toFinset (fun a => eNorm a) Y T G hYT hYle hTle hGcont
  have hcardN : ((hfinL.toFinset.card : ℕ) : ℝ) = coneCount L v w γ T - coneCount L v w γ Y := by
    have h := BallConeK.coneCountSub L v w γ T Y hYT (le_of_lt hYpos)
    have h' : coneCount L v w γ T - coneCount L v w γ Y
        = (((largeSet L v w γ Y T).ncard : ℕ) : ℝ) := h
    rw [Set.ncard_eq_toFinset_card _ hfinL] at h'
    exact h'.symm
  have hIntC : ∫ t in Y..T, G t * (((hfinL.toFinset.filter (fun a => eNorm a ≤ t)).card : ℕ) : ℝ)
      = ∫ t in Y..T, G t * (coneCount L v w γ t - coneCount L v w γ Y) := by
    refine intervalIntegral.integral_congr fun t ht => ?_
    rw [Set.uIcc_of_le hYT] at ht
    rw [BallConeK.largeFilterCard L v w γ Y T hfinL ht (le_of_lt hYpos)]
  have hlarge_eq : (∑ᶠ a ∈ largeSet L v w γ Y T, 1 / eNorm a ^ k)
      = (coneCount L v w γ T - coneCount L v w γ Y) / T ^ k
        + ∫ t in Y..T, G t * (coneCount L v w γ t - coneCount L v w γ Y) := by
    rw [finsum_mem_eq_finite_toFinset_sum _ hfinL]
    calc ∑ a ∈ hfinL.toFinset, (1:ℝ) / eNorm a ^ k
        = ∑ a ∈ hfinL.toFinset, (1 / T ^ k + ∫ t in (eNorm a)..T, G t) :=
            Finset.sum_congr rfl hpoint
      _ = (∑ a ∈ hfinL.toFinset, 1 / T ^ k)
            + ∑ a ∈ hfinL.toFinset, ∫ t in (eNorm a)..T, G t := Finset.sum_add_distrib
      _ = ((hfinL.toFinset.card : ℕ) : ℝ) * (1 / T ^ k)
            + ∫ t in Y..T, G t * (coneCount L v w γ t - coneCount L v w γ Y) := by
            rw [Finset.sum_const, nsmul_eq_mul, hlc, hIntC]
      _ = (coneCount L v w γ T - coneCount L v w γ Y) / T ^ k
            + ∫ t in Y..T, G t * (coneCount L v w γ t - coneCount L v w γ Y) := by
            rw [hcardN]; ring
  -- ============ (4) splitting the integral ============
  have hGcont' : ContinuousOn G (Set.uIcc Y T) := by rwa [Set.uIcc_of_le hYT]
  have hsub1 : ContinuousOn (fun t : ℝ => t ^ (rk L) - Y ^ (rk L)) (Set.Icc Y T) :=
    ((continuous_pow (rk L)).sub continuous_const).continuousOn
  have hi1 : IntervalIntegrable (fun t => q * (G t * (t ^ (rk L) - Y ^ (rk L)))) volume Y T :=
    ((hGcont.mul hsub1).intervalIntegrable_of_Icc hYT).const_mul q
  have hJ : IntervalIntegrable (fun t => G t * (coneCount L v w γ t - coneCount L v w γ Y))
      volume Y T := by
    have hmono : Monotone (fun t => coneCount L v w γ t - coneCount L v w γ Y) :=
      fun s t hst => sub_le_sub_right (coneCount_mono L v w γ hst) _
    have h := (hmono.intervalIntegrable (μ := volume) (a := Y) (b := T)).mul_continuousOn hGcont'
    refine (intervalIntegrable_congr ?_).mp h
    intro t ht
    exact mul_comm _ _
  have hK : IntervalIntegrable (fun t => G t * (q * (t ^ (rk L) - Y ^ (rk L)))) volume Y T :=
    (hGcont.mul (continuousOn_const.mul hsub1)).intervalIntegrable_of_Icc hYT
  have hi2 : IntervalIntegrable (fun t => G t * (ee t - ee Y)) volume Y T := by
    have hJK := hJ.sub hK
    refine (intervalIntegrable_congr ?_).mp hJK
    intro t ht
    rw [hee]; ring
  have hpt2 : ∀ t ∈ Set.uIcc Y T, G t * (coneCount L v w γ t - coneCount L v w γ Y)
      = q * (G t * (t ^ (rk L) - Y ^ (rk L))) + G t * (ee t - ee Y) := by
    intro t ht
    rw [hee]; ring
  have hint_eq : ∫ t in Y..T, G t * (coneCount L v w γ t - coneCount L v w γ Y)
      = q * (∫ t in Y..T, G t * (t ^ (rk L) - Y ^ (rk L)))
        + ∫ t in Y..T, G t * (ee t - ee Y) := by
    rw [intervalIntegral.integral_congr hpt2, intervalIntegral.integral_add hi1 hi2,
      intervalIntegral.integral_const_mul]
  -- ============ (5) the error integral ============
  have hcntIcc : ∀ t ∈ Set.Icc Y T, |ee t| ≤ C₀ * t ^ (rk L - 1) * Y / detL L :=
    fun t ht => hcnt t (le_trans hY1 ht.1) ht.1
  have herr : |∫ t in Y..T, G t * (ee t - ee Y)| ≤ (C₀ * ((k : ℝ) + 1)) * Dv := by
    have h := errIntegralBound k (rk L) hk hkr hYpos hYT hdetpos hCnn ee hcntIcc hi2
    rw [hDv]
    simpa only [hG] using h
  -- ============ (6) assembling the main term ============
  have hmodel : ∫ t in Y..T, G t * (t ^ (rk L) - Y ^ (rk L))
      = (k:ℝ) * (T ^ (rk L - k) - Y ^ (rk L - k)) / ((rk L - k : ℕ) : ℝ)
        - Y ^ (rk L) * (1 / Y ^ k - 1 / T ^ k) := by
    have h := integral_model (k := k) (r := rk L) hkr hYpos hYT
    simpa only [hG] using h
  have hmain : ((rk L : ℝ) / ((rk L : ℝ) - (k : ℝ))) * T ^ (rk L - k) / detL L
        * coneSliceVol L v w γ
      = q * (((rk L : ℝ) / ((rk L : ℝ) - (k : ℝ))) * (T ^ (rk L - k) - Y ^ (rk L - k)))
        + q * (((rk L : ℝ) / ((rk L : ℝ) - (k : ℝ))) * Y ^ (rk L - k)) := by
    rw [hq]; ring
  have hP : ((T ^ (rk L) - Y ^ (rk L)) / T ^ k)
      + (k:ℝ) * (T ^ (rk L - k) - Y ^ (rk L - k)) / ((rk L - k : ℕ) : ℝ)
      - Y ^ (rk L) * (1 / Y ^ k - 1 / T ^ k)
      = ((rk L : ℝ) / ((rk L : ℝ) - (k : ℝ))) * (T ^ (rk L - k) - Y ^ (rk L - k)) :=
    BallConeK.mainTermIdent (rk L) k hk hkr hYpos hTpos
  have hN : coneCount L v w γ T - coneCount L v w γ Y
      = q * (T ^ (rk L) - Y ^ (rk L)) + (ee T - ee Y) := by
    rw [hee]; ring
  have hkey : (coneCount L v w γ T - coneCount L v w γ Y) / T ^ k
        + (q * ((k:ℝ) * (T ^ (rk L - k) - Y ^ (rk L - k)) / ((rk L - k : ℕ) : ℝ)
            - Y ^ (rk L) * (1 / Y ^ k - 1 / T ^ k))
          + ∫ t in Y..T, G t * (ee t - ee Y))
      = q * (((rk L : ℝ) / ((rk L : ℝ) - (k : ℝ))) * (T ^ (rk L - k) - Y ^ (rk L - k)))
        + (ee T - ee Y) / T ^ k
        + ∫ t in Y..T, G t * (ee t - ee Y) := by
    rw [hN]
    linear_combination q * hP
  have hSlarge : (∑ᶠ a ∈ largeSet L v w γ Y T, 1 / eNorm a ^ k)
      = q * (((rk L : ℝ) / ((rk L : ℝ) - (k : ℝ))) * (T ^ (rk L - k) - Y ^ (rk L - k)))
        + (ee T - ee Y) / T ^ k
        + ∫ t in Y..T, G t * (ee t - ee Y) := by
    rw [hlarge_eq, hint_eq, hmodel, hkey]
  -- ============ (7) the term produced by the split at `Y` ============
  have hTpow : Y ^ (rk L - k) ≤ T ^ (rk L - k - 1) * Y := by
    calc Y ^ (rk L - k) = Y ^ (rk L - k - 1) * Y := by
          have h1 : Y ^ (rk L - k) = Y ^ ((rk L - k - 1) + 1) := by
            congr 1
            omega
          rw [h1, pow_succ]
      _ ≤ T ^ (rk L - k - 1) * Y :=
          mul_le_mul_of_nonneg_right
            (pow_le_pow_left₀ (le_of_lt hYpos) hYT (rk L - k - 1)) (le_of_lt hYpos)
  have hMYle : q * (((rk L : ℝ) / ((rk L : ℝ) - (k : ℝ))) * Y ^ (rk L - k))
      ≤ (Fintype.card ι : ℝ) * K * Dv := by
    have hkge : 1 ≤ (rk L : ℝ) - (k : ℝ) := by
      have h1 : k + 1 ≤ rk L := by omega
      have h2 : ((k + 1 : ℕ) : ℝ) ≤ (rk L : ℝ) := by exact_mod_cast h1
      push_cast at h2
      linarith
    have hden : (0:ℝ) < (rk L : ℝ) - (k : ℝ) := by linarith
    have hfac : (rk L : ℝ) / ((rk L : ℝ) - (k : ℝ)) ≤ (rk L : ℝ) := by
      have h1 : 1 / ((rk L : ℝ) - (k : ℝ)) ≤ 1 := by
        simpa using one_div_le_one_div_of_le (show (0:ℝ) < 1 by norm_num) hkge
      have h2 : (rk L : ℝ) * (1 / ((rk L : ℝ) - (k : ℝ))) ≤ (rk L : ℝ) * 1 :=
        mul_le_mul_of_nonneg_left h1 (Nat.cast_nonneg (rk L))
      have h3 : (rk L : ℝ) / ((rk L : ℝ) - (k : ℝ))
          = (rk L : ℝ) * (1 / ((rk L : ℝ) - (k : ℝ))) := by rw [mul_one_div]
      rw [h3]
      simpa using h2
    have h1 : q * Y ^ (rk L - k) ≤ K * Dv := by
      rw [hq, hDv]
      have hYknn : 0 ≤ Y ^ (rk L - k) := pow_nonneg (le_of_lt hYpos) _
      calc coneSliceVol L v w γ / detL L * Y ^ (rk L - k)
          ≤ K / detL L * (T ^ (rk L - k - 1) * Y) := by
            refine mul_le_mul (div_le_div_of_nonneg_right hCVle (le_of_lt hdetpos)) hTpow
              hYknn ?_
            positivity
        _ = K * (T ^ (rk L - k - 1) * Y / detL L) := by ring
    have h2 : q * (((rk L : ℝ) / ((rk L : ℝ) - (k : ℝ))) * Y ^ (rk L - k))
        = ((rk L : ℝ) / ((rk L : ℝ) - (k : ℝ))) * (q * Y ^ (rk L - k)) := by ring
    rw [h2]
    calc ((rk L : ℝ) / ((rk L : ℝ) - (k : ℝ))) * (q * Y ^ (rk L - k))
        ≤ (rk L : ℝ) * (K * Dv) := by
          refine mul_le_mul hfac h1 ?_ (Nat.cast_nonneg _)
          rw [hq]; positivity
      _ ≤ (Fintype.card ι : ℝ) * (K * Dv) :=
          mul_le_mul_of_nonneg_right hrkcard (by positivity)
      _ = (Fintype.card ι : ℝ) * K * Dv := by ring
  have hquot : |(ee T - ee Y) / T ^ k| ≤ 2 * C₀ * Dv := by
    have hTk1 : (1:ℝ) ≤ T ^ k := one_le_pow₀ hT1
    have hTkpos : (0:ℝ) < T ^ k := lt_of_lt_of_le zero_lt_one hTk1
    have h1 : |ee T - ee Y| ≤ C₀ * T ^ (rk L - 1) * Y / detL L
        + C₀ * Y ^ (rk L - 1) * Y / detL L := by
      have h2 := hcnt T hT1 hYT
      have h3 := hcnt Y hY1 le_rfl
      have h4 : |ee T - ee Y| ≤ |ee T| + |ee Y| := by simpa using abs_sub_le (ee T) 0 (ee Y)
      linarith
    rw [abs_div, abs_of_pos hTkpos]
    have hdiv : |ee T - ee Y| / T ^ k
        ≤ (C₀ * T ^ (rk L - 1) * Y / detL L + C₀ * Y ^ (rk L - 1) * Y / detL L) / T ^ k :=
      div_le_div_of_nonneg_right h1 (le_of_lt hTkpos)
    refine hdiv.trans ?_
    have hYp : Y ^ (rk L - 1) * Y = Y ^ (rk L) := by
      rw [← pow_succ, Nat.sub_add_cancel hrk1]
    have hsplit2 : (C₀ * T ^ (rk L - 1) * Y / detL L + C₀ * Y ^ (rk L - 1) * Y / detL L) / T ^ k
        = C₀ * T ^ (rk L - 1) * Y / (detL L * T ^ k)
          + C₀ * Y ^ (rk L) / (detL L * T ^ k) := by
      rw [← hYp]; ring
    rw [hsplit2]
    have hTp : T ^ (rk L - 1) / T ^ k = T ^ (rk L - k - 1) := by
      rw [div_eq_mul_inv]
      have h7 : rk L - k - 1 = rk L - 1 - k := by omega
      rw [h7]
      simpa using (pow_sub₀ T (ne_of_gt hTpos) (show k ≤ rk L - 1 by omega)).symm
    have hterm1 : C₀ * T ^ (rk L - 1) * Y / (detL L * T ^ k)
        = C₀ * (T ^ (rk L - 1) / T ^ k) * Y / detL L := by ring
    have hYZ : Y ^ (rk L) ≤ T ^ (rk L - 1) * Y := by
      have h1 : Y ^ (rk L) = Y ^ (rk L - 1) * Y := by
        rw [← pow_succ, Nat.sub_add_cancel hrk1]
      rw [h1]
      exact mul_le_mul_of_nonneg_right
        (pow_le_pow_left₀ (le_of_lt hYpos) hYT (rk L - 1)) (le_of_lt hYpos)
    have h6 : C₀ * Y ^ (rk L) / (detL L * T ^ k) ≤ C₀ * Dv := by
      have h7 : Y ^ (rk L) / T ^ k ≤ T ^ (rk L - k - 1) * Y := by
        rw [div_le_iff₀ (pow_pos hTpos k)]
        have h8 : (T ^ (rk L - k - 1) * Y) * T ^ k = T ^ (rk L - 1) * Y := by
          have hp : rk L - k - 1 + k = rk L - 1 := by omega
          rw [mul_assoc, mul_comm Y (T ^ k), ← mul_assoc, ← pow_add, hp]
        rw [h8]
        exact hYZ
      have h9 : C₀ * (Y ^ (rk L) / T ^ k) / detL L ≤ C₀ * (T ^ (rk L - k - 1) * Y) / detL L :=
        div_le_div_of_nonneg_right (mul_le_mul_of_nonneg_left h7 hCnn) (le_of_lt hdetpos)
      have e1 : C₀ * Y ^ (rk L) / (detL L * T ^ k) = C₀ * (Y ^ (rk L) / T ^ k) / detL L := by ring
      have e2 : C₀ * (T ^ (rk L - k - 1) * Y) / detL L = C₀ * Dv := by rw [hDv]; ring
      rw [e1]
      exact h9.trans (le_of_eq e2)
    have hA : C₀ * T ^ (rk L - 1) * Y / (detL L * T ^ k) ≤ C₀ * Dv := by
      have e : C₀ * T ^ (rk L - 1) * Y / (detL L * T ^ k) = C₀ * Dv := by
        rw [hterm1, hTp, hDv]; ring
      rw [e]
    have hsum : C₀ * T ^ (rk L - 1) * Y / (detL L * T ^ k) + C₀ * Y ^ (rk L) / (detL L * T ^ k)
        ≤ C₀ * Dv + C₀ * Dv := add_le_add hA h6
    linarith
  -- ============ (8) final assembly ============
  have hSmain : (∑ᶠ a ∈ fullSet L v w γ T, 1 / eNorm a ^ k)
      - ((rk L : ℝ) / ((rk L : ℝ) - (k : ℝ))) * T ^ (rk L - k) / detL L * coneSliceVol L v w γ
      = (∑ᶠ a ∈ smallSet L v w γ Y, 1 / eNorm a ^ k)
        + (ee T - ee Y) / T ^ k
        + (∫ t in Y..T, G t * (ee t - ee Y))
        - q * (((rk L : ℝ) / ((rk L : ℝ) - (k : ℝ))) * Y ^ (rk L - k)) := by
    rw [hsplitS, hSlarge, hmain]
    ring
  have hSnn : 0 ≤ ∑ᶠ a ∈ smallSet L v w γ Y, 1 / eNorm a ^ k := by
    rw [finsum_mem_eq_finite_toFinset_sum _ hfinS]
    exact Finset.sum_nonneg fun a _ => div_nonneg zero_le_one (pow_nonneg (eNorm_nonneg a) k)
  have hQnn : 0 ≤ q * (((rk L : ℝ) / ((rk L : ℝ) - (k : ℝ))) * Y ^ (rk L - k)) := by
    refine mul_nonneg hqnn (mul_nonneg ?_ (pow_nonneg (le_of_lt hYpos) _))
    exact div_nonneg (Nat.cast_nonneg _) (le_of_lt (by
      have hklt : (k : ℝ) < (rk L : ℝ) := by exact_mod_cast (by omega : k < rk L)
      linarith))
  show |(∑ᶠ a ∈ fullSet L v w γ T, 1 / eNorm a ^ k) -
        ((rk L : ℝ) / ((rk L : ℝ) - (k : ℝ))) * T ^ (rk L - k) / detL L *
          coneSliceVol L v w γ|
      ≤ C * T ^ (rk L - k - 1) * Y / detL L
        + ∑ᶠ a ∈ smallSet L v w γ Y, 1 / eNorm a ^ k
  calc |(∑ᶠ a ∈ fullSet L v w γ T, 1 / eNorm a ^ k) -
        ((rk L : ℝ) / ((rk L : ℝ) - (k : ℝ))) * T ^ (rk L - k) / detL L * coneSliceVol L v w γ|
      ≤ (∑ᶠ a ∈ smallSet L v w γ Y, 1 / eNorm a ^ k)
        + (2 * C₀ + C₀ * ((k : ℝ) + 1) + (Fintype.card ι : ℝ) * K) * Dv := by
        rw [hSmain]
        have htri := abs_add_add_sub_le (∑ᶠ a ∈ smallSet L v w γ Y, 1 / eNorm a ^ k)
          ((ee T - ee Y) / T ^ k) (∫ t in Y..T, G t * (ee t - ee Y))
          (q * (((rk L : ℝ) / ((rk L : ℝ) - (k : ℝ))) * Y ^ (rk L - k)))
        rw [abs_of_nonneg hSnn, abs_of_nonneg hQnn] at htri
        linarith [htri, hquot, herr, hMYle]
    _ = C * T ^ (rk L - k - 1) * Y / detL L
        + ∑ᶠ a ∈ smallSet L v w γ Y, 1 / eNorm a ^ k := by
        rw [hCdef, hDv]; ring

end Work.HP.MM2
