import Mathlib
import Submission.Work.KMTPlan.A6.MdlFZeroTwoLe
import Submission.Work.KMTPlan.A6.LowpassVarOnCore
import Submission.Work.KMTPlan.A6.iwQl_mul_le_splitCut
import Submission.Work.KMTPlan.A6.lowpassSmallHeightCore
import Submission.Work.KMTPlan.A6.MdlLpH.exists_logN_floor_a_ge
import Submission.Work.KMTPlan.A6.MdlLpH.kmtProj_two_le_of_le
import Submission.Work.KMTPlan.A6.MdlLpH.mdlCore_bad_l_bound
import Submission.Work.KMTPlan.A6.MdlLpH.mdlF_uniform_two_le
import Submission.Work.KMTPlan.A6.MdlLpH.variationalNorm_comp_mono_range_le
import Submission.Work.KMTAreas.A7LoLin.lowpass0
import Submission.Port.Aesm

set_option maxHeartbeats 4000000

namespace Work.KMTPlan.A6

open MeasureTheory
open scoped ENNReal NNReal BigOperators
open PointwiseErgodicTheorems

/-! ## Elementary helpers for the low-pass case at positive height -/

/-- A `Λ`-lacunary sequence with `Λ > 1` and `a n ≥ 1` is monotone. -/
private theorem mdlLowHigh_lac_monotone {Λ : NNReal} (hΛ : 1 < Λ) {a : ℕ → NNReal}
    (ha : PointwiseErgodicTheorems.Lacunary Λ a) (ha1 : ∀ n, 1 ≤ a n) : Monotone a := by
  refine monotone_nat_of_le_succ (fun n => ?_)
  have hpos : (0 : NNReal) < a n := lt_of_lt_of_le zero_lt_one (ha1 n)
  have h2 : Λ < a (n + 1) / a n := ha n
  have h1 : Λ * a n < a (n + 1) := by rwa [lt_div_iff₀ hpos] at h2
  have h3 : a n ≤ Λ * a n := by
    simpa using mul_le_mul_of_nonneg_right (le_of_lt hΛ) (le_of_lt hpos)
  exact le_trans h3 h1.le

/-- `n ↦ logN ⌊a n⌋` is monotone for a `Λ`-lacunary sequence with `Λ > 1` and `a n ≥ 1`. -/
private theorem mdlLowHigh_logN_floor_mono {Λ : NNReal} (hΛ : 1 < Λ) {a : ℕ → NNReal}
    (ha : PointwiseErgodicTheorems.Lacunary Λ a) (ha1 : ∀ n, 1 ≤ a n) :
    Monotone (fun n : ℕ => Work.Analysis.EndVar.logN (Nat.floor (a n))) :=
  fun n m hnm =>
    Work.Analysis.EndVar.logN_mono (Nat.floor_mono (mdlLowHigh_lac_monotone hΛ ha ha1 hnm))

/-- `(1 + l₁)²` is dominated by the loss weight. -/
private theorem mdlLowHigh_one_add_sq_le_lossWeight {ρ : ℝ} (hρ : 0 ≤ ρ) (l₁ l₂ k₂ : ℕ) :
    (1 + (l₁ : ℝ)) ^ 2 ≤ Work.KMTAreas.A7.lossWeight 2 ρ l₁ l₂ 0 k₂ := by
  have hlmax : (l₁ : ℝ) ≤ Work.KMTAreas.A7.lmaxR l₁ l₂ 0 k₂ := by
    rw [Work.KMTAreas.A7.lmaxR, Work.Analysis.EndVar.lmax]
    have h : (l₁ : ℤ) ≤ max (max (l₁ : ℤ) (l₂ : ℤ)) (max (0 : ℤ) (k₂ : ℤ)) :=
      le_trans (le_max_left _ _) (le_max_left _ _)
    exact_mod_cast h
  have hlmax0 : (0 : ℝ) ≤ Work.KMTAreas.A7.lmaxR l₁ l₂ 0 k₂ :=
    le_trans (Nat.cast_nonneg l₁) hlmax
  rw [Work.KMTAreas.A7.lossWeight]
  have hexp0 : (0 : ℝ) ≤ 2 * ρ * Work.KMTAreas.A7.lmaxR l₁ l₂ 0 k₂ :=
    mul_nonneg (mul_nonneg (by norm_num) hρ) hlmax0
  have hbase : (1 + (l₁ : ℝ)) ^ (2 : ℝ)
      ≤ (1 + Work.KMTAreas.A7.lmaxR l₁ l₂ 0 k₂) ^ (2 : ℝ) := by
    rw [Real.rpow_two, Real.rpow_two]
    have h1 : (1 + (l₁ : ℝ)) ≤ 1 + Work.KMTAreas.A7.lmaxR l₁ l₂ 0 k₂ := by linarith
    have h0 : (0 : ℝ) ≤ 1 + (l₁ : ℝ) := by linarith [Nat.cast_nonneg (α := ℝ) l₁]
    nlinarith
  have hb0 : (0 : ℝ) ≤ (1 + Work.KMTAreas.A7.lmaxR l₁ l₂ 0 k₂) ^ (2 : ℝ) := by
    rw [Real.rpow_two]
    exact sq_nonneg _
  have hone : (1 : ℝ) ≤ (2 : ℝ) ^ (2 * ρ * Work.KMTAreas.A7.lmaxR l₁ l₂ 0 k₂) :=
    Real.one_le_rpow (by norm_num) hexp0
  calc (1 + (l₁ : ℝ)) ^ 2 = (1 + (l₁ : ℝ)) ^ (2 : ℝ) * 1 := by rw [mul_one, Real.rpow_two]
    _ ≤ (1 + Work.KMTAreas.A7.lmaxR l₁ l₂ 0 k₂) ^ (2 : ℝ)
          * (2 : ℝ) ^ (2 * ρ * Work.KMTAreas.A7.lmaxR l₁ l₂ 0 k₂) :=
        mul_le_mul hbase hone (by norm_num) hb0

/-- `mdlCore` is upward closed in the scale index. -/
private theorem mdlLowHigh_mdlCore_of_le {ρ : ℝ} {C₀ : ℕ} {a : ℕ → NNReal} {l₁ l₂ k₁ k₂ m n : ℕ}
    (hfloor : Monotone fun n => Nat.floor (a n)) (hnm : n ≤ m)
    (hm : mdlCore ρ C₀ a l₁ l₂ k₁ k₂ n) : mdlCore ρ C₀ a l₁ l₂ k₁ k₂ m := by
  obtain ⟨hin, hcut, hmain⟩ := hm
  have hN : Nat.floor (a n) ≤ Nat.floor (a m) := hfloor hnm
  have hhs : Work.Analysis.EndVar.heightScale C₀ (Nat.floor (a n))
      ≤ Work.Analysis.EndVar.heightScale C₀ (Nat.floor (a m)) := by
    unfold Work.Analysis.EndVar.heightScale
    exact Nat.mul_le_mul_left C₀ (Work.Analysis.EndVar.logLogN_mono hN)
  have hlog : Work.Analysis.EndVar.logN (Nat.floor (a n))
      ≤ Work.Analysis.EndVar.logN (Nat.floor (a m)) := Work.Analysis.EndVar.logN_mono hN
  have hhsZ : ((Work.Analysis.EndVar.heightScale C₀ (Nat.floor (a n)) : ℕ) : ℤ)
      ≤ ((Work.Analysis.EndVar.heightScale C₀ (Nat.floor (a m)) : ℕ) : ℤ) := by
    exact_mod_cast hhs
  refine ⟨⟨le_trans hin.1 hhsZ, le_trans hin.2.1 hhsZ, le_trans hin.2.2 hhsZ⟩,
    lt_of_lt_of_le hcut hN, ?_⟩
  have htoNat : (Work.Analysis.EndVar.logN (Nat.floor (a n))).toNat
      ≤ (Work.Analysis.EndVar.logN (Nat.floor (a m))).toNat := Int.toNat_le_toNat hlog
  unfold Work.KMTAreas.A7.mainRegime at hmain ⊢
  constructor <;> omega

/-- `ofReal a * X ≤ ofReal K * ofReal L * X` when `a ≤ K * L`. -/
private theorem mdlLowHigh_ofReal_le_mul_ofReal {a K L : ℝ} (hK : 0 ≤ K) (h : a ≤ K * L)
    (X : ENNReal) :
    ENNReal.ofReal a * X ≤ ENNReal.ofReal K * ENNReal.ofReal L * X := by
  refine mul_le_mul' ?_ le_rfl
  calc ENNReal.ofReal a ≤ ENNReal.ofReal (K * L) := ENNReal.ofReal_le_ofReal h
    _ = ENNReal.ofReal K * ENNReal.ofReal L := ENNReal.ofReal_mul hK

/-- `3 * (ofReal c * (ofReal C * X)) = ofReal (3 c C) * X`. -/
private theorem mdlLowHigh_three_mul_ofReal (c C : ℝ) (hc : 0 ≤ c) (X : ENNReal) :
    3 * (ENNReal.ofReal c * (ENNReal.ofReal C * X))
      = ENNReal.ofReal (3 * c * C) * X := by
  rw [show (3 : ENNReal) = ENNReal.ofReal 3 from (ENNReal.ofReal_ofNat 3).symm]
  rw [← mul_assoc, ← ENNReal.ofReal_mul (by norm_num : (0 : ℝ) ≤ 3), ← mul_assoc,
    ← ENNReal.ofReal_mul (by positivity : (0 : ℝ) ≤ 3 * c)]

/-- `∑_{m<Y} 4 * (ofReal a * X) = ofReal (4 Y a) * X`. -/
private theorem mdlLowHigh_sum_ofReal (Y : ℕ) (a : ℝ) (X : ENNReal) :
    ∑ _m ∈ Finset.range Y, 4 * (ENNReal.ofReal a * X)
      = ENNReal.ofReal (4 * (Y : ℝ) * a) * X := by
  rw [show (fun _m : ℕ => 4 * (ENNReal.ofReal a * X))
      = fun _m : ℕ => (4 * ENNReal.ofReal a) * X from by funext m; ring]
  rw [Finset.sum_const, Finset.card_range, nsmul_eq_mul]
  rw [show (4 : ENNReal) = ENNReal.ofReal 4 from (ENNReal.ofReal_ofNat 4).symm]
  rw [show ((Y : ℕ) : ENNReal) = ENNReal.ofReal (Y : ℝ) from (ENNReal.ofReal_natCast Y).symm]
  rw [← ENNReal.ofReal_mul (by norm_num : (0 : ℝ) ≤ 4), ← mul_assoc,
    ← ENNReal.ofReal_mul (by positivity : (0 : ℝ) ≤ (Y : ℝ))]
  rw [show ((Y : ℝ) * (4 * a)) = 4 * (Y : ℝ) * a by ring]

/-- `ofReal a * (ofReal C * X) + 3 * (ofReal b * (ofReal C * X)) = ofReal (a C + 3 b C) * X`. -/
private theorem mdlLowHigh_ofReal_add_mul (a b C : ℝ) (ha : 0 ≤ a) (hb : 0 ≤ b) (hC : 0 ≤ C)
    (X : ENNReal) :
    ENNReal.ofReal a * (ENNReal.ofReal C * X) + 3 * (ENNReal.ofReal b * (ENNReal.ofReal C * X))
      = ENNReal.ofReal (a * C + 3 * b * C) * X := by
  rw [show ENNReal.ofReal a * (ENNReal.ofReal C * X) = ENNReal.ofReal (a * C) * X from by
    rw [← mul_assoc, ← ENNReal.ofReal_mul ha]]
  rw [show 3 * (ENNReal.ofReal b * (ENNReal.ofReal C * X))
      = ENNReal.ofReal (3 * b * C) * X from by
    rw [show (3 : ENNReal) = ENNReal.ofReal 3 from (ENNReal.ofReal_ofNat 3).symm]
    rw [← mul_assoc, ← ENNReal.ofReal_mul (by norm_num : (0 : ℝ) ≤ 3), ← mul_assoc,
      ← ENNReal.ofReal_mul (by positivity : (0 : ℝ) ≤ 3 * b)]]
  rw [← add_mul, ← ENNReal.ofReal_add (by positivity : (0 : ℝ) ≤ a * C)
    (by positivity : (0 : ℝ) ≤ 3 * b * C)]
/-! ## The main theorem -/

/-- **The A6 low-pass case `mdlLowpassCaseHigh`, with the `l₁`-free crux replaced by the
*decimation* route on the core scales and by the `#A`-sieve route for bounded heights.**

This is the proof of `Work.KMTPlan.A6.mdlLowpassCaseHigh_of_crux`, with its `hcrux` hypothesis
(the `l₁`-free low-pass variational estimate, i.e. the workspace's crux
`Work.KMTAreas.A7Hi.LowpassChainLe` / `A7HiRep.chainPartSqFunLeTwo`) replaced by a spec that is
*supplied* from two placed inputs:

* `Work.KMTPlan.A6.lowpassVarOnCore` (PROVED): the low-pass variational estimate for the shifted
  lacunary walk, **provided the base scale is large** (`24 · iwQl ρ l₁ ≤ ⌊a m⌋`), which on the A6
  core scales is a consequence of `mdlCore` (`N > splitCut ρ L`) and of the arithmetic
  `Work.KMTPlan.A6.iwQl_mul_le_splitCut`;
* `Work.KMTPlan.A6.lowpassSmallHeightCore` (PROVED): the same bound for **bounded height**
  `l₁ ≤ L₁(ρ)`, from the `#A`-sieve values-maximal bound and the `#A`-cardinality chain bound.

Both applications of the spec inside the proof happen at a *core* base index (`m₀`, resp. `m₁`),
so the disjunction `24 · iwQl ρ l₁ ≤ ⌊a m⌋ ∨ l₁ ≤ L₁(ρ)` is available there. -/
theorem mdlLowpassCaseHigh_of_decim (C₀ : ℕ) (hC₀ : 1 ≤ C₀) (R : NNReal) (hR : 2 < R) :
    ∃ ρ₀ : ℝ, 0 < ρ₀ ∧ ∀ ρ : ℝ, 0 < ρ → ρ ≤ ρ₀ → ∃ K : NNReal → NNReal,
      ∀ (a : ℕ → NNReal) (Λ : NNReal) (l₁ l₂ k₂ : ℕ) (f : ℤ → ℂ),
        1 < Λ → PointwiseErgodicTheorems.Lacunary Λ a → (∀ n, 1 ≤ a n) → 1 ≤ l₁ →
        MeasureTheory.eLpNorm (fun x : ℤ => PointwiseErgodicTheorems.variationalNorm R
          (fun n : ℕ =>
            if Work.KMTPlan.A6.mdlCore ρ C₀ a l₁ l₂ 0 k₂ n then
              Work.KMTAreas.A7.Tle ρ l₁ (Work.KMTAreas.A7.varphiN (Nat.floor (a n)) 0)
                (Work.KMTPlan.A6.mdlF ρ (Work.KMTAreas.A7.uScale ρ
                  (max (max l₁ l₂) (max 0 k₂))) l₁ f) x
            else 0)) 2 MeasureTheory.Measure.count
          ≤ (K Λ : ENNReal) *
              ENNReal.ofReal (Work.KMTAreas.A7.lossWeight 2 ρ l₁ l₂ 0 k₂) *
              MeasureTheory.eLpNorm f 2 MeasureTheory.Measure.count := by
  classical
  refine ⟨min 1 (1 / (2 * (C₀ : ℝ))), lt_min one_pos (by positivity), ?_⟩
  intro ρ hρ hρle
  have hρ1 : ρ ≤ 1 := le_trans hρle (min_le_left _ _)
  -- the arithmetic threshold of the decimation route
  obtain ⟨L₁p, harith⟩ := iwQl_mul_le_splitCut ρ hρ hρ1
  have hρC : ρ * (C₀ : ℝ) ≤ 1 / 2 := by
    have hC0 : (0 : ℝ) < (C₀ : ℝ) := by exact_mod_cast (lt_of_lt_of_le zero_lt_one hC₀)
    have hle : ρ ≤ 1 / (2 * (C₀ : ℝ)) := le_trans hρle (min_le_right _ _)
    rw [le_div_iff₀ (by positivity)] at hle
    nlinarith [hle]
  obtain ⟨Csta, hCstapos, hCsta⟩ := MdlLpH.mdlF_uniform_two_le ρ hρ hρ1
  have hexK : ∀ Λ : NNReal, ∃ K : NNReal,
      ∀ (a : ℕ → NNReal) (l₁ l₂ k₂ : ℕ) (f : ℤ → ℂ),
        1 < Λ → PointwiseErgodicTheorems.Lacunary Λ a → (∀ n, 1 ≤ a n) → 1 ≤ l₁ →
        MeasureTheory.eLpNorm (fun x : ℤ => PointwiseErgodicTheorems.variationalNorm R
          (fun n : ℕ =>
            if Work.KMTPlan.A6.mdlCore ρ C₀ a l₁ l₂ 0 k₂ n then
              Work.KMTAreas.A7.Tle ρ l₁ (Work.KMTAreas.A7.varphiN (Nat.floor (a n)) 0)
                (Work.KMTPlan.A6.mdlF ρ (Work.KMTAreas.A7.uScale ρ
                  (max (max l₁ l₂) (max 0 k₂))) l₁ f) x
            else 0)) 2 MeasureTheory.Measure.count
          ≤ (K : ENNReal) *
              ENNReal.ofReal (Work.KMTAreas.A7.lossWeight 2 ρ l₁ l₂ 0 k₂) *
              MeasureTheory.eLpNorm f 2 MeasureTheory.Measure.count := by
    intro Λ
    by_cases hΛ : 1 < Λ
    · -- ## the spec of the shifted-family bound: decimation on the core, sieve for bounded height
      obtain ⟨Cρ₁, hCρ₁pos, C₁, hC₁pos, hspec₁⟩ := lowpassVarOnCore ρ hρ hρ1 R hR Λ hΛ
      obtain ⟨Cρ₂, hCρ₂pos, K₂, hK₂pos, hspec₂⟩ :=
        lowpassSmallHeightCore ρ hρ hρ1 R hR Λ hΛ L₁p
      set Cρ : ℝ := max Cρ₁ Cρ₂ with hCρdef
      set C : ℝ := max C₁ K₂ with hCdef
      have hCρpos : 0 < Cρ := by rw [hCρdef]; exact lt_max_of_lt_left hCρ₁pos
      have hCpos : 0 < C := by rw [hCdef]; exact lt_max_of_lt_left hC₁pos
      have hspec : ∀ (m l₁ : ℕ) (a : ℕ → NNReal),
          PointwiseErgodicTheorems.Lacunary Λ a → (∀ n : ℕ, 1 ≤ a n) → ∀ g : ℤ → ℂ,
          Work.Analysis.IonescuWainger.GoodMajorArcs ρ Cρ l₁
            (-(Work.Analysis.EndVar.logN (Nat.floor (a m)))) →
          (24 * Work.Analysis.IonescuWainger.iwQl ρ l₁ ≤ Nat.floor (a m) ∨ l₁ ≤ L₁p) →
          MeasureTheory.eLpNorm (fun x : ℤ => PointwiseErgodicTheorems.variationalNorm R
            (fun n : ℕ => Work.KMTAreas.A7.Tle ρ l₁
              (Work.KMTAreas.A7.varphiN (Nat.floor (a (n + m))) 0) g x))
            2 MeasureTheory.Measure.count
          ≤ ENNReal.ofReal (C * (1 + (l₁ : ℝ)) ^ 2) *
              MeasureTheory.eLpNorm g 2 MeasureTheory.Measure.count := by
        intro m l₁ a ha ha1 g hGMA hdisj
        have hsq1 : (1 : ℝ) ≤ (1 + (l₁ : ℝ)) ^ 2 := by
          nlinarith [Nat.cast_nonneg (α := ℝ) l₁]
        rcases hdisj with hbig | hsl
        · -- decimation branch: the base scale is large
          have hgood₁ : Work.Analysis.IonescuWainger.GoodMajorArcs ρ Cρ₁ l₁
              (-(Work.Analysis.EndVar.logN (Nat.floor (a m)))) :=
            Work.KMTAreas.A7Hi.goodMajorArcs_mono
              (by rw [hCρdef]; exact le_max_left _ _) hGMA
          have hC₁le : C₁ * (1 + (l₁ : ℝ)) ^ 2 ≤ C * (1 + (l₁ : ℝ)) ^ 2 := by
            have hle : C₁ ≤ C := by rw [hCdef]; exact le_max_left _ _
            exact mul_le_mul_of_nonneg_right hle (by positivity)
          exact (hspec₁ m l₁ a ha ha1 g hgood₁ hbig).trans
            (mul_le_mul' (ENNReal.ofReal_le_ofReal hC₁le) le_rfl)
        · -- small-height branch: the `#A`-sieve bounds
          by_cases hgtop : MeasureTheory.eLpNorm g 2 MeasureTheory.Measure.count = ⊤
          · rw [hgtop, ENNReal.mul_top (ENNReal.ofReal_ne_zero_iff.mpr (by positivity :
              (0 : ℝ) < C * (1 + (l₁ : ℝ)) ^ 2))]
            exact le_top
          · have hgood₂ : Work.Analysis.IonescuWainger.GoodMajorArcs ρ Cρ₂ l₁
                (-(Work.Analysis.EndVar.logN (Nat.floor (a m)))) :=
              Work.KMTAreas.A7Hi.goodMajorArcs_mono
                (by rw [hCρdef]; exact le_max_right _ _) hGMA
            have hmem : MeasureTheory.MemLp g 2 MeasureTheory.Measure.count :=
              MeasureTheory.memLp_iff.mpr (lt_top_iff_ne_top.mpr hgtop)
            have hK₂le : K₂ ≤ C * (1 + (l₁ : ℝ)) ^ 2 := by
              have hle : K₂ ≤ C := by rw [hCdef]; exact le_max_right _ _
              nlinarith [hCpos.le, hsq1]
            exact (hspec₂ m l₁ a g hsl ha ha1 hmem hgood₂).trans
              (mul_le_mul' (ENNReal.ofReal_le_ofReal hK₂le) le_rfl)
      set L₁ : ℕ := Nat.ceil (2 * (C₀ : ℝ) * Real.logb 2 (Cρ + 2)) with hL₁
      set Y : ℕ := Nat.ceil (Cρ * (2 : ℝ) ^ (ρ * (L₁ : ℝ))) + 2 with hY
      obtain ⟨B, hBpos, hBspec⟩ := MdlLpH.kmtProj_two_le_of_le ρ hρ hρ1 L₁
      have hB0 : (0 : ℝ) ≤ B := hBpos.le
      have hY0 : (0 : ℝ) ≤ (Y : ℝ) := Nat.cast_nonneg Y
      have hKpos : (0 : ℝ) < 4 * (Y : ℝ) * B * Csta + 3 * C * Csta + 1 := by
        have h1 : (0 : ℝ) ≤ 4 * (Y : ℝ) * B * Csta :=
          mul_nonneg (mul_nonneg (mul_nonneg (by norm_num) hY0) hB0) hCstapos.le
        have h2 : (0 : ℝ) ≤ 3 * C * Csta :=
          mul_nonneg (mul_nonneg (by norm_num) hCpos.le) hCstapos.le
        linarith
      set Kc : NNReal := ⟨4 * (Y : ℝ) * B * Csta + 3 * C * Csta + 1, hKpos.le⟩ with hKc
      have hKcR : (Kc : ℝ) = 4 * (Y : ℝ) * B * Csta + 3 * C * Csta + 1 := rfl
      refine ⟨Kc, ?_⟩
      intro a l₁ l₂ k₂ f hΛ' ha ha1 hl₁
      have hR1 : (1 : NNReal) ≤ R := le_trans (by norm_num : (1 : NNReal) ≤ 2) hR.le
      have hmono := mdlLowHigh_logN_floor_mono hΛ' ha ha1
      have hfl : Monotone fun n : ℕ => Nat.floor (a n) :=
        fun _ _ hnm => Nat.floor_mono (mdlLowHigh_lac_monotone hΛ' ha ha1 hnm)
      set g : ℤ → ℂ := mdlF ρ (Work.KMTAreas.A7.uScale ρ (max (max l₁ l₂) (max 0 k₂))) l₁ f
        with hg
      have hgle : MeasureTheory.eLpNorm g 2 MeasureTheory.Measure.count
          ≤ ENNReal.ofReal Csta * MeasureTheory.eLpNorm f 2 MeasureTheory.Measure.count := by
        rw [hg]
        exact hCsta l₁ (max (max l₁ l₂) (max 0 k₂))
          (le_trans (le_max_left l₁ l₂) (le_max_left (max l₁ l₂) (max 0 k₂))) f
      have hL1 : (1 : ℝ) ≤ Work.KMTAreas.A7.lossWeight 2 ρ l₁ l₂ 0 k₂ :=
        le_trans (by nlinarith [Nat.cast_nonneg (α := ℝ) l₁])
          (mdlLowHigh_one_add_sq_le_lossWeight hρ.le l₁ l₂ k₂)
      have hLpos : (0 : ℝ) < Work.KMTAreas.A7.lossWeight 2 ρ l₁ l₂ 0 k₂ :=
        lt_of_lt_of_le one_pos hL1
      -- on the core scales the base is large (arithmetic), and for bounded height the sieve
      -- branch of the spec applies: the disjunction consumed by `hspec`
      have harithCore : ∀ m : ℕ, mdlCore ρ C₀ a l₁ l₂ 0 k₂ m →
          L₁p ≤ max (max l₁ l₂) (max 0 k₂) →
          24 * Work.Analysis.IonescuWainger.iwQl ρ l₁ ≤ Nat.floor (a m) := by
        intro m hm hL
        have hl₁L : l₁ ≤ max (max l₁ l₂) (max 0 k₂) :=
          le_trans (le_max_left l₁ l₂) (le_max_left (max l₁ l₂) (max 0 k₂))
        have h1 := harith (max (max l₁ l₂) (max 0 k₂)) l₁ hL hl₁L
        have h2 := hm.2.1
        omega
      have hdisjAt : ∀ m : ℕ, mdlCore ρ C₀ a l₁ l₂ 0 k₂ m →
          24 * Work.Analysis.IonescuWainger.iwQl ρ l₁ ≤ Nat.floor (a m) ∨ l₁ ≤ L₁p := by
        intro m hm
        by_cases hL : L₁p ≤ max (max l₁ l₂) (max 0 k₂)
        · exact Or.inl (harithCore m hm hL)
        · exact Or.inr (by
            have h1 : l₁ ≤ max (max l₁ l₂) (max 0 k₂) :=
              le_trans (le_max_left l₁ l₂) (le_max_left (max l₁ l₂) (max 0 k₂))
            have h2 : max (max l₁ l₂) (max 0 k₂) < L₁p := not_le.mp hL
            omega)
      by_cases hcore : ∃ n : ℕ, mdlCore ρ C₀ a l₁ l₂ 0 k₂ n
      · set m₀ : ℕ := Nat.find hcore with hm₀def
        have hm₀ : mdlCore ρ C₀ a l₁ l₂ 0 k₂ m₀ := Nat.find_spec hcore
        have hm₀min : ∀ n, mdlCore ρ C₀ a l₁ l₂ 0 k₂ n → m₀ ≤ n :=
          fun n hn => Nat.find_min' hcore hn
        have hcore_iff : ∀ n, mdlCore ρ C₀ a l₁ l₂ 0 k₂ n ↔ m₀ ≤ n :=
          fun n => ⟨fun hn => hm₀min n hn, fun hn => mdlLowHigh_mdlCore_of_le hfl hn hm₀⟩
        set F : ℕ → ℤ → ℂ := fun n x =>
          if mdlCore ρ C₀ a l₁ l₂ 0 k₂ n then
            Work.KMTAreas.A7.Tle ρ l₁ (Work.KMTAreas.A7.varphiN (Nat.floor (a n)) 0) g x
          else 0 with hF
        set W : ℤ → ℝ≥0∞ := fun x =>
          PointwiseErgodicTheorems.variationalNorm R (fun n : ℕ => F n x) with hW
        have hkey : MeasureTheory.eLpNorm W 2 MeasureTheory.Measure.count
            ≤ (Kc : ENNReal)
              * ENNReal.ofReal (Work.KMTAreas.A7.lossWeight 2 ρ l₁ l₂ 0 k₂)
              * MeasureTheory.eLpNorm f 2 MeasureTheory.Measure.count := by
          by_cases hgood : Work.Analysis.IonescuWainger.GoodMajorArcs ρ Cρ l₁
              (-(Work.Analysis.EndVar.logN (Nat.floor (a m₀))))
          · -- ## Case A: good major arcs at the first core index
            set sh : ℕ → ℤ → ℂ := fun k x =>
              Work.KMTAreas.A7.Tle ρ l₁
                (Work.KMTAreas.A7.varphiN (Nat.floor (a (k + m₀))) 0) g x with hsh
            set W2 : ℤ → ℝ≥0∞ := fun x =>
              PointwiseErgodicTheorems.variationalNorm R (fun k : ℕ => sh k x) with hW2
            have hF_eq : ∀ x : ℤ, (fun n : ℕ => F n x)
                = fun n : ℕ => if n < m₀ then 0 else sh (n - m₀) x := by
              intro x
              funext n
              simp only [hF, hsh]
              by_cases hn : n < m₀
              · have hnc : ¬ mdlCore ρ C₀ a l₁ l₂ 0 k₂ n :=
                  fun hc => absurd (hm₀min n hc) (not_le.mpr hn)
                simp only [hnc, if_false, if_pos hn]
              · have hnc : mdlCore ρ C₀ a l₁ l₂ 0 k₂ n := (hcore_iff n).mpr (le_of_not_gt hn)
                simp only [hnc, if_true, if_neg hn]
                rw [Nat.sub_add_cancel (le_of_not_gt hn)]
            have hpt : ∀ x : ℤ, W x ≤ 3 * W2 x := by
              intro x
              show PointwiseErgodicTheorems.variationalNorm R (fun n : ℕ => F n x)
                ≤ 3 * PointwiseErgodicTheorems.variationalNorm R (fun k : ℕ => sh k x)
              rw [hF_eq x]
              exact Submission.PointwiseErgodicTheorems.variationalNorm_prependZeros_le
                hR1 m₀ (fun k => sh k x)
            have hcrux_apply : MeasureTheory.eLpNorm W2 2 MeasureTheory.Measure.count
                ≤ ENNReal.ofReal (C * (1 + (l₁ : ℝ)) ^ 2) *
                    MeasureTheory.eLpNorm g 2 MeasureTheory.Measure.count := by
              simpa only [hW2, hsh] using hspec m₀ l₁ a ha ha1 g hgood (hdisjAt m₀ hm₀)
            have hstep : MeasureTheory.eLpNorm W 2 MeasureTheory.Measure.count
                ≤ 3 * MeasureTheory.eLpNorm W2 2 MeasureTheory.Measure.count := by
              have hmono : MeasureTheory.eLpNorm W 2 MeasureTheory.Measure.count
                  ≤ MeasureTheory.eLpNorm (fun x : ℤ => (3 : ENNReal) * W2 x)
                    2 MeasureTheory.Measure.count :=
                MeasureTheory.eLpNorm_mono_enorm (hf := by pw_aesm) (fun x => by
                  rw [enorm_eq_self, enorm_eq_self]
                  exact hpt x)
              rwa [Commons.MeasureTheory.Lp.eLpNorm_const_mul_ennreal
                (show (3 : ENNReal) ≠ ⊤ from by norm_num) (by norm_num) (by norm_num)] at hmono
            have hreal : 3 * (C * (1 + (l₁ : ℝ)) ^ 2) * Csta
                ≤ (4 * (Y : ℝ) * B * Csta + 3 * C * Csta + 1)
                  * Work.KMTAreas.A7.lossWeight 2 ρ l₁ l₂ 0 k₂ := by
              have h1 := mdlLowHigh_one_add_sq_le_lossWeight hρ.le l₁ l₂ k₂
              have h3 : (0 : ℝ) ≤ 3 * C * Csta :=
                mul_nonneg (mul_nonneg (by norm_num) hCpos.le) hCstapos.le
              have h4 : (0 : ℝ) ≤ 4 * (Y : ℝ) * B * Csta :=
                mul_nonneg (mul_nonneg (mul_nonneg (by norm_num) hY0) hB0) hCstapos.le
              calc 3 * (C * (1 + (l₁ : ℝ)) ^ 2) * Csta
                  = (3 * C * Csta) * (1 + (l₁ : ℝ)) ^ 2 := by ring
                _ ≤ (3 * C * Csta) * Work.KMTAreas.A7.lossWeight 2 ρ l₁ l₂ 0 k₂ :=
                    mul_le_mul_of_nonneg_left h1 h3
                _ ≤ (4 * (Y : ℝ) * B * Csta + 3 * C * Csta + 1)
                      * Work.KMTAreas.A7.lossWeight 2 ρ l₁ l₂ 0 k₂ := by
                    refine mul_le_mul_of_nonneg_right ?_ hLpos.le
                    linarith
            calc MeasureTheory.eLpNorm W 2 MeasureTheory.Measure.count
                ≤ 3 * MeasureTheory.eLpNorm W2 2 MeasureTheory.Measure.count := hstep
              _ ≤ 3 * (ENNReal.ofReal (C * (1 + (l₁ : ℝ)) ^ 2)
                    * MeasureTheory.eLpNorm g 2 MeasureTheory.Measure.count) :=
                  mul_le_mul' le_rfl hcrux_apply
              _ ≤ 3 * (ENNReal.ofReal (C * (1 + (l₁ : ℝ)) ^ 2)
                    * (ENNReal.ofReal Csta
                      * MeasureTheory.eLpNorm f 2 MeasureTheory.Measure.count)) :=
                  mul_le_mul' le_rfl (mul_le_mul' le_rfl hgle)
              _ = ENNReal.ofReal (3 * (C * (1 + (l₁ : ℝ)) ^ 2) * Csta)
                    * MeasureTheory.eLpNorm f 2 MeasureTheory.Measure.count :=
                  mdlLowHigh_three_mul_ofReal (C * (1 + (l₁ : ℝ)) ^ 2) Csta (by positivity) _
              _ ≤ (Kc : ENNReal)
                    * ENNReal.ofReal (Work.KMTAreas.A7.lossWeight 2 ρ l₁ l₂ 0 k₂)
                    * MeasureTheory.eLpNorm f 2 MeasureTheory.Measure.count := by
                  rw [← ENNReal.ofReal_coe_nnreal]
                  exact mdlLowHigh_ofReal_le_mul_ofReal (by linarith)
                    (by rw [hKcR]; exact hreal) _
          · -- ## Case B: the first core index is below the good-major-arcs threshold
            have hbad₀ : (((Work.Analysis.EndVar.logN (Nat.floor (a m₀)) : ℤ)) : ℝ)
                < Cρ * (2 : ℝ) ^ (ρ * (l₁ : ℝ)) := by
              by_contra hcon
              refine hgood ?_
              rw [Work.Analysis.IonescuWainger.GoodMajorArcs]
              push_cast
              linarith
            have hl₁L : (l₁ : ℝ) ≤ 2 * (C₀ : ℝ) * Real.logb 2 (Cρ + 2) :=
              MdlLpH.mdlCore_bad_l_bound ρ hρ C₀ hC₀ Cρ (Nat.floor (a m₀)) l₁ l₂ k₂ hρC hm₀.1 hbad₀
            have hl₁L₁ : l₁ ≤ L₁ := by
              rw [hL₁]
              exact_mod_cast (le_trans hl₁L (Nat.le_ceil _))
            -- the first index at or after `m₀` with good major arcs
            have hexm₁ : ∃ n : ℕ, m₀ ≤ n ∧
                Work.Analysis.IonescuWainger.GoodMajorArcs ρ Cρ l₁
                  (-(Work.Analysis.EndVar.logN (Nat.floor (a n)))) := by
              obtain ⟨n, hn⟩ := MdlLpH.exists_logN_floor_a_ge hΛ' ha ha1
                (Nat.ceil (Cρ * (2 : ℝ) ^ (ρ * (l₁ : ℝ))))
              refine ⟨max m₀ n, le_max_left _ _, ?_⟩
              rw [Work.Analysis.IonescuWainger.GoodMajorArcs]
              have h1 : (Cρ * (2 : ℝ) ^ (ρ * (l₁ : ℝ)))
                  ≤ ((Nat.ceil (Cρ * (2 : ℝ) ^ (ρ * (l₁ : ℝ))) : ℕ) : ℝ) := Nat.le_ceil _
              have h2 : ((Nat.ceil (Cρ * (2 : ℝ) ^ (ρ * (l₁ : ℝ))) : ℕ) : ℝ)
                  ≤ ((Work.Analysis.EndVar.logN (Nat.floor (a n)) : ℤ) : ℝ) := by
                exact_mod_cast hn
              have h3 : ((Work.Analysis.EndVar.logN (Nat.floor (a n)) : ℤ) : ℝ)
                  ≤ ((Work.Analysis.EndVar.logN (Nat.floor (a (max m₀ n))) : ℤ) : ℝ) := by
                exact_mod_cast hmono (le_max_right _ _)
              push_cast
              linarith [h1, h2, h3]
            set m₁ : ℕ := Nat.find hexm₁ with hm₁def
            have hm₁ge : m₀ ≤ m₁ := (Nat.find_spec hexm₁).1
            have hm₁good : Work.Analysis.IonescuWainger.GoodMajorArcs ρ Cρ l₁
                (-(Work.Analysis.EndVar.logN (Nat.floor (a m₁)))) := (Nat.find_spec hexm₁).2
            have hm₁min : ∀ n, m₀ ≤ n →
                Work.Analysis.IonescuWainger.GoodMajorArcs ρ Cρ l₁
                  (-(Work.Analysis.EndVar.logN (Nat.floor (a n)))) → m₁ ≤ n :=
              fun n hn hg => Nat.find_min' hexm₁ ⟨hn, hg⟩
            have hy : ∀ n : ℕ, m₀ ≤ n → n < m₁ →
                ((Work.Analysis.EndVar.logN (Nat.floor (a n))).toNat) < Y := by
              intro n hn hlt
              have hng : ¬ Work.Analysis.IonescuWainger.GoodMajorArcs ρ Cρ l₁
                  (-(Work.Analysis.EndVar.logN (Nat.floor (a n)))) :=
                fun hg => absurd (hm₁min n hn hg) (not_le.mpr hlt)
              have hlt2 : ((Work.Analysis.EndVar.logN (Nat.floor (a n)) : ℤ) : ℝ)
                  < Cρ * (2 : ℝ) ^ (ρ * (l₁ : ℝ)) := by
                by_contra hcon
                refine hng ?_
                rw [Work.Analysis.IonescuWainger.GoodMajorArcs]
                push_cast
                linarith
              have hmono2 : Cρ * (2 : ℝ) ^ (ρ * (l₁ : ℝ))
                  ≤ Cρ * (2 : ℝ) ^ (ρ * (L₁ : ℝ)) := by
                refine mul_le_mul_of_nonneg_left ?_ hCρpos.le
                refine Real.rpow_le_rpow_of_exponent_le (by norm_num) ?_
                have : (l₁ : ℝ) ≤ (L₁ : ℝ) := by exact_mod_cast hl₁L₁
                nlinarith [hρ]
              have hYc : Cρ * (2 : ℝ) ^ (ρ * (L₁ : ℝ)) ≤ (Y : ℝ) := by
                rw [hY]
                push_cast
                linarith [Nat.le_ceil (Cρ * (2 : ℝ) ^ (ρ * (L₁ : ℝ)))]
              have hYz : Work.Analysis.EndVar.logN (Nat.floor (a n)) < (Y : ℤ) := by
                have h : ((Work.Analysis.EndVar.logN (Nat.floor (a n)) : ℤ) : ℝ) < (Y : ℝ) :=
                  lt_of_lt_of_le (lt_of_lt_of_le hlt2 hmono2) hYc
                exact_mod_cast h
              omega
            -- ## the prefix `n < m₁`
            set U : ℕ → ℤ → ℂ := fun m x => Work.KMTContract.kmtProj ρ l₁ (-(m : ℤ)) g x with hU
            set US : ℤ → ℝ≥0∞ := fun x =>
              ∑ m ∈ Finset.range Y, 4 * ENNReal.ofReal ‖U m x‖ with hUS
            set UG : ℤ → ℝ≥0∞ := fun x => PointwiseErgodicTheorems.variationalNorm R
              (fun n : ℕ => if m₀ ≤ n ∧ n < m₁ then
                U ((Work.Analysis.EndVar.logN (Nat.floor (a n))).toNat) x else 0) with hUG
            set WG : ℤ → ℝ≥0∞ := fun x => PointwiseErgodicTheorems.variationalNorm R
              (fun n : ℕ => if n < m₁ then F n x else 0) with hWG
            set WH : ℤ → ℝ≥0∞ := fun x => PointwiseErgodicTheorems.variationalNorm R
              (fun n : ℕ => if m₁ ≤ n then F n x else 0) with hWH
            have hσmono : Monotone
                (fun n : ℕ => (Work.Analysis.EndVar.logN (Nat.floor (a n))).toNat) :=
              fun _ _ hnm => Int.toNat_le_toNat (hmono hnm)
            have hWG_eq : WG = UG := by
              funext x
              show PointwiseErgodicTheorems.variationalNorm R
                    (fun n : ℕ => if n < m₁ then F n x else 0)
                  = PointwiseErgodicTheorems.variationalNorm R
                    (fun n : ℕ => if m₀ ≤ n ∧ n < m₁ then
                      U ((Work.Analysis.EndVar.logN (Nat.floor (a n))).toNat) x else 0)
              congr 1
              funext n
              simp only [hF, hU]
              by_cases h : m₀ ≤ n ∧ n < m₁
              · have hc : mdlCore ρ C₀ a l₁ l₂ 0 k₂ n := (hcore_iff n).mpr h.1
                simp only [h.2, hc, h, if_true]
                rw [Work.KMTAreas.A7.Tle_varphiN_zero]
                congr 1
              · by_cases hlt : n < m₁
                · have hnle : ¬ (m₀ ≤ n) := fun hge => h ⟨hge, hlt⟩
                  have hc : ¬ mdlCore ρ C₀ a l₁ l₂ 0 k₂ n :=
                    fun hc => hnle ((hcore_iff n).mp hc)
                  simp only [if_pos hlt, if_neg hc, if_neg h]
                · simp only [if_neg hlt, if_neg h]
            have hUG_le : ∀ x : ℤ, UG x ≤ US x := fun x =>
              MdlLpH.variationalNorm_comp_mono_range_le hR1 (fun m => U m x)
                (fun n : ℕ => (Work.Analysis.EndVar.logN (Nat.floor (a n))).toNat) hσmono
                m₀ m₁ Y hy
            have hperlevel : ∀ m : ℕ, MeasureTheory.eLpNorm
                (fun x : ℤ => ENNReal.ofReal ‖U m x‖) 2 MeasureTheory.Measure.count
                ≤ ENNReal.ofReal B * MeasureTheory.eLpNorm g 2 MeasureTheory.Measure.count := by
              intro m
              rw [show (fun x : ℤ => ENNReal.ofReal ‖U m x‖) = (fun x : ℤ => ‖U m x‖ₑ) from
                funext (fun x => ofReal_norm _)]
              rw [MeasureTheory.eLpNorm_enorm (hf := by pw_aesm)]
              exact hBspec l₁ (-(m : ℤ)) hl₁L₁ (by omega) g
            have hGbound : MeasureTheory.eLpNorm WG 2 MeasureTheory.Measure.count
                ≤ ENNReal.ofReal (4 * (Y : ℝ) * B)
                  * MeasureTheory.eLpNorm g 2 MeasureTheory.Measure.count := by
              calc MeasureTheory.eLpNorm WG 2 MeasureTheory.Measure.count
                  = MeasureTheory.eLpNorm UG 2 MeasureTheory.Measure.count := by rw [hWG_eq]
                _ ≤ MeasureTheory.eLpNorm US 2 MeasureTheory.Measure.count :=
                    MeasureTheory.eLpNorm_mono_enorm (hf := by pw_aesm) hUG_le
                _ ≤ ∑ m ∈ Finset.range Y, MeasureTheory.eLpNorm
                      (fun x : ℤ => 4 * ENNReal.ofReal ‖U m x‖)
                      2 MeasureTheory.Measure.count := by
                    rw [hUS]
                    exact Commons.MeasureTheory.Lp.eLpNorm_finset_sum_le_ennreal (by norm_num)
                      (fun m _ => (measurable_of_countable _).aemeasurable)
                _ = ∑ m ∈ Finset.range Y, 4 * MeasureTheory.eLpNorm
                      (fun x : ℤ => ENNReal.ofReal ‖U m x‖)
                      2 MeasureTheory.Measure.count := by
                    refine Finset.sum_congr rfl (fun m _ => ?_)
                    exact Commons.MeasureTheory.Lp.eLpNorm_const_mul_ennreal
                      (show (4 : ENNReal) ≠ ⊤ from by norm_num) (by norm_num) (by norm_num)
                _ ≤ ∑ m ∈ Finset.range Y, 4 * (ENNReal.ofReal B
                      * MeasureTheory.eLpNorm g 2 MeasureTheory.Measure.count) := by
                    refine Finset.sum_le_sum (fun m _ => ?_)
                    exact mul_le_mul' le_rfl (hperlevel m)
                _ = ENNReal.ofReal (4 * (Y : ℝ) * B)
                      * MeasureTheory.eLpNorm g 2 MeasureTheory.Measure.count :=
                    mdlLowHigh_sum_ofReal Y B _
            -- ## the tail `n ≥ m₁`
            set sh₁ : ℕ → ℤ → ℂ := fun k x =>
              Work.KMTAreas.A7.Tle ρ l₁
                (Work.KMTAreas.A7.varphiN (Nat.floor (a (k + m₁))) 0) g x with hsh₁
            set W₃ : ℤ → ℝ≥0∞ := fun x =>
              PointwiseErgodicTheorems.variationalNorm R (fun k : ℕ => sh₁ k x) with hW₃
            have hH_eq : WH = fun x : ℤ => PointwiseErgodicTheorems.variationalNorm R
                (fun n : ℕ => if n < m₁ then 0 else sh₁ (n - m₁) x) := by
              funext x
              show PointwiseErgodicTheorems.variationalNorm R
                    (fun n : ℕ => if m₁ ≤ n then F n x else 0)
                  = PointwiseErgodicTheorems.variationalNorm R
                    (fun n : ℕ => if n < m₁ then 0 else sh₁ (n - m₁) x)
              congr 1
              funext n
              simp only [hF, hsh₁]
              by_cases hn : n < m₁
              · simp only [if_neg (not_le.mpr hn), if_pos hn]
              · have hge : m₁ ≤ n := le_of_not_gt hn
                have hc : mdlCore ρ C₀ a l₁ l₂ 0 k₂ n :=
                  (hcore_iff n).mpr (le_trans hm₁ge hge)
                simp only [if_pos hge, hc, if_true, if_neg hn]
                rw [Nat.sub_add_cancel hge]
            have hHbound : MeasureTheory.eLpNorm WH 2 MeasureTheory.Measure.count
                ≤ 3 * (ENNReal.ofReal (C * (1 + (l₁ : ℝ)) ^ 2)
                  * MeasureTheory.eLpNorm g 2 MeasureTheory.Measure.count) := by
              have hpt : ∀ x : ℤ, WH x ≤ 3 * W₃ x := by
                intro x
                rw [hH_eq]
                show PointwiseErgodicTheorems.variationalNorm R
                    (fun n : ℕ => if n < m₁ then 0 else sh₁ (n - m₁) x)
                  ≤ 3 * PointwiseErgodicTheorems.variationalNorm R (fun k : ℕ => sh₁ k x)
                exact Submission.PointwiseErgodicTheorems.variationalNorm_prependZeros_le
                  hR1 m₁ (fun k => sh₁ k x)
              have hcrux₁ : MeasureTheory.eLpNorm W₃ 2 MeasureTheory.Measure.count
                  ≤ ENNReal.ofReal (C * (1 + (l₁ : ℝ)) ^ 2) *
                      MeasureTheory.eLpNorm g 2 MeasureTheory.Measure.count := by
                simpa only [hW₃, hsh₁] using hspec m₁ l₁ a ha ha1 g hm₁good
                  (hdisjAt m₁ ((hcore_iff m₁).mpr hm₁ge))
              have hmono : MeasureTheory.eLpNorm WH 2 MeasureTheory.Measure.count
                  ≤ MeasureTheory.eLpNorm (fun x : ℤ => (3 : ENNReal) * W₃ x)
                    2 MeasureTheory.Measure.count :=
                MeasureTheory.eLpNorm_mono_enorm (hf := by pw_aesm) (fun x => by
                  rw [enorm_eq_self, enorm_eq_self]
                  exact hpt x)
              rw [Commons.MeasureTheory.Lp.eLpNorm_const_mul_ennreal
                (show (3 : ENNReal) ≠ ⊤ from by norm_num) (by norm_num) (by norm_num)] at hmono
              exact hmono.trans (mul_le_mul' le_rfl hcrux₁)
            have hVsplit : ∀ x : ℤ, W x ≤ WG x + WH x := by
              intro x
              have hdecomp : (fun n : ℕ => F n x) = fun n : ℕ =>
                  (if n < m₁ then F n x else 0) + (if m₁ ≤ n then F n x else 0) := by
                funext n
                by_cases h : n < m₁
                · simp only [if_pos h, if_neg (not_le.mpr h), add_zero]
                · simp only [if_neg h, if_pos (le_of_not_gt h), zero_add]
              show PointwiseErgodicTheorems.variationalNorm R (fun n : ℕ => F n x)
                ≤ PointwiseErgodicTheorems.variationalNorm R
                    (fun n : ℕ => if n < m₁ then F n x else 0)
                  + PointwiseErgodicTheorems.variationalNorm R
                    (fun n : ℕ => if m₁ ≤ n then F n x else 0)
              rw [hdecomp]
              exact Submission.PointwiseErgodicTheorems.variationalNorm_add_le hR1 _ _
            have hfinal : (4 * (Y : ℝ) * B) * Csta
                  + 3 * (C * (1 + (l₁ : ℝ)) ^ 2) * Csta
                ≤ (4 * (Y : ℝ) * B * Csta + 3 * C * Csta + 1)
                  * Work.KMTAreas.A7.lossWeight 2 ρ l₁ l₂ 0 k₂ := by
              have h1 := mdlLowHigh_one_add_sq_le_lossWeight hρ.le l₁ l₂ k₂
              have h3 : (0 : ℝ) ≤ 4 * (Y : ℝ) * B * Csta :=
                mul_nonneg (mul_nonneg (mul_nonneg (by norm_num) hY0) hB0) hCstapos.le
              have h4 : (0 : ℝ) ≤ 3 * C * Csta :=
                mul_nonneg (mul_nonneg (by norm_num) hCpos.le) hCstapos.le
              calc (4 * (Y : ℝ) * B) * Csta + 3 * (C * (1 + (l₁ : ℝ)) ^ 2) * Csta
                  = (4 * (Y : ℝ) * B * Csta) * 1 + (3 * C * Csta) * (1 + (l₁ : ℝ)) ^ 2 := by
                    ring
                _ ≤ (4 * (Y : ℝ) * B * Csta)
                      * Work.KMTAreas.A7.lossWeight 2 ρ l₁ l₂ 0 k₂
                    + (3 * C * Csta) * Work.KMTAreas.A7.lossWeight 2 ρ l₁ l₂ 0 k₂ := by
                    exact add_le_add (mul_le_mul_of_nonneg_left hL1 h3)
                      (mul_le_mul_of_nonneg_left h1 h4)
                _ ≤ (4 * (Y : ℝ) * B * Csta + 3 * C * Csta + 1)
                      * Work.KMTAreas.A7.lossWeight 2 ρ l₁ l₂ 0 k₂ := by
                    have h5 : (0 : ℝ) ≤ Work.KMTAreas.A7.lossWeight 2 ρ l₁ l₂ 0 k₂ := hLpos.le
                    nlinarith [h5]
            calc MeasureTheory.eLpNorm W 2 MeasureTheory.Measure.count
                ≤ MeasureTheory.eLpNorm WG 2 MeasureTheory.Measure.count
                  + MeasureTheory.eLpNorm WH 2 MeasureTheory.Measure.count :=
                  (MeasureTheory.eLpNorm_mono_enorm (hf := by pw_aesm) hVsplit).trans
                    (MeasureTheory.eLpNorm_add_le (by norm_num))
              _ ≤ ENNReal.ofReal (4 * (Y : ℝ) * B)
                    * MeasureTheory.eLpNorm g 2 MeasureTheory.Measure.count
                  + 3 * (ENNReal.ofReal (C * (1 + (l₁ : ℝ)) ^ 2)
                    * MeasureTheory.eLpNorm g 2 MeasureTheory.Measure.count) :=
                  add_le_add hGbound hHbound
              _ ≤ ENNReal.ofReal (4 * (Y : ℝ) * B)
                    * (ENNReal.ofReal Csta
                      * MeasureTheory.eLpNorm f 2 MeasureTheory.Measure.count)
                  + 3 * (ENNReal.ofReal (C * (1 + (l₁ : ℝ)) ^ 2)
                    * (ENNReal.ofReal Csta
                      * MeasureTheory.eLpNorm f 2 MeasureTheory.Measure.count)) :=
                  add_le_add (mul_le_mul' le_rfl hgle)
                    (mul_le_mul' le_rfl (mul_le_mul' le_rfl hgle))
              _ = ENNReal.ofReal ((4 * (Y : ℝ) * B) * Csta
                    + 3 * (C * (1 + (l₁ : ℝ)) ^ 2) * Csta)
                    * MeasureTheory.eLpNorm f 2 MeasureTheory.Measure.count :=
                  mdlLowHigh_ofReal_add_mul (4 * (Y : ℝ) * B) (C * (1 + (l₁ : ℝ)) ^ 2) Csta
                    (by positivity) (by positivity) hCstapos.le _
              _ ≤ (Kc : ENNReal)
                    * ENNReal.ofReal (Work.KMTAreas.A7.lossWeight 2 ρ l₁ l₂ 0 k₂)
                    * MeasureTheory.eLpNorm f 2 MeasureTheory.Measure.count := by
                  rw [← ENNReal.ofReal_coe_nnreal]
                  exact mdlLowHigh_ofReal_le_mul_ofReal (by linarith)
                    (by rw [hKcR]; exact hfinal) _
        simpa only [hW, hF, hg] using hkey
      · -- ## no core index: the family is identically zero
        have hzero : (fun x : ℤ => PointwiseErgodicTheorems.variationalNorm R (fun n : ℕ =>
            if Work.KMTPlan.A6.mdlCore ρ C₀ a l₁ l₂ 0 k₂ n then
              Work.KMTAreas.A7.Tle ρ l₁ (Work.KMTAreas.A7.varphiN (Nat.floor (a n)) 0)
                (Work.KMTPlan.A6.mdlF ρ (Work.KMTAreas.A7.uScale ρ
                  (max (max l₁ l₂) (max 0 k₂))) l₁ f) x
            else 0)) = 0 := by
          funext x
          have hthis : (fun n : ℕ =>
              if Work.KMTPlan.A6.mdlCore ρ C₀ a l₁ l₂ 0 k₂ n then
                Work.KMTAreas.A7.Tle ρ l₁ (Work.KMTAreas.A7.varphiN (Nat.floor (a n)) 0)
                  (Work.KMTPlan.A6.mdlF ρ (Work.KMTAreas.A7.uScale ρ
                    (max (max l₁ l₂) (max 0 k₂))) l₁ f) x
              else 0) = 0 := by
            funext n
            simp only [if_neg (fun hc => hcore ⟨n, hc⟩), Pi.zero_apply]
          rw [hthis]
          have hvn0 : PointwiseErgodicTheorems.variationalNorm R (0 : ℕ → ℂ) = 0 := by
            have h := Submission.PointwiseErgodicTheorems.variationalNorm_smul (r := R)
              hR1 (0 : ℂ) (0 : ℕ → ℂ)
            simpa using h
          exact hvn0
        rw [hzero]
        simp
    · -- ## `Λ ≤ 1`: the conclusion is vacuous
      exact ⟨1, fun a l₁ l₂ k₂ f h => absurd h hΛ⟩
  refine ⟨fun Λ => Classical.choose (hexK Λ), ?_⟩
  intro a Λ l₁ l₂ k₂ f hΛ ha ha1 hl₁
  exact (Classical.choose_spec (hexK Λ)) a l₁ l₂ k₂ f hΛ ha ha1 hl₁

end Work.KMTPlan.A6
