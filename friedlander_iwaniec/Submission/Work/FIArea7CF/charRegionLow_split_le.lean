/-
# `Submission.Work.FIArea7CF.charRegionLow_split_le` — clash-free copy of `Submission.Work.FIArea7.charRegionLow_split_le`

Imports redirected to the `FIArea7CF` copies; renamed: norm_uniCoeff_le→crs_norm_uniCoeff_le.  The workspace contains several
incompatible declarations of `Work.FIArea7.mem_gBox_iff` (and of `norm_uniCoeff_le`,
`log_pow_le_rpow`, `gnorm_mk_eq`), so the amended area-7 assembly and the *FI* §§19–26
chain can only meet through copies.  See NOTES §63.
-/
import Mathlib
import Submission.Work.FIArea7.Area7Regions6b
import Submission.Work.FIArea7.UniCharTerm6
import Submission.Work.FIArea7.Section16Expansion
import Submission.Work.FIArea7CF.charRegionSplitAux
import Submission.Work.FIArea7.WUniOmega6Pull6CharLow_aux
import Submission.Work.FIArea7.sumChiNormUniSCharSq
import Submission.Work.FIArea7.sumChiNormUniJCharSq
import Submission.Work.FIArea7CF.regionLowSplitWeightSum
import Submission.Work.FIArea7.fiberBoundNum

set_option maxHeartbeats 1600000

namespace Work.FIArea7

open Finset
open scoped BigOperators

attribute [local instance] Classical.propDecidable

noncomputable section

/-- The mode weight of the (17.10) expansion is a `log(K+2)`: `2log2 + log4 + Σ 1/|k| ≤
25·log(K+2)` (`sum_inv_abs_evenFreq_le` and `log 2 ≤ 1`). -/
private lemma uniH_le_log (K : ℕ) (hK : 1 ≤ K) : uniH K ≤ 25 * Real.log ((K : ℝ) + 2) := by
  have hsum : (∑ k ∈ evenFreq K, (1 / ((|k| : ℤ) : ℝ))) ≤ 2 * Real.log (2 * (K:ℝ) + 2) + 2 := by
    refine le_trans (le_of_eq ?_) (sum_inv_abs_evenFreq_le K)
    refine Finset.sum_congr rfl fun k _ => ?_
    rw [show (((|k| : ℤ)) : ℝ) = |(k : ℝ)| from Int.cast_abs]
  have h2 : Real.log 2 ≤ 1 := by
    have h := Real.log_le_sub_one_of_pos (show (0 : ℝ) < 2 by norm_num)
    linarith
  have h4 : Real.log 4 = 2 * Real.log 2 := by
    rw [show (4 : ℝ) = 2 ^ 2 by norm_num, Real.log_pow]
    norm_num
  have hlogm : Real.log (2 * (K:ℝ) + 2) = Real.log 2 + Real.log ((K:ℝ) + 1) := by
    rw [show 2 * (K:ℝ) + 2 = 2 * ((K:ℝ) + 1) by ring,
      Real.log_mul (by norm_num) (by positivity)]
  have hlog1 : 1 ≤ Real.log ((K : ℝ) + 2) := by
    have h3 : (3 : ℝ) ≤ (K : ℝ) + 2 := by
      have : (1 : ℝ) ≤ (K : ℝ) := by exact_mod_cast hK
      linarith
    have h1 : 1 ≤ Real.log 3 := by
      have h := Real.log_le_log (Real.exp_pos 1) (le_of_lt Real.exp_one_lt_three)
      rwa [Real.log_exp] at h
    exact le_trans h1 (Real.log_le_log (by norm_num) h3)
  have hlogK1le : Real.log ((K:ℝ) + 1) ≤ Real.log ((K:ℝ) + 2) :=
    Real.log_le_log (by linarith [Nat.cast_nonneg (α := ℝ) K]) (by linarith)
  rw [uniH, h4]
  nlinarith [hsum, h2, hlog1, hlogm, hlogK1le]

/-- **The per-`(b,e)` cross-term bound of region I.**  For `(b,e)` in region I, the sesquilinear
cross term `uniCharTermCross` is bounded by `(1/b)·uniH K·2s·√(4be·(M·E2))` with the box fibre
count `M = ((2·radN Pa + 1)/4be + 1)²`; the analytic content is Cauchy–Schwarz over the characters
(`uniCrossMode_le`) plus the numeric fibre bound `fiberBoundNum`. -/
private lemma termBound : ∀ (Pa : Work.FITop.Params) (X K L₀ : ℕ) (δ₁ s : ℝ)
    (u v : GaussianInt → ℂ),
    1 ≤ X → 1 ≤ K → 0 ≤ s →
    (∀ (Q : ℕ) [NeZero Q] (k : ℤ) (χ : AddChar (Additive (Work.FIArea7.GaussUnit Q)) ℂ),
        (Q:ℝ) * (2 * (K:ℝ) + (L₀:ℝ) + 2) ≤ Pa.N ^ δ₁ → |(k:ℝ)| ≤ 2 * K →
        ‖Work.FIArea7.uniSChar Pa Q (fun _ => 1) u k χ‖ ≤ s) →
    ∀ p ∈ Work.FIArea7.charRegionLowFinset Pa X K L₀ δ₁,
      ‖Work.FIArea7.uniCharTermCross Pa p.1 p.2 (fun _ => (1:ℤ)) u v K‖
        ≤ (1 / (p.1 : ℝ)) * Work.FIArea7.uniH K * (2 * s)
            * ((15 * Real.sqrt Pa.N / Real.sqrt (4 * (p.1 : ℝ) * (p.2 : ℝ))
                + 2 * Real.sqrt (4 * (p.1 : ℝ) * (p.2 : ℝ)))
                * Real.sqrt (∑ z ∈ Work.FIPlan.gBox (Work.FITop.radN Pa), ‖v z‖ ^ 2)) := by
  intro Pa X K L₀ δ₁ s u v hX hK hs hhyp p hp
  set E2 : ℝ := ∑ z ∈ Work.FIPlan.gBox (Work.FITop.radN Pa), ‖v z‖ ^ 2 with hE2
  have hE20 : 0 ≤ E2 := by rw [hE2]; exact Finset.sum_nonneg (fun z _ => sq_nonneg _)
  have hε : ∀ z : GaussianInt, ‖(((1 : ℤ)) : ℂ)‖ ≤ 1 := by intro z; norm_num
  obtain ⟨hp1, hp2, hreg⟩ := Work.FIArea7.mem_charRegionLowFinset.mp hp
  have hb : 1 ≤ p.1 := (Finset.mem_Icc.mp hp1).1
  have he : 1 ≤ p.2 := (Finset.mem_Icc.mp hp2).1
  have hQpos : 0 < 4 * p.1 * p.2 := by positivity
  haveI : NeZero (4 * p.1 * p.2) := ⟨by omega⟩
  have hcastQ : ((4 * p.1 * p.2 : ℕ) : ℝ) = 4 * (p.1 : ℝ) * (p.2 : ℝ) := by push_cast; ring
  set M : ℝ := ((((2 * Work.FITop.radN Pa + 1).toNat / (4 * p.1 * p.2) + 1 : ℕ)) : ℝ) ^ 2 with hM
  have hM0 : 0 ≤ M := by rw [hM]; positivity
  have hregQ : ((4 * p.1 * p.2 : ℕ) : ℝ) * (2 * (K:ℝ) + (L₀:ℝ) + 2) ≤ Pa.N ^ δ₁ := by
    rw [hcastQ]; exact hreg
  have hN0 : (0:ℝ) ≤ Pa.N := by linarith [Pa.hN1]
  have hmodel : ∀ k : ℤ, |(k:ℝ)| ≤ 2 * K →
      ‖Work.FIArea7.uniCrossMode Pa (4 * p.1 * p.2) p.2 (fun _ => (1:ℤ)) u v k‖
        ≤ 2 * s * Real.sqrt (4 * (p.1:ℝ) * (p.2:ℝ) * (M * E2)) := by
    intro k hk
    have hV : (∑ χ : AddChar (Additive (GaussUnit (4 * p.1 * p.2))) ℂ,
        ‖Work.FIArea7.uniSChar Pa (4 * p.1 * p.2) (fun _ => (1:ℤ)) v k χ‖ ^ 2)
        ≤ (Fintype.card (GaussUnit (4 * p.1 * p.2)) : ℝ) * (M * E2) := by
      have hh := sumChiNormUniSCharSq (Pa := Pa) (4 * p.1 * p.2) (fun _ => (1:ℤ)) v k hε
      rw [hM, hE2]
      simpa only [mul_assoc] using hh
    have h1 := Work.FIArea7.uniCrossMode_le (Pa := Pa) (Q := 4 * p.1 * p.2) (e := p.2)
      (ε := fun _ => (1:ℤ)) (u := u) (v := v) (k := k) hs (mul_nonneg hM0 hE20)
      (fun χ => hhyp (4 * p.1 * p.2) k χ hregQ hk)
      (sumChiNormUniJCharSq (4 * p.1 * p.2) p.2) hV
    rwa [hcastQ] at h1
  have hkle : ∀ k ∈ Work.FIArea7.evenFreq K, |(k:ℝ)| ≤ 2 * K := by
    intro k hk
    rw [Work.FIArea7.evenFreq, Finset.mem_filter, Finset.mem_Icc] at hk
    obtain ⟨⟨hl, hr⟩, -⟩ := hk
    have h2 : |(k:ℝ)| = (((|k| : ℤ)) : ℝ) := (Int.cast_abs).symm
    rw [h2]
    exact_mod_cast (abs_le.mpr ⟨hl, hr⟩)
  have hk0 : |((0:ℤ):ℝ)| ≤ 2 * K := by rw [Int.cast_zero, abs_zero]; positivity
  have hnum : Real.sqrt (4 * (p.1:ℝ) * (p.2:ℝ) * (M * E2))
      ≤ (15 * Real.sqrt Pa.N / Real.sqrt (4 * (p.1:ℝ) * (p.2:ℝ))
          + 2 * Real.sqrt (4 * (p.1:ℝ) * (p.2:ℝ))) * Real.sqrt E2 := by
    have hf := fiberBoundNum (Pa := Pa) (Q := 4 * p.1 * p.2) hQpos
    rw [hcastQ] at hf
    have hQM : 4 * (p.1:ℝ) * (p.2:ℝ) * M
        ≤ 200 * Pa.N / (4 * (p.1:ℝ) * (p.2:ℝ)) + 4 * (4 * (p.1:ℝ) * (p.2:ℝ)) := hf
    have hsplit1 : Real.sqrt (4 * (p.1:ℝ) * (p.2:ℝ) * (M * E2))
        = Real.sqrt (4 * (p.1:ℝ) * (p.2:ℝ) * M) * Real.sqrt E2 := by
      rw [show 4 * (p.1:ℝ) * (p.2:ℝ) * (M * E2)
            = (4 * (p.1:ℝ) * (p.2:ℝ) * M) * E2 by ring,
        Real.sqrt_mul (by positivity : (0:ℝ) ≤ 4 * (p.1:ℝ) * (p.2:ℝ) * M)]
    rw [hsplit1]
    refine mul_le_mul_of_nonneg_right ?_ (Real.sqrt_nonneg _)
    have hs1 : Real.sqrt (200 * Pa.N / (4 * (p.1:ℝ) * (p.2:ℝ)))
        = Real.sqrt 200 * (Real.sqrt Pa.N / Real.sqrt (4 * (p.1:ℝ) * (p.2:ℝ))) := by
      rw [show 200 * Pa.N / (4 * (p.1:ℝ) * (p.2:ℝ))
            = 200 * (Pa.N / (4 * (p.1:ℝ) * (p.2:ℝ))) by ring]
      rw [Real.sqrt_mul (by norm_num : (0:ℝ) ≤ 200), Real.sqrt_div hN0]
    have hs2 : Real.sqrt (4 * (4 * (p.1:ℝ) * (p.2:ℝ)))
        = 2 * Real.sqrt (4 * (p.1:ℝ) * (p.2:ℝ)) := by
      rw [Real.sqrt_mul (by norm_num : (0:ℝ) ≤ 4)]
      rw [show Real.sqrt (4:ℝ) = 2 from by
        rw [show (4:ℝ) = 2^2 by norm_num, Real.sqrt_sq (by norm_num)]]
    have h200 : Real.sqrt 200 ≤ 15 := by
      have h := Real.sqrt_le_sqrt (show (200:ℝ) ≤ 225 by norm_num)
      rwa [show Real.sqrt (225:ℝ) = 15 from by
        rw [show (225:ℝ) = 15^2 by norm_num, Real.sqrt_sq (by norm_num)]] at h
    have hsqrtQ0 : (0:ℝ) ≤ Real.sqrt (4 * (p.1:ℝ) * (p.2:ℝ)) := Real.sqrt_nonneg _
    have hQinv0 : (0:ℝ) ≤ Real.sqrt Pa.N / Real.sqrt (4 * (p.1:ℝ) * (p.2:ℝ)) :=
      div_nonneg (Real.sqrt_nonneg _) hsqrtQ0
    calc Real.sqrt (4 * (p.1:ℝ) * (p.2:ℝ) * M)
        ≤ Real.sqrt (200 * Pa.N / (4 * (p.1:ℝ) * (p.2:ℝ)) + 4 * (4 * (p.1:ℝ) * (p.2:ℝ))) :=
          Real.sqrt_le_sqrt hQM
      _ ≤ Real.sqrt (200 * Pa.N / (4 * (p.1:ℝ) * (p.2:ℝ)))
          + Real.sqrt (4 * (4 * (p.1:ℝ) * (p.2:ℝ))) := Work.FIArea7.sqrt_add_le _ _
      _ = Real.sqrt 200 * (Real.sqrt Pa.N / Real.sqrt (4 * (p.1:ℝ) * (p.2:ℝ)))
          + 2 * Real.sqrt (4 * (p.1:ℝ) * (p.2:ℝ)) := by rw [hs1, hs2]
      _ ≤ 15 * (Real.sqrt Pa.N / Real.sqrt (4 * (p.1:ℝ) * (p.2:ℝ)))
          + 2 * Real.sqrt (4 * (p.1:ℝ) * (p.2:ℝ)) :=
          add_le_add (mul_le_mul_of_nonneg_right h200 hQinv0) le_rfl
      _ = 15 * Real.sqrt Pa.N / Real.sqrt (4 * (p.1:ℝ) * (p.2:ℝ))
          + 2 * Real.sqrt (4 * (p.1:ℝ) * (p.2:ℝ)) := by ring
  have hfin := Work.FIArea7.uniCharTermCross_le_mode p.1 p.2 K (fun _ => (1:ℤ)) u v hb hs
    (hmodel 0 hk0) (fun k hk => hmodel k (hkle k hk)) hnum
  calc ‖Work.FIArea7.uniCharTermCross Pa p.1 p.2 (fun _ => (1:ℤ)) u v K‖
      ≤ (1 / (p.1 : ℝ)) * Work.FIArea7.uniH K
          * (2 * s * ((15 * Real.sqrt Pa.N / Real.sqrt (4 * (p.1:ℝ) * (p.2:ℝ))
              + 2 * Real.sqrt (4 * (p.1:ℝ) * (p.2:ℝ))) * Real.sqrt E2)) := hfin
    _ = (1 / (p.1 : ℝ)) * Work.FIArea7.uniH K * (2 * s)
          * ((15 * Real.sqrt Pa.N / Real.sqrt (4 * (p.1:ℝ) * (p.2:ℝ))
              + 2 * Real.sqrt (4 * (p.1:ℝ) * (p.2:ℝ))) * Real.sqrt E2) := by ring

/-- **A7: the sesquilinear split of region I.**  `uniCharTerm` is sesquilinear in `β` (because
`uniSChar` is linear), so region I of `u + v` splits into the three pieces below; the cross terms
are bounded with Cauchy–Schwarz over `χ` (`Σ_χ|J|² = Φ·Σ_p|ratWeight|² ≤ ΦQ` and
`Σ_χ|S_χ(v)|² = Φ Σ_a|Σ_{z≡a}v|²`), giving `≤ H_K·s·√Q·‖v‖·(5√N/Q + 1) ≤ H_K s‖v‖(5√N + N^{δ₁/2})`
since `Q ≤ N^{δ₁}/(2K+L₀+2) ≤ N^{δ₁}`.

This is how the cross terms `W(β̃,δ)` are handled through Proposition 17.2's power saving `s`
(`AREA7_ROUTE_LEAD.md` §2.2 (A7)). -/
theorem charRegionLow_split_le : ∃ C : ℝ, 0 < C ∧
  ∀ {Pa : Work.FITop.Params} {X K L₀ : ℕ} {δ₁ s : ℝ} (u v : GaussianInt → ℂ),
    1 ≤ X → 1 ≤ K → 0 < δ₁ → 0 ≤ s →
    (∀ (Q : ℕ) [NeZero Q] (k : ℤ) (χ : AddChar (Additive (Work.FIArea7.GaussUnit Q)) ℂ),
        (Q:ℝ) * (2 * (K:ℝ) + (L₀:ℝ) + 2) ≤ Pa.N ^ δ₁ → |(k:ℝ)| ≤ 2 * K →
        ‖Work.FIArea7.uniSChar Pa Q (fun _ => 1) u k χ‖ ≤ s) →
    ‖Work.FIArea7.charRegionLow6 Pa X K L₀ δ₁ (u + v) (fun _ => 1)‖
      ≤ ‖Work.FIArea7.charRegionLow6 Pa X K L₀ δ₁ u (fun _ => 1)‖
        + ‖Work.FIArea7.charRegionLow6 Pa X K L₀ δ₁ v (fun _ => 1)‖
        + C * (Real.log ((K:ℝ) + 2)) ^ 2 * ((X:ℝ) * (1 + Real.log ((Work.FIArea7.uniB Pa : ℝ) + 2)))
            * s * Real.sqrt (∑ z ∈ Work.FIPlan.gBox (Work.FITop.radN Pa), ‖v z‖ ^ 2)
            * (5 * Real.sqrt Pa.N + Pa.N ^ (δ₁ / 2)) := by
  refine ⟨1000000, by norm_num, ?_⟩
  intro Pa X K L₀ δ₁ s u v hX hK hδ₁ hs hhyp
  set E2 : ℝ := ∑ z ∈ Work.FIPlan.gBox (Work.FITop.radN Pa), ‖v z‖ ^ 2 with hE2
  have hsqrtN0 : 0 ≤ Real.sqrt Pa.N := Real.sqrt_nonneg _
  have hNpow0 : 0 ≤ Pa.N ^ (δ₁ / 2) := Real.rpow_nonneg (by linarith [Pa.hN1]) _
  have hX0 : 0 ≤ (X:ℝ) := Nat.cast_nonneg _
  have hE2sq : 0 ≤ Real.sqrt E2 := Real.sqrt_nonneg _
  have hC0 : 0 ≤ Work.FIArea7.uniH K * (2 * s) * Real.sqrt E2 :=
    mul_nonneg (mul_nonneg (Work.FIArea7.uniH_nonneg K) (by linarith)) hE2sq
  set CT : ℂ := ∑ p ∈ Work.FIArea7.charRegionLowFinset Pa X K L₀ δ₁,
      Work.FIArea7.uniCharTermCross Pa p.1 p.2 (fun _ => (1:ℤ)) u v K with hCT
  have htri : ‖Work.FIArea7.charRegionLow6 Pa X K L₀ δ₁ (u + v) (fun _ => (1:ℤ))‖
      ≤ ‖Work.FIArea7.charRegionLow6 Pa X K L₀ δ₁ u (fun _ => (1:ℤ))‖
        + ‖Work.FIArea7.charRegionLow6 Pa X K L₀ δ₁ v (fun _ => (1:ℤ))‖
        + ‖2 * CT‖ := by
    rw [Work.FIArea7.charRegionLow6_add Pa X K L₀ δ₁ (fun _ => (1:ℤ)) u v, hCT]
    calc ‖Work.FIArea7.charRegionLow6 Pa X K L₀ δ₁ u (fun _ => (1:ℤ))
            + Work.FIArea7.charRegionLow6 Pa X K L₀ δ₁ v (fun _ => (1:ℤ))
            + 2 * ∑ p ∈ Work.FIArea7.charRegionLowFinset Pa X K L₀ δ₁,
                Work.FIArea7.uniCharTermCross Pa p.1 p.2 (fun _ => (1:ℤ)) u v K‖
        ≤ ‖Work.FIArea7.charRegionLow6 Pa X K L₀ δ₁ u (fun _ => (1:ℤ))
            + Work.FIArea7.charRegionLow6 Pa X K L₀ δ₁ v (fun _ => (1:ℤ))‖
          + ‖2 * ∑ p ∈ Work.FIArea7.charRegionLowFinset Pa X K L₀ δ₁,
                Work.FIArea7.uniCharTermCross Pa p.1 p.2 (fun _ => (1:ℤ)) u v K‖ := norm_add_le _ _
      _ ≤ (‖Work.FIArea7.charRegionLow6 Pa X K L₀ δ₁ u (fun _ => (1:ℤ))‖
            + ‖Work.FIArea7.charRegionLow6 Pa X K L₀ δ₁ v (fun _ => (1:ℤ))‖)
          + ‖2 * ∑ p ∈ Work.FIArea7.charRegionLowFinset Pa X K L₀ δ₁,
                Work.FIArea7.uniCharTermCross Pa p.1 p.2 (fun _ => (1:ℤ)) u v K‖ :=
          add_le_add (norm_add_le _ _) le_rfl
  have hSbound : ‖2 * CT‖ ≤ 2 * (Work.FIArea7.uniH K * (2 * s) * Real.sqrt E2
        * (20 * (X:ℝ) * Real.log ((Work.FIArea7.uniB Pa : ℝ) + 2)
            * (Real.sqrt Pa.N + Pa.N ^ (δ₁ / 2)))) := by
    rw [norm_mul, show ‖(2:ℂ)‖ = 2 from by norm_num]
    refine mul_le_mul_of_nonneg_left ?_ (by norm_num)
    rw [hCT]
    calc ‖∑ p ∈ Work.FIArea7.charRegionLowFinset Pa X K L₀ δ₁,
            Work.FIArea7.uniCharTermCross Pa p.1 p.2 (fun _ => (1:ℤ)) u v K‖
        ≤ ∑ p ∈ Work.FIArea7.charRegionLowFinset Pa X K L₀ δ₁,
            ((1 / (p.1 : ℝ)) * Work.FIArea7.uniH K * (2 * s)
              * ((15 * Real.sqrt Pa.N / Real.sqrt (4 * (p.1 : ℝ) * (p.2 : ℝ))
                  + 2 * Real.sqrt (4 * (p.1 : ℝ) * (p.2 : ℝ))) * Real.sqrt E2)) := by
          refine le_trans (norm_sum_le _ _) (Finset.sum_le_sum fun p hp => ?_)
          exact termBound Pa X K L₀ δ₁ s u v hX hK hs hhyp p hp
      _ = Work.FIArea7.uniH K * (2 * s) * Real.sqrt E2
            * ∑ p ∈ Work.FIArea7.charRegionLowFinset Pa X K L₀ δ₁,
                (1 / (p.1 : ℝ)) * (15 * Real.sqrt Pa.N / Real.sqrt (4 * (p.1 : ℝ) * (p.2 : ℝ))
                  + 2 * Real.sqrt (4 * (p.1 : ℝ) * (p.2 : ℝ))) := by
          rw [Finset.mul_sum]
          exact Finset.sum_congr rfl (fun p _ => by ring)
      _ ≤ Work.FIArea7.uniH K * (2 * s) * Real.sqrt E2
            * (20 * (X:ℝ) * Real.log ((Work.FIArea7.uniB Pa : ℝ) + 2)
                * (Real.sqrt Pa.N + Pa.N ^ (δ₁ / 2))) :=
          mul_le_mul_of_nonneg_left (regionLowSplitWeightSum Pa X K L₀ δ₁ hX hK) hC0
  have hstep : 2 * (Work.FIArea7.uniH K * (2 * s) * Real.sqrt E2
        * (20 * (X:ℝ) * Real.log ((Work.FIArea7.uniB Pa : ℝ) + 2)
            * (Real.sqrt Pa.N + Pa.N ^ (δ₁ / 2))))
      ≤ 1000000 * (Real.log ((K:ℝ) + 2)) ^ 2
          * ((X:ℝ) * (1 + Real.log ((Work.FIArea7.uniB Pa : ℝ) + 2)))
          * s * Real.sqrt E2 * (5 * Real.sqrt Pa.N + Pa.N ^ (δ₁ / 2)) := by
    have hlogB0 : 0 ≤ Real.log ((Work.FIArea7.uniB Pa : ℝ) + 2) := Real.log_nonneg (by
      have : (0:ℝ) ≤ (Work.FIArea7.uniB Pa : ℝ) := Nat.cast_nonneg _
      linarith)
    have hlogK1 : 1 ≤ Real.log ((K:ℝ) + 2) := by
      have h3 : (3:ℝ) ≤ (K:ℝ) + 2 := by
        have : (1:ℝ) ≤ (K:ℝ) := by exact_mod_cast hK
        linarith
      have h1 : 1 ≤ Real.log 3 := by
        have h := Real.log_le_log (Real.exp_pos 1) (le_of_lt Real.exp_one_lt_three)
        rwa [Real.log_exp] at h
      exact le_trans h1 (Real.log_le_log (by norm_num) h3)
    have huniH : Work.FIArea7.uniH K ≤ 25 * Real.log ((K:ℝ) + 2) := uniH_le_log K hK
    have hlogKle : Real.log ((K:ℝ) + 2) ≤ (Real.log ((K:ℝ) + 2)) ^ 2 := by
      nlinarith [hlogK1]
    have hUL : 80 * Work.FIArea7.uniH K ≤ 1000000 * (Real.log ((K:ℝ) + 2))^2 := by
      have h1 : 80 * Work.FIArea7.uniH K ≤ 80 * (25 * Real.log ((K:ℝ) + 2)) :=
        mul_le_mul_of_nonneg_left huniH (by norm_num)
      have h2 : 80 * (25 * Real.log ((K:ℝ) + 2)) ≤ 2000 * (Real.log ((K:ℝ) + 2))^2 := by
        have h3 : 25 * Real.log ((K:ℝ) + 2) ≤ 25 * (Real.log ((K:ℝ) + 2))^2 :=
          mul_le_mul_of_nonneg_left hlogKle (by norm_num)
        linarith
      have h4 : (2000:ℝ) * (Real.log ((K:ℝ) + 2))^2
          ≤ 1000000 * (Real.log ((K:ℝ) + 2))^2 := by
        have := sq_nonneg (Real.log ((K:ℝ) + 2)); linarith
      linarith
    have hYle : Real.log ((Work.FIArea7.uniB Pa : ℝ) + 2)
          * (Real.sqrt Pa.N + Pa.N ^ (δ₁ / 2))
        ≤ (1 + Real.log ((Work.FIArea7.uniB Pa : ℝ) + 2))
          * (5 * Real.sqrt Pa.N + Pa.N ^ (δ₁ / 2)) := by
      refine mul_le_mul (by linarith) (by linarith) (by linarith) (by linarith)
    set P : ℝ := s * Real.sqrt E2 with hP
    set Q : ℝ := (X:ℝ) * (Real.log ((Work.FIArea7.uniB Pa : ℝ) + 2)
        * (Real.sqrt Pa.N + Pa.N ^ (δ₁ / 2))) with hQ
    set R : ℝ := (X:ℝ) * ((1 + Real.log ((Work.FIArea7.uniB Pa : ℝ) + 2))
        * (5 * Real.sqrt Pa.N + Pa.N ^ (δ₁ / 2))) with hR
    have hP0 : 0 ≤ P := by rw [hP]; exact mul_nonneg hs hE2sq
    have hQ0 : 0 ≤ Q := by
      rw [hQ]; exact mul_nonneg hX0 (mul_nonneg hlogB0 (by linarith))
    have hQR : Q ≤ R := by rw [hQ, hR]; exact mul_le_mul_of_nonneg_left hYle hX0
    have hLHS : 2 * (Work.FIArea7.uniH K * (2 * s) * Real.sqrt E2
          * (20 * (X:ℝ) * Real.log ((Work.FIArea7.uniB Pa : ℝ) + 2)
              * (Real.sqrt Pa.N + Pa.N ^ (δ₁ / 2))))
        = 80 * Work.FIArea7.uniH K * P * Q := by rw [hP, hQ]; ring
    rw [hLHS]
    calc 80 * Work.FIArea7.uniH K * P * Q
        ≤ (1000000 * (Real.log ((K:ℝ) + 2))^2 * P) * R :=
          mul_le_mul (mul_le_mul_of_nonneg_right hUL hP0) hQR hQ0
            (mul_nonneg (mul_nonneg (by norm_num) (sq_nonneg _)) hP0)
      _ = 1000000 * (Real.log ((K:ℝ) + 2)) ^ 2
          * ((X:ℝ) * (1 + Real.log ((Work.FIArea7.uniB Pa : ℝ) + 2)))
          * s * Real.sqrt E2 * (5 * Real.sqrt Pa.N + Pa.N ^ (δ₁ / 2)) := by rw [hP, hR]; ring
  linarith [htri, hSbound, hstep]

end

end Work.FIArea7
