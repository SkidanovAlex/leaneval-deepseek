/-
# `Submission.Work.FIArea7.guard_clashfree_le` — the coprimality-guard removal, clash-free

`Work.FIArea7.uniModeSum` carries the guard `(z₁,z₂) = 1` which the §16 character expansion
(`Work.FIArea7.section16_omegaDetect_expansion`) does not; `Work.FIArea7.uniModeSumFree` is the
same sum with the guard dropped (the `unitInd` factors are kept).  This file proves the sharp
estimate

  `‖uniModeSum − uniModeSumFree‖ ≤ C·(Pz⁻¹ + X⁻¹)·N²·log (N+2)`,

the same statement as `uniModeSum_sub_free_sharp`, but with an import closure that does **not**
contain the module `Submission.Work.FIArea7.sum_inv_abs_evenFreq_le`: that module redeclares
`Work.FIArea7.sum_inv_abs_evenFreq_le`, which `Work.FIArea7.WUniOmega6Pull6CharLow_aux` (needed by
`charRegionLowSharp_le`) also declares, so the two cannot be imported together (NOTES.md §59.16).
Here the frequency weight is taken from `WUniOmega6Pull6CharLow_aux` (`≤ 2 log(2K+2) + 2`, a
slightly weaker form of the same bound); this shifts the numerical constant from `60` to `120`
and nothing else.

The proof follows `uniModeSum_sub_free_sharp`: the difference is bounded by the total mode weight
times the weighted non-coprime pair mass (`gcf_norm_uniModeSum_sub_free_le_pairMass`), and the
pair mass by the `θ`-retaining estimate `pairMass_theta_of_pieces`.
-/
import Mathlib
import Submission.Work.FIArea7.WUniOmega6Pull6CharLow_aux
import Submission.Work.FIArea7.UniCharFree6
import Submission.Work.FIArea7.UniMollify6
import Submission.Work.FIArea7.UniPairMassDefs
import Submission.Work.FIArea7.norm_uniModeChar_sub_free_le
import Submission.Work.FIArea7.PiPairDefs
import Submission.Work.FIArea7.PiPairAux
import Submission.Work.FIArea7.PiPairSum
import Submission.Work.FIArea7.pairMass_fibre_le
import Submission.Work.FIArea7CF.card_piDvd_filter_dvd_absDelta_le
import Submission.Work.FIArea7.SumMassDefs
import Submission.Work.FIArea7CF.ThetaPairPieces
import Submission.Work.FIArea7CF.uniMode_pairInner_le_sum_pairPi

set_option maxHeartbeats 2000000

namespace Work.FIArea7

open Finset
open scoped BigOperators

attribute [local instance] Classical.propDecidable

noncomputable section


/-- The weight of the `k`-th mode. -/
def gcf_modeWeight (K : ℕ) (k : ℤ) : ℂ := (1 / |(k : ℝ)| : ℝ)

/-- **The difference is the `(b,e)`-sum of the mode-wise differences.** -/
lemma gcf_uniModeSum_sub_free_eq (Pa : Work.FITop.Params) (X : ℕ) (β : GaussianInt → ℂ)
    (K : ℕ) (ε : GaussianInt → ℤ) :
    uniModeSum Pa X β K ε - uniModeSumFree Pa X β K ε
      = 2 * ∑ b ∈ Finset.Icc 1 (uniB Pa), ∑ e ∈ Finset.Icc 1 X,
          (((ArithmeticFunction.moebius b : ℝ) / (b : ℝ) : ℝ) : ℂ) *
            ((((2 * Real.log 2 + Real.log 4 : ℝ)) : ℂ) *
                (uniModeChar Pa b e β 0 ε - uniModeCharFree Pa b e β 0 ε)
              + ∑ k ∈ evenFreq K, gcf_modeWeight K k *
                  (uniModeChar Pa b e β k ε - uniModeCharFree Pa b e β k ε)) := by
  unfold uniModeSum uniModeSumFree
  rw [← mul_sub]
  congr 1
  rw [← Finset.sum_sub_distrib]
  refine Finset.sum_congr rfl (fun b _ => ?_)
  rw [← Finset.sum_sub_distrib]
  refine Finset.sum_congr rfl (fun e _ => ?_)
  set Sc := ∑ k ∈ evenFreq K, (1 / |(k : ℝ)| : ℂ) * uniModeChar Pa b e β k ε with hSc
  set Sf := ∑ k ∈ evenFreq K, (1 / |(k : ℝ)| : ℂ) * uniModeCharFree Pa b e β k ε with hSf
  have hX : (((ArithmeticFunction.moebius b : ℝ) / (b : ℝ) : ℝ) : ℂ) *
        ((((2 * Real.log 2 + Real.log 4 : ℝ)) : ℂ) * uniModeChar Pa b e β 0 ε + Sc)
      - (((ArithmeticFunction.moebius b : ℝ) / (b : ℝ) : ℝ) : ℂ) *
        ((((2 * Real.log 2 + Real.log 4 : ℝ)) : ℂ) * uniModeCharFree Pa b e β 0 ε + Sf)
      = (((ArithmeticFunction.moebius b : ℝ) / (b : ℝ) : ℝ) : ℂ) *
        ((((2 * Real.log 2 + Real.log 4 : ℝ)) : ℂ) *
            (uniModeChar Pa b e β 0 ε - uniModeCharFree Pa b e β 0 ε) + (Sc - Sf)) := by
    ring
  have hS : Sc - Sf = ∑ k ∈ evenFreq K, gcf_modeWeight K k *
      (uniModeChar Pa b e β k ε - uniModeCharFree Pa b e β k ε) := by
    rw [hSc, hSf, ← Finset.sum_sub_distrib]
    refine Finset.sum_congr rfl (fun k _ => ?_)
    rw [gcf_modeWeight]; push_cast; ring
  rw [hX, hS]

/-- The norm of the Möbius weight: `‖(μ(b)/b : ℂ)‖ ≤ 1/b`. -/
lemma gcf_norm_moebius_weight_le (b : ℕ) :
    ‖(((ArithmeticFunction.moebius b : ℝ) / (b : ℝ) : ℝ) : ℂ)‖ ≤ 1 / (b : ℝ) := by
  rw [Complex.norm_def, Complex.normSq_ofReal, ← sq, Real.sqrt_sq_eq_abs, abs_div,
    abs_of_nonneg (by positivity : (0 : ℝ) ≤ (b : ℝ))]
  rcases eq_or_lt_of_le (Nat.cast_nonneg b : (0 : ℝ) ≤ (b : ℝ)) with h | h
  · rw [← h]; simp
  · rw [div_le_div_iff₀ h h, one_mul]
    have h1 : |((ArithmeticFunction.moebius b : ℤ) : ℝ)| ≤ 1 := by
      rw [← Int.cast_abs]
      exact_mod_cast ArithmeticFunction.abs_moebius_le_one (n := b)
    nlinarith [h1, h]

lemma gcf_norm_ofReal_cast (v : ℝ) : ‖((v : ℂ))‖ = |v| := by
  rw [Complex.norm_def, Complex.normSq_ofReal, ← sq, Real.sqrt_sq_eq_abs]

lemma gcf_norm_gcf_modeWeight (K : ℕ) (k : ℤ) : ‖gcf_modeWeight K k‖ = 1 / |(k : ℝ)| := by
  rw [gcf_modeWeight, gcf_norm_ofReal_cast, abs_of_nonneg (by positivity)]

/-- **The guard-removal difference is bounded by the total mode weight times the weighted
non-coprime pair mass.** -/
lemma gcf_norm_uniModeSum_sub_free_le_pairMass (Pa : Work.FITop.Params) (φ : ℝ) (X : ℕ)
    (β : GaussianInt → ℂ) (K : ℕ) (ε : GaussianInt → ℤ)
    (hβbox : ∀ z : GaussianInt, β z ≠ 0 → Work.FITop3.InPolarBox Pa φ z)
    (hεn : ∀ z : GaussianInt, Work.FITop3.InPolarBox Pa φ z → ‖((ε z : ℤ) : ℂ)‖ = 1) :
    ‖uniModeSum Pa X β K ε - uniModeSumFree Pa X β K ε‖
      ≤ 2 * (((2 * Real.log 2 + Real.log 4 : ℝ)) + ∑ k ∈ evenFreq K, 1 / |(k : ℝ)|)
          * uniMode_pairMass Pa X β := by
  rw [gcf_uniModeSum_sub_free_eq, norm_mul]
  have h2 : ‖(2 : ℂ)‖ = 2 := by norm_num
  rw [h2]
  have hpos1 : (0 : ℝ) ≤ 2 * Real.log 2 + Real.log 4 := by positivity
  have hterm : ∀ b ∈ Finset.Icc 1 (uniB Pa), ∀ e ∈ Finset.Icc 1 X,
      ‖(((ArithmeticFunction.moebius b : ℝ) / (b : ℝ) : ℝ) : ℂ) *
        ((((2 * Real.log 2 + Real.log 4 : ℝ)) : ℂ) *
            (uniModeChar Pa b e β 0 ε - uniModeCharFree Pa b e β 0 ε)
          + ∑ k ∈ evenFreq K, gcf_modeWeight K k *
              (uniModeChar Pa b e β k ε - uniModeCharFree Pa b e β k ε))‖
        ≤ (1 / (b : ℝ)) * (((2 * Real.log 2 + Real.log 4 : ℝ)
              + ∑ k ∈ evenFreq K, 1 / |(k : ℝ)|) * uniMode_pairInner Pa b e β) := by
    intro b hb e he
    rw [norm_mul]
    have hb1 : (1 : ℝ) ≤ (b : ℝ) := by
      have h := (Finset.mem_Icc.mp hb).1
      exact_mod_cast h
    have hμ : ‖(((ArithmeticFunction.moebius b : ℝ) / (b : ℝ) : ℝ) : ℂ)‖ ≤ 1 / (b : ℝ) :=
      gcf_norm_moebius_weight_le b
    have hbr : ‖(((2 * Real.log 2 + Real.log 4 : ℝ)) : ℂ) *
            (uniModeChar Pa b e β 0 ε - uniModeCharFree Pa b e β 0 ε)
          + ∑ k ∈ evenFreq K, gcf_modeWeight K k *
              (uniModeChar Pa b e β k ε - uniModeCharFree Pa b e β k ε)‖
        ≤ ((2 * Real.log 2 + Real.log 4 : ℝ) + ∑ k ∈ evenFreq K, 1 / |(k : ℝ)|)
            * uniMode_pairInner Pa b e β := by
      refine le_trans (norm_add_le _ _) ?_
      have hA : ‖(((2 * Real.log 2 + Real.log 4 : ℝ)) : ℂ) *
            (uniModeChar Pa b e β 0 ε - uniModeCharFree Pa b e β 0 ε)‖
          ≤ (2 * Real.log 2 + Real.log 4 : ℝ) * uniMode_pairInner Pa b e β := by
        rw [norm_mul, gcf_norm_ofReal_cast, abs_of_nonneg hpos1]
        exact mul_le_mul_of_nonneg_left
          (norm_uniModeChar_sub_free_le Pa φ b e β 0 ε hβbox hεn) hpos1
      have hB : ‖∑ k ∈ evenFreq K, gcf_modeWeight K k *
              (uniModeChar Pa b e β k ε - uniModeCharFree Pa b e β k ε)‖
          ≤ (∑ k ∈ evenFreq K, 1 / |(k : ℝ)|) * uniMode_pairInner Pa b e β := by
        refine le_trans (norm_sum_le _ _) ?_
        have hstep : ∀ k ∈ evenFreq K,
            ‖gcf_modeWeight K k *
              (uniModeChar Pa b e β k ε - uniModeCharFree Pa b e β k ε)‖
              ≤ (1 / |(k : ℝ)|) * uniMode_pairInner Pa b e β := by
          intro k _
          rw [norm_mul, gcf_norm_gcf_modeWeight]
          exact mul_le_mul_of_nonneg_left
            (norm_uniModeChar_sub_free_le Pa φ b e β k ε hβbox hεn) (by positivity)
        refine le_trans (Finset.sum_le_sum hstep) ?_
        rw [← Finset.sum_mul]
      have hsum := add_le_add hA hB
      rwa [← add_mul] at hsum
    exact mul_le_mul hμ hbr (norm_nonneg _) (by positivity)
  have hinner : ‖∑ b ∈ Finset.Icc 1 (uniB Pa), ∑ e ∈ Finset.Icc 1 X,
        (((ArithmeticFunction.moebius b : ℝ) / (b : ℝ) : ℝ) : ℂ) *
          ((((2 * Real.log 2 + Real.log 4 : ℝ)) : ℂ) *
              (uniModeChar Pa b e β 0 ε - uniModeCharFree Pa b e β 0 ε)
            + ∑ k ∈ evenFreq K, gcf_modeWeight K k *
                (uniModeChar Pa b e β k ε - uniModeCharFree Pa b e β k ε))‖
      ≤ ((2 * Real.log 2 + Real.log 4 : ℝ) + ∑ k ∈ evenFreq K, 1 / |(k : ℝ)|)
          * uniMode_pairMass Pa X β := by
    refine le_trans (norm_sum_le _ _) ?_
    have hs1 : (∑ b ∈ Finset.Icc 1 (uniB Pa), ∑ e ∈ Finset.Icc 1 X,
          (1 / (b : ℝ)) * (((2 * Real.log 2 + Real.log 4 : ℝ)
              + ∑ k ∈ evenFreq K, 1 / |(k : ℝ)|) * uniMode_pairInner Pa b e β))
        = ((2 * Real.log 2 + Real.log 4 : ℝ) + ∑ k ∈ evenFreq K, 1 / |(k : ℝ)|)
          * uniMode_pairMass Pa X β := by
      rw [uniMode_pairMass, Finset.mul_sum]
      refine Finset.sum_congr rfl (fun b _ => ?_)
      rw [Finset.mul_sum]
      refine Finset.sum_congr rfl (fun e _ => ?_)
      ring
    rw [← hs1]
    refine Finset.sum_le_sum (fun b hb => ?_)
    exact le_trans (norm_sum_le _ _) (Finset.sum_le_sum (fun e he => hterm b hb e he))
  calc 2 * ‖∑ b ∈ Finset.Icc 1 (uniB Pa), ∑ e ∈ Finset.Icc 1 X,
        (((ArithmeticFunction.moebius b : ℝ) / (b : ℝ) : ℝ) : ℂ) *
          ((((2 * Real.log 2 + Real.log 4 : ℝ)) : ℂ) *
              (uniModeChar Pa b e β 0 ε - uniModeCharFree Pa b e β 0 ε)
            + ∑ k ∈ evenFreq K, gcf_modeWeight K k *
                (uniModeChar Pa b e β k ε - uniModeCharFree Pa b e β k ε))‖
      ≤ 2 * ((((2 * Real.log 2 + Real.log 4 : ℝ)) + ∑ k ∈ evenFreq K, 1 / |(k : ℝ)|)
          * uniMode_pairMass Pa X β) := mul_le_mul_of_nonneg_left hinner (by norm_num)
    _ = 2 * (((2 * Real.log 2 + Real.log 4 : ℝ)) + ∑ k ∈ evenFreq K, 1 / |(k : ℝ)|)
          * uniMode_pairMass Pa X β := by ring

/-- `log y ≤ 10·y^{1/10}`. -/
lemma gcf_log_le_rpow10 {y : ℝ} (hy : 0 < y) : Real.log y ≤ 10 * y ^ ((1:ℝ)/10) := by
  calc Real.log y ≤ y ^ ((1:ℝ)/10) / ((1:ℝ)/10) :=
        Real.log_le_rpow_div hy.le (by norm_num : (0:ℝ) < (1:ℝ)/10)
    _ = 10 * y ^ ((1:ℝ)/10) := by rw [div_eq_mul_inv]; ring

/-- `(log (y+2))^5 ≤ 2·10^5·√y` for `1 ≤ y`. -/
lemma gcf_log5_le_sqrt {y : ℝ} (hy : 1 ≤ y) :
    (Real.log (y + 2)) ^ 5 ≤ 200000 * Real.sqrt y := by
  have hy2 : (0:ℝ) < y + 2 := by linarith
  have h1 := gcf_log_le_rpow10 hy2
  have h2 : (Real.log (y+2)) ^ 5 ≤ (10 * (y+2) ^ ((1:ℝ)/10)) ^ 5 :=
    pow_le_pow_left₀ (Real.log_nonneg (by linarith)) h1 5
  have h3 : (10 * (y+2) ^ ((1:ℝ)/10)) ^ 5 ≤ 100000 * Real.sqrt (y+2) := by
    have hb : ((y+2) ^ ((1:ℝ)/10)) ^ (5:ℕ) ≤ Real.sqrt (y+2) := by
      have he : ((y+2) ^ ((1:ℝ)/10)) ^ (5:ℕ) = (y+2) ^ ((1:ℝ)/2) := by
        have h5 : ((1:ℝ)/10 * ((5:ℕ):ℝ)) = 1/2 := by norm_num
        have h6 : ((y+2) ^ ((1:ℝ)/10)) ^ ((5:ℕ):ℝ)
            = (y+2) ^ ((1:ℝ)/10 * ((5:ℕ):ℝ)) := (Real.rpow_mul hy2.le _ _).symm
        rw [← Real.rpow_natCast, h6, h5]
      rw [he, Real.sqrt_eq_rpow]
    calc (10 * (y+2) ^ ((1:ℝ)/10)) ^ 5
        = 10^5 * ((y+2) ^ ((1:ℝ)/10)) ^ 5 := by rw [mul_pow]
      _ ≤ 10^5 * Real.sqrt (y+2) :=
          mul_le_mul_of_nonneg_left hb (by positivity)
      _ = 100000 * Real.sqrt (y+2) := by norm_num
  have h4 : Real.sqrt (y+2) ≤ 2 * Real.sqrt y := by
    rw [show (2:ℝ) * Real.sqrt y = Real.sqrt (4 * y) by
      rw [Real.sqrt_mul (by norm_num : (0:ℝ) ≤ 4)]; norm_num]
    exact Real.sqrt_le_sqrt (by linarith)
  linarith [h2, h3, h4]

theorem guard_clashfree_le :
    ∃ C : ℝ, 0 < C ∧
      ∀ {Pa : Work.FITop.Params} {φ : ℝ} {z0 : GaussianInt} {β : GaussianInt → ℂ},
        Work.FITop4.IsBetaCoeff6 Pa φ z0 β → ∀ (X K : ℕ) (ε : GaussianInt → ℤ),
        1 ≤ X →
        (K : ℝ) ≤ 2 * (X : ℝ) ^ 3 * (Real.log (Pa.N + 2)) ^ 20 →
        (X : ℝ) ^ 9 ≤ Pa.N →
        (∀ z1 z2 : GaussianInt, Work.FITop3.InPolarBox Pa φ z1 →
            Work.FITop3.InPolarBox Pa φ z2 →
            Work.FIArea7.reflSign z1 z2 = ε z1 * ε z2) →
        (((Work.FIPlan.gBox (Work.FITop.radN Pa)).filter (fun z => β z ≠ 0)).card : ℝ)
          ≤ 200 * (Pa.θ ^ 2 * Pa.N + Pa.θ * Real.sqrt Pa.N + 1) →
        (∑ z ∈ Work.FIPlan.gBox (Work.FITop.radN Pa), ‖β z‖ ^ 2)
          ≤ 1000 * (Pa.θ * Pa.N + Real.sqrt Pa.N + 1) * (Real.log (2 + Pa.N)) ^ 3 →
        ‖Work.FIArea7.uniModeSum Pa X β K ε - Work.FIArea7.uniModeSumFree Pa X β K ε‖
          ≤ C * ((Pa.Pz : ℝ)⁻¹ + (X : ℝ)⁻¹) * Pa.N ^ 2 * Real.log (Pa.N + 2) := by
  obtain ⟨C_D, hC_Dpos, hD⟩ := Work.FIArea7.pairMass_theta_of_pieces
    (fun hβ b e hb he => Work.FIArea7.uniMode_pairInner_le_sum_pairPi hβ b e hb he)
    (fun Pa b e β π hb he hπ => Work.FIArea7.pairPi_le_massW_rhoPi' Pa b e β π hb he hπ)
    (fun hβ m => Work.FIArea7.sum_massW_le' hβ m)
  refine ⟨120 * C_D * 1000000000, by positivity, ?_⟩
  intro Pa φ z0 β hβ X K ε hX1 hKu hX9 hε hcard henergy
  have hβbox : ∀ z : GaussianInt, β z ≠ 0 → Work.FITop3.InPolarBox Pa φ z :=
    fun z hz => hβ.support hz
  have hεn : ∀ z : GaussianInt, Work.FITop3.InPolarBox Pa φ z → ‖((ε z : ℤ) : ℂ)‖ = 1 :=
    fun z hz => Work.FIArea7.norm_eps_eq_one hε hz
  have hmain := gcf_norm_uniModeSum_sub_free_le_pairMass Pa φ X β K ε hβbox hεn
  have hpm := hD hβ X hX1 hX9 hcard henergy
  -- basic facts
  have hN1 : (1 : ℝ) ≤ (Pa.N : ℝ) := Pa.hN1
  have hNpos : (0 : ℝ) < (Pa.N : ℝ) := by linarith
  have hX1R : (1 : ℝ) ≤ (X : ℝ) := by exact_mod_cast hX1
  have hPz2 : (2 : ℝ) ≤ (Pa.Pz : ℝ) := by exact_mod_cast Pa.hP2
  set L : ℝ := Real.log (Pa.N + 2) with hLdef
  have hL1 : 1 ≤ L := by
    rw [hLdef]
    have h3 : (3 : ℝ) ≤ Pa.N + 2 := by linarith
    have hlog3 : (1 : ℝ) < Real.log 3 :=
      (Real.lt_log_iff_exp_lt (by norm_num)).mpr Real.exp_one_lt_three
    exact le_trans (le_of_lt hlog3) (Real.log_le_log (by norm_num) h3)
  have hLpos : (0 : ℝ) < L := by linarith
  have hX3N : (X : ℝ) ^ 3 ≤ (Pa.N : ℝ) := by
    have h1 : (X : ℝ) ^ 3 ≤ (X : ℝ) ^ 9 := pow_le_pow_right₀ hX1R (by norm_num)
    linarith
  -- the mode-weight bound Λ ≤ 60 L
  have hLam : ((2 * Real.log 2 + Real.log 4 : ℝ)) + ∑ k ∈ Work.FIArea7.evenFreq K, 1 / |(k : ℝ)|
      ≤ 60 * L := by
    have h1 : (2 * Real.log 2 + Real.log 4 : ℝ) ≤ 4 := by
      have h2 : Real.log 2 ≤ 1 := by
        have := Real.log_le_sub_one_of_pos (by norm_num : (0:ℝ) < 2); linarith
      have h4 : Real.log 4 = 2 * Real.log 2 := by
        rw [show (4:ℝ) = 2^2 by norm_num, Real.log_pow]; push_cast; ring
      rw [h4]; linarith
    have hKlog : Real.log ((K:ℝ)+2) ≤ 24 * L := by
      have hL20 : (1:ℝ) ≤ L^20 := one_le_pow₀ hL1
      have hK0 : (K:ℝ) + 2 ≤ 4 * ((Pa.N:ℝ) + 2) * L ^ 20 := by
        have h1 : (X:ℝ)^3 * L^20 ≤ (Pa.N:ℝ) * L^20 :=
          mul_le_mul_of_nonneg_right hX3N (by positivity)
        nlinarith [hKu, h1, hL20]
      have hK1 : (0:ℝ) < (K:ℝ) + 2 := by positivity
      have h4 : Real.log ((K:ℝ)+2) ≤ Real.log (4 * ((Pa.N:ℝ) + 2) * L ^ 20) :=
        Real.log_le_log hK1 hK0
      have h5 : Real.log (4 * ((Pa.N:ℝ) + 2) * L ^ 20)
          = Real.log 4 + Real.log ((Pa.N:ℝ) + 2) + 20 * Real.log L := by
        have hA : (4 * ((Pa.N:ℝ) + 2) : ℝ) ≠ 0 := by positivity
        have hB : L ^ 20 ≠ 0 := by positivity
        have hC : ((Pa.N:ℝ) + 2) ≠ 0 := by positivity
        rw [Real.log_mul hA hB, Real.log_mul (by norm_num : (4:ℝ) ≠ 0) hC,
          Real.log_pow (x := L) (n := 20)]
        push_cast; ring
      rw [h5, hLdef] at h4
      have h7 : Real.log L ≤ L := by
        have := Real.log_le_sub_one_of_pos hLpos; linarith
      have h8 : Real.log 4 ≤ 2 := by
        have h2' : Real.log 2 ≤ 1 := by
          have := Real.log_le_sub_one_of_pos (by norm_num : (0:ℝ) < 2); linarith
        have h4' : Real.log 4 = 2 * Real.log 2 := by
          rw [show (4:ℝ) = 2^2 by norm_num, Real.log_pow]; push_cast; ring
        rw [h4']; linarith
      linarith
    have h2 : (∑ k ∈ Work.FIArea7.evenFreq K, 1 / |(k : ℝ)|) ≤ 4 + 48 * L := by
      have haux : (∑ k ∈ Work.FIArea7.evenFreq K, 1 / (((|k| : ℤ)) : ℝ))
          ≤ 2 * Real.log (2 * (K:ℝ) + 2) + 2 := Work.FIArea7.sum_inv_abs_evenFreq_le K
      have hEq : (∑ k ∈ Work.FIArea7.evenFreq K, 1 / (((|k| : ℤ)) : ℝ))
          = ∑ k ∈ Work.FIArea7.evenFreq K, 1 / |(k : ℝ)| := by
        refine Finset.sum_congr rfl (fun k _ => ?_)
        rw [Int.cast_abs]
      rw [← hEq]
      have hlog2 : Real.log (2 * (K:ℝ) + 2) ≤ 1 + Real.log ((K:ℝ) + 2) := by
        have h2K : 2 * (K:ℝ) + 2 = 2 * ((K:ℝ) + 1) := by ring
        rw [h2K]
        have hpos : (0:ℝ) < (K:ℝ) + 1 := by positivity
        have hmul := Real.log_mul (by norm_num : (2:ℝ) ≠ 0) (ne_of_gt hpos)
        have hl2 : Real.log 2 ≤ 1 := by
          have := Real.log_le_sub_one_of_pos (by norm_num : (0:ℝ) < 2); linarith
        have hle : Real.log ((K:ℝ) + 1) ≤ Real.log ((K:ℝ) + 2) :=
          Real.log_le_log hpos (by linarith)
        linarith
      linarith
    linarith
  -- θ L^5 is bounded (θ = (log x)^{-A'}, L ≤ 2 log x)
  have hth : Pa.θ * L^5 ≤ 32 := by
    rw [Pa.hθ]
    have hx3 : (3:ℝ) ≤ (Pa.x:ℝ) := by exact_mod_cast Pa.hx
    have hxpos : (0:ℝ) < (Pa.x:ℝ) := by linarith
    have hlogx1 : (1:ℝ) ≤ Real.log (Pa.x:ℝ) :=
      le_of_lt ((Real.lt_log_iff_exp_lt hxpos).mpr (lt_of_lt_of_le Real.exp_one_lt_three hx3))
    have hlogxpos : (0:ℝ) < Real.log (Pa.x:ℝ) := by linarith
    have hNgrowth : (Pa.N:ℝ) + 2 ≤ 2 * (Pa.x:ℝ) := by
      have hB0 : (0:ℝ) < Pa.B := Pa.hB
      have hlogx_le : (Real.log (Pa.x:ℝ)) ^ (-Pa.B) ≤ 1 :=
        Real.rpow_le_one_of_one_le_of_nonpos hlogx1 (by linarith)
      have hsqrt : (Pa.x:ℝ)^((1:ℝ)/2) = Real.sqrt (Pa.x:ℝ) := (Real.sqrt_eq_rpow _).symm
      have hNlt : (Pa.N:ℝ) < Real.sqrt (Pa.x:ℝ) := by
        have h := Pa.hNhi
        rw [hsqrt] at h
        calc (Pa.N:ℝ) < Real.sqrt (Pa.x:ℝ) * (Real.log (Pa.x:ℝ)) ^ (-Pa.B) := h
          _ ≤ Real.sqrt (Pa.x:ℝ) * 1 := by
              apply mul_le_mul_of_nonneg_left hlogx_le (Real.sqrt_nonneg _)
          _ = Real.sqrt (Pa.x:ℝ) := by ring
      have h2 : Real.sqrt (Pa.x:ℝ) + 2 ≤ 2 * (Pa.x:ℝ) := by
        nlinarith [Real.sq_sqrt (le_of_lt hxpos), Real.sqrt_nonneg (Pa.x:ℝ), hx3]
      linarith
    have hLx : L ≤ 2 * Real.log (Pa.x:ℝ) := by
      rw [hLdef]
      have h := Real.log_le_log (by linarith) hNgrowth
      have h2x : Real.log (2 * (Pa.x:ℝ)) = Real.log 2 + Real.log (Pa.x:ℝ) :=
        Real.log_mul (by norm_num) (by linarith)
      rw [h2x] at h
      have hlog2 : Real.log 2 ≤ Real.log (Pa.x:ℝ) := Real.log_le_log (by norm_num) (by linarith)
      linarith
    have hA'5 : (5:ℝ) ≤ Pa.A' := by linarith [Pa.hA', Pa.hA]
    have h5 : (Real.log (Pa.x:ℝ)) ^ (-Pa.A') * (Real.log (Pa.x:ℝ)) ^ ((5:ℝ))
        = (Real.log (Pa.x:ℝ)) ^ (-Pa.A' + 5) := by
      rw [← Real.rpow_add hlogxpos]
    have h6 : (Real.log (Pa.x:ℝ)) ^ (-Pa.A' + 5) ≤ 1 :=
      Real.rpow_le_one_of_one_le_of_nonpos hlogx1 (by linarith)
    have h2 : L^5 ≤ 32 * (Real.log (Pa.x:ℝ))^((5:ℝ)) := by
      have h2' : L^5 ≤ (2 * Real.log (Pa.x:ℝ))^5 := pow_le_pow_left₀ (by linarith) hLx 5
      have h3 : (2 * Real.log (Pa.x:ℝ))^5 = 32 * (Real.log (Pa.x:ℝ))^5 := by ring
      have h4 : (Real.log (Pa.x:ℝ))^((5:ℝ)) = (Real.log (Pa.x:ℝ))^5 := by
        rw [show (5:ℝ) = ((5:ℕ):ℝ) by norm_num, Real.rpow_natCast]
      rw [h4]; linarith [h2', h3]
    nlinarith [h5, h6, h2, Real.rpow_pos_of_pos hlogxpos (-Pa.A')]
  have hL5s : L^5 ≤ 200000 * Real.sqrt (Pa.N:ℝ) := by
    have h := gcf_log5_le_sqrt Pa.hN1
    rw [hLdef]; exact h
  have hsN1 : (1:ℝ) ≤ Real.sqrt (Pa.N:ℝ) := by
    rw [← Real.sqrt_one]; exact Real.sqrt_le_sqrt hN1
  have hsNpos : (0:ℝ) < Real.sqrt (Pa.N:ℝ) := by linarith
  have hXsq : (X:ℝ)^2 ≤ Real.sqrt (Pa.N:ℝ) := by
    have h4 : (X:ℝ)^4 ≤ (Pa.N:ℝ) := by
      have h1 : (X:ℝ)^4 ≤ (X:ℝ)^9 := pow_le_pow_right₀ hX1R (by norm_num)
      linarith [hX9]
    nlinarith [h4, Real.sq_sqrt hNpos.le, Real.sqrt_nonneg (Pa.N:ℝ), sq_nonneg (X:ℝ)]
  have hXleS : (X:ℝ) ≤ Real.sqrt (Pa.N:ℝ) := by nlinarith [hXsq, hX1R]
  -- the numeric core
  set mm : ℝ := min (Pa.Pz:ℝ) (X:ℝ) with hmmdef
  have hmm1 : (1:ℝ) ≤ mm := by rw [hmmdef, min_def]; split_ifs <;> linarith
  have hmm0 : (0:ℝ) < mm := by linarith
  have hmmP : mm ≤ (Pa.Pz:ℝ) := min_le_left _ _
  have hmmX : mm ≤ (X:ℝ) := min_le_right _ _
  have hPzR : (0:ℝ) < (Pa.Pz:ℝ) := by linarith
  have hkey : (Pa.θ * Pa.N + Real.sqrt Pa.N + 1) * L^5
        * ((Pa.N / (Pa.Pz : ℝ) + 1) + (Real.sqrt Pa.N + 1) * (X : ℝ))
        * mm / (Pa.N : ℝ)^2 ≤ 1000000000 := by
    have hAm : (Pa.N / (Pa.Pz:ℝ) + 1 + (Real.sqrt Pa.N + 1) * (X:ℝ)) * mm ≤ 4 * (Pa.N:ℝ) := by
      have h3 : (Pa.N/(Pa.Pz:ℝ)) * mm ≤ (Pa.N:ℝ) := by
        rw [div_mul_eq_mul_div, div_le_iff₀ hPzR]
        nlinarith [hmmP]
      have h4 : (Real.sqrt Pa.N + 1) * (X:ℝ) * mm ≤ 2 * (Pa.N:ℝ) := by
        have hX2 : (X:ℝ) * mm ≤ Real.sqrt (Pa.N:ℝ) := by
          nlinarith [hmmX, hXsq, hmm0, hX1R, sq_nonneg (X:ℝ)]
        have hsq : (Real.sqrt (Pa.N:ℝ))^2 = (Pa.N:ℝ) := Real.sq_sqrt hNpos.le
        have hs0 : (0:ℝ) ≤ Real.sqrt (Pa.N:ℝ) := Real.sqrt_nonneg _
        nlinarith [hX2, hsq, hs0, hsN1]
      nlinarith [h3, h4, le_of_lt hmm0]
    have hkey' : (Pa.θ * Pa.N + Real.sqrt Pa.N + 1) * L^5
        * ((Pa.N / (Pa.Pz : ℝ) + 1) + (Real.sqrt Pa.N + 1) * (X : ℝ)) * mm
        ≤ 4 * (Pa.N:ℝ) * ((Pa.θ * Pa.N + Real.sqrt Pa.N + 1) * L^5) := by
      calc (Pa.θ * Pa.N + Real.sqrt Pa.N + 1) * L^5
            * ((Pa.N / (Pa.Pz : ℝ) + 1) + (Real.sqrt Pa.N + 1) * (X : ℝ)) * mm
          = ((Pa.θ * Pa.N + Real.sqrt Pa.N + 1) * L^5)
            * ((Pa.N / (Pa.Pz : ℝ) + 1 + (Real.sqrt Pa.N + 1) * (X : ℝ)) * mm) := by ring
        _ ≤ ((Pa.θ * Pa.N + Real.sqrt Pa.N + 1) * L^5) * (4 * (Pa.N:ℝ)) :=
            mul_le_mul_of_nonneg_left hAm
              (mul_nonneg (by nlinarith [Pa.hθ0, hN1, hsN1]) (by positivity))
        _ = 4 * (Pa.N:ℝ) * ((Pa.θ * Pa.N + Real.sqrt Pa.N + 1) * L^5) := by ring
    have hL5_3 : L^5 * Real.sqrt (Pa.N:ℝ) * (Pa.N:ℝ) ≤ 200000 * (Pa.N:ℝ)^2 := by
      have hmul : Real.sqrt (Pa.N:ℝ) * Real.sqrt (Pa.N:ℝ) = (Pa.N:ℝ) :=
        Real.mul_self_sqrt hNpos.le
      have hs0 : (0:ℝ) ≤ Real.sqrt (Pa.N:ℝ) := Real.sqrt_nonneg _
      have hN0 : (0:ℝ) ≤ (Pa.N:ℝ) := hNpos.le
      have h1 : L^5 * (Real.sqrt (Pa.N:ℝ) * (Pa.N:ℝ))
          ≤ (200000 * Real.sqrt (Pa.N:ℝ)) * (Real.sqrt (Pa.N:ℝ) * (Pa.N:ℝ)) :=
        mul_le_mul_of_nonneg_right hL5s (mul_nonneg hs0 hN0)
      have h2 : (200000 * Real.sqrt (Pa.N:ℝ)) * (Real.sqrt (Pa.N:ℝ) * (Pa.N:ℝ))
          = 200000 * (Pa.N:ℝ)^2 := by
        calc (200000 * Real.sqrt (Pa.N:ℝ)) * (Real.sqrt (Pa.N:ℝ) * (Pa.N:ℝ))
            = 200000 * (Real.sqrt (Pa.N:ℝ) * Real.sqrt (Pa.N:ℝ)) * (Pa.N:ℝ) := by ring
          _ = 200000 * (Pa.N:ℝ) * (Pa.N:ℝ) := by rw [hmul]
          _ = 200000 * (Pa.N:ℝ)^2 := by ring
      linarith [h1, h2]
    have hθL : Pa.θ * L^5 * (Pa.N:ℝ)^2 ≤ 32 * (Pa.N:ℝ)^2 :=
      mul_le_mul_of_nonneg_right hth (by positivity)
    have hN5 : L^5 * (Pa.N:ℝ) ≤ 200000 * (Pa.N:ℝ)^2 := by
      have hsq : (Real.sqrt (Pa.N:ℝ))^2 = (Pa.N:ℝ) := Real.sq_sqrt hNpos.le
      nlinarith [hL5s, hsN1, hsNpos, hN1, hsq]
    rw [div_le_iff₀ (by positivity : (0:ℝ) < (Pa.N:ℝ)^2)]
    calc (Pa.θ * Pa.N + Real.sqrt Pa.N + 1) * L^5
          * ((Pa.N / (Pa.Pz : ℝ) + 1) + (Real.sqrt Pa.N + 1) * (X : ℝ))
          * mm
        ≤ 4 * (Pa.N:ℝ) * ((Pa.θ * Pa.N + Real.sqrt Pa.N + 1) * L^5) := hkey'
      _ = 4 * (Pa.θ * L^5 * (Pa.N:ℝ)^2) + 4 * (L^5 * Real.sqrt (Pa.N:ℝ) * (Pa.N:ℝ))
            + 4 * (L^5 * (Pa.N:ℝ)) := by ring
      _ ≤ 4 * (32 * (Pa.N:ℝ)^2) + 4 * (200000 * (Pa.N:ℝ)^2)
            + 4 * (200000 * (Pa.N:ℝ)^2) := by linarith [hθL, hL5_3, hN5]
      _ ≤ 1000000000 * (Pa.N:ℝ)^2 := by nlinarith [sq_nonneg (Pa.N:ℝ)]
  have hinv : mm⁻¹ ≤ (Pa.Pz:ℝ)⁻¹ + (X:ℝ)⁻¹ := by
    rcases le_total (Pa.Pz:ℝ) (X:ℝ) with h | h
    · rw [hmmdef, min_eq_left h]
      have h' : (0:ℝ) ≤ (X:ℝ)⁻¹ := inv_nonneg.mpr (Nat.cast_nonneg X)
      linarith
    · rw [hmmdef, min_eq_right h]
      have h' : (0:ℝ) ≤ (Pa.Pz:ℝ)⁻¹ := inv_nonneg.mpr hPzR.le
      linarith
  have h2 : (Pa.θ * Pa.N + Real.sqrt Pa.N + 1) * L^5
      * ((Pa.N / (Pa.Pz : ℝ) + 1) + (Real.sqrt Pa.N + 1) * (X : ℝ))
      ≤ 1000000000 * ((Pa.Pz : ℝ)⁻¹ + (X : ℝ)⁻¹) * (Pa.N:ℝ)^2 := by
    have hkey_iff : (Pa.θ * Pa.N + Real.sqrt Pa.N + 1) * L^5
        * ((Pa.N / (Pa.Pz : ℝ) + 1) + (Real.sqrt Pa.N + 1) * (X : ℝ)) * mm
        ≤ 1000000000 * (Pa.N:ℝ)^2 := by
      have h := hkey
      rwa [div_le_iff₀ (by positivity : (0:ℝ) < (Pa.N:ℝ)^2)] at h
    have hkey'' : (Pa.θ * Pa.N + Real.sqrt Pa.N + 1) * L^5
        * ((Pa.N / (Pa.Pz : ℝ) + 1) + (Real.sqrt Pa.N + 1) * (X : ℝ))
        ≤ 1000000000 * (Pa.N:ℝ)^2 / mm := by
      rw [le_div_iff₀ hmm0]; exact hkey_iff
    calc (Pa.θ * Pa.N + Real.sqrt Pa.N + 1) * L^5
          * ((Pa.N / (Pa.Pz : ℝ) + 1) + (Real.sqrt Pa.N + 1) * (X : ℝ))
        ≤ 1000000000 * (Pa.N:ℝ)^2 / mm := hkey''
      _ = 1000000000 * (Pa.N:ℝ)^2 * mm⁻¹ := by rw [div_eq_mul_inv]
      _ ≤ 1000000000 * (Pa.N:ℝ)^2 * ((Pa.Pz : ℝ)⁻¹ + (X : ℝ)⁻¹) :=
          mul_le_mul_of_nonneg_left hinv (by positivity)
      _ = 1000000000 * ((Pa.Pz : ℝ)⁻¹ + (X : ℝ)⁻¹) * (Pa.N:ℝ)^2 := by ring
  have hm2 : Work.FIArea7.uniMode_pairMass Pa X β
      ≤ C_D * 1000000000 * ((Pa.Pz : ℝ)⁻¹ + (X : ℝ)⁻¹) * (Pa.N:ℝ)^2 := by
    calc Work.FIArea7.uniMode_pairMass Pa X β
        ≤ C_D * (Pa.θ * Pa.N + Real.sqrt Pa.N + 1) * L ^ 5
            * ((Pa.N / (Pa.Pz : ℝ) + 1) + (Real.sqrt Pa.N + 1) * (X : ℝ)) := hpm
      _ = C_D * ((Pa.θ * Pa.N + Real.sqrt Pa.N + 1) * L ^ 5
            * ((Pa.N / (Pa.Pz : ℝ) + 1) + (Real.sqrt Pa.N + 1) * (X : ℝ))) := by ring
      _ ≤ C_D * (1000000000 * ((Pa.Pz : ℝ)⁻¹ + (X : ℝ)⁻¹) * (Pa.N:ℝ)^2) :=
          mul_le_mul_of_nonneg_left h2 (le_of_lt hC_Dpos)
      _ = C_D * 1000000000 * ((Pa.Pz : ℝ)⁻¹ + (X : ℝ)⁻¹) * (Pa.N:ℝ)^2 := by ring
  have hpm_nonneg : (0:ℝ) ≤ Work.FIArea7.uniMode_pairMass Pa X β := by
    rw [Work.FIArea7.uniMode_pairMass]
    apply Finset.sum_nonneg; intro b _
    apply Finset.sum_nonneg; intro e _
    apply mul_nonneg (by positivity)
    rw [Work.FIArea7.uniMode_pairInner]
    apply Finset.sum_nonneg; intro z1 _
    apply Finset.sum_nonneg; intro z2 _
    split_ifs <;> positivity
  calc ‖Work.FIArea7.uniModeSum Pa X β K ε - Work.FIArea7.uniModeSumFree Pa X β K ε‖
      ≤ 2 * ((2 * Real.log 2 + Real.log 4 : ℝ) + ∑ k ∈ Work.FIArea7.evenFreq K, 1 / |(k : ℝ)|)
          * Work.FIArea7.uniMode_pairMass Pa X β := hmain
    _ ≤ 2 * (60 * L) * (C_D * 1000000000 * ((Pa.Pz : ℝ)⁻¹ + (X : ℝ)⁻¹) * (Pa.N:ℝ)^2) := by
        refine mul_le_mul (by linarith [hLam]) hm2 hpm_nonneg (by positivity)
    _ = 120 * C_D * 1000000000 * ((Pa.Pz : ℝ)⁻¹ + (X : ℝ)⁻¹) * Pa.N ^ 2 * Real.log (Pa.N + 2) := by
        rw [hLdef]; ring

end

end Work.FIArea7

