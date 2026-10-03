import Mathlib
import Submission.Work.FIArea6.TauPieces.TsumHeartDefs
import Submission.Work.FIArea6.TsumMellinRepLocal
import Submission.Work.FIArea6Road.tau_sq_le_d4
import Submission.Work.FITop3.Defs3
import Submission.Work.FIArea6.S16.truncation_regroup
import Submission.Work.FIArea6Road.ZsfunBohrMean
import Submission.Work.FIArea6Road.ZsfunWitnessL1Key

open Finset
open scoped BigOperators

namespace Work.FIArea6Road

open Work.FIArea5.S16Hecke

/-- Pointwise size bound for the Möbius-twisted Hecke coefficients: `‖c(n)‖ ≤ 4τ(n)²`. -/
lemma norm_tcoef_le_tauSq_aux (Pa : Work.FITop.Params) (chi : GaussianInt → ℂ) (m : ℤ)
    (hchi : ∀ z : GaussianInt, ‖chi z‖ ≤ 1) (n : ℕ) :
    ‖Work.FIArea6.TauPieces.tcoef Pa chi m n‖ ≤ 4 * ((n.divisors.card : ℝ)) ^ 2 := by
  rcases Nat.eq_zero_or_pos n with hn | hn
  · subst hn
    simp [Work.FIArea6.TauPieces.tcoef, Nat.divisors_zero]
  · have hn1 : 1 ≤ n := hn
    by_cases hP : Work.FIArea6Hecke.NoSmallPrimesNat Pa n
    · rw [Work.FIArea6.TauPieces.tcoef, if_pos hP]
      have hlam : ‖Work.FIArea5.S16Hecke.heckeLam chi m n‖ ≤ 4 * (n.divisors.card : ℝ) :=
        Work.FIArea5.S16Hecke.heckeLam_bound chi m hchi hn1
      have hmu : ‖(ArithmeticFunction.moebius n : ℂ)‖ ≤ 1 := Work.FITop3.norm_moebius_le_one n
      have hgam : ‖(Work.FIPlan.gammaTrunc Pa.C n : ℂ)‖ ≤ (n.divisors.card : ℝ) := by
        rw [Complex.norm_real, Real.norm_eq_abs]
        exact Work.FITop3.abs_gammaTrunc_le Pa.C n
      rw [norm_mul, norm_mul]
      calc ‖Work.FIArea5.S16Hecke.heckeLam chi m n‖ * ‖(ArithmeticFunction.moebius n : ℂ)‖
              * ‖(Work.FIPlan.gammaTrunc Pa.C n : ℂ)‖
          ≤ (4 * (n.divisors.card : ℝ)) * 1 * (n.divisors.card : ℝ) :=
            mul_le_mul (mul_le_mul hlam hmu (norm_nonneg _) (by positivity)) hgam
              (norm_nonneg _) (by positivity)
        _ = 4 * ((n.divisors.card : ℝ)) ^ 2 := by ring
    · rw [Work.FIArea6.TauPieces.tcoef, if_neg hP, norm_zero]
      positivity

/-- The `L¹` bound for the coefficients of `Zsfun`: `Σ ‖c(n)‖ n^{-σ} ≤ 4(1 + 1/(σ-1))^4`. -/
theorem ZsfunL1BoundMine (Pa : Work.FITop.Params) (chi : GaussianInt → ℂ) (m : ℤ)
    (hchi : ∀ z : GaussianInt, ‖chi z‖ ≤ 1) {σ : ℝ} (hσ : 1 < σ) :
    (∑' n : ℕ, ‖Work.FIArea6.TauPieces.tcoef Pa chi m n‖ * (n : ℝ) ^ (-σ))
      ≤ 4 * (1 + 1 / (σ - 1)) ^ (4 : ℕ) := by
  have hkey := ZsfunWitnessL1Key hσ
  have hpoint : ∀ n : ℕ, ‖Work.FIArea6.TauPieces.tcoef Pa chi m n‖ * (n : ℝ) ^ (-σ)
      ≤ 4 * (((n.divisors.card : ℝ)) ^ 2 * (n : ℝ) ^ (-σ)) := by
    intro n
    have h1 := norm_tcoef_le_tauSq_aux Pa chi m hchi n
    have h2 : (0 : ℝ) ≤ (n : ℝ) ^ (-σ) := Real.rpow_nonneg (Nat.cast_nonneg n) _
    calc ‖Work.FIArea6.TauPieces.tcoef Pa chi m n‖ * (n : ℝ) ^ (-σ)
        ≤ (4 * ((n.divisors.card : ℝ)) ^ 2) * (n : ℝ) ^ (-σ) :=
          mul_le_mul_of_nonneg_right h1 h2
      _ = 4 * (((n.divisors.card : ℝ)) ^ 2 * (n : ℝ) ^ (-σ)) := by ring
  have hmaj : Summable (fun n : ℕ => 4 * (((n.divisors.card : ℝ)) ^ 2 * (n : ℝ) ^ (-σ))) :=
    (Work.FIArea6.S16.summable_card_divisors_sq_mul_rpow_neg hσ).mul_left 4
  have hsum : Summable (fun n : ℕ =>
      ‖Work.FIArea6.TauPieces.tcoef Pa chi m n‖ * (n : ℝ) ^ (-σ)) :=
    Summable.of_nonneg_of_le (fun n => by positivity) hpoint hmaj
  calc (∑' n : ℕ, ‖Work.FIArea6.TauPieces.tcoef Pa chi m n‖ * (n : ℝ) ^ (-σ))
      ≤ ∑' n : ℕ, 4 * (((n.divisors.card : ℝ)) ^ 2 * (n : ℝ) ^ (-σ)) :=
        Summable.tsum_le_tsum hpoint hsum hmaj
    _ = 4 * (∑' n : ℕ, ((n.divisors.card : ℝ)) ^ 2 * (n : ℝ) ^ (-σ)) := tsum_mul_left
    _ ≤ 4 * (1 + 1 / (σ - 1)) ^ (4 : ℕ) :=
        mul_le_mul_of_nonneg_left hkey (by norm_num)

/-- **Right-edge witness for `Zsfun`** (own copy, using `ZsfunL1BoundMine`). -/
theorem ZsfunRightEdgeWitnessMine :
    ∃ K₁ : ℝ, 0 < K₁ ∧
    ∀ (Pa : Work.FITop.Params) (chi : GaussianInt → ℂ) (m : ℤ) (d : ℕ),
      Work.FIArea5.S16Hecke.IsCharMod4dStrict d chi →
      (∀ z : GaussianInt, ‖chi z‖ ≤ 1) →
      |(m : ℝ)| ≤ 4 * Real.exp (Real.sqrt (Real.log Pa.N)) →
      100 ≤ Real.log Pa.N →
      ∃ s : ℂ, 1 < s.re ∧ s.re ≤ 1 + 1 / Real.log Pa.N ∧ s.re ≤ 2 ∧
        |s.im| ≤ K₁ * ((Real.log Pa.N) ^ (4 : ℕ) + 1) ∧
        (1 : ℝ) / 2 ≤ ‖Work.FIArea6.TauPieces.Zsfun Pa chi m s‖ := by
  refine ⟨8192, by norm_num, ?_⟩
  intro Pa chi m d hstr hchibd hm hlogN
  have hlogNpos : 0 < Real.log Pa.N := by linarith
  have hlogN1 : 1 ≤ Real.log Pa.N := by linarith
  set σ : ℝ := 1 + 1 / Real.log Pa.N with hσdef
  set T : ℝ := 8192 * (Real.log Pa.N) ^ (4 : ℕ) with hTdef
  have hσ1 : 1 < σ := by
    rw [hσdef]; have := one_div_pos.mpr hlogNpos; linarith
  have hσ2 : σ ≤ 1 + 1 / Real.log Pa.N := le_of_eq hσdef
  have hσ3 : σ ≤ 2 := by
    rw [hσdef]
    have hle : 1 / Real.log Pa.N ≤ 1 := by rw [div_le_one hlogNpos]; linarith
    linarith
  have hinv : 1 / (σ - 1) = Real.log Pa.N := by
    rw [hσdef]; field_simp; ring
  have hTpos : 0 < T := by rw [hTdef]; positivity
  have hchi1 : chi 1 = 1 := hstr.1.1
  have htcoef1 : Work.FIArea6.TauPieces.tcoef Pa chi m 1 = 1 := by
    rw [Work.FIArea6.TauPieces.tcoef]
    have hns : Work.FIArea6Hecke.NoSmallPrimesNat Pa 1 := by
      intro q hq hqP hdvd
      have h1 : q ≤ 1 := Nat.le_of_dvd (by norm_num : 0 < 1) hdvd
      have h2 : 2 ≤ q := hq.two_le
      omega
    rw [if_pos hns, Work.FIArea5.S16Hecke.heckeLam_one, hchi1,
      ArithmeticFunction.moebius_apply_one]
    have hg : Work.FIPlan.gammaTrunc Pa.C 1 = 1 := by
      rw [Work.FIPlan.gammaTrunc, Nat.divisors_one, Finset.filter_singleton]
      rw [if_pos (by simpa using Pa.hC1 : (((1 : ℕ) : ℝ)) ≤ Pa.C),
        Finset.sum_singleton, ArithmeticFunction.moebius_apply_one]
      norm_num
    rw [hg]; norm_num
  have hsumm := Work.FIArea6.Trunc.summable_norm_tcoef_mul_rpow_neg Pa chi m hchibd hσ1
  have hL1 := ZsfunL1BoundMine Pa chi m hchibd hσ1
  have hS : (∑' n : ℕ, ‖Work.FIArea6.TauPieces.tcoef Pa chi m n‖ * (n : ℝ) ^ (-σ))
      ≤ 4 * (1 + Real.log Pa.N) ^ (4 : ℕ) := by
    rw [← hinv]; exact hL1
  have hmean := ZsfunBohrMean (a := Work.FIArea6.TauPieces.tcoef Pa chi m) htcoef1 hσ1 hTpos hsumm
  have hnum : (1 : ℝ) / 2 < 1 - 2 * (∑' n : ℕ,
      ‖Work.FIArea6.TauPieces.tcoef Pa chi m n‖ * (n : ℝ) ^ (-σ)) / (T * Real.log 2) := by
    have hlog2 : (1 : ℝ) / 16 ≤ Real.log 2 := by linarith [Real.log_two_gt_d9]
    have hlog2pos : 0 < Real.log 2 := by linarith
    have hL4 : (0 : ℝ) ≤ (Real.log Pa.N) ^ (4 : ℕ) := pow_nonneg hlogNpos.le 4
    have hINN : (0 : ℝ) ≤ 1 + Real.log Pa.N := by linarith
    have h16 : (1 + Real.log Pa.N) ^ (4 : ℕ) ≤ 16 * (Real.log Pa.N) ^ (4 : ℕ) := by
      have h2 : 1 + Real.log Pa.N ≤ 2 * Real.log Pa.N := by linarith
      calc (1 + Real.log Pa.N) ^ (4:ℕ) ≤ (2 * Real.log Pa.N) ^ (4:ℕ) :=
            pow_le_pow_left₀ hINN h2 4
        _ = 16 * (Real.log Pa.N) ^ (4:ℕ) := by ring
    have hden : 0 < T * Real.log 2 := mul_pos hTpos hlog2pos
    have key : 2 * (∑' n : ℕ, ‖Work.FIArea6.TauPieces.tcoef Pa chi m n‖ * (n : ℝ) ^ (-σ))
        ≤ (1 / 4) * (T * Real.log 2) := by
      have h1 : 2 * (∑' n : ℕ, ‖Work.FIArea6.TauPieces.tcoef Pa chi m n‖ * (n : ℝ) ^ (-σ))
          ≤ 8 * (1 + Real.log Pa.N) ^ (4 : ℕ) := by linarith
      have h2 : 8 * (1 + Real.log Pa.N) ^ (4 : ℕ) ≤ 128 * (Real.log Pa.N) ^ (4 : ℕ) := by
        linarith
      have h3 : (1 / 4 : ℝ) * (T * Real.log 2) = 2048 * Real.log 2 * (Real.log Pa.N) ^ (4:ℕ) := by
        rw [hTdef]; ring
      have h4 : (128 : ℝ) * (Real.log Pa.N) ^ (4:ℕ) ≤ 2048 * Real.log 2 * (Real.log Pa.N) ^ (4:ℕ) := by
        have : (128:ℝ) ≤ 2048 * Real.log 2 := by linarith
        exact mul_le_mul_of_nonneg_right this hL4
      rw [h3]
      linarith
    have hfin : 2 * (∑' n : ℕ, ‖Work.FIArea6.TauPieces.tcoef Pa chi m n‖ * (n : ℝ) ^ (-σ))
        / (T * Real.log 2) ≤ 1 / 4 := by
      rw [div_le_iff₀ hden]; linarith
    linarith
  have hbig : (1 : ℝ) / 2 < ‖(1 / T) * ∫ t in (0 : ℝ)..T,
      Work.FIArea6.TauPieces.Zsfun Pa chi m ((σ : ℂ) + (t : ℂ) * Complex.I)‖ :=
    lt_of_lt_of_le hnum hmean
  have hwit : ∃ t : ℝ, 0 ≤ t ∧ t ≤ T ∧
      (1 : ℝ) / 2 ≤ ‖Work.FIArea6.TauPieces.Zsfun Pa chi m ((σ : ℂ) + (t : ℂ) * Complex.I)‖ := by
    by_contra hcon
    push_neg at hcon
    have hle : ‖∫ t in (0 : ℝ)..T,
        Work.FIArea6.TauPieces.Zsfun Pa chi m ((σ : ℂ) + (t : ℂ) * Complex.I)‖
        ≤ (1 / 2) * T := by
      have hmain := intervalIntegral.norm_integral_le_of_norm_le_const
        (a := (0:ℝ)) (b := T) (C := (1/2 : ℝ))
        (f := fun t : ℝ => Work.FIArea6.TauPieces.Zsfun Pa chi m ((σ : ℂ) + (t : ℂ) * Complex.I))
        ?_
      · simpa [Set.uIoc_of_le hTpos.le, abs_of_nonneg hTpos.le] using hmain
      · intro x hx
        rw [Set.uIoc_of_le hTpos.le] at hx
        exact le_of_lt (hcon x (le_of_lt hx.1) hx.2)
    have h1T : ‖(1 / T : ℂ)‖ = 1 / T := by
      rw [Complex.norm_div]
      simp only [norm_one]
      rw [show ‖((T : ℝ) : ℂ)‖ = T by
          rw [Complex.norm_def, Complex.normSq_ofReal, Real.sqrt_mul_self_eq_abs,
            abs_of_pos hTpos]]
    have hfin2 : ‖(1 / T) * ∫ t in (0 : ℝ)..T,
        Work.FIArea6.TauPieces.Zsfun Pa chi m ((σ : ℂ) + (t : ℂ) * Complex.I)‖ ≤ 1 / 2 := by
      rw [norm_mul, h1T]
      have h2 : (1 / T) * ‖∫ t in (0 : ℝ)..T,
            Work.FIArea6.TauPieces.Zsfun Pa chi m ((σ : ℂ) + (t : ℂ) * Complex.I)‖
          ≤ (1 / T) * ((1 / 2) * T) :=
        mul_le_mul_of_nonneg_left hle (by positivity)
      have h3 : (1 / T) * ((1 / 2) * T) = 1 / 2 := by field_simp
      linarith
    linarith
  obtain ⟨t, ht0, htT, htval⟩ := hwit
  refine ⟨(σ : ℂ) + (t : ℂ) * Complex.I, ?_, ?_, ?_, ?_, ?_⟩
  · simp only [Complex.add_re, Complex.ofReal_re, Complex.mul_re, Complex.ofReal_im,
      Complex.I_re, mul_zero, sub_zero, Complex.I_im, mul_one, add_zero]
    exact hσ1
  · simp only [Complex.add_re, Complex.ofReal_re, Complex.mul_re, Complex.ofReal_im,
      Complex.I_re, mul_zero, sub_zero, Complex.I_im, mul_one, add_zero]
    exact hσ2
  · simp only [Complex.add_re, Complex.ofReal_re, Complex.mul_re, Complex.ofReal_im,
      Complex.I_re, mul_zero, sub_zero, Complex.I_im, mul_one, add_zero]
    exact hσ3
  · simp only [Complex.add_im, Complex.ofReal_im, Complex.mul_im, Complex.ofReal_re,
      Complex.I_im, mul_one, Complex.I_re, mul_zero, add_zero, zero_add]
    have htabs : |t| ≤ T := abs_le.mpr ⟨by linarith, htT⟩
    have hpow1 : (1:ℝ) ≤ (Real.log Pa.N) ^ (4:ℕ) := one_le_pow₀ hlogN1
    calc |t| ≤ T := htabs
      _ = 8192 * (Real.log Pa.N) ^ (4:ℕ) := hTdef
      _ ≤ 8192 * ((Real.log Pa.N) ^ (4:ℕ) + 1) := by linarith
  · exact htval

end Work.FIArea6Road
