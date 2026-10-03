/-
# The bounded-height modulated ball bound, in a form compatible with `ballVarBound`

This is a *verbatim* re-proof of `Work.KMTPlan.A6.ballVarBoundBdd`
(`Submission/Work/KMTPlan/A6/ballVarBoundBdd.lean`) with two changes:

* the four vocabulary declarations of `Submission/Work/KMTPlan/A6/BallVarBoundDefs.lean`
  (`modChar`, `norm_fourier_apply_one`, `enorm_eq_ofReal_norm''`, `eLpNorm_modChar`) are inlined
  here under fresh names (`modCharC`, `norm_fourier_apply_oneC`, `enorm_eq_ofReal_normC`,
  `eLpNorm_modCharC`), and
* every other declaration is renamed with the suffix `C`.

The reason: `BallVarBoundDefs.norm_fourier_apply_one` clashes with
`Submission/Work/KMTPlan/A6/SchwartzLiftSummable.norm_fourier_apply_one`, and the latter is in the
import closure of `Submission.Work.KMTPlan.A6.ballVarBound` — so a file that wants *both* the
height-`0` ball bound and the bounded-height consequence cannot import
`ballVarBoundBdd.lean`.  This module provides the bounded-height consequence without importing
`BallVarBoundDefs`, so that it can be used together with `ballVarBound`.
-/
import Mathlib
import Submission.Work.KMTPlan.A6.BallBoundDefs
import Submission.Work.KMTPlan.A6.MdlTleKer
import Submission.Work.KMTAreas.A7.Tle_varphitildeNt_bounded
import Submission.Work.KMTAreas.A7.lacDilTriVar
import Submission.Work.KMTAreas.A7.bounded_of_eLpNorm_count_lt_top
import Submission.Port.Aesm

namespace Work.KMTPlan.A6

open MeasureTheory Finset
open scoped ENNReal NNReal BigOperators FourierTransform
open Work.Analysis.IonescuWainger Work.KMTAreas.A7

noncomputable section

/-! ## §0.  The inlined vocabulary (renamed copies of `BallVarBoundDefs`) -/

/-- The **window modulation** `M_α v = e(α·)·v`, written with the circle character at the
exponent `-x`. -/
noncomputable def modCharC (α : Work.Analysis.IonescuWainger.Circle) (v : ℤ → ℂ) : ℤ → ℂ :=
  fun x => fourier (T := 1) (-x) α * v x

theorem modCharC_apply (α : Work.Analysis.IonescuWainger.Circle) (v : ℤ → ℂ) (x : ℤ) :
    modCharC α v x = fourier (T := 1) (-x) α * v x := rfl

/-- The character is unitary. -/
theorem norm_fourier_apply_oneC (n : ℤ) (α : Work.Analysis.IonescuWainger.Circle) :
    ‖(fourier (T := 1) n) α‖ = 1 := by
  rw [fourier_apply]
  exact _root_.Circle.norm_coe _

/-- `‖z‖ₑ = ofReal ‖z‖` for a complex number. -/
theorem enorm_eq_ofReal_normC (z : ℂ) : ‖z‖ₑ = ENNReal.ofReal ‖z‖ := by
  rw [enorm_eq_nnnorm, ← ENNReal.ofReal_coe_nnreal]
  congr 1

/-- **Modulating by a circle character does not change the `ℓᵖ`-seminorm.** -/
theorem eLpNorm_modCharC (α : Work.Analysis.IonescuWainger.Circle) (h : ℤ → ℂ) (p : ENNReal) :
    eLpNorm (modCharC α h) p MeasureTheory.Measure.count
      = eLpNorm h p MeasureTheory.Measure.count := by
  rw [← eLpNorm_enorm (hf := by pw_aesm) (f := modCharC α h), ← eLpNorm_enorm (hf := by pw_aesm) (f := h)]
  refine eLpNorm_congr_ae (Filter.Eventually.of_forall fun x => ?_)
  have h1 : ‖(fourier (T := 1) (-x)) α‖ₑ = 1 := by
    rw [enorm_eq_ofReal_normC, norm_fourier_apply_oneC, ENNReal.ofReal_one]
  simp only [modCharC, enorm_mul, h1, one_mul]

/-! ## §1.  Elementary facts about the height-`0` kernel -/

/-- The arithmetic character sum of height `≤ 0` is the constant `1`. -/
theorem TleArChar_zeroC (ρ : ℝ) (j : ℤ) : TleArChar ρ 0 j = 1 := by
  rw [TleArChar, iwArithFreqs_zero, Finset.sum_singleton]
  simp

/-- `Tle ρ 0 ψ` is the convolution with the Fourier coefficients `cw ψ` of `ψ`. -/
theorem Tle_zero_eq_cwC (ρ : ℝ) {ψ : ℝ → ℂ} (hψ : Integrable ψ) (g : ℤ → ℂ) (y : ℤ) :
    Work.KMTAreas.A7.Tle ρ 0 ψ g y = ∑' j : ℤ, cw ψ j * g (y - j) := by
  rw [Tle_eq_convOp_TleKer, convOp]
  refine tsum_congr fun j => ?_
  rw [TleKer_eq_arChar_cw ρ 0 hψ j, TleArChar_zeroC ρ j, one_mul]

/-- The coefficients of the modulated `d`-fold bump are absolutely summable. -/
theorem summable_cw_norm_varphitildeNtC (P : Polynomial ℤ) (d N k : ℕ) (t : ℝ) :
    Summable (fun j : ℤ => ‖cw (Work.KMTAreas.A7.varphitildeNt P d N k t) j‖) := by
  obtain ⟨Cf, hCfpos, hCfdec⟩ := Work.KMTAreas.A7.fourierDecay_varphitildeN d N k
  set M : ℝ := max 1 |Work.KMTAreas.A7.PevalR P ((N : ℝ) * t)| with hM
  set K : ℝ := (2 * M + 1) ^ 2 with hK
  have hM0 : 0 ≤ M := le_trans zero_le_one (le_max_left _ _)
  have hcM : |Work.KMTAreas.A7.PevalR P ((N : ℝ) * t)| ≤ M := le_max_right _ _
  have hdec : ∀ j : ℤ,
      ‖cw (Work.KMTAreas.A7.varphitildeNt P d N k t) j‖
        ≤ Cf * K / (1 + |(j : ℝ)|) ^ 2 := by
    intro j
    rw [Work.KMTAreas.A7.cw_eq_fourierTransform, Work.KMTAreas.A7.fourier_varphitildeNt_eq]
    calc ‖FourierTransform.fourier (Work.KMTAreas.A7.varphitildeN d N k)
            ((j : ℝ) - Work.KMTAreas.A7.PevalR P ((N : ℝ) * t))‖
        ≤ Cf / (1 + |(j : ℝ) - Work.KMTAreas.A7.PevalR P ((N : ℝ) * t)|) ^ 2 := hCfdec _
      _ = Cf * (1 / (1 + |(j : ℝ) - Work.KMTAreas.A7.PevalR P ((N : ℝ) * t)|) ^ 2) :=
          div_eq_mul_one_div _ _
      _ ≤ Cf * (K / (1 + |(j : ℝ)|) ^ 2) := by
          refine mul_le_mul_of_nonneg_left ?_ hCfpos.le
          rw [hK]
          exact Work.KMTAreas.A7.one_div_sq_le_of_abs_sub_le hM0 hcM j
      _ = Cf * K / (1 + |(j : ℝ)|) ^ 2 := (mul_div_assoc _ _ _).symm
  refine Summable.of_nonneg_of_le (fun j => norm_nonneg _) hdec ?_
  exact (by simpa only [mul_one_div] using
    (Work.KMTAreas.A7.summable_one_div_sq_int.mul_left (Cf * K)))

/-! ## §2.  The height decomposition -/

/-- The character identity behind the decomposition: the `j`-dependence of the cross terms is the
difference `-j` of the two frequencies. -/
theorem fourier_neg_mulC (x j : ℤ) (α : Work.Analysis.IonescuWainger.Circle) :
    (fourier (T := 1) (-x)) α * (fourier (T := 1) (-(x - j))) (-α)
      = (fourier (T := 1) (-j)) α := by
  have hpt : ∀ (n : ℤ) (β : Work.Analysis.IonescuWainger.Circle),
      fourier (T := 1) n (-β) = fourier (T := 1) (-n) β := by
    intro n β
    simp only [fourier_apply, smul_neg, neg_smul]
  rw [hpt]
  rw [← fourier_add]
  congr 1
  ring

/-- **The height decomposition of the Ionescu--Wainger multiplier.**  For an integrable symbol
`ψ`, the height-`≤ l` multiplier is the sum, over the arithmetic frequencies
`α ∈ (ℚ/ℤ)_{≤l}`, of the height-`0` multiplier conjugated by the modulation `modCharC α`. -/
theorem Tle_eq_sum_modCharC (ρ : ℝ) (l : ℕ) {ψ : ℝ → ℂ} (hψ : Integrable ψ) (f : ℤ → ℂ) (x : ℤ)
    (hsumm : Summable (fun j : ℤ => cw ψ j * f (x - j))) :
    Work.KMTAreas.A7.Tle ρ l ψ f x
      = ∑ α ∈ iwArithFreqs ρ l,
          modCharC α (Work.KMTAreas.A7.Tle ρ 0 ψ (modCharC (-α) f)) x := by
  classical
  have hsummα : ∀ α : Work.Analysis.IonescuWainger.Circle, Summable (fun j : ℤ =>
      (fourier (T := 1) (-j)) α * (cw ψ j * f (x - j))) := by
    intro α
    refine Summable.of_norm_bounded hsumm.norm (fun j => le_of_eq ?_)
    rw [norm_mul, norm_fourier_apply_oneC, one_mul]
  have hLHS : Work.KMTAreas.A7.Tle ρ l ψ f x
      = ∑' j : ℤ, ∑ α ∈ iwArithFreqs ρ l,
          (fourier (T := 1) (-j)) α * (cw ψ j * f (x - j)) := by
    rw [Tle_eq_convOp_TleKer, convOp]
    refine tsum_congr fun j => ?_
    rw [TleKer_eq_arChar_cw ρ l hψ j, TleArChar, Finset.sum_mul, Finset.sum_mul]
    exact Finset.sum_congr rfl (fun α _ => by ring)
  rw [hLHS, Summable.tsum_finsetSum (s := iwArithFreqs ρ l) (fun α _ => hsummα α)]
  refine Finset.sum_congr rfl (fun α _ => ?_)
  rw [modCharC_apply, Tle_zero_eq_cwC ρ hψ (modCharC (-α) f) x, ← tsum_mul_left]
  refine tsum_congr (fun j => ?_)
  rw [modCharC_apply, ← fourier_neg_mulC x j α]
  ring

/-! ## §3.  The `ℒ²` bound for the sum over the arithmetic frequencies -/

/-- The `ℒ²` version of the height decomposition: the `ℒ²`-seminorm of the variational norm of the
height-`≤ l` family is bounded by the sum of the `ℒ²`-seminorms of the modulated height-`0`
families. -/
theorem eLpNorm_varNorm_Tle_le_sumC (R : NNReal) (hR1 : 1 ≤ R) (ρ : ℝ) (l : ℕ)
    (ψ : ℕ → ℝ → ℂ) (hψ : ∀ n : ℕ, Integrable (ψ n)) (f : ℤ → ℂ)
    (hsumm : ∀ (n : ℕ) (x : ℤ), Summable (fun j : ℤ => cw (ψ n) j * f (x - j))) :
    MeasureTheory.eLpNorm (fun x : ℤ => PointwiseErgodicTheorems.variationalNorm R
        (fun n : ℕ => Work.KMTAreas.A7.Tle ρ l (ψ n) f x)) 2 MeasureTheory.Measure.count
      ≤ ∑ α ∈ iwArithFreqs ρ l, MeasureTheory.eLpNorm (fun x : ℤ =>
            PointwiseErgodicTheorems.variationalNorm R
              (fun n : ℕ => Work.KMTAreas.A7.Tle ρ 0 (ψ n) (modCharC (-α) f) x))
          2 MeasureTheory.Measure.count := by
  have hpt : ∀ x : ℤ, PointwiseErgodicTheorems.variationalNorm R
        (fun n : ℕ => Work.KMTAreas.A7.Tle ρ l (ψ n) f x)
      ≤ ∑ α ∈ iwArithFreqs ρ l, PointwiseErgodicTheorems.variationalNorm R
          (fun n : ℕ => Work.KMTAreas.A7.Tle ρ 0 (ψ n) (modCharC (-α) f) x) := by
    intro x
    have hfun : (fun n : ℕ => Work.KMTAreas.A7.Tle ρ l (ψ n) f x)
        = fun n : ℕ => ∑ α ∈ iwArithFreqs ρ l,
            modCharC α (Work.KMTAreas.A7.Tle ρ 0 (ψ n) (modCharC (-α) f)) x := by
      funext n
      exact Tle_eq_sum_modCharC ρ l (hψ n) f x (hsumm n x)
    rw [hfun]
    refine (variationalNorm_finset_sum_le hR1 (iwArithFreqs ρ l)
      (fun α n => modCharC α (Work.KMTAreas.A7.Tle ρ 0 (ψ n) (modCharC (-α) f)) x)).trans ?_
    refine Finset.sum_le_sum (fun α _ => ?_)
    rw [show (fun n : ℕ => modCharC α (Work.KMTAreas.A7.Tle ρ 0 (ψ n) (modCharC (-α) f)) x)
          = (fourier (T := 1) (-x)) α •
              (fun n : ℕ => Work.KMTAreas.A7.Tle ρ 0 (ψ n) (modCharC (-α) f) x)
        from funext fun n => by simp only [modCharC, Pi.smul_apply, smul_eq_mul]]
    rw [Submission.PointwiseErgodicTheorems.variationalNorm_smul hR1,
      enorm_eq_ofReal_normC, norm_fourier_apply_oneC, ENNReal.ofReal_one, one_mul]
  calc MeasureTheory.eLpNorm (fun x : ℤ => PointwiseErgodicTheorems.variationalNorm R
          (fun n : ℕ => Work.KMTAreas.A7.Tle ρ l (ψ n) f x)) 2 MeasureTheory.Measure.count
      ≤ MeasureTheory.eLpNorm (fun x : ℤ => ∑ α ∈ iwArithFreqs ρ l,
          PointwiseErgodicTheorems.variationalNorm R
            (fun n : ℕ => Work.KMTAreas.A7.Tle ρ 0 (ψ n) (modCharC (-α) f) x))
        2 MeasureTheory.Measure.count :=
        Work.KMTAreas.A7.eLpNorm_mono_ennreal hpt (q := 2)
          (by norm_num) (by norm_num) (μ := MeasureTheory.Measure.count)
    _ ≤ ∑ α ∈ iwArithFreqs ρ l, MeasureTheory.eLpNorm (fun x : ℤ =>
          PointwiseErgodicTheorems.variationalNorm R
            (fun n : ℕ => Work.KMTAreas.A7.Tle ρ 0 (ψ n) (modCharC (-α) f) x))
        2 MeasureTheory.Measure.count :=
        Work.KMTAreas.A7.eLpNorm_finset_sum_le_ennreal (iwArithFreqs ρ l)
          (fun α x => PointwiseErgodicTheorems.variationalNorm R
            (fun n : ℕ => Work.KMTAreas.A7.Tle ρ 0 (ψ n) (modCharC (-α) f) x))
          (q := 2) (by norm_num) (by norm_num) (μ := MeasureTheory.Measure.count)

/-! ## §4.  The bounded-height `ℓ²` variational bound -/

/-- **The modulated bounded-height family is `R`-variationally bounded on `ℓ²`**, deduced from the
height-`0` ball bound `BallZeroBound`. -/
theorem ballVarBoundBddClean (P : Polynomial ℤ) (hd : 2 ≤ P.natDegree) (R : NNReal) (hR : 2 < R)
    (hball : ∀ (Λ : NNReal), 1 < Λ → BallZeroBound P R Λ) :
    ∀ (B : ℕ) (Λ : NNReal), 1 < Λ → ∀ (ρ : ℝ), 0 < ρ → ρ ≤ 1 → ∃ C : ℝ, 0 < C ∧
      ∀ (a : ℕ → NNReal) (l₂ : ℕ), l₂ ≤ B →
        PointwiseErgodicTheorems.Lacunary Λ a → (∀ n : ℕ, 1 ≤ a n) →
        ∀ (t : ℝ), t ∈ Set.Icc (1 / 2 : ℝ) 1 → ∀ h : ℤ → ℂ,
          MeasureTheory.eLpNorm (fun x : ℤ => PointwiseErgodicTheorems.variationalNorm R
            (fun n : ℕ => Work.KMTAreas.A7.Tle ρ l₂
              (Work.KMTPlan.A6.varphitildeNtj P (Nat.floor (a n)) 0 0 t) h x))
            2 MeasureTheory.Measure.count
          ≤ ENNReal.ofReal C * MeasureTheory.eLpNorm h 2 MeasureTheory.Measure.count := by
  intro B Λ hΛ ρ hρ hρ1
  obtain ⟨C₀, hC₀pos, hC₀⟩ := hball Λ hΛ ρ hρ hρ1
  have hR1 : (1 : NNReal) ≤ R := le_trans (by norm_num) (le_of_lt hR)
  refine ⟨max 1 (((iwArithFreqs ρ B).card : ℝ) * C₀),
    lt_of_lt_of_le zero_lt_one (le_max_left _ _), ?_⟩
  intro a l₂ hl₂ ha ha1 t ht h
  by_cases htop : MeasureTheory.eLpNorm h 2 MeasureTheory.Measure.count = ⊤
  · rw [htop, ENNReal.mul_top
      (ENNReal.ofReal_ne_zero_iff.mpr (lt_of_lt_of_le zero_lt_one (le_max_left _ _)))]
    exact le_top
  · obtain ⟨Bh, hBh⟩ := Work.KMTAreas.A7.bounded_of_eLpNorm_count_lt_top (p := 2)
      (by norm_num) (lt_top_iff_ne_top.mpr htop)
    have hψ : ∀ n : ℕ, MeasureTheory.Integrable
        (Work.KMTPlan.A6.varphitildeNtj P (Nat.floor (a n)) 0 0 t) := by
      intro n
      rw [Work.KMTPlan.A6.varphitildeNtj_zero]
      exact Work.KMTAreas.A7.integrable_varphitildeNt_aux P P.natDegree (Nat.floor (a n)) 0 t
    have hκ : ∀ n : ℕ, Summable (fun j : ℤ =>
        ‖cw (Work.KMTPlan.A6.varphitildeNtj P (Nat.floor (a n)) 0 0 t) j‖) := by
      intro n
      rw [Work.KMTPlan.A6.varphitildeNtj_zero]
      exact summable_cw_norm_varphitildeNtC P P.natDegree (Nat.floor (a n)) 0 t
    have hsumm : ∀ (n : ℕ) (x : ℤ), Summable (fun j : ℤ =>
        cw (Work.KMTPlan.A6.varphitildeNtj P (Nat.floor (a n)) 0 0 t) j * h (x - j)) :=
      fun n x => Work.KMTAreas.A7.summable_mul_of_bounded_ (hκ n) (fun j => hBh (x - j))
    have hcard : (((iwArithFreqs ρ l₂).card : ℝ)) ≤ (((iwArithFreqs ρ B).card : ℝ)) := by
      have hsub := Finset.card_le_card
        (Work.Analysis.IonescuWainger.iwArithFreqs_mono hρ hρ1 hl₂)
      exact_mod_cast hsub
    have hstep1 : (∑ α ∈ iwArithFreqs ρ l₂, MeasureTheory.eLpNorm (fun x : ℤ =>
          PointwiseErgodicTheorems.variationalNorm R
            (fun n : ℕ => Work.KMTAreas.A7.Tle ρ 0
              (Work.KMTPlan.A6.varphitildeNtj P (Nat.floor (a n)) 0 0 t) (modCharC (-α) h) x))
          2 MeasureTheory.Measure.count)
        ≤ ∑ α ∈ iwArithFreqs ρ l₂,
            ENNReal.ofReal C₀ * MeasureTheory.eLpNorm (modCharC (-α) h)
              2 MeasureTheory.Measure.count :=
      Finset.sum_le_sum (fun α _ => hC₀ a ha ha1 t ht (modCharC (-α) h))
    have hstep2 : (∑ α ∈ iwArithFreqs ρ l₂,
          ENNReal.ofReal C₀ * MeasureTheory.eLpNorm (modCharC (-α) h) 2 MeasureTheory.Measure.count)
        = ∑ α ∈ iwArithFreqs ρ l₂,
            ENNReal.ofReal C₀ * MeasureTheory.eLpNorm h 2 MeasureTheory.Measure.count := by
      refine Finset.sum_congr rfl (fun α _ => ?_)
      rw [eLpNorm_modCharC]
    have hstep3 : (∑ α ∈ iwArithFreqs ρ l₂,
          ENNReal.ofReal C₀ * MeasureTheory.eLpNorm h 2 MeasureTheory.Measure.count)
        = ENNReal.ofReal (((iwArithFreqs ρ l₂).card : ℝ) * C₀)
            * MeasureTheory.eLpNorm h 2 MeasureTheory.Measure.count := by
      rw [Finset.sum_const, nsmul_eq_mul, ← ENNReal.ofReal_natCast, ← mul_assoc,
        ← ENNReal.ofReal_mul (Nat.cast_nonneg _)]
    have hstep4 : ENNReal.ofReal (((iwArithFreqs ρ l₂).card : ℝ) * C₀)
          * MeasureTheory.eLpNorm h 2 MeasureTheory.Measure.count
        ≤ ENNReal.ofReal (max 1 (((iwArithFreqs ρ B).card : ℝ) * C₀))
          * MeasureTheory.eLpNorm h 2 MeasureTheory.Measure.count := by
      refine mul_le_mul' ?_ le_rfl
      refine ENNReal.ofReal_le_ofReal ?_
      exact le_trans (mul_le_mul_of_nonneg_right hcard hC₀pos.le) (le_max_right _ _)
    refine le_trans (eLpNorm_varNorm_Tle_le_sumC R hR1 ρ l₂
      (fun n : ℕ => Work.KMTPlan.A6.varphitildeNtj P (Nat.floor (a n)) 0 0 t)
      hψ h hsumm) ?_
    exact le_trans hstep1 (le_trans (le_of_eq hstep2) (le_trans (le_of_eq hstep3) hstep4))


end

end Work.KMTPlan.A6
