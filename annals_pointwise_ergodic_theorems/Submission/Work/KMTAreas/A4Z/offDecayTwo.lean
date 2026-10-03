
/-
# Off-diagonal decay of the Ionescu--Wainger projections (§5.2 form)

Krause--Mirek--Tao, Lemma `iw-prop`(i), second half (the estimate `(off-decay)`, proved in
Appendix A of the paper), in the vocabulary of the `A4Z` chapter: for good major arcs `(l,k)`, every
`1 < q < ∞` and every `M`, the Ionescu--Wainger projection `Π_{≤l,≤k} = kmtProj ρ l k` decays off
the support of its input,

`‖Π_{≤l,≤k} f‖_{ℓ^q(J)} ≤ C_{ρ,q,M} ⟨l⟩ ⟨2^k dist(I,J)⟩^{-M} ‖f‖_{ℓ^q(I)}`.

The file proves the predicate `Work.KMTAreas.A4Z.OffDecayHyp ρ` (which is *the same term* as
`Work.KMTAreas.A4.OffDecayClaim ρ` and as the statement of `Work.KMTAreas.A4.offDecay`) by the
Appendix A argument: the three-piece decomposition `λ_k = η_{≤jj}λ_k + B ∗ λ_{-jv} + (B - B ∗ λ_{-jv})`
of the kernel (`pieceLo`, `pieceMid`, `pieceHigh`, `lam_eq_pieces`), the Ionescu--Wainger multiplier
theorem (`A7.IwLqGeneral`) for the smooth middle piece, and the sampled `ℓ¹` estimate
(`pieceBDerivTailL1`, `cruxBound_holds`) for the high piece; the far-window case is then pure
bookkeeping (`offDecayTwo_of_high`).

## Main result

* `Work.KMTAreas.A4Z.offDecayTwo`
-/
/-
# Off-diagonal decay of the Ionescu--Wainger projections (§5.2 form)

Krause--Mirek--Tao, Lemma `iw-prop`(i), second half (the estimate `(off-decay)`), in the
vocabulary of the `A4Z` chapter.

## The proof

This is the paper's Appendix A argument in the form designed by the `A4` development.  For a pair
`(l,k)` of good major arcs and an interval `J = [c,d]` at distance `D = c - b` from the support
`[a,b]` of `f`, write the kernel of `Π_{≤l,≤k}` as `c_j λ_k(j)` (`offKernMod`), with
`|c_j| ≤ #(ℚ/ℤ)_{≤l}` and `λ_k = 𝓕⁻η_{≤k}`, and cut it at the scale `2^jj ≈ D` and again at the
height scale `2^jv` of the arithmetic frequencies:

* piece 1, `η_{≤jj} λ_k`, is supported in `|j| ≤ 2^{jj} < D`, hence annihilated by the window
  condition `j ≥ D`;
* piece 2, `B * λ_{-jv}` with `B = λ_k (1 - η_{≤jj})`, has a *smooth* symbol, so the
  Ionescu--Wainger multiplier theorem (`IwLqGeneral`, i.e. area A1) bounds its operator by
  `⟨l⟩ · ‖B * λ_{-jv}‖₁ ≤ ⟨l⟩ · ⟨2^k D⟩^{-N}`;
* piece 3, `B - B * λ_{-jv}`, has frequency content of scale `2^{k+jv}` below the height of the
  arithmetic frequencies, and its sampled `ℓ¹` mass is `≲ 2^{k+jv} ⟨2^k D⟩^{-N}`
  (`offPieceHighZ`), which beats the arithmetic factor `#(ℚ/ℤ)_{≤l} ≲ 2^{2^{ρl}}`
  (`iw_height_card_le`) on good major arcs.

If `2^k D ≤ 2` the plain `ℓ^q` bound (`kmtProj_lp_bound_holds`) suffices.

## Main result

* `Work.KMTAreas.A4Z.offDecayTwo`
-/
import Mathlib
import Submission.Work.KMTAreas.A4Z.Defs
import Submission.Work.KMTAreas.A4.offKernMod
import Submission.Work.KMTAreas.A4.offPieceMid
import Submission.Work.KMTAreas.A4.offLamMoment
import Submission.Work.KMTAreas.A4.offSample
import Submission.Work.KMTAreas.A4.offConvMoment
import Submission.Work.KMTAreas.A4.offConvL1
import Submission.Work.KMTAreas.A4.offYoung
import Submission.Work.KMTAreas.A4.offCutDeriv
import Submission.Work.A4Z.derivCSEq
import Submission.Work.KMTAreas.A7.IwLqGeneral
import Submission.Work.KMTAreas.A7.eLpNorm_iwConv_le_of_IWLqBound
import Submission.Work.KMTAreas.A7.IsLqMultiplierBound_star
import Submission.Port.Aesm

set_option autoImplicit false
set_option maxHeartbeats 2000000

noncomputable section

open MeasureTheory Polynomial Finset Filter Topology
open scoped ENNReal NNReal BigOperators FourierTransform Topology
open Work.Analysis.IonescuWainger
open Work.Analysis.IWMultiplier
open Work.Analysis.InverseTheory
open Work.Analysis.EndVar
open Work.KMTAreas.A7

namespace Work.KMTAreas.A4Z

open Work.KMTAreas.A4 (lam bmp mS cS offCutDeriv offLamTail absSet_eq_Ici_union_Iic
  bmp_one_of_le norm_one_sub_bmp_le lam_eq_etaMult_K)

/-! ## 1. Parity and scaling of the rescaled kernels -/

/-- `𝓕⁻ (𝓕 f) = f` for Schwartz `f`, at the level of functions. -/
theorem fourierInv_fourier_eq (w : SchwartzMap ℝ ℂ) :
    (FourierTransformInv.fourierInv (FourierTransform.fourier (⇑w)) : ℝ → ℂ) = ⇑w := by
  have h2 : (fun y : ℝ => FourierTransform.fourier (⇑w) (-y))
      = (⇑(FourierTransformInv.fourierInv w) : ℝ → ℂ) := by
    funext y
    rw [SchwartzMap.fourierInv_coe]
    exact (Real.fourierInv_eq_fourier_neg (⇑w) y).symm
  calc (FourierTransformInv.fourierInv (FourierTransform.fourier (⇑w)) : ℝ → ℂ)
      = FourierTransform.fourier (fun y : ℝ => FourierTransform.fourier (⇑w) (-y)) :=
        Real.fourierInv_eq_fourier_comp_neg (FourierTransform.fourier (⇑w))
    _ = FourierTransform.fourier (⇑(FourierTransformInv.fourierInv w)) := by rw [h2]
    _ = ⇑(FourierTransform.fourier (FourierTransformInv.fourierInv w)) :=
        (SchwartzMap.fourier_coe (FourierTransformInv.fourierInv w)).symm
    _ = ⇑w := by rw [FourierInvPair.fourier_fourierInv_eq]

/-- **`𝓕𝓕` is the reflection**: `𝓕 (𝓕 f) x = f (-x)` for Schwartz `f`. -/
theorem fourier_fourier_apply (w : SchwartzMap ℝ ℂ) (x : ℝ) :
    FourierTransform.fourier (⇑(FourierTransform.fourier w)) x = w (-x) := by
  have hd : (FourierTransformInv.fourierInv
        (FourierTransform.fourier (⇑w)) : ℝ → ℂ) = ⇑w := fourierInv_fourier_eq w
  have hx := congrFun hd (-x)
  rw [Real.fourierInv_eq_fourier_neg, neg_neg] at hx
  exact hx

/-- Pointwise form of `𝓕 (η_{≤j}) = λ_j`. -/
theorem fourier_bmp_apply (j : ℤ) (x : ℝ) : 𝓕 (⇑(bmp j)) x = lam j x := by
  rw [← SchwartzMap.fourier_coe (bmp j), Work.KMTAreas.A4.fourier_bmp j]

/-- `bmp j` is even. -/
theorem bmp_even (j : ℤ) (x : ℝ) : bmp j (-x) = bmp j x :=
  Work.KMTAreas.A4.bmp_neg_apply j x

/-- **The rescaled kernels `λ_j = 𝓕⁻ η_{≤j}` are even.** -/
theorem lam_even (j : ℤ) (x : ℝ) : lam j (-x) = lam j x := by
  rw [← fourier_bmp_apply j (-x), ← fourier_bmp_apply j x]
  rw [← Real.fourierInv_eq_fourier_neg (⇑(bmp j)) x,
    Real.fourierInv_eq_fourier_comp_neg (⇑(bmp j))]
  rw [show (fun y : ℝ => ⇑(bmp j) (-y)) = ⇑(bmp j) from funext fun y => bmp_even j y]

/-- `etaMult_psiSch` is `λ_0`. -/
theorem psiSch_eq_lam_zero (y : ℝ) : Work.KMTAreas.A7.etaMult_psiSch y = lam 0 y := by
  have h := congrFun (Work.KMTAreas.A4.etaMult_K_coe 0) y
  have h' : (Work.KMTAreas.A7.etaMult_K 0 : ℝ → ℂ) y = Work.KMTAreas.A7.etaMult_psiSch y := by
    simpa using h
  rw [← h', Work.KMTAreas.A4.lam_eq_etaMult_K 0]

/-- Pointwise scaling of `λ_j`: `λ_j(x) = 2^j λ_0(2^j x)`. -/
theorem lam_apply (j : ℤ) (x : ℝ) :
    lam j x = ((((2 : ℝ) ^ j : ℝ)) : ℂ) * lam 0 (((2 : ℝ) ^ j) * x) := by
  rw [Work.KMTAreas.A4.lam_eq_etaMult_K j,
    congrFun (Work.KMTAreas.A4.etaMult_K_coe j) x, psiSch_eq_lam_zero]

/-- Samples of a Schwartz function are summable. -/
theorem summable_samples (f : SchwartzMap ℝ ℂ) : Summable (fun j : ℤ => ‖f (j : ℝ)‖) := by
  obtain ⟨A, hA, hdec⟩ := Work.KMTAreas.A4.schwartz_decay_rpow f 2
  have hbase : Summable (fun j : ℤ => (1 : ℝ) / |(j : ℝ) + 1 / 2| ^ (2 : ℝ)) :=
    (Real.summable_one_div_int_add_rpow (1 / 2) 2).mpr (by norm_num)
  have hcmp : Summable (fun j : ℤ => A * (4 * (1 / |(j : ℝ) + 1 / 2| ^ (2 : ℝ)))) :=
    (hbase.mul_left 4).mul_left A
  refine Summable.of_nonneg_of_le (fun j => norm_nonneg _) (fun j => ?_) hcmp
  have h1 : ‖f (j : ℝ)‖ ≤ A * (1 + |(j : ℝ)|) ^ (-(2 : ℕ) : ℝ) := hdec _
  have hhalf : (1 / 2 : ℝ) ≤ |(j : ℝ) + 1 / 2| := by
    by_cases hj : 0 ≤ j
    · rw [abs_of_nonneg (by
        have : (0 : ℝ) ≤ (j : ℝ) := by exact_mod_cast hj
        linarith)]
      have : (0 : ℝ) ≤ (j : ℝ) := by exact_mod_cast hj
      linarith
    · rw [abs_of_nonpos (by
        have hjm : j ≤ -1 := by omega
        have : (j : ℝ) ≤ -1 := by exact_mod_cast hjm
        linarith)]
      have hjm : j ≤ -1 := by omega
      have : (j : ℝ) ≤ -1 := by exact_mod_cast hjm
      linarith
  have h2 : (1 + |(j : ℝ)|) ^ (-(2 : ℕ) : ℝ)
      ≤ 4 * (1 / |(j : ℝ) + 1 / 2| ^ (2 : ℝ)) := by
    rw [Real.rpow_neg (by positivity), Real.rpow_natCast, Real.rpow_two]
    have hsq : |(j : ℝ) + 1 / 2| ≤ 2 * (1 + |(j : ℝ)|) := by
      have h1' : |(j : ℝ) + 1 / 2| ≤ |(j : ℝ)| + 1 / 2 := by
        simpa using abs_add_le (j : ℝ) (1 / 2)
      linarith [abs_nonneg ((j : ℝ))]
    have hpos : (0 : ℝ) < |(j : ℝ) + 1 / 2| := by linarith
    have hkey : |(j : ℝ) + 1 / 2| ^ 2 / 4 ≤ (1 + |(j : ℝ)|) ^ 2 := by
      nlinarith [hsq, abs_nonneg ((j : ℝ) + 1 / 2)]
    have hpos2 : (0 : ℝ) < |(j : ℝ) + 1 / 2| ^ 2 / 4 := by positivity
    calc ((1 + |(j : ℝ)|) ^ 2)⁻¹ ≤ (|(j : ℝ) + 1 / 2| ^ 2 / 4)⁻¹ := by
          simpa only [one_div] using one_div_le_one_div_of_le hpos2 hkey
      _ = 4 * (1 / |(j : ℝ) + 1 / 2| ^ 2) := by
          rw [one_div]
          field_simp
  calc ‖f (j : ℝ)‖ ≤ A * (1 + |(j : ℝ)|) ^ (-(2 : ℕ) : ℝ) := h1
    _ ≤ A * (4 * (1 / |(j : ℝ) + 1 / 2| ^ (2 : ℝ))) := mul_le_mul_of_nonneg_left h2 hA

/-! ## 2. The kernel of the Ionescu--Wainger projection as a sum -/

/-- **The kernel of `kmtProj ρ l k`**, with the arithmetic factor `|c j| ≤ #(ℚ/ℤ)_{≤l}`. -/
theorem kmtProj_kernel (ρ : ℝ) (l : ℕ) :
    ∃ c : ℤ → ℂ, (∀ j, ‖c j‖ ≤ ((iwArithFreqs ρ l).card : ℝ)) ∧
      (∀ (Φ : SchwartzMap ℝ ℂ) (j : ℤ),
        Work.Analysis.IWMultiplier.iwKernel
          (Work.Analysis.IonescuWainger.iwSymbolSet (iwArithFreqs ρ l)
            (Work.Analysis.IonescuWainger.periodize (⇑Φ))) j = c j * 𝓕 (⇑Φ) (j : ℝ)) ∧
      (∀ (k : ℤ) (f : ℤ → ℂ) (n : ℤ),
        Work.KMTContract.kmtProj ρ l k f n = ∑' j : ℤ, c j * lam k (j : ℝ) * f (n - j)) := by
  choose c hc hcmod using fun j => Work.KMTAreas.A4.offKernMod ρ l j
  refine ⟨c, hc, fun Φ j => hcmod j Φ, fun k f n => ?_⟩
  rw [Work.KMTContract.kmtProj_apply]
  refine tsum_congr fun j => ?_
  have hker : Work.Analysis.IWMultiplier.iwKernel
      (Work.Analysis.IonescuWainger.iwSymbolSet (iwArithFreqs ρ l)
        (Work.Analysis.IonescuWainger.periodize
          (Work.Analysis.IonescuWainger.etaCut Work.KMTContract.kmtEta k))) j
      = c j * lam k (j : ℝ) := by
    rw [show (Work.Analysis.IonescuWainger.etaCut Work.KMTContract.kmtEta k) = ⇑(bmp k) from
      (Work.KMTAreas.A4.bmp_coe k).symm]
    rw [hcmod j (bmp k), fourier_bmp_apply]
  rw [hker]

/-! ## 3. The three pieces of the cut kernel -/

/-- The low (window) piece `η_{≤jj} λ_k`. -/
noncomputable def pieceLo (jj k : ℤ) : SchwartzMap ℝ ℂ := mS (bmp jj) (lam k)

/-- The tail `B = λ_k (1 - η_{≤jj})`. -/
noncomputable abbrev pieceB (jj k : ℤ) : SchwartzMap ℝ ℂ := lam k - mS (bmp jj) (lam k)

/-- The middle piece `B * λ_{-jv}`. -/
noncomputable def pieceMid (jj k jv : ℤ) : SchwartzMap ℝ ℂ := cS (pieceB jj k) (lam (-jv))

/-- The high piece `B - B * λ_{-jv}`. -/
noncomputable abbrev pieceHigh (jj k jv : ℤ) : SchwartzMap ℝ ℂ :=
  pieceB jj k - cS (pieceB jj k) (lam (-jv))

theorem pieceLo_apply (jj k : ℤ) (x : ℝ) : pieceLo jj k x = bmp jj x * lam k x :=
  Work.KMTAreas.A4.mS_apply _ _ _

theorem pieceB_apply (jj k : ℤ) (x : ℝ) :
    pieceB jj k x = lam k x * (1 - bmp jj x) := by
  show (lam k x - mS (bmp jj) (lam k) x) = _
  rw [Work.KMTAreas.A4.mS_apply]
  ring

theorem pieceB_even (jj k : ℤ) (x : ℝ) : pieceB jj k (-x) = pieceB jj k x := by
  rw [pieceB_apply, pieceB_apply, lam_even, bmp_even]

/-- The decomposition of the kernel `λ_k` used for the off-diagonal estimate: at the *reflected*
point `-x` the middle and high pieces sum to `B`. -/
theorem pieceMid_add_pieceHigh (jj k jv : ℤ) (x : ℝ) :
    pieceMid jj k jv (-x) + pieceHigh jj k jv (-x) = pieceB jj k (-x) := by
  show (cS (pieceB jj k) (lam (-jv)) : ℝ → ℂ) (-x)
      + ((pieceB jj k : ℝ → ℂ) (-x) - (cS (pieceB jj k) (lam (-jv)) : ℝ → ℂ) (-x))
      = (pieceB jj k : ℝ → ℂ) (-x)
  ring

/-- The decomposition of the kernel `λ_k` used for the off-diagonal estimate. -/
theorem lam_eq_pieces (jj k jv : ℤ) (x : ℝ) :
    lam k x = pieceLo jj k x + (pieceMid jj k jv (-x) + pieceHigh jj k jv (-x)) := by
  rw [pieceMid_add_pieceHigh, pieceB_even, pieceLo_apply, pieceB_apply]
  ring

/-- The low piece of the *kernel* vanishes on the window: `η_{≤jj}(j) = 0` for `|j| > 2^{jj}`. -/
theorem pieceLo_zero_of_gt (jj k : ℤ) {j : ℤ} (hj : (2 : ℝ) ^ jj < |(j : ℝ)|) :
    pieceLo jj k (j : ℝ) = 0 := by
  rw [pieceLo_apply]
  have hb : bmp jj (j : ℝ) = 0 := by
    by_contra hne
    exact absurd (Work.KMTAreas.A4.bmp_support jj hne) (not_le.mpr hj)
  rw [hb, zero_mul]


/-- The crux input: the sampled `ℓ¹` mass of the high piece. -/
def CruxBound : Prop := ∀ N : ℕ, ∃ C : ℝ, 0 < C ∧
    ∀ (k jj jv : ℤ), k ≤ 0 → 0 ≤ jj → 0 ≤ jv → k + jv ≤ 0 → 0 ≤ k + jj →
      ∑' j : ℤ, ‖pieceHigh jj k jv (j : ℝ)‖
        ≤ C * (2 : ℝ) ^ (k + jv) * (max ((2 : ℝ) ^ (k + jj - 1)) 1) ^ (-(N : ℝ))

/-- `eLpNorm · 1` is the `ofReal` of the integral of the norm. -/
theorem eLpNorm_one_eq_ofReal_integral (g : ℝ → ℂ) (hg : Integrable g volume) :
    eLpNorm g 1 volume = ENNReal.ofReal (∫ x : ℝ, ‖g x‖) := by
  have h1 : eLpNorm g 1 volume = ∫⁻ x : ℝ, ‖g x‖ₑ := eLpNorm_one_eq_lintegral_enorm (hf := by pw_aesm)
  have h2 : (∫⁻ x : ℝ, ENNReal.ofReal ‖g x‖) = ENNReal.ofReal (∫ x : ℝ, ‖g x‖) :=
    (ofReal_integral_eq_lintegral_ofReal hg.norm (Eventually.of_forall fun x => norm_nonneg _)).symm
  rw [h1]
  conv_rhs => rw [← h2]
  refine lintegral_congr fun x => ?_
  exact (ofReal_norm _).symm

/-- **Lemma `iw-prop`(i), off-diagonal decay** (Appendix A), in the form used by the `A4Z`
chapter, from the crux estimate on the high piece. -/
theorem offDecayTwo_of_high (hA1 : Work.KMTContract.AreaA1) (hHigh : CruxBound) :
    ∀ (ρ : ℝ), 0 < ρ → ρ ≤ 1 → Work.KMTAreas.A4Z.OffDecayHyp ρ := by
  intro ρ hρ hρ1 q hq M
  obtain ⟨CρIw, hCρIw, hIwfun⟩ := IwLqGeneral hA1 ρ hρ hρ1
  obtain ⟨CIq, hCIq, hIW⟩ := hIwfun q hq
  obtain ⟨CρPl, hCρPl, C₂, hC₂, hPlain⟩ := kmtProj_lp_bound_holds hA1 ρ hρ hρ1 q hq
  obtain ⟨Cm, hCm, hMid⟩ := Work.KMTAreas.A4.offPieceMid (M + 2)
  obtain ⟨Cmom, hCmom, hMom⟩ := Work.KMTAreas.A4.offLamMoment
  obtain ⟨Cc, hCc, hCard⟩ := iw_height_card_le hρ
  obtain ⟨Chigh, hChigh, hHighN⟩ := hHigh (M + 2)
  have hEtaMnn : (0:ℝ) ≤ (etaMult_M : ℝ) := le_of_lt (by exact_mod_cast Work.KMTAreas.A7.etaMult_M_pos)
  have hEtaMpos : (0:ℝ) < (etaMult_M : ℝ) := by exact_mod_cast Work.KMTAreas.A7.etaMult_M_pos
  set Cρ₀ : ℝ := max (max CρIw CρPl) (max (2 * CρIw + 8) (2 * Cc + 8)) with hCρ₀def
  have hCρ₀pos : 0 < Cρ₀ := by
    rw [hCρ₀def]
    have h2 : (0:ℝ) < 2 * Cc + 8 := by linarith
    have h1 : (0:ℝ) < 2 * CρIw + 8 := by linarith
    exact lt_max_of_lt_right (lt_max_of_lt_right h2)
  have hleIw : CρIw ≤ Cρ₀ := by
    rw [hCρ₀def]
    exact le_trans (le_max_left _ _) (le_max_left _ _)
  have hlePl : CρPl ≤ Cρ₀ := by
    rw [hCρ₀def]
    exact le_trans (le_max_right _ _) (le_max_left _ _)
  have hle2Iw : 2 * CρIw + 8 ≤ Cρ₀ := by
    rw [hCρ₀def]
    exact le_trans (le_max_left _ _) (le_max_right _ _)
  have hle2C : 2 * Cc + 8 ≤ Cρ₀ := by
    rw [hCρ₀def]
    exact le_trans (le_max_right _ _) (le_max_right _ _)
  set Cfin : ℝ := (2 : ℝ) ^ (M : ℝ) * (C₂ : ℝ)
      + 8 ^ (M + 2) * (CIq * Cm * (etaMult_M : ℝ) + 2 * Cc * Chigh) + 1 with hCfindef
  have hExtra : (0:ℝ) ≤ 8 ^ (M + 2) * (CIq * Cm * (etaMult_M : ℝ) + 2 * Cc * Chigh) := by
    refine mul_nonneg (by positivity) (add_nonneg ?_ ?_)
    · exact mul_nonneg (mul_nonneg hCIq.le hCm.le) hEtaMnn
    · exact mul_nonneg (mul_nonneg (by norm_num) hCc.le) hChigh.le
  have hCfinpos : 0 < Cfin := by
    rw [hCfindef]
    have h1 : (0:ℝ) < (2:ℝ)^(M:ℝ) * (C₂:ℝ) := by
      exact mul_pos (Real.rpow_pos_of_pos (by norm_num) _) hC₂.pos
    linarith
  set Cfinn : ℝ≥0 := ⟨Cfin, hCfinpos.le⟩ with hCfinn
  have hCfinnR : (Cfinn : ℝ) = Cfin := rfl
  refine ⟨Cρ₀, hCρ₀pos, ⟨Cfinn, by rw [hCfinn]; exact_mod_cast hCfinpos, ?_⟩⟩
  intro l k hgood a b c d f hbc hsupp
  have hk_nonpos : k ≤ 0 := by
    have hp : (0:ℝ) < (2:ℝ)^(ρ*(l:ℝ)) := Real.rpow_pos_of_pos (by norm_num) _
    have h : (k:ℝ) ≤ -Cρ₀ * (2:ℝ)^(ρ*(l:ℝ)) := hgood
    have h5 : (0:ℝ) < Cρ₀ * (2:ℝ)^(ρ*(l:ℝ)) := mul_pos hCρ₀pos hp
    have : (k:ℝ) ≤ 0 := by nlinarith [h, h5]
    exact_mod_cast this
  set D : ℝ := ((c - b : ℤ) : ℝ) with hDdef
  have hDpos : 0 < D := by rw [hDdef]; exact_mod_cast (by omega : (0:ℤ) < c - b)
  have hD1 : 1 ≤ D := by rw [hDdef]; exact_mod_cast (by omega : (1:ℤ) ≤ c - b)
  set X : ℝ := max ((2 : ℝ) ^ k * ((c - b : ℤ) : ℝ)) 1 with hXdef
  have hX1 : 1 ≤ X := le_max_right _ _
  have hXpos : 0 < X := lt_of_lt_of_le zero_lt_one hX1
  have hl1 : (1:ℝ) ≤ max ((l:ℝ)) 1 := le_max_right _ _
  have hl1' : (0:ℝ) ≤ max ((l:ℝ)) 1 := le_trans zero_le_one hl1
  have hangle : (angleBracket l : ℝ) = max ((l:ℝ)) 1 := by
    rw [Work.Analysis.IWMultiplier.angleBracket, max_comm]
    rfl
  by_cases hcase : (2 : ℝ) ^ k * D ≤ 2
  · -- Case A: the plain `ℓ^q` bound
    have hgPl : GoodMajorArcs ρ CρPl l k := GoodMajorArcs.mono_const hlePl hgood
    have hXle : X ≤ 2 := by
      rw [hXdef]
      exact max_le (by rw [← hDdef]; exact hcase) (by norm_num)
    have hXinv : (2:ℝ) ^ (-(M:ℝ)) ≤ X ^ (-(M:ℝ)) :=
      Real.rpow_le_rpow_of_nonpos hXpos hXle (neg_nonpos.mpr (Nat.cast_nonneg M))
    have hC₂le : (C₂:ℝ) ≤ Cfin * X ^ (-(M:ℝ)) := by
      have h2 : (2:ℝ)^(M:ℝ) * (2:ℝ)^(-(M:ℝ)) = 1 := by
        rw [Real.rpow_neg (by norm_num : (0:ℝ) ≤ 2),
          mul_inv_cancel₀ (ne_of_gt (Real.rpow_pos_of_pos (by norm_num) _))]
      have h3 : (2:ℝ)^(M:ℝ) * (C₂:ℝ) * (2:ℝ)^(-(M:ℝ)) = (C₂:ℝ) := by
        calc (2:ℝ)^(M:ℝ) * (C₂:ℝ) * (2:ℝ)^(-(M:ℝ))
            = (C₂:ℝ) * ((2:ℝ)^(M:ℝ) * (2:ℝ)^(-(M:ℝ))) := by ring
          _ = (C₂:ℝ) * 1 := by rw [h2]
          _ = (C₂:ℝ) := by ring
      have h4 : (2:ℝ)^(M:ℝ) * (C₂:ℝ) ≤ Cfin := by
        rw [hCfindef]; linarith
      calc (C₂:ℝ) = (2:ℝ)^(M:ℝ) * (C₂:ℝ) * (2:ℝ)^(-(M:ℝ)) := h3.symm
        _ ≤ Cfin * X ^ (-(M:ℝ)) :=
            mul_le_mul h4 hXinv (by positivity) (le_of_lt hCfinpos)
    have hkey : (C₂ : ℝ) * max ((l:ℝ)) 1
        ≤ Cfin * (max ((l:ℝ)) 1 * X ^ (-(M:ℝ))) := by
      calc (C₂ : ℝ) * max ((l:ℝ)) 1 ≤ (Cfin * X ^ (-(M:ℝ))) * max ((l:ℝ)) 1 :=
            mul_le_mul_of_nonneg_right hC₂le hl1'
        _ = Cfin * (max ((l:ℝ)) 1 * X ^ (-(M:ℝ))) := by ring
    calc eLpNorm (fun x : ℤ => if c ≤ x ∧ x ≤ d then Work.KMTContract.kmtProj ρ l k f x else 0)
            (ENNReal.ofReal q) Measure.count
        ≤ eLpNorm (Work.KMTContract.kmtProj ρ l k f) (ENNReal.ofReal q) Measure.count := by
          refine eLpNorm_mono (hf := by pw_aesm) (fun x => ?_)
          by_cases hx : c ≤ x ∧ x ≤ d
          · rw [if_pos hx]
          · rw [if_neg hx]; simp only [norm_zero]; positivity
      _ ≤ ENNReal.ofReal (C₂ : ℝ) * ENNReal.ofReal (angleBracket l : ℝ)
            * eLpNorm f (ENNReal.ofReal q) Measure.count := hPlain l k hgPl f
      _ = ENNReal.ofReal ((C₂ : ℝ) * max ((l:ℝ)) 1) * eLpNorm f (ENNReal.ofReal q) Measure.count := by
          rw [hangle, ENNReal.ofReal_mul (by positivity)]
      _ ≤ ENNReal.ofReal (Cfin * (max ((l:ℝ)) 1 * X ^ (-(M:ℝ))))
            * eLpNorm f (ENNReal.ofReal q) Measure.count :=
          mul_le_mul' (ENNReal.ofReal_le_ofReal hkey) le_rfl
      _ = (Cfinn : ℝ≥0∞) *
            ENNReal.ofReal (max ((l:ℝ)) 1 * (max ((2 : ℝ) ^ k * ((c - b : ℤ) : ℝ)) 1) ^ (-(M:ℝ))) *
            eLpNorm f (ENNReal.ofReal q) Measure.count := by
          rw [hXdef, ENNReal.ofReal_mul (le_of_lt hCfinpos), ← hCfinnR,
            ENNReal.ofReal_coe_nnreal]
  · -- Case B: the off-diagonal argument
    have hkD2 : 2 < (2 : ℝ) ^ k * D := not_le.mp hcase
    have hkD1 : (1:ℝ) ≤ (2 : ℝ) ^ k * D := by linarith
    have hkDpos : (0:ℝ) < (2 : ℝ) ^ k * D := by linarith
    set ylog : ℝ := Real.logb 2 ((2 : ℝ) ^ k * D) with hylogdef
    have hyeq : (2 : ℝ) ^ ylog = (2 : ℝ) ^ k * D := by
      rw [hylogdef]
      exact Real.rpow_logb (by norm_num) (by norm_num) hkDpos
    set m : ℤ := ⌊ylog⌋ - 1 with hmdef
    have hm_low : (2 : ℝ) ^ (m + 1) ≤ (2 : ℝ) ^ k * D := by
      have h1 : ((m + 1 : ℤ) : ℝ) ≤ ylog := by
        have h2 : ((⌊ylog⌋ : ℤ) : ℝ) ≤ ylog := Int.floor_le ylog
        have h3 : m + 1 = ⌊ylog⌋ := by rw [hmdef]; ring
        rw [h3]; exact h2
      calc (2 : ℝ) ^ (m + 1) = (2 : ℝ) ^ ((m + 1 : ℤ) : ℝ) := (Real.rpow_intCast 2 (m+1)).symm
        _ ≤ (2 : ℝ) ^ ylog := Real.rpow_le_rpow_of_exponent_le (by norm_num) h1
        _ = (2 : ℝ) ^ k * D := hyeq
    have hm_up : (2 : ℝ) ^ k * D < (2 : ℝ) ^ (m + 2) := by
      have h1 : ylog < ((m + 2 : ℤ) : ℝ) := by
        have h2 : ylog < ((⌊ylog⌋ : ℤ) : ℝ) + 1 := Int.lt_floor_add_one ylog
        have h3 : ((m + 2 : ℤ) : ℝ) = ((⌊ylog⌋ : ℤ) : ℝ) + 1 := by rw [hmdef]; push_cast; ring
        rw [h3]; exact h2
      calc (2 : ℝ) ^ k * D = (2 : ℝ) ^ ylog := hyeq.symm
        _ < (2 : ℝ) ^ ((m + 2 : ℤ) : ℝ) := Real.rpow_lt_rpow_of_exponent_lt (by norm_num) h1
        _ = (2 : ℝ) ^ (m + 2) := Real.rpow_intCast 2 (m+2)
    have hm_nonneg : 0 ≤ m := by
      by_contra hm
      push_neg at hm
      have h1 : m + 2 ≤ (1:ℤ) := by omega
      have h2 : (2:ℝ)^(m+2) ≤ (2:ℝ)^((1:ℤ)) := zpow_le_zpow_right₀ (by norm_num) h1
      norm_num at h2
      linarith [hm_up, hkD2, h2]
    set jj : ℤ := m - k with hjjdef
    have hkjjm : k + jj = m := by rw [hjjdef]; ring
    have hkjj : 0 ≤ k + jj := by rw [hkjjm]; exact hm_nonneg
    have hjj_nonneg : 0 ≤ jj := by rw [hjjdef]; omega
    set jv : ℤ := ⌈-((k:ℝ)/2)⌉ with hjvdef
    have hjv_nonneg : 0 ≤ jv := by
      have hk0 : (k:ℝ) ≤ 0 := by exact_mod_cast hk_nonpos
      have h1 : (0:ℝ) ≤ -((k:ℝ)/2) := by linarith
      have h2 : (0:ℝ) ≤ (jv:ℝ) := by
        rw [hjvdef]
        exact le_trans h1 (Int.le_ceil _)
      exact_mod_cast h2
    have hkjv : k + jv ≤ 0 := by
      have h1 : (jv:ℝ) < -((k:ℝ)/2) + 1 := Int.ceil_lt_add_one _
      have hp : (1:ℝ) ≤ (2:ℝ)^(ρ*(l:ℝ)) := Real.one_le_rpow (by norm_num) (by positivity)
      have h3 : (k:ℝ) ≤ -Cρ₀ * (2:ℝ)^(ρ*(l:ℝ)) := hgood
      have h4 : (Cρ₀:ℝ) ≤ Cρ₀ * (2:ℝ)^(ρ*(l:ℝ)) := by nlinarith [hp, hCρ₀pos]
      have : (k:ℝ) + (jv:ℝ) < (k:ℝ)/2 + 1 := by linarith
      have h5 : (k:ℝ)/2 + 1 ≤ 0 := by nlinarith [h3, h4, hCρ₀pos]
      have : (k:ℝ) + (jv:ℝ) ≤ 0 := by linarith
      exact_mod_cast this
    have hgoodIw : GoodMajorArcs ρ CρIw l (-jv) := by
      have hp : (0:ℝ) < (2:ℝ)^(ρ*(l:ℝ)) := Real.rpow_pos_of_pos (by norm_num) _
      have h2 : (CρIw:ℝ) * (2:ℝ)^(ρ*(l:ℝ)) ≤ Cρ₀ * (2:ℝ)^(ρ*(l:ℝ)) :=
        mul_le_mul_of_nonneg_right hleIw hp.le
      have h3 : -((k:ℝ)/2) ≤ (jv:ℝ) := by rw [hjvdef]; exact Int.le_ceil (-((k:ℝ)/2))
      have h4 : (CρIw:ℝ) * (2:ℝ)^(ρ*(l:ℝ)) ≤ (Cρ₀ * (2:ℝ)^(ρ*(l:ℝ)))/2 := by
        nlinarith [hle2Iw, hp, hCρIw, h2]
      have h5 : (Cρ₀ * (2:ℝ)^(ρ*(l:ℝ)))/2 ≤ -((k:ℝ)/2) := by
        have hg' : (k:ℝ) ≤ -Cρ₀ * (2:ℝ)^(ρ*(l:ℝ)) := hgood
        have h6 : (Cρ₀ * (2:ℝ)^(ρ*(l:ℝ))) ≤ -((k:ℝ)) := by linarith [hg']
        have h7 : (Cρ₀ * (2:ℝ)^(ρ*(l:ℝ)))/2 = (Cρ₀ * (2:ℝ)^(ρ*(l:ℝ))) * (1/2) := by ring
        have h8 : -((k:ℝ)/2) = -((k:ℝ)) * (1/2) := by ring
        rw [h7, h8]
        exact mul_le_mul_of_nonneg_right h6 (by norm_num)
      show ((-jv : ℤ) : ℝ) ≤ -CρIw * (2:ℝ)^(ρ*(l:ℝ))
      push_cast
      linarith [h2, h3, h4, h5]
    -- the window identity and the operators
    obtain ⟨kk, hkk, hkerAny, hker⟩ := kmtProj_kernel ρ l
    set W2 : ℤ → ℂ := fun n => ∑' j : ℤ, kk j * pieceMid jj k jv (-(j:ℝ)) * f (n - j) with hW2def
    set W3 : ℤ → ℂ := fun n => ∑' j : ℤ, kk j * pieceHigh jj k jv (-(j:ℝ)) * f (n - j) with hW3def
    have hfinaux : ∀ n j : ℤ, f (n - j) ≠ 0 → j ∈ Finset.Icc (n - b) (n - a) := by
      intro n j hf0
      rw [Finset.mem_Icc]
      constructor <;> by_contra hlt <;> push_neg at hlt
      · exact hf0 (hsupp _ (Or.inr (by omega)))
      · exact hf0 (hsupp _ (Or.inl (by omega)))
    have hwin_eq : ∀ n : ℤ, (if c ≤ n ∧ n ≤ d then Work.KMTContract.kmtProj ρ l k f n else 0)
        = (if c ≤ n ∧ n ≤ d then W2 n else 0) + (if c ≤ n ∧ n ≤ d then W3 n else 0) := by
      intro n
      by_cases hn : c ≤ n ∧ n ≤ d
      · rw [if_pos hn, if_pos hn, if_pos hn]
        have hfin : Work.KMTContract.kmtProj ρ l k f n
            = ∑ j ∈ Finset.Icc (n - b) (n - a), kk j * (lam k (j:ℝ)) * f (n - j) := by
          rw [hker k f n]
          refine tsum_eq_sum ?_
          intro j hj
          by_contra hne
          exact hj (hfinaux n j (fun h => hne (by rw [h, mul_zero])))
        have hsplit2 : ∀ j ∈ Finset.Icc (n - b) (n - a),
            kk j * (lam k (j:ℝ)) * f (n - j)
              = kk j * pieceMid jj k jv (-(j:ℝ)) * f (n - j)
                + kk j * pieceHigh jj k jv (-(j:ℝ)) * f (n - j) := by
          intro j hj
          have hjmem := Finset.mem_Icc.mp hj
          have hjD : (2:ℝ)^jj < |((j:ℤ):ℝ)| := by
            have h1 : ((n - b : ℤ) : ℝ) ≤ (j:ℝ) := by exact_mod_cast hjmem.1
            have h2 : ((n:ℤ):ℝ) - (b:ℝ) ≤ (j:ℝ) := by push_cast at h1; linarith
            have h3 : ((n:ℤ):ℝ) ≥ (c:ℝ) := by exact_mod_cast hn.1
            have h4 : D = (c:ℝ) - (b:ℝ) := by rw [hDdef]; push_cast; ring
            have h5 : D ≤ (j:ℝ) := by rw [h4]; linarith
            have h6 : (2:ℝ)^jj ≤ D/2 := by
              have h7 : (2:ℝ)^jj = (2:ℝ)^m / (2:ℝ)^k := by
                rw [hjjdef, zpow_sub₀ (by norm_num)]
              have h10 : (0:ℝ) < (2:ℝ)^k := zpow_pos (by norm_num) k
              have h11 : (2:ℝ)^m * 2 ≤ (2:ℝ)^k * D := by
                rw [show (2:ℝ)^(m+1) = (2:ℝ)^m * 2 from by
                  rw [zpow_add_one₀ (by norm_num)]] at hm_low
                exact hm_low
              rw [h7, div_le_iff₀ h10]
              nlinarith [h11]
            have h8 : (0:ℝ) ≤ (j:ℝ) := le_trans hDpos.le h5
            rw [abs_of_nonneg h8]; linarith
          have hzero : pieceLo jj k (j:ℝ) = 0 := pieceLo_zero_of_gt jj k hjD
          have hdecomp := lam_eq_pieces jj k jv (j:ℝ)
          rw [hzero, zero_add] at hdecomp
          rw [hdecomp]
          ring
        rw [hfin, Finset.sum_congr rfl hsplit2, Finset.sum_add_distrib]
        congr 1
        · rw [hW2def]
          exact (tsum_eq_sum (fun j hj => by
            by_contra hne
            exact hj (hfinaux n j (fun h => hne (by rw [h, mul_zero]))))).symm
        · rw [hW3def]
          exact (tsum_eq_sum (fun j hj => by
            by_contra hne
            exact hj (hfinaux n j (fun h => hne (by rw [h, mul_zero]))))).symm
      · rw [if_neg hn, if_neg hn, if_neg hn, add_zero]
    -- the constant `Yc`
    set Yc : ℝ := max ((2:ℝ)^(k + jj - 1)) 1 with hYcdef
    have hYc1 : 1 ≤ Yc := le_max_right _ _
    have hYcpos : 0 < Yc := lt_of_lt_of_le zero_lt_one hYc1
    have hYc_eq : Yc = max ((2:ℝ)^(m - 1)) 1 := by rw [hYcdef, hkjjm]
    have hYcX : X / 8 ≤ Yc := by
      have h2m : X ≤ (2:ℝ)^(m+2) := by
        rw [hXdef]
        refine max_le ?_ (by linarith)
        rw [← hDdef]
        exact le_of_lt hm_up
      have h4 : (2:ℝ)^(m+2) = 8 * (2:ℝ)^(m-1) := by
        rw [show m + 2 = (m-1) + 3 by ring, zpow_add₀ (by norm_num)]
        ring
      rw [h4] at h2m
      have h5 : (2:ℝ)^(m-1) ≤ Yc := by
        rw [hYc_eq]
        exact le_max_left _ _
      linarith
    have hYc_small : Yc ^ (-(((M+2:ℕ)):ℝ)) ≤ 8 ^ (M + 2) * X ^ (-(M:ℝ)) := by
      have hx8 : (0:ℝ) < X / 8 := by linarith [hXpos]
      have h1 : Yc ^ (-(((M+2:ℕ)):ℝ)) ≤ (X/8) ^ (-(((M+2:ℕ)):ℝ)) :=
        Real.rpow_le_rpow_of_nonpos hx8 hYcX (neg_nonpos.mpr (Nat.cast_nonneg _))
      have h2 : (X/8) ^ (-(((M+2:ℕ)):ℝ)) = 8 ^ (M+2) * X ^ (-(((M+2:ℕ)):ℝ)) := by
        rw [Real.div_rpow hXpos.le (by norm_num : (0:ℝ) ≤ 8),
          Real.rpow_neg (by norm_num : (0:ℝ) ≤ 8), Real.rpow_natCast, div_inv_eq_mul]
        ring
      have h3 : X ^ (-(((M+2:ℕ)):ℝ)) ≤ X ^ (-(M:ℝ)) := by
        refine Real.rpow_le_rpow_of_exponent_le hX1 ?_
        push_cast
        linarith
      calc Yc ^ (-(((M+2:ℕ)):ℝ)) ≤ (X/8) ^ (-(((M+2:ℕ)):ℝ)) := h1
        _ = 8 ^ (M+2) * X ^ (-(((M+2:ℕ)):ℝ)) := h2
        _ ≤ 8 ^ (M+2) * X ^ (-(M:ℝ)) :=
            mul_le_mul_of_nonneg_left h3 (by positivity)
    -- the cardinality gain
    have hcard_gain : ((iwArithFreqs ρ l).card : ℝ) * (2:ℝ)^(k+jv) ≤ 2 * Cc := by
      have hp : (0:ℝ) < (2:ℝ)^(ρ*(l:ℝ)) := Real.rpow_pos_of_pos (by norm_num) _
      have h1 : ((iwArithFreqs ρ l).card : ℝ) ≤ Cc * (2:ℝ)^((2:ℝ)^(ρ*(l:ℝ))) := hCard l
      have h2 : ((k:ℝ) + (jv:ℝ)) ≤ -(Cρ₀ * (2:ℝ)^(ρ*(l:ℝ))/2) + 1 := by
        have h3 : (jv:ℝ) < -((k:ℝ)/2) + 1 := Int.ceil_lt_add_one _
        have h4 : (k:ℝ) ≤ -Cρ₀ * (2:ℝ)^(ρ*(l:ℝ)) := hgood
        linarith [h3, h4]
      have h5 : (2:ℝ)^(k+jv) ≤ 2 * (2:ℝ)^(-(Cρ₀ * (2:ℝ)^(ρ*(l:ℝ))/2)) := by
        have h6 : (2:ℝ)^((k:ℝ)+(jv:ℝ)) ≤ (2:ℝ)^(-(Cρ₀ * (2:ℝ)^(ρ*(l:ℝ))/2) + 1) :=
          Real.rpow_le_rpow_of_exponent_le (by norm_num) h2
        have h7 : (2:ℝ)^((k:ℝ)+(jv:ℝ)) = (2:ℝ)^(k+jv) := by
          rw [← Real.rpow_intCast]; norm_num
        rw [h7] at h6
        calc (2:ℝ)^(k+jv) ≤ (2:ℝ)^(-(Cρ₀ * (2:ℝ)^(ρ*(l:ℝ))/2) + 1) := h6
          _ = 2 * (2:ℝ)^(-(Cρ₀ * (2:ℝ)^(ρ*(l:ℝ))/2)) := by
              rw [Real.rpow_add (by norm_num : (0:ℝ) < 2), Real.rpow_one]; ring
      have h8 : (2:ℝ)^((2:ℝ)^(ρ*(l:ℝ))) * (2:ℝ)^(-(Cρ₀ * (2:ℝ)^(ρ*(l:ℝ))/2)) ≤ 1 := by
        rw [← Real.rpow_add (by norm_num : (0:ℝ) < 2), ← Real.rpow_zero (2:ℝ)]
        refine Real.rpow_le_rpow_of_exponent_le (by norm_num) ?_
        have hp1 : (1:ℝ) ≤ (2:ℝ)^(ρ*(l:ℝ)) := Real.one_le_rpow (by norm_num) (by positivity)
        have h9 : (2:ℝ) ≤ Cρ₀ := by linarith [hle2Iw, hCρIw]
        nlinarith [hp1, h9, hp]
      calc ((iwArithFreqs ρ l).card : ℝ) * (2:ℝ)^(k+jv)
          ≤ (Cc * (2:ℝ)^((2:ℝ)^(ρ*(l:ℝ)))) * (2 * (2:ℝ)^(-(Cρ₀ * (2:ℝ)^(ρ*(l:ℝ))/2))) := by
            refine mul_le_mul h1 h5 (by positivity) (by positivity)
        _ = 2 * Cc * ((2:ℝ)^((2:ℝ)^(ρ*(l:ℝ))) * (2:ℝ)^(-(Cρ₀ * (2:ℝ)^(ρ*(l:ℝ))/2))) := by ring
        _ ≤ 2 * Cc * 1 := by
            refine mul_le_mul_of_nonneg_left h8 (by linarith [hCc.le])
        _ = 2 * Cc := by ring
    -- the middle-piece multiplier bound
    set M2 : ℝ≥0 := ⟨Cm * Yc ^ (-(((M+2:ℕ)):ℝ)) * (etaMult_M : ℝ),
      mul_nonneg (mul_nonneg hCm.le (Real.rpow_nonneg hYcpos.le _)) hEtaMnn⟩ with hM2def
    have hM2coe : (M2:ℝ) = Cm * Yc ^ (-(((M+2:ℕ)):ℝ)) * (etaMult_M : ℝ) := by
      rw [hM2def]; rfl
    have hYmid : max ((2:ℝ)^k * (2:ℝ)^(jj-1)) 1 = Yc := by
      have hk1 : k + (jj - 1) = m - 1 := by omega
      rw [hYc_eq, ← hk1, ← zpow_add₀ (by norm_num : (2:ℝ) ≠ 0)]
    have hmidL1 : eLpNorm (⇑(pieceMid jj k jv)) 1 volume ≤ ENNReal.ofReal (M2:ℝ) := by
      rw [eLpNorm_one_eq_ofReal_integral _ (SchwartzMap.integrable _)]
      refine ENNReal.ofReal_le_ofReal ?_
      have h1 : ∫ x, ‖(pieceB jj k) x‖ ≤ Cm * Yc ^ (-(((M+2:ℕ)):ℝ)) := by
        have h := hMid k jj hk_nonpos hjj_nonneg
        rwa [hYmid] at h
      have h2 : ∫ x, ‖(lam (-jv)) x‖ ≤ (etaMult_M:ℝ) := by
        have h3 : eLpNorm (⇑(Work.KMTAreas.A7.etaMult_K (-jv))) 1 volume ≤ ENNReal.ofReal (etaMult_M:ℝ) :=
          Work.KMTAreas.A7.etaMult_K_norm (-jv)
        rw [eLpNorm_one_eq_ofReal_integral _ (SchwartzMap.integrable _)] at h3
        rw [← Work.KMTAreas.A4.lam_eq_etaMult_K (-jv)] at h3
        exact (ENNReal.ofReal_le_ofReal_iff (by positivity)).mp h3
      calc ∫ x, ‖(pieceMid jj k jv) x‖
          = ∫ x, ‖(Work.KMTAreas.A4.cS (pieceB jj k) (lam (-jv))) x‖ := rfl
        _ ≤ (∫ x, ‖(pieceB jj k) x‖) * (∫ x, ‖(lam (-jv)) x‖) :=
            Work.KMTAreas.A4.offConvL1 (pieceB jj k) (lam (-jv))
        _ ≤ (Cm * Yc ^ (-(((M+2:ℕ)):ℝ))) * (etaMult_M:ℝ) :=
            mul_le_mul h1 h2 (integral_nonneg fun x => norm_nonneg _)
              (mul_nonneg hCm.le (Real.rpow_nonneg hYcpos.le _))
        _ = (M2:ℝ) := hM2coe.symm
    have hsym : (𝓕 (pieceMid jj k jv) : SchwartzMap ℝ ℂ)
        = mS (𝓕 (pieceB jj k)) (bmp (-jv)) := by
      rw [pieceMid, Work.KMTAreas.A4.fourier_cS]
      exact congrArg (fun g => mS (𝓕 (pieceB jj k)) g) (Work.KMTAreas.A4.lam_fourier (-jv))
    have hsapply : ∀ x : ℝ, (𝓕 (pieceMid jj k jv) : SchwartzMap ℝ ℂ) x
        = (𝓕 (pieceB jj k)) x * (bmp (-jv)) x := by
      intro x
      rw [hsym, Work.KMTAreas.A4.mS_apply]
    have hsuppM : ∀ x : ℝ, (𝓕 (pieceMid jj k jv) : SchwartzMap ℝ ℂ) x ≠ 0 → x ∈ realArc (-jv) := by
      intro x hx
      rw [hsapply] at hx
      have hb : (bmp (-jv)) x ≠ 0 := fun h => hx (by rw [h, mul_zero])
      have h4 : |x| ≤ (2:ℝ)^(-jv) := Work.KMTAreas.A4.bmp_support (-jv) hb
      rw [Work.Analysis.IonescuWainger.realArc]
      exact ⟨by linarith [neg_abs_le x], by linarith [le_abs_self x]⟩
    have hmult : ∀ p : ℝ, 1 < p → IsLqMultiplierBound (ENNReal.ofReal p)
        (fun x : ℝ => (𝓕 (pieceMid jj k jv) : SchwartzMap ℝ ℂ) x) M2 := by
      intro p hp
      exact etaMult_lqBound_finite (K := pieceMid jj k jv)
        (φ := fun x : ℝ => (𝓕 (pieceMid jj k jv) : SchwartzMap ℝ ℂ) x)
        (M := M2) (fun ξ => by rw [SchwartzMap.fourier_coe]) hmidL1
        (by rw [← ENNReal.ofReal_one]; exact ENNReal.ofReal_le_ofReal (le_of_lt hp))
        (ENNReal.ofReal_ne_top)
    have hmultstar : ∀ p : ℝ, 1 < p → IsLqMultiplierBound (ENNReal.ofReal p)
        (fun x => star ((fun x : ℝ => (𝓕 (pieceMid jj k jv) : SchwartzMap ℝ ℂ) x) x)) M2 := by
      intro p hp
      exact Work.KMTAreas.A7.IsLqMultiplierBound_star (hmult p hp)
    have hIWb := hIW l (-jv) hgoodIw (𝓕 (pieceMid jj k jv)) M2 hsuppM hmult hmultstar
    have hW2eq : W2 = Work.Analysis.IWMultiplier.iwConv (iwArithFreqs ρ l)
        (periodize (⇑(𝓕 (pieceMid jj k jv) : SchwartzMap ℝ ℂ))) f := by
      funext n
      rw [hW2def, Work.Analysis.IWMultiplier.iwConv_apply]
      refine tsum_congr fun j => ?_
      rw [hkerAny (𝓕 (pieceMid jj k jv)) j, fourier_fourier_apply, smul_eq_mul]
    have hW2le : eLpNorm W2 (ENNReal.ofReal q) Measure.count
        ≤ ENNReal.ofReal ((CIq * angleBracket l * M2 : ℝ≥0) : ℝ)
            * eLpNorm f (ENNReal.ofReal q) Measure.count := by
      rw [hW2eq]
      refine eLpNorm_iwConv_le_of_IWLqBound (iwArithFreqs ρ l)
        (𝓕 (pieceMid jj k jv)) hq ?_ hIWb f
      exact mul_pos (mul_pos hCIq (Work.Analysis.IWMultiplier.angleBracket_pos l))
        (by rw [hM2def]; exact mul_pos (mul_pos hCm (Real.rpow_pos_of_pos hYcpos _)) hEtaMpos)
    have hW3le : eLpNorm W3 (ENNReal.ofReal q) Measure.count
        ≤ (∑' t : ℤ, ENNReal.ofReal ‖kk t * pieceHigh jj k jv (-(t:ℝ))‖)
            * eLpNorm f (ENNReal.ofReal q) Measure.count := by
      rw [hW3def]
      exact Work.KMTAreas.A4.offYoung_conv_count_le (le_of_lt hq) _ _
    have hsummHigh : Summable (fun t : ℤ => ‖pieceHigh jj k jv (t:ℝ)‖) := summable_samples _
    set K1 : ℝ := (CIq:ℝ) * Cm * (etaMult_M:ℝ) with hK1def
    set K2 : ℝ := 2 * Cc * Chigh with hK2def
    have hK1nn : 0 ≤ K1 := by rw [hK1def]; exact mul_nonneg (mul_nonneg hCIq.le hCm.le) hEtaMnn
    have hK2nn : 0 ≤ K2 := by rw [hK2def]; exact mul_nonneg (mul_nonneg (by norm_num) hCc.le) hChigh.le
    have hCfin_eq : Cfin = 2 ^ (M:ℝ) * (C₂:ℝ) + 8 ^ (M+2) * (K1 + K2) + 1 := by
      rw [hCfindef, hK1def, hK2def]
    have hKsum : 8 ^ (M+2) * (K1 + K2) ≤ Cfin := by
      rw [hCfin_eq]
      have h2 : (0:ℝ) ≤ (2:ℝ)^(M:ℝ) * (C₂:ℝ) :=
        (mul_pos (Real.rpow_pos_of_pos (by norm_num) _) hC₂.pos).le
      linarith
    have hYinv : (0:ℝ) ≤ Yc ^ (-(((M+2:ℕ)):ℝ)) := Real.rpow_nonneg hYcpos.le _
    have hXinv1 : (0:ℝ) ≤ X ^ (-(M:ℝ)) := Real.rpow_nonneg hXpos.le _
    have hmass : (∑' t : ℤ, ENNReal.ofReal ‖kk t * pieceHigh jj k jv (-(t:ℝ))‖)
        ≤ ENNReal.ofReal (2 * Cc * (Chigh * Yc ^ (-(((M+2:ℕ)):ℝ)))) := by
      have h1 : ∀ t : ℤ, ENNReal.ofReal ‖kk t * pieceHigh jj k jv (-(t:ℝ))‖
          ≤ ENNReal.ofReal (((iwArithFreqs ρ l).card : ℝ) * ‖pieceHigh jj k jv (-(t:ℝ))‖) := by
        intro t
        refine ENNReal.ofReal_le_ofReal ?_
        rw [norm_mul]
        exact mul_le_mul_of_nonneg_right (hkk t) (norm_nonneg _)
      have h2 : (∑' t : ℤ, ENNReal.ofReal (((iwArithFreqs ρ l).card : ℝ) * ‖pieceHigh jj k jv (-(t:ℝ))‖))
          = ENNReal.ofReal (((iwArithFreqs ρ l).card : ℝ)) *
              ∑' t : ℤ, ENNReal.ofReal ‖pieceHigh jj k jv (-(t:ℝ))‖ := by
        rw [← ENNReal.tsum_mul_left]
        refine tsum_congr fun t => ?_
        rw [ENNReal.ofReal_mul (by positivity)]
      have h3 : (∑' t : ℤ, ENNReal.ofReal ‖pieceHigh jj k jv (-(t:ℝ))‖)
          = ∑' t : ℤ, ENNReal.ofReal ‖pieceHigh jj k jv (t:ℝ)‖ := by
        simpa only [Int.cast_neg] using
          (tsum_comp_neg (f := fun t : ℤ => ENNReal.ofReal ‖pieceHigh jj k jv (t:ℝ)‖))
      have h4 : (∑' t : ℤ, ENNReal.ofReal ‖pieceHigh jj k jv (t:ℝ)‖)
          = ENNReal.ofReal (∑' t : ℤ, ‖pieceHigh jj k jv (t:ℝ)‖) :=
        (ENNReal.ofReal_tsum_of_nonneg (fun t => norm_nonneg _) hsummHigh).symm
      have h5 : (∑' t : ℤ, ‖pieceHigh jj k jv (t:ℝ)‖)
          ≤ Chigh * (2:ℝ)^(k+jv) * (max ((2:ℝ)^(k+jj-1)) 1) ^ (-(((M+2:ℕ)):ℝ)) :=
        hHighN k jj jv hk_nonpos hjj_nonneg hjv_nonneg hkjv hkjj
      calc (∑' t : ℤ, ENNReal.ofReal ‖kk t * pieceHigh jj k jv (-(t:ℝ))‖)
          ≤ ∑' t : ℤ, ENNReal.ofReal (((iwArithFreqs ρ l).card : ℝ) * ‖pieceHigh jj k jv (-(t:ℝ))‖) :=
            ENNReal.tsum_le_tsum h1
        _ = ENNReal.ofReal (((iwArithFreqs ρ l).card : ℝ)) *
              ∑' t : ℤ, ENNReal.ofReal ‖pieceHigh jj k jv (-(t:ℝ))‖ := h2
        _ = ENNReal.ofReal (((iwArithFreqs ρ l).card : ℝ)) *
              ENNReal.ofReal (∑' t : ℤ, ‖pieceHigh jj k jv (t:ℝ)‖) := by rw [h3, h4]
        _ ≤ ENNReal.ofReal (((iwArithFreqs ρ l).card : ℝ)) *
              ENNReal.ofReal (Chigh * (2:ℝ)^(k+jv) * Yc ^ (-(((M+2:ℕ)):ℝ))) := by
            refine mul_le_mul_of_nonneg_left ?_ (by positivity)
            refine ENNReal.ofReal_le_ofReal ?_
            rw [hYcdef]
            exact h5
        _ = ENNReal.ofReal (((iwArithFreqs ρ l).card : ℝ) *
              (Chigh * (2:ℝ)^(k+jv) * Yc ^ (-(((M+2:ℕ)):ℝ)))) := by
            rw [← ENNReal.ofReal_mul (by positivity)]
        _ ≤ ENNReal.ofReal (2 * Cc * (Chigh * Yc ^ (-(((M+2:ℕ)):ℝ)))) := by
            refine ENNReal.ofReal_le_ofReal ?_
            have h6 : ((iwArithFreqs ρ l).card : ℝ) * (2:ℝ)^(k+jv) ≤ 2 * Cc := hcard_gain
            have h7 : (0:ℝ) ≤ Chigh * Yc ^ (-(((M+2:ℕ)):ℝ)) := mul_nonneg hChigh.le hYinv
            calc ((iwArithFreqs ρ l).card : ℝ) * (Chigh * (2:ℝ)^(k+jv) * Yc ^ (-(((M+2:ℕ)):ℝ)))
                = (((iwArithFreqs ρ l).card : ℝ) * (2:ℝ)^(k+jv)) *
                    (Chigh * Yc ^ (-(((M+2:ℕ)):ℝ))) := by ring
              _ ≤ (2 * Cc) * (Chigh * Yc ^ (-(((M+2:ℕ)):ℝ))) :=
                  mul_le_mul_of_nonneg_right h6 h7
              _ = 2 * Cc * (Chigh * Yc ^ (-(((M+2:ℕ)):ℝ))) := by ring
    have hstep : eLpNorm (fun x : ℤ => if c ≤ x ∧ x ≤ d then Work.KMTContract.kmtProj ρ l k f x else 0)
          (ENNReal.ofReal q) Measure.count
        ≤ eLpNorm W2 (ENNReal.ofReal q) Measure.count + eLpNorm W3 (ENNReal.ofReal q) Measure.count := by
      have hcongr : (fun x : ℤ => if c ≤ x ∧ x ≤ d then Work.KMTContract.kmtProj ρ l k f x else 0)
          = (fun x : ℤ => (if c ≤ x ∧ x ≤ d then W2 x else 0) + (if c ≤ x ∧ x ≤ d then W3 x else 0)) :=
        funext hwin_eq
      rw [hcongr]
      have hh := eLpNorm_add_le (μ := Measure.count) (p := ENNReal.ofReal q)
        (f := fun x : ℤ => if c ≤ x ∧ x ≤ d then W2 x else 0)
        (g := fun x : ℤ => if c ≤ x ∧ x ≤ d then W3 x else 0)
        (by rw [← ENNReal.ofReal_one]; exact ENNReal.ofReal_le_ofReal (le_of_lt hq))
      have h2pt : ∀ x : ℤ, ‖(if c ≤ x ∧ x ≤ d then W2 x else 0)‖ ≤ ‖W2 x‖ := by
        intro x
        by_cases hx : c ≤ x ∧ x ≤ d <;> simp [hx]
      have h3pt : ∀ x : ℤ, ‖(if c ≤ x ∧ x ≤ d then W3 x else 0)‖ ≤ ‖W3 x‖ := by
        intro x
        by_cases hx : c ≤ x ∧ x ≤ d <;> simp [hx]
      have h2 : eLpNorm (fun x : ℤ => if c ≤ x ∧ x ≤ d then W2 x else 0) (ENNReal.ofReal q) Measure.count
          ≤ eLpNorm W2 (ENNReal.ofReal q) Measure.count :=
        eLpNorm_mono (hf := by pw_aesm) h2pt
      have h3 : eLpNorm (fun x : ℤ => if c ≤ x ∧ x ≤ d then W3 x else 0) (ENNReal.ofReal q) Measure.count
          ≤ eLpNorm W3 (ENNReal.ofReal q) Measure.count :=
        eLpNorm_mono (hf := by pw_aesm) h3pt
      calc eLpNorm (fun x : ℤ =>
              (if c ≤ x ∧ x ≤ d then W2 x else 0) + (if c ≤ x ∧ x ≤ d then W3 x else 0))
            (ENNReal.ofReal q) Measure.count
          = eLpNorm ((fun x : ℤ => if c ≤ x ∧ x ≤ d then W2 x else 0)
              + (fun x : ℤ => if c ≤ x ∧ x ≤ d then W3 x else 0))
              (ENNReal.ofReal q) Measure.count := rfl
        _ ≤ eLpNorm (fun x : ℤ => if c ≤ x ∧ x ≤ d then W2 x else 0) (ENNReal.ofReal q) Measure.count
              + eLpNorm (fun x : ℤ => if c ≤ x ∧ x ≤ d then W3 x else 0)
                  (ENNReal.ofReal q) Measure.count := hh
        _ ≤ eLpNorm W2 (ENNReal.ofReal q) Measure.count
              + eLpNorm W3 (ENNReal.ofReal q) Measure.count := add_le_add h2 h3
    have hcoef1' : ((CIq * angleBracket l * M2 : ℝ≥0) : ℝ) = (CIq:ℝ) * max ((l:ℝ)) 1 * (M2:ℝ) := by
      push_cast
      rw [hangle]
    have hW2le' : eLpNorm W2 (ENNReal.ofReal q) Measure.count
        ≤ ENNReal.ofReal ((CIq:ℝ) * max ((l:ℝ)) 1 * (M2:ℝ)) * eLpNorm f (ENNReal.ofReal q) Measure.count := by
      refine hW2le.trans (le_of_eq ?_)
      rw [hcoef1']
    have hW3le' : eLpNorm W3 (ENNReal.ofReal q) Measure.count
        ≤ ENNReal.ofReal (2 * Cc * (Chigh * Yc ^ (-(((M+2:ℕ)):ℝ))))
            * eLpNorm f (ENNReal.ofReal q) Measure.count :=
      hW3le.trans (mul_le_mul' hmass le_rfl)
    have hcomp : ((CIq:ℝ) * max ((l:ℝ)) 1 * (M2:ℝ))
        + (2 * Cc * (Chigh * Yc ^ (-(((M+2:ℕ)):ℝ))))
        ≤ Cfin * (max ((l:ℝ)) 1 * X ^ (-(M:ℝ))) := by
      calc ((CIq:ℝ) * max ((l:ℝ)) 1 * (M2:ℝ)) + (2 * Cc * (Chigh * Yc ^ (-(((M+2:ℕ)):ℝ))))
          = max ((l:ℝ)) 1 * (K1 * Yc ^ (-(((M+2:ℕ)):ℝ))) + K2 * Yc ^ (-(((M+2:ℕ)):ℝ)) := by
            rw [hM2coe, hK1def, hK2def]; ring
        _ ≤ max ((l:ℝ)) 1 * (8 ^ (M+2) * K1 * X ^ (-(M:ℝ)))
            + max ((l:ℝ)) 1 * (8 ^ (M+2) * K2 * X ^ (-(M:ℝ))) := by
            refine add_le_add ?_ ?_
            · calc max ((l:ℝ)) 1 * (K1 * Yc ^ (-(((M+2:ℕ)):ℝ)))
                  ≤ max ((l:ℝ)) 1 * (K1 * (8 ^ (M+2) * X ^ (-(M:ℝ)))) :=
                    mul_le_mul_of_nonneg_left (mul_le_mul_of_nonneg_left hYc_small hK1nn) hl1'
                _ = max ((l:ℝ)) 1 * (8 ^ (M+2) * K1 * X ^ (-(M:ℝ))) := by ring
            · have h2 : K2 * Yc ^ (-(((M+2:ℕ)):ℝ)) ≤ K2 * (8 ^ (M+2) * X ^ (-(M:ℝ))) :=
                mul_le_mul_of_nonneg_left hYc_small hK2nn
              have h3 : K2 * (8 ^ (M+2) * X ^ (-(M:ℝ))) = 8 ^ (M+2) * K2 * X ^ (-(M:ℝ)) := by ring
              calc K2 * Yc ^ (-(((M+2:ℕ)):ℝ)) ≤ 8 ^ (M+2) * K2 * X ^ (-(M:ℝ)) := by rw [← h3]; exact h2
                _ = 1 * (8 ^ (M+2) * K2 * X ^ (-(M:ℝ))) := (one_mul _).symm
                _ ≤ max ((l:ℝ)) 1 * (8 ^ (M+2) * K2 * X ^ (-(M:ℝ))) :=
                    mul_le_mul_of_nonneg_right hl1 (by positivity)
        _ = max ((l:ℝ)) 1 * (8 ^ (M+2) * (K1 + K2) * X ^ (-(M:ℝ))) := by ring
        _ ≤ max ((l:ℝ)) 1 * (Cfin * X ^ (-(M:ℝ))) :=
            mul_le_mul_of_nonneg_left (mul_le_mul_of_nonneg_right hKsum hXinv1) hl1'
        _ = Cfin * (max ((l:ℝ)) 1 * X ^ (-(M:ℝ))) := by ring
    have hfinal : eLpNorm (fun x : ℤ => if c ≤ x ∧ x ≤ d then Work.KMTContract.kmtProj ρ l k f x else 0)
          (ENNReal.ofReal q) Measure.count
        ≤ (Cfinn : ℝ≥0∞) *
            ENNReal.ofReal (max ((l:ℝ)) 1 * (max ((2 : ℝ) ^ k * ((c - b : ℤ) : ℝ)) 1) ^ (-(M:ℝ))) *
            eLpNorm f (ENNReal.ofReal q) Measure.count := by
      have hY3 : (0:ℝ) ≤ (CIq:ℝ) * max ((l:ℝ)) 1 * (M2:ℝ) := by
        refine mul_nonneg (mul_nonneg hCIq.le hl1') ?_
        rw [hM2coe]
        exact mul_nonneg (mul_nonneg hCm.le hYinv) hEtaMnn
      have hY2b : (0:ℝ) ≤ 2 * Cc * (Chigh * Yc ^ (-(((M+2:ℕ)):ℝ))) :=
        mul_nonneg (by positivity) (mul_nonneg hChigh.le hYinv)
      have hcoef : ENNReal.ofReal ((CIq:ℝ) * max ((l:ℝ)) 1 * (M2:ℝ))
          + ENNReal.ofReal (2 * Cc * (Chigh * Yc ^ (-(((M+2:ℕ)):ℝ))))
          ≤ (Cfinn : ℝ≥0∞) *
              ENNReal.ofReal (max ((l:ℝ)) 1 * (max ((2 : ℝ) ^ k * ((c - b : ℤ) : ℝ)) 1) ^ (-(M:ℝ))) := by
        rw [← ENNReal.ofReal_add hY3 hY2b]
        rw [← ENNReal.ofReal_coe_nnreal (p := Cfinn), hCfinnR]
        rw [← ENNReal.ofReal_mul (le_of_lt hCfinpos)]
        refine ENNReal.ofReal_le_ofReal ?_
        rw [← hXdef]
        exact hcomp
      calc eLpNorm (fun x : ℤ => if c ≤ x ∧ x ≤ d then Work.KMTContract.kmtProj ρ l k f x else 0)
              (ENNReal.ofReal q) Measure.count
          ≤ eLpNorm W2 (ENNReal.ofReal q) Measure.count + eLpNorm W3 (ENNReal.ofReal q) Measure.count := hstep
        _ ≤ ENNReal.ofReal ((CIq:ℝ) * max ((l:ℝ)) 1 * (M2:ℝ)) * eLpNorm f (ENNReal.ofReal q) Measure.count
            + ENNReal.ofReal (2 * Cc * (Chigh * Yc ^ (-(((M+2:ℕ)):ℝ))))
              * eLpNorm f (ENNReal.ofReal q) Measure.count := add_le_add hW2le' hW3le'
        _ = (ENNReal.ofReal ((CIq:ℝ) * max ((l:ℝ)) 1 * (M2:ℝ))
              + ENNReal.ofReal (2 * Cc * (Chigh * Yc ^ (-(((M+2:ℕ)):ℝ)))))
              * eLpNorm f (ENNReal.ofReal q) Measure.count := by rw [add_mul]
        _ ≤ (Cfinn : ℝ≥0∞) *
              ENNReal.ofReal (max ((l:ℝ)) 1 * (max ((2 : ℝ) ^ k * ((c - b : ℤ) : ℝ)) 1) ^ (-(M:ℝ))) *
              eLpNorm f (ENNReal.ofReal q) Measure.count := mul_le_mul' hcoef le_rfl
    exact hfinal


theorem bmp_eventuallyEq_oneZ {jj : ℤ} {x : ℝ} (hx : |x| < (2 : ℝ) ^ (jj - 1)) :
    ((bmp jj : SchwartzMap ℝ ℂ) : ℝ → ℂ) =ᶠ[𝓝 x] (fun _ => (1 : ℂ)) := by
  show ∀ᶠ y in 𝓝 x, ((bmp jj : SchwartzMap ℝ ℂ) : ℝ → ℂ) y = 1
  rw [Metric.eventually_nhds_iff]
  refine ⟨(2 : ℝ) ^ (jj - 1) - |x|, by linarith, ?_⟩
  intro y hy
  have hy' : |y - x| < (2 : ℝ) ^ (jj - 1) - |x| := by rwa [Real.dist_eq] at hy
  have h1 : |y| ≤ |x| + |y - x| := by
    have := abs_add_le x (y - x)
    rwa [show x + (y - x) = y by ring] at this
  rw [bmp_one_of_le jj (by linarith)]

/-- The middle piece `λ_k - η_{≤jj} λ_k` vanishes in a neighbourhood of every point with
`|x| < 2^{jj-1}`. -/
theorem midPiece_eventuallyEq_zeroZ (k jj : ℤ) {x : ℝ} (hx : |x| < (2 : ℝ) ^ (jj - 1)) :
    ((lam k - mS (bmp jj) (lam k) : SchwartzMap ℝ ℂ) : ℝ → ℂ)
      =ᶠ[𝓝 x] (fun _ => (0 : ℂ)) := by
  filter_upwards [bmp_eventuallyEq_oneZ (jj := jj) hx] with y hy
  show (lam k) y - (bmp jj) y * (lam k) y = 0
  rw [hy]; ring

/-- The derivative of the middle piece vanishes at every point with `|x| < 2^{jj-1}`. -/
theorem deriv_midPiece_eq_zero (k jj : ℤ) {x : ℝ} (hx : |x| < (2 : ℝ) ^ (jj - 1)) :
    deriv ((lam k - mS (bmp jj) (lam k) : SchwartzMap ℝ ℂ) : ℝ → ℂ) x = 0 := by
  have h := (midPiece_eventuallyEq_zeroZ k jj hx).deriv_eq
  simpa using h

/-- The product rule for the middle piece. -/
theorem deriv_midPiece_eqZ (k jj : ℤ) (x : ℝ) :
    deriv ((lam k - mS (bmp jj) (lam k) : SchwartzMap ℝ ℂ) : ℝ → ℂ) x
      = deriv (⇑(lam k)) x * (1 - (bmp jj) x)
        + (lam k) x * (- deriv (⇑(bmp jj)) x) := by
  have hF : ((lam k - mS (bmp jj) (lam k) : SchwartzMap ℝ ℂ) : ℝ → ℂ)
      = fun y : ℝ => (lam k) y * (1 - (bmp jj) y) := by
    funext y
    show (lam k) y - (bmp jj) y * (lam k) y = _
    ring
  rw [hF]
  have h1 : deriv (fun y : ℝ => (lam k) y * (1 - (bmp jj) y)) x
      = deriv (fun y : ℝ => (lam k) y) x * (1 - (bmp jj) x)
        + (lam k) x * deriv (fun y : ℝ => 1 - (bmp jj) y) x := by
    rw [show (fun y : ℝ => (lam k) y * (1 - (bmp jj) y))
        = ((fun y : ℝ => (lam k) y) * (fun y : ℝ => 1 - (bmp jj) y)) from rfl]
    exact deriv_mul ((lam k).differentiable.differentiableAt)
      (((bmp jj).differentiable.differentiableAt).const_sub 1)
  rw [h1, deriv_const_sub]

/-! ## The main estimate -/

theorem pieceBDerivTailL1 (N : ℕ) : ∃ C : ℝ, 0 < C ∧ ∀ (k jj : ℤ), k ≤ 0 → 0 ≤ jj → 0 ≤ k + jj → ∫ x : ℝ, ‖deriv (((Work.KMTAreas.A4.lam k - Work.KMTAreas.A4.mS (Work.KMTAreas.A4.bmp jj) (Work.KMTAreas.A4.lam k)) : SchwartzMap ℝ ℂ) : ℝ → ℂ) x‖ ≤ C * (2:ℝ)^k * (max ((2:ℝ)^(k+jj-1)) 1) ^ (-(N:ℝ)) := by
  obtain ⟨Cd, hCdpos, hCd⟩ := offCutDeriv
  obtain ⟨C₁, hC₁pos, hC₁⟩ := offLamTail 1 N
  obtain ⟨C₀, hC₀pos, hC₀⟩ := offLamTail 0 N
  refine ⟨C₁ + Cd * C₀, add_pos hC₁pos (mul_pos hCdpos hC₀pos), ?_⟩
  intro k jj hk hjj hkj
  -- abbreviations
  set R : ℝ := (2 : ℝ) ^ (jj - 1) with hR
  set T : Set ℝ := {x : ℝ | R ≤ |x|} with hT
  have hRpos : 0 < R := by rw [hR]; exact zpow_pos (by norm_num) (jj - 1)
  have hTmeas : MeasurableSet T := by
    have h := absSet_eq_Ici_union_Iic hRpos.le
    rw [hT, h]
    exact measurableSet_Ici.union measurableSet_Iic
  have hkR : (2 : ℝ) ^ k * R = (2 : ℝ) ^ (k + jj - 1) := by
    rw [hR, ← zpow_add₀ (by norm_num : (2 : ℝ) ≠ 0)]
    congr 1
    ring
  -- **the pointwise bound**
  have hpoint : ∀ x : ℝ, ‖deriv ((lam k - mS (bmp jj) (lam k) : SchwartzMap ℝ ℂ) : ℝ → ℂ) x‖
      ≤ ‖deriv (⇑(lam k)) x‖ + ‖(lam k) x‖ * (Cd * (2 : ℝ) ^ (-jj)) := by
    intro x
    by_cases hx : R ≤ |x|
    · have h1 := deriv_midPiece_eqZ k jj x
      have h2 : ‖1 - (bmp jj) x‖ ≤ 1 := norm_one_sub_bmp_le jj x
      have h3 : ‖deriv (⇑(bmp jj)) x‖ ≤ Cd * (2 : ℝ) ^ (-jj) := (hCd jj x).1
      calc ‖deriv ((lam k - mS (bmp jj) (lam k) : SchwartzMap ℝ ℂ) : ℝ → ℂ) x‖
          = ‖deriv (⇑(lam k)) x * (1 - (bmp jj) x)
              + (lam k) x * (- deriv (⇑(bmp jj)) x)‖ := by rw [h1]
        _ ≤ ‖deriv (⇑(lam k)) x * (1 - (bmp jj) x)‖
              + ‖(lam k) x * (- deriv (⇑(bmp jj)) x)‖ := norm_add_le _ _
        _ = ‖deriv (⇑(lam k)) x‖ * ‖1 - (bmp jj) x‖
              + ‖(lam k) x‖ * ‖deriv (⇑(bmp jj)) x‖ := by
              rw [norm_mul, norm_mul, norm_neg]
        _ ≤ ‖deriv (⇑(lam k)) x‖ * 1 + ‖(lam k) x‖ * (Cd * (2 : ℝ) ^ (-jj)) := by
              gcongr
        _ = ‖deriv (⇑(lam k)) x‖ + ‖(lam k) x‖ * (Cd * (2 : ℝ) ^ (-jj)) := by ring
    · have hx' : |x| < (2 : ℝ) ^ (jj - 1) := by rw [← hR]; exact not_le.mp hx
      have hz : deriv ((lam k - mS (bmp jj) (lam k) : SchwartzMap ℝ ℂ) : ℝ → ℂ) x = 0 :=
        deriv_midPiece_eq_zero k jj hx'
      rw [hz, norm_zero]
      exact add_nonneg (norm_nonneg _)
        (mul_nonneg (norm_nonneg _) (mul_nonneg hCdpos.le (by positivity)))
  -- **the pointwise `ENNReal` bound**
  have hpointE : ∀ x : ℝ,
      ENNReal.ofReal (‖deriv ((lam k - mS (bmp jj) (lam k) : SchwartzMap ℝ ℂ) : ℝ → ℂ) x‖)
        ≤ T.indicator (fun x => ENNReal.ofReal (‖deriv (⇑(lam k)) x‖)) x
          + ENNReal.ofReal (Cd * (2 : ℝ) ^ (-jj)) *
              T.indicator (fun x => ENNReal.ofReal (‖(lam k) x‖)) x := by
    intro x
    by_cases hx : x ∈ T
    · rw [Set.indicator_of_mem hx, Set.indicator_of_mem hx]
      have h := hpoint x
      have hCdnn : 0 ≤ Cd * (2 : ℝ) ^ (-jj) := by positivity
      calc ENNReal.ofReal (‖deriv ((lam k - mS (bmp jj) (lam k) : SchwartzMap ℝ ℂ) : ℝ → ℂ) x‖)
          ≤ ENNReal.ofReal (‖deriv (⇑(lam k)) x‖ + ‖(lam k) x‖ * (Cd * (2 : ℝ) ^ (-jj))) :=
              ENNReal.ofReal_le_ofReal h
        _ = ENNReal.ofReal (‖deriv (⇑(lam k)) x‖)
              + ENNReal.ofReal (Cd * (2 : ℝ) ^ (-jj)) * ENNReal.ofReal (‖(lam k) x‖) := by
              rw [ENNReal.ofReal_add (norm_nonneg _) (by positivity),
                ENNReal.ofReal_mul (norm_nonneg _), mul_comm]
        _ = ENNReal.ofReal (‖deriv (⇑(lam k)) x‖)
              + ENNReal.ofReal (Cd * (2 : ℝ) ^ (-jj)) * ENNReal.ofReal (‖(lam k) x‖) := rfl
    · rw [Set.indicator_of_notMem hx, Set.indicator_of_notMem hx]
      have hx' : |x| < (2 : ℝ) ^ (jj - 1) := by
        simp only [hT, Set.mem_ofPred_eq] at hx
        rw [← hR]
        exact not_le.mp hx
      rw [deriv_midPiece_eq_zero k jj hx']
      simp
  -- **the two tail estimates**
  have hb1 : ∫⁻ x in T, ENNReal.ofReal (‖deriv (⇑(lam k)) x‖)
      ≤ ENNReal.ofReal (C₁ * (2 : ℝ) ^ k * (max ((2 : ℝ) ^ (k + jj - 1)) 1) ^ (-(N : ℝ))) := by
    have h1 := hC₁ k R hRpos.le
    rw [pow_one] at h1
    have hfun : (fun x : ℝ => ENNReal.ofReal (‖deriv (⇑(lam k)) x‖))
        = fun x : ℝ => ‖iteratedDeriv 1 (⇑(Work.KMTAreas.A7.etaMult_K k)) x‖ₑ := by
      funext x
      simp only [ofReal_norm, iteratedDeriv_one, lam_eq_etaMult_K]
    rw [hT, hfun, ← hkR]
    exact h1
  have hb2 : ∫⁻ x in T, ENNReal.ofReal (‖(lam k) x‖)
      ≤ ENNReal.ofReal (C₀ * (max ((2 : ℝ) ^ (k + jj - 1)) 1) ^ (-(N : ℝ))) := by
    have h1 := hC₀ k R hRpos.le
    rw [pow_zero, mul_one] at h1
    have hfun : (fun x : ℝ => ENNReal.ofReal (‖(lam k) x‖))
        = fun x : ℝ => ‖iteratedDeriv 0 (⇑(Work.KMTAreas.A7.etaMult_K k)) x‖ₑ := by
      funext x
      simp only [ofReal_norm, iteratedDeriv_zero, lam_eq_etaMult_K]
    rw [hT, hfun, ← hkR]
    exact h1
  -- **the `lintegral` chain**
  have hlin : ∫⁻ x, ENNReal.ofReal
        (‖deriv ((lam k - mS (bmp jj) (lam k) : SchwartzMap ℝ ℂ) : ℝ → ℂ) x‖)
      ≤ ENNReal.ofReal (C₁ * (2 : ℝ) ^ k * (max ((2 : ℝ) ^ (k + jj - 1)) 1) ^ (-(N : ℝ)))
        + ENNReal.ofReal (Cd * (2 : ℝ) ^ (-jj)) *
            ENNReal.ofReal (C₀ * (max ((2 : ℝ) ^ (k + jj - 1)) 1) ^ (-(N : ℝ))) := by
    have hmeasA : Measurable
        (fun x : ℝ => T.indicator (fun x => ENNReal.ofReal (‖deriv (⇑(lam k)) x‖)) x) :=
      Measurable.indicator (by fun_prop) hTmeas
    have hmeasB : Measurable (fun x : ℝ => T.indicator (fun x => ENNReal.ofReal (‖(lam k) x‖)) x) :=
      Measurable.indicator (by fun_prop) hTmeas
    calc ∫⁻ x, ENNReal.ofReal
          (‖deriv ((lam k - mS (bmp jj) (lam k) : SchwartzMap ℝ ℂ) : ℝ → ℂ) x‖)
        ≤ ∫⁻ x, (T.indicator (fun x => ENNReal.ofReal (‖deriv (⇑(lam k)) x‖)) x
            + ENNReal.ofReal (Cd * (2 : ℝ) ^ (-jj)) *
                T.indicator (fun x => ENNReal.ofReal (‖(lam k) x‖)) x) :=
            lintegral_mono hpointE
      _ = (∫⁻ x, T.indicator (fun x => ENNReal.ofReal (‖deriv (⇑(lam k)) x‖)) x)
            + ∫⁻ x, ENNReal.ofReal (Cd * (2 : ℝ) ^ (-jj)) *
                T.indicator (fun x => ENNReal.ofReal (‖(lam k) x‖)) x :=
            lintegral_add_left hmeasA _
      _ = (∫⁻ x in T, ENNReal.ofReal (‖deriv (⇑(lam k)) x‖))
            + ENNReal.ofReal (Cd * (2 : ℝ) ^ (-jj)) *
                ∫⁻ x in T, ENNReal.ofReal (‖(lam k) x‖) := by
            rw [lintegral_indicator hTmeas, lintegral_const_mul _ hmeasB, lintegral_indicator hTmeas]
      _ ≤ ENNReal.ofReal (C₁ * (2 : ℝ) ^ k * (max ((2 : ℝ) ^ (k + jj - 1)) 1) ^ (-(N : ℝ)))
            + ENNReal.ofReal (Cd * (2 : ℝ) ^ (-jj)) *
                ENNReal.ofReal (C₀ * (max ((2 : ℝ) ^ (k + jj - 1)) 1) ^ (-(N : ℝ))) := by
            gcongr
  -- **the final real arithmetic**
  have hArith : C₁ * (2 : ℝ) ^ k * (max ((2 : ℝ) ^ (k + jj - 1)) 1) ^ (-(N : ℝ))
      + Cd * (2 : ℝ) ^ (-jj) * (C₀ * (max ((2 : ℝ) ^ (k + jj - 1)) 1) ^ (-(N : ℝ)))
      ≤ (C₁ + Cd * C₀) * (2 : ℝ) ^ k * (max ((2 : ℝ) ^ (k + jj - 1)) 1) ^ (-(N : ℝ)) := by
    have hM1 : (1 : ℝ) ≤ max ((2 : ℝ) ^ (k + jj - 1)) 1 := le_max_right _ _
    have hMnn : 0 ≤ (max ((2 : ℝ) ^ (k + jj - 1)) 1) ^ (-(N : ℝ)) :=
      Real.rpow_nonneg (le_trans zero_le_one hM1) _
    have h2k : (0 : ℝ) < (2 : ℝ) ^ k := zpow_pos (by norm_num) k
    have hjj2 : (2 : ℝ) ^ (-jj) ≤ (2 : ℝ) ^ k :=
      zpow_le_zpow_right₀ (by norm_num : (1 : ℝ) ≤ 2) (by omega)
    have hle : (2 : ℝ) ^ (-jj) * (max ((2 : ℝ) ^ (k + jj - 1)) 1) ^ (-(N : ℝ))
        ≤ (2 : ℝ) ^ k * (max ((2 : ℝ) ^ (k + jj - 1)) 1) ^ (-(N : ℝ)) :=
      mul_le_mul_of_nonneg_right hjj2 hMnn
    have hsub : Cd * (2 : ℝ) ^ (-jj) * (C₀ * (max ((2 : ℝ) ^ (k + jj - 1)) 1) ^ (-(N : ℝ)))
        ≤ Cd * C₀ * ((2 : ℝ) ^ k * (max ((2 : ℝ) ^ (k + jj - 1)) 1) ^ (-(N : ℝ))) := by
      calc Cd * (2 : ℝ) ^ (-jj) * (C₀ * (max ((2 : ℝ) ^ (k + jj - 1)) 1) ^ (-(N : ℝ)))
          = (Cd * C₀) * ((2 : ℝ) ^ (-jj) * (max ((2 : ℝ) ^ (k + jj - 1)) 1) ^ (-(N : ℝ))) := by
            ring
        _ ≤ (Cd * C₀) * ((2 : ℝ) ^ k * (max ((2 : ℝ) ^ (k + jj - 1)) 1) ^ (-(N : ℝ))) :=
            mul_le_mul_of_nonneg_left hle (mul_nonneg hCdpos.le hC₀pos.le)
    calc C₁ * (2 : ℝ) ^ k * (max ((2 : ℝ) ^ (k + jj - 1)) 1) ^ (-(N : ℝ))
        + Cd * (2 : ℝ) ^ (-jj) * (C₀ * (max ((2 : ℝ) ^ (k + jj - 1)) 1) ^ (-(N : ℝ)))
        ≤ C₁ * (2 : ℝ) ^ k * (max ((2 : ℝ) ^ (k + jj - 1)) 1) ^ (-(N : ℝ))
          + Cd * C₀ * ((2 : ℝ) ^ k * (max ((2 : ℝ) ^ (k + jj - 1)) 1) ^ (-(N : ℝ))) := by
          linarith [hsub]
      _ = (C₁ + Cd * C₀) * (2 : ℝ) ^ k
            * (max ((2 : ℝ) ^ (k + jj - 1)) 1) ^ (-(N : ℝ)) := by ring
  -- **assembly**
  have hInt : Integrable (fun x : ℝ =>
      ‖deriv ((lam k - mS (bmp jj) (lam k) : SchwartzMap ℝ ℂ) : ℝ → ℂ) x‖) := by
    have hd : ∀ x : ℝ, deriv (⇑(lam k) - ⇑(mS (bmp jj) (lam k))) x
        = deriv (⇑(lam k)) x - deriv (⇑(mS (bmp jj) (lam k))) x := by
      intro x
      rw [deriv_sub]
      · exact (lam k).differentiable.differentiableAt
      · exact (mS (bmp jj) (lam k)).differentiable.differentiableAt
    have h := (SchwartzMap.integrable (SchwartzMap.derivCLM ℂ ℂ (lam k - mS (bmp jj) (lam k))) (μ := volume)).norm
    simpa [funext hd] using h
  have hfinal : ∫⁻ x, ENNReal.ofReal
        (‖deriv ((lam k - mS (bmp jj) (lam k) : SchwartzMap ℝ ℂ) : ℝ → ℂ) x‖)
      ≤ ENNReal.ofReal ((C₁ + Cd * C₀) * (2 : ℝ) ^ k
          * (max ((2 : ℝ) ^ (k + jj - 1)) 1) ^ (-(N : ℝ))) := by
    have hnn1 : 0 ≤ C₁ * (2 : ℝ) ^ k * (max ((2 : ℝ) ^ (k + jj - 1)) 1) ^ (-(N : ℝ)) := by
      have h1 : (1 : ℝ) ≤ max ((2 : ℝ) ^ (k + jj - 1)) 1 := le_max_right _ _
      positivity
    have hnn2 : 0 ≤ Cd * (2 : ℝ) ^ (-jj) := by positivity
    have hnn3 : 0 ≤ C₀ * (max ((2 : ℝ) ^ (k + jj - 1)) 1) ^ (-(N : ℝ)) := by
      have h1 : (1 : ℝ) ≤ max ((2 : ℝ) ^ (k + jj - 1)) 1 := le_max_right _ _
      positivity
    calc ∫⁻ x, ENNReal.ofReal
          (‖deriv ((lam k - mS (bmp jj) (lam k) : SchwartzMap ℝ ℂ) : ℝ → ℂ) x‖)
        ≤ ENNReal.ofReal (C₁ * (2 : ℝ) ^ k * (max ((2 : ℝ) ^ (k + jj - 1)) 1) ^ (-(N : ℝ)))
          + ENNReal.ofReal (Cd * (2 : ℝ) ^ (-jj)) *
              ENNReal.ofReal (C₀ * (max ((2 : ℝ) ^ (k + jj - 1)) 1) ^ (-(N : ℝ))) := hlin
      _ = ENNReal.ofReal (C₁ * (2 : ℝ) ^ k * (max ((2 : ℝ) ^ (k + jj - 1)) 1) ^ (-(N : ℝ))
            + Cd * (2 : ℝ) ^ (-jj) * (C₀ * (max ((2 : ℝ) ^ (k + jj - 1)) 1) ^ (-(N : ℝ)))) := by
            rw [← ENNReal.ofReal_mul hnn2, ← ENNReal.ofReal_add hnn1 (mul_nonneg hnn2 hnn3)]
      _ ≤ ENNReal.ofReal ((C₁ + Cd * C₀) * (2 : ℝ) ^ k
            * (max ((2 : ℝ) ^ (k + jj - 1)) 1) ^ (-(N : ℝ))) :=
            ENNReal.ofReal_le_ofReal hArith
  calc ∫ x : ℝ, ‖deriv ((lam k - mS (bmp jj) (lam k) : SchwartzMap ℝ ℂ) : ℝ → ℂ) x‖
      = (ENNReal.ofReal
          (∫ x : ℝ, ‖deriv ((lam k - mS (bmp jj) (lam k) : SchwartzMap ℝ ℂ) : ℝ → ℂ) x‖)).toReal :=
          (ENNReal.toReal_ofReal (integral_nonneg fun x => norm_nonneg _)).symm
    _ = (∫⁻ x, ENNReal.ofReal
          (‖deriv ((lam k - mS (bmp jj) (lam k) : SchwartzMap ℝ ℂ) : ℝ → ℂ) x‖)).toReal := by
          rw [ofReal_integral_eq_lintegral_ofReal hInt (Eventually.of_forall fun x => norm_nonneg _)]
    _ ≤ (ENNReal.ofReal ((C₁ + Cd * C₀) * (2 : ℝ) ^ k
          * (max ((2 : ℝ) ^ (k + jj - 1)) 1) ^ (-(N : ℝ)))).toReal :=
          ENNReal.toReal_mono ENNReal.ofReal_ne_top hfinal
    _ = (C₁ + Cd * C₀) * (2 : ℝ) ^ k * (max ((2 : ℝ) ^ (k + jj - 1)) 1) ^ (-(N : ℝ)) := by
          have h1 : (1 : ℝ) ≤ max ((2 : ℝ) ^ (k + jj - 1)) 1 := le_max_right _ _
          rw [ENNReal.toReal_ofReal (by positivity)]
/-- The coercion of the `derivCLM` of a Schwartz function is its derivative. -/
theorem coe_derivCLMZ (f : SchwartzMap ℝ ℂ) :
    ⇑(SchwartzMap.derivCLM ℂ ℂ f) = deriv (f : ℝ → ℂ) :=
  funext fun x => SchwartzMap.derivCLM_apply ℂ f x

theorem cruxBound_holds : CruxBound := by
  intro N
  obtain ⟨Cs, hCs0, hSamp⟩ := Work.KMTAreas.A4.offSample
  obtain ⟨Cb, hCb0, hBd⟩ := pieceBDerivTailL1 N
  obtain ⟨Cmom, hCmom0, hMom⟩ := Work.KMTAreas.A4.offLamMoment
  have hEtaMpos : (0 : ℝ) < (Work.KMTAreas.A7.etaMult_M : ℝ) := by
    exact_mod_cast Work.KMTAreas.A7.etaMult_M_pos
  refine ⟨Cs * (Cmom + 1 + (Work.KMTAreas.A7.etaMult_M : ℝ)) * Cb, by positivity, ?_⟩
  intro k jj jv hk hjj hjv hkjv hkjj
  set Y : ℝ := (max ((2 : ℝ) ^ (k + jj - 1)) 1) ^ (-(N : ℝ)) with hY
  have hIbnn : 0 ≤ ∫ x : ℝ, ‖deriv (pieceB jj k : ℝ → ℂ) x‖ :=
    integral_nonneg fun x => norm_nonneg _
  have hI : (∫ x : ℝ, ‖deriv (pieceB jj k : ℝ → ℂ) x‖)
      ≤ Cb * (2 : ℝ) ^ k * Y := by
    have h := hBd k jj hk hjj hkjj
    simpa only [hY] using h
  have hmom : (∫ y : ℝ, |y| * ‖(lam (-jv)) y‖) ≤ Cmom * (2 : ℝ) ^ jv := by
    have h := hMom (-jv)
    simpa [Work.KMTAreas.A4.lam_eq_etaMult_K] using h
  have hvl1 : (∫ y : ℝ, ‖(lam (-jv)) y‖) ≤ (Work.KMTAreas.A7.etaMult_M : ℝ) := by
    have h3 : eLpNorm (⇑(Work.KMTAreas.A7.etaMult_K (-jv))) 1 volume
        ≤ ENNReal.ofReal (Work.KMTAreas.A7.etaMult_M : ℝ) :=
      Work.KMTAreas.A7.etaMult_K_norm (-jv)
    rw [eLpNorm_one_eq_ofReal_integral _ (SchwartzMap.integrable _)] at h3
    rw [← Work.KMTAreas.A4.lam_eq_etaMult_K (-jv)] at h3
    exact (ENNReal.ofReal_le_ofReal_iff (by positivity)).mp h3
  have hA : (∫ x : ℝ, ‖pieceHigh jj k jv x‖)
      ≤ (∫ y : ℝ, |y| * ‖(lam (-jv)) y‖) * ∫ x : ℝ, ‖deriv (pieceB jj k : ℝ → ℂ) x‖ := by
    have hφ : ∀ x : ℝ, pieceHigh jj k jv x
        = (pieceB jj k) x - SchwartzMap.convolution (ContinuousLinearMap.mul ℂ ℂ)
            (pieceB jj k) (lam (-jv)) x := by
      intro x
      show ((pieceB jj k) - cS (pieceB jj k) (lam (-jv))) x = _
      rw [sub_apply]
      rfl
    calc (∫ x : ℝ, ‖pieceHigh jj k jv x‖)
        = ∫ x : ℝ, ‖(pieceB jj k) x - SchwartzMap.convolution (ContinuousLinearMap.mul ℂ ℂ)
            (pieceB jj k) (lam (-jv)) x‖ := by
          apply integral_congr_ae
          filter_upwards with x
          rw [hφ]
      _ ≤ (∫ y : ℝ, |y| * ‖(lam (-jv)) y‖) * ∫ x : ℝ, ‖deriv (pieceB jj k : ℝ → ℂ) x‖ :=
          Work.KMTAreas.A4.offConvMoment (pieceB jj k) (lam (-jv))
            (Work.KMTAreas.A4.integral_lam (-jv))
  have hB2 : (∫ x : ℝ, ‖deriv (pieceHigh jj k jv : ℝ → ℂ) x‖)
      ≤ (1 + (Work.KMTAreas.A7.etaMult_M : ℝ)) * ∫ x : ℝ, ‖deriv (pieceB jj k : ℝ → ℂ) x‖ := by
    have hd1 := Work.A4Z.derivCSEq (pieceB jj k) (lam (-jv))
    have hpt : ∀ x : ℝ, deriv (pieceHigh jj k jv : ℝ → ℂ) x
        = deriv (pieceB jj k : ℝ → ℂ) x
          - SchwartzMap.convolution (ContinuousLinearMap.mul ℂ ℂ)
              (SchwartzMap.derivCLM ℂ ℂ (pieceB jj k)) (lam (-jv)) x := by
      intro x
      rw [← SchwartzMap.derivCLM_apply ℂ (pieceHigh jj k jv) x]
      show (SchwartzMap.derivCLM ℂ ℂ
        ((pieceB jj k) - cS (pieceB jj k) (lam (-jv)))) x = _
      rw [map_sub, hd1, sub_apply, SchwartzMap.derivCLM_apply]
      rfl
    have hIa : Integrable (fun x : ℝ => deriv (pieceB jj k : ℝ → ℂ) x) := by
      have h := SchwartzMap.integrable (SchwartzMap.derivCLM ℂ ℂ (pieceB jj k)) (μ := volume)
      rw [coe_derivCLMZ] at h
      exact h
    have hIb : Integrable (fun x : ℝ => SchwartzMap.convolution (ContinuousLinearMap.mul ℂ ℂ)
        (SchwartzMap.derivCLM ℂ ℂ (pieceB jj k)) (lam (-jv)) x) :=
      SchwartzMap.integrable (SchwartzMap.convolution (ContinuousLinearMap.mul ℂ ℂ)
        (SchwartzMap.derivCLM ℂ ℂ (pieceB jj k)) (lam (-jv))) (μ := volume)
    have hInt1 : Integrable (fun x : ℝ => ‖deriv (pieceB jj k : ℝ → ℂ) x‖) := hIa.norm
    have hInt2 : Integrable (fun x : ℝ => ‖SchwartzMap.convolution (ContinuousLinearMap.mul ℂ ℂ)
        (SchwartzMap.derivCLM ℂ ℂ (pieceB jj k)) (lam (-jv)) x‖) := hIb.norm
    have hIntd : Integrable (fun x : ℝ => ‖deriv (pieceB jj k : ℝ → ℂ) x
        - SchwartzMap.convolution (ContinuousLinearMap.mul ℂ ℂ)
            (SchwartzMap.derivCLM ℂ ℂ (pieceB jj k)) (lam (-jv)) x‖) :=
      (hIa.sub hIb).norm
    have htri : (∫ x : ℝ, ‖deriv (pieceHigh jj k jv : ℝ → ℂ) x‖)
        ≤ (∫ x : ℝ, ‖deriv (pieceB jj k : ℝ → ℂ) x‖)
          + ∫ x : ℝ, ‖SchwartzMap.convolution (ContinuousLinearMap.mul ℂ ℂ)
              (SchwartzMap.derivCLM ℂ ℂ (pieceB jj k)) (lam (-jv)) x‖ := by
      calc (∫ x : ℝ, ‖deriv (pieceHigh jj k jv : ℝ → ℂ) x‖)
          = ∫ x : ℝ, ‖deriv (pieceB jj k : ℝ → ℂ) x
              - SchwartzMap.convolution (ContinuousLinearMap.mul ℂ ℂ)
                  (SchwartzMap.derivCLM ℂ ℂ (pieceB jj k)) (lam (-jv)) x‖ := by
            apply integral_congr_ae
            filter_upwards with x
            rw [hpt]
        _ ≤ ∫ x : ℝ, (‖deriv (pieceB jj k : ℝ → ℂ) x‖
              + ‖SchwartzMap.convolution (ContinuousLinearMap.mul ℂ ℂ)
                  (SchwartzMap.derivCLM ℂ ℂ (pieceB jj k)) (lam (-jv)) x‖) := by
            refine integral_mono_ae hIntd (hInt1.add hInt2) ?_
            filter_upwards with x
            exact norm_sub_le _ _
        _ = (∫ x : ℝ, ‖deriv (pieceB jj k : ℝ → ℂ) x‖)
            + ∫ x : ℝ, ‖SchwartzMap.convolution (ContinuousLinearMap.mul ℂ ℂ)
                (SchwartzMap.derivCLM ℂ ℂ (pieceB jj k)) (lam (-jv)) x‖ :=
            integral_add hInt1 hInt2
    have hyoung : (∫ x : ℝ, ‖SchwartzMap.convolution (ContinuousLinearMap.mul ℂ ℂ)
            (SchwartzMap.derivCLM ℂ ℂ (pieceB jj k)) (lam (-jv)) x‖)
        ≤ (∫ x : ℝ, ‖deriv (pieceB jj k : ℝ → ℂ) x‖) * (Work.KMTAreas.A7.etaMult_M : ℝ) := by
      have hy := Work.KMTAreas.A4.offConvL1 (SchwartzMap.derivCLM ℂ ℂ (pieceB jj k)) (lam (-jv))
      have hcoe : (∫ x : ℝ, ‖(SchwartzMap.derivCLM ℂ ℂ (pieceB jj k)) x‖)
          = ∫ x : ℝ, ‖deriv (pieceB jj k : ℝ → ℂ) x‖ := by
        rw [coe_derivCLMZ]
      calc (∫ x : ℝ, ‖SchwartzMap.convolution (ContinuousLinearMap.mul ℂ ℂ)
              (SchwartzMap.derivCLM ℂ ℂ (pieceB jj k)) (lam (-jv)) x‖)
          ≤ (∫ x : ℝ, ‖(SchwartzMap.derivCLM ℂ ℂ (pieceB jj k)) x‖)
              * (∫ x : ℝ, ‖(lam (-jv)) x‖) := hy
        _ = (∫ x : ℝ, ‖deriv (pieceB jj k : ℝ → ℂ) x‖) * (∫ x : ℝ, ‖(lam (-jv)) x‖) := by
            rw [hcoe]
        _ ≤ (∫ x : ℝ, ‖deriv (pieceB jj k : ℝ → ℂ) x‖) * (Work.KMTAreas.A7.etaMult_M : ℝ) :=
            mul_le_mul_of_nonneg_left hvl1 hIbnn
    calc (∫ x : ℝ, ‖deriv (pieceHigh jj k jv : ℝ → ℂ) x‖)
        ≤ (∫ x : ℝ, ‖deriv (pieceB jj k : ℝ → ℂ) x‖)
          + (∫ x : ℝ, ‖SchwartzMap.convolution (ContinuousLinearMap.mul ℂ ℂ)
              (SchwartzMap.derivCLM ℂ ℂ (pieceB jj k)) (lam (-jv)) x‖) := htri
      _ ≤ (∫ x : ℝ, ‖deriv (pieceB jj k : ℝ → ℂ) x‖)
          + (∫ x : ℝ, ‖deriv (pieceB jj k : ℝ → ℂ) x‖) * (Work.KMTAreas.A7.etaMult_M : ℝ) :=
          add_le_add le_rfl hyoung
      _ = (1 + (Work.KMTAreas.A7.etaMult_M : ℝ)) * ∫ x : ℝ, ‖deriv (pieceB jj k : ℝ → ℂ) x‖ := by
          ring
  have hkey : (∫ x : ℝ, ‖pieceHigh jj k jv x‖)
        + (∫ x : ℝ, ‖deriv (pieceHigh jj k jv : ℝ → ℂ) x‖)
      ≤ ((Cmom + 1 + (Work.KMTAreas.A7.etaMult_M : ℝ)) * (2 : ℝ) ^ jv)
          * (∫ x : ℝ, ‖deriv (pieceB jj k : ℝ → ℂ) x‖) := by
    have hA' : (∫ x : ℝ, ‖pieceHigh jj k jv x‖)
        ≤ (Cmom * (2 : ℝ) ^ jv) * (∫ x : ℝ, ‖deriv (pieceB jj k : ℝ → ℂ) x‖) :=
      le_trans hA (mul_le_mul_of_nonneg_right hmom hIbnn)
    have hsum1 : (∫ x : ℝ, ‖pieceHigh jj k jv x‖)
        + (∫ x : ℝ, ‖deriv (pieceHigh jj k jv : ℝ → ℂ) x‖)
        ≤ (Cmom * (2 : ℝ) ^ jv + (1 + (Work.KMTAreas.A7.etaMult_M : ℝ)))
            * (∫ x : ℝ, ‖deriv (pieceB jj k : ℝ → ℂ) x‖) := by
      rw [add_mul]
      exact add_le_add hA' hB2
    have h2jv1 : (1 : ℝ) ≤ (2 : ℝ) ^ jv := by
      simpa using zpow_le_zpow_right₀ (by norm_num : (1 : ℝ) ≤ 2) hjv
    have hC0 : Cmom * (2 : ℝ) ^ jv + (1 + (Work.KMTAreas.A7.etaMult_M : ℝ))
        ≤ (Cmom + 1 + (Work.KMTAreas.A7.etaMult_M : ℝ)) * (2 : ℝ) ^ jv := by
      have hb : (1 + (Work.KMTAreas.A7.etaMult_M : ℝ))
          ≤ (1 + (Work.KMTAreas.A7.etaMult_M : ℝ)) * (2 : ℝ) ^ jv := by
        calc (1 + (Work.KMTAreas.A7.etaMult_M : ℝ))
            = (1 + (Work.KMTAreas.A7.etaMult_M : ℝ)) * 1 := by ring
          _ ≤ (1 + (Work.KMTAreas.A7.etaMult_M : ℝ)) * (2 : ℝ) ^ jv :=
              mul_le_mul_of_nonneg_left h2jv1 (by linarith [hEtaMpos])
      nlinarith [hb]
    exact le_trans hsum1 (mul_le_mul_of_nonneg_right hC0 hIbnn)
  calc ∑' j : ℤ, ‖pieceHigh jj k jv (j : ℝ)‖
      ≤ Cs * ((∫ x : ℝ, ‖pieceHigh jj k jv x‖)
          + (∫ x : ℝ, ‖deriv (pieceHigh jj k jv : ℝ → ℂ) x‖)) := hSamp (pieceHigh jj k jv)
    _ ≤ Cs * (((Cmom + 1 + (Work.KMTAreas.A7.etaMult_M : ℝ)) * (2 : ℝ) ^ jv)
          * (∫ x : ℝ, ‖deriv (pieceB jj k : ℝ → ℂ) x‖)) :=
        mul_le_mul_of_nonneg_left hkey hCs0.le
    _ ≤ Cs * (((Cmom + 1 + (Work.KMTAreas.A7.etaMult_M : ℝ)) * (2 : ℝ) ^ jv)
          * (Cb * (2 : ℝ) ^ k * Y)) := by
        refine mul_le_mul_of_nonneg_left (mul_le_mul_of_nonneg_left hI ?_) hCs0.le
        positivity
    _ = (Cs * (Cmom + 1 + (Work.KMTAreas.A7.etaMult_M : ℝ)) * Cb
          * (2 : ℝ) ^ (k + jv)) * Y := by
        rw [zpow_add₀ (by norm_num : (2 : ℝ) ≠ 0)]
        ring


/-! ## The statement of `iw-prop`(i) -/

/-- **Lemma `iw-prop`(i), off-diagonal decay** (Appendix A of Krause--Mirek--Tao), in the form
used by the `A4Z` chapter: on good major arcs, the Ionescu--Wainger projection `Π_{≤l,≤k}` decays
off the support of its input. -/
theorem offDecayTwo (hA1 : Work.KMTContract.AreaA1) :
    ∀ (ρ : ℝ), 0 < ρ → ρ ≤ 1 → Work.KMTAreas.A4Z.OffDecayHyp ρ :=
  offDecayTwo_of_high hA1 cruxBound_holds

end Work.KMTAreas.A4Z
