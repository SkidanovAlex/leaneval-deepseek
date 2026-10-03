/-
# `Submission.Work.FIArea7CF.charRegionSplitAux` — clash-free copy of `Submission.Work.FIArea7.charRegionSplitAux`

Imports redirected to the `FIArea7CF` copies; renamed: norm_uniCoeff_le→crs_norm_uniCoeff_le.  The workspace contains several
incompatible declarations of `Work.FIArea7.mem_gBox_iff` (and of `norm_uniCoeff_le`,
`log_pow_le_rpow`, `gnorm_mk_eq`), so the amended area-7 assembly and the *FI* §§19–26
chain can only meet through copies.  See NOTES §63.
-/
import Mathlib
import Submission.Work.FIArea7.Area7Regions6b
import Submission.Work.FIArea7.UniCharTerm6
import Submission.Work.FIArea7.Section16Expansion

set_option autoImplicit false

namespace Work.FIArea7

open Finset
open scoped BigOperators

attribute [local instance] Classical.propDecidable

noncomputable section

/-- The mode weight of the (17.10) expansion: `2log2 + log4` for `k = 0` and `1/|k|` for the even
non-zero frequencies `|k| ≤ 2K`. -/
def uniH (K : ℕ) : ℝ :=
  2 * Real.log 2 + Real.log 4 + ∑ k ∈ evenFreq K, (1 / ((|k| : ℤ) : ℝ))

/-- The index set of region I of the (17.10) main term (the finset summed in
`Work.FIArea7.charRegionLow6`). -/
def charRegionLowFinset (Pa : Work.FITop.Params) (X K L₀ : ℕ) (δ₁ : ℝ) : Finset (ℕ × ℕ) :=
  ((Finset.Icc 1 (uniB Pa)).product (Finset.Icc 1 X)).filter
    (fun p => 4 * (p.1 : ℝ) * (p.2 : ℝ) * (2 * (K : ℝ) + (L₀ : ℝ) + 2) ≤ Pa.N ^ δ₁)

/-- `charRegionLow6` is the `2`-multiple of `uniCharTerm` over `charRegionLowFinset` (definitional). -/
lemma charRegionLow6_eq_sumF (Pa : Work.FITop.Params) (X K L₀ : ℕ) (δ₁ : ℝ)
    (β : GaussianInt → ℂ) (ε : GaussianInt → ℤ) :
    charRegionLow6 Pa X K L₀ δ₁ β ε
      = 2 * ∑ p ∈ charRegionLowFinset Pa X K L₀ δ₁, uniCharTerm Pa p.1 p.2 β K ε := rfl

/-- The region-I condition, unfolded. -/
lemma mem_charRegionLowFinset {Pa : Work.FITop.Params} {X K L₀ : ℕ} {δ₁ : ℝ} {p : ℕ × ℕ} :
    p ∈ charRegionLowFinset Pa X K L₀ δ₁ ↔
      p.1 ∈ Finset.Icc 1 (uniB Pa) ∧ p.2 ∈ Finset.Icc 1 X ∧
        4 * (p.1 : ℝ) * (p.2 : ℝ) * (2 * (K : ℝ) + (L₀ : ℝ) + 2) ≤ Pa.N ^ δ₁ := by
  simp only [charRegionLowFinset, Finset.mem_filter]
  constructor
  · rintro ⟨hp, hreg⟩
    exact ⟨(Finset.mem_product.mp hp).1, (Finset.mem_product.mp hp).2, hreg⟩
  · rintro ⟨h1, h2, hreg⟩
    exact ⟨Finset.mem_product.mpr ⟨h1, h2⟩, hreg⟩

/-- **The cross term of one `(b,e,k)` mode.**  Comes from the polarisation
`|S(u+v)|² = |S(u)|² + |S(v)|² + S(u)conj(S(v)) + S(v)conj(S(u))`. -/
def uniCrossMode (Pa : Work.FITop.Params) (Q e : ℕ) [NeZero Q] (ε : GaussianInt → ℤ)
    (u v : GaussianInt → ℂ) (k : ℤ) : ℂ :=
  (1 / (Fintype.card (GaussUnit Q) : ℂ)) *
    ∑ χ : AddChar (Additive (GaussUnit Q)) ℂ, uniJChar Q e χ *
      (uniSChar Pa Q ε u k χ * star (uniSChar Pa Q ε v k χ)
        + uniSChar Pa Q ε v k χ * star (uniSChar Pa Q ε u k χ))

/-- **The cross term of `uniCharTerm`**: the same Möbius weight, mode weights and `4be = 0` guard
as `uniCharTerm`, applied to `uniCrossMode`. -/
def uniCharTermCross (Pa : Work.FITop.Params) (b e : ℕ) (ε : GaussianInt → ℤ)
    (u v : GaussianInt → ℂ) (K : ℕ) : ℂ :=
  (((ArithmeticFunction.moebius b : ℝ) / (b : ℝ) : ℝ) : ℂ) *
    (if h : 4 * b * e = 0 then 0 else
      haveI : NeZero (4 * b * e) := ⟨h⟩
      ((((2 * Real.log 2 + Real.log 4 : ℝ)) : ℂ) * uniCrossMode Pa (4 * b * e) e ε u v 0
        + ∑ k ∈ evenFreq K, (1 / (|k| : ℝ) : ℂ) * uniCrossMode Pa (4 * b * e) e ε u v k))

/-! ## Elementary norm bounds (public copies) -/

/-- `‖uniPow z k‖ ≤ 1` for every `z` (including `z = 0`). -/
lemma norm_uniPow_le_one (z : GaussianInt) (k : ℤ) : ‖uniPow z k‖ ≤ 1 := by
  rw [uniPow]
  by_cases hz : z.toComplex = 0
  · rw [hz, zero_div, norm_zpow, norm_zero, zero_zpow_eq]
    split <;> norm_num
  · have hnorm : ‖z.toComplex / ((‖z.toComplex‖ : ℝ) : ℂ)‖ = 1 := by
      rw [norm_div, Complex.norm_real, Real.norm_eq_abs, abs_of_nonneg (norm_nonneg _),
        div_self (norm_ne_zero_iff.mpr hz)]
    rw [norm_zpow, hnorm]
    simp

/-- `‖uniCoeff ε β k z‖ ≤ ‖β z‖` as soon as `‖ε z‖ ≤ 1`. -/
lemma crs_norm_uniCoeff_le (ε : GaussianInt → ℤ) (β : GaussianInt → ℂ) (k : ℤ)
    (hε : ∀ z : GaussianInt, ‖((ε z : ℤ) : ℂ)‖ ≤ 1) (z : GaussianInt) :
    ‖uniCoeff ε β k z‖ ≤ ‖β z‖ := by
  rw [uniCoeff, norm_mul, norm_mul]
  calc ‖((ε z : ℤ) : ℂ)‖ * ‖betaPrime β z‖ * ‖uniPow z k‖
      ≤ 1 * ‖β z‖ * 1 := by
        gcongr
        · exact hε z
        · exact norm_betaPrime_le β z
        · exact norm_uniPow_le_one z k
    _ = ‖β z‖ := by ring

/-- `‖unitInd Q z‖ ≤ 1`. -/
lemma norm_unitInd_le_one (Q : ℕ) (z : GaussianInt) : ‖unitInd Q z‖ ≤ 1 := by
  rw [unitInd]; split <;> simp

/-- `‖unitCoeff Q c z‖ ≤ ‖c z‖`. -/
lemma norm_unitCoeff_le (Q : ℕ) (c : GaussianInt → ℂ) (z : GaussianInt) :
    ‖unitCoeff Q c z‖ ≤ ‖c z‖ := by
  rw [unitCoeff, norm_mul, norm_star]
  calc ‖c z‖ * ‖unitInd Q z‖ ≤ ‖c z‖ * 1 :=
        mul_le_mul_of_nonneg_left (norm_unitInd_le_one Q z) (norm_nonneg _)
    _ = ‖c z‖ := by ring

/-! ## Additivity of the coefficient in `β` -/

lemma betaPrime_add (u v : GaussianInt → ℂ) :
    betaPrime (u + v) = betaPrime u + betaPrime v := by
  funext z
  simp only [betaPrime, Pi.add_apply]
  ring

lemma uniCoeff_add (ε : GaussianInt → ℤ) (u v : GaussianInt → ℂ) (k : ℤ) :
    uniCoeff ε (u + v) k = uniCoeff ε u k + uniCoeff ε v k := by
  funext z
  simp only [uniCoeff, betaPrime_add, Pi.add_apply]
  ring

lemma unitCoeff_add (Q : ℕ) (c d : GaussianInt → ℂ) :
    unitCoeff Q (c + d) = unitCoeff Q c + unitCoeff Q d := by
  funext z
  simp only [unitCoeff, Pi.add_apply, star_add]
  ring_nf

/-- **`uniSChar` is additive in the coefficient.** -/
lemma uniSChar_add (Pa : Work.FITop.Params) (Q : ℕ) [NeZero Q] (ε : GaussianInt → ℤ)
    (u v : GaussianInt → ℂ) (k : ℤ)
    (χ : AddChar (Additive (GaussUnit Q)) ℂ) :
    uniSChar Pa Q ε (u + v) k χ = uniSChar Pa Q ε u k χ + uniSChar Pa Q ε v k χ := by
  rw [uniSChar, uniSChar, uniSChar, ← Finset.sum_add_distrib]
  refine Finset.sum_congr rfl fun z _ => ?_
  rw [uniCoeff_add ε u v k, unitCoeff_add, Pi.add_apply]
  ring

/-- **Polarisation of one mode**: `uniModeCharSum` of `u+v` is the sum of the two sesquilinear
diagonal terms and the cross term `uniCrossMode`. -/
lemma uniModeCharSum_add (Pa : Work.FITop.Params) (b e : ℕ) [NeZero (4 * b * e)]
    (ε : GaussianInt → ℤ) (u v : GaussianInt → ℂ) (k : ℤ) :
    uniModeCharSum Pa b e (u + v) k ε
      = uniModeCharSum Pa b e u k ε + uniModeCharSum Pa b e v k ε
        + uniCrossMode Pa (4 * b * e) e ε u v k := by
  have hχ : ∀ χ : AddChar (Additive (GaussUnit (4 * b * e))) ℂ,
      uniSChar Pa (4 * b * e) ε (u + v) k χ * star (uniSChar Pa (4 * b * e) ε (u + v) k χ)
        = uniSChar Pa (4 * b * e) ε u k χ * star (uniSChar Pa (4 * b * e) ε u k χ)
          + uniSChar Pa (4 * b * e) ε v k χ * star (uniSChar Pa (4 * b * e) ε v k χ)
          + (uniSChar Pa (4 * b * e) ε u k χ * star (uniSChar Pa (4 * b * e) ε v k χ)
             + uniSChar Pa (4 * b * e) ε v k χ * star (uniSChar Pa (4 * b * e) ε u k χ)) := by
    intro χ
    rw [uniSChar_add Pa (4 * b * e) ε u v k χ, star_add]
    ring
  have hsum : (∑ χ : AddChar (Additive (GaussUnit (4 * b * e))) ℂ,
        uniJChar (4 * b * e) e χ *
          (uniSChar Pa (4 * b * e) ε (u + v) k χ
            * star (uniSChar Pa (4 * b * e) ε (u + v) k χ)))
      = (∑ χ : AddChar (Additive (GaussUnit (4 * b * e))) ℂ,
          uniJChar (4 * b * e) e χ *
            (uniSChar Pa (4 * b * e) ε u k χ * star (uniSChar Pa (4 * b * e) ε u k χ)))
        + (∑ χ : AddChar (Additive (GaussUnit (4 * b * e))) ℂ,
            uniJChar (4 * b * e) e χ *
              (uniSChar Pa (4 * b * e) ε v k χ * star (uniSChar Pa (4 * b * e) ε v k χ)))
        + (∑ χ : AddChar (Additive (GaussUnit (4 * b * e))) ℂ,
            uniJChar (4 * b * e) e χ *
              (uniSChar Pa (4 * b * e) ε u k χ * star (uniSChar Pa (4 * b * e) ε v k χ)
                + uniSChar Pa (4 * b * e) ε v k χ
                  * star (uniSChar Pa (4 * b * e) ε u k χ))) := by
    rw [← Finset.sum_add_distrib, ← Finset.sum_add_distrib]
    refine Finset.sum_congr rfl fun χ _ => ?_
    rw [hχ χ]; ring
  rw [uniModeCharSum, uniModeCharSum, uniModeCharSum, uniCrossMode]
  simp only [mul_assoc]
  rw [hsum]
  ring


/-! ## The pointwise polarisation of `uniCharTerm` -/

/-- **`uniCharTerm` splits sesquilinearly.** -/
lemma uniCharTerm_add (Pa : Work.FITop.Params) (b e : ℕ) (ε : GaussianInt → ℤ)
    (u v : GaussianInt → ℂ) (K : ℕ) :
    uniCharTerm Pa b e (u + v) K ε
      = uniCharTerm Pa b e u K ε + uniCharTerm Pa b e v K ε
        + uniCharTermCross Pa b e ε u v K := by
  rw [uniCharTerm, uniCharTerm, uniCharTerm, uniCharTermCross]
  by_cases h : 4 * b * e = 0
  · rw [dif_pos h, dif_pos h, dif_pos h, dif_pos h]
    ring
  · haveI : NeZero (4 * b * e) := ⟨h⟩
    rw [dif_neg h, dif_neg h, dif_neg h, dif_neg h]
    have hk : ∀ k : ℤ, uniModeCharSum Pa b e (u + v) k ε
        = uniModeCharSum Pa b e u k ε + uniModeCharSum Pa b e v k ε
          + uniCrossMode Pa (4 * b * e) e ε u v k :=
      fun k => uniModeCharSum_add Pa b e ε u v k
    have hsum : (∑ k ∈ evenFreq K, (1 / (|k| : ℝ) : ℂ) * uniModeCharSum Pa b e (u + v) k ε)
        = (∑ k ∈ evenFreq K, (1 / (|k| : ℝ) : ℂ) * uniModeCharSum Pa b e u k ε)
          + (∑ k ∈ evenFreq K, (1 / (|k| : ℝ) : ℂ) * uniModeCharSum Pa b e v k ε)
          + (∑ k ∈ evenFreq K, (1 / (|k| : ℝ) : ℂ)
              * uniCrossMode Pa (4 * b * e) e ε u v k) := by
      rw [← Finset.sum_add_distrib, ← Finset.sum_add_distrib]
      exact Finset.sum_congr rfl (fun k _ => by rw [hk k]; ring)
    rw [hk 0, hsum]
    ring

/-- **The sesquilinear split of region I.** -/
theorem charRegionLow6_add (Pa : Work.FITop.Params) (X K L₀ : ℕ) (δ₁ : ℝ)
    (ε : GaussianInt → ℤ) (u v : GaussianInt → ℂ) :
    charRegionLow6 Pa X K L₀ δ₁ (u + v) ε
      = charRegionLow6 Pa X K L₀ δ₁ u ε + charRegionLow6 Pa X K L₀ δ₁ v ε
        + 2 * ∑ p ∈ charRegionLowFinset Pa X K L₀ δ₁, uniCharTermCross Pa p.1 p.2 ε u v K := by
  rw [charRegionLow6_eq_sumF, charRegionLow6_eq_sumF, charRegionLow6_eq_sumF]
  have hsum : (∑ p ∈ charRegionLowFinset Pa X K L₀ δ₁, uniCharTerm Pa p.1 p.2 (u + v) K ε)
      = (∑ p ∈ charRegionLowFinset Pa X K L₀ δ₁, uniCharTerm Pa p.1 p.2 u K ε)
        + (∑ p ∈ charRegionLowFinset Pa X K L₀ δ₁, uniCharTerm Pa p.1 p.2 v K ε)
        + (∑ p ∈ charRegionLowFinset Pa X K L₀ δ₁, uniCharTermCross Pa p.1 p.2 ε u v K) := by
    rw [← Finset.sum_add_distrib, ← Finset.sum_add_distrib]
    exact Finset.sum_congr rfl (fun p _ => uniCharTerm_add Pa p.1 p.2 ε u v K)
  rw [hsum]; ring

/-! ## Norm arithmetic helpers -/

/-- `‖(1 : ℂ)/(n : ℂ)‖ = 1/n` for `n : ℕ` in `ℂ`. -/
lemma norm_one_div_natCast (n : ℕ) : ‖(1 : ℂ) / (n : ℂ)‖ = 1 / (n : ℝ) := by
  rw [norm_div, norm_one, Complex.norm_natCast]

/-- The norm of the mode weight `1/|k|` of the (17.10) expansion, written as a real quotient in
`ℂ`, is `1/((|k| : ℤ) : ℝ)`. -/
lemma norm_one_div_abs_real_cast (k : ℤ) :
    ‖((1 / (|k| : ℝ) : ℝ) : ℂ)‖ = 1 / (((|k| : ℤ)) : ℝ) := by
  rw [Complex.norm_real, Real.norm_eq_abs, abs_of_nonneg (by positivity),
    show |(k : ℝ)| = (((|k| : ℤ)) : ℝ) from (Int.cast_abs).symm]

/-- The same norm bound for the shape `1/|k|` produced by Lean's coercion of `1/(|k| : ℝ)` to
`ℂ` (a *complex* division). -/
lemma norm_one_div_abs_complex (k : ℤ) :
    ‖(1 / (|k| : ℝ) : ℂ)‖ = 1 / (((|k| : ℤ)) : ℝ) := by
  rw [norm_div, norm_one, Complex.norm_real, Real.norm_eq_abs,
    abs_of_nonneg (abs_nonneg (k : ℝ))]
  congr 1
  exact (Int.cast_abs).symm

/-- `√(a + b) ≤ √a + √b`. -/
lemma sqrt_add_le (a b : ℝ) : Real.sqrt (a + b) ≤ Real.sqrt a + Real.sqrt b := by
  have ha : a ≤ (Real.sqrt a) ^ 2 := by
    by_cases h : 0 ≤ a
    · rw [Real.sq_sqrt h]
    · rw [Real.sqrt_eq_zero_of_nonpos (le_of_lt (not_le.mp h))]; simp; linarith
  have hb : b ≤ (Real.sqrt b) ^ 2 := by
    by_cases h : 0 ≤ b
    · rw [Real.sq_sqrt h]
    · rw [Real.sqrt_eq_zero_of_nonpos (le_of_lt (not_le.mp h))]; simp; linarith
  have hle : a + b ≤ (Real.sqrt a + Real.sqrt b) ^ 2 := by
    nlinarith [Real.sqrt_nonneg a, Real.sqrt_nonneg b]
  have h0 : 0 ≤ Real.sqrt a + Real.sqrt b := by positivity
  calc Real.sqrt (a + b) ≤ Real.sqrt ((Real.sqrt a + Real.sqrt b) ^ 2) := Real.sqrt_le_sqrt hle
    _ = Real.sqrt a + Real.sqrt b := Real.sqrt_sq h0

/-- `uniH K ≥ 0`. -/
lemma uniH_nonneg (K : ℕ) : 0 ≤ uniH K := by
  rw [uniH]
  have hsum : 0 ≤ ∑ k ∈ evenFreq K, (1 / ((|k| : ℤ) : ℝ)) := by
    refine Finset.sum_nonneg fun k hk => ?_
    rw [evenFreq, Finset.mem_filter] at hk
    have hk0 : k ≠ 0 := hk.2.1
    have hpos : (0 : ℝ) < ((|k| : ℤ) : ℝ) := by
      have : (0 : ℤ) < |k| := abs_pos.mpr hk0
      exact_mod_cast this
    positivity
  have h2 : 0 ≤ Real.log 2 := Real.log_nonneg (by norm_num)
  have h4 : 0 ≤ Real.log 4 := Real.log_nonneg (by norm_num)
  linarith

/-! ## The Cauchy-Schwarz bound on the cross term of one mode -/

/-- **The cross term of one mode is bounded by `2s√(Q·Mv)`.**  From `‖S_χ(u)‖ ≤ s` on every
character, Cauchy–Schwarz over `χ` and the two Plancherel inputs `Σ_χ‖J(χ)‖² ≤ ΦQ`,
`Σ_χ‖S_χ(v)‖² ≤ Φ·Mv`. -/
lemma uniCrossMode_le {Pa : Work.FITop.Params} {Q e : ℕ} [NeZero Q] {ε : GaussianInt → ℤ}
    {u v : GaussianInt → ℂ} {k : ℤ} {s Mv : ℝ} (hs : 0 ≤ s) (hMv : 0 ≤ Mv)
    (hS : ∀ χ : AddChar (Additive (GaussUnit Q)) ℂ, ‖uniSChar Pa Q ε u k χ‖ ≤ s)
    (hJ : ∑ χ : AddChar (Additive (GaussUnit Q)) ℂ, ‖uniJChar Q e χ‖ ^ 2
            ≤ (Fintype.card (GaussUnit Q) : ℝ) * (Q : ℝ))
    (hV : ∑ χ : AddChar (Additive (GaussUnit Q)) ℂ, ‖uniSChar Pa Q ε v k χ‖ ^ 2
            ≤ (Fintype.card (GaussUnit Q) : ℝ) * Mv) :
    ‖uniCrossMode Pa Q e ε u v k‖ ≤ 2 * s * Real.sqrt ((Q : ℝ) * Mv) := by
  classical
  have hΦpos : 0 < (Fintype.card (GaussUnit Q) : ℝ) := by
    have hne : Nonempty (GaussUnit Q) := ⟨⟨(1, 0), by simp [gaussNorm]⟩⟩
    exact_mod_cast Fintype.card_pos_iff.mpr hne
  have hΦ0 : 0 ≤ (Fintype.card (GaussUnit Q) : ℝ) := le_of_lt hΦpos
  have hΦinv : (0:ℝ) ≤ 1 / (Fintype.card (GaussUnit Q) : ℝ) := by positivity
  have h2s : (0:ℝ) ≤ 2 * s := by linarith
  set X : ℂ := ∑ χ : AddChar (Additive (GaussUnit Q)) ℂ,
      uniJChar Q e χ * (uniSChar Pa Q ε u k χ * star (uniSChar Pa Q ε v k χ)
        + uniSChar Pa Q ε v k χ * star (uniSChar Pa Q ε u k χ)) with hX
  have h1 : ‖(1 / ((Fintype.card (GaussUnit Q) : ℂ))) * X‖
      = (1 / (Fintype.card (GaussUnit Q) : ℝ)) * ‖X‖ := by
    rw [norm_mul, norm_div, norm_one, Complex.norm_natCast]
  have h2 : ‖X‖ ≤ ∑ χ : AddChar (Additive (GaussUnit Q)) ℂ,
      ‖uniJChar Q e χ‖ * (‖uniSChar Pa Q ε u k χ‖ * ‖uniSChar Pa Q ε v k χ‖
        + ‖uniSChar Pa Q ε v k χ‖ * ‖uniSChar Pa Q ε u k χ‖) := by
    rw [hX]
    refine le_trans (norm_sum_le _ _) (Finset.sum_le_sum fun χ _ => ?_)
    calc ‖uniJChar Q e χ * (uniSChar Pa Q ε u k χ * star (uniSChar Pa Q ε v k χ)
          + uniSChar Pa Q ε v k χ * star (uniSChar Pa Q ε u k χ))‖
        = ‖uniJChar Q e χ‖ * ‖uniSChar Pa Q ε u k χ * star (uniSChar Pa Q ε v k χ)
          + uniSChar Pa Q ε v k χ * star (uniSChar Pa Q ε u k χ)‖ := norm_mul _ _
      _ ≤ ‖uniJChar Q e χ‖ * (‖uniSChar Pa Q ε u k χ * star (uniSChar Pa Q ε v k χ)‖
          + ‖uniSChar Pa Q ε v k χ * star (uniSChar Pa Q ε u k χ)‖) :=
          mul_le_mul_of_nonneg_left (norm_add_le _ _) (norm_nonneg _)
      _ = ‖uniJChar Q e χ‖ * (‖uniSChar Pa Q ε u k χ‖ * ‖uniSChar Pa Q ε v k χ‖
          + ‖uniSChar Pa Q ε v k χ‖ * ‖uniSChar Pa Q ε u k χ‖) := by
          rw [norm_mul, norm_mul, norm_star, norm_star]
  have h3 : ∀ χ : AddChar (Additive (GaussUnit Q)) ℂ,
      ‖uniJChar Q e χ‖ * (‖uniSChar Pa Q ε u k χ‖ * ‖uniSChar Pa Q ε v k χ‖
        + ‖uniSChar Pa Q ε v k χ‖ * ‖uniSChar Pa Q ε u k χ‖)
      ≤ ‖uniJChar Q e χ‖ * (2 * s * ‖uniSChar Pa Q ε v k χ‖) := by
    intro χ
    have hSu : ‖uniSChar Pa Q ε u k χ‖ ≤ s := hS χ
    have hSv0 : (0:ℝ) ≤ ‖uniSChar Pa Q ε v k χ‖ := norm_nonneg _
    have hkey : ‖uniSChar Pa Q ε u k χ‖ * ‖uniSChar Pa Q ε v k χ‖
        + ‖uniSChar Pa Q ε v k χ‖ * ‖uniSChar Pa Q ε u k χ‖
        ≤ 2 * s * ‖uniSChar Pa Q ε v k χ‖ := by
      nlinarith [mul_le_mul_of_nonneg_right hSu hSv0, norm_nonneg (uniSChar Pa Q ε u k χ)]
    exact mul_le_mul_of_nonneg_left hkey (norm_nonneg _)
  have h4 : (∑ χ : AddChar (Additive (GaussUnit Q)) ℂ,
      ‖uniJChar Q e χ‖ * (2 * s * ‖uniSChar Pa Q ε v k χ‖))
      = 2 * s * ∑ χ : AddChar (Additive (GaussUnit Q)) ℂ,
          ‖uniJChar Q e χ‖ * ‖uniSChar Pa Q ε v k χ‖ := by
    rw [Finset.mul_sum]
    exact Finset.sum_congr rfl (fun χ _ => by ring)
  have h5 : (∑ χ : AddChar (Additive (GaussUnit Q)) ℂ,
        ‖uniJChar Q e χ‖ * ‖uniSChar Pa Q ε v k χ‖)
      ≤ Real.sqrt (∑ χ, ‖uniJChar Q e χ‖ ^ 2)
        * Real.sqrt (∑ χ, ‖uniSChar Pa Q ε v k χ‖ ^ 2) :=
    Real.sum_mul_le_sqrt_mul_sqrt _ _ _
  have h6 : Real.sqrt (∑ χ : AddChar (Additive (GaussUnit Q)) ℂ, ‖uniJChar Q e χ‖ ^ 2)
      ≤ Real.sqrt ((Fintype.card (GaussUnit Q) : ℝ) * (Q : ℝ)) := Real.sqrt_le_sqrt hJ
  have h7 : Real.sqrt (∑ χ : AddChar (Additive (GaussUnit Q)) ℂ, ‖uniSChar Pa Q ε v k χ‖ ^ 2)
      ≤ Real.sqrt ((Fintype.card (GaussUnit Q) : ℝ) * Mv) := Real.sqrt_le_sqrt hV
  have h8 : Real.sqrt ((Fintype.card (GaussUnit Q) : ℝ) * (Q:ℝ))
        * Real.sqrt ((Fintype.card (GaussUnit Q) : ℝ) * Mv)
      = (Fintype.card (GaussUnit Q) : ℝ) * Real.sqrt ((Q:ℝ) * Mv) := by
    rw [← Real.sqrt_mul (mul_nonneg hΦ0 (Nat.cast_nonneg Q))
      ((Fintype.card (GaussUnit Q) : ℝ) * Mv)]
    have harg : (Fintype.card (GaussUnit Q) : ℝ) * (Q:ℝ)
        * ((Fintype.card (GaussUnit Q) : ℝ) * Mv)
        = ((Fintype.card (GaussUnit Q) : ℝ)) ^ 2 * ((Q:ℝ) * Mv) := by ring
    rw [harg, Real.sqrt_mul (sq_nonneg _), Real.sqrt_sq hΦ0]
  calc ‖uniCrossMode Pa Q e ε u v k‖
      = (1 / (Fintype.card (GaussUnit Q) : ℝ)) * ‖X‖ := by
        rw [uniCrossMode, hX]; exact h1
    _ ≤ (1 / (Fintype.card (GaussUnit Q) : ℝ)) *
          (∑ χ : AddChar (Additive (GaussUnit Q)) ℂ,
            ‖uniJChar Q e χ‖ * (‖uniSChar Pa Q ε u k χ‖ * ‖uniSChar Pa Q ε v k χ‖
              + ‖uniSChar Pa Q ε v k χ‖ * ‖uniSChar Pa Q ε u k χ‖)) :=
        mul_le_mul_of_nonneg_left h2 hΦinv
    _ ≤ (1 / (Fintype.card (GaussUnit Q) : ℝ)) *
          (∑ χ : AddChar (Additive (GaussUnit Q)) ℂ,
            ‖uniJChar Q e χ‖ * (2 * s * ‖uniSChar Pa Q ε v k χ‖)) :=
        mul_le_mul_of_nonneg_left (Finset.sum_le_sum fun χ _ => h3 χ) hΦinv
    _ = (1 / (Fintype.card (GaussUnit Q) : ℝ)) *
          (2 * s * ∑ χ : AddChar (Additive (GaussUnit Q)) ℂ,
            ‖uniJChar Q e χ‖ * ‖uniSChar Pa Q ε v k χ‖) := by rw [h4]
    _ ≤ (1 / (Fintype.card (GaussUnit Q) : ℝ)) *
          (2 * s * (Real.sqrt (∑ χ : AddChar (Additive (GaussUnit Q)) ℂ, ‖uniJChar Q e χ‖ ^ 2)
            * Real.sqrt (∑ χ : AddChar (Additive (GaussUnit Q)) ℂ,
                ‖uniSChar Pa Q ε v k χ‖ ^ 2))) :=
        mul_le_mul_of_nonneg_left (mul_le_mul_of_nonneg_left h5 h2s) hΦinv
    _ ≤ (1 / (Fintype.card (GaussUnit Q) : ℝ)) *
          (2 * s * (Real.sqrt ((Fintype.card (GaussUnit Q) : ℝ) * (Q:ℝ))
            * Real.sqrt ((Fintype.card (GaussUnit Q) : ℝ) * Mv))) :=
        mul_le_mul_of_nonneg_left (mul_le_mul_of_nonneg_left
          (mul_le_mul h6 h7 (Real.sqrt_nonneg _) (Real.sqrt_nonneg _)) h2s) hΦinv
    _ = 2 * s * Real.sqrt ((Q : ℝ) * Mv) := by
        rw [h8]
        have hc : (Fintype.card (GaussUnit Q) : ℝ) ≠ 0 := ne_of_gt hΦpos
        field_simp


/-! ## The cross term of one `(b,e)` -/

/-- **The cross term of one `(b,e)` of region I.**  Summing the per-mode Cauchy–Schwarz bounds with
the mode weights of `uniCharTerm` gives `(1/b)·uniH K·2s·yq`. -/
lemma uniCharTermCross_le_mode {Pa : Work.FITop.Params} (b e K : ℕ) (ε : GaussianInt → ℤ)
    (u v : GaussianInt → ℂ) [NeZero (4 * b * e)] {s Mv yq : ℝ}
    (hb : 1 ≤ b) (hs : 0 ≤ s)
    (hmode0 : ‖uniCrossMode Pa (4 * b * e) e ε u v 0‖
        ≤ 2 * s * Real.sqrt ((4 * (b:ℝ) * (e:ℝ)) * Mv))
    (hmode : ∀ k ∈ evenFreq K, ‖uniCrossMode Pa (4 * b * e) e ε u v k‖
        ≤ 2 * s * Real.sqrt ((4 * (b:ℝ) * (e:ℝ)) * Mv))
    (hsqrt : Real.sqrt ((4 * (b:ℝ) * (e:ℝ)) * Mv) ≤ yq) :
    ‖uniCharTermCross Pa b e ε u v K‖ ≤ (1 / (b:ℝ)) * uniH K * (2 * s * yq) := by
  classical
  have hb0 : (0:ℝ) < (b:ℝ) := by exact_mod_cast hb
  have hne : ¬ (4 * b * e = 0) := NeZero.ne _
  set c0 : ℂ := ((2 * Real.log 2 + Real.log 4 : ℝ) : ℂ) with hc0def
  set Mk : ℂ := ∑ k ∈ evenFreq K, (1 / (|k| : ℝ) : ℂ)
      * uniCrossMode Pa (4 * b * e) e ε u v k with hMk
  set A : ℝ := 2 * s * Real.sqrt ((4 * (b:ℝ) * (e:ℝ)) * Mv) with hA
  have hA0 : 0 ≤ A := by
    rw [hA]; exact mul_nonneg (by linarith) (Real.sqrt_nonneg _)
  have hAq : A ≤ 2 * s * yq := by
    rw [hA]; exact mul_le_mul_of_nonneg_left hsqrt (by linarith)
  have hc0n : ‖c0‖ = 2 * Real.log 2 + Real.log 4 := by
    rw [hc0def, Complex.norm_real, Real.norm_eq_abs, abs_of_nonneg]
    have h2 : 0 ≤ Real.log 2 := Real.log_nonneg (by norm_num)
    have h4 : 0 ≤ Real.log 4 := Real.log_nonneg (by norm_num)
    linarith
  have hc00 : (0:ℝ) ≤ 2 * Real.log 2 + Real.log 4 := by
    have h2 : 0 ≤ Real.log 2 := Real.log_nonneg (by norm_num)
    have h4 : 0 ≤ Real.log 4 := Real.log_nonneg (by norm_num)
    linarith
  have hcoef : ‖((((ArithmeticFunction.moebius b : ℝ) / (b:ℝ) : ℝ)) : ℂ)‖ ≤ 1 / (b:ℝ) := by
    rw [Complex.norm_real, Real.norm_eq_abs]
    have hμ : |((ArithmeticFunction.moebius b : ℝ))| ≤ 1 := by
      have h := ArithmeticFunction.abs_moebius_le_one (n := b)
      exact_mod_cast h
    calc |((ArithmeticFunction.moebius b : ℝ)) / (b:ℝ)|
        = |((ArithmeticFunction.moebius b : ℝ))| / (b:ℝ) := by rw [abs_div, abs_of_pos hb0]
      _ ≤ 1 / (b:ℝ) := div_le_div_of_nonneg_right hμ hb0.le
  have hsum_le : ‖Mk‖ ≤ ∑ k ∈ evenFreq K, (1 / ((|k| : ℤ) : ℝ)) * A := by
    rw [hMk]
    refine le_trans (norm_sum_le _ _) (Finset.sum_le_sum fun k hk => ?_)
    have hw : ‖(1 / (|k| : ℝ) : ℂ)‖ = 1 / ((|k| : ℤ) : ℝ) :=
      norm_one_div_abs_complex k
    rw [norm_mul, hw]
    exact mul_le_mul_of_nonneg_left (hmode k hk) (by positivity)
  have hmodesum : ‖c0 * uniCrossMode Pa (4 * b * e) e ε u v 0 + Mk‖ ≤ uniH K * A := by
    calc ‖c0 * uniCrossMode Pa (4 * b * e) e ε u v 0 + Mk‖
        ≤ ‖c0 * uniCrossMode Pa (4 * b * e) e ε u v 0‖ + ‖Mk‖ := norm_add_le _ _
      _ = (2 * Real.log 2 + Real.log 4) * ‖uniCrossMode Pa (4 * b * e) e ε u v 0‖ + ‖Mk‖ := by
          rw [norm_mul, hc0n]
      _ ≤ (2 * Real.log 2 + Real.log 4) * A
          + ∑ k ∈ evenFreq K, (1 / ((|k| : ℤ) : ℝ)) * A :=
          add_le_add (mul_le_mul_of_nonneg_left hmode0 hc00) hsum_le
      _ = uniH K * A := by
          rw [uniH]
          ring_nf
          rw [Finset.mul_sum]
  rw [uniCharTermCross, dif_neg hne]
  rw [← hc0def, ← hMk]
  calc ‖((((ArithmeticFunction.moebius b : ℝ) / (b:ℝ) : ℝ)) : ℂ) * (c0 * uniCrossMode Pa (4 * b * e) e ε u v 0 + Mk)‖
      = ‖((((ArithmeticFunction.moebius b : ℝ) / (b:ℝ) : ℝ)) : ℂ)‖
        * ‖c0 * uniCrossMode Pa (4 * b * e) e ε u v 0 + Mk‖ := norm_mul _ _
    _ ≤ (1 / (b:ℝ)) * (uniH K * A) :=
        mul_le_mul hcoef hmodesum (norm_nonneg _) (by positivity)
    _ ≤ (1 / (b:ℝ)) * (uniH K * (2 * s * yq)) := by
        refine mul_le_mul_of_nonneg_left ?_ (by positivity)
        exact mul_le_mul_of_nonneg_left hAq (uniH_nonneg K)
    _ = (1 / (b:ℝ)) * uniH K * (2 * s * yq) := by ring

end

end Work.FIArea7
