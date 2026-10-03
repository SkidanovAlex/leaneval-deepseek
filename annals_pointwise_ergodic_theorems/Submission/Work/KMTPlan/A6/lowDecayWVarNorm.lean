import Mathlib
import Submission.Work.KMTPlan.A6.maskedSliceVarNorm
import Submission.Port.Aesm

/-!
# The weighted `t`-integral estimate of Case B (`lowDecayW`)

`Work.KMTPlan.A6.lowDecayWVarNorm` is the `t`-integral companion of
`Work.KMTPlan.A6.lowDecayBVarNorm`: it bounds the `ℒ¹(ℤ)`-norm of the `r`-variational norm of
the *weighted* family

  `lowDecayW ρ P C₀ a f g l₁ l₂ k₁ k₂ j₁ j₂ w n x
      = if lowSmallSet … n then ∫_{1/2}^1 w n t · BtwistEx_{m_*}(Tm (φ_{N,k₁,j₁}(t)) f)
          (Tm (φ̃_{N,k₂,j₂}(t)) g) x dt else 0`

by `2·Cw·(FRZ + 2·SPK)`.  The proof is the `t`-integral (Minkowski in `t`) of the frozen-`t`
estimate: for each fixed `t ∈ [1/2,1]` the family `lowDecayW` is pointwise the *weight*
`(if Bw ≤ ⌊a n⌋ then w n t else 0)` times the clamped single-scale family `caseBMasked`, so

* the multiplicativity of the variational norm (`Work.KMTPlan.A6.variationalNorm_prod_le`)
  together with the variational bound on the weight (the hypothesis `hwt`) controls the
  variational norm pointwise, and the const-multiplier rule for `eLpNorm` on `ℓ¹(ℤ)` gives the
  factor `2·Cw`;
* the **masked slice bound** for `caseBMasked` (`maskedSliceVarNorm`, whose spike hypothesis at
  `n = 0` is masked by `lowSmallSet … 0`, exactly as in `hSpk`) gives the factor `FRZ + 2·SPK`;
* Minkowski in `t` (`Work.KMTPlan.A6.mdlWIntF_norm_le`) passes from the frozen `t` to the
  `t`-integral, using the measurability and interval-integrability hypotheses `hmeas`, `hint`.
-/

set_option autoImplicit false
set_option linter.unusedVariables false

namespace Work.KMTPlan.A6

noncomputable section

open MeasureTheory Polynomial Finset Filter Topology
open scoped ENNReal NNReal BigOperators Interval
open PointwiseErgodicTheorems Submission.PointwiseErgodicTheorems
open Work.Analysis.IonescuWainger
open Work.KMTAreas.A7

/-! ## Elementary measure-theoretic helpers on `ℓ¹(ℤ)` -/

private lemma eLpNorm_le_of_le_int (A B : ℤ → ℝ≥0∞) (h : ∀ x, A x ≤ B x) :
    eLpNorm A 1 MeasureTheory.Measure.count ≤ eLpNorm B 1 MeasureTheory.Measure.count := by
  have hae : ∀ᵐ x ∂MeasureTheory.Measure.count, ‖A x‖ₑ ≤ (1 : ℝ≥0) * ‖B x‖ₑ := by
    filter_upwards with x
    simpa using h x
  have h' := MeasureTheory.eLpNorm_le_nnreal_smul_eLpNorm_of_ae_le_mul' (hf := by pw_aesm)
    (μ := MeasureTheory.Measure.count) (f := A) (g := B) (c := 1) hae 1
  simpa [ENNReal.smul_def, smul_eq_mul] using h'

private lemma eLpNorm_const_mul_eq {c : ℝ≥0∞} (hc : c ≠ ⊤) (B : ℤ → ℝ≥0∞) :
    eLpNorm (fun x : ℤ => c * B x) 1 MeasureTheory.Measure.count
      = c * eLpNorm B 1 MeasureTheory.Measure.count := by
  rw [MeasureTheory.eLpNorm_one_eq_lintegral_enorm (hf := by pw_aesm),
    MeasureTheory.eLpNorm_one_eq_lintegral_enorm (hf := by pw_aesm)]
  simp only [enorm_eq_self]
  exact MeasureTheory.lintegral_const_mul' c _ hc

private lemma two_mul_ofReal_ne_top (Cw : ℝ) :
    (2 * ENNReal.ofReal Cw : ℝ≥0∞) ≠ ⊤ :=
  ENNReal.mul_ne_top (by norm_num) ENNReal.ofReal_ne_top

/-! ## The weighted `t`-integral estimate -/

theorem lowDecayWVarNorm
    (ρ : ℝ) (P : Polynomial ℤ) (C₀ : ℕ) (a : ℕ → NNReal) (f g : ℤ → ℂ)
    (l₁ l₂ k₁ k₂ : ℕ) (j₁ j₂ : ℤ) (r : NNReal) (hr2 : 2 ≤ r)
    (Bw : ℕ) (Cw : ℝ) (w : ℕ → ℝ → ℂ) (Kv : ℕ) (hKv1 : 1 ≤ Kv)
    (hlssK : ∀ k : ℕ, Kv ≤ k → ¬ Work.KMTPlan.A6.lowSmallSet ρ C₀ a l₁ l₂ k₁ k₂ k)
    (hlower : ∀ n : ℕ, Work.KMTPlan.A6.lowSmallSet ρ C₀ a l₁ l₂ k₁ k₂ n →
      Bw ≤ Nat.floor (a n))
    (hwt : ∀ t ∈ Set.Icc (1 / 2 : ℝ) 1, PointwiseErgodicTheorems.variationalNorm r
      (fun n : ℕ => if Bw ≤ Nat.floor (a n) then w n t else 0) ≤ ENNReal.ofReal Cw)
    (hmeas : ∀ (n : ℕ) (x : ℤ), Measurable (fun t : ℝ =>
      (if Bw ≤ Nat.floor (a n) then w n t else 0) *
        Work.KMTPlan.A6.caseBMasked ρ P C₀ a f g l₁ l₂ k₁ k₂ j₁ j₂ t n x))
    (hint : ∀ (n : ℕ) (x : ℤ), IntervalIntegrable (fun t : ℝ =>
      (if Bw ≤ Nat.floor (a n) then w n t else 0) *
        Work.KMTPlan.A6.caseBMasked ρ P C₀ a f g l₁ l₂ k₁ k₂ j₁ j₂ t n x)
      MeasureTheory.volume (1 / 2) 1)
    (hf : MeasureTheory.MemLp f 2 MeasureTheory.Measure.count)
    (hg : MeasureTheory.MemLp g 2 MeasureTheory.Measure.count)
    {FRZ SPK : ENNReal}
    (hFrz : ∀ t ∈ Set.Icc (1 / 2 : ℝ) 1, MeasureTheory.eLpNorm (fun x : ℤ =>
        Work.Analysis.Variation.VrFull 2 Kv
          (fun n : ℕ => Work.KMTPlan.A6.caseBAnchored ρ P C₀ a f g l₁ l₂ k₁ k₂ j₁ j₂ t n x))
        1 MeasureTheory.Measure.count ≤ FRZ)
    (hSpk : ∀ t ∈ Set.Icc (1 / 2 : ℝ) 1, MeasureTheory.eLpNorm (fun x : ℤ =>
        if Work.KMTPlan.A6.lowSmallSet ρ C₀ a l₁ l₂ k₁ k₂ 0 then
          ENNReal.ofReal ‖Work.KMTPlan.A6.caseBSpike ρ P a f g l₁ l₂ k₁ k₂ j₁ j₂ t x‖ else 0)
        1 MeasureTheory.Measure.count ≤ SPK) :
    MeasureTheory.eLpNorm (fun x : ℤ => PointwiseErgodicTheorems.variationalNorm r
        (fun n : ℕ => Work.KMTPlan.A6.lowDecayW ρ P C₀ a f g l₁ l₂ k₁ k₂ j₁ j₂ w n x))
      1 MeasureTheory.Measure.count ≤ 2 * ENNReal.ofReal Cw * (FRZ + 2 * SPK) := by
  classical
  have hr1 : (1 : NNReal) ≤ r := le_trans (by norm_num : (1 : NNReal) ≤ 2) hr2
  have hEq : (lowDecayW ρ P C₀ a f g l₁ l₂ k₁ k₂ j₁ j₂ w)
      = mdlWIntF (fun n t => if Bw ≤ Nat.floor (a n) then w n t else 0)
          (fun t n x => caseBMasked ρ P C₀ a f g l₁ l₂ k₁ k₂ j₁ j₂ t n x) := by
    funext n x
    by_cases h : lowSmallSet ρ C₀ a l₁ l₂ k₁ k₂ n
    · simp only [lowDecayW, mdlWIntF, caseBMasked, if_pos h, if_pos (hlower n h), one_mul]
    · simp only [lowDecayW, mdlWIntF, caseBMasked, if_neg h, mul_zero,
        intervalIntegral.integral_zero]
  rw [hEq]
  refine (mdlWIntF_norm_le (r := r) hr1 _ _ hmeas hint (fun t ht => ?_)).trans le_rfl
  have hms := maskedSliceVarNorm ρ P C₀ a f g l₁ l₂ k₁ k₂ j₁ j₂ t r hr2 Kv hKv1 hlssK hf hg
    (hFrz t ht) (hSpk t ht)
  have hpt : ∀ x : ℤ, PointwiseErgodicTheorems.variationalNorm r
      (fun n : ℕ => (if Bw ≤ Nat.floor (a n) then w n t else 0) *
        caseBMasked ρ P C₀ a f g l₁ l₂ k₁ k₂ j₁ j₂ t n x)
      ≤ (2 * ENNReal.ofReal Cw) * PointwiseErgodicTheorems.variationalNorm r
          (fun n : ℕ => caseBMasked ρ P C₀ a f g l₁ l₂ k₁ k₂ j₁ j₂ t n x) := by
    intro x
    refine (Work.KMTPlan.A6.variationalNorm_prod_le (r := r) hr1 _ _).trans ?_
    refine (mul_le_mul' le_rfl (mul_le_mul' (hwt t ht) le_rfl)).trans ?_
    exact le_of_eq (by ring)
  refine (eLpNorm_le_of_le_int _ _ hpt).trans ?_
  rw [eLpNorm_const_mul_eq (two_mul_ofReal_ne_top Cw) _]
  exact by gcongr

end

end Work.KMTPlan.A6
