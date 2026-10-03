/-
# The masked slice bound for the low case of area A6 (Case B)

`Work.KMTPlan.A6.maskedSliceVarNorm` is the *masked* form of the single-scale slice bound of
Case B: the variational norm of the clamped single-scale family
`caseBMasked`, taken over the scales `n` with `lowSmallSet ρ C₀ a l₁ l₂ k₁ k₂ n` true, is
controlled by
* the frozen (`VrFull 2 Kv`) variation of the *anchored* family `caseBAnchored`, plus
* twice the `ℓ¹`-norm of the spike at `n = 0` — and here the spike hypothesis is on the
  **masked** spike, i.e. the spike multiplied by the indicator of `lowSmallSet … 0`, which is
  exactly the value of `caseBMasked` at `n = 0`.

The statement is the sharp form of `Work.KMTPlan.A6.eLpNorm_varNorm_maskedSlice_le` (which
assumes the un-masked spike bound): since the masked spike is pointwise dominated by the
un-masked one, the hypothesis here is weaker, and the same proof applies, with the `n = 0`
term bounded directly by `hSpk`.
-/
import Mathlib
import Submission.Work.KMTPlan.A6.LowModelVarCaseBDefs
import Submission.Port.Aesm

set_option autoImplicit false
set_option maxHeartbeats 8000000
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

private lemma eLpNorm_add_le_int (A B : ℤ → ℝ≥0∞) :
    eLpNorm (fun x : ℤ => A x + B x) 1 MeasureTheory.Measure.count
      ≤ eLpNorm A 1 MeasureTheory.Measure.count + eLpNorm B 1 MeasureTheory.Measure.count :=
  MeasureTheory.eLpNorm_add_le le_rfl

private lemma eLpNorm_two_mul_le_int (B : ℤ → ℝ≥0∞) :
    eLpNorm (fun x : ℤ => (2 : ℝ≥0∞) * B x) 1 MeasureTheory.Measure.count
      ≤ 2 * eLpNorm B 1 MeasureTheory.Measure.count := by
  have hae : ∀ᵐ x ∂MeasureTheory.Measure.count,
      ‖(2 : ℝ≥0∞) * B x‖ₑ ≤ (2 : ℝ≥0) * ‖B x‖ₑ := by
    filter_upwards with x
    simp
  have h := MeasureTheory.eLpNorm_le_nnreal_smul_eLpNorm_of_ae_le_mul' (hf := by pw_aesm)
    (μ := MeasureTheory.Measure.count) (f := fun x : ℤ => (2 : ℝ≥0∞) * B x) (g := B)
    (c := 2) hae 1
  simpa [ENNReal.smul_def, smul_eq_mul] using h

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

/-! ## The masked slice bound -/

theorem maskedSliceVarNorm
    (ρ : ℝ) (P : Polynomial ℤ) (C₀ : ℕ) (a : ℕ → NNReal) (f g : ℤ → ℂ)
    (l₁ l₂ k₁ k₂ : ℕ) (j₁ j₂ : ℤ) (t : ℝ) (r : NNReal) (hr2 : 2 ≤ r)
    (Kv : ℕ) (hKv1 : 1 ≤ Kv)
    (hlssK : ∀ k : ℕ, Kv ≤ k → ¬ Work.KMTPlan.A6.lowSmallSet ρ C₀ a l₁ l₂ k₁ k₂ k)
    (hf : MeasureTheory.MemLp f 2 MeasureTheory.Measure.count)
    (hg : MeasureTheory.MemLp g 2 MeasureTheory.Measure.count)
    {FRZ SPK : ENNReal}
    (hFrz : MeasureTheory.eLpNorm (fun x : ℤ => Work.Analysis.Variation.VrFull 2 Kv
        (fun n : ℕ => Work.KMTPlan.A6.caseBAnchored ρ P C₀ a f g l₁ l₂ k₁ k₂ j₁ j₂ t n x))
        1 MeasureTheory.Measure.count ≤ FRZ)
    (hSpk : MeasureTheory.eLpNorm (fun x : ℤ =>
        if Work.KMTPlan.A6.lowSmallSet ρ C₀ a l₁ l₂ k₁ k₂ 0 then
          ENNReal.ofReal ‖Work.KMTPlan.A6.caseBSpike ρ P a f g l₁ l₂ k₁ k₂ j₁ j₂ t x‖ else 0)
        1 MeasureTheory.Measure.count ≤ SPK) :
    MeasureTheory.eLpNorm (fun x : ℤ => PointwiseErgodicTheorems.variationalNorm r
        (fun n : ℕ => Work.KMTPlan.A6.caseBMasked ρ P C₀ a f g l₁ l₂ k₁ k₂ j₁ j₂ t n x))
      1 MeasureTheory.Measure.count ≤ FRZ + 2 * SPK := by
  classical
  have hr1 : (1 : NNReal) ≤ r := le_trans (by norm_num : (1 : NNReal) ≤ 2) hr2
  have hW1 : Summable fun j : ℤ => ‖cw (mStarF (uScale ρ (lcL l₁ l₂ k₁ k₂))) j‖ :=
    cw_mStarF_summable _
  have hW2 : Summable fun j : ℤ =>
      ‖cw (mStargF P.natDegree (uScale ρ (lcL l₁ l₂ k₁ k₂))) j‖ :=
    cw_mStargF_summable _ _
  have hanc0 : caseBAnchored ρ P C₀ a f g l₁ l₂ k₁ k₂ j₁ j₂ t 0 = 0 := by
    funext y
    show BtwistEx ρ P l₁ l₂ _ _
      (Tm ρ l₁ (lowModSymbF ρ C₀ a l₁ l₂ k₁ k₂ j₁ t 0) f)
      (Tm ρ l₂ (lowModSymbG ρ P C₀ a l₁ l₂ k₁ k₂ j₂ t 0) g) y = 0
    rw [lowModSymbF_zero, lowModSymbG_zero, Tm_zero ρ l₁ f hf, Tm_zero ρ l₂ g hg]
    exact congrFun (BtwistEx_zero_zero ρ P l₁ l₂ _ _ hW1 hW2) y
  have hagree : ∀ n : ℕ, 1 ≤ n →
      (fun x : ℤ => caseBMasked ρ P C₀ a f g l₁ l₂ k₁ k₂ j₁ j₂ t n x)
        = (fun x : ℤ => caseBAnchored ρ P C₀ a f g l₁ l₂ k₁ k₂ j₁ j₂ t n x) := by
    intro n hn
    funext y
    show (if lowSmallSet ρ C₀ a l₁ l₂ k₁ k₂ n then
        BtwistEx ρ P l₁ l₂ _ _ (Tm ρ l₁ (varphiNtj (Nat.floor (a n)) k₁ j₁ t) f)
          (Tm ρ l₂ (varphitildeNtj P (Nat.floor (a n)) k₂ j₂ t) g) y else 0)
      = BtwistEx ρ P l₁ l₂ _ _
          (Tm ρ l₁ (lowModSymbF ρ C₀ a l₁ l₂ k₁ k₂ j₁ t n) f)
          (Tm ρ l₂ (lowModSymbG ρ P C₀ a l₁ l₂ k₁ k₂ j₂ t n) g) y
    by_cases hsl : lowSmallSet ρ C₀ a l₁ l₂ k₁ k₂ n
    · have hn0 : n ≠ 0 := by omega
      have h1 : lowModSymbF ρ C₀ a l₁ l₂ k₁ k₂ j₁ t n
          = varphiNtj (Nat.floor (a n)) k₁ j₁ t := by
        funext ξ; simp only [lowModSymbF, if_neg hn0, if_pos hsl]
      have h2 : lowModSymbG ρ P C₀ a l₁ l₂ k₁ k₂ j₂ t n
          = varphitildeNtj P (Nat.floor (a n)) k₂ j₂ t := by
        funext ξ; simp only [lowModSymbG, if_neg hn0, if_pos hsl]
      simp only [if_pos hsl, h1, h2]
    · have hn0 : n ≠ 0 := by omega
      have h1 : lowModSymbF ρ C₀ a l₁ l₂ k₁ k₂ j₁ t n = 0 := by
        funext ξ; simp [lowModSymbF, hn0, hsl]
      have h2 : lowModSymbG ρ P C₀ a l₁ l₂ k₁ k₂ j₂ t n = 0 := by
        funext ξ; simp [lowModSymbG, hn0, hsl]
      rw [if_neg hsl, h1, h2, Tm_zero ρ l₁ f hf, Tm_zero ρ l₂ g hg]
      exact (congrFun (BtwistEx_zero_zero ρ P l₁ l₂ _ _ hW1 hW2) y).symm
  have hpt : ∀ x : ℤ, PointwiseErgodicTheorems.variationalNorm r
      (fun n : ℕ => caseBMasked ρ P C₀ a f g l₁ l₂ k₁ k₂ j₁ j₂ t n x)
      ≤ Work.Analysis.Variation.VrFull 2 Kv
          (fun n : ℕ => caseBAnchored ρ P C₀ a f g l₁ l₂ k₁ k₂ j₁ j₂ t n x)
        + 2 * ENNReal.ofReal ‖caseBMasked ρ P C₀ a f g l₁ l₂ k₁ k₂ j₁ j₂ t 0 x‖ := by
    intro x
    have hshift := Work.KMTPlan.A6.variationalNorm_le_of_shift r hr1
      (fun n : ℕ => caseBMasked ρ P C₀ a f g l₁ l₂ k₁ k₂ j₁ j₂ t n x)
      (fun n : ℕ => caseBAnchored ρ P C₀ a f g l₁ l₂ k₁ k₂ j₁ j₂ t n x)
      (congrFun hanc0 x) (fun n hn => congrFun (hagree n hn) x)
    have hvr : Work.Analysis.Variation.VrFull 2 Kv
        (fun n : ℕ => caseBAnchored ρ P C₀ a f g l₁ l₂ k₁ k₂ j₁ j₂ t n x)
        = Work.Analysis.Variation.VrFull 2 ((Kv - 1) + 1)
          (fun n : ℕ => caseBAnchored ρ P C₀ a f g l₁ l₂ k₁ k₂ j₁ j₂ t n x) := by
      rw [Nat.sub_add_cancel hKv1]
    rw [hvr]
    refine hshift.trans (add_le_add ?_ le_rfl)
    refine Work.KMTPlan.A6.variationalNorm_le_VrFull hr2 (Kv - 1) _ (fun k hk => ?_)
    have hkv : Kv ≤ k := by omega
    have hk0 : k ≠ 0 := by omega
    have h1 : lowModSymbF ρ C₀ a l₁ l₂ k₁ k₂ j₁ t k = 0 := by
      funext ξ; simp [lowModSymbF, hk0, hlssK k hkv]
    have h2 : lowModSymbG ρ P C₀ a l₁ l₂ k₁ k₂ j₂ t k = 0 := by
      funext ξ; simp [lowModSymbG, hk0, hlssK k hkv]
    show BtwistEx ρ P l₁ l₂ _ _ (Tm ρ l₁ (lowModSymbF ρ C₀ a l₁ l₂ k₁ k₂ j₁ t k) f)
      (Tm ρ l₂ (lowModSymbG ρ P C₀ a l₁ l₂ k₁ k₂ j₂ t k) g) x = 0
    rw [h1, h2, Tm_zero ρ l₁ f hf, Tm_zero ρ l₂ g hg]
    exact congrFun (BtwistEx_zero_zero ρ P l₁ l₂ _ _ hW1 hW2) x
  have hspkB : MeasureTheory.eLpNorm (fun x : ℤ =>
      ENNReal.ofReal ‖caseBMasked ρ P C₀ a f g l₁ l₂ k₁ k₂ j₁ j₂ t 0 x‖)
      1 MeasureTheory.Measure.count ≤ SPK := by
    have hfun : (fun x : ℤ => ENNReal.ofReal
          ‖caseBMasked ρ P C₀ a f g l₁ l₂ k₁ k₂ j₁ j₂ t 0 x‖)
        = (fun x : ℤ => if lowSmallSet ρ C₀ a l₁ l₂ k₁ k₂ 0 then
            ENNReal.ofReal ‖caseBSpike ρ P a f g l₁ l₂ k₁ k₂ j₁ j₂ t x‖ else 0) := by
      funext x
      have hmsk0 : caseBMasked ρ P C₀ a f g l₁ l₂ k₁ k₂ j₁ j₂ t 0 x
          = (if lowSmallSet ρ C₀ a l₁ l₂ k₁ k₂ 0 then
              caseBSpike ρ P a f g l₁ l₂ k₁ k₂ j₁ j₂ t x else 0) := rfl
      rw [hmsk0]
      by_cases h0 : lowSmallSet ρ C₀ a l₁ l₂ k₁ k₂ 0
      · rw [if_pos h0, if_pos h0]
      · rw [if_neg h0, if_neg h0]
        simp
    rw [hfun]
    exact hSpk
  calc MeasureTheory.eLpNorm (fun x : ℤ =>
        PointwiseErgodicTheorems.variationalNorm r
          (fun n : ℕ => caseBMasked ρ P C₀ a f g l₁ l₂ k₁ k₂ j₁ j₂ t n x))
        1 MeasureTheory.Measure.count
      ≤ MeasureTheory.eLpNorm (fun x : ℤ => Work.Analysis.Variation.VrFull 2 Kv
          (fun n : ℕ => caseBAnchored ρ P C₀ a f g l₁ l₂ k₁ k₂ j₁ j₂ t n x)
        + 2 * ENNReal.ofReal
            ‖caseBMasked ρ P C₀ a f g l₁ l₂ k₁ k₂ j₁ j₂ t 0 x‖)
        1 MeasureTheory.Measure.count := eLpNorm_le_of_le_int _ _ hpt
    _ ≤ MeasureTheory.eLpNorm (fun x : ℤ => Work.Analysis.Variation.VrFull 2 Kv
          (fun n : ℕ => caseBAnchored ρ P C₀ a f g l₁ l₂ k₁ k₂ j₁ j₂ t n x))
          1 MeasureTheory.Measure.count
        + 2 * MeasureTheory.eLpNorm (fun x : ℤ => ENNReal.ofReal
            ‖caseBMasked ρ P C₀ a f g l₁ l₂ k₁ k₂ j₁ j₂ t 0 x‖)
          1 MeasureTheory.Measure.count := by
        refine (eLpNorm_add_le_int
          (fun x : ℤ => Work.Analysis.Variation.VrFull 2 Kv
            (fun n : ℕ => caseBAnchored ρ P C₀ a f g l₁ l₂ k₁ k₂ j₁ j₂ t n x))
          (fun x : ℤ => 2 * ENNReal.ofReal
            ‖caseBMasked ρ P C₀ a f g l₁ l₂ k₁ k₂ j₁ j₂ t 0 x‖)).trans ?_
        exact add_le_add le_rfl (eLpNorm_two_mul_le_int
          (fun x : ℤ => ENNReal.ofReal
            ‖caseBMasked ρ P C₀ a f g l₁ l₂ k₁ k₂ j₁ j₂ t 0 x‖))
    _ ≤ FRZ + 2 * SPK := add_le_add hFrz (mul_le_mul_of_nonneg_left hspkB (by norm_num))

end

end Work.KMTPlan.A6
