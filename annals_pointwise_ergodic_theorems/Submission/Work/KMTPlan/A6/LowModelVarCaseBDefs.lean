/-
# Case B of the small-scale model estimate of the low case of area A6: the assembly

This module assembles the target `Work.KMTPlan.A6.lowModelVarCaseB` from the two exact-height
integration-by-parts identities of `LowModelVarCaseBAssembly.lean` and the frozen-`t`
single-scale bound `Work.KMTPlan.A6.lowFrozenBilinBound`.
-/
import Mathlib
import Submission.Work.KMTPlan.A6.LowModelVarCaseBAssembly
import Submission.Work.KMTPlan.A6.MdlPartLowHighGain
import Submission.Work.KMTPlan.A6.le_two_rpow_self_of_ceil
import Submission.Work.KMTPlan.A6.variationalNorm_le_of_shift
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

/-! ## The three families of a single frozen scale -/

/-- The **clamped single-scale family** of Case B: the exact-height twisted bilinear multiplier
with the narrow window applied to the two modified bumps, clamped to `lowSmallSet`. -/
noncomputable def caseBMasked (ρ : ℝ) (P : Polynomial ℤ) (C₀ : ℕ) (a : ℕ → NNReal)
    (f g : ℤ → ℂ) (l₁ l₂ k₁ k₂ : ℕ) (j₁ j₂ : ℤ) (t : ℝ) : ℕ → ℤ → ℂ :=
  fun n x => if lowSmallSet ρ C₀ a l₁ l₂ k₁ k₂ n then
    BtwistEx ρ P l₁ l₂ (mStarF (uScale ρ (lcL l₁ l₂ k₁ k₂)))
      (mStargF P.natDegree (uScale ρ (lcL l₁ l₂ k₁ k₂)))
      (Tm ρ l₁ (varphiNtj (Nat.floor (a n)) k₁ j₁ t) f)
      (Tm ρ l₂ (varphitildeNtj P (Nat.floor (a n)) k₂ j₂ t) g) x else 0

/-- The **anchored** version of the clamped single-scale family: the modified bumps are replaced
by the anchored, vanishing-at-`n = 0` families `lowModSymbF`/`lowModSymbG`.  This is the object
of `Work.KMTPlan.A6.lowFrozenBilinBound`. -/
noncomputable def caseBAnchored (ρ : ℝ) (P : Polynomial ℤ) (C₀ : ℕ) (a : ℕ → NNReal)
    (f g : ℤ → ℂ) (l₁ l₂ k₁ k₂ : ℕ) (j₁ j₂ : ℤ) (t : ℝ) : ℕ → ℤ → ℂ :=
  fun n x => BtwistEx ρ P l₁ l₂ (mStarF (uScale ρ (lcL l₁ l₂ k₁ k₂)))
    (mStargF P.natDegree (uScale ρ (lcL l₁ l₂ k₁ k₂)))
    (Tm ρ l₁ (lowModSymbF ρ C₀ a l₁ l₂ k₁ k₂ j₁ t n) f)
    (Tm ρ l₂ (lowModSymbG ρ P C₀ a l₁ l₂ k₁ k₂ j₂ t n) g) x

/-- The **single-scale spike** at `n = 0`: the value of the clamped single-scale family at
`n = 0` before anchoring. -/
noncomputable def caseBSpike (ρ : ℝ) (P : Polynomial ℤ) (a : ℕ → NNReal)
    (f g : ℤ → ℂ) (l₁ l₂ k₁ k₂ : ℕ) (j₁ j₂ : ℤ) (t : ℝ) : ℤ → ℂ :=
  fun x => BtwistEx ρ P l₁ l₂ (mStarF (uScale ρ (lcL l₁ l₂ k₁ k₂)))
    (mStargF P.natDegree (uScale ρ (lcL l₁ l₂ k₁ k₂)))
    (Tm ρ l₁ (varphiNtj (Nat.floor (a 0)) k₁ j₁ t) f)
    (Tm ρ l₂ (varphitildeNtj P (Nat.floor (a 0)) k₂ j₂ t) g) x

/-- **The masked slice bound.** -/
theorem eLpNorm_varNorm_maskedSlice_le
    (ρ : ℝ) (P : Polynomial ℤ) (C₀ : ℕ) (a : ℕ → NNReal) (f g : ℤ → ℂ)
    (l₁ l₂ k₁ k₂ : ℕ) (j₁ j₂ : ℤ) (t : ℝ) (r : NNReal) (hr2 : 2 ≤ r)
    (Kv : ℕ) (hKv1 : 1 ≤ Kv)
    (hlssK : ∀ k : ℕ, Kv ≤ k → ¬ lowSmallSet ρ C₀ a l₁ l₂ k₁ k₂ k)
    (hf : MeasureTheory.MemLp f 2 MeasureTheory.Measure.count)
    (hg : MeasureTheory.MemLp g 2 MeasureTheory.Measure.count)
    {FRZ SPK : ENNReal}
    (hFrz : MeasureTheory.eLpNorm (fun x : ℤ => Work.Analysis.Variation.VrFull 2 Kv
        (fun n : ℕ => caseBAnchored ρ P C₀ a f g l₁ l₂ k₁ k₂ j₁ j₂ t n x))
        1 MeasureTheory.Measure.count ≤ FRZ)
    (hSpk : MeasureTheory.eLpNorm (fun x : ℤ =>
        ENNReal.ofReal ‖caseBSpike ρ P a f g l₁ l₂ k₁ k₂ j₁ j₂ t x‖)
        1 MeasureTheory.Measure.count ≤ SPK) :
    MeasureTheory.eLpNorm (fun x : ℤ => PointwiseErgodicTheorems.variationalNorm r
        (fun n : ℕ => caseBMasked ρ P C₀ a f g l₁ l₂ k₁ k₂ j₁ j₂ t n x))
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
    refine (eLpNorm_le_of_le_int
      (fun x : ℤ => ENNReal.ofReal ‖caseBMasked ρ P C₀ a f g l₁ l₂ k₁ k₂ j₁ j₂ t 0 x‖)
      (fun x : ℤ => ENNReal.ofReal ‖caseBSpike ρ P a f g l₁ l₂ k₁ k₂ j₁ j₂ t x‖)
      (fun x => ?_)).trans ?_
    · have hmsk0 : caseBMasked ρ P C₀ a f g l₁ l₂ k₁ k₂ j₁ j₂ t 0 x
          = (if lowSmallSet ρ C₀ a l₁ l₂ k₁ k₂ 0 then
              caseBSpike ρ P a f g l₁ l₂ k₁ k₂ j₁ j₂ t x else 0) := rfl
      refine ENNReal.ofReal_le_ofReal ?_
      rw [hmsk0]
      by_cases h0 : lowSmallSet ρ C₀ a l₁ l₂ k₁ k₂ 0
      · rw [if_pos h0]
      · rw [if_neg h0, norm_zero]
        exact norm_nonneg _
    · simpa only using hSpk
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


/-! ## The two weighted families -/

/-- **The boundary (`B`) family of the integration-by-parts identity.** -/
theorem eLpNorm_varNorm_lowDecayB_le
    (ρ : ℝ) (P : Polynomial ℤ) (C₀ : ℕ) (a : ℕ → NNReal) (f g : ℤ → ℂ)
    (l₁ l₂ k₁ k₂ : ℕ) (j₁ j₂ : ℤ) (t : ℝ) (r : NNReal) (hr2 : 2 ≤ r)
    (Bw : ℕ) (Cw : ℝ) (w : ℕ → ℂ) (Kv : ℕ) (hKv1 : 1 ≤ Kv)
    (hlssK : ∀ k : ℕ, Kv ≤ k → ¬ lowSmallSet ρ C₀ a l₁ l₂ k₁ k₂ k)
    (hlower : ∀ n : ℕ, lowSmallSet ρ C₀ a l₁ l₂ k₁ k₂ n → Bw ≤ Nat.floor (a n))
    (hw : PointwiseErgodicTheorems.variationalNorm r
      (fun n : ℕ => if Bw ≤ Nat.floor (a n) then w n else 0) ≤ ENNReal.ofReal Cw)
    (hf : MeasureTheory.MemLp f 2 MeasureTheory.Measure.count)
    (hg : MeasureTheory.MemLp g 2 MeasureTheory.Measure.count)
    {FRZ SPK : ENNReal}
    (hFrz : MeasureTheory.eLpNorm (fun x : ℤ => Work.Analysis.Variation.VrFull 2 Kv
        (fun n : ℕ => caseBAnchored ρ P C₀ a f g l₁ l₂ k₁ k₂ j₁ j₂ t n x))
        1 MeasureTheory.Measure.count ≤ FRZ)
    (hSpk : MeasureTheory.eLpNorm (fun x : ℤ =>
        ENNReal.ofReal ‖caseBSpike ρ P a f g l₁ l₂ k₁ k₂ j₁ j₂ t x‖)
        1 MeasureTheory.Measure.count ≤ SPK) :
    MeasureTheory.eLpNorm (fun x : ℤ => PointwiseErgodicTheorems.variationalNorm r
        (fun n : ℕ => lowDecayB ρ P C₀ a f g l₁ l₂ k₁ k₂ j₁ j₂ t w n x))
      1 MeasureTheory.Measure.count ≤ (2 * ENNReal.ofReal Cw) * (FRZ + 2 * SPK) := by
  classical
  have hr1 : (1 : NNReal) ≤ r := le_trans (by norm_num : (1 : NNReal) ≤ 2) hr2
  have hms := eLpNorm_varNorm_maskedSlice_le ρ P C₀ a f g l₁ l₂ k₁ k₂ j₁ j₂ t r hr2 Kv hKv1
    hlssK hf hg hFrz hSpk
  have hEq : (fun (n : ℕ) (x : ℤ) => lowDecayB ρ P C₀ a f g l₁ l₂ k₁ k₂ j₁ j₂ t w n x)
      = fun (n : ℕ) (x : ℤ) => (if Bw ≤ Nat.floor (a n) then w n else 0) *
          caseBMasked ρ P C₀ a f g l₁ l₂ k₁ k₂ j₁ j₂ t n x := by
    funext n x
    simp only [lowDecayB, caseBMasked]
    by_cases h : lowSmallSet ρ C₀ a l₁ l₂ k₁ k₂ n
    · simp only [if_pos h, if_pos (hlower n h), one_mul]
    · simp only [if_neg h, mul_zero]
  have hpt : ∀ x : ℤ, PointwiseErgodicTheorems.variationalNorm r
      (fun n : ℕ => lowDecayB ρ P C₀ a f g l₁ l₂ k₁ k₂ j₁ j₂ t w n x)
      ≤ (2 * ENNReal.ofReal Cw) * PointwiseErgodicTheorems.variationalNorm r
          (fun n : ℕ => caseBMasked ρ P C₀ a f g l₁ l₂ k₁ k₂ j₁ j₂ t n x) := by
    intro x
    have hpt' : (fun n : ℕ => lowDecayB ρ P C₀ a f g l₁ l₂ k₁ k₂ j₁ j₂ t w n x)
        = fun n : ℕ => (if Bw ≤ Nat.floor (a n) then w n else 0) *
            caseBMasked ρ P C₀ a f g l₁ l₂ k₁ k₂ j₁ j₂ t n x := by
      funext n; exact congrFun (congrFun hEq n) x
    rw [hpt']
    refine (Work.KMTPlan.A6.variationalNorm_prod_le (r := r) hr1 _ _).trans ?_
    refine (mul_le_mul' le_rfl (mul_le_mul' hw le_rfl)).trans ?_
    exact le_of_eq (by ring)
  calc MeasureTheory.eLpNorm (fun x : ℤ => PointwiseErgodicTheorems.variationalNorm r
        (fun n : ℕ => lowDecayB ρ P C₀ a f g l₁ l₂ k₁ k₂ j₁ j₂ t w n x))
        1 MeasureTheory.Measure.count
      ≤ MeasureTheory.eLpNorm (fun x : ℤ => (2 * ENNReal.ofReal Cw) *
          PointwiseErgodicTheorems.variationalNorm r
            (fun n : ℕ => caseBMasked ρ P C₀ a f g l₁ l₂ k₁ k₂ j₁ j₂ t n x))
        1 MeasureTheory.Measure.count := eLpNorm_le_of_le_int _ _ hpt
    _ = (2 * ENNReal.ofReal Cw) * MeasureTheory.eLpNorm (fun x : ℤ =>
          PointwiseErgodicTheorems.variationalNorm r
            (fun n : ℕ => caseBMasked ρ P C₀ a f g l₁ l₂ k₁ k₂ j₁ j₂ t n x))
          1 MeasureTheory.Measure.count :=
        eLpNorm_const_mul_eq (two_mul_ofReal_ne_top Cw) _
    _ ≤ (2 * ENNReal.ofReal Cw) * (FRZ + 2 * SPK) := by gcongr

/-- **The weighted `t`-integral family of the integration-by-parts identity.** -/
theorem eLpNorm_varNorm_lowDecayW_le
    (ρ : ℝ) (P : Polynomial ℤ) (C₀ : ℕ) (a : ℕ → NNReal) (f g : ℤ → ℂ)
    (l₁ l₂ k₁ k₂ : ℕ) (j₁ j₂ : ℤ) (r : NNReal) (hr2 : 2 ≤ r)
    (Bw : ℕ) (Cw : ℝ) (w : ℕ → ℝ → ℂ) (Kv : ℕ) (hKv1 : 1 ≤ Kv)
    (hlssK : ∀ k : ℕ, Kv ≤ k → ¬ lowSmallSet ρ C₀ a l₁ l₂ k₁ k₂ k)
    (hlower : ∀ n : ℕ, lowSmallSet ρ C₀ a l₁ l₂ k₁ k₂ n → Bw ≤ Nat.floor (a n))
    (hwt : ∀ t ∈ Set.Icc (1 / 2 : ℝ) 1, PointwiseErgodicTheorems.variationalNorm r
      (fun n : ℕ => if Bw ≤ Nat.floor (a n) then w n t else 0) ≤ ENNReal.ofReal Cw)
    (hmeas : ∀ (n : ℕ) (x : ℤ), Measurable (fun t : ℝ =>
      (if Bw ≤ Nat.floor (a n) then w n t else 0) *
        caseBMasked ρ P C₀ a f g l₁ l₂ k₁ k₂ j₁ j₂ t n x))
    (hint : ∀ (n : ℕ) (x : ℤ), IntervalIntegrable (fun t : ℝ =>
      (if Bw ≤ Nat.floor (a n) then w n t else 0) *
        caseBMasked ρ P C₀ a f g l₁ l₂ k₁ k₂ j₁ j₂ t n x)
      MeasureTheory.volume (1 / 2) 1)
    (hf : MeasureTheory.MemLp f 2 MeasureTheory.Measure.count)
    (hg : MeasureTheory.MemLp g 2 MeasureTheory.Measure.count)
    {FRZ SPK : ENNReal}
    (hFrz : ∀ t ∈ Set.Icc (1 / 2 : ℝ) 1, MeasureTheory.eLpNorm (fun x : ℤ =>
        Work.Analysis.Variation.VrFull 2 Kv
          (fun n : ℕ => caseBAnchored ρ P C₀ a f g l₁ l₂ k₁ k₂ j₁ j₂ t n x))
        1 MeasureTheory.Measure.count ≤ FRZ)
    (hSpk : ∀ t ∈ Set.Icc (1 / 2 : ℝ) 1, MeasureTheory.eLpNorm (fun x : ℤ =>
        ENNReal.ofReal ‖caseBSpike ρ P a f g l₁ l₂ k₁ k₂ j₁ j₂ t x‖)
        1 MeasureTheory.Measure.count ≤ SPK) :
    MeasureTheory.eLpNorm (fun x : ℤ => PointwiseErgodicTheorems.variationalNorm r
        (fun n : ℕ => lowDecayW ρ P C₀ a f g l₁ l₂ k₁ k₂ j₁ j₂ w n x))
      1 MeasureTheory.Measure.count ≤ (2 * ENNReal.ofReal Cw) * (FRZ + 2 * SPK) := by
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
  have hms := eLpNorm_varNorm_maskedSlice_le ρ P C₀ a f g l₁ l₂ k₁ k₂ j₁ j₂ t r hr2 Kv hKv1
    hlssK hf hg (hFrz t ht) (hSpk t ht)
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


/-! ## Thresholds and the logarithmic loss -/

/-- Beyond a `ρ`-dependent threshold the window scale `uScale ρ L` dominates both `L` and
`2^{ρL}`. -/
theorem uScale_window (ρ : ℝ) (hρ : 0 < ρ) :
    ∃ B : ℕ, ∀ L : ℕ, B ≤ L →
      L ≤ Work.KMTAreas.A7.uScale ρ L ∧
      (2 : ℝ) ^ (ρ * (L : ℝ)) ≤ (Work.KMTAreas.A7.uScale ρ L : ℝ) := by
  refine ⟨max (Nat.ceil (16 / (2 * ρ) ^ 2)) (Nat.ceil (1 / ρ) + 1), fun L hL => ?_⟩
  have hL1 : Nat.ceil (16 / (2 * ρ) ^ 2) ≤ L := le_trans (le_max_left _ _) hL
  have hL2 : Nat.ceil (1 / ρ) ≤ L :=
    le_trans (le_of_lt (Nat.lt_succ_self _)) (le_trans (le_max_right _ _) hL)
  have h2ρ : (0 : ℝ) < 2 * ρ := by linarith
  have h1 : (L : ℝ) ≤ (2 : ℝ) ^ ((2 * ρ) * (L : ℝ)) :=
    Work.KMTPlan.A6.le_two_rpow_self_of_ceil (2 * ρ) h2ρ L hL1
  have hρL : (1 : ℝ) ≤ ρ * (L : ℝ) := by
    have h : (1 : ℝ) / ρ ≤ (L : ℝ) := le_trans (Nat.le_ceil _) (by exact_mod_cast hL2)
    rw [div_le_iff₀ hρ] at h
    linarith
  set X : ℝ := (2 : ℝ) ^ (ρ * (L : ℝ)) with hXdef
  have hX2 : (2 : ℝ) ≤ X := by
    rw [hXdef]
    have := Real.rpow_le_rpow_of_exponent_le (by norm_num : (1:ℝ) ≤ 2) hρL
    simpa using this
  have hsplit : (2 : ℝ) ^ ((2 * ρ) * (L : ℝ)) = X * X := by
    rw [hXdef, ← Real.rpow_add (by norm_num : (0:ℝ) < 2)]
    congr 1
    ring
  have hxge : X + 1 ≤ (2 : ℝ) ^ ((2 * ρ) * (L : ℝ)) := by
    rw [hsplit]; nlinarith
  have hfloor : X ≤ (⌊(2 : ℝ) ^ ((2 * ρ) * (L : ℝ))⌋ : ℝ) := by
    have h := Int.lt_floor_add_one ((2 : ℝ) ^ ((2 * ρ) * (L : ℝ)))
    linarith
  have hxpos : (0 : ℝ) ≤ (2 : ℝ) ^ ((2 * ρ) * (L : ℝ)) := by positivity
  have hfloor_nonneg : (0 : ℤ) ≤ ⌊(2 : ℝ) ^ ((2 * ρ) * (L : ℝ))⌋ := by
    refine Int.le_floor.mpr ?_
    simpa using hxpos
  have huval : Work.KMTAreas.A7.uScale ρ L
      = ⌊(2 : ℝ) ^ ((2 * ρ) * (L : ℝ))⌋.toNat := by
    simp only [Work.KMTAreas.A7.uScale, Work.Analysis.EndVar.scaleCount, Nat.cast_one, one_mul]
  have hcastZ : (Work.KMTAreas.A7.uScale ρ L : ℤ) = ⌊(2 : ℝ) ^ ((2 * ρ) * (L : ℝ))⌋ := by
    rw [huval]
    exact Int.toNat_of_nonneg hfloor_nonneg
  have hcast : ((Work.KMTAreas.A7.uScale ρ L : ℕ) : ℝ)
      = (⌊(2 : ℝ) ^ ((2 * ρ) * (L : ℝ))⌋ : ℝ) := by
    have h3 : ((⌊(2 : ℝ) ^ ((2 * ρ) * (L : ℝ))⌋.toNat : ℕ) : ℤ)
        = ⌊(2 : ℝ) ^ ((2 * ρ) * (L : ℝ))⌋ := Int.toNat_of_nonneg hfloor_nonneg
    rw [huval]
    exact_mod_cast h3
  refine ⟨?_, ?_⟩
  · have hLZ : (L : ℤ) ≤ ⌊(2 : ℝ) ^ ((2 * ρ) * (L : ℝ))⌋ := by
      refine Int.le_floor.mpr ?_
      push_cast
      exact h1
    have : (L : ℤ) ≤ (Work.KMTAreas.A7.uScale ρ L : ℤ) := by
      rw [hcastZ]; exact hLZ
    exact_mod_cast this
  · rw [hcast]
    exact hfloor

/-- **The Rademacher--Menshov loss at the truncation `lowTrunc D ρ L`, for the explicit
`Λ`-independent-threshold constant `D = 2 log 2 / log Λ + 3`.** -/
theorem lowTruncLogBoundIndep (ρ : ℝ) (hρ : 0 < ρ) (Λ : NNReal) (hΛ : 1 < Λ) (L : ℕ) :
    ((Nat.log2 (lowTrunc (2 * Real.log 2 / Real.log (Λ : ℝ) + 3) ρ L + 2) : ℝ) + 2) ^ 2
      ≤ (4 * lowMfun Λ) * (2 : ℝ) ^ (4 * ρ * (L : ℝ)) := by
  set D : ℝ := 2 * Real.log 2 / Real.log (Λ : ℝ) + 3 with hDdef
  have hlogΛ : 0 < Real.log (Λ : ℝ) := Real.log_pos (by exact_mod_cast hΛ)
  have hDrel : D = 2 * (Real.log 2 / Real.log (Λ : ℝ)) + 3 := by
    rw [hDdef]; ring
  have hDlow : lowD Λ ≤ D := by
    have hx : 0 < Real.log 2 / Real.log (Λ : ℝ) := div_pos (Real.log_pos (by norm_num)) hlogΛ
    rw [lowD, hDrel]
    linarith
  have hD2 : D ≤ 2 * lowD Λ := by
    have hx : 0 < Real.log 2 / Real.log (Λ : ℝ) := div_pos (Real.log_pos (by norm_num)) hlogΛ
    rw [lowD, hDrel]
    linarith
  set u : ℕ := Work.KMTAreas.A7.uScale ρ L with hu
  have hY1 : (1 : ℝ) ≤ (2 : ℝ) ^ (u : ℝ) := Real.one_le_rpow (by norm_num) (by positivity)
  -- the ceiling comparison
  have hceil : Nat.ceil (D * (2 : ℝ) ^ u) ≤ 2 * (Nat.ceil (lowD Λ * (2 : ℝ) ^ u) + 1) := by
    refine Nat.ceil_le.mpr ?_
    have hx : D * (2 : ℝ) ^ u ≤ 2 * (lowD Λ * (2 : ℝ) ^ u) := by
      have := mul_le_mul_of_nonneg_right hD2 (by positivity : (0:ℝ) ≤ (2:ℝ)^u)
      linarith
    have h2 : 2 * (lowD Λ * (2 : ℝ) ^ u) ≤ 2 * (Nat.ceil (lowD Λ * (2 : ℝ) ^ u) : ℝ) := by
      have := Nat.le_ceil (lowD Λ * (2 : ℝ) ^ u)
      linarith
    have h3 : 2 * (Nat.ceil (lowD Λ * (2 : ℝ) ^ u) : ℝ)
        ≤ (2 * (Nat.ceil (lowD Λ * (2 : ℝ) ^ u) + 1) : ℕ) := by
      push_cast; linarith
    linarith
  have htrunc : lowTrunc D ρ L + 2
      ≤ 4 * (Nat.ceil (lowD Λ * (2 : ℝ) ^ u) + 2) := by
    rw [lowTrunc]
    have := hceil
    nlinarith [Nat.zero_le (Nat.ceil (lowD Λ * (2 : ℝ) ^ u))]
  have hpos1 : (1 : ℝ) ≤ ((Nat.ceil (lowD Λ * (2 : ℝ) ^ u) + 2 : ℕ) : ℝ) := by
    have : (0 : ℝ) < ((Nat.ceil (lowD Λ * (2 : ℝ) ^ u) : ℕ) : ℝ) + 2 := by positivity
    push_cast; linarith
  have hpos2 : (0 : ℝ) < ((lowTrunc D ρ L + 2 : ℕ) : ℝ) := by positivity
  have hlog : Real.logb 2 ((lowTrunc D ρ L + 2 : ℕ) : ℝ)
      ≤ Real.logb 2 (4 * ((Nat.ceil (lowD Λ * (2 : ℝ) ^ u) + 2 : ℕ) : ℝ)) := by
    refine Real.logb_le_logb_of_le (b := 2) (by norm_num) hpos2 ?_
    exact_mod_cast htrunc
  have hsplit : Real.logb 2 (4 * ((Nat.ceil (lowD Λ * (2 : ℝ) ^ u) + 2 : ℕ) : ℝ))
      = 2 + Real.logb 2 (((Nat.ceil (lowD Λ * (2 : ℝ) ^ u) + 2 : ℕ) : ℝ)) := by
    have hy : (((Nat.ceil (lowD Λ * (2 : ℝ) ^ u) + 2 : ℕ) : ℝ)) ≠ 0 :=
      ne_of_gt (by positivity)
    rw [Real.logb_mul (show (4:ℝ) ≠ 0 by norm_num) hy]
    have h4 : Real.logb 2 (4 : ℝ) = 2 := by
      have hlog2 : Real.log 2 ≠ 0 := ne_of_gt (Real.log_pos (by norm_num))
      rw [Real.logb, show (4 : ℝ) = 2 ^ 2 by norm_num, Real.log_pow]
      field_simp
      norm_num
    rw [h4]
  have hnat : (Nat.log2 (lowTrunc D ρ L + 2) : ℝ)
      ≤ Real.logb 2 ((lowTrunc D ρ L + 2 : ℕ) : ℝ) := by
    have := Work.KMTPlan.A6.nat_log2_cast_le_logb (lowTrunc D ρ L + 2)
    simpa using this
  have hbase : (0 : ℝ) ≤ Real.logb 2 (((Nat.ceil (lowD Λ * (2 : ℝ) ^ u) + 2 : ℕ) : ℝ)) := by
    refine Real.logb_nonneg (by norm_num) ?_
    exact hpos1
  have hsq : ((Nat.log2 (lowTrunc D ρ L + 2) : ℝ) + 2) ^ 2
      ≤ 4 * (Real.logb 2 (((Nat.ceil (lowD Λ * (2 : ℝ) ^ u) + 2 : ℕ) : ℝ)) + 2) ^ 2 := by
    have h1 : (Nat.log2 (lowTrunc D ρ L + 2) : ℝ) + 2
        ≤ Real.logb 2 (((Nat.ceil (lowD Λ * (2 : ℝ) ^ u) + 2 : ℕ) : ℝ)) + 4 := by
      have := le_trans hnat hlog
      rw [hsplit] at this
      linarith
    have h2 : (0 : ℝ) ≤ (Nat.log2 (lowTrunc D ρ L + 2) : ℝ) + 2 := by positivity
    have h3 : Real.logb 2 (((Nat.ceil (lowD Λ * (2 : ℝ) ^ u) + 2 : ℕ) : ℝ)) + 4
        ≤ 2 * (Real.logb 2 (((Nat.ceil (lowD Λ * (2 : ℝ) ^ u) + 2 : ℕ) : ℝ)) + 2) := by
      linarith
    nlinarith [hbase, h1, h2, h3]
  have hM := Work.KMTPlan.A6.lowTruncLogBoundM ρ hρ Λ hΛ L
  have hM' : (Real.logb 2 (((Nat.ceil (lowD Λ * (2 : ℝ) ^ u) + 2 : ℕ) : ℝ)) + 2) ^ 2
      ≤ lowMfun Λ * (2 : ℝ) ^ (4 * ρ * (L : ℝ)) := by
    simpa only [hu] using hM
  have hlowM : (0 : ℝ) ≤ lowMfun Λ := Work.KMTPlan.A6.lowMfun_nonneg Λ
  calc ((Nat.log2 (lowTrunc D ρ L + 2) : ℝ) + 2) ^ 2
      ≤ 4 * (Real.logb 2 (((Nat.ceil (lowD Λ * (2 : ℝ) ^ u) + 2 : ℕ) : ℝ)) + 2) ^ 2 := hsq
    _ ≤ 4 * (lowMfun Λ * (2 : ℝ) ^ (4 * ρ * (L : ℝ))) := by
        have := mul_le_mul_of_nonneg_left hM' (by norm_num : (0:ℝ) ≤ 4)
        linarith
    _ = (4 * lowMfun Λ) * (2 : ℝ) ^ (4 * ρ * (L : ℝ)) := by ring

end

end Work.KMTPlan.A6
