/-
# Case B of the small-scale model estimate, low--high case, bounded-bump interface

A copy of `Submission/Work/KMTPlan/A6/lowModelVarCaseBLowHigh.lean` in which the single-scale
estimate `hSS` is the `Linf` (bounded-bump) interface `Work.KMTPlan.A6.SSUBodyAtLinf`, the
frozen-`t` engine is `Work.KMTPlan.A6.Linf.lowFrozenBilinBound` (with the two extra pointwise
bounds on the two clamped bump families) and the spike bound is
`Work.KMTPlan.A6.Linf.caseBSpikeLe`.
-/
import Mathlib
import Submission.Work.KMTPlan.A6.caseBSliceWMeasInt
import Submission.Work.KMTPlan.A6.lowWeightMaskBound
import Submission.Work.KMTPlan.A6.scale_ge_of_heightScale
import Submission.Work.KMTPlan.A6.varphiNt_support_lowSmall
import Submission.Work.KMTPlan.A6.lowSmallSetLogIndep
import Submission.Work.KMTPlan.A6.LinfLowFrozenBilinBound
import Submission.Work.KMTPlan.A6.LinfCaseBSpikeLe
import Submission.Port.Aesm

set_option autoImplicit false
set_option maxHeartbeats 8000000
set_option linter.unusedVariables false

namespace Work.KMTPlan.A6.Linf

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

/-! ## Helper lemmas -/

/-- **The truncation index is beyond the small-scale set.** -/
private lemma not_lss_of_lowTrunc_lt (ρ : ℝ) (hρ : 0 < ρ) (C₀ : ℕ) (Λ : NNReal) (hΛ : 1 < Λ)
    (a : ℕ → NNReal) (hlac : PointwiseErgodicTheorems.Lacunary Λ a) (ha1 : ∀ n, 1 ≤ a n)
    (l₁ l₂ k₁ k₂ n : ℕ)
    (hn : lowTrunc (2 * Real.log 2 / Real.log (Λ : ℝ) + 3) ρ (lcL l₁ l₂ k₁ k₂) < n) :
    ¬ lowSmallSet ρ C₀ a l₁ l₂ k₁ k₂ n := by
  intro hls
  set D : ℝ := 2 * Real.log 2 / Real.log (Λ : ℝ) + 3 with hD
  have h1 : (n : ℝ) + 1 ≤ D * (2 : ℝ) ^ (uScale ρ (lcL l₁ l₂ k₁ k₂)) := by
    rw [hD]
    exact lowSmallSetLogIndep ρ hρ C₀ a Λ hΛ hlac ha1 l₁ l₂ k₁ k₂ n hls
  have h2 : D * (2 : ℝ) ^ (uScale ρ (lcL l₁ l₂ k₁ k₂)) < (n : ℝ) := by
    rw [lowTrunc] at hn
    have h3 : Nat.ceil (D * (2 : ℝ) ^ (uScale ρ (lcL l₁ l₂ k₁ k₂))) + 2 ≤ n := by omega
    have h4 : ((Nat.ceil (D * (2 : ℝ) ^ (uScale ρ (lcL l₁ l₂ k₁ k₂))) + 2 : ℕ) : ℝ)
        ≤ (n : ℝ) := by exact_mod_cast h3
    have h5 : D * (2 : ℝ) ^ (uScale ρ (lcL l₁ l₂ k₁ k₂))
        ≤ (Nat.ceil (D * (2 : ℝ) ^ (uScale ρ (lcL l₁ l₂ k₁ k₂))) : ℝ) := Nat.le_ceil _
    push_cast at h4
    linarith
  linarith

/-- **Support of the anchored clamped `f`-side modified family in the narrow arc** (`k₁ = 0`,
twist `j ∈ {0,1}`). -/
private theorem lowModSymbF_support_narrow' (ρ : ℝ) (hρ : 0 < ρ) (C₀ : ℕ) (hC₀ : 1 ≤ C₀)
    (hρC₀ : ρ * (C₀ : ℝ) ≤ 1 / 8) :
    ∃ B : ℕ, ∀ (a : ℕ → NNReal) (l₁ l₂ L : ℕ),
      B ≤ lcL l₁ l₂ 0 L →
      ∀ (j : ℤ), j ∈ ({0, 1} : Finset ℤ) → ∀ (t : ℝ), t ∈ Set.Icc (1 / 2 : ℝ) 1 →
      ∀ (n : ℕ) (ξ : ℝ),
        lowModSymbF ρ C₀ a l₁ l₂ 0 L j t n ξ ≠ 0 →
        |ξ| ≤ (2 : ℝ) ^ (-(3 * (uScale ρ (lcL l₁ l₂ 0 L) : ℤ))) := by
  obtain ⟨B, hB⟩ := varphiNt_support_lowSmall ρ hρ C₀ hC₀ hρC₀
  refine ⟨B, fun a l₁ l₂ L hBL j hj t ht n ξ hne => ?_⟩
  obtain ⟨-, hls, hne1⟩ := support_lowModSymbF hne
  have hφt : varphiNt (Nat.floor (a n)) 0 t ξ ≠ 0 :=
    varphiNt_ne_zero_of_varphiNtj_ne_zero _ _ _ _ _ hne1
  have hsupp := varphiNt_support (Nat.floor (a n)) 0 t ξ hφt
  have harith := hB l₁ l₂ 0 L (Nat.floor (a n)) hls.1 hls.2 hBL
  have hLU : (3 * (uScale ρ (lcL l₁ l₂ 0 L) : ℤ) : ℝ)
      ≤ (Work.Analysis.EndVar.logN (Nat.floor (a n)) : ℝ) := by
    have hz : (3 * (uScale ρ (lcL l₁ l₂ 0 L) : ℤ))
        ≤ Work.Analysis.EndVar.logN (Nat.floor (a n)) := by
      have h1 : 3 * uScale ρ (lcL l₁ l₂ 0 L)
          ≤ (Work.Analysis.EndVar.logN (Nat.floor (a n))).toNat :=
        le_trans (Nat.le_add_left _ _) harith
      have h2 : ((Work.Analysis.EndVar.logN (Nat.floor (a n))).toNat : ℤ)
          = Work.Analysis.EndVar.logN (Nat.floor (a n)) :=
        Int.toNat_of_nonneg (Work.Analysis.EndVar.logN_nonneg _)
      have h3 : ((3 * uScale ρ (lcL l₁ l₂ 0 L) : ℕ) : ℤ)
          ≤ ((Work.Analysis.EndVar.logN (Nat.floor (a n))).toNat : ℤ) := by
        exact_mod_cast h1
      push_cast at h3
      rwa [h2] at h3
    exact_mod_cast hz
  have hexp : (0 : ℝ) - (Work.Analysis.EndVar.logN (Nat.floor (a n)) : ℝ)
      ≤ ((-(3 * (uScale ρ (lcL l₁ l₂ 0 L) : ℤ)) : ℤ) : ℝ) := by
    simp only [Int.cast_neg, Int.cast_mul, Int.cast_ofNat]
    linarith [hLU]
  have h1' : |ξ| ≤ (2 : ℝ) ^
      ((0 : ℝ) - (Work.Analysis.EndVar.logN (Nat.floor (a n)) : ℝ)) := by
    simpa using hsupp
  refine h1'.trans ?_
  rw [← Real.rpow_intCast]
  exact Real.rpow_le_rpow_of_exponent_le (by norm_num) hexp

/-- **Support of the anchored clamped `g`-side modified family in the narrow arc** (`k₂ = L`,
twist `j = -1`). -/
private theorem lowModSymbG_support_narrow' (P : Polynomial ℤ) (hd : 1 ≤ P.natDegree) (ρ : ℝ)
    (hρ : 0 < ρ) (C₀ : ℕ) (hC₀ : 1 ≤ C₀) (hρC₀ : ρ * (C₀ : ℝ) ≤ 1 / 8) :
    ∃ B : ℕ, ∀ (a : ℕ → NNReal) (l₁ l₂ L : ℕ),
      B ≤ lcL l₁ l₂ 0 L →
      ∀ (t : ℝ), t ∈ Set.Icc (1 / 2 : ℝ) 1 → ∀ (n : ℕ) (ξ : ℝ),
        lowModSymbG ρ P C₀ a l₁ l₂ 0 L (-1) t n ξ ≠ 0 →
        |ξ| ≤ (2 : ℝ) ^
          (-(3 * (P.natDegree : ℤ) * (uScale ρ (lcL l₁ l₂ 0 L) : ℤ))) := by
  obtain ⟨B, hB⟩ := varphiNt_support_lowSmall ρ hρ C₀ hC₀ hρC₀
  refine ⟨B, fun a l₁ l₂ L hBL t ht n ξ hne => ?_⟩
  have hls : lowSmallSet ρ C₀ a l₁ l₂ 0 L n ∧
      varphitildeNtj P (Nat.floor (a n)) L (-1) t ξ ≠ 0 := by
    simp only [lowModSymbG] at hne
    by_cases h0 : n = 0
    · rw [if_pos h0] at hne; exact absurd rfl hne
    · rw [if_neg h0] at hne
      by_cases hc : lowSmallSet ρ C₀ a l₁ l₂ 0 L n
      · rw [if_pos hc] at hne; exact ⟨hc, hne⟩
      · rw [if_neg hc] at hne; exact absurd rfl hne
  obtain ⟨hls, hne1⟩ := hls
  have hψt : varphitildeNt P P.natDegree (Nat.floor (a n)) L t ξ ≠ 0 := by
    intro h0
    refine hne1 ?_
    rw [varphitildeNtj, h0, mul_zero]
  have hsupp := varphitildeNt_support_all P P.natDegree (Nat.floor (a n)) L t ξ hψt
  have harith := hB l₁ l₂ 0 L (Nat.floor (a n)) hls.1 hls.2 hBL
  have hLU : ((L : ℝ) + 3 * (uScale ρ (lcL l₁ l₂ 0 L) : ℝ))
      ≤ (Work.Analysis.EndVar.logN (Nat.floor (a n)) : ℝ) := by
    have hz : ((L : ℤ) + 3 * (uScale ρ (lcL l₁ l₂ 0 L) : ℤ))
        ≤ Work.Analysis.EndVar.logN (Nat.floor (a n)) := by
      have h1 : L + 3 * uScale ρ (lcL l₁ l₂ 0 L)
          ≤ (Work.Analysis.EndVar.logN (Nat.floor (a n))).toNat :=
        le_trans (Nat.add_le_add_right (le_max_right (0 : ℕ) L) _) harith
      have h2 : ((Work.Analysis.EndVar.logN (Nat.floor (a n))).toNat : ℤ)
          = Work.Analysis.EndVar.logN (Nat.floor (a n)) :=
        Int.toNat_of_nonneg (Work.Analysis.EndVar.logN_nonneg _)
      have h3 : ((L + 3 * uScale ρ (lcL l₁ l₂ 0 L) : ℕ) : ℤ)
          ≤ ((Work.Analysis.EndVar.logN (Nat.floor (a n))).toNat : ℤ) := by
        exact_mod_cast h1
      push_cast at h3
      rwa [h2] at h3
    exact_mod_cast hz
  have hd0 : (0 : ℝ) ≤ (P.natDegree : ℝ) := by positivity
  have hexp : (P.natDegree : ℝ)
        * ((L : ℝ) - (Work.Analysis.EndVar.logN (Nat.floor (a n)) : ℝ))
      ≤ ((-(3 * (P.natDegree : ℤ) * (uScale ρ (lcL l₁ l₂ 0 L) : ℤ)) : ℤ) : ℝ) := by
    have h1' : (L : ℝ) - (Work.Analysis.EndVar.logN (Nat.floor (a n)) : ℝ)
        ≤ -3 * (uScale ρ (lcL l₁ l₂ 0 L) : ℝ) := by linarith
    have h2' := mul_le_mul_of_nonneg_left h1' hd0
    have h3' : (P.natDegree : ℝ) * (-3 * (uScale ρ (lcL l₁ l₂ 0 L) : ℝ))
        = ((-(3 * (P.natDegree : ℤ) * (uScale ρ (lcL l₁ l₂ 0 L) : ℤ)) : ℤ) : ℝ) := by
      push_cast; ring
    linarith [h2', h3']
  calc |ξ| ≤ (2 : ℝ) ^ ((P.natDegree : ℝ)
        * ((L : ℝ) - (Work.Analysis.EndVar.logN (Nat.floor (a n)) : ℝ))) := hsupp
    _ ≤ (2 : ℝ) ^ (-(3 * (P.natDegree : ℤ) * (uScale ρ (lcL l₁ l₂ 0 L) : ℤ))) := by
        rw [← Real.rpow_intCast]
        exact Real.rpow_le_rpow_of_exponent_le (by norm_num) hexp

/-- `lcWeight c l₁ l₂ 0 k₂ = 2^{-c·k₂}` when `max l₁ l₂ < k₂`. -/
private lemma lcWeight_zero_left_lt {c : ℝ} {l₁ l₂ k₂ : ℕ} (hk : max l₁ l₂ < k₂) :
    lcWeight c l₁ l₂ 0 k₂ = (2 : ℝ) ^ (-(c * (k₂ : ℝ))) := by
  have h1 : ((max l₁ l₂ : ℕ) : ℤ) < (k₂ : ℤ) := by exact_mod_cast hk
  have hlmax : Work.Analysis.EndVar.lmax l₁ l₂ ((0 : ℕ) : ℤ) ((k₂ : ℕ) : ℤ)
      = ((k₂ : ℕ) : ℤ) := by
    rw [Work.Analysis.EndVar.lmax, ← Nat.cast_max]
    omega
  rw [lcWeight, hlmax, Int.cast_natCast]

/-- **The absorption of the doubly-exponential Rademacher--Menshov loss into the gain.** -/
private theorem exp_absorb_lowHigh' (cS d ρ : ℝ) (hcS : 0 < cS) (hd : 2 ≤ d) (hρ : 0 < ρ)
    (hρ8 : 8 * ρ ≤ 1) :
    ∃ C : ℝ, 0 < C ∧ ∀ (l₁ l₂ L : ℕ), max l₁ l₂ < L →
      (2 : ℝ) ^ (4 * ρ * (L : ℝ)) * (2 : ℝ) ^ (-(cS * (max (l₁ : ℝ) (l₂ : ℝ))))
        * (2 : ℝ) ^ (-(d * (L : ℝ)))
        ≤ C * lcWeight (min cS 1 / 2) l₁ l₂ 0 L := by
  refine ⟨1, one_pos, fun l₁ l₂ L hLt => ?_⟩
  rw [lcWeight_zero_left_lt (c := min cS 1 / 2) hLt, one_mul]
  have hLnn : (0 : ℝ) ≤ (L : ℝ) := Nat.cast_nonneg L
  have hmaxnn : (0 : ℝ) ≤ max (l₁ : ℝ) (l₂ : ℝ) := by positivity
  have hfac1 : (2 : ℝ) ^ (-(cS * max (l₁ : ℝ) (l₂ : ℝ))) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by nlinarith [hcS, hmaxnn])
  have hkey : 4 * ρ - d + min cS 1 / 2 ≤ 0 := by
    have h4ρ : 4 * ρ ≤ 1 / 2 := by linarith
    have hmin : min cS 1 / 2 ≤ 1 / 2 := by
      have : min cS 1 ≤ 1 := min_le_right _ _; linarith
    linarith
  have hAp : (0 : ℝ) < (2 : ℝ) ^ (4 * ρ * (L : ℝ)) := Real.rpow_pos_of_pos (by norm_num) _
  have hCp : (0 : ℝ) < (2 : ℝ) ^ (-(d * (L : ℝ))) := Real.rpow_pos_of_pos (by norm_num) _
  have hstep : (2 : ℝ) ^ (4 * ρ * (L : ℝ)) * (2 : ℝ) ^ (-(cS * max (l₁ : ℝ) (l₂ : ℝ)))
        * (2 : ℝ) ^ (-(d * (L : ℝ)))
      ≤ (2 : ℝ) ^ (4 * ρ * (L : ℝ)) * (2 : ℝ) ^ (-(d * (L : ℝ))) := by
    calc (2 : ℝ) ^ (4 * ρ * (L : ℝ)) * (2 : ℝ) ^ (-(cS * max (l₁ : ℝ) (l₂ : ℝ)))
          * (2 : ℝ) ^ (-(d * (L : ℝ)))
        = ((2 : ℝ) ^ (4 * ρ * (L : ℝ)) * (2 : ℝ) ^ (-(cS * max (l₁ : ℝ) (l₂ : ℝ))))
            * (2 : ℝ) ^ (-(d * (L : ℝ))) := by ring
      _ ≤ ((2 : ℝ) ^ (4 * ρ * (L : ℝ)) * 1) * (2 : ℝ) ^ (-(d * (L : ℝ))) := by
          refine mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_left hfac1 hAp.le) hCp.le
      _ = (2 : ℝ) ^ (4 * ρ * (L : ℝ)) * (2 : ℝ) ^ (-(d * (L : ℝ))) := by ring
  have hAC : (2 : ℝ) ^ (4 * ρ * (L : ℝ)) * (2 : ℝ) ^ (-(d * (L : ℝ)))
      = (2 : ℝ) ^ ((4 * ρ - d) * (L : ℝ)) := by
    rw [← Real.rpow_add (by norm_num : (0 : ℝ) < 2)]
    congr 1
    ring
  refine hstep.trans ?_
  rw [hAC]
  refine Real.rpow_le_rpow_of_exponent_le (by norm_num) ?_
  nlinarith [hkey, hLnn]

/-! ## The masked-slice bound with a spike hypothesis about the masked family -/

/-- **The masked slice bound, with the spike hypothesis stated for the masked family itself.** -/
private theorem maskedSlice_le_direct
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
    (hSpk0 : MeasureTheory.eLpNorm (fun x : ℤ => ENNReal.ofReal
        ‖caseBMasked ρ P C₀ a f g l₁ l₂ k₁ k₂ j₁ j₂ t 0 x‖)
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
    have hshift := variationalNorm_le_of_shift r hr1
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
    refine variationalNorm_le_VrFull hr2 (Kv - 1) _ (fun k hk => ?_)
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
  have hspkB : MeasureTheory.eLpNorm (fun x : ℤ => ENNReal.ofReal
      ‖caseBMasked ρ P C₀ a f g l₁ l₂ k₁ k₂ j₁ j₂ t 0 x‖)
      1 MeasureTheory.Measure.count ≤ SPK := hSpk0
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

/-- **The frozen boundary family of the integration-by-parts identity.** -/
private theorem lowDecayB_le_direct
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
    (hSpk0 : MeasureTheory.eLpNorm (fun x : ℤ => ENNReal.ofReal
        ‖caseBMasked ρ P C₀ a f g l₁ l₂ k₁ k₂ j₁ j₂ t 0 x‖)
        1 MeasureTheory.Measure.count ≤ SPK) :
    MeasureTheory.eLpNorm (fun x : ℤ => PointwiseErgodicTheorems.variationalNorm r
        (fun n : ℕ => lowDecayB ρ P C₀ a f g l₁ l₂ k₁ k₂ j₁ j₂ t w n x))
      1 MeasureTheory.Measure.count ≤ (2 * ENNReal.ofReal Cw) * (FRZ + 2 * SPK) := by
  classical
  have hr1 : (1 : NNReal) ≤ r := le_trans (by norm_num : (1 : NNReal) ≤ 2) hr2
  have hms := maskedSlice_le_direct ρ P C₀ a f g l₁ l₂ k₁ k₂ j₁ j₂ t r hr2 Kv hKv1
    hlssK hf hg hFrz hSpk0
  have hEq : (fun (n : ℕ) (x : ℤ) => lowDecayB ρ P C₀ a f g l₁ l₂ k₁ k₂ j₁ j₂ t w n x)
      = fun (n : ℕ) (x : ℤ) => (if Bw ≤ Nat.floor (a n) then w n else 0) *
          caseBMasked ρ P C₀ a f g l₁ l₂ k₁ k₂ j₁ j₂ t n x := by
    funext n x
    simp only [lowDecayB, caseBMasked]
    by_cases h : lowSmallSet ρ C₀ a l₁ l₂ k₁ k₂ n
    · simp only [if_pos h, if_pos (hlower n h), mul_one]
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
private theorem lowDecayW_le_direct
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
    (hSpk0 : ∀ t ∈ Set.Icc (1 / 2 : ℝ) 1, MeasureTheory.eLpNorm (fun x : ℤ =>
        ENNReal.ofReal ‖caseBMasked ρ P C₀ a f g l₁ l₂ k₁ k₂ j₁ j₂ t 0 x‖)
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
    · simp only [lowDecayW, mdlWIntF, caseBMasked, if_pos h, if_pos (hlower n h), mul_one]
    · simp only [lowDecayW, mdlWIntF, caseBMasked, if_neg h, mul_zero,
        intervalIntegral.integral_zero]
  rw [hEq]
  refine (mdlWIntF_norm_le (r := r) hr1 _ _ hmeas hint (fun t ht => ?_)).trans le_rfl
  have hms := maskedSlice_le_direct ρ P C₀ a f g l₁ l₂ k₁ k₂ j₁ j₂ t r hr2 Kv hKv1
    hlssK hf hg (hFrz t ht) (hSpk0 t ht)
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

/-! ## The target theorem -/

theorem lowModelVarCaseBLowHighLinf
    (P : Polynomial ℤ) (hd : 2 ≤ P.natDegree) (r : NNReal) (hr : 2 < r)
    (hA1 : Work.KMTContract.AreaA1) (ρ : ℝ) (hρ : 0 < ρ) (hρ8 : 8 * ρ ≤ 1)
    (C₀ : ℕ) (hC₀ : 1 ≤ C₀) (hρC₀ : ρ * (C₀ : ℝ) ≤ 1 / 8)
    {cS : ℝ} (hcS : 0 < cS) {Cssu : NNReal}
    (hSS : Work.KMTPlan.A6.SSUBodyAtLinf P cS Cssu ρ)
    (B : ℕ) (C : NNReal → NNReal)
    (hRanF : Work.KMTPlan.A6.LowModRandL2FBody P C₀ ρ B C)
    (hRanG : Work.KMTPlan.A6.LowModRandL2GBody P C₀ ρ B C)
    {Cb : ℝ} (hCb : 0 < Cb)
    (hCbb : ∀ (N k : ℕ) (j : ℤ) (t : ℝ), j ∈ ({-1, 0, 1} : Finset ℤ) →
      ¬ (k = 0 ∧ j = -1) → 1 ≤ N → ∀ ξ : ℝ,
      ‖Work.KMTPlan.A6.varphitildeNtj P N k j t ξ‖ ≤ Cb) :
    ∃ Cc : NNReal → NNReal, ∃ Bc : ℕ,
      ∀ (a : ℕ → NNReal) (Λ : NNReal) (l₁ l₂ L : ℕ) (f g : ℤ → ℂ),
        1 < Λ → PointwiseErgodicTheorems.Lacunary Λ a → (∀ n, 1 ≤ a n) →
        max l₁ l₂ < L → Bc ≤ L →
        MeasureTheory.MemLp f 2 MeasureTheory.Measure.count →
        MeasureTheory.MemLp g 2 MeasureTheory.Measure.count →
        MeasureTheory.eLpNorm (fun x : ℤ => PointwiseErgodicTheorems.variationalNorm r
            (fun n : ℕ => Work.KMTPlan.A6.lowModel ρ P C₀ a f g l₁ l₂ 0 L n x))
          1 MeasureTheory.Measure.count
          ≤ (Cc Λ : ENNReal) * ENNReal.ofReal
              (Work.KMTPlan.A6.lcWeight (min cS 1 / 2) l₁ l₂ 0 L)
              * MeasureTheory.eLpNorm f 2 MeasureTheory.Measure.count
              * MeasureTheory.eLpNorm g 2 MeasureTheory.Measure.count := by
  classical
  have hr1 : (1 : NNReal) ≤ r := le_trans (by norm_num : (1 : NNReal) ≤ 2) (le_of_lt hr)
  have hd1 : 1 ≤ P.natDegree := by omega
  obtain ⟨C_RM, hC_RM, hgen⟩ := lowFrozenBilinBound P hd hA1
  obtain ⟨Bφ, hφ⟩ := varphiNt_support_lowSmall ρ hρ C₀ hC₀ hρC₀
  obtain ⟨Bpd, hBpdpos, hBpd⟩ := PderivThreshold P hd
  obtain ⟨Bw, hBwpos, Cw, hCwpos, hWmask⟩ := lowWeightMaskBound P hd1 r hr1
  obtain ⟨Bu, hBu⟩ := uScale_window ρ hρ
  obtain ⟨Bna, hBna⟩ := nonAliasing_diffFreqs ρ hρ
  obtain ⟨Bfs, hfs⟩ := lowModSymbF_support_narrow' ρ hρ C₀ hC₀ hρC₀
  obtain ⟨Bgs, hgs⟩ := lowModSymbG_support_narrow' P hd1 ρ hρ C₀ hC₀ hρC₀
  obtain ⟨Cexp, hCexppos, hCexp⟩ := exp_absorb_lowHigh' cS (P.natDegree : ℝ) ρ hcS
    (by exact_mod_cast hd) hρ hρ8
  -- the size threshold for the admissible scales
  obtain ⟨K₀, hK₀⟩ := exists_pow_ge (max (max (Bw : ℝ) Bpd) 1)
  obtain ⟨K₁, hK₁⟩ := exists_pow_ge ((K₀ : ℝ) + 1)
  have hK₁' : (K₀ : ℝ) ≤ (2 : ℝ) ^ (K₁ : ℝ) := by
    have h := hK₁
    rw [← Real.rpow_natCast] at h
    linarith
  -- the constant
  let ιb : ℝ := max 1 ‖mdlIota‖
  have hιb1 : 1 ≤ ιb := le_max_left _ _
  have hιb0 : 0 ≤ ιb := le_trans zero_le_one hιb1
  let Cc : NNReal → NNReal := fun Lam => ⟨ιb * 4 * (2 * Cw + 1) *
      (C_RM * (4 * lowMfun Lam) * (Cssu : ℝ) * ((C Lam : ℝ) * (C Lam : ℝ)) * Cexp
        + 2 * ((Cssu : ℝ) * ((max 8 Cb) * (max 8 Cb)))), by
      have h1 : (0 : ℝ) ≤ lowMfun Lam := lowMfun_nonneg Lam
      have h2 : (0 : ℝ) ≤ (C Lam : ℝ) := by positivity
      have h2b : (0 : ℝ) ≤ (Cssu : ℝ) := by positivity
      have h3 : (0 : ℝ) ≤ C_RM * (4 * lowMfun Lam) * (Cssu : ℝ) *
          ((C Lam : ℝ) * (C Lam : ℝ)) * Cexp :=
        mul_nonneg (mul_nonneg (mul_nonneg (mul_nonneg hC_RM.le (mul_nonneg (by norm_num) h1))
          h2b) (mul_nonneg h2 h2)) hCexppos.le
      have h4 : (0 : ℝ) ≤ 2 * ((Cssu : ℝ) * ((max 8 Cb) * (max 8 Cb))) := by positivity
      have h5 : (0 : ℝ) ≤ C_RM * (4 * lowMfun Lam) * (Cssu : ℝ) *
          ((C Lam : ℝ) * (C Lam : ℝ)) * Cexp + 2 * ((Cssu : ℝ) * ((max 8 Cb) * (max 8 Cb))) :=
        add_nonneg h3 h4
      have h6 : (0 : ℝ) ≤ ιb * 4 * (2 * Cw + 1) :=
        mul_nonneg (mul_nonneg hιb0 (by norm_num)) (by positivity)
      have h7 : (0 : ℝ) ≤ ιb * 4 * (2 * Cw + 1) *
          (C_RM * (4 * lowMfun Lam) * (Cssu : ℝ) * ((C Lam : ℝ) * (C Lam : ℝ)) * Cexp
            + 2 * ((Cssu : ℝ) * ((max 8 Cb) * (max 8 Cb)))) :=
        mul_nonneg h6 h5
      linarith⟩
  -- the scale threshold
  let Bc : ℕ := max 1 (max (2 * C₀ + 1) (max (Nat.ceil (C₀ * ((K₁ : ℝ) + 2)) + 1)
      (max (max (max (max B Bu) Bna) (max Bfs Bgs)) (max Bφ Bw))))
  refine ⟨Cc, Bc, ?_⟩
  intro a Λ l₁ l₂ L f g hΛ hlac ha1 hLt hBcL hf hg
  -- ===== extraction of the thresholds from `Bc ≤ L` =====
  have hex := hBcL
  simp only [Bc] at hex
  rw [max_le_iff] at hex
  obtain ⟨hL1, hex1⟩ := hex
  rw [max_le_iff] at hex1
  obtain ⟨h2C₀n, hex2⟩ := hex1
  rw [max_le_iff] at hex2
  obtain ⟨hceil, hex3⟩ := hex2
  rw [max_le_iff] at hex3
  obtain ⟨hex4, hex5⟩ := hex3
  rw [max_le_iff] at hex4
  obtain ⟨hex6, hex7⟩ := hex4
  rw [max_le_iff] at hex6
  obtain ⟨hex8, hBna_le_L⟩ := hex6
  rw [max_le_iff] at hex8
  obtain ⟨hB_le_L, hBu_le_L⟩ := hex8
  rw [max_le_iff] at hex7
  obtain ⟨hBfs_le_L, hBgs_le_L⟩ := hex7
  rw [max_le_iff] at hex5
  obtain ⟨hBφ_le_L, hBw_le_L⟩ := hex5
  have h2C₀ : 2 * C₀ ≤ L := by omega
  have hC₀pos : (0 : ℝ) < (C₀ : ℝ) := by exact_mod_cast (by omega : 0 < C₀)
  have hBC₀ : C₀ * ((K₁ : ℝ) + 2) < (L : ℝ) := by
    have h2 : C₀ * ((K₁ : ℝ) + 2) ≤ (Nat.ceil (C₀ * ((K₁ : ℝ) + 2)) : ℝ) := Nat.le_ceil _
    have h3 : ((Nat.ceil (C₀ * ((K₁ : ℝ) + 2)) + 1 : ℕ) : ℝ) ≤ (L : ℝ) := by exact_mod_cast hceil
    push_cast at h3
    linarith
  -- ===== basic facts =====
  have hLc : lcL l₁ l₂ 0 L = L := by
    rw [lcL, max_eq_right (Nat.zero_le L), max_eq_right (le_of_lt hLt)]
  have hl₁L : l₁ ≤ L := le_trans (le_max_left _ _) (le_of_lt hLt)
  have hl₂L : l₂ ≤ L := le_trans (le_max_right _ _) (le_of_lt hLt)
  have hN : ∀ n : ℕ, 1 ≤ Nat.floor (a n) := fun n => Nat.le_floor (by exact_mod_cast ha1 n)
  have hmaxlR : max (l₁ : ℝ) (l₂ : ℝ) < (L : ℝ) := by
    have h2 : ((max l₁ l₂ : ℕ) : ℝ) < (L : ℝ) := by exact_mod_cast hLt
    rwa [Nat.cast_max] at h2
  -- ===== the size of `⌊a n⌋` on the small-scale set =====
  have hscale : ∀ (N : ℕ), 1 ≤ N → L ≤ Work.Analysis.EndVar.heightScale C₀ N →
      (max (max (Bw : ℝ) Bpd) 1) ≤ (N : ℝ) := by
    intro N hN1 hLN
    have h1 : (2 : ℝ) ^ ((2 : ℝ) ^ ((L : ℝ) / (C₀ : ℝ) - 2)) ≤ (N : ℝ) :=
      scale_ge_of_heightScale C₀ hC₀ hN1 hLN h2C₀
    have hK1t : ((K₁ : ℝ) + 2) ≤ (L : ℝ) / (C₀ : ℝ) := by
      rw [le_div_iff₀ hC₀pos]
      linarith
    have ht : (K₁ : ℝ) ≤ (L : ℝ) / (C₀ : ℝ) - 2 := by linarith
    have h2 : (2 : ℝ) ^ (K₁ : ℝ) ≤ (2 : ℝ) ^ ((L : ℝ) / (C₀ : ℝ) - 2) :=
      Real.rpow_le_rpow_of_exponent_le (by norm_num) ht
    have h3 : (K₀ : ℝ) ≤ (2 : ℝ) ^ ((L : ℝ) / (C₀ : ℝ) - 2) := le_trans hK₁' h2
    have h4 : (2 : ℝ) ^ (K₀ : ℝ) ≤ (2 : ℝ) ^ ((2 : ℝ) ^ ((L : ℝ) / (C₀ : ℝ) - 2)) :=
      Real.rpow_le_rpow_of_exponent_le (by norm_num) h3
    have h5 : (max (max (Bw : ℝ) Bpd) 1) ≤ (2 : ℝ) ^ (K₀ : ℝ) := by
      have hh := hK₀
      rw [← Real.rpow_natCast] at hh
      exact hh
    linarith [h5]
  have hlow : ∀ n : ℕ, lowSmallSet ρ C₀ a l₁ l₂ 0 L n →
      (max (max (Bw : ℝ) Bpd) 1) ≤ ((Nat.floor (a n) : ℕ) : ℝ) := by
    intro n hn
    have h3 : (L : ℤ) ≤ (Work.Analysis.EndVar.heightScale C₀ (Nat.floor (a n)) : ℤ) :=
      (lowSmallSet_iff.mp hn).1.2.2
    have h3' : L ≤ Work.Analysis.EndVar.heightScale C₀ (Nat.floor (a n)) := by exact_mod_cast h3
    exact hscale (Nat.floor (a n)) (hN n) h3'
  have hP : ∀ n : ℕ, lowSmallSet ρ C₀ a l₁ l₂ 0 L n →
      ∀ t ∈ Set.Icc (1 / 2 : ℝ) 1, PderivR P ((Nat.floor (a n) : ℝ) * t) ≠ 0 := by
    intro n hn t ht
    refine hBpd (Nat.floor (a n)) t ?_ ht
    have h1 := hlow n hn
    have h2 : Bpd ≤ max (max (Bw : ℝ) Bpd) 1 := le_trans (le_max_right _ _) (le_max_left _ _)
    linarith
  have hlower : ∀ n : ℕ, lowSmallSet ρ C₀ a l₁ l₂ 0 L n → Bw ≤ Nat.floor (a n) := by
    intro n hn
    have h1 := hlow n hn
    have h2 : (Bw : ℝ) ≤ max (max (Bw : ℝ) Bpd) 1 := le_trans (le_max_left _ _) (le_max_left _ _)
    have h3 : (Bw : ℝ) ≤ ((Nat.floor (a n) : ℕ) : ℝ) := le_trans h2 h1
    exact_mod_cast h3
  -- ===== the uScale conditions =====
  have hBuL := hBu L hBu_le_L
  have hu1 : 1 ≤ uScale ρ L := le_trans hL1 hBuL.1
  have huL : max (l₁ : ℝ) (l₂ : ℝ) ≤ (uScale ρ L : ℝ) := by
    have h2 : (max l₁ l₂ : ℕ) ≤ uScale ρ L := le_trans (le_of_lt hLt) hBuL.1
    have h3 : ((max l₁ l₂ : ℕ) : ℝ) ≤ (uScale ρ L : ℝ) := by exact_mod_cast h2
    rwa [Nat.cast_max] at h3
  have huL' : max l₁ l₂ ≤ uScale ρ (lcL l₁ l₂ 0 L) := by
    rw [hLc]
    exact le_trans (le_of_lt hLt) hBuL.1
  have hu2 : (2 : ℝ) ^ (ρ * max (l₁ : ℝ) (l₂ : ℝ)) ≤ (uScale ρ L : ℝ) := by
    refine le_trans ?_ hBuL.2
    refine Real.rpow_le_rpow_of_exponent_le (by norm_num) ?_
    have : max (l₁ : ℝ) (l₂ : ℝ) ≤ (L : ℝ) := le_of_lt hmaxlR
    nlinarith [hρ.le]
  have hNA₁ : NonAliasing (-(3 * (uScale ρ L : ℤ))) (diffFreqs ρ l₁) :=
    hBna L l₁ hBna_le_L hl₁L
  have hNA₂ : NonAliasing (-(3 * (uScale ρ L : ℤ))) (diffFreqs ρ l₂) :=
    hBna L l₂ hBna_le_L hl₂L
  -- ===== the supports =====
  have hsupF : ∀ (j₁ : ℤ), (j₁ = 0 ∨ j₁ = 1) → ∀ (t : ℝ), t ∈ Set.Icc (1 / 2 : ℝ) 1 →
      ∀ (n : ℕ) (ξ : ℝ),
        lowModSymbF ρ C₀ a l₁ l₂ 0 L j₁ t n ξ ≠ 0 →
        |ξ| ≤ (2 : ℝ) ^ (-(3 * (uScale ρ (lcL l₁ l₂ 0 L) : ℤ))) := by
    intro j₁ hj₁ t ht n ξ hne
    exact hfs a l₁ l₂ L (by rw [hLc]; exact hBfs_le_L) j₁
      (by rcases hj₁ with h | h <;> simp [h]) t ht n ξ hne
  have hsupG : ∀ (t : ℝ), t ∈ Set.Icc (1 / 2 : ℝ) 1 → ∀ (n : ℕ) (ξ : ℝ),
      lowModSymbG ρ P C₀ a l₁ l₂ 0 L (-1) t n ξ ≠ 0 →
      |ξ| ≤ (2 : ℝ) ^
        (-(3 * (P.natDegree : ℤ) * (uScale ρ (lcL l₁ l₂ 0 L) : ℤ))) :=
    fun t ht n ξ hne => hgs a l₁ l₂ L (by rw [hLc]; exact hBgs_le_L) t ht n ξ hne
  -- the window hypothesis of the spike bound
  have hφ' : ∀ Nr : ℕ,
      Work.Analysis.EndVar.inIndexSet C₀ (max (l₁ : ℤ) (l₂ : ℤ)) (0 : ℤ) (L : ℤ) Nr →
      Nr ≤ Work.KMTAreas.A7.splitCut ρ (lcL l₁ l₂ 0 L) →
      Bφ ≤ lcL l₁ l₂ 0 L →
      L + 3 * uScale ρ (lcL l₁ l₂ 0 L) ≤ (Work.Analysis.EndVar.logN Nr).toNat := by
    intro Nr h1 h2 h3
    have := hφ l₁ l₂ 0 L Nr h1 h2 h3
    rwa [max_eq_right (Nat.zero_le L)] at this
  -- ===== the truncation `Kv` =====
  set Kv : ℕ := lowTrunc (2 * Real.log 2 / Real.log (Λ : ℝ) + 3) ρ (lcL l₁ l₂ 0 L) + 1
    with hKvdef
  have hKv1 : 1 ≤ Kv := by rw [hKvdef]; omega
  have hlssK : ∀ k : ℕ, Kv ≤ k → ¬ lowSmallSet ρ C₀ a l₁ l₂ 0 L k := by
    intro k hk
    exact not_lss_of_lowTrunc_lt ρ hρ C₀ Λ hΛ a hlac ha1 l₁ l₂ 0 L k (by rw [hKvdef] at hk; omega)
  set F2 : ENNReal := MeasureTheory.eLpNorm f 2 MeasureTheory.Measure.count with hF2def
  set G2 : ENNReal := MeasureTheory.eLpNorm g 2 MeasureTheory.Measure.count with hG2def
  set FRZ : ENNReal := ENNReal.ofReal (C_RM * ((Nat.log2 Kv : ℝ) + 2) ^ (2 : ℝ)) *
      (ENNReal.ofReal (Cssu : ℝ) *
        ENNReal.ofReal ((2 : ℝ) ^ (-(cS * max (l₁ : ℝ) (l₂ : ℝ)))) *
        (ENNReal.ofReal (C Λ : ℝ) * ENNReal.ofReal (C Λ : ℝ))) * F2 * G2 with hFRZdef
  set SPK : ENNReal := (ENNReal.ofReal (Cssu : ℝ) *
      ENNReal.ofReal ((2 : ℝ) ^ (-(cS * max (l₁ : ℝ) (l₂ : ℝ)))) *
      (ENNReal.ofReal (max 8 Cb) * ENNReal.ofReal (max 8 Cb))) * F2 * G2 with hSPKdef
  have hFrzJ : ∀ (j₁ : ℤ), (j₁ = 0 ∨ j₁ = 1) → ∀ t ∈ Set.Icc (1 / 2 : ℝ) 1,
      MeasureTheory.eLpNorm (fun x : ℤ => Work.Analysis.Variation.VrFull 2 Kv
          (fun n : ℕ => caseBAnchored ρ P C₀ a f g l₁ l₂ 0 L j₁ (-1) t n x))
        1 MeasureTheory.Measure.count ≤ FRZ := by
    intro j₁ hj₁ t ht
    have hj₁' : j₁ ∈ ({-1, 0, 1} : Finset ℤ) := by rcases hj₁ with h | h <;> simp [h]
    have hkj : ¬ ((0 : ℕ) = 0 ∧ j₁ = -1) := by
      rintro ⟨-, h⟩
      rcases hj₁ with h' | h' <;> omega
    have hk₂ : ¬ (L = 0 ∧ (-1 : ℤ) = -1) := by rintro ⟨h, -⟩; omega
    have hbF : ∀ (n : ℕ) (ξ : ℝ),
        ‖lowModSymbF ρ C₀ a l₁ l₂ 0 L j₁ t n ξ‖ ≤ 8 := by
      intro n ξ
      simp only [lowModSymbF]
      split_ifs with hn hls
      · simp
      · exact norm_varphiNtj_le_eight (Nat.floor (a n)) 0 j₁ hj₁'
          (Or.inr (by rcases hj₁ with h | h <;> omega))
          (Nat.le_floor (by exact_mod_cast ha1 n)) t ξ
      · simp
    have hbG : ∀ (n : ℕ) (ξ : ℝ),
        ‖lowModSymbG ρ P C₀ a l₁ l₂ 0 L (-1) t n ξ‖ ≤ Cb := by
      intro n ξ
      simp only [lowModSymbG]
      split_ifs with hn hls
      · simp only [norm_zero]; exact hCb.le
      · exact hCbb (Nat.floor (a n)) L (-1) t (by simp) (by rintro ⟨h, -⟩; omega)
          (Nat.le_floor (by exact_mod_cast ha1 n)) ξ
      · simp only [norm_zero]; exact hCb.le
    have h := hgen C₀ hC₀ ρ hρ B C hRanF hRanG cS hcS Cssu hSS
      (uScale ρ (lcL l₁ l₂ 0 L)) Λ hΛ a hlac ha1 l₁ l₂ 0 L Kv
      (by rw [hLc]; exact hB_le_L) (by rw [hLc]; exact huL) (by rw [hLc]; exact hu2)
      j₁ (-1) hj₁' (by simp) hkj hk₂ t ht f g hf hg
      (hsupF j₁ hj₁ t ht) (hsupG t ht) 8 Cb hbF hbG
    simpa only [hFRZdef, hF2def, hG2def, caseBAnchored, ENNReal.ofReal_coe_nnreal] using h
  have hSpk0J : ∀ (j₁ : ℤ), (j₁ = 0 ∨ j₁ = 1) → ∀ t ∈ Set.Icc (1 / 2 : ℝ) 1,
      MeasureTheory.eLpNorm (fun x : ℤ => ENNReal.ofReal
          ‖caseBMasked ρ P C₀ a f g l₁ l₂ 0 L j₁ (-1) t 0 x‖)
        1 MeasureTheory.Measure.count ≤ SPK := by
    intro j₁ hj₁ t ht
    have hj₁' : j₁ ∈ ({-1, 0, 1} : Finset ℤ) := by rcases hj₁ with h | h <;> simp [h]
    have hkj : ¬ ((0 : ℕ) = 0 ∧ j₁ = -1) := by
      rintro ⟨-, h⟩
      rcases hj₁ with h' | h' <;> omega
    have hk₂ : ¬ (L = 0 ∧ (-1 : ℤ) = -1) := by rintro ⟨h, -⟩; omega
    by_cases h0 : lowSmallSet ρ C₀ a l₁ l₂ 0 L 0
    · have hfun : caseBMasked ρ P C₀ a f g l₁ l₂ 0 L j₁ (-1) t 0
          = caseBSpike ρ P a f g l₁ l₂ 0 L j₁ (-1) t := by
        funext x
        simp only [caseBMasked, caseBSpike, if_pos h0]
      have heq : (fun x : ℤ => ENNReal.ofReal
            ‖caseBMasked ρ P C₀ a f g l₁ l₂ 0 L j₁ (-1) t 0 x‖)
          = (fun x : ℤ => ENNReal.ofReal
            ‖caseBSpike ρ P a f g l₁ l₂ 0 L j₁ (-1) t x‖) := by
        rw [hfun]
      rw [heq]
      refine (caseBSpikeLe P hd ρ hρ hcS hSS C₀ hC₀ hρC₀ a l₁ l₂ L j₁ (-1) t ht hj₁' (by simp)
        hkj hk₂ Bφ hφ' hBφ_le_L hLc hu1 huL hu2 hNA₁ hNA₂ h0
        hCb hCbb f g hf hg).trans (le_of_eq ?_)
      rw [hSPKdef, hF2def, hG2def]
      simp only [← ENNReal.ofReal_coe_nnreal]
      ring
    · have hz : caseBMasked ρ P C₀ a f g l₁ l₂ 0 L j₁ (-1) t 0 = 0 := by
        funext x
        simp only [caseBMasked, if_neg h0, Pi.zero_apply]
      have hgoal : (fun x : ℤ => ENNReal.ofReal
            ‖caseBMasked ρ P C₀ a f g l₁ l₂ 0 L j₁ (-1) t 0 x‖)
          = fun _ : ℤ => (0 : ENNReal) := by
        funext x
        rw [hz]
        simp
      rw [hgoal]
      simp
  -- ===== the four slice bounds =====
  set Nw : ENNReal := ENNReal.ofReal (2 * Cw + 1) with hNwdef
  have hNw_ge : (2 : ENNReal) * ENNReal.ofReal Cw ≤ Nw := by
    have h2 : (2 : ENNReal) = ENNReal.ofReal (2 : ℝ) := (ENNReal.ofReal_ofNat 2).symm
    rw [h2, hNwdef, ← ENNReal.ofReal_mul (by norm_num : (0 : ℝ) ≤ 2)]
    exact ENNReal.ofReal_le_ofReal (by linarith)
  have hr2 : 2 ≤ r := le_of_lt hr
  obtain ⟨Y1, hY1def⟩ : ∃ Y : ℕ → ℤ → ℂ, Y = (fun n x =>
      lowDecayB ρ P C₀ a f g l₁ l₂ 0 L 0 (-1) 1
        (fun n => mdlW1 P (Nat.floor (a n)) 1) n x) := ⟨_, rfl⟩
  obtain ⟨Y2, hY2def⟩ : ∃ Y : ℕ → ℤ → ℂ, Y = (fun n x =>
      lowDecayB ρ P C₀ a f g l₁ l₂ 0 L 0 (-1) (1 / 2)
        (fun n => mdlW1 P (Nat.floor (a n)) (1 / 2)) n x) := ⟨_, rfl⟩
  obtain ⟨Y3, hY3def⟩ : ∃ Y : ℕ → ℤ → ℂ, Y = (fun n x =>
      lowDecayW ρ P C₀ a f g l₁ l₂ 0 L 1 (-1)
        (fun n t => mdlW1 P (Nat.floor (a n)) t) n x) := ⟨_, rfl⟩
  obtain ⟨Y4, hY4def⟩ : ∃ Y : ℕ → ℤ → ℂ, Y = (fun n x =>
      lowDecayW ρ P C₀ a f g l₁ l₂ 0 L 0 (-1)
        (fun n t => mdlW1 P (Nat.floor (a n)) t) n x) := ⟨_, rfl⟩
  -- ===== the four slice bounds =====
  set Nw : ENNReal := ENNReal.ofReal (2 * Cw + 1) with hNwdef
  have hNw_ge : (2 : ENNReal) * ENNReal.ofReal Cw ≤ Nw := by
    have h2 : (2 : ENNReal) = ENNReal.ofReal (2 : ℝ) := (ENNReal.ofReal_ofNat 2).symm
    rw [h2, hNwdef, ← ENNReal.ofReal_mul (by norm_num : (0 : ℝ) ≤ 2)]
    exact ENNReal.ofReal_le_ofReal (by linarith)
  have hr2 : 2 ≤ r := le_of_lt hr
  have ht1 : (1 : ℝ) ∈ Set.Icc (1 / 2 : ℝ) 1 := ⟨by norm_num, le_rfl⟩
  have ht2 : ((1 / 2 : ℝ)) ∈ Set.Icc (1 / 2 : ℝ) 1 := ⟨le_rfl, by norm_num⟩
  have hNmono : Monotone (fun n : ℕ => Nat.floor (a n)) := lacunary_floor_mono Λ hΛ hlac
  have hw1 : PointwiseErgodicTheorems.variationalNorm r
      (fun n : ℕ => if Bw ≤ Nat.floor (a n) then mdlW1 P (Nat.floor (a n)) 1 else 0)
      ≤ ENNReal.ofReal Cw := (hWmask (fun n => Nat.floor (a n)) 1 hNmono ht1).1
  have hw2 : PointwiseErgodicTheorems.variationalNorm r
      (fun n : ℕ => if Bw ≤ Nat.floor (a n) then mdlW1 P (Nat.floor (a n)) (1 / 2) else 0)
      ≤ ENNReal.ofReal Cw := (hWmask (fun n => Nat.floor (a n)) (1 / 2) hNmono ht2).1
  have hwW1 : ∀ t ∈ Set.Icc (1 / 2 : ℝ) 1, PointwiseErgodicTheorems.variationalNorm r
      (fun n : ℕ => if Bw ≤ Nat.floor (a n) then mdlW1 P (Nat.floor (a n)) t else 0)
      ≤ ENNReal.ofReal Cw := fun t ht => (hWmask (fun n => Nat.floor (a n)) t hNmono ht).1
  have hwW2 : ∀ t ∈ Set.Icc (1 / 2 : ℝ) 1, PointwiseErgodicTheorems.variationalNorm r
      (fun n : ℕ => if Bw ≤ Nat.floor (a n) then mdlW2 P (Nat.floor (a n)) t else 0)
      ≤ ENNReal.ofReal Cw := fun t ht => (hWmask (fun n => Nat.floor (a n)) t hNmono ht).2.1
  have hwm1 : ∀ n : ℕ, Measurable (fun t : ℝ =>
      if Bw ≤ Nat.floor (a n) then mdlW1 P (Nat.floor (a n)) t else 0) := by
    intro n
    by_cases h : Bw ≤ Nat.floor (a n)
    · simp only [if_pos h]; exact measurable_mdlW1 P _
    · simp only [if_neg h]; exact measurable_const
  have hwbd1 : ∀ n : ℕ, lowSmallSet ρ C₀ a l₁ l₂ 0 L n → ∃ C : ℝ,
      ∀ t ∈ Set.Icc (1 / 2 : ℝ) 1,
        ‖(if Bw ≤ Nat.floor (a n) then mdlW1 P (Nat.floor (a n)) t else 0)‖ ≤ C := by
    intro n hn
    obtain ⟨C, _hC0, hC⟩ := mdl_W1_bound P (Nat.floor (a n)) (hP n hn)
    exact ⟨C, fun t ht => by rw [if_pos (hlower n hn)]; exact hC t ht⟩
  have hwm2 : ∀ n : ℕ, Measurable (fun t : ℝ =>
      if Bw ≤ Nat.floor (a n) then mdlW2 P (Nat.floor (a n)) t else 0) := by
    intro n
    by_cases h : Bw ≤ Nat.floor (a n)
    · simp only [if_pos h]; exact measurable_mdlW2 P _
    · simp only [if_neg h]; exact measurable_const
  have hwbd2 : ∀ n : ℕ, lowSmallSet ρ C₀ a l₁ l₂ 0 L n → ∃ C : ℝ,
      ∀ t ∈ Set.Icc (1 / 2 : ℝ) 1,
        ‖(if Bw ≤ Nat.floor (a n) then mdlW2 P (Nat.floor (a n)) t else 0)‖ ≤ C := by
    intro n hn
    obtain ⟨C, _hC0, hC⟩ := mdl_W2_bound P (Nat.floor (a n)) (hP n hn)
    exact ⟨C, fun t ht => by rw [if_pos (hlower n hn)]; exact hC t ht⟩
  have hM1 := caseBSliceWMeasInt ρ P C₀ a f g l₁ l₂ 0 L 1 (-1) 0
      (fun n t => if Bw ≤ Nat.floor (a n) then mdlW1 P (Nat.floor (a n)) t else 0)
      hwm1 hwbd1 (by simp) (by simp) (Or.inr (by norm_num))
      (Or.inl (by omega)) hf hg
  have hM2 := caseBSliceWMeasInt ρ P C₀ a f g l₁ l₂ 0 L 0 (-1) 0
      (fun n t => if Bw ≤ Nat.floor (a n) then mdlW2 P (Nat.floor (a n)) t else 0)
      hwm2 hwbd2 (by simp) (by simp) (Or.inr (by norm_num))
      (Or.inl (by omega)) hf hg
  obtain ⟨Y1, hY1def⟩ : ∃ Y : ℕ → ℤ → ℂ, Y = (fun n x =>
      lowDecayB ρ P C₀ a f g l₁ l₂ 0 L 0 (-1) 1
        (fun n => mdlW1 P (Nat.floor (a n)) 1) n x) := ⟨_, rfl⟩
  obtain ⟨Y2, hY2def⟩ : ∃ Y : ℕ → ℤ → ℂ, Y = (fun n x =>
      lowDecayB ρ P C₀ a f g l₁ l₂ 0 L 0 (-1) (1 / 2)
        (fun n => mdlW1 P (Nat.floor (a n)) (1 / 2)) n x) := ⟨_, rfl⟩
  obtain ⟨Y3, hY3def⟩ : ∃ Y : ℕ → ℤ → ℂ, Y = (fun n x =>
      lowDecayW ρ P C₀ a f g l₁ l₂ 0 L 1 (-1)
        (fun n t => mdlW1 P (Nat.floor (a n)) t) n x) := ⟨_, rfl⟩
  obtain ⟨Y4, hY4def⟩ : ∃ Y : ℕ → ℤ → ℂ, Y = (fun n x =>
      lowDecayW ρ P C₀ a f g l₁ l₂ 0 L 0 (-1)
        (fun n t => mdlW2 P (Nat.floor (a n)) t) n x) := ⟨_, rfl⟩
  have hY1 : MeasureTheory.eLpNorm (fun x : ℤ => PointwiseErgodicTheorems.variationalNorm r
      (fun n : ℕ => Y1 n x)) 1 MeasureTheory.Measure.count ≤ Nw * (FRZ + 2 * SPK) := by
    have h := lowDecayB_le_direct ρ P C₀ a f g l₁ l₂ 0 L 0 (-1) 1 r hr2 Bw Cw
      (fun n => mdlW1 P (Nat.floor (a n)) 1) Kv hKv1 hlssK hlower hw1 hf hg
      (hFrzJ 0 (Or.inl rfl) 1 ht1) (hSpk0J 0 (Or.inl rfl) 1 ht1)
    rw [hY1def]
    exact h.trans (mul_le_mul_of_nonneg_right hNw_ge bot_le)
  have hY2 : MeasureTheory.eLpNorm (fun x : ℤ => PointwiseErgodicTheorems.variationalNorm r
      (fun n : ℕ => Y2 n x)) 1 MeasureTheory.Measure.count ≤ Nw * (FRZ + 2 * SPK) := by
    have h := lowDecayB_le_direct ρ P C₀ a f g l₁ l₂ 0 L 0 (-1) (1 / 2) r hr2 Bw Cw
      (fun n => mdlW1 P (Nat.floor (a n)) (1 / 2)) Kv hKv1 hlssK hlower hw2 hf hg
      (hFrzJ 0 (Or.inl rfl) (1 / 2) ht2) (hSpk0J 0 (Or.inl rfl) (1 / 2) ht2)
    rw [hY2def]
    exact h.trans (mul_le_mul_of_nonneg_right hNw_ge bot_le)
  have hY3 : MeasureTheory.eLpNorm (fun x : ℤ => PointwiseErgodicTheorems.variationalNorm r
      (fun n : ℕ => Y3 n x)) 1 MeasureTheory.Measure.count ≤ Nw * (FRZ + 2 * SPK) := by
    have h := lowDecayW_le_direct ρ P C₀ a f g l₁ l₂ 0 L 1 (-1) r hr2 Bw Cw
      (fun n t => mdlW1 P (Nat.floor (a n)) t) Kv hKv1 hlssK hlower hwW1 hM1.1 hM1.2 hf hg
      (fun t ht => hFrzJ 1 (Or.inr rfl) t ht) (fun t ht => hSpk0J 1 (Or.inr rfl) t ht)
    rw [hY3def]
    exact h.trans (mul_le_mul_of_nonneg_right hNw_ge bot_le)
  have hY4 : MeasureTheory.eLpNorm (fun x : ℤ => PointwiseErgodicTheorems.variationalNorm r
      (fun n : ℕ => Y4 n x)) 1 MeasureTheory.Measure.count ≤ Nw * (FRZ + 2 * SPK) := by
    have h := lowDecayW_le_direct ρ P C₀ a f g l₁ l₂ 0 L 0 (-1) r hr2 Bw Cw
      (fun n t => mdlW2 P (Nat.floor (a n)) t) Kv hKv1 hlssK hlower hwW2 hM2.1 hM2.2 hf hg
      (fun t ht => hFrzJ 0 (Or.inl rfl) t ht) (fun t ht => hSpk0J 0 (Or.inl rfl) t ht)
    rw [hY4def]
    exact h.trans (mul_le_mul_of_nonneg_right hNw_ge bot_le)
  -- ===== the pointwise identity and the four-term bound =====
  obtain ⟨cs, hcs⟩ : ∃ Y : ℂ, Y = (mdlScale P L : ℂ) * mdlIota := ⟨_, rfl⟩
  obtain ⟨cg, hcg⟩ : ∃ Y : ℂ, Y = ((mdlScaleGe P 0 L : ℝ) : ℂ) := ⟨_, rfl⟩
  have hident : ∀ (n : ℕ) (x : ℤ), lowModel ρ P C₀ a f g l₁ l₂ 0 L n x
      = cs * (Y1 n x - Y2 n x) - cg * Y3 n x + cs * Y4 n x := by
    intro n x
    rw [hY1def, hY2def, hY3def, hY4def, hcs, hcg]
    exact lowModel_eq_decayLowHigh ρ P C₀ a f g l₁ l₂ L hL1 hLc hN hP hf hg n x
  set Ccoef : ENNReal := ENNReal.ofReal ((2 : ℝ) ^ (-((P.natDegree : ℝ) * (L : ℝ)))) *
      ENNReal.ofReal ιb with hCcoefdef
  have hCtop : Ccoef ≠ ⊤ := by
    rw [hCcoefdef]
    exact ENNReal.mul_ne_top ENNReal.ofReal_ne_top ENNReal.ofReal_ne_top
  have hcs_norm : ‖cs‖ ≤ (2 : ℝ) ^ (-((P.natDegree : ℝ) * (L : ℝ))) * ιb := by
    rw [hcs]
    calc ‖((mdlScale P L : ℝ) : ℂ) * mdlIota‖
        ≤ ‖(((mdlScale P L : ℝ)) : ℂ)‖ * ‖mdlIota‖ := norm_mul_le _ _
      _ = (2 : ℝ) ^ (-((P.natDegree : ℝ) * (L : ℝ))) * ‖mdlIota‖ := by
          rw [norm_ofReal_complex', mdlScale,
            abs_of_nonneg (Real.rpow_pos_of_pos (by norm_num) _).le]
      _ ≤ (2 : ℝ) ^ (-((P.natDegree : ℝ) * (L : ℝ))) * ιb :=
          mul_le_mul_of_nonneg_left (le_max_right _ _) (Real.rpow_pos_of_pos (by norm_num) _).le
  have hcg_norm : ‖cg‖ ≤ (2 : ℝ) ^ (-((P.natDegree : ℝ) * (L : ℝ))) * ιb := by
    rw [hcg]
    have hge : mdlScaleGe P 0 L = (2 : ℝ) ^ (-((P.natDegree : ℝ) * (L : ℝ))) := by
      rw [mdlScaleGe]; congr 1; ring
    calc ‖((mdlScaleGe P 0 L : ℝ) : ℂ)‖ = |mdlScaleGe P 0 L| := norm_ofReal_complex' _
      _ = (2 : ℝ) ^ (-((P.natDegree : ℝ) * (L : ℝ))) := by
          rw [hge, abs_of_nonneg (Real.rpow_pos_of_pos (by norm_num) _).le]
      _ ≤ (2 : ℝ) ^ (-((P.natDegree : ℝ) * (L : ℝ))) * ιb :=
          le_mul_of_one_le_right (Real.rpow_pos_of_pos (by norm_num) _).le hιb1
  have hcs_bd : ‖cs‖ₑ ≤ Ccoef := by
    rw [enorm_eq_ofReal_norm', hCcoefdef,
      ← ENNReal.ofReal_mul (Real.rpow_pos_of_pos (by norm_num) _).le]
    exact ENNReal.ofReal_le_ofReal hcs_norm
  have hcg_bd : ‖cg‖ₑ ≤ Ccoef := by
    rw [enorm_eq_ofReal_norm', hCcoefdef,
      ← ENNReal.ofReal_mul (Real.rpow_pos_of_pos (by norm_num) _).le]
    exact ENNReal.ofReal_le_ofReal hcg_norm
  have hfour := eLpNorm_varNorm_four_le (r := r) hr1 cs cg hCtop hcs_bd hcg_bd Y1 Y2 Y3 Y4
  have hlhs : (fun x : ℤ => PointwiseErgodicTheorems.variationalNorm r
        (fun n : ℕ => cs * (Y1 n x - Y2 n x) - cg * Y3 n x + cs * Y4 n x))
      = (fun x : ℤ => PointwiseErgodicTheorems.variationalNorm r
        (fun n : ℕ => lowModel ρ P C₀ a f g l₁ l₂ 0 L n x)) := by
    funext x
    congr 1
    funext n
    exact (hident n x).symm
  rw [hlhs] at hfour
  have hsum : ((MeasureTheory.eLpNorm (fun x : ℤ => PointwiseErgodicTheorems.variationalNorm r
          (fun n : ℕ => Y1 n x)) 1 MeasureTheory.Measure.count
        + MeasureTheory.eLpNorm (fun x : ℤ => PointwiseErgodicTheorems.variationalNorm r
          (fun n : ℕ => Y2 n x)) 1 MeasureTheory.Measure.count)
        + MeasureTheory.eLpNorm (fun x : ℤ => PointwiseErgodicTheorems.variationalNorm r
          (fun n : ℕ => Y3 n x)) 1 MeasureTheory.Measure.count)
        + MeasureTheory.eLpNorm (fun x : ℤ => PointwiseErgodicTheorems.variationalNorm r
          (fun n : ℕ => Y4 n x)) 1 MeasureTheory.Measure.count
      ≤ 4 * (Nw * (FRZ + 2 * SPK)) := by
    have h4 : (4 : ENNReal) * (Nw * (FRZ + 2 * SPK))
        = (((Nw * (FRZ + 2 * SPK)) + Nw * (FRZ + 2 * SPK)) + Nw * (FRZ + 2 * SPK))
          + Nw * (FRZ + 2 * SPK) := by ring
    rw [h4]
    exact add_le_add (add_le_add (add_le_add hY1 hY2) hY3) hY4
  have hmain : MeasureTheory.eLpNorm (fun x : ℤ => PointwiseErgodicTheorems.variationalNorm r
      (fun n : ℕ => lowModel ρ P C₀ a f g l₁ l₂ 0 L n x)) 1 MeasureTheory.Measure.count
      ≤ Ccoef * (4 * (Nw * (FRZ + 2 * SPK))) :=
    hfour.trans (mul_le_mul_of_nonneg_left hsum bot_le)
  -- ===== the final absorption =====
  have hCssu_nn : (0 : ℝ) ≤ (Cssu : ℝ) := by positivity
  have hLam_nn : (0 : ℝ) ≤ (C Λ : ℝ) := by positivity
  have hKb_nn : (0 : ℝ) ≤ max 8 Cb := by positivity
  have hLw_nn : (0 : ℝ) ≤ (2 : ℝ) ^ (-((P.natDegree : ℝ) * (L : ℝ))) :=
    (Real.rpow_pos_of_pos (by norm_num) _).le
  have hg₀_nn : (0 : ℝ) ≤ (2 : ℝ) ^ (-(cS * max (l₁ : ℝ) (l₂ : ℝ))) :=
    (Real.rpow_pos_of_pos (by norm_num) _).le
  have hU_nn : (0 : ℝ) ≤ 4 * lowMfun Λ := by
    have h := lowMfun_nonneg Λ; linarith
  have hC_RM_nn : (0 : ℝ) ≤ C_RM := hC_RM.le
  have hCexp_nn : (0 : ℝ) ≤ Cexp := hCexppos.le
  have hCw_nn : (0 : ℝ) ≤ Cw := hCwpos.le
  set lcW : ℝ := lcWeight (min cS 1 / 2) l₁ l₂ 0 L with hlcWdef
  have hlcWe : lcW = (2 : ℝ) ^ (-((min cS 1 / 2) * (L : ℝ))) := by
    rw [hlcWdef, lcWeight_zero_left_lt (c := min cS 1 / 2) hLt]
  have hlcWnn : (0 : ℝ) ≤ lcW := by rw [hlcWe]; positivity
  set A1r : ℝ := C_RM * ((Nat.log2 Kv : ℝ) + 2) ^ (2 : ℝ) with hA1rdef
  set A2r : ℝ := (Cssu : ℝ) * ((2 : ℝ) ^ (-(cS * max (l₁ : ℝ) (l₂ : ℝ)))) *
      ((C Λ : ℝ) * (C Λ : ℝ)) with hA2rdef
  set A3r : ℝ := (Cssu : ℝ) * ((2 : ℝ) ^ (-(cS * max (l₁ : ℝ) (l₂ : ℝ)))) *
      ((max 8 Cb) * (max 8 Cb)) with hA3rdef
  have hA1r_nn : (0 : ℝ) ≤ A1r := by rw [hA1rdef]; positivity
  have hA2r_nn : (0 : ℝ) ≤ A2r := by rw [hA2rdef]; positivity
  have hA3r_nn : (0 : ℝ) ≤ A3r := by rw [hA3rdef]; positivity
  have hA2e : ENNReal.ofReal (Cssu : ℝ) *
        ENNReal.ofReal ((2 : ℝ) ^ (-(cS * max (l₁ : ℝ) (l₂ : ℝ)))) *
        (ENNReal.ofReal (C Λ : ℝ) * ENNReal.ofReal (C Λ : ℝ))
      = ENNReal.ofReal A2r := by
    rw [hA2rdef]
    rw [show ((Cssu : ℝ) * (2 : ℝ) ^ (-(cS * max (l₁ : ℝ) (l₂ : ℝ))) *
            ((C Λ : ℝ) * (C Λ : ℝ)))
        = (Cssu : ℝ) * ((2 : ℝ) ^ (-(cS * max (l₁ : ℝ) (l₂ : ℝ))) *
            ((C Λ : ℝ) * (C Λ : ℝ))) by ring]
    rw [ENNReal.ofReal_mul hCssu_nn, ENNReal.ofReal_mul hg₀_nn, ENNReal.ofReal_mul hLam_nn]
    ring
  have hA3e : ENNReal.ofReal (Cssu : ℝ) *
        ENNReal.ofReal ((2 : ℝ) ^ (-(cS * max (l₁ : ℝ) (l₂ : ℝ)))) *
        (ENNReal.ofReal (max 8 Cb) * ENNReal.ofReal (max 8 Cb))
      = ENNReal.ofReal A3r := by
    rw [hA3rdef]
    rw [show ((Cssu : ℝ) * (2 : ℝ) ^ (-(cS * max (l₁ : ℝ) (l₂ : ℝ))) *
            ((max 8 Cb) * (max 8 Cb)))
        = (Cssu : ℝ) * ((2 : ℝ) ^ (-(cS * max (l₁ : ℝ) (l₂ : ℝ))) *
            ((max 8 Cb) * (max 8 Cb))) by ring]
    rw [ENNReal.ofReal_mul hCssu_nn, ENNReal.ofReal_mul hg₀_nn, ENNReal.ofReal_mul hKb_nn]
    ring
  have hFRZe : FRZ = ENNReal.ofReal A1r * ENNReal.ofReal A2r * F2 * G2 := by
    rw [hFRZdef, hA2e]
  have hSPKe : SPK = ENNReal.ofReal A3r * F2 * G2 := by
    rw [hSPKdef, hA3e]
  have hBbound : FRZ + 2 * SPK ≤ ENNReal.ofReal (A1r * A2r + (A3r + A3r)) * F2 * G2 := by
    have hX : ENNReal.ofReal (A1r * A2r + (A3r + A3r))
        = ENNReal.ofReal A1r * ENNReal.ofReal A2r
          + (ENNReal.ofReal A3r + ENNReal.ofReal A3r) := by
      rw [ENNReal.ofReal_add (mul_nonneg hA1r_nn hA2r_nn) (by linarith),
          ENNReal.ofReal_add hA3r_nn hA3r_nn, ENNReal.ofReal_mul hA1r_nn]
    have hY : FRZ + 2 * SPK
        = (ENNReal.ofReal A1r * ENNReal.ofReal A2r
            + (ENNReal.ofReal A3r + ENNReal.ofReal A3r)) * F2 * G2 := by
      rw [hFRZe, hSPKe, two_mul]
      ring
    rw [hY, hX]
  have hmerge : Ccoef * (4 * (Nw * (ENNReal.ofReal (A1r * A2r + (A3r + A3r)) * F2 * G2)))
      = ENNReal.ofReal ((2 : ℝ) ^ (-((P.natDegree : ℝ) * (L : ℝ))) * ιb * 4 * (2 * Cw + 1) *
          (A1r * A2r + (A3r + A3r))) * (F2 * G2) := by
    have h4of : (4 : ENNReal) = ENNReal.ofReal (4 : ℝ) := by
      rw [show (4 : ENNReal) = ((4 : ℕ) : ENNReal) from rfl, ← ENNReal.ofReal_natCast 4]
      norm_num
    rw [hCcoefdef, hNwdef, h4of]
    rw [show (2 : ℝ) ^ (-((P.natDegree : ℝ) * (L : ℝ))) * ιb * 4 * (2 * Cw + 1) *
          (A1r * A2r + (A3r + A3r))
        = (2 : ℝ) ^ (-((P.natDegree : ℝ) * (L : ℝ))) *
            (ιb * (4 * ((2 * Cw + 1) * (A1r * A2r + (A3r + A3r))))) by ring,
      ENNReal.ofReal_mul hLw_nn, ENNReal.ofReal_mul hιb0,
      ENNReal.ofReal_mul (by norm_num : (0 : ℝ) ≤ 4),
      ENNReal.ofReal_mul (by positivity)]
    ring
  have hlog2Kv : ((Nat.log2 Kv : ℝ) + 2) ^ (2 : ℝ)
      ≤ (4 * lowMfun Λ) * (2 : ℝ) ^ (4 * ρ * (L : ℝ)) := by
    have h3 : ((Nat.log2 Kv : ℝ) + 2)
        ≤ ((Nat.log2 (lowTrunc (2 * Real.log 2 / Real.log (Λ : ℝ) + 3) ρ (lcL l₁ l₂ 0 L) + 2) : ℝ)
          + 2) := by
      have h2 : (Nat.log2 Kv : ℕ)
          ≤ Nat.log2 (lowTrunc (2 * Real.log 2 / Real.log (Λ : ℝ) + 3) ρ (lcL l₁ l₂ 0 L) + 2) := by
        have hle : lowTrunc (2 * Real.log 2 / Real.log (Λ : ℝ) + 3) ρ (lcL l₁ l₂ 0 L) + 1
            ≤ lowTrunc (2 * Real.log 2 / Real.log (Λ : ℝ) + 3) ρ (lcL l₁ l₂ 0 L) + 2 := by omega
        have h2' : Nat.log 2 (lowTrunc (2 * Real.log 2 / Real.log (Λ : ℝ) + 3) ρ (lcL l₁ l₂ 0 L) + 1)
            ≤ Nat.log 2 (lowTrunc (2 * Real.log 2 / Real.log (Λ : ℝ) + 3) ρ (lcL l₁ l₂ 0 L) + 2) :=
          Nat.log_mono_right hle
        rw [hKvdef]
        simp only [Nat.log2_eq_log_two]
        exact h2'
      have h4 : (↑(Nat.log2 Kv) : ℝ)
          ≤ (↑(Nat.log2 (lowTrunc (2 * Real.log 2 / Real.log (Λ : ℝ) + 3) ρ (lcL l₁ l₂ 0 L) + 2)) : ℝ) := by
        exact_mod_cast h2
      linarith
    have h5 : ((Nat.log2 Kv : ℝ) + 2) ^ (2 : ℝ) = ((Nat.log2 Kv : ℝ) + 2) ^ 2 := by
      rw [show (2 : ℝ) = ((2 : ℕ) : ℝ) by norm_num, Real.rpow_natCast]
    rw [h5]
    refine le_trans (pow_le_pow_left₀ (by positivity) h3 2) ?_
    simpa only [hLc] using lowTruncLogBoundIndep ρ hρ Λ hΛ (lcL l₁ l₂ 0 L)
  have hcoef1 : (2 : ℝ) ^ (-((P.natDegree : ℝ) * (L : ℝ))) * A1r * A2r
      ≤ C_RM * (4 * lowMfun Λ) * (Cssu : ℝ) * ((C Λ : ℝ) * (C Λ : ℝ)) * Cexp * lcW := by
    rw [hA1rdef, hA2rdef]
    have h2 : (2 : ℝ) ^ (4 * ρ * (L : ℝ)) *
          ((2 : ℝ) ^ (-(cS * max (l₁ : ℝ) (l₂ : ℝ)))) * (2 : ℝ) ^ (-((P.natDegree : ℝ) * (L : ℝ)))
        = (2 : ℝ) ^ (-((P.natDegree : ℝ) * (L : ℝ))) * (2 : ℝ) ^ (4 * ρ * (L : ℝ)) *
            ((2 : ℝ) ^ (-(cS * max (l₁ : ℝ) (l₂ : ℝ)))) := by ring
    calc (2 : ℝ) ^ (-((P.natDegree : ℝ) * (L : ℝ))) *
            (C_RM * ((Nat.log2 Kv : ℝ) + 2) ^ (2 : ℝ)) *
            ((Cssu : ℝ) * ((2 : ℝ) ^ (-(cS * max (l₁ : ℝ) (l₂ : ℝ)))) * ((C Λ : ℝ) * (C Λ : ℝ)))
        ≤ (2 : ℝ) ^ (-((P.natDegree : ℝ) * (L : ℝ))) *
            (C_RM * ((4 * lowMfun Λ) * (2 : ℝ) ^ (4 * ρ * (L : ℝ)))) *
            ((Cssu : ℝ) * ((2 : ℝ) ^ (-(cS * max (l₁ : ℝ) (l₂ : ℝ)))) * ((C Λ : ℝ) * (C Λ : ℝ))) := by
          refine mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_left ?_ hLw_nn) (by positivity)
          exact mul_le_mul_of_nonneg_left hlog2Kv hC_RM_nn
      _ = C_RM * (4 * lowMfun Λ) * (Cssu : ℝ) * ((C Λ : ℝ) * (C Λ : ℝ)) *
            ((2 : ℝ) ^ (-((P.natDegree : ℝ) * (L : ℝ))) *
              (2 : ℝ) ^ (4 * ρ * (L : ℝ)) * ((2 : ℝ) ^ (-(cS * max (l₁ : ℝ) (l₂ : ℝ))))) := by ring
      _ ≤ C_RM * (4 * lowMfun Λ) * (Cssu : ℝ) * ((C Λ : ℝ) * (C Λ : ℝ)) * (Cexp * lcW) := by
          refine mul_le_mul_of_nonneg_left ?_ (by positivity)
          have hg := hCexp l₁ l₂ L hLt
          rw [h2, ← hlcWdef] at hg
          exact hg
      _ = C_RM * (4 * lowMfun Λ) * (Cssu : ℝ) * ((C Λ : ℝ) * (C Λ : ℝ)) * Cexp * lcW := by ring
  have hcoef2 : (2 : ℝ) ^ (-((P.natDegree : ℝ) * (L : ℝ))) * A3r
      ≤ (Cssu : ℝ) * ((max 8 Cb) * (max 8 Cb)) * lcW := by
    rw [hA3rdef]
    have hLwle : (2 : ℝ) ^ (-((P.natDegree : ℝ) * (L : ℝ))) ≤ lcW := by
      rw [hlcWe]
      refine Real.rpow_le_rpow_of_exponent_le (by norm_num) ?_
      have hLnn : (0 : ℝ) ≤ (L : ℝ) := Nat.cast_nonneg L
      have hmin : min cS 1 / 2 ≤ 1 / 2 := by
        have : min cS 1 ≤ 1 := min_le_right _ _; linarith
      have hd2 : (2 : ℝ) ≤ ((P.natDegree : ℕ) : ℝ) := by exact_mod_cast hd
      have hmm : min cS 1 / 2 ≤ ((P.natDegree : ℕ) : ℝ) := by linarith
      have hmul : (min cS 1 / 2) * (L : ℝ) ≤ ((P.natDegree : ℕ) : ℝ) * (L : ℝ) :=
        mul_le_mul_of_nonneg_right hmm hLnn
      linarith
    have hg1 : (2 : ℝ) ^ (-(cS * max (l₁ : ℝ) (l₂ : ℝ))) ≤ 1 :=
      Real.rpow_le_one_of_one_le_of_nonpos (by norm_num)
        (by nlinarith [hcS, (by positivity : (0 : ℝ) ≤ max (l₁ : ℝ) (l₂ : ℝ))])
    calc (2 : ℝ) ^ (-((P.natDegree : ℝ) * (L : ℝ))) *
            ((Cssu : ℝ) * ((2 : ℝ) ^ (-(cS * max (l₁ : ℝ) (l₂ : ℝ)))) * ((max 8 Cb) * (max 8 Cb)))
        = ((Cssu : ℝ) * ((max 8 Cb) * (max 8 Cb))) *
            ((2 : ℝ) ^ (-((P.natDegree : ℝ) * (L : ℝ))) *
              (2 : ℝ) ^ (-(cS * max (l₁ : ℝ) (l₂ : ℝ)))) := by ring
      _ ≤ ((Cssu : ℝ) * ((max 8 Cb) * (max 8 Cb))) * (lcW * 1) := by
          refine mul_le_mul_of_nonneg_left ?_ (by positivity)
          exact mul_le_mul hLwle hg1 (by positivity) hlcWnn
      _ = (Cssu : ℝ) * ((max 8 Cb) * (max 8 Cb)) * lcW := by ring
  have hsum2 : (2 : ℝ) ^ (-((P.natDegree : ℝ) * (L : ℝ))) * (A1r * A2r + (A3r + A3r))
      ≤ (C_RM * (4 * lowMfun Λ) * (Cssu : ℝ) * ((C Λ : ℝ) * (C Λ : ℝ)) * Cexp
          + 2 * ((Cssu : ℝ) * ((max 8 Cb) * (max 8 Cb)))) * lcW := by
    have hsplit : (2 : ℝ) ^ (-((P.natDegree : ℝ) * (L : ℝ))) * (A1r * A2r + (A3r + A3r))
        = (2 : ℝ) ^ (-((P.natDegree : ℝ) * (L : ℝ))) * A1r * A2r
          + 2 * ((2 : ℝ) ^ (-((P.natDegree : ℝ) * (L : ℝ))) * A3r) := by ring
    rw [hsplit, add_mul]
    refine add_le_add hcoef1 ?_
    calc 2 * ((2 : ℝ) ^ (-((P.natDegree : ℝ) * (L : ℝ))) * A3r)
        ≤ 2 * ((Cssu : ℝ) * ((max 8 Cb) * (max 8 Cb)) * lcW) :=
          mul_le_mul_of_nonneg_left hcoef2 (by norm_num)
      _ = (2 * ((Cssu : ℝ) * ((max 8 Cb) * (max 8 Cb)))) * lcW := by ring
  have hZreal : (2 : ℝ) ^ (-((P.natDegree : ℝ) * (L : ℝ))) * ιb * 4 * (2 * Cw + 1) *
        (A1r * A2r + (A3r + A3r))
      ≤ (ιb * 4 * (2 * Cw + 1) *
          (C_RM * (4 * lowMfun Λ) * (Cssu : ℝ) * ((C Λ : ℝ) * (C Λ : ℝ)) * Cexp
            + 2 * ((Cssu : ℝ) * ((max 8 Cb) * (max 8 Cb))))) * lcW := by
    calc (2 : ℝ) ^ (-((P.natDegree : ℝ) * (L : ℝ))) * ιb * 4 * (2 * Cw + 1) *
            (A1r * A2r + (A3r + A3r))
        = (ιb * 4 * (2 * Cw + 1)) *
            ((2 : ℝ) ^ (-((P.natDegree : ℝ) * (L : ℝ))) * (A1r * A2r + (A3r + A3r))) := by ring
      _ ≤ (ιb * 4 * (2 * Cw + 1)) *
            ((C_RM * (4 * lowMfun Λ) * (Cssu : ℝ) * ((C Λ : ℝ) * (C Λ : ℝ)) * Cexp
              + 2 * ((Cssu : ℝ) * ((max 8 Cb) * (max 8 Cb)))) * lcW) :=
          mul_le_mul_of_nonneg_left hsum2 (by positivity)
      _ = (ιb * 4 * (2 * Cw + 1) *
            (C_RM * (4 * lowMfun Λ) * (Cssu : ℝ) * ((C Λ : ℝ) * (C Λ : ℝ)) * Cexp
              + 2 * ((Cssu : ℝ) * ((max 8 Cb) * (max 8 Cb))))) * lcW := by ring
  have hKtot_nn : (0 : ℝ) ≤ ιb * 4 * (2 * Cw + 1) *
      (C_RM * (4 * lowMfun Λ) * (Cssu : ℝ) * ((C Λ : ℝ) * (C Λ : ℝ)) * Cexp
        + 2 * ((Cssu : ℝ) * ((max 8 Cb) * (max 8 Cb)))) := by
    have h1 : (0 : ℝ) ≤ lowMfun Λ := lowMfun_nonneg Λ
    have h2 : (0 : ℝ) ≤ (C Λ : ℝ) := by positivity
    have h3 : (0 : ℝ) ≤ C_RM * (4 * lowMfun Λ) * (Cssu : ℝ) *
        ((C Λ : ℝ) * (C Λ : ℝ)) * Cexp :=
      mul_nonneg (mul_nonneg (mul_nonneg (mul_nonneg hC_RM_nn (mul_nonneg (by norm_num) h1))
        hCssu_nn) (mul_nonneg h2 h2)) hCexp_nn
    have h4 : (0 : ℝ) ≤ 2 * ((Cssu : ℝ) * ((max 8 Cb) * (max 8 Cb))) :=
      mul_nonneg (by norm_num) (mul_nonneg hCssu_nn (mul_nonneg hKb_nn hKb_nn))
    have h5 := add_nonneg h3 h4
    exact mul_nonneg (mul_nonneg (mul_nonneg hιb0 (by norm_num)) (by positivity)) h5
  have hCcval : (Cc Λ : ENNReal) = ENNReal.ofReal (ιb * 4 * (2 * Cw + 1) *
      (C_RM * (4 * lowMfun Λ) * (Cssu : ℝ) * ((C Λ : ℝ) * (C Λ : ℝ)) * Cexp
        + 2 * ((Cssu : ℝ) * ((max 8 Cb) * (max 8 Cb))))) :=
    (ENNReal.ofReal_coe_nnreal (p := Cc Λ)).symm
  have hZenn : ENNReal.ofReal ((2 : ℝ) ^ (-((P.natDegree : ℝ) * (L : ℝ))) * ιb * 4 * (2 * Cw + 1) *
        (A1r * A2r + (A3r + A3r)))
      ≤ (Cc Λ : ENNReal) * ENNReal.ofReal lcW := by
    rw [hCcval, ← ENNReal.ofReal_mul hKtot_nn]
    exact ENNReal.ofReal_le_ofReal hZreal
  refine hmain.trans ?_
  have hmid : Ccoef * (4 * (Nw * (FRZ + 2 * SPK)))
      ≤ Ccoef * (4 * (Nw * (ENNReal.ofReal (A1r * A2r + (A3r + A3r)) * F2 * G2))) :=
    mul_le_mul_of_nonneg_left
      (mul_le_mul_of_nonneg_left (mul_le_mul_of_nonneg_left hBbound bot_le) bot_le) bot_le
  refine hmid.trans ?_
  rw [hmerge]
  refine (mul_le_mul_of_nonneg_right hZenn (by positivity)).trans (le_of_eq ?_)
  ring

end

end Work.KMTPlan.A6.Linf
