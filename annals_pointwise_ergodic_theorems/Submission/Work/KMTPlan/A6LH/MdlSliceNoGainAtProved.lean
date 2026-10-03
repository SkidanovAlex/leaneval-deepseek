import Mathlib
import Submission.Work.KMTPlan.A6Clean.MdlSliceNoGainAt
import Submission.Work.KMTPlan.A6.MdlFibreIdent
import Submission.Work.KMTPlan.A6.MdlSliceLinG
import Submission.Work.KMTPlan.A6.TleMemLp
import Submission.Work.KMTPlan.A6.slicesTwoLe
import Submission.Work.KMTPlan.A6.MdlAdelicPackets
import Submission.Port.Aesm

set_option maxHeartbeats 4000000

namespace Work.KMTPlan.A6LH

open MeasureTheory Polynomial Finset
open scoped ENNReal NNReal BigOperators
open PointwiseErgodicTheorems Submission.PointwiseErgodicTheorems

noncomputable section

/-! ## Square summability of the two packet families

(Local copies of the two lemmas of the same content in
`Submission/Work/KMTPlan/A6Clean/mdlSliceNoGainMain.lean`, kept here so that this file does not
depend on the sibling lane's files.) -/

/-- The `f`-side packet family is square summable. -/
theorem memℓp_mdlSliceF_loc (ρ : ℝ) (hρ : 0 < ρ) (C₀ : ℕ) (a : ℕ → NNReal)
    (l₁ l₂ k₁ k₂ : ℕ) (j₁ : ℤ) (t : ℝ) (f : ℤ → ℂ) (ha1 : ∀ n : ℕ, 1 ≤ a n)
    (hj₁ : j₁ ∈ ({-1, 0, 1} : Finset ℤ)) (hk₁ : k₁ = 0 → j₁ ≠ -1)
    (hf : MeasureTheory.MemLp f 2 MeasureTheory.Measure.count) :
    ∀ n : ℕ, Memℓp (Work.KMTPlan.A6.mdlSliceF ρ C₀ a l₁ l₂ k₁ k₂ j₁ t f n) 2 := by
  intro n
  by_cases hc : Work.KMTPlan.A6.mdlCore ρ C₀ a l₁ l₂ k₁ k₂ n
  · have hmain := ((Work.KMTPlan.A6.mdlCore_iff ρ C₀ a l₁ l₂ k₁ k₂ n).mp hc).2.2
    obtain ⟨hlog₁, -⟩ := Work.KMTPlan.A6.le_logN_of_mainRegime hρ.le hmain
    have hN1 : 1 ≤ Nat.floor (a n) := (Nat.one_le_floor_iff (a n)).mpr (ha1 n)
    simp only [Work.KMTPlan.A6.mdlSliceF, hc, if_true]
    refine Work.KMTPlan.A6.TleMemLp ρ l₁ (Work.KMTPlan.A6.varphiNtj (Nat.floor (a n)) k₁ j₁ t) 24
      (by norm_num) (Work.KMTPlan.A6.periodize_varphiNtj_le (Nat.floor (a n)) k₁ j₁ t hj₁
        (Work.KMTPlan.A6.ne_zero_or_nonneg_ssu hj₁ hk₁) hN1 hlog₁) _
      (Work.KMTPlan.A6.memℓp_mdlF ρ _ l₁
        (Work.KMTPlan.A6.memlpOfMemLpCount (p := 2) (by norm_num) (by norm_num) hf))
  · simp only [Work.KMTPlan.A6.mdlSliceF, hc, if_false]
    simp [Memℓp]

/-- The `g`-side packet family is square summable. -/
theorem memℓp_mdlSliceG_loc (ρ : ℝ) (hρ : 0 < ρ) (P : Polynomial ℤ) (hd : 2 ≤ P.natDegree)
    (C₀ : ℕ) (a : ℕ → NNReal) (l₁ l₂ k₁ k₂ : ℕ) (j₂ : ℤ) (t : ℝ) (g : ℤ → ℂ)
    (ha1 : ∀ n : ℕ, 1 ≤ a n) (hj₂ : j₂ ∈ ({-1, 0, 1} : Finset ℤ)) (hk₂ : k₂ = 0 → j₂ ≠ -1)
    (hg : MeasureTheory.MemLp g 2 MeasureTheory.Measure.count) :
    ∀ n : ℕ, Memℓp (Work.KMTPlan.A6.mdlSliceG ρ P C₀ a l₁ l₂ k₁ k₂ j₂ t g n) 2 := by
  intro n
  obtain ⟨⟨Cb, hCb0, hCb⟩, -⟩ := Work.KMTPlan.A6.varphitildeNtjPointwise P hd
  by_cases hc : Work.KMTPlan.A6.mdlCore ρ C₀ a l₁ l₂ k₁ k₂ n
  · have hmain := ((Work.KMTPlan.A6.mdlCore_iff ρ C₀ a l₁ l₂ k₁ k₂ n).mp hc).2.2
    obtain ⟨-, hlog₂⟩ := Work.KMTPlan.A6.le_logN_of_mainRegime hρ.le hmain
    have hN1 : 1 ≤ Nat.floor (a n) := (Nat.one_le_floor_iff (a n)).mpr (ha1 n)
    have hkj : ¬ (k₂ = 0 ∧ j₂ = -1) := fun h => hk₂ h.1 h.2
    simp only [Work.KMTPlan.A6.mdlSliceG, hc, if_true]
    refine Work.KMTPlan.A6.TleMemLp ρ l₂
      (Work.KMTPlan.A6.varphitildeNtj P (Nat.floor (a n)) k₂ j₂ t)
      (3 * Cb) (by positivity)
      (Work.KMTPlan.A6.periodize_varphitildeNtj_le P hd hCb (Nat.floor (a n)) k₂ j₂ t hj₂ hkj hN1
        hlog₂) _ (Work.KMTPlan.A6.memℓp_mdlG ρ P _ l₂
          (Work.KMTPlan.A6.memlpOfMemLpCount (p := 2) (by norm_num) (by norm_num) hg))
  · simp only [Work.KMTPlan.A6.mdlSliceG, hc, if_false]
    simp [Memℓp]

/-! ## The two cumulative-fibre bounds

These are the `f`/`g` consumers of the two *proved* vanishing lemmas
`Work.KMTPlan.A6Clean.fiberOpSet_mdlSliceF_eq_fiberOp_of_largeRho` /
`…fiberOpPSet_mdlSliceG_eq_fiberOpP_of_largeRho` of `Submission/Work/KMTPlan/A6/MdlFibreIdent.lean`
(their threshold `B` is allowed to depend on `ρ`, which is exactly the freedom the final statement
of `MdlSliceNoGainAt` grants). -/

/-- **The `f`-side cumulative-fibre residue bound, with the loss weight** (ρ-dependent vanishing
input). -/
theorem fiberFAt (r : NNReal) (hr : 2 < r)
    (hVan : ∀ (ρ : ℝ), 0 < ρ → ρ ≤ 1 → ∃ B : ℕ, ∀ (C₀ : ℕ) (a : ℕ → NNReal)
      (l₁ l₂ k₁ k₂ : ℕ) (j₁ : ℤ) (t : ℝ) (f : ℤ → ℂ),
      B ≤ Work.KMTPlan.A6.lcL l₁ l₂ k₁ k₂ → 1 ≤ l₁ →
      (∀ n : ℕ, 1 ≤ a n) → j₁ ∈ ({-1, 0, 1} : Finset ℤ) → (k₁ = 0 → j₁ ≠ -1) →
      MeasureTheory.MemLp f 2 MeasureTheory.Measure.count →
      t ∈ Set.Icc (1 / 2 : ℝ) 1 →
      ∀ (n : ℕ), Work.KMTPlan.A6.mdlCore ρ C₀ a l₁ l₂ k₁ k₂ n → ∀ (n₀ : ℤ) (x : ℤ),
        Work.KMTAreas.A7.fiberOpSet (Work.Analysis.IonescuWainger.iwArithFreqs ρ l₁)
            (Work.KMTAreas.A7.mStarF (Work.KMTAreas.A7.uScale ρ
              (Work.KMTPlan.A6.lcL l₁ l₂ k₁ k₂)))
            n₀ (Work.KMTPlan.A6.mdlSliceF ρ C₀ a l₁ l₂ k₁ k₂ j₁ t f n) x
          = Work.KMTAreas.A7.fiberOp ρ l₁
            (Work.KMTAreas.A7.mStarF (Work.KMTAreas.A7.uScale ρ
              (Work.KMTPlan.A6.lcL l₁ l₂ k₁ k₂)))
            n₀ (Work.KMTPlan.A6.mdlSliceF ρ C₀ a l₁ l₂ k₁ k₂ j₁ t f n) x) :
    ∃ cD : ℝ, 0 ≤ cD ∧ ∃ ρ₀ : ℝ, 0 < ρ₀ ∧
      ∀ ρ : ℝ, 0 < ρ → ρ ≤ ρ₀ → ∃ CU : ℝ, 0 < CU ∧
        ∀ (C₀ : ℕ) (a : ℕ → NNReal) (Λ : NNReal) (l₁ l₂ k₁ k₂ : ℕ) (j₁ : ℤ) (t : ℝ)
          (f : ℤ → ℂ),
          1 < Λ → PointwiseErgodicTheorems.Lacunary Λ a → (∀ n : ℕ, 1 ≤ a n) →
          t ∈ Set.Icc (1 / 2 : ℝ) 1 → j₁ ∈ ({-1, 0, 1} : Finset ℤ) → (k₁ = 0 → j₁ ≠ -1) →
          MeasureTheory.MemLp f 2 MeasureTheory.Measure.count →
          MeasureTheory.eLpNorm (fun x : ℤ => Work.KMTAreas.A7.residueLp 2
              (Work.KMTAreas.A7.arithQ ρ (max l₁ l₂))
              (fun y n₀ => PointwiseErgodicTheorems.variationalNorm r (fun n : ℕ =>
                Work.KMTAreas.A7.fiberOpSet (Work.Analysis.IonescuWainger.iwArithFreqs ρ l₁)
                  (Work.KMTAreas.A7.mStarF (Work.KMTAreas.A7.uScale ρ
                    (Work.KMTPlan.A6.lcL l₁ l₂ k₁ k₂)))
                  n₀ (Work.KMTPlan.A6.mdlSliceF ρ C₀ a l₁ l₂ k₁ k₂ j₁ t f n) y)) x)
            2 MeasureTheory.Measure.count
          ≤ ENNReal.ofReal (CU * Work.KMTAreas.A7.lossWeight cD ρ l₁ l₂ k₁ k₂)
            * MeasureTheory.eLpNorm (fun x : ℤ => PointwiseErgodicTheorems.variationalNorm r
                (fun n : ℕ => Work.KMTPlan.A6.mdlSliceF ρ C₀ a l₁ l₂ k₁ k₂ j₁ t f n x))
              2 MeasureTheory.Measure.count := by
  obtain ⟨As, hAs0, ρs, hρs0, hsamp⟩ := Work.KMTPlan.A6Clean.mdlSliceF_fiberVarSampling r hr
  obtain ⟨Cconv, hCconv0, hCconv⟩ :=
    Work.KMTPlan.A6Clean.eLpNorm_residueLp_fiberOpSet_le r (le_trans (by norm_num) (le_of_lt hr))
  obtain ⟨Cw, hCw0, hCw⟩ := Work.KMTPlan.A6.cw_etaCut_tsum_le_uniform_ssu
  refine ⟨max As 0, le_max_right _ _, min ρs 1, lt_min hρs0 zero_lt_one, ?_⟩
  intro ρ hρ hρle
  have hρs : ρ ≤ ρs := le_trans hρle (min_le_left _ _)
  have hρ1 : ρ ≤ 1 := le_trans hρle (min_le_right _ _)
  obtain ⟨Bv, hVanρ⟩ := hVan ρ hρ hρ1
  obtain ⟨CF, hCF0, hCsamp⟩ := hsamp 2 (by norm_num) (by norm_num) ρ hρ hρs
  refine ⟨max (Cconv * ((Work.Analysis.IonescuWainger.iwArithFreqs ρ (Bv + 1)).card : ℝ) * Cw
      + 1) CF, lt_max_of_lt_left (by positivity), ?_⟩
  intro C₀ a Λ l₁ l₂ k₁ k₂ j₁ t f hΛ ha ha1 ht hj₁ hk₁ hf
  set U : ℕ := Work.KMTAreas.A7.uScale ρ (Work.KMTPlan.A6.lcL l₁ l₂ k₁ k₂) with hUdef
  set q : ℕ := Work.KMTAreas.A7.arithQ ρ (max l₁ l₂) with hqdef
  set Bc : ℕ := Bv + 1 with hBcdef
  by_cases hcase : l₁ = 0 ∨ Work.KMTPlan.A6.lcL l₁ l₂ k₁ k₂ ≤ Bc - 1
  · -- the crude regime
    have hLl₁ : l₁ ≤ Bc := by
      rcases hcase with h | h
      · omega
      · have h2 : l₁ ≤ Work.KMTPlan.A6.lcL l₁ l₂ k₁ k₂ := by
          rw [Work.KMTPlan.A6.lcL]; omega
        omega
    have hmsum : Summable (fun j : ℤ => ‖Work.KMTAreas.A7.cw (Work.KMTAreas.A7.mStarF U) j‖) :=
      Work.KMTAreas.A7.summable_cw_mStarF U
    have hb := hCconv (Work.Analysis.IonescuWainger.iwArithFreqs ρ l₁)
      (Work.KMTAreas.A7.mStarF U) q hmsum
      (Work.KMTPlan.A6.mdlSliceF ρ C₀ a l₁ l₂ k₁ k₂ j₁ t f)
    have hcard : ((Work.Analysis.IonescuWainger.iwArithFreqs ρ l₁).card : ℝ)
        ≤ ((Work.Analysis.IonescuWainger.iwArithFreqs ρ Bc).card : ℝ) := by
      exact_mod_cast Finset.card_le_card
        (Work.Analysis.IonescuWainger.iwArithFreqs_mono hρ hρ1 hLl₁)
    have hcw : (∑' j : ℤ, ‖Work.KMTAreas.A7.cw (Work.KMTAreas.A7.mStarF U) j‖) ≤ Cw := by
      have hc : -(2 * (U : ℤ)) ≤ 0 := by
        have h0 : (0 : ℤ) ≤ (U : ℤ) := Int.natCast_nonneg U
        omega
      simpa only [Work.KMTAreas.A7.mStarF] using hCw (-(2 * (U : ℤ))) hc
    have hlw1 : (1 : ℝ) ≤ Work.KMTAreas.A7.lossWeight (max As 0) ρ l₁ l₂ k₁ k₂ :=
      Work.KMTPlan.A6Clean.one_le_lossWeightc _ ρ (le_max_right _ _) hρ.le l₁ l₂ k₁ k₂
    have hconst : Cconv * ((Work.Analysis.IonescuWainger.iwArithFreqs ρ l₁).card : ℝ)
          * (∑' j : ℤ, ‖Work.KMTAreas.A7.cw (Work.KMTAreas.A7.mStarF U) j‖)
        ≤ (max (Cconv * ((Work.Analysis.IonescuWainger.iwArithFreqs ρ Bc).card : ℝ) * Cw + 1) CF)
          * Work.KMTAreas.A7.lossWeight (max As 0) ρ l₁ l₂ k₁ k₂ := by
      have h1 : Cconv * ((Work.Analysis.IonescuWainger.iwArithFreqs ρ l₁).card : ℝ)
            * (∑' j : ℤ, ‖Work.KMTAreas.A7.cw (Work.KMTAreas.A7.mStarF U) j‖)
          ≤ Cconv * ((Work.Analysis.IonescuWainger.iwArithFreqs ρ Bc).card : ℝ) * Cw :=
        mul_le_mul (mul_le_mul_of_nonneg_left hcard hCconv0.le) hcw
          (tsum_nonneg fun j => norm_nonneg _) (by positivity)
      have h2 : Cconv * ((Work.Analysis.IonescuWainger.iwArithFreqs ρ Bc).card : ℝ) * Cw + 1
          ≤ max (Cconv * ((Work.Analysis.IonescuWainger.iwArithFreqs ρ Bc).card : ℝ) * Cw + 1)
            CF :=
        le_max_left _ _
      calc Cconv * ((Work.Analysis.IonescuWainger.iwArithFreqs ρ l₁).card : ℝ)
            * (∑' j : ℤ, ‖Work.KMTAreas.A7.cw (Work.KMTAreas.A7.mStarF U) j‖)
          ≤ Cconv * ((Work.Analysis.IonescuWainger.iwArithFreqs ρ Bc).card : ℝ) * Cw + 1 := by
            linarith [h1]
        _ ≤ (max (Cconv * ((Work.Analysis.IonescuWainger.iwArithFreqs ρ Bc).card : ℝ) * Cw + 1)
              CF) * Work.KMTAreas.A7.lossWeight (max As 0) ρ l₁ l₂ k₁ k₂ :=
            le_trans h2 (le_mul_of_one_le_right (by positivity) hlw1)
    refine hb.trans ?_
    exact mul_le_mul_left (ENNReal.ofReal_le_ofReal hconst) _
  · -- the deep regime
    push_neg at hcase
    obtain ⟨hl₁ne, hBclt⟩ := hcase
    have hl₁1 : 1 ≤ l₁ := Nat.one_le_iff_ne_zero.mpr hl₁ne
    have hBle : Bc ≤ Work.KMTPlan.A6.lcL l₁ l₂ k₁ k₂ := by omega
    have hBv : Bv ≤ Work.KMTPlan.A6.lcL l₁ l₂ k₁ k₂ := le_trans (by omega) hBle
    have hfun : (fun x : ℤ => Work.KMTAreas.A7.residueLp 2 q
          (fun y n₀ => PointwiseErgodicTheorems.variationalNorm r (fun n : ℕ =>
            Work.KMTAreas.A7.fiberOpSet (Work.Analysis.IonescuWainger.iwArithFreqs ρ l₁)
              (Work.KMTAreas.A7.mStarF U) n₀
              (Work.KMTPlan.A6.mdlSliceF ρ C₀ a l₁ l₂ k₁ k₂ j₁ t f n) y)) x)
        = (fun x : ℤ => Work.KMTAreas.A7.residueLp 2 q
          (fun y n₀ => PointwiseErgodicTheorems.variationalNorm r (fun n : ℕ =>
            Work.KMTAreas.A7.fiberOp ρ l₁ (Work.KMTAreas.A7.mStarF U) n₀
              (Work.KMTPlan.A6.mdlSliceF ρ C₀ a l₁ l₂ k₁ k₂ j₁ t f n) y)) x) := by
      refine congrArg (fun F : ℤ → ℕ → ENNReal =>
        fun x : ℤ => Work.KMTAreas.A7.residueLp 2 q F x) ?_
      funext y n₀
      refine congrArg (fun F : ℕ → ℂ => PointwiseErgodicTheorems.variationalNorm r F) ?_
      funext n
      by_cases hc : Work.KMTPlan.A6.mdlCore ρ C₀ a l₁ l₂ k₁ k₂ n
      · exact hVanρ C₀ a l₁ l₂ k₁ k₂ j₁ t f hBv hl₁1 ha1 hj₁ hk₁ hf ht n hc n₀ y
      · have h0 : Work.KMTPlan.A6.mdlSliceF ρ C₀ a l₁ l₂ k₁ k₂ j₁ t f n = 0 := by
          funext x
          simp only [Work.KMTPlan.A6.mdlSliceF, hc, if_false]
        rw [h0, Work.KMTPlan.A6Clean.fiberOpSet_zero_right, Work.KMTPlan.A6Clean.fiberOp_zero_right]
    rw [hfun]
    have hgoal := hCsamp C₀ a Λ hΛ ha ha1 l₁ l₂ k₁ k₂ t j₁ hj₁ hk₁ f hf ht
    rw [show (2 : ENNReal).toReal = 2 from by norm_num] at hgoal
    rw [hqdef, hUdef]
    refine hgoal.trans ?_
    refine mul_le_mul_left (ENNReal.ofReal_le_ofReal ?_) _
    exact mul_le_mul (le_max_right _ _)
      (Work.KMTPlan.A6Clean.lossWeight_mono As (max As 0) ρ (le_max_left _ _) hρ.le hAs0 l₁ l₂ k₁ k₂)
      (Work.KMTPlan.A6Clean.lossWeight_nonnegc _ _ l₁ l₂ k₁ k₂) (by positivity)

/-- **The `g`-side cumulative-fibre residue bound, with the loss weight** (ρ-dependent vanishing
input). -/
theorem fiberGAt (P : Polynomial ℤ) (hd : 2 ≤ P.natDegree) (r : NNReal) (hr : 2 < r)
    (hVan : ∀ (ρ : ℝ), 0 < ρ → ρ ≤ 1 → ∃ B : ℕ, ∀ (P : Polynomial ℤ) (hd : 2 ≤ P.natDegree)
      (C₀ : ℕ) (a : ℕ → NNReal) (l₁ l₂ k₁ k₂ : ℕ) (j₂ : ℤ) (t : ℝ) (g : ℤ → ℂ),
      B ≤ Work.KMTPlan.A6.lcL l₁ l₂ k₁ k₂ → 1 ≤ l₂ →
      (∀ n : ℕ, 1 ≤ a n) → j₂ ∈ ({-1, 0, 1} : Finset ℤ) → (k₂ = 0 → j₂ ≠ -1) →
      MeasureTheory.MemLp g 2 MeasureTheory.Measure.count →
      t ∈ Set.Icc (1 / 2 : ℝ) 1 →
      ∀ (n : ℕ), Work.KMTPlan.A6.mdlCore ρ C₀ a l₁ l₂ k₁ k₂ n → ∀ (n₀ : ℤ) (x : ℤ),
        Work.KMTAreas.A7.fiberOpPSet P (Work.Analysis.IonescuWainger.iwArithFreqs ρ l₂)
            (Work.KMTAreas.A7.mStargF P.natDegree (Work.KMTAreas.A7.uScale ρ
              (Work.KMTPlan.A6.lcL l₁ l₂ k₁ k₂)))
            n₀ (Work.KMTPlan.A6.mdlSliceG ρ P C₀ a l₁ l₂ k₁ k₂ j₂ t g n) x
          = Work.KMTAreas.A7.fiberOpP ρ P l₂
            (Work.KMTAreas.A7.mStargF P.natDegree (Work.KMTAreas.A7.uScale ρ
              (Work.KMTPlan.A6.lcL l₁ l₂ k₁ k₂)))
            n₀ (Work.KMTPlan.A6.mdlSliceG ρ P C₀ a l₁ l₂ k₁ k₂ j₂ t g n) x) :
    ∃ cD : ℝ, 0 ≤ cD ∧ ∃ ρ₀ : ℝ, 0 < ρ₀ ∧
      ∀ ρ : ℝ, 0 < ρ → ρ ≤ ρ₀ → ∃ CU : ℝ, 0 < CU ∧
        ∀ (C₀ : ℕ) (a : ℕ → NNReal) (Λ : NNReal) (l₁ l₂ k₁ k₂ : ℕ) (j₂ : ℤ) (t : ℝ)
          (g : ℤ → ℂ),
          1 < Λ → PointwiseErgodicTheorems.Lacunary Λ a → (∀ n : ℕ, 1 ≤ a n) →
          t ∈ Set.Icc (1 / 2 : ℝ) 1 → j₂ ∈ ({-1, 0, 1} : Finset ℤ) → (k₂ = 0 → j₂ ≠ -1) →
          MeasureTheory.MemLp g 2 MeasureTheory.Measure.count →
          MeasureTheory.eLpNorm (fun x : ℤ => Work.KMTAreas.A7.residueLp 2
              (Work.KMTAreas.A7.arithQ ρ (max l₁ l₂))
              (fun y n₀ => PointwiseErgodicTheorems.variationalNorm r (fun n : ℕ =>
                Work.KMTAreas.A7.fiberOpPSet P (Work.Analysis.IonescuWainger.iwArithFreqs ρ l₂)
                  (Work.KMTAreas.A7.mStargF P.natDegree (Work.KMTAreas.A7.uScale ρ
                    (Work.KMTPlan.A6.lcL l₁ l₂ k₁ k₂)))
                  n₀ (Work.KMTPlan.A6.mdlSliceG ρ P C₀ a l₁ l₂ k₁ k₂ j₂ t g n) y)) x)
            2 MeasureTheory.Measure.count
          ≤ ENNReal.ofReal (CU * Work.KMTAreas.A7.lossWeight cD ρ l₁ l₂ k₁ k₂)
            * MeasureTheory.eLpNorm (fun x : ℤ => PointwiseErgodicTheorems.variationalNorm r
                (fun n : ℕ => Work.KMTPlan.A6.mdlSliceG ρ P C₀ a l₁ l₂ k₁ k₂ j₂ t g n x))
              2 MeasureTheory.Measure.count := by
  obtain ⟨As, hAs0, ρs, hρs0, hsamp⟩ := Work.KMTPlan.A6Clean.mdlSliceG_fiberVarSampling P hd r hr
  obtain ⟨Cconv, hCconv0, hCconv⟩ :=
    Work.KMTPlan.A6Clean.eLpNorm_residueLp_fiberOpPSet_le r (le_trans (by norm_num) (le_of_lt hr))
  obtain ⟨Cw, hCw0, hCw⟩ := Work.KMTPlan.A6.cw_etaCut_tsum_le_uniform_ssu
  refine ⟨max As 0, le_max_right _ _, min ρs 1, lt_min hρs0 zero_lt_one, ?_⟩
  intro ρ hρ hρle
  have hρs : ρ ≤ ρs := le_trans hρle (min_le_left _ _)
  have hρ1 : ρ ≤ 1 := le_trans hρle (min_le_right _ _)
  obtain ⟨Bv, hVanρ⟩ := hVan ρ hρ hρ1
  obtain ⟨CF, hCF0, hCsamp⟩ := hsamp 2 (by norm_num) (by norm_num) ρ hρ hρs
  refine ⟨max (Cconv * ((Work.Analysis.IonescuWainger.iwArithFreqs ρ (Bv + 1)).card : ℝ) * Cw
      + 1) CF, lt_max_of_lt_left (by positivity), ?_⟩
  intro C₀ a Λ l₁ l₂ k₁ k₂ j₂ t g hΛ ha ha1 ht hj₂ hk₂ hg
  set U : ℕ := Work.KMTAreas.A7.uScale ρ (Work.KMTPlan.A6.lcL l₁ l₂ k₁ k₂) with hUdef
  set q : ℕ := Work.KMTAreas.A7.arithQ ρ (max l₁ l₂) with hqdef
  set Bc : ℕ := Bv + 1 with hBcdef
  by_cases hcase : l₂ = 0 ∨ Work.KMTPlan.A6.lcL l₁ l₂ k₁ k₂ ≤ Bc - 1
  · -- the crude regime
    have hLl₂ : l₂ ≤ Bc := by
      rcases hcase with h | h
      · omega
      · have h2 : l₂ ≤ Work.KMTPlan.A6.lcL l₁ l₂ k₁ k₂ := by
          rw [Work.KMTPlan.A6.lcL]; omega
        omega
    have hmsum : Summable (fun j : ℤ =>
        ‖Work.KMTAreas.A7.cw (Work.KMTAreas.A7.mStargF P.natDegree U) j‖) :=
      Work.KMTAreas.A7.summable_cw_mStargF P.natDegree U
    have hb := hCconv P (Work.Analysis.IonescuWainger.iwArithFreqs ρ l₂)
      (Work.KMTAreas.A7.mStargF P.natDegree U) q hmsum
      (Work.KMTPlan.A6.mdlSliceG ρ P C₀ a l₁ l₂ k₁ k₂ j₂ t g)
    have hcard : ((Work.Analysis.IonescuWainger.iwArithFreqs ρ l₂).card : ℝ)
        ≤ ((Work.Analysis.IonescuWainger.iwArithFreqs ρ Bc).card : ℝ) := by
      exact_mod_cast Finset.card_le_card
        (Work.Analysis.IonescuWainger.iwArithFreqs_mono hρ hρ1 hLl₂)
    have hcw : (∑' j : ℤ, ‖Work.KMTAreas.A7.cw (Work.KMTAreas.A7.mStargF P.natDegree U) j‖)
        ≤ Cw := by
      have hc : -((P.natDegree : ℤ) * 2 * (U : ℤ)) ≤ 0 := by
        have h0 : (0 : ℤ) ≤ (U : ℤ) := Int.natCast_nonneg U
        have h1 : (0 : ℤ) ≤ (P.natDegree : ℤ) := Int.natCast_nonneg _
        nlinarith
      simpa only [Work.KMTAreas.A7.mStargF] using hCw (-((P.natDegree : ℤ) * 2 * (U : ℤ))) hc
    have hlw1 : (1 : ℝ) ≤ Work.KMTAreas.A7.lossWeight (max As 0) ρ l₁ l₂ k₁ k₂ :=
      Work.KMTPlan.A6Clean.one_le_lossWeightc _ ρ (le_max_right _ _) hρ.le l₁ l₂ k₁ k₂
    have hconst : Cconv * ((Work.Analysis.IonescuWainger.iwArithFreqs ρ l₂).card : ℝ)
          * (∑' j : ℤ, ‖Work.KMTAreas.A7.cw (Work.KMTAreas.A7.mStargF P.natDegree U) j‖)
        ≤ (max (Cconv * ((Work.Analysis.IonescuWainger.iwArithFreqs ρ Bc).card : ℝ) * Cw + 1) CF)
          * Work.KMTAreas.A7.lossWeight (max As 0) ρ l₁ l₂ k₁ k₂ := by
      have h1 : Cconv * ((Work.Analysis.IonescuWainger.iwArithFreqs ρ l₂).card : ℝ)
            * (∑' j : ℤ, ‖Work.KMTAreas.A7.cw (Work.KMTAreas.A7.mStargF P.natDegree U) j‖)
          ≤ Cconv * ((Work.Analysis.IonescuWainger.iwArithFreqs ρ Bc).card : ℝ) * Cw :=
        mul_le_mul (mul_le_mul_of_nonneg_left hcard hCconv0.le) hcw
          (tsum_nonneg fun j => norm_nonneg _) (by positivity)
      have h2 : Cconv * ((Work.Analysis.IonescuWainger.iwArithFreqs ρ Bc).card : ℝ) * Cw + 1
          ≤ max (Cconv * ((Work.Analysis.IonescuWainger.iwArithFreqs ρ Bc).card : ℝ) * Cw + 1)
            CF :=
        le_max_left _ _
      calc Cconv * ((Work.Analysis.IonescuWainger.iwArithFreqs ρ l₂).card : ℝ)
            * (∑' j : ℤ, ‖Work.KMTAreas.A7.cw (Work.KMTAreas.A7.mStargF P.natDegree U) j‖)
          ≤ Cconv * ((Work.Analysis.IonescuWainger.iwArithFreqs ρ Bc).card : ℝ) * Cw + 1 := by
            linarith [h1]
        _ ≤ (max (Cconv * ((Work.Analysis.IonescuWainger.iwArithFreqs ρ Bc).card : ℝ) * Cw + 1)
              CF) * Work.KMTAreas.A7.lossWeight (max As 0) ρ l₁ l₂ k₁ k₂ :=
            le_trans h2 (le_mul_of_one_le_right (by positivity) hlw1)
    refine hb.trans ?_
    exact mul_le_mul_left (ENNReal.ofReal_le_ofReal hconst) _
  · -- the deep regime
    push_neg at hcase
    obtain ⟨hl₂ne, hBclt⟩ := hcase
    have hl₂1 : 1 ≤ l₂ := Nat.one_le_iff_ne_zero.mpr hl₂ne
    have hBle : Bc ≤ Work.KMTPlan.A6.lcL l₁ l₂ k₁ k₂ := by omega
    have hBv : Bv ≤ Work.KMTPlan.A6.lcL l₁ l₂ k₁ k₂ := le_trans (by omega) hBle
    have hW : (fun (y : ℤ) (n₀ : ℕ) => PointwiseErgodicTheorems.variationalNorm r (fun n : ℕ =>
          Work.KMTAreas.A7.fiberOpPSet P (Work.Analysis.IonescuWainger.iwArithFreqs ρ l₂)
            (Work.KMTAreas.A7.mStargF P.natDegree U) n₀
            (Work.KMTPlan.A6.mdlSliceG ρ P C₀ a l₁ l₂ k₁ k₂ j₂ t g n) y))
        = (fun (y : ℤ) (n₀ : ℕ) => PointwiseErgodicTheorems.variationalNorm r (fun n : ℕ =>
          Work.KMTAreas.A7.fiberOpP ρ P l₂ (Work.KMTAreas.A7.mStargF P.natDegree U) n₀
            (Work.KMTPlan.A6.mdlSliceG ρ P C₀ a l₁ l₂ k₁ k₂ j₂ t g n) y)) := by
      funext y n₀
      refine congrArg (fun F : ℕ → ℂ => PointwiseErgodicTheorems.variationalNorm r F) ?_
      funext n
      by_cases hc : Work.KMTPlan.A6.mdlCore ρ C₀ a l₁ l₂ k₁ k₂ n
      · exact hVanρ P hd C₀ a l₁ l₂ k₁ k₂ j₂ t g hBv hl₂1 ha1 hj₂ hk₂ hg ht n hc n₀ y
      · have h0 : Work.KMTPlan.A6.mdlSliceG ρ P C₀ a l₁ l₂ k₁ k₂ j₂ t g n = 0 := by
          funext x
          simp only [Work.KMTPlan.A6.mdlSliceG, hc, if_false]
        rw [h0, Work.KMTPlan.A6Clean.fiberOpPSet_zero_right, Work.KMTPlan.A6Clean.fiberOpP_zero_right]
    have hfun : (fun x : ℤ => Work.KMTAreas.A7.residueLp 2 q
          (fun y n₀ => PointwiseErgodicTheorems.variationalNorm r (fun n : ℕ =>
            Work.KMTAreas.A7.fiberOpPSet P (Work.Analysis.IonescuWainger.iwArithFreqs ρ l₂)
              (Work.KMTAreas.A7.mStargF P.natDegree U) n₀
              (Work.KMTPlan.A6.mdlSliceG ρ P C₀ a l₁ l₂ k₁ k₂ j₂ t g n) y)) x)
        = (fun x : ℤ => Work.KMTAreas.A7.residueLp 2 q
          (fun y n₀ => PointwiseErgodicTheorems.variationalNorm r (fun n : ℕ =>
            Work.KMTAreas.A7.fiberOpP ρ P l₂ (Work.KMTAreas.A7.mStargF P.natDegree U) n₀
              (Work.KMTPlan.A6.mdlSliceG ρ P C₀ a l₁ l₂ k₁ k₂ j₂ t g n) y)) x) :=
      congrArg (fun W : ℤ → ℕ → ENNReal =>
        fun x : ℤ => Work.KMTAreas.A7.residueLp 2 q W x) hW
    rw [hfun]
    have hgoal := hCsamp C₀ a Λ hΛ ha ha1 l₁ l₂ k₁ k₂ t j₂ hj₂ hk₂ g hg ht
    rw [show (2 : ENNReal).toReal = 2 from by norm_num] at hgoal
    rw [hqdef, hUdef]
    refine hgoal.trans ?_
    refine mul_le_mul_left (ENNReal.ofReal_le_ofReal ?_) _
    exact mul_le_mul (le_max_right _ _)
      (Work.KMTPlan.A6Clean.lossWeight_mono As (max As 0) ρ (le_max_left _ _) hρ.le hAs0 l₁ l₂ k₁ k₂)
      (Work.KMTPlan.A6Clean.lossWeight_nonnegc _ _ l₁ l₂ k₁ k₂) (by positivity)

/-! ## The assembly -/

/-- `(2 : ENNReal)⁻¹ + (2 : ENNReal)⁻¹ = 1`. -/
theorem inv_two_add_inv_two_loc : (2 : ENNReal)⁻¹ + (2 : ENNReal)⁻¹ = 1 := by
  rw [← two_mul]
  exact ENNReal.mul_inv_cancel (by norm_num) (by simp)

theorem mdlSliceNoGain_of_vanishing_loc (P : Polynomial ℤ) (hd : 2 ≤ P.natDegree)
    (hA1 : Work.KMTContract.AreaA1) (C₀ : ℕ) (hC₀ : 1 ≤ C₀) (r : NNReal) (hr : 2 < r)
    (j₁ j₂ : ℤ) (hj₁ : j₁ ∈ ({-1, 0, 1} : Finset ℤ)) (hj₂ : j₂ ∈ ({-1, 0, 1} : Finset ℤ))
    (hVanF : ∀ (ρ : ℝ), 0 < ρ → ρ ≤ 1 → ∃ B : ℕ, ∀ (C₀ : ℕ) (a : ℕ → NNReal)
      (l₁ l₂ k₁ k₂ : ℕ) (j₁ : ℤ) (t : ℝ) (f : ℤ → ℂ),
      B ≤ Work.KMTPlan.A6.lcL l₁ l₂ k₁ k₂ → 1 ≤ l₁ →
      (∀ n : ℕ, 1 ≤ a n) → j₁ ∈ ({-1, 0, 1} : Finset ℤ) → (k₁ = 0 → j₁ ≠ -1) →
      MeasureTheory.MemLp f 2 MeasureTheory.Measure.count →
      t ∈ Set.Icc (1 / 2 : ℝ) 1 →
      ∀ (n : ℕ), Work.KMTPlan.A6.mdlCore ρ C₀ a l₁ l₂ k₁ k₂ n → ∀ (n₀ : ℤ) (x : ℤ),
        Work.KMTAreas.A7.fiberOpSet (Work.Analysis.IonescuWainger.iwArithFreqs ρ l₁)
            (Work.KMTAreas.A7.mStarF (Work.KMTAreas.A7.uScale ρ
              (Work.KMTPlan.A6.lcL l₁ l₂ k₁ k₂)))
            n₀ (Work.KMTPlan.A6.mdlSliceF ρ C₀ a l₁ l₂ k₁ k₂ j₁ t f n) x
          = Work.KMTAreas.A7.fiberOp ρ l₁
            (Work.KMTAreas.A7.mStarF (Work.KMTAreas.A7.uScale ρ
              (Work.KMTPlan.A6.lcL l₁ l₂ k₁ k₂)))
            n₀ (Work.KMTPlan.A6.mdlSliceF ρ C₀ a l₁ l₂ k₁ k₂ j₁ t f n) x)
    (hVanG : ∀ (ρ : ℝ), 0 < ρ → ρ ≤ 1 → ∃ B : ℕ, ∀ (P : Polynomial ℤ) (hd : 2 ≤ P.natDegree)
      (C₀ : ℕ) (a : ℕ → NNReal) (l₁ l₂ k₁ k₂ : ℕ) (j₂ : ℤ) (t : ℝ) (g : ℤ → ℂ),
      B ≤ Work.KMTPlan.A6.lcL l₁ l₂ k₁ k₂ → 1 ≤ l₂ →
      (∀ n : ℕ, 1 ≤ a n) → j₂ ∈ ({-1, 0, 1} : Finset ℤ) → (k₂ = 0 → j₂ ≠ -1) →
      MeasureTheory.MemLp g 2 MeasureTheory.Measure.count →
      t ∈ Set.Icc (1 / 2 : ℝ) 1 →
      ∀ (n : ℕ), Work.KMTPlan.A6.mdlCore ρ C₀ a l₁ l₂ k₁ k₂ n → ∀ (n₀ : ℤ) (x : ℤ),
        Work.KMTAreas.A7.fiberOpPSet P (Work.Analysis.IonescuWainger.iwArithFreqs ρ l₂)
            (Work.KMTAreas.A7.mStargF P.natDegree (Work.KMTAreas.A7.uScale ρ
              (Work.KMTPlan.A6.lcL l₁ l₂ k₁ k₂)))
            n₀ (Work.KMTPlan.A6.mdlSliceG ρ P C₀ a l₁ l₂ k₁ k₂ j₂ t g n) x
          = Work.KMTAreas.A7.fiberOpP ρ P l₂
            (Work.KMTAreas.A7.mStargF P.natDegree (Work.KMTAreas.A7.uScale ρ
              (Work.KMTPlan.A6.lcL l₁ l₂ k₁ k₂)))
            n₀ (Work.KMTPlan.A6.mdlSliceG ρ P C₀ a l₁ l₂ k₁ k₂ j₂ t g n) x) :
    Work.KMTPlan.A6Clean.MdlSliceNoGainAt P hd hA1 C₀ r j₁ j₂ := by
  unfold Work.KMTPlan.A6Clean.MdlSliceNoGainAt
  obtain ⟨cF, hcF0, ρF, hρF0, hFibF⟩ := fiberFAt r hr hVanF
  obtain ⟨cG, hcG0, ρG, hρG0, hFibG⟩ := fiberGAt P hd r hr hVanG
  obtain ⟨AlF, hAlF0, ρlF, hρlF0, hlinF⟩ := Work.KMTPlan.A6.MdlSliceLinF C₀ hC₀ r hr j₁ hj₁
  obtain ⟨AlG, hAlG0, ρlG, hρlG0, hlinG⟩ := Work.KMTPlan.A6.MdlSliceLinG P hd C₀ hC₀ r hr j₂ hj₂
  refine ⟨cF + cG + AlF + AlG, by positivity, min (min ρF ρG) (min ρlF ρlG),
    lt_min (lt_min hρF0 hρG0) (lt_min hρlF0 hρlG0), ?_⟩
  intro ρ hρ hρle
  have hρF : ρ ≤ ρF := le_trans hρle (le_trans (min_le_left _ _) (min_le_left _ _))
  have hρG : ρ ≤ ρG := le_trans hρle (le_trans (min_le_left _ _) (min_le_right _ _))
  have hρlF : ρ ≤ ρlF := le_trans hρle (le_trans (min_le_right _ _) (min_le_left _ _))
  have hρlG : ρ ≤ ρlG := le_trans hρle (le_trans (min_le_right _ _) (min_le_right _ _))
  obtain ⟨CUF, hCUF0, hFF⟩ := hFibF ρ hρ hρF
  obtain ⟨CUG, hCUG0, hGG⟩ := hFibG ρ hρ hρG
  obtain ⟨KlF, hKlF⟩ := hlinF ρ hρ hρlF
  obtain ⟨KlG, hKlG⟩ := hlinG ρ hρ hρlG
  let K₀ : NNReal → NNReal :=
    fun Λ => ⟨(CUF * CUG) * ((KlF Λ : ℝ) * (KlG Λ : ℝ)) + 1, by positivity⟩
  refine ⟨K₀, ?_⟩
  intro a Λ l₁ l₂ k₁ k₂ t f g hΛ ha ha1 ht hk₁ hk₂ hf hg
  set q : ℕ := Work.KMTAreas.A7.arithQ ρ (max l₁ l₂) with hqdef
  set U : ℕ := Work.KMTAreas.A7.uScale ρ (Work.KMTPlan.A6.lcL l₁ l₂ k₁ k₂) with hUdef
  -- the pointwise fibre decomposition of the frozen slice
  have hpt : ∀ x : ℤ, PointwiseErgodicTheorems.variationalNorm r
        (fun n : ℕ => Work.KMTPlan.A6.mdlSliceJ ρ P C₀ a f g l₁ l₂ k₁ k₂ j₁ j₂ t n x)
      ≤ (q : ENNReal)⁻¹ * ∑ n₀ ∈ Finset.range q,
          PointwiseErgodicTheorems.variationalNorm r (fun n : ℕ =>
            Work.KMTAreas.A7.fiberOpSet (Work.Analysis.IonescuWainger.iwArithFreqs ρ l₁)
              (Work.KMTAreas.A7.mStarF U) n₀
              (Work.KMTPlan.A6.mdlSliceF ρ C₀ a l₁ l₂ k₁ k₂ j₁ t f n) x)
          * PointwiseErgodicTheorems.variationalNorm r (fun n : ℕ =>
            Work.KMTAreas.A7.fiberOpPSet P (Work.Analysis.IonescuWainger.iwArithFreqs ρ l₂)
              (Work.KMTAreas.A7.mStargF P.natDegree U) n₀
              (Work.KMTPlan.A6.mdlSliceG ρ P C₀ a l₁ l₂ k₁ k₂ j₂ t g n) x) := by
    intro x
    have hmemF := memℓp_mdlSliceF_loc ρ hρ C₀ a l₁ l₂ k₁ k₂ j₁ t f ha1 hj₁ hk₁ hf
    have hmemG := memℓp_mdlSliceG_loc ρ hρ P hd C₀ a l₁ l₂ k₁ k₂ j₂ t g ha1 hj₂ hk₂ hg
    have hfam : (fun n : ℕ => Work.KMTPlan.A6.mdlSliceJ ρ P C₀ a f g l₁ l₂ k₁ k₂ j₁ j₂ t n x)
        = (fun n : ℕ => Work.KMTAreas.A7.Btwist ρ P l₁ l₂ (Work.KMTAreas.A7.mStarF U)
            (Work.KMTAreas.A7.mStargF P.natDegree U)
            (Work.KMTPlan.A6.mdlSliceF ρ C₀ a l₁ l₂ k₁ k₂ j₁ t f n)
            (Work.KMTPlan.A6.mdlSliceG ρ P C₀ a l₁ l₂ k₁ k₂ j₂ t g n) x) := by
      funext n
      exact Work.KMTPlan.A6.mdlSliceJ_eq_Btwist ρ P C₀ a f g l₁ l₂ k₁ k₂ j₁ j₂ t n x
    rw [hfam]
    refine Work.KMTPlan.A6Clean.variationalNorm_Btwist_fiber_le ρ P l₁ l₂ (Work.KMTAreas.A7.mStarF U)
      (Work.KMTAreas.A7.mStargF P.natDegree U) _ _ r
      (le_trans (by norm_num) (le_of_lt hr)) x ?_ ?_
    · intro m n₀
      have hs := Work.KMTAreas.A7.summable_cw_mul_of_memℓp (Work.KMTAreas.A7.summable_cw_mStarF U)
        (hmemF m) x
      refine Summable.of_norm_bounded (hs.norm.mul_left
        ((Work.Analysis.IonescuWainger.iwArithFreqs ρ l₁).card : ℝ)) fun j => ?_
      have hb := Work.KMTPlan.A6Clean.norm_arithCharSet_le_card (Work.Analysis.IonescuWainger.iwArithFreqs ρ l₁)
        (n₀ - j)
      rw [show Work.KMTAreas.A7.arithChar ρ l₁ (n₀ - j)
          = Work.KMTAreas.A7.arithCharSet (Work.Analysis.IonescuWainger.iwArithFreqs ρ l₁)
            (n₀ - j) from rfl]
      calc ‖Work.KMTAreas.A7.arithCharSet (Work.Analysis.IonescuWainger.iwArithFreqs ρ l₁)
              (n₀ - j)
            * Work.KMTAreas.A7.cw (Work.KMTAreas.A7.mStarF U) j
            * Work.KMTPlan.A6.mdlSliceF ρ C₀ a l₁ l₂ k₁ k₂ j₁ t f m (x - j)‖
          = ‖Work.KMTAreas.A7.arithCharSet (Work.Analysis.IonescuWainger.iwArithFreqs ρ l₁)
                (n₀ - j)‖
              * ‖Work.KMTAreas.A7.cw (Work.KMTAreas.A7.mStarF U) j
                * Work.KMTPlan.A6.mdlSliceF ρ C₀ a l₁ l₂ k₁ k₂ j₁ t f m (x - j)‖ := by
            simp only [norm_mul]
            ring
        _ ≤ ((Work.Analysis.IonescuWainger.iwArithFreqs ρ l₁).card : ℝ)
              * ‖Work.KMTAreas.A7.cw (Work.KMTAreas.A7.mStarF U) j
                * Work.KMTPlan.A6.mdlSliceF ρ C₀ a l₁ l₂ k₁ k₂ j₁ t f m (x - j)‖ :=
            mul_le_mul_of_nonneg_right hb (by positivity)
    · intro m n₀
      have hs := Work.KMTAreas.A7.summable_cw_mul_of_memℓp
        (Work.KMTAreas.A7.summable_cw_mStargF P.natDegree U) (hmemG m) x
      refine Summable.of_norm_bounded (hs.norm.mul_left
        ((Work.Analysis.IonescuWainger.iwArithFreqs ρ l₂).card : ℝ)) fun j => ?_
      have hb := Work.KMTPlan.A6Clean.norm_arithCharSet_le_card (Work.Analysis.IonescuWainger.iwArithFreqs ρ l₂)
        (P.eval n₀ - j)
      rw [show Work.KMTAreas.A7.arithChar ρ l₂ (P.eval n₀ - j)
          = Work.KMTAreas.A7.arithCharSet (Work.Analysis.IonescuWainger.iwArithFreqs ρ l₂)
              (P.eval n₀ - j) from rfl]
      calc ‖Work.KMTAreas.A7.arithCharSet (Work.Analysis.IonescuWainger.iwArithFreqs ρ l₂)
              (P.eval n₀ - j)
            * Work.KMTAreas.A7.cw (Work.KMTAreas.A7.mStargF P.natDegree U) j
            * Work.KMTPlan.A6.mdlSliceG ρ P C₀ a l₁ l₂ k₁ k₂ j₂ t g m (x - j)‖
          = ‖Work.KMTAreas.A7.arithCharSet (Work.Analysis.IonescuWainger.iwArithFreqs ρ l₂)
                (P.eval n₀ - j)‖
              * ‖Work.KMTAreas.A7.cw (Work.KMTAreas.A7.mStargF P.natDegree U) j
                * Work.KMTPlan.A6.mdlSliceG ρ P C₀ a l₁ l₂ k₁ k₂ j₂ t g m (x - j)‖ := by
            simp only [norm_mul]
            ring
        _ ≤ ((Work.Analysis.IonescuWainger.iwArithFreqs ρ l₂).card : ℝ)
              * ‖Work.KMTAreas.A7.cw (Work.KMTAreas.A7.mStargF P.natDegree U) j
                * Work.KMTPlan.A6.mdlSliceG ρ P C₀ a l₁ l₂ k₁ k₂ j₂ t g m (x - j)‖ :=
            mul_le_mul_of_nonneg_right hb (by positivity)
  -- the `ℓ¹`-monotonicity and the identification with `residueLp 1`
  have hstep1 : MeasureTheory.eLpNorm (fun x : ℤ => PointwiseErgodicTheorems.variationalNorm r
        (fun n : ℕ => Work.KMTPlan.A6.mdlSliceJ ρ P C₀ a f g l₁ l₂ k₁ k₂ j₁ j₂ t n x))
        1 MeasureTheory.Measure.count
      ≤ MeasureTheory.eLpNorm (fun x : ℤ => (q : ENNReal)⁻¹ * ∑ n₀ ∈ Finset.range q,
          PointwiseErgodicTheorems.variationalNorm r (fun n : ℕ =>
            Work.KMTAreas.A7.fiberOpSet (Work.Analysis.IonescuWainger.iwArithFreqs ρ l₁)
              (Work.KMTAreas.A7.mStarF U) n₀
              (Work.KMTPlan.A6.mdlSliceF ρ C₀ a l₁ l₂ k₁ k₂ j₁ t f n) x)
          * PointwiseErgodicTheorems.variationalNorm r (fun n : ℕ =>
            Work.KMTAreas.A7.fiberOpPSet P (Work.Analysis.IonescuWainger.iwArithFreqs ρ l₂)
              (Work.KMTAreas.A7.mStargF P.natDegree U) n₀
              (Work.KMTPlan.A6.mdlSliceG ρ P C₀ a l₁ l₂ k₁ k₂ j₂ t g n) x))
        1 MeasureTheory.Measure.count :=
    MeasureTheory.eLpNorm_mono_enorm (hf := by pw_aesm) fun x => by simpa using hpt x
  -- the residue Hölder inequality
  have hstep2 : MeasureTheory.eLpNorm (fun x : ℤ => (q : ENNReal)⁻¹ * ∑ n₀ ∈ Finset.range q,
        PointwiseErgodicTheorems.variationalNorm r (fun n : ℕ =>
          Work.KMTAreas.A7.fiberOpSet (Work.Analysis.IonescuWainger.iwArithFreqs ρ l₁)
            (Work.KMTAreas.A7.mStarF U) n₀
            (Work.KMTPlan.A6.mdlSliceF ρ C₀ a l₁ l₂ k₁ k₂ j₁ t f n) x)
        * PointwiseErgodicTheorems.variationalNorm r (fun n : ℕ =>
          Work.KMTAreas.A7.fiberOpPSet P (Work.Analysis.IonescuWainger.iwArithFreqs ρ l₂)
            (Work.KMTAreas.A7.mStargF P.natDegree U) n₀
            (Work.KMTPlan.A6.mdlSliceG ρ P C₀ a l₁ l₂ k₁ k₂ j₂ t g n) x))
      1 MeasureTheory.Measure.count
      ≤ MeasureTheory.eLpNorm (fun x : ℤ => Work.KMTAreas.A7.residueLp 2 q
            (fun y n₀ => PointwiseErgodicTheorems.variationalNorm r (fun n : ℕ =>
              Work.KMTAreas.A7.fiberOpSet (Work.Analysis.IonescuWainger.iwArithFreqs ρ l₁)
                (Work.KMTAreas.A7.mStarF U) n₀
                (Work.KMTPlan.A6.mdlSliceF ρ C₀ a l₁ l₂ k₁ k₂ j₁ t f n) y)) x)
          2 MeasureTheory.Measure.count
        * MeasureTheory.eLpNorm (fun x : ℤ => Work.KMTAreas.A7.residueLp 2 q
            (fun y n₀ => PointwiseErgodicTheorems.variationalNorm r (fun n : ℕ =>
              Work.KMTAreas.A7.fiberOpPSet P (Work.Analysis.IonescuWainger.iwArithFreqs ρ l₂)
                (Work.KMTAreas.A7.mStargF P.natDegree U) n₀
                (Work.KMTPlan.A6.mdlSliceG ρ P C₀ a l₁ l₂ k₁ k₂ j₂ t g n) y)) x)
          2 MeasureTheory.Measure.count := by
    have h := Work.KMTAreas.A7.residueLp_mul_le q 2 2 (by norm_num) (by norm_num)
      (by norm_num) (by norm_num) (le_of_eq inv_two_add_inv_two_loc)
      (U := fun y n₀ => PointwiseErgodicTheorems.variationalNorm r (fun n : ℕ =>
        Work.KMTAreas.A7.fiberOpSet (Work.Analysis.IonescuWainger.iwArithFreqs ρ l₁)
          (Work.KMTAreas.A7.mStarF U) n₀
          (Work.KMTPlan.A6.mdlSliceF ρ C₀ a l₁ l₂ k₁ k₂ j₁ t f n) y))
      (V := fun y n₀ => PointwiseErgodicTheorems.variationalNorm r (fun n : ℕ =>
        Work.KMTAreas.A7.fiberOpPSet P (Work.Analysis.IonescuWainger.iwArithFreqs ρ l₂)
          (Work.KMTAreas.A7.mStargF P.natDegree U) n₀
          (Work.KMTPlan.A6.mdlSliceG ρ P C₀ a l₁ l₂ k₁ k₂ j₂ t g n) y))
    rw [inv_two_add_inv_two_loc] at h
    simpa only [ENNReal.toReal_ofNat, inv_one] using h
  -- the two fibre bounds
  have hfibF := hFF C₀ a Λ l₁ l₂ k₁ k₂ j₁ t f hΛ ha ha1 ht hj₁ hk₁ hf
  have hfibG := hGG C₀ a Λ l₁ l₂ k₁ k₂ j₂ t g hΛ ha ha1 ht hj₂ hk₂ hg
  -- the two linear bounds, folded into the `mdlSliceF`/`mdlSliceG` carriers
  have hlinF' : MeasureTheory.eLpNorm (fun x : ℤ => PointwiseErgodicTheorems.variationalNorm r
        (fun n : ℕ => Work.KMTPlan.A6.mdlSliceF ρ C₀ a l₁ l₂ k₁ k₂ j₁ t f n x))
      2 MeasureTheory.Measure.count
      ≤ (KlF Λ : ENNReal) * ENNReal.ofReal (Work.KMTAreas.A7.lossWeight AlF ρ l₁ l₂ k₁ k₂)
        * MeasureTheory.eLpNorm f 2 MeasureTheory.Measure.count := by
    simpa only [Work.KMTPlan.A6.mdlSliceF, ite_apply, Pi.zero_apply]
      using hKlF a Λ l₁ l₂ k₁ k₂ t f hΛ ha ha1 ht hk₁
  have hlinG' : MeasureTheory.eLpNorm (fun x : ℤ => PointwiseErgodicTheorems.variationalNorm r
        (fun n : ℕ => Work.KMTPlan.A6.mdlSliceG ρ P C₀ a l₁ l₂ k₁ k₂ j₂ t g n x))
      2 MeasureTheory.Measure.count
      ≤ (KlG Λ : ENNReal) * ENNReal.ofReal (Work.KMTAreas.A7.lossWeight AlG ρ l₁ l₂ k₁ k₂)
        * MeasureTheory.eLpNorm g 2 MeasureTheory.Measure.count := by
    simpa only [Work.KMTPlan.A6.mdlSliceG, ite_apply, Pi.zero_apply]
      using hKlG a Λ l₁ l₂ k₁ k₂ t g hΛ ha ha1 ht hk₂
  -- the constant collapse
  have hcollapse : MeasureTheory.eLpNorm (fun x : ℤ => Work.KMTAreas.A7.residueLp 2 q
            (fun y n₀ => PointwiseErgodicTheorems.variationalNorm r (fun n : ℕ =>
              Work.KMTAreas.A7.fiberOpSet (Work.Analysis.IonescuWainger.iwArithFreqs ρ l₁)
                (Work.KMTAreas.A7.mStarF U) n₀
                (Work.KMTPlan.A6.mdlSliceF ρ C₀ a l₁ l₂ k₁ k₂ j₁ t f n) y)) x)
          2 MeasureTheory.Measure.count
        * MeasureTheory.eLpNorm (fun x : ℤ => Work.KMTAreas.A7.residueLp 2 q
            (fun y n₀ => PointwiseErgodicTheorems.variationalNorm r (fun n : ℕ =>
              Work.KMTAreas.A7.fiberOpPSet P (Work.Analysis.IonescuWainger.iwArithFreqs ρ l₂)
                (Work.KMTAreas.A7.mStargF P.natDegree U) n₀
                (Work.KMTPlan.A6.mdlSliceG ρ P C₀ a l₁ l₂ k₁ k₂ j₂ t g n) y)) x)
          2 MeasureTheory.Measure.count
        ≤ ((K₀ Λ : NNReal) : ENNReal)
          * ENNReal.ofReal (Work.KMTAreas.A7.lossWeight (cF + cG + AlF + AlG) ρ l₁ l₂ k₁ k₂)
          * MeasureTheory.eLpNorm f 2 MeasureTheory.Measure.count
          * MeasureTheory.eLpNorm g 2 MeasureTheory.Measure.count := by
    have hlwF := Work.KMTPlan.A6Clean.lossWeight_nonnegc cF ρ l₁ l₂ k₁ k₂
    have hlwG := Work.KMTPlan.A6Clean.lossWeight_nonnegc cG ρ l₁ l₂ k₁ k₂
    have hlwAlF := Work.KMTPlan.A6Clean.lossWeight_nonnegc AlF ρ l₁ l₂ k₁ k₂
    have hlwAlG := Work.KMTPlan.A6Clean.lossWeight_nonnegc AlG ρ l₁ l₂ k₁ k₂
    have hprod : Work.KMTAreas.A7.lossWeight cF ρ l₁ l₂ k₁ k₂
          * Work.KMTAreas.A7.lossWeight cG ρ l₁ l₂ k₁ k₂
          * Work.KMTAreas.A7.lossWeight AlF ρ l₁ l₂ k₁ k₂
          * Work.KMTAreas.A7.lossWeight AlG ρ l₁ l₂ k₁ k₂
        = Work.KMTAreas.A7.lossWeight (cF + cG + AlF + AlG) ρ l₁ l₂ k₁ k₂ := by
      rw [Work.KMTPlan.A6Clean.lossWeight_mulc, Work.KMTPlan.A6Clean.lossWeight_mulc, Work.KMTPlan.A6Clean.lossWeight_mulc]
    have hcoe : ((K₀ Λ : NNReal) : ENNReal)
        = ENNReal.ofReal ((CUF * CUG) * ((KlF Λ : ℝ) * (KlG Λ : ℝ)) + 1) := by
      rw [ENNReal.coe_nnreal_eq]
      rfl
    rw [hcoe]
    refine le_trans (mul_le_mul hfibF hfibG bot_le bot_le) ?_
    refine le_trans (mul_le_mul
      (mul_le_mul_of_nonneg_left hlinF' bot_le)
      (mul_le_mul_of_nonneg_left hlinG' bot_le) bot_le bot_le) ?_
    -- collapse the constants
    have hstep : ENNReal.ofReal (CUF * Work.KMTAreas.A7.lossWeight cF ρ l₁ l₂ k₁ k₂)
          * ((KlF Λ : ENNReal) * ENNReal.ofReal (Work.KMTAreas.A7.lossWeight AlF ρ l₁ l₂ k₁ k₂)
              * MeasureTheory.eLpNorm f 2 MeasureTheory.Measure.count)
          * (ENNReal.ofReal (CUG * Work.KMTAreas.A7.lossWeight cG ρ l₁ l₂ k₁ k₂)
              * ((KlG Λ : ENNReal) * ENNReal.ofReal (Work.KMTAreas.A7.lossWeight AlG ρ l₁ l₂ k₁ k₂)
                * MeasureTheory.eLpNorm g 2 MeasureTheory.Measure.count))
        = ENNReal.ofReal (CUF * Work.KMTAreas.A7.lossWeight cF ρ l₁ l₂ k₁ k₂)
          * ENNReal.ofReal ((KlF Λ : ℝ))
          * ENNReal.ofReal (Work.KMTAreas.A7.lossWeight AlF ρ l₁ l₂ k₁ k₂)
          * ENNReal.ofReal (CUG * Work.KMTAreas.A7.lossWeight cG ρ l₁ l₂ k₁ k₂)
          * ENNReal.ofReal ((KlG Λ : ℝ))
          * ENNReal.ofReal (Work.KMTAreas.A7.lossWeight AlG ρ l₁ l₂ k₁ k₂)
          * MeasureTheory.eLpNorm f 2 MeasureTheory.Measure.count
          * MeasureTheory.eLpNorm g 2 MeasureTheory.Measure.count := by
      rw [ENNReal.coe_nnreal_eq (KlF Λ), ENNReal.coe_nnreal_eq (KlG Λ)]
      ring
    rw [hstep]
    repeat rw [← ENNReal.ofReal_mul (by positivity)]
    refine mul_le_mul_of_nonneg_right
      (a := MeasureTheory.eLpNorm g 2 MeasureTheory.Measure.count)
      (mul_le_mul_of_nonneg_right
        (a := MeasureTheory.eLpNorm f 2 MeasureTheory.Measure.count)
        (ENNReal.ofReal_le_ofReal ?_) bot_le) bot_le
    have h4 : (0 : ℝ) ≤ (Work.KMTAreas.A7.lossWeight cF ρ l₁ l₂ k₁ k₂
          * Work.KMTAreas.A7.lossWeight cG ρ l₁ l₂ k₁ k₂)
          * (Work.KMTAreas.A7.lossWeight AlF ρ l₁ l₂ k₁ k₂
            * Work.KMTAreas.A7.lossWeight AlG ρ l₁ l₂ k₁ k₂) :=
      mul_nonneg (mul_nonneg hlwF hlwG) (mul_nonneg hlwAlF hlwAlG)
    rw [← hprod]
    nlinarith [h4]
  exact le_trans hstep1 (le_trans hstep2 hcollapse)

/-- **The loss-form (no-gain) slice bound at every admissible parameter** — the `hNoGain` input of
`Work.KMTPlan.A6Clean.MdlSliceCoreGainMemLp_of_pieces_split`, packaged as one statement
(`MdlSliceNoGainAt` is the def in `Submission/Work/KMTPlan/A6Clean/MdlSliceNoGainAt.lean`).

Content: for every `C₀ ≥ 1`, `r > 2`, `(j₁,j₂) ∈ {-1,0,1}²` there are `c ≥ 0`, `ρ₀ > 0` and, for
each `ρ ≤ ρ₀`, a `K`, such that for **all** data
`eLpNorm (fun x => variationalNorm r (fun n => mdlSliceJ ρ P C₀ a f g l₁ l₂ k₁ k₂ j₁ j₂ t n x)) 1 count
  ≤ (K Λ) * ofReal (lossWeight c ρ l₁ l₂ k₁ k₂) * ‖f‖₂ * ‖g‖₂`
(the unfolding of `MdlSliceNoGainAt`).  This is the A6 twin of the PROVED
`Work.KMTAreas.A7.ModelLargeBound` at `(p₁,p₂) = (2,2)`; it covers **all** data (in particular the
bounded `lcL l₁ l₂ k₁ k₂`, where the gated §8 adelic form does not apply) because its proof uses no
Shannon sampling.

Proved/available ingredients: `Work.KMTPlan.A6.mdlSliceJ_eq_Btwist` +
`Work.KMTAreas.A7.Btwist_eq_fiberSum` (pointwise fibre factorisation
`mdlSliceJ n x = q⁻¹ ∑_{n₀<q} U_{n₀}(x) V_{n₀}(x)`), the variational bilinear bound
`V^r(UV) ≲ (sup+V^R)(U)·(sup+V^R)(V)` for `R < r` (`BilinearFkr`/`FkrInterchange`) plus the
homogeneity over the `q` fibres (`Work.KMTPlan.A6.VarNormFibreJensen`) and residue Hölder
(`Work.KMTAreas.A7.residueLp_mul_le`), the PROVED fibre sampling estimates
`A6Clean/mdlSliceF_fiberVarSampling` / `mdlSliceG_fiberVarSampling` at `p = 2`, the PROVED linear
estimates `Work.KMTPlan.A6.MdlSliceLinF` / `MdlSliceLinG`, and Cauchy–Schwarz in `x ∈ ℤ` for the
outer `ℓ¹`.

Note.  Two sibling files carry the same statement with a hole —
`Submission/Work/KMTPlan/A6Clean/mdlSliceNoGain.lean` (mid-work; its `F` component is proved) and
`Submission/Work/KMTPlan/A6/MdlSliceNoGainCopy.lean` — and belong to another lane; do not edit
them.  This module is the clean copy under the required name: it is a copy of the sibling
development `Submission/Work/KMTPlan/A6LH/MdlSliceNoGainProved.lean` (namespace `Work.A6LH`), with
the last-mile tactic repairs applied, and it rests only on `propext, Classical.choice, Quot.sound`.
See `NOTES_A6_VrSamplingVecUniform_SESSION.md` §7 (workspace root).-/
theorem MdlSliceNoGainAtProved (P : Polynomial ℤ) (hd : 2 ≤ P.natDegree)
    (hA1 : Work.KMTContract.AreaA1) :
    ∀ (C₀ : ℕ), 1 ≤ C₀ → ∀ (r : NNReal), 2 < r → ∀ (j₁ j₂ : ℤ),
      j₁ ∈ ({-1, 0, 1} : Finset ℤ) → j₂ ∈ ({-1, 0, 1} : Finset ℤ) →
      Work.KMTPlan.A6Clean.MdlSliceNoGainAt P hd hA1 C₀ r j₁ j₂ := by
  intro C₀ hC₀ r hr j₁ j₂ hj₁ hj₂
  -- the two vanishing inputs, in the `ρ`-dependent form proved in `A6/MdlFibreIdent.lean`
  have hVanF : ∀ (ρ : ℝ), 0 < ρ → ρ ≤ 1 → ∃ B : ℕ, ∀ (C₀ : ℕ) (a : ℕ → NNReal)
      (l₁ l₂ k₁ k₂ : ℕ) (j₁ : ℤ) (t : ℝ) (f : ℤ → ℂ),
      B ≤ Work.KMTPlan.A6.lcL l₁ l₂ k₁ k₂ → 1 ≤ l₁ →
      (∀ n : ℕ, 1 ≤ a n) → j₁ ∈ ({-1, 0, 1} : Finset ℤ) → (k₁ = 0 → j₁ ≠ -1) →
      MeasureTheory.MemLp f 2 MeasureTheory.Measure.count →
      t ∈ Set.Icc (1 / 2 : ℝ) 1 →
      ∀ (n : ℕ), Work.KMTPlan.A6.mdlCore ρ C₀ a l₁ l₂ k₁ k₂ n → ∀ (n₀ : ℤ) (x : ℤ),
        Work.KMTAreas.A7.fiberOpSet (Work.Analysis.IonescuWainger.iwArithFreqs ρ l₁)
            (Work.KMTAreas.A7.mStarF (Work.KMTAreas.A7.uScale ρ
              (Work.KMTPlan.A6.lcL l₁ l₂ k₁ k₂)))
            n₀ (Work.KMTPlan.A6.mdlSliceF ρ C₀ a l₁ l₂ k₁ k₂ j₁ t f n) x
          = Work.KMTAreas.A7.fiberOp ρ l₁
            (Work.KMTAreas.A7.mStarF (Work.KMTAreas.A7.uScale ρ
              (Work.KMTPlan.A6.lcL l₁ l₂ k₁ k₂)))
            n₀ (Work.KMTPlan.A6.mdlSliceF ρ C₀ a l₁ l₂ k₁ k₂ j₁ t f n) x :=
    fun ρ hρ hρ1 => Work.KMTPlan.A6Clean.fiberOpSet_mdlSliceF_eq_fiberOp_of_largeRho ρ hρ hρ1
  have hVanG : ∀ (ρ : ℝ), 0 < ρ → ρ ≤ 1 → ∃ B : ℕ, ∀ (P : Polynomial ℤ) (hd : 2 ≤ P.natDegree)
      (C₀ : ℕ) (a : ℕ → NNReal) (l₁ l₂ k₁ k₂ : ℕ) (j₂ : ℤ) (t : ℝ) (g : ℤ → ℂ),
      B ≤ Work.KMTPlan.A6.lcL l₁ l₂ k₁ k₂ → 1 ≤ l₂ →
      (∀ n : ℕ, 1 ≤ a n) → j₂ ∈ ({-1, 0, 1} : Finset ℤ) → (k₂ = 0 → j₂ ≠ -1) →
      MeasureTheory.MemLp g 2 MeasureTheory.Measure.count →
      t ∈ Set.Icc (1 / 2 : ℝ) 1 →
      ∀ (n : ℕ), Work.KMTPlan.A6.mdlCore ρ C₀ a l₁ l₂ k₁ k₂ n → ∀ (n₀ : ℤ) (x : ℤ),
        Work.KMTAreas.A7.fiberOpPSet P (Work.Analysis.IonescuWainger.iwArithFreqs ρ l₂)
            (Work.KMTAreas.A7.mStargF P.natDegree (Work.KMTAreas.A7.uScale ρ
              (Work.KMTPlan.A6.lcL l₁ l₂ k₁ k₂)))
            n₀ (Work.KMTPlan.A6.mdlSliceG ρ P C₀ a l₁ l₂ k₁ k₂ j₂ t g n) x
          = Work.KMTAreas.A7.fiberOpP ρ P l₂
            (Work.KMTAreas.A7.mStargF P.natDegree (Work.KMTAreas.A7.uScale ρ
              (Work.KMTPlan.A6.lcL l₁ l₂ k₁ k₂)))
            n₀ (Work.KMTPlan.A6.mdlSliceG ρ P C₀ a l₁ l₂ k₁ k₂ j₂ t g n) x :=
    fun ρ hρ hρ1 => Work.KMTPlan.A6Clean.fiberOpPSet_mdlSliceG_eq_fiberOpP_of_largeRho ρ hρ hρ1
  exact mdlSliceNoGain_of_vanishing_loc P hd hA1 C₀ hC₀ r hr j₁ j₂ hj₁ hj₂ hVanF hVanG

end

end Work.KMTPlan.A6LH
