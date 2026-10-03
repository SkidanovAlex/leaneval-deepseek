/-
# `Work.KMTPlan.A6.MdlSliceLinGOne`

The linear lacunary variational estimate of §8 of Krause--Mirek--Tao for the `g`-side packet
family with the *modified* bumps `φ̃_{N,t,j₂}`, `j₂ ∈ {0,1}` (the `f`-side height `k₁` is `0`).

At `p = 2` the variational norm is dominated by the square function
(`Work.KMTAreas.A7.variationalNorm_le_sqSum`), and the square function of a family of
Ionescu--Wainger multipliers is computed by Plancherel (`tsum_eLpNorm_sq_iwConv_le`).  The two
remaining inputs are the pointwise square-function bounds for the `≤ l₂`- and the exact-height
symbols (`iwSymbolTle_sqSum_le`, `iwSymbolExact_sqSum_le`) and, for the excluded pair
`(j₂,k₂) = (0,0)`, the low-pass estimate `MdlSliceLinGOne_ball`.
-/
import Mathlib
import Submission.Work.KMTPlan.A6.varphitildeNtjPointwise
import Submission.Work.KMTPlan.A6.Tle_piExact_eq_convOp
import Submission.Work.KMTPlan.A6.eLpNorm_varNorm_two_le_sqSum
import Submission.Work.KMTPlan.A6.MdlGL2Bound
import Submission.Work.KMTPlan.A6.iwSymbolTleSqSumGen
import Submission.Work.KMTAreas.A7.LoModelLargeScaleHolds
import Submission.Work.KMTAreas.A7.MixedGSideNonAlias
import Submission.Work.KMTAreas.A7G.lowpassAlphaTransferG
import Submission.Work.KMTAreas.A7Hi.Gassembly
import Submission.Work.KMTPlan.A6.LowpassVarOnCore
import Submission.Work.KMTPlan.A6.eLpNorm_piExact_le
import Submission.Work.KMTPlan.A6.iwQl_mul_le_splitCut
import Submission.Work.KMTPlan.A6.lowpassSmallHeightCore
import Submission.Work.KMTPlan.A6.pieceL2BoundRect

namespace Work.KMTPlan.A6

open MeasureTheory
open scoped ENNReal NNReal BigOperators

noncomputable section

/-! ## Elementary helpers -/

/-- The loss weight is at least `1`. -/
theorem one_le_lossWeight {A ρ : ℝ} (hA : 0 ≤ A) (hρ : 0 ≤ ρ) (l₁ l₂ k₁ k₂ : ℕ) :
    1 ≤ Work.KMTAreas.A7.lossWeight A ρ l₁ l₂ k₁ k₂ := by
  have hL : (0 : ℝ) ≤ Work.KMTAreas.A7.lmaxR l₁ l₂ k₁ k₂ := by
    rw [Work.KMTAreas.A7.lmaxR]
    exact_mod_cast (show (0 : ℤ) ≤ Work.Analysis.EndVar.lmax l₁ l₂ (k₁ : ℤ) (k₂ : ℤ) from by
      simp only [Work.Analysis.EndVar.lmax]; omega)
  unfold Work.KMTAreas.A7.lossWeight
  have h1 : (1 : ℝ) ≤ 1 + Work.KMTAreas.A7.lmaxR l₁ l₂ k₁ k₂ := by linarith
  have h2 : (1 : ℝ) ≤ (1 + Work.KMTAreas.A7.lmaxR l₁ l₂ k₁ k₂) ^ A := Real.one_le_rpow h1 hA
  have h3 : (0 : ℝ) ≤ A * ρ * Work.KMTAreas.A7.lmaxR l₁ l₂ k₁ k₂ := by positivity
  have h5 : (1 : ℝ) ≤ (2 : ℝ) ^ (A * ρ * Work.KMTAreas.A7.lmaxR l₁ l₂ k₁ k₂) :=
    Real.one_le_rpow (by norm_num) h3
  have h6 : (0 : ℝ) ≤ (1 + Work.KMTAreas.A7.lmaxR l₁ l₂ k₁ k₂) ^ A := by positivity
  exact le_trans (by norm_num) (mul_le_mul h2 h5 zero_le_one h6)

/-- `lossWeight` is monotone in its exponent. -/
theorem lossWeight_mono' {A A' ρ : ℝ} (hAA' : A ≤ A') (hρ : 0 ≤ ρ) (l₁ l₂ k₁ k₂ : ℕ) :
    Work.KMTAreas.A7.lossWeight A ρ l₁ l₂ k₁ k₂
      ≤ Work.KMTAreas.A7.lossWeight A' ρ l₁ l₂ k₁ k₂ := by
  have hL : (0 : ℝ) ≤ Work.KMTAreas.A7.lmaxR l₁ l₂ k₁ k₂ := by
    rw [Work.KMTAreas.A7.lmaxR]
    exact_mod_cast (show (0 : ℤ) ≤ Work.Analysis.EndVar.lmax l₁ l₂ (k₁ : ℤ) (k₂ : ℤ) from by
      simp only [Work.Analysis.EndVar.lmax]; omega)
  rw [Work.KMTAreas.A7.lossWeight, Work.KMTAreas.A7.lossWeight]
  refine mul_le_mul ?_ ?_ (by positivity) (by positivity)
  · exact Real.rpow_le_rpow_of_exponent_le (by linarith) hAA'
  · refine Real.rpow_le_rpow_of_exponent_le (by norm_num) ?_
    exact mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_right hAA' hρ) hL

/-- `eLpNorm f 2 count ≠ ⊤` gives `f ∈ ℓ²(ℤ)`. -/
theorem memLp_two_count_of_ne_top' {f : ℤ → ℂ}
    (h : MeasureTheory.eLpNorm f 2 MeasureTheory.Measure.count ≠ ⊤) :
    MeasureTheory.MemLp f 2 MeasureTheory.Measure.count := by
  refine MeasureTheory.memLp_iff.mpr ?_
  rwa [lt_top_iff_ne_top]


/-- The `≤ l₂` multiplier applied to the narrow exact-height projection `mdlG` collapses to the
exact-height multiplier `Tm` applied to `g`. -/
theorem Tle_mdlG_eq_Tm (ρ : ℝ) (hρ : 0 < ρ) (hρ1 : ρ ≤ 1) (P : Polynomial ℤ) (u l₂ : ℕ)
    (φ : ℝ → ℂ)
    (hc : (2 : ℝ) ^ (-((P.natDegree : ℤ) * (u : ℤ))) ≤ 1 / 2)
    {g : ℤ → ℂ} (hg : MeasureTheory.MemLp g 2 MeasureTheory.Measure.count)
    (hnA : Work.Analysis.IonescuWainger.NonAliasing
      (-((P.natDegree : ℤ) * (u : ℤ))) (Work.Analysis.IonescuWainger.iwArithFreqs ρ l₂))
    (hφmem : MeasureTheory.MemLp (Work.Analysis.IonescuWainger.periodize φ) ⊤
      Work.Analysis.IonescuWainger.circleMeasure)
    (hΦ : Work.Analysis.IonescuWainger.SupportedInArc
      (-((P.natDegree : ℤ) * (u : ℤ)) - 1) (Work.Analysis.IonescuWainger.periodize φ)) :
    Work.KMTAreas.A7.Tle ρ l₂ φ (mdlG ρ P u l₂ g) = Work.KMTAreas.A7.Tm ρ l₂ φ g := by
  rw [mdlG, Tle_piExact_eq_convOp ρ hρ hρ1 l₂ (-((P.natDegree : ℤ) * (u : ℤ))) φ hc hg hnA
      hφmem hΦ, mae_Tm_eq_convOp_maeKer]

/-- The modified `g`-bump of the model is supported in the narrow arc of the window of `mdlG`. -/
theorem supportedInArc_varphitildeNtj (P : Polynomial ℤ) (hd : 2 ≤ P.natDegree)
    (N k₂ : ℕ) (j₂ : ℤ) (t : ℝ) {u : ℕ} (hu : 1 ≤ u)
    (hmain : k₂ + 2 * u ≤ (Work.Analysis.EndVar.logN N).toNat) :
    Work.Analysis.IonescuWainger.SupportedInArc (-((P.natDegree : ℤ) * (u : ℤ)) - 1)
      (Work.Analysis.IonescuWainger.periodize (varphitildeNtj P N k₂ j₂ t)) := by
  refine supportedInArc_periodize_of_arc fun x hx => ?_
  have hvt : Work.KMTAreas.A7.varphitildeNt P P.natDegree N k₂ t x ≠ 0 := by
    intro h0
    exact hx (by simp only [varphitildeNtj, h0, mul_zero])
  have hsupp := Work.KMTAreas.A7.varphitildeNt_support_all P P.natDegree N k₂ t x hvt
  have hd1 : (1 : ℤ) ≤ (P.natDegree : ℤ) := by
    have : 1 ≤ P.natDegree := by omega
    exact_mod_cast this
  have hu1 : (1 : ℤ) ≤ (u : ℤ) := by exact_mod_cast hu
  have hlogN : (k₂ : ℤ) + 2 * (u : ℤ) ≤ Work.Analysis.EndVar.logN N := by
    have h0 : (0 : ℤ) ≤ Work.Analysis.EndVar.logN N := by
      simp only [Work.Analysis.EndVar.logN]; exact Int.natCast_nonneg _
    have h1 : ((Work.Analysis.EndVar.logN N).toNat : ℤ) = Work.Analysis.EndVar.logN N :=
      Int.toNat_of_nonneg h0
    omega
  have hexp : (P.natDegree : ℝ) * ((k₂ : ℝ) - (Work.Analysis.EndVar.logN N : ℝ)) ≤
      (((-((P.natDegree : ℤ) * (u : ℤ)) - 1 : ℤ)) : ℝ) := by
    have h3 : (1 : ℤ) ≤ (P.natDegree : ℤ) * (u : ℤ) :=
      le_trans (by omega) (mul_le_mul hd1 hu1 (by omega) (by omega))
    have h4 : (P.natDegree : ℤ) * ((k₂ : ℤ) - Work.Analysis.EndVar.logN N) ≤
        -((P.natDegree : ℤ) * (u : ℤ)) - 1 := by
      have h5 : (P.natDegree : ℤ) * ((k₂ : ℤ) - Work.Analysis.EndVar.logN N)
          ≤ (P.natDegree : ℤ) * (-(2 * (u : ℤ))) := by
        refine mul_le_mul_of_nonneg_left ?_ (by omega)
        omega
      nlinarith [h5, h3]
    calc (P.natDegree : ℝ) * ((k₂ : ℝ) - (Work.Analysis.EndVar.logN N : ℝ))
        = (((P.natDegree : ℤ) * ((k₂ : ℤ) - Work.Analysis.EndVar.logN N) : ℤ) : ℝ) := by
          push_cast; ring
      _ ≤ (((-((P.natDegree : ℤ) * (u : ℤ)) - 1 : ℤ)) : ℝ) := by exact_mod_cast h4
  rw [Work.Analysis.IonescuWainger.realArc, Set.mem_Icc]
  have hle : |x| ≤ (2 : ℝ) ^ (((-((P.natDegree : ℤ) * (u : ℤ)) - 1 : ℤ)) : ℝ) :=
    le_trans hsupp (Real.rpow_le_rpow_of_exponent_le (by norm_num) hexp)
  rw [Real.rpow_intCast] at hle
  exact ⟨neg_le_of_abs_le hle, le_of_abs_le hle⟩

/-- `MemLp (periodize (φ̃_{N,k,j})) ⊤`. -/
theorem memLp_periodize_varphitildeNtj (P : Polynomial ℤ) (hd : 2 ≤ P.natDegree)
    (N k₂ : ℕ) (j₂ : ℤ) (t : ℝ) (hk : k₂ ≠ 0 ∨ 0 ≤ j₂) (hN : 1 ≤ N)
    (ht : t ∈ Set.Icc (1 / 2 : ℝ) 1) (hj : j₂ ∈ ({-1, 0, 1} : Finset ℤ)) :
    MeasureTheory.MemLp (Work.Analysis.IonescuWainger.periodize
      (varphitildeNtj P N k₂ j₂ t)) ⊤ Work.Analysis.IonescuWainger.circleMeasure := by
  obtain ⟨hbd, -⟩ := varphitildeNtjPointwise P hd
  obtain ⟨Cb, hCbpos, hCb⟩ := hbd
  obtain ⟨S, hSpos, hS⟩ := varphitildeNtj_bounds P N k₂ j₂ hk
  obtain ⟨hScd, hScs, -, -⟩ := hS t ht
  obtain ⟨R, hR⟩ := Work.KMTAreas.A7.exists_abs_le_of_hasCompactSupport hScs
  refine Work.Analysis.IonescuWainger.memLp_periodize hScd.continuous.measurable (R := max R 0) (C := Cb)
    (le_max_right R 0) ?_ ?_
  · intro x hx
    exact hR x (le_of_lt (lt_of_le_of_lt (le_max_left R 0) hx))
  · intro x
    have hnot : ¬(k₂ = 0 ∧ j₂ = -1) := by
      rintro ⟨h1, h2⟩
      rcases hk with h | h
      · exact h h1
      · omega
    exact hCb N k₂ j₂ t hj hnot hN x

/-- `1 + l₂` is dominated by the loss weight (for exponent `A ≥ 1`). -/
theorem one_add_le_lossWeight {A ρ : ℝ} (hA : 1 ≤ A) (hρ : 0 ≤ ρ) (l₁ l₂ k₁ k₂ : ℕ) :
    1 + (l₂ : ℝ) ≤ Work.KMTAreas.A7.lossWeight A ρ l₁ l₂ k₁ k₂ := by
  have hlmax : (l₂ : ℝ) ≤ Work.KMTAreas.A7.lmaxR l₁ l₂ k₁ k₂ := by
    rw [Work.KMTAreas.A7.lmaxR]
    have h : (l₂ : ℤ) ≤ Work.Analysis.EndVar.lmax l₁ l₂ (k₁ : ℤ) (k₂ : ℤ) := by
      rw [Work.Analysis.EndVar.lmax]
      exact le_trans (le_max_right _ _) (le_max_left _ _)
    exact_mod_cast h
  rw [Work.KMTAreas.A7.lossWeight]
  have hbase : (1 : ℝ) ≤ 1 + Work.KMTAreas.A7.lmaxR l₁ l₂ k₁ k₂ := by
    linarith [le_trans (Nat.cast_nonneg l₂) hlmax]
  have h2 : (1 : ℝ) + Work.KMTAreas.A7.lmaxR l₁ l₂ k₁ k₂
      ≤ (1 + Work.KMTAreas.A7.lmaxR l₁ l₂ k₁ k₂) ^ A := by
    calc (1 : ℝ) + Work.KMTAreas.A7.lmaxR l₁ l₂ k₁ k₂
        = (1 + Work.KMTAreas.A7.lmaxR l₁ l₂ k₁ k₂) ^ (1 : ℝ) := (Real.rpow_one _).symm
      _ ≤ (1 + Work.KMTAreas.A7.lmaxR l₁ l₂ k₁ k₂) ^ A :=
          Real.rpow_le_rpow_of_exponent_le hbase hA
  have hexp : (0 : ℝ) ≤ A * ρ * Work.KMTAreas.A7.lmaxR l₁ l₂ k₁ k₂ :=
    mul_nonneg (mul_nonneg (by linarith) hρ) (le_trans (Nat.cast_nonneg l₂) hlmax)
  have h3 : (1 : ℝ) ≤ (2 : ℝ) ^ (A * ρ * Work.KMTAreas.A7.lmaxR l₁ l₂ k₁ k₂) :=
    Real.one_le_rpow (by norm_num) hexp
  have h4 : (0 : ℝ) ≤ (1 + Work.KMTAreas.A7.lmaxR l₁ l₂ k₁ k₂) ^ A :=
    Real.rpow_nonneg (by linarith [le_trans (Nat.cast_nonneg l₂) hlmax]) A
  calc 1 + (l₂ : ℝ)
      ≤ (1 + Work.KMTAreas.A7.lmaxR l₁ l₂ k₁ k₂) ^ A :=
        le_trans (by linarith [hlmax]) h2
    _ = (1 + Work.KMTAreas.A7.lmaxR l₁ l₂ k₁ k₂) ^ A * 1 := by ring
    _ ≤ (1 + Work.KMTAreas.A7.lmaxR l₁ l₂ k₁ k₂) ^ A *
          (2 : ℝ) ^ (A * ρ * Work.KMTAreas.A7.lmaxR l₁ l₂ k₁ k₂) :=
        mul_le_mul_of_nonneg_left h3 h4

/-! ## The non-exceptional cases `k₂ ≠ 0 ∨ j₂ = 1`

When `k₂ ≠ 0` or `j₂ = 1` the modified bump `φ̃_{⌊a n⌋,k₂,j₂,t}` vanishes at the frequency origin
(by the level collapse `varphitildeNtjLevelCollapse`), so the pointwise square sum of the
Ionescu--Wainger symbols `iwSymbolSet (iwArithFreqs ρ l₂) (periodize ψ_n)` is *uniformly* bounded
(`Work.KMTPlan.A6.iwSymbolTle_sqSum_le`, PROVED).  Since `p = 2`, the variational norm is
dominated by the square function (`Work.KMTPlan.A6.eLpNorm_varNorm_two_le_sqSum`) and the square
function of a family of IW multipliers is computed by Plancherel
(`Work.KMTPlan.A6.tsum_eLpNorm_sq_iwConv_le`), while the input `mdlG` is controlled in `ℓ²` by
`Work.KMTPlan.A6.MdlGL2Bound`. -/
/-- Associativity of `ENNReal.ofReal` products. -/
private theorem ofReal_mul_mul (x y : ℝ) (hx : 0 ≤ x) (hy : 0 ≤ y) (X : ENNReal) :
    ENNReal.ofReal x * (ENNReal.ofReal y * X) = ENNReal.ofReal (x * y) * X := by
  rw [← mul_assoc, ← ENNReal.ofReal_mul hx]

theorem mdlSliceLinGOne_ne (P : Polynomial ℤ) (hd : 2 ≤ P.natDegree) (r : NNReal) (hr : 2 < r)
    (C₀ : ℕ) (hC₀ : 1 ≤ C₀) (A : ℝ) (hA : 1 ≤ A) (j₂ : ℤ)
    (hj₂ : j₂ ∈ ({0, 1} : Finset ℤ)) :
    ∃ ρ₀ : ℝ, 0 < ρ₀ ∧
      ∀ ρ : ℝ, 0 < ρ → ρ ≤ ρ₀ → ∃ K : NNReal → NNReal,
        ∀ (a : ℕ → NNReal) (Λ : NNReal) (l₁ l₂ k₂ : ℕ) (t : ℝ) (g : ℤ → ℂ),
          1 < Λ → PointwiseErgodicTheorems.Lacunary Λ a → (∀ n : ℕ, 1 ≤ a n) →
          t ∈ Set.Icc (1 / 2 : ℝ) 1 → (k₂ ≠ 0 ∨ j₂ = 1) →
          MeasureTheory.eLpNorm (fun x : ℤ => PointwiseErgodicTheorems.variationalNorm r
              (fun n : ℕ =>
                if Work.KMTPlan.A6.mdlCore ρ C₀ a l₁ l₂ 0 k₂ n then
                  Work.KMTAreas.A7.Tle ρ l₂
                    (Work.KMTPlan.A6.varphitildeNtj P (Nat.floor (a n)) k₂ j₂ t)
                    (Work.KMTPlan.A6.mdlG ρ P
                      (Work.KMTAreas.A7.uScale ρ (max (max l₁ l₂) k₂)) l₂ g) x
                else 0))
            2 MeasureTheory.Measure.count
            ≤ (K Λ : ENNReal) *
                ENNReal.ofReal (Work.KMTAreas.A7.lossWeight A ρ l₁ l₂ 0 k₂) *
                MeasureTheory.eLpNorm g 2 MeasureTheory.Measure.count := by
  classical
  obtain ⟨Csf, hCsfpos, hsf⟩ := Work.KMTPlan.A6.eLpNorm_varNorm_two_le_sqSum r hr
  refine ⟨1, by norm_num, ?_⟩
  intro ρ hρ hρ1
  obtain ⟨Cg, hCgpos, hCg⟩ := Work.KMTPlan.A6.MdlGL2Bound ρ hρ hρ1 P hd
  have hper : ∀ Λ : NNReal, 1 < Λ → ∃ C : NNReal,
      ∀ (a : ℕ → NNReal) (l₁ l₂ k₂ : ℕ) (t : ℝ) (g : ℤ → ℂ),
        PointwiseErgodicTheorems.Lacunary Λ a → (∀ n : ℕ, 1 ≤ a n) →
        t ∈ Set.Icc (1 / 2 : ℝ) 1 → (k₂ ≠ 0 ∨ j₂ = 1) →
        MeasureTheory.eLpNorm (fun x : ℤ => PointwiseErgodicTheorems.variationalNorm r
            (fun n : ℕ =>
              if Work.KMTPlan.A6.mdlCore ρ C₀ a l₁ l₂ 0 k₂ n then
                Work.KMTAreas.A7.Tle ρ l₂
                  (Work.KMTPlan.A6.varphitildeNtj P (Nat.floor (a n)) k₂ j₂ t)
                  (Work.KMTPlan.A6.mdlG ρ P
                    (Work.KMTAreas.A7.uScale ρ (max (max l₁ l₂) k₂)) l₂ g) x
              else 0))
          2 MeasureTheory.Measure.count
          ≤ (C : ENNReal) *
              ENNReal.ofReal (Work.KMTAreas.A7.lossWeight A ρ l₁ l₂ 0 k₂) *
              MeasureTheory.eLpNorm g 2 MeasureTheory.Measure.count := by
    intro Λ hΛ
    obtain ⟨W, hW⟩ := Work.KMTPlan.A6.iwSymbolTleSqSumGen P hd ρ hρ hρ1 C₀ hC₀ Λ hΛ
    set C : NNReal := ⟨max (Csf * (W : ℝ) * Cg) 1, le_trans zero_le_one (le_max_right _ _)⟩
      with hCdef
    have hCval : (C : ℝ) = max (Csf * (W : ℝ) * Cg) 1 := rfl
    have hCne : (C : ENNReal) ≠ 0 := by
      rw [← ENNReal.ofReal_coe_nnreal, hCval]
      exact (ENNReal.ofReal_pos.mpr (lt_of_lt_of_le zero_lt_one (le_max_right _ _))).ne'
    refine ⟨C, ?_⟩
    intro a l₁ l₂ k₂ t g ha ha1 ht hne
    have hj₂' : j₂ ∈ ({-1, 0, 1} : Finset ℤ) := by
      simp only [Finset.mem_insert, Finset.mem_singleton] at hj₂ ⊢
      tauto
    have hbridge : ∀ n : ℕ, (if Work.KMTPlan.A6.mdlCore ρ C₀ a l₁ l₂ 0 k₂ n then
          Work.KMTPlan.A6.varphitildeNtj P (Nat.floor (a n)) k₂ j₂ t else 0)
        = (fun ξ : ℝ => if Work.KMTPlan.A6.mdlCore ρ C₀ a l₁ l₂ 0 k₂ n then
            Work.KMTPlan.A6.varphitildeNtj P (Nat.floor (a n)) k₂ j₂ t ξ else 0) := by
      intro n
      funext ξ
      by_cases h : Work.KMTPlan.A6.mdlCore ρ C₀ a l₁ l₂ 0 k₂ n <;> simp [h]
    have hsym : ∀ θ : Work.Analysis.IonescuWainger.Circle,
        (∑' n : ℕ, ‖Work.Analysis.IonescuWainger.iwSymbolSet
            (Work.Analysis.IonescuWainger.iwArithFreqs ρ l₂)
            (Work.Analysis.IonescuWainger.periodize
              (fun ξ : ℝ => if Work.KMTPlan.A6.mdlCore ρ C₀ a l₁ l₂ 0 k₂ n then
                Work.KMTPlan.A6.varphitildeNtj P (Nat.floor (a n)) k₂ j₂ t ξ else 0)) θ‖ₑ ^ (2 : ℝ))
          ≤ (W : ENNReal) ^ 2 := by
      intro θ
      have h := hW a l₁ l₂ 0 k₂ t j₂ ha ha1 ht hj₂' hne θ
      simpa only [hbridge] using h
    by_cases htop : MeasureTheory.eLpNorm g 2 MeasureTheory.Measure.count = ⊤
    · have hlwpos : (0 : ℝ) < Work.KMTAreas.A7.lossWeight A ρ l₁ l₂ 0 k₂ :=
        lt_of_lt_of_le zero_lt_one (one_le_lossWeight (by linarith) hρ.le l₁ l₂ 0 k₂)
      have hlwne : ENNReal.ofReal (Work.KMTAreas.A7.lossWeight A ρ l₁ l₂ 0 k₂) ≠ 0 :=
        ENNReal.ofReal_ne_zero_iff.mpr hlwpos
      rw [htop, ENNReal.mul_top (mul_ne_zero hCne hlwne)]
      exact le_top
    · have hgmem : MeasureTheory.MemLp g 2 MeasureTheory.Measure.count :=
        memLp_two_count_of_ne_top' htop
      have hLle : l₂ ≤ max (max l₁ l₂) k₂ :=
        le_trans (le_max_right l₁ l₂) (le_max_left _ _)
      have hmle := hCg (max (max l₁ l₂) k₂) l₂ hLle g
      have hmmem : MeasureTheory.MemLp
          (Work.KMTPlan.A6.mdlG ρ P (Work.KMTAreas.A7.uScale ρ (max (max l₁ l₂) k₂)) l₂ g)
          2 MeasureTheory.Measure.count :=
        MeasureTheory.memLp_iff.mpr (lt_of_le_of_lt hmle
            (ENNReal.mul_lt_top ENNReal.ofReal_lt_top (lt_top_iff_ne_top.mpr htop)))
      have hplan := Work.KMTPlan.A6.tsum_eLpNorm_sq_iwConv_le
        (Work.Analysis.IonescuWainger.iwArithFreqs ρ l₂)
        (fun n => fun ξ : ℝ => if Work.KMTPlan.A6.mdlCore ρ C₀ a l₁ l₂ 0 k₂ n then
          Work.KMTPlan.A6.varphitildeNtj P (Nat.floor (a n)) k₂ j₂ t ξ else 0)
        (Work.KMTPlan.A6.mdlG ρ P (Work.KMTAreas.A7.uScale ρ (max (max l₁ l₂) k₂)) l₂ g)
        hmmem W (by simpa only [hbridge] using hsym)
      have hfam : ∀ n : ℕ,
          Work.Analysis.IWMultiplier.iwConv (Work.Analysis.IonescuWainger.iwArithFreqs ρ l₂)
              (Work.Analysis.IonescuWainger.periodize
                (fun ξ : ℝ => if Work.KMTPlan.A6.mdlCore ρ C₀ a l₁ l₂ 0 k₂ n then
                  Work.KMTPlan.A6.varphitildeNtj P (Nat.floor (a n)) k₂ j₂ t ξ else 0))
              (Work.KMTPlan.A6.mdlG ρ P (Work.KMTAreas.A7.uScale ρ (max (max l₁ l₂) k₂)) l₂ g)
            = (fun x : ℤ => if Work.KMTPlan.A6.mdlCore ρ C₀ a l₁ l₂ 0 k₂ n then
                Work.KMTAreas.A7.Tle ρ l₂
                  (Work.KMTPlan.A6.varphitildeNtj P (Nat.floor (a n)) k₂ j₂ t)
                  (Work.KMTPlan.A6.mdlG ρ P
                    (Work.KMTAreas.A7.uScale ρ (max (max l₁ l₂) k₂)) l₂ g) x
              else 0) := by
        intro n
        exact Work.KMTAreas.A7.Tle_ite ρ l₂
          (Work.KMTPlan.A6.mdlCore ρ C₀ a l₁ l₂ 0 k₂ n)
          (φ := Work.KMTPlan.A6.varphitildeNtj P (Nat.floor (a n)) k₂ j₂ t)
          (f := Work.KMTPlan.A6.mdlG ρ P
            (Work.KMTAreas.A7.uScale ρ (max (max l₁ l₂) k₂)) l₂ g)
      have hconst : ENNReal.ofReal (Csf * (W : ℝ) * (Cg * (1 + (l₂ : ℝ))))
          ≤ (C : ENNReal) * ENNReal.ofReal (Work.KMTAreas.A7.lossWeight A ρ l₁ l₂ 0 k₂) := by
        have hmax : Csf * (W : ℝ) * (Cg * (1 + (l₂ : ℝ)))
            ≤ (C : ℝ) * Work.KMTAreas.A7.lossWeight A ρ l₁ l₂ 0 k₂ := by
          rw [hCval, show Csf * (W : ℝ) * (Cg * (1 + (l₂ : ℝ)))
              = (Csf * (W : ℝ) * Cg) * (1 + (l₂ : ℝ)) by ring]
          exact mul_le_mul (le_max_left _ _) (one_add_le_lossWeight hA hρ.le l₁ l₂ 0 k₂)
            (by positivity) (le_trans zero_le_one (le_max_right _ _))
        calc ENNReal.ofReal (Csf * (W : ℝ) * (Cg * (1 + (l₂ : ℝ))))
            ≤ ENNReal.ofReal ((C : ℝ) * Work.KMTAreas.A7.lossWeight A ρ l₁ l₂ 0 k₂) :=
              ENNReal.ofReal_le_ofReal hmax
          _ = (C : ENNReal) * ENNReal.ofReal (Work.KMTAreas.A7.lossWeight A ρ l₁ l₂ 0 k₂) := by
              rw [ENNReal.ofReal_mul (by positivity), ENNReal.ofReal_coe_nnreal]
      have hbound : MeasureTheory.eLpNorm (fun x : ℤ => PointwiseErgodicTheorems.variationalNorm r
            (fun n : ℕ =>
              if Work.KMTPlan.A6.mdlCore ρ C₀ a l₁ l₂ 0 k₂ n then
                Work.KMTAreas.A7.Tle ρ l₂
                  (Work.KMTPlan.A6.varphitildeNtj P (Nat.floor (a n)) k₂ j₂ t)
                  (Work.KMTPlan.A6.mdlG ρ P
                    (Work.KMTAreas.A7.uScale ρ (max (max l₁ l₂) k₂)) l₂ g) x
              else 0)) 2 MeasureTheory.Measure.count
          ≤ ENNReal.ofReal (Csf * (W : ℝ) * (Cg * (1 + (l₂ : ℝ)))) *
              MeasureTheory.eLpNorm g 2 MeasureTheory.Measure.count := by
        calc MeasureTheory.eLpNorm (fun x : ℤ => PointwiseErgodicTheorems.variationalNorm r
              (fun n : ℕ =>
                if Work.KMTPlan.A6.mdlCore ρ C₀ a l₁ l₂ 0 k₂ n then
                  Work.KMTAreas.A7.Tle ρ l₂
                    (Work.KMTPlan.A6.varphitildeNtj P (Nat.floor (a n)) k₂ j₂ t)
                    (Work.KMTPlan.A6.mdlG ρ P
                      (Work.KMTAreas.A7.uScale ρ (max (max l₁ l₂) k₂)) l₂ g) x
                else 0)) 2 MeasureTheory.Measure.count
            ≤ ENNReal.ofReal Csf *
                (∑' n : ℕ, (MeasureTheory.eLpNorm
                  (fun x : ℤ =>
                    if Work.KMTPlan.A6.mdlCore ρ C₀ a l₁ l₂ 0 k₂ n then
                      Work.KMTAreas.A7.Tle ρ l₂
                        (Work.KMTPlan.A6.varphitildeNtj P (Nat.floor (a n)) k₂ j₂ t)
                        (Work.KMTPlan.A6.mdlG ρ P
                          (Work.KMTAreas.A7.uScale ρ (max (max l₁ l₂) k₂)) l₂ g) x
                    else 0) 2 MeasureTheory.Measure.count) ^ (2 : ℝ)) ^ (1 / 2 : ℝ) :=
              hsf (fun n x => if Work.KMTPlan.A6.mdlCore ρ C₀ a l₁ l₂ 0 k₂ n then
                  Work.KMTAreas.A7.Tle ρ l₂
                    (Work.KMTPlan.A6.varphitildeNtj P (Nat.floor (a n)) k₂ j₂ t)
                    (Work.KMTPlan.A6.mdlG ρ P
                      (Work.KMTAreas.A7.uScale ρ (max (max l₁ l₂) k₂)) l₂ g) x
                else 0)
          _ = ENNReal.ofReal Csf *
                (∑' n : ℕ, (MeasureTheory.eLpNorm
                  (Work.Analysis.IWMultiplier.iwConv (Work.Analysis.IonescuWainger.iwArithFreqs ρ l₂)
                    (Work.Analysis.IonescuWainger.periodize
                      (fun ξ : ℝ => if Work.KMTPlan.A6.mdlCore ρ C₀ a l₁ l₂ 0 k₂ n then
                        Work.KMTPlan.A6.varphitildeNtj P (Nat.floor (a n)) k₂ j₂ t ξ else 0))
                    (Work.KMTPlan.A6.mdlG ρ P
                      (Work.KMTAreas.A7.uScale ρ (max (max l₁ l₂) k₂)) l₂ g))
                  2 MeasureTheory.Measure.count) ^ (2 : ℝ)) ^ (1 / 2 : ℝ) := by
              simp only [hfam]
          _ ≤ ENNReal.ofReal Csf * ((W : ENNReal) *
                MeasureTheory.eLpNorm (Work.KMTPlan.A6.mdlG ρ P
                  (Work.KMTAreas.A7.uScale ρ (max (max l₁ l₂) k₂)) l₂ g)
                  2 MeasureTheory.Measure.count) :=
              mul_le_mul_right hplan _
          _ ≤ ENNReal.ofReal Csf * ((W : ENNReal) *
                (ENNReal.ofReal (Cg * (1 + (l₂ : ℝ))) *
                  MeasureTheory.eLpNorm g 2 MeasureTheory.Measure.count)) :=
              mul_le_mul_right (mul_le_mul_right hmle _) _
          _ = ENNReal.ofReal Csf * (ENNReal.ofReal (W : ℝ) *
                (ENNReal.ofReal (Cg * (1 + (l₂ : ℝ))) *
                  MeasureTheory.eLpNorm g 2 MeasureTheory.Measure.count)) := by
              rw [ENNReal.ofReal_coe_nnreal]
          _ = ENNReal.ofReal (Csf * (W : ℝ)) *
                (ENNReal.ofReal (Cg * (1 + (l₂ : ℝ))) *
                  MeasureTheory.eLpNorm g 2 MeasureTheory.Measure.count) := by
              rw [ofReal_mul_mul Csf (W : ℝ) (le_of_lt hCsfpos) W.coe_nonneg]
          _ = ENNReal.ofReal (Csf * (W : ℝ) * (Cg * (1 + (l₂ : ℝ)))) *
                MeasureTheory.eLpNorm g 2 MeasureTheory.Measure.count := by
              rw [ofReal_mul_mul (Csf * (W : ℝ)) (Cg * (1 + (l₂ : ℝ))) (by positivity)
                (by positivity)]
      exact hbound.trans (mul_le_mul_of_nonneg_right hconst (by positivity))
  refine ⟨fun Λ => if h : 1 < Λ then Classical.choose (hper Λ h) else 1, ?_⟩
  intro a Λ l₁ l₂ k₂ t g hΛ ha ha1 ht hne
  have hC := (Classical.choose_spec (hper Λ hΛ)) a l₁ l₂ k₂ t g ha ha1 ht hne
  simpa only [dif_pos hΛ] using hC

/-! ## The exceptional pair `(j₂, k₂) = (0,0)`

Here the bump is the *ball* `φ̃_{N,t,0,0} = η(N^d ·) · e(PevalR P (N t) ·)`, whose value at the
frequency origin is `1` at every scale.  Consequently the pointwise square sum
`∑'_n ‖iwSymbolSet (iwArithFreqs ρ l₂) (periodize ψ_n) θ‖²` is *infinite* at `θ = 0`, the
square-function route of `mdlSliceLinGOne_ne` is unavailable, and the family is instead the
lacunary family of *modulated low-pass filters* (`Tle ρ 0 ψ = convOp (cw ψ)`,
`Tle_zero_eq_convOp_cw`): with `K = 𝓕 kmtEta` (a fixed Schwartz kernel),
`σ_n = 2^{d·logN ⌊a n⌋}` and `c_n = PevalR P (⌊a n⌋ t)/σ_n`, the family is
`n ↦ g * dilate(K(· + c_n), σ_n)`, i.e. *window averages of `g` at the moving positions*
`PevalR P (⌊a n⌋ t)` -- the non-conventional (polynomial-shift) low-pass variational estimate.

This is the workspace's documented central open crux (`Work.KMTPlan.A6.MdlSliceLowpassG`,
reduced there to `Work.KMTAreas.A7Hi2.SupPiece` and `Work.KMTAreas.A7Hi2.ChainPieceCanonical`
together with the height-`0` carrier `Work.KMTPlan.A6.MdlSliceLowpassGZero`); it is isolated here
as the single obligation of the target. -/
def MdlSliceGZeroSlice (P : Polynomial ℤ) (r : NNReal) (C₀ : ℕ) : Prop :=
  ∃ A : ℝ, 0 ≤ A ∧ ∃ ρ₀ : ℝ, 0 < ρ₀ ∧
    ∀ ρ : ℝ, 0 < ρ → ρ ≤ ρ₀ → ∃ K : NNReal → NNReal,
      ∀ (a : ℕ → NNReal) (Λ : NNReal) (l₁ l₂ : ℕ) (t : ℝ) (g : ℤ → ℂ),
        1 < Λ → PointwiseErgodicTheorems.Lacunary Λ a → (∀ n : ℕ, 1 ≤ a n) →
        t ∈ Set.Icc (1 / 2 : ℝ) 1 →
        MeasureTheory.eLpNorm (fun x : ℤ => PointwiseErgodicTheorems.variationalNorm r
            (fun n : ℕ =>
              if Work.KMTPlan.A6.mdlCore ρ C₀ a l₁ l₂ 0 0 n then
                Work.KMTAreas.A7.Tle ρ l₂
                  (Work.KMTPlan.A6.varphitildeNtj P (Nat.floor (a n)) 0 0 t)
                  (Work.KMTPlan.A6.mdlG ρ P
                    (Work.KMTAreas.A7.uScale ρ (max (max l₁ l₂) 0)) l₂ g) x
              else 0))
          2 MeasureTheory.Measure.count
          ≤ (K Λ : ENNReal) *
              ENNReal.ofReal (Work.KMTAreas.A7.lossWeight A ρ l₁ l₂ 0 0) *
              MeasureTheory.eLpNorm g 2 MeasureTheory.Measure.count

/-- **The reduction of the target to the exceptional slice.**  For `j₂ = 1` every `k₂` is covered
by `mdlSliceLinGOne_ne`; for `j₂ = 0` the case `k₂ ≠ 0` is again covered by it, and only
`k₂ = 0` remains, which is `MdlSliceGZeroSlice`. -/
theorem mdlSliceLinGOne_of_gzero (P : Polynomial ℤ) (hd : 2 ≤ P.natDegree) (r : NNReal)
    (hr : 2 < r) (C₀ : ℕ) (hC₀ : 1 ≤ C₀) (j₂ : ℤ) (hj₂ : j₂ ∈ ({0, 1} : Finset ℤ))
    (hGZ : MdlSliceGZeroSlice P r C₀) :
    ∃ A : ℝ, 0 ≤ A ∧ ∃ ρ₀ : ℝ, 0 < ρ₀ ∧
      ∀ ρ : ℝ, 0 < ρ → ρ ≤ ρ₀ → ∃ K : NNReal → NNReal,
        ∀ (a : ℕ → NNReal) (Λ : NNReal) (l₁ l₂ k₂ : ℕ) (t : ℝ) (g : ℤ → ℂ),
          1 < Λ → PointwiseErgodicTheorems.Lacunary Λ a → (∀ n : ℕ, 1 ≤ a n) →
          t ∈ Set.Icc (1 / 2 : ℝ) 1 →
          MeasureTheory.eLpNorm (fun x : ℤ => PointwiseErgodicTheorems.variationalNorm r
              (fun n : ℕ =>
                if Work.KMTPlan.A6.mdlCore ρ C₀ a l₁ l₂ 0 k₂ n then
                  Work.KMTAreas.A7.Tle ρ l₂
                    (Work.KMTPlan.A6.varphitildeNtj P (Nat.floor (a n)) k₂ j₂ t)
                    (Work.KMTPlan.A6.mdlG ρ P
                      (Work.KMTAreas.A7.uScale ρ (max (max l₁ l₂) k₂)) l₂ g) x
                else 0))
            2 MeasureTheory.Measure.count
            ≤ (K Λ : ENNReal) *
                ENNReal.ofReal (Work.KMTAreas.A7.lossWeight A ρ l₁ l₂ 0 k₂) *
                MeasureTheory.eLpNorm g 2 MeasureTheory.Measure.count := by
  classical
  have hj01 : j₂ = 0 ∨ j₂ = 1 := by
    simpa [Finset.mem_insert, Finset.mem_singleton] using hj₂
  rcases hj01 with h0 | h1
  · subst h0
    obtain ⟨A₂, hA₂, ρ₀₂, hρ₀₂, hlow⟩ := hGZ
    set Am : ℝ := max 1 A₂ with hAmdef
    have hAm1 : (1 : ℝ) ≤ Am := le_max_left _ _
    have hAm0 : (0 : ℝ) ≤ Am := le_trans zero_le_one hAm1
    obtain ⟨ρ₀₁, hρ₀₁, hne⟩ :=
      mdlSliceLinGOne_ne P hd r hr C₀ hC₀ Am hAm1 0 (by decide)
    refine ⟨Am, hAm0, min ρ₀₁ ρ₀₂, lt_min hρ₀₁ hρ₀₂, ?_⟩
    intro ρ hρ hρmin
    obtain ⟨K₁, hK₁⟩ := hne ρ hρ (le_trans hρmin (min_le_left _ _))
    obtain ⟨K₂, hK₂⟩ := hlow ρ hρ (le_trans hρmin (min_le_right _ _))
    refine ⟨fun Λ => max (K₁ Λ) (K₂ Λ), ?_⟩
    intro a Λ l₁ l₂ k₂ t g hΛ ha ha1 ht
    by_cases hk : k₂ = 0
    · subst hk
      have h := hK₂ a Λ l₁ l₂ t g hΛ ha ha1 ht
      have hmono : ENNReal.ofReal (Work.KMTAreas.A7.lossWeight A₂ ρ l₁ l₂ 0 0)
          ≤ ENNReal.ofReal (Work.KMTAreas.A7.lossWeight Am ρ l₁ l₂ 0 0) :=
        ENNReal.ofReal_le_ofReal (lossWeight_mono' (le_max_right (1 : ℝ) A₂) hρ.le l₁ l₂ 0 0)
      have hKle : (K₂ Λ : ENNReal) ≤ ((max (K₁ Λ) (K₂ Λ) : NNReal) : ENNReal) := by
        exact_mod_cast le_max_right (K₁ Λ) (K₂ Λ)
      refine h.trans ?_
      exact mul_le_mul_of_nonneg_right
        (mul_le_mul hKle hmono (by positivity) (by positivity)) (by positivity)
    · have h := hK₁ a Λ l₁ l₂ k₂ t g hΛ ha ha1 ht (Or.inl hk)
      have hKle : (K₁ Λ : ENNReal) ≤ ((max (K₁ Λ) (K₂ Λ) : NNReal) : ENNReal) := by
        exact_mod_cast le_max_left (K₁ Λ) (K₂ Λ)
      refine h.trans ?_
      exact mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_right hKle (by positivity))
        (by positivity)
  · subst h1
    obtain ⟨ρ₀₁, hρ₀₁, hne⟩ :=
      mdlSliceLinGOne_ne P hd r hr C₀ hC₀ 1 (le_refl 1) 1 (by decide)
    refine ⟨1, by norm_num, ρ₀₁, hρ₀₁, ?_⟩
    intro ρ hρ hρ1
    obtain ⟨K₁, hK₁⟩ := hne ρ hρ hρ1
    exact ⟨K₁, fun a Λ l₁ l₂ k₂ t g hΛ ha ha1 ht =>
      hK₁ a Λ l₁ l₂ k₂ t g hΛ ha ha1 ht (Or.inr rfl)⟩

/-- **The `l₂ = 0` half of the exceptional slice** (delegated as
`Submission/Work/KMTPlan/A6/MdlSliceGZeroLow.lean`, PROVED): the `(j₂,k₂) = (0,0)` case of the
target at arithmetic height `l₂ = 0`.  The family is then the pure height-`0` multiplier family
`n ↦ Tle ρ 0 (φ̃_{⌊a n⌋,t}) G` on the *fixed* input `G = mdlG ρ P u 0 g`; the arithmetic-free
`(lin-2)` estimate at height `0` (`Work.KMTAreas.A7.LoGLinVarClipped`, which contains the
unmodulated low-pass `A7G.plainBumpVarG`, the modulated deviation and the Farey/narrow split)
bounds it, and `‖G‖₂ ≤ C‖g‖₂` comes from `eLpNorm_piExact_le_of_height_le_one`. -/
def MdlSliceGZeroLowSlice (P : Polynomial ℤ) (r : NNReal) (C₀ : ℕ) : Prop :=
  ∃ A : ℝ, 0 ≤ A ∧ ∃ ρ₀ : ℝ, 0 < ρ₀ ∧
    ∀ ρ : ℝ, 0 < ρ → ρ ≤ ρ₀ → ∃ K : NNReal → NNReal,
      ∀ (a : ℕ → NNReal) (Λ : NNReal) (l₁ : ℕ) (t : ℝ) (g : ℤ → ℂ),
        1 < Λ → PointwiseErgodicTheorems.Lacunary Λ a → (∀ n : ℕ, 1 ≤ a n) →
        t ∈ Set.Icc (1 / 2 : ℝ) 1 →
        MeasureTheory.eLpNorm (fun x : ℤ => PointwiseErgodicTheorems.variationalNorm r
            (fun n : ℕ =>
              if Work.KMTPlan.A6.mdlCore ρ C₀ a l₁ 0 0 0 n then
                Work.KMTAreas.A7.Tle ρ 0
                  (Work.KMTPlan.A6.varphitildeNtj P (Nat.floor (a n)) 0 0 t)
                  (Work.KMTPlan.A6.mdlG ρ P
                    (Work.KMTAreas.A7.uScale ρ (max (max l₁ 0) 0)) 0 g) x
              else 0))
          2 MeasureTheory.Measure.count
          ≤ (K Λ : ENNReal) *
              ENNReal.ofReal (Work.KMTAreas.A7.lossWeight A ρ l₁ 0 0 0) *
              MeasureTheory.eLpNorm g 2 MeasureTheory.Measure.count

/-- **The `l₂ ≥ 1` half of the exceptional slice** (delegated as
`Submission/Work/KMTPlan/A6/MdlSliceGZeroHigh.lean`).  Here the `≤ l₂` multiplier composed with
the narrow exact-height projection is the *exact-height* multiplier `Tex ρ l₂` (`tm_eq_tex`), which
is the family covered by the tree's `A7Hi`/`A7G` low-pass machinery. -/
def MdlSliceGZeroHighSlice (P : Polynomial ℤ) (r : NNReal) (C₀ : ℕ) : Prop :=
  ∃ A : ℝ, 0 ≤ A ∧ ∃ ρ₀ : ℝ, 0 < ρ₀ ∧
    ∀ ρ : ℝ, 0 < ρ → ρ ≤ ρ₀ → ∃ K : NNReal → NNReal,
      ∀ (a : ℕ → NNReal) (Λ : NNReal) (l₁ l₂ : ℕ) (t : ℝ) (g : ℤ → ℂ),
        1 ≤ l₂ → 1 < Λ → PointwiseErgodicTheorems.Lacunary Λ a → (∀ n : ℕ, 1 ≤ a n) →
        t ∈ Set.Icc (1 / 2 : ℝ) 1 →
        MeasureTheory.eLpNorm (fun x : ℤ => PointwiseErgodicTheorems.variationalNorm r
            (fun n : ℕ =>
              if Work.KMTPlan.A6.mdlCore ρ C₀ a l₁ l₂ 0 0 n then
                Work.KMTAreas.A7.Tle ρ l₂
                  (Work.KMTPlan.A6.varphitildeNtj P (Nat.floor (a n)) 0 0 t)
                  (Work.KMTPlan.A6.mdlG ρ P
                    (Work.KMTAreas.A7.uScale ρ (max (max l₁ l₂) 0)) l₂ g) x
              else 0))
          2 MeasureTheory.Measure.count
          ≤ (K Λ : ENNReal) *
              ENNReal.ofReal (Work.KMTAreas.A7.lossWeight A ρ l₁ l₂ 0 0) *
              MeasureTheory.eLpNorm g 2 MeasureTheory.Measure.count

/-- **The exceptional slice from its two halves** (`l₂ = 0` and `l₂ ≥ 1`). -/
theorem mdlSliceGZeroSlice_of_pieces (P : Polynomial ℤ) (r : NNReal) (C₀ : ℕ)
    (hLow : MdlSliceGZeroLowSlice P r C₀) (hHigh : MdlSliceGZeroHighSlice P r C₀) :
    MdlSliceGZeroSlice P r C₀ := by
  obtain ⟨A₁, hA₁, ρ₀₁, hρ₀₁, hlow⟩ := hLow
  obtain ⟨A₂, hA₂, ρ₀₂, hρ₀₂, hhigh⟩ := hHigh
  refine ⟨max A₁ A₂, le_trans hA₁ (le_max_left _ _), min ρ₀₁ ρ₀₂, lt_min hρ₀₁ hρ₀₂, ?_⟩
  intro ρ hρ hρmin
  obtain ⟨K₁, hK₁⟩ := hlow ρ hρ (le_trans hρmin (min_le_left _ _))
  obtain ⟨K₂, hK₂⟩ := hhigh ρ hρ (le_trans hρmin (min_le_right _ _))
  refine ⟨fun Λ => max (K₁ Λ) (K₂ Λ), ?_⟩
  intro a Λ l₁ l₂ t g hΛ ha ha1 ht
  by_cases hl₂ : l₂ = 0
  · subst hl₂
    have h := hK₁ a Λ l₁ t g hΛ ha ha1 ht
    have hKle : (K₁ Λ : ENNReal) ≤ ((max (K₁ Λ) (K₂ Λ) : NNReal) : ENNReal) := by
      exact_mod_cast le_max_left (K₁ Λ) (K₂ Λ)
    have hwle : ENNReal.ofReal (Work.KMTAreas.A7.lossWeight A₁ ρ l₁ 0 0 0)
        ≤ ENNReal.ofReal (Work.KMTAreas.A7.lossWeight (max A₁ A₂) ρ l₁ 0 0 0) :=
      ENNReal.ofReal_le_ofReal (lossWeight_mono' (le_max_left A₁ A₂) hρ.le l₁ 0 0 0)
    refine h.trans ?_
    exact mul_le_mul_of_nonneg_right
      (mul_le_mul hKle hwle (by positivity) (by positivity)) (by positivity)
  · have hl₂1 : 1 ≤ l₂ := Nat.one_le_iff_ne_zero.mpr hl₂
    have h := hK₂ a Λ l₁ l₂ t g hl₂1 hΛ ha ha1 ht
    have hKle : (K₂ Λ : ENNReal) ≤ ((max (K₁ Λ) (K₂ Λ) : NNReal) : ENNReal) := by
      exact_mod_cast le_max_right (K₁ Λ) (K₂ Λ)
    have hwle : ENNReal.ofReal (Work.KMTAreas.A7.lossWeight A₂ ρ l₁ l₂ 0 0)
        ≤ ENNReal.ofReal (Work.KMTAreas.A7.lossWeight (max A₁ A₂) ρ l₁ l₂ 0 0) :=
      ENNReal.ofReal_le_ofReal (lossWeight_mono' (le_max_right A₁ A₂) hρ.le l₁ l₂ 0 0)
    refine h.trans ?_
    exact mul_le_mul_of_nonneg_right
      (mul_le_mul hKle hwle (by positivity) (by positivity)) (by positivity)

/-! ## The target -/

end

end Work.KMTPlan.A6
