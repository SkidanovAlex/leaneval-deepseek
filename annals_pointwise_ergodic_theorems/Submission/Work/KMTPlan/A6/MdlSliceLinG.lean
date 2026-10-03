import Mathlib
import Submission.Work.KMTPlan.A6.eLpNorm_varNorm_two_le_sqSum
import Submission.Work.KMTPlan.A6.MdlGL2Bound
import Submission.Work.KMTPlan.A6.iwSymbolTleSqSumGen
import Submission.Work.KMTPlan.A6.MdlSliceLowpassGDecim
-- 2026-10-02: the crux-free twin of `MdlSliceLowpassG`, used at line ~291 below (see the note
-- `NOTES_MdlCoreGainEstimate_STRUCTURAL_SESSION.md`).

set_option autoImplicit false
set_option maxHeartbeats 4000000

namespace Work.KMTPlan.A6

open MeasureTheory Polynomial Finset
open scoped ENNReal NNReal BigOperators
open PointwiseErgodicTheorems Submission.PointwiseErgodicTheorems

noncomputable section

/-! ## The symbol family and the family of the target -/

/-- The clipped symbol family `n ↦ 1_{mdlCore n} · φ̃_{⌊a n⌋,j₂,t}`. -/
def sliceSymb (P : Polynomial ℤ) (ρ : ℝ) (C₀ : ℕ) (a : ℕ → NNReal)
    (l₁ l₂ k₁ k₂ : ℕ) (j₂ : ℤ) (t : ℝ) : ℕ → ℝ → ℂ :=
  fun n => if Work.KMTPlan.A6.mdlCore ρ C₀ a l₁ l₂ k₁ k₂ n then
    Work.KMTPlan.A6.varphitildeNtj P (Nat.floor (a n)) k₂ j₂ t else 0

/-- The family of the target. -/
def sliceFam (P : Polynomial ℤ) (ρ : ℝ) (C₀ : ℕ) (a : ℕ → NNReal) (l₁ l₂ k₁ k₂ : ℕ)
    (j₂ : ℤ) (t : ℝ) (g : ℤ → ℂ) : ℕ → ℤ → ℂ :=
  fun n x => if Work.KMTPlan.A6.mdlCore ρ C₀ a l₁ l₂ k₁ k₂ n then
      Work.KMTAreas.A7.Tle ρ l₂ (Work.KMTPlan.A6.varphitildeNtj P (Nat.floor (a n)) k₂ j₂ t)
        (Work.KMTPlan.A6.mdlG ρ P (Work.KMTAreas.A7.uScale ρ (max (max l₁ l₂) (max k₁ k₂)))
          l₂ g) x
    else 0

/-- The family of the target is `Tle` of the clipped symbol family. -/
lemma sliceFam_eq (P : Polynomial ℤ) (ρ : ℝ) (C₀ : ℕ) (a : ℕ → NNReal) (l₁ l₂ k₁ k₂ : ℕ)
    (j₂ : ℤ) (t : ℝ) (g : ℤ → ℂ) :
    sliceFam P ρ C₀ a l₁ l₂ k₁ k₂ j₂ t g
      = fun n => Work.KMTAreas.A7.Tle ρ l₂ (sliceSymb P ρ C₀ a l₁ l₂ k₁ k₂ j₂ t n)
          (Work.KMTPlan.A6.mdlG ρ P (Work.KMTAreas.A7.uScale ρ (max (max l₁ l₂) (max k₁ k₂)))
            l₂ g) := by
  funext n x
  have hsym : (if Work.KMTPlan.A6.mdlCore ρ C₀ a l₁ l₂ k₁ k₂ n then
        Work.KMTPlan.A6.varphitildeNtj P (Nat.floor (a n)) k₂ j₂ t else 0)
      = fun ξ : ℝ => if Work.KMTPlan.A6.mdlCore ρ C₀ a l₁ l₂ k₁ k₂ n then
          Work.KMTPlan.A6.varphitildeNtj P (Nat.floor (a n)) k₂ j₂ t ξ else 0 := by
    funext ξ
    by_cases h : Work.KMTPlan.A6.mdlCore ρ C₀ a l₁ l₂ k₁ k₂ n <;> simp [h]
  simp only [sliceFam, sliceSymb]
  rw [hsym]
  exact (congrFun (Work.KMTAreas.A7.Tle_ite ρ l₂
    (Work.KMTPlan.A6.mdlCore ρ C₀ a l₁ l₂ k₁ k₂ n)
    (φ := Work.KMTPlan.A6.varphitildeNtj P (Nat.floor (a n)) k₂ j₂ t)
    (f := Work.KMTPlan.A6.mdlG ρ P
      (Work.KMTAreas.A7.uScale ρ (max (max l₁ l₂) (max k₁ k₂))) l₂ g)) x).symm

/-! ## Elementary facts about the loss weight -/

/-- `lossWeight` is at least `1`. -/
lemma one_le_lossWeight' (A ρ : ℝ) (hA : 0 ≤ A) (hρ : 0 ≤ ρ) (l₁ l₂ k₁ k₂ : ℕ) :
    1 ≤ Work.KMTAreas.A7.lossWeight A ρ l₁ l₂ k₁ k₂ := by
  have hL : (0 : ℝ) ≤ Work.KMTAreas.A7.lmaxR l₁ l₂ k₁ k₂ := by
    rw [Work.KMTAreas.A7.lmaxR]
    exact_mod_cast (show (0 : ℤ) ≤ Work.Analysis.EndVar.lmax l₁ l₂ (k₁ : ℤ) (k₂ : ℤ) from by
      simp only [Work.Analysis.EndVar.lmax]; omega)
  rw [Work.KMTAreas.A7.lossWeight]
  have h1 : (1 : ℝ) ≤ (1 + Work.KMTAreas.A7.lmaxR l₁ l₂ k₁ k₂) ^ A :=
    Real.one_le_rpow (by linarith) hA
  have h2 : (0 : ℝ) ≤ A * ρ * Work.KMTAreas.A7.lmaxR l₁ l₂ k₁ k₂ := by positivity
  have h3 : (1 : ℝ) ≤ (2 : ℝ) ^ (A * ρ * Work.KMTAreas.A7.lmaxR l₁ l₂ k₁ k₂) :=
    Real.one_le_rpow (by norm_num) h2
  calc (1 : ℝ) = 1 * 1 := by ring
    _ ≤ (1 + Work.KMTAreas.A7.lmaxR l₁ l₂ k₁ k₂) ^ A *
          (2 : ℝ) ^ (A * ρ * Work.KMTAreas.A7.lmaxR l₁ l₂ k₁ k₂) :=
        mul_le_mul h1 h3 (by norm_num) (by positivity)

/-- `lossWeight` dominates `1 + max l₁ l₂` (for exponent `A ≥ 1`). -/
lemma one_add_lmax_le_lossWeight {A ρ : ℝ} (hA : 1 ≤ A) (hρ : 0 ≤ ρ) (l₁ l₂ k₁ k₂ : ℕ) :
    1 + ((max (max l₁ l₂) (max k₁ k₂) : ℕ) : ℝ)
      ≤ Work.KMTAreas.A7.lossWeight A ρ l₁ l₂ k₁ k₂ := by
  have hL : Work.KMTAreas.A7.lmaxR l₁ l₂ k₁ k₂
      = ((max (max l₁ l₂) (max k₁ k₂) : ℕ) : ℝ) := by
    rw [Work.KMTAreas.A7.lmaxR, Work.Analysis.EndVar.lmax]
    norm_num [Nat.cast_max]
  have hL0 : (0 : ℝ) ≤ ((max (max l₁ l₂) (max k₁ k₂) : ℕ) : ℝ) := by positivity
  rw [Work.KMTAreas.A7.lossWeight, hL]
  have h2 : (1 : ℝ) ≤ (2 : ℝ) ^ (A * ρ * ((max (max l₁ l₂) (max k₁ k₂) : ℕ) : ℝ)) :=
    Real.one_le_rpow (by norm_num) (by positivity)
  have h1 : (1 : ℝ) + ((max (max l₁ l₂) (max k₁ k₂) : ℕ) : ℝ)
      ≤ (1 + ((max (max l₁ l₂) (max k₁ k₂) : ℕ) : ℝ)) ^ A := by
    have hbase : (1 : ℝ) ≤ 1 + ((max (max l₁ l₂) (max k₁ k₂) : ℕ) : ℝ) := by linarith
    calc (1 : ℝ) + ((max (max l₁ l₂) (max k₁ k₂) : ℕ) : ℝ)
        = (1 + ((max (max l₁ l₂) (max k₁ k₂) : ℕ) : ℝ)) ^ (1 : ℝ) := (Real.rpow_one _).symm
      _ ≤ (1 + ((max (max l₁ l₂) (max k₁ k₂) : ℕ) : ℝ)) ^ A :=
          Real.rpow_le_rpow_of_exponent_le hbase hA
  nlinarith [h1, h2]

/-- `lossWeight` is monotone in its exponent. -/
lemma lossWeight_mono {A A' ρ : ℝ} (hAA' : A ≤ A') (hρ : 0 ≤ ρ) (l₁ l₂ k₁ k₂ : ℕ) :
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
    have h1 : A * ρ ≤ A' * ρ := mul_le_mul_of_nonneg_right hAA' hρ
    exact mul_le_mul_of_nonneg_right h1 hL

/-! ## The non-low-pass case -/

/-- **The estimate in the case `k₂ ≠ 0 ∨ j₂ = 1`.**  The variational norm is dominated by the square
function of the family (`eLpNorm_varNorm_two_le_sqSum`), the square function of the family of
Ionescu--Wainger multipliers is computed by Plancherel from the pointwise square-sum of the symbols
(`tsum_eLpNorm_sq_iwConv_le`), the symbols are controlled by `iwSymbolTleSqSumGen`, and the input
`G = mdlG g` is controlled by `MdlGL2Bound`. -/
theorem sliceFam_bound_ne (P : Polynomial ℤ) (hd : 2 ≤ P.natDegree) (C₀ : ℕ) (hC₀ : 1 ≤ C₀)
    (R : NNReal) (hR : 2 < R) (A : ℝ) (hA1 : 1 ≤ A) (j₂ : ℤ)
    (hj₂ : j₂ ∈ ({-1, 0, 1} : Finset ℤ)) (Λ : NNReal) (hΛ : 1 < Λ) (ρ : ℝ) (hρ : 0 < ρ)
    (hρ1 : ρ ≤ 1) :
    ∃ C : NNReal, 0 < C ∧
      ∀ (a : ℕ → NNReal) (l₁ l₂ k₁ k₂ : ℕ) (t : ℝ) (g : ℤ → ℂ),
        PointwiseErgodicTheorems.Lacunary Λ a → (∀ n, 1 ≤ a n) →
        t ∈ Set.Icc (1 / 2 : ℝ) 1 → (k₂ ≠ 0 ∨ j₂ = 1) →
        MeasureTheory.eLpNorm (fun x : ℤ => PointwiseErgodicTheorems.variationalNorm R
            (fun n : ℕ => sliceFam P ρ C₀ a l₁ l₂ k₁ k₂ j₂ t g n x))
            2 MeasureTheory.Measure.count
          ≤ (C : ENNReal) * ENNReal.ofReal (Work.KMTAreas.A7.lossWeight A ρ l₁ l₂ k₁ k₂) *
              MeasureTheory.eLpNorm g 2 MeasureTheory.Measure.count := by
  classical
  obtain ⟨Csf, hCsfpos, hsf⟩ := Work.KMTPlan.A6.eLpNorm_varNorm_two_le_sqSum R hR
  obtain ⟨W, hW⟩ := Work.KMTPlan.A6.iwSymbolTleSqSumGen P hd ρ hρ hρ1 C₀ hC₀ Λ hΛ
  obtain ⟨Cg, hCgpos, hCg⟩ := Work.KMTPlan.A6.MdlGL2Bound ρ hρ hρ1 P hd
  let Cc : NNReal := ⟨max (Csf * (W : ℝ) * Cg) 1,
    le_trans zero_le_one (le_max_right (Csf * (W : ℝ) * Cg) 1)⟩
  have hCcpos : (0 : NNReal) < Cc := by
    rw [← NNReal.coe_lt_coe]
    simp only [Cc]
    push_cast
    exact lt_of_lt_of_le zero_lt_one (le_max_right _ _)
  refine ⟨Cc, hCcpos, ?_⟩
  intro a l₁ l₂ k₁ k₂ t g ha ha1 ht hne
  have hLW : (1 + (l₂ : ℝ)) ≤ Work.KMTAreas.A7.lossWeight A ρ l₁ l₂ k₁ k₂ := by
    refine le_trans ?_ (one_add_lmax_le_lossWeight hA1 hρ.le l₁ l₂ k₁ k₂)
    have h : (l₂ : ℝ) ≤ ((max (max l₁ l₂) (max k₁ k₂) : ℕ) : ℝ) := by
      exact_mod_cast (le_trans (le_max_right l₁ l₂) (le_max_left _ _))
    linarith
  -- the clipped symbol family, in the shape produced by `iwSymbolTleSqSumGen`
  set ψ : ℕ → ℝ → ℂ := fun n => if Work.KMTPlan.A6.mdlCore ρ C₀ a l₁ l₂ k₁ k₂ n then
      Work.KMTPlan.A6.varphitildeNtj P (Nat.floor (a n)) k₂ j₂ t else 0 with hψ
  by_cases htop : MeasureTheory.eLpNorm g 2 MeasureTheory.Measure.count = ⊤
  · have hCne : (Cc : ENNReal) ≠ 0 := (ENNReal.coe_pos.mpr hCcpos).ne'
    have hlwpos : (0 : ℝ) < Work.KMTAreas.A7.lossWeight A ρ l₁ l₂ k₁ k₂ :=
      lt_of_lt_of_le zero_lt_one (one_le_lossWeight' A ρ (by linarith) hρ.le l₁ l₂ k₁ k₂)
    have hlwne : ENNReal.ofReal (Work.KMTAreas.A7.lossWeight A ρ l₁ l₂ k₁ k₂) ≠ 0 :=
      ENNReal.ofReal_ne_zero_iff.mpr hlwpos
    have hne0 : (Cc : ENNReal) *
        ENNReal.ofReal (Work.KMTAreas.A7.lossWeight A ρ l₁ l₂ k₁ k₂) ≠ 0 := by
      intro h
      rcases mul_eq_zero.mp h with h1 | h1
      · exact hCne h1
      · exact hlwne h1
    rw [htop, ENNReal.mul_top hne0]
    exact le_top
  · have hgmem : MeasureTheory.MemLp g 2 MeasureTheory.Measure.count :=
      MeasureTheory.memLp_iff.mpr (lt_top_iff_ne_top.mpr htop)
    have hLle : l₂ ≤ max (max l₁ l₂) (max k₁ k₂) :=
      le_trans (le_max_right l₁ l₂) (le_max_left _ _)
    have hmle := hCg (max (max l₁ l₂) (max k₁ k₂)) l₂ hLle g
    have hmmem : MeasureTheory.MemLp
        (Work.KMTPlan.A6.mdlG ρ P (Work.KMTAreas.A7.uScale ρ (max (max l₁ l₂) (max k₁ k₂)))
          l₂ g) 2 MeasureTheory.Measure.count :=
      MeasureTheory.memLp_iff.mpr (lt_of_le_of_lt hmle
          (ENNReal.mul_lt_top ENNReal.ofReal_lt_top (lt_top_iff_ne_top.mpr htop)))
    have hsym : ∀ θ : Work.Analysis.IonescuWainger.Circle,
        (∑' n : ℕ, ‖Work.Analysis.IonescuWainger.iwSymbolSet
            (Work.Analysis.IonescuWainger.iwArithFreqs ρ l₂)
            (Work.Analysis.IonescuWainger.periodize (ψ n)) θ‖ₑ ^ (2 : ℝ))
          ≤ (W : ENNReal) ^ 2 :=
      fun θ => hW a l₁ l₂ k₁ k₂ t j₂ ha ha1 ht hj₂ hne θ
    have hplan := Work.KMTPlan.A6.tsum_eLpNorm_sq_iwConv_le
      (Work.Analysis.IonescuWainger.iwArithFreqs ρ l₂) ψ
      (Work.KMTPlan.A6.mdlG ρ P (Work.KMTAreas.A7.uScale ρ (max (max l₁ l₂) (max k₁ k₂)))
        l₂ g) hmmem W hsym
    have hfam : ∀ n : ℕ, sliceFam P ρ C₀ a l₁ l₂ k₁ k₂ j₂ t g n
        = Work.Analysis.IWMultiplier.iwConv
            (Work.Analysis.IonescuWainger.iwArithFreqs ρ l₂)
            (Work.Analysis.IonescuWainger.periodize (ψ n))
            (Work.KMTPlan.A6.mdlG ρ P
              (Work.KMTAreas.A7.uScale ρ (max (max l₁ l₂) (max k₁ k₂))) l₂ g) := by
      intro n
      have h := sliceFam_eq P ρ C₀ a l₁ l₂ k₁ k₂ j₂ t g
      rw [hψ]
      exact congrFun h n
    calc MeasureTheory.eLpNorm (fun x : ℤ => PointwiseErgodicTheorems.variationalNorm R
          (fun n : ℕ => sliceFam P ρ C₀ a l₁ l₂ k₁ k₂ j₂ t g n x))
          2 MeasureTheory.Measure.count
        ≤ ENNReal.ofReal Csf *
            (∑' n : ℕ, (MeasureTheory.eLpNorm
              (sliceFam P ρ C₀ a l₁ l₂ k₁ k₂ j₂ t g n)
              2 MeasureTheory.Measure.count) ^ (2 : ℝ)) ^ (1 / 2 : ℝ) :=
          hsf (fun n => sliceFam P ρ C₀ a l₁ l₂ k₁ k₂ j₂ t g n)
      _ = ENNReal.ofReal Csf *
            (∑' n : ℕ, (MeasureTheory.eLpNorm
              (Work.Analysis.IWMultiplier.iwConv
                (Work.Analysis.IonescuWainger.iwArithFreqs ρ l₂)
                (Work.Analysis.IonescuWainger.periodize (ψ n))
                (Work.KMTPlan.A6.mdlG ρ P
                  (Work.KMTAreas.A7.uScale ρ (max (max l₁ l₂) (max k₁ k₂))) l₂ g))
              2 MeasureTheory.Measure.count) ^ (2 : ℝ)) ^ (1 / 2 : ℝ) := by
          simp only [hfam]
      _ ≤ ENNReal.ofReal Csf * ((W : ENNReal) *
            MeasureTheory.eLpNorm (Work.KMTPlan.A6.mdlG ρ P
              (Work.KMTAreas.A7.uScale ρ (max (max l₁ l₂) (max k₁ k₂))) l₂ g)
              2 MeasureTheory.Measure.count) :=
          mul_le_mul_right hplan _
      _ ≤ ENNReal.ofReal Csf * ((W : ENNReal) *
            (ENNReal.ofReal (Cg * (1 + (l₂ : ℝ))) *
              MeasureTheory.eLpNorm g 2 MeasureTheory.Measure.count)) :=
          mul_le_mul_right (mul_le_mul_right hmle _) _
      _ = ENNReal.ofReal (Csf * (W : ℝ) * (Cg * (1 + (l₂ : ℝ)))) *
            MeasureTheory.eLpNorm g 2 MeasureTheory.Measure.count := by
          have key : ∀ x y z : ℝ, 0 ≤ x → 0 ≤ y → 0 ≤ z →
              ENNReal.ofReal x * (ENNReal.ofReal y * (ENNReal.ofReal z *
                  MeasureTheory.eLpNorm g 2 MeasureTheory.Measure.count))
                = ENNReal.ofReal (x * y * z) *
                  MeasureTheory.eLpNorm g 2 MeasureTheory.Measure.count := by
            intro x y z hx hy hz
            rw [show ENNReal.ofReal x * (ENNReal.ofReal y * (ENNReal.ofReal z *
                  MeasureTheory.eLpNorm g 2 MeasureTheory.Measure.count))
                = (ENNReal.ofReal x * ENNReal.ofReal y) * (ENNReal.ofReal z *
                    MeasureTheory.eLpNorm g 2 MeasureTheory.Measure.count) by ring,
              ← ENNReal.ofReal_mul hx,
              show ENNReal.ofReal (x * y) * (ENNReal.ofReal z *
                    MeasureTheory.eLpNorm g 2 MeasureTheory.Measure.count)
                = (ENNReal.ofReal (x * y) * ENNReal.ofReal z) *
                    MeasureTheory.eLpNorm g 2 MeasureTheory.Measure.count by ring,
              ← ENNReal.ofReal_mul (mul_nonneg hx hy)]
          rw [← ENNReal.ofReal_coe_nnreal (p := W)]
          exact key Csf (W : ℝ) (Cg * (1 + (l₂ : ℝ))) (le_of_lt hCsfpos) W.coe_nonneg (by positivity)
      _ ≤ (Cc : ENNReal) *
            ENNReal.ofReal (Work.KMTAreas.A7.lossWeight A ρ l₁ l₂ k₁ k₂) *
            MeasureTheory.eLpNorm g 2 MeasureTheory.Measure.count := by
          have hCcval : (Cc : ℝ) = max (Csf * (W : ℝ) * Cg) 1 := rfl
          have h1 : Csf * (W : ℝ) * Cg ≤ (Cc : ℝ) := by
            rw [hCcval]; exact le_max_left _ _
          have hscal : Csf * (W : ℝ) * (Cg * (1 + (l₂ : ℝ)))
              ≤ (Cc : ℝ) * Work.KMTAreas.A7.lossWeight A ρ l₁ l₂ k₁ k₂ := by
            rw [show Csf * (W : ℝ) * (Cg * (1 + (l₂ : ℝ)))
                = (Csf * (W : ℝ) * Cg) * (1 + (l₂ : ℝ)) by ring]
            refine mul_le_mul h1 hLW (by linarith) ?_
            rw [hCcval]
            exact le_trans zero_le_one (le_max_right (Csf * (W : ℝ) * Cg) 1)
          have hA : ENNReal.ofReal (Csf * (W : ℝ) * (Cg * (1 + (l₂ : ℝ))))
              ≤ (Cc : ENNReal) * ENNReal.ofReal (Work.KMTAreas.A7.lossWeight A ρ l₁ l₂ k₁ k₂) := by
            calc ENNReal.ofReal (Csf * (W : ℝ) * (Cg * (1 + (l₂ : ℝ))))
                ≤ ENNReal.ofReal ((Cc : ℝ) * Work.KMTAreas.A7.lossWeight A ρ l₁ l₂ k₁ k₂) :=
                  ENNReal.ofReal_le_ofReal hscal
              _ = (Cc : ENNReal) *
                    ENNReal.ofReal (Work.KMTAreas.A7.lossWeight A ρ l₁ l₂ k₁ k₂) := by
                  rw [ENNReal.ofReal_mul (by positivity), ENNReal.ofReal_coe_nnreal]
          exact mul_le_mul_of_nonneg_right hA (by positivity)
/-! ## The target -/

theorem MdlSliceLinG (P : Polynomial ℤ) (hd : 2 ≤ P.natDegree) (C₀ : ℕ) (hC₀ : 1 ≤ C₀)
    (R : NNReal) (hR : 2 < R) (j₂ : ℤ) (hj₂ : j₂ ∈ ({-1, 0, 1} : Finset ℤ)) :
    ∃ A : ℝ, 0 ≤ A ∧ ∃ ρ₀ : ℝ, 0 < ρ₀ ∧
      ∀ ρ : ℝ, 0 < ρ → ρ ≤ ρ₀ → ∃ K : NNReal → NNReal,
        ∀ (a : ℕ → NNReal) (Λ : NNReal) (l₁ l₂ k₁ k₂ : ℕ) (t : ℝ) (g : ℤ → ℂ),
          1 < Λ → PointwiseErgodicTheorems.Lacunary Λ a → (∀ n, 1 ≤ a n) →
          t ∈ Set.Icc (1 / 2 : ℝ) 1 → (k₂ = 0 → j₂ ≠ -1) →
          MeasureTheory.eLpNorm (fun x : ℤ => PointwiseErgodicTheorems.variationalNorm R
              (fun n : ℕ =>
                if Work.KMTPlan.A6.mdlCore ρ C₀ a l₁ l₂ k₁ k₂ n then
                  Work.KMTAreas.A7.Tle ρ l₂
                    (Work.KMTPlan.A6.varphitildeNtj P (Nat.floor (a n)) k₂ j₂ t)
                    (Work.KMTPlan.A6.mdlG ρ P (Work.KMTAreas.A7.uScale ρ
                      (max (max l₁ l₂) (max k₁ k₂))) l₂ g) x
                else 0)) 2 MeasureTheory.Measure.count
            ≤ (K Λ : ENNReal) *
                ENNReal.ofReal (Work.KMTAreas.A7.lossWeight A ρ l₁ l₂ k₁ k₂) *
                MeasureTheory.eLpNorm g 2 MeasureTheory.Measure.count := by
  obtain ⟨Alow, hAlow, hlow⟩ := Work.KMTPlan.A6.MdlSliceLowpassGDecim P hd C₀ hC₀ R hR
  refine ⟨max Alow 2, by positivity, min 1 (1 / (2 * (C₀ : ℝ))),
    lt_min one_pos (by positivity), ?_⟩
  intro ρ hρ hρ0
  have hρ1 : ρ ≤ 1 := le_trans hρ0 (min_le_left _ _)
  have hρC : ρ ≤ 1 / (2 * (C₀ : ℝ)) := le_trans hρ0 (min_le_right _ _)
  have hA1 : (1 : ℝ) ≤ max Alow 2 := le_trans (by norm_num) (le_max_right Alow 2)
  have hj₂' : j₂ = -1 ∨ j₂ = 0 ∨ j₂ = 1 := by
    simpa only [Finset.mem_insert, Finset.mem_singleton] using hj₂
  have hex : ∀ (Λ : NNReal), 1 < Λ → ∃ Cc : NNReal, 0 < Cc ∧
      ∀ (a : ℕ → NNReal) (l₁ l₂ k₁ k₂ : ℕ) (t : ℝ) (g : ℤ → ℂ),
        PointwiseErgodicTheorems.Lacunary Λ a → (∀ n, 1 ≤ a n) →
        t ∈ Set.Icc (1 / 2 : ℝ) 1 → (k₂ = 0 → j₂ ≠ -1) →
        MeasureTheory.eLpNorm (fun x : ℤ => PointwiseErgodicTheorems.variationalNorm R
            (fun n : ℕ => sliceFam P ρ C₀ a l₁ l₂ k₁ k₂ j₂ t g n x))
            2 MeasureTheory.Measure.count
          ≤ (Cc : ENNReal) *
              ENNReal.ofReal (Work.KMTAreas.A7.lossWeight (max Alow 2) ρ l₁ l₂ k₁ k₂) *
              MeasureTheory.eLpNorm g 2 MeasureTheory.Measure.count := by
    intro Λ hΛ
    obtain ⟨C₁, hC₁, h₁⟩ := sliceFam_bound_ne P hd C₀ hC₀ R hR (max Alow 2) hA1 j₂ hj₂ Λ hΛ ρ hρ hρ1
    obtain ⟨C₂, hC₂, h₂⟩ := hlow Λ hΛ ρ hρ hρ1 hρC
    refine ⟨max C₁ ⟨C₂, le_of_lt hC₂⟩, lt_max_of_lt_left hC₁, ?_⟩
    intro a l₁ l₂ k₁ k₂ t g ha ha1 ht hk
    by_cases hlp : k₂ = 0 ∧ j₂ = 0
    · -- the low-pass case
      have h2 := h₂ a l₁ l₂ k₁ t g ha ha1 ht
      rw [hlp.1, hlp.2]
      simp only [sliceFam] at h2 ⊢
      refine h2.trans ?_
      have hcoef : ENNReal.ofReal (Work.KMTAreas.A7.lossWeight Alow ρ l₁ l₂ k₁ 0)
          ≤ ENNReal.ofReal (Work.KMTAreas.A7.lossWeight (max Alow 2) ρ l₁ l₂ k₁ 0) :=
        ENNReal.ofReal_le_ofReal (lossWeight_mono (le_max_left Alow 2) hρ.le l₁ l₂ k₁ 0)
      have hcst : ENNReal.ofReal C₂
          ≤ ((max C₁ ⟨C₂, le_of_lt hC₂⟩ : NNReal) : ENNReal) := by
        exact_mod_cast (le_max_right C₁ (⟨C₂, le_of_lt hC₂⟩ : NNReal))
      calc ENNReal.ofReal C₂ * ENNReal.ofReal (Work.KMTAreas.A7.lossWeight Alow ρ l₁ l₂ k₁ 0) *
              MeasureTheory.eLpNorm g 2 MeasureTheory.Measure.count
          ≤ ((max C₁ ⟨C₂, le_of_lt hC₂⟩ : NNReal) : ENNReal) *
              ENNReal.ofReal (Work.KMTAreas.A7.lossWeight (max Alow 2) ρ l₁ l₂ k₁ 0) *
              MeasureTheory.eLpNorm g 2 MeasureTheory.Measure.count := by
            refine mul_le_mul_of_nonneg_right
              (mul_le_mul hcst hcoef (by positivity) (by positivity)) zero_le
        _ = _ := rfl
    · -- the non-low-pass case
      have hne : k₂ ≠ 0 ∨ j₂ = 1 := by
        by_cases hk2 : k₂ = 0
        · refine Or.inr ?_
          rcases hj₂' with h | h | h
          · exact absurd h (hk hk2)
          · exact absurd ⟨hk2, h⟩ hlp
          · exact h
        · exact Or.inl hk2
      have h1' := h₁ a l₁ l₂ k₁ k₂ t g ha ha1 ht hne
      refine h1'.trans ?_
      refine mul_le_mul_of_nonneg_right
        (mul_le_mul_of_nonneg_right (ENNReal.coe_le_coe.mpr (le_max_left C₁ ⟨C₂, le_of_lt hC₂⟩))
          (by positivity)) zero_le
  refine ⟨fun Λ => if h : 1 < Λ then Classical.choose (hex Λ h) else 1, ?_⟩
  intro a Λ l₁ l₂ k₁ k₂ t g hΛ ha ha1 ht hk
  have hspec := Classical.choose_spec (hex Λ hΛ)
  have hK : ((fun Λ => if h : 1 < Λ then Classical.choose (hex Λ h) else 1) Λ : NNReal)
      = Classical.choose (hex Λ hΛ) := by
    simp only [dif_pos hΛ]
  rw [hK]
  exact hspec.2 a l₁ l₂ k₁ k₂ t g ha ha1 ht hk

end

end Work.KMTPlan.A6
