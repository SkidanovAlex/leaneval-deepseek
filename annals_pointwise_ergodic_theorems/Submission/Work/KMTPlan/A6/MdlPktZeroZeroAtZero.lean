/-
# The height-`0` instance of the `(k₁,j₁) = (0,0)` case, completely proved

`Work.KMTPlan.A6.MdlPktZeroZeroAtZero C₀ R`: the bottom-height family
`n ↦ 1_{mdlCore} · Tle ρ 0 (varphiNtj (⌊a n⌋) 0 0 t) (mdlF ρ (uScale ρ L) 0 f)` obeys the `ℓ²`
variational estimate with the weight `lossWeight 0 ρ 0 l₂ 0 k₂ = 1`.

Three ingredients, all proved (axiom-clean):

* the **identity** `Tle ρ 0 (varphiNtj N 0 0 t) (mdlF ρ u 0 f) = Tle ρ 0 (varphiNt N 0 t) f` on the
  core: `Work.KMTPlan.A6.Tle_mdlF_eq_Tle_atZero_singleton` (singleton gate of `iwConv_comp`, so no
  non-aliasing is needed) + `Work.KMTPlan.A6.varphiNtj_zero`;
* the **narrowness**: `Work.KMTPlan.A6.supportedInArc_varphiNt_zero_of_core`;
* the **estimate**: `Work.KMTAreas.A7.LoLinVar` (clean height-`0` lacunary bound at `k = 0`), with
  `Work.KMTAreas.A7.eLpNorm_variationalNorm_clip_le` for the core clip.

Formalisation note: every manipulation of the `if` that defines the clipped family is done with
`by_cases` (so the branch proof has the *goal's* syntactic predicate, not the defeq-but-different
`Work.KMTAreas.A7.core` form), rather than with `rw [if_pos …]`/`rw [if_neg …]`.
-/
import Mathlib
import Submission.Work.KMTPlan.A6.MdlPktZeroZeroAtZeroSingleton
import Submission.Work.KMTPlan.A6.MdlPktNarrowness
import Submission.Work.KMTPlan.A6.MdlPktLinFLac
import Submission.Work.KMTAreas.A7.LoLinVar

set_option autoImplicit false
set_option maxHeartbeats 4000000

namespace Work.KMTPlan.A6

open MeasureTheory
open scoped BigOperators ENNReal NNReal
open Work.Analysis.IonescuWainger
open Work.Analysis.EndVar
open Work.KMTAreas.A7
open Work.KMTContract

noncomputable section

/-- The loss weight at exponent `0` is `1`. -/
theorem lossWeight_zero_exp (ρ : ℝ) (l₁ l₂ k₁ k₂ : ℕ) :
    Work.KMTAreas.A7.lossWeight 0 ρ l₁ l₂ k₁ k₂ = 1 := by
  unfold Work.KMTAreas.A7.lossWeight
  simp

/-- The analytic core of the height-`0` case, with the weight already reduced to `1`. -/
theorem mdlPktZeroZeroAtZero_aux (ρ : ℝ) (hρ : 0 < ρ) (hρ1 : ρ ≤ 1) (C₀ : ℕ) (R : NNReal)
    (hR : 2 < R) (Λ : NNReal) (hΛ : 1 < Λ) (a : ℕ → NNReal)
    (ha : PointwiseErgodicTheorems.Lacunary Λ a) (ha1 : ∀ n : ℕ, 1 ≤ a n) (t : ℝ)
    (ht : t ∈ Set.Icc (1 / 2 : ℝ) 1) (CL : NNReal)
    (hCL : ∀ (a' : ℕ → NNReal) (ha' : PointwiseErgodicTheorems.Lacunary Λ a')
      (ha1' : ∀ n : ℕ, 1 ≤ a' n) (t' : ℝ) (ht' : t' ∈ Set.Icc (1 / 2 : ℝ) 1) (f : ℤ → ℂ),
      MeasureTheory.eLpNorm (fun x : ℤ => PointwiseErgodicTheorems.variationalNorm R
          (fun n : ℕ => Work.KMTAreas.A7.Tle ρ 0
            (Work.KMTAreas.A7.varphiNt (Nat.floor (a' n)) 0 t') f x))
        2 MeasureTheory.Measure.count
        ≤ (CL : ENNReal) * MeasureTheory.eLpNorm f 2 MeasureTheory.Measure.count)
    (l₂ k₂ : ℕ) (u : ℕ)
    (hu : u = Work.KMTAreas.A7.uScale ρ (max (max 0 l₂) (max 0 k₂))) (f : ℤ → ℂ) :
    MeasureTheory.eLpNorm (fun x : ℤ => PointwiseErgodicTheorems.variationalNorm R
        (fun n : ℕ =>
          if Work.KMTPlan.A6.mdlCore ρ C₀ a 0 l₂ 0 k₂ n then
            Work.KMTAreas.A7.Tle ρ 0 (Work.KMTPlan.A6.varphiNtj (Nat.floor (a n)) 0 0 t)
              (Work.KMTPlan.A6.mdlF ρ u 0 f) x
          else 0))
      2 MeasureTheory.Measure.count
      ≤ (((3 : ℝ≥0) * CL + 1 : ℝ≥0) : ENNReal) *
          MeasureTheory.eLpNorm f 2 MeasureTheory.Measure.count := by
  classical
  have hr1 : (1 : NNReal) ≤ R := le_trans (by norm_num) (le_of_lt hR)
  by_cases hftop : MeasureTheory.eLpNorm f 2 MeasureTheory.Measure.count = ⊤
  · rw [hftop]
    have hne : ((((3 : ℝ≥0) * CL + 1 : ℝ≥0)) : ENNReal) ≠ 0 := by simp
    rw [ENNReal.mul_top hne]
    exact le_top
  have hfflt : MeasureTheory.eLpNorm f 2 MeasureTheory.Measure.count < ⊤ :=
    lt_top_iff_ne_top.mpr hftop
  have hf : MemLp f 2 MeasureTheory.Measure.count :=
    MeasureTheory.memLp_iff.mpr (hfflt)
  have hamono : Monotone a := Work.KMTPlan.A6.lowpass_monotone_of_lacunary' hΛ ha ha1
  -- the pointwise identity on the core
  have hident : ∀ n : ℕ, Work.KMTPlan.A6.mdlCore ρ C₀ a 0 l₂ 0 k₂ n →
      Work.KMTAreas.A7.Tle ρ 0 (Work.KMTPlan.A6.varphiNtj (Nat.floor (a n)) 0 0 t)
          (Work.KMTPlan.A6.mdlF ρ u 0 f)
        = Work.KMTAreas.A7.Tle ρ 0 (Work.KMTAreas.A7.varphiNt (Nat.floor (a n)) 0 t) f := by
    intro n hn
    rw [Work.KMTPlan.A6.varphiNtj_zero]
    refine Work.KMTPlan.A6.Tle_mdlF_eq_Tle_atZero_singleton ρ hρ hρ1 u (Nat.floor (a n))
      (by rw [hu]; exact Work.KMTAreas.A7.uScale_pos hρ.le _) t hf ?_
    simpa only [hu] using
      Work.KMTPlan.A6.supportedInArc_varphiNt_zero_of_core ρ C₀ a l₂ k₂ n t hn
  -- ## the clip: the core is upward closed in `n`, so the clipped family is a tail
  have hclip : MeasureTheory.eLpNorm (fun x : ℤ => PointwiseErgodicTheorems.variationalNorm R
        (fun n : ℕ =>
          if Work.KMTPlan.A6.mdlCore ρ C₀ a 0 l₂ 0 k₂ n then
            Work.KMTAreas.A7.Tle ρ 0 (Work.KMTPlan.A6.varphiNtj (Nat.floor (a n)) 0 0 t)
              (Work.KMTPlan.A6.mdlF ρ u 0 f) x
          else 0))
      2 MeasureTheory.Measure.count
      ≤ 3 * MeasureTheory.eLpNorm (fun x : ℤ => PointwiseErgodicTheorems.variationalNorm R
          (fun n : ℕ => Work.KMTAreas.A7.Tle ρ 0
            (Work.KMTAreas.A7.varphiNt (Nat.floor (a n)) 0 t) f x))
        2 MeasureTheory.Measure.count := by
    by_cases hex : ∃ n : ℕ, Work.KMTPlan.A6.mdlCore ρ C₀ a 0 l₂ 0 k₂ n
    · refine Work.KMTAreas.A7.eLpNorm_variationalNorm_clip_le (r := R) hr1 2
        (Nat.find hex)
        (fun n x => Work.KMTAreas.A7.Tle ρ 0
          (Work.KMTAreas.A7.varphiNt (Nat.floor (a n)) 0 t) f x)
        (fun n x => if Work.KMTPlan.A6.mdlCore ρ C₀ a 0 l₂ 0 k₂ n then
          Work.KMTAreas.A7.Tle ρ 0 (Work.KMTPlan.A6.varphiNtj (Nat.floor (a n)) 0 0 t)
            (Work.KMTPlan.A6.mdlF ρ u 0 f) x else 0) ?_ ?_
      · intro n hn
        funext x
        by_cases hc : Work.KMTPlan.A6.mdlCore ρ C₀ a 0 l₂ 0 k₂ n
        · exact absurd hc (Nat.find_min hex hn)
        · simp [hc]
      · intro n hn
        funext x
        by_cases hc : Work.KMTPlan.A6.mdlCore ρ C₀ a 0 l₂ 0 k₂ n
        · simp only [hc, if_true]
          exact congrFun (hident n hc) x
        · exact absurd (show Work.KMTPlan.A6.mdlCore ρ C₀ a 0 l₂ 0 k₂ n from
            Work.KMTAreas.A7.core_mono hamono hn (Nat.find_spec hex)) hc
    · -- the core is empty: the clipped family vanishes identically
      have hfam0 : (fun x : ℤ => PointwiseErgodicTheorems.variationalNorm R
          (fun n : ℕ => (if Work.KMTPlan.A6.mdlCore ρ C₀ a 0 l₂ 0 k₂ n then
            Work.KMTAreas.A7.Tle ρ 0 (Work.KMTPlan.A6.varphiNtj (Nat.floor (a n)) 0 0 t)
              (Work.KMTPlan.A6.mdlF ρ u 0 f) x else 0)))
          = (fun x : ℤ => PointwiseErgodicTheorems.variationalNorm R
              (fun _ : ℕ => (0 : ℂ))) := by
        funext x
        have hfam : (fun n : ℕ => (if Work.KMTPlan.A6.mdlCore ρ C₀ a 0 l₂ 0 k₂ n then
            Work.KMTAreas.A7.Tle ρ 0 (Work.KMTPlan.A6.varphiNtj (Nat.floor (a n)) 0 0 t)
              (Work.KMTPlan.A6.mdlF ρ u 0 f) x else 0)) = fun _ : ℕ => (0 : ℂ) := by
          funext n
          by_cases hc : Work.KMTPlan.A6.mdlCore ρ C₀ a 0 l₂ 0 k₂ n
          · exact (hex ⟨n, hc⟩).elim
          · simp [hc]
        rw [hfam]
      rw [hfam0, Work.KMTAreas.A7.eLpNorm_variationalNorm_zero hr1 2]
      exact zero_le
  -- ## the estimate for the unclipped family
  have hbound : MeasureTheory.eLpNorm (fun x : ℤ => PointwiseErgodicTheorems.variationalNorm R
        (fun n : ℕ => Work.KMTAreas.A7.Tle ρ 0
          (Work.KMTAreas.A7.varphiNt (Nat.floor (a n)) 0 t) f x))
      2 MeasureTheory.Measure.count ≤ (CL : ENNReal) *
        MeasureTheory.eLpNorm f 2 MeasureTheory.Measure.count :=
    hCL a ha ha1 t ht f
  refine (hclip.trans (mul_le_mul' (le_refl (3 : ENNReal)) hbound)).trans ?_
  rw [← mul_assoc]
  refine mul_le_mul' ?_ le_rfl
  rw [← ENNReal.coe_ofNat, ← ENNReal.coe_mul]
  exact ENNReal.coe_le_coe.mpr le_self_add

/-- **`MdlPktZeroZeroAtZero`**: the height-`0` instance of the `(k₁,j₁) = (0,0)` case of
`Work.KMTPlan.A6.MdlSlicePktLinF`. -/
theorem mdlPktZeroZeroAtZero (C₀ : ℕ) (hC₀ : 1 ≤ C₀) (R : NNReal) (hR : 2 < R) :
    MdlPktZeroZeroAtZero C₀ R := by
  classical
  refine ⟨0, le_rfl, 1, one_pos, ?_⟩
  intro ρ hρ hρ1
  -- for each `Λ > 1`, the constant of the clean height-`0` estimate `LoLinVar`
  have hkey : ∀ Λ : NNReal, 1 < Λ → ∃ CL : NNReal, ∀ (a : ℕ → NNReal)
      (ha : PointwiseErgodicTheorems.Lacunary Λ a) (ha1 : ∀ n : ℕ, 1 ≤ a n) (t : ℝ)
      (ht : t ∈ Set.Icc (1 / 2 : ℝ) 1) (f : ℤ → ℂ),
      MeasureTheory.eLpNorm (fun x : ℤ => PointwiseErgodicTheorems.variationalNorm R
        (fun n : ℕ => Work.KMTAreas.A7.Tle ρ 0
          (Work.KMTAreas.A7.varphiNt (Nat.floor (a n)) 0 t) f x))
        2 MeasureTheory.Measure.count
        ≤ (CL : ENNReal) * MeasureTheory.eLpNorm f 2 MeasureTheory.Measure.count := by
    intro Λ hΛ
    obtain ⟨C, hC⟩ := Work.KMTAreas.A7.LoLinVar ρ hρ hρ1 2 (by norm_num) (by norm_num) R hR Λ hΛ
    refine ⟨C, ?_⟩
    intro a ha ha1 t ht f
    have hkN : ∀ n : ℕ, 2 ^ 0 ≤ Nat.floor (a n) := by
      intro n
      have h1 : (1 : ℝ≥0) ≤ a n := ha1 n
      have h2 : 0 < Nat.floor (a n) := Nat.floor_pos.mpr h1
      omega
    have h := hC a ha ha1 0 hkN t ht f
    rw [show ((1 : ℝ) + ((0 : ℕ) : ℝ)) ^ 2 = 1 by norm_num, ENNReal.ofReal_one, mul_one] at h
    exact h
  let K : NNReal → NNReal := fun Λ =>
    ⟨max 1 (if h : 1 < Λ then 3 * Classical.choose (hkey Λ h) + 1 else 1),
      le_trans zero_le_one (le_max_left 1 _)⟩
  refine ⟨K, ?_⟩
  intro a Λ l₂ k₂ t f hΛ ha ha1 ht
  have hCL := Classical.choose_spec (hkey Λ hΛ)
  have hK : ((3 * Classical.choose (hkey Λ hΛ) + 1 : ℝ≥0) : ENNReal) ≤ (K Λ : ENNReal) := by
    dsimp only [K]
    rw [dif_pos hΛ]
    exact ENNReal.coe_le_coe.mpr (le_max_right 1 _)
  have hweight : ENNReal.ofReal (Work.KMTAreas.A7.lossWeight 0 ρ 0 l₂ 0 k₂) = 1 := by
    rw [lossWeight_zero_exp]
    norm_num
  rw [hweight, mul_one]
  refine (mdlPktZeroZeroAtZero_aux ρ hρ hρ1 C₀ R hR Λ hΛ a ha ha1 t ht
    (Classical.choose (hkey Λ hΛ)) hCL l₂ k₂
    (Work.KMTAreas.A7.uScale ρ (max (max 0 l₂) (max 0 k₂))) rfl f).trans ?_
  exact mul_le_mul' hK le_rfl

end

end Work.KMTPlan.A6
