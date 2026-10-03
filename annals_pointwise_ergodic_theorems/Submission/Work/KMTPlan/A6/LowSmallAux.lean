import Mathlib
import Submission.Work.KMTPlan.A6.lowSmallSet_le_log_sharp
import Submission.Work.KMTPlan.A6.Tm_finset_sum
import Submission.Work.KMTPlan.A6.BtwistEx_bilinear_of_bounded
import Submission.Work.KMTAreas.A7.cw_etaCut_decay
import Submission.Work.KMTAreas.A7.KmtKernelL1Uniform
import Submission.Work.KMTAreas.A7.cw_etaCut_decay

set_option autoImplicit false
set_option maxHeartbeats 2000000
set_option linter.unusedVariables false

/-!
# The shared definitions of the small-scale model tuple of the low case of area A6

These definitions (`lowModelSlice`, `lowTrunc`, the anchored bump families, the randomised slice
family, the side conditions of the Rademacher--Menshov step, ...) used to live in
`Submission/Work/KMTPlan/A6/lowSmallModelVar.lean`.  They are moved here so that lemmas *about*
them can be stated in modules that do **not** import the target file - otherwise such a lemma can
never be used inside the target file itself (import cycle).  The target file imports this module,
so the names are unchanged for everything that imported the target file.
-/

namespace Work.KMTPlan.A6

noncomputable section

open MeasureTheory Polynomial Finset Filter Topology
open scoped ENNReal NNReal BigOperators
open PointwiseErgodicTheorems Submission.PointwiseErgodicTheorems
open Work.Analysis.EndVar Work.KMTContract

/-- The `t`-slice of the small-scale model tuple `lowModel`: the single-scale model expression,
clamped by `lowSmallSet`. -/
noncomputable def lowModelSlice (ρ : ℝ) (P : ℤ[X]) (C₀ : ℕ) (a : ℕ → ℝ≥0) (f g : ℤ → ℂ)
    (l₁ l₂ k₁ k₂ : ℕ) (t : ℝ) : ℕ → ℤ → ℂ :=
  fun n x =>
    if lowSmallSet ρ C₀ a l₁ l₂ k₁ k₂ n then
      BtwistEx ρ P l₁ l₂
        (Work.KMTAreas.A7.mStarF (Work.KMTAreas.A7.uScale ρ (lcL l₁ l₂ k₁ k₂)))
        (Work.KMTAreas.A7.mStargF P.natDegree
          (Work.KMTAreas.A7.uScale ρ (lcL l₁ l₂ k₁ k₂)))
        (Work.KMTAreas.A7.Tm ρ l₁
          (Work.KMTAreas.A7.varphiNt (Nat.floor (a n)) k₁ t) f)
        (Work.KMTAreas.A7.Tm ρ l₂
          (Work.KMTAreas.A7.varphitildeNt P P.natDegree (Nat.floor (a n)) k₂ t) g) x
    else 0

/-- **The model tuple is the `t`-integral of its slices.** -/
theorem lowModel_eq_integral_slice (ρ : ℝ) (P : ℤ[X]) (C₀ : ℕ) (a : ℕ → ℝ≥0) (f g : ℤ → ℂ)
    (l₁ l₂ k₁ k₂ : ℕ) (n : ℕ) (x : ℤ) :
    lowModel ρ P C₀ a f g l₁ l₂ k₁ k₂ n x
      = ∫ t in (1 / 2 : ℝ)..1, lowModelSlice ρ P C₀ a f g l₁ l₂ k₁ k₂ t n x := by
  rw [lowModel_apply]
  by_cases h : lowSmallSet ρ C₀ a l₁ l₂ k₁ k₂ n
  · rw [if_pos h]
    refine (intervalIntegral.integral_congr (fun t _ => ?_)).symm
    simp only [lowModelSlice, h, if_true]
  · rw [if_neg h]
    have hz : (∫ t in (1 / 2 : ℝ)..1, lowModelSlice ρ P C₀ a f g l₁ l₂ k₁ k₂ t n x) = 0 := by
      have : (fun t : ℝ => lowModelSlice ρ P C₀ a f g l₁ l₂ k₁ k₂ t n x)
          = fun _ : ℝ => (0 : ℂ) := by
        funext t
        simp only [lowModelSlice, h, if_false]
      rw [this, intervalIntegral.integral_zero]
    rw [hz]


/-- The submodule of *bounded* sequences `ℤ → ℂ`.  This is the space on which the iterated
`tsum` defining `BtwistEx` converges unconditionally, hence the space on which `BtwistEx`
is bilinear and the Rademacher--Menshov inequality is applied. -/
def bddSub : Submodule ℂ (ℤ → ℂ) where
  carrier := {u : ℤ → ℂ | ∃ C : ℝ, ∀ y : ℤ, ‖u y‖ ≤ C}
  zero_mem' := ⟨0, by intro y; simp⟩
  add_mem' := by
    rintro u v ⟨Cu, hu⟩ ⟨Cv, hv⟩
    refine ⟨max Cu 0 + max Cv 0, fun y => ?_⟩
    rw [Pi.add_apply]
    refine le_trans (norm_add_le _ _) ?_
    have h1 : ‖u y‖ ≤ max Cu 0 := le_trans (hu y) (le_max_left _ _)
    have h2 : ‖v y‖ ≤ max Cv 0 := le_trans (hv y) (le_max_left _ _)
    linarith
  smul_mem' := by
    rintro c u ⟨Cu, hu⟩
    refine ⟨‖c‖ * max Cu 0, fun y => ?_⟩
    rw [Pi.smul_apply, norm_smul]
    exact mul_le_mul_of_nonneg_left (le_trans (hu y) (le_max_left _ _)) (norm_nonneg c)


/-! ## The symbols of the slices and the anchored slice family -/

/-- The `f`-side bump family of the small-scale slices, anchored at `0`: this is what lets the
Rademacher--Menshov inequality, whose sequences start at `0`, be applied to the columns. -/
noncomputable def lowSymbF (ρ : ℝ) (C₀ : ℕ) (a : ℕ → ℝ≥0) (l₁ l₂ k₁ k₂ : ℕ) (t : ℝ) :
    ℕ → ℝ → ℂ :=
  fun n ξ =>
    if n = 0 then 0
    else if lowSmallSet ρ C₀ a l₁ l₂ k₁ k₂ n then
      Work.KMTAreas.A7.varphiNt (Nat.floor (a n)) k₁ t ξ else 0

/-- The `g`-side bump family of the small-scale slices, anchored at `0`. -/
noncomputable def lowSymbG (ρ : ℝ) (P : ℤ[X]) (C₀ : ℕ) (a : ℕ → ℝ≥0) (l₁ l₂ k₁ k₂ : ℕ)
    (t : ℝ) : ℕ → ℝ → ℂ :=
  fun n ξ =>
    if n = 0 then 0
    else if lowSmallSet ρ C₀ a l₁ l₂ k₁ k₂ n then
      Work.KMTAreas.A7.varphitildeNt P P.natDegree (Nat.floor (a n)) k₂ t ξ else 0

theorem lowSymbF_zero (ρ : ℝ) (C₀ : ℕ) (a : ℕ → ℝ≥0) (l₁ l₂ k₁ k₂ : ℕ) (t : ℝ) :
    lowSymbF ρ C₀ a l₁ l₂ k₁ k₂ t 0 = 0 := by
  funext ξ; simp [lowSymbF]

theorem lowSymbG_zero (ρ : ℝ) (P : ℤ[X]) (C₀ : ℕ) (a : ℕ → ℝ≥0) (l₁ l₂ k₁ k₂ : ℕ) (t : ℝ) :
    lowSymbG ρ P C₀ a l₁ l₂ k₁ k₂ t 0 = 0 := by
  funext ξ; simp [lowSymbG]

/-- The *anchored* single-scale slice of the model tuple. -/
noncomputable def lowSliceA (ρ : ℝ) (P : ℤ[X]) (C₀ : ℕ) (a : ℕ → ℝ≥0) (f g : ℤ → ℂ)
    (l₁ l₂ k₁ k₂ : ℕ) (t : ℝ) : ℕ → ℤ → ℂ :=
  fun n x =>
    BtwistEx ρ P l₁ l₂
      (Work.KMTAreas.A7.mStarF (Work.KMTAreas.A7.uScale ρ (lcL l₁ l₂ k₁ k₂)))
      (Work.KMTAreas.A7.mStargF P.natDegree
        (Work.KMTAreas.A7.uScale ρ (lcL l₁ l₂ k₁ k₂)))
      (Work.KMTAreas.A7.Tm ρ l₁ (lowSymbF ρ C₀ a l₁ l₂ k₁ k₂ t n) f)
      (Work.KMTAreas.A7.Tm ρ l₂ (lowSymbG ρ P C₀ a l₁ l₂ k₁ k₂ t n) g) x


/-- The side conditions on a bump family under which `Tm` is linear in its symbol
(`Work.KMTPlan.A6.Tm_randSymb_eq`). -/
def TmSide (ρ : ℝ) (l K : ℕ) (Φ : ℕ → ℝ → ℂ) : Prop :=
  (∀ k ∈ Finset.range (K + 1), ∀ x : ℝ, Summable fun j : ℤ => Φ k (x + (j : ℝ))) ∧
  (∀ k ∈ Finset.range (K + 1), MeasureTheory.Integrable
    (Work.Analysis.IonescuWainger.iwSymbolSet (Work.KMTAreas.A7.diffFreqs ρ l)
      (Work.Analysis.IonescuWainger.periodize (Φ k)))
    Work.Analysis.IonescuWainger.circleMeasure) ∧
  (∀ k ∈ Finset.range (K + 1), Summable fun j : ℤ =>
    ‖Work.Analysis.IWMultiplier.iwKernel (Work.Analysis.IonescuWainger.iwSymbolSet
      (Work.KMTAreas.A7.diffFreqs ρ l)
      (Work.Analysis.IonescuWainger.periodize (Φ k))) j‖ ^ 2)


/-! ## The truncation of the lacunary scales -/

/-- The index beyond which `lowSmallSet` is empty, given the quantitative `lowSmallSet_le_log`
bound for the specific lacunary sequence. -/
noncomputable def lowTrunc (D : ℝ) (ρ : ℝ) (L : ℕ) : ℕ :=
  Nat.ceil (D * (2 : ℝ) ^ (Work.KMTAreas.A7.uScale ρ L)) + 1


/-- The *randomised* slice family: the twisted model operator applied to the two randomised
cut-offs of `lowSymbF`/`lowSymbG` (the object appearing on the right-hand side of the
Rademacher--Menshov reduction). -/
noncomputable def lowSliceRand (ρ : ℝ) (P : ℤ[X]) (C₀ : ℕ) (a : ℕ → ℝ≥0) (f g : ℤ → ℂ)
    (l₁ l₂ k₁ k₂ : ℕ) (t : ℝ) (K : ℕ) (ε ε' : ℕ → ℂ) : ℤ → ℂ :=
  fun x => BtwistEx ρ P l₁ l₂
    (Work.KMTAreas.A7.mStarF (Work.KMTAreas.A7.uScale ρ (lcL l₁ l₂ k₁ k₂)))
    (Work.KMTAreas.A7.mStargF P.natDegree (Work.KMTAreas.A7.uScale ρ (lcL l₁ l₂ k₁ k₂)))
    (Work.KMTAreas.A7.Tm ρ l₁ (Work.KMTAreas.A7.randSymb
      (lowSymbF ρ C₀ a l₁ l₂ k₁ k₂ t) ε K) f)
    (Work.KMTAreas.A7.Tm ρ l₂ (Work.KMTAreas.A7.randSymb
      (lowSymbG ρ P C₀ a l₁ l₂ k₁ k₂ t) ε' K) g) x

/-- The `ℓ¹(ℤ)` norm of the variational norm of the slice family (the left-hand side of the
per-`t` estimate). -/
noncomputable def LowSliceVarNorm (ρ : ℝ) (P : ℤ[X]) (C₀ : ℕ) (a : ℕ → ℝ≥0) (f g : ℤ → ℂ)
    (l₁ l₂ k₁ k₂ : ℕ) (t : ℝ) (r : NNReal) : ℝ≥0∞ :=
  MeasureTheory.eLpNorm (fun x : ℤ => PointwiseErgodicTheorems.variationalNorm r
    (fun n : ℕ => lowModelSlice ρ P C₀ a f g l₁ l₂ k₁ k₂ t n x))
    1 MeasureTheory.Measure.count


/-- The randomised single-scale bound: the object that `ssuBtwistEx` + `tmRandSymb_l2` supply. -/
def LowRandBound (ρ : ℝ) (P : ℤ[X]) (C₀ : ℕ) (a : ℕ → ℝ≥0) (f g : ℤ → ℂ)
    (l₁ l₂ k₁ k₂ : ℕ) (t : ℝ) (D : ℝ) (Cbound : ℝ≥0∞) : Prop :=
  ∀ (ε ε' : ℕ → ℂ), (∀ k, ‖ε k‖ ≤ 1) → (∀ k, ‖ε' k‖ ≤ 1) →
    MeasureTheory.eLpNorm (lowSliceRand ρ P C₀ a f g l₁ l₂ k₁ k₂ t
      (lowTrunc D ρ (lcL l₁ l₂ k₁ k₂) + 1) ε ε') 1 MeasureTheory.Measure.count ≤ Cbound


/-- The `cw`-coefficients of the narrow window `m_* = η_{≤-2u}` are absolutely summable
(quantitative: they decay like `j^{-2}`). -/
theorem cw_etaCut_summable (c : ℤ) :
    Summable fun j : ℤ => ‖Work.KMTAreas.A7.cw
      (Work.Analysis.IonescuWainger.etaCut Work.KMTContract.kmtEta c) j‖ := by
  obtain ⟨C, _hC, h⟩ := Work.KMTAreas.A7.cw_etaCut_decay c
  refine Summable.of_nonneg_of_le (fun j => norm_nonneg _) (fun j => ?_)
    (Work.KMTAreas.A7.summable_kmtKernWeight.mul_left C)
  calc ‖Work.KMTAreas.A7.cw (Work.Analysis.IonescuWainger.etaCut Work.KMTContract.kmtEta c) j‖
      ≤ C / (1 + |(j : ℝ)|) ^ 2 := h j
    _ = C * ‖Work.KMTAreas.A7.kmtKernWeight j‖ := by
        rw [Work.KMTAreas.A7.norm_kmtKernWeight, div_eq_mul_inv, one_div]


theorem cw_mStarF_summable (u : ℕ) :
    Summable fun j : ℤ => ‖Work.KMTAreas.A7.cw (Work.KMTAreas.A7.mStarF u) j‖ := by
  simpa [Work.KMTAreas.A7.mStarF] using cw_etaCut_summable (-(2 * (u : ℤ)))

theorem cw_mStargF_summable (d u : ℕ) :
    Summable fun j : ℤ => ‖Work.KMTAreas.A7.cw (Work.KMTAreas.A7.mStargF d u) j‖ := by
  simpa [Work.KMTAreas.A7.mStargF] using cw_etaCut_summable (-((d : ℤ) * 2 * (u : ℤ)))

theorem BtwistEx_bdd_add₁ (ρ : ℝ) (P : ℤ[X]) (l₁ l₂ : ℕ) (m₁ m₂ : ℝ → ℂ)
    (hm₁ : Summable fun j : ℤ => ‖Work.KMTAreas.A7.cw m₁ j‖)
    (hm₂ : Summable fun j : ℤ => ‖Work.KMTAreas.A7.cw m₂ j‖)
    (u u' w : bddSub) :
    BtwistEx ρ P l₁ l₂ m₁ m₂ (u + u').1 w.1
      = BtwistEx ρ P l₁ l₂ m₁ m₂ u.1 w.1 + BtwistEx ρ P l₁ l₂ m₁ m₂ u'.1 w.1 := by
  obtain ⟨Cu, hu⟩ := u.2
  obtain ⟨Cu', hu'⟩ := u'.2
  obtain ⟨Cw, hw⟩ := w.2
  have h := (Work.KMTPlan.A6.BtwistEx_bilinear_of_bounded ρ P l₁ l₂ m₁ m₂ hm₁ hm₂
    u.1 u'.1 w.1 (0 : ℤ → ℂ) Cu Cu' Cw 0 hu hu' hw (by intro y; simp)).1
  simpa [Submodule.coe_add] using h

theorem BtwistEx_bdd_add₂ (ρ : ℝ) (P : ℤ[X]) (l₁ l₂ : ℕ) (m₁ m₂ : ℝ → ℂ)
    (hm₁ : Summable fun j : ℤ => ‖Work.KMTAreas.A7.cw m₁ j‖)
    (hm₂ : Summable fun j : ℤ => ‖Work.KMTAreas.A7.cw m₂ j‖)
    (u w w' : bddSub) :
    BtwistEx ρ P l₁ l₂ m₁ m₂ u.1 (w + w').1
      = BtwistEx ρ P l₁ l₂ m₁ m₂ u.1 w.1 + BtwistEx ρ P l₁ l₂ m₁ m₂ u.1 w'.1 := by
  obtain ⟨Cu, hu⟩ := u.2
  obtain ⟨Cw, hw⟩ := w.2
  obtain ⟨Cw', hw'⟩ := w'.2
  have h := (Work.KMTPlan.A6.BtwistEx_bilinear_of_bounded ρ P l₁ l₂ m₁ m₂ hm₁ hm₂
    u.1 (0 : ℤ → ℂ) w.1 w'.1 Cu 0 Cw Cw' hu (by intro y; simp) hw hw').2.1
  simpa [Submodule.coe_add] using h

theorem BtwistEx_bdd_smul₁ (ρ : ℝ) (P : ℤ[X]) (l₁ l₂ : ℕ) (m₁ m₂ : ℝ → ℂ)
    (hm₁ : Summable fun j : ℤ => ‖Work.KMTAreas.A7.cw m₁ j‖)
    (hm₂ : Summable fun j : ℤ => ‖Work.KMTAreas.A7.cw m₂ j‖)
    (c : ℂ) (u w : bddSub) :
    BtwistEx ρ P l₁ l₂ m₁ m₂ (c • u).1 w.1
      = c • BtwistEx ρ P l₁ l₂ m₁ m₂ u.1 w.1 := by
  obtain ⟨Cu, hu⟩ := u.2
  obtain ⟨Cw, hw⟩ := w.2
  have h := (Work.KMTPlan.A6.BtwistEx_bilinear_of_bounded ρ P l₁ l₂ m₁ m₂ hm₁ hm₂
    u.1 (0 : ℤ → ℂ) w.1 (0 : ℤ → ℂ) Cu 0 Cw 0 hu (by intro y; simp) hw
    (by intro y; simp)).2.2.1 c
  simpa [Submodule.coe_smul] using h

theorem BtwistEx_bdd_smul₂ (ρ : ℝ) (P : ℤ[X]) (l₁ l₂ : ℕ) (m₁ m₂ : ℝ → ℂ)
    (hm₁ : Summable fun j : ℤ => ‖Work.KMTAreas.A7.cw m₁ j‖)
    (hm₂ : Summable fun j : ℤ => ‖Work.KMTAreas.A7.cw m₂ j‖)
    (c : ℂ) (u w : bddSub) :
    BtwistEx ρ P l₁ l₂ m₁ m₂ u.1 (c • w).1
      = c • BtwistEx ρ P l₁ l₂ m₁ m₂ u.1 w.1 := by
  obtain ⟨Cu, hu⟩ := u.2
  obtain ⟨Cw, hw⟩ := w.2
  have h := (Work.KMTPlan.A6.BtwistEx_bilinear_of_bounded ρ P l₁ l₂ m₁ m₂ hm₁ hm₂
    u.1 (0 : ℤ → ℂ) w.1 (0 : ℤ → ℂ) Cu 0 Cw 0 hu (by intro y; simp) hw
    (by intro y; simp)).2.2.2.1 c
  simpa [Submodule.coe_smul] using h

theorem Tm_zero (ρ : ℝ) (l : ℕ) (f : ℤ → ℂ)
    (hf : MeasureTheory.MemLp f 2 MeasureTheory.Measure.count) :
    Work.KMTAreas.A7.Tm ρ l (0 : ℝ → ℂ) f = 0 := by
  have h := Work.KMTPlan.A6.Tm_finset_sum (ρ := ρ) (l := l) (s := (∅ : Finset ℕ))
    (c := fun _ => (0 : ℂ)) (φ := fun _ => (0 : ℝ → ℂ)) (f := f) hf
    (by intro i hi; exact absurd hi (by simp))
    (by intro i hi; exact absurd hi (by simp))
    (by intro i hi; exact absurd hi (by simp))
  simpa using h

theorem BtwistEx_zero_zero (ρ : ℝ) (P : ℤ[X]) (l₁ l₂ : ℕ) (m₁ m₂ : ℝ → ℂ)
    (hm₁ : Summable fun j : ℤ => ‖Work.KMTAreas.A7.cw m₁ j‖)
    (hm₂ : Summable fun j : ℤ => ‖Work.KMTAreas.A7.cw m₂ j‖) :
    BtwistEx ρ P l₁ l₂ m₁ m₂ (0 : ℤ → ℂ) 0 = 0 :=
  (Work.KMTPlan.A6.BtwistEx_bilinear_of_bounded ρ P l₁ l₂ m₁ m₂ hm₁ hm₂
    (0 : ℤ → ℂ) 0 0 0 0 0 0 0 (by intro y; simp) (by intro y; simp)
    (by intro y; simp) (by intro y; simp)).2.2.2.2.1

theorem lowSliceA_eq_lowModelSlice (ρ : ℝ) (P : ℤ[X]) (C₀ : ℕ) (a : ℕ → ℝ≥0) (f g : ℤ → ℂ)
    (l₁ l₂ k₁ k₂ : ℕ) (t : ℝ)
    (hf : MeasureTheory.MemLp f 2 MeasureTheory.Measure.count)
    (hg : MeasureTheory.MemLp g 2 MeasureTheory.Measure.count)
    (n : ℕ) (hn : 1 ≤ n) (x : ℤ) :
    lowSliceA ρ P C₀ a f g l₁ l₂ k₁ k₂ t n x
      = lowModelSlice ρ P C₀ a f g l₁ l₂ k₁ k₂ t n x := by
  have hn0 : n ≠ 0 := by omega
  by_cases h : lowSmallSet ρ C₀ a l₁ l₂ k₁ k₂ n
  · have h1 : lowSymbF ρ C₀ a l₁ l₂ k₁ k₂ t n
        = Work.KMTAreas.A7.varphiNt (Nat.floor (a n)) k₁ t := by
      funext ξ; simp [lowSymbF, hn0, h]
    have h2 : lowSymbG ρ P C₀ a l₁ l₂ k₁ k₂ t n
        = Work.KMTAreas.A7.varphitildeNt P P.natDegree (Nat.floor (a n)) k₂ t := by
      funext ξ; simp [lowSymbG, hn0, h]
    rw [lowSliceA, h1, h2]
    simp only [lowModelSlice, h, if_true]
  · have h1 : lowSymbF ρ C₀ a l₁ l₂ k₁ k₂ t n = 0 := by
      funext ξ; simp [lowSymbF, hn0, h]
    have h2 : lowSymbG ρ P C₀ a l₁ l₂ k₁ k₂ t n = 0 := by
      funext ξ; simp [lowSymbG, hn0, h]
    rw [lowSliceA, h1, h2, Tm_zero ρ l₁ f hf, Tm_zero ρ l₂ g hg,
      BtwistEx_zero_zero ρ P l₁ l₂ _ _ (cw_mStarF_summable _) (cw_mStargF_summable _ _)]
    simp only [lowModelSlice, h, if_false]
    rfl

/-! ## The Rademacher--Menshov reduction for the twisted multiplier -/

/-- **The `ρ`-instantiated body of the paper's Lemma `ssu`, with the boundedness hypotheses on the
bumps.**  This is the form in which the lemma is actually *proved* in this tree
(`Work.KMTPlan.A6.ssuBtwistExBdd`, and `Work.KMTPlan.A6.ssuMainBound`), and — crucially — it is the
form the A6 small-scale assembly consumes, because every bump that occurs there (`varphiNt`,
`varphitildeNt`, their polynomial modifications `varphiNtj`/`varphitildeNtj`, and `randSymb`
combinations of them) is essentially bounded.

*Why the boundedness hypotheses cannot be dropped*: without them, `Tm ρ l φ f` is defined through
`iwKernel (iwSymbolSet (diffFreqs ρ l) (periodize φ))`, and the value of that `tsum` is Mathlib's
junk value `0` on non-summable families; for a measurable bump with
`iwSymbolSet … (periodize φ) ∈ L¹ \ L²` and `f ∈ ℓ² \ ℓ¹` the two sides of the estimate are not
comparable, and the statement is not provable (verified by two independent provers of
`KMTPlan/A6/ssuBandProjectionF` and `KMTPlan/A6/ssuProjZeroGen`). -/
def SSUBodyAtLinf (P : Polynomial ℤ) (cS : ℝ) (Cssu : NNReal) (ρ : ℝ) : Prop :=
  ∀ (l₁ l₂ u : ℕ) (φ ψ : ℝ → ℂ) (f g : ℤ → ℂ),
    (max l₁ l₂ : ℝ) ≤ (u : ℝ) →
    (2 : ℝ) ^ (ρ * (max l₁ l₂ : ℝ)) ≤ (u : ℝ) →
    MeasureTheory.MemLp f 2 MeasureTheory.Measure.count →
    MeasureTheory.MemLp g 2 MeasureTheory.Measure.count →
    MeasureTheory.MemLp (Work.Analysis.IonescuWainger.periodize φ) ⊤
      Work.Analysis.IonescuWainger.circleMeasure →
    MeasureTheory.MemLp (Work.Analysis.IonescuWainger.periodize ψ) ⊤
      Work.Analysis.IonescuWainger.circleMeasure →
    (∀ ξ : ℝ, φ ξ ≠ 0 → |ξ| ≤ (2 : ℝ) ^ (-(3 * (u : ℤ)))) →
    (∀ ξ : ℝ, ψ ξ ≠ 0 → |ξ| ≤ (2 : ℝ) ^ (-(3 * (P.natDegree : ℤ) * (u : ℤ)))) →
    MeasureTheory.eLpNorm (fun x : ℤ => BtwistEx ρ P l₁ l₂
        (Work.KMTAreas.A7.mStarF u) (Work.KMTAreas.A7.mStargF P.natDegree u)
        (Work.KMTAreas.A7.Tm ρ l₁ φ f) (Work.KMTAreas.A7.Tm ρ l₂ ψ g) x)
      1 MeasureTheory.Measure.count
    ≤ (Cssu : ENNReal) * ENNReal.ofReal ((2 : ℝ) ^ (-(cS * (max (l₁ : ℝ) (l₂ : ℝ)))))
        * MeasureTheory.eLpNorm (Work.KMTAreas.A7.Tm ρ l₁ φ f) 2 MeasureTheory.Measure.count
        * MeasureTheory.eLpNorm (Work.KMTAreas.A7.Tm ρ l₂ ψ g) 2 MeasureTheory.Measure.count

/-- **`SSUShape P` with the boundedness hypotheses on the bumps** — the shape proved by
`Work.KMTPlan.A6.ssuBtwistExBdd`. -/
def SSUShapeLinf (P : Polynomial ℤ) : Prop :=
  ∃ c : ℝ, 0 < c ∧ ∃ ρ₀ : ℝ, 0 < ρ₀ ∧ ∀ ρ : ℝ, 0 < ρ → ρ ≤ ρ₀ →
    ∃ C : NNReal, 0 < C ∧ SSUBodyAtLinf P c C ρ

/-- **The `ρ`-instantiated body of the paper's Lemma `ssu`.**  This is the shape in which every
consumer of `SSUShape` uses it: the single-scale estimate at a *fixed* `ρ`, with the gain
`2^{-cS·max(l₁,l₂)}` and the constant `Cssu`, for all bumps `φ, ψ` supported in the narrow arcs
`2^{-3u}`, `2^{-3du}` and all `ℓ²` inputs.  Abstracting it as a `def` keeps the statements of the
Rademacher--Menshov step and of the spike bound short. -/
def SSUBodyAt (P : Polynomial ℤ) (cS : ℝ) (Cssu : NNReal) (ρ : ℝ) : Prop :=
  ∀ (l₁ l₂ u : ℕ) (φ ψ : ℝ → ℂ) (f g : ℤ → ℂ),
    (max l₁ l₂ : ℝ) ≤ (u : ℝ) →
    (2 : ℝ) ^ (ρ * (max l₁ l₂ : ℝ)) ≤ (u : ℝ) →
    MeasureTheory.MemLp f 2 MeasureTheory.Measure.count →
    MeasureTheory.MemLp g 2 MeasureTheory.Measure.count →
    (∀ ξ : ℝ, φ ξ ≠ 0 → |ξ| ≤ (2 : ℝ) ^ (-(3 * (u : ℤ)))) →
    (∀ ξ : ℝ, ψ ξ ≠ 0 → |ξ| ≤ (2 : ℝ) ^ (-(3 * (P.natDegree : ℤ) * (u : ℤ)))) →
    MeasureTheory.eLpNorm (fun x : ℤ => BtwistEx ρ P l₁ l₂
        (Work.KMTAreas.A7.mStarF u) (Work.KMTAreas.A7.mStargF P.natDegree u)
        (Work.KMTAreas.A7.Tm ρ l₁ φ f) (Work.KMTAreas.A7.Tm ρ l₂ ψ g) x)
      1 MeasureTheory.Measure.count
    ≤ (Cssu : ENNReal) * ENNReal.ofReal ((2 : ℝ) ^ (-(cS * (max (l₁ : ℝ) (l₂ : ℝ)))))
        * MeasureTheory.eLpNorm (Work.KMTAreas.A7.Tm ρ l₁ φ f) 2 MeasureTheory.Measure.count
        * MeasureTheory.eLpNorm (Work.KMTAreas.A7.Tm ρ l₂ ψ g) 2 MeasureTheory.Measure.count

/-- **The `ℓ²` bound for the randomised `f`-side symbol, as a standalone interface.**  This is
the conclusion of `Work.KMTPlan.A6.tmRandSymb_l2` (`LowSmallAux`-based form) and one of the two
hypotheses of the Rademacher--Menshov step. -/
def TmRandL2ShapeF (P : Polynomial ℤ) (C₀ : ℕ) : Prop :=
  ∃ ρ₀ : ℝ, 0 < ρ₀ ∧ ∀ ρ : ℝ, 0 < ρ → ρ ≤ ρ₀ → ∃ C : NNReal → NNReal,
    ∀ (a : ℕ → NNReal) (Λ : NNReal) (l₁ l₂ k₁ k₂ K : ℕ) (t : ℝ) (ε : ℕ → ℂ) (f : ℤ → ℂ),
      1 < Λ → PointwiseErgodicTheorems.Lacunary Λ a → (∀ n, 1 ≤ a n) →
      (∀ n, ‖ε n‖ ≤ 1) → t ∈ Set.Icc (1 / 2 : ℝ) 1 →
      MeasureTheory.MemLp f 2 MeasureTheory.Measure.count →
      MeasureTheory.eLpNorm (Work.KMTAreas.A7.Tm ρ l₁
          (Work.KMTAreas.A7.randSymb (lowSymbF ρ C₀ a l₁ l₂ k₁ k₂ t) ε K) f)
        2 MeasureTheory.Measure.count
      ≤ (C Λ : ENNReal) * MeasureTheory.eLpNorm f 2 MeasureTheory.Measure.count

/-- **The `ℓ²` bound for the randomised `g`-side symbol** (the mirror of `TmRandL2ShapeF`). -/
def TmRandL2ShapeG (P : Polynomial ℤ) (C₀ : ℕ) : Prop :=
  ∃ ρ₀ : ℝ, 0 < ρ₀ ∧ ∀ ρ : ℝ, 0 < ρ → ρ ≤ ρ₀ → ∃ C : NNReal → NNReal,
    ∀ (a : ℕ → NNReal) (Λ : NNReal) (l₁ l₂ k₁ k₂ K : ℕ) (t : ℝ) (ε : ℕ → ℂ) (g : ℤ → ℂ),
      1 < Λ → PointwiseErgodicTheorems.Lacunary Λ a → (∀ n, 1 ≤ a n) →
      (∀ n, ‖ε n‖ ≤ 1) → t ∈ Set.Icc (1 / 2 : ℝ) 1 →
      MeasureTheory.MemLp g 2 MeasureTheory.Measure.count →
      MeasureTheory.eLpNorm (Work.KMTAreas.A7.Tm ρ l₂
          (Work.KMTAreas.A7.randSymb (lowSymbG ρ P C₀ a l₁ l₂ k₁ k₂ t) ε K) g)
        2 MeasureTheory.Measure.count
      ≤ (C Λ : ENNReal) * MeasureTheory.eLpNorm g 2 MeasureTheory.Measure.count

/-! ## The interface of the single-scale estimate (the paper's Lemma `ssu`)

`SSUShape P` is the paper's Lemma `ssu` at `BtwistEx` in the form in which the assembly consumes
it: for `φ, ψ` supported in the narrow arcs of scales `2^{-3u}`, `2^{-3du}` and with
`max l₁ l₂ ≤ u`, `2^{ρ max l₁ l₂} ≤ u`, the twisted bilinear multiplier with the narrow window
`m_*` obeys the `ℓ² × ℓ² → ℓ¹` bound with the gain `2^{-c max(l₁,l₂)}`.  It is the conclusion of
`Work.KMTPlan.A6.ssuModelGain` (spawned this session); the assembly below only uses it through
`lowRandBound_of_ssu`. -/
def SSUShape (P : Polynomial ℤ) : Prop :=
  ∃ c : ℝ, 0 < c ∧ ∃ ρ₀ : ℝ, 0 < ρ₀ ∧ ∀ ρ : ℝ, 0 < ρ → ρ ≤ ρ₀ →
    ∃ C : NNReal, 0 < C ∧
    ∀ (l₁ l₂ u : ℕ) (φ ψ : ℝ → ℂ) (f g : ℤ → ℂ),
      (max l₁ l₂ : ℝ) ≤ (u : ℝ) →
      (2 : ℝ) ^ (ρ * (max l₁ l₂ : ℝ)) ≤ (u : ℝ) →
      MeasureTheory.MemLp f 2 MeasureTheory.Measure.count →
      MeasureTheory.MemLp g 2 MeasureTheory.Measure.count →
      (∀ ξ : ℝ, φ ξ ≠ 0 → |ξ| ≤ (2 : ℝ) ^ (-(3 * (u : ℤ)))) →
      (∀ ξ : ℝ, ψ ξ ≠ 0 → |ξ| ≤ (2 : ℝ) ^ (-(3 * (P.natDegree : ℤ) * (u : ℤ)))) →
      MeasureTheory.eLpNorm (fun x : ℤ => BtwistEx ρ P l₁ l₂
          (Work.KMTAreas.A7.mStarF u)
          (Work.KMTAreas.A7.mStargF P.natDegree u)
          (Work.KMTAreas.A7.Tm ρ l₁ φ f)
          (Work.KMTAreas.A7.Tm ρ l₂ ψ g) x)
        1 MeasureTheory.Measure.count
      ≤ (C : ENNReal) * ENNReal.ofReal ((2 : ℝ) ^ (-(c * (max (l₁ : ℝ) (l₂ : ℝ)))))
          * MeasureTheory.eLpNorm (Work.KMTAreas.A7.Tm ρ l₁ φ f) 2 MeasureTheory.Measure.count
          * MeasureTheory.eLpNorm (Work.KMTAreas.A7.Tm ρ l₂ ψ g) 2 MeasureTheory.Measure.count


/-- The `ρ`-instantiated version of `TmRandL2ShapeF`. -/
def TmRandL2AtF (P : Polynomial ℤ) (C₀ : ℕ) (ρ : ℝ) : Prop :=
  ∃ C : NNReal → NNReal,
    ∀ (a : ℕ → NNReal) (Λ : NNReal) (l₁ l₂ k₁ k₂ K : ℕ) (t : ℝ) (ε : ℕ → ℂ) (f : ℤ → ℂ),
      1 < Λ → PointwiseErgodicTheorems.Lacunary Λ a → (∀ n, 1 ≤ a n) →
      (∀ n, ‖ε n‖ ≤ 1) → t ∈ Set.Icc (1 / 2 : ℝ) 1 →
      MeasureTheory.MemLp f 2 MeasureTheory.Measure.count →
      MeasureTheory.eLpNorm (Work.KMTAreas.A7.Tm ρ l₁
          (Work.KMTAreas.A7.randSymb (lowSymbF ρ C₀ a l₁ l₂ k₁ k₂ t) ε K) f)
        2 MeasureTheory.Measure.count
      ≤ (C Λ : ENNReal) * MeasureTheory.eLpNorm f 2 MeasureTheory.Measure.count

/-- The `ρ`-instantiated version of `TmRandL2ShapeG`. -/
def TmRandL2AtG (P : Polynomial ℤ) (C₀ : ℕ) (ρ : ℝ) : Prop :=
  ∃ C : NNReal → NNReal,
    ∀ (a : ℕ → NNReal) (Λ : NNReal) (l₁ l₂ k₁ k₂ K : ℕ) (t : ℝ) (ε : ℕ → ℂ) (g : ℤ → ℂ),
      1 < Λ → PointwiseErgodicTheorems.Lacunary Λ a → (∀ n, 1 ≤ a n) →
      (∀ n, ‖ε n‖ ≤ 1) → t ∈ Set.Icc (1 / 2 : ℝ) 1 →
      MeasureTheory.MemLp g 2 MeasureTheory.Measure.count →
      MeasureTheory.eLpNorm (Work.KMTAreas.A7.Tm ρ l₂
          (Work.KMTAreas.A7.randSymb (lowSymbG ρ P C₀ a l₁ l₂ k₁ k₂ t) ε K) g)
        2 MeasureTheory.Measure.count
      ≤ (C Λ : ENNReal) * MeasureTheory.eLpNorm g 2 MeasureTheory.Measure.count

/-- **Destructuring `SSUShape` into the normal form used by the assembly.**  Produces the gain
exponent `cS`, the threshold `ρ₀`, and a `ρ`-indexed family of constants `Cssu` together with the
body `SSUBody P cS (Cssu ρ)` — which is exactly the hypothesis consumed by `RMStepShape`. -/
theorem exists_ssuBodyAt_of_ssuShape {P : Polynomial ℤ} (h : SSUShape P) :
    ∃ cS : ℝ, 0 < cS ∧ ∃ ρ₀ : ℝ, 0 < ρ₀ ∧
      ∀ ρ : ℝ, 0 < ρ → ρ ≤ ρ₀ → ∃ Cssu : NNReal, 0 < Cssu ∧ SSUBodyAt P cS Cssu ρ := h


/-- **Destructuring `SSUShapeLinf`** (the bounded-bump form). -/
theorem exists_ssuBodyAtLinf_of_ssuShapeLinf {P : Polynomial ℤ} (h : SSUShapeLinf P) :
    ∃ cS : ℝ, 0 < cS ∧ ∃ ρ₀ : ℝ, 0 < ρ₀ ∧
      ∀ ρ : ℝ, 0 < ρ → ρ ≤ ρ₀ → ∃ Cssu : NNReal, 0 < Cssu ∧ SSUBodyAtLinf P cS Cssu ρ := h

/-- `TmRandL2ShapeF` gives `TmRandL2AtF` for every `ρ` below the threshold. -/
theorem tmRandL2AtF_of_shape {P : Polynomial ℤ} {C₀ : ℕ} (h : TmRandL2ShapeF P C₀) :
    ∃ ρ₀ : ℝ, 0 < ρ₀ ∧ ∀ ρ : ℝ, 0 < ρ → ρ ≤ ρ₀ → TmRandL2AtF P C₀ ρ := h

/-- `TmRandL2ShapeG` gives `TmRandL2AtG` for every `ρ` below the threshold. -/
theorem tmRandL2AtG_of_shape {P : Polynomial ℤ} {C₀ : ℕ} (h : TmRandL2ShapeG P C₀) :
    ∃ ρ₀ : ℝ, 0 < ρ₀ ∧ ∀ ρ : ℝ, 0 < ρ → ρ ≤ ρ₀ → TmRandL2AtG P C₀ ρ := h



/-- The logarithmic threshold of the small-scale assembly, as a function of `Λ`:
`D = log 2 / log Λ + 2`.  (At `Λ = 1` the Lean division convention gives `D = 2`; the assembly only
uses `D` under the hypothesis `1 < Λ`, where `0 < D` holds.) -/
noncomputable def lowD (Λ : NNReal) : ℝ := Real.log 2 / Real.log (Λ : ℝ) + 2

/-- The explicit constant of the logarithmic truncation bound, as a function of `Λ`: this is the
`M` of `Work.KMTPlan.A6.lowTruncLogBound`, made into a total function of `Λ` so that it can appear
inside a constant `NNReal → NNReal`. -/
noncomputable def lowMfun (Λ : NNReal) : ℝ := (5 + max 0 (Real.logb 2 (lowD Λ))) ^ 2

theorem lowMfun_nonneg (Λ : NNReal) : 0 ≤ lowMfun Λ := by
  rw [lowMfun]; positivity

theorem lowTruncLogBoundM (ρ : ℝ) (hρ : 0 < ρ) (Λ : NNReal) (hΛ : 1 < Λ) (L : ℕ) :
    (Real.logb 2 (((Nat.ceil (lowD Λ * (2 : ℝ) ^ (Work.KMTAreas.A7.uScale ρ L)) + 2 : ℕ) : ℝ))
        + 2) ^ 2 ≤ lowMfun Λ * (2 : ℝ) ^ (4 * ρ * (L : ℝ)) := by
  have hD : 0 < lowD Λ := by
    rw [lowD]
    have hlog : 0 < Real.log (Λ : ℝ) := Real.log_pos (by exact_mod_cast hΛ)
    positivity
  have hmain :
      (Real.logb 2 (((Nat.ceil (lowD Λ * (2 : ℝ) ^ (Work.KMTAreas.A7.uScale ρ L)) + 2 : ℕ) : ℝ))
        + 2) ^ 2 ≤ (5 + max 0 (Real.logb 2 (lowD Λ))) ^ 2
          * (2 : ℝ) ^ (4 * ρ * (L : ℝ)) := by
    set u : ℕ := Work.KMTAreas.A7.uScale ρ L with hu
    set Y : ℝ := (2 : ℝ) ^ (2 * ρ * (L : ℝ)) with hY
    set x : ℝ := (lowD Λ) * (2 : ℝ) ^ u with hx
    have hxpos : 0 < x := by rw [hx]; positivity
    have hY1 : 1 ≤ Y := by rw [hY]; exact Real.one_le_rpow (by norm_num) (by positivity)
    have hu_le_Y : (u : ℝ) ≤ Y := by
      rw [hu, hY, Work.KMTAreas.A7.uScale, Work.Analysis.EndVar.scaleCount]
      simp only [Nat.cast_one, one_mul, Int.floor_toNat]
      exact Nat.floor_le (Real.rpow_nonneg (by norm_num) _)
    have hceil : ((Nat.ceil x : ℕ) : ℝ) < x + 1 := Nat.ceil_lt_add_one hxpos.le
    have hnpos : (0 : ℝ) < ((Nat.ceil x + 2 : ℕ) : ℝ) := by
      have h : (0 : ℝ) < ((Nat.ceil x : ℕ) : ℝ) := lt_of_lt_of_le hxpos (Nat.le_ceil x)
      push_cast
      linarith
    have hnle : ((Nat.ceil x + 2 : ℕ) : ℝ) ≤ x + 3 := by
      push_cast; linarith [hceil]
    have hn1 : (1 : ℝ) ≤ ((Nat.ceil x + 2 : ℕ) : ℝ) := by
      have := Nat.cast_nonneg (α := ℝ) (Nat.ceil x); push_cast; linarith
    have hstep1 : Real.logb 2 ((Nat.ceil x + 2 : ℕ) : ℝ) ≤ Real.logb 2 (x + 3) :=
      Real.logb_le_logb_of_le (b := 2) (by norm_num) hnpos hnle
    have hstep2 : x + 3 ≤ 4 * max 1 x := by
      rcases lt_or_ge x 1 with h | h
      · rw [max_eq_left h.le]; linarith
      · rw [max_eq_right h]; linarith
    have hmax : Real.logb 2 (max 1 x) = max 0 (Real.logb 2 x) := by
      rcases lt_or_ge x 1 with h | h
      · rw [max_eq_left h.le, Real.logb_one]
        have hneg : Real.logb 2 x ≤ 0 := by
          have := Real.logb_le_logb_of_le (b := 2) (by norm_num : (1 : ℝ) < 2) hxpos h.le
          rwa [Real.logb_one] at this
        rw [max_eq_left hneg]
      · rw [max_eq_right h, max_eq_right (Real.logb_nonneg (by norm_num : (1 : ℝ) < 2) h)]
    have hlog2 : Real.logb 2 (x + 3) ≤ 2 + max 0 (Real.logb 2 x) := by
      have hmono := Real.logb_le_logb_of_le (b := 2) (by norm_num : (1 : ℝ) < 2)
        (by linarith : (0 : ℝ) < x + 3) hstep2
      have hmul4 : Real.logb 2 (4 * max 1 x) = 2 + max 0 (Real.logb 2 x) := by
        rw [Real.logb_mul (b := 2) (by norm_num : (4 : ℝ) ≠ 0)
             (ne_of_gt (lt_of_lt_of_le zero_lt_one (le_max_left 1 x))), hmax]
        have h4 : Real.logb 2 (4 : ℝ) = 2 := by
          have h42 : (4 : ℝ) = 2 ^ 2 := by norm_num
          rw [h42, Real.logb_pow, Real.logb_self_eq_one (by norm_num : (1 : ℝ) < 2), mul_one]
          norm_num
        rw [h4]
      rwa [hmul4] at hmono
    have hlog3 : Real.logb 2 x = Real.logb 2 (lowD Λ) + (u : ℝ) := by
      have hpowpos : (0 : ℝ) < (2 : ℝ) ^ u := by positivity
      have ha := Real.logb_mul (b := 2) (ne_of_gt hD) (ne_of_gt hpowpos)
      rw [← hx] at ha
      rw [ha, Real.logb_pow, Real.logb_self_eq_one (by norm_num : (1 : ℝ) < 2), mul_one]
    have hmax_le : max 0 (Real.logb 2 x) ≤ max 0 (Real.logb 2 (lowD Λ)) + Y := by
      rw [hlog3]
      have h1 : max 0 (Real.logb 2 (lowD Λ) + (u : ℝ)) ≤ max 0 (Real.logb 2 (lowD Λ)) + (u : ℝ) :=
        max_le (by positivity) (by linarith [le_max_right (0 : ℝ) (Real.logb 2 (lowD Λ))])
      linarith [hu_le_Y]
    have hfinal : Real.logb 2 ((Nat.ceil x + 2 : ℕ) : ℝ) + 2
        ≤ (5 + max 0 (Real.logb 2 (lowD Λ))) * Y := by
      have h1 : Real.logb 2 ((Nat.ceil x + 2 : ℕ) : ℝ) + 2
          ≤ 4 + max 0 (Real.logb 2 x) := by
        linarith [hstep1, hlog2]
      have h3 : 4 + (max 0 (Real.logb 2 (lowD Λ)) + Y) ≤ (5 + max 0 (Real.logb 2 (lowD Λ))) * Y := by
        have hc : 0 ≤ max 0 (Real.logb 2 (lowD Λ)) := le_max_left _ _
        nlinarith [mul_nonneg (by linarith : (0 : ℝ) ≤ 4 + max 0 (Real.logb 2 (lowD Λ)))
          (by linarith : (0 : ℝ) ≤ Y - 1)]
      linarith
    have hYsq : Y ^ 2 = (2 : ℝ) ^ (4 * ρ * (L : ℝ)) := by
      rw [hY, ← Real.rpow_natCast ((2 : ℝ) ^ (2 * ρ * (L : ℝ))) 2,
        ← Real.rpow_mul (by norm_num : (0 : ℝ) ≤ 2)]
      congr 1; ring
    have hnn : 0 ≤ (5 + max 0 (Real.logb 2 (lowD Λ))) * Y :=
      mul_nonneg (by linarith [le_max_left (0 : ℝ) (Real.logb 2 (lowD Λ))]) (by linarith)
    have hnn2 : 0 ≤ Real.logb 2 ((Nat.ceil x + 2 : ℕ) : ℝ) + 2 := by
      have := Real.logb_nonneg (b := 2) (by norm_num : (1 : ℝ) < 2) hn1
      linarith
    calc (Real.logb 2 ((Nat.ceil x + 2 : ℕ) : ℝ) + 2) ^ 2
        ≤ ((5 + max 0 (Real.logb 2 (lowD Λ))) * Y) ^ 2 := pow_le_pow_left₀ hnn2 hfinal 2
      _ = (5 + max 0 (Real.logb 2 (lowD Λ))) ^ 2 * Y ^ 2 := by ring
      _ = (5 + max 0 (Real.logb 2 (lowD Λ))) ^ 2 * (2 : ℝ) ^ (4 * ρ * (L : ℝ)) := by rw [hYsq]
  rw [lowMfun]
  exact hmain

/-- `Nat.log2` is bounded by `Real.logb 2` (the former is the floor of the latter). -/
theorem nat_log2_cast_le_logb (n : ℕ) :
    (Nat.log2 n : ℝ) ≤ Real.logb 2 (n : ℝ) := Real.log2_le_logb n


/-- **The `Λ`-dependent threshold of the sharp logarithmic truncation bound**, as a total function
of `Λ` (so that it may be used inside a constant `NNReal → NNReal`).  It is the `B` of
`Work.KMTPlan.A6.lowSmallSet_le_log_sharp` at `(ρ, C₀, Λ)`; see `lowLogB_spec`. -/
noncomputable def lowLogB (ρ : ℝ) (C₀ : ℕ) (Λ : NNReal) : ℕ :=
  if h : 0 < ρ ∧ 1 < Λ then
    Classical.choose (Work.KMTPlan.A6.lowSmallSet_le_log_sharp ρ h.1 C₀ Λ h.2)
  else 0

/-- The defining property of `lowLogB`. -/
theorem lowLogB_spec (ρ : ℝ) (hρ : 0 < ρ) (C₀ : ℕ) (Λ : NNReal) (hΛ : 1 < Λ) :
    ∀ (a : ℕ → NNReal) (l₁ l₂ k₁ k₂ n : ℕ),
      PointwiseErgodicTheorems.Lacunary Λ a → (∀ n, 1 ≤ a n) →
      lowLogB ρ C₀ Λ ≤ lcL l₁ l₂ k₁ k₂ → lowSmallSet ρ C₀ a l₁ l₂ k₁ k₂ n →
      (n : ℝ) + 1 ≤ lowD Λ * (2 : ℝ) ^ (Work.KMTAreas.A7.uScale ρ (lcL l₁ l₂ k₁ k₂)) := by
  intro a l₁ l₂ k₁ k₂ n ha ha1 hB hsm
  have heq : lowLogB ρ C₀ Λ
      = Classical.choose (Work.KMTPlan.A6.lowSmallSet_le_log_sharp ρ hρ C₀ Λ hΛ) := by
    rw [lowLogB, dif_pos ⟨hρ, hΛ⟩]
  rw [heq] at hB
  have hspec := Classical.choose_spec
    (Work.KMTPlan.A6.lowSmallSet_le_log_sharp ρ hρ C₀ Λ hΛ)
  have h := hspec a l₁ l₂ k₁ k₂ n ha ha1 hB hsm
  simpa only [lowD] using h


/-- **`SSUShape` implies `SSUShapeLinf`** (the latter has two more hypotheses and hence a weaker,
provable statement). -/
theorem ssuShapeLinf_of_ssuShape {P : Polynomial ℤ} (h : SSUShape P) : SSUShapeLinf P := by
  obtain ⟨c, hc, ρ₀, hρ₀, hbody⟩ := h
  refine ⟨c, hc, ρ₀, hρ₀, fun ρ hρ hρle => ?_⟩
  obtain ⟨C, hC, hb⟩ := hbody ρ hρ hρle
  exact ⟨C, hC, fun l₁ l₂ u φ ψ f g hm1 hm2 hf hg _ _ hφ hψ =>
    hb l₁ l₂ u φ ψ f g hm1 hm2 hf hg hφ hψ⟩

/-- **The conclusion of `lowSmallModelVar`, abstracted as a shape.** -/
def LowModelVarShape (P : Polynomial ℤ) (r : NNReal) (C₀ : ℕ) : Prop :=
  ∃ c : ℝ, 0 < c ∧ ∃ ρ₀ : ℝ, 0 < ρ₀ ∧ ∀ ρ : ℝ, 0 < ρ → ρ ≤ ρ₀ →
    ∃ C : NNReal → NNReal,
      ∀ (a : ℕ → NNReal) (Λ : NNReal) (l₁ l₂ k₁ k₂ : ℕ) (f g : ℤ → ℂ),
        1 < Λ → PointwiseErgodicTheorems.Lacunary Λ a → (∀ n, 1 ≤ a n) →
        (k₁ = 0 ∨ k₂ = 0) →
        MeasureTheory.MemLp f 2 MeasureTheory.Measure.count →
        MeasureTheory.MemLp g 2 MeasureTheory.Measure.count →
        lcL l₁ l₂ k₁ k₂ ≤ 2 * Work.KMTAreas.A7.uScale ρ (lcL l₁ l₂ k₁ k₂) →
        MeasureTheory.eLpNorm (fun x : ℤ =>
            PointwiseErgodicTheorems.variationalNorm r
              (fun n : ℕ => lowModel ρ P C₀ a f g l₁ l₂ k₁ k₂ n x))
          1 MeasureTheory.Measure.count
          ≤ (C Λ : ENNReal) * ENNReal.ofReal (lcWeight c l₁ l₂ k₁ k₂) *
              MeasureTheory.eLpNorm f 2 MeasureTheory.Measure.count
              * MeasureTheory.eLpNorm g 2 MeasureTheory.Measure.count

/-- **Case B as a shape** (the conclusion of `Work.KMTPlan.A6.lowModelVarCaseB`). -/
def LowModelCaseBShape (P : Polynomial ℤ) (r : NNReal) (C₀ : ℕ) : Prop :=
  ∃ c : ℝ, 0 < c ∧ ∃ ρ₀ : ℝ, 0 < ρ₀ ∧ ∀ ρ : ℝ, 0 < ρ → ρ ≤ ρ₀ →
    ∃ C : NNReal → NNReal, ∃ B : ℕ,
      ∀ (a : ℕ → NNReal) (Λ : NNReal) (l₁ l₂ k₁ k₂ : ℕ) (f g : ℤ → ℂ),
        1 < Λ → PointwiseErgodicTheorems.Lacunary Λ a → (∀ n, 1 ≤ a n) →
        (k₁ = 0 ∨ k₂ = 0) →
        B ≤ lcL l₁ l₂ k₁ k₂ →
        max l₁ l₂ < lcL l₁ l₂ k₁ k₂ →
        lcL l₁ l₂ k₁ k₂ ≤ 2 * Work.KMTAreas.A7.uScale ρ (lcL l₁ l₂ k₁ k₂) →
        MeasureTheory.MemLp f 2 MeasureTheory.Measure.count →
        MeasureTheory.MemLp g 2 MeasureTheory.Measure.count →
        MeasureTheory.eLpNorm (fun x : ℤ =>
            PointwiseErgodicTheorems.variationalNorm r
              (fun n : ℕ => lowModel ρ P C₀ a f g l₁ l₂ k₁ k₂ n x))
          1 MeasureTheory.Measure.count
          ≤ (C Λ : ENNReal) * ENNReal.ofReal (lcWeight c l₁ l₂ k₁ k₂) *
              MeasureTheory.eLpNorm f 2 MeasureTheory.Measure.count
              * MeasureTheory.eLpNorm g 2 MeasureTheory.Measure.count

end

end Work.KMTPlan.A6
