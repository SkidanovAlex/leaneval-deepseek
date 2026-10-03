import Mathlib
import Submission.Work.KMTPlan.A6.LowModelVarCaseBAux
import Submission.Work.KMTPlan.A6.VrFull_TmBtwist_le_rand_abs
import Submission.Work.KMTPlan.A6.tmRandSymb_l2

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

/-! ## The non-singularity condition on the modified bumps

The modified bumps `varphiNtj N k j t` (`j`-th power of the frequency variable times the modulated
bump) are `C²` with compact support exactly when the weight `(2^{-k}Nξ)^j` is not singular at the
frequency origin.  For `j ∈ {-1,0,1}` this is the disjunction `k ≠ 0 ∨ 0 ≤ j`; it is implied by the
paper's exclusion of the pair `(k,j) = (0,-1)`. -/

theorem modBump_nonsingular (k : ℕ) (j : ℤ) (hj : j ∈ ({-1, 0, 1} : Finset ℤ))
    (hk : ¬ (k = 0 ∧ j = -1)) : k ≠ 0 ∨ 0 ≤ j := by
  simp only [Finset.mem_insert, Finset.mem_singleton] at hj
  rcases hj with h | h | h
  · subst h
    by_contra hcon
    push_neg at hcon
    exact hk ⟨hcon.1, rfl⟩
  · subst h
    exact Or.inr (by norm_num)
  · subst h
    exact Or.inr (by norm_num)

/-! ## The `TmSide` side conditions for the single modified bumps -/

/-- **The three `TmSide` conditions for the modified `f`-side bump `varphiNtj N k j t`**
(`j ∈ ℤ` with `k ≠ 0 ∨ 0 ≤ j`, `t ∈ [1/2,1]`): the translates are summable, the Ionescu--Wainger
symbol of the periodisation is integrable on the circle, and the kernel of that symbol is square
summable.  This is `tmSide_of_bump` applied to `varphiNtj N k j t`, whose `C²`, compact support and
support radius come from `varphiNtj_bounds` and `varphiNt_support_all`. -/
theorem tmSideBumpNtj (ρ : ℝ) (l N k : ℕ) (j : ℤ) (t : ℝ)
    (hk : k ≠ 0 ∨ 0 ≤ j) (ht : t ∈ Set.Icc (1 / 2 : ℝ) 1) :
    (∀ x : ℝ, Summable fun i : ℤ => varphiNtj N k j t (x + (i : ℝ))) ∧
      MeasureTheory.Integrable (iwSymbolSet (diffFreqs ρ l) (periodize (varphiNtj N k j t)))
        circleMeasure ∧
      Summable fun i : ℤ => ‖Work.Analysis.IWMultiplier.iwKernel
        (iwSymbolSet (diffFreqs ρ l) (periodize (varphiNtj N k j t))) i‖ ^ 2 := by
  obtain ⟨S, hSnn, hbd⟩ := varphiNtj_bounds N k j hk
  have hcd : ContDiff ℝ 2 (varphiNtj N k j t) := (hbd t ht).1
  have hcs : HasCompactSupport (varphiNtj N k j t) := (hbd t ht).2.1
  obtain ⟨C, hC⟩ := hcs.exists_bound_of_continuous hcd.continuous
  have hR : (0 : ℝ) ≤ (2 : ℝ) ^ ((k : ℝ) - (Work.Analysis.EndVar.logN N : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  refine tmSide_of_bump ρ l (varphiNtj N k j t)
    ((2 : ℝ) ^ ((k : ℝ) - (Work.Analysis.EndVar.logN N : ℝ))) C hR
    hcd.continuous.measurable ?_ hC hcd hcs
  intro x hx
  by_contra hne
  have h1 : varphiNt N k t x ≠ 0 := by
    intro h
    exact hne (by simp only [varphiNtj, h, mul_zero])
  exact absurd hx (not_lt.mpr (varphiNt_support N k t x h1))

/-- **The three `TmSide` conditions for the modified `g`-side bump `varphitildeNtj P N k j t`**
(the `d`-fold analogue of `tmSideBumpNtj`, with `d = P.natDegree`). -/
theorem tmSideBumpNtjG (ρ : ℝ) (l : ℕ) (P : Polynomial ℤ) (N k : ℕ) (j : ℤ) (t : ℝ)
    (hk : k ≠ 0 ∨ 0 ≤ j) (ht : t ∈ Set.Icc (1 / 2 : ℝ) 1) :
    (∀ x : ℝ, Summable fun i : ℤ => varphitildeNtj P N k j t (x + (i : ℝ))) ∧
      MeasureTheory.Integrable (iwSymbolSet (diffFreqs ρ l) (periodize (varphitildeNtj P N k j t)))
        circleMeasure ∧
      Summable fun i : ℤ => ‖Work.Analysis.IWMultiplier.iwKernel
        (iwSymbolSet (diffFreqs ρ l) (periodize (varphitildeNtj P N k j t))) i‖ ^ 2 := by
  obtain ⟨S, hSnn, hbd⟩ := varphitildeNtj_bounds P N k j hk
  have hcd : ContDiff ℝ 2 (varphitildeNtj P N k j t) := (hbd t ht).1
  have hcs : HasCompactSupport (varphitildeNtj P N k j t) := (hbd t ht).2.1
  obtain ⟨C, hC⟩ := hcs.exists_bound_of_continuous hcd.continuous
  have hR : (0 : ℝ) ≤
      (2 : ℝ) ^ ((P.natDegree : ℝ) * ((k : ℝ) - (Work.Analysis.EndVar.logN N : ℝ))) :=
    Real.rpow_nonneg (by norm_num) _
  refine tmSide_of_bump ρ l (varphitildeNtj P N k j t)
    ((2 : ℝ) ^ ((P.natDegree : ℝ) * ((k : ℝ) - (Work.Analysis.EndVar.logN N : ℝ)))) C hR
    hcd.continuous.measurable ?_ hC hcd hcs
  intro x hx
  by_contra hne
  have h1 : varphitildeNt P P.natDegree N k t x ≠ 0 := by
    intro h
    exact hne (by simp only [varphitildeNtj, h, mul_zero])
  exact absurd hx (not_lt.mpr (varphitildeNt_support_all P P.natDegree N k t x h1))

/-! ## Pointwise boundedness of the `Tm`-images of the clamped families -/

/-- **Pointwise boundedness of `Tm ρ l₁ (lowModSymbF … k) f`.**  Each member of the clamped,
anchored family `lowModSymbF` is either `0` (at `k = 0` and off `lowSmallSet`) or the modified
bump `varphiNtj ⌊a k⌋ k₁ j₁ t`; in the first case `Tm` vanishes (`Tm_zero`), in the second
`Tm_bdd_of_l2` bounds the multiplier image by a constant times the `ℓ²` norm of `f`. -/
theorem tmBddLowModSymbF (ρ : ℝ) (C₀ : ℕ) (a : ℕ → NNReal) (l₁ l₂ k₁ k₂ : ℕ) (j₁ : ℤ)
    (t : ℝ) (hj₁ : j₁ ∈ ({-1, 0, 1} : Finset ℤ)) (hk₁ : ¬ (k₁ = 0 ∧ j₁ = -1))
    (ht : t ∈ Set.Icc (1 / 2 : ℝ) 1) (f : ℤ → ℂ)
    (hf : MeasureTheory.MemLp f 2 MeasureTheory.Measure.count) :
    ∀ k : ℕ, ∃ D : ℝ, ∀ y : ℤ,
      ‖Tm ρ l₁ (lowModSymbF ρ C₀ a l₁ l₂ k₁ k₂ j₁ t k) f y‖ ≤ D := by
  have hns : k₁ ≠ 0 ∨ 0 ≤ j₁ := modBump_nonsingular k₁ j₁ hj₁ hk₁
  intro k
  obtain ⟨S, hSnn, hbd⟩ := varphiNtj_bounds (Nat.floor (a k)) k₁ j₁ hns
  by_cases hk0 : k = 0
  · have hs : lowModSymbF ρ C₀ a l₁ l₂ k₁ k₂ j₁ t k = 0 := by
      funext ξ; simp [lowModSymbF, hk0]
    refine ⟨0, fun y => ?_⟩
    rw [hs, Tm_zero ρ l₁ f hf]
    simp
  · by_cases hls : lowSmallSet ρ C₀ a l₁ l₂ k₁ k₂ k
    · have hs : lowModSymbF ρ C₀ a l₁ l₂ k₁ k₂ j₁ t k
          = varphiNtj (Nat.floor (a k)) k₁ j₁ t := by
        funext ξ; simp [lowModSymbF, hk0, hls]
      obtain ⟨Cc, _hCc, hCc⟩ := Tm_bdd_of_l2 ρ l₁ S hSnn
      refine ⟨Cc * Real.sqrt (∑' i : ℤ, ‖f i‖ ^ 2), fun y => ?_⟩
      rw [hs]
      exact hCc (varphiNtj (Nat.floor (a k)) k₁ j₁ t) (hbd t ht).1 (hbd t ht).2.1
        (hbd t ht).2.2.1 (hbd t ht).2.2.2 f hf y
    · have hs : lowModSymbF ρ C₀ a l₁ l₂ k₁ k₂ j₁ t k = 0 := by
        funext ξ; simp [lowModSymbF, hk0, hls]
      refine ⟨0, fun y => ?_⟩
      rw [hs, Tm_zero ρ l₁ f hf]
      simp

/-- **Pointwise boundedness of `Tm ρ l₂ (lowModSymbG … k) g`** (the `g`-side analogue of
`tmBddLowModSymbF`). -/
theorem tmBddLowModSymbG (P : Polynomial ℤ) (ρ : ℝ) (C₀ : ℕ) (a : ℕ → NNReal)
    (l₁ l₂ k₁ k₂ : ℕ) (j₂ : ℤ) (t : ℝ)
    (hj₂ : j₂ ∈ ({-1, 0, 1} : Finset ℤ)) (hk₂ : ¬ (k₂ = 0 ∧ j₂ = -1))
    (ht : t ∈ Set.Icc (1 / 2 : ℝ) 1) (g : ℤ → ℂ)
    (hg : MeasureTheory.MemLp g 2 MeasureTheory.Measure.count) :
    ∀ k : ℕ, ∃ D : ℝ, ∀ y : ℤ,
      ‖Tm ρ l₂ (lowModSymbG ρ P C₀ a l₁ l₂ k₁ k₂ j₂ t k) g y‖ ≤ D := by
  have hns : k₂ ≠ 0 ∨ 0 ≤ j₂ := modBump_nonsingular k₂ j₂ hj₂ hk₂
  intro k
  obtain ⟨S, hSnn, hbd⟩ := varphitildeNtj_bounds P (Nat.floor (a k)) k₂ j₂ hns
  by_cases hk0 : k = 0
  · have hs : lowModSymbG ρ P C₀ a l₁ l₂ k₁ k₂ j₂ t k = 0 := by
      funext ξ; simp [lowModSymbG, hk0]
    refine ⟨0, fun y => ?_⟩
    rw [hs, Tm_zero ρ l₂ g hg]
    simp
  · by_cases hls : lowSmallSet ρ C₀ a l₁ l₂ k₁ k₂ k
    · have hs : lowModSymbG ρ P C₀ a l₁ l₂ k₁ k₂ j₂ t k
          = varphitildeNtj P (Nat.floor (a k)) k₂ j₂ t := by
        funext ξ; simp [lowModSymbG, hk0, hls]
      obtain ⟨Cc, _hCc, hCc⟩ := Tm_bdd_of_l2 ρ l₂ S hSnn
      refine ⟨Cc * Real.sqrt (∑' i : ℤ, ‖g i‖ ^ 2), fun y => ?_⟩
      rw [hs]
      exact hCc (varphitildeNtj P (Nat.floor (a k)) k₂ j₂ t) (hbd t ht).1 (hbd t ht).2.1
        (hbd t ht).2.2.1 (hbd t ht).2.2.2 g hg y
    · have hs : lowModSymbG ρ P C₀ a l₁ l₂ k₁ k₂ j₂ t k = 0 := by
        funext ξ; simp [lowModSymbG, hk0, hls]
      refine ⟨0, fun y => ?_⟩
      rw [hs, Tm_zero ρ l₂ g hg]
      simp

/-! ## The `TmSide` conditions for the two clamped families -/

/-- **`TmSide` for the anchored, clamped `f`-side family.**  Each member is `0` or a single
modified bump, so the three conditions of `TmSide` follow memberwise from `tmSideBumpNtj` (the
zero members trivially, via `tmSide_of_bump`). -/
theorem TmSide_lowModSymbF (ρ : ℝ) (C₀ : ℕ) (a : ℕ → NNReal) (l₁ l₂ k₁ k₂ K : ℕ) (j₁ : ℤ)
    (t : ℝ) (hj₁ : j₁ ∈ ({-1, 0, 1} : Finset ℤ)) (hk₁ : ¬ (k₁ = 0 ∧ j₁ = -1))
    (ht : t ∈ Set.Icc (1 / 2 : ℝ) 1) :
    TmSide ρ l₁ K (lowModSymbF ρ C₀ a l₁ l₂ k₁ k₂ j₁ t) := by
  have hns : k₁ ≠ 0 ∨ 0 ≤ j₁ := modBump_nonsingular k₁ j₁ hj₁ hk₁
  have hside0 := tmSide_of_bump ρ l₁ (fun _ : ℝ => (0 : ℂ)) 0 0 le_rfl measurable_const
    (fun x _ => rfl) (fun x => by simp) contDiff_const HasCompactSupport.zero
  refine ⟨?_, ?_, ?_⟩
  · intro k _ x
    by_cases hk0 : k = 0
    · have hs : lowModSymbF ρ C₀ a l₁ l₂ k₁ k₂ j₁ t k = 0 := by
        funext ξ; simp [lowModSymbF, hk0]
      rw [hs]
      simpa using hside0.1 x
    · by_cases hls : lowSmallSet ρ C₀ a l₁ l₂ k₁ k₂ k
      · have hs : lowModSymbF ρ C₀ a l₁ l₂ k₁ k₂ j₁ t k
            = varphiNtj (Nat.floor (a k)) k₁ j₁ t := by
          funext ξ; simp [lowModSymbF, hk0, hls]
        rw [hs]
        exact (tmSideBumpNtj ρ l₁ (Nat.floor (a k)) k₁ j₁ t hns ht).1 x
      · have hs : lowModSymbF ρ C₀ a l₁ l₂ k₁ k₂ j₁ t k = 0 := by
          funext ξ; simp [lowModSymbF, hk0, hls]
        rw [hs]
        simpa using hside0.1 x
  · intro k _
    by_cases hk0 : k = 0
    · have hs : lowModSymbF ρ C₀ a l₁ l₂ k₁ k₂ j₁ t k = 0 := by
        funext ξ; simp [lowModSymbF, hk0]
      rw [hs]
      exact hside0.2.1
    · by_cases hls : lowSmallSet ρ C₀ a l₁ l₂ k₁ k₂ k
      · have hs : lowModSymbF ρ C₀ a l₁ l₂ k₁ k₂ j₁ t k
            = varphiNtj (Nat.floor (a k)) k₁ j₁ t := by
          funext ξ; simp [lowModSymbF, hk0, hls]
        rw [hs]
        exact (tmSideBumpNtj ρ l₁ (Nat.floor (a k)) k₁ j₁ t hns ht).2.1
      · have hs : lowModSymbF ρ C₀ a l₁ l₂ k₁ k₂ j₁ t k = 0 := by
          funext ξ; simp [lowModSymbF, hk0, hls]
        rw [hs]
        exact hside0.2.1
  · intro k _
    by_cases hk0 : k = 0
    · have hs : lowModSymbF ρ C₀ a l₁ l₂ k₁ k₂ j₁ t k = 0 := by
        funext ξ; simp [lowModSymbF, hk0]
      rw [hs]
      exact hside0.2.2
    · by_cases hls : lowSmallSet ρ C₀ a l₁ l₂ k₁ k₂ k
      · have hs : lowModSymbF ρ C₀ a l₁ l₂ k₁ k₂ j₁ t k
            = varphiNtj (Nat.floor (a k)) k₁ j₁ t := by
          funext ξ; simp [lowModSymbF, hk0, hls]
        rw [hs]
        exact (tmSideBumpNtj ρ l₁ (Nat.floor (a k)) k₁ j₁ t hns ht).2.2
      · have hs : lowModSymbF ρ C₀ a l₁ l₂ k₁ k₂ j₁ t k = 0 := by
          funext ξ; simp [lowModSymbF, hk0, hls]
        rw [hs]
        exact hside0.2.2

/-- **`TmSide` for the anchored, clamped `g`-side family** (the analogue of
`TmSide_lowModSymbF`). -/
theorem TmSide_lowModSymbG (ρ : ℝ) (P : Polynomial ℤ) (C₀ : ℕ) (a : ℕ → NNReal)
    (l₁ l₂ k₁ k₂ K : ℕ) (j₂ : ℤ)
    (t : ℝ) (hj₂ : j₂ ∈ ({-1, 0, 1} : Finset ℤ)) (hk₂ : ¬ (k₂ = 0 ∧ j₂ = -1))
    (ht : t ∈ Set.Icc (1 / 2 : ℝ) 1) :
    TmSide ρ l₂ K (lowModSymbG ρ P C₀ a l₁ l₂ k₁ k₂ j₂ t) := by
  have hns : k₂ ≠ 0 ∨ 0 ≤ j₂ := modBump_nonsingular k₂ j₂ hj₂ hk₂
  have hside0 := tmSide_of_bump ρ l₂ (fun _ : ℝ => (0 : ℂ)) 0 0 le_rfl measurable_const
    (fun x _ => rfl) (fun x => by simp) contDiff_const HasCompactSupport.zero
  refine ⟨?_, ?_, ?_⟩
  · intro k _ x
    by_cases hk0 : k = 0
    · have hs : lowModSymbG ρ P C₀ a l₁ l₂ k₁ k₂ j₂ t k = 0 := by
        funext ξ; simp [lowModSymbG, hk0]
      rw [hs]
      simpa using hside0.1 x
    · by_cases hls : lowSmallSet ρ C₀ a l₁ l₂ k₁ k₂ k
      · have hs : lowModSymbG ρ P C₀ a l₁ l₂ k₁ k₂ j₂ t k
            = varphitildeNtj P (Nat.floor (a k)) k₂ j₂ t := by
          funext ξ; simp [lowModSymbG, hk0, hls]
        rw [hs]
        exact (tmSideBumpNtjG ρ l₂ P (Nat.floor (a k)) k₂ j₂ t hns ht).1 x
      · have hs : lowModSymbG ρ P C₀ a l₁ l₂ k₁ k₂ j₂ t k = 0 := by
          funext ξ; simp [lowModSymbG, hk0, hls]
        rw [hs]
        simpa using hside0.1 x
  · intro k _
    by_cases hk0 : k = 0
    · have hs : lowModSymbG ρ P C₀ a l₁ l₂ k₁ k₂ j₂ t k = 0 := by
        funext ξ; simp [lowModSymbG, hk0]
      rw [hs]
      exact hside0.2.1
    · by_cases hls : lowSmallSet ρ C₀ a l₁ l₂ k₁ k₂ k
      · have hs : lowModSymbG ρ P C₀ a l₁ l₂ k₁ k₂ j₂ t k
            = varphitildeNtj P (Nat.floor (a k)) k₂ j₂ t := by
          funext ξ; simp [lowModSymbG, hk0, hls]
        rw [hs]
        exact (tmSideBumpNtjG ρ l₂ P (Nat.floor (a k)) k₂ j₂ t hns ht).2.1
      · have hs : lowModSymbG ρ P C₀ a l₁ l₂ k₁ k₂ j₂ t k = 0 := by
          funext ξ; simp [lowModSymbG, hk0, hls]
        rw [hs]
        exact hside0.2.1
  · intro k _
    by_cases hk0 : k = 0
    · have hs : lowModSymbG ρ P C₀ a l₁ l₂ k₁ k₂ j₂ t k = 0 := by
        funext ξ; simp [lowModSymbG, hk0]
      rw [hs]
      exact hside0.2.2
    · by_cases hls : lowSmallSet ρ C₀ a l₁ l₂ k₁ k₂ k
      · have hs : lowModSymbG ρ P C₀ a l₁ l₂ k₁ k₂ j₂ t k
            = varphitildeNtj P (Nat.floor (a k)) k₂ j₂ t := by
          funext ξ; simp [lowModSymbG, hk0, hls]
        rw [hs]
        exact (tmSideBumpNtjG ρ l₂ P (Nat.floor (a k)) k₂ j₂ t hns ht).2.2
      · have hs : lowModSymbG ρ P C₀ a l₁ l₂ k₁ k₂ j₂ t k = 0 := by
          funext ξ; simp [lowModSymbG, hk0, hls]
        rw [hs]
        exact hside0.2.2

/-! ## The Rademacher--Menshov reduction with a constant independent of `ρ` and of the twist -/

/-- **The two-dimensional Rademacher--Menshov reduction with an absolute constant.**  This is
`Work.KMTPlan.A6.VrFull_TmBtwist_le_rand_abs` with the constant `C_RM` moved outside the
quantifiers over `ρ` and `P`: the underlying engine `rmVarBound_uniform` produces a constant that
depends only on the ambient `ℓ¹`(ℤ) space and the bilinear-form geometry, not on the particular
twist, the heights or the window. -/
theorem VrFull_TmBtwist_le_rand_uniform :
    ∃ C_RM : ℝ, 0 < C_RM ∧
      ∀ (ρ : ℝ) (P : Polynomial ℤ) (l₁ l₂ : ℕ) (m₁ m₂ : ℝ → ℂ)
        (hm₁ : Summable fun j : ℤ => ‖cw m₁ j‖)
        (hm₂ : Summable fun j : ℤ => ‖cw m₂ j‖)
        (K : ℕ) (Φ Ψ : ℕ → ℝ → ℂ) (f g : ℤ → ℂ) (C : ENNReal),
        Φ 0 = 0 → Ψ 0 = 0 →
        MeasureTheory.MemLp f 2 MeasureTheory.Measure.count →
        MeasureTheory.MemLp g 2 MeasureTheory.Measure.count →
        TmSide ρ l₁ K Φ → TmSide ρ l₂ K Ψ →
        (∀ k : ℕ, ∃ D : ℝ, ∀ y : ℤ, ‖Tm ρ l₁ (Φ k) f y‖ ≤ D) →
        (∀ k : ℕ, ∃ D : ℝ, ∀ y : ℤ, ‖Tm ρ l₂ (Ψ k) g y‖ ≤ D) →
        (∀ (ε ε' : ℕ → ℂ), (∀ k, ‖ε k‖ ≤ 1) → (∀ k, ‖ε' k‖ ≤ 1) →
          MeasureTheory.eLpNorm (fun x : ℤ => BtwistEx ρ P l₁ l₂ m₁ m₂
            (Tm ρ l₁ (randSymb Φ ε K) f) (Tm ρ l₂ (randSymb Ψ ε' K) g) x)
            1 MeasureTheory.Measure.count ≤ C) →
        MeasureTheory.eLpNorm (fun x : ℤ => Work.Analysis.Variation.VrFull 2 K (fun k : ℕ =>
            BtwistEx ρ P l₁ l₂ m₁ m₂ (Tm ρ l₁ (Φ k) f) (Tm ρ l₂ (Ψ k) g) x))
          1 MeasureTheory.Measure.count
          ≤ ENNReal.ofReal (C_RM * ((Nat.log2 K : ℝ) + 2) ^ (2 : ℝ)) * C := by
  obtain ⟨C_RM, hC_RM, hgen⟩ :=
    Work.Analysis.Variation.rmVarBound_uniform 1 (by norm_num) (by norm_num)
      (V := bddSub) (W := bddSub) (X := ℤ) (μ := MeasureTheory.Measure.count)
  refine ⟨C_RM, hC_RM, ?_⟩
  intro ρ P l₁ l₂ m₁ m₂ hm₁ hm₂ K Φ Ψ f g C hΦ0 hΨ0 hf hg hside₁ hside₂ hbd₁ hbd₂ hSS
  obtain ⟨hper₁, hI₁, hκ₁⟩ := hside₁
  obtain ⟨hper₂, hI₂, hκ₂⟩ := hside₂
  let Useq : ℕ → bddSub := fun k => ⟨Tm ρ l₁ (Φ k) f, hbd₁ k⟩
  let Wseq : ℕ → bddSub := fun k => ⟨Tm ρ l₂ (Ψ k) g, hbd₂ k⟩
  have hU0 : Useq 0 = 0 := by
    apply Subtype.ext
    show Tm ρ l₁ (Φ 0) f = (0 : ℤ → ℂ)
    rw [hΦ0]
    exact Tm_zero ρ l₁ f hf
  have hW0 : Wseq 0 = 0 := by
    apply Subtype.ext
    show Tm ρ l₂ (Ψ 0) g = (0 : ℤ → ℂ)
    rw [hΨ0]
    exact Tm_zero ρ l₂ g hg
  have hmain : MeasureTheory.eLpNorm (fun x : ℤ => Work.Analysis.Variation.VrFull 2 K
        (fun k : ℕ => BtwistEx ρ P l₁ l₂ m₁ m₂ (Useq k).1 (Wseq k).1 x))
        (ENNReal.ofReal 1) MeasureTheory.Measure.count
      ≤ ENNReal.ofReal (C_RM * ((Nat.log2 K : ℝ) + 2) ^ (2 : ℕ)) * C := by
    refine hgen (fun u v x => BtwistEx ρ P l₁ l₂ m₁ m₂ u.1 v.1 x)
      (BtwistEx_bdd_add₁ ρ P l₁ l₂ m₁ m₂ hm₁ hm₂)
      (BtwistEx_bdd_smul₁ ρ P l₁ l₂ m₁ m₂ hm₁ hm₂)
      (BtwistEx_bdd_add₂ ρ P l₁ l₂ m₁ m₂ hm₁ hm₂)
      (BtwistEx_bdd_smul₂ ρ P l₁ l₂ m₁ m₂ hm₁ hm₂)
      K Useq Wseq C hU0 hW0
      (fun k k' => (measurable_of_countable (fun x : ℤ =>
        BtwistEx ρ P l₁ l₂ m₁ m₂ (Useq k).1 (Wseq k').1 x)).aemeasurable) ?_
    intro ε ε' hε hε'
    have h1 : (∑ k ∈ Finset.range K, ε k • (Useq (k + 1) - Useq k)).1
        = Tm ρ l₁ (randSymb Φ ε K) f := by
      have hstep : (∑ k ∈ Finset.range K, ε k • (Useq (k + 1) - Useq k)).1
          = ∑ k ∈ Finset.range K, ε k • (Tm ρ l₁ (Φ (k + 1)) f
              - Tm ρ l₁ (Φ k) f) := by
        rw [Submodule.coe_sum]
        refine Finset.sum_congr rfl fun k _ => ?_
        funext y
        simp only [Submodule.coe_smul, Submodule.coe_sub, Pi.smul_apply, Pi.sub_apply,
          smul_eq_mul, Useq]
      rw [hstep]
      exact (Tm_randSymb_eq ρ l₁ K Φ ε f hf hper₁ hI₁ hκ₁).symm
    have h2 : (∑ k ∈ Finset.range K, ε' k • (Wseq (k + 1) - Wseq k)).1
        = Tm ρ l₂ (randSymb Ψ ε' K) g := by
      have hstep : (∑ k ∈ Finset.range K, ε' k • (Wseq (k + 1) - Wseq k)).1
          = ∑ k ∈ Finset.range K, ε' k • (Tm ρ l₂ (Ψ (k + 1)) g
              - Tm ρ l₂ (Ψ k) g) := by
        rw [Submodule.coe_sum]
        refine Finset.sum_congr rfl fun k _ => ?_
        funext y
        simp only [Submodule.coe_smul, Submodule.coe_sub, Pi.smul_apply, Pi.sub_apply,
          smul_eq_mul, Wseq]
      rw [hstep]
      exact (Tm_randSymb_eq ρ l₂ K Ψ ε' g hg hper₂ hI₂ hκ₂).symm
    rw [h1, h2, ENNReal.ofReal_one]
    exact hSS ε ε' hε hε'
  have hexp : ((Nat.log2 K : ℝ) + 2) ^ (2 : ℕ) = ((Nat.log2 K : ℝ) + 2) ^ (2 : ℝ) :=
    (Real.rpow_natCast ((Nat.log2 K : ℝ) + 2) 2).symm
  rw [hexp] at hmain
  rw [ENNReal.ofReal_one] at hmain
  exact hmain

/-! ## The frozen-`t` single-scale bound of Case B -/

/-- **The frozen-`t` single-scale bound of Case B**: the two-dimensional Rademacher--Menshov
reduction of the *anchored, clamped* bilinear family
`n ↦ BtwistEx_{m_*}(Tm ρ l₁ (φ_{N,k₁,j₁}(t)) f, Tm ρ l₂ (φ̃_{N,k₂,j₂}(t)) g)`, `N = ⌊a n⌋`,
followed by the single-scale estimate `hSS` applied to the randomised cut-offs and the two
`ℓ²`-interfaces `LowModRandL2FBody`/`LowModRandL2GBody` for those cut-offs.

The two families are `lowModSymbF ρ C₀ a l₁ l₂ k₁ k₂ j₁ t` and `lowModSymbG ρ P C₀ a l₁ l₂ k₁ k₂ j₂ t`
of `LowModelVarCaseBAux`; they vanish at `n = 0` and off `lowSmallSet`, and their members are the
modified bumps `φ_{N,k₁,j₁}(t)`, `φ̃_{N,k₂,j₂}(t)`.  `hsupF`/`hsupG` supply the narrow support of
the members (needed by `hSS`), `hRanF`/`hRanG` bound the randomised packets, `hB` lets those
interfaces be used at `lcL l₁ l₂ k₁ k₂`, and `huL`/`hu2` place the scale `u` above `max l₁ l₂` as
`hSS` requires.

Route: apply `Work.KMTPlan.A6.VrFull_TmBtwist_le_rand_abs ρ P` (whose constant `C_RM` is
independent of `ρ` and of the parameters, being built from `rmVarBound_uniform` at `bddSub`), with
`Φ := lowModSymbF …`, `Ψ := lowModSymbG …`, `K := K`, `m₁ := mStarF u`, `m₂ := mStargF P.natDegree u`;
the `hSS`-hypothesis of that result is discharged by `hSS` together with `hRanF`/`hRanG`; the
support of the randomised sums is obtained from `hsupF`/`hsupG` via
`Work.KMTPlan.A6.exists_ne_zero_of_randSymb_ne_zero`; `TmSide` from
`Work.KMTPlan.A6.tmSide_of_bump` (each member of the family is either `0` or one of the modified
bumps, which is measurable, vanishes outside the narrow arc, is bounded, `C²` and compactly
supported by `Work.KMTPlan.A6.varphiNtj_bounds`/`varphitildeNtj_bounds`); and the `ℓ^∞`-boundedness
of the `Tm`-images from the kernel packages
`Work.KMTPlan.A6.tmKerPackage_varphiNtj`/`tmKerPackage_varphitildeNtj` together with
`Work.A7.ModelApproxCore_aux.norm_convOp_le` and `Work.KMTAreas.A5.boundedZ_of_memLp`. -/
theorem lowFrozenBilinBound (P : Polynomial ℤ) (hd : 2 ≤ P.natDegree)
    (hA1 : Work.KMTContract.AreaA1) :
    ∃ C_RM : ℝ, 0 < C_RM ∧
      ∀ (C₀ : ℕ) (hC₀ : 1 ≤ C₀) (ρ : ℝ) (hρ : 0 < ρ) (B : ℕ)
        (C : NNReal → NNReal)
        (hRanF : Work.KMTPlan.A6.LowModRandL2FBody P C₀ ρ B C)
        (hRanG : Work.KMTPlan.A6.LowModRandL2GBody P C₀ ρ B C)
        (cS : ℝ) (hcS : 0 < cS) (Cssu : NNReal)
        (hSS : ∀ (m₁ m₂ u : ℕ) (φ ψ : ℝ → ℂ) (f' g' : ℤ → ℂ),
          (max m₁ m₂ : ℝ) ≤ (u : ℝ) →
          (2 : ℝ) ^ (ρ * (max m₁ m₂ : ℝ)) ≤ (u : ℝ) →
          MeasureTheory.MemLp f' 2 MeasureTheory.Measure.count →
          MeasureTheory.MemLp g' 2 MeasureTheory.Measure.count →
          (∀ ξ : ℝ, φ ξ ≠ 0 → |ξ| ≤ (2 : ℝ) ^ (-(3 * (u : ℤ)))) →
          (∀ ξ : ℝ, ψ ξ ≠ 0 → |ξ| ≤ (2 : ℝ) ^ (-(3 * (P.natDegree : ℤ) * (u : ℤ)))) →
          MeasureTheory.eLpNorm (fun x : ℤ => Work.KMTPlan.A6.BtwistEx ρ P m₁ m₂
              (Work.KMTAreas.A7.mStarF u)
              (Work.KMTAreas.A7.mStargF P.natDegree u)
              (Work.KMTAreas.A7.Tm ρ m₁ φ f') (Work.KMTAreas.A7.Tm ρ m₂ ψ g') x)
            1 MeasureTheory.Measure.count
            ≤ (Cssu : ENNReal) * ENNReal.ofReal ((2 : ℝ) ^ (-(cS * (max (m₁ : ℝ) (m₂ : ℝ)))))
                * MeasureTheory.eLpNorm (Work.KMTAreas.A7.Tm ρ m₁ φ f') 2 MeasureTheory.Measure.count
                * MeasureTheory.eLpNorm (Work.KMTAreas.A7.Tm ρ m₂ ψ g') 2 MeasureTheory.Measure.count)
        (u : ℕ) (Λ : NNReal) (hΛ : 1 < Λ) (a : ℕ → NNReal)
        (ha : PointwiseErgodicTheorems.Lacunary Λ a) (ha1 : ∀ n, 1 ≤ a n)
        (l₁ l₂ k₁ k₂ K : ℕ) (hB : B ≤ Work.KMTPlan.A6.lcL l₁ l₂ k₁ k₂)
        (huL : (max l₁ l₂ : ℝ) ≤ (u : ℝ))
        (hu2 : (2 : ℝ) ^ (ρ * (max l₁ l₂ : ℝ)) ≤ (u : ℝ))
        (j₁ j₂ : ℤ) (hj₁ : j₁ ∈ ({-1, 0, 1} : Finset ℤ)) (hj₂ : j₂ ∈ ({-1, 0, 1} : Finset ℤ))
        (hk₁ : ¬ (k₁ = 0 ∧ j₁ = -1)) (hk₂ : ¬ (k₂ = 0 ∧ j₂ = -1))
        (t : ℝ) (ht : t ∈ Set.Icc (1 / 2 : ℝ) 1) (f g : ℤ → ℂ)
        (hf : MeasureTheory.MemLp f 2 MeasureTheory.Measure.count)
        (hg : MeasureTheory.MemLp g 2 MeasureTheory.Measure.count)
        (hsupF : ∀ n : ℕ, ∀ ξ : ℝ,
          Work.KMTPlan.A6.lowModSymbF ρ C₀ a l₁ l₂ k₁ k₂ j₁ t n ξ ≠ 0 →
            |ξ| ≤ (2 : ℝ) ^ (-(3 * (u : ℤ))))
        (hsupG : ∀ n : ℕ, ∀ ξ : ℝ,
          Work.KMTPlan.A6.lowModSymbG ρ P C₀ a l₁ l₂ k₁ k₂ j₂ t n ξ ≠ 0 →
            |ξ| ≤ (2 : ℝ) ^ (-(3 * (P.natDegree : ℤ) * (u : ℤ)))),
        MeasureTheory.eLpNorm (fun x : ℤ => Work.Analysis.Variation.VrFull 2 K
            (fun n : ℕ => Work.KMTPlan.A6.BtwistEx ρ P l₁ l₂
              (Work.KMTAreas.A7.mStarF u) (Work.KMTAreas.A7.mStargF P.natDegree u)
              (Work.KMTAreas.A7.Tm ρ l₁ (Work.KMTPlan.A6.lowModSymbF ρ C₀ a l₁ l₂ k₁ k₂ j₁ t n) f)
              (Work.KMTAreas.A7.Tm ρ l₂ (Work.KMTPlan.A6.lowModSymbG ρ P C₀ a l₁ l₂ k₁ k₂ j₂ t n) g) x))
          1 MeasureTheory.Measure.count
          ≤ ENNReal.ofReal (C_RM * ((Nat.log2 K : ℝ) + 2) ^ (2 : ℝ)) *
              ((Cssu : ENNReal) * ENNReal.ofReal ((2 : ℝ) ^ (-(cS * (max (l₁ : ℝ) (l₂ : ℝ)))))
                * ((C Λ : ENNReal) * (C Λ : ENNReal))) *
              MeasureTheory.eLpNorm f 2 MeasureTheory.Measure.count *
              MeasureTheory.eLpNorm g 2 MeasureTheory.Measure.count := by
  obtain ⟨C_RM, hC_RM, hgen⟩ := VrFull_TmBtwist_le_rand_uniform
  refine ⟨C_RM, hC_RM, ?_⟩
  intro C₀ hC₀ ρ hρ B C hRanF hRanG cS hcS Cssu hSS u Λ hΛ a ha ha1
    l₁ l₂ k₁ k₂ K hB huL hu2 j₁ j₂ hj₁ hj₂ hk₁ hk₂ t ht f g hf hg hsupF hsupG
  set Φ : ℕ → ℝ → ℂ := lowModSymbF ρ C₀ a l₁ l₂ k₁ k₂ j₁ t with hΦdef
  set Ψ : ℕ → ℝ → ℂ := lowModSymbG ρ P C₀ a l₁ l₂ k₁ k₂ j₂ t with hΨdef
  set Xa : ENNReal :=
    (Cssu : ENNReal) * ENNReal.ofReal ((2 : ℝ) ^ (-(cS * (max (l₁ : ℝ) (l₂ : ℝ))))) with hXadef
  set Yb : ENNReal := (C Λ : ENNReal) * (C Λ) with hYbdef
  set F2 : ENNReal := MeasureTheory.eLpNorm f 2 MeasureTheory.Measure.count with hF2def
  set G2 : ENNReal := MeasureTheory.eLpNorm g 2 MeasureTheory.Measure.count with hG2def
  have hSSinst : ∀ (ε ε' : ℕ → ℂ), (∀ k, ‖ε k‖ ≤ 1) → (∀ k, ‖ε' k‖ ≤ 1) →
      MeasureTheory.eLpNorm (fun x : ℤ => Work.KMTPlan.A6.BtwistEx ρ P l₁ l₂
        (Work.KMTAreas.A7.mStarF u) (Work.KMTAreas.A7.mStargF P.natDegree u)
        (Work.KMTAreas.A7.Tm ρ l₁ (Work.KMTAreas.A7.randSymb Φ ε K) f)
        (Work.KMTAreas.A7.Tm ρ l₂ (Work.KMTAreas.A7.randSymb Ψ ε' K) g) x)
        1 MeasureTheory.Measure.count ≤ Xa * Yb * F2 * G2 := by
    intro ε ε' hε hε'
    have hsF : ∀ ξ : ℝ, randSymb Φ ε K ξ ≠ 0 → |ξ| ≤ (2 : ℝ) ^ (-(3 * (u : ℤ))) := by
      intro ξ hξ
      obtain ⟨n, _hnK, hn⟩ := exists_ne_zero_of_randSymb_ne_zero hξ
      exact hsupF n ξ hn
    have hsG : ∀ ξ : ℝ, randSymb Ψ ε' K ξ ≠ 0 →
        |ξ| ≤ (2 : ℝ) ^ (-(3 * (P.natDegree : ℤ) * (u : ℤ))) := by
      intro ξ hξ
      obtain ⟨n, _hnK, hn⟩ := exists_ne_zero_of_randSymb_ne_zero hξ
      exact hsupG n ξ hn
    have h1 := hSS l₁ l₂ u (randSymb Φ ε K) (randSymb Ψ ε' K) f g huL hu2 hf hg hsF hsG
    have h2 : MeasureTheory.eLpNorm (Tm ρ l₁ (randSymb Φ ε K) f) 2 MeasureTheory.Measure.count
        ≤ (C Λ : ENNReal) * F2 := by
      rw [hF2def]
      exact hRanF a Λ l₁ l₂ k₁ k₂ K t j₁ ε f hΛ ha ha1 hε ht hj₁ hk₁ hB hf
    have h3 : MeasureTheory.eLpNorm (Tm ρ l₂ (randSymb Ψ ε' K) g) 2 MeasureTheory.Measure.count
        ≤ (C Λ : ENNReal) * G2 := by
      rw [hG2def]
      exact hRanG a Λ l₁ l₂ k₁ k₂ K t j₂ ε' g hΛ ha ha1 hε' ht hj₂ hk₂ hB hg
    calc MeasureTheory.eLpNorm (fun x : ℤ => Work.KMTPlan.A6.BtwistEx ρ P l₁ l₂
          (Work.KMTAreas.A7.mStarF u) (Work.KMTAreas.A7.mStargF P.natDegree u)
          (Work.KMTAreas.A7.Tm ρ l₁ (Work.KMTAreas.A7.randSymb Φ ε K) f)
          (Work.KMTAreas.A7.Tm ρ l₂ (Work.KMTAreas.A7.randSymb Ψ ε' K) g) x)
          1 MeasureTheory.Measure.count
        ≤ (Cssu : ENNReal) * ENNReal.ofReal ((2 : ℝ) ^ (-(cS * (max (l₁ : ℝ) (l₂ : ℝ)))))
            * MeasureTheory.eLpNorm (Tm ρ l₁ (randSymb Φ ε K) f)
                2 MeasureTheory.Measure.count
            * MeasureTheory.eLpNorm (Tm ρ l₂ (randSymb Ψ ε' K) g)
                2 MeasureTheory.Measure.count := h1
      _ ≤ (Cssu : ENNReal) * ENNReal.ofReal ((2 : ℝ) ^ (-(cS * (max (l₁ : ℝ) (l₂ : ℝ)))))
            * ((C Λ : ENNReal) * F2)
            * MeasureTheory.eLpNorm (Tm ρ l₂ (randSymb Ψ ε' K) g)
                2 MeasureTheory.Measure.count :=
          mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_left h2 zero_le) zero_le
      _ ≤ (Cssu : ENNReal) * ENNReal.ofReal ((2 : ℝ) ^ (-(cS * (max (l₁ : ℝ) (l₂ : ℝ)))))
            * ((C Λ : ENNReal) * F2) * ((C Λ : ENNReal) * G2) :=
          mul_le_mul_of_nonneg_left h3 zero_le
      _ = Xa * Yb * F2 * G2 := by rw [hXadef, hYbdef]; ac_rfl
  have hmain := hgen ρ P l₁ l₂ (mStarF u) (mStargF P.natDegree u) (cw_mStarF_summable u)
    (cw_mStargF_summable P.natDegree u) K Φ Ψ f g (Xa * Yb * F2 * G2)
    (by rw [hΦdef]; exact lowModSymbF_zero ρ C₀ a l₁ l₂ k₁ k₂ j₁ t)
    (by rw [hΨdef]; exact lowModSymbG_zero ρ P C₀ a l₁ l₂ k₁ k₂ j₂ t)
    hf hg
    (by rw [hΦdef]; exact TmSide_lowModSymbF ρ C₀ a l₁ l₂ k₁ k₂ K j₁ t hj₁ hk₁ ht)
    (by rw [hΨdef]; exact TmSide_lowModSymbG ρ P C₀ a l₁ l₂ k₁ k₂ K j₂ t hj₂ hk₂ ht)
    (by rw [hΦdef]; exact tmBddLowModSymbF ρ C₀ a l₁ l₂ k₁ k₂ j₁ t hj₁ hk₁ ht f hf)
    (by rw [hΨdef]; exact tmBddLowModSymbG P ρ C₀ a l₁ l₂ k₁ k₂ j₂ t hj₂ hk₂ ht g hg)
    hSSinst
  refine le_trans hmain ?_
  simp only [hXadef, hYbdef, hF2def, hG2def, mul_assoc, le_refl]

end

end Work.KMTPlan.A6
