/-
# The height-`0` window-piece lift of the model `g`-side family

`mdlLiftGZero` is the `l₂ = 0` member of the family `mdlWindowLiftG`
(`MdlWindowLiftF.lean`): for the `g`-side packet family `mdlSliceG ρ P C₀ a l₁ 0 k₁ k₂ j₂ t g n`
of the frozen-`t` slice at *arithmetic height* `0`, there is a family `W : Circle → ℝ → ℂ` with the
properties the §8 adelic form needs:

* each `W α` is the inverse Fourier transform of an integrable function supported in the real arc
  `[-γ, γ]`, `γ = 2^{d(k₂ - Log ⌊a n⌋)}`, `d = P.natDegree`;
* `W α` vanishes off the arithmetic frequency set `(ℚ/ℤ)_{≤0} = {0}`, and on `(ℚ/ℤ)_{≤0}` its
  integer samples are the window pieces `winConvR (mStargF d U) (winModR (-α) s)` of the slice `s`.

## Why height `0` is a separate statement

This is the `g`-side twin of the proved `Work.KMTPlan.A6Clean.mdlLiftFZero`, and the reason is the
same as there: at height `0` the arithmetic frequency set collapses to the singleton
`iwArithFreqs ρ 0 = {0}` (`Work.KMTAreas.A7.iwArithFreqs_zero`), so

* the separation condition `S + γ < ‖α - β‖` of the abstract lift `windowPieceLift_abs` is vacuous
  (there are no two distinct elements);
* the vanishing of the window pieces off the exact height (`winConvR_eq_zero_of_not_exact`, which
  `mdlWindowLiftG` needs at `l₂ ≠ 0` for every `α ∈ (ℚ/ℤ)_{≤l₂}` of non-exact height) is exactly the
  vanishing *off* the whole height-`0` set, which is a conjunct of the statement.

So the only band statement needed is that the slice is band limited to
`⋃_{α ∈ (ℚ/ℤ)_{≤0}} arcSet α γ`, which is the general
`Work.KMTPlan.A6.Tle_hasFreqSupport_of_memℓp` applied to the modified `g`-side bump at `l = 0`
(proved below as `mdlSliceG_zero_band`, in the *exact* radius form appearing in `mdlLiftGZero`).

The final `Summable` conjunct is the proved
`Work.KMTAreas.A7.summable_cw_mul_of_memℓp`, applied to the `ℓ²`-membership of the slice.
-/
import Mathlib
import Submission.Work.KMTPlan.A6Clean.MdlWindowLiftF

set_option autoImplicit false
set_option maxHeartbeats 1600000

namespace Work.KMTPlan.A6Clean

open MeasureTheory
open scoped BigOperators ENNReal NNReal

local notation "Circ" => Work.Analysis.IonescuWainger.Circle

/-- **The band of the `g`-side packet family at arithmetic height `0`.**  On the core condition
the family `mdlSliceG ρ P C₀ a l₁ 0 k₁ k₂ j₂ t g n` is the Ionescu–Wainger projection
`Tle ρ 0 (varphitildeNtj P ⌊a n⌋ k₂ j₂ t) (mdlG ρ P U 0 g)` of the modified `g`-side bump against
the exact-height shell `mdlG`; by `Work.KMTPlan.A6.Tle_hasFreqSupport_of_memℓp` it is square
summable and band limited to the `2^{d(k₂ - Log ⌊a n⌋)}`-arc around `0` — the only element of
`(ℚ/ℤ)_{≤0} = {0}`. -/
theorem mdlSliceG_zero_band (ρ : ℝ) (hρ : 0 < ρ) (hρ1 : ρ ≤ 1) (P : Polynomial ℤ)
    (C₀ : ℕ) (a : ℕ → NNReal) (g : ℤ → ℂ) (l₁ k₁ k₂ : ℕ) (j₂ : ℤ) (t : ℝ) (n : ℕ)
    (hj₂ : j₂ ∈ ({-1, 0, 1} : Finset ℤ)) (hk₂ : k₂ = 0 → j₂ ≠ -1)
    (hN : 1 ≤ Nat.floor (a n)) (hg : Memℓp g 2)
    (hmc : Work.KMTPlan.A6.mdlCore ρ C₀ a l₁ 0 k₁ k₂ n) :
    ∃ h : Memℓp (Work.KMTPlan.A6.mdlSliceG ρ P C₀ a l₁ 0 k₁ k₂ j₂ t g n) 2,
      Work.BourgainPlan.IonescuWainger.HasFreqSupport
        (Work.KMTPlan.A6.mdlSliceG ρ P C₀ a l₁ 0 k₁ k₂ j₂ t g n) h
        (⋃ α ∈ Work.Analysis.IonescuWainger.iwArithFreqs ρ 0,
          Work.BourgainPlan.IonescuWainger.arcSet α
            ((2 : ℝ) ^ ((P.natDegree : ℝ) *
              ((k₂ : ℝ) - ((Work.Analysis.EndVar.logN (Nat.floor (a n)) : ℤ) : ℝ))))) := by
  classical
  -- the excluded case `(k₂, j₂) = (0, -1)`: the weight `(N^dξ)^{-1}` is singular at the origin
  have hmod : k₂ ≠ 0 ∨ 0 ≤ j₂ := by
    have hj : j₂ = -1 ∨ j₂ = 0 ∨ j₂ = 1 := by simpa using hj₂
    rcases hj with h | h | h
    · by_cases hk : k₂ = 0
      · exact absurd h (hk₂ hk)
      · exact Or.inl hk
    · exact Or.inr (by omega)
    · exact Or.inr (by omega)
  -- on the core condition the family is a single `Tle` of the modified bump
  have hslice : Work.KMTPlan.A6.mdlSliceG ρ P C₀ a l₁ 0 k₁ k₂ j₂ t g n
      = Work.KMTAreas.A7.Tle ρ 0 (Work.KMTPlan.A6.varphitildeNtj P (Nat.floor (a n)) k₂ j₂ t)
          (Work.KMTPlan.A6.mdlG ρ P
            (Work.KMTAreas.A7.uScale ρ (max (max l₁ 0) (max k₁ k₂))) 0 g) := by
    simp only [Work.KMTPlan.A6.mdlSliceG, hmc, if_true]
  rw [hslice]
  exact Work.KMTPlan.A6.Tle_hasFreqSupport_of_memℓp ρ 0
    (Work.KMTPlan.A6.varphitildeNtj P (Nat.floor (a n)) k₂ j₂ t)
    ((2 : ℝ) ^ ((P.natDegree : ℝ) *
      ((k₂ : ℝ) - ((Work.Analysis.EndVar.logN (Nat.floor (a n)) : ℤ) : ℝ))))
    (Work.KMTPlan.A6.integrable_varphitildeNtj P (Nat.floor (a n)) k₂ j₂ t hmod)
    (Work.KMTPlan.A6.summable_cw_varphitildeNtj P (Nat.floor (a n)) k₂ j₂ t hmod)
    (fun θ hθ => Work.KMTAreas.A7.fiberOpTex_periodize_ne_zero_mem_arcSet
      (Work.KMTPlan.A6.varphitildeNtj_abs_le P (Nat.floor (a n)) k₂ j₂ t) hθ)
    (Work.KMTPlan.A6.mdlG ρ P
      (Work.KMTAreas.A7.uScale ρ (max (max l₁ 0) (max k₁ k₂))) 0 g)
    (Work.KMTPlan.A6.memℓp_mdlG ρ P _ 0 hg)

theorem mdlLiftGZero (ρ : ℝ) (hρ : 0 < ρ) (hρ1 : ρ ≤ 1) (P : Polynomial ℤ) (hd : 2 ≤ P.natDegree) (C₀ : ℕ) (a : ℕ → NNReal) (g : ℤ → ℂ) (hg : MeasureTheory.MemLp g 2 MeasureTheory.Measure.count) (l₁ k₁ k₂ : ℕ) (j₂ : ℤ) (hj₂ : j₂ ∈ ({-1, 0, 1} : Finset ℤ)) (hk₂ : k₂ = 0 → j₂ ≠ -1) (t : ℝ) (n : ℕ) (hmc : Work.KMTPlan.A6.mdlCore ρ C₀ a l₁ 0 k₁ k₂ n) (hN : 1 ≤ Nat.floor (a n)) (hrad : (2 : ℝ) ^ ((P.natDegree : ℝ) * ((k₂ : ℝ) - ((Work.Analysis.EndVar.logN (Nat.floor (a n)) : ℤ) : ℝ))) ≤ (2 : ℝ) ^ (-((P.natDegree : ℤ) * 2 * (Work.KMTAreas.A7.uScale ρ (Work.KMTPlan.A6.lcL l₁ 0 k₁ k₂) : ℤ)) - 1)) : ∃ W : Work.Analysis.IonescuWainger.Circle → ℝ → ℂ, (∀ α, Measurable (W α)) ∧ (∀ α, Work.KMTAreas.A7Rep.HasRealFreqSupport (W α) (Set.Icc (-((2 : ℝ) ^ ((P.natDegree : ℝ) * ((k₂ : ℝ) - ((Work.Analysis.EndVar.logN (Nat.floor (a n)) : ℤ) : ℝ))))) ((2 : ℝ) ^ ((P.natDegree : ℝ) * ((k₂ : ℝ) - ((Work.Analysis.EndVar.logN (Nat.floor (a n)) : ℤ) : ℝ)))))) ∧ (∀ α, α ∉ Work.Analysis.IonescuWainger.iwArithFreqs ρ 0 → W α = 0) ∧ (∀ α ∈ Work.Analysis.IonescuWainger.iwArithFreqs ρ 0, ∀ x : ℤ, W α (x : ℝ) = Work.KMTAreas.A7.winConvR (Work.KMTAreas.A7.mStargF P.natDegree (Work.KMTAreas.A7.uScale ρ (Work.KMTPlan.A6.lcL l₁ 0 k₁ k₂))) (Work.KMTAreas.A7.winModR (-α) (Work.KMTPlan.A6.mdlSliceG ρ P C₀ a l₁ 0 k₁ k₂ j₂ t g n)) x) ∧ (∀ z : ℤ, Summable (fun j : ℤ => Work.KMTAreas.A7.cw (Work.KMTAreas.A7.mStargF P.natDegree (Work.KMTAreas.A7.uScale ρ (Work.KMTPlan.A6.lcL l₁ 0 k₁ k₂))) j * Work.KMTPlan.A6.mdlSliceG ρ P C₀ a l₁ 0 k₁ k₂ j₂ t g n (z - j))) := by
  classical
  -- the window scale and the band radius
  let U : ℕ := Work.KMTAreas.A7.uScale ρ (Work.KMTPlan.A6.lcL l₁ 0 k₁ k₂)
  let γ : ℝ := (2 : ℝ) ^ ((P.natDegree : ℝ) *
    ((k₂ : ℝ) - ((Work.Analysis.EndVar.logN (Nat.floor (a n)) : ℤ) : ℝ)))
  have hd1 : 1 ≤ P.natDegree := le_trans (by norm_num) hd
  have hU1 : 1 ≤ U := Work.KMTAreas.A7.one_le_uScale ρ hρ.le _
  have h2U : (2 : ℝ) ^ (-((P.natDegree : ℤ) * 2 * (U : ℤ)))
      = 2 * ((2 : ℝ) ^ (-((P.natDegree : ℤ) * 2 * (U : ℤ)) - 1)) := by
    rw [show (-((P.natDegree : ℤ) * 2 * (U : ℤ)) : ℤ)
        = (-((P.natDegree : ℤ) * 2 * (U : ℤ)) - 1) + 1 by ring,
      zpow_add₀ (by norm_num : (2 : ℝ) ≠ 0), zpow_one]
    ring
  have hγpos : 0 < γ := Real.rpow_pos_of_pos (by norm_num : (0 : ℝ) < 2) _
  have hγhalf : γ < 1 / 2 := by
    have hle : γ ≤ (2 : ℝ) ^ (-((P.natDegree : ℤ) * 2 * (U : ℤ)) - 1) := hrad
    have h1 : (2 : ℝ) ^ (-((P.natDegree : ℤ) * 2 * (U : ℤ)) - 1) ≤ (8 : ℝ)⁻¹ := by
      have h2 : (-((P.natDegree : ℤ) * 2 * (U : ℤ)) - 1 : ℤ) ≤ -3 := by
        have hdZ : (1 : ℤ) ≤ (P.natDegree : ℤ) := by exact_mod_cast hd1
        have hUZ : (1 : ℤ) ≤ (U : ℤ) := by exact_mod_cast hU1
        nlinarith
      have h3 := zpow_le_zpow_right₀ (by norm_num : (1 : ℝ) ≤ 2) h2
      have h4 : (2 : ℝ) ^ ((-3 : ℤ)) = (8 : ℝ)⁻¹ := by norm_num
      rw [h4] at h3
      exact h3
    have h12 : (8 : ℝ)⁻¹ < 1 / 2 := by norm_num
    linarith
  -- the window facts
  have hm : Integrable (Work.KMTAreas.A7.mStargF P.natDegree U) :=
    Work.KMTAreas.A7.kmt_integrable_mStargF P.natDegree U
  have hmsum : Summable (fun j : ℤ =>
      ‖Work.KMTAreas.A7.cw (Work.KMTAreas.A7.mStargF P.natDegree U) j‖) :=
    Work.KMTAreas.A7.summable_cw_mStargF P.natDegree U
  have hmsup : ∀ θ : Circ, Work.Analysis.IonescuWainger.periodize
      (Work.KMTAreas.A7.mStargF P.natDegree U) θ ≠ 0 →
      θ ∈ Work.BourgainPlan.IonescuWainger.arcSet 0
        (2 * (2 : ℝ) ^ (-((P.natDegree : ℤ) * 2 * (U : ℤ)) - 1)) := by
    intro θ hθ
    rw [mStargF_eq_mStarF P.natDegree U] at hθ
    have h1 := Work.KMTAreas.A7.periodize_mStarF_mem_arcSet (U := P.natDegree * U) hθ
    have he : (2 : ℝ) ^ (-(2 * (((P.natDegree * U : ℕ)) : ℤ)))
        = (2 : ℝ) ^ (-((P.natDegree : ℤ) * 2 * (U : ℤ))) := by
      congr 1
      push_cast
      ring
    rw [he, h2U] at h1
    exact h1
  -- the band of the slice, and its `ℓ²`-membership
  have hgℓ : Memℓp g 2 :=
    Work.KMTPlan.A6.memlpOfMemLpCount (p := 2) (by norm_num) (by norm_num) hg
  obtain ⟨hh, hhE⟩ :=
    mdlSliceG_zero_band ρ hρ hρ1 P C₀ a g l₁ k₁ k₂ j₂ t n hj₂ hk₂ hN hgℓ hmc
  -- the separation hypothesis of the lift is vacuous at height `0`
  have hsep : ∀ α ∈ Work.Analysis.IonescuWainger.iwArithFreqs ρ 0,
      ∀ β ∈ Work.Analysis.IonescuWainger.iwArithFreqs ρ 0, α ≠ β →
      2 * (2 : ℝ) ^ (-((P.natDegree : ℤ) * 2 * (U : ℤ)) - 1) + γ < ‖α - β‖ := by
    intro α hα β hβ hne
    rw [Work.KMTAreas.A7.iwArithFreqs_zero] at hα hβ
    rw [Finset.mem_singleton] at hα hβ
    exact absurd (hα.trans hβ.symm) hne
  -- the abstract lift
  obtain ⟨W, hWmeas, hWband, hWzero, hWsample⟩ :=
    windowPieceLift_abs (m := Work.KMTAreas.A7.mStargF P.natDegree U) hm hmsum
      (S := 2 * (2 : ℝ) ^ (-((P.natDegree : ℤ) * 2 * (U : ℤ)) - 1)) hmsup (γ := γ)
      hγpos hγhalf (Work.Analysis.IonescuWainger.iwArithFreqs ρ 0)
      (Work.KMTPlan.A6.mdlSliceG ρ P C₀ a l₁ 0 k₁ k₂ j₂ t g n) hh hhE hsep
  refine ⟨W, hWmeas, hWband, hWzero, ?_, ?_⟩
  · intro α hα x
    exact hWsample α hα x
  · intro z
    exact Work.KMTAreas.A7.summable_cw_mul_of_memℓp hmsum hh z

end Work.KMTPlan.A6Clean
