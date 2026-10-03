/-
# The height-`0` window-piece lift of the model `f`-side family

`mdlLiftFZero` is the `l₁ = 0` member of the family `mdlWindowLiftF`
(`MdlWindowLiftF.lean`): for the `f`-side packet family `mdlSliceF ρ C₀ a 0 l₂ k₁ k₂ j₁ t f n`
of the frozen-`t` slice at *arithmetic height* `0`, there is a family
`W : Circle → ℝ → ℂ` with the properties the §8 adelic form needs:

* each `W α` is the inverse Fourier transform of an integrable function supported in the real
  arc `[-γ, γ]`, `γ = 2^{k₁ - Log ⌊a n⌋}`;
* `W α` vanishes off the arithmetic frequency set `(ℚ/ℤ)_{≤0} = {0}`, and on `(ℚ/ℤ)_{≤0}` its
  integer samples are the window pieces `winConvR (mStarF U) (winModR (-α) s)` of the slice `s`.

## Why height `0` is a separate statement

At height `0` the arithmetic frequency set collapses to the singleton
`iwArithFreqs ρ 0 = {0}` (`Work.KMTAreas.A7.iwArithFreqs_zero`), hence

* the separation condition `S + γ < ‖α - β‖` of the abstract lift `windowPieceLift_abs` is
  vacuous (there are no two distinct elements);
* the band of the input is the band of the plain multiplier `Tle ρ 0 φ`, produced by the
  height-`0` band statement `Work.KMTPlan.A6.TleBandVarphiNtj` — *not* by the exact-height
  form `Tm` used at `l₁ ≥ 1`, whose non-aliasing hypothesis at the arc `-uScale ρ L` is
  **false** when `uScale ρ L = 1` (`realArc (-1) = [-1/2, 1/2]` and `1/2 = -1/2` on the circle).
  So the `l₁ = 0` case is genuinely not an instance of `mdlWindowLiftF`.

The band of `mdlSliceF` is established here as `mdlSliceF_zero_band` in the *exact* radius form
appearing in `mdlLiftFZero` (it is `Work.KMTPlan.A6.MdlSliceFband` without its unused `hmain`
hypothesis, at `l₁ = 0` so that no separate vanishing of the window pieces off the exact heights
is needed).

The final `Summable` conjunct is the proved
`Work.KMTAreas.A7.summable_cw_mul_of_memℓp`, applied to the `ℓ²`-membership of the slice.
-/
import Mathlib
import Submission.Work.KMTPlan.A6Clean.MdlWindowLiftF
import Submission.Work.KMTPlan.A6Clean.mdlF_hasFreqSupport_exact

set_option autoImplicit false
set_option maxHeartbeats 1600000

namespace Work.KMTPlan.A6Clean

open MeasureTheory
open scoped BigOperators ENNReal NNReal

local notation "Circ" => Work.Analysis.IonescuWainger.Circle

/-- **The band of the `f`-side packet family at arithmetic height `0`.**  On the core condition
the family `mdlSliceF ρ C₀ a 0 l₂ k₁ k₂ j₁ t f n` is the Ionescu–Wainger projection
`Tle ρ 0 (varphiNtj ⌊a n⌋ k₁ j₁ t) (mdlF ρ U 0 f)` of the modified bump against the exact-height
shell `mdlF`; by `Work.KMTPlan.A6.TleBandVarphiNtj` it is square summable and band limited to the
`2^{k₁ - Log ⌊a n⌋}`-arc around `0` — the only element of `(ℚ/ℤ)_{≤0} = {0}`. -/
theorem mdlSliceF_zero_band (ρ : ℝ) (hρ : 0 < ρ) (hρ1 : ρ ≤ 1) (C₀ : ℕ) (a : ℕ → NNReal)
    (f : ℤ → ℂ) (l₂ k₁ k₂ : ℕ) (j₁ : ℤ) (t : ℝ) (n : ℕ)
    (hj₁ : j₁ ∈ ({-1, 0, 1} : Finset ℤ)) (hk₁ : k₁ = 0 → j₁ ≠ -1)
    (hN : 1 ≤ Nat.floor (a n)) (hf : Memℓp f 2)
    (hmc : Work.KMTPlan.A6.mdlCore ρ C₀ a 0 l₂ k₁ k₂ n) :
    ∃ h : Memℓp (Work.KMTPlan.A6.mdlSliceF ρ C₀ a 0 l₂ k₁ k₂ j₁ t f n) 2,
      Work.BourgainPlan.IonescuWainger.HasFreqSupport
        (Work.KMTPlan.A6.mdlSliceF ρ C₀ a 0 l₂ k₁ k₂ j₁ t f n) h
        (⋃ α ∈ Work.Analysis.IonescuWainger.iwArithFreqs ρ 0,
          Work.BourgainPlan.IonescuWainger.arcSet α
            ((2 : ℝ) ^ ((k₁ : ℝ)
              - ((Work.Analysis.EndVar.logN (Nat.floor (a n)) : ℤ) : ℝ)))) := by
  classical
  -- on the core condition the family is a single `Tle` of the modified bump
  have hslice : Work.KMTPlan.A6.mdlSliceF ρ C₀ a 0 l₂ k₁ k₂ j₁ t f n
      = Work.KMTAreas.A7.Tle ρ 0 (Work.KMTPlan.A6.varphiNtj (Nat.floor (a n)) k₁ j₁ t)
          (Work.KMTPlan.A6.mdlF ρ
            (Work.KMTAreas.A7.uScale ρ (max (max 0 l₂) (max k₁ k₂))) 0 f) := by
    simp only [Work.KMTPlan.A6.mdlSliceF, hmc, if_true]
  -- the input `mdlF` is `ℓ²`
  obtain ⟨hm, -⟩ := mdlF_hasFreqSupport_exact ρ hρ hρ1
    (Work.KMTAreas.A7.uScale ρ (max (max 0 l₂) (max k₁ k₂))) 0 f hf
  rw [hslice]
  exact Work.KMTPlan.A6.TleBandVarphiNtj ρ 0 (Nat.floor (a n)) k₁ j₁ t
    (Work.KMTPlan.A6.mdlF ρ (Work.KMTAreas.A7.uScale ρ (max (max 0 l₂) (max k₁ k₂))) 0 f)
    hj₁ hk₁ hN hm

theorem mdlLiftFZero (ρ : ℝ) (hρ : 0 < ρ) (hρ1 : ρ ≤ 1) (P : Polynomial ℤ) (hd : 2 ≤ P.natDegree) (C₀ : ℕ) (a : ℕ → NNReal) (f : ℤ → ℂ) (hf : MeasureTheory.MemLp f 2 MeasureTheory.Measure.count) (l₂ k₁ k₂ : ℕ) (j₁ : ℤ) (hj₁ : j₁ ∈ ({-1, 0, 1} : Finset ℤ)) (hk₁ : k₁ = 0 → j₁ ≠ -1) (t : ℝ) (n : ℕ) (hmc : Work.KMTPlan.A6.mdlCore ρ C₀ a 0 l₂ k₁ k₂ n) (hN : 1 ≤ Nat.floor (a n)) (hrad : (2 : ℝ) ^ ((k₁ : ℝ) - ((Work.Analysis.EndVar.logN (Nat.floor (a n)) : ℤ) : ℝ)) ≤ (2 : ℝ) ^ (-(2 * (Work.KMTAreas.A7.uScale ρ (Work.KMTPlan.A6.lcL 0 l₂ k₁ k₂) : ℤ)) - 1)) : ∃ W : Work.Analysis.IonescuWainger.Circle → ℝ → ℂ, (∀ α, Measurable (W α)) ∧ (∀ α, Work.KMTAreas.A7Rep.HasRealFreqSupport (W α) (Set.Icc (-((2 : ℝ) ^ ((k₁ : ℝ) - ((Work.Analysis.EndVar.logN (Nat.floor (a n)) : ℤ) : ℝ)))) ((2 : ℝ) ^ ((k₁ : ℝ) - ((Work.Analysis.EndVar.logN (Nat.floor (a n)) : ℤ) : ℝ))))) ∧ (∀ α, α ∉ Work.Analysis.IonescuWainger.iwArithFreqs ρ 0 → W α = 0) ∧ (∀ α ∈ Work.Analysis.IonescuWainger.iwArithFreqs ρ 0, ∀ x : ℤ, W α (x : ℝ) = Work.KMTAreas.A7.winConvR (Work.KMTAreas.A7.mStarF (Work.KMTAreas.A7.uScale ρ (Work.KMTPlan.A6.lcL 0 l₂ k₁ k₂))) (Work.KMTAreas.A7.winModR (-α) (Work.KMTPlan.A6.mdlSliceF ρ C₀ a 0 l₂ k₁ k₂ j₁ t f n)) x) ∧ (∀ z : ℤ, Summable (fun j : ℤ => Work.KMTAreas.A7.cw (Work.KMTAreas.A7.mStarF (Work.KMTAreas.A7.uScale ρ (Work.KMTPlan.A6.lcL 0 l₂ k₁ k₂))) j * Work.KMTPlan.A6.mdlSliceF ρ C₀ a 0 l₂ k₁ k₂ j₁ t f n (z - j))) := by
  classical
  -- the window scale and the band radius
  let U : ℕ := Work.KMTAreas.A7.uScale ρ (Work.KMTPlan.A6.lcL 0 l₂ k₁ k₂)
  let γ : ℝ := (2 : ℝ) ^ ((k₁ : ℝ) - ((Work.Analysis.EndVar.logN (Nat.floor (a n)) : ℤ) : ℝ))
  have hU1 : 1 ≤ U := Work.KMTAreas.A7.one_le_uScale ρ hρ.le _
  have h2U : (2 : ℝ) ^ (-(2 * (U : ℤ))) = 2 * ((2 : ℝ) ^ (-(2 * (U : ℤ)) - 1)) := by
    rw [show (-(2 * (U : ℤ)) : ℤ) = (-(2 * (U : ℤ)) - 1) + 1 by ring,
      zpow_add₀ (by norm_num : (2 : ℝ) ≠ 0), zpow_one]
    ring
  have hγpos : 0 < γ := by
    rw [show γ = (2 : ℝ) ^ ((k₁ : ℝ)
      - ((Work.Analysis.EndVar.logN (Nat.floor (a n)) : ℤ) : ℝ)) from rfl]
    exact Real.rpow_pos_of_pos (by norm_num) _
  have hγhalf : γ < 1 / 2 := by
    have hle : γ ≤ (2 : ℝ) ^ (-(2 * (U : ℤ)) - 1) := hrad
    have h1 : (2 : ℝ) ^ (-(2 * (U : ℤ)) - 1) ≤ (8 : ℝ)⁻¹ := by
      have h2 : (-(2 * (U : ℤ)) - 1 : ℤ) ≤ -3 := by
        have hUZ : (1 : ℤ) ≤ (U : ℤ) := by exact_mod_cast hU1
        omega
      have h3 := zpow_le_zpow_right₀ (by norm_num : (1 : ℝ) ≤ 2) h2
      have h4 : (2 : ℝ) ^ ((-3 : ℤ)) = (8 : ℝ)⁻¹ := by norm_num
      rw [h4] at h3
      exact h3
    have h12 : (8 : ℝ)⁻¹ < 1 / 2 := by norm_num
    linarith
  -- the window facts
  have hm : Integrable (Work.KMTAreas.A7.mStarF U) := Work.KMTAreas.A7.kmt_integrable_mStarF U
  have hmsum : Summable (fun j : ℤ => ‖Work.KMTAreas.A7.cw (Work.KMTAreas.A7.mStarF U) j‖) :=
    Work.KMTAreas.A7.summable_cw_mStarF U
  have hmsup : ∀ θ : Circ, Work.Analysis.IonescuWainger.periodize (Work.KMTAreas.A7.mStarF U) θ
      ≠ 0 → θ ∈ Work.BourgainPlan.IonescuWainger.arcSet 0 (2 * (2 : ℝ) ^ (-(2 * (U : ℤ)) - 1)) := by
    intro θ hθ
    have h1 := Work.KMTAreas.A7.periodize_mStarF_mem_arcSet (U := U) hθ
    rw [h2U] at h1
    exact h1
  -- the band of the slice, and its `ℓ²`-membership
  have hfℓ : Memℓp f 2 :=
    Work.KMTPlan.A6.memlpOfMemLpCount (p := 2) (by norm_num) (by norm_num) hf
  obtain ⟨hh, hhE⟩ := mdlSliceF_zero_band ρ hρ hρ1 C₀ a f l₂ k₁ k₂ j₁ t n hj₁ hk₁ hN hfℓ hmc
  -- the separation hypothesis of the lift is vacuous at height `0`
  have hsep : ∀ α ∈ Work.Analysis.IonescuWainger.iwArithFreqs ρ 0,
      ∀ β ∈ Work.Analysis.IonescuWainger.iwArithFreqs ρ 0, α ≠ β →
      2 * (2 : ℝ) ^ (-(2 * (U : ℤ)) - 1) + γ < ‖α - β‖ := by
    intro α hα β hβ hne
    rw [Work.KMTAreas.A7.iwArithFreqs_zero] at hα hβ
    rw [Finset.mem_singleton] at hα hβ
    exact absurd (hα.trans hβ.symm) hne
  -- the abstract lift
  obtain ⟨W, hWmeas, hWband, hWzero, hWsample⟩ :=
    windowPieceLift_abs (m := Work.KMTAreas.A7.mStarF U) hm hmsum
      (S := 2 * (2 : ℝ) ^ (-(2 * (U : ℤ)) - 1)) hmsup (γ := γ) hγpos hγhalf
      (Work.Analysis.IonescuWainger.iwArithFreqs ρ 0)
      (Work.KMTPlan.A6.mdlSliceF ρ C₀ a 0 l₂ k₁ k₂ j₁ t f n) hh hhE hsep
  refine ⟨W, hWmeas, hWband, hWzero, ?_, ?_⟩
  · intro α hα x
    exact hWsample α hα x
  · intro z
    exact Work.KMTAreas.A7.summable_cw_mul_of_memℓp hmsum hh z

end Work.KMTPlan.A6Clean
