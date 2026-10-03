/-
# The height-`0` window-piece lifts with the narrow-band hypothesis derived from `mdlCore`

`Work.KMTPlan.A6Clean.mdlLiftFZero` / `mdlLiftGZero` (`A6Clean/mdlLiftFZero.lean`,
`A6Clean/mdlLiftGZero.lean`) prove the height-`0` window-piece lift of the model slice from the
five hypotheses `mdlCore`, `1 ≤ ⌊a n⌋` and the *narrow band* inequality

  `2^{k₁ - logN ⌊a n⌋} ≤ 2^{-2·uScale ρ (lcL 0 l₂ k₁ k₂) - 1}`   (`hrad`, f-side),

resp. the `d`-scaled twin.  In the proof of `mdlLiftFZero` that inequality is used **exactly
once**, to produce `γ < 1/2` (`γ = 2^{k₁ - logN ⌊a n⌋}`), and the proof of `mdlLiftGZero` uses it
the same way.  But `γ < 1/2` is *already* a consequence of `mdlCore`: `mainRegime ρ k₁ k₂ ⌊a n⌋`
(one of the three conjuncts of `mdlCore`) reads `k₁ + 2·uScale ρ (max k₁ k₂) ≤ logN ⌊a n⌋`, and
`uScale ρ L ≥ 1`, so `k₁ - logN ⌊a n⌋ ≤ -2` and `γ ≤ 1/4 < 1/2`; the `g`-side is the same with the
extra factor `d = P.natDegree ≥ 2`, giving `γ ≤ 2^{-4}`.

Consequently the two lifts are available with **no** narrow-band hypothesis beyond `mdlCore`,
which is what a producer of the §8 adelic clauses for the degenerate data `l₁ = 0 ∨ l₂ = 0` needs
(the docstring of `adelicClausesCaseZero` asserts this; the present module supplies it).

This module is deliberately separate from `adelicClausesCaseZero.lean` so that the two lift lemmas
stay in a `sorry`-free module and can be imported by any consumer (the sibling producer
`adelicClausesCaseA` may drop its regime hypotheses for the degenerate side as well).
-/
import Mathlib
import Submission.Work.KMTPlan.A6Clean.mdlLiftFZero
import Submission.Work.KMTPlan.A6Clean.mdlLiftGZero

set_option autoImplicit false
set_option maxHeartbeats 1600000

namespace Work.KMTPlan.A6Clean

open MeasureTheory
open scoped BigOperators ENNReal NNReal

local notation "Circ" => Work.Analysis.IonescuWainger.Circle

/-- `iwP ρ 0 = {1}`, hence the common denominator `arithQ ρ 0` of the height-`0` arithmetic
frequencies is `1`: at `l = 0` the only arithmetic frequency is `0`, and `(ℚ/ℤ)_{≤0} = {0}`. -/
theorem arithQ_zero (ρ : ℝ) : Work.KMTAreas.A7.arithQ ρ 0 = 1 := by
  rw [Work.KMTAreas.A7.arithQ]
  have h : Work.Analysis.IonescuWainger.iwP ρ 0 = {1} := by
    simp [Work.Analysis.IonescuWainger.iwP]
  rw [h]
  simp

/-- `2^{k₁ - logN ⌊a n⌋} < 1/2` on the core condition (`mainRegime`, a conjunct of `mdlCore`). -/
theorem two_pow_k_sub_logN_lt_half (ρ : ℝ) (hρ : 0 < ρ) (C₀ : ℕ) (a : ℕ → NNReal)
    (l₁ l₂ k₁ k₂ : ℕ) (n : ℕ)
    (hmc : Work.KMTPlan.A6.mdlCore ρ C₀ a l₁ l₂ k₁ k₂ n) :
    (2 : ℝ) ^ ((k₁ : ℝ) - ((Work.Analysis.EndVar.logN (Nat.floor (a n)) : ℤ) : ℝ)) < 1 / 2 := by
  have hmain : k₁ + 2 * Work.KMTAreas.A7.uScale ρ (max k₁ k₂) ≤
      (Work.Analysis.EndVar.logN (Nat.floor (a n))).toNat :=
    ((Work.KMTPlan.A6.mdlCore_iff ρ C₀ a l₁ l₂ k₁ k₂ n).mp hmc).2.2.1
  have hlog0 : (0 : ℤ) ≤ Work.Analysis.EndVar.logN (Nat.floor (a n)) :=
    Work.Analysis.EndVar.logN_nonneg _
  have ht : ((Work.Analysis.EndVar.logN (Nat.floor (a n))).toNat : ℤ)
      = Work.Analysis.EndVar.logN (Nat.floor (a n)) := Int.toNat_of_nonneg hlog0
  have hu : (1 : ℤ) ≤ (Work.KMTAreas.A7.uScale ρ (max k₁ k₂) : ℤ) := by
    exact_mod_cast Work.KMTAreas.A7.one_le_uScale ρ hρ.le (max k₁ k₂)
  have hexp : (k₁ : ℤ) - Work.Analysis.EndVar.logN (Nat.floor (a n)) ≤ -2 := by
    have h1 : (k₁ : ℤ) + 2 * (Work.KMTAreas.A7.uScale ρ (max k₁ k₂) : ℤ)
        ≤ Work.Analysis.EndVar.logN (Nat.floor (a n)) := by
      rw [← ht]
      exact_mod_cast hmain
    omega
  have hcast : ((k₁ : ℝ) - ((Work.Analysis.EndVar.logN (Nat.floor (a n)) : ℤ) : ℝ))
      = ((((k₁ : ℤ) - Work.Analysis.EndVar.logN (Nat.floor (a n))) : ℤ) : ℝ) := by
    push_cast
    ring
  rw [hcast]
  calc (2 : ℝ) ^ ((((k₁ : ℤ) - Work.Analysis.EndVar.logN (Nat.floor (a n))) : ℤ) : ℝ)
      ≤ (2 : ℝ) ^ (((-2 : ℤ)) : ℝ) := by
        refine (Real.rpow_le_rpow_left_iff (by norm_num : (1 : ℝ) < 2)).mpr ?_
        exact_mod_cast hexp
    _ = 1 / 4 := by norm_num
    _ < 1 / 2 := by norm_num

/-- The `g`-side twin: `2^{d·(k₂ - logN ⌊a n⌋)} < 1/2` on the core condition. -/
theorem two_pow_d_mul_k_sub_logN_lt_half (ρ : ℝ) (hρ : 0 < ρ) (P : Polynomial ℤ)
    (hd : 2 ≤ P.natDegree) (C₀ : ℕ) (a : ℕ → NNReal)
    (l₁ l₂ k₁ k₂ : ℕ) (n : ℕ)
    (hmc : Work.KMTPlan.A6.mdlCore ρ C₀ a l₁ l₂ k₁ k₂ n) :
    (2 : ℝ) ^ ((P.natDegree : ℝ) *
      ((k₂ : ℝ) - ((Work.Analysis.EndVar.logN (Nat.floor (a n)) : ℤ) : ℝ))) < 1 / 2 := by
  have hmain : k₂ + 2 * Work.KMTAreas.A7.uScale ρ (max k₁ k₂) ≤
      (Work.Analysis.EndVar.logN (Nat.floor (a n))).toNat :=
    ((Work.KMTPlan.A6.mdlCore_iff ρ C₀ a l₁ l₂ k₁ k₂ n).mp hmc).2.2.2
  have hlog0 : (0 : ℤ) ≤ Work.Analysis.EndVar.logN (Nat.floor (a n)) :=
    Work.Analysis.EndVar.logN_nonneg _
  have ht : ((Work.Analysis.EndVar.logN (Nat.floor (a n))).toNat : ℤ)
      = Work.Analysis.EndVar.logN (Nat.floor (a n)) := Int.toNat_of_nonneg hlog0
  have hu : (1 : ℤ) ≤ (Work.KMTAreas.A7.uScale ρ (max k₁ k₂) : ℤ) := by
    exact_mod_cast Work.KMTAreas.A7.one_le_uScale ρ hρ.le (max k₁ k₂)
  have hk₂ : (k₂ : ℤ) - Work.Analysis.EndVar.logN (Nat.floor (a n)) ≤ -2 := by
    have h1 : (k₂ : ℤ) + 2 * (Work.KMTAreas.A7.uScale ρ (max k₁ k₂) : ℤ)
        ≤ Work.Analysis.EndVar.logN (Nat.floor (a n)) := by
      rw [← ht]
      exact_mod_cast hmain
    omega
  have hd2 : (2 : ℤ) ≤ (P.natDegree : ℤ) := by exact_mod_cast hd
  have hexp : (P.natDegree : ℤ) * ((k₂ : ℤ) - Work.Analysis.EndVar.logN (Nat.floor (a n)))
      ≤ -4 := by
    have h2 := mul_le_mul_of_nonneg_left hk₂ (by omega : (0 : ℤ) ≤ (P.natDegree : ℤ))
    nlinarith
  have hcast : ((P.natDegree : ℝ) *
      ((k₂ : ℝ) - ((Work.Analysis.EndVar.logN (Nat.floor (a n)) : ℤ) : ℝ)))
      = ((((P.natDegree : ℤ) *
          ((k₂ : ℤ) - Work.Analysis.EndVar.logN (Nat.floor (a n)))) : ℤ) : ℝ) := by
    push_cast
    ring
  rw [hcast]
  calc (2 : ℝ) ^ ((((P.natDegree : ℤ) *
        ((k₂ : ℤ) - Work.Analysis.EndVar.logN (Nat.floor (a n)))) : ℤ) : ℝ)
      ≤ (2 : ℝ) ^ (((-2 : ℤ)) : ℝ) := by
        refine (Real.rpow_le_rpow_left_iff (by norm_num : (1 : ℝ) < 2)).mpr ?_
        exact_mod_cast (le_trans hexp (by norm_num : (-4 : ℤ) ≤ -2))
    _ = 1 / 4 := by norm_num
    _ < 1 / 2 := by norm_num

/-- **The `f`-side height-`0` window-piece lift from `mdlCore` alone.**  Identical to
`Work.KMTPlan.A6Clean.mdlLiftFZero` with the narrow-band hypothesis `hrad` deleted (its only use
there is `γ < 1/2`, which `two_pow_k_sub_logN_lt_half` obtains from `mdlCore`). -/
theorem mdlLiftFZeroOfMdlCore (ρ : ℝ) (hρ : 0 < ρ) (hρ1 : ρ ≤ 1) (P : Polynomial ℤ) (hd : 2 ≤ P.natDegree) (C₀ : ℕ) (a : ℕ → NNReal) (f : ℤ → ℂ) (hf : MeasureTheory.MemLp f 2 MeasureTheory.Measure.count) (l₂ k₁ k₂ : ℕ) (j₁ : ℤ) (hj₁ : j₁ ∈ ({-1, 0, 1} : Finset ℤ)) (hk₁ : k₁ = 0 → j₁ ≠ -1) (t : ℝ) (n : ℕ) (hmc : Work.KMTPlan.A6.mdlCore ρ C₀ a 0 l₂ k₁ k₂ n) (hN : 1 ≤ Nat.floor (a n)) : ∃ W : Work.Analysis.IonescuWainger.Circle → ℝ → ℂ, (∀ α, Measurable (W α)) ∧ (∀ α, Work.KMTAreas.A7Rep.HasRealFreqSupport (W α) (Set.Icc (-((2 : ℝ) ^ ((k₁ : ℝ) - ((Work.Analysis.EndVar.logN (Nat.floor (a n)) : ℤ) : ℝ)))) ((2 : ℝ) ^ ((k₁ : ℝ) - ((Work.Analysis.EndVar.logN (Nat.floor (a n)) : ℤ) : ℝ))))) ∧ (∀ α, α ∉ Work.Analysis.IonescuWainger.iwArithFreqs ρ 0 → W α = 0) ∧ (∀ α ∈ Work.Analysis.IonescuWainger.iwArithFreqs ρ 0, ∀ x : ℤ, W α (x : ℝ) = Work.KMTAreas.A7.winConvR (Work.KMTAreas.A7.mStarF (Work.KMTAreas.A7.uScale ρ (Work.KMTPlan.A6.lcL 0 l₂ k₁ k₂))) (Work.KMTAreas.A7.winModR (-α) (Work.KMTPlan.A6.mdlSliceF ρ C₀ a 0 l₂ k₁ k₂ j₁ t f n)) x) ∧ (∀ z : ℤ, Summable (fun j : ℤ => Work.KMTAreas.A7.cw (Work.KMTAreas.A7.mStarF (Work.KMTAreas.A7.uScale ρ (Work.KMTPlan.A6.lcL 0 l₂ k₁ k₂))) j * Work.KMTPlan.A6.mdlSliceF ρ C₀ a 0 l₂ k₁ k₂ j₁ t f n (z - j))) := by
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
    rw [show γ = (2 : ℝ) ^ ((k₁ : ℝ)
      - ((Work.Analysis.EndVar.logN (Nat.floor (a n)) : ℤ) : ℝ)) from rfl]
    exact two_pow_k_sub_logN_lt_half ρ hρ C₀ a 0 l₂ k₁ k₂ n hmc
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

/-- **The `g`-side height-`0` window-piece lift from `mdlCore` alone.**  Identical to
`Work.KMTPlan.A6Clean.mdlLiftGZero` with the narrow-band hypothesis deleted. -/
theorem mdlLiftGZeroOfMdlCore (ρ : ℝ) (hρ : 0 < ρ) (hρ1 : ρ ≤ 1) (P : Polynomial ℤ) (hd : 2 ≤ P.natDegree) (C₀ : ℕ) (a : ℕ → NNReal) (g : ℤ → ℂ) (hg : MeasureTheory.MemLp g 2 MeasureTheory.Measure.count) (l₁ k₁ k₂ : ℕ) (j₂ : ℤ) (hj₂ : j₂ ∈ ({-1, 0, 1} : Finset ℤ)) (hk₂ : k₂ = 0 → j₂ ≠ -1) (t : ℝ) (n : ℕ) (hmc : Work.KMTPlan.A6.mdlCore ρ C₀ a l₁ 0 k₁ k₂ n) (hN : 1 ≤ Nat.floor (a n)) : ∃ W : Work.Analysis.IonescuWainger.Circle → ℝ → ℂ, (∀ α, Measurable (W α)) ∧ (∀ α, Work.KMTAreas.A7Rep.HasRealFreqSupport (W α) (Set.Icc (-((2 : ℝ) ^ ((P.natDegree : ℝ) * ((k₂ : ℝ) - ((Work.Analysis.EndVar.logN (Nat.floor (a n)) : ℤ) : ℝ))))) ((2 : ℝ) ^ ((P.natDegree : ℝ) * ((k₂ : ℝ) - ((Work.Analysis.EndVar.logN (Nat.floor (a n)) : ℤ) : ℝ)))))) ∧ (∀ α, α ∉ Work.Analysis.IonescuWainger.iwArithFreqs ρ 0 → W α = 0) ∧ (∀ α ∈ Work.Analysis.IonescuWainger.iwArithFreqs ρ 0, ∀ x : ℤ, W α (x : ℝ) = Work.KMTAreas.A7.winConvR (Work.KMTAreas.A7.mStargF P.natDegree (Work.KMTAreas.A7.uScale ρ (Work.KMTPlan.A6.lcL l₁ 0 k₁ k₂))) (Work.KMTAreas.A7.winModR (-α) (Work.KMTPlan.A6.mdlSliceG ρ P C₀ a l₁ 0 k₁ k₂ j₂ t g n)) x) ∧ (∀ z : ℤ, Summable (fun j : ℤ => Work.KMTAreas.A7.cw (Work.KMTAreas.A7.mStargF P.natDegree (Work.KMTAreas.A7.uScale ρ (Work.KMTPlan.A6.lcL l₁ 0 k₁ k₂))) j * Work.KMTPlan.A6.mdlSliceG ρ P C₀ a l₁ 0 k₁ k₂ j₂ t g n (z - j))) := by
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
    rw [show γ = (2 : ℝ) ^ ((P.natDegree : ℝ) *
      ((k₂ : ℝ) - ((Work.Analysis.EndVar.logN (Nat.floor (a n)) : ℤ) : ℝ))) from rfl]
    exact two_pow_d_mul_k_sub_logN_lt_half ρ hρ P hd C₀ a l₁ 0 k₁ k₂ n hmc
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

/-- The window convolution of the zero sequence vanishes (the off-core case of the glue below). -/
private lemma winConvR_winModR_zero_zero (m : ℝ → ℂ) (α : Circ) :
    Work.KMTAreas.A7.winConvR m (Work.KMTAreas.A7.winModR (-α) (fun _ : ℤ => (0 : ℂ))) = 0 := by
  funext x
  simp [Work.KMTAreas.A7.winConvR, Work.KMTAreas.A7.winModR]

/-- **The `f`-side lift family at arithmetic height `0`, from `mdlCore` alone.**

This is the (regime-free) `l₁ = 0` analogue of `exists_liftFamilyF` in
`Work.KMTPlan.A6Clean.adelicClausesCaseA`: the per-scale lift is
`mdlLiftFZeroOfMdlCore` on the core scales (where `1 ≤ ⌊a n⌋` follows from
`∀ n, 1 ≤ a n`) and `0` off them. -/
theorem exists_liftFamilyFZero (ρ : ℝ) (hρ : 0 < ρ) (hρ1 : ρ ≤ 1)
    (P : Polynomial ℤ) (hd : 2 ≤ P.natDegree)
    (C₀ : ℕ) (a : ℕ → NNReal) (f : ℤ → ℂ)
    (hf : MeasureTheory.MemLp f 2 MeasureTheory.Measure.count)
    (l₂ k₁ k₂ : ℕ) (j₁ : ℤ) (hj₁ : j₁ ∈ ({-1, 0, 1} : Finset ℤ))
    (hk₁ : k₁ = 0 → j₁ ≠ -1) (t : ℝ) (ha1 : ∀ n : ℕ, 1 ≤ a n) :
    ∃ W : ℕ → Circ → ℝ → ℂ,
      (∀ (n : ℕ) (α : Circ), Measurable (W n α)) ∧
      (∀ (n : ℕ) (α : Circ), Work.KMTAreas.A7Rep.HasRealFreqSupport (W n α)
        (Set.Icc (-((2 : ℝ) ^ ((k₁ : ℝ) - ((Work.Analysis.EndVar.logN (Nat.floor (a n)) : ℤ) : ℝ))))
          ((2 : ℝ) ^ ((k₁ : ℝ) - ((Work.Analysis.EndVar.logN (Nat.floor (a n)) : ℤ) : ℝ))))) ∧
      (∀ (n : ℕ) (α : Circ), α ∉ Work.Analysis.IonescuWainger.iwArithFreqs ρ 0 → W n α = 0) ∧
      (∀ (n : ℕ) (α : Circ), α ∈ Work.Analysis.IonescuWainger.iwArithFreqs ρ 0 → ∀ x : ℤ,
        W n α (x : ℝ) = Work.KMTAreas.A7.winConvR (Work.KMTAreas.A7.mStarF (Work.KMTAreas.A7.uScale ρ (Work.KMTPlan.A6.lcL 0 l₂ k₁ k₂)))
          (Work.KMTAreas.A7.winModR (-α) (Work.KMTPlan.A6.mdlSliceF ρ C₀ a 0 l₂ k₁ k₂ j₁ t f n)) x) ∧
      (∀ (n : ℕ) (z : ℤ), Summable (fun j : ℤ =>
        Work.KMTAreas.A7.cw (Work.KMTAreas.A7.mStarF (Work.KMTAreas.A7.uScale ρ (Work.KMTPlan.A6.lcL 0 l₂ k₁ k₂))) j *
          Work.KMTPlan.A6.mdlSliceF ρ C₀ a 0 l₂ k₁ k₂ j₁ t f n (z - j))) ∧
      (∀ n, ¬ Work.KMTPlan.A6.mdlCore ρ C₀ a 0 l₂ k₁ k₂ n → W n = fun _ _ => (0 : ℂ)) := by
  classical
  have key : ∀ n, Work.KMTPlan.A6.mdlCore ρ C₀ a 0 l₂ k₁ k₂ n → ∃ W₀ : Circ → ℝ → ℂ,
      (∀ α, Measurable (W₀ α)) ∧
      (∀ α, Work.KMTAreas.A7Rep.HasRealFreqSupport (W₀ α)
        (Set.Icc (-((2 : ℝ) ^ ((k₁ : ℝ) - ((Work.Analysis.EndVar.logN (Nat.floor (a n)) : ℤ) : ℝ))))
          ((2 : ℝ) ^ ((k₁ : ℝ) - ((Work.Analysis.EndVar.logN (Nat.floor (a n)) : ℤ) : ℝ))))) ∧
      (∀ α, α ∉ Work.Analysis.IonescuWainger.iwArithFreqs ρ 0 → W₀ α = 0) ∧
      (∀ α, α ∈ Work.Analysis.IonescuWainger.iwArithFreqs ρ 0 → ∀ x : ℤ,
        W₀ α (x : ℝ) = Work.KMTAreas.A7.winConvR (Work.KMTAreas.A7.mStarF (Work.KMTAreas.A7.uScale ρ (Work.KMTPlan.A6.lcL 0 l₂ k₁ k₂)))
          (Work.KMTAreas.A7.winModR (-α) (Work.KMTPlan.A6.mdlSliceF ρ C₀ a 0 l₂ k₁ k₂ j₁ t f n)) x) ∧
      (∀ z : ℤ, Summable (fun j : ℤ =>
        Work.KMTAreas.A7.cw (Work.KMTAreas.A7.mStarF (Work.KMTAreas.A7.uScale ρ (Work.KMTPlan.A6.lcL 0 l₂ k₁ k₂))) j *
          Work.KMTPlan.A6.mdlSliceF ρ C₀ a 0 l₂ k₁ k₂ j₁ t f n (z - j))) := by
    intro n h
    exact mdlLiftFZeroOfMdlCore ρ hρ hρ1 P hd C₀ a f hf l₂ k₁ k₂ j₁ hj₁ hk₁ t n h
      (Nat.le_floor (by exact_mod_cast ha1 n))
  refine ⟨fun n => if h : Work.KMTPlan.A6.mdlCore ρ C₀ a 0 l₂ k₁ k₂ n then
      Classical.choose (key n h) else fun _ _ => 0, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · intro n α
    by_cases h : Work.KMTPlan.A6.mdlCore ρ C₀ a 0 l₂ k₁ k₂ n
    · simp only [dif_pos h]
      exact (Classical.choose_spec (key n h)).1 α
    · simp only [dif_neg h]
      exact measurable_const
  · intro n α
    by_cases h : Work.KMTPlan.A6.mdlCore ρ C₀ a 0 l₂ k₁ k₂ n
    · simp only [dif_pos h]
      exact (Classical.choose_spec (key n h)).2.1 α
    · simp only [dif_neg h]
      exact hasRealFreqSupport_zero _
  · intro n α hα
    by_cases h : Work.KMTPlan.A6.mdlCore ρ C₀ a 0 l₂ k₁ k₂ n
    · simp only [dif_pos h]
      exact (Classical.choose_spec (key n h)).2.2.1 α hα
    · simp only [dif_neg h]
      rfl
  · intro n α hα x
    by_cases h : Work.KMTPlan.A6.mdlCore ρ C₀ a 0 l₂ k₁ k₂ n
    · simp only [dif_pos h]
      exact (Classical.choose_spec (key n h)).2.2.2.1 α hα x
    · simp only [dif_neg h]
      have hz : Work.KMTPlan.A6.mdlSliceF ρ C₀ a 0 l₂ k₁ k₂ j₁ t f n = fun _ : ℤ => (0 : ℂ) := by
        simp only [Work.KMTPlan.A6.mdlSliceF, h, if_false]
        rfl
      rw [hz, winConvR_winModR_zero_zero]
      rfl
  · intro n z
    by_cases h : Work.KMTPlan.A6.mdlCore ρ C₀ a 0 l₂ k₁ k₂ n
    · exact (Classical.choose_spec (key n h)).2.2.2.2 z
    · have hz : Work.KMTPlan.A6.mdlSliceF ρ C₀ a 0 l₂ k₁ k₂ j₁ t f n = fun _ : ℤ => (0 : ℂ) := by
        simp only [Work.KMTPlan.A6.mdlSliceF, h, if_false]
        rfl
      rw [hz]
      simp [mul_zero]
  · intro n h
    simp only [dif_neg h]

/-- **The `g`-side lift family at arithmetic height `0`, from `mdlCore` alone.**  The `l₂ = 0`
twin of `exists_liftFamilyFZero`. -/
theorem exists_liftFamilyGZero (ρ : ℝ) (hρ : 0 < ρ) (hρ1 : ρ ≤ 1)
    (P : Polynomial ℤ) (hd : 2 ≤ P.natDegree)
    (C₀ : ℕ) (a : ℕ → NNReal) (g : ℤ → ℂ)
    (hg : MeasureTheory.MemLp g 2 MeasureTheory.Measure.count)
    (l₁ k₁ k₂ : ℕ) (j₂ : ℤ) (hj₂ : j₂ ∈ ({-1, 0, 1} : Finset ℤ))
    (hk₂ : k₂ = 0 → j₂ ≠ -1) (t : ℝ) (ha1 : ∀ n : ℕ, 1 ≤ a n) :
    ∃ W : ℕ → Circ → ℝ → ℂ,
      (∀ (n : ℕ) (α : Circ), Measurable (W n α)) ∧
      (∀ (n : ℕ) (α : Circ), Work.KMTAreas.A7Rep.HasRealFreqSupport (W n α)
        (Set.Icc (-((2 : ℝ) ^ ((P.natDegree : ℝ) *
              ((k₂ : ℝ) - ((Work.Analysis.EndVar.logN (Nat.floor (a n)) : ℤ) : ℝ)))))
          ((2 : ℝ) ^ ((P.natDegree : ℝ) *
              ((k₂ : ℝ) - ((Work.Analysis.EndVar.logN (Nat.floor (a n)) : ℤ) : ℝ)))))) ∧
      (∀ (n : ℕ) (α : Circ), α ∉ Work.Analysis.IonescuWainger.iwArithFreqs ρ 0 → W n α = 0) ∧
      (∀ (n : ℕ) (α : Circ), α ∈ Work.Analysis.IonescuWainger.iwArithFreqs ρ 0 → ∀ x : ℤ,
        W n α (x : ℝ) = Work.KMTAreas.A7.winConvR (Work.KMTAreas.A7.mStargF P.natDegree (Work.KMTAreas.A7.uScale ρ (Work.KMTPlan.A6.lcL l₁ 0 k₁ k₂)))
          (Work.KMTAreas.A7.winModR (-α) (Work.KMTPlan.A6.mdlSliceG ρ P C₀ a l₁ 0 k₁ k₂ j₂ t g n)) x) ∧
      (∀ (n : ℕ) (z : ℤ), Summable (fun j : ℤ =>
        Work.KMTAreas.A7.cw (Work.KMTAreas.A7.mStargF P.natDegree (Work.KMTAreas.A7.uScale ρ (Work.KMTPlan.A6.lcL l₁ 0 k₁ k₂))) j *
          Work.KMTPlan.A6.mdlSliceG ρ P C₀ a l₁ 0 k₁ k₂ j₂ t g n (z - j))) ∧
      (∀ n, ¬ Work.KMTPlan.A6.mdlCore ρ C₀ a l₁ 0 k₁ k₂ n → W n = fun _ _ => (0 : ℂ)) := by
  classical
  have key : ∀ n, Work.KMTPlan.A6.mdlCore ρ C₀ a l₁ 0 k₁ k₂ n → ∃ W₀ : Circ → ℝ → ℂ,
      (∀ α, Measurable (W₀ α)) ∧
      (∀ α, Work.KMTAreas.A7Rep.HasRealFreqSupport (W₀ α)
        (Set.Icc (-((2 : ℝ) ^ ((P.natDegree : ℝ) *
              ((k₂ : ℝ) - ((Work.Analysis.EndVar.logN (Nat.floor (a n)) : ℤ) : ℝ)))))
          ((2 : ℝ) ^ ((P.natDegree : ℝ) *
              ((k₂ : ℝ) - ((Work.Analysis.EndVar.logN (Nat.floor (a n)) : ℤ) : ℝ)))))) ∧
      (∀ α, α ∉ Work.Analysis.IonescuWainger.iwArithFreqs ρ 0 → W₀ α = 0) ∧
      (∀ α, α ∈ Work.Analysis.IonescuWainger.iwArithFreqs ρ 0 → ∀ x : ℤ,
        W₀ α (x : ℝ) = Work.KMTAreas.A7.winConvR (Work.KMTAreas.A7.mStargF P.natDegree (Work.KMTAreas.A7.uScale ρ (Work.KMTPlan.A6.lcL l₁ 0 k₁ k₂)))
          (Work.KMTAreas.A7.winModR (-α) (Work.KMTPlan.A6.mdlSliceG ρ P C₀ a l₁ 0 k₁ k₂ j₂ t g n)) x) ∧
      (∀ z : ℤ, Summable (fun j : ℤ =>
        Work.KMTAreas.A7.cw (Work.KMTAreas.A7.mStargF P.natDegree (Work.KMTAreas.A7.uScale ρ (Work.KMTPlan.A6.lcL l₁ 0 k₁ k₂))) j *
          Work.KMTPlan.A6.mdlSliceG ρ P C₀ a l₁ 0 k₁ k₂ j₂ t g n (z - j))) := by
    intro n h
    exact mdlLiftGZeroOfMdlCore ρ hρ hρ1 P hd C₀ a g hg l₁ k₁ k₂ j₂ hj₂ hk₂ t n h
      (Nat.le_floor (by exact_mod_cast ha1 n))
  refine ⟨fun n => if h : Work.KMTPlan.A6.mdlCore ρ C₀ a l₁ 0 k₁ k₂ n then
      Classical.choose (key n h) else fun _ _ => 0, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · intro n α
    by_cases h : Work.KMTPlan.A6.mdlCore ρ C₀ a l₁ 0 k₁ k₂ n
    · simp only [dif_pos h]
      exact (Classical.choose_spec (key n h)).1 α
    · simp only [dif_neg h]
      exact measurable_const
  · intro n α
    by_cases h : Work.KMTPlan.A6.mdlCore ρ C₀ a l₁ 0 k₁ k₂ n
    · simp only [dif_pos h]
      exact (Classical.choose_spec (key n h)).2.1 α
    · simp only [dif_neg h]
      exact hasRealFreqSupport_zero _
  · intro n α hα
    by_cases h : Work.KMTPlan.A6.mdlCore ρ C₀ a l₁ 0 k₁ k₂ n
    · simp only [dif_pos h]
      exact (Classical.choose_spec (key n h)).2.2.1 α hα
    · simp only [dif_neg h]
      rfl
  · intro n α hα x
    by_cases h : Work.KMTPlan.A6.mdlCore ρ C₀ a l₁ 0 k₁ k₂ n
    · simp only [dif_pos h]
      exact (Classical.choose_spec (key n h)).2.2.2.1 α hα x
    · simp only [dif_neg h]
      have hz : Work.KMTPlan.A6.mdlSliceG ρ P C₀ a l₁ 0 k₁ k₂ j₂ t g n = fun _ : ℤ => (0 : ℂ) := by
        simp only [Work.KMTPlan.A6.mdlSliceG, h, if_false]
        rfl
      rw [hz, winConvR_winModR_zero_zero]
      rfl
  · intro n z
    by_cases h : Work.KMTPlan.A6.mdlCore ρ C₀ a l₁ 0 k₁ k₂ n
    · exact (Classical.choose_spec (key n h)).2.2.2.2 z
    · have hz : Work.KMTPlan.A6.mdlSliceG ρ P C₀ a l₁ 0 k₁ k₂ j₂ t g n = fun _ : ℤ => (0 : ℂ) := by
        simp only [Work.KMTPlan.A6.mdlSliceG, h, if_false]
        rfl
      rw [hz]
      simp [mul_zero]
  · intro n h
    simp only [dif_neg h]

end Work.KMTPlan.A6Clean
