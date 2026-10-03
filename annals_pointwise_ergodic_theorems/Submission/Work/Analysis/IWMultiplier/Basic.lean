/-
Copyright (c) 2026 The AnnalsChallenge team. All rights reserved.
Released under Apache 2.0 license as described in the LICENSE file.
Authors: The AnnalsChallenge team
-/
import Submission.Work.Analysis.IWMultiplier.iwConv_eq_iwOpSet
import Submission.Port.Aesm

/-!
# Elementary API for the vector-valued Ionescu–Wainger multiplier theorem

This file collects the elementary (but not entirely trivial) ingredients of the `q = 2` case of
Theorem `thm:iw` which do not need any Fourier analysis:

* `memLp_of_finiteSupport` — a finitely supported sequence is in `ℓ²(ℤ)`;
* `two_pow_succ_lt_one_of_goodMajorArcs` — for good major arcs with `C_ρ ≥ 2` the frequency arc
  `ℝ_{≤k} = [-2^k, 2^k]` has length `< 1`;
* `periodize_norm_le` — consequently the periodisation does not increase the sup norm;
* `iwConv_eq_sum_of_support` — the IW multiplier on a finitely supported sequence is a finite sum.
-/

set_option autoImplicit false
set_option maxHeartbeats 1000000

open scoped BigOperators ENNReal NNReal FourierTransform
open MeasureTheory

namespace Work.Analysis.IWMultiplier

open Work.Analysis.IonescuWainger

/-- A finitely supported sequence on `ℤ` belongs to `ℓ²(ℤ)`. -/
theorem memLp_of_finiteSupport (f : ℤ → ℂ) (hf : (Function.support f).Finite) : Memℓp f 2 :=
  (memℓp_zero_iff.mpr hf).of_exponent_ge (by norm_num)

/-- Good major arcs with `C_ρ ≥ 2` put the frequency arc `ℝ_{≤k} = [-2^k, 2^k]` strictly inside
an interval of length `< 1`: `2^{k+1} < 1`. -/
theorem two_pow_succ_lt_one_of_goodMajorArcs {ρ Cρ : ℝ} {l : ℕ} {k : ℤ}
    (hgood : GoodMajorArcs ρ Cρ l k) (hCρ : 2 ≤ Cρ) (hρ : 0 < ρ) :
    (2 : ℝ) ^ (k + 1) < 1 := by
  have hS : (1 : ℝ) ≤ (2 : ℝ) ^ (ρ * (l : ℝ)) :=
    Real.one_le_rpow (by norm_num) (by positivity)
  have hmul : 2 * 1 ≤ Cρ * (2 : ℝ) ^ (ρ * (l : ℝ)) :=
    mul_le_mul hCρ hS (by norm_num) (by linarith)
  have hk : (k : ℝ) ≤ -2 := by
    have hg : (k : ℝ) ≤ -Cρ * (2 : ℝ) ^ (ρ * (l : ℝ)) := hgood
    nlinarith
  have hk1 : (k : ℝ) + 1 < 0 := by linarith
  have hlt : (2 : ℝ) ^ ((k : ℝ) + 1) < 1 := by
    have h := (Real.rpow_lt_rpow_left_iff (by norm_num : (1 : ℝ) < 2)).mpr hk1
    simpa using h
  have hcast : ((k + 1 : ℤ) : ℝ) = (k : ℝ) + 1 := by push_cast; ring
  rwa [← Real.rpow_intCast, hcast]

/-- The periodisation of a function supported in `ℝ_{≤k}` with `2^{k+1} < 1` does not increase the
sup norm: at every point of the circle at most one of the summands `φ (x + j)` is nonzero. -/
theorem periodize_norm_le {k : ℤ} (h2 : (2 : ℝ) ^ (k + 1) < 1) {φ : ℝ → ℂ}
    (hφ : ∀ x, φ x ≠ 0 → x ∈ realArc k) {C : ℝ} (hC : ∀ x, ‖φ x‖ ≤ C) :
    ∀ ξ, ‖periodize φ ξ‖ ≤ C := by
  intro ξ
  change ‖∑' j : ℤ, φ ((AddCircle.equivIco (1 : ℝ) 0 ξ).val + j)‖ ≤ C
  set x : ℝ := (AddCircle.equivIco (1 : ℝ) 0 ξ).val with hx
  have hz : (2 : ℝ) ^ (k + 1) = 2 * (2 : ℝ) ^ k := by
    rw [zpow_add_one₀ (by norm_num : (2 : ℝ) ≠ 0)]; ring
  by_cases h : ∃ j : ℤ, φ (x + j) ≠ 0
  · obtain ⟨j₀, hj₀⟩ := h
    have huniq : ∀ j : ℤ, φ (x + j) ≠ 0 → j = j₀ := by
      intro j hj
      have hs : x + j ∈ realArc k := hφ _ hj
      have hs₀ : x + j₀ ∈ realArc k := hφ _ hj₀
      rw [realArc, Set.mem_Icc] at hs hs₀
      have habs : |((j - j₀ : ℤ) : ℝ)| < 1 := by
        rw [abs_lt]
        refine ⟨?_, ?_⟩
        · push_cast; linarith [hs.1, hs₀.2, hz]
        · push_cast; linarith [hs.2, hs₀.1, hz]
      have h1' : (-1 : ℤ) < j - j₀ := by exact_mod_cast (abs_lt.mp habs).1
      have h2' : j - j₀ < (1 : ℤ) := by exact_mod_cast (abs_lt.mp habs).2
      omega
    rw [tsum_eq_single j₀ (fun j hj => by
      by_contra hc
      exact hj (huniq j hc))]
    exact hC _
  · push_neg at h
    rw [show (fun j : ℤ => φ (x + j)) = fun _ => (0 : ℂ) from funext h, tsum_zero, norm_zero]
    exact le_trans (norm_nonneg (φ 0)) (hC 0)

/-- The IW symbol over a finite set of frequencies of an `L^∞` symbol is again `L^∞`: it is a
finite sum of translates of `Φ`, and Haar measure on the circle is translation invariant. -/
theorem memLp_iwSymbolSet (A : Finset Circle) {Φ : Circle → ℂ}
    (h : MemLp Φ ⊤ circleMeasure) :
    MemLp (iwSymbolSet A Φ) ⊤ circleMeasure := by
  have hterm : ∀ α : Circle, MemLp (fun ξ : Circle => Φ (ξ - α)) ⊤ circleMeasure := by
    intro α
    have hmp : MeasurePreserving (fun ξ : Circle => ξ + (-α)) circleMeasure circleMeasure :=
      measurePreserving_add_right circleMeasure (-α)
    have := h.comp_measurePreserving hmp
    simpa [Function.comp_def, sub_eq_add_neg] using this
  have hsum : (∑ α ∈ A, fun ξ : Circle => Φ (ξ - α)) = iwSymbolSet A Φ := by
    funext ξ
    simp [iwSymbolSet]
  rw [← hsum]
  exact memLp_finsetSum' A (fun α _ => hterm α)

/-- `eLpNorm` against the counting measure on `ℤ` is the `ℓ²` norm of the corresponding element
of `lp (fun _ : ℤ => ℂ) 2`. -/
theorem eLpNorm_two_count_eq_ofReal_lpNorm (f : ℤ → ℂ) (hf : Memℓp f 2) :
    eLpNorm f 2 Measure.count = ENNReal.ofReal ‖(⟨f, hf⟩ : lp (fun _ : ℤ => ℂ) 2)‖ := by
  rw [eLpNorm_eq_lintegral_rpow_enorm_toReal (hf := by pw_aesm) (by norm_num) (by norm_num)]
  rw [lintegral_count]
  rw [lp.norm_eq_tsum_rpow (show (0 : ℝ) < (2 : ℝ≥0∞).toReal by norm_num)]
  have h2r : (2 : ℝ≥0∞).toReal = 2 := by norm_num
  rw [h2r]
  have hsumm : Summable (fun n : ℤ => ‖f n‖ ^ (2 : ℝ)) := by
    have h := (memℓp_gen_iff (show (0 : ℝ) < (2 : ℝ≥0∞).toReal by norm_num)).mp hf
    simpa [h2r] using h
  have h1 : (∑' n : ℤ, ‖f n‖ₑ ^ (2 : ℝ)) = ENNReal.ofReal (∑' n : ℤ, ‖f n‖ ^ (2 : ℝ)) := by
    rw [ENNReal.ofReal_tsum_of_nonneg (fun n => Real.rpow_nonneg (norm_nonneg _) 2) hsumm]
    refine tsum_congr fun n => ?_
    rw [← ofReal_norm (f n),
      ENNReal.ofReal_rpow_of_nonneg (norm_nonneg _) (by norm_num : (0 : ℝ) ≤ 2)]
  rw [h1]
  rw [ENNReal.ofReal_rpow_of_nonneg (tsum_nonneg fun n => Real.rpow_nonneg (norm_nonneg _) 2)
    (by norm_num : (0 : ℝ) ≤ 1 / 2)]

/-- **The scalar `q = 2` case of the IW multiplier bound, in ℓ² form.**  If the ℓ² operator norm
of the IW multiplier with symbol `iwSymbolSet A Φ` is at most `C`, then the multiplier is bounded
on `ℓ²(ℤ; ℂ)` with the same constant, in the `IWLqBoundScalar` sense.  This is the combination of
the identification `iwConv_eq_iwOpSet` with the bridge
`eLpNorm_two_count_eq_ofReal_lpNorm`. -/
theorem IWLqBoundScalar_of_norm_le (A : Finset Circle) (Φ : Circle → ℂ)
    (h : MemLp (iwSymbolSet A Φ) ⊤ circleMeasure)
    {C : NNReal} (hC : ‖iwOpSet A Φ h‖ ≤ (C : ℝ)) :
    IWLqBoundScalar A Φ 2 C := by
  intro f hf
  have hfm : Memℓp f 2 := memLp_of_finiteSupport f hf
  set F : L2Z := ⟨f, hfm⟩ with hFdef
  have hFcoe : ⇑F = f := rfl
  have hconv : ⇑(iwOpSet A Φ h F) = iwConv A Φ f := iwConv_eq_iwOpSet A Φ h f hf F hFcoe
  have hmem : Memℓp (iwConv A Φ f) 2 := hconv ▸ (iwOpSet A Φ h F).property
  have e2 : (⟨iwConv A Φ f, hmem⟩ : L2Z) = iwOpSet A Φ h F := Subtype.ext hconv.symm
  rw [eLpNorm_two_count_eq_ofReal_lpNorm (iwConv A Φ f) hmem, e2,
    eLpNorm_two_count_eq_ofReal_lpNorm f hfm]
  calc ENNReal.ofReal ‖iwOpSet A Φ h F‖
      ≤ ENNReal.ofReal ((C : ℝ) * ‖F‖) := by
        refine ENNReal.ofReal_le_ofReal ?_
        calc ‖iwOpSet A Φ h F‖ ≤ ‖iwOpSet A Φ h‖ * ‖F‖ := ContinuousLinearMap.le_opNorm _ _
          _ ≤ (C : ℝ) * ‖F‖ := by gcongr
    _ = ENNReal.ofReal (C : ℝ) * ENNReal.ofReal ‖F‖ := ENNReal.ofReal_mul (by positivity)

end Work.Analysis.IWMultiplier
