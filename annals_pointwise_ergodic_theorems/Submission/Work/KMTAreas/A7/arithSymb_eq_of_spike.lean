/-
# The arithmetic symbol on a spike (Area A7)

The lemma `Work.KMTAreas.A7.arithSymb_eq_of_spike` is the *collapse* of the arithmetic symbol
`Arith` of the §6 model approximation at a frequency `(β₁,β₂)` of the exact-height arithmetic
frequencies, with non-aliasing at the scale `-2u`:

    arithSymb ρ P l₁ l₂ u θ₁ θ₂ = mZ P (arithQ ρ (max l₁ l₂)) β₁ β₂

whenever `θ₁` is within `2^{-2u-1}` of `β₁` and `θ₂` is within `2^{-(d·2u)-1}` of `β₂`
(`d = P.natDegree`).

The content is the standard non-aliasing collapse: `arithSymb` is the double sum over
`α₁ ∈ (ℚ/ℤ)_{l₁} \ (ℚ/ℤ)_{l₁-1}`, `α₂ ∈ (ℚ/ℤ)_{l₂} \ (ℚ/ℤ)_{l₂-1}` of
`m_Ẑ(α₁,α₂) · (periodize m_*)(θ₁-α₁) · (periodize m̃_*)(θ₂-α₂)`, where the two windows are

* `m_* = mStarF u = η_{≤-2u}`, which equals `1` on the arc of radius `2^{-2u-1}` and vanishes off
  the arc of radius `2^{-2u}`, and
* `m̃_* = mStargF d u = η_{≤-d·2u}`, which equals `1` on the arc of radius `2^{-d·2u-1}` and
  vanishes off the arc of radius `2^{-d·2u}`.

Since `θ₁ - β₁` lies in the *plateau* of `m_*` and `θ₂ - β₂` in the plateau of `m̃_*`, the
supports of the two periodised windows meet the spike arcs of `β₁` and `β₂`; non-aliasing at the
(coarser) scale `-2u` then forces `α₁ = β₁`, `α₂ = β₂`, and the two plateau factors are `1`, which
is exactly the collapse.

The mathematical hypotheses are also quantitatively sharp: the support of `m_*` has radius
`2^{-2u}`, which is `< 1/2` exactly because `u ≥ 1`, and the support of `m̃_*` has radius
`2^{-d·2u} < 1/2` exactly because `d = P.natDegree ≥ 1`; this is where `hu` and `hd` are used.
-/
import Mathlib
import Submission.Work.KMTAreas.A7.smallKernelMass_le

namespace Work.KMTAreas.A7

noncomputable section

open MeasureTheory Polynomial Finset Filter Topology
open scoped ENNReal NNReal BigOperators
open PointwiseErgodicTheorems Submission.PointwiseErgodicTheorems
open Work.Analysis.IonescuWainger

/-! ## The plateau and support of the two §6 windows -/

/-- `m_* = η_{≤-2u}` is `1` on `[-2^{-2u-1}, 2^{-2u-1}]`. -/
lemma arithSymbSpike_mStarF_eq_one {U : ℕ} {x : ℝ}
    (hx : |x| ≤ (2 : ℝ) ^ (-(2 * (U : ℤ)) - 1)) : mStarF U x = 1 := by
  rw [mStarF, etaCut]
  refine Work.KMTContract.kmtEta_one ?_
  have hb : (0 : ℝ) < (2 : ℝ) ^ (-(2 * (U : ℤ))) := zpow_pos (by norm_num) _
  rw [abs_div, abs_of_pos hb, div_le_iff₀ hb]
  calc |x| ≤ (2 : ℝ) ^ (-(2 * (U : ℤ)) - 1) := hx
    _ = (1 / 2) * (2 : ℝ) ^ (-(2 * (U : ℤ))) := by
        rw [zpow_sub₀ (by norm_num : (2 : ℝ) ≠ 0), zpow_one]
        ring

/-- `m_* = η_{≤-2u}` vanishes off `(-2^{-2u}, 2^{-2u})`. -/
lemma arithSymbSpike_mStarF_eq_zero {U : ℕ} {x : ℝ}
    (hx : (2 : ℝ) ^ (-(2 * (U : ℤ))) ≤ |x|) : mStarF U x = 0 := by
  rw [mStarF, etaCut]
  refine Work.KMTContract.kmtEta_zero ?_
  have hb : (0 : ℝ) < (2 : ℝ) ^ (-(2 * (U : ℤ))) := zpow_pos (by norm_num) _
  rw [abs_div, abs_of_pos hb, le_div_iff₀ hb]
  simpa using hx

/-- The support of `m_* = η_{≤-2u}` is `[-2^{-2u}, 2^{-2u}]`. -/
lemma arithSymbSpike_mStarF_support (U : ℕ) :
    ∀ x : ℝ, mStarF U x ≠ 0 → |x| ≤ (2 : ℝ) ^ (-(2 * (U : ℤ))) := by
  intro x hx
  by_contra hlt
  rw [not_le] at hlt
  exact hx (arithSymbSpike_mStarF_eq_zero hlt.le)

/-- `m̃_* = η_{≤-d·2u}` is `1` on `[-2^{-d·2u-1}, 2^{-d·2u-1}]`. -/
lemma arithSymbSpike_mStargF_eq_one {d U : ℕ} {x : ℝ}
    (hx : |x| ≤ (2 : ℝ) ^ (-((d : ℤ) * 2 * (U : ℤ)) - 1)) : mStargF d U x = 1 := by
  rw [mStargF, etaCut]
  refine Work.KMTContract.kmtEta_one ?_
  have hb : (0 : ℝ) < (2 : ℝ) ^ (-((d : ℤ) * 2 * (U : ℤ))) := zpow_pos (by norm_num) _
  rw [abs_div, abs_of_pos hb, div_le_iff₀ hb]
  calc |x| ≤ (2 : ℝ) ^ (-((d : ℤ) * 2 * (U : ℤ)) - 1) := hx
    _ = (1 / 2) * (2 : ℝ) ^ (-((d : ℤ) * 2 * (U : ℤ))) := by
        rw [zpow_sub₀ (by norm_num : (2 : ℝ) ≠ 0), zpow_one]
        ring

/-- `m̃_* = η_{≤-d·2u}` vanishes off `(-2^{-d·2u}, 2^{-d·2u})`. -/
lemma arithSymbSpike_mStargF_eq_zero {d U : ℕ} {x : ℝ}
    (hx : (2 : ℝ) ^ (-((d : ℤ) * 2 * (U : ℤ))) ≤ |x|) : mStargF d U x = 0 := by
  rw [mStargF, etaCut]
  refine Work.KMTContract.kmtEta_zero ?_
  have hb : (0 : ℝ) < (2 : ℝ) ^ (-((d : ℤ) * 2 * (U : ℤ))) := zpow_pos (by norm_num) _
  rw [abs_div, abs_of_pos hb, le_div_iff₀ hb]
  simpa using hx

/-- The support of `m̃_* = η_{≤-d·2u}` is `[-2^{-d·2u}, 2^{-d·2u}]`. -/
lemma arithSymbSpike_mStargF_support (d U : ℕ) :
    ∀ x : ℝ, mStargF d U x ≠ 0 → |x| ≤ (2 : ℝ) ^ (-((d : ℤ) * 2 * (U : ℤ))) := by
  intro x hx
  by_contra hlt
  rw [not_le] at hlt
  exact hx (arithSymbSpike_mStargF_eq_zero hlt.le)

/-! ## Elementary circle facts -/

/-- Membership of `realArc k` from an absolute-value bound. -/
lemma arithSymbSpike_mem_realArc {k : ℤ} {x : ℝ} (hx : |x| ≤ (2 : ℝ) ^ k) : x ∈ realArc k := by
  rw [realArc, Set.mem_Icc]
  exact abs_le.mp hx

/-- **A nonvanishing periodisation detects a real representative in the support.**  If `φ`
vanishes off `[-δ,δ]` and `periodize φ θ ≠ 0`, then `θ` is the image of some real `θ₀` with
`|θ₀| ≤ δ`.  (A translate `x + k` of the canonical representative `x ∈ [0,1)` of `θ` carries a
nonzero value of `φ`.) -/
lemma arithSymbSpike_exists_coe_abs_le_of_periodize_ne_zero {φ : ℝ → ℂ} {δ : ℝ}
    (hsupp : ∀ y : ℝ, φ y ≠ 0 → |y| ≤ δ) {θ : Work.Analysis.IonescuWainger.Circle} (h : periodize φ θ ≠ 0) :
    ∃ θ₀ : ℝ, (θ₀ : Work.Analysis.IonescuWainger.Circle) = θ ∧ |θ₀| ≤ δ := by
  set x : ℝ := (AddCircle.equivIco (1 : ℝ) 0 θ).val with hxdef
  have hxθ : (x : Work.Analysis.IonescuWainger.Circle) = θ := by
    rw [hxdef]; exact AddCircle.coe_equivIco
  have hper : periodize φ θ = ∑' k : ℤ, φ (x + (k : ℝ)) := by
    rw [← hxθ]
    exact Work.KMTContract.periodizeCoeEqTsum φ x
  have hne : ∃ k : ℤ, φ (x + (k : ℝ)) ≠ 0 := by
    by_contra hcon
    have hcon' : ∀ k : ℤ, φ (x + (k : ℝ)) = 0 := fun k => by
      by_contra hk
      exact hcon ⟨k, hk⟩
    refine h ?_
    rw [hper]
    have h0 : (fun k : ℤ => φ (x + (k : ℝ))) = fun _ => (0 : ℂ) := funext hcon'
    rw [h0, tsum_zero]
  obtain ⟨k, hk⟩ := hne
  refine ⟨x + (k : ℝ), ?_, hsupp _ hk⟩
  have hkc : (((k : ℝ)) : Work.Analysis.IonescuWainger.Circle) = 0 := by
    rw [AddCircle.coe_eq_zero_iff]
    exact ⟨k, by simp⟩
  rw [AddCircle.coe_add, hxθ, hkc, add_zero]

/-- **The periodisation of `m_*` is `1` on the spike arc** of radius `2^{-2u-1}`. -/
lemma arithSymbSpike_periodize_mStarF_eq_one {U : ℕ} (hU : 1 ≤ U) {θ : Work.Analysis.IonescuWainger.Circle}
    (hθ : |lift θ| ≤ (2 : ℝ) ^ (-(2 * (U : ℤ)) - 1)) : periodize (mStarF U) θ = 1 := by
  have hUZ : (1 : ℤ) ≤ (U : ℤ) := by exact_mod_cast hU
  have hw : (2 : ℝ) ^ (-(2 * (U : ℤ))) < 1 / 2 := by
    have h1 : (2 : ℝ) ^ (-(2 * (U : ℤ))) ≤ (2 : ℝ) ^ (-2 : ℤ) :=
      zpow_le_zpow_right₀ (by norm_num : (1 : ℝ) ≤ 2) (by omega)
    have h2 : (2 : ℝ) ^ (-2 : ℤ) = 1 / 4 := by norm_num
    rw [h2] at h1; linarith
  rw [periodize_eq_lift hw (arithSymbSpike_mStarF_support U) θ]
  exact arithSymbSpike_mStarF_eq_one hθ

/-- **The periodisation of `m̃_*` is `1` on the spike arc** of radius `2^{-d·2u-1}`. -/
lemma arithSymbSpike_periodize_mStargF_eq_one {d U : ℕ} (hd : 1 ≤ d) (hU : 1 ≤ U) {θ : Work.Analysis.IonescuWainger.Circle}
    (hθ : |lift θ| ≤ (2 : ℝ) ^ (-((d : ℤ) * 2 * (U : ℤ)) - 1)) :
    periodize (mStargF d U) θ = 1 := by
  have hdZ : (1 : ℤ) ≤ (d : ℤ) := by exact_mod_cast hd
  have hUZ : (1 : ℤ) ≤ (U : ℤ) := by exact_mod_cast hU
  have hw : (2 : ℝ) ^ (-((d : ℤ) * 2 * (U : ℤ))) < 1 / 2 := by
    have h1 : (2 : ℝ) ^ (-((d : ℤ) * 2 * (U : ℤ))) ≤ (2 : ℝ) ^ (-2 : ℤ) :=
      zpow_le_zpow_right₀ (by norm_num : (1 : ℝ) ≤ 2) (by nlinarith)
    have h2 : (2 : ℝ) ^ (-2 : ℤ) = 1 / 4 := by norm_num
    rw [h2] at h1; linarith
  rw [periodize_eq_lift hw (arithSymbSpike_mStargF_support d U) θ]
  exact arithSymbSpike_mStargF_eq_one hθ

/-! ## The collapse -/

theorem arithSymb_eq_of_spike (ρ : ℝ) (P : Polynomial ℤ) (l₁ l₂ u : ℕ)
    (hd : 1 ≤ P.natDegree)
    {β₁ β₂ : Work.Analysis.IonescuWainger.Circle}
    (hβ₁ : β₁ ∈ Work.KMTAreas.A7.diffFreqs ρ l₁)
    (hβ₂ : β₂ ∈ Work.KMTAreas.A7.diffFreqs ρ l₂)
    (hNA₁ : Work.Analysis.IonescuWainger.NonAliasing (-(2 * (u : ℤ)))
      (Work.KMTAreas.A7.diffFreqs ρ l₁))
    (hNA₂ : Work.Analysis.IonescuWainger.NonAliasing (-(2 * (u : ℤ)))
      (Work.KMTAreas.A7.diffFreqs ρ l₂))
    (hu : 1 ≤ u)
    {θ₁ θ₂ : Work.Analysis.IonescuWainger.Circle}
    (hξ₁ : |Work.KMTAreas.A7.lift (θ₁ - β₁)| ≤ (2 : ℝ) ^ (-(2 * (u : ℤ)) - 1))
    (hξ₂ : |Work.KMTAreas.A7.lift (θ₂ - β₂)|
      ≤ (2 : ℝ) ^ (-((P.natDegree : ℤ) * 2 * (u : ℤ)) - 1)) :
    Work.KMTAreas.A7.arithSymb ρ P l₁ l₂ u θ₁ θ₂
      = Work.KMTAreas.A7.mZ P (Work.KMTAreas.A7.arithQ ρ (max l₁ l₂)) β₁ β₂ := by
  have hUZ : (1 : ℤ) ≤ (u : ℤ) := by exact_mod_cast hu
  have hdZ : (1 : ℤ) ≤ (P.natDegree : ℤ) := by exact_mod_cast hd
  -- the arc of `m̃_*` sits inside the (coarser) arc at which non-aliasing is assumed
  have harc : realArc (-((P.natDegree : ℤ) * 2 * (u : ℤ))) ⊆ realArc (-(2 * (u : ℤ))) := by
    intro x hx
    rw [realArc, Set.mem_Icc] at hx ⊢
    have hle : (2 : ℝ) ^ (-((P.natDegree : ℤ) * 2 * (u : ℤ))) ≤ (2 : ℝ) ^ (-(2 * (u : ℤ))) := by
      refine zpow_le_zpow_right₀ (by norm_num : (1 : ℝ) ≤ 2) ?_
      have hmul : (2 : ℤ) * (u : ℤ) ≤ (P.natDegree : ℤ) * 2 * (u : ℤ) := by
        have h1 : (2 : ℤ) ≤ (P.natDegree : ℤ) * 2 := by linarith
        exact mul_le_mul_of_nonneg_right h1 (by linarith)
      linarith
    exact ⟨by linarith [hx.1], by linarith [hx.2]⟩
  -- the two spike facts: only `α₁ = β₁` and `α₂ = β₂` can be seen by the windows
  have spike₁ : ∀ α ∈ diffFreqs ρ l₁, periodize (mStarF u) (θ₁ - α) ≠ 0 → α = β₁ := by
    intro α hα hne
    obtain ⟨y, hyc, hyle⟩ :=
      arithSymbSpike_exists_coe_abs_le_of_periodize_ne_zero (arithSymbSpike_mStarF_support u) hne
    have hyarc : y ∈ realArc (-(2 * (u : ℤ))) := arithSymbSpike_mem_realArc hyle
    have hlift : lift (θ₁ - β₁) ∈ realArc (-(2 * (u : ℤ))) :=
      arithSymbSpike_mem_realArc (le_trans hξ₁ (zpow_le_zpow_right₀ (by norm_num) (by omega)))
    have heq : β₁ + ((lift (θ₁ - β₁)) : Work.Analysis.IonescuWainger.Circle) = α + (y : Work.Analysis.IonescuWainger.Circle) := by
      rw [hyc, lift_coe]
      abel
    exact (hNA₁ β₁ hβ₁ α hα (lift (θ₁ - β₁)) hlift y hyarc heq).1.symm
  have spike₂ : ∀ α ∈ diffFreqs ρ l₂, periodize (mStargF P.natDegree u) (θ₂ - α) ≠ 0 → α = β₂ := by
    intro α hα hne
    obtain ⟨y, hyc, hyle⟩ :=
      arithSymbSpike_exists_coe_abs_le_of_periodize_ne_zero
        (arithSymbSpike_mStargF_support P.natDegree u) hne
    have hyarc : y ∈ realArc (-(2 * (u : ℤ))) := harc (arithSymbSpike_mem_realArc hyle)
    have hlift : lift (θ₂ - β₂) ∈ realArc (-(2 * (u : ℤ))) :=
      harc (arithSymbSpike_mem_realArc
        (le_trans hξ₂ (zpow_le_zpow_right₀ (by norm_num) (by omega))))
    have heq : β₂ + ((lift (θ₂ - β₂)) : Work.Analysis.IonescuWainger.Circle) = α + (y : Work.Analysis.IonescuWainger.Circle) := by
      rw [hyc, lift_coe]
      abel
    exact (hNA₂ β₂ hβ₂ α hα (lift (θ₂ - β₂)) hlift y hyarc heq).1.symm
  -- the two plateau factors at the spike are `1`
  have hP₁ : periodize (mStarF u) (θ₁ - β₁) = 1 := arithSymbSpike_periodize_mStarF_eq_one hu hξ₁
  have hP₂ : periodize (mStargF P.natDegree u) (θ₂ - β₂) = 1 :=
    arithSymbSpike_periodize_mStargF_eq_one hd hu hξ₂
  unfold arithSymb
  rw [Finset.sum_eq_single_of_mem β₁ hβ₁ (fun α hα hne => by
    refine Finset.sum_eq_zero (fun α₂ _ => ?_)
    have h0 : periodize (mStarF u) (θ₁ - α) = 0 := by
      by_contra hc
      exact hne (spike₁ α hα hc)
    simp [h0])]
  rw [Finset.sum_eq_single_of_mem β₂ hβ₂ (fun α hα hne => by
    have h0 : periodize (mStargF P.natDegree u) (θ₂ - α) = 0 := by
      by_contra hc
      exact hne (spike₂ α hα hc)
    simp [h0])]
  rw [hP₁, hP₂]
  ring

end

end Work.KMTAreas.A7
