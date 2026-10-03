import Mathlib
import Submission.Work.KMTAreas.A7.spikeDefs
import Submission.Work.KMTAreas.A7.collapse
import Submission.Work.KMTAreas.A7c.AvgSymbWeyl
import Submission.Work.KMTAreas.A7c.ArithSymbSpike

set_option maxHeartbeats 4000000

/-
# The §6 collapse `concSymb − modSymbC = ∑_β spike_β` (Area A7)

This module proves the two symbol identities on which the §6 model approximation
(`Work.KMTAreas.A7.smallKernelMass_le`, the paper's Proposition `mod-approx`) rests, in the
`𝕋²`-symbol vocabulary of `Work.KMTAreas.A7.symbolDefs`:

* `integral_iwSymbolSet_varphiNt_mul` — the `t`-integral of the product of the two *modulated*
  exact-height Ionescu--Wainger symbols is the (finite) sum over the exact-height arithmetic
  frequencies `β = (β₁,β₂)` of the *mean spike* `meanSpike β`; this is the `t`-integral version of
  `Work.KMTAreas.A7.integral_periodize_varphiNt_mul`.  It is what shows that `modSymbC` is
  `arithSymb` times a sum of spikes.

* `modSymbC_eq_arithSymb_mul` — the symbol `modSymbC` of the model kernel is the arithmetic symbol
  `arithSymb` times that sum of mean spikes.

* `concSymb_sub_modSymbC_eq_sum_spikeSymb` — **the collapse**: on the main regime
  `max k₁ k₂ + 2u + 1 ≤ Log N` and under the non-aliasing of the exact-height arithmetic
  frequencies at the arc radius `2^{-2u}`, the difference of the two symbols is the sum of the
  *spike symbols* `spikeSymb β = Φ₁(·-β₁)Φ₂(·-β₂)·M₀(β,ξ)`.  The point is that on the support of
  the narrow bump `Φ₁(·-β₁)Φ₂(·-β₂)` the arithmetic symbol collapses to its `β`-term and the
  discrete average equals the Weyl average `weylAvg β ξ`, so the bracket is exactly the paper's
  symbol difference `M₀`.
-/

set_option autoImplicit false
set_option maxHeartbeats 16000000

namespace Work.KMTAreas.A7.Cpy

noncomputable section

open MeasureTheory Polynomial Finset Filter Topology
open scoped ENNReal NNReal BigOperators
open Work.Analysis.IonescuWainger

/-! ## The support radii of the §6 bumps -/

/-- If `2^A * |ξ| < 1` then `|ξ| ≤ 2^{-A}`. -/
lemma abs_le_rpow_neg_of_mul_lt_one {A : ℝ} {ξ : ℝ} (h : (2 : ℝ) ^ A * |ξ| < 1) :
    |ξ| ≤ (2 : ℝ) ^ (-A) := by
  have hp : (0 : ℝ) < (2 : ℝ) ^ A := Real.rpow_pos_of_pos (by norm_num) _
  have h1 : |ξ| < 1 / (2 : ℝ) ^ A := by
    rw [lt_div_iff₀ hp]
    rwa [mul_comm] at h
  have h2 : (2 : ℝ) ^ (-A) = 1 / (2 : ℝ) ^ A := by
    rw [Real.rpow_neg (by norm_num : (0 : ℝ) ≤ 2), inv_eq_one_div]
  rw [h2]
  exact le_of_lt h1

/-- The support radius of the §6 bump `φ_N`: a nonzero value of `φ_N` forces `|ξ| ≤ 2^{k - Log N}`.
(The `k = 0` case is not covered by `varphiNt_support_le`, which assumes `1 ≤ k`.) -/
theorem varphiN_ne_zero_abs_le (N k : ℕ) {ξ : ℝ} (h : varphiN N k ξ ≠ 0) :
    |ξ| ≤ (2 : ℝ) ^ ((k : ℝ) - (Work.Analysis.EndVar.logN N : ℝ)) := by
  rcases eq_or_ne k 0 with hk | hk
  · subst hk
    have hf : varphiN N 0 ξ
        = Work.KMTContract.kmtEta ((2 : ℝ) ^ ((Work.Analysis.EndVar.logN N : ℝ)) * ξ) := by
      rw [varphiN, if_pos rfl]
    rw [hf] at h
    have h2 : (2 : ℝ) ^ ((Work.Analysis.EndVar.logN N : ℝ)) * |ξ| < 1 := by
      have h1 : ¬ ((1 : ℝ) ≤ |(2 : ℝ) ^ ((Work.Analysis.EndVar.logN N : ℝ)) * ξ|) :=
        fun hc => h (Work.KMTContract.kmtEta_zero hc)
      have h3 : |(2 : ℝ) ^ ((Work.Analysis.EndVar.logN N : ℝ)) * ξ| < 1 := lt_of_not_ge h1
      rwa [abs_mul, abs_of_pos (Real.rpow_pos_of_pos (by norm_num) _)] at h3
    have h4 := abs_le_rpow_neg_of_mul_lt_one (A := (Work.Analysis.EndVar.logN N : ℝ))
      (ξ := ξ) h2
    simpa using h4
  · have hk1 : 1 ≤ k := Nat.one_le_iff_ne_zero.mpr hk
    refine varphiNt_support_le k hk1 N 0 ξ ?_
    simpa [varphiNt, ee] using h

/-- The support radius of the §6 bump `φ̃_N`: a nonzero value of `φ̃_N` forces
`|ξ| ≤ 2^{d(k - Log N)}`. -/
theorem varphitildeN_ne_zero_abs_le (d N k : ℕ) (hd : 1 ≤ d) {ξ : ℝ}
    (h : varphitildeN d N k ξ ≠ 0) :
    |ξ| ≤ (2 : ℝ) ^ ((d : ℝ) * ((k : ℝ) - (Work.Analysis.EndVar.logN N : ℝ))) := by
  rcases eq_or_ne k 0 with hk | hk
  · subst hk
    have hf : varphitildeN d N 0 ξ
        = Work.KMTContract.kmtEta
            ((2 : ℝ) ^ ((d : ℝ) * (Work.Analysis.EndVar.logN N : ℝ)) * ξ) := by
      rw [varphitildeN, if_pos rfl]
    rw [hf] at h
    have h2 : (2 : ℝ) ^ ((d : ℝ) * (Work.Analysis.EndVar.logN N : ℝ)) * |ξ| < 1 := by
      have h1 : ¬ ((1 : ℝ) ≤
          |(2 : ℝ) ^ ((d : ℝ) * (Work.Analysis.EndVar.logN N : ℝ)) * ξ|) :=
        fun hc => h (Work.KMTContract.kmtEta_zero hc)
      have h3 : |(2 : ℝ) ^ ((d : ℝ) * (Work.Analysis.EndVar.logN N : ℝ)) * ξ| < 1 :=
        lt_of_not_ge h1
      rwa [abs_mul, abs_of_pos (Real.rpow_pos_of_pos (by norm_num) _)] at h3
    have h4 := abs_le_rpow_neg_of_mul_lt_one
      (A := (d : ℝ) * (Work.Analysis.EndVar.logN N : ℝ)) (ξ := ξ) h2
    simpa using h4
  · have hf : varphitildeN d N k ξ
        = Work.KMTContract.kmtEta
            ((2 : ℝ) ^ ((d : ℝ) * ((Work.Analysis.EndVar.logN N : ℝ) - (k : ℝ))) * ξ)
          - Work.KMTContract.kmtEta
              ((2 : ℝ) ^ ((d : ℝ) * ((Work.Analysis.EndVar.logN N : ℝ) - (k : ℝ) + 1)) * ξ) := by
      rw [varphitildeN, if_neg hk]
    rw [hf] at h
    have hbor : Work.KMTContract.kmtEta
          ((2 : ℝ) ^ ((d : ℝ) * ((Work.Analysis.EndVar.logN N : ℝ) - (k : ℝ))) * ξ) ≠ 0
        ∨ Work.KMTContract.kmtEta
          ((2 : ℝ) ^ ((d : ℝ) * ((Work.Analysis.EndVar.logN N : ℝ) - (k : ℝ) + 1)) * ξ) ≠ 0 := by
      by_contra hc
      push Not at hc
      exact h (by rw [hc.1, hc.2, sub_zero])
    have hrearr : (2 : ℝ) ^ ((d : ℝ) * ((k : ℝ) - (Work.Analysis.EndVar.logN N : ℝ)))
        = (2 : ℝ) ^ (-((d : ℝ) * ((Work.Analysis.EndVar.logN N : ℝ) - (k : ℝ)))) := by
      congr 1; ring
    rw [hrearr]
    rcases hbor with h1 | h1
    · refine abs_le_rpow_neg_of_mul_lt_one (A := (d : ℝ) * ((Work.Analysis.EndVar.logN N : ℝ) - (k : ℝ)))
        (ξ := ξ) ?_
      have h3 : ¬ ((1 : ℝ) ≤
          |(2 : ℝ) ^ ((d : ℝ) * ((Work.Analysis.EndVar.logN N : ℝ) - (k : ℝ))) * ξ|) :=
        fun hc => h1 (Work.KMTContract.kmtEta_zero hc)
      have h4 : |(2 : ℝ) ^ ((d : ℝ) * ((Work.Analysis.EndVar.logN N : ℝ) - (k : ℝ))) * ξ| < 1 :=
        lt_of_not_ge h3
      rwa [abs_mul, abs_of_pos (Real.rpow_pos_of_pos (by norm_num) _)] at h4
    · have h4 : |ξ| ≤ (2 : ℝ) ^
          (-((d : ℝ) * ((Work.Analysis.EndVar.logN N : ℝ) - (k : ℝ) + 1))) := by
        refine abs_le_rpow_neg_of_mul_lt_one
          (A := (d : ℝ) * ((Work.Analysis.EndVar.logN N : ℝ) - (k : ℝ) + 1)) (ξ := ξ) ?_
        have h3 : ¬ ((1 : ℝ) ≤
            |(2 : ℝ) ^ ((d : ℝ) * ((Work.Analysis.EndVar.logN N : ℝ) - (k : ℝ) + 1)) * ξ|) :=
          fun hc => h1 (Work.KMTContract.kmtEta_zero hc)
        have h5 : |(2 : ℝ) ^ ((d : ℝ) * ((Work.Analysis.EndVar.logN N : ℝ) - (k : ℝ) + 1)) * ξ| < 1 :=
          lt_of_not_ge h3
        rwa [abs_mul, abs_of_pos (Real.rpow_pos_of_pos (by norm_num) _)] at h5
      have hd0 : (0 : ℝ) ≤ (d : ℝ) := by positivity
      have hexp2 : -((d : ℝ) * ((Work.Analysis.EndVar.logN N : ℝ) - (k : ℝ) + 1))
          ≤ -((d : ℝ) * ((Work.Analysis.EndVar.logN N : ℝ) - (k : ℝ))) := by nlinarith
      exact le_trans h4
        (Real.rpow_le_rpow_left_iff (by norm_num : (1 : ℝ) < 2) |>.mpr hexp2)

/-! ## Continuity in `t` of the periodised modulated bumps -/

private lemma continuous_periodize_varphiNt (N k : ℕ) {w : ℝ} (hw : w < 1 / 2)
    (h : ∀ x : ℝ, varphiN N k x ≠ 0 → |x| ≤ w) (γ : AddCircle 1) :
    Continuous (fun t : ℝ => periodize (varphiNt N k t) γ) := by
  have hfun : ∀ t : ℝ, periodize (varphiNt N k t) γ
      = varphiN N k (lift γ) * ee ((N : ℝ) * t * lift γ) := by
    intro t
    change periodize (fun ξ : ℝ => varphiN N k ξ * ee (((N : ℝ) * t) * ξ)) γ = _
    exact periodize_mul_ee_eq_lift (w := w) hw h γ
  rw [show (fun t : ℝ => periodize (varphiNt N k t) γ)
      = fun t : ℝ => varphiN N k (lift γ) * ee ((N : ℝ) * t * lift γ) from funext hfun]
  refine Continuous.mul continuous_const ?_
  unfold ee
  fun_prop

private lemma continuous_periodize_varphitildeNt (P : Polynomial ℤ) (d N k : ℕ) {w : ℝ}
    (hw : w < 1 / 2) (h : ∀ x : ℝ, varphitildeN d N k x ≠ 0 → |x| ≤ w) (γ : AddCircle 1) :
    Continuous (fun t : ℝ => periodize (varphitildeNt P d N k t) γ) := by
  have hfun : ∀ t : ℝ, periodize (varphitildeNt P d N k t) γ
      = varphitildeN d N k (lift γ) * ee (PevalR P ((N : ℝ) * t) * lift γ) := by
    intro t
    change periodize (fun ξ : ℝ => varphitildeN d N k ξ * ee (PevalR P ((N : ℝ) * t) * ξ)) γ = _
    exact periodize_mul_ee_eq_lift (w := w) hw h γ
  rw [show (fun t : ℝ => periodize (varphitildeNt P d N k t) γ)
      = fun t : ℝ => varphitildeN d N k (lift γ) * ee (PevalR P ((N : ℝ) * t) * lift γ) from
      funext hfun]
  refine Continuous.mul continuous_const ?_
  have hP : Continuous (fun t : ℝ => PevalR P ((N : ℝ) * t)) :=
    ((P.map (Int.castRingHom ℝ)).continuous).comp (continuous_const.mul continuous_id)
  unfold ee
  refine Complex.continuous_exp.comp ?_
  have h2 : Continuous (fun t : ℝ => ((PevalR P ((N : ℝ) * t) * lift γ : ℝ) : ℂ)) :=
    Complex.continuous_ofReal.comp (hP.mul continuous_const)
  have h3 : Continuous (fun t : ℝ => (2 : ℂ) * ↑Real.pi * Complex.I
      * ((PevalR P ((N : ℝ) * t) * lift γ : ℝ) : ℂ)) := by
    refine Continuous.mul continuous_const h2
  simpa only [Complex.ofReal_mul] using h3

/-! ## The `t`-integral of the two modulated Ionescu--Wainger symbols -/

/-- **The `t`-integral of the product of the two modulated exact-height symbols.**  For narrow
bumps the `t`-integral of the product of the two periodised modulated bumps is the product of the
bumps times the oscillatory integral `mTilde` (`integral_periodize_varphiNt_mul`), so the
`t`-integral of the product of the two *symbols* is the sum of the *mean spikes* over the
exact-height arithmetic frequencies. -/
theorem integral_iwSymbolSet_varphiNt_mul (P : Polynomial ℤ) (ρ : ℝ) (l₁ l₂ k₁ k₂ N : ℕ)
    (θ₁ θ₂ : AddCircle 1) {w₁ w₂ : ℝ} (hw₁ : w₁ < 1 / 2) (hw₂ : w₂ < 1 / 2)
    (h₁ : ∀ x : ℝ, varphiN N k₁ x ≠ 0 → |x| ≤ w₁)
    (h₂ : ∀ x : ℝ, varphitildeN P.natDegree N k₂ x ≠ 0 → |x| ≤ w₂) :
    (∫ t in (1 / 2 : ℝ)..1,
        iwSymbolSet (diffFreqs ρ l₁) (periodize (varphiNt N k₁ t)) θ₁
          * iwSymbolSet (diffFreqs ρ l₂) (periodize (varphitildeNt P P.natDegree N k₂ t)) θ₂)
      = ∑ β₁ ∈ diffFreqs ρ l₁, ∑ β₂ ∈ diffFreqs ρ l₂,
          meanSpike P k₁ k₂ N β₁ β₂ θ₁ θ₂ := by
  have hexp : ∀ t : ℝ, iwSymbolSet (diffFreqs ρ l₁) (periodize (varphiNt N k₁ t)) θ₁
        * iwSymbolSet (diffFreqs ρ l₂) (periodize (varphitildeNt P P.natDegree N k₂ t)) θ₂
      = ∑ p ∈ (diffFreqs ρ l₁) ×ˢ (diffFreqs ρ l₂),
          periodize (varphiNt N k₁ t) (θ₁ - p.1)
            * periodize (varphitildeNt P P.natDegree N k₂ t) (θ₂ - p.2) := by
    intro t
    rw [iwSymbolSet_apply, iwSymbolSet_apply, Finset.sum_mul_sum, Finset.sum_product]
  have hint : ∀ p ∈ (diffFreqs ρ l₁) ×ˢ (diffFreqs ρ l₂), IntervalIntegrable (fun t : ℝ =>
      periodize (varphiNt N k₁ t) (θ₁ - p.1)
        * periodize (varphitildeNt P P.natDegree N k₂ t) (θ₂ - p.2)) volume (1 / 2) 1 := by
    intro p hp
    refine Continuous.intervalIntegrable ?_ _ _
    exact (continuous_periodize_varphiNt N k₁ hw₁ h₁ (θ₁ - p.1)).mul
      (continuous_periodize_varphitildeNt P P.natDegree N k₂ hw₂ h₂ (θ₂ - p.2))
  rw [intervalIntegral.integral_congr (fun t _ => hexp t)]
  rw [intervalIntegral.integral_finsetSum
    (s := (diffFreqs ρ l₁) ×ˢ (diffFreqs ρ l₂))
    (f := fun p t => periodize (varphiNt N k₁ t) (θ₁ - p.1)
      * periodize (varphitildeNt P P.natDegree N k₂ t) (θ₂ - p.2)) hint]
  rw [Finset.sum_product]
  refine Finset.sum_congr rfl fun β₁ hβ₁ => Finset.sum_congr rfl fun β₂ hβ₂ => ?_
  rw [integral_periodize_varphiNt_mul N k₁ k₂ P hw₁ hw₂ h₁ h₂ (θ₁ - β₁) (θ₂ - β₂)]
  simp only [meanSpike, bumpSymb]
  rw [periodize_eq_lift (w := w₁) hw₁ h₁, periodize_eq_lift (w := w₂) hw₂ h₂]

/-- **The symbol of the model kernel is the arithmetic symbol times the sum of the mean spikes.** -/
theorem modSymbC_eq_arithSymb_mul_meanSpike (ρ : ℝ) (P : Polynomial ℤ) (l₁ l₂ k₁ k₂ N : ℕ)
    {w₁ w₂ : ℝ} (hw₁ : w₁ < 1 / 2) (hw₂ : w₂ < 1 / 2)
    (h₁ : ∀ x : ℝ, varphiN N k₁ x ≠ 0 → |x| ≤ w₁)
    (h₂ : ∀ x : ℝ, varphitildeN P.natDegree N k₂ x ≠ 0 → |x| ≤ w₂) :
    modSymbC ρ P l₁ l₂ k₁ k₂ N
      = fun θ₁ θ₂ => arithSymb ρ P l₁ l₂ (uScale ρ (smallL l₁ l₂ k₁ k₂)) θ₁ θ₂
          * ∑ β₁ ∈ diffFreqs ρ l₁, ∑ β₂ ∈ diffFreqs ρ l₂,
              meanSpike P k₁ k₂ N β₁ β₂ θ₁ θ₂ := by
  funext θ₁ θ₂
  simp only [modSymbC]
  rw [show (∫ t in (1 / 2 : ℝ)..1,
        arithSymb ρ P l₁ l₂ (uScale ρ (smallL l₁ l₂ k₁ k₂)) θ₁ θ₂
          * iwSymbolSet (diffFreqs ρ l₁) (periodize (varphiNt N k₁ t)) θ₁
          * iwSymbolSet (diffFreqs ρ l₂) (periodize (varphitildeNt P P.natDegree N k₂ t)) θ₂)
      = ∫ t in (1 / 2 : ℝ)..1,
          arithSymb ρ P l₁ l₂ (uScale ρ (smallL l₁ l₂ k₁ k₂)) θ₁ θ₂
            * (iwSymbolSet (diffFreqs ρ l₁) (periodize (varphiNt N k₁ t)) θ₁
              * iwSymbolSet (diffFreqs ρ l₂) (periodize (varphitildeNt P P.natDegree N k₂ t)) θ₂)
      from intervalIntegral.integral_congr (fun t _ => by ring)]
  rw [intervalIntegral.integral_const_mul]
  congr 1
  exact integral_iwSymbolSet_varphiNt_mul P ρ l₁ l₂ k₁ k₂ N θ₁ θ₂ hw₁ hw₂ h₁ h₂

/-! ## The collapse -/

/-- **The §6 collapse.**  On the main regime (the bumps narrow enough that the windows `m_*` are
`1` on their support, encoded by `hw₁u`, `hw₂u`) and under the non-aliasing of the exact-height
arithmetic frequencies at the arc radius `2^{-2u}`, the difference of the two symbols is the sum
of the spike symbols. -/
theorem concSymb_sub_modSymbC_eq_sum_spikeSymb (ρ : ℝ) (P : Polynomial ℤ) (l₁ l₂ k₁ k₂ N : ℕ)
    (hd : 1 ≤ P.natDegree)
    {w₁ w₂ : ℝ} (hw₁ : w₁ < 1 / 2) (hw₂ : w₂ < 1 / 2)
    (h₁ : ∀ x : ℝ, varphiN N k₁ x ≠ 0 → |x| ≤ w₁)
    (h₂ : ∀ x : ℝ, varphitildeN P.natDegree N k₂ x ≠ 0 → |x| ≤ w₂)
    (hw₁u : w₁ ≤ (2 : ℝ) ^ (-(2 * ((uScale ρ (smallL l₁ l₂ k₁ k₂)) : ℤ)) - 1))
    (hw₂u : w₂ ≤ (2 : ℝ) ^
      (-((P.natDegree : ℤ) * 2 * ((uScale ρ (smallL l₁ l₂ k₁ k₂)) : ℤ)) - 1))
    (hu : 1 ≤ uScale ρ (smallL l₁ l₂ k₁ k₂))
    (hNA₁ : NonAliasing (-(2 * ((uScale ρ (smallL l₁ l₂ k₁ k₂)) : ℤ))) (diffFreqs ρ l₁))
    (hNA₂ : NonAliasing (-(2 * ((uScale ρ (smallL l₁ l₂ k₁ k₂)) : ℤ))) (diffFreqs ρ l₂)) :
    concSymb ρ P l₁ l₂ k₁ k₂ N - modSymbC ρ P l₁ l₂ k₁ k₂ N
      = fun θ₁ θ₂ => ∑ β₁ ∈ diffFreqs ρ l₁, ∑ β₂ ∈ diffFreqs ρ l₂,
          spikeSymb ρ P l₁ l₂ k₁ k₂ N β₁ β₂ θ₁ θ₂ := by
  funext θ₁ θ₂
  change concSymb ρ P l₁ l₂ k₁ k₂ N θ₁ θ₂ - modSymbC ρ P l₁ l₂ k₁ k₂ N θ₁ θ₂
      = ∑ β₁ ∈ diffFreqs ρ l₁, ∑ β₂ ∈ diffFreqs ρ l₂, spikeSymb ρ P l₁ l₂ k₁ k₂ N β₁ β₂ θ₁ θ₂
  rw [modSymbC_eq_arithSymb_mul_meanSpike ρ P l₁ l₂ k₁ k₂ N hw₁ hw₂ h₁ h₂]
  have hconc : concSymb ρ P l₁ l₂ k₁ k₂ N θ₁ θ₂
      = ∑ β₁ ∈ diffFreqs ρ l₁, ∑ β₂ ∈ diffFreqs ρ l₂,
          (periodize (varphiN N k₁) (θ₁ - β₁)
            * periodize (varphitildeN P.natDegree N k₂) (θ₂ - β₂)) * avgSymb P N θ₁ θ₂ := by
    simp only [concSymb, iwSymbolSet_apply]
    rw [Finset.sum_mul_sum, Finset.sum_mul]
    congr 1
    funext β₁
    rw [Finset.sum_mul]
  rw [hconc]
  beta_reduce
  rw [Finset.mul_sum, ← Finset.sum_sub_distrib]
  refine Finset.sum_congr rfl fun β₁ hβ₁ => ?_
  rw [Finset.mul_sum, ← Finset.sum_sub_distrib]
  refine Finset.sum_congr rfl fun β₂ hβ₂ => ?_
  by_cases hb : periodize (varphiN N k₁) (θ₁ - β₁)
      * periodize (varphitildeN P.natDegree N k₂) (θ₂ - β₂) = 0
  · simp only [spikeSymb, bumpSymb, meanSpike, hb]
    ring
  · have hb1 : periodize (varphiN N k₁) (θ₁ - β₁) ≠ 0 := fun hh => hb (by rw [hh, zero_mul])
    have hb2 : periodize (varphitildeN P.natDegree N k₂) (θ₂ - β₂) ≠ 0 :=
      fun hh => hb (by rw [hh, mul_zero])
    have hp1 : periodize (varphiN N k₁) (θ₁ - β₁) = varphiN N k₁ (lift (θ₁ - β₁)) :=
      periodize_eq_lift (w := w₁) hw₁ h₁ _
    have hp2 : periodize (varphitildeN P.natDegree N k₂) (θ₂ - β₂)
        = varphitildeN P.natDegree N k₂ (lift (θ₂ - β₂)) :=
      periodize_eq_lift (w := w₂) hw₂ h₂ _
    have hξ₁ : |lift (θ₁ - β₁)| ≤ (2 : ℝ) ^ (-(2 * ((uScale ρ (smallL l₁ l₂ k₁ k₂)) : ℤ)) - 1) := by
      rw [hp1] at hb1
      exact le_trans (h₁ _ hb1) hw₁u
    have hξ₂ : |lift (θ₂ - β₂)|
        ≤ (2 : ℝ) ^ (-((P.natDegree : ℤ) * 2 * ((uScale ρ (smallL l₁ l₂ k₁ k₂)) : ℤ)) - 1) := by
      rw [hp2] at hb2
      exact le_trans (h₂ _ hb2) hw₂u
    have havg : avgSymb P N θ₁ θ₂
        = weylAvg P N β₁ β₂ (lift (θ₁ - β₁)) (lift (θ₂ - β₂)) :=
      avgSymb_eq_weylAvg P N β₁ β₂ θ₁ θ₂
    have harith : arithSymb ρ P l₁ l₂ (uScale ρ (smallL l₁ l₂ k₁ k₂)) θ₁ θ₂
        = mZ P (arithQ ρ (max l₁ l₂)) β₁ β₂ :=
      arithSymb_eq_of_spike ρ P l₁ l₂ (uScale ρ (smallL l₁ l₂ k₁ k₂)) hd hβ₁ hβ₂
        hNA₁ hNA₂ hu hξ₁ hξ₂
    simp only [spikeSymb, bumpSymb, meanSpike, havg, harith, M0]
    ring


end

end Work.KMTAreas.A7.Cpy

