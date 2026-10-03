/-
# The model side of the §6 collapse: the `t`-integral of the two modulated pieces

This module proves the analytic/algebraic core of step 2 of the collapse identity
`Σ₁ − Σ₂ = ∑_α Φ₁(θ₁-α₁)Φ₂(θ₂-α₂)·M0(α, ξ)` of `NOTES_A7_smallKernelMass_le.md` §2:

    ∫_{1/2}^{1} periodize (varphiNt N k₁ t) γ₁ · periodize (varphitildeNt P d N k₂ t) γ₂ dt
      = varphiN N k₁ (lift γ₁) · varphitildeN d N k₂ (lift γ₂) · mTilde P N (lift γ₁) (lift γ₂),

for narrow bumps (`supp φ ⊆ [-w, w]`, `w < 1/2`).  The proof is the `t`-integral of the product
of the two periodised modulated bumps: each periodisation is the bump evaluated at the canonical
lift (`periodize_mul_ee_eq_lift`, `A7/liftCollapse.lean`), the two oscillations combine by
`ee (a) · ee (b) = ee (a + b)`, and the resulting integral is `mTilde` by definition.

It depends only on `A7/symbolDefs.lean`, `A7/liftCollapse.lean` and the bump definitions of
`A7/Large/Defs.lean` (not on `A7/SmallModApprox.lean`).
-/
import Mathlib
import Submission.Work.KMTAreas.A7.symbolDefs
import Submission.Work.KMTAreas.A7.liftCollapse
import Submission.Work.KMTAreas.A7.varphiNt_support_le

set_option autoImplicit false
set_option maxHeartbeats 1000000

namespace Work.KMTAreas.A7

noncomputable section

open MeasureTheory Polynomial Finset
open scoped ENNReal NNReal BigOperators
open Work.Analysis.IonescuWainger

/-- `ee (a + b) = ee a * ee b`. -/
theorem ee_add' (a b : ℝ) : ee (a + b) = ee a * ee b := by
  rw [ee, ee, ee, ← Complex.exp_add]
  congr 1
  push_cast
  ring

/-- **The `t`-integral of the product of the two periodised modulated bumps.**  For narrow bumps
(`supp ⊆ [-w,w]`, `w < 1/2`) the `t`-integral of the product is the product of the bumps, times
`mTilde` — because each periodisation collapses to the bump at the canonical lift and the two
oscillations combine. -/
theorem integral_periodize_varphiNt_mul (N k₁ k₂ : ℕ) (P : Polynomial ℤ)
    {w₁ w₂ : ℝ} (hw₁ : w₁ < 1/2) (hw₂ : w₂ < 1/2)
    (h₁ : ∀ x : ℝ, varphiN N k₁ x ≠ 0 → |x| ≤ w₁)
    (h₂ : ∀ x : ℝ, varphitildeN P.natDegree N k₂ x ≠ 0 → |x| ≤ w₂)
    (γ₁ γ₂ : AddCircle (1 : ℝ)) :
    (∫ t in (1/2 : ℝ)..1,
        periodize (varphiNt N k₁ t) γ₁ * periodize (varphitildeNt P P.natDegree N k₂ t) γ₂)
      = varphiN N k₁ (lift γ₁) * varphitildeN P.natDegree N k₂ (lift γ₂)
        * mTilde P N (lift γ₁) (lift γ₂) := by
  -- the pointwise value of the integrand
  have hkey : ∀ t : ℝ,
      periodize (varphiNt N k₁ t) γ₁ * periodize (varphitildeNt P P.natDegree N k₂ t) γ₂
        = (varphiN N k₁ (lift γ₁) * varphitildeN P.natDegree N k₂ (lift γ₂))
          * ee ((N : ℝ) * t * lift γ₁ + PevalR P ((N : ℝ) * t) * lift γ₂) := by
    intro t
    have h1 : periodize (varphiNt N k₁ t) γ₁
        = varphiN N k₁ (lift γ₁) * ee ((N : ℝ) * t * lift γ₁) := by
      change periodize (fun ξ : ℝ => varphiN N k₁ ξ * ee ((N : ℝ) * t * ξ)) γ₁
          = varphiN N k₁ (lift γ₁) * ee ((N : ℝ) * t * lift γ₁)
      exact periodize_mul_ee_eq_lift (φ := varphiN N k₁) (c := (N : ℝ) * t) hw₁ h₁ γ₁
    have h2 : periodize (varphitildeNt P P.natDegree N k₂ t) γ₂
        = varphitildeN P.natDegree N k₂ (lift γ₂) * ee (PevalR P ((N : ℝ) * t) * lift γ₂) := by
      change periodize
          (fun ξ : ℝ => varphitildeN P.natDegree N k₂ ξ * ee (PevalR P ((N : ℝ) * t) * ξ)) γ₂
          = varphitildeN P.natDegree N k₂ (lift γ₂) * ee (PevalR P ((N : ℝ) * t) * lift γ₂)
      exact periodize_mul_ee_eq_lift (φ := varphitildeN P.natDegree N k₂)
        (c := PevalR P ((N : ℝ) * t)) hw₂ h₂ γ₂
    rw [h1, h2, ee_add']
    ring
  rw [intervalIntegral.integral_congr (fun t _ => hkey t)]
  rw [intervalIntegral.integral_const_mul]
  congr 1
  rw [mTilde]
  refine intervalIntegral.integral_congr (fun t _ => ?_)
  congr 1
  ring

/-- Non-aliasing restricts to subsets. -/
theorem NonAliasing_of_subset {k : ℤ}
    {A B : Finset Work.Analysis.IonescuWainger.Circle}
    (h : NonAliasing k B) (hAB : A ⊆ B) : NonAliasing k A := by
  intro α hα β hβ θ hθ θ' hθ' hEq
  exact h α (hAB hα) β (hAB hβ) θ hθ θ' hθ' hEq

/-- The exact-height frequencies at level `l` sit inside `(ℚ/ℤ)_{≤L}` for `L ≥ l`. -/
theorem diffFreqs_subset_iwArithFreqs_le {ρ : ℝ} (hρ : 0 < ρ) (hρ1 : ρ ≤ 1) {l L : ℕ}
    (hl : l ≤ L) : diffFreqs ρ l ⊆ iwArithFreqs ρ L := by
  rw [diffFreqs]
  split
  · exact iwArithFreqs_mono hρ hρ1 (Nat.zero_le L)
  · exact Finset.Subset.trans Finset.sdiff_subset (iwArithFreqs_mono hρ hρ1 hl)

/-- **The collapse of the arithmetic symbol at a spike.**  On the spike of `β = (β₁,β₂)` — i.e.
where the two auxiliary windows `mStarF u`, `mStargF d u` are supported at scale `k` — the weighted
sum `arithSymb` collapses to the single term `β`, provided `(ℚ/ℤ)_{≤ max(l₁,l₂)}` is non-aliasing at
scale `k`. -/
theorem arithSymb_eq_of_nonAliasing (ρ : ℝ) (hρ : 0 < ρ) (hρ1 : ρ ≤ 1)
    (P : Polynomial ℤ) (l₁ l₂ u : ℕ) {k : ℤ}
    (hNA : NonAliasing k (iwArithFreqs ρ (max l₁ l₂)))
    (hΦ₁ : SupportedInArc k (periodize (mStarF u)))
    (hΦ₂ : SupportedInArc k (periodize (mStargF P.natDegree u)))
    {β₁ : Work.Analysis.IonescuWainger.Circle} (hβ₁ : β₁ ∈ diffFreqs ρ l₁)
    {β₂ : Work.Analysis.IonescuWainger.Circle} (hβ₂ : β₂ ∈ diffFreqs ρ l₂)
    {θ₁ θ₂ : Work.Analysis.IonescuWainger.Circle}
    (hθ₁ : ∃ y ∈ realArc k, ((y : ℝ) : Work.Analysis.IonescuWainger.Circle) = θ₁ - β₁)
    (hθ₂ : ∃ y ∈ realArc k, ((y : ℝ) : Work.Analysis.IonescuWainger.Circle) = θ₂ - β₂) :
    arithSymb ρ P l₁ l₂ u θ₁ θ₂
      = mZ P (arithQ ρ (max l₁ l₂)) β₁ β₂
        * periodize (mStarF u) (θ₁ - β₁) * periodize (mStargF P.natDegree u) (θ₂ - β₂) := by
  have hNA₁ : NonAliasing k (diffFreqs ρ l₁) :=
    NonAliasing_of_subset hNA (diffFreqs_subset_iwArithFreqs_le hρ hρ1 (le_max_left _ _))
  have hNA₂ : NonAliasing k (diffFreqs ρ l₂) :=
    NonAliasing_of_subset hNA (diffFreqs_subset_iwArithFreqs_le hρ hρ1 (le_max_right _ _))
  unfold arithSymb
  have hstep : ∀ α₁ : Work.Analysis.IonescuWainger.Circle,
      (∑ α₂ ∈ diffFreqs ρ l₂,
          mZ P (arithQ ρ (max l₁ l₂)) α₁ α₂
            * periodize (mStarF u) (θ₁ - α₁) * periodize (mStargF P.natDegree u) (θ₂ - α₂))
        = (∑ α₂ ∈ diffFreqs ρ l₂,
            mZ P (arithQ ρ (max l₁ l₂)) α₁ α₂
              * periodize (mStargF P.natDegree u) (θ₂ - α₂))
          * periodize (mStarF u) (θ₁ - α₁) := by
    intro α₁
    rw [Finset.sum_mul]
    exact Finset.sum_congr rfl fun α₂ _ => by ring
  rw [Finset.sum_congr rfl fun α₁ _ => hstep α₁]
  rw [sum_weighted_eq_of_nonAliasing hNA₁ hΦ₁ hβ₁ hθ₁]
  rw [sum_weighted_eq_of_nonAliasing hNA₂ hΦ₂ hβ₂ hθ₂]
  ring

/-- **The piece-spike collapse of the concrete side**: on the spike of `β` the exact-height
Ionescu--Wainger symbol of the piece `varphiN N k` is just the bump evaluated at the canonical lift
of `θ - β`. -/
theorem iwSymbolSet_varphiN_eq_of_nonAliasing (ρ : ℝ) (N k l : ℕ) {kb : ℤ}
    {w : ℝ} (hw : w < 1/2) (hφ : ∀ x : ℝ, varphiN N k x ≠ 0 → |x| ≤ w)
    (hNA : NonAliasing kb (diffFreqs ρ l))
    (hsupp : SupportedInArc kb (periodize (varphiN N k)))
    {β : Work.Analysis.IonescuWainger.Circle} (hβ : β ∈ diffFreqs ρ l)
    {θ : Work.Analysis.IonescuWainger.Circle}
    (hθ : ∃ y ∈ realArc kb, ((y : ℝ) : Work.Analysis.IonescuWainger.Circle) = θ - β) :
    iwSymbolSet (diffFreqs ρ l) (periodize (varphiN N k)) θ
      = varphiN N k (lift (θ - β)) := by
  rw [iwSymbolSet_eq_of_nonAliasing hNA hsupp hβ hθ]
  exact periodize_eq_lift hw hφ (θ - β)

/-- The same for the `d`-rescaled piece `varphitildeN d N k`. -/
theorem iwSymbolSet_varphitildeN_eq_of_nonAliasing (ρ : ℝ) (P : Polynomial ℤ) (N k l : ℕ) {kb : ℤ}
    {w : ℝ} (hw : w < 1/2)
    (hφ : ∀ x : ℝ, varphitildeN P.natDegree N k x ≠ 0 → |x| ≤ w)
    (hNA : NonAliasing kb (diffFreqs ρ l))
    (hsupp : SupportedInArc kb (periodize (varphitildeN P.natDegree N k)))
    {β : Work.Analysis.IonescuWainger.Circle} (hβ : β ∈ diffFreqs ρ l)
    {θ : Work.Analysis.IonescuWainger.Circle}
    (hθ : ∃ y ∈ realArc kb, ((y : ℝ) : Work.Analysis.IonescuWainger.Circle) = θ - β) :
    iwSymbolSet (diffFreqs ρ l) (periodize (varphitildeN P.natDegree N k)) θ
      = varphitildeN P.natDegree N k (lift (θ - β)) := by
  rw [iwSymbolSet_eq_of_nonAliasing hNA hsupp hβ hθ]
  exact periodize_eq_lift hw hφ (θ - β)

end

end Work.KMTAreas.A7
