/-
Copyright (c) 2026 The AnnalsChallenge team. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The AnnalsChallenge team
-/
import Mathlib
import Submission.Work.Analysis.IonescuWainger.Symbol

/-!
# Multiplicativity of the Ionescu–Wainger symbol over a non-aliasing frequency set

The Ionescu–Wainger symbol attached to a finite set `A` of arithmetic frequencies is
`iwSymbolSet A Φ ξ = ∑_{α ∈ A} Φ (ξ - α)`.  Its product over two symbols `Φ₁`, `Φ₂` supported
in frequency arcs of *different* scales, `Φ₁` in `ℝ_{≤k}` and `Φ₂` in `ℝ_{≤k'}` with `k ≤ k'`,
distributes, provided `A` is non-aliasing at the larger scale `k'`:

`iwSymbolSet A (Φ₁ * Φ₂) = iwSymbolSet A Φ₁ * iwSymbolSet A Φ₂`.

The point is that the off-diagonal terms of the product vanish.  Evaluating at `ξ` and expanding,

`(∑_{α ∈ A} Φ₁ (ξ - α)) (∑_{β ∈ A} Φ₂ (ξ - β)) = ∑_{α ∈ A} ∑_{β ∈ A} Φ₁ (ξ - α) Φ₂ (ξ - β)`,

and a term with `α ≠ β` is zero: if both `Φ₁ (ξ - α) ≠ 0` and `Φ₂ (ξ - β) ≠ 0`, then
`ξ - α ∈ ℝ_{≤k}` and `ξ - β ∈ ℝ_{≤k'}`, i.e. there are `θ ∈ ℝ_{≤k}`, `θ' ∈ ℝ_{≤k'}` with
`α + θ = ξ = β + θ'`.  Since `k ≤ k'` we may view both `θ` and `θ'` in the larger arc `ℝ_{≤k'}`,
and non-aliasing at scale `k'` forces `α = β`.  Hence only the diagonal `α = β` survives and the
two expressions agree.

This is the multiplicativity used when the paper composes two IW Fourier projections whose
frequencies live at the same height.

## Main result

* `Work.Analysis.IonescuWainger.iwSymbolSet_mul`
-/

set_option autoImplicit false
-- the hypothesis `hA : NonAliasing k A` is genuinely unused: only the non-aliasing at the
-- larger scale `k'`, together with `k ≤ k'`, enters the argument.
set_option linter.unusedVariables false
set_option maxHeartbeats 1000000

open scoped BigOperators

namespace Work.Analysis.IonescuWainger

open MeasureTheory

/-- The frequency arcs `ℝ_{≤k} = [-2^k, 2^k]` increase with `k`. -/
theorem realArc_mono {k k' : ℤ} (h : k ≤ k') : realArc k ⊆ realArc k' := by
  intro θ hθ
  simp only [realArc, Set.mem_Icc] at hθ ⊢
  have hpow : (2 : ℝ) ^ k ≤ (2 : ℝ) ^ k' := zpow_le_zpow_right₀ (by norm_num) h
  exact ⟨by linarith, by linarith⟩

/-- If every off-diagonal product `f a * g b` (`a ≠ b`, `a, b ∈ A`) vanishes, then the product of
the two sums collapses to the diagonal sum `∑_{a ∈ A} f a * g a`. -/
private theorem sum_mul_sum_eq_sum_diag {ι : Type*} (A : Finset ι) (f g : ι → ℂ)
    (h : ∀ a ∈ A, ∀ b ∈ A, f a * g b ≠ 0 → a = b) :
    (∑ a ∈ A, f a) * (∑ b ∈ A, g b) = ∑ a ∈ A, f a * g a := by
  classical
  rw [Finset.sum_mul_sum]
  refine Finset.sum_congr rfl fun a ha => ?_
  by_cases hfa : f a = 0
  · simp [hfa]
  · have hterm : ∀ b ∈ A, f a * g b = if a = b then f a * g b else 0 := by
      intro b hb
      by_cases hab : a = b
      · rw [if_pos hab]
      · have hz : f a * g b = 0 := by
          by_contra hne
          exact hab (h a ha b hb hne)
        rw [if_neg hab, hz]
    calc ∑ b ∈ A, f a * g b
        = ∑ b ∈ A, (if a = b then f a * g b else 0) := Finset.sum_congr rfl hterm
      _ = (if a ∈ A then f a * g a else 0) := Finset.sum_ite_eq A a (fun b => f a * g b)
      _ = f a * g a := by simp [ha]

/-- **Multiplicativity of the IW symbol over a non-aliasing frequency set.**  If `Φ₁` is
supported in the arc `ℝ_{≤k}`, `Φ₂` in the arc `ℝ_{≤k'}` with `k ≤ k'`, and the finite set `A` of
arithmetic frequencies is non-aliasing at scale `k'`, then the symbol of the product is the
product of the symbols. -/
theorem iwSymbolSet_mul {k k' : ℤ} (hkk : k ≤ k') {A : Finset Circle}
    (hA : NonAliasing k A) (hA' : NonAliasing k' A) {Φ₁ Φ₂ : Circle → ℂ}
    (h₁ : SupportedInArc k Φ₁) (h₂ : SupportedInArc k' Φ₂) :
    iwSymbolSet A (Φ₁ * Φ₂) = iwSymbolSet A Φ₁ * iwSymbolSet A Φ₂ := by
  have hmono : realArc k ⊆ realArc k' := realArc_mono hkk
  funext ξ
  simp only [iwSymbolSet_apply, Pi.mul_apply]
  have hkey : ∀ α ∈ A, ∀ β ∈ A, Φ₁ (ξ - α) * Φ₂ (ξ - β) ≠ 0 → α = β := by
    intro α hα β hβ hne
    obtain ⟨h₁ne, h₂ne⟩ := mul_ne_zero_iff.mp hne
    -- `ξ - α` lies in the arc of scale `k`
    obtain ⟨θ, hθ, hθξ⟩ := h₁ (ξ - α) h₁ne
    -- `ξ - β` lies in the arc of scale `k'`
    obtain ⟨θ', hθ', hθ'ξ⟩ := h₂ (ξ - β) h₂ne
    have hαθ : α + (θ : Circle) = ξ := by rw [hθξ]; abel
    have hβθ' : β + (θ' : Circle) = ξ := by rw [hθ'ξ]; abel
    -- both arcs are contained in `ℝ_{≤k'}`, where `A` is non-aliasing
    exact (hA' α hα β hβ θ (hmono hθ) θ' hθ' (hαθ.trans hβθ'.symm)).1
  exact (sum_mul_sum_eq_sum_diag A (fun α => Φ₁ (ξ - α)) (fun β => Φ₂ (ξ - β)) hkey).symm

end Work.Analysis.IonescuWainger
