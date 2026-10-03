/-
Copyright (c) 2026 The AnnalsChallenge team. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The AnnalsChallenge team
-/
import Submission.Work.Analysis.IonescuWainger.FourierZ

/-!
# The Ionescu–Wainger Fourier projection operators

This file contains the definition of the Ionescu–Wainger (IW) Fourier projection operators
`T^{≤l}_Φ = Π_{≤l,≤k}` of Krause–Mirek–Tao, Appendix A and §5, together with the basic
manipulations of their symbols.

For a finite set `A ⊆ ℝ/ℤ` of arithmetic frequencies and a symbol `Φ : ℝ/ℤ → ℂ` on the
circle, the *IW symbol* is

`iwSymbolSet A Φ ξ = ∑_{α ∈ A} Φ (ξ - α)`,

and the corresponding Fourier multiplier on `ℓ²(ℤ)` is `iwOpSet A Φ`.  The paper's operator
`T^{≤l}_φ = T_{Proj(φ ⊗ 1_{(ℚ/ℤ)_{≤l}})}` is `iwOpSet (iwArithFreqs ρ l) (periodize φ)`, with
the identifications discussed in the docstrings of `periodize` and `iwSymbolSet`.

## Main definitions

* `Work.Analysis.IonescuWainger.realArc` — `ℝ_{≤k} = [-2^k, 2^k]`;
* `Work.Analysis.IonescuWainger.GoodMajorArcs` — the condition `k ≤ -C_ρ 2^{ρl}`;
* `Work.Analysis.IonescuWainger.NonAliasing` — injectivity of `(θ,α) ↦ θ + α` on `ℝ_{≤k} × A`;
* `Work.Analysis.IonescuWainger.periodize` — the periodisation `ℝ → ℝ/ℤ` of `φ`;
* `Work.Analysis.IonescuWainger.iwSymbolSet`, `…iwSymbol`;
* `Work.Analysis.IonescuWainger.iwOpSet`, `…iwOp`.
-/

set_option autoImplicit false
set_option maxHeartbeats 1000000

open scoped BigOperators

namespace Work.Analysis.IonescuWainger

open MeasureTheory

/-- The continuous frequency interval `ℝ_{≤k} = [-2^k, 2^k]`. -/
def realArc (k : ℤ) : Set ℝ := Set.Icc (-(2 : ℝ) ^ k) (2 ^ k)

/-- The pair `(l,k)` has *good major arcs* (with constant `Cρ`) if `k ≤ -Cρ · 2^{ρl}`.
This is the paper's condition `m-small`, with `Cρ = C_ρ` chosen large enough depending on `ρ`. -/
def GoodMajorArcs (ρ Cρ : ℝ) (l : ℕ) (k : ℤ) : Prop :=
  (k : ℝ) ≤ -Cρ * (2 : ℝ) ^ (ρ * (l : ℝ))

/-- A finite set `A ⊆ ℝ/ℤ` of arithmetic frequencies is *non-aliasing* at scale `k` if the
addition map `(θ, α) ↦ θ + α` is injective on `ℝ_{≤k} × A`, i.e. the major arcs
`α + ℝ_{≤k}`, `α ∈ A`, are pairwise disjoint in `ℝ/ℤ`. -/
def NonAliasing (k : ℤ) (A : Finset Circle) : Prop :=
  ∀ α ∈ A, ∀ β ∈ A, ∀ θ ∈ realArc k, ∀ θ' ∈ realArc k,
    α + (θ : Circle) = β + (θ' : Circle) → α = β ∧ θ = θ'

/-- A symbol `Φ` on the circle is supported in the image of `ℝ_{≤k}`. -/
def SupportedInArc (k : ℤ) (Φ : Circle → ℂ) : Prop :=
  ∀ ξ : Circle, Φ ξ ≠ 0 → ∃ θ ∈ realArc k, (θ : Circle) = ξ

/-- The periodisation of `φ : ℝ → ℂ` to the circle: `Φ(ξ) = ∑' k, φ(x + k)`, where `x ∈ [0,1)`
is the canonical representative of `ξ`.  For Schwartz `φ` this is a smooth `1`-periodic function
and it agrees with `φ` itself on the support, when `supp φ ⊆ ℝ_{≤k}` with `2^k < 1/2`. -/
noncomputable def periodize (φ : ℝ → ℂ) : Circle → ℂ :=
  fun ξ => ∑' k : ℤ, φ ((AddCircle.equivIco (1 : ℝ) 0 ξ).val + k)

/-- The Ionescu–Wainger symbol attached to a finite set `A` of arithmetic frequencies:
`ξ ↦ ∑_{α ∈ A} Φ (ξ - α)`. -/
noncomputable def iwSymbolSet (A : Finset Circle) (Φ : Circle → ℂ) : Circle → ℂ :=
  fun ξ => ∑ α ∈ A, Φ (ξ - α)

/-- The Ionescu–Wainger symbol of height `≤ l`: `∑_{α ∈ (ℚ/ℤ)_{≤l}} Φ (ξ - α)`. -/
noncomputable def iwSymbol (ρ : ℝ) (l : ℕ) (Φ : Circle → ℂ) : Circle → ℂ :=
  iwSymbolSet (iwArithFreqs ρ l) Φ

/-- The Fourier multiplier on `ℓ²(ℤ)` with symbol `iwSymbolSet A Φ`. -/
noncomputable def iwOpSet (A : Finset Circle) (Φ : Circle → ℂ)
    (h : MemLp (iwSymbolSet A Φ) ⊤ circleMeasure) : L2Z →L[ℂ] L2Z :=
  multiplierOf (iwSymbolSet A Φ) h

/-- The Ionescu–Wainger Fourier projection-type operator `T^{≤l}_Φ` on `ℓ²(ℤ)`. -/
noncomputable def iwOp (ρ : ℝ) (l : ℕ) (Φ : Circle → ℂ)
    (h : MemLp (iwSymbol ρ l Φ) ⊤ circleMeasure) : L2Z →L[ℂ] L2Z :=
  multiplierOf (iwSymbol ρ l Φ) h

@[simp]
theorem iwSymbolSet_apply (A : Finset Circle) (Φ : Circle → ℂ) (ξ : Circle) :
    iwSymbolSet A Φ ξ = ∑ α ∈ A, Φ (ξ - α) := rfl

theorem iwSymbolSet_add (A : Finset Circle) (Φ₁ Φ₂ : Circle → ℂ) :
    iwSymbolSet A (Φ₁ + Φ₂) = iwSymbolSet A Φ₁ + iwSymbolSet A Φ₂ := by
  funext ξ
  simp only [iwSymbolSet, Pi.add_apply, Finset.sum_add_distrib]

theorem iwSymbolSet_zero (A : Finset Circle) : iwSymbolSet A 0 = 0 := by
  funext ξ
  simp [iwSymbolSet]

theorem iwSymbolSet_const_mul (A : Finset Circle) (c : ℂ) (Φ : Circle → ℂ) :
    iwSymbolSet A (fun ξ => c * Φ ξ) = fun ξ => c * iwSymbolSet A Φ ξ := by
  funext ξ
  simp only [iwSymbolSet, Finset.mul_sum]

/-- If `B ⊆ A`, the symbol over `A` splits as the symbol over `B` plus the symbol over the
complement.  This is the paper's decomposition `T^{≤l}_φ = T^{≤l-1}_φ + T^{l}_φ`. -/
theorem iwSymbolSet_sdiff (A B : Finset Circle) (hBA : B ⊆ A) (Φ : Circle → ℂ) :
    iwSymbolSet A Φ = iwSymbolSet B Φ + iwSymbolSet (A \ B) Φ := by
  funext ξ
  simp only [iwSymbolSet, Pi.add_apply]
  rw [← Finset.sum_sdiff hBA, add_comm]

/-- The symbol of a bounded symbol is bounded by the cardinality times the sup norm. -/
theorem norm_iwSymbolSet_le (A : Finset Circle) {Φ : Circle → ℂ} {C : ℝ} (hC : ∀ ξ, ‖Φ ξ‖ ≤ C) :
    ∀ ξ, ‖iwSymbolSet A Φ ξ‖ ≤ A.card * C := by
  intro ξ
  calc ‖iwSymbolSet A Φ ξ‖ = ‖∑ α ∈ A, Φ (ξ - α)‖ := rfl
    _ ≤ ∑ α ∈ A, ‖Φ (ξ - α)‖ := norm_sum_le _ _
    _ ≤ ∑ _α ∈ A, C := Finset.sum_le_sum fun α _ => hC _
    _ = A.card * C := by simp [Finset.sum_const, nsmul_eq_mul]

end Work.Analysis.IonescuWainger
