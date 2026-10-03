/-
# Auxiliary structural lemmas for the large-scale model estimate (`A7/Large`)

This module records the *elementary Fourier-combinatorial skeleton* of the large-scale
(`§8`) analysis of Krause--Mirek--Tao, *Pointwise ergodic theorems for non-conventional
bilinear polynomial averages*, Annals 195 (2022), for the twisted bilinear multiplier
`Work.KMTAreas.A7.Btwist`.

The twisted bilinear multiplier `Btwist` has the kernel
`K(j₁,j₂) = arithKernel ρ P q l₁ l₂ j₁ j₂ · cw m₁ j₁ · cw m₂ j₂`, and the arithmetic kernel is a
*double Fourier sum* over the arithmetic frequency sets.  The point of this file is the
**factorisation** of that double sum into a single sum over the residues `n` of the arithmetic
averaging variable: with

  `arithChar ρ l y = ∑_{α ∈ (ℚ/ℤ)_{≤l}} e(α y)`

one has

  `arithKernel ρ P q l₁ l₂ j₁ j₂ = q⁻¹ ∑_{n < q} arithChar ρ l₁ (n - j₁) · arithChar ρ l₂ (P(n) - j₂)`.

This is the `ℤ`-form of the tensor factorisation of the twisted multiplier (the paper's `form-1`
/ `form-2`): the kernel is the average over `n` of the product of the two "arithmetic factors"
attached to the two frequency variables.  Equivalently, `Btwist` is the average over the residues
`n` of `q` of the products of the two linear operators

  `A_n^{(i)} g(x) = ∑_j arithChar ρ lᵢ (n - j) · cw mᵢ j · g(x - j)`

applied to the two arguments.
-/
import Mathlib
import Submission.Work.KMTAreas.A7.Large.Defs

set_option autoImplicit false
set_option maxHeartbeats 1000000

namespace Work.KMTAreas.A7

open MeasureTheory Polynomial Finset
open scoped ENNReal NNReal BigOperators
open Work.Analysis.IonescuWainger

noncomputable section

/-- The arithmetic character factor `C(y) = ∑_{α ∈ (ℚ/ℤ)_{≤l}} e(α y)`, the (inverse) Fourier
transform of the arithmetic frequency set `iwArithFreqs ρ l` evaluated at the integer `y`. -/
noncomputable def arithChar (ρ : ℝ) (l : ℕ) (y : ℤ) : ℂ :=
  ∑ α ∈ iwArithFreqs ρ l, fourier (T := 1) y α

/-- Reordering of a triple sum: put the innermost index first. -/
lemma sum_comm_three {α β γ : Type*} (s : Finset α) (t : Finset β)
    (u : Finset γ) (g : α → β → γ → ℂ) :
    (∑ a ∈ s, ∑ b ∈ t, ∑ k ∈ u, g a b k) = (∑ k ∈ u, ∑ a ∈ s, ∑ b ∈ t, g a b k) := by
  rw [show (∑ a ∈ s, ∑ b ∈ t, ∑ k ∈ u, g a b k)
        = (∑ a ∈ s, ∑ k ∈ u, ∑ b ∈ t, g a b k) from
      Finset.sum_congr rfl (fun a _ => Finset.sum_comm)]
  exact Finset.sum_comm

/-- Pull a constant out of a triple sum, simultaneously putting the innermost index first. -/
lemma const_sum_three {α β γ : Type*} (s : Finset α) (t : Finset β) (u : Finset γ) (c : ℂ)
    (g : α → β → γ → ℂ) :
    (∑ a ∈ s, ∑ b ∈ t, c * ∑ k ∈ u, g a b k) = (∑ k ∈ u, ∑ a ∈ s, ∑ b ∈ t, c * g a b k) := by
  rw [show (∑ a ∈ s, ∑ b ∈ t, c * ∑ k ∈ u, g a b k)
        = (∑ a ∈ s, ∑ b ∈ t, ∑ k ∈ u, c * g a b k) from
      Finset.sum_congr rfl (fun a _ => Finset.sum_congr rfl (fun b _ =>
        Finset.mul_sum u (fun k => g a b k) c))]
  exact sum_comm_three s t u (fun a b k => c * g a b k)

/-- **Factorisation of the arithmetic kernel of the twisted bilinear multiplier.**  The `q`-th
arithmetic kernel is the average over the residues `n` of `q` of the products of the two
arithmetic character factors:

  `arithKernel ρ P q l₁ l₂ j₁ j₂ = q⁻¹ ∑_{n < q} C₁(n - j₁) C₂(P(n) - j₂)`.

The proof is the distribution of the finite sums defining `mZ` and the multiplicativity of the
additive characters `fourier`. -/
theorem arithKernel_eq_arithChar (ρ : ℝ) (P : ℤ[X]) (q : ℕ) (l₁ l₂ : ℕ) (j₁ j₂ : ℤ) :
    arithKernel ρ P q l₁ l₂ j₁ j₂
      = (q : ℂ)⁻¹ * ∑ n ∈ Finset.range q,
          arithChar ρ l₁ ((n : ℤ) - j₁) * arithChar ρ l₂ (P.eval (n : ℤ) - j₂) := by
  classical
  unfold arithKernel mZ arithChar
  have hpt : ∀ (α₁ α₂ : Work.Analysis.IonescuWainger.Circle),
      ((↑q)⁻¹ * ∑ n ∈ Finset.range q,
          (fourier (T:=1) (↑n)) α₁ * (fourier (T:=1) (eval (↑n) P)) α₂)
          * (fourier (T:=1) (-j₁)) α₁ * (fourier (T:=1) (-j₂)) α₂
        = (↑q)⁻¹ * ∑ n ∈ Finset.range q,
            (fourier (T:=1) ((↑n) - j₁)) α₁ * (fourier (T:=1) (eval (↑n) P - j₂)) α₂ := by
    intro α₁ α₂
    have hf1 : ∀ n : ℕ, (fourier (T:=1) (↑n : ℤ)) α₁ * (fourier (T:=1) (-j₁)) α₁
        = (fourier (T:=1) ((↑n : ℤ) - j₁)) α₁ := by
      intro n
      rw [show ((n:ℤ) - j₁) = (n:ℤ) + (-j₁) by ring, fourier_add]
    have hf2 : ∀ n : ℕ, (fourier (T:=1) (eval (↑n) P)) α₂ * (fourier (T:=1) (-j₂)) α₂
        = (fourier (T:=1) (eval (↑n) P - j₂)) α₂ := by
      intro n
      rw [show (eval (↑n) P - j₂) = (eval (↑n) P) + (-j₂) by ring, fourier_add]
    rw [Finset.mul_sum, Finset.sum_mul, Finset.sum_mul, Finset.mul_sum]
    refine Finset.sum_congr rfl fun n _ => ?_
    rw [← hf1 n, ← hf2 n]
    ring
  rw [Finset.sum_congr rfl (fun α₁ _ => Finset.sum_congr rfl (fun α₂ _ => hpt α₁ α₂))]
  rw [const_sum_three (iwArithFreqs ρ l₁) (iwArithFreqs ρ l₂) (Finset.range q) ((↑q)⁻¹)
      (fun α₁ α₂ n =>
        (fourier (T:=1) ((↑n:ℤ) - j₁)) α₁ * (fourier (T:=1) (eval (↑n) P - j₂)) α₂)]
  rw [Finset.mul_sum (Finset.range q) (fun n =>
      (∑ α₁ ∈ iwArithFreqs ρ l₁, (fourier (T:=1) ((↑n:ℤ) - j₁)) α₁)
        * (∑ α₂ ∈ iwArithFreqs ρ l₂, (fourier (T:=1) (eval (↑n) P - j₂)) α₂)) ((↑q)⁻¹)]
  refine Finset.sum_congr rfl (fun n _ => ?_)
  rw [Finset.sum_mul_sum (iwArithFreqs ρ l₁) (iwArithFreqs ρ l₂)
      (fun α₁ => (fourier (T:=1) ((↑n:ℤ) - j₁)) α₁)
      (fun α₂ => (fourier (T:=1) (eval (↑n) P - j₂)) α₂)]
  rw [Finset.mul_sum (iwArithFreqs ρ l₁) (fun α₁ => ∑ α₂ ∈ iwArithFreqs ρ l₂,
        (fourier (T:=1) ((↑n:ℤ) - j₁)) α₁ * (fourier (T:=1) (eval (↑n) P - j₂)) α₂) ((↑q)⁻¹)]
  rw [Finset.sum_congr rfl (fun α₁ _ => Finset.mul_sum (iwArithFreqs ρ l₂)
      (fun α₂ => (fourier (T:=1) ((↑n:ℤ) - j₁)) α₁
        * (fourier (T:=1) (eval (↑n) P - j₂)) α₂) ((↑q)⁻¹))]

end

end Work.KMTAreas.A7
