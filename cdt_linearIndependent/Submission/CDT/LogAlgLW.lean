import Mathlib
import Submission.CDT.LogAlgIndependent
import Submission.CDT.LogMultiplicativeField
import Submission.CDT.RatFuncConstants
import Submission.CDT.LogRelation
import Submission.CDT.RatFuncDifferential

/-!
# Function-field Lindemann–Weierstrass: algebraic independence of logarithms

This module combines two developments:

* `Submission.CDT.LogAlgIndependent` — the Ostrowski–Kolchin theorem: for a differential field
  extension `F ⊆ L` with the constants of `L` inside `F`, the elements `v` of `F(u₁, …, uₙ)` whose
  derivative lies in `F` are exactly `F + C_F·u₁ + ⋯ + C_F·uₙ`, and consequently the `uᵢ` are
  algebraically independent over `F` as soon as no nontrivial `C_F`-linear combination of them lies
  in `F`;
* `Submission.CDT.LogRelation` / `LogMultiplicativeField` — the *dependence* form of the
  function-field Lindemann–Weierstrass theorem: a nonzero `K`-linear relation
  `Σᵢ cᵢ·(dRat fᵢ)/fᵢ = dRat h` among the logarithmic derivatives of the nonzero `fᵢ ∈ K(X)`
  forces a nontrivial multiplicative relation `∏ᵢ fᵢ^{mᵢ} ∈ K`.

The main result, `algebraicIndependent_log_of_multiplicativeIndependent`, is the classical
Lindemann–Weierstrass statement for function fields: if `f₁, …, fₙ ∈ K(X)` are multiplicatively
independent (no nontrivial product with constant value), and `ℓ₁, …, ℓₙ` lie in a differential field
extension of `K(X)` with `ℓᵢ′ = (dRat fᵢ)/fᵢ` (so `ℓᵢ` plays the role of `log fᵢ`), then
`ℓ₁, …, ℓₙ` are algebraically independent over `K(X)`.
-/

noncomputable section

namespace Submission.CDT

open Polynomial

variable {K L : Type*} [Field K] [CharZero K] [Field L] [Algebra (RatFunc K) L]
  [Differential L] [DifferentialAlgebra (RatFunc K) L]

/-- **Function-field Lindemann–Weierstrass: algebraic independence of logarithms.** -/
theorem algebraicIndependent_log_of_multiplicativeIndependent (n : ℕ)
    [IsAlgClosed K] [Differential.ContainConstants (RatFunc K) L]
    (f : Fin n → RatFunc K) (hf : ∀ i, f i ≠ 0)
    (hindep : ∀ m : Fin n → ℤ, m ≠ 0 → ∀ C : K, C ≠ 0 →
      (∏ i, f i ^ (m i)) ≠ algebraMap K (RatFunc K) C)
    (u : Fin n → L)
    (hu : ∀ i, Differential.deriv (u i) = algebraMap (RatFunc K) L (dRat (f i) / f i)) :
    AlgebraicIndependent (RatFunc K) u := by
  haveI : CharZero (RatFunc K) := Algebra.charZero_of_charZero K (RatFunc K)
  refine algebraicIndependent_of_linearIndependent (F := RatFunc K) (L := L) n u ?_ ?_
  · intro i
    exact ⟨dRat (f i) / f i, hu i⟩
  · intro c r hc hsum
    have hcK : ∀ i, ∃ α : K, c i = algebraMap K (RatFunc K) α := fun i =>
      exists_const_of_dRat_eq_zero (by simpa only [deriv_ratFunc_eq_dRat] using hc i)
    choose α hα using hcK
    have hczero : ∀ i, α i = 0 := by
      by_contra hne
      have hαne : α ≠ 0 := fun h => hne (fun i => by rw [h]; rfl)
      have hsum' : ∑ i, algebraMap (RatFunc K) L (algebraMap K (RatFunc K) (α i)) * u i
          = algebraMap (RatFunc K) L r := by
        rw [← hsum]
        exact Finset.sum_congr rfl (fun i _ => by rw [hα i])
      have hrel := sum_dRat_div_eq_of_sum_log_eq (fun r => rfl) f α u hu r hsum'
      obtain ⟨m, hm, C, hC, hprod⟩ :=
        exists_int_prod_zpow_const_of_sum_dRat_div_field f hf α hαne ⟨r, hrel⟩
      exact hindep m hm C hC hprod
    intro i
    rw [hα i, hczero i, map_zero]
end Submission.CDT
