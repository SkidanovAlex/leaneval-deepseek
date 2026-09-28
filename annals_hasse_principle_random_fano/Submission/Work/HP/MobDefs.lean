import Mathlib
import Submission.Work.HP.MMDefs

/-!
# The scaling map `ℓ • a` on integer vectors, for the Möbius inversion in `𝓢*_k`

This file provides the elementary definition `scaleVec ℓ a = fun i => (ℓ : ℤ) * a i`
used to state the Möbius inversion
`𝓢*_k(Λ; R) = ∑_{ℓ} μ(ℓ)/ℓ^k 𝓢_k(ℓ^{-1}Λ; ℓ^{-1}R)`
of Browning--Le Boudec--Sawin (Lemma D loc / Lemma D mix), and its basic API.
-/

set_option autoImplicit false
noncomputable section

namespace Work.HP

/-- The vector `ℓ • a` for `a : ι → ℤ` and `ℓ : ℕ`, written coordinatewise as
`fun i => (ℓ : ℤ) * a i`. -/
def scaleVec {ι : Type*} (ℓ : ℕ) (a : ι → ℤ) : ι → ℤ := fun i => (ℓ : ℤ) * a i

@[simp] lemma scaleVec_one {ι : Type*} (a : ι → ℤ) : scaleVec 1 a = a := by
  funext i; simp [scaleVec]

@[simp] lemma scaleVec_zero {ι : Type*} (a : ι → ℤ) : scaleVec 0 a = 0 := by
  funext i; simp [scaleVec]

lemma scaleVec_eq_nsmul {ι : Type*} (ℓ : ℕ) (a : ι → ℤ) : scaleVec ℓ a = ℓ • a := by
  funext i; simp [scaleVec, nsmul_eq_mul]

end Work.HP
