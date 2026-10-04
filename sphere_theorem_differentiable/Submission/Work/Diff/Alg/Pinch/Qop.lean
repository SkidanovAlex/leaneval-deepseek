import Mathlib
import Submission.Diff.Alg
import Submission.Work.Diff.Alg.q2p_defs
import Submission.Work.Diff.Alg.Pinch.Base

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false

/-!
# The operator picture for the Hamilton reaction term `Q`

This module sets up the dictionary between the component array `R : Curv4 n` and the associated
self-adjoint operator `R̃` on the space `ℂ^{n²}` of complex matrices (indexed here by pairs of
elements of `Fin n`), together with the commutator `ad_X` and the operator `T_X = ad_X^* R̃ ad_X`.

It is the first half of the proof of `Work.Diff.Alg.Pinch.inPIC2_Q_pointwise`: the Hamilton term
`Q R` evaluated on a degenerate direction `X = ζ ∧ η` equals

`⟨R̃ X, R̃ X⟩ + tr(T_X R̃)`,

and both summands are nonnegative when `InPIC2 R` and the degenerate direction has vanishing
`R̃`-energy.
-/

namespace Work.Diff.Alg.Pinch

open Finset Submission.Diff.Alg Matrix

variable {n : ℕ}

/-- Entrywise complex conjugation of a pair-indexed vector. -/
def bar (X : Fin n × Fin n → ℂ) : Fin n × Fin n → ℂ := fun p => star (X p)

/-- Transposition of a pair-indexed vector. -/
def swapF (X : Fin n × Fin n → ℂ) : Fin n × Fin n → ℂ := fun p => X (p.2, p.1)

/-- The exterior square `ζ ∧ η` as a pair-indexed vector. -/
def wedgeF (ζ η : Fin n → ℂ) : Fin n × Fin n → ℂ := fun p => ζ p.1 * η p.2 - ζ p.2 * η p.1

/-- The `ℂ`-bilinear form associated with a `4`-index array: `Phi R X Y = ∑ Rᵢⱼₖₗ Xᵢⱼ Yₖₗ`. -/
noncomputable def Phi (R : Curv4 n) (X Y : Fin n × Fin n → ℂ) : ℂ :=
  ∑ p, ∑ q, (R p.1 p.2 q.1 q.2 : ℂ) * X p * Y q

/-- `R` viewed as an operator on the space of pair-indexed vectors. -/
noncomputable def Rm (R : Curv4 n) : Matrix (Fin n × Fin n) (Fin n × Fin n) ℂ :=
  fun p q => (R p.1 p.2 q.1 q.2 : ℂ)

/-- The operator `R̃` applied to a vector. -/
noncomputable def Rop (R : Curv4 n) (X : Fin n × Fin n → ℂ) : Fin n × Fin n → ℂ := Matrix.mulVec (Rm R) X

/-- The commutator `Z ↦ X Z - Z X`, on pair-indexed vectors. -/
noncomputable def adF (X Z : Fin n × Fin n → ℂ) : Fin n × Fin n → ℂ :=
  fun p => (∑ k : Fin n, X (p.1, k) * Z (k, p.2)) - ∑ k : Fin n, Z (p.1, k) * X (k, p.2)

/-- The matrix of the linear map `adF X`. -/
noncomputable def adMat (X : Fin n × Fin n → ℂ) : Matrix (Fin n × Fin n) (Fin n × Fin n) ℂ :=
  fun p q => X (p.1, q.1) * (if p.2 = q.2 then (1 : ℂ) else 0)
    - (if p.1 = q.1 then (1 : ℂ) else 0) * X (q.2, p.2)

/-- The operator `T_X = ad_X^* R̃ ad_X`. -/
noncomputable def Tmat (R : Curv4 n) (X : Fin n × Fin n → ℂ) :
    Matrix (Fin n × Fin n) (Fin n × Fin n) ℂ :=
  (adMat X)ᴴ * Rm R * adMat X

/-- The "operator square" part of Hamilton's term: `Q₁(R)ᵢⱼₖₗ = ∑ₚq Rᵢⱼₚq Rₖₗₚq`. -/
noncomputable def Q1 (R : Curv4 n) : Curv4 n :=
  fun i j k l => ∑ p : Fin n, ∑ q : Fin n, R i j p q * R k l p q

/-- The "Lie algebra square" part of Hamilton's term
`Q₂(R)ᵢⱼₖₗ = ∑ₚq (2 Rᵢₚₖq Rⱼₚₗq - 2 Rᵢₚₗq Rⱼₚₖq)`; indeed `Q R = Q₁ R + Q₂ R`. -/
noncomputable def Q2 (R : Curv4 n) : Curv4 n :=
  fun i j k l => ∑ p : Fin n, ∑ q : Fin n,
    (2 * R i p k q * R j p l q - 2 * R i p l q * R j p k q)

/-- `Q = Q₁ + Q₂` on the nose. -/
theorem Q_eq_Q1_add_Q2 (R : Curv4 n) : Q R = Q1 R + Q2 R := by
  funext i j k l
  simp only [Q, Q1, Q2, Pi.add_apply]
  rw [← Finset.sum_add_distrib]
  apply Finset.sum_congr rfl; intro p _
  rw [← Finset.sum_add_distrib]
  apply Finset.sum_congr rfl; intro q _
  ring

/-- `Phi` is additive in the `4`-index array. -/
theorem Phi_add (R S : Curv4 n) (X Y : Fin n × Fin n → ℂ) :
    Phi (R + S) X Y = Phi R X Y + Phi S X Y := by
  simp only [Phi, Pi.add_apply]
  push_cast
  simp only [add_mul, Finset.sum_add_distrib]


theorem star_ofReal' (r : ℝ) : star ((r : ℂ)) = (r : ℂ) := by simp

/-! ## Elementary simplifications -/

@[simp] theorem bar_apply (X : Fin n × Fin n → ℂ) (p : Fin n × Fin n) : bar X p = star (X p) := rfl

@[simp] theorem bar_bar (X : Fin n × Fin n → ℂ) : bar (bar X) = X := by
  funext p; simp [bar]

theorem bar_add (X Y : Fin n × Fin n → ℂ) : bar (X + Y) = bar X + bar Y := by
  funext p; simp [bar]

theorem bar_neg (X : Fin n × Fin n → ℂ) : bar (-X) = - bar X := by
  funext p; simp [bar]

theorem bar_sub (X Y : Fin n × Fin n → ℂ) : bar (X - Y) = bar X - bar Y := by
  funext p; simp [bar]

theorem bar_smul (c : ℂ) (X : Fin n × Fin n → ℂ) : bar (c • X) = star c • bar X := by
  funext p; simp [bar]

theorem swapF_bar (X : Fin n × Fin n → ℂ) : swapF (bar X) = bar (swapF X) := by
  funext p; simp [swapF, bar]

theorem adF_mulVec (X Z : Fin n × Fin n → ℂ) : Matrix.mulVec (adMat X) Z = adF X Z := by
  funext p
  rw [Matrix.mulVec]
  simp only [dotProduct, adF, adMat]
  rw [Fintype.sum_prod_type]
  simp only [sub_mul, Finset.sum_sub_distrib]
  congr 1
  · apply Finset.sum_congr rfl; intro x _
    rw [Finset.sum_eq_single p.2]
    · simp
    · intro y _ hy
      rw [if_neg (fun hc => hy hc.symm)]
      ring
    · intro h; exact absurd (Finset.mem_univ p.2) h
  · rw [Finset.sum_eq_single p.1]
    · apply Finset.sum_congr rfl; intro y _
      simp [mul_comm]
    · intro x _ hx
      apply Finset.sum_eq_zero; intro y _
      rw [if_neg (fun hc => hx hc.symm)]
      ring
    · intro h; exact absurd (Finset.mem_univ p.1) h

theorem Rm_mulVec (R : Curv4 n) (X : Fin n × Fin n → ℂ) : Matrix.mulVec (Rm R) X = Rop R X := rfl

end Work.Diff.Alg.Pinch
