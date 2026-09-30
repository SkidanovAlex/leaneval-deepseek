import Mathlib

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false

/-! # Framework for the ray Hilbert function (Baker–Wüstholz multiplicity block)

This file sets up the two ingredients of the proof of `Work.BW.rayHilb_poly`:

* the combinatorial operators `Δᵢ`, `Sᵢ` (mutually inverse) on functions `(Fin m → ℕ) → ℚ`,
  their iterates, and the extraction formula `[x^d] Q(x)/(1-x)ⁿ = ∑_a Q_a ∏ᵢ C(dᵢ-aᵢ+nᵢ-1, nᵢ-1)`;
* the multigraded pieces of `MvPolynomial (Fin s) ℂ` with respect to a weight function
  `w : Fin s → Fin m` (variable `j` has weight `e_{w j}`), the graded pieces of ideals, and the
  Hilbert function `hfun w I J d = dim (J/I)_d` of the subquotient `J/I`.
-/

namespace Work.BW

namespace RayH

open MvPolynomial

variable {m : ℕ}

/-! ## Combinatorial operators on functions `(Fin m → ℕ) → ℚ` -/

/-- The shift `T i`: `(T i f) d = f (d - eᵢ)`, and `0` when the `i`-th coordinate of `d` is `0`. -/
def T (i : Fin m) (f : (Fin m → ℕ) → ℚ) : (Fin m → ℕ) → ℚ :=
  fun d => if d i = 0 then 0 else f (Function.update d i (d i - 1))

/-- The difference operator `Δ i = 1 - T i`. -/
def del (i : Fin m) (f : (Fin m → ℕ) → ℚ) : (Fin m → ℕ) → ℚ :=
  fun d => f d - T i f d

/-- The summation operator `S i`, inverse to `Δ i`: `(S i g) d = ∑_{k=0}^{d i} g (d - k eᵢ)`. -/
def Sop (i : Fin m) (g : (Fin m → ℕ) → ℚ) : (Fin m → ℕ) → ℚ :=
  fun d => ∑ k ∈ Finset.range (d i + 1), g (Function.update d i (d i - k))

/-- The Kronecker delta at `a`. -/
def delt (a : Fin m → ℕ) : (Fin m → ℕ) → ℚ := fun d => if d = a then 1 else 0

/-- `Ψ n k` is the coefficient of `x^k` in `(1-x)^{-n}`, with the convention `Ψ 0 k = [k = 0]`. -/
def Psi (n k : ℕ) : ℚ :=
  if n = 0 then (if k = 0 then 1 else 0) else ((k + n - 1).choose (n - 1) : ℚ)

/-- A function `(Fin m → ℕ) → ℚ` with finite support. -/
def FinSupp (f : (Fin m → ℕ) → ℚ) : Prop := (Function.support f).Finite

/-- `Sop i` as a `ℚ`-linear endomorphism. -/
noncomputable def SopE (i : Fin m) : Module.End ℚ ((Fin m → ℕ) → ℚ) where
  toFun := Sop i
  map_add' f g := by
    funext d
    simp only [Sop, Pi.add_apply, Finset.sum_add_distrib]
  map_smul' c f := by
    funext d
    simp only [Sop, Pi.smul_apply]
    rw [Finset.smul_sum]
    exact Finset.sum_congr rfl fun k _ => by simp [smul_eq_mul]

/-- `T i` as a `ℚ`-linear endomorphism. -/
noncomputable def TE (i : Fin m) : Module.End ℚ ((Fin m → ℕ) → ℚ) where
  toFun := T i
  map_add' f g := by
    funext d
    simp only [T, Pi.add_apply]
    split <;> simp
  map_smul' c f := by
    funext d
    simp only [T, Pi.smul_apply, smul_eq_mul]
    split <;> · simp only [RingHom.id_apply]; try ring

/-- `del i` as a `ℚ`-linear endomorphism. -/
noncomputable def delE (i : Fin m) : Module.End ℚ ((Fin m → ℕ) → ℚ) := 1 - TE i

/-- Iterated operator `∏_{i ∈ l} (Sop i)^{n i}`. -/
noncomputable def itS (n : Fin m → ℕ) (l : List (Fin m)) :
    Module.End ℚ ((Fin m → ℕ) → ℚ) :=
  l.foldr (fun i h => (SopE i) ^ (n i) * h) 1

/-- Iterated operator `∏_{i ∈ l} (del i)^{n i}`. -/
noncomputable def itD (n : Fin m → ℕ) (l : List (Fin m)) :
    Module.End ℚ ((Fin m → ℕ) → ℚ) :=
  l.foldr (fun i h => (delE i) ^ (n i) * h) 1

end RayH

/-! ## Multigraded pieces -/

namespace RayH

open MvPolynomial

variable {m s : ℕ}

attribute [instance] MvPolynomial.weightedGradedAlgebra

/-- The weight of the variable `j : Fin s` is the unit vector `e_{w j}` of `ℤ^m`. -/
noncomputable def wt (w : Fin s → Fin m) : Fin s → (Fin m → ℤ) := fun j => Pi.single (w j) 1

/-- The multigraded piece of degree `d` of the polynomial ring `ℂ[X : Fin s]`. -/
noncomputable def Pc (w : Fin s → Fin m) (d : Fin m → ℤ) :
    Submodule ℂ (MvPolynomial (Fin s) ℂ) :=
  weightedHomogeneousSubmodule ℂ (wt w) d

/-- The degree-`d` piece of an ideal `I`. -/
noncomputable def Pci (w : Fin s → Fin m) (I : Ideal (MvPolynomial (Fin s) ℂ))
    (d : Fin m → ℤ) : Submodule ℂ (MvPolynomial (Fin s) ℂ) :=
  I.restrictScalars ℂ ⊓ Pc w d

/-- Dimension of a `ℂ`-subspace of `ℂ[X : Fin s]`. -/
noncomputable def fr {s : ℕ} (X : Submodule ℂ (MvPolynomial (Fin s) ℂ)) : ℕ :=
  Module.finrank ℂ ↥X

/-- The Hilbert function `d ↦ dim (J/I)_d` of the subquotient `J/I` of `ℂ[X : Fin s]`. -/
noncomputable def hfun (w : Fin s → Fin m) (I J : Ideal (MvPolynomial (Fin s) ℂ))
    (d : Fin m → ℕ) : ℕ :=
  fr (Pci w J (fun i => (d i : ℤ))) - fr (Pci w I (fun i => (d i : ℤ)))

/-- `Z` kills `J/I`: every variable in `Z` multiplies `J` into `I`. -/
def Kills (Z : Finset (Fin s)) (I J : Ideal (MvPolynomial (Fin s) ℂ)) : Prop :=
  ∀ j ∈ Z, Ideal.span ({MvPolynomial.X j} : Set (MvPolynomial (Fin s) ℂ)) * J ≤ I

/-- Number of variables of weight `i` that are not in `Z`. -/
noncomputable def ncount (w : Fin s → Fin m) (Z : Finset (Fin s)) (i : Fin m) : ℕ :=
  (Finset.univ.filter (fun j => w j = i ∧ j ∉ Z)).card

end RayH

end Work.BW
