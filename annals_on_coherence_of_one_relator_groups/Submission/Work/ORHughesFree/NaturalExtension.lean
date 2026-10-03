/-
Copyright (c) 2025. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.

# Natural extensions of Sylvester rank functions to skew Laurent polynomial rings

Following [JZLA20, §3], we set up the natural extension of a Sylvester rank function from a ring `R`
to the skew Laurent polynomial ring `R[t^{±1}; τ]`, where `τ` is an automorphism of `R`.

We model `R[t^{±1}; τ]` as the skew monoid algebra `SkewMonoidAlgebra R (Multiplicative ℤ)`,
with the twist encoded by a `MulSemiringAction (Multiplicative ℤ) R` instance.

Main definitions:

* `IsTauCompatible rk τ` : `rk` is invariant under `τ` ([JZLA20, §3.1]);
* `onePlusAt n A` : the matrix `I_n + A t` over `R[t^{±1}; τ]`;
* `IsNaturalExtension rk rkE` : the characterisation of the natural extension
  ([JZLA20, Proposition 3.5]).
-/
import Mathlib
import Submission.Work.ORHughesFree.SylvesterRank

set_option autoImplicit false

universe u

namespace Work.ORHughesFree

open Matrix

variable {R : Type u}

/-- A Sylvester rank function `rk` on `R` is **`τ`-compatible** if `rk (τ A) = rk A` for every
matrix `A` ([JZLA20, §3.1]). -/
def IsTauCompatible [Ring R] (rk : SylvesterRank R) (τ : R ≃+* R) : Prop :=
  ∀ (n m : ℕ) (A : Matrix (Fin n) (Fin m) R), rk.rk n m (A.map τ) = rk.rk n m A

section SkewLaurent

variable [Ring R] [MulSemiringAction (Multiplicative ℤ) R]

/-- The variable `t` of the skew Laurent polynomial ring `R[t^{±1}; τ]`. -/
noncomputable def skewLaurentT : SkewMonoidAlgebra R (Multiplicative ℤ) :=
  SkewMonoidAlgebra.single (Multiplicative.ofAdd 1) 1

/-- The constant matrix `A` embedded in `R[t^{±1}; τ]`. -/
noncomputable def skewLaurentConst (n m : ℕ) (A : Matrix (Fin n) (Fin m) R) :
    Matrix (Fin n) (Fin m) (SkewMonoidAlgebra R (Multiplicative ℤ)) :=
  A.map (fun a => SkewMonoidAlgebra.single 1 a)

/-- The matrix `I_n + A t` over `R[t^{±1}; τ]` ([JZLA20, Proposition 3.5]). -/
noncomputable def onePlusAt (n : ℕ) (A : Matrix (Fin n) (Fin n) R) :
    Matrix (Fin n) (Fin n) (SkewMonoidAlgebra R (Multiplicative ℤ)) :=
  1 + A.map (fun a => SkewMonoidAlgebra.single (Multiplicative.ofAdd 1) a)

/-- `rkE` is a **natural extension** of `rk` to the skew Laurent polynomial ring
`R[t^{±1}; τ]` if it extends `rk` and satisfies the characterisation of
[JZLA20, Proposition 3.5]: `rkE (I_n + A t) = n` for every `n × n` matrix `A` over `R`. -/
def IsNaturalExtension (rk : SylvesterRank R)
    (rkE : SylvesterRank (SkewMonoidAlgebra R (Multiplicative ℤ))) : Prop :=
  (∀ (n m : ℕ) (A : Matrix (Fin n) (Fin m) R), rkE.rk n m (skewLaurentConst n m A) = rk.rk n m A) ∧
    (∀ (n : ℕ) (A : Matrix (Fin n) (Fin n) R), rkE.rk n n (onePlusAt n A) = n)

end SkewLaurent

end Work.ORHughesFree
