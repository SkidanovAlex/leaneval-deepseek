/-
Copyright (c) 2024. All rights reserved.

# Coordinates for the two-step model

Auxiliary definitions for `Work.Higman.nonempty_twoStepModel`.

Let `G` be a group and `A : Fin n → G`.  For `v : Fin n → ZMod 2` we build, by recursion
on the *last* coordinate, the "section element"

  `coordSec n A v = ∏ i, A i ^ (v i).val`

(the product taken in the order of `Fin n`; the group `G` need not be commutative, so this
is written as a recursion rather than a `Finset.prod`).

The *cocycle* of this section is `cocy n A v w = s v * s w * (s (v+w))⁻¹`.

The point of the file is the theorem `Work.Higman.cocy_props` (in `CoordCocycle.lean`):
when commutators of `G` are central, every square is central and every central element
squares to `1`, this cocycle is bi-additive and central-valued.  In the application `G = P`
is a group with `∀ x, x ^ 2 ∈ Z(P)` and `∀ z ∈ Z(P), z ^ 2 = 1`, and `A` lifts a basis of
`P / Z(P)`.
-/

import Mathlib

-- ftport:v435-opts-begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- ftport:v435-opts-end

set_option autoImplicit false

open scoped commutatorElement

namespace Work.Higman

variable {G : Type*} [Group G]

/-- `coordSec n A v = ∏ i, A i ^ (v i).val`, built as a recursion on the last coordinate of
`Fin n` (indices are processed so that `A 0` is the leftmost factor). -/
def coordSec : (n : ℕ) → (Fin n → G) → (Fin n → ZMod 2) → G
  | 0, _, _ => 1
  | n + 1, A, v =>
      coordSec n (fun i => A i.castSucc) (fun i => v i.castSucc)
        * A (Fin.last n) ^ (v (Fin.last n)).val

@[simp] theorem coordSec_zero (A : Fin 0 → G) (v : Fin 0 → ZMod 2) :
    coordSec 0 A v = 1 := rfl

theorem coordSec_succ (n : ℕ) (A : Fin (n + 1) → G) (v : Fin (n + 1) → ZMod 2) :
    coordSec (n + 1) A v =
      coordSec n (fun i => A i.castSucc) (fun i => v i.castSucc)
        * A (Fin.last n) ^ (v (Fin.last n)).val := rfl

/-- The cocycle of the section `coordSec`. -/
def cocy (n : ℕ) (A : Fin n → G) (v w : Fin n → ZMod 2) : G :=
  coordSec n A v * coordSec n A w * (coordSec n A (v + w))⁻¹

/-- The section lands on `1` at the zero vector. -/
theorem coordSec_zero_fun (n : ℕ) (A : Fin n → G) :
    coordSec n A (0 : Fin n → ZMod 2) = 1 := by
  induction n with
  | zero => rfl
  | succ n ih =>
      rw [coordSec_succ,
        show (fun i => (0 : Fin (n + 1) → ZMod 2) i.castSucc) = (0 : Fin n → ZMod 2) from rfl,
        ih]
      simp


variable {P V : Type*} [Group P] [AddCommGroup V] [Module (ZMod 2) V]

/-- If `π : P → V` is additive (`π (xy) = π x + π y`, `π 1 = 0`) and `π (A i) = B i`, then
`π` sends the section element `coordSec n A w` to the linear combination `∑ i, w i • B i`. -/
theorem pi_coordSec (π : P → V) (hπ : ∀ x y, π (x * y) = π x + π y) (hπ1 : π 1 = 0)
    (n : ℕ) (A : Fin n → P) (B : Fin n → V) (hB : ∀ i, π (A i) = B i)
    (w : Fin n → ZMod 2) :
    π (coordSec n A w) = ∑ i, w i • B i := by
  have hpow : ∀ (a : P) (m : ℕ), π (a ^ m) = m • π a := by
    intro a m
    induction m with
    | zero => simpa using hπ1
    | succ m ih => rw [pow_succ, hπ, ih, succ_nsmul]
  induction n with
  | zero => simp [coordSec, hπ1]
  | succ n ih =>
      rw [coordSec_succ, hπ]
      rw [ih (fun i => A i.castSucc) (fun i => B i.castSucc) (fun i => hB i.castSucc)
            (fun i => w i.castSucc)]
      rw [hpow, hB, Fin.sum_univ_castSucc]
      congr 1
      conv_rhs => rw [← ZMod.natCast_zmod_val (w (Fin.last n))]
      rw [Nat.cast_smul_eq_nsmul]

end Work.Higman
