import Mathlib
import Submission.Work.ORHughesFree.NaturalExtension.envelopeDefs
import Submission.Work.ORHughesFree.NaturalExtension.starSkewLaurent
import Submission.Work.ORHughesFree.NaturalExtension
import Submission.Work.ORHughesFree.SkewLaurentSeriesInstances

/-!
# The evaluation homomorphism `U[t^{±1}; τ] → U` for an inner twist

When the twist `τ` of the skew Laurent polynomial ring `U[t^{±1}; τ]` is the inner automorphism
`x ↦ v x v⁻¹` given by a unit `v ∈ Uˣ` (with `v^* = v⁻¹`), the skew Laurent polynomial ring maps
onto `U` by `t ↦ v`, and this evaluation is a `∗`-ring homomorphism for the involution `starSkewL`
of `U[t^{±1}; τ]`.  This file constructs that homomorphism `θ` (as
`SkewMonoidAlgebra.liftNCRingHom`) and records its basic properties, together with the two matrix
computations needed in §6 of the coherence paper.
-/

namespace Work.ORHughesFree.Section6

open Work.ORHughesFree
open Work.ORHughesFree.NaturalExtension

/-- Consequence of `star v = v⁻¹` for the powers of the unit `v`: the involution of `U` sends
`v ^ k` to `v ^ (-k)`. -/
theorem star_zpow_val {U : Type} [Ring U] [StarRing U] (v : Uˣ)
    (hstar : star (v : U) = (((v⁻¹ : Uˣ)) : U)) (k : ℤ) :
    star (((v ^ k : Uˣ)) : U) = (((v ^ (-k) : Uˣ)) : U) := by
  have hvinv : star (((v⁻¹ : Uˣ)) : U) = ((v : Uˣ) : U) := by
    rw [← hstar, star_star]
  refine Int.induction_on k ?h0 ?hpos ?hneg
  case h0 => simp
  case hpos =>
    intro i ih
    have hstep : (v ^ ((i : ℤ) + 1) : Uˣ) = v ^ (i : ℤ) * v := zpow_add_one v (i : ℤ)
    rw [hstep, Units.val_mul, star_mul, hstar, ih]
    rw [← Units.val_mul, ← zpow_neg_one v, ← zpow_add]
    congr 2
    ring
  case hneg =>
    intro i ih
    have hstep : (v ^ (-(i : ℤ) - 1) : Uˣ) = v⁻¹ * v ^ (-(i : ℤ)) := by
      rw [show -(i : ℤ) - 1 = -1 + -(i : ℤ) from by ring, zpow_add, zpow_neg_one]
    have ih' : star (((v ^ (-(i : ℤ) : ℤ) : Uˣ)) : U) = (((v ^ (i : ℤ) : Uˣ)) : U) := by
      have h := ih
      rw [show -(-(i : ℤ)) = (i : ℤ) from by ring] at h
      exact h
    rw [hstep, Units.val_mul, star_mul, hvinv, ih']
    rw [← Units.val_mul, ← zpow_add_one v (i : ℤ)]
    congr 2
    ring

/-- Multiplication of a square matrix on the right by the scalar matrix `c • 1` multiplies every
entry by `c`. -/
theorem mul_scalar_eq_map {U : Type} [Ring U] (n : ℕ) (A : Matrix (Fin n) (Fin n) U) (c : U) :
    A * Matrix.scalar (Fin n) c = A.map (fun a => a * c) := by
  ext i j
  simp [Matrix.mul_apply, Matrix.scalar, Matrix.diagonal, Matrix.map_apply]

/-- **Evaluation of `U[t^{±1}; τ]` at `t ↦ v`.**  If the `ℤ`-action on `U` is conjugation by the
unit `v` and `star v = v⁻¹`, there is a ring homomorphism
`θ : U[t^{±1}; τ] → U` with `θ (t^k · x) = x v^k`; it is compatible with the involutions, and it
computes the constant matrices and the matrices `I_n + A t` over `U[t^{±1}; τ]`. -/
theorem exists_theta {U : Type} [Ring U] [StarRing U] [MulSemiringAction (Multiplicative ℤ) U]
    (v : Uˣ) (hstar : star (v : U) = (((v⁻¹ : Uˣ)) : U))
    (hact : ∀ (k : ℤ) (x : U),
      (Multiplicative.ofAdd k) • x = ((v ^ k : Uˣ) : U) * x * ((v ^ (-k) : Uˣ) : U)) :
    ∃ θ : SkewMonoidAlgebra U (Multiplicative ℤ) →+* U,
      (∀ (k : ℤ) (x : U),
        θ (SkewMonoidAlgebra.single (Multiplicative.ofAdd k) x) = x * ((v ^ k : Uˣ) : U)) ∧
      (∀ p : SkewMonoidAlgebra U (Multiplicative ℤ),
        θ (Work.ORHughesFree.NaturalExtension.starSkewL p) = star (θ p)) ∧
      (∀ (n m : ℕ) (A : Matrix (Fin n) (Fin m) U),
        (Work.ORHughesFree.skewLaurentConst n m A).map θ = A) ∧
      (∀ (n : ℕ) (A : Matrix (Fin n) (Fin n) U),
        (Work.ORHughesFree.onePlusAt n A).map θ = 1 + A * Matrix.scalar (Fin n) (v : U)) := by
  classical
  -- the monoid homomorphism `ℤ →* U`, `k ↦ v ^ k`
  let g : Multiplicative ℤ →* U := (Units.coeHom U).comp (zpowersHom Uˣ v)
  have hg : ∀ k : ℤ, g (Multiplicative.ofAdd k) = (((v ^ k : Uˣ)) : U) := by
    intro k; simp [g]
  have hg_inv : ∀ k : ℤ, g (Multiplicative.ofAdd k)⁻¹ = (((v ^ (-k) : Uˣ)) : U) := by
    intro k
    rw [show (Multiplicative.ofAdd k)⁻¹ = Multiplicative.ofAdd (-k) from by simp, hg]
  -- the compatibility of the action with `g`, i.e. `τ(y)(x) · g y = g y · x`
  have hcomm : ∀ {x : U} {y : Multiplicative ℤ},
      (RingHom.id U) (y • x) * g y = g y * (RingHom.id U) x := by
    intro x y
    rw [RingHom.id_apply, RingHom.id_apply]
    obtain ⟨k, hk⟩ := Multiplicative.ofAdd.surjective y
    rw [← hk, hg k, hact k x]
    rw [mul_assoc, ← Units.val_mul, zpow_neg, inv_mul_cancel, Units.val_one, mul_one]
  -- the evaluation homomorphism
  let θ : SkewMonoidAlgebra U (Multiplicative ℤ) →+* U :=
    SkewMonoidAlgebra.liftNCRingHom (RingHom.id U) g hcomm
  have hsingle : ∀ (m : Multiplicative ℤ) (x : U),
      θ (SkewMonoidAlgebra.single m x) = x * (g m : U) := by
    intro m x
    change (SkewMonoidAlgebra.liftNC ((RingHom.id U : U →+* U) : U →+ U)
      (g : Multiplicative ℤ → U)) (SkewMonoidAlgebra.single m x) = x * (g m : U)
    rw [SkewMonoidAlgebra.liftNC_single]
    rfl
  have hstar_pow := star_zpow_val (U := U) v hstar
  have hsingle_star : ∀ (m : Multiplicative ℤ) (a : U),
      θ (starSkewL (SkewMonoidAlgebra.single m a)) = star (θ (SkewMonoidAlgebra.single m a)) := by
    intro m a
    obtain ⟨k, hk⟩ := Multiplicative.ofAdd.surjective m
    subst hk
    rw [starSkewL_single,
      hsingle ((Multiplicative.ofAdd k)⁻¹) ((Multiplicative.ofAdd k)⁻¹ • star a),
      hsingle (Multiplicative.ofAdd k) a]
    have hsmul : (Multiplicative.ofAdd k)⁻¹ • star a =
        (((v ^ (-k) : Uˣ)) : U) * star a * (((v ^ k : Uˣ)) : U) := by
      rw [show (Multiplicative.ofAdd k)⁻¹ = Multiplicative.ofAdd (-k) from by simp,
        hact (-k) (star a), show -(-k) = k from by ring]
    rw [hsmul, hg_inv k, hg k, star_mul, hstar_pow k, mul_assoc, ← Units.val_mul, ← zpow_add,
      add_neg_cancel, zpow_zero, Units.val_one, mul_one]
  refine ⟨θ, ?_, ?_, ?_, ?_⟩
  · intro k x
    rw [hsingle, hg k]
  · intro p
    induction p using SkewMonoidAlgebra.induction_on with
    | zero => rw [starSkewL_zero, map_zero, star_zero]
    | single m a => exact hsingle_star m a
    | add p q ihp ihq => rw [starSkewL_add, map_add, ihp, ihq, map_add, star_add]
  · intro n m A
    ext i j
    simp only [skewLaurentConst, Matrix.map_apply]
    rw [hsingle, map_one, mul_one]
  · intro n A
    rw [onePlusAt, Matrix.map_add θ (fun a b => map_add θ a b),
      Matrix.map_one θ (map_zero θ) (map_one θ)]
    have hfun : ∀ a : U,
        θ (SkewMonoidAlgebra.single (Multiplicative.ofAdd (1 : ℤ)) a) = a * ((v : Uˣ) : U) := by
      intro a
      rw [hsingle, hg 1, zpow_one]
    have h2 : (A.map fun a => SkewMonoidAlgebra.single (Multiplicative.ofAdd (1 : ℤ)) a).map θ
        = A.map (fun a => a * ((v : Uˣ) : U)) := by
      ext i j
      simp only [Matrix.map_apply]
      exact hfun (A i j)
    rw [h2, ← mul_scalar_eq_map n A ((v : Uˣ) : U)]

end Work.ORHughesFree.Section6
