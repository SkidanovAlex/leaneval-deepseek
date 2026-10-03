import Mathlib
import Submission.Work.ORHughesFree.Section6.exists_theta
import Submission.Work.ORHughesFree.NaturalExtension.envelopeDefs
import Submission.Work.ORHughesFree.NaturalExtension.starSkewLaurent
import Submission.Work.ORHughesFree.NaturalExtension
import Submission.Work.ORHughesFree.SkewLaurentSeriesInstances

/-!
# The evaluation homomorphism `A[t^{±1}; τ] → U` along a `∗`-ring homomorphism

This is the general form of `Work.ORHughesFree.Section6.exists_theta`: instead of evaluating the
skew Laurent polynomial ring `U[t^{±1}; τ]` at `t ↦ v` when the twist is the inner automorphism
`x ↦ v x v⁻¹`, we start from a `∗`-ring homomorphism `f : A →+* U` out of an arbitrary ring `A`
carrying a `ℤ`-action, and a unit `v ∈ Uˣ` with `v^* = v⁻¹`, subject to the compatibility

`f (k • x) = v^k * f x * v^{-k}`.

Then there is a ring homomorphism `θ : A[t^{±1}; τ] → U` with `θ (t^k · x) = f x · v^k` which is
compatible with the involutions and which computes the constant matrices and the matrices
`I_n + A t`.
-/

namespace Work.ORHughesFree.Section6

open Work.ORHughesFree
open Work.ORHughesFree.NaturalExtension

theorem exists_theta_gen {A : Type} [Ring A] [StarRing A] [MulSemiringAction (Multiplicative ℤ) A]
    {U : Type} [Ring U] [StarRing U] (f : A →+* U) (hf_star : ∀ x : A, f (star x) = star (f x))
    (v : Uˣ) (hstar : star (v : U) = (((v⁻¹ : Uˣ)) : U))
    (hf : ∀ (k : ℤ) (x : A), f ((Multiplicative.ofAdd k) • x) =
      ((v ^ k : Uˣ) : U) * f x * ((v ^ (-k) : Uˣ) : U)) :
    ∃ θ : SkewMonoidAlgebra A (Multiplicative ℤ) →+* U,
      (∀ (k : ℤ) (x : A), θ (SkewMonoidAlgebra.single (Multiplicative.ofAdd k) x) =
        f x * ((v ^ k : Uˣ) : U)) ∧
      (∀ p : SkewMonoidAlgebra A (Multiplicative ℤ),
        θ (Work.ORHughesFree.NaturalExtension.starSkewL p) = star (θ p)) ∧
      (∀ (n m : ℕ) (B : Matrix (Fin n) (Fin m) A),
        (Work.ORHughesFree.skewLaurentConst n m B).map θ = B.map f) ∧
      (∀ (n : ℕ) (B : Matrix (Fin n) (Fin n) A),
        (Work.ORHughesFree.onePlusAt n B).map θ = 1 + B.map f * Matrix.scalar (Fin n) (v : U)) := by
  classical
  -- the monoid homomorphism `ℤ →* U`, `k ↦ v ^ k`
  let g : Multiplicative ℤ →* U := (Units.coeHom U).comp (zpowersHom Uˣ v)
  have hg : ∀ k : ℤ, g (Multiplicative.ofAdd k) = (((v ^ k : Uˣ)) : U) := by
    intro k; simp [g]
  have hg_inv : ∀ k : ℤ, g ((Multiplicative.ofAdd k)⁻¹) = (((v ^ (-k) : Uˣ)) : U) := by
    intro k
    rw [show (Multiplicative.ofAdd k)⁻¹ = Multiplicative.ofAdd (-k) from by simp, hg]
  -- compatibility of `f` with the `ℤ`-action and `g`
  have hcomm : ∀ {x : A} {y : Multiplicative ℤ}, f (y • x) * g y = g y * f x := by
    intro x y
    obtain ⟨k, hk⟩ := Multiplicative.ofAdd.surjective y
    rw [← hk, hg k, hf k x]
    rw [mul_assoc, ← Units.val_mul, ← zpow_add, neg_add_cancel, zpow_zero, Units.val_one, mul_one]
  -- the evaluation homomorphism
  let θ : SkewMonoidAlgebra A (Multiplicative ℤ) →+* U :=
    SkewMonoidAlgebra.liftNCRingHom f g hcomm
  have hsingle : ∀ (m : Multiplicative ℤ) (x : A),
      θ (SkewMonoidAlgebra.single m x) = f x * (g m : U) := by
    intro m x
    change (SkewMonoidAlgebra.liftNC (f : A →+ U) (g : Multiplicative ℤ → U))
      (SkewMonoidAlgebra.single m x) = f x * (g m : U)
    rw [SkewMonoidAlgebra.liftNC_single]
    rfl
  have hstar_pow := star_zpow_val (U := U) v hstar
  have hsingle_star : ∀ (m : Multiplicative ℤ) (a : A),
      θ (starSkewL (SkewMonoidAlgebra.single m a)) =
        star (θ (SkewMonoidAlgebra.single m a)) := by
    intro m a
    obtain ⟨k, hk⟩ := Multiplicative.ofAdd.surjective m
    subst hk
    rw [starSkewL_single,
      hsingle ((Multiplicative.ofAdd k)⁻¹) ((Multiplicative.ofAdd k)⁻¹ • star a),
      hsingle (Multiplicative.ofAdd k) a]
    have h1 : f ((Multiplicative.ofAdd k)⁻¹ • star a) =
        (((v ^ (-k) : Uˣ)) : U) * f (star a) * (((v ^ k : Uˣ)) : U) := by
      rw [show (Multiplicative.ofAdd k)⁻¹ = Multiplicative.ofAdd (-k) from by simp,
        hf (-k) (star a)]
      simp only [neg_neg]
    rw [h1, hg_inv k, hg k, star_mul, hstar_pow k, ← hf_star a]
    rw [mul_assoc, ← Units.val_mul, ← zpow_add, add_neg_cancel, zpow_zero, Units.val_one, mul_one]
  refine ⟨θ, ?_, ?_, ?_, ?_⟩
  · intro k x
    rw [hsingle, hg k]
  · intro p
    induction p using SkewMonoidAlgebra.induction_on with
    | zero => rw [starSkewL_zero, map_zero, star_zero]
    | single m a => exact hsingle_star m a
    | add p q ihp ihq => rw [starSkewL_add, map_add, ihp, ihq, map_add, star_add]
  · intro n m B
    ext i j
    simp only [skewLaurentConst, Matrix.map_apply]
    rw [hsingle, MonoidHom.map_one, mul_one]
  · intro n B
    rw [onePlusAt, Matrix.map_add θ (fun a b => map_add θ a b),
      Matrix.map_one θ (map_zero θ) (map_one θ)]
    have hfun : ∀ a : A,
        θ (SkewMonoidAlgebra.single (Multiplicative.ofAdd (1 : ℤ)) a) =
          f a * ((v : Uˣ) : U) := by
      intro a
      rw [hsingle, hg 1, zpow_one]
    have h2 : (B.map fun a => SkewMonoidAlgebra.single (Multiplicative.ofAdd (1 : ℤ)) a).map θ
        = (B.map f).map (fun a => a * ((v : Uˣ) : U)) := by
      ext i j
      simp only [Matrix.map_apply]
      exact hfun (B i j)
    rw [h2, ← mul_scalar_eq_map n (B.map f) ((v : Uˣ) : U)]

end Work.ORHughesFree.Section6
