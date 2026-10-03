import Mathlib
import Submission.Work.ORLyndon.Fox

/-!
# The Fox chain rule for a group homomorphism of free groups

This file records the "chain rule" for the (left) Fox derivative `foxD` implemented in
`Submission.Work.ORLyndon.Fox`: for a group homomorphism `φ : FreeGroup X →* FreeGroup Y`,
a generator `y : Y` and an element `w : FreeGroup X` one has

`∂(φ w)/∂y = ∑_x Φ(∂w/∂x) · ∂(φ x)/∂y`,

where `Φ = MonoidAlgebra.mapDomainRingHom K φ` is the induced map of group algebras.

Equivalently, interpreting the family `∂w/∂x ∈ K[F X]` as a finitely supported function
`foxFD w : X →₀ K[F X]`, the identity reads

`foxD y (φ w) = (foxFD w).sum (fun x c => Φ c * foxD y (φ (FreeGroup.of x)))`.

The proof is a structural induction on `w` using `FreeGroup.induction_on`, so we also record
the basic compatibilities of `foxFD` with `1`, generators, inverses of generators and
multiplication.
-/

set_option autoImplicit false

namespace Work.ORLyndon

open MonoidAlgebra

universe u v w

section Comp

variable {X : Type u} {Y : Type w} {K : Type v}
variable [DecidableEq X] [DecidableEq Y] [Ring K]

/-- `foxFD` of the trivial element is the zero finitely supported function. -/
theorem foxFD_one : foxFD (K := K) (1 : FreeGroup X) = 0 := by
  apply Finsupp.ext; intro x
  simp [foxFD_apply]

/-- `foxFD` of a generator is the corresponding Dirac mass. -/
theorem foxFD_of (x : X) : foxFD (K := K) (FreeGroup.of x) = Finsupp.single x 1 := by
  apply Finsupp.ext; intro z
  rw [foxFD_apply, foxD_of, Finsupp.single_apply]

/-- `foxFD` of the inverse of a generator. -/
theorem foxFD_inv_of (x : X) :
    foxFD (K := K) ((FreeGroup.of x)⁻¹) =
      Finsupp.single x (-(MonoidAlgebra.of K (FreeGroup X) ((FreeGroup.of x)⁻¹))) := by
  apply Finsupp.ext; intro z
  rw [foxFD_apply, foxD_inv_of, Finsupp.single_apply]

/-- The Leibniz rule for the finitely supported version `foxFD` of the Fox derivative. -/
theorem foxFD_mul (g h : FreeGroup X) :
    foxFD (K := K) (g * h) = foxFD g + MonoidAlgebra.of K (FreeGroup X) g • foxFD h := by
  apply Finsupp.ext; intro z
  rw [foxFD_apply, foxD_mul, Finsupp.add_apply, Finsupp.smul_apply, smul_eq_mul,
      foxFD_apply, foxFD_apply]

/-- The induced map of group algebras sends the basis element `of g` to `of (φ g)`. -/
@[simp] theorem mapDomainRingHom_of (φ : FreeGroup X →* FreeGroup Y) (g : FreeGroup X) :
    MonoidAlgebra.mapDomainRingHom K φ (MonoidAlgebra.of K (FreeGroup X) g) =
      MonoidAlgebra.of K (FreeGroup Y) (φ g) := by
  rw [MonoidAlgebra.of_apply, MonoidAlgebra.mapDomainRingHom_apply, MonoidAlgebra.mapDomain_single,
      MonoidAlgebra.of_apply]

end Comp

/-- Pulling a constant left factor out of a `Finsupp.sum`. -/
theorem finsupp_sum_const_mul {X : Type u} {Y : Type v} {K : Type w}
    [DecidableEq X] [DecidableEq Y] [Ring K]
    (f : X →₀ MonoidAlgebra K (FreeGroup X))
    (c : MonoidAlgebra K (FreeGroup Y))
    (H : X → MonoidAlgebra K (FreeGroup X) → MonoidAlgebra K (FreeGroup Y)) :
    f.sum (fun i a => c * H i a) = c * f.sum H := by
  rw [Finsupp.sum, Finsupp.sum, Finset.mul_sum]

section Comp

variable {X : Type u} {Y : Type w} {K : Type v}
variable [DecidableEq X] [DecidableEq Y] [Ring K]

/-- **The Fox chain rule.** For a group homomorphism `φ : FreeGroup X →* FreeGroup Y`, a generator
`y : Y` and `w : FreeGroup X`:
`∂(φ w)/∂y = ∑_x Φ(∂w/∂x) · ∂(φ x)/∂y` where `Φ = MonoidAlgebra.mapDomainRingHom K φ`. -/
theorem foxD_comp (φ : FreeGroup X →* FreeGroup Y) (y : Y) (w : FreeGroup X) :
    foxD (K := K) y (φ w) =
      (foxFD (K := K) w).sum (fun x c =>
        MonoidAlgebra.mapDomainRingHom K φ c * foxD (K := K) y (φ (FreeGroup.of x))) := by
  set H : X → MonoidAlgebra K (FreeGroup X) → MonoidAlgebra K (FreeGroup Y) :=
    fun x c => MonoidAlgebra.mapDomainRingHom K φ c * foxD (K := K) y (φ (FreeGroup.of x)) with hH
  have H0 : ∀ x, H x 0 = 0 := by intro x; simp [hH]
  have Hadd : ∀ x (a b : MonoidAlgebra K (FreeGroup X)), H x (a + b) = H x a + H x b := by
    intro x a b; simp only [hH, map_add, add_mul]
  have Hlin : ∀ (g : FreeGroup X) (x : X) (a : MonoidAlgebra K (FreeGroup X)),
      H x (MonoidAlgebra.of K (FreeGroup X) g * a) =
        MonoidAlgebra.of K (FreeGroup Y) (φ g) * H x a := by
    intro g x a
    simp only [hH]
    rw [map_mul, mapDomainRingHom_of, mul_assoc]
  refine FreeGroup.induction_on w ?_ ?_ ?_ ?_
  · rw [map_one, foxD_one, foxFD_one, Finsupp.sum_zero_index]
  · intro x
    rw [foxFD_of, Finsupp.sum_single_index (H0 x)]
    simp only [hH, map_one, one_mul]
  · intro x ih
    have hstep : (foxFD (K := K) ((FreeGroup.of x)⁻¹)).sum H =
        -(MonoidAlgebra.of K (FreeGroup Y) ((φ (FreeGroup.of x))⁻¹) *
          foxD (K := K) y (φ (FreeGroup.of x))) := by
      rw [foxFD_inv_of, Finsupp.sum_single_index (H0 x)]
      simp only [hH, map_neg, mapDomainRingHom_of, map_inv, neg_mul]
    rw [hstep, map_inv, foxD_inv]
  · intro g h ihg ihh
    rw [map_mul, foxD_mul, ihg, ihh]
    conv_rhs =>
      rw [foxFD_mul,
        Finsupp.sum_add_index (fun a _ => H0 a) (fun a _ b1 b2 => Hadd a b1 b2),
        Finsupp.sum_smul_index H0,
        Finsupp.sum_congr (f := foxFD h)
          (g2 := fun i a => (MonoidAlgebra.of K (FreeGroup Y)) (φ g) * H i a)
          (fun i _ => Hlin g i ((foxFD h) i)),
        finsupp_sum_const_mul]

end Comp

end Work.ORLyndon
