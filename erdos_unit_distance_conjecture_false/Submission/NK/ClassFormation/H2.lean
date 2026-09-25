import Mathlib

/-!
# Second cohomology (2-cocycles) in additive form

For a finite group `G` acting on an additive commutative group `A` we set up the groups of
`2`-cocycles and `2`-coboundaries for a subgroup `H`, so that `H²(H,A) = Z²(H,A)/B²(H,A)`.
-/

namespace Commons.ClassFormation

variable {G A : Type*} [Group G] [AddCommGroup A] [DistribMulAction G A]

/-- The inhomogeneous `2`-cocycle condition. -/
def IsAdd2Cocycle (H : Subgroup G) (f : H → H → A) : Prop :=
  ∀ x y z : H, x • f y z - f (x * y) z + f x (y * z) - f x y = 0

lemma IsAdd2Cocycle.add {H : Subgroup G} {f g : H → H → A}
    (hf : IsAdd2Cocycle H f) (hg : IsAdd2Cocycle H g) :
    IsAdd2Cocycle H (fun x y => f x y + g x y) := by
  intro x y z
  have hf' := hf x y z
  have hg' := hg x y z
  simp only [smul_add]
  rw [show x • f y z + x • g y z - (f (x * y) z + g (x * y) z) +
        (f x (y * z) + g x (y * z)) - (f x y + g x y)
      = (x • f y z - f (x * y) z + f x (y * z) - f x y) +
        (x • g y z - g (x * y) z + g x (y * z) - g x y) by abel]
  rw [hf', hg', add_zero]

end Commons.ClassFormation

namespace Commons.ClassFormation

variable {G A : Type*} [Group G] [AddCommGroup A] [DistribMulAction G A]

lemma IsAdd2Cocycle.zero (H : Subgroup G) : IsAdd2Cocycle H (fun _ _ => (0 : A)) := by
  intro x y z; simp

lemma IsAdd2Cocycle.neg {H : Subgroup G} {f : H → H → A} (hf : IsAdd2Cocycle H f) :
    IsAdd2Cocycle H (fun x y => - f x y) := by
  intro x y z
  have hf' := hf x y z
  simp only [smul_neg]
  rw [show -(x • f y z) - -f (x * y) z + -f x (y * z) - -f x y =
      -(x • f y z - f (x * y) z + f x (y * z) - f x y) by abel]
  rw [hf', neg_zero]

/-- The `2`-cocycles of `H` as an additive subgroup of `H → H → A`. -/
def Z2 (H : Subgroup G) : AddSubgroup (H → H → A) where
  carrier := {f | IsAdd2Cocycle H f}
  zero_mem' := IsAdd2Cocycle.zero H
  add_mem' := IsAdd2Cocycle.add
  neg_mem' := IsAdd2Cocycle.neg

/-- The `2`-coboundaries of `H`. -/
def IsAdd2Coboundary (H : Subgroup G) (f : H → H → A) : Prop :=
  ∃ g : H → A, ∀ x y : H, f x y = x • g y - g (x * y) + g x

end Commons.ClassFormation

namespace Commons.ClassFormation

variable {G A : Type*} [Group G] [AddCommGroup A] [DistribMulAction G A]

lemma IsAdd2Coboundary.isCocycle {H : Subgroup G} {f : H → H → A}
    (hf : IsAdd2Coboundary H f) : IsAdd2Cocycle H f := by
  obtain ⟨g, hg⟩ := hf
  intro x y z
  rw [hg x y, hg y z, hg (x * y) z, hg x (y * z)]
  simp only [smul_sub, smul_add, smul_smul, mul_assoc]
  abel

end Commons.ClassFormation
