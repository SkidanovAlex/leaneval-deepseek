import Mathlib
-- PORT435-BEGIN (v4.35 isDefEq respectTransparency compat)
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- PORT435-END
open scoped BigOperators

/-!
# Abstract norm/cohomology machinery for the theory of class formations

For a finite group `G` acting multiplicatively on a commutative group `A` we package the
`0`-th Tate cohomology `Ĥ⁰(H, A) = A^H / N_H(A)` (fixed points modulo the norm) for a finite
subgroup `H ≤ G`.  These are the objects appearing in the statement of the main theorem of
class formations (Tate–Nakayama).
-/

namespace Commons.ClassFormation

variable {G A : Type*} [Group G] [CommGroup A] [MulDistribMulAction G A]

/-- The norm endomorphism `a ↦ ∏_{h∈H} h • a` of `A`, for a finite subgroup `H`. -/
noncomputable def normHom (H : Subgroup G) [Fintype H] : A →* A where
  toFun a := ∏ h : H, h • a
  map_one' := by simp
  map_mul' a b := by
    have h : (∏ h : H, h • (a * b)) = ∏ h : H, (h • a) * (h • b) :=
      Finset.prod_congr rfl (fun h _ => smul_mul' h.1 a b)
    rw [h, Finset.prod_mul_distrib]

@[simp] lemma normHom_apply (H : Subgroup G) [Fintype H] (a : A) :
    normHom H a = ∏ h : H, h • a := rfl

/-- The norm lands in the `H`-fixed points. -/
lemma normHom_mem_fixed (H : Subgroup G) [Fintype H] (a : A) (h : H) :
    h • (normHom H a) = normHom H a := by
  rw [normHom_apply]
  have h1 : h • (∏ x : H, x • a) = ∏ x : H, h • (x • a) := by
    rw [← MulDistribMulAction.toMonoidHom_apply A h, map_prod]
    simp [MulDistribMulAction.toMonoidHom_apply]
  rw [h1]
  exact Fintype.prod_equiv (Equiv.mulLeft h) _ _ (fun x => by simp only [Equiv.coe_mulLeft, smul_smul])

/-- `Ĥ⁰(H, A) = A^H ⧸ N_H(A)` as a subgroup quotient. -/
noncomputable def H0 (H : Subgroup G) [Fintype H] :
    Subgroup A := (normHom H).range

end Commons.ClassFormation

namespace Commons.ClassFormation

variable {G A : Type*} [Group G] [CommGroup A] [MulDistribMulAction G A]

/-- A crossed homomorphism (1-cocycle) for a subgroup `H` acting on `A`. -/
def IsCocycle (H : Subgroup G) (f : H → A) : Prop :=
  ∀ x y : H, f (x * y) = x • f y * f x

/-- A principal crossed homomorphism (1-coboundary). -/
def IsCoboundary (H : Subgroup G) (f : H → A) : Prop :=
  ∃ a : A, ∀ x : H, f x = x • a * a⁻¹

/-- `H¹(H,A)=0` in cocycle form: every crossed homomorphism is principal. -/
def H1Trivial (H : Subgroup G) : Prop :=
  ∀ f : H → A, IsCocycle H f → IsCoboundary H f

lemma isCocycle_one (H : Subgroup G) : IsCocycle H (fun _ => (1 : A)) := by
  intro x y; rw [smul_one, mul_one]

end Commons.ClassFormation

namespace Commons.ClassFormation

variable {G A : Type*} [Group G] [CommGroup A] [MulDistribMulAction G A]

/-- Additive form of a crossed 2-cocycle for a subgroup `H` acting on `A`. -/
def IsCocycle2 (H : Subgroup G) (f : H → H → A) : Prop :=
  ∀ x y z : H,
    (x • f y z) * (f (x * y) z)⁻¹ * f x (y * z) * (f x y)⁻¹ = 1

/-- A 2-coboundary: the coboundary of a `1`-cochain. -/
def IsCoboundary2 (H : Subgroup G) (f : H → H → A) : Prop :=
  ∃ g : H → A, ∀ x y : H, f x y = (x • g y) * (g (x * y))⁻¹ * g x

/-- The `H²(H,A)=0` statement in cocycle form. -/
def H2Trivial (H : Subgroup G) : Prop :=
  ∀ f : H → H → A, IsCocycle2 H f → IsCoboundary2 H f

end Commons.ClassFormation

namespace Commons.ClassFormation

variable {G A : Type*} [Group G] [CommGroup A] [MulDistribMulAction G A]

end Commons.ClassFormation
