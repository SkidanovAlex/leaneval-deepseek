import Mathlib
import Submission.Work.CharCore.Main

-- ftport:v435-opts-begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- ftport:v435-opts-end

/-!
# The dimension of the centre of a finite group algebra

For a finite group `A` and a field `k`, the centre of the group algebra `k[A]` has
`k`-dimension at most the number of conjugacy classes of `A`
(`Work.NormalComplement.AppVII.CenterFinrankLe`).  In fact the two numbers are equal,
but only the inequality is needed here.

The argument is the classical one.  Membership in the centre `Subalgebra.center k k[A]`
means commuting with every element, and testing against the group elements `of c` shows
that the coefficients of a central element are invariant under conjugation
(`coeff_eq_of_mem_center`).  Hence a central element may be viewed as a function on the
set `ConjClasses A` of conjugacy classes, giving a `k`-linear map
`centerToClassFun` from the centre into the function space `ConjClasses A → k`.  That map
is injective, because if all coefficients on the conjugacy classes vanish then all
coefficients vanish.  Comparing `k`-dimensions with the finite-dimensional space
`ConjClasses A → k`, whose dimension is `Nat.card (ConjClasses A)`, yields the bound.
-/

open Classical

namespace Work.NormalComplement.AppVII

/-- A central element of the group algebra `k[A]` has coefficients which are constant on
conjugacy classes: conjugate group elements carry the same coefficient. -/
theorem coeff_eq_of_mem_center {k : Type*} [Field k] {A : Type*} [Group A]
    {x : MonoidAlgebra k A} (hx : x ∈ Subalgebra.center k (MonoidAlgebra k A))
    {a b : A} (hab : IsConj a b) : x.coeff a = x.coeff b := by
  obtain ⟨c, hc⟩ := isConj_iff.mp hab
  -- `x` commutes with the group element `c`, hence with `of c`.
  have hcomm : MonoidAlgebra.of k A c * x = x * MonoidAlgebra.of k A c :=
    Subalgebra.mem_center_iff.mp hx (MonoidAlgebra.of k A c)
  -- Compare the coefficient at `c * a` on both sides.
  have h1 : (MonoidAlgebra.of k A c * x).coeff (c * a) = x.coeff a := by
    rw [MonoidAlgebra.of_apply, MonoidAlgebra.coeff_single_mul_apply]
    simp
  have h2 : (x * MonoidAlgebra.of k A c).coeff (c * a) = x.coeff b := by
    rw [MonoidAlgebra.of_apply, MonoidAlgebra.coeff_mul_single_apply, hc]
    simp
  rw [← h1, hcomm, h2]

/-- The `k`-linear map sending a central element of `k[A]` to its coefficient function on
the set of conjugacy classes of `A`.  It is well defined by `coeff_eq_of_mem_center`. -/
noncomputable def centerToClassFun (k : Type*) [Field k] (A : Type*) [Group A] :
    ↥(Subalgebra.center k (MonoidAlgebra k A)) →ₗ[k] (ConjClasses A → k) where
  toFun x := Quotient.lift (fun a => x.1.coeff a)
    (fun _ _ hab => coeff_eq_of_mem_center x.2 hab)
  map_add' x y := by
    funext C
    induction C using Quotient.inductionOn with
    | h a => rfl
  map_smul' r x := by
    funext C
    induction C using Quotient.inductionOn with
    | h a => rfl

/-- The value of `centerToClassFun` on the class of `a` is the coefficient of `a`. -/
@[simp]
theorem centerToClassFun_apply_mk {k : Type*} [Field k] {A : Type*} [Group A]
    (x : ↥(Subalgebra.center k (MonoidAlgebra k A))) (a : A) :
    centerToClassFun k A x (ConjClasses.mk a) = x.1.coeff a := rfl

/-- A central element is determined by the values of its coefficient function on the
conjugacy classes, so `centerToClassFun` is injective. -/
theorem centerToClassFun_injective {k : Type*} [Field k] {A : Type*} [Group A] :
    Function.Injective (centerToClassFun k A) := by
  intro x y hxy
  apply Subtype.ext
  rw [← MonoidAlgebra.coeff_inj]
  refine Finsupp.ext (fun a => ?_)
  have h := congrFun hxy (ConjClasses.mk a)
  simpa using h

theorem CenterFinrankLe {k : Type*} [Field k] {A : Type*} [Group A] [Fintype A] :
    Module.finrank k ↥(Subalgebra.center k (MonoidAlgebra k A)) ≤ Nat.card (ConjClasses A) := by
  classical
  calc Module.finrank k ↥(Subalgebra.center k (MonoidAlgebra k A))
      ≤ Module.finrank k (ConjClasses A → k) :=
        LinearMap.finrank_le_finrank_of_injective (centerToClassFun_injective (k := k) (A := A))
    _ = Nat.card (ConjClasses A) := by
        rw [Module.finrank_fintype_fun_eq_card, Nat.card_eq_fintype_card]

end Work.NormalComplement.AppVII
