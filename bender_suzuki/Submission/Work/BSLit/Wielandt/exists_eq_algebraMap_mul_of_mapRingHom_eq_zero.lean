import Mathlib

-- ftport:v435-opts-begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- ftport:v435-opts-end

namespace Work.BSLit.Wielandt

/-- `MonoidAlgebra.mapRingHom` applied to `y` vanishes precisely when the ring homomorphism
annihilates every coefficient of `y`. -/
lemma mapRingHom_eq_zero_iff {A : Type*} [CommSemiring A] {B : Type*} [Semiring B] {M : Type*}
    [Monoid M] (ψ : A →+* B) (y : MonoidAlgebra A M) :
    MonoidAlgebra.mapRingHom M ψ y = 0 ↔ ∀ m : M, ψ (y.coeff m) = 0 := by
  constructor
  · intro hy m
    have h := congrArg (fun t : MonoidAlgebra B M => t.coeff m) hy
    simpa [MonoidAlgebra.coeff_mapRingHom] using h
  · intro h
    apply MonoidAlgebra.coeff_injective
    apply Finsupp.ext
    intro m
    rw [MonoidAlgebra.coeff_mapRingHom]
    simpa using h m

/-- If `r` divides (in the sense of the hypothesis `hdiv`, tested through `ψ`) every element of
`A`, then every element of `A[M]` lying in the kernel of `MonoidAlgebra.mapRingHom M ψ` is
divisible on the left by `algebraMap A A[M] r`. -/
theorem exists_eq_algebraMap_mul_of_mapRingHom_eq_zero {A : Type*} [CommSemiring A] {B : Type*}
    [Semiring B] {M : Type*} [Monoid M] (ψ : A →+* B) (r : A)
    (hdiv : ∀ a : A, ψ a = 0 → ∃ b : A, a = r * b) (y : MonoidAlgebra A M)
    (hy : MonoidAlgebra.mapRingHom M ψ y = 0) :
    ∃ z : MonoidAlgebra A M, y = algebraMap A (MonoidAlgebra A M) r * z := by
  classical
  have hψ : ∀ m : M, ψ (y.coeff m) = 0 := (mapRingHom_eq_zero_iff ψ y).mp hy
  -- For every `m` pick a witness `b m` of divisibility of the coefficient `y.coeff m`
  -- (and `0` when the coefficient is already `0`), so that `y.coeff m = r * b m`.
  let b : M → A := fun m =>
    if y.coeff m = 0 then 0 else Classical.choose (hdiv (y.coeff m) (hψ m))
  have hb : ∀ m, y.coeff m = r * b m := by
    intro m
    by_cases h : y.coeff m = 0
    · simp [b, h]
    · simp only [b, h, ite_false]
      exact Classical.choose_spec (hdiv (y.coeff m) (hψ m))
  have hbsupp : ∀ m, b m ≠ 0 → m ∈ y.coeff.support := by
    intro m hm
    rw [Finsupp.mem_support_iff]
    intro h0
    exact hm (by simp [b, h0])
  let z : MonoidAlgebra A M := MonoidAlgebra.ofCoeff (Finsupp.onFinset y.coeff.support b hbsupp)
  have hz : ∀ m, z.coeff m = b m := fun m => rfl
  refine ⟨z, ?_⟩
  have halg : algebraMap A (MonoidAlgebra A M) r = MonoidAlgebra.single 1 r := by
    have := congrFun (MonoidAlgebra.coe_algebraMap (R := A) (A := A) (M := M)) r
    simpa only [Function.comp_apply, Algebra.algebraMap_self_apply] using this
  rw [halg]
  apply MonoidAlgebra.coeff_injective
  apply Finsupp.ext
  intro m
  rw [MonoidAlgebra.coeff_single_one_mul, hz m]
  exact hb m

end Work.BSLit.Wielandt
