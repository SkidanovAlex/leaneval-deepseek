import Mathlib
import Submission.Work.BSLit.Wielandt.exists_eq_mul_of_castHom_eq_zero
import Submission.Work.BSLit.Wielandt.exists_eq_algebraMap_mul_of_mapRingHom_eq_zero

-- ftport:v435-opts-begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- ftport:v435-opts-end

namespace Work.BSLit.Wielandt

/-- Membership in the range of the endomorphism `r • 1` of a product of copies of a module is
componentwise: `x` is divisible by `r` (as a function) iff every one of its values is. -/
lemma mem_range_smul_one_pi {R : Type*} [CommSemiring R] {M : Type*} [AddCommMonoid M]
    [Module R M] {ι : Type*} (r : R) (x : ι → M) :
    x ∈ LinearMap.range (r • (1 : (ι → M) →ₗ[R] (ι → M))) ↔
      ∀ i, x i ∈ LinearMap.range (r • (1 : M →ₗ[R] M)) := by
  constructor
  · rintro ⟨y, hy⟩ i
    refine ⟨y i, ?_⟩
    have := congrFun hy i
    simpa using this
  · intro h
    choose y hy using h
    refine ⟨y, ?_⟩
    funext i
    simpa using hy i

/-- Kernel/range description of the reduction for a single monoid algebra element: if `ψ` is a
ring homomorphism whose kernel consists of the multiples of `r` and which kills `r`, then the
kernel of `MonoidAlgebra.mapRingHom M ψ` is the range of multiplication by `r`. -/
lemma mem_range_smul_one_iff_mapRingHom_eq_zero {A : Type*} [CommSemiring A] {B : Type*}
    [Semiring B] {M : Type*} [Monoid M] (ψ : A →+* B) (r : A)
    (hdiv : ∀ a : A, ψ a = 0 → ∃ b : A, a = r * b) (hroot : ψ r = 0)
    (y : MonoidAlgebra A M) :
    y ∈ LinearMap.range (r • (1 : MonoidAlgebra A M →ₗ[A] MonoidAlgebra A M)) ↔
      MonoidAlgebra.mapRingHom M ψ y = 0 := by
  have halg : algebraMap A (MonoidAlgebra A M) r = MonoidAlgebra.single 1 r := by
    have := congrFun (MonoidAlgebra.coe_algebraMap (R := A) (A := A) (M := M)) r
    simpa only [Function.comp_apply, Algebra.algebraMap_self_apply] using this
  constructor
  · rintro ⟨z, hz⟩
    have hy : y = r • z := by rw [← hz]; simp
    rw [hy, Algebra.smul_def, halg, map_mul, MonoidAlgebra.mapRingHom_single, hroot,
      MonoidAlgebra.single_zero, zero_mul]
  · intro hy
    obtain ⟨z, hz⟩ := exists_eq_algebraMap_mul_of_mapRingHom_eq_zero ψ r hdiv y hy
    refine ⟨z, ?_⟩
    have h1 : (r • (1 : MonoidAlgebra A M →ₗ[A] MonoidAlgebra A M)) z = r • z := by simp
    rw [h1, Algebra.smul_def, hz]

theorem ForallMapRingHomEqZero {F : Type*} [Group F] {p k : ℕ} [Fact p.Prime] (hk : 1 ≤ k) {n : ℕ}
    (x : Fin n → MonoidAlgebra (ZMod (p ^ k)) F) :
    (∀ i, MonoidAlgebra.mapRingHom F (ZMod.castHom (dvd_pow_self p (Nat.pos_iff_ne_zero.mp hk)) (ZMod p)) (x i) = 0)
      ↔ x ∈ LinearMap.range ((p : ZMod (p ^ k)) • (1 :
          (Fin n → MonoidAlgebra (ZMod (p ^ k)) F) →ₗ[ZMod (p ^ k)]
          (Fin n → MonoidAlgebra (ZMod (p ^ k)) F))) := by
  have hroot : ZMod.castHom (dvd_pow_self p (Nat.pos_iff_ne_zero.mp hk)) (ZMod p)
      (p : ZMod (p ^ k)) = 0 := by
    have := map_natCast (ZMod.castHom (dvd_pow_self p (Nat.pos_iff_ne_zero.mp hk)) (ZMod p)) p
    rw [this, ZMod.natCast_self]
  have hdiv : ∀ a : ZMod (p ^ k),
      ZMod.castHom (dvd_pow_self p (Nat.pos_iff_ne_zero.mp hk)) (ZMod p) a = 0 →
        ∃ b, a = (p : ZMod (p ^ k)) * b :=
    fun a ha => exists_eq_mul_of_castHom_eq_zero (dvd_pow_self p (Nat.pos_iff_ne_zero.mp hk)) a ha
  rw [mem_range_smul_one_pi]
  simp only [mem_range_smul_one_iff_mapRingHom_eq_zero
    (ZMod.castHom (dvd_pow_self p (Nat.pos_iff_ne_zero.mp hk)) (ZMod p)) (p : ZMod (p ^ k))
    hdiv hroot]

end Work.BSLit.Wielandt
