import Mathlib.RingTheory.Henselian
import Mathlib.RingTheory.RegularLocalRing.Defs
import Mathlib.RingTheory.SimpleRing.Principal

namespace Commons.Algebra.Field

open scoped BigOperators

/-- If `φ : ∏ i, A i →ₐ[F] B` is a surjective `F`-algebra homomorphism from a finite product of
fields onto a field `B`, then `B` is `F`-isomorphic to one of the factors `A i`. -/
theorem exists_algEquiv_factor_of_surjective_pi
    {F : Type*} [Field F] {ι : Type*} [Fintype ι] (A : ι → Type*)
    [∀ i, Field (A i)] [∀ i, Algebra F (A i)]
    {B : Type*} [Field B] [Algebra F B]
    (φ : (∀ i, A i) →ₐ[F] B) (hφ : Function.Surjective φ) :
    ∃ i : ι, Nonempty ((A i) ≃ₐ[F] B) := by
  classical
  -- The standard idempotents `e i = Pi.single i 1` of the product.
  -- Each `φ (e i)` is an idempotent of the field `B`, hence is `0` or `1`.
  have hidem : ∀ i, IsIdempotentElem (φ (Pi.single i (1 : A i))) := by
    intro i
    show φ (Pi.single i (1 : A i)) * φ (Pi.single i (1 : A i)) = φ (Pi.single i (1 : A i))
    rw [← map_mul]
    congr 1
    rw [← Pi.single_mul, mul_one]
  have hzo : ∀ i, φ (Pi.single i (1 : A i)) = 0 ∨ φ (Pi.single i (1 : A i)) = 1 :=
    fun i => IsIdempotentElem.iff_eq_zero_or_one.mp (hidem i)
  -- The idempotents sum to `1`.
  have hsum_id : (∑ i, Pi.single i (1 : A i)) = 1 := by
    funext j
    rw [Finset.sum_apply]
    rw [show (∑ i, (Pi.single i (1 : A i)) j)
          = (∑ i, if j = i then (1 : A j) else 0) from
        Finset.sum_congr rfl (fun i _ => by
          by_cases h : j = i
          · rw [if_pos h, h, Pi.single_eq_same]
          · rw [if_neg h, Pi.single_eq_of_ne h (1 : A i)])]
    rw [Finset.sum_ite_eq]
    simp
  have hsum : (∑ i, φ (Pi.single i (1 : A i))) = 1 := by
    rw [← map_sum φ (fun i => Pi.single i (1 : A i)) Finset.univ, hsum_id, map_one]
  -- Hence some `φ (e i)` equals `1`.
  have hexists : ∃ i, φ (Pi.single i (1 : A i)) = 1 := by
    by_contra h
    rw [not_exists] at h
    have hzero : (∑ i, φ (Pi.single i (1 : A i))) = 0 := by
      apply Finset.sum_eq_zero
      intro i _
      rcases hzo i with h0 | h1
      · exact h0
      · exact absurd h1 (h i)
    rw [hsum] at hzero
    exact one_ne_zero hzero
  obtain ⟨i, hi⟩ := hexists
  refine ⟨i, ?_⟩
  -- The `i`-th coordinate inclusion, followed by `φ`.
  let ψ : A i →ₐ[F] B :=
  { toFun := fun a => φ (Pi.single i a)
    map_one' := hi
    map_zero' := by rw [Pi.single_zero, map_zero]
    map_mul' := fun a b => by rw [Pi.single_mul, map_mul]
    map_add' := fun a b => by rw [Pi.single_add, map_add]
    commutes' := fun c => by
      have h1 : Pi.single i (algebraMap F (A i) c)
          = algebraMap F (∀ j, A j) c * Pi.single i (1 : A i) := by
        funext j
        by_cases h : j = i
        · rw [h, Pi.single_eq_same, Pi.mul_apply, Pi.algebraMap_apply, Pi.single_eq_same, mul_one]
        · rw [Pi.single_eq_of_ne h, Pi.mul_apply, Pi.single_eq_of_ne h, mul_zero]
      rw [h1, map_mul, hi, mul_one]
      exact φ.commutes c }
  -- `ψ` is surjective.
  have hsurj : Function.Surjective ψ := by
    intro b
    obtain ⟨x, hx⟩ := hφ b
    refine ⟨x i, ?_⟩
    have hs : Pi.single i (x i) = x * Pi.single i (1 : A i) := by
      funext j
      by_cases h : j = i
      · rw [h, Pi.single_eq_same, Pi.mul_apply, Pi.single_eq_same, mul_one]
      · rw [Pi.single_eq_of_ne h, Pi.mul_apply, Pi.single_eq_of_ne h, mul_zero]
    show φ (Pi.single i (x i)) = b
    rw [hs, map_mul, hi, mul_one, hx]
  exact ⟨AlgEquiv.ofBijective ψ ⟨RingHom.injective (ψ : A i →+* B), hsurj⟩⟩

end Commons.Algebra.Field