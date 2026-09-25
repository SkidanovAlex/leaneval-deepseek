import Mathlib
import Submission.Work.QuadraticFields.QuadField

/-!
# When is the quadratic field `ℚ(√a)` totally real?

The quadratic field `ℚ(√a)` attached to a rational number `a` (see
`Work.QuadraticFields.quadField`) is totally real exactly when `a ≥ 0`.

The two directions are proved in quite different ways.

* If `a ≥ 0`, then every complex embedding `φ` of `ℚ(√a)` sends the generator `√a`
  to a square root of the *nonnegative* rational number `a`, hence to a real number;
  since `ℚ(√a)` is generated over `ℚ` by `√a`, the embedding `φ` is automatically
  real (`IsReal` is a property of the ring hom `φ`, so it suffices to compare the
  two `ℚ`-algebra maps `φ` and its conjugate on the generator).

* If `ℚ(√a)` is totally real, pick any real infinite place `v` and let `ψ : ℚ(√a) →+* ℝ`
  be the associated real embedding.  Applying `ψ` to `√a ^ 2 = a` gives
  `ψ(√a) ^ 2 = a`, a square in `ℝ`, whence `a ≥ 0`.

## Main results

* `complexEmbedding_isReal_quadField`
* `isTotallyReal_quadField_of_nonneg`
* `nonneg_of_isTotallyReal_quadField`
* `isTotallyReal_quadField_iff`
-/

namespace Work.QuadraticFields

open NumberField

set_option autoImplicit false

noncomputable section

/-- If a complex number `z` has square the (image of a) nonnegative rational number `a`,
then `z` is real. -/
theorem star_eq_self_of_sq_eq_ofReal {a : ℚ} (ha : 0 ≤ a) {z : ℂ}
    (hz : z ^ 2 = ((a : ℝ) : ℂ)) : star z = z := by
  have ha' : (0 : ℝ) ≤ (a : ℝ) := by exact_mod_cast ha
  have hz' : z ^ 2 = ((Real.sqrt (a : ℝ) : ℝ) : ℂ) ^ 2 := by
    rw [hz, ← Complex.ofReal_pow, Real.sq_sqrt ha']
  have h2 : (z - ((Real.sqrt (a : ℝ) : ℝ) : ℂ)) *
      (z + ((Real.sqrt (a : ℝ) : ℝ) : ℂ)) = 0 := by
    linear_combination hz'
  rcases mul_eq_zero.mp h2 with h3 | h3
  · have hz0 : z = ((Real.sqrt (a : ℝ) : ℝ) : ℂ) := sub_eq_zero.mp h3
    rw [hz0]
    exact Complex.conj_ofReal _
  · have hz0 : z = -((Real.sqrt (a : ℝ) : ℝ) : ℂ) := add_eq_zero_iff_eq_neg.mp h3
    rw [hz0]
    simp

/-- The generator `√a` of `ℚ(√a)` squares to `a`, for any proof of membership of `√a`
in `ℚ(√a)`. -/
theorem quadField_sqrtVal_sq (a : ℚ) (hx : sqrtVal a ∈ quadField a) :
    (⟨sqrtVal a, hx⟩ : ↥(quadField a)) ^ 2 = (a : ↥(quadField a)) := by
  apply Subtype.ext
  show (sqrtVal a : AlgebraicClosure ℚ) ^ 2 = ((a : ↥(quadField a)) : AlgebraicClosure ℚ)
  rw [sqrtVal_sq]
  rfl

/-- Every complex embedding of `ℚ(√a)` is real when `a ≥ 0`. -/
theorem complexEmbedding_isReal_quadField (a : ℚ) (ha : 0 ≤ a)
    (φ : ↥(quadField a) →+* ℂ) : ComplexEmbedding.IsReal φ := by
  rw [ComplexEmbedding.isReal_iff]
  have key : ∀ hx : sqrtVal a ∈ quadField a,
      star (φ ⟨sqrtVal a, hx⟩) = φ ⟨sqrtVal a, hx⟩ := by
    intro hx
    have h2 : φ ((a : ↥(quadField a))) = ((a : ℝ) : ℂ) := by
      rw [map_ratCast φ a]
      norm_num
    have h3 : φ (⟨sqrtVal a, hx⟩ : ↥(quadField a)) ^ 2 = ((a : ℝ) : ℂ) := by
      rw [← map_pow, quadField_sqrtVal_sq a hx, h2]
    exact star_eq_self_of_sq_eq_ofReal ha h3
  have h := IntermediateField.adjoin_algHom_ext (F := ℚ)
    (s := ({sqrtVal a} : Set (AlgebraicClosure ℚ)))
    (φ₁ := (star φ).toRatAlgHom) (φ₂ := φ.toRatAlgHom) ?_
  · have h2 : ((star φ).toRatAlgHom : ↥(quadField a) →+* ℂ) =
        (φ.toRatAlgHom : ↥(quadField a) →+* ℂ) := congrArg AlgHom.toRingHom h
    rwa [RingHom.toRatAlgHom_toRingHom] at h2
  · intro x hx
    rw [Set.mem_singleton_iff] at hx
    subst hx
    exact key _

/-- `ℚ(√a)` is totally real when `a ≥ 0`. -/
theorem isTotallyReal_quadField_of_nonneg (a : ℚ) (ha : 0 ≤ a) :
    NumberField.IsTotallyReal ↥(quadField a) :=
  ⟨fun v => InfinitePlace.isReal_iff.mpr (complexEmbedding_isReal_quadField a ha v.embedding)⟩

/-- If `ℚ(√a)` is totally real then `a ≥ 0`. -/
theorem nonneg_of_isTotallyReal_quadField (a : ℚ)
    (h : NumberField.IsTotallyReal ↥(quadField a)) : 0 ≤ a := by
  obtain ⟨v⟩ := (inferInstance : Nonempty (InfinitePlace ↥(quadField a)))
  have hvreal : v.IsReal := @IsTotallyReal.isReal _ _ h v
  let ψ : ↥(quadField a) →+* ℝ :=
    ComplexEmbedding.IsReal.embedding (InfinitePlace.isReal_iff.mp hvreal)
  have h1 : ψ (⟨sqrtVal a, sqrtVal_mem_quadField a⟩ : ↥(quadField a)) ^ 2 = (a : ℝ) := by
    rw [← map_pow, quadField_sqrtVal_sq a (sqrtVal_mem_quadField a), map_ratCast ψ a]
  have h2 : (0 : ℝ) ≤ (a : ℝ) := by
    have := sq_nonneg (ψ (⟨sqrtVal a, sqrtVal_mem_quadField a⟩ : ↥(quadField a)))
    linarith
  exact_mod_cast h2

theorem isTotallyReal_quadField_iff (a : ℚ) :
    NumberField.IsTotallyReal ↥(quadField a) ↔ 0 ≤ a :=
  ⟨nonneg_of_isTotallyReal_quadField a, isTotallyReal_quadField_of_nonneg a⟩

end

end Work.QuadraticFields
