import Mathlib
import Submission.Work.MotT.T4Setup
import Submission.Work.MotT.AM2_descent

set_option linter.unusedVariables false -- v435-speed

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

namespace Work.MotT

/-! ## An elementary field-automorphism lemma

If an `L`-algebra automorphism `f` of a field `F` scales an element `x` by a constant `a ∈ L`, say
`f x = a · x`, then the *inverse* automorphism scales `x` by the inverse constant:
`f⁻¹ x = a⁻¹ · x`.  (If `a = 0` then `f x = 0`, so `x = 0` by injectivity and both sides vanish.)

This is the arithmetic content of `transAlgEquiv_neg_ratio`: for a translation `τ_A` of the
function field of an elliptic curve, the translation `τ_{-A}` acts by `(τ_A)⁻¹`, so it scales the
Klein ratios by the inverse of the character of `τ_A`. -/
theorem algEquiv_inv_apply_of_apply_eq_smul {F L : Type*} [Field F] [Field L] [Algebra L F]
    (f : F ≃ₐ[L] F) (a : L) (x : F) (h : f x = algebraMap L F a * x) :
    f⁻¹ x = (algebraMap L F a)⁻¹ * x := by
  change f.symm x = (algebraMap L F a)⁻¹ * x
  by_cases ha : a = 0
  · subst ha
    simp only [map_zero, zero_mul] at h ⊢
    have hx : x = 0 := f.injective (by simpa using h)
    rw [hx, map_zero, inv_zero, zero_mul]
  · have hane : algebraMap L F a ≠ 0 := (map_ne_zero (algebraMap L F)).mpr ha
    apply f.injective
    rw [map_mul, map_inv₀, AlgEquiv.commutes, h, ← mul_assoc, inv_mul_cancel₀ hane, one_mul,
      AlgEquiv.apply_symm_apply]

theorem transAlgEquiv_neg_ratio {K : Type} [Field K] (D : Work.MotV.KleinData K)
    (h₁ h₂ : K) (hk : ringChar K ≠ 5)
    [instDec : DecidableEq ↥(KummerField2 K h₁ h₂ hk)]
    [instEll : (D.E.baseChange ↥(KummerField2 K h₁ h₂ hk)).IsElliptic]
    (A : (D.E.baseChange ↥(KummerField2 K h₁ h₂ hk)).toAffine.Point)
    (c : ↥(KummerField2 K h₁ h₂ hk))
    (hA : ∀ i : Fin 5,
      Work.MotC2.transAlgEquiv (D.E.baseChange ↥(KummerField2 K h₁ h₂ hk)) A
          (Work.MotV.kleinCoord D ↥(KummerField2 K h₁ h₂ hk) i /
            Work.MotV.kleinCoord D ↥(KummerField2 K h₁ h₂ hk) 0) =
        (algebraMap ↥(KummerField2 K h₁ h₂ hk) (ML2 D h₁ h₂ hk) c) ^ (i : ℕ) *
          (Work.MotV.kleinCoord D ↥(KummerField2 K h₁ h₂ hk) i /
            Work.MotV.kleinCoord D ↥(KummerField2 K h₁ h₂ hk) 0)) :
    ∀ i : Fin 5,
      Work.MotC2.transAlgEquiv (D.E.baseChange ↥(KummerField2 K h₁ h₂ hk)) (-A)
          (Work.MotV.kleinCoord D ↥(KummerField2 K h₁ h₂ hk) i /
            Work.MotV.kleinCoord D ↥(KummerField2 K h₁ h₂ hk) 0) =
        ((algebraMap ↥(KummerField2 K h₁ h₂ hk) (ML2 D h₁ h₂ hk) c) ^ (i : ℕ))⁻¹ *
          (Work.MotV.kleinCoord D ↥(KummerField2 K h₁ h₂ hk) i /
            Work.MotV.kleinCoord D ↥(KummerField2 K h₁ h₂ hk) 0) := by
  intro i
  -- The translation `τ_{-A}` is the inverse of `τ_A`, since `τ` is an additive-to-multiplicative
  -- homomorphism and `A + (-A) = 0`.
  have hneg : Work.MotC2.transAlgEquiv (D.E.baseChange ↥(KummerField2 K h₁ h₂ hk)) (-A)
      = (Work.MotC2.transAlgEquiv (D.E.baseChange ↥(KummerField2 K h₁ h₂ hk)) A)⁻¹ := by
    have h := Work.MotC2.transAlgEquiv_add (D.E.baseChange ↥(KummerField2 K h₁ h₂ hk)) A (-A)
    rw [add_neg_cancel, Work.MotC2.transAlgEquiv_zero] at h
    exact eq_inv_of_mul_eq_one_right h.symm
  rw [hneg]
  -- The scaling constant is `(algebraMap c)^i = algebraMap (c^i)`; apply the field-automorphism
  -- lemma to the hypothesis `hA i`.
  rw [← map_pow (algebraMap ↥(KummerField2 K h₁ h₂ hk) (ML2 D h₁ h₂ hk)) c (i : ℕ)]
  exact algEquiv_inv_apply_of_apply_eq_smul _ (c ^ (i : ℕ)) _
    (by rw [map_pow]; exact hA i)

end Work.MotT
