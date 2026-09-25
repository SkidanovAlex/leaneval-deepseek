import Mathlib
import Submission.Work.QuadraticFields.CertificateRealSummary

/-!
# Every `ℚ`-automorphism of the multiquadratic field `gsM` has order dividing `2`

`gsM = ℚ(√5, √13, √17, √29, √37, √41, √53)` is a multiquadratic field: it is generated over `ℚ`
by the seven square roots `gsRoot a` (`a ∈ gsPrimes`), each satisfying `gsRoot a ^ 2 = a`.  Any
`ℚ`-algebra automorphism `σ` of `gsM` therefore sends each generator `gsRoot a` to a square root
of `a`, i.e. to `± gsRoot a` (`sq_eq_sq_iff_eq_or_eq_neg`), and hence fixes `σ (gsRoot a)`; as the
generators generate `gsM` as a `ℚ`-algebra (`gsRoot_generates`), `σ * σ = 1`.

No arithmetic of the seven primes is used: the argument applies to every multiquadratic field.

## Main result

* `Work.WingbergRoute.gsM_aut_exp_two`.
-/

open Work.QuadraticFields

namespace Work.WingbergRoute

noncomputable section

/-- In a multiquadratic field the square-roots generating it are sent to `±` themselves by every
`ℚ`-automorphism, so the automorphism squares to the identity. -/
theorem gsM_aut_exp_two (σ : Work.QuadraticFields.gsM ≃ₐ[ℚ] Work.QuadraticFields.gsM) :
    σ * σ = 1 := by
  -- `gsM` is generated over `ℚ` by the seven square roots `gsRoot a`, `a ∈ gsPrimes`.
  have hgen : Algebra.adjoin ℚ (gsRoot '' (gsPrimes : Set ℤ)) = ⊤ := by
    rw [← IntermediateField.adjoin_eq_top_iff]
    exact gsRoot_generates
  refine AlgEquiv.ext (fun x => ?_)
  rw [AlgEquiv.mul_apply, AlgEquiv.one_apply]
  have hx : x ∈ Algebra.adjoin ℚ (gsRoot '' (gsPrimes : Set ℤ)) := by rw [hgen]; trivial
  -- It suffices to check `σ (σ x) = x` on the generators, `algebraMap` and under `+`, `*`.
  refine Algebra.adjoin_induction (p := fun y _ => σ (σ y) = y) ?_ ?_ ?_ ?_ hx
  · rintro y ⟨a, ha, rfl⟩
    -- `σ (gsRoot a)` is again a square root of `a`, hence `± gsRoot a` ...
    have h1 : σ ((gsRoot a) ^ 2) = (gsRoot a) ^ 2 := by
      rw [gsRoot_sq a ha, AlgEquiv.commutes σ (a : ℚ), ← gsRoot_sq a ha]
    have hsq : (σ (gsRoot a)) ^ 2 = (gsRoot a) ^ 2 := by simpa only [map_pow] using h1
    -- ... so `σ` fixes `σ (gsRoot a)`.
    rcases sq_eq_sq_iff_eq_or_eq_neg.mp hsq with h | h
    · rw [h, h]
    · rw [h, map_neg, h, neg_neg]
  · intro r
    rw [AlgEquiv.commutes, AlgEquiv.commutes]
  · intro y z _ _ hy hz
    rw [map_add, map_add, hy, hz]
  · intro y z _ _ hy hz
    rw [map_mul, map_mul, hy, hz]

end

end Work.WingbergRoute
