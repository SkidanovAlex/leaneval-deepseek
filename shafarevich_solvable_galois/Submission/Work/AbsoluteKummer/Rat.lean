/-
Copyright (c) 2025. All rights reserved.

# The Kummer isomorphism over `ℚ`

For `k = ℚ` and `n = 2` (so that `μ₂ = {±1} ⊆ ℚ`), the Kummer isomorphism of
`Submission/Work/AbsoluteKummer/Kummer.lean` specialises to

`ℚˣ/(ℚˣ)² ≃* H¹(G_ℚ, μ₂)`   (`Work.AbsoluteKummer.kummerEquivRatTwo`),

the arithmetic shadow of the quadratic (degree-`2`) local–global theory of
`Submission/Work/QuadraticLocalGlobal`.
-/
import Submission.Work.AbsoluteKummer.Kummer
import Submission.Work.AbsoluteKummer.Kummer.kummerMap_injective
import Submission.Work.AbsoluteKummer.Kummer.kummerMap_surjective
import Submission.Work.AbsoluteGalois.Basic
-- PORT435-BEGIN (v4.35 isDefEq respectTransparency compat)
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- PORT435-END

namespace Work.AbsoluteKummer

noncomputable section

/-- `-1` is a primitive second root of unity in `ℚ`. -/
theorem isPrimitiveRoot_neg_one_rat : IsPrimitiveRoot (-1 : ℚ) 2 :=
  IsPrimitiveRoot.neg_one (R := ℚ) 0 (by norm_num)

/-- **The Kummer isomorphism for `ℚ` and `μ₂ = {±1}`**: the group `ℚˣ/(ℚˣ)²` of rational square
classes is canonically the first continuous cohomology of `G_ℚ` with coefficients `μ₂`. -/
noncomputable def kummerEquivRatTwo :
    (ℚˣ ⧸ Work.Kummer.nthPowerSubgroup 2 ℚˣ) ≃*
      Multiplicative (H1 (Field.absoluteGaloisGroup ℚ)
        (Additive (rootsOfUnity 2 (AlgebraicClosure ℚ)))) :=
  MulEquiv.ofBijective
    (kummerMap (k := ℚ) (n := 2) (ζ := (-1 : ℚ)) isPrimitiveRoot_neg_one_rat)
    ⟨Kummer.kummerMap_injective isPrimitiveRoot_neg_one_rat,
      Kummer.kummerMap_surjective isPrimitiveRoot_neg_one_rat⟩

/-- The value of the Kummer isomorphism on the class of `x : ℚˣ`: the crossed homomorphism
`σ ↦ σ α/α` for any square root `α` of `x` in `ℚ̄`. -/
theorem kummerEquivRatTwo_mk (x : ℚˣ) :
    kummerEquivRatTwo (QuotientGroup.mk' (Work.Kummer.nthPowerSubgroup 2 ℚˣ) x) =
      Multiplicative.ofAdd (kummerClassFun (k := ℚ) (n := 2) (ζ := (-1 : ℚ))
        isPrimitiveRoot_neg_one_rat x) :=
  kummerMap_mk _ x

/-- **The Kummer isomorphism over `ℚ` in additive form**: `ℚˣ/(ℚˣ)² ≃+ H¹(G_ℚ, μ₂)`. -/
noncomputable def kummerAddEquivRatTwo :
    Additive (ℚˣ ⧸ Work.Kummer.nthPowerSubgroup 2 ℚˣ) ≃+
      H1 (Field.absoluteGaloisGroup ℚ)
        (Additive (rootsOfUnity 2 (AlgebraicClosure ℚ))) :=
  kummerEquivRatTwo.toAdditive

/-- The value of the additive Kummer isomorphism over `ℚ` on the class of `x`. -/
theorem kummerAddEquivRatTwo_apply (x : ℚˣ) :
    kummerAddEquivRatTwo
        (Additive.ofMul (QuotientGroup.mk' (Work.Kummer.nthPowerSubgroup 2 ℚˣ) x)) =
      kummerClassFun (k := ℚ) (n := 2) (ζ := (-1 : ℚ)) isPrimitiveRoot_neg_one_rat x := by
  show Additive.ofMul (kummerEquivRatTwo
    (QuotientGroup.mk' (Work.Kummer.nthPowerSubgroup 2 ℚˣ) x)) = _
  rw [kummerEquivRatTwo_mk]
  rfl

end

end Work.AbsoluteKummer
