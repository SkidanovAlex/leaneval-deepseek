/-
Copyright (c) 2025. All rights reserved.

# The Kummer isomorphism (packaged)

The two halves proved in `Submission/Work/AbsoluteKummer/Kummer/` assemble into the headline
statement of this chapter: for a field `k` and `n > 0` with a primitive `n`-th root of unity
`ζ ∈ k`,

`kˣ/(kˣ)^n ≃* H¹(G_k, μ_n)`   (`Work.AbsoluteKummer.kummerEquiv`),

the class of `x : kˣ` corresponding to the crossed homomorphism `σ ↦ σ α/α` for any `n`-th root
`α ∈ k̄ˣ` of `x` (`Work.AbsoluteKummer.kummerEquiv_mk`).
-/
import Submission.Work.AbsoluteKummer.Kummer
import Submission.Work.AbsoluteKummer.Kummer.kummerMap_injective
import Submission.Work.AbsoluteKummer.Kummer.kummerMap_surjective
-- PORT435-BEGIN (v4.35 isDefEq respectTransparency compat)
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- PORT435-END

namespace Work.AbsoluteKummer

noncomputable section

variable {k : Type*} [Field k] [IsGalois k (AlgebraicClosure k)] {n : ℕ} [NeZero n] {ζ : k}

/-- **The Kummer isomorphism**: the group `kˣ/(kˣ)^n` of `n`-th power classes is canonically the
first continuous cohomology of `G_k` with coefficients `μ_n`. -/
noncomputable def kummerEquiv (hζ : IsPrimitiveRoot ζ n) :
    (kˣ ⧸ Work.Kummer.nthPowerSubgroup n kˣ) ≃*
      Multiplicative (H1 (G k) (Additive (rootsOfUnity n (AlgebraicClosure k)))) :=
  MulEquiv.ofBijective (kummerMap hζ)
    ⟨Kummer.kummerMap_injective hζ, Kummer.kummerMap_surjective hζ⟩

/-- `kummerMap` is bijective: the Kummer map "is" the Kummer isomorphism. -/
theorem kummerMap_bijective (hζ : IsPrimitiveRoot ζ n) :
    Function.Bijective (kummerMap hζ) :=
  ⟨Kummer.kummerMap_injective hζ, Kummer.kummerMap_surjective hζ⟩

/-- The class of `x : kˣ` under the Kummer isomorphism is the class of the crossed homomorphism
`σ ↦ σ α/α`, for any `n`-th root `α` of `x` in `k̄ˣ`. -/
theorem kummerEquiv_mk (hζ : IsPrimitiveRoot ζ n) (x : kˣ) :
    kummerEquiv hζ (QuotientGroup.mk' (Work.Kummer.nthPowerSubgroup n kˣ) x) =
      Multiplicative.ofAdd (kummerClassFun hζ x) :=
  kummerMap_mk hζ x

/-- **The Kummer isomorphism, in additive form**: `kˣ/(kˣ)^n ≃+ H¹(G_k, μ_n)`, with the
codomain written as the additive group `H¹(G_k, μ_n)` rather than as `Multiplicative (H¹ ...)`.
It is `(kummerEquiv hζ).toAdditive`. -/
noncomputable def kummerAddEquiv (hζ : IsPrimitiveRoot ζ n) :
    (Additive (kˣ ⧸ Work.Kummer.nthPowerSubgroup n kˣ)) ≃+
      H1 (G k) (Additive (rootsOfUnity n (AlgebraicClosure k))) :=
  (kummerEquiv hζ).toAdditive

/-- The additive form of the Kummer isomorphism on the class of `x : kˣ`. -/
theorem kummerAddEquiv_apply (hζ : IsPrimitiveRoot ζ n) (x : kˣ) :
    kummerAddEquiv hζ (Additive.ofMul (QuotientGroup.mk' (Work.Kummer.nthPowerSubgroup n kˣ) x)) =
      kummerClassFun hζ x := by
  show Additive.ofMul ((kummerEquiv hζ)
    (QuotientGroup.mk' (Work.Kummer.nthPowerSubgroup n kˣ) x)) = kummerClassFun hζ x
  rw [kummerEquiv_mk hζ x]
  rfl

end

end Work.AbsoluteKummer
