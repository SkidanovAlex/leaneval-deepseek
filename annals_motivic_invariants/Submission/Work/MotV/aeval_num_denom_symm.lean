import Mathlib

set_option linter.unusedVariables false -- v435-speed

namespace Work.MotV

/-- Compatibility of `Polynomial.aeval` with a `𝕜`-algebra equivalence of `RatFunc 𝕜`:
substituting `RatFunc.X` by `β RatFunc.X` commutes with `β` applied to polynomials
(seen inside `RatFunc 𝕜` via `algebraMap`). -/
private lemma aeval_algEquiv_apply (𝕜 : Type*) [Field 𝕜] (β : RatFunc 𝕜 ≃ₐ[𝕜] RatFunc 𝕜)
    (p : Polynomial 𝕜) :
    β ((algebraMap (Polynomial 𝕜) (RatFunc 𝕜)) p) = p.aeval (β RatFunc.X) := by
  -- `aeval RatFunc.X` is the structure map `𝕜[X] → RatFunc 𝕜`
  have key : ∀ q : Polynomial 𝕜,
      (Polynomial.aeval (RatFunc.X : RatFunc 𝕜)) q = (algebraMap (Polynomial 𝕜) (RatFunc 𝕜)) q := by
    intro q
    rw [show RatFunc.X = (algebraMap (Polynomial 𝕜) (RatFunc 𝕜)) Polynomial.X from rfl]
    rw [Polynomial.aeval_algebraMap_apply (RatFunc 𝕜) Polynomial.X q]
    simp
  rw [← key p]
  exact (Polynomial.aeval_algHom_apply β RatFunc.X p).symm

/-- If `β` is a `𝕜`-algebra automorphism of `RatFunc 𝕜` and `g := β.symm RatFunc.X`, then the
numerator of `g`, evaluated at `β RatFunc.X` (i.e. `X` after the substitution `β`), equals `X`
times the corresponding evaluation of the denominator.  Equivalently, `X` is the value of `g`
after substituting `X ↦ β RatFunc.X`, written as the reduced fraction `num g / denom g`. -/
theorem aeval_num_denom_symm (𝕜 : Type*) [Field 𝕜] (β : RatFunc 𝕜 ≃ₐ[𝕜] RatFunc 𝕜) :
    RatFunc.X * ((β.symm RatFunc.X).denom.aeval (β RatFunc.X))
      = (β.symm RatFunc.X).num.aeval (β RatFunc.X) := by
  set g := β.symm RatFunc.X with hg
  have hβg : β g = RatFunc.X := by rw [hg]; exact β.apply_symm_apply RatFunc.X
  -- the denominator stays nonzero after substitution
  have hb : β ((algebraMap (Polynomial 𝕜) (RatFunc 𝕜)) g.denom) ≠ 0 := by
    rw [ne_eq, map_eq_zero_iff β β.injective]
    simpa using (RatFunc.algebraMap_injective 𝕜).ne (RatFunc.denom_ne_zero g)
  -- `X = β (num g) / β (denom g)`
  have h2 : β ((algebraMap (Polynomial 𝕜) (RatFunc 𝕜)) g.num)
        / β ((algebraMap (Polynomial 𝕜) (RatFunc 𝕜)) g.denom) = RatFunc.X := by
    rw [← map_div₀ β, RatFunc.num_div_denom g, hβg]
  -- clear denominators
  have h3 : β ((algebraMap (Polynomial 𝕜) (RatFunc 𝕜)) g.num)
      = RatFunc.X * β ((algebraMap (Polynomial 𝕜) (RatFunc 𝕜)) g.denom) :=
    (div_eq_iff hb).mp h2
  rw [aeval_algEquiv_apply 𝕜 β g.num, aeval_algEquiv_apply 𝕜 β g.denom] at h3
  exact h3.symm

end Work.MotV
