import Mathlib

set_option linter.unusedVariables false -- v435-speed

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

open scoped IntermediateField

namespace Work.MotC

/-- A rational function over a field `M` which is algebraic over `M` is constant:
the base field is algebraically closed in the rational function field `M(X)`.
This is because `M(X)/M` is a purely transcendental extension of transcendence
degree one: as soon as `M⟮r⟯ ≠ M`, the intermediate field `M(r)` is a nontrivial
intermediate field of `M(X)`, so `X` is algebraic over `M(r)`
(`RatFunc.IntermediateField.isAlgebraic_X`); transitivity of algebraicity would
then make `X` algebraic over `M`, contradicting `RatFunc.transcendental_X`. -/
theorem ratFunc_eq_C_of_isAlgebraic {M : Type*} [Field M] (r : RatFunc M) (hr : IsAlgebraic M r) :
    ∃ m : M, r = algebraMap M (RatFunc M) m := by
  by_contra h
  -- If `r` were not constant, `M⟮r⟯ = M(r)` would be a nontrivial intermediate field.
  have hne : IntermediateField.adjoin M {r} ≠ ⊥ := by
    intro hb
    apply h
    have hb' : (M⟮r⟯ : IntermediateField M (RatFunc M)) = ⊥ := hb
    have hmem : r ∈ (⊥ : IntermediateField M (RatFunc M)) :=
      IntermediateField.adjoin_simple_eq_bot_iff.mp hb'
    obtain ⟨m, hm⟩ := IntermediateField.mem_bot.mp hmem
    exact ⟨m, hm.symm⟩
  -- `M(r)/M` is algebraic since `r` is algebraic over `M`.
  have halg : Algebra.IsAlgebraic M (IntermediateField.adjoin M {r}) :=
    (IntermediateField.isAlgebraic_adjoin_iff_isAlgebraic M (RatFunc M) (S := {r})).mpr
      (fun x hx => by rw [Set.mem_singleton_iff] at hx; subst hx; exact hr)
  -- A nontrivial intermediate field of `M(X)` makes `X` algebraic over it.
  have hEX : IsAlgebraic (IntermediateField.adjoin M {r}) (RatFunc.X : RatFunc M) :=
    RatFunc.IntermediateField.isAlgebraic_X hne
  -- Transitivity of algebraicity contradicts transcendence of `X` over `M`.
  have : Algebra.IsAlgebraic M (IntermediateField.adjoin M {r}) := halg
  exact RatFunc.transcendental_X (IsAlgebraic.restrictScalars M hEX)

end Work.MotC
