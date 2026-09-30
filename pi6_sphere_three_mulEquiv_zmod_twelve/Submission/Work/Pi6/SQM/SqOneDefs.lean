import Mathlib
import Submission.Work.Pi6.SQM.RedDefs
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false  -- v435port
set_option backward.isDefEq.respectTransparency.types false  -- v435port

/-!
# The Sq-one-injective lemma: the half-coboundary cochain

This file adds to the vocabulary of `Submission/Work/Pi6/SQM/RedDefs.lean` (the `0/1` lift
`liftZ`, the reduction `redC` of cochains and `redChain` of chains) the one cochain on which
`Work.Pi6.SQM.sqOneInjective` rests:

* `deltaHalf X x` — for a mod-2 `2`-cochain `x` with `0/1` lift `x̃ = liftZ X 2 x`, the integral
  `3`-cochain whose value on a `3`-simplex `σ` is `x̃(σ|012) x̃(σ|013) - x̃(σ|123) x̃(σ|023)`.

For a mod-2 **cocycle** `x` one has `δx̃ = 2 · deltaHalf X x` (the coboundary `δx̃` is even and this
is its half, in the exact form `c - b + d - a = 2 (c d - a b)` for `0/1` valued `a b c d` with even
sum), and `deltaHalf X x` reduces mod `2` to the cup-1 square `x ∪₁ x = Sq¹ x`.  The corresponding
statements are `Pi6/SQM/deltaHalfSpec` and `Pi6/SQM/pointwiseSqOne`.
-/

set_option autoImplicit false
set_option maxHeartbeats 1600000
set_option linter.style.haveILetI false
set_option backward.isDefEq.respectTransparency false

open CategoryTheory AlgebraicTopology Simplicial Limits
open scoped Simplicial

namespace Work.Pi6.SQM

noncomputable section

open Work.Cohomology (Cochain genEval cochainDiff cohomologyClassOf)

/-- **The integral `3`-cochain `deltaHalf x`** attached to a mod-2 `2`-cochain `x`: on a
`3`-simplex `σ` it is `x̃(σ|012) x̃(σ|013) - x̃(σ|123) x̃(σ|023)`, where `x̃ = liftZ X 2 x`. -/
noncomputable def deltaHalf (X : SSet) (x : Cochain F2 X 2) : Cochain ℤ X 3 :=
  ((X.isColimitChainComplexXCofan (ModuleCat.of ℤ ℤ) 3).desc
    (Cofan.mk (ModuleCat.of ℤ ℤ)
      (fun σ : X _⦋3⦌ =>
        ModuleCat.ofHom (LinearMap.toSpanSingleton ℤ ℤ
          (genEval ℤ X (liftZ X 2 x) (X.δ 0 σ) * genEval ℤ X (liftZ X 2 x) (X.δ 2 σ)
            - genEval ℤ X (liftZ X 2 x) (X.δ 3 σ)
              * genEval ℤ X (liftZ X 2 x) (X.δ 1 σ)))))).hom

/-- The value of `deltaHalf x` on a simplex. -/
theorem genEval_deltaHalf (X : SSet) (x : Cochain F2 X 2) (σ : X _⦋3⦌) :
    genEval ℤ X (deltaHalf X x) σ =
      genEval ℤ X (liftZ X 2 x) (X.δ 0 σ) * genEval ℤ X (liftZ X 2 x) (X.δ 2 σ)
        - genEval ℤ X (liftZ X 2 x) (X.δ 3 σ) * genEval ℤ X (liftZ X 2 x) (X.δ 1 σ) := by
  have h := Cofan.IsColimit.fac (X.isColimitChainComplexXCofan (ModuleCat.of ℤ ℤ) 3)
    (fun σ : X _⦋3⦌ =>
        ModuleCat.ofHom (LinearMap.toSpanSingleton ℤ ℤ
          (genEval ℤ X (liftZ X 2 x) (X.δ 0 σ) * genEval ℤ X (liftZ X 2 x) (X.δ 2 σ)
            - genEval ℤ X (liftZ X 2 x) (X.δ 3 σ)
              * genEval ℤ X (liftZ X 2 x) (X.δ 1 σ)))) σ
  have h2 := congrArg (fun (g : ModuleCat.of ℤ ℤ ⟶ ModuleCat.of ℤ ℤ) => g.hom 1) h
  simp only [ModuleCat.hom_comp, LinearMap.comp_apply, ModuleCat.hom_ofHom, deltaHalf,
    LinearMap.toSpanSingleton_apply, one_smul, genEval] at h2 ⊢
  exact h2

end

end Work.Pi6.SQM
