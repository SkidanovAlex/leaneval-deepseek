import Mathlib
import Submission.Work.MotV5.Defs
import Submission.Work.MotV.Defs

set_option linter.unusedVariables false -- v435-speed

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

/-!
# The standing hypotheses on the twisted Artin–Schreier action (characteristic `5`)

The characteristic-`5` nodes of `Submission/Work/MotV5` all concern the corrected twist field
`Work.MotV5.asTwistFieldTrue D g τ σS = asTwistFieldFix D τ σS ⊓ asFieldL D g`, the fixed field of
the twisted action `asTwistAction D τ σS = τ.trans (σS.restrictScalars _)` inside `L(E)`.

Two reviewers of the first versions of the nodes `bridge_AS` and `constantsOnly_AS` found that the
hypotheses as then stated (`hτ` and `hσ` only) do **not** determine the twist: with `σS = 1`, or
with `τ` differing from the coefficient action by a geometric automorphism, the field
`asTwistFieldTrue` collapses to `kleinField D = K(E) ≈ RatFunc (𝕜(E))`, a geometrically ruled field
for which both `ConstantsOnly` and the rigidity `IsEmpty (F₁ ≃ₐ[𝕜] F₂)` are false.

`ASTwistData` is the collected hypothesis bundle that excludes those degenerations and under which
the nodes are stated.  Every field is satisfied by the canonical data of the branch:

* `hτ`, provided by `Work.MotV5.coeffAut` (the coefficient action `coeffAction D.E σ` of `σ`);
* `hτk`, likewise: the coefficient action of a `K`-automorphism fixes the geometric part `K(E)`
  (the Klein coordinates have coefficients in `𝕜`);
* `hσ`, provided by `Work.MotV5.asAut_Kb` (the AS generator, `asRoot g ↦ asRoot g + 1`);
* `hσS`, provided by `Work.MotV5.exists_kleinData_shiftProj` (`ASGood D ∧ ShiftCompatProj D`,
  i.e. a genuinely nontrivial fifth-torsion shift `σS κ_i = λ κ_{i+1}`, `λ ≠ 0`);
* `h5`, `hne`, `hpres`: `Work.MotV5.twistedAction_order5` produces `h5` and `hne` from `hτ5`,
  `hcomm` and `hσS`; `hpres` (stability of `asFieldL D g`) is a short computation from the
  shift property of `σS` and `σ (asRoot g) = asRoot g + 1`.
-/

set_option autoImplicit false

namespace Work.MotV5

/-- The standing hypotheses on the twisted Artin–Schreier action `asTwistAction D τ σS` of the
characteristic-`5` branch: `τ` is the coefficient action of `σ` and fixes the geometric part, `σ`
is the Artin–Schreier generator, `σS` is a genuine projective fifth-torsion shift, and the twisted
action `σ' = τ.trans (σS.restrictScalars _)` has order `5`, is nontrivial, and preserves
`L(E) = asFieldL D g`. -/
structure ASTwistData (𝕜 : Type) [Field 𝕜] (D : Work.MotV.KleinData 𝕜) (g : RatFunc 𝕜)
    (τ : Work.MotV.Om D ≃ₐ[RatFunc 𝕜] Work.MotV.Om D)
    (σS : Work.MotV.Om D ≃ₐ[Work.MotV.Kb 𝕜] Work.MotV.Om D)
    (σ : Work.MotV.Kb 𝕜 ≃ₐ[RatFunc 𝕜] Work.MotV.Kb 𝕜) : Prop where
  /-- `τ` acts on the constants `Kb 𝕜` by `σ`. -/
  hτ : ∀ c : Work.MotV.Kb 𝕜,
    τ (algebraMap (Work.MotV.Kb 𝕜) (Work.MotV.Om D) c)
      = algebraMap (Work.MotV.Kb 𝕜) (Work.MotV.Om D) (σ c)
  /-- `τ` fixes the geometric part `K(E) = kleinField D` pointwise. -/
  hτk : ∀ x : Work.MotV.Om D, x ∈ kleinField D → τ x = x
  /-- `σ` is the Artin–Schreier generator on `Kb 𝕜`: `σ (asRoot g) = asRoot g + 1`. -/
  hσ : σ (asRoot g) = asRoot g + 1
  /-- `σS` is the projective fifth-torsion shift `σS κ_i = λ κ_{i+1}`, `λ ≠ 0`. -/
  hσS : Work.MotV5.KleinData.ShiftOf D σS
  /-- the fifth power of the twisted action fixes `L(E) = asFieldL D g` pointwise.

  This is the correct *level-wise* replacement of `(asTwistAction D τ σS) ^ 5 = 1`, which is
  **inconsistent** with `hτ`: `(asTwistAction D τ σS) ^ 5 = 1` forces `σ ^ 5 = 1` on all of
  `Kb 𝕜` (`Work.MotV5.Nodes.sigma_pow_five_eq_one`, proved), and an algebraically closed field of
  characteristic `5` has no nontrivial automorphism of finite order (Artin–Schreier: the fixed field
  of a finite group acting on an algebraically closed field is real closed, hence of
  characteristic `0`).  In the actual datum `σ` has *infinite* order on `Kb 𝕜` (it only satisfies
  `σ (asRoot g) = asRoot g + 1`, so `σ ^ 5` fixes `K(asRoot g)` but not `Kb 𝕜`), while
  `(σ') ^ 5` does fix `L(E) = K(asRoot g)(E)` pointwise.  The twist field
  `asTwistFieldTrue D g τ σS = asTwistFieldFix D τ σS ⊓ asFieldL D g` is the fixed field of the
  *cyclic group* `⟨σ'⟩` inside `L(E)`, which by the order-`5` action on `L(E)` has degree `5`. -/
  h5L : ∀ x ∈ asFieldL D g, ((asTwistAction D τ σS) ^ 5) x = x
  /-- the twisted action is nontrivial on `L(E)`. -/
  hneL : ∃ x ∈ asFieldL D g, asTwistAction D τ σS x ≠ x
  /-- the twisted action preserves `L(E) = asFieldL D g`. -/
  hpres : ∀ x ∈ asFieldL D g, asTwistAction D τ σS x ∈ asFieldL D g

end Work.MotV5
