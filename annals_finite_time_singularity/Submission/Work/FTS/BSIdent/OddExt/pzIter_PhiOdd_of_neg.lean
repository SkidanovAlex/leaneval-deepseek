import Mathlib.Analysis.Calculus.Deriv.Add
import Mathlib.Analysis.InnerProductSpace.Basic
import Submission.Work.FTS.BSIdent.Defs

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

/-!
# `∂_z²` of the odd extension in `θ`, at `θ < 0`

For `θ < 0` the odd extension `PhiOdd Φ` is in its reflected branch,
`PhiOdd Φ z' θ' τ = -Φ z' (-θ') τ`, and the reflection `θ' ↦ -θ'` *fixes* `z`.  Hence the
`z`-slices of the two families are *equal as functions*, and every `z`-derivative picks up
exactly one sign:

`∂_z^k (PhiOdd Φ · · τ) z θ = -(∂_z^k (Φ · · τ) z (-θ))`.

Only the case `k = 2` is recorded here (`k = 0` is `PhiOdd_of_neg` itself, `k = 1` is the
sibling identity used in `bslOp_PhiOdd_of_neg`).  Since `deriv` is a total function and the two
slices agree *everywhere* (not merely on a germ), no regularity hypothesis on `Φ` is needed.
-/

namespace Work.FTS.BSIdent.OddExt

/-- **`∂_z²` of the odd extension at a negative angle.**  For `θ < 0`,

`∂_z² (PhiOdd Φ · · τ) z θ = -(∂_z² (Φ · · τ) z (-θ))`.

Proof: on `θ' < 0` the reflected branch of `PhiOdd` is `-Φ · (-θ') · τ`, so at the fixed angle
`θ < 0` the two `z`-slices are equal as functions; differentiating the identity
`(fun ζ => PhiOdd Φ ζ θ τ) = fun ζ => -(Φ ζ (-θ) τ)` twice (the reflection in `θ'` does not
touch `z`) yields the claim. -/
theorem pzIter_PhiOdd_of_neg {Φ : Work.FTS.BSIdent.Fam} {z θ τ : ℝ} (hθ : θ < 0) :
    Work.Spaces.pzIter 2 (fun z' θ' => Work.FTS.BSIdent.PhiOdd Φ z' θ' τ) z θ
      = -(Work.Spaces.pzIter 2 (fun z' θ' => Φ z' θ' τ) z (-θ)) := by
  -- at the fixed angle `θ < 0` the two `z`-slices coincide as functions
  have hslice : (fun ζ => Work.FTS.BSIdent.PhiOdd Φ ζ θ τ) = fun ζ => -(Φ ζ (-θ) τ) :=
    funext fun ζ => Work.FTS.BSIdent.PhiOdd_of_neg (not_le.mpr hθ)
  -- hence so do their derivatives, with the sign flipped
  have hslice' : (fun ζ => Work.Spaces.pz (fun z' θ' => Work.FTS.BSIdent.PhiOdd Φ z' θ' τ) ζ θ)
      = fun ζ => -(Work.Spaces.pz (fun z' θ' => Φ z' θ' τ) ζ (-θ)) := by
    funext ζ
    simp only [Work.Spaces.pz]
    rw [hslice]
    exact deriv.neg
  calc Work.Spaces.pzIter 2 (fun z' θ' => Work.FTS.BSIdent.PhiOdd Φ z' θ' τ) z θ
      = deriv (fun ζ => Work.Spaces.pz
          (fun z' θ' => Work.FTS.BSIdent.PhiOdd Φ z' θ' τ) ζ θ) z := rfl
    _ = deriv (fun ζ => -(Work.Spaces.pz (fun z' θ' => Φ z' θ' τ) ζ (-θ))) z := by rw [hslice']
    _ = -deriv (fun ζ => Work.Spaces.pz (fun z' θ' => Φ z' θ' τ) ζ (-θ)) z := deriv.neg
    _ = -(Work.Spaces.pzIter 2 (fun z' θ' => Φ z' θ' τ) z (-θ)) := rfl

end Work.FTS.BSIdent.OddExt
