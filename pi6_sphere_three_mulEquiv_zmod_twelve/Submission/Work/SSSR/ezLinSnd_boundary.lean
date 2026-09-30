import Mathlib
import Submission.Work.SSSR.ezGen_snd_sum_zero
import Submission.Work.SSSR.KunnethEZ.ez23_eq_ezGen
import Submission.Work.SSSR.iotaF_chainMap
set_option backward.isDefEq.respectTransparency false  -- v435port
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false  -- v435port
set_option backward.isDefEq.respectTransparency.types false  -- v435port

variable {R : Type} [CommRing R] [Nontrivial R]

namespace Work.SSSR

open CategoryTheory CategoryTheory.Limits Simplicial Opposite MonoidalCategory
open scoped MonoidalCategory Simplicial
/-! ## Auxiliary rewrites for the linearised Eilenberg–Zilber boundary formula

The proof of `Work.SSSR.ezLinSnd_boundary` evaluates the two sides of the identity on the
generators `ι_τ` of the `(q+1)`-chains of `Y`.  The following four small lemmas perform that
evaluation: on a generator, `ezLinSnd n q X Y σ` becomes the shuffle chain `ezGen n q X Y σ τ`,
and the differential `d` of `Y` becomes the alternating sum of its faces. -/

/-- On the generators of the chain complex, `ezLinSnd` is the Eilenberg–Zilber shuffle chain,
spelled with `eltHom`: the two are the same morphism up to unfolding `eltHom`. -/
lemma ezLinSnd_ι_eltHom (n q : ℕ) (X Y : SSet) (σ : X _⦋n⦌) (τ : Y _⦋q⦌) :
    Y.ιChainComplex (R := (ezR R)) τ ≫ ezLinSnd n q X Y σ
      = eltHom (Work.SSSR.Cohomology.Crux33.ezGen n q X Y σ τ) :=
  ezLinSnd_ι n q X Y σ τ

end Work.SSSR
