import Mathlib
import Submission.Work.ProPDeficiency.Specialisations

/-!
# `dim_{𝔽₂} H¹(Γ, 𝔽₂) ≤ d(Γ)` for a finite group

**Namespace** `Work.CFTLib`; module
`Submission.Work.CFTLib.finrank_groupCohomology_one_le_dGens`.

For a finite group `Γ` the `𝔽₂`-dimension of the first group cohomology with trivial
coefficients is at most the minimal number of generators:

`finrank_groupCohomology_one_le_dGens : dim_{𝔽₂} H¹(Γ, 𝔽₂) ≤ dGens Γ`.

This is the elementary half of the dictionary "cohomological bound ⟹ generator count" that the
CFT-consumer files need (`Work.CFTLib.martinet_of_cftlib`): a generating set of `Γ` of minimal
cardinality `dGens Γ` determines every homomorphism `Γ → 𝔽₂`, so there are at most
`2 ^ dGens Γ` of them.

The mathematics is in two steps.

* **Low-degree cohomology.**  For trivial coefficients the inhomogeneous `1`-cocycle identity is
  multiplicativity, so `H¹(Γ, 𝔽₂) ≅ Hom(Γ, 𝔽₂)` as `𝔽₂`-vector spaces.  This is Mathlib's
  `groupCohomology.H1IsoOfIsTrivial` (the isomorphism `H¹(G, A) ≅ (Additive G →+ A)` for a
  trivial representation `A : Rep k G`), transported to a `LinearEquiv` by
  `CategoryTheory.Iso.toLinearEquiv`.  Hence
  `finrank_groupCohomology_one_eq_pHomDim`:
  `dim_{𝔽₂} H¹(Γ, 𝔽₂) = pHomDim 2 Γ`.

* **Counting homs.**  `pHomDim 2 Γ = log₂ #Hom(Γ, 𝔽₂)` by definition, and
  `Work.ProPDeficiency.pHomDim_two_le_dGens` supplies `pHomDim 2 Γ ≤ dGens Γ`
  (the restriction map `Hom(Γ, 𝔽₂) → (S → 𝔽₂)` for a minimal generating set `S` is injective).

The finiteness bookkeeping is where the `Nat.card`/`finrank` interface has to be built by hand:
`AddMonoidHom` carries no `Fintype` instance, so one is installed locally with
`Fintype.ofInjective` (homs are determined by their underlying functions), after which
`Module.card_eq_pow_finrank` gives `#V = 2 ^ dim V` for the `𝔽₂`-module `V = (Additive Γ →+ 𝔽₂)`,
and `AddMonoidHom.toMultiplicativeRight` identifies `#V` with `#Hom(Γ, 𝔽₂)`.
-/

set_option linter.style.haveILetI false

namespace Work.CFTLib

/-- **`dim_{𝔽₂} H¹(Γ, 𝔽₂) = pHomDim 2 Γ`.**

For a finite group `Γ` the first cohomology with trivial `𝔽₂`-coefficients is the dual of the
maximal elementary abelian `2`-quotient of `Γ`, i.e. it has the same `𝔽₂`-dimension as
`Hom(Γ, 𝔽₂)`. -/
theorem finrank_groupCohomology_one_eq_pHomDim (Γ : Type) [Group Γ] [Fintype Γ] :
    Module.finrank (ZMod 2) (groupCohomology (Rep.trivial (ZMod 2) Γ (ZMod 2)) 1) =
      Work.ProPDeficiency.pHomDim 2 Γ := by
  classical
  haveI : Group.FG Γ := Group.fg_of_finite
  -- Step 1: `H¹(Γ, 𝔽₂) ≅ (Additive Γ →+ 𝔽₂)` as `𝔽₂`-vector spaces (trivial coefficients).
  have hfr : Module.finrank (ZMod 2) (groupCohomology (Rep.trivial (ZMod 2) Γ (ZMod 2)) 1) =
      Module.finrank (ZMod 2) (Additive Γ →+ ZMod 2) := by
    let A : Rep (ZMod 2) Γ := Rep.trivial (ZMod 2) Γ (ZMod 2)
    haveI : A.IsTrivial := inferInstance
    exact LinearEquiv.finrank_eq
      (CategoryTheory.Iso.toLinearEquiv (groupCohomology.H1IsoOfIsTrivial A))
  -- Step 2: `V = (Additive Γ →+ 𝔽₂)` is a finite `𝔽₂`-module, and `#V = 2 ^ dim V`.
  haveI : Fintype (Additive Γ →+ ZMod 2) :=
    Fintype.ofInjective (fun f : Additive Γ →+ ZMod 2 => fun a => f a)
      (fun f g h => AddMonoidHom.ext (congrFun h))
  have hcard : Nat.card (Additive Γ →+ ZMod 2) = Nat.card (Work.ProPDeficiency.HomFp 2 Γ) :=
    Nat.card_congr AddMonoidHom.toMultiplicativeRight
  have hpow : Nat.card (Additive Γ →+ ZMod 2) =
      2 ^ Module.finrank (ZMod 2) (Additive Γ →+ ZMod 2) := by
    rw [Nat.card_eq_fintype_card]
    rw [Module.card_eq_pow_finrank (K := ZMod 2) (V := Additive Γ →+ ZMod 2)]
    rw [ZMod.card 2]
  rw [hfr, Work.ProPDeficiency.pHomDim, ← hcard, hpow]
  exact (Nat.log_pow (by norm_num) _).symm

/-- **`dim_{𝔽₂} H¹(Γ, 𝔽₂) ≤ d(Γ)`** for a finite group `Γ`, with trivial `𝔽₂`-coefficients.

A minimal generating set of `Γ` of size `dGens Γ` determines every homomorphism into the abelian
group `𝔽₂`, so `Hom(Γ, 𝔽₂)` has at most `2 ^ dGens Γ` elements; passing to `𝔽₂`-dimensions and
using `H¹(Γ, 𝔽₂) ≅ Hom(Γ, 𝔽₂)` gives the bound. -/
theorem finrank_groupCohomology_one_le_dGens (Γ : Type) [Group Γ] [Fintype Γ] :
    Module.finrank (ZMod 2) (groupCohomology (Rep.trivial (ZMod 2) Γ (ZMod 2)) 1) ≤
      Work.ProPDeficiency.dGens Γ := by
  haveI : Group.FG Γ := Group.fg_of_finite
  rw [finrank_groupCohomology_one_eq_pHomDim]
  exact Work.ProPDeficiency.pHomDim_two_le_dGens

end Work.CFTLib
