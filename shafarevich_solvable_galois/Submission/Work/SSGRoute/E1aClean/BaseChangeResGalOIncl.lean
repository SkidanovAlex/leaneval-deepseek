import Submission.Work.SSGRoute.E1aClean.BaseChangeConj
-- PORT435-BEGIN (v4.35 isDefEq respectTransparency compat)
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- PORT435-END

/-! # `res_galOIncl`: the restriction-map identity, stated up to the conjugation

The original failure (`NOTE_levelChangeRoute.md` §2g(3)) was that
`SSGRoute.res k K (galOIncl L σ)` and `SSGRoute.res ↥L (Kover L) σ` live in the *non-defeq* groups
`Gal(↥K/k)` and `Gal(↥(Kover L)/↥L)`.  Two identifications fix that: the conjugation `galKConj L`
(between `Gal(↥K/↥L)` and `Gal(↥(Kover L)/↥L)`) and the inclusion `galKIncl L`
(`Gal(↥K/↥L) →* Gal(↥K/k)`).  Composing them makes the two sides comparable, and — as with every
other step of this corner — all obligations are memberwise, hence `rfl`. -/

namespace Work.SSGRoute.E1aClean

open CategoryTheory SSGRoute.PTExt

noncomputable section

variable {k : Type} [Field k] {Ω : Type} [Field Ω] [Algebra k Ω]
variable {K : IntermediateField k Ω} [FiniteDimensional k K] [IsGalois k K]

/-- **The restriction-map identity of the `hM`/`hN` step.**  Restricting a `k`-linear automorphism
of `Ω` to `K` (right-hand side) agrees with first restricting it to the base-changed top field and
then comparing groups (left-hand side). -/
theorem res_galOIncl (L : IntermediateField k K)
    [FiniteDimensional ↥L (Kover L)] [IsGalois ↥L (Kover L)] (σ : Ω ≃ₐ[↥L] Ω) :
    galKIncl L ((galKConj L).symm (SSGRoute.res ↥L (Kover L) σ))
      = SSGRoute.res k K (galOIncl L σ) :=
  AlgEquiv.ext fun _ => rfl

end

end Work.SSGRoute.E1aClean
