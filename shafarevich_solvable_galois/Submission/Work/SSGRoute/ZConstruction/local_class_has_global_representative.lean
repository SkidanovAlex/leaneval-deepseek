import Mathlib.RingTheory.Henselian
import Mathlib.RingTheory.DedekindDomain.AdicValuation
import Mathlib.RingTheory.Flat.TorsionFree
import Mathlib.RingTheory.RegularLocalRing.Defs
import Mathlib.RingTheory.SimpleRing.Principal
import Submission.Work.SSGRoute.ZConstruction.levelK_kummerCharHom_dictionary
import Submission.Work.SSGRoute.adicCompletion_units_mul_pow
-- PORT435-BEGIN (v4.35 isDefEq respectTransparency compat)
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- PORT435-END

/-!
# Local `p`-th power classes have global representatives

The surjectivity half of the level-`K` local Kummer isomorphism: the localisation
`Kˣ → κˣ ⧸ (κˣ)^p` (`κ = 𝔭.adicCompletion ↥K`) is **surjective** — every local `p`-th power class
has a global representative in `Kˣ`.  This is weak approximation (density of `↥K` in its completion,
so a given local unit can be approximated by a global element, the quotient being then a deep
principal unit, hence a `p`-th power).

It is the existing proved theorem `Work.SSGRoute.adicCompletion_units_mul_pow`
(`Submission/Work/SSGRoute/adicCompletion_units_mul_pow.lean`, axiom-clean) at `K := ↥K`, recorded
here in the `ZConstruction` vocabulary next to the Kummer map
`Work.SSGRoute.ZConstruction.kummerCharHom`, whose kernel (`kummerCharHom_eq_one_iff`) is exactly the
subgroup of local `p`-th powers.  Together: `Kˣ ⧸ N_𝔭 ≅ κˣ ⧸ (κˣ)^p`, and hence, combining with the
Kummer map `Kˣ → ↥(lcHoms p ↥(decomp (k := ↥K) A))` -- additive, killing `p`-th powers, kernel `N_𝔭`
-- and the cardinality count `|lcHoms p ↥(decomp A)| = |κˣ ⧸ (κˣ)^p|` (transport of
`PTembedding.lcHoms_localUnits` along the level-`K` local Galois identification, via
`Work.SSGRoute.ZConstruction.natCard_lcHoms_congr` and
`Work.SSGRoute.ZConstruction.localGaloisEquiv_decomp`), the Kummer map is *bijective*: the level-`K`
local Kummer isomorphism `K_𝔭ˣ ⧸ (K_𝔭ˣ)^p ≅ H1loc p k Ω K (ZMod p) (decomp k A ⊓ K.fixingSubgroup)`.

Beware the name: `Kˣ` is the unit group of the *field* `↥K`, i.e. `↥K \ {0}`, not the group of units
of `𝓞 K` (for integral global units the statement is false).
-/

open scoped Pointwise

namespace Work.SSGRoute.ZConstruction

open _root_.SSGRoute

/-- **Every local `p`-th power class is represented by a global element.** -/
theorem exists_globalUnit_mul_pow_eq_of_local
    (p : ℕ) [Fact p.Prime] (k Ω : Type) [Field k] [NumberField k] [Field Ω] [Algebra k Ω]
    [IsAlgClosure k Ω]
    (K : IntermediateField k Ω) [FiniteDimensional k K] [IsGalois k K] [NumberField ↥K]
    (𝔭 : IsDedekindDomain.HeightOneSpectrum (NumberField.RingOfIntegers ↥K))
    (a : (𝔭.adicCompletion ↥K)ˣ) :
    ∃ (β : Kˣ) (γ : (𝔭.adicCompletion ↥K)ˣ),
      Units.map (algebraMap ↥K (𝔭.adicCompletion ↥K)) β * γ ^ p = a :=
  SSGRoute.adicCompletion_units_mul_pow ↥K 𝔭 p a

end Work.SSGRoute.ZConstruction
