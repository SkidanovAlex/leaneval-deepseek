import Mathlib
import Submission.Work.SSGRoute.ZDataMup.ideleArtin_restrictNormalHom
-- PORT435-BEGIN (v4.35 isDefEq respectTransparency compat)
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- PORT435-END

/-!
# The local factors of the idelic Artin map are compatible in a tower

`Work.SSGRoute.ZDataMup.ideleArtin_restrictNormalHom` (Milne, *CFT*, Lemma 8.4(a)) says that for a
congruence datum `(m, U, hadj)` on `K` the idelic Artin maps of `L/K` and of a normal intermediate
field `↥M` are related by restriction: `proj_M ∘ Φ_L = Φ_M`.

This file records the shape in which the level-`K` pairing lane consumes it: **the local factors
`θ_v := Φ ∘ onePlace_v` are compatible in the tower**, i.e. for every place `v` and every local
element `x ∈ K_vˣ` the restriction to `↥M` of the local factor of `Φ_L` is the local factor of
`Φ_M`:

  `restrictNormalHom M (Φ_L (onePlace v x)) = Φ_M (onePlace v x)`.

This is the λᶜᵃⁿ-free form of "the local scalars `c_v` of the map `Φ` are invariant under passing
to a bigger extension": the scalar `c_v` is the ratio of `θ_v` to the canonical local Artin map
`λ_vᶜᵃⁿ`, and since both the local factors and `λ_vᶜᵃⁿ` are compatible under `proj_M`, the scalars
agree (`c_v(L) = c_v(↥M)` for `↥M ⊆ L`).  Iterating over the compositum `L·M ⊆ LM` of two cyclic
degree-`p` extensions gives the independence of `c_v` from the extension, which is step (a) of
§6 of `SSGRoute/ZConstruction/levelK_pairing_productFormula.lean`.
-/

open scoped NumberField nonZeroDivisors
open NumberField IsDedekindDomain

noncomputable section

namespace Work.SSGRoute.ZDataMup

/-- **The local factors of the idelic Artin map are compatible with restriction to a normal
intermediate field.**  Specialisation of `ideleArtin_restrictNormalHom` (Milne, *CFT*, Lemma
8.4(a)) to the one-place idèles `onePlace v x`. -/
theorem ideleArtin_onePlace_restrictNormalHom
    {K L : Type} [Field K] [NumberField K] [Field L] [NumberField L] [Algebra K L]
    [FiniteDimensional K L] [IsGalois K L]
    (hcomm : ∀ a b : Gal(L/K), a * b = b * a)
    (m : ℕ) (hm : 0 < m)
    (hram : ∀ p : IsDedekindDomain.HeightOneSpectrum (NumberField.RingOfIntegers K),
      (m : NumberField.RingOfIntegers K) ∉ p.asIdeal →
      Ideal.ramificationIdxIn p.asIdeal (NumberField.RingOfIntegers L) = 1)
    (U : Subgroup (NK.GlobalCFT.Idele K))
    (hU : NK.CFTLib.Arl.IsCongruenceSubgroup (K := K) m U)
    (hadj : ∀ x : NK.GlobalCFT.Idele K, ∃ b : Kˣ,
      x * NK.GlobalCFT.Idele.principalIdele K b ∈ U)
    (M : IntermediateField K L) [FiniteDimensional K M] [NumberField ↥M] [Normal K M]
    (hcommM : ∀ a b : Gal(↥M/K), a * b = b * a)
    (v : NK.GlobalCFT.Place K) (x : (NK.GlobalCFT.Place.localField K v)ˣ) :
    AlgEquiv.restrictNormalHom (F := K) (K₁ := L) M
        (NK.CFTLib.Arl.ideleArtin hcomm U hadj (NK.HassePrinciple.onePlace v x))
      = NK.CFTLib.Arl.ideleArtin hcommM U hadj (NK.HassePrinciple.onePlace v x) :=
  ideleArtin_restrictNormalHom (K := K) (L := L) hcomm m hm hram U hU hadj M hcommM
    (NK.HassePrinciple.onePlace v x)

end Work.SSGRoute.ZDataMup
