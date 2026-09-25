import Mathlib
import Submission.NK.CFTLib.HR.transferOnePlace

/-!
# The one-place descent step of the Brauer transfer (`transferOnePlace`)

This module is the interface of the "one-place" Brauer descent of Hilbert reciprocity (Milne,
*CFT*, VII §8, Lemma 8.5 + Proposition 7.2 + Lemma 8.6 for a single pair of cyclic levels), in the
*local norm subgroup* vocabulary of the workspace.

The mathematical content is the transfer argument.  Let `K ⊆ L, M ⊆ E` be number fields with
`E = L·M` (`hgen`) and `L/K`, `M/K` cyclic; let `x ∈ Kˣ` and let `v₀` be a place of `K`.

* `hx` says that `x` is a local norm for `L/K` at every place `≠ v₀`;
* `hv₀` says that at every place `w | v₀` of `M` the image of `x` in `M_wˣ` is a norm from `E_w`;
* `hM` is the one-place (Hilbert-reciprocity) statement for the *auxiliary* level `M/K` at the
  single place `v₀`.

The conclusion is that `x` is a local norm for `L/K` at `v₀` as well.

The proof (carried out in `NK.CFTLib.IdeleHasse.Descent.transferOnePlaceStep`) is the Brauer
transfer, in the cyclic-class formulation of `NK.CFTLib.IdeleHasse.Descent.transferCore`:

* `c := cycClassOf x ∈ H²(Gal(L/K), Lˣ)` is the class of the cyclic algebra `(L/K, x)`;
* its image `α ∈ H²(Gal(E/K), Eˣ)` under the level inflation `L → E`, restricted to
  `Gal(E/M)`, is the cyclic class of `x` at the level `E/M`
  (`NK.CFTLib.Existence.descentTransferAux.map_rhoRestrict_cycClassOf`);
* by the Hasse–Brauer–Noether theorem (`NK.GlobalCFTdeep.hbnUnits`) at the level `E/M` this
  class vanishes — its localisations vanish at all places over `v ≠ v₀` by `hx` (a `ℚ`-localised
  level change) and at the places over `v₀` by `hv₀` (the localisation dictionary at the level
  `E/M`);
* inflation–restriction exactness then writes `α = inf(β)` with `β ∈ H²(Gal(M/K), Mˣ)`;
* periodicity writes `β = cycClassOf b` with `b ∈ Kˣ` (Galois descent `(Mˣ)^{Gal(M/K)} = Kˣ`);
* the localisations of `β` at all places `≠ v₀` vanish, so `b` is a local norm for `M/K` there,
  and `hM` upgrades this to `v₀`; the Hasse–Brauer–Noether theorem at the level `M/K` gives
  `β = 0`, hence `α = 0`, hence `c = 0` (injectivity of the level inflation, Hilbert 90);
* finally `c = 0` says that `x` is a global norm from `L`, hence a local norm at `v₀`
  (`NK.NUV2.ChebAux.auxDescentTransfer_of_cycClassOf_eq_zero`, via the localisation dictionary
  `NK.CFTLib.IdeleHasse.Descent.localNormSubgroup_iff_cycClass_finite`).
-/

set_option autoImplicit false
set_option linter.unusedSectionVars false
set_option linter.unusedVariables false

namespace NK.CFTLib.IdeleHasse.Descent

theorem transferOnePlace {K L M E : Type} [Field K] [NumberField K] [Field L]
    [NumberField L] [Field M] [NumberField M] [Field E] [NumberField E]
    [Algebra K L] [Algebra K M] [Algebra K E] [Algebra L E] [Algebra M E]
    [IsScalarTower K L E] [IsScalarTower K M E]
    [FiniteDimensional K L] [FiniteDimensional K M] [FiniteDimensional K E]
    [IsGalois K L] [IsGalois K M] [IsGalois K E]
    (hgen : Algebra.adjoin K (Set.range (algebraMap L E) ∪ Set.range (algebraMap M E)) = ⊤)
    (hcycL : IsCyclic (L ≃ₐ[K] L)) (hcycM : IsCyclic (M ≃ₐ[K] M))
    (v₀ : NK.GlobalCFT.Place K)
    (hM : ∀ y : Kˣ,
      (∀ v : NK.GlobalCFT.Place K, v ≠ v₀ →
        NK.CFTLib.IdeleHasse.localImageAt v y ∈
          NK.CFTLib.IdeleHasse.localNormSubgroup (K := K) (L := M) v) →
      NK.CFTLib.IdeleHasse.localImageAt v₀ y ∈
        NK.CFTLib.IdeleHasse.localNormSubgroup (K := K) (L := M) v₀)
    (x : Kˣ)
    (hx : ∀ v : NK.GlobalCFT.Place K, v ≠ v₀ →
      NK.CFTLib.IdeleHasse.localImageAt v x ∈
        NK.CFTLib.IdeleHasse.localNormSubgroup (K := K) (L := L) v)
    (hv₀ : ∀ w : NK.GlobalCFT.Place M, NK.GlobalCFT.Place.LiesOver w v₀ →
      Units.map (algebraMap M (NK.GlobalCFT.Place.localField M w)).toMonoidHom
        (Units.map (algebraMap K M).toMonoidHom x) ∈
        NK.CFTLib.IdeleHasse.localNormSubgroup (K := M) (L := E) w) :
    NK.CFTLib.IdeleHasse.localImageAt v₀ x ∈
      NK.CFTLib.IdeleHasse.localNormSubgroup (K := K) (L := L) v₀ :=
  NK.CFTLib.HR.transferOnePlace hgen hcycL hcycM v₀ hM x hx hv₀

end NK.CFTLib.IdeleHasse.Descent
