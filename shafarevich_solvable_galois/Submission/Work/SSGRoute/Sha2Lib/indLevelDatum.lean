import Mathlib.NumberTheory.NumberField.Basic
import Mathlib.RingTheory.RamificationInertia.Ramification
import Submission.Work.SSGRoute.SSGStage.mem_cocycles_coordKer
import Submission.Work.SSGRoute.Sha2Lib.indDatumAction
-- PORT435-BEGIN (v4.35 isDefEq respectTransparency compat)
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- PORT435-END

/-!
# The *induced* level datum of `exists_induced_level_augDetecting`

`Ind_{D_w}^{G₀} 𝔽_p = ↥(Work.SSGRoute.E7cC.indDatum p k K w)` (`G₀ = Gal(K/k)`,
`D_w = decompK w ≤ G₀`) is the `G₀`-module of `𝔽_p`-valued functions on `G₀` that are invariant
under right multiplication by `D_w`, with the left-translation action.  Its "distinguished basis
vector" is `indDatumBase` — the indicator of `D_w`, i.e. the indicator of the identity coset of
`G₀/D_w`.

The target `Work.SSGRoute.Sha2Lib.exists_induced_level_augDetecting` asks for a finite Galois level
`L ⊇ K` over `k`, a place `q' | w` with `p ∤ e(q'|q)`, a `G₀`-equivariant isomorphism
`e : ker (galRes k K L) ≃* Ind`, a splitting `s` of `galRes`, and *some* nonzero `G₀`-invariant
additive functional `a` on `Ind` which is nonzero on the `e`-coordinate of some `d ∈ D_{q'}` and
zero on the `e`-coordinates of the inertia.

The space of `G₀`-invariant additive functionals on `Ind_{D_w}^{G₀} 𝔽_p` is **one dimensional**,
spanned by the augmentation `datumAug` (`Work.SSGRoute.Sha2Lib.datumAug_unique`), and
`datumAug (indDatumBase) = 1` (`Work.SSGRoute.Sha2Lib.datumAug_base`).  Hence the target is
*equivalent* to the following **concrete** statement about the level alone, in which the abstract
functional `a` has been resolved into the single explicit element `indDatumBase`:

* the inertia coordinates of `q'` are *trivial*: `coordKer γ = 1` for every inertial `γ`;
* some `d ∈ D_{q'}` has coordinate the basis vector: `e (coordKer d) = indDatumBase`.

This is `IndLevelDatum` below.  It is the exact analogue, for the *induced* module, of
`Work.SSGRoute.HSRow.RegularLevelDatum` for the *regular* module
(`HSRow/c6_leaf_of_splitPlace.lean`), with one important difference: the element demanded of the
Frobenius coordinate is the indicator of the **set** `D_w` — which is precisely
`indDatumBase : ↥(indDatum p k K w)`.  (For the regular module `𝔽_p[G₀]` the corresponding
"natural" coordinate is still the indicator of `D_w`, which is the demanded basis vector only when
`D_w = ⊥`, the reason recorded in the header of `HSRow/c6_leaf_of_splitPlace.lean`.)  So for the
*induced* module the natural Kummer level is expected to satisfy the datum as stated.

`Work.SSGRoute.Sha2Lib.exists_induced_level_augDetecting_of_indLevelDatum` (proved in the target's
file) is the reduction: `IndLevelDatum` *implies* the target.  It is a genuine reduction because the
datum is stated with the single concrete vector `indDatumBase` and the concrete vanishing
`coordKer = 1`, while the target quantifies over an arbitrary invariant functional `a`.
-/

set_option linter.unusedSectionVars false
set_option linter.unusedVariables false

namespace Work.SSGRoute.Sha2Lib

/-- **The induced level datum** of `Work.SSGRoute.Sha2Lib.exists_induced_level_augDetecting`.

There are a finite Galois level `L ⊇ K` over `k`, a place `q' | w` with `e(q'|q)` prime to `p`, a
`Gal(K/k)`-equivariant isomorphism `e : ker (galRes k K L) ≃* Ind_{D_w}^{G₀} 𝔽_p`, and a splitting
`s` of `galRes k K L` such that

* every inertial `γ ∈ Gal(L/k)` has trivial coordinate, `coordKer γ = 1`;
* some `d ∈ D_{q'}` has coordinate the basis vector `indDatumBase` (the indicator of `D_w`).

The target follows from it (`exists_induced_level_augDetecting_of_indLevelDatum`) by taking
`a :=` the augmentation `datumAugHom`, which is nonzero, `G₀`-invariant, and equal to `1` on
`indDatumBase`. -/
def IndLevelDatum (p : ℕ) [Fact p.Prime] (k K : Type) [Field k] [NumberField k]
    [Field K] [NumberField K] [Algebra k K] [FiniteDimensional k K] [IsGalois k K]
    (Ω : Type) [Field Ω] [IsAlgClosed Ω] [Algebra K Ω] [Algebra k Ω] [IsScalarTower k K Ω]
    (w : NK.GlobalCFT.Place K)
    (q : IsDedekindDomain.HeightOneSpectrum (NumberField.RingOfIntegers K))
    (_hwq : w = NK.GlobalCFT.Place.ofFinite q) : Prop :=
  ∃ (L : IntermediateField K Ω) (_ : NumberField ↥L) (_ : FiniteDimensional k ↥L)
    (_ : IsGalois k ↥L)
    (q' : IsDedekindDomain.HeightOneSpectrum (NumberField.RingOfIntegers ↥L))
    (hq' : NK.GlobalCFT.Place.LiesOver (NK.GlobalCFT.Place.ofFinite q') w),
    Nat.Coprime (q'.asIdeal.ramificationIdx (NumberField.RingOfIntegers K)) p ∧
    ∃ e : (SSGRoute.PTExt.galRes k K ↥L).ker ≃*
        Multiplicative ↥(Work.SSGRoute.E7cC.indDatum p k K w),
      (∀ (σ : ↥L ≃ₐ[k] ↥L) (g : (SSGRoute.PTExt.galRes k K ↥L).ker),
        ((e ⟨σ * (g : ↥L ≃ₐ[k] ↥L) * σ⁻¹,
            Work.SSGRoute.SSGStage.ker_galRes_conj_mem p k K Ω L σ g⟩).toAdd :
            (K ≃ₐ[k] K) → ZMod p)
          = fun τ : K ≃ₐ[k] K =>
              ((e g).toAdd : (K ≃ₐ[k] K) → ZMod p)
                ((SSGRoute.PTExt.galRes k K ↥L σ)⁻¹ * τ)) ∧
      ∃ (s : (K ≃ₐ[k] K) →* (↥L ≃ₐ[k] ↥L))
        (hs : ∀ σ : K ≃ₐ[k] K, SSGRoute.PTExt.galRes k K ↥L (s σ) = σ),
        (∀ γ : ↥L ≃ₐ[k] ↥L, SSGRoute.PTExt.IsInertiaAt q' γ →
          Work.SSGRoute.SSGStage.coordKer k K Ω L s hs γ = 1) ∧
        (∃ d : ↥L ≃ₐ[k] ↥L,
          d ∈ SSGRoute.PTExt.decompK (k := k) (K := ↥L) (NK.GlobalCFT.Place.ofFinite q') ∧
          e (Work.SSGRoute.SSGStage.coordKer k K Ω L s hs d)
            = Multiplicative.ofAdd (Work.SSGRoute.E7cC.indDatumBase p k K w))

end Work.SSGRoute.Sha2Lib
