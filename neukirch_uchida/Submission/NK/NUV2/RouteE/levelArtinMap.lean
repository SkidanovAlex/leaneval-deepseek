import Mathlib
import Submission.NK.LocalReciprocityLubinTate.Target
import Submission.NK.NUV2.RouteC.delta_qmodz
import Submission.NK.LocalCFT.Reduction.nonempty_artinReciprocity_of_reciprocityLaw

/-!
# The local Artin map at every finite abelian level (Route E, brick 1)

Let `K` be a number field, `Q` a finite place, `F = Q.adicCompletion K` and
`F' = SeparableClosure F`, so that `F^{ab} = maxAbelianSubext F F'`.

**Main result of this file** (`NK.NUV2.RouteE.exists_levelArtinMap`): for every finite-dimensional
normal (hence abelian Galois) level `L ≤ F^{ab}` there is a *surjective* group homomorphism

`Φ_L : Fˣ →* Gal(L/F)` with `ker Φ_L = N_{L/F} Lˣ`,

i.e. the level-wise reciprocity statement of local class field theory.  Equivalently
(`exists_levelMulEquiv`) the quotient `Fˣ ⧸ N_{L/F}Lˣ` is isomorphic to `Gal(L/F)`.

## Where this comes from, and what it does *not* give

This is not new mathematics: it is exactly the per-level output of the on-disk theorem
`Commons.NumberTheory.NumberField.Completion.ArtinMap.exists_surjective_ker_norm_of_fundamental_class`
(local Tate duality from the local fundamental class
`…exists_addOrderOf_eq_finrank_groupCohomology_two_units_aux`, Hilbert 90 and the norm index
theorem), transported to the vocabulary of intermediate fields of `F^{ab}`.  What this file adds is
that transport, and hence a *single* place from which the level-wise Artin map can be consumed in
the Neukirch–Uchida development.

**It does not give `NK.LocalArtin.KernelCondition F F'`**: that asks for a *single* map
`Fˣ →* Gal(F^{ab}/F)` whose level maps have kernel `N_L`, i.e. for the *coherence* of the family
`(Φ_L)_L` across levels.  Coherence is the classical canonicity of the local norm residue symbol
(Milne, *CFT*, III.1–III.3; Iwasawa, *Local Class Field Theory*, Thm. 6.9) and is the remaining
input of the local side; see `Submission/Work/NUV2/RouteC/NOTES_session_G_global_route.md` §1.
-/

open IsDedekindDomain

namespace NK.NUV2.RouteE

set_option linter.style.haveILetI false

noncomputable section

/-- Every finite-dimensional normal level `L` of `F^{ab}/F` is a finite Galois extension of `F`
(in characteristic zero, separability comes for free from the ambient separable closure). -/
theorem isGalois_level {K : Type} [Field K] [NumberField K]
    (Q : IsDedekindDomain.HeightOneSpectrum (NumberField.RingOfIntegers K))
    (L : IntermediateField (Q.adicCompletion K)
      (NK.LocalReciprocity.maxAbelianSubext (Q.adicCompletion K)
        (SeparableClosure (Q.adicCompletion K))))
    [FiniteDimensional (Q.adicCompletion K) L] [Normal (Q.adicCompletion K) L] :
    IsGalois (Q.adicCompletion K) ↥L :=
  isGalois_iff.mpr ⟨inferInstance, inferInstance⟩

/-- **The local Artin map at a finite abelian level.**  For every finite-dimensional normal level
`L` of `F^{ab}/F` there is a surjective homomorphism `Φ : Fˣ →* Gal(L/F)` whose kernel is exactly
the norm group `N_{L/F} Lˣ`.

This is the level-wise reciprocity statement of local class field theory, obtained from the on-disk
local Tate duality (`Commons…ArtinMap.exists_surjective_ker_norm_of_fundamental_class`); the family
of these maps is *not* automatically compatible across levels (that coherence is the remaining
classical input). -/
theorem exists_levelArtinMap {K : Type} [Field K] [NumberField K]
    (Q : IsDedekindDomain.HeightOneSpectrum (NumberField.RingOfIntegers K))
    (L : IntermediateField (Q.adicCompletion K)
      (NK.LocalReciprocity.maxAbelianSubext (Q.adicCompletion K)
        (SeparableClosure (Q.adicCompletion K))))
    [FiniteDimensional (Q.adicCompletion K) L] [Normal (Q.adicCompletion K) L] :
    ∃ Φ : (Q.adicCompletion K)ˣ →* (↥L ≃ₐ[Q.adicCompletion K] ↥L),
      Function.Surjective Φ ∧
        MonoidHom.ker Φ = NK.LocalReciprocity.normGroup (Q.adicCompletion K) ↥L := by
  haveI : IsGalois (Q.adicCompletion K) ↥L := isGalois_level Q L
  exact Commons.NumberTheory.NumberField.Completion.ArtinMap.exists_surjective_ker_norm_of_fundamental_class
    (Commons.NumberTheory.NumberField.Completion.ArtinMap.exists_addOrderOf_eq_finrank_groupCohomology_two_units_aux)
    Q (NK.LocalCFT.Reduction.commutative_level L)

/-- **The level reciprocity isomorphism**: for every finite abelian level `L` of `F^{ab}/F` the
quotient `Fˣ ⧸ N_{L/F}Lˣ` is isomorphic to `Gal(L/F)`.

This is `exists_levelArtinMap` in quotient form (`QuotientGroup.quotientKerEquivOfSurjective`). -/
theorem exists_levelMulEquiv {K : Type} [Field K] [NumberField K]
    (Q : IsDedekindDomain.HeightOneSpectrum (NumberField.RingOfIntegers K))
    (L : IntermediateField (Q.adicCompletion K)
      (NK.LocalReciprocity.maxAbelianSubext (Q.adicCompletion K)
        (SeparableClosure (Q.adicCompletion K))))
    [FiniteDimensional (Q.adicCompletion K) L] [Normal (Q.adicCompletion K) L] :
    Nonempty (((Q.adicCompletion K)ˣ ⧸ NK.LocalReciprocity.normGroup (Q.adicCompletion K) ↥L) ≃*
      (↥L ≃ₐ[Q.adicCompletion K] ↥L)) := by
  obtain ⟨Φ, hsurj, hker⟩ := exists_levelArtinMap Q L
  exact ⟨(QuotientGroup.quotientMulEquivOfEq hker.symm).trans
    (QuotientGroup.quotientKerEquivOfSurjective Φ hsurj)⟩

end

end NK.NUV2.RouteE
