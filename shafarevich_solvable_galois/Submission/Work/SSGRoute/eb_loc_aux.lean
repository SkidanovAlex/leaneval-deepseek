import Mathlib.RingTheory.DedekindDomain.AdicValuation
import Submission.Work.SSGRoute.E8Defs
-- PORT435-BEGIN (v4.35 isDefEq respectTransparency compat)
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- PORT435-END

set_option autoImplicit false
set_option maxHeartbeats 1600000
set_option linter.unusedSectionVars false
set_option linter.style.haveILetI false

namespace Work.SSGRoute

open NK.GlobalCFT CategoryTheory NumberField

/-- **The stabiliser of a finite place is its decomposition group** (in the sense of
`Commons.NumberTheory.NumberField.Completion.decompositionSubgroup`), for `k ⊆ K ⊆ E`. -/
theorem eb_stab_eq_decomp_aux (k K E : Type) [Field k] [NumberField k] [Field K] [NumberField K]
    [Field E] [NumberField E] [Algebra k K] [Algebra k E] [Algebra K E] [IsScalarTower k K E]
    [FiniteDimensional k K] [FiniteDimensional K E] [FiniteDimensional k E]
    [IsGalois k K] [IsGalois k E] [IsGalois K E]
    (ŵ : IsDedekindDomain.HeightOneSpectrum (NumberField.RingOfIntegers E)) :
    EB_StabEqDecomp k K E ŵ := by
  unfold EB_StabEqDecomp
  ext σ
  rw [MulAction.mem_stabilizer_iff,
    NK.GlobalCFT.Inclusion.globalCFT_mem_decompositionSubgroup_iff,
    NK.GlobalCFT.Place.smul_ofFinite, NK.GlobalCFT.Place.ofFinite_inj]

/-- **The relative decomposition group has the local degree as its cardinality.**

For `k ⊆ K ⊆ E` finite Galois extensions of number fields, a finite place `ŵ` of `E` and `W` the
place of `K` below it, the stabiliser of `ŵ` in `Gal(E/K)` has cardinality the local degree
`[E_ŵ : K_W]`.  Proof: the bridge `eb_stab_eq_decomp_aux`, the decomposition-group isomorphism
`Commons…decompositionSubgroupMulEquivLocalGalois` and `IsGalois.card_aut_eq_finrank`. -/
theorem eb_stab_card_aux (k K E : Type) [Field k] [NumberField k] [Field K] [NumberField K]
    [Field E] [NumberField E] [Algebra k K] [Algebra k E] [Algebra K E] [IsScalarTower k K E]
    [FiniteDimensional k K] [FiniteDimensional K E] [FiniteDimensional k E]
    [IsGalois k K] [IsGalois k E] [IsGalois K E]
    (ŵ : IsDedekindDomain.HeightOneSpectrum (NumberField.RingOfIntegers E))
    (W : IsDedekindDomain.HeightOneSpectrum (NumberField.RingOfIntegers K))
    (hW : ŵ.asIdeal.LiesOver W.asIdeal) :
    letI : Algebra (W.adicCompletion K) (ŵ.adicCompletion E) :=
      Commons.NumberTheory.NumberField.Completion.adicCompletionAlgebra W ŵ hW
    Nat.card (MulAction.stabilizer (E ≃ₐ[K] E) (NK.GlobalCFT.Place.ofFinite ŵ)) =
      Module.finrank (W.adicCompletion K) (ŵ.adicCompletion E) := by
  letI : Algebra (W.adicCompletion K) (ŵ.adicCompletion E) :=
    Commons.NumberTheory.NumberField.Completion.adicCompletionAlgebra W ŵ hW
  haveI hfd : FiniteDimensional (W.adicCompletion K) (ŵ.adicCompletion E) :=
    Commons.NumberTheory.NumberField.Completion.module_finite_adicCompletion W ŵ hW
  haveI hgal : IsGalois (W.adicCompletion K) (ŵ.adicCompletion E) :=
    Commons.NumberTheory.NumberField.Completion.isGalois_adicCompletion W ŵ hW
  rw [show (MulAction.stabilizer (E ≃ₐ[K] E) (NK.GlobalCFT.Place.ofFinite ŵ))
      = Commons.NumberTheory.NumberField.Completion.decompositionSubgroup (K := K) ŵ
      from eb_stab_eq_decomp_aux k K E ŵ]
  rw [Nat.card_congr (Commons.NumberTheory.NumberField.Completion.decompositionSubgroupMulEquivLocalGalois
      (K := K) (L := E) W ŵ hW).toEquiv]
  exact IsGalois.card_aut_eq_finrank (W.adicCompletion K) (ŵ.adicCompletion E)

end Work.SSGRoute
