import Mathlib.RingTheory.DedekindDomain.AdicValuation
import Submission.Work.SSGRoute.PT.localCohomologicalFieldAxiom_units

set_option maxHeartbeats 2000000
set_option synthInstance.maxHeartbeats 4000000
set_option linter.style.haveILetI false

namespace Work.SSGRoute.PT

/-- **Solvability of the Galois group of a finite Galois extension of a `p`-adic field.**

For `K` a number field, `Q` a finite place of `K`, `F` a finite extension of the `Q`-adic
completion `K_Q` and `E / F` a finite Galois extension, the Galois group `Gal(E/F)` is solvable.

The proof realises both `F` and `E` as completions of number fields
(`exists_algEquiv_adicCompletion_of_finiteDimensional`,
`exists_galois_adicCompletion_of_finiteDimensional`), where the solvability of the local Galois
group of the number-field realisation is the ramification-filtration theorem
`NK.NUV2.ABHN.solvable_algEquiv_adicCompletion`; solvability is then transported back along the
two algebra equivalences. -/
theorem isSolvable_algEquiv_of_finiteDimensional {K : Type} [Field K] [NumberField K]
    (Q : IsDedekindDomain.HeightOneSpectrum (NumberField.RingOfIntegers K))
    {F E : Type} [Field F] [Field E] [Algebra (Q.adicCompletion K) F] [Algebra F E]
    [Algebra (Q.adicCompletion K) E] [IsScalarTower (Q.adicCompletion K) F E]
    [FiniteDimensional (Q.adicCompletion K) F] [FiniteDimensional F E]
    [FiniteDimensional (Q.adicCompletion K) E] [IsGalois F E] :
    Group.IsSolvable (E ≃ₐ[F] E) := by
  classical
  -- ## Step 1: realise the base `F` as the completion `q.adicCompletion L` of a number field `L`
  obtain ⟨L : Type, hLf, hLn, hLa, q, hq, ⟨e⟩⟩ :=
    Commons.NumberTheory.NumberField.Completion.exists_algEquiv_adicCompletion_of_finiteDimensional
      (Q := Q) (B := F)
  letI : Algebra (Q.adicCompletion K) (q.adicCompletion L) :=
    RingHom.toAlgebra (Commons.RingTheory.Henselian.adicCompletionMap Q q hq)
  -- ## Step 2: transport the `F`-algebra structure on `E` to `q.adicCompletion L`
  letI : Algebra (q.adicCompletion L) E := ((algebraMap F E).comp e.symm.toRingHom).toAlgebra
  have hhe : (algebraMap (q.adicCompletion L) E).comp e.toRingHom = algebraMap F E := by
    ext x
    show algebraMap (q.adicCompletion L) E (e x) = algebraMap F E x
    rw [show algebraMap (q.adicCompletion L) E = (algebraMap F E).comp e.symm.toRingHom from rfl]
    simp [RingHom.comp_apply]
  haveI : FiniteDimensional (q.adicCompletion L) E :=
    Commons.NumberTheory.NumberField.Completion.finiteDimensional_transport e.toRingEquiv hhe
  haveI : IsGalois (q.adicCompletion L) E :=
    Commons.NumberTheory.NumberField.Completion.isGalois_transport e.toRingEquiv hhe
  -- ## Step 3: realise the Galois extension `E / q.adicCompletion L` by a Galois extension of
  -- number fields `L' / L`
  obtain ⟨L' : Type, hL'f, hL'n, hL'a, q', hq', hgal', ⟨e'⟩⟩ :=
    Commons.NumberTheory.NumberField.Completion.exists_galois_adicCompletion_of_finiteDimensional
      (Q := q) (B := E)
  letI : Algebra L L' := hL'a
  letI : Algebra (q.adicCompletion L) (q'.adicCompletion L') :=
    RingHom.toAlgebra (Commons.RingTheory.Henselian.adicCompletionMap q q' hq')
  haveI : FiniteDimensional L L' := Module.Finite.of_restrictScalars_finite ℚ L L'
  haveI : IsGalois L L' := hgal'
  -- ## Step 4: the local Galois group of `L'_{q'} / L_q` is solvable (ramification filtration)
  haveI hsolv : Group.IsSolvable
      (q'.adicCompletion L' ≃ₐ[q.adicCompletion L] q'.adicCompletion L') :=
    NK.NUV2.ABHN.solvable_algEquiv_adicCompletion q q' hq'
  -- ## Step 5: transport solvability back along `e'` to `E / q.adicCompletion L`
  haveI : Group.IsSolvable (E ≃ₐ[q.adicCompletion L] E) := by
    let φ : (q'.adicCompletion L' ≃ₐ[q.adicCompletion L] q'.adicCompletion L') →*
        (E ≃ₐ[q.adicCompletion L] E) :=
      { toFun := fun τ => e'.trans (τ.trans e'.symm)
        map_one' := by
          ext x
          simp
        map_mul' := by
          intro σ τ
          ext x
          simp [AlgEquiv.mul_apply] }
    have hsurj : Function.Surjective φ := by
      intro σ
      refine ⟨e'.symm.trans (σ.trans e'), ?_⟩
      change e'.trans ((e'.symm.trans (σ.trans e')).trans e'.symm) = σ
      ext x
      simp [AlgEquiv.trans_apply]
    exact Group.isSolvable_of_surjective (f := φ) hsurj
  -- ## Step 6: transport solvability back along `e` to `E / F`
  have hcast : (E ≃ₐ[F] E) ≃* (E ≃ₐ[q.adicCompletion L] E) :=
    Commons.NumberTheory.NumberField.Completion.algEquiv_cast (φ := e.toRingEquiv) hhe
  exact Group.isSolvable_of_surjective (f := hcast.symm.toMonoidHom) hcast.symm.surjective

end Work.SSGRoute.PT
