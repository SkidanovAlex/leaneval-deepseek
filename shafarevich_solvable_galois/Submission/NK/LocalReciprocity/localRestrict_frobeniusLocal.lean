import Mathlib
import Submission.NK.LocalReciprocity.LocalSetup
import Submission.NK.LocalReciprocity.Frobenius
-- PORT435-BEGIN (v4.35 isDefEq respectTransparency compat)
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- PORT435-END

namespace NK.LocalReciprocity

/-- **Restriction of the local Frobenius is the Frobenius of the subextension.**  Here `M / K`
is a finite Galois extension of number fields, `L` an intermediate field normal over `K`, `p` a
place of `K` and `w` a place of `M` above `p`, assumed unramified over `p`
(`hunrM : e(w|p) = 1`).  The restriction map on local Galois groups is
`Submission.NeukirchUchida.Local.localRestrict`, whose concrete meaning is recorded in
`localRestrict_adicCompletionMap`:
`adicCompletionMap (w|_L → w) (localRestrict σ y) = σ (adicCompletionMap (w|_L → w) y)`.

Both sides are Frobenius elements of the unramified local extension `L_{w|_L} / K_p`; use the
characterisation `NK.LocalReciprocity.eq_frobeniusLocal_iff` and the congruence defining
`IsFrobeniusLocal` (with the same modulus `residueCard K p` on both sides), the compatibilities
`localRestrict_adicCompletionMap`, `adicCompletionMap_mem_integers_iff` (integrality of the image)
and `val_adicCompletionMap_eq_pow` (valuations are preserved since `e = 1`). -/
theorem localRestrict_frobeniusLocal {K M : Type*} [Field K] [NumberField K] [Field M]
    [NumberField M] [Algebra K M] [FiniteDimensional K M] [IsGalois K M]
    (L : IntermediateField K M) [Normal K L]
    (p : IsDedekindDomain.HeightOneSpectrum (NumberField.RingOfIntegers K))
    (w : IsDedekindDomain.HeightOneSpectrum (NumberField.RingOfIntegers M))
    [hw : w.asIdeal.LiesOver p.asIdeal]
    [hwL : (Submission.NeukirchUchida.Local.placeUnder (K := K) L w).asIdeal.LiesOver p.asIdeal]
    (hunrM : w.asIdeal.ramificationIdx (NumberField.RingOfIntegers K) = 1)
    (hunrL : (Submission.NeukirchUchida.Local.placeUnder (K := K) L w).asIdeal.ramificationIdx
        (NumberField.RingOfIntegers K) = 1) :
    Submission.NeukirchUchida.Local.localRestrict (K := K) L p w hw
        (NK.LocalReciprocity.frobeniusLocal p w hunrM) =
      NK.LocalReciprocity.frobeniusLocal p
        (Submission.NeukirchUchida.Local.placeUnder (K := K) L w) hunrL := by
  classical
  refine (NK.LocalReciprocity.eq_frobeniusLocal_iff p
    (Submission.NeukirchUchida.Local.placeUnder (K := K) L w) hunrL
    (Submission.NeukirchUchida.Local.localRestrict (K := K) L p w hw
      (NK.LocalReciprocity.frobeniusLocal p w hunrM))).mp ?_
  intro x
  let φ : (Submission.NeukirchUchida.Local.placeUnder (K := K) L w).adicCompletion ↥L →+*
      w.adicCompletion M :=
    Commons.RingTheory.Henselian.adicCompletionMap
      (Submission.NeukirchUchida.Local.placeUnder (K := K) L w) w
      (Submission.NeukirchUchida.Local.placeUnder_liesOver (K := K) L w)
  have hcompat : ∀ y : (Submission.NeukirchUchida.Local.placeUnder (K := K) L w).adicCompletion ↥L,
      φ ((Submission.NeukirchUchida.Local.localRestrict (K := K) L p w hw
          (NK.LocalReciprocity.frobeniusLocal p w hunrM)) y) =
        (NK.LocalReciprocity.frobeniusLocal p w hunrM) (φ y) := by
    intro y
    obtain ⟨ψ, hψ⟩ : ∃ ψ, Submission.NeukirchUchida.Local.decompositionSubgroupMulEquivLocalGalois
        (K := K) (L := M) p w hw ψ = NK.LocalReciprocity.frobeniusLocal p w hunrM :=
      ⟨(Submission.NeukirchUchida.Local.decompositionSubgroupMulEquivLocalGalois
          (K := K) (L := M) p w hw).symm (NK.LocalReciprocity.frobeniusLocal p w hunrM),
       (Submission.NeukirchUchida.Local.decompositionSubgroupMulEquivLocalGalois
          (K := K) (L := M) p w hw).apply_symm_apply _⟩
    have h := Submission.NeukirchUchida.Local.localRestrict_adicCompletionMap
      (K := K) L p w hw ψ y
    rw [hψ] at h
    exact h
  have hy : φ (x : (Submission.NeukirchUchida.Local.placeUnder (K := K) L w).adicCompletion ↥L)
      ∈ w.adicCompletionIntegers M :=
    (Commons.NumberTheory.NumberField.Completion.adicCompletionMap_mem_integers_iff
      (Submission.NeukirchUchida.Local.placeUnder (K := K) L w) w
      (Submission.NeukirchUchida.Local.placeUnder_liesOver (K := K) L w)
      (x : (Submission.NeukirchUchida.Local.placeUnder (K := K) L w).adicCompletion ↥L)).mpr x.2
  have hspec := (NK.LocalReciprocity.frobeniusLocal_spec p w hunrM)
    ⟨φ (x : (Submission.NeukirchUchida.Local.placeUnder (K := K) L w).adicCompletion ↥L), hy⟩
  have hmap : φ ((Submission.NeukirchUchida.Local.localRestrict (K := K) L p w hw
        (NK.LocalReciprocity.frobeniusLocal p w hunrM))
          (x : (Submission.NeukirchUchida.Local.placeUnder (K := K) L w).adicCompletion ↥L)
        - (x : (Submission.NeukirchUchida.Local.placeUnder (K := K) L w).adicCompletion ↥L)
            ^ NK.LocalReciprocity.residueCard K p) =
      (NK.LocalReciprocity.frobeniusLocal p w hunrM)
          (φ (x : (Submission.NeukirchUchida.Local.placeUnder (K := K) L w).adicCompletion ↥L))
        - (φ (x : (Submission.NeukirchUchida.Local.placeUnder (K := K) L w).adicCompletion ↥L))
            ^ NK.LocalReciprocity.residueCard K p := by
    rw [map_sub, map_pow, hcompat]
  have hval := Commons.NumberTheory.NumberField.Completion.val_adicCompletionMap_eq_pow
    (Submission.NeukirchUchida.Local.placeUnder (K := K) L w) w
    (Submission.NeukirchUchida.Local.placeUnder_liesOver (K := K) L w)
    ((Submission.NeukirchUchida.Local.localRestrict (K := K) L p w hw
        (NK.LocalReciprocity.frobeniusLocal p w hunrM))
          (x : (Submission.NeukirchUchida.Local.placeUnder (K := K) L w).adicCompletion ↥L)
        - (x : (Submission.NeukirchUchida.Local.placeUnder (K := K) L w).adicCompletion ↥L)
            ^ NK.LocalReciprocity.residueCard K p)
  have he : w.asIdeal.ramificationIdx (NumberField.RingOfIntegers ↥L) ≠ 0 :=
    (Ideal.ramificationIdx_pos (NumberField.RingOfIntegers ↥L) w.asIdeal).ne'
  have h1 : (Valued.v ((Submission.NeukirchUchida.Local.localRestrict (K := K) L p w hw
        (NK.LocalReciprocity.frobeniusLocal p w hunrM))
          (x : (Submission.NeukirchUchida.Local.placeUnder (K := K) L w).adicCompletion ↥L)
        - (x : (Submission.NeukirchUchida.Local.placeUnder (K := K) L w).adicCompletion ↥L)
            ^ NK.LocalReciprocity.residueCard K p))
        ^ (w.asIdeal.ramificationIdx (NumberField.RingOfIntegers ↥L)) < 1 := by
    rw [← hval, hmap]
    exact hspec
  exact (pow_lt_one_iff_of_nonneg (zero_le) he).mp h1

end NK.LocalReciprocity
