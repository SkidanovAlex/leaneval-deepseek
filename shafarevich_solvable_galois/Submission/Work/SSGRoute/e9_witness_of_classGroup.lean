import Mathlib.RingTheory.Henselian
import Mathlib.NumberTheory.RamificationInertia.Galois
import Mathlib.RingTheory.ClassGroup.Basic
import Mathlib.RingTheory.DedekindDomain.Different
import Mathlib.RingTheory.RegularLocalRing.Defs
import Mathlib.RingTheory.SimpleRing.Principal
import Mathlib.NumberTheory.NumberField.InfinitePlace.Ramification
import Submission.Work.SSGRoute.E9Nodes.e9_abelian_wide_witness
import Submission.Work.SSGRoute.E9Nodes.e9_classGroup_generators
import Submission.Work.SSGRoute.PTDefsOmega
import Submission.Work.SSGRoute.glue_involution_place
-- PORT435-BEGIN (v4.35 isDefEq respectTransparency compat)
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- PORT435-END

namespace Work.SSGRoute

open scoped NumberField

/-- The stabiliser of the finite place of `E` attached to a nonzero prime `w` of `𝓞 E` is the
decomposition subgroup of `w` in the sense of
`Commons.NumberTheory.NumberField.Completion.decompositionSubgroup`.

Both are `{σ | σ • w = w}` for the Galois action on height-one primes; the two definitions of that
action (`Submission.NeukirchUchida.Local.placeSmul` and
`Commons.NumberTheory.NumberField.Completion.placeSmul`) have the same underlying formula
`w.asIdeal.map (galRestrict … σ)`, so the two subgroups are equal. -/
lemma stabilizer_ofFinite_eq_decompositionSubgroup_commons {K E : Type} [Field K] [NumberField K]
    [Field E] [NumberField E] [Algebra K E] [FiniteDimensional K E] [IsGalois K E]
    (w : IsDedekindDomain.HeightOneSpectrum (𝓞 E)) :
    MulAction.stabilizer (E ≃ₐ[K] E) (NK.GlobalCFT.Place.ofFinite w) =
      Commons.NumberTheory.NumberField.Completion.decompositionSubgroup (K := K) w := by
  ext σ
  rw [Work.SSGRoute.mem_stabilizer_ofFinite_iff w σ,
    Commons.NumberTheory.NumberField.Completion.mem_decompositionSubgroup]
  constructor
  · intro h
    apply IsDedekindDomain.HeightOneSpectrum.ext
    rw [Commons.NumberTheory.NumberField.Completion.placeSmul_asIdeal]
    exact h
  · intro h
    have h' := congrArg IsDedekindDomain.HeightOneSpectrum.asIdeal h
    rwa [Commons.NumberTheory.NumberField.Completion.placeSmul_asIdeal] at h'

/-- **The witness places coming from a class-group generating set.**  There is a finite set `W` of
places of `K` such that every nontrivial finite abelian Galois extension `E/K` which is unramified
at every finite and every infinite place is *nonsplit* at some place of `W`: there are `v ∈ W` and a
place `Wp` of `E` above `v` whose decomposition group (`MulAction.stabilizer (E ≃ₐ[K] E) Wp`) is
nontrivial.

Route.  Take `S` a finite set of primes of `𝓞 K` whose classes generate the ideal class group
(`E9Nodes.e9_classGroup_generators`) and set `W := S.image Place.ofFinite`.  If `E ≠ K` had all
primes of `S` splitting completely (`(𝔮.asIdeal.primesOver (𝓞 E)).ncard = [E : K]`), then
`E9Nodes.e9_abelian_wide_witness` would give `[E : K] = 1`, a contradiction; so some `𝔮 ∈ S` does
not split completely.  By
`Commons.NumberTheory.NumberField.ncard_primesOver_eq_finrank_iff_splitCompletely` this means
`𝔮.asIdeal.ramificationIdxIn` or `𝔮.asIdeal.inertiaDegIn` is `≠ 1`, so by
`Commons.NumberTheory.NumberField.Completion.decompositionSubgroup_eq_bot_iff_ramificationIdx_eq_one_and_inertiaDeg_eq_one`
there is a prime `w` of `E` over `𝔮` whose decomposition subgroup is nontrivial; the place
`Place.ofFinite w` above `Place.ofFinite 𝔮` is then the desired witness
(`Work.SSGRoute.mem_stabilizer_ofFinite_iff` identifies the stabiliser of `Place.ofFinite w` with
the set of `σ` preserving the prime `w`). -/
theorem e9_witness_of_classGroup (K : Type) [Field K] [NumberField K] :
    ∃ W : Finset (NK.GlobalCFT.Place K),
      ∀ (E : Type) [Field E] [NumberField E] [Algebra K E] [FiniteDimensional K E]
        [IsGalois K E] [IsMulCommutative (E ≃ₐ[K] E)],
        differentIdeal (𝓞 K) (𝓞 E) = ⊤ → IsUnramifiedAtInfinitePlaces K E →
        Module.finrank K E ≠ 1 →
        ∃ (v : NK.GlobalCFT.Place K) (Wp : NK.GlobalCFT.Place E),
          v ∈ W ∧ NK.GlobalCFT.Place.LiesOver Wp v ∧
            MulAction.stabilizer (E ≃ₐ[K] E) Wp ≠ ⊥ := by
  classical
  -- a finite set of primes whose classes generate the ideal class group
  obtain ⟨S, hS⟩ := E9Nodes.e9_classGroup_generators K
  refine ⟨S.image NK.GlobalCFT.Place.ofFinite, ?_⟩
  intro E _ _ _ _ _ _ hfin hinf hne
  -- suppose no place of `W` witnesses nonsplitting
  by_contra hno
  have hno' : ∀ (v : NK.GlobalCFT.Place K) (Wp : NK.GlobalCFT.Place E),
      v ∈ (S.image NK.GlobalCFT.Place.ofFinite) → NK.GlobalCFT.Place.LiesOver Wp v →
      MulAction.stabilizer (E ≃ₐ[K] E) Wp = ⊥ := by
    intro v Wp hv hL
    by_contra h
    exact hno ⟨v, Wp, hv, hL, h⟩
  -- then every prime of `S` splits completely in `E / K`
  have hsplit : ∀ 𝔮 ∈ S, (𝔮.asIdeal.primesOver (𝓞 E)).ncard = Module.finrank K E := by
    intro 𝔮 h𝔮
    rw [Commons.NumberTheory.NumberField.ncard_primesOver_eq_finrank_iff_splitCompletely
      (K := K) (L := E) 𝔮]
    -- a prime `w` of `𝓞 E` above `𝔮`
    obtain ⟨P⟩ :=
      (Ideal.nonempty_primesOver 𝔮.asIdeal : Nonempty (𝔮.asIdeal.primesOver (𝓞 E)))
    set w : IsDedekindDomain.HeightOneSpectrum (𝓞 E) :=
      ⟨P.1, P.2.1, Ideal.ne_bot_of_mem_primesOver 𝔮.ne_bot P.2⟩ with hwdef
    have hwL : w.asIdeal.LiesOver 𝔮.asIdeal := P.2.2
    -- its decomposition subgroup is trivial by hypothesis
    have hstab : MulAction.stabilizer (E ≃ₐ[K] E) (NK.GlobalCFT.Place.ofFinite w) = ⊥ :=
      hno' (NK.GlobalCFT.Place.ofFinite 𝔮) (NK.GlobalCFT.Place.ofFinite w)
        (Finset.mem_image.mpr ⟨𝔮, h𝔮, rfl⟩) (NK.GlobalCFT.Place.liesOver_ofFinite hwL)
    have hdec : Commons.NumberTheory.NumberField.Completion.decompositionSubgroup
        (K := K) w = ⊥ := by
      rw [← stabilizer_ofFinite_eq_decompositionSubgroup_commons (K := K) (E := E) w]
      exact hstab
    rw [← Commons.NumberTheory.NumberField.Completion.decompositionSubgroup_eq_bot_iff_ramificationIdx_eq_one_and_inertiaDeg_eq_one
      (K := K) (L := E) 𝔮 w hwL]
    exact hdec
  -- so the abelian extension is trivial, contradicting `finrank ≠ 1`
  exact hne (E9Nodes.e9_abelian_wide_witness K E S hS hfin hinf hsplit)

end Work.SSGRoute
