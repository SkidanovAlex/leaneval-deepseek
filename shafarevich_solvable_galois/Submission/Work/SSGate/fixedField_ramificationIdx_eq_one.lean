import Mathlib
import Submission.Work.SSGRoute.E9Nodes.e9_baseS
import Submission.Work.SSGRoute.TPatom.fixedField_inertia_eq_bot
import Submission.Work.Sha2Lib.inertia_map_galRes_eq
import Submission.Work.SSGRoute.decompK_restrict_surjective
-- PORT435-BEGIN (v4.35 isDefEq respectTransparency compat)
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- PORT435-END

namespace Work.SSGate

theorem fixedField_ramificationIdx_eq_one {k K : Type} [Field k] [NumberField k] [Field K]
    [NumberField K] [Algebra k K] [FiniteDimensional k K] [IsGalois k K]
    (N : Subgroup (K ≃ₐ[k] K)) [N.Normal]
    (q : IsDedekindDomain.HeightOneSpectrum (NumberField.RingOfIntegers K))
    (hNI : ∀ σ : K ≃ₐ[k] K, SSGRoute.PTExt.IsInertiaAt q σ → σ ∈ N)
    (u : IsDedekindDomain.HeightOneSpectrum
        (NumberField.RingOfIntegers ↥(IntermediateField.fixedField N)))
    (hu : u.asIdeal.LiesOver (q.asIdeal.under (NumberField.RingOfIntegers k))) :
    u.asIdeal.ramificationIdx (NumberField.RingOfIntegers k) = 1 := by
  -- `L = K^N` is the fixed field of `N`; write `J` for the prime of `𝓞 L` lying below `q`.
  set J : Ideal (NumberField.RingOfIntegers ↥(IntermediateField.fixedField N)) :=
    q.asIdeal.under (NumberField.RingOfIntegers ↥(IntermediateField.fixedField N)) with hJ
  -- `u'` is that prime, bundled as a height-one spectrum.
  let u' : IsDedekindDomain.HeightOneSpectrum
      (NumberField.RingOfIntegers ↥(IntermediateField.fixedField N)) :=
    q.under (NumberField.RingOfIntegers ↥(IntermediateField.fixedField N))
  -- `q` lies over `u'`.
  have hlies : q.asIdeal.LiesOver u'.asIdeal := Ideal.over_under _
  -- The inertia group of `u'` in `Gal(L/k)` is trivial.
  have hIbot : Ideal.inertia
      (↥(IntermediateField.fixedField N) ≃ₐ[k] ↥(IntermediateField.fixedField N)) J = ⊥ := by
    rw [Subgroup.eq_bot_iff_forall]
    intro τ hτ
    have hτi : SSGRoute.PTExt.IsInertiaAt u' τ :=
      (Work.SSGRoute.E9Nodes.isInertiaAt_iff_mem_inertia (k := k)
        (K := ↥(IntermediateField.fixedField N)) u' τ).mpr hτ
    exact Work.SSGRoute.TPatom.fixedField_inertia_eq_bot (k := k) (K := K) N q u' hlies hNI τ hτi
  -- Hence the ramification index of `u'` over `k` is one.
  have hram_u' : J.ramificationIdx (NumberField.RingOfIntegers k) = 1 :=
    (Commons.NumberTheory.RamificationInertia.inertia_eq_bot_iff_ramificationIdx_eq_one
      (q.asIdeal.under (NumberField.RingOfIntegers k)) J).mp hIbot
  -- So the invariant ramification index of the prime `q ∩ 𝓞 k` in `L` is one, and this is the
  -- ramification index of *every* prime of `𝓞 L` above it, in particular of `u`.
  have hIn : (q.asIdeal.under (NumberField.RingOfIntegers k)).ramificationIdxIn
      (NumberField.RingOfIntegers ↥(IntermediateField.fixedField N)) = 1 := by
    rw [Ideal.ramificationIdxIn_eq_ramificationIdx
      (p := q.asIdeal.under (NumberField.RingOfIntegers k))
      (P := J) (G := ↥(IntermediateField.fixedField N) ≃ₐ[k] ↥(IntermediateField.fixedField N))]
    exact hram_u'
  rw [← Ideal.ramificationIdxIn_eq_ramificationIdx
      (p := q.asIdeal.under (NumberField.RingOfIntegers k))
      (P := u.asIdeal) (G := ↥(IntermediateField.fixedField N) ≃ₐ[k] ↥(IntermediateField.fixedField N))
      (hp := hu)]
  exact hIn

end Work.SSGate
