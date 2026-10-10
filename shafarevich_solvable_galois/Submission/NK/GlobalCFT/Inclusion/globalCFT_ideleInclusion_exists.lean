import Mathlib.RingTheory.DedekindDomain.AdicValuation
import Mathlib.NumberTheory.NumberField.Completion.LiesOverInstances
import Mathlib.Topology.Algebra.RestrictedProduct.Basic
import Submission.NK.GlobalCFT.Idele
import Submission.NK.GlobalCFT.Inclusion.globalCFT_localAlgebraMapUnits_mem_localUnits
-- PORT435-BEGIN (v4.35 isDefEq respectTransparency compat)
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- PORT435-END

namespace NK.GlobalCFT.Inclusion

open scoped NumberField RestrictedProduct
open NumberField IsDedekindDomain

/-- The canonical local map `K_vˣ →* L_wˣ` carries local units into local units: at an
archimedean place the target is everything, at a nonarchimedean place this is the statement
that the map between adic completions preserves the ring of integers, whence units. -/
theorem globalCFT_localAlgebraMapUnits_mapsTo_localUnits {K L : Type*} [Field K] [NumberField K]
    [Field L] [NumberField L] [Algebra K L] {w : Place L} {v : Place K}
    (h : Place.LiesOver w v) :
    Set.MapsTo (Place.localAlgebraMapUnits w v h) (Place.localUnits K v)
      (Place.localUnits L w) := by
  intro x hx
  rcases w with w | q <;> rcases v with v | Q
  · rw [Place.localUnits_ofInfinite]
    exact Subgroup.mem_top _
  · exact absurd ((Place.isFinite_of_liesOver h).mpr (Place.isFinite_ofFinite Q))
      (Place.not_isFinite_ofInfinite w)
  · exact absurd ((Place.isFinite_of_liesOver h).mp (Place.isFinite_ofFinite q))
      (Place.not_isFinite_ofInfinite v)
  · have hq : q.asIdeal.LiesOver Q.asIdeal := by
      rcases (Place.liesOver_iff _ _).mp h with ⟨w', v', h1, h2, h3⟩ | ⟨q', Q', h1, h2, h3⟩
      · exact absurd h1.symm (Place.ofInfinite_ne_ofFinite w' q)
      · rw [Place.ofFinite_inj] at h1 h2
        rw [← h1, ← h2] at h3
        exact h3
    rw [Place.localUnits_ofFinite] at hx ⊢
    rw [Place.localAlgebraMapUnits]
    simp only [Sum.casesOn]
    rw [dif_pos hq]
    change (Units.map ((Commons.RingTheory.Henselian.adicCompletionMap Q q hq).toMonoidHom)) x ∈
      (HeightOneSpectrum.adicCompletionIntegers L q).units
    change x ∈ (HeightOneSpectrum.adicCompletionIntegers K Q).units at hx
    rw [Submonoid.mem_units_iff] at hx ⊢
    refine ⟨?_, ?_⟩
    · rw [Units.coe_map]
      exact Commons.RingTheory.Henselian.adicCompletionMap_mem_integers Q q hq hx.1
    · rw [Units.coe_map_inv]
      exact Commons.RingTheory.Henselian.adicCompletionMap_mem_integers Q q hq hx.2

/-- For a finite extension `L / K` of number fields and a place `v` of `K`, only finitely many
places of `L` lie over `v`. -/
theorem globalCFT_liesOver_fiber_finite {K L : Type*} [Field K] [NumberField K] [Field L]
    [NumberField L] [Algebra K L] [FiniteDimensional K L] (v : Place K) :
    {w : Place L | Place.LiesOver w v}.Finite := by
  classical
  rcases v with v' | Q
  · refine Set.Finite.subset
      ((Place.fiberInfinite (K := K) (L := L) v').finite_toSet.image Place.ofInfinite) ?_
    rintro w hw
    change Place.LiesOver w (Place.ofInfinite v') at hw
    have hfin : ¬ Place.IsFinite w := fun h =>
      Place.not_isFinite_ofInfinite v' ((Place.isFinite_of_liesOver hw).mp h)
    have hinf : Place.IsInfinite w := by
      by_contra h
      exact hfin h
    obtain ⟨w', rfl⟩ := Place.isInfinite_iff.mp hinf
    refine ⟨w', ?_, rfl⟩
    exact Finset.mem_coe.mpr ((Place.mem_fiberInfinite (v := v') (w := w')).mpr (by
      rw [Place.liesOver_iff] at hw
      rcases hw with ⟨w'', v'', h1, h2, h3⟩ | ⟨q', Q', h1, h2, h3⟩
      · have e1 : w' = w'' := Place.ofInfinite_inj.mp h1
        have e2 : v' = v'' := Place.ofInfinite_inj.mp h2
        rw [e1, e2]
        exact h3
      · exact absurd h1 (Place.ofInfinite_ne_ofFinite w' q')))
  · refine Set.Finite.subset
      ((Place.primesOverFinite (K := K) (L := L) Q).finite_toSet.image Place.ofFinite) ?_
    rintro w hw
    change Place.LiesOver w (Place.ofFinite Q) at hw
    have hfin : Place.IsFinite w :=
      (Place.isFinite_of_liesOver hw).mpr (Place.isFinite_ofFinite Q)
    obtain ⟨q, rfl⟩ := Place.isFinite_iff.mp hfin
    refine ⟨q, ?_, rfl⟩
    exact Finset.mem_coe.mpr ((Place.mem_primesOverFinite (Q := Q) (q := q)).mpr (by
      rw [Place.liesOver_iff] at hw
      rcases hw with ⟨w'', v'', h1, h2, h3⟩ | ⟨q', Q', h1, h2, h3⟩
      · exact absurd h1.symm (Place.ofInfinite_ne_ofFinite w'' q)
      · have e1 : q = q' := Place.ofFinite_inj.mp h1
        have e2 : Q = Q' := Place.ofFinite_inj.mp h2
        rw [← e1, ← e2] at h3
        exact h3))

theorem globalCFT_ideleInclusion_exists {K L : Type*} [Field K] [NumberField K] [Field L]
    [NumberField L] [Algebra K L] [FiniteDimensional K L]
    (u : Place L → Place K) (hu : ∀ w : Place L, Place.LiesOver w (u w)) :
    ∃ φ : 𝕀[K] →* 𝕀[L], ∀ (x : 𝕀[K]) (w : Place L),
      φ x w = Place.localAlgebraMapUnits w (u w) (hu w) (x (u w)) := by
  classical
  -- each place `w` of `L` lies over `u w`, and only finitely many places of `L` lie over a
  -- given place of `K`, so `u` is a cofinite-to-cofinite map
  have htend : Filter.Tendsto u Filter.cofinite Filter.cofinite :=
    Filter.Tendsto.cofinite_of_finite_preimage_singleton fun v =>
      (globalCFT_liesOver_fiber_finite (K := K) (L := L) v).subset fun w hw => by
        rw [Set.mem_preimage, Set.mem_singleton_iff] at hw
        rw [← hw]
        exact hu w
  -- the diagonal of the local embeddings, restricted against the local units
  refine ⟨{ toFun := fun x => (⟨fun w => Place.localAlgebraMapUnits w (u w) (hu w) (x (u w)),
      ?_⟩ : 𝕀[L]), map_one' := ?_, map_mul' := ?_ }, ?_⟩
  · filter_upwards [htend.eventually x.2] with w hw
    exact globalCFT_localAlgebraMapUnits_mapsTo_localUnits (hu w) hw
  · ext w
    simp only [Idele.one_apply, map_one]
    rfl
  · intro x y
    ext w
    simp only [Idele.mul_apply, map_mul]
    rfl
  · intro x w
    rfl

end NK.GlobalCFT.Inclusion
