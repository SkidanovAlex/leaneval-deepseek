import Mathlib.RingTheory.Henselian
import Mathlib.Algebra.Lie.OfAssociative
import Mathlib.FieldTheory.Galois.GaloisClosure
import Mathlib.RingTheory.DedekindDomain.AdicValuation
import Mathlib.RingTheory.Flat.TorsionFree
import Mathlib.RingTheory.RegularLocalRing.Defs
import Mathlib.RingTheory.SimpleRing.Principal
import Mathlib.RepresentationTheory.Homological.GroupCohomology.Basic
import Submission.Work.SSGRoute.PT.p_dvd_H2_units_adicCompletion
-- PORT435-BEGIN (v4.35 isDefEq respectTransparency compat)
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- PORT435-END

set_option linter.style.haveILetI false
set_option backward.isDefEq.respectTransparency false

/-- **The level `H²(Gal(L/F), Lˣ)` of a finite Galois level of a finite extension `F` of a
`Q`-adic field is cyclic of order `[L : F]`.**

This is the `LevelH2`-form of the generalised local fundamental class
`NK.NUV2.LC.exists_addOrderOf_eq_finrank_groupCohomology_two_units_local` (an element of additive
order `[L : F]`) together with the order computation
`NK.NUV2.LC.natCard_groupCohomology_two_units_local_eq_finrank`
(`#H²(Gal(L/F), Lˣ) = [L : F]`), and hence mirrors `Work.SSGRoute.PT.levelH2_cyclic` for the base
field `K_Q` replaced by an arbitrary finite extension `F / K_Q`. -/
theorem levelH2_cyclic_finiteExtension {K : Type} [Field K] [NumberField K]
    (Q : IsDedekindDomain.HeightOneSpectrum (NumberField.RingOfIntegers K))
    {F : Type} [Field F] [Algebra (Q.adicCompletion K) F] [FiniteDimensional (Q.adicCompletion K) F]
    (L : FiniteGaloisIntermediateField F (AlgebraicClosure F)) :
    ∃ u : Work.SSGRoute.PTCore.LevelH2 L, AddSubgroup.zmultiples u = ⊤ ∧
      addOrderOf u = Module.finrank F ↥L := by
  classical
  haveI hk : CharZero (Q.adicCompletion K) :=
    charZero_of_injective_algebraMap
      (RingHom.injective (algebraMap ℚ (Q.adicCompletion K)))
  have hInj : Function.Injective (algebraMap (Q.adicCompletion K) F) :=
    RingHom.injective (algebraMap (Q.adicCompletion K) F)
  haveI hFc : CharZero F :=
    CharZero.of_addMonoidHom (algebraMap (Q.adicCompletion K) F).toAddMonoidHom (by simp) hInj
  haveI hG : IsGalois F (AlgebraicClosure F) := IsAlgClosure.isGalois F (AlgebraicClosure F)
  -- transport the `K_Q`-algebra structure on `F` to the finite level `↥L`
  letI instAlgL : Algebra (Q.adicCompletion K) ↥L :=
    ((algebraMap F ↥L).comp (algebraMap (Q.adicCompletion K) F)).toAlgebra
  -- fix the associated module structure explicitly so that the `Module.Finite` instance below is
  -- stated for the very same structure that the instance search will use
  letI instModL : Module (Q.adicCompletion K) ↥L := instAlgL.toModule
  haveI instST : IsScalarTower (Q.adicCompletion K) F ↥L :=
    IsScalarTower.of_algebraMap_eq (fun _ => rfl)
  haveI instFin : Module.Finite (Q.adicCompletion K) ↥L :=
    Module.Finite.trans (R := Q.adicCompletion K) F ↥L
  obtain ⟨u, hu⟩ :=
    NK.NUV2.LC.exists_addOrderOf_eq_finrank_groupCohomology_two_units_local (K := K) Q
      (F := F) (E := ↥L)
  refine ⟨Work.SSGRoute.PTCore.h2LevelEquiv L u, ?_, ?_⟩
  · have hA : Nat.card (groupCohomology (Rep.ofAlgebraAutOnUnits F ↥L) 2) =
        Module.finrank F ↥L :=
      NK.NUV2.LC.natCard_groupCohomology_two_units_local_eq_finrank (K := K) Q (F := F) (E := ↥L)
    have hfinrank_ne : Module.finrank F ↥L ≠ 0 :=
      ne_of_gt ((Module.finrank_pos_iff_of_free F ↥L).mpr inferInstance)
    have hcard : Nat.card ↥(AddSubgroup.zmultiples u) =
        Nat.card (groupCohomology (Rep.ofAlgebraAutOnUnits F ↥L) 2) := by
      rw [Nat.card_zmultiples, hu, hA]
    have hgen : AddSubgroup.zmultiples u = ⊤ := by
      have hfin : Finite ↥(AddSubgroup.zmultiples u) :=
        Nat.finite_of_card_ne_zero (by rw [hcard, hA]; exact hfinrank_ne)
      exact AddSubgroup.eq_top_of_card_eq (AddSubgroup.zmultiples u) hcard
    exact Work.SSGRoute.PT.zmultiples_map_addEquiv (Work.SSGRoute.PTCore.h2LevelEquiv L) hgen
  · exact (addOrderOf_injective (Work.SSGRoute.PTCore.h2LevelEquiv L).toAddMonoidHom
      (Work.SSGRoute.PTCore.h2LevelEquiv L).injective u).trans hu
