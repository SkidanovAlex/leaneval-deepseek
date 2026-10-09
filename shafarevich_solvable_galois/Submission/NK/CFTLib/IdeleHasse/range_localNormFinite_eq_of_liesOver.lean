import Mathlib
import Submission.NK.GlobalCFT.Place
import Submission.NK.NumberTheory.NumberField.Completion.exists_algEquiv_adicCompletion_of_valuationSubringAtPrime_comap
import Submission.Commons.NumberTheory.RamificationInertia.exists_smul_valuationSubringAtPrime_eq
import Submission.NeukirchUchida.Local.PlaceFromValuation
-- PORT435-BEGIN (v4.35 isDefEq respectTransparency compat)
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- PORT435-END

/-!
# The local norm group at a finite place depends only on the place below

Let `L / K` be a finite Galois extension of number fields, `Q` a finite place of `K` and `q`, `q'`
two finite places of `L` above `Q`.  The local fields `L_q`, `L_{q'}` are isomorphic as
`K_Q`-algebras (the Galois group of `L/K` acts transitively on the places above `Q`), and the norm
map is an invariant of the `K_Q`-algebra up to isomorphism.  Consequently the local norm groups
agree:

`N_{L_q/K_Q} L_qˣ = N_{L_{q'}/K_Q} L_{q'}ˣ`.

This is the reason why "`x ∈ K_Qˣ` is a norm from `L_w` for some `w | Q`" is equivalent to
"`x` is a norm from `L_w` for all `w | Q`", i.e. why the local norm subgroup
`NK.CFTLib.IdeleHasse.localNormSubgroup K L (Place.ofFinite Q)` is the supremum of a family of
*equal* subgroups.
-/

set_option autoImplicit false
set_option linter.unusedSectionVars false
set_option linter.style.haveILetI false

open scoped NumberField Pointwise

namespace NK.CFTLib.IdeleHasse

/-- **The range of the norm map on units is invariant under a `K_Q`-algebra isomorphism.**

The norm is invariant under conjugation by an algebra equivalence
(`Algebra.norm_eq_of_algEquiv`), hence the range of `Units.map (Algebra.norm R)` on the units of
`A` and on the units of `B` coincide as subgroups of `Rˣ`. -/
theorem range_units_map_norm_eq_of_algEquiv {R A B : Type*} [CommRing R] [Ring A] [Ring B]
    [Algebra R A] [Algebra R B] (e : A ≃ₐ[R] B) :
    (Units.map (Algebra.norm R : A →* R)).range
      = (Units.map (Algebra.norm R : B →* R)).range := by
  refine le_antisymm ?_ ?_
  · rintro z ⟨y, rfl⟩
    refine ⟨Units.map (e.toRingEquiv.toMonoidHom : A →* B) y, ?_⟩
    apply Units.ext
    rw [Units.coe_map, Units.coe_map, Units.coe_map]
    exact Algebra.norm_eq_of_algEquiv e (y : A)
  · rintro z ⟨y, rfl⟩
    refine ⟨Units.map ((e.symm).toRingEquiv.toMonoidHom : B →* A) y, ?_⟩
    apply Units.ext
    rw [Units.coe_map, Units.coe_map, Units.coe_map]
    exact Algebra.norm_eq_of_algEquiv e.symm (y : B)

theorem range_localNormFinite_eq_of_liesOver {K L : Type} [Field K] [NumberField K]
    [Field L] [NumberField L] [Algebra K L] [FiniteDimensional K L] [IsGalois K L]
    (Q : IsDedekindDomain.HeightOneSpectrum (NumberField.RingOfIntegers K))
    (q q' : IsDedekindDomain.HeightOneSpectrum (NumberField.RingOfIntegers L))
    (hq : q.asIdeal.LiesOver Q.asIdeal) (hq' : q'.asIdeal.LiesOver Q.asIdeal) :
    MonoidHom.range (NK.GlobalCFT.Place.localNormFinite q Q hq) =
      MonoidHom.range (NK.GlobalCFT.Place.localNormFinite q' Q hq') := by
  classical
  haveI : q.asIdeal.LiesOver Q.asIdeal := hq
  haveI : q'.asIdeal.LiesOver Q.asIdeal := hq'
  -- The Galois group of `L/K` acts transitively on the places of `L` above `Q`.
  obtain ⟨σ, hσ⟩ :=
    Commons.NumberTheory.RamificationInertia.exists_smul_valuationSubringAtPrime_eq
      (K := K) (L := L) Q q q'
  -- Rewrite "the valuation ring of `q` is carried to that of `q'`" as a `comap` statement.
  have hV : IsDedekindDomain.HeightOneSpectrum.valuationSubringAtPrime L q' =
      (IsDedekindDomain.HeightOneSpectrum.valuationSubringAtPrime L q).comap
        (σ.symm : L →+* L) := by
    rw [← hσ]
    exact Submission.NeukirchUchida.Local.smul_eq_comap_symm_alg _ σ
  -- The global isomorphism `σ` therefore induces an isomorphism of the local fields over `K_Q`.
  obtain ⟨e⟩ :=
    NK.NumberTheory.NumberField.Completion.exists_algEquiv_adicCompletion_of_valuationSubringAtPrime_comap
      σ Q q q' hq hq' hV
  -- Install the `K_Q`-algebra structures used by `localNormFinite`.
  letI : Algebra (IsDedekindDomain.HeightOneSpectrum.adicCompletion K Q)
      (IsDedekindDomain.HeightOneSpectrum.adicCompletion L q) :=
    (Commons.RingTheory.Henselian.adicCompletionMap Q q hq).toAlgebra
  letI : Algebra (IsDedekindDomain.HeightOneSpectrum.adicCompletion K Q)
      (IsDedekindDomain.HeightOneSpectrum.adicCompletion L q') :=
    (Commons.RingTheory.Henselian.adicCompletionMap Q q' hq').toAlgebra
  have h1 : NK.GlobalCFT.Place.localNormFinite q Q hq =
      Units.map (Algebra.norm (IsDedekindDomain.HeightOneSpectrum.adicCompletion K Q) :
        IsDedekindDomain.HeightOneSpectrum.adicCompletion L q →*
          IsDedekindDomain.HeightOneSpectrum.adicCompletion K Q) := rfl
  have h2 : NK.GlobalCFT.Place.localNormFinite q' Q hq' =
      Units.map (Algebra.norm (IsDedekindDomain.HeightOneSpectrum.adicCompletion K Q) :
        IsDedekindDomain.HeightOneSpectrum.adicCompletion L q' →*
          IsDedekindDomain.HeightOneSpectrum.adicCompletion K Q) := rfl
  rw [h1, h2]
  exact range_units_map_norm_eq_of_algEquiv e

end NK.CFTLib.IdeleHasse
