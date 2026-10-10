import Mathlib.RingTheory.DedekindDomain.AdicValuation
import Mathlib.RingTheory.RamificationInertia.Inertia
import Mathlib.RingTheory.RamificationInertia.Ramification
import Submission.Commons.NumberTheory.NumberField.Completion.natCard_quotient_units_range_norm_eq_card_of_abelian_pgroup_base
import Submission.NK.GlobalCFT.Place
-- PORT435-BEGIN (v4.35 isDefEq respectTransparency compat)
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- PORT435-END

set_option linter.style.haveILetI false
set_option linter.unusedVariables false

/-!
# The ramification index is one when the local units are norms

If `L / K` is a finite Galois extension of number fields whose local extension `L_q / K_Q` at a
finite place `q | Q` has all local units of `K_Q` in the image of the local norm (i.e. the norm on
units is surjective), then `q | Q` is unramified: `e(q|Q) = 1`.

The proof is the classical norm-index computation for local fields.  Writing
`B = K_Qˣ`, `U = 𝒪_{K_Q}ˣ` for the local units, and `N = N_{L_q/K_Q}(L_qˣ) ≤ B`:

* the "valuation" formula splits the norm index as
  `#(B ⧸ N) = f · [U : U ∩ N]` (kernel of the valuation logarithm, Herbrand quotient);
* the cyclic norm index theorem gives `#(B ⧸ N) = #Gal(L_q/K_Q) = e · f`.

The hypothesis says `U ≤ N`, so `[U : U ∩ N] = 1` and hence `e · f = f`, so `e = 1` as `f ≠ 0`.
-/

namespace IsDedekindDomain.HeightOneSpectrum

/-- The prime ideal underlying a point of the height one spectrum (an alias for `asIdeal`). -/
abbrev asIdeIdeal {R : Type*} [CommRing R] (q : HeightOneSpectrum R) : Ideal R := q.asIdeal

end IsDedekindDomain.HeightOneSpectrum

namespace NK.CFTLib.Existence

open IsDedekindDomain

theorem ramificationIdx_eq_one_of_localUnits_le_localNorm
    {K : Type} [Field K] [NumberField K] {L : Type} [Field L] [NumberField L] [Algebra K L]
    [FiniteDimensional K L] [IsGalois K L] {p : ℕ} [Fact p.Prime]
    (hcyc : IsCyclic (L ≃ₐ[K] L)) (hdeg : Module.finrank K L = p)
    (Q : IsDedekindDomain.HeightOneSpectrum (NumberField.RingOfIntegers K))
    (q : IsDedekindDomain.HeightOneSpectrum (NumberField.RingOfIntegers L))
    (hq : q.asIdeal.LiesOver Q.asIdeal)
    (hsurj : ∀ u ∈ NK.GlobalCFT.Place.localUnits K (NK.GlobalCFT.Place.ofFinite Q),
      ∃ u' ∈ NK.GlobalCFT.Place.localUnits L (NK.GlobalCFT.Place.ofFinite q),
        NK.GlobalCFT.Place.localNormFinite q Q hq u' = u) :
    q.asIdeIdeal.ramificationIdx (NumberField.RingOfIntegers K) = 1 := by
  letI : Algebra (Q.adicCompletion K) (q.adicCompletion L) :=
    RingHom.toAlgebra (Commons.RingTheory.Henselian.adicCompletionMap Q q hq)
  set N : Subgroup (Q.adicCompletion K)ˣ :=
    MonoidHom.range (Units.map (Algebra.norm (Q.adicCompletion K) :
      q.adicCompletion L →* Q.adicCompletion K)) with hN
  set U : Subgroup (Q.adicCompletion K)ˣ :=
    Commons.NumberTheory.NumberField.Completion.adicUnitsVal K Q with hU
  have hUN : U ≤ N := by
    intro u hu
    have hmem : u ∈ NK.GlobalCFT.Place.localUnits K (NK.GlobalCFT.Place.ofFinite Q) := by
      rw [NK.GlobalCFT.Place.mem_localUnits_ofFinite_iff_valued_eq_one]
      exact (Commons.NumberTheory.NumberField.Completion.mem_adicUnitsVal K Q u).mp
        (by rw [hU] at hu; exact hu)
    obtain ⟨u', _hu', hnorm⟩ := hsurj u hmem
    rw [hN]
    refine ⟨u', ?_⟩
    rw [← hnorm]
    rfl
  -- The valuation formula for the norm index.
  have hval := Commons.NumberTheory.NumberField.Completion.NormIndexUnits.natCard_quotient_units_range_norm_adicCompletion_eq_mul_adicUnitsVal_aux Q q hq
  rw [← hN, ← hU] at hval
  have hunit_index : N.relIndex U = 1 := Subgroup.relIndex_eq_one.mpr hUN
  have hval' : Nat.card ((Q.adicCompletion K)ˣ ⧸ N) =
      q.asIdeal.inertiaDeg (NumberField.RingOfIntegers K) := by
    rw [hval, hunit_index, mul_one]
  -- The cyclic norm index theorem for the local extension.
  haveI hGalCyc : IsCyclic (L ≃ₐ[K] L) := hcyc
  have hdecCyc : IsCyclic (Commons.NumberTheory.NumberField.Completion.decompositionSubgroup
      (K := K) q) :=
    isCyclic_of_injective (Subgroup.subtype _) (fun a b h => Subtype.ext h)
  have hcycLocal : IsCyclic (q.adicCompletion L ≃ₐ[Q.adicCompletion K] q.adicCompletion L) :=
    (Commons.NumberTheory.NumberField.Completion.decompositionSubgroupMulEquivLocalGalois
      Q q hq).isCyclic.mp hdecCyc
  have hquot := Commons.NumberTheory.NumberField.Completion.natCard_quotient_units_range_norm_adicCompletion_eq_natCard_abelianization_of_isCyclic
    Q q hq hcycLocal
  have hquot' : Nat.card ((Q.adicCompletion K)ˣ ⧸ N) =
      Nat.card (Abelianization (q.adicCompletion L ≃ₐ[Q.adicCompletion K] q.adicCompletion L)) := by
    rw [hN]
    exact hquot
  have hab : Nat.card (Abelianization
        (q.adicCompletion L ≃ₐ[Q.adicCompletion K] q.adicCompletion L)) =
      q.asIdeal.ramificationIdx (NumberField.RingOfIntegers K) *
        q.asIdeal.inertiaDeg (NumberField.RingOfIntegers K) := by
    letI : CommGroup (q.adicCompletion L ≃ₐ[Q.adicCompletion K] q.adicCompletion L) :=
      IsCyclic.commGroup
    rw [Nat.card_congr (Abelianization.equivOfComm).symm.toEquiv]
    exact Commons.NumberTheory.NumberField.Completion.natCard_algEquiv_adicCompletion_eq_ramificationIdx_mul_inertiaDeg
      Q q hq
  -- Combine: `e · f = f`.
  have hef : q.asIdeal.ramificationIdx (NumberField.RingOfIntegers K) *
      q.asIdeal.inertiaDeg (NumberField.RingOfIntegers K) =
      q.asIdeal.inertiaDeg (NumberField.RingOfIntegers K) := by
    rw [← hquot'.trans hab, hval']
  have hf : 0 < q.asIdeal.inertiaDeg (NumberField.RingOfIntegers K) :=
    Ideal.inertiaDeg_pos q.asIdeal (NumberField.RingOfIntegers K)
  have he : q.asIdeal.ramificationIdx (NumberField.RingOfIntegers K) = 1 :=
    Nat.mul_right_cancel hf (by rw [hef, one_mul])
  show q.asIdeIdeal.ramificationIdx (NumberField.RingOfIntegers K) = 1
  exact he

end NK.CFTLib.Existence
