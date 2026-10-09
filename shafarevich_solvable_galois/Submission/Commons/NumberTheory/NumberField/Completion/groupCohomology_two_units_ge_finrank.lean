import Mathlib
import Submission.Commons.NumberTheory.NumberField.Completion.natCard_groupCohomology_two_units_le_finrank_of_abelian
import Submission.Commons.NumberTheory.NumberField.Completion.natCard_groupCohomology_two_units_eq_card_of_cyclic_arbitrary_base
import Submission.Commons.NumberTheory.NumberField.Completion.exists_algEquiv_adicCompletion_of_finiteDimensional
import Submission.Commons.NumberTheory.NumberField.Completion.exists_galois_adicCompletion_of_finiteDimensional
import Submission.Commons.NumberTheory.NumberField.Completion.exists_unramified_extension_of_inertiaDeg
import Submission.Commons.NumberTheory.NumberField.Completion.norm_units_surjective_of_ramificationIdx_eq_one
import Submission.Commons.NumberTheory.NumberField.Completion.isCyclic_algEquiv_adicCompletion_of_ramificationIdx_eq_one
import Submission.Commons.NumberTheory.NumberField.Completion.natCard_algEquiv_adicCompletion_eq_ramificationIdx_mul_inertiaDeg
import Submission.Commons.NumberTheory.NumberField.Completion.module_finite_adicCompletion
import Submission.Commons.NumberTheory.NumberField.Completion.natCard_quotient_units_range_norm_le_finrank_of_abelian_local
import Submission.Commons.NumberTheory.NumberField.Completion.ge_finrank_adicCompletion_of_galois
import Submission.Commons.NumberTheory.NumberField.Completion.natCard_groupCohomology_two_units_topAlgEquiv
import Submission.Commons.NumberTheory.NumberField.Completion.addEquiv_groupCohomology_two_units_baseRingEquiv
import Submission.Commons.RepresentationTheory.GroupCohomology.H2_inflation_injective_of_subsingleton_H1
import Submission.Commons.RepresentationTheory.GroupCohomology.H2_inflation_restriction_exact_of_subsingleton_H1
import Submission.Commons.RepresentationTheory.GroupCohomology.natCard_nsmul_H2_eq_zero
-- PORT435-BEGIN (v4.35 isDefEq respectTransparency compat)
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- PORT435-END

/-!
# The lower bound `[E : F] ≤ #H²(Gal(E/F), Eˣ)` for local fields

Local class field theory (`Milne, *Class Field Theory*, III.2`, Lemma 2.2 / Theorem 2.1) states
that for a finite Galois extension `E/F` of local fields,

  `[E : F] ≤ #H²(Gal(E/F), Eˣ)`,

with equality in fact.  This file proves the *lower bound* in the abstract setting where `F` is a
finite extension of `F₀ = Q.adicCompletion K` for a number field `K` and a finite place `Q`.

## Proof

The mathematical content is the number-field form
`Commons.NumberTheory.NumberField.Completion.ge_finrank_adicCompletion_of_galois`: for number
fields `L ⊆ L'` with `L'/L` Galois and places `q' | q`,

  `[L'_{q'} : L_q] ≤ #H²(Gal(L'_{q'}/L_q), (L'_{q'})ˣ)`.

Everything else is the reduction of the abstract statement to that one.  Since every finite
extension of the local field `Q.adicCompletion K` is the completion of a number field
(`exists_algEquiv_adicCompletion_of_finiteDimensional`), and since the Galois extension `E/F`
can be realized by a Galois extension of number fields
(`exists_galois_adicCompletion_of_finiteDimensional`), it suffices to transport the inequality
along the two algebra isomorphisms `F ≅ q.adicCompletion L` and `E ≅ q'.adicCompletion L'`:

* `Module.finrank` is invariant under a change of base ring along a ring isomorphism that
  commutes with the structure maps (`finrank_eq_of_algebraMap_eq`), and unchanged by an
  algebra isomorphism of the total algebra (`LinearEquiv.finrank_eq`);
* `Nat.card` of `H²` of the units representation is invariant under a change of base ring
  (`addEquiv_groupCohomology_two_units_baseRingEquiv`) and under a base-field-mapping algebra
  isomorphism of the total algebra (`natCard_groupCohomology_two_units_topAlgEquiv`).

The only subtlety is that the `q.adicCompletion L`-algebra structure on `E` obtained by
transporting the `F`-algebra structure along `F ≅ q.adicCompletion L` has to be introduced as a
`letI` *before* any of the transport lemmas is applied; this is done below and elaborates
without trouble (the instance-search issue recorded in
`NOTE_session25_ge_finrank_general_twist.md` §8 does not arise with all implicit arguments of the
realization lemmas instantiated in the way used here).
-/

open CategoryTheory Representation groupCohomology

namespace Commons.NumberTheory.NumberField.Completion

set_option maxHeartbeats 2000000
set_option synthInstance.maxHeartbeats 4000000
set_option linter.style.haveILetI false
set_option linter.unusedSectionVars false

/-- **The lower bound / local fundamental class.**  For a finite Galois extension `E/F` of local
fields over `F = Q.adicCompletion K`, the second cohomology of the units of `E` has cardinality at
least the degree `[E : F]`.  This is Milne, *Class Field Theory*, III.2 (Lemma 2.2 / Theorem 2.1);
here it is deduced from the number-field form
`Commons.NumberTheory.NumberField.Completion.ge_finrank_adicCompletion_of_galois`. -/
theorem groupCohomology_two_units_ge_finrank
    {K : Type} [Field K] [NumberField K]
    (Q : IsDedekindDomain.HeightOneSpectrum (NumberField.RingOfIntegers K))
    {F E : Type} [Field F] [Field E]
    [Algebra (Q.adicCompletion K) F] [Algebra F E] [Algebra (Q.adicCompletion K) E]
    [IsScalarTower (Q.adicCompletion K) F E]
    [FiniteDimensional (Q.adicCompletion K) F] [FiniteDimensional F E]
    [FiniteDimensional (Q.adicCompletion K) E]
    [IsGalois F E] :
    Module.finrank F E ≤ Nat.card (groupCohomology (Rep.ofAlgebraAutOnUnits F E) 2) := by
  -- ## Step 1: realize the base field `F` as the completion `q.adicCompletion L`
  obtain ⟨L : Type, hLf, hLn, hLa, q, hq, ⟨e⟩⟩ :=
    Commons.NumberTheory.NumberField.Completion.exists_algEquiv_adicCompletion_of_finiteDimensional
      (Q := Q) (B := F)
  letI : Field L := hLf
  letI : NumberField L := hLn
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
  -- ## Step 3: realize the Galois extension `E / q.adicCompletion L` by a Galois extension of
  -- number fields `L' / L`
  obtain ⟨L' : Type, hL'f, hL'n, hL'a, q', hq', hgal', ⟨e'⟩⟩ :=
    Commons.NumberTheory.NumberField.Completion.exists_galois_adicCompletion_of_finiteDimensional
      (Q := q) (B := E)
  letI : Field L' := hL'f
  letI : NumberField L' := hL'n
  letI : Algebra L L' := hL'a
  letI : Algebra (q.adicCompletion L) (q'.adicCompletion L') :=
    RingHom.toAlgebra (Commons.RingTheory.Henselian.adicCompletionMap q q' hq')
  haveI : FiniteDimensional L L' := Module.Finite.of_restrictScalars_finite ℚ L L'
  haveI : IsGalois L L' := hgal'
  -- ## Step 4: the number-field form of the inequality
  have hglobal := Commons.NumberTheory.NumberField.Completion.ge_finrank_adicCompletion_of_galois
    (L := L) (L' := L') q q' hq'
  -- ## Step 5: transport the two sides back to `(F, E)`
  have hcard₁ : Nat.card (groupCohomology (Rep.ofAlgebraAutOnUnits (q.adicCompletion L) E) 2)
      = Nat.card (groupCohomology (Rep.ofAlgebraAutOnUnits F E) 2) := by
    obtain ⟨h⟩ :=
      Commons.NumberTheory.NumberField.Completion.addEquiv_groupCohomology_two_units_baseRingEquiv
        (M := F) (M' := q.adicCompletion L) (E := E) e.toRingEquiv hhe
    exact Nat.card_congr h.toEquiv.symm
  have hcard₂ : Nat.card (groupCohomology (Rep.ofAlgebraAutOnUnits (q.adicCompletion L) E) 2)
      = Nat.card (groupCohomology
          (Rep.ofAlgebraAutOnUnits (q.adicCompletion L) (q'.adicCompletion L')) 2) :=
    Commons.NumberTheory.NumberField.Completion.natCard_groupCohomology_two_units_topAlgEquiv
      (F := q.adicCompletion L) e'
  have hrank₁ : Module.finrank (q.adicCompletion L) E = Module.finrank F E :=
    Commons.NumberTheory.NumberField.Completion.finrank_eq_of_algebraMap_eq
      (E := E) e.toRingEquiv hhe
  have hrank₂ : Module.finrank (q.adicCompletion L) E =
      Module.finrank (q.adicCompletion L) (q'.adicCompletion L') :=
    (AlgEquiv.toLinearEquiv e').finrank_eq
  calc Module.finrank F E
      = Module.finrank (q.adicCompletion L) E := hrank₁.symm
    _ = Module.finrank (q.adicCompletion L) (q'.adicCompletion L') := hrank₂
    _ ≤ Nat.card (groupCohomology
          (Rep.ofAlgebraAutOnUnits (q.adicCompletion L) (q'.adicCompletion L')) 2) := hglobal
    _ = Nat.card (groupCohomology (Rep.ofAlgebraAutOnUnits (q.adicCompletion L) E) 2) :=
        hcard₂.symm
    _ = Nat.card (groupCohomology (Rep.ofAlgebraAutOnUnits F E) 2) := hcard₁

end Commons.NumberTheory.NumberField.Completion
