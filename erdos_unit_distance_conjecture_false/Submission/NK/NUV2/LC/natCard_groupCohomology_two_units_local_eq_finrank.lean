import Mathlib
import Submission.NK.NUV2.ABHN.unitsLevelH2_card
import Submission.NK.NUV2.LC.unitsLevelH2_addOrderOf_realization
import Submission.NK.NUV2.ABHN.CommonsImports

/-!
# The local Brauer group of a Galois extension of a local field

`NK.NUV2.LC.natCard_groupCohomology_two_units_local_eq_finrank`:
for `K` a number field, `Q` a finite place of `K`, `F` a finite extension of the `Q`-adic
completion `K_Q` and `E / F` a finite Galois extension,

  `#H²(Gal(E/F), Eˣ) = [E : F]`.

Both inequalities are on disk:

* the **lower bound** `[E : F] ≤ #H²(...)` is
  `Commons.NumberTheory.NumberField.Completion.groupCohomology_two_units_ge_finrank` (the local
  fundamental class, transported from its number-field form `ge_finrank_adicCompletion_of_galois`);
* the **upper bound** `#H²(...) ≤ [E : F]` is
  `Commons.NumberTheory.NumberField.Completion.natCard_groupCohomology_two_units_le_finrank_of_solvable`
  (the solvable dévissage), which however requires `Gal(E/F)` to be **solvable**.

The content of this file is the case of the upper bound at an arbitrary finite base `F` of a
`p`-adic field: `Gal(E/F)` is solvable for `E/F` a finite Galois extension of a local field.  The
workspace has solvability only at the *base* `K_Q` (`NK.NUV2.LC.isSolvable_algEquiv_local`, via
the ramification filtration), so — exactly as in `groupCohomology_two_units_ge_finrank` — we
realise `F` as the completion `L_q` of a number field `L` and `E` as the completion
`L'_{q'}` of a *Galois* extension `L'/L` of number fields
(`exists_algEquiv_adicCompletion_of_finiteDimensional`,
`exists_galois_adicCompletion_of_finiteDimensional`), where
`NK.NUV2.ABHN.solvable_algEquiv_adicCompletion` supplies the solvability of
`Gal(L'_{q'}/L_q)`; the whole statements are then transported back along the two algebra
isomorphisms.

Everything used is on disk; this file only assembles.
-/

open CategoryTheory Representation groupCohomology

namespace NK.NUV2.LC

set_option maxHeartbeats 2000000
set_option synthInstance.maxHeartbeats 4000000
set_option linter.style.haveILetI false
set_option linter.unusedSectionVars false

open IsDedekindDomain.HeightOneSpectrum in
/-- **The upper bound `#H²(Gal(E/F), Eˣ) ≤ [E : F]` for a finite Galois extension of a local
field.**  Obtained from the number-field-completion form by realising the base and the extension
as completions of number fields, where `Gal` is solvable by the ramification filtration. -/
theorem natCard_groupCohomology_two_units_le_finrank_local
    {K : Type} [Field K] [NumberField K]
    (Q : IsDedekindDomain.HeightOneSpectrum (NumberField.RingOfIntegers K))
    {F E : Type} [Field F] [Field E]
    [Algebra (Q.adicCompletion K) F] [Algebra F E] [Algebra (Q.adicCompletion K) E]
    [IsScalarTower (Q.adicCompletion K) F E]
    [FiniteDimensional (Q.adicCompletion K) F] [FiniteDimensional F E]
    [FiniteDimensional (Q.adicCompletion K) E]
    [IsGalois F E] :
    Nat.card (↥(groupCohomology (Rep.ofAlgebraAutOnUnits F E) 2)) ≤ Module.finrank F E := by
  classical
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
  -- ## Step 4: the local Galois group of `L'_{q'} / L_q` is solvable (ramification filtration)
  haveI hsolv : Group.IsSolvable
      (q'.adicCompletion L' ≃ₐ[q.adicCompletion L] q'.adicCompletion L') :=
    NK.NUV2.ABHN.solvable_algEquiv_adicCompletion q q' hq'
  haveI : FiniteDimensional (q.adicCompletion L) (q'.adicCompletion L') :=
    Commons.NumberTheory.NumberField.Completion.module_finite_adicCompletion q q' hq'
  haveI : IsGalois (q.adicCompletion L) (q'.adicCompletion L') :=
    Commons.NumberTheory.NumberField.Completion.isGalois_adicCompletion q q' hq'
  -- ## Step 5: the upper bound at the number-field realization
  have hub :=
    Commons.NumberTheory.NumberField.Completion.natCard_groupCohomology_two_units_le_finrank_of_solvable
      (K := L) (Q := q) (F := q.adicCompletion L) (E := q'.adicCompletion L') hsolv
  -- ## Step 6: transport the two sides back to `(F, E)`
  have hcard₁ : Nat.card (↥(groupCohomology (Rep.ofAlgebraAutOnUnits (q.adicCompletion L) E) 2))
      = Nat.card (↥(groupCohomology (Rep.ofAlgebraAutOnUnits F E) 2)) := by
    obtain ⟨h⟩ :=
      Commons.NumberTheory.NumberField.Completion.addEquiv_groupCohomology_two_units_baseRingEquiv
        (M := F) (M' := q.adicCompletion L) (E := E) e.toRingEquiv hhe
    exact Nat.card_congr h.toEquiv.symm
  have hcard₂ : Nat.card (↥(groupCohomology (Rep.ofAlgebraAutOnUnits (q.adicCompletion L) E) 2))
      = Nat.card (↥(groupCohomology
          (Rep.ofAlgebraAutOnUnits (q.adicCompletion L) (q'.adicCompletion L')) 2)) :=
    Commons.NumberTheory.NumberField.Completion.natCard_groupCohomology_two_units_topAlgEquiv
      (F := q.adicCompletion L) e'
  have hrank₁ : Module.finrank (q.adicCompletion L) E = Module.finrank F E :=
    Commons.NumberTheory.NumberField.Completion.finrank_eq_of_algebraMap_eq
      (E := E) e.toRingEquiv hhe
  have hrank₂ : Module.finrank (q.adicCompletion L) E =
      Module.finrank (q.adicCompletion L) (q'.adicCompletion L') :=
    (AlgEquiv.toLinearEquiv e').finrank_eq
  calc Nat.card (↥(groupCohomology (Rep.ofAlgebraAutOnUnits F E) 2))
      = Nat.card (↥(groupCohomology (Rep.ofAlgebraAutOnUnits (q.adicCompletion L) E) 2)) :=
        hcard₁.symm
    _ = Nat.card (↥(groupCohomology
          (Rep.ofAlgebraAutOnUnits (q.adicCompletion L) (q'.adicCompletion L')) 2)) := hcard₂
    _ ≤ Module.finrank (q.adicCompletion L) (q'.adicCompletion L') := hub
    _ = Module.finrank (q.adicCompletion L) E := hrank₂.symm
    _ = Module.finrank F E := hrank₁

open IsDedekindDomain.HeightOneSpectrum in
/-- **The order of the relative Brauer group of a Galois extension of a local field is the
degree.**  For `K` a number field, `Q` a finite place of `K`, `F` a finite extension of the
`Q`-adic completion `K_Q` and `E / F` finite Galois, the second cohomology of the units has
cardinality `[E : F]`.  This is `H²(Gal(E/F), Eˣ) ≅ ℤ/[E : F]` (local reciprocity). -/
theorem natCard_groupCohomology_two_units_local_eq_finrank {K : Type} [Field K]
    [NumberField K] (Q : IsDedekindDomain.HeightOneSpectrum (NumberField.RingOfIntegers K))
    {F E : Type} [Field F] [Field E] [Algebra (Q.adicCompletion K) F] [Algebra F E]
    [Algebra (Q.adicCompletion K) E] [IsScalarTower (Q.adicCompletion K) F E]
    [FiniteDimensional (Q.adicCompletion K) F] [FiniteDimensional F E]
    [FiniteDimensional (Q.adicCompletion K) E] [IsGalois F E] :
    Nat.card (↥(groupCohomology (Rep.ofAlgebraAutOnUnits F E) 2)) = Module.finrank F E :=
  le_antisymm (natCard_groupCohomology_two_units_le_finrank_local Q)
    (Commons.NumberTheory.NumberField.Completion.groupCohomology_two_units_ge_finrank Q)

end NK.NUV2.LC
