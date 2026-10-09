import Mathlib
import Submission.NK.NUV2.RouteC.crux
import Submission.Commons.NumberTheory.NumberField.Completion.exists_addOrderOf_eq_finrank_groupCohomology_two_units
import Submission.Commons.NumberTheory.NumberField.Completion.natCard_groupCohomology_two_units_le_finrank_of_abelian
import Submission.Commons.NumberTheory.NumberField.Completion.groupCohomology_two_units_ge_finrank
-- PORT435-BEGIN (v4.35 isDefEq respectTransparency compat)
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- PORT435-END

/-!
# `#H²(Gal(L_q/K_Q), L_qˣ) = #Gal(L_q/K_Q)` for an abelian local extension

For a finite Galois extension `L/K` of number fields, a place `Q` of `K` and a place `q | Q` of
`L`, the local extension `L_q / K_Q` of completions has abelian Galois group precisely when
`Gal(L_q/K_Q)` is abelian; then the second cohomology of the units is cyclic of order
`#Gal(L_q/K_Q)` (local class field theory: `H²(Gal(E/F), Eˣ) ≅ (1/n)ℤ/ℤ`).

The two numerical inputs are already available in the shared commons:

* the lower bound `[E : F] ≤ #H²(Gal(E/F), Eˣ)`
  (`Commons.NumberTheory.NumberField.Completion.groupCohomology_two_units_ge_finrank`);
* the upper bound `#H²(Gal(E/F), Eˣ) ≤ [E : F]` for *abelian* `E/F`
  (`…natCard_groupCohomology_two_units_le_finrank_of_abelian`);

together with the local fundamental class `∃ u, addOrderOf u = [E : F]`
(`…exists_addOrderOf_eq_finrank_groupCohomology_two_units`) and the order formula
`Nat.card Gal(L_q/K_Q) = [L_q : K_Q]`
(`…natCard_algEquiv_adicCompletion_eq_finrank`).
-/

set_option linter.style.haveILetI false

namespace NK.NUV2.RouteC

theorem h2_card_eq_card_of_abelian_local {K L : Type} [Field K] [NumberField K] [Field L]
    [NumberField L] [Algebra K L] [FiniteDimensional K L] [IsGalois K L]
    (Q : IsDedekindDomain.HeightOneSpectrum (NumberField.RingOfIntegers K))
    (q : IsDedekindDomain.HeightOneSpectrum (NumberField.RingOfIntegers L))
    (hq : q.asIdeal.LiesOver Q.asIdeal)
    (hcomm : ∀ σ τ : NK.NUV2.RouteC.localGaloisGroup K L Q q hq, σ * τ = τ * σ) :
    Nat.card (groupCohomology (NK.NUV2.RouteC.localUnitsRep K L Q q hq) 2)
        = Nat.card (NK.NUV2.RouteC.localGaloisGroup K L Q q hq) ∧
      ∃ u : groupCohomology (NK.NUV2.RouteC.localUnitsRep K L Q q hq) 2,
        addOrderOf u = Nat.card (NK.NUV2.RouteC.localGaloisGroup K L Q q hq) := by
  letI : Algebra (Q.adicCompletion K) (q.adicCompletion L) :=
    RingHom.toAlgebra (Commons.RingTheory.Henselian.adicCompletionMap Q q hq)
  haveI : FiniteDimensional (Q.adicCompletion K) (q.adicCompletion L) :=
    Commons.NumberTheory.NumberField.Completion.module_finite_adicCompletion Q q hq
  haveI : IsGalois (Q.adicCompletion K) (q.adicCompletion L) :=
    Commons.NumberTheory.NumberField.Completion.isGalois_adicCompletion Q q hq
  -- `#Gal(L_q/K_Q) = [L_q : K_Q]`
  have hcard : Nat.card (NK.NUV2.RouteC.localGaloisGroup K L Q q hq)
      = Module.finrank (Q.adicCompletion K) (q.adicCompletion L) :=
    Commons.NumberTheory.NumberField.Completion.natCard_algEquiv_adicCompletion_eq_finrank Q q hq
  -- upper bound on the order of `H²` (abelian case)
  have hle : Nat.card (groupCohomology (NK.NUV2.RouteC.localUnitsRep K L Q q hq) 2)
      ≤ Module.finrank (Q.adicCompletion K) (q.adicCompletion L) :=
    Commons.NumberTheory.NumberField.Completion.natCard_groupCohomology_two_units_le_finrank_of_abelian
      (Q := Q) (B := Q.adicCompletion K) (E := q.adicCompletion L) hcomm
  -- lower bound on the order of `H²` (local fundamental class)
  have hge : Module.finrank (Q.adicCompletion K) (q.adicCompletion L)
      ≤ Nat.card (groupCohomology (NK.NUV2.RouteC.localUnitsRep K L Q q hq) 2) :=
    Commons.NumberTheory.NumberField.Completion.groupCohomology_two_units_ge_finrank
      (Q := Q) (F := Q.adicCompletion K) (E := q.adicCompletion L)
  -- the local fundamental class: an element of order `[L_q : K_Q]`
  obtain ⟨u, hu⟩ :=
    Commons.NumberTheory.NumberField.Completion.exists_addOrderOf_eq_finrank_groupCohomology_two_units
      (Q := Q) (F := Q.adicCompletion K) (E := q.adicCompletion L)
  refine ⟨?_, ?_⟩
  · rw [hcard]
    exact le_antisymm hle hge
  · refine ⟨u, ?_⟩
    rw [hcard]
    exact hu

end NK.NUV2.RouteC
