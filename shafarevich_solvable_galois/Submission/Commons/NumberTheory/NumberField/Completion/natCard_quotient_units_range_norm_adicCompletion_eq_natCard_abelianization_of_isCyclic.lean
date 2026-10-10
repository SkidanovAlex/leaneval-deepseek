import Mathlib.RingTheory.DedekindDomain.AdicValuation
import Mathlib.RingTheory.RamificationInertia.Inertia
import Mathlib.RingTheory.RamificationInertia.Ramification
import Submission.Commons.NumberTheory.NumberField.Completion.exists_open_subgroup_units_tate_trivial_exp
import Submission.Commons.NumberTheory.NumberField.Completion.natCard_quotient_units_range_norm_adicCompletion_eq_mul_of_exists_open_subgroup_units_tate_trivial
-- PORT435-BEGIN (v4.35 isDefEq respectTransparency compat)
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- PORT435-END

/-!
# The norm index in the cyclic case of the local norm index theorem

This file assembles the target statement
`#(K_Qˣ ⧸ N_{L_q/K_Q}(L_qˣ)) = #Gal(L_q/K_Q)ᵃᵇ` from the two classical inputs:

* `Commons.NumberTheory.NumberField.Completion.exists_open_subgroup_units_tate_trivial_exp`: the
  existence of an open Galois-stable subgroup `W` of the units of `L_q` on which the Tate
  cohomology of the cyclic group `Gal(L_q/K_Q)` is trivial (obtained from the normal basis
  lattice `𝒪[G] ⊆ L_q` together with the `p`-adic exponential, or by a Newton approximation
  argument);
* `Commons.NumberTheory.NumberField.Completion.natCard_quotient_units_range_norm_adicCompletion_eq_mul_of_exists_open_subgroup_units_tate_trivial`:
  the "valuation sequence" computation which, given such a `W`, identifies the norm index with
  the product of the ramification index and the inertia degree (the Herbrand quotient of the
  units of a local field is `1`).

Both sides are then compared with `e(q|Q) · f(q|Q) = [L_q : K_Q] = #Gal(L_q/K_Q)`, using the
local fundamental identity of the completion and the fact that a cyclic group is commutative
(so that its abelianization is itself).
-/

set_option linter.style.haveILetI false
set_option linter.unusedSectionVars false

open scoped NumberField WithZero
open IsDedekindDomain.HeightOneSpectrum

noncomputable section

namespace Commons.NumberTheory.NumberField.Completion

theorem natCard_quotient_units_range_norm_adicCompletion_eq_natCard_abelianization_of_isCyclic
    {K L : Type*} [Field K] [NumberField K] [Field L] [NumberField L] [Algebra K L]
    [FiniteDimensional K L] [IsGalois K L]
    (Q : IsDedekindDomain.HeightOneSpectrum (NumberField.RingOfIntegers K))
    (q : IsDedekindDomain.HeightOneSpectrum (NumberField.RingOfIntegers L))
    (hq : q.asIdeal.LiesOver Q.asIdeal) :
    letI : Algebra (Q.adicCompletion K) (q.adicCompletion L) :=
      RingHom.toAlgebra (Commons.RingTheory.Henselian.adicCompletionMap Q q hq)
    IsCyclic (q.adicCompletion L ≃ₐ[Q.adicCompletion K] q.adicCompletion L) →
    Nat.card ((Q.adicCompletion K)ˣ ⧸
        MonoidHom.range (Units.map (Algebra.norm (Q.adicCompletion K) :
          q.adicCompletion L →* Q.adicCompletion K))) =
      Nat.card (Abelianization
        (q.adicCompletion L ≃ₐ[Q.adicCompletion K] q.adicCompletion L)) := by
  letI : Algebra (Q.adicCompletion K) (q.adicCompletion L) :=
    RingHom.toAlgebra (Commons.RingTheory.Henselian.adicCompletionMap Q q hq)
  intro hcyc
  -- a generator of the cyclic local Galois group
  obtain ⟨σ, hσ⟩ := isCyclic_iff_exists_zpowers_eq_top.mp hcyc
  -- the open Galois-stable subgroup with trivial Tate cohomology
  obtain ⟨W, hW⟩ := exists_open_subgroup_units_tate_trivial_exp Q q hq σ hσ
  -- the norm index is the product of the ramification index and the inertia degree
  have hindex :=
    natCard_quotient_units_range_norm_adicCompletion_eq_mul_of_exists_open_subgroup_units_tate_trivial
      Q q hq σ hσ ⟨W, hW⟩
  -- both sides equal `e · f`
  have hcardG : Nat.card (q.adicCompletion L ≃ₐ[Q.adicCompletion K] q.adicCompletion L) =
      Module.finrank (Q.adicCompletion K) (q.adicCompletion L) :=
    natCard_algEquiv_adicCompletion_eq_finrank Q q hq
  have hfin : Module.finrank (Q.adicCompletion K) (q.adicCompletion L) =
      (q.asIdeal.ramificationIdx (NumberField.RingOfIntegers K)) *
        (q.asIdeal.inertiaDeg (NumberField.RingOfIntegers K)) :=
    (Commons.NumberTheory.NumberField.finrank_adicCompletion_eq_ramificationIdx_mul_inertiaDeg
      Q q hq).symm
  have hab : Nat.card (Abelianization
      (q.adicCompletion L ≃ₐ[Q.adicCompletion K] q.adicCompletion L)) =
      (q.asIdeal.ramificationIdx (NumberField.RingOfIntegers K)) *
        (q.asIdeal.inertiaDeg (NumberField.RingOfIntegers K)) := by
    letI : CommGroup (q.adicCompletion L ≃ₐ[Q.adicCompletion K] q.adicCompletion L) :=
      IsCyclic.commGroup
    rw [Nat.card_congr (Abelianization.equivOfComm).symm.toEquiv, hcardG, hfin]
  rw [hindex, hab]

end Commons.NumberTheory.NumberField.Completion
