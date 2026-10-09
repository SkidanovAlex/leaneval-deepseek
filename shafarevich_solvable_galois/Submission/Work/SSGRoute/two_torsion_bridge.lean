import Mathlib
import Submission.Work.SSGRoute.two_torsion_assembly
import Submission.Work.SSGRoute.gradedStep_j_one
import Submission.Work.SSGRoute.gradedStep_j_ge_two
-- PORT435-BEGIN (v4.35 isDefEq respectTransparency compat)
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- PORT435-END

/-!
# Bridge: the graded-step family from its two halves, and the `p = 2` lifting

`Work.SSGRoute.GradedStep` (defined in `two_torsion_assembly.lean`) splits, according to the second
refinement index `j`, into

* the `j = 1` ("`p`-power") family, proved in `Submission/Work/SSGRoute/gradedStep_j_one.lean`
  (`Work.SSGRoute.gradedStep_j_one`, sorry-free), and
* the `j ≥ 2` ("commutator/quadratic") family, stated in
  `Submission/Work/SSGRoute/gradedStep_j_ge_two.lean` (`Work.SSGRoute.gradedStep_j_ge_two`).

Feeding the two halves into `Work.SSGRoute.two_torsion_lift_two_of_gradedStep` produces the `p = 2`
two-torsion lifting in the shape consumed by `Work.SSGRoute.stage_local_shrinking`.
-/

open Work.CohomologicalShrinking

namespace Work.SSGRoute

/-- **The graded-step family from its two halves.** -/
theorem gradedStep_of_pieces (G : Type*) [Group G] [Fintype G] (n : ℕ) (δ : G)
    (hδ : δ * δ = 1) (hδ1 : δ ≠ 1) : GradedStep G n δ := by
  intro i j hj hji c hc hfix
  rcases eq_or_lt_of_le hj with h1 | h2
  · subst h1
    exact gradedStep_j_one G n δ hδ hδ1 i (by omega) c hc hfix
  · exact gradedStep_j_ge_two G n δ hδ hδ1 i j (by omega) hji c hc hfix

/-- **The `p = 2` two-torsion lifting** in the shape consumed by `stage_local_shrinking`. -/
theorem two_torsion_lift_two_of_pieces (K : IntermediateField ℚ SSGRoute.QBar)
    [FiniteDimensional ℚ K] [Normal ℚ K] (n i j : ℕ) (hj : 1 ≤ j) (hji : j ≤ i) :
    ∀ γ : flowGroup 2 (K ≃ₐ[ℚ] K) n i j, γ ^ 2 = 1 →
      flowQuot 2 (K ≃ₐ[ℚ] K) n i j γ ≠ 1 →
      ∃ y : flowGroup 2 (K ≃ₐ[ℚ] K) n (tauSucc i j).1 (tauSucc i j).2,
        SSGRoute.LiftsFlowAt y γ ∧ y ^ 2 = 1 := by
  classical
  haveI : Fintype (K ≃ₐ[ℚ] K) := AlgEquiv.fintype ℚ ↥K
  exact two_torsion_lift_two_of_gradedStep K n i j hj hji
    (fun δ hδ hδ1 => gradedStep_of_pieces (K ≃ₐ[ℚ] K) n δ hδ hδ1)

end Work.SSGRoute

namespace Work.SSGRoute

/-- `Work.SSGRoute.flowQuotient_antifixed_is_delta_difference_aux` (the statement of
`two_torsion_lift_two.lean`), in the *relativised* form: every anti-fixed element of `Q_{σ}` is a
`δ`-difference, derived from the graded-step family through the descent of
`Work.SSGRoute.antifixed_is_delta_difference_of_gradedStep`.

(The name carries the suffix `_of_pieces` so that it can coexist with the declaration of the same
statement in `two_torsion_lift_two.lean`; that file may replace its `sorry` by this lemma.) -/
theorem flowQuotient_antifixed_is_delta_difference_aux_of_pieces
    (K : IntermediateField ℚ SSGRoute.QBar) [FiniteDimensional ℚ K] [Normal ℚ K]
    (n i j : ℕ) (hj : 1 ≤ j) (hji : j ≤ i)
    (δ : K ≃ₐ[ℚ] K) (hδ : δ * δ = 1) (hδ1 : δ ≠ 1) :
    ∀ x : flowQuotient 2 (K ≃ₐ[ℚ] K) n i j,
      flowAction 2 (K ≃ₐ[ℚ] K) n i j δ x = x⁻¹ →
      ∃ r : flowQuotient 2 (K ≃ₐ[ℚ] K) n i j,
        x = (flowAction 2 (K ≃ₐ[ℚ] K) n i j δ r)⁻¹ * r := by
  classical
  haveI : Fintype (K ≃ₐ[ℚ] K) := AlgEquiv.fintype ℚ ↥K
  exact antifixed_is_delta_difference_of_gradedStep (G := K ≃ₐ[ℚ] K) (n := n) (δ := δ) hδ
    (gradedStep_of_pieces (K ≃ₐ[ℚ] K) n δ hδ hδ1) i j hj hji

end Work.SSGRoute
