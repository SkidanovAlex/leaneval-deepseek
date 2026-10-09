import Mathlib
import Submission.Work.SSGRoute.Step4CokerData
import Submission.Work.SSGRoute.Interfaces
import Submission.Work.SSGRoute.step4_y_alpha_one_prime
-- PORT435-BEGIN (v4.35 isDefEq respectTransparency compat)
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- PORT435-END

/-! # Auxiliary structural facts about a coker-side datum `D` (node `step4_y_exists`)

These are the consequences of the stage-3 data of `Step4CokerData p K n i j` that every step of the
construction of the datum `y` of Schmidt–Wingberg's Fourth Step uses.  They are separated from
`Submission/Work/SSGRoute/step4_y_exists.lean` (whose target still contains the arithmetic `sorry`)
so that they can be imported on their own — in particular by the lemmas of the assembly, which must
stay axiom-clean.

* `step4_psi_ramified_isSplitIn`: at a finite place where the pushed-down level-`n` map `D.psi` has a
  nontrivial inertia element inside `G_K` (a place of *new ramification*), the decomposition group is
  contained in `G_K`, i.e. the place is completely decomposed in `K/ℚ`.  (Last clause of
  `IsProperStageData`.)
* `step4_psi_ramified_not_over_p`: such a place is never over `p`.  (`T¹`-clause of
  `IsProperStageData`: the places over `p` are `T¹`-places, and there `ψ` is trivial on `D_A ∩ G_K`.)

The two together are exactly the hypotheses of `Work.SSGRoute.step4_local_target`, which provides the
local targets `ηt` of `Step4YData` at the places of new ramification. -/

namespace Work.SSGRoute

open _root_.SSGRoute
open Work.CohomologicalShrinking

variable {p : ℕ} [Fact p.Prime] {K : IntermediateField ℚ SSGRoute.QBar}
  [FiniteDimensional ℚ K] [Normal ℚ K] {n i j : ℕ}

/-- **A place of "new ramification" is completely decomposed in `K`.**  If the pushed-down level-`n`
map `D.psi` has a nontrivial inertia element inside `G_K` at a finite place `A`, then the whole
decomposition group of `A` lies in `G_K`. -/
theorem step4_psi_ramified_isSplitIn (D : Step4CokerData p K n i j)
    (A : ValuationSubring SSGRoute.QBar) (hAfin : SSGRoute.IsFinPlace ℚ A)
    (h : ∃ σ, SSGRoute.IsInertia ℚ A σ ∧ σ ∈ K.fixingSubgroup ∧ D.psi σ ≠ 1) :
    SSGRoute.IsSplitIn ℚ K A := by
  obtain ⟨σ, hσI, hσK, hσne⟩ := h
  have hψm : D.ψm σ ≠ 1 := fun h1 =>
    hσne (by rw [Step4CokerData.psi, MonoidHom.comp_apply, h1, map_one])
  exact (D.data.2.2.2.2.2 A hAfin ⟨σ, hσI, hσK, hψm⟩).1

/-- **A place of "new ramification" is not over `p`.**  The `T¹`-clause of the stage-3 data forces
`ψ` to be trivial on `D_A ∩ G_K` at every place over `p`. -/
theorem step4_psi_ramified_not_over_p (D : Step4CokerData p K n i j)
    (A : ValuationSubring SSGRoute.QBar) (hAfin : SSGRoute.IsFinPlace ℚ A)
    (h : ∃ σ, SSGRoute.IsInertia ℚ A σ ∧ σ ∈ K.fixingSubgroup ∧ D.psi σ ≠ 1) :
    ¬ A.valuation (p : SSGRoute.QBar) < 1 := by
  obtain ⟨σ, hσI, hσK, hσne⟩ := h
  intro hp
  have hT1 : SSGRoute.IsT1Place p K A := ⟨hAfin, Or.inl hp⟩
  have hψm : D.ψm σ = 1 := D.data.2.2.2.1 A hT1 σ hσI.1 hσK
  exact hσne (by rw [Step4CokerData.psi, MonoidHom.comp_apply, hψm, map_one])

/-- **The local target at a place of new ramification, in the form required by `Step4YData`.**

This is the instantiation of `Work.SSGRoute.step4_local_target` (via
`Work.SSGRoute.step4_y_alpha_one_prime`) at an element `A ∈ D.S` at which the level-`n` stage-`τ`
solution `D.phi` is trivial on the whole of `D_A` and the level-`n` stage-`τ+1` solution `D.psi` has
a nontrivial inertia element inside `G_K`.  The two hypotheses of `step4_local_target` that are not
part of the data of `D` — that `A` is not over `p`, and that `D_A ≤ G_K` — are supplied by
`step4_psi_ramified_not_over_p` and `step4_psi_ramified_isSplitIn`. -/
theorem step4_local_target_at_new_ram (D : Step4CokerData p K n i j) (hj : 1 ≤ j) (hji : j ≤ i)
    (A : ValuationSubring SSGRoute.QBar) (hAfin : SSGRoute.IsFinPlace ℚ A) (hAS : A ∈ D.S)
    (hφA : ∀ σ ∈ SSGRoute.decomp ℚ A, D.phi σ = 1)
    (hram : ∃ σ, SSGRoute.IsInertia ℚ A σ ∧ σ ∈ K.fixingSubgroup ∧ D.psi σ ≠ 1) :
    ∃ η : SSGRoute.GalQ → E p (K ≃ₐ[ℚ] K) n i j,
      (∀ σ ∈ SSGRoute.decomp ℚ A, ∀ τ ∈ SSGRoute.decomp ℚ A, η (σ * τ) = η σ + η τ) ∧
      SSGRoute.IsLocConstOn (SSGRoute.decomp ℚ A) η ∧
      (∀ σ, SSGRoute.IsInertia ℚ A σ → η σ = 0) ∧
      IsCyclic (Subgroup.closure
        ((Work.SSGRoute.flowTwistE p K n i j η D.psi) ''
          (SSGRoute.decomp ℚ A : Set SSGRoute.GalQ))) ∧
      (∀ σ ∈ SSGRoute.decomp ℚ A, ∃ τ, SSGRoute.IsInertia ℚ A τ ∧
        Work.SSGRoute.flowTwistE p K n i j η D.psi τ =
          Work.SSGRoute.flowTwistE p K n i j η D.psi σ) :=
  step4_y_alpha_one_prime p K n i j hj hji D A hAS
    (step4_psi_ramified_not_over_p D A hAfin hram) hφA

end Work.SSGRoute
