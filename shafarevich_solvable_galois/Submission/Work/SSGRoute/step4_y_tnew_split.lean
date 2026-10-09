import Mathlib
import Submission.Work.SSGRoute.Step4CokerData
import Submission.Work.SSGRoute.step4_local_target
import Submission.Work.SSGRoute.step4_y_alpha_one_prime
import Submission.Work.SSGRoute.step4_tnew_cover
import Submission.Work.SSGRoute.twistLayer
import Submission.Work.SSGRoute.Interfaces
-- PORT435-BEGIN (v4.35 isDefEq respectTransparency compat)
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- PORT435-END

namespace Work.SSGRoute

open _root_.SSGRoute

variable {p : ℕ} [Fact p.Prime] {K : IntermediateField ℚ SSGRoute.QBar}
  [FiniteDimensional ℚ K] [Normal ℚ K] {n i j : ℕ}

/-- The places of `S` at which the *new ramification* of the level-`n` map `D.psi` occurs: those
`A ∈ D.S` at which the level-`n` stage-`τ` solution `D.phi` is trivial on the whole decomposition
group `D_A` and `D.psi` has a nontrivial inertia element inside `G_K`.  At these places `A` is
completely decomposed in `K` and is not over `p`, so `step4_local_target` supplies the local
targets `η_A`. -/
def Step4CokerData.IsNewRamp (D : Step4CokerData p K n i j)
    (A : ValuationSubring SSGRoute.QBar) : Prop :=
  (∀ σ ∈ SSGRoute.decomp ℚ A, D.phi σ = 1) ∧
  (∃ σ, SSGRoute.IsInertia ℚ A σ ∧ σ ∈ K.fixingSubgroup ∧ D.psi σ ≠ 1)

/-- The chosen prolongations `Tnew`: the places of new ramification inside `D.S`.  Since `D.S` is
pairwise non-conjugate (`D.hSdisj`), so is `Tnew`; and every place of new ramification that is
conjugate to an element of `D.S` (hence, by `step4_tnew_cover`, is `G_ℚ`-conjugate to a place of
new ramification in `D.S`) is conjugate to an element of `Tnew`. -/
theorem step4_y_tnew_split (p : ℕ) [Fact p.Prime] (K : IntermediateField ℚ SSGRoute.QBar)
    [FiniteDimensional ℚ K] [Normal ℚ K] (n i j : ℕ) (hj : 1 ≤ j) (hji : j ≤ i)
    (D : Work.SSGRoute.Step4CokerData p K n i j) :
    ∃ (Tnew : Finset (ValuationSubring SSGRoute.QBar))
      (ηt : (A : ValuationSubring SSGRoute.QBar) → A ∈ Tnew →
        SSGRoute.GalQ → Work.CohomologicalShrinking.E p (K ≃ₐ[ℚ] K) n i j),
      (∀ A ∈ Tnew, A ∈ D.S) ∧
      (∀ A ∈ Tnew, SSGRoute.IsFinPlace ℚ A) ∧
      (∀ A ∈ Tnew, ¬ A.valuation (p : SSGRoute.QBar) < 1) ∧
      (∀ A ∈ Tnew, ∀ σ ∈ SSGRoute.decomp ℚ A, D.phi σ = 1) ∧
      (∀ A ∈ Tnew, ∀ B ∈ Tnew, SSGRoute.IsConjPlace ℚ A B → A = B) ∧
      (∀ A ∈ Tnew, SSGRoute.IsSplitIn ℚ K A) ∧
      (∀ A : ValuationSubring SSGRoute.QBar, SSGRoute.IsFinPlace ℚ A → A ∉ D.T0 →
        (∃ A₀ ∈ D.S, SSGRoute.IsConjPlace ℚ A₀ A) →
        (∀ σ ∈ SSGRoute.decomp ℚ A, D.phi σ = 1) →
        (∃ σ, SSGRoute.IsInertia ℚ A σ ∧ σ ∈ K.fixingSubgroup ∧ D.psi σ ≠ 1) →
        ∃ P ∈ Tnew, SSGRoute.IsConjPlace ℚ P A) ∧
      (∀ (A : ValuationSubring SSGRoute.QBar) (hA : A ∈ Tnew),
        (∀ σ ∈ SSGRoute.decomp ℚ A, ∀ τ ∈ SSGRoute.decomp ℚ A,
          ηt A hA (σ * τ) = ηt A hA σ + ηt A hA τ) ∧
        SSGRoute.IsLocConstOn (SSGRoute.decomp ℚ A) (ηt A hA) ∧
        (∀ σ, SSGRoute.IsInertia ℚ A σ → ηt A hA σ = 0) ∧
        IsCyclic (Subgroup.closure
          ((Work.SSGRoute.flowTwistE p K n i j (ηt A hA) D.psi) ''
            (SSGRoute.decomp ℚ A : Set SSGRoute.GalQ))) ∧
        (∀ σ ∈ SSGRoute.decomp ℚ A, ∃ τ, SSGRoute.IsInertia ℚ A τ ∧
          Work.SSGRoute.flowTwistE p K n i j (ηt A hA) D.psi τ
            = Work.SSGRoute.flowTwistE p K n i j (ηt A hA) D.psi σ)) := by
  classical
  -- `Tnew` is the set of places of new ramification inside `D.S`.
  let Tnew : Finset (ValuationSubring SSGRoute.QBar) :=
    D.S.filter (fun A => D.IsNewRamp A)
  -- membership in `Tnew` unfolds to `A ∈ D.S` together with `D.IsNewRamp A`
  have hmem : ∀ A ∈ Tnew, A ∈ D.S ∧ D.IsNewRamp A := by
    intro A hA
    rw [Finset.mem_filter] at hA
    exact hA
  have hTnewS : ∀ A ∈ Tnew, A ∈ D.S := fun A hA => (hmem A hA).1
  have hTnewφ : ∀ A ∈ Tnew, ∀ σ ∈ SSGRoute.decomp ℚ A, D.phi σ = 1 :=
    fun A hA => (hmem A hA).2.1
  have hTnewram : ∀ A ∈ Tnew,
      ∃ σ, SSGRoute.IsInertia ℚ A σ ∧ σ ∈ K.fixingSubgroup ∧ D.psi σ ≠ 1 :=
    fun A hA => (hmem A hA).2.2
  have hTnewfin : ∀ A ∈ Tnew, SSGRoute.IsFinPlace ℚ A :=
    fun A hA => D.hSfin A (hTnewS A hA)
  have hTnewnotp : ∀ A ∈ Tnew, ¬ A.valuation (p : SSGRoute.QBar) < 1 :=
    fun A hA => step4_psi_ramified_not_over_p D A (hTnewfin A hA) (hTnewram A hA)
  -- The local targets: at `A ∈ Tnew` the hypotheses of `step4_y_alpha_one_prime` hold.
  have hα : ∀ A ∈ Tnew, ∃ η : SSGRoute.GalQ →
      Work.CohomologicalShrinking.E p (K ≃ₐ[ℚ] K) n i j,
      (∀ σ ∈ SSGRoute.decomp ℚ A, ∀ τ ∈ SSGRoute.decomp ℚ A, η (σ * τ) = η σ + η τ) ∧
      SSGRoute.IsLocConstOn (SSGRoute.decomp ℚ A) η ∧
      (∀ σ, SSGRoute.IsInertia ℚ A σ → η σ = 0) ∧
      IsCyclic (Subgroup.closure
        ((Work.SSGRoute.flowTwistE p K n i j η D.psi) ''
          (SSGRoute.decomp ℚ A : Set SSGRoute.GalQ))) ∧
      (∀ σ ∈ SSGRoute.decomp ℚ A, ∃ τ, SSGRoute.IsInertia ℚ A τ ∧
        Work.SSGRoute.flowTwistE p K n i j η D.psi τ
          = Work.SSGRoute.flowTwistE p K n i j η D.psi σ) :=
    fun A hA => step4_y_alpha_one_prime p K n i j hj hji D A
      (hTnewS A hA) (hTnewnotp A hA) (hTnewφ A hA)
  refine ⟨Tnew, (fun A hA => Classical.choose (hα A hA)),
    hTnewS, hTnewfin, hTnewnotp, hTnewφ, ?_, ?_, ?_, ?_⟩
  · -- `Tnew ⊆ D.S` is pairwise non-conjugate because `D.S` is.
    intro A hA B hB hc
    exact D.hSdisj A (hTnewS A hA) B (hTnewS B hB) hc
  · -- every place of `Tnew` is completely decomposed in `K` (it is of new ramification)
    intro A hA
    exact step4_psi_ramified_isSplitIn D A (hTnewfin A hA) (hTnewram A hA)
  · -- covering: every place of new ramification conjugate to `D.S` is conjugate to an element of
    -- `Tnew` (`step4_tnew_cover` gives such a place inside `D.S`)
    intro A hAfin hAT0 hconj hφ hram
    obtain ⟨P, hPS, hc, hφP, hramP⟩ := (step4_tnew_cover D).2 A hAfin hAT0 hconj hφ hram
    exact ⟨P, Finset.mem_filter.mpr ⟨hPS, hφP, hramP⟩, hc⟩
  · -- the local-target clauses, from the choice made above
    intro A hA
    exact Classical.choose_spec (hα A hA)

end Work.SSGRoute
