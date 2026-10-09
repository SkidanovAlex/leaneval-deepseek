import Mathlib
import Submission.Work.SSGRoute.Interfaces
import Submission.Work.SSGRoute.ProperStageDefs
import Submission.Work.SSGRoute.exists_cocycle_at_frob_of_split
import Submission.Work.SSGRoute.exists_split_places_avoiding
-- PORT435-BEGIN (v4.35 isDefEq respectTransparency compat)
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- PORT435-END

namespace Work.SSGRoute

set_option linter.style.haveILetI false

/-- The Frobenius element of a finite place does not depend on the proof that the place is
finite (the two proofs are equal by proof irrelevance, and `localFrobElem` is a function of the
proof-carrying place). -/
theorem localFrobElem_congr_SSGRoute {A : ValuationSubring SSGRoute.QBar}
    (h h' : SSGRoute.IsFinPlace ℚ A) :
    ((Work.SSGRoute.localFrobElem (⟨A, h⟩ : NK.FrobeniusBridge.FinitePlaceOf ℚ SSGRoute.QBar) :
        ↥(SSGRoute.decomp ℚ A)) : SSGRoute.GalQ) =
      ((Work.SSGRoute.localFrobElem (⟨A, h'⟩ : NK.FrobeniusBridge.FinitePlaceOf ℚ SSGRoute.QBar) :
        ↥(SSGRoute.decomp ℚ A)) : SSGRoute.GalQ) :=
  congrArg (fun A' : NK.FrobeniusBridge.FinitePlaceOf ℚ SSGRoute.QBar =>
      ((Work.SSGRoute.localFrobElem A' : ↥(SSGRoute.decomp ℚ A'.1)) : SSGRoute.GalQ))
    (Subtype.ext rfl)

/-- `d` splitting places avoiding a prescribed finite set, in the fixed form `k = ℚ`,
`Ω = ℚ̄` used below; the instance arguments of `Work.SSGRoute.exists_split_places_avoiding`
are given explicitly (automatic synthesis of `IsGalois ℚ ↥Λ` at the generic `k, Ω` fails
because of an instance diamond in `Algebra ℚ ↥Λ`). -/
theorem exists_split_places_avoiding_rat
    (Λ : IntermediateField ℚ SSGRoute.QBar) [FiniteDimensional ℚ Λ] [IsGalois ℚ Λ]
    (S : Finset (ValuationSubring SSGRoute.QBar)) (hS : ∀ A ∈ S, SSGRoute.IsFinPlace ℚ A) (d : ℕ) :
    ∃ T : Finset (ValuationSubring SSGRoute.QBar), T.card = d ∧
      (∀ A ∈ T, SSGRoute.IsFinPlace ℚ A) ∧
      (∀ A ∈ T, SSGRoute.IsSplitIn ℚ Λ A) ∧
      (∀ A ∈ T, ∀ B ∈ S, ¬ SSGRoute.IsConjPlace ℚ A B) ∧
      (∀ A ∈ T, ∀ B ∈ T, SSGRoute.IsConjPlace ℚ A B → A = B) :=
  @Work.SSGRoute.exists_split_places_avoiding ℚ SSGRoute.QBar
    (inferInstance : Field ℚ) (inferInstance : NumberField ℚ) (inferInstance : Field SSGRoute.QBar)
    (inferInstance : Algebra ℚ SSGRoute.QBar) (AlgebraicClosure.instIsAlgClosure ℚ)
    Λ (inferInstance : FiniteDimensional ℚ ↥Λ) (inferInstance : IsGalois ℚ ↥Λ) S hS d

theorem stage3T0Data (p : ℕ) [Fact p.Prime] (K : IntermediateField ℚ SSGRoute.QBar)
    [FiniteDimensional ℚ K] [Normal ℚ K] {m i j : ℕ}
    (Λ : IntermediateField ℚ SSGRoute.QBar) [FiniteDimensional ℚ Λ] [Normal ℚ Λ] [IsGalois ℚ Λ]
    (hKΛ : K ≤ Λ)
    (S : Finset (ValuationSubring SSGRoute.QBar)) (hSfin : ∀ A ∈ S, SSGRoute.IsFinPlace ℚ A) :
    ∃ (T0 : Finset (ValuationSubring SSGRoute.QBar))
      (α : ValuationSubring SSGRoute.QBar → SSGRoute.GalQ →
        Work.CohomologicalShrinking.E p (K ≃ₐ[ℚ] K) m i j),
      (∀ A ∈ T0, SSGRoute.IsFinPlace ℚ A) ∧
      (∀ A ∈ T0, SSGRoute.decomp ℚ A ≤ Λ.fixingSubgroup) ∧
      (∀ A ∈ T0, ∀ B ∈ S, ¬ SSGRoute.IsConjPlace ℚ A B) ∧
      (∀ A ∈ T0, ∀ B ∈ T0, SSGRoute.IsConjPlace ℚ A B → A = B) ∧
      (∀ A ∈ T0, SSGRoute.IsCocycleOn (Work.SSGRoute.restrict K) (SSGRoute.decomp ℚ A) (α A) ∧
        SSGRoute.IsLocConstOn (SSGRoute.decomp ℚ A) (α A)) ∧
      (∀ A ∈ T0, ∀ σ : SSGRoute.GalQ, SSGRoute.IsInertia ℚ A σ → α A σ = 0) ∧
      (∀ y : Work.CohomologicalShrinking.E p (K ≃ₐ[ℚ] K) m i j,
        ∃ A ∈ T0, ∀ (hA : SSGRoute.IsFinPlace ℚ A),
          α A ((Work.SSGRoute.localFrobElem ⟨A, hA⟩ : ↥(SSGRoute.decomp ℚ A)) : SSGRoute.GalQ) = y) := by
  classical
  haveI hFintypeGal : Fintype (K ≃ₐ[ℚ] K) := Fintype.ofFinite _
  haveI hFinE : Finite (Work.CohomologicalShrinking.E p (K ≃ₐ[ℚ] K) m i j) := by
    show Finite (Work.CohomologicalShrinking.refinedQuotient p
      (Work.Shrinking.freeOperatorGroup (K ≃ₐ[ℚ] K) m) i j)
    exact Work.CohomologicalShrinking.flow.finite_refinedQuotient p (K ≃ₐ[ℚ] K) m i j
  haveI hFintypeE : Fintype (Work.CohomologicalShrinking.E p (K ≃ₐ[ℚ] K) m i j) :=
    Fintype.ofFinite _
  obtain ⟨T, hTcard, hTfin, hTsplit, hTavoid, hTdisj⟩ :=
    exists_split_places_avoiding_rat Λ S hSfin
      (Fintype.card (Work.CohomologicalShrinking.E p (K ≃ₐ[ℚ] K) m i j))
  have hKfix : Λ.fixingSubgroup ≤ K.fixingSubgroup := IntermediateField.fixingSubgroup_le hKΛ
  have hsplitT : ∀ A ∈ T, SSGRoute.decomp ℚ A ≤ K.fixingSubgroup :=
    fun A hA => le_trans (hTsplit A hA) hKfix
  let eT : ↥T ≃ Fin (Fintype.card (Work.CohomologicalShrinking.E p (K ≃ₐ[ℚ] K) m i j)) :=
    hTcard ▸ Finset.equivFin T
  let eE : Work.CohomologicalShrinking.E p (K ≃ₐ[ℚ] K) m i j ≃
      Fin (Fintype.card (Work.CohomologicalShrinking.E p (K ≃ₐ[ℚ] K) m i j)) :=
    Fintype.equivFin _
  let xof : ↥T → Work.CohomologicalShrinking.E p (K ≃ₐ[ℚ] K) m i j := fun A => eE.symm (eT A)
  have h0 : ∀ A : ↥T, ∃ f : SSGRoute.GalQ → Work.CohomologicalShrinking.E p (K ≃ₐ[ℚ] K) m i j,
      SSGRoute.IsCocycleOn (Work.SSGRoute.restrict K) (SSGRoute.decomp ℚ A.1) f ∧
      SSGRoute.IsLocConstOn (SSGRoute.decomp ℚ A.1) f ∧
      (∀ σ ∈ SSGRoute.decomp ℚ A.1, SSGRoute.IsInertia ℚ A.1 σ → f σ = 0) ∧
      f ((Work.SSGRoute.localFrobElem ⟨A.1, hTfin A.1 A.2⟩ : ↥(SSGRoute.decomp ℚ A.1)) :
        SSGRoute.GalQ) = xof A :=
    fun A => exists_cocycle_at_frob_of_split p K A.1 (hTfin A.1 A.2) (hsplitT A.1 A.2) _ (xof A)
  let F : ↥T → SSGRoute.GalQ → Work.CohomologicalShrinking.E p (K ≃ₐ[ℚ] K) m i j :=
    fun A => Classical.choose (h0 A)
  have hFspec : ∀ A : ↥T,
      SSGRoute.IsCocycleOn (Work.SSGRoute.restrict K) (SSGRoute.decomp ℚ A.1) (F A) ∧
      SSGRoute.IsLocConstOn (SSGRoute.decomp ℚ A.1) (F A) ∧
      (∀ σ ∈ SSGRoute.decomp ℚ A.1, SSGRoute.IsInertia ℚ A.1 σ → F A σ = 0) ∧
      F A ((Work.SSGRoute.localFrobElem ⟨A.1, hTfin A.1 A.2⟩ : ↥(SSGRoute.decomp ℚ A.1)) :
        SSGRoute.GalQ) = xof A :=
    fun A => Classical.choose_spec (h0 A)
  let α : ValuationSubring SSGRoute.QBar → SSGRoute.GalQ →
      Work.CohomologicalShrinking.E p (K ≃ₐ[ℚ] K) m i j :=
    fun A => if h : A ∈ T then F ⟨A, h⟩ else fun _ => 0
  have hαeq : ∀ (A : ValuationSubring SSGRoute.QBar) (hA : A ∈ T), α A = F ⟨A, hA⟩ :=
    fun A hA => dif_pos hA
  refine ⟨T, α, hTfin, hTsplit, hTavoid, hTdisj, ?_, ?_, ?_⟩
  · intro A hA
    rw [hαeq A hA]
    exact ⟨(hFspec ⟨A, hA⟩).1, (hFspec ⟨A, hA⟩).2.1⟩
  · intro A hA σ hI
    rw [hαeq A hA]
    exact (hFspec ⟨A, hA⟩).2.2.1 σ hI.1 hI
  · intro y
    set A : ValuationSubring SSGRoute.QBar := (eT.symm (eE y)).1 with hAdef
    set hAT : A ∈ T := (eT.symm (eE y)).2 with hATdef
    refine ⟨A, hAT, ?_⟩
    intro hA
    have hα : α A = F ⟨A, hAT⟩ := dif_pos hAT
    rw [hα, localFrobElem_congr_SSGRoute hA (hTfin A hAT)]
    refine (hFspec ⟨A, hAT⟩).2.2.2.trans ?_
    show xof ⟨A, hAT⟩ = y
    have hsub : (⟨A, hAT⟩ : ↥T) = eT.symm (eE y) := Subtype.ext hAdef
    show eE.symm (eT ⟨A, hAT⟩) = y
    rw [hsub, Equiv.apply_symm_apply, Equiv.symm_apply_apply]

end Work.SSGRoute
