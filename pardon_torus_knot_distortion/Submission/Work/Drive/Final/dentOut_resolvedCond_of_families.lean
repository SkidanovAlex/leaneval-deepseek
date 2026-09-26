import Mathlib
import Submission.Work.Drive.Final.dentOut_resolvedCond
import Submission.Work.Drive.Final.dentOut_hgen
import Submission.Work.Drive.Final.dentOut_sweep_subset
import Submission.Work.Drive.Final.AnyEventDefs

/-!
# The two families of the `(L)` residual, combined — conditional span form

`Work.Drive.Final.dentOutResolvedDisc_of_families` combines the trace family of the deformed level
(`Work.Drive.Final.exists_dentOut_trace_family`) with the box-sphere family
(`Work.Drive.Final.exists_family_of_boxSphere`) into the family of `DentOutResolved`.  This module is
the same assembly for the honest residual `Work.Drive.Final.DentOutResolvedCond`, whose span clause is
**conditional** on `WindingSpan P (X lam*) = ⊥` (the hypothesis the no-jump statement provides).  The
proof is the one of the sibling module with the span clause replaced by the conditional one.
-/

namespace Work.Drive.Final

open LeanEval.KnotTheory.PardonDistortion Set

noncomputable section

/-- **The two families of the `(L)` residual, combined, with the conditional span clause.** -/
theorem dentOutResolvedCond_of_families
    {ψ : Submission.Diffeo} {K : Knot} {s u h R : ℝ} {c v : R3} {σ : Equiv.Perm (Fin 3)}
    {ℓ : R3 →L[ℝ] ℝ} {U : Set R3} {exc : Finset ℝ} {lam0 lam1 : ℝ}
    (D : Work.Drive.Final.AnyDentDatum ψ K s c σ u v h R ℓ U)
    (hG : Work.Drive.Final.GoodSweepData3 ψ K s c σ u v h R ℓ exc lam0 lam1)
    {n₁ : ℕ} {cs₁ : Fin n₁ → Work.CoreTopology.ClosedCurve (Work.Drive.EpsSphere.torusOf ψ)}
    (hsimple₁ : ∀ i, Work.CoreTopology.IsSimple (Work.Drive.EpsSphere.torusOf ψ) (cs₁ i))
    (hess₁ : ∀ i, ¬ Work.CoreTopology.IsEssential (Work.Drive.EpsSphere.torusOf ψ) (cs₁ i))
    (hdisj₁ : ∀ i j : Fin n₁, i ≠ j → Disjoint (Set.range (cs₁ i).γ) (Set.range (cs₁ j).γ))
    (htrace₁ : (Work.Drive.EpsSphere.torusOf ψ).carrier ∩
      frontier (D.deform ⁻¹' Work.Drive.Mono.tiltedLevelRemoved s c σ u v h ℓ (ℓ D.centre)) =
      ⋃ i, Set.range (cs₁ i).γ)
    {n₂ : ℕ} {cs₂ : Fin n₂ → Work.CoreTopology.ClosedCurve (Work.Drive.EpsSphere.torusOf ψ)}
    (hsimple₂ : ∀ i, Work.CoreTopology.IsSimple (Work.Drive.EpsSphere.torusOf ψ) (cs₂ i))
    (hess₂ : ∀ i, ¬ Work.CoreTopology.IsEssential (Work.Drive.EpsSphere.torusOf ψ) (cs₂ i))
    (hdisj₂ : ∀ i j : Fin n₂, i ≠ j → Disjoint (Set.range (cs₂ i).γ) (Set.range (cs₂ j).γ))
    (htrans₂ : ∀ (i : Fin n₂) (t : ℝ), (cs₂ i).γ t ∈ (Work.Drive.EpsSphere.torusOf ψ).carrier ∩
      {z : R3 | Submission.boxNorm c σ z = s})
    (hcov₂ : ∀ z : R3, z ∈ (Work.Drive.EpsSphere.torusOf ψ).carrier →
      Submission.boxNorm c σ z = s → ∃ (i : Fin n₂) (t : ℝ), (cs₂ i).γ t = z)
    (hdisjx : ∀ (i : Fin n₁) (j : Fin n₂), Disjoint (Set.range (cs₁ i).γ) (Set.range (cs₂ j).γ))
    (hspan : Work.SurgeryInvariance.WindingSpan (Work.Drive.EpsSphere.torusOf ψ)
        (Work.Drive.EpsFormSphere.openTiltedSweepRegion (Work.Drive.EpsSphere.torusOf ψ) s c σ u v h ℓ
          (ℓ D.centre)) = ⊥ →
      Work.SurgeryInvariance.WindingSpan (Work.Drive.EpsSphere.torusOf ψ)
        (dentOutRegion ψ s c σ u v h R ℓ D) = ⊥) :
    Work.Drive.Final.DentOutResolvedCond D := by
  classical
  set cs : Fin (n₁ + n₂) → Work.CoreTopology.ClosedCurve (Work.Drive.EpsSphere.torusOf ψ) :=
    fun i => Sum.elim cs₁ cs₂ (finSumFinEquiv.symm i) with hcsdef
  have hunion : (⋃ i : Fin (n₁ + n₂), Set.range (cs i).γ)
      = (⋃ i : Fin n₁, Set.range (cs₁ i).γ) ∪ (⋃ j : Fin n₂, Set.range (cs₂ j).γ) := by
    have hcomp : (⋃ i : Fin (n₁ + n₂), Set.range (cs i).γ)
        = ⋃ k : Fin n₁ ⊕ Fin n₂, Set.range ((Sum.elim cs₁ cs₂) k).γ := by
      ext z
      constructor
      · intro hz
        obtain ⟨i, hi⟩ := Set.mem_iUnion.mp hz
        exact Set.mem_iUnion.mpr ⟨finSumFinEquiv.symm i, by simpa using hi⟩
      · intro hz
        obtain ⟨k, hk⟩ := Set.mem_iUnion.mp hz
        exact Set.mem_iUnion.mpr ⟨finSumFinEquiv k, by rw [hcsdef]; simpa using hk⟩
    rw [hcomp, Set.iUnion_sum]
    simp
  refine ⟨⟨n₁ + n₂, cs, ?_, ?_, ?_, ?_, ?_, ?_⟩, hspan⟩
  · -- simplicity
    intro i
    rcases hi : finSumFinEquiv.symm i with a | b
    · rw [show cs i = cs₁ a by simp [hcsdef, hi]]
      exact hsimple₁ a
    · rw [show cs i = cs₂ b by simp [hcsdef, hi]]
      exact hsimple₂ b
  · -- inessentiality
    intro i
    rcases hi : finSumFinEquiv.symm i with a | b
    · rw [show cs i = cs₁ a by simp [hcsdef, hi]]
      exact hess₁ a
    · rw [show cs i = cs₂ b by simp [hcsdef, hi]]
      exact hess₂ b
  · -- pairwise disjointness
    intro i j hij
    rcases hi : finSumFinEquiv.symm i with a | a <;> rcases hj : finSumFinEquiv.symm j with b | b
    · rw [show cs i = cs₁ a by simp [hcsdef, hi],
          show cs j = cs₁ b by simp [hcsdef, hj]]
      refine hdisj₁ a b (fun hab => hij ?_)
      apply finSumFinEquiv.symm.injective
      rw [hi, hj, ← hab]
    · rw [show cs i = cs₁ a by simp [hcsdef, hi],
          show cs j = cs₂ b by simp [hcsdef, hj]]
      exact hdisjx a b
    · rw [show cs i = cs₂ a by simp [hcsdef, hi],
          show cs j = cs₁ b by simp [hcsdef, hj]]
      exact (hdisjx b a).symm
    · rw [show cs i = cs₂ a by simp [hcsdef, hi],
          show cs j = cs₂ b by simp [hcsdef, hj]]
      refine hdisj₂ a b (fun hab => hij ?_)
      apply finSumFinEquiv.symm.injective
      rw [hi, hj, ← hab]
  · -- the trace of the deformed level is covered
    rw [hunion, htrace₁]
    exact subset_union_left
  · -- the family misses `Ω₁`
    rw [hunion, Set.disjoint_union_right]
    refine ⟨?_, ?_⟩
    · rw [Set.disjoint_iUnion_right]
      intro i
      rw [Set.disjoint_left]
      intro z hzΩ hzcs
      have hzfr : z ∈ (Work.Drive.EpsSphere.torusOf ψ).carrier ∩
          frontier (D.deform ⁻¹' Work.Drive.Mono.tiltedLevelRemoved s c σ u v h ℓ (ℓ D.centre)) := by
        rw [htrace₁]
        exact Set.mem_iUnion.mpr ⟨i, hzcs⟩
      exact Set.disjoint_left.mp disjoint_interior_frontier hzΩ.2 hzfr.2
    · rw [Set.disjoint_iUnion_right]
      intro j
      rw [Set.disjoint_left]
      intro z hzΩ hzcs
      have hzP : z ∈ Submission.PBox s c σ := dentOutRegion_subset_PBox D hzΩ
      have hlt : Submission.boxNorm c σ z < s := (Submission.mem_PBox_iff s c σ z).mp hzP
      obtain ⟨t, rfl⟩ := hzcs
      have hn : Submission.boxNorm c σ ((cs₂ j).γ t) = s := (htrans₂ j t).2
      exact absurd hn (ne_of_lt hlt)
  · -- the union-form genericity (L6b)
    intro z hzc hzbox hzslab hzℓ
    refine dentOut_hgen (ι := Fin (n₁ + n₂)) (cs := cs) hG D ?_ hzc hzbox hzslab hzℓ
    intro z hzc' hbn
    obtain ⟨j, t, ht⟩ := hcov₂ z hzc' hbn
    refine ⟨finSumFinEquiv (Sum.inr j), Set.mem_range.mpr ⟨t, ?_⟩⟩
    rw [hcsdef]
    simpa using ht

end

end Work.Drive.Final
