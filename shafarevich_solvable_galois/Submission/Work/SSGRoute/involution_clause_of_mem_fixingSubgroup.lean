import Mathlib
import Submission.Work.SSGRoute.stage_local_shrinking
-- PORT435-BEGIN (v4.35 isDefEq respectTransparency compat)
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- PORT435-END

namespace Work.SSGRoute

/-- **Clause (B) in the degenerate case.**  If every involution `c ∈ G_ℚ` lies in
`K.fixingSubgroup`, then Scholz condition (ii) (`hφ.2.2.1`) gives `φ c = 1`, hence the pushed
solution `Ψ = (flowGroupMap p G i j Φ).comp φ` is trivial on `⟨c⟩`, and `l := 1` is a kernel-killing
splitting.  This is the first branch of `Work.SSGRoute.involution_clause_of_two_torsion`
(`Submission/Work/SSGRoute/stage_local_shrinking.lean`) with the single-element hypothesis replaced
by the `∀ c` hypothesis `hfix`. -/
theorem involution_clause_of_mem_fixingSubgroup (p : ℕ) [Fact p.Prime]
    (K : IntermediateField ℚ SSGRoute.QBar) [FiniteDimensional ℚ K] [Normal ℚ K] (i j m n : ℕ)
    (φ : SSGRoute.GalQ →* Work.CohomologicalShrinking.flowGroup p (K ≃ₐ[ℚ] K) m i j)
    (hφ : SSGRoute.IsScholzSolution p K m i j φ)
    (Φ : Work.CohomologicalShrinking.OperatorMap (K ≃ₐ[ℚ] K) m n)
    (hfix : ∀ c : SSGRoute.GalQ, c ^ 2 = 1 → c ∈ K.fixingSubgroup) :
    ∀ c : SSGRoute.GalQ, c ^ 2 = 1 →
      ∃ l : ↥(Subgroup.zpowers c) →* Work.CohomologicalShrinking.flowGroup p (K ≃ₐ[ℚ] K) n
            (Work.CohomologicalShrinking.tauSucc i j).1 (Work.CohomologicalShrinking.tauSucc i j).2,
        (∀ σ : ↥(Subgroup.zpowers c),
          SSGRoute.LiftsFlowAt (l σ)
            (((Work.CohomologicalShrinking.flowGroupMap p (K ≃ₐ[ℚ] K) i j Φ).comp φ) σ)) ∧
        (∀ σ : ↥(Subgroup.zpowers c),
          (((Work.CohomologicalShrinking.flowGroupMap p (K ≃ₐ[ℚ] K) i j Φ).comp φ) σ) = 1 → l σ = 1) := by
  intro c hc
  -- the pushed solution `Ψ`
  set Ψ : SSGRoute.GalQ →* Work.CohomologicalShrinking.flowGroup p (K ≃ₐ[ℚ] K) n i j :=
    (Work.CohomologicalShrinking.flowGroupMap p (K ≃ₐ[ℚ] K) i j Φ).comp φ with hΨdef
  -- Scholz condition (ii): `c ∈ K.fixingSubgroup` gives `φ c = 1`
  have hφc : φ c = 1 := hφ.2.2.1 c hc (hfix c hc)
  have hΨc : Ψ c = 1 := by simp [hΨdef, hφc]
  -- `l := 1` is a kernel-killing splitting
  refine ⟨1, ?_, ?_⟩
  · intro σ
    have hσ1 : Ψ (σ : SSGRoute.GalQ) = 1 := by
      obtain ⟨k, hk⟩ := Subgroup.mem_zpowers_iff.mp σ.2
      rw [← hk, map_zpow, hΨc, one_zpow]
    rw [hσ1]
    exact (liftsFlowAt_iff_flowGroupSucc p K n i j 1 1).mpr (map_one _)
  · intro σ _
    exact MonoidHom.one_apply σ

end Work.SSGRoute
