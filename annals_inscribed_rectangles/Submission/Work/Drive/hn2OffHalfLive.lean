import Mathlib
import Submission.Work.Drive.sideGermDefs
import Submission.Work.Drive.planeChartDefs
import Submission.Work.Drive.sideGerm_indep
import Submission.Work.Drive.hn2CountInterface
import Submission.Work.Drive.sideGermLoop
import Submission.Work.Drive.coreLoop_disjoint_rotCapping
import Submission.Work.Drive.chartIsSmooth
import Submission.Work.Drive.exists_chartPert
import Submission.Work.Drive.chartPertData
import Submission.Work.Drive.hn2_refCountExists

/-!
# The off-`1/2` antisymmetry of the germ side value, from the **proved** counting datum

`Submission/Work/Drive/hn2_off_half.lean` proves the off-`1/2` antisymmetry from
`Work.Drive.hn2_refCount` (`Drive/hn2_refCount.lean`), which is still a `sorry`-hole; the lane has
since re-proved the *same* counting datum under the fresh name
`Work.Drive.hn2_refCountExists` (`Drive/hn2_refCountExists.lean`, **proved, sorry-free, axiom-clean**).

This file is the same three-line derivation with the *proved* twin substituted, so that the wall
`Work.Drive.chainParity` no longer depends on the historical hole file `hn2_refCount.lean`.  The proof
is character-identical to `Work.Drive.hn2_off_half`'s (same call site, same arguments); only the name of
the counting datum changes.
-/

namespace Work.Drive

open Manifold
open scoped Manifold ContDiff

/-- **The off-`1/2` antisymmetry of the germ side value, from the proved counting datum.** -/
theorem hn2_off_half_live {γ : Circle → ℝ × ℝ} {hγne : ∀ x : Circle, γ x ≠ 0}
    (hγsm : Manifold.IsSmoothEmbedding (modelWithCornersSelf ℝ (EuclideanSpace ℝ (Fin 1)))
      (modelWithCornersSelf ℝ (ℝ × ℝ)) ((⊤ : ℕ∞) : WithTop ℕ∞) γ)
    {Q : ℂ → Work.Drive.CappingSpace} (hQ : Work.Drive.IsPlaneChart γ hγne Q) {m : ℕ}
    (Ξ : EuclideanSpace ℝ (Fin m) → Work.Drive.CappingSpace → Work.Drive.CappingSpace) (c : ℝ)
    (hΞ : Work.Drive.ChartPert Q m Ξ) (hc : 0 < c)
    (hcbot : ∀ p ∈ Work.Drive.chartDisk Q, c < Work.Drive.levelOf p)
    (hdisjZc : ∀ w : UnitAddCircle, w ∈ Work.Drive.Zc γ →
      Disjoint (Work.Drive.chartDisk Q) (Work.Drive.rotCapping w '' Work.Drive.chartDisk Q)) :
    ∀ u v : UnitAddCircle, v - u ∈ Work.Drive.Zc γ →
      v - u ≠ (((1 : ℝ) / 2 : ℝ) : UnitAddCircle) →
      Work.Drive.sideGerm Ξ Q c (v - u) + Work.Drive.sideGerm Ξ Q c (u - v) = 1 := by
  intro u v huv hne
  have hγinj : Function.Injective γ := hγsm.isEmbedding.injective
  have hQd : IsChartData Q := IsChartData_of_isPlaneChart hQ
  have hΞc : ChartPert Q 4 (fun s p => chartPert s p) :=
    ⟨chartPert_zero, contMDiff_chartPert,
      fun t p => surjective_mfderiv_chartPert p contMDiff_chartPert t⟩
  have hloopA : Disjoint (Set.range (coreLoop Q)) (rotCapping (v - u) '' chartDisk Q) :=
    disjoint_range_coreLoop_rotCapping_chartDisk hγne hγinj hQ huv
  have hloopN : Disjoint (Set.range (coreLoop Q)) (rotCapping (-(v - u)) '' chartDisk Q) :=
    disjoint_range_coreLoop_rotCapping_chartDisk hγne hγinj hQ (neg_mem_Zc huv)
  have hcount : sideGerm (fun s p => chartPert s p) Q c (v - u)
      + sideGerm (fun s p => chartPert s p) Q c (-(v - u)) = 1 := by
    obtain ⟨ε, hε, hconc⟩ :=
      exists_pos_sideGerm_add_neg_eq_one_of_counts_loop (fun s p => chartPert s p) Q c (v - u)
        hΞc hQd hc hcbot hloopA hloopN
    obtain ⟨t, t', ht, ht', hg, hg', hodd⟩ :=
      hn2_refCountExists hγsm hQ hc hcbot hdisjZc ε hε (v - u) huv hne
    exact hconc t t' ht ht' hg hg' hodd
  have hneg : u - v ∈ Work.Drive.Zc γ := by
    have h := neg_mem_Zc huv
    rwa [neg_sub] at h
  have hcount' : sideGerm (fun s p => chartPert s p) Q c (v - u)
      + sideGerm (fun s p => chartPert s p) Q c (u - v) = 1 := by
    rw [neg_sub] at hcount
    exact hcount
  rw [sideGerm_indep hγinj hQ Ξ (fun s p => chartPert s p) c hΞ hΞc hc hcbot (v - u) huv,
    sideGerm_indep hγinj hQ Ξ (fun s p => chartPert s p) c hΞ hΞc hc hcbot (u - v) hneg]
  exact hcount'

end Work.Drive
