import Mathlib
import Submission.Work.Compact.Noncompact.Good
import Submission.Work.Compact.Noncompact.forall_localMap_eq_zero_of_exists
import Submission.Work.Compact.Noncompact.isZero_hatH_convex

/-!
# Hatcher's Lemma 3.27 for a closed ball inside a chart

For a chart `e` of a `(k+1)`-manifold `M` and `ρ > 0` with `Metric.ball c ρ ⊆ e.target`, the set
`K = e.source ∩ e⁻¹' Metric.closedBall c (ρ/2)` satisfies `GoodC k`:

* compactness: `isCompact_inter_preimage`;
* vanishing `H_j(M, M∖K) = 0` for `j > k+1`: `isZero_hatH_convex` applied to the compact convex
  ball `Metric.closedBall c (ρ/2) ⊆ Metric.ball c ρ ⊆ e.target`;
* uniqueness in degree `k+1`: evaluate the localizations at the centre `z = e.symm c ∈ K` and use
  `localMap_injective_ball`, whose injectivity hypothesis holds since `dist (e z) c = 0 < ρ/4`.
-/

namespace Work.Compact.Noncompact

open CategoryTheory AlgebraicTopology CategoryTheory.Limits

set_option maxHeartbeats 1600000
set_option backward.isDefEq.respectTransparency false

noncomputable section

theorem goodC_closedBall {k : ℕ} {M : Type} [TopologicalSpace M] [T2Space M]
    [ChartedSpace (EuclideanSpace ℝ (Fin (k + 1))) M]
    (e : OpenPartialHomeomorph M (EuclideanSpace ℝ (Fin (k + 1))))
    {c : EuclideanSpace ℝ (Fin (k + 1))} {ρ : ℝ} (hρ : 0 < ρ)
    (hsub : Metric.ball c ρ ⊆ e.target) :
    GoodC k (TopCat.of M) (e.source ∩ e⁻¹' Metric.closedBall c (ρ / 2)) := by
  have hcl_sub_ball : Metric.closedBall c (ρ / 2) ⊆ Metric.ball c ρ := by
    intro x hx
    rw [Metric.mem_closedBall] at hx
    rw [Metric.mem_ball]
    linarith
  have hcl_sub_tgt : Metric.closedBall c (ρ / 2) ⊆ e.target := hcl_sub_ball.trans hsub
  refine ⟨?_, ?_, ?_⟩
  · exact isCompact_inter_preimage e (isCompact_closedBall c (ρ / 2)) hcl_sub_tgt
  · intro u hu
    have hct : c ∈ e.target := hsub (Metric.mem_ball_self hρ)
    have hzsrc : e.symm c ∈ e.source := e.map_target hct
    have hez : e (e.symm c) = c := e.right_inv hct
    have hzd : dist (e (e.symm c)) c < ρ / 4 := by
      rw [hez, dist_self]; linarith
    have hzK : e.symm c ∈ e.source ∩ e⁻¹' Metric.closedBall c (ρ / 2) :=
      ⟨hzsrc, by
        rw [Set.mem_preimage, hez]
        exact Metric.mem_closedBall_self (by linarith)⟩
    have hKz : (e.source ∩ e⁻¹' Metric.closedBall c (ρ / 2))ᶜ
        ⊆ ({e.symm c}ᶜ : Set M) := by
      rintro w hw hwz
      exact hw (hwz ▸ hzK)
    have hinj := localMap_injective_ball e hρ hsub hzsrc hzd hKz
    have h0 : relMapHom (X := TopCat.of M)
        (A := (e.source ∩ e⁻¹' Metric.closedBall c (ρ / 2))ᶜ) (B := ({e.symm c}ᶜ : Set M))
        (Set.compl_subset_compl.mpr (Set.singleton_subset_iff.mpr hzK)) (k + 1) u = 0 :=
      hu (e.symm c) hzK
    have h1 : relMapHom (X := TopCat.of M)
        (A := (e.source ∩ e⁻¹' Metric.closedBall c (ρ / 2))ᶜ) (B := ({e.symm c}ᶜ : Set M))
        hKz (k + 1) u = 0 := by
      rw [← relMapHom_eq_of_subset_eq
        (h₁ := Set.compl_subset_compl.mpr (Set.singleton_subset_iff.mpr hzK)) (h₂ := hKz)
        (k := k + 1)]
      exact h0
    exact hinj (by rw [h1, map_zero])
  · intro j hj
    exact isZero_hatH_convex (n := k + 1) (k := j) (Nat.succ_le_succ (Nat.zero_le k)) e
      (convex_closedBall c (ρ / 2)) (isCompact_closedBall c (ρ / 2)) hcl_sub_tgt hj

end

end Work.Compact.Noncompact
