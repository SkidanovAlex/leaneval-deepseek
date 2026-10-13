import Mathlib
import Submission.Work.WilE7.BelowAux.belowOpenDefs
import Submission.Work.WilE7.BelowAux.belowOpenAux
import Submission.Work.WilE7.BelowAux.preconn_under_graph
import Submission.Work.WilE7.imageSubsetConnectedComponentIn
import Submission.Work.WilE7.BelowAux.BelowDefs

namespace Work.WilE7.BelowAux

open WilkiesDesign WilkiesDesign.E

/-- The strict-lower-bound analogue of `belowComp_cov`: the *open* below cell

  `{y | Fin.init y ∈ C ∧ -1 < y (Fin.last p) ∧ y (Fin.last p) < (s 0 (Fin.init y)) (Fin.last m)}`

is contained in the `belowExtract`-image of the connected component of `belowSopen` through the
interior point `belowPt u₀ (s 0 (π u₀)) (belowT0 s 0 u₀)`.

The proof is the same as for the closed cell, with `belowH` replaced by the strict region
`belowHlt` (whose preconnectedness is `preconn_under_graph_open`), `belowPhi_mem` replaced by
`belowPhi_mem_open`, and the canonical point `(u₀, -1)` replaced by
`(u₀, belowT0 s 0 u₀)`. -/
theorem belowOpenComp_cov
    {p m : ℕ} (S : WilkiesDesign.E.Stratum p (m + 1))
    (Z : WilkiesDesign.E.SemiPf (p + (m + 1))) (u₀ : Fin (p + (m + 1)) → ℝ) (hu₀ : u₀ ∈ Z.set)
    (C : Set (Fin p → ℝ))
    (hC : C = Set.image (WilkiesDesign.E.projFirst p (m + 1)) (connectedComponentIn Z.set u₀))
    (k : ℕ) (hk : 0 < k) (s : Fin k → (Fin p → ℝ) → (Fin (m + 1) → ℝ))
    (hcont : ∀ j, ContinuousOn (s j) C)
    (hsub : ∀ j : Fin k, ∀ x ∈ C, Fin.append x (s j x) ∈ S.X.set)
    (hlt : ∀ x ∈ C, -1 < (s ⟨0, hk⟩ x) (Fin.last m)) :
    {y : Fin (p + 1) → ℝ | Fin.init y ∈ C ∧ -1 < y (Fin.last p) ∧
        y (Fin.last p) < (s ⟨0, hk⟩ (Fin.init y)) (Fin.last m)}
      ⊆ Work.WilE7.BelowAux.belowExtract ''
          (connectedComponentIn (Work.WilE7.BelowAux.belowSopen Z S).set
            (Work.WilE7.BelowAux.belowPt u₀
              (s ⟨0, hk⟩ (WilkiesDesign.E.projFirst p (m + 1) u₀))
              (Work.WilE7.BelowAux.belowT0 s ⟨0, hk⟩ u₀))) := by
  intro y hy
  obtain ⟨hyC0, hy1, hy2⟩ := hy
  -- a point of the base component lying over `Fin.init y`
  obtain ⟨u, hucomp, hux⟩ : ∃ u ∈ connectedComponentIn Z.set u₀,
      projFirst p (m + 1) u = Fin.init y := by
    have h := hyC0
    rw [hC] at h
    exact h
  -- the base component projects into `C`
  have hpi : ∀ u ∈ connectedComponentIn Z.set u₀, projFirst p (m + 1) u ∈ C :=
    fun u hu => by rw [hC]; exact ⟨u, hu, rfl⟩
  -- the level function of the lowest sheet is continuous on the base component
  have hσ : ContinuousOn
      (fun u : Fin (p + (m + 1)) → ℝ => (s ⟨0, hk⟩ (projFirst p (m + 1) u)) (Fin.last m))
      (connectedComponentIn Z.set u₀) :=
    (continuous_apply (Fin.last m)).comp_continuousOn
      ((hcont ⟨0, hk⟩).comp (continuous_projFirst p (m + 1)).continuousOn hpi)
  -- the parametrising region is preconnected
  have hpc : IsPreconnected (belowHlt Z s ⟨0, hk⟩ u₀) := by
    rw [belowHlt]
    exact preconn_under_graph_open isPreconnected_connectedComponentIn hσ
      (fun u hu => hlt _ (hpi u hu))
  -- the parametrisation is continuous on the region and lands in `(belowSopen Z S).set`
  have hphi : ContinuousOn (belowPhi s ⟨0, hk⟩) (belowHlt Z s ⟨0, hk⟩ u₀) :=
    belowPhi_continuousOn C s ⟨0, hk⟩ (hcont ⟨0, hk⟩) (belowHlt Z s ⟨0, hk⟩ u₀)
      (fun q hq => hpi q.1 ((mem_belowHlt.mp hq).1))
  have hF : ∀ q ∈ belowHlt Z s ⟨0, hk⟩ u₀, belowPhi s ⟨0, hk⟩ q ∈ (belowSopen Z S).set :=
    belowPhi_mem_open S Z u₀ C hC s ⟨0, hk⟩ hsub
  -- the canonical point is the image of `(u₀, belowT0 s 0 u₀)`, and `(u, y (Fin.last p)) ∈ belowHlt`
  have hlt0 : -1 < (s ⟨0, hk⟩ (projFirst p (m + 1) u₀)) (Fin.last m) :=
    hlt _ (hpi u₀ (mem_connectedComponentIn hu₀))
  have hq0 : ((u₀, belowT0 s ⟨0, hk⟩ u₀) : (Fin (p + (m + 1)) → ℝ) × ℝ) ∈
      belowHlt Z s ⟨0, hk⟩ u₀ := by
    rw [mem_belowHlt]
    exact ⟨mem_connectedComponentIn hu₀, belowT0_gt hlt0, belowT0_lt hlt0⟩
  have hq : ((u, y (Fin.last p)) : (Fin (p + (m + 1)) → ℝ) × ℝ) ∈
      belowHlt Z s ⟨0, hk⟩ u₀ := by
    rw [mem_belowHlt]
    exact ⟨hucomp, hy1, by rw [hux]; exact hy2⟩
  have hmem := Work.WilE7.imageSubsetConnectedComponentIn hpc hphi hq0 hF
    ((u, y (Fin.last p)) : (Fin (p + (m + 1)) → ℝ) × ℝ) hq
  refine ⟨belowPhi s ⟨0, hk⟩ (u, y (Fin.last p)), ?_, ?_⟩
  · show belowPhi s ⟨0, hk⟩ (u, y (Fin.last p)) ∈
      connectedComponentIn (belowSopen Z S).set
        (belowPhi s ⟨0, hk⟩ (u₀, belowT0 s ⟨0, hk⟩ u₀))
    exact hmem
  · rw [belowExtract_belowPhi, hux, Fin.snoc_init_self]

end Work.WilE7.BelowAux
