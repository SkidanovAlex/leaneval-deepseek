/-
  WilE7 (`Submission.Work.WilE7.BelowAux.belowComp_cov`): coverage of the below cell by the
  connected component of `belowS` through the canonical point.

  Let `S : Stratum p (m+1)`, `Z : SemiPf (p+(m+1))` with `u₀ ∈ Z.set`, and let
  `C = π_p (connectedComponentIn Z.set u₀)` be the base cell.  For continuous sheets
  `s j : C → ℝ^{m+1}` whose graphs meet `S.X.set` over `C` and whose lowest sheet sits
  strictly above the level `-1` on `C`, the below cell

    `{y : Fin (p+1) → ℝ | Fin.init y ∈ C ∧ -1 ≤ y (Fin.last p) ∧
        y (Fin.last p) < (s 0 (Fin.init y)) (Fin.last m)}`

  is contained in the `belowExtract`-image of the connected component of the point
  `belowPt u₀ (s 0 (π_p u₀)) (-1)` of `(belowS Z S).set`.

  The proof follows the band-cell analogue (`Work.WilE7.BandAux.bandComp_cover`):
  the region

    `belowH Z s 0 u₀ = {q | q.1 ∈ connectedComponentIn Z.set u₀ ∧ -1 ≤ q.2 ∧
        q.2 < (s 0 (π_p q.1)) (Fin.last m)}`

  is preconnected (`preconn_under_graph`, applied to the preconnected base component and the
  continuous level function `q.1 ↦ (s 0 (π_p q.1)) (Fin.last m)`), the parametrisation
  `belowPhi s 0` is continuous on it and maps it into `(belowS Z S).set`, and it sends the point
  `(u₀, -1)` to the canonical point.  Hence its image lies in the connected component of that
  point (`Work.WilE7.imageSubsetConnectedComponentIn`).  Given `y` in the below cell, a point `u`
  of the base component over `Fin.init y` is picked and `q = (u, y (Fin.last p))` lies in
  `belowH`, so `belowPhi s 0 q` belongs to the component and `belowExtract` sends it back to `y`.
-/
import Mathlib
import Submission.Work.WilE7.BelowAux.BelowDefs
import Submission.Work.WilE7.BelowAux.preconn_under_graph
import Submission.Work.WilE7.BelowAux.belowPhi_continuous
import Submission.Work.WilE7.BelowAux.belowPhi_mem
import Submission.Work.WilE7.imageSubsetConnectedComponentIn

set_option autoImplicit false
noncomputable section
open Classical
namespace Work.WilE7.BelowAux
open WilkiesDesign WilkiesDesign.E

theorem belowComp_cov
    {p m : ℕ} (S : WilkiesDesign.E.Stratum p (m + 1))
    (Z : WilkiesDesign.E.SemiPf (p + (m + 1))) (u₀ : Fin (p + (m + 1)) → ℝ)
    (hu₀ : u₀ ∈ Z.set)
    (C : Set (Fin p → ℝ))
    (hC : C = Set.image (WilkiesDesign.E.projFirst p (m + 1)) (connectedComponentIn Z.set u₀))
    (k : ℕ) (hk : 0 < k) (s : Fin k → (Fin p → ℝ) → (Fin (m + 1) → ℝ))
    (hcont : ∀ j, ContinuousOn (s j) C)
    (hsub : ∀ j : Fin k, ∀ x ∈ C, Fin.append x (s j x) ∈ S.X.set)
    (hlt : ∀ x ∈ C, -1 < (s ⟨0, hk⟩ x) (Fin.last m)) :
    {y : Fin (p + 1) → ℝ | Fin.init y ∈ C ∧ -1 ≤ y (Fin.last p) ∧
        y (Fin.last p) < (s ⟨0, hk⟩ (Fin.init y)) (Fin.last m)}
      ⊆ Work.WilE7.BelowAux.belowExtract ''
        (connectedComponentIn (Work.WilE7.BelowAux.belowS Z S).set
          (Work.WilE7.BelowAux.belowPt u₀
            (s ⟨0, hk⟩ (WilkiesDesign.E.projFirst p (m + 1) u₀)) (-1))) := by
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
  have hpc : IsPreconnected (belowH Z s ⟨0, hk⟩ u₀) := by
    rw [belowH]
    exact preconn_under_graph isPreconnected_connectedComponentIn hσ
      (fun u hu => hlt _ (hpi u hu))
  -- the parametrisation is continuous on the region and lands in `(belowS Z S).set`
  have hphi : ContinuousOn (belowPhi s ⟨0, hk⟩) (belowH Z s ⟨0, hk⟩ u₀) :=
    belowPhi_continuous Z u₀ C hC s ⟨0, hk⟩ (hcont ⟨0, hk⟩)
  have hF : ∀ q ∈ belowH Z s ⟨0, hk⟩ u₀, belowPhi s ⟨0, hk⟩ q ∈ (belowS Z S).set :=
    belowPhi_mem S Z u₀ C hC s ⟨0, hk⟩ hsub
  -- the canonical point is the image of `(u₀, -1)`, and `(u, y (Fin.last p))` lies in the region
  have hq0 : ((u₀, (-1 : ℝ)) : (Fin (p + (m + 1)) → ℝ) × ℝ) ∈ belowH Z s ⟨0, hk⟩ u₀ := by
    rw [belowH]
    exact ⟨mem_connectedComponentIn hu₀, le_refl (-1),
      hlt _ (hpi u₀ (mem_connectedComponentIn hu₀))⟩
  have hq : ((u, y (Fin.last p)) : (Fin (p + (m + 1)) → ℝ) × ℝ) ∈ belowH Z s ⟨0, hk⟩ u₀ := by
    rw [belowH]
    exact ⟨hucomp, hy1, by rw [hux]; exact hy2⟩
  have hmem := Work.WilE7.imageSubsetConnectedComponentIn hpc hphi hq0 hF
    ((u, y (Fin.last p)) : (Fin (p + (m + 1)) → ℝ) × ℝ) hq
  refine ⟨belowPt u (s ⟨0, hk⟩ (Fin.init y)) (y (Fin.last p)), ?_, ?_⟩
  · simpa only [belowPhi, hux] using hmem
  · rw [belowExtract_belowPt, hux, Fin.snoc_init_self]

end Work.WilE7.BelowAux
