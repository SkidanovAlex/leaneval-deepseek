import Mathlib
import Submission.Work.WilE7.AboveAux.AboveDefs
import Submission.Work.WilE7.AboveAux.preconn_over_graph
import Submission.Work.WilE7.AboveAux.abovePhi_continuous
import Submission.Work.WilE7.AboveAux.abovePhi_mem
import Submission.Work.WilE7.imageSubsetConnectedComponentIn

namespace Work.WilE7.AboveAux

open WilkiesDesign WilkiesDesign.E
open Work.WilE7.BelowAux

theorem aboveComp_cov
    {p m : ℕ} (S : WilkiesDesign.E.Stratum p (m + 1))
    (Z : WilkiesDesign.E.SemiPf (p + (m + 1))) (u₀ : Fin (p + (m + 1)) → ℝ)
    (hu₀ : u₀ ∈ Z.set)
    (C : Set (Fin p → ℝ))
    (hC : C = Set.image (WilkiesDesign.E.projFirst p (m + 1)) (connectedComponentIn Z.set u₀))
    (k : ℕ) (hk : 0 < k) (s : Fin k → (Fin p → ℝ) → (Fin (m + 1) → ℝ))
    (hcont : ∀ j, ContinuousOn (s j) C)
    (hsub : ∀ j : Fin k, ∀ x ∈ C, Fin.append x (s j x) ∈ S.X.set)
    (hgt : ∀ x ∈ C, (s ⟨k - 1, Nat.sub_lt hk (by norm_num)⟩ x) (Fin.last m) < 1) :
    {y : Fin (p + 1) → ℝ | Fin.init y ∈ C ∧
        (s ⟨k - 1, Nat.sub_lt hk (by norm_num)⟩ (Fin.init y)) (Fin.last m) < y (Fin.last p) ∧
        y (Fin.last p) ≤ 1}
      ⊆ Work.WilE7.BelowAux.belowExtract ''
        (connectedComponentIn (Work.WilE7.AboveAux.aboveS Z S).set
          (Work.WilE7.BelowAux.belowPt u₀
            (s ⟨k - 1, Nat.sub_lt hk (by norm_num)⟩ (WilkiesDesign.E.projFirst p (m + 1) u₀)) 1)) := by
  set j : Fin k := ⟨k - 1, Nat.sub_lt hk (by norm_num)⟩ with hj
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
  -- the level function of the top sheet is continuous on the base component
  have hσ : ContinuousOn
      (fun u : Fin (p + (m + 1)) → ℝ => (s j (projFirst p (m + 1) u)) (Fin.last m))
      (connectedComponentIn Z.set u₀) :=
    (continuous_apply (Fin.last m)).comp_continuousOn
      ((hcont j).comp (continuous_projFirst p (m + 1)).continuousOn hpi)
  -- the parametrising region is preconnected
  have hpc : IsPreconnected (aboveH Z s j u₀) := by
    rw [aboveH]
    exact preconn_over_graph isPreconnected_connectedComponentIn hσ
      (fun u hu => hgt _ (hpi u hu))
  -- the parametrisation is continuous on the region and lands in `(aboveS Z S).set`
  have hphi : ContinuousOn (abovePhi s j) (aboveH Z s j u₀) :=
    abovePhi_continuous Z u₀ C hC s j (hcont j)
  have hF : ∀ q ∈ aboveH Z s j u₀, abovePhi s j q ∈ (aboveS Z S).set :=
    abovePhi_mem S Z u₀ C hC s j hsub
  -- the canonical point is the image of `(u₀, 1)`, and `(u, y (Fin.last p))` lies in the region
  have hq0 : ((u₀, (1 : ℝ)) : (Fin (p + (m + 1)) → ℝ) × ℝ) ∈ aboveH Z s j u₀ := by
    rw [aboveH]
    exact ⟨mem_connectedComponentIn hu₀, hgt _ (hpi u₀ (mem_connectedComponentIn hu₀)), le_refl 1⟩
  have hq : ((u, y (Fin.last p)) : (Fin (p + (m + 1)) → ℝ) × ℝ) ∈ aboveH Z s j u₀ := by
    rw [aboveH]
    exact ⟨hucomp, by rw [hux]; exact hy1, hy2⟩
  have hmem := Work.WilE7.imageSubsetConnectedComponentIn hpc hphi hq0 hF
    ((u, y (Fin.last p)) : (Fin (p + (m + 1)) → ℝ) × ℝ) hq
  refine ⟨belowPt u (s j (Fin.init y)) (y (Fin.last p)), ?_, ?_⟩
  · simpa only [abovePhi, hux] using hmem
  · rw [belowExtract_belowPt, hux, Fin.snoc_init_self]

end Work.WilE7.AboveAux
