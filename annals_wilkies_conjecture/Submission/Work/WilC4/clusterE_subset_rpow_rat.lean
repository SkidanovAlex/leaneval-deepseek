import Mathlib
import Submission.Work.WilC4.ErealDefs
import Submission.Work.WilC4.ulpm_E_finite
import Submission.Work.WilC4.candidate_bound

namespace Work.WilC4

theorem clusterE_subset_rpow_rat {k : ℕ}
    (hR : ∀ (n : ℕ) (X : Set (Fin n → ℝ)), WilkiesDesign.RExpExist X → WilkiesDesign.RExpExist Xᶜ)
    (hOM : WilkiesDesign.CG.OMinModels) (hPB : WilkiesDesign.CG.PolyBoundedRExp)
    (Y : Set (Fin (k + 2) → ℝ)) (hY : (∅ : Set ℝ).Definable WilkiesDesign.CG.LRc Y)
    (hfun : ∀ (c : Fin k → ℝ) (x y y' : ℝ), Work.WilC4.Route.Gr Y c x y →
      Work.WilC4.Route.Gr Y c x y' → y = y')
    (B₀ : Set (Fin (k + 1) → ℝ)) (hB₀ : (∅ : Set ℝ).Definable WilkiesDesign.CG.LRc B₀)
    (hgood : Work.WilC4.GoodFibre Y B₀) :
    Work.WilC4.Route.ClusterE Y B₀ ⊆
      ({0} : Set ℝ) ∪ Set.range (fun q : ℚ => (2 : ℝ) ^ (q : ℝ)) := by
  have hgf : GoodFibre Y B₀ := hgood
  -- the candidate bound in the form consumed by `logb_rat_of_candidate_bound`
  have hcand : ∀ ρ ∈ ClusterER Y B₀, 0 < ρ → ∃ C : ℝ, 1 ≤ C ∧ ∃ β₀ : ℝ, ∀ β : ℝ, β₀ ≤ β →
      ∀ y ∈ Cand Y B₀ ρ β,
        C⁻¹ * β ^ (Real.logb 2 ρ) ≤ y ∧ y ≤ C * β ^ (Real.logb 2 ρ) := by
    intro ρ hρ hρ0
    obtain ⟨C, hC, β₀, hb⟩ := candidate_bound hOM Y hY hfun B₀ hB₀ hgf hρ hρ0
    refine ⟨C, hC, max β₀ 1, fun β hβ y hy => ?_⟩
    have hβ1 : 1 ≤ β := le_trans (le_max_right _ _) hβ
    have hβb : β₀ ≤ β := le_trans (le_max_left _ _) hβ
    obtain ⟨h1, h2⟩ := hb β hβb y hy
    have hypos : 0 < y := Cand_pos hgf hρ hβ1 hy
    rw [abs_of_pos hypos] at h1 h2
    exact ⟨h1, h2⟩
  intro ρ hρ
  have hρER : ρ ∈ ClusterER Y B₀ := ClusterE_subset_ClusterER Y B₀ hρ
  rcases eq_or_lt_of_le (ClusterER_nonneg hgf hρER) with h0 | hpos
  · exact Or.inl h0.symm
  · refine Or.inr ?_
    obtain ⟨q, hq⟩ := logb_rat_of_candidate_bound hR hPB
      (fun R => Diag_definable Y B₀ hY hB₀ ρ R)
      (fun β hβ => Cand_nonempty hgf hρER hβ) (hcand ρ hρER hpos)
    refine ⟨q, ?_⟩
    show (2 : ℝ) ^ (q : ℝ) = ρ
    rw [← hq]
    exact Real.rpow_logb (b := 2) (x := ρ) (by norm_num) (by norm_num) hpos

end Work.WilC4
