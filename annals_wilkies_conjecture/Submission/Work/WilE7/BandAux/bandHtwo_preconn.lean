import Mathlib
import Submission.Work.WilE7.BandAux.bandCoverTwo_defs

namespace Work.WilE7.BandAux

open Work.WilE7

/-- The two-strata band `bandHtwo` is the vertical band over the base component `bandZc Z u₀`
cut by the two level functions `bandLevel s₁ i` and `bandLevel s₂ j`.  Since the base component
of a `SemiPf` set is preconnected and the two level functions are continuous on it (with a
strict pointwise inequality `hlvl` supplied by the hypotheses), the elementary topological lemma
`band_preconn` gives that the band is preconnected. -/
theorem bandHtwo_preconn {p m : ℕ} (Z : WilkiesDesign.E.SemiPf (p + (m + 1)))
    (u₀ : Fin (p + (m + 1)) → ℝ) (C : Set (Fin p → ℝ))
    (hC : C = Set.image (WilkiesDesign.E.projFirst p (m + 1)) (connectedComponentIn Z.set u₀))
    (k₁ : ℕ) (s₁ : Fin k₁ → (Fin p → ℝ) → (Fin (m + 1) → ℝ))
    (hcont₁ : ∀ i, ContinuousOn (s₁ i) C)
    (k₂ : ℕ) (s₂ : Fin k₂ → (Fin p → ℝ) → (Fin (m + 1) → ℝ))
    (hcont₂ : ∀ i, ContinuousOn (s₂ i) C)
    (i : Fin k₁) (j : Fin k₂)
    (hlvl : ∀ x ∈ C, (s₁ i x) (Fin.last m) < (s₂ j x) (Fin.last m)) :
    IsPreconnected (Work.WilE7.BandAux.bandHtwo Z s₁ s₂ i j u₀) := by
  -- the base component is preconnected
  have hCz : IsPreconnected (bandZc Z u₀) := isPreconnected_connectedComponentIn
  -- the two level functions are continuous on the base component
  have hsi : ContinuousOn (fun u : Fin (p + (m + 1)) → ℝ =>
      s₁ i (WilkiesDesign.E.projFirst p (m + 1) u)) (bandZc Z u₀) :=
    (hcont₁ i).comp (continuous_projFirst p (m + 1)).continuousOn
      (fun u hu => by rw [hC]; exact ⟨u, hu, rfl⟩)
  have hsj : ContinuousOn (fun u : Fin (p + (m + 1)) → ℝ =>
      s₂ j (WilkiesDesign.E.projFirst p (m + 1) u)) (bandZc Z u₀) :=
    (hcont₂ j).comp (continuous_projFirst p (m + 1)).continuousOn
      (fun u hu => by rw [hC]; exact ⟨u, hu, rfl⟩)
  have ha : ContinuousOn (bandLevel s₁ i) (bandZc Z u₀) := by
    change ContinuousOn (fun u : Fin (p + (m + 1)) → ℝ =>
      ((s₁ i (WilkiesDesign.E.projFirst p (m + 1) u)) (Fin.last m) : EReal)) (bandZc Z u₀)
    exact continuous_coe_real_ereal.comp_continuousOn
      ((continuous_apply (Fin.last m)).comp_continuousOn hsi)
  have hb : ContinuousOn (bandLevel s₂ j) (bandZc Z u₀) := by
    change ContinuousOn (fun u : Fin (p + (m + 1)) → ℝ =>
      ((s₂ j (WilkiesDesign.E.projFirst p (m + 1) u)) (Fin.last m) : EReal)) (bandZc Z u₀)
    exact continuous_coe_real_ereal.comp_continuousOn
      ((continuous_apply (Fin.last m)).comp_continuousOn hsj)
  -- the two levels are strictly ordered on the base component
  have hab : ∀ u ∈ bandZc Z u₀, bandLevel s₁ i u < bandLevel s₂ j u := by
    intro u hu
    change ((s₁ i (WilkiesDesign.E.projFirst p (m + 1) u)) (Fin.last m) : EReal) <
      ((s₂ j (WilkiesDesign.E.projFirst p (m + 1) u)) (Fin.last m) : EReal)
    exact EReal.coe_lt_coe_iff.mpr
      (hlvl (WilkiesDesign.E.projFirst p (m + 1) u) (by rw [hC]; exact ⟨u, hu, rfl⟩))
  rw [bandHtwo]
  exact band_preconn hCz ha hb hab

end Work.WilE7.BandAux
