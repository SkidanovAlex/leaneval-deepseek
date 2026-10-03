import Mathlib
import Submission.Work.Interfaces.Parabolic

namespace Work.Horn.Basins

/-- If `B` is a subset of the parabolic basin that contains every point of the basin in its
closure (i.e. `B` is closed relatively to the basin), then for any compact `L` contained in `B`
the set `B ∩ f ⁻¹' L` is compact, provided the the same is known for the whole basin. -/
theorem isCompact_inter_preimage_of_isCompact {f : ℂ → ℂ} {D B L : Set ℂ}
    (hprop : ∀ K : Set ℂ, K ⊆ MandelDim.ParabolicBasin f D → IsCompact K →
      IsCompact (MandelDim.ParabolicBasin f D ∩ f ⁻¹' K))
    (hBsub : B ⊆ MandelDim.ParabolicBasin f D)
    (hBcl : ∀ y ∈ MandelDim.ParabolicBasin f D, y ∈ closure B → y ∈ B)
    (hLB : L ⊆ B) (hLc : IsCompact L) :
    IsCompact (B ∩ f ⁻¹' L) := by
  -- `L` lies in the basin, so the basin version is compact.
  have hLC : L ⊆ MandelDim.ParabolicBasin f D := hLB.trans hBsub
  have hC : IsCompact (MandelDim.ParabolicBasin f D ∩ f ⁻¹' L) := hprop L hLC hLc
  -- `B ∩ f ⁻¹' L` is closed in that compact set: any of its limit points that stays in the
  -- basin lies in `B` (hypothesis `hBcl`), and already lies in `f ⁻¹' L`.
  have hkey : B ∩ f ⁻¹' L
      = (MandelDim.ParabolicBasin f D ∩ f ⁻¹' L) ∩ closure (B ∩ f ⁻¹' L) := by
    apply Set.Subset.antisymm
    · intro x hx
      exact ⟨⟨hBsub hx.1, hx.2⟩, subset_closure hx⟩
    · rintro x ⟨hxC, hxcl⟩
      exact ⟨hBcl x hxC.1 (closure_mono Set.inter_subset_left hxcl), hxC.2⟩
  rw [hkey]
  exact hC.inter_right isClosed_closure

end Work.Horn.Basins
