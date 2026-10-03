import Mathlib
import Submission.Work.Pert.MaxDom
import Submission.Work.Interfaces.Parabolic

/-!
# `Work.Pert.DE_open`: openness of the datum's horn domain `DE` and the `K`-thickening

`d.DE = d.Dφ ∩ d.φ ⁻¹ (ParabolicBasin f₀ D₀)` is OPEN: the basin is open *by definition* (an open
sub-neighbourhood witnesses every one of its points, exactly as in the crux's proof), `Dφ` is open,
and `d.φ` is continuous at every point of `Dφ`.

Consequence used by the final PERT assembly (see `NOTES_pert2_findings.md` §L.5): for a compact
`K ⊆ d.DE` there is an OPEN neighbourhood `O ⊇ K` with `closure O ⊆ d.DE`, namely a thickening of
`K`.  This is what lets the crux be applied to a compact `K̂ ⊇ K` WITHOUT any `T`-invariance of
`d.DE` (which is false for a general `f : ℂ → ℂ`).
-/

namespace Work.Pert

open MandelDim

noncomputable section

/-- The parabolic basin is open. -/
theorem isOpen_parabolicBasin {f₀ : ℂ → ℂ} {D₀ : Set ℂ} :
    IsOpen (ParabolicBasin f₀ D₀) := by
  rw [isOpen_iff_mem_nhds]
  intro z hz
  obtain ⟨U, hU, hmap, hconv⟩ := hz
  obtain ⟨V, hVU, hVopen, hzV⟩ := _root_.mem_nhds_iff.mp hU
  refine Filter.mem_of_superset (hVopen.mem_nhds hzV) (fun y hy => ?_)
  exact ⟨V, hVopen.mem_nhds hy, fun n => (hmap n).mono hVU (fun _ hz => hz), hconv.mono hVU⟩

/-- **`d.DE` is open.** -/
theorem DE_isOpen {f₀ : ℂ → ℂ} {D₀ : Set ℂ} (d : ParabData f₀ D₀) : IsOpen d.DE := by
  show IsOpen {w : ℂ | w ∈ d.Dφ ∧ d.φ w ∈ ParabolicBasin f₀ D₀}
  rw [isOpen_iff_mem_nhds]
  intro w hw
  obtain ⟨hwφ, hwb⟩ := hw
  have hcont : ContinuousAt d.φ w :=
    d.φ_holo.continuousOn.continuousAt (d.Dφ_open.mem_nhds hwφ)
  exact Filter.inter_mem (d.Dφ_open.mem_nhds hwφ)
    (hcont.preimage_mem_nhds (isOpen_parabolicBasin.mem_nhds hwb))

/-- **The `K`-thickening**: a compact subset of the open set `d.DE` has an open neighbourhood whose
closure still lies in `d.DE`.  (Used with the crux on `K̂ := closure O ∪ band`.) -/
theorem exists_cthickening_subset_DE {f₀ : ℂ → ℂ} {D₀ : Set ℂ} (d : ParabData f₀ D₀)
    {K : Set ℂ} (hK : IsCompact K) (hKDE : K ⊆ d.DE) :
    ∃ δ : ℝ, 0 < δ ∧ Metric.cthickening δ K ⊆ d.DE :=
  hK.exists_cthickening_subset_open (DE_isOpen d) hKDE

end

end Work.Pert
