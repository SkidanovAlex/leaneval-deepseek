import Mathlib
import Submission.Work.Interfaces.Parabolic
import Submission.Work.Horn.basic
import Submission.Work.Horn.Basins.basin_forward

namespace Work.Horn

/-- `T`-invariance of the lifted domain `DE = φ⁻¹(basin)` of the horn map `E = Φ ∘ φ`.

The forward direction `w ∈ DE → w + 1 ∈ DE` uses `succ_iff` together with `φ (Dφ) ⊆ D₀` (which
holds here by hypothesis) and the forward invariance of the parabolic basin; the backward
direction uses `left_inv` and the "backward" implication `z ∈ D₀, f₀ z ∈ basin → z ∈ basin`.

(Neither `φ (Dφ) ⊆ D₀` nor the backward basin implication is a field of `ParabData`; both are
honest extra assumptions for a bounded `D₀` — see `NOTES_SESSION14.md` §2.) -/
theorem DE_T_of_phi_maps_to_D0 {f₀ : ℂ → ℂ} {D₀ : Set ℂ} (d : MandelDim.ParabData f₀ D₀)
    (hφD0 : ∀ w ∈ d.Dφ, d.φ w ∈ D₀)
    (hback : ∀ z ∈ D₀, f₀ z ∈ MandelDim.ParabolicBasin f₀ D₀ →
      z ∈ MandelDim.ParabolicBasin f₀ D₀)
    (hfwd : ∀ z ∈ MandelDim.ParabolicBasin f₀ D₀, f₀ z ∈ MandelDim.ParabolicBasin f₀ D₀) :
    MandelDim.IsTInvariant d.DE := by
  intro w
  simp only [MandelDim.ParabData.DE, Set.mem_ofPred_eq]
  constructor
  · -- forward: `w ∈ DE → w + 1 ∈ DE`
    intro hw
    obtain ⟨hwDφ, hwB⟩ := hw
    have hwD0 : d.φ w ∈ D₀ := hφD0 w hwDφ
    have hsucc : w + 1 ∈ d.Dφ := (d.succ_iff w hwDφ).mpr hwD0
    refine ⟨hsucc, ?_⟩
    rw [d.φ_abel w hwDφ hsucc]
    exact hfwd (d.φ w) hwB
  · -- backward: `w + 1 ∈ DE → w ∈ DE`
    intro hw
    obtain ⟨hw1Dφ, hw1B⟩ := hw
    have hwDφ : w ∈ d.Dφ := by
      have h := d.left_inv (w + 1) hw1Dφ
      simpa using h
    refine ⟨hwDφ, ?_⟩
    have habel := d.φ_abel w hwDφ hw1Dφ
    have hf : f₀ (d.φ w) ∈ MandelDim.ParabolicBasin f₀ D₀ := by
      rw [← habel]
      exact hw1B
    exact hback (d.φ w) (hφD0 w hwDφ) hf

end Work.Horn
