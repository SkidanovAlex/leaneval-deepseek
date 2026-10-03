import Mathlib
import Submission.Work.Interfaces.HornParts
import Submission.Work.Horn.basic

/-!
# Surfjectivity of the pushed-down horn map onto its parabolic basin

`immediate_basins_of_petals` (the `q = 1` step of Lemma 5.4) needs
`∀ z ∈ ParabolicBasin g Dg, ∃ w ∈ Dg, g w = z` for the pushed-down horn map
`g = pushdown d.E` on `Dg = insert 0 (π '' (Bu ∪ Bl))`.  This is easy once `E : Bu → ℂ` is onto:
`E` descends to `g` on `π '' Bu` (via `T`-invariance of `Bu` and `E_add_one`), and `0` is not in the
basin.
-/

namespace Work.Horn

noncomputable section

open MandelDim Set Filter Topology

/-- `E` descends to `pushdown d.E` on `π '' Bu`. -/
theorem pushdown_piExp_on_Bu {f₀ : ℂ → ℂ} {D₀ B : Set ℂ} (d : MandelDim.ParabData f₀ D₀)
    (hBuT : MandelDim.IsTInvariant (MandelDim.BuOf d B))
    (hsub : MandelDim.BuOf d B ⊆ d.DE) {w : ℂ} (hw : w ∈ MandelDim.BuOf d B) :
    MandelDim.pushdown d.E (MandelDim.piExp w) = MandelDim.piExp (d.E w) :=
  MandelDim.pushdown_piExp hBuT
    (fun u hu _ => Work.Horn.MandelDim.ParabData.E_add_one d (hsub hu) (hsub ((hBuT u).mp hu))) hw

/-- **`g = pushdown d.E` maps `Dg` onto its parabolic basin.** -/
theorem pushdown_basin_surj (hTopo : MandelDim.HornTopoStatement)
    (f₀ : ℂ → ℂ) (D₀ B : Set ℂ) (c : ℂ) (d : MandelDim.ParabData f₀ D₀)
    (hsetup : MandelDim.IsF0Setup f₀ D₀ B c)
    (hsurjE : ∀ y : ℂ, ∃ w ∈ MandelDim.BuOf d B, d.E w = y)
    (h0out : (0 : ℂ) ∉ MandelDim.ParabolicBasin (MandelDim.pushdown d.E)
      (insert 0 (MandelDim.piExp '' (MandelDim.BuOf d B ∪ MandelDim.BlOf d B)))) :
    ∀ z ∈ MandelDim.ParabolicBasin (MandelDim.pushdown d.E)
        (insert 0 (MandelDim.piExp '' (MandelDim.BuOf d B ∪ MandelDim.BlOf d B))),
      ∃ w ∈ insert 0 (MandelDim.piExp '' (MandelDim.BuOf d B ∪ MandelDim.BlOf d B)),
        MandelDim.pushdown d.E w = z := by
  intro z hz
  have htopo := hTopo f₀ D₀ B c d hsetup
  have htBu : MandelDim.IsTInvariant (MandelDim.BuOf d B) := htopo.2.2.1
  have hsub : MandelDim.BuOf d B ∪ MandelDim.BlOf d B ⊆ d.DE := htopo.2.2.2.2.2.2
  have hzne : z ≠ 0 := by
    intro hz0
    exact h0out (hz0 ▸ hz)
  obtain ⟨U, hU, hmap, -⟩ := hz
  obtain ⟨y, hy⟩ : ∃ y : ℂ, MandelDim.piExp y = z :=
    ⟨Complex.log z / (2 * Real.pi * Complex.I), MandelDim.piExp_log_div z hzne⟩
  obtain ⟨w, hw, hwE⟩ := hsurjE y
  exact ⟨MandelDim.piExp w, Or.inr ⟨w, Or.inl hw, rfl⟩,
    by rw [pushdown_piExp_on_Bu d htBu (fun u hu => hsub (Or.inl hu)) hw, hwE, hy]⟩

end

end Work.Horn
