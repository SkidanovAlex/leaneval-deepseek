import Mathlib
import Submission.Work.Interfaces.Parabolic
import Submission.Work.Repel.Spec
import Submission.Work.L62.basin_iface

namespace Work.Repel

open MandelDim

/-- A point `ζ` whose Fatou-coordinate value `φ ζ` is `s₀ · π(w)`, with `π w` outside the
pushed-down horn-map domain `{0} ∪ π(Bᵘ ∪ Bˡ)`, cannot lie in the lifted horn-map domain
`D_E = φ⁻¹(basin)` of the level-1 germ: the parabolic basin is contained in the germ's domain,
and `Dg0germ = s₀ • ({0} ∪ π(Bᵘ ∪ Bˡ))`. -/
theorem not_mem_DE_scaled {f₀ : ℂ → ℂ} {D₀ : Set ℂ} (d : MandelDim.ParabData f₀ D₀) (hd : MandelDim.HornData d)
    (d₁ : MandelDim.ParabData (Work.Repel.g0germ d) (Work.Repel.Dg0germ d hd)) (w ζ : ℂ)
    (hw : MandelDim.piExp w ∉ insert 0 (MandelDim.piExp '' (hd.Bu ∪ hd.Bl)))
    (hζ : MandelDim.ParabData.φ d₁ ζ = Work.Repel.s0 d * MandelDim.piExp w) : ζ ∉ MandelDim.ParabData.DE d₁ := by
  intro hmem
  -- `D_E = φ⁻¹(basin)`; membership unfolds to the pair `(ζ ∈ Dφ, φ ζ ∈ basin)`
  have hb : MandelDim.ParabData.φ d₁ ζ ∈
      MandelDim.ParabolicBasin (Work.Repel.g0germ d) (Work.Repel.Dg0germ d hd) := hmem.2
  rw [hζ] at hb
  -- the basin is contained in the germ's domain `Dg0germ d hd = s₀ • ({0} ∪ π(Bᵘ ∪ Bˡ))`
  have hD : Work.Repel.s0 d * MandelDim.piExp w ∈ Work.Repel.Dg0germ d hd :=
    Work.L62.parabolicBasin_subset _ _ hb
  rw [Work.Repel.Dg0germ_eq d hd] at hD
  obtain ⟨z, hz, hzeq⟩ := hD
  apply hw
  have hz' : z = MandelDim.piExp w :=
    mul_left_cancel₀ (Work.Repel.s0_ne_zero d hd) hzeq
  rwa [hz'] at hz

end Work.Repel
