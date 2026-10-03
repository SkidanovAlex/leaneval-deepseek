import Mathlib
import Submission.Work.Interfaces.Parabolic

open MandelDim Set Filter Topology
open scoped Topology

namespace Work.L62

/-- The lifted horn map `d.E = Φ ∘ φ` is `T`-equivariant (`w ↦ w + 1`) in the end regions `{η₀ < |Im w|}`.  Uses only the §4.1 fields: `ends_sub` puts `w` and `w + 1` in `Dφ`, `φ (w+1) = g₀ (φ w)` by `φ_abel`, and `Φ_abel` at the basin point `φ w` gives `Φ (g₀ (φ w)) = Φ (φ w) + 1`. -/
theorem E_equivariant_of_eta0 {g₀ : ℂ → ℂ} {D : Set ℂ} (d : ParabData g₀ D) {w : ℂ}
    (hw : d.η₀ < |w.im|) : d.E (w + 1) = d.E w + 1 := by
  have hw1 : d.η₀ < |(w + 1).im| := by simpa using hw
  obtain ⟨hwd, hφw⟩ := d.ends_sub w hw
  obtain ⟨hw1d, _⟩ := d.ends_sub (w + 1) hw1
  have habel := d.φ_abel w hwd hw1d
  show d.Φ (d.φ (w + 1)) = d.Φ (d.φ w) + 1
  rw [habel, d.Φ_abel (d.φ w) hφw]

end Work.L62
