import Mathlib.Analysis.SpecialFunctions.Trigonometric.Basic
import Submission.Work.FTS.EllipticEst.OpenQDefs

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

/-!
# `Work.FTS_RegExport.RXT0.RXJets.slabDefs` — the slab of the coefficient-jet statements

The slab `(0,∞) × (0,π/2) × [0,S]` on which the order-`≤ 2` mixed jets of the three transport
coefficients `VR`, `bR`, `cR` are jointly continuous, together with its membership
characterisation and the projections used to pull a slab statement back to
`(0,∞) × [0,S]`, to the open quadrant `Q0`, and to `(0,π/2)` / `[0,S]`.
-/

noncomputable section

open scoped Real Topology
open Set Filter

namespace Work.FTS_RegExport.RXT0.RXJets

set_option autoImplicit false

/-- **The slab** `(0,∞) × (0,π/2) × [0,S]` of the coefficient-jet statements. -/
def slb (S : ℝ) : Set (ℝ × ℝ × ℝ) :=
  Set.Ioi (0 : ℝ) ×ˢ (Set.Ioo (0 : ℝ) (Real.pi / 2) ×ˢ Set.Icc (0 : ℝ) S)

/-- Membership in the slab, in the conjunction shape used by `intro`/`obtain`. -/
theorem mem_slb {S : ℝ} {p : ℝ × ℝ × ℝ} :
    p ∈ slb S ↔ 0 < p.1 ∧ 0 < p.2.1 ∧ p.2.1 < Real.pi / 2 ∧ 0 ≤ p.2.2 ∧ p.2.2 ≤ S := by
  simp only [slb, Set.mem_prod, Set.mem_Ioi, Set.mem_Ioo, Set.mem_Icc]
  tauto

/-- The `(z,θ)`-projection of the slab is the open quadrant. -/
theorem mapsTo_slab_Q0 {S : ℝ} :
    Set.MapsTo (fun p : ℝ × ℝ × ℝ => (p.1, p.2.1)) (slb S) Work.FTS.EllipticEst.Q0 := by
  intro p hp
  obtain ⟨h1, h2, h3, -, -⟩ := mem_slb.mp hp
  exact Work.FTS.EllipticEst.mem_Q0.mpr ⟨h1, h2, h3⟩

/-- The `(z,τ)`-projection of the slab lies in `(0,∞) × [0,S]`. -/
theorem mapsTo_slab_zτ {S : ℝ} :
    Set.MapsTo (fun p : ℝ × ℝ × ℝ => (p.1, p.2.2)) (slb S)
      (Set.Ioi (0 : ℝ) ×ˢ Set.Icc (0 : ℝ) S) := by
  intro p hp
  obtain ⟨h1, -, -, h4, h5⟩ := mem_slb.mp hp
  exact ⟨h1, h4, h5⟩

/-- The `τ`-projection of the slab lies in `[0,S]`. -/
theorem mapsTo_slab_τ {S : ℝ} :
    Set.MapsTo (fun p : ℝ × ℝ × ℝ => p.2.2) (slb S) (Set.Icc (0 : ℝ) S) := by
  intro p hp
  obtain ⟨-, -, -, h4, h5⟩ := mem_slb.mp hp
  exact ⟨h4, h5⟩

/-- The `θ`-projection of the slab lies in `(0,π/2)`. -/
theorem mapsTo_slab_θ {S : ℝ} :
    Set.MapsTo (fun p : ℝ × ℝ × ℝ => p.2.1) (slb S) (Set.Ioo (0 : ℝ) (Real.pi / 2)) := by
  intro p hp
  obtain ⟨-, h2, h3, -, -⟩ := mem_slb.mp hp
  exact ⟨h2, h3⟩

end Work.FTS_RegExport.RXT0.RXJets
