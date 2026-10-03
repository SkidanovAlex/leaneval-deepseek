import Mathlib
import Submission.Work.L62LD.cyl_family
import Submission.Work.L62LD.refl_pushdown

/-!
# L62LD — existence of the lower-end head data

For every parameter `β` at which the lower horn is *available* (`Work.L62.AvailableDown d hd β`,
i.e. `hd.Bl` avoids the critical class `v + ℤ - β` of `ĥ = d.E - β`), the lower-end inverse
branch `Work.L62.section_Bl` produces a `T`-equivariant holomorphic section `σ` of `ĥ` over
`hd.Bl` whose drift at the lower end is `β - cl`, and `Work.L62LD.refl_pushdown` turns such a
section into the reflected pushdown `H` on the lower cylinder.  This file packages the two into
`Work.L62LD.HeadData` — the provider assumed throughout
`Submission/Work/L62LD/escape.lean`.

Note that `HeadData` lives in `Type` (it carries the two functions `σ` and `H`), whereas
`Work.L62.section_Bl` produces its section as the *proof* of an existential statement.  The
passage from the latter to the former therefore uses `Classical.choose`.
-/

namespace Work.L62LD

open Classical MandelDim Set Filter Topology
open scoped Topology

noncomputable section

variable {g₀ : ℂ → ℂ} {D : Set ℂ}

theorem headDataExists {g₀ : ℂ → ℂ} {D : Set ℂ} (d : MandelDim.ParabData g₀ D)
    (hd : MandelDim.HornData d) {cl : ℂ}
    (hcl : Filter.Tendsto (fun w => d.E w - w) MandelDim.lowerEnd (nhds cl)) :
    Nonempty (∀ β : ℂ, Work.L62.AvailableDown d hd β → Work.L62LD.HeadData d hd cl β) := by
  classical
  refine ⟨fun β hβ => ?_⟩
  -- `AvailableDown` is exactly the critical-value avoidance hypothesis of `Work.L62.section_Bl`
  have havoid : ∀ w ∈ hd.Bl, ∀ k : ℤ, w + β ≠ hd.v + (k : ℂ) := hβ
  -- the section is produced as a *proof* of an existential; select its data
  have hex := Work.L62.section_Bl d hd hcl havoid
  let y₀ : ℂ := Classical.choose hex
  have h1 : ∃ x₀ σ, y₀ ∈ hd.Bl ∧ x₀ ∈ hd.Bl ∧ d.E x₀ - β = y₀ ∧
      DifferentiableOn ℂ σ hd.Bl ∧ σ y₀ = x₀ ∧
      (∀ y ∈ hd.Bl, σ y ∈ hd.Bl ∧ d.E (σ y) - β = y) ∧
      (∀ y ∈ hd.Bl, σ (y + 1) = σ y + 1) ∧
      Filter.Tendsto (fun w => σ w - w - (β - cl)) MandelDim.lowerEnd (nhds 0) :=
    Classical.choose_spec hex
  let x₀ : ℂ := Classical.choose h1
  have h2 : ∃ σ, y₀ ∈ hd.Bl ∧ x₀ ∈ hd.Bl ∧ d.E x₀ - β = y₀ ∧
      DifferentiableOn ℂ σ hd.Bl ∧ σ y₀ = x₀ ∧
      (∀ y ∈ hd.Bl, σ y ∈ hd.Bl ∧ d.E (σ y) - β = y) ∧
      (∀ y ∈ hd.Bl, σ (y + 1) = σ y + 1) ∧
      Filter.Tendsto (fun w => σ w - w - (β - cl)) MandelDim.lowerEnd (nhds 0) :=
    Classical.choose_spec h1
  let σ : ℂ → ℂ := Classical.choose h2
  obtain ⟨hy₀, hx₀, hx₀sec, hσd, hσy₀, hσsec, hσT, hσlim⟩ := Classical.choose_spec h2
  have hσmem : ∀ y ∈ hd.Bl, σ y ∈ hd.Bl := fun y hy => (hσsec y hy).1
  have hσsec' : ∀ y ∈ hd.Bl, d.E (σ y) - β = y := fun y hy => (hσsec y hy).2
  -- the reflected pushdown `H = reflPushdown σ` has all the cylinder-side properties
  obtain ⟨hH0, hHderiv, hHd, hHmap, hHinj, hHne, hHrel, -⟩ :=
    Work.L62LD.refl_pushdown d hd hcl hσd hσmem hσsec' hσT hσlim
      (H := Work.L62LD.reflPushdown σ) (fun ζ => rfl)
  exact ⟨σ, Work.L62LD.reflPushdown σ, hσd, hσmem, hσsec', hσT, hσlim, (fun ζ => rfl),
    hHd, hHmap, hH0, hHderiv, hHinj, hHne, hHrel⟩

end

end Work.L62LD
