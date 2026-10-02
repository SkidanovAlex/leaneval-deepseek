/-
# Growth of the critical Böttcher coordinate at a mandelbar parameter

`Work.SeedDyn.grow_varphiCrit` (**D11** of the design note of the area `Work.SeedDyn`): for
`c ∈ M*` and every real `M`, the set of escaping points `z ∈ esc c` whose Böttcher coordinate
has modulus `≤ M` is *bounded*:

`∃ R', ∀ z ∈ esc c, ‖varphiCrit c z‖ ≤ M → ‖z‖ ≤ R'`.

Equivalently, `‖varphiCrit c ·‖ → ∞` along the escaping set, which is the "properness at
infinity" input (`hgrow`) of the local-homeomorphism glue
`Work.SeedDyn.homeo_of_proper_localHomeo`.

## Proof

The only analytic input is the tangency of a Böttcher coordinate at infinity,
`‖varphiCrit c z - z‖ ≤ (1/2)‖z‖` for all `z` outside some compact set (this is the third
component of `Work.ParamRays.IsCritBottcher`, instantiated at `varphiCrit c`).  Write that
cocompact eventual inequality as `tᶜ ⊆ {z | ‖φ z - z‖ ≤ (1/2)‖z‖}` with `t` compact, and let
`ρ` be a radius with `t ⊆ closedBall 0 ρ` (compactness).  Then for `‖z‖ > max ρ (2M)` we have

* `z ∉ t`, hence `‖φ z - z‖ ≤ ‖z‖/2`, and
* `‖z‖ = ‖φ z + (z - φ z)‖ ≤ ‖φ z‖ + ‖z‖/2`, so `‖z‖/2 ≤ ‖φ z‖`,
* while `‖z‖ > 2M` gives `M < ‖z‖/2`.

So `‖φ z‖ ≤ M` is impossible, and `R' = max ρ (2M)` works.  No property of the escaping set
(or of the mandelbar) is used: the statement holds for every parameter `c`.
-/
import Mathlib
import Submission.Work.SeedDyn.Defs

-- Lean v4.35.0-rc3 / Mathlib 5e0c4e5 made `isDefEq` respect transparency when unifying instances; with it,
-- `ZMod.instField` and `ZMod.commRing` (and `Neg (ZMod p)` via `SubtractionMonoid`) no longer unify, which
-- breaks `ring`/`rw`/module-instance search on `ZMod p`. Restore the v4.34 behaviour for this file.
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false


namespace Work.SeedDyn

set_option linter.unusedVariables false in
theorem grow_varphiCrit {c : ℂ} (hc : c ∈ LeanEval.ComplexAnalysis.Mandelbar) (M : ℝ) :
    ∃ R' : ℝ, ∀ z ∈ Work.SeedDyn.esc c, ‖Work.Bottcher.varphiCrit c z‖ ≤ M → ‖z‖ ≤ R' := by
  -- tangency of the Böttcher coordinate at infinity
  have hev : ∀ᶠ z : ℂ in Filter.cocompact ℂ,
      ‖Work.Bottcher.varphiCrit c z - z‖ ≤ (1 / 2) * ‖z‖ :=
    (Work.Bottcher.isCritBottcher_varphiCrit c).2.2 (1 / 2) (by norm_num)
  obtain ⟨t, ht, hts⟩ := Filter.mem_cocompact.mp hev
  -- the compact exceptional set is contained in a closed ball
  obtain ⟨ρ, hρ⟩ := (Metric.isBounded_iff_subset_closedBall (0 : ℂ)).mp ht.isBounded
  refine ⟨max ρ (2 * M), fun z _ hzM => ?_⟩
  by_contra hcon
  push Not at hcon
  -- `z` is outside the exceptional compact set
  have hzt : z ∉ t := by
    intro hzt
    have h1 := hρ hzt
    rw [Metric.mem_closedBall, dist_zero_right] at h1
    have h2 : ρ < ‖z‖ := lt_of_le_of_lt (le_max_left ρ (2 * M)) hcon
    linarith
  -- hence the tangency estimate holds at `z`
  have hineq : ‖Work.Bottcher.varphiCrit c z - z‖ ≤ (1 / 2) * ‖z‖ := hts hzt
  have hφz : ‖z - Work.Bottcher.varphiCrit c z‖ ≤ ‖z‖ / 2 := by
    rw [norm_sub_rev]
    linarith
  -- `‖φ z‖ ≥ ‖z‖/2`
  have h2 : ‖z‖ / 2 ≤ ‖Work.Bottcher.varphiCrit c z‖ := by
    have hadd : ‖z‖ ≤ ‖Work.Bottcher.varphiCrit c z‖ + ‖z - Work.Bottcher.varphiCrit c z‖ := by
      have hsum : Work.Bottcher.varphiCrit c z + (z - Work.Bottcher.varphiCrit c z) = z := by
        ring
      calc ‖z‖ = ‖Work.Bottcher.varphiCrit c z + (z - Work.Bottcher.varphiCrit c z)‖ := by
            rw [hsum]
        _ ≤ _ := norm_add_le _ _
    linarith
  -- but `‖z‖ > 2M`, so `M < ‖z‖/2`
  have h3 : M < ‖z‖ / 2 := by
    have hle : 2 * M ≤ max ρ (2 * M) := le_max_right _ _
    linarith
  linarith

end Work.SeedDyn
