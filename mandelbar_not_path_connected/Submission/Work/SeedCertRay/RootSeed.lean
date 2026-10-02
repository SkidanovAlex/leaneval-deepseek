/-
# `Work.SeedCertRay.RootSeed` — the explicit root seed of the α-root arc

Assembly of the deliverable of the area (§2.1 of `NOTES_LEAD_mandelbar_noncusp.md`): the
interval ray-chain certificate (`Final.landsAt_alphas_data`) proves that the rays `α₁` and `α₂`
land at the certified parabolic point `z₁`; together with the parabolic data certified by
`SeedCertNum` (membership `c ∈ Mandelbar`, exact period `5`, multiplier `1`, `F'' ≠ 0`) this is
exactly `Work.SeedExist.ExplicitRootSeed`.
-/
import Submission.Work.SeedCertRay.Final
import Submission.Work.SeedExist.Defs

-- Lean v4.35.0-rc3 / Mathlib 5e0c4e5 made `isDefEq` respect transparency when unifying instances; with it,
-- `ZMod.instField` and `ZMod.commRing` (and `Neg (ZMod p)` via `SubtractionMonoid`) no longer unify, which
-- breaks `ring`/`rw`/module-instance search on `ZMod p`. Restore the v4.34 behaviour for this file.
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false


noncomputable section

namespace Work.SeedCertRay

open LeanEval.ComplexAnalysis (Tantibar Mandelbar)

/-- **The explicit root seed**, assembled from the chain certificate and the `SeedCertNum` data.

The two petal facts `hP1`/`hP2` are `SeedCertNum`'s `petal_P1`/`petal_P2` for `R = 4` (this
area's `Petal`/`fatou` are its `petal`/`fatouW`, and `Work.EL.F c = (Tantibar c)^[10]`); the
hypotheses `hcX`, `hz1`, `hA` are its box inclusions, and `hper`, `hmult`, `hjet` its A1/A3
exports (`exact period`, `multiplier2 c 5 z₁ = 1`, `iteratedDeriv 2 (F c) z₁ ≠ 0`). -/
theorem explicitRootSeed_data {c z₁ A : ℂ} {φ : ℂ → ℂ} (hN : Work.EL.DynB c φ)
    (hφ : Work.ParamRays.IsDynBottcher c φ) (hmem : c ∈ Mandelbar) (hc2 : ‖c‖ ≤ 2)
    (hcX : Xb.mem c) (hz1 : Zb.mem z₁) (hA : Ab.mem A) (hg : (Tantibar c)^[5] z₁ = z₁)
    (hper : ∀ j : ℕ, 0 < j → j < 5 → (Tantibar c)^[j] z₁ ≠ z₁)
    (hmult : Work.Landing.multiplier2 c 5 z₁ = 1)
    (hjet : iteratedDeriv 2 (Work.FSeed.F c) z₁ ≠ 0)
    (δ ρ₁ : ℝ) (hρ₁ : 0 < ρ₁) (hδ : 0 < δ) (hAne : A ≠ 0) (hRQ : 1 ≤ 4 * ‖A‖ * ρ₁)
    (hP1 : ∀ z : ℂ, ‖z - z₁‖ = ρ₁ → Work.EL.F c z ∉ Petal z₁ A 4)
    (hP2 : ∀ z : ℂ, ‖z - z₁‖ ≤ ρ₁ → Work.EL.F c z ∈ Petal z₁ A 4 →
      z ∈ Petal z₁ A 4 ∧ (fatou z₁ A z).re ≤ (fatou z₁ A (Work.EL.F c z)).re - δ) :
    Work.SeedExist.ExplicitRootSeed := by
  have hland := landsAt_alphas_data hN hφ hmem hc2 hcX z₁ A hz1 hA hg δ ρ₁ hρ₁ hδ hAne hRQ hP1 hP2
  refine ⟨c, z₁, hmem, hg, hper, hmult, hjet, ?_, ?_⟩
  · simpa only [Work.EL.alpha1, Work.FSeed.α₁] using hland.1
  · simpa only [Work.EL.alpha2, Work.FSeed.α₂] using hland.2

end Work.SeedCertRay
