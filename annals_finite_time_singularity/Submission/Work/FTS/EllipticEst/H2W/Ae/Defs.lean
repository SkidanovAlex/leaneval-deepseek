/-
Copyright: work module for the Elgindi finite-time singularity project.

# `H2W.Ae.Defs` — the *almost-everywhere* class of the level-`0` elliptic estimate

This module fixes the hypothesis class of the lemma
`Work.FTS.EllipticEst.H2W.level0Ae`:

```
∃ C > 0, ∀ α u G, AeData α u G →
    α^4 * HkSq α 0 (z^2 ∂_zz u) + HkSq α 0 (∂_θθ u) ≤ C * HkSq α 0 G
```

(the paper's `(radialandangularweightL2)`, i.e. Steps 1–2 of Proposition `prop:H2` of
T. M. Elgindi, *Finite-time singularity formation for `C^{1,α}` solutions to the incompressible
Euler equations on `ℝ³`*, Annals of Math. **194** (2021), in the weak class where

* `bslOp α u = G` is required only on the *open* quadrant `(0,∞) × (0,π/2)`,
* `u` is only `C^∞` on the open quadrant (no `SmoothNbhd`, no decay at `z = ∞`),
* the two solvability conditions `F_*(u) = 0`, `F_*(G) = 0` are assumed only for
  *almost every* `z > 0`,
* the `ℋ⁰`-integrands of only `G`, `z^2 ∂_zz u` and `∂_θθ u` are assumed honest, while `u`,
  `z ∂_z u` and their `θ`-derivatives are *not*.

## Vocabulary

* `σ θ = sin(2θ)^{-η}` (`η = 99/100`), `w z = (1+z)^2/z^2`, `ρ = w^2 σ`;
* `‖g‖_ρ² = HkSq α 0 g = ∫_z ∫_θ (g z θ · w z / sin(2θ)^{η/2})²` for honest `g`
  (`HkSq_zero_eq`);
* `A = z^2 ∂_zz u`, `B = ∂_θθ u`, `Grad = z ∂_z u`, `U = ∂_θ (tan θ · u)`;
* `F_* f z = ∫_θ f z θ sinθ cos²θ dθ` (`Work.Elliptic.Fstar`).

The two *almost everywhere* moment conditions are not a technicality: with the equation they
say precisely that the `θ`-slices of `u` carry no jump at the endpoints (the boundary term in
`⟨Lzero u, sinθcos²θ⟩ = ⟨u, Lzero* (sinθcos²θ)⟩` vanishes), which is the endpoint regularity
that `SmoothNbhd` would otherwise supply.
-/
import Mathlib.Analysis.Calculus.ContDiff.Defs
import Mathlib.MeasureTheory.Measure.Haar.OfBasis
import Submission.Work.Spaces.Defs
import Submission.Work.Elliptic.Defs
import Submission.Work.FTS.EllipticEst.Defs

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

noncomputable section

open scoped Real Topology
open MeasureTheory Set Filter

namespace Work.FTS.EllipticEst.H2W.Ae

set_option autoImplicit false

/-- **The almost-everywhere class of the level-`0` elliptic estimate** (the hypotheses of
`Work.FTS.EllipticEst.H2W.level0Ae`). -/
def AeData (α : ℝ) (u G : ℝ → ℝ → ℝ) : Prop :=
  0 < α ∧ α ≤ 1 / 4 ∧
    (∀ z, 0 < z → ∀ θ, 0 < θ → θ < Real.pi / 2 → Work.Elliptic.bslOp α u z θ = G z θ) ∧
    (∀ z, u z 0 = 0) ∧ (∀ z, u z (Real.pi / 2) = 0) ∧
    (∀ n : ℕ, ContDiffOn ℝ n (Function.uncurry u)
      (Set.Ioi 0 ×ˢ Set.Ioo 0 (Real.pi / 2))) ∧
    Work.Spaces.HkMem α 0 G ∧
    Work.Spaces.HkMem α 0 (fun z θ => z ^ 2 * Work.Spaces.pzIter 2 u z θ) ∧
    Work.Spaces.HkMem α 0 (Work.Spaces.pthIter 2 u) ∧
    (∀ᵐ z ∂(MeasureTheory.volume.restrict (Set.Ioi 0)), Work.Elliptic.Fstar u z = 0) ∧
    (∀ᵐ z ∂(MeasureTheory.volume.restrict (Set.Ioi 0)), Work.Elliptic.Fstar G z = 0)

/-- The open quadrant `(0,∞) × (0,π/2)`. -/
def quad : Set (ℝ × ℝ) := Set.Ioi 0 ×ˢ Set.Ioo 0 (Real.pi / 2)

/-- The radial first derivative `z ∂_z u` (`D_z u`). -/
def grad (u : ℝ → ℝ → ℝ) : ℝ → ℝ → ℝ := fun z θ => z * Work.Spaces.pz u z θ

/-- The radial second derivative `z^2 ∂_zz u`. -/
def rad2 (u : ℝ → ℝ → ℝ) : ℝ → ℝ → ℝ := fun z θ => z ^ 2 * Work.Spaces.pzIter 2 u z θ

/-- The angular first order term `∂_θ (tan θ · u)`. -/
def ang1 (u : ℝ → ℝ → ℝ) : ℝ → ℝ → ℝ :=
  fun z θ => Work.Spaces.pth (fun z θ => Real.tan θ * u z θ) z θ

/-- The angular second derivative `∂_θθ u`. -/
def ang2 (u : ℝ → ℝ → ℝ) : ℝ → ℝ → ℝ := Work.Spaces.pthIter 2 u

/-- The `ρ`-norm of `g`, i.e. the square root of `HkSq α 0 g`. -/
def nrm (α : ℝ) (g : ℝ → ℝ → ℝ) : ℝ := Real.sqrt (Work.Spaces.HkSq α 0 g)

theorem AeData.hα {α : ℝ} {u G : ℝ → ℝ → ℝ} (h : AeData α u G) : 0 < α := h.1

theorem AeData.hα4 {α : ℝ} {u G : ℝ → ℝ → ℝ} (h : AeData α u G) : α ≤ 1 / 4 := h.2.1

theorem AeData.eq {α : ℝ} {u G : ℝ → ℝ → ℝ} (h : AeData α u G) :
    ∀ z, 0 < z → ∀ θ, 0 < θ → θ < Real.pi / 2 → Work.Elliptic.bslOp α u z θ = G z θ :=
  h.2.2.1

theorem AeData.dirZero {α : ℝ} {u G : ℝ → ℝ → ℝ} (h : AeData α u G) : ∀ z, u z 0 = 0 :=
  h.2.2.2.1

theorem AeData.dirPi {α : ℝ} {u G : ℝ → ℝ → ℝ} (h : AeData α u G) :
    ∀ z, u z (Real.pi / 2) = 0 := h.2.2.2.2.1

theorem AeData.smooth {α : ℝ} {u G : ℝ → ℝ → ℝ} (h : AeData α u G) :
    ∀ n : ℕ, ContDiffOn ℝ n (Function.uncurry u)
      (Set.Ioi 0 ×ˢ Set.Ioo 0 (Real.pi / 2)) :=
  h.2.2.2.2.2.1

theorem AeData.memG {α : ℝ} {u G : ℝ → ℝ → ℝ} (h : AeData α u G) :
    Work.Spaces.HkMem α 0 G := h.2.2.2.2.2.2.1

theorem AeData.memRad2 {α : ℝ} {u G : ℝ → ℝ → ℝ} (h : AeData α u G) :
    Work.Spaces.HkMem α 0 (fun z θ => z ^ 2 * Work.Spaces.pzIter 2 u z θ) :=
  h.2.2.2.2.2.2.2.1

theorem AeData.memAng2 {α : ℝ} {u G : ℝ → ℝ → ℝ} (h : AeData α u G) :
    Work.Spaces.HkMem α 0 (Work.Spaces.pthIter 2 u) := h.2.2.2.2.2.2.2.2.1

theorem AeData.momU {α : ℝ} {u G : ℝ → ℝ → ℝ} (h : AeData α u G) :
    ∀ᵐ z ∂(MeasureTheory.volume.restrict (Set.Ioi 0)), Work.Elliptic.Fstar u z = 0 :=
  h.2.2.2.2.2.2.2.2.2.1

theorem AeData.momG {α : ℝ} {u G : ℝ → ℝ → ℝ} (h : AeData α u G) :
    ∀ᵐ z ∂(MeasureTheory.volume.restrict (Set.Ioi 0)), Work.Elliptic.Fstar G z = 0 :=
  h.2.2.2.2.2.2.2.2.2.2

end Work.FTS.EllipticEst.H2W.Ae
