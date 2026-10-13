/-
# `FTS/PhiStar/CoreAux/FieldsDefs.lean` — the `Ŷ`-expressions of the eleven `StarPkgo2` fields

`VocabO2.StarCore α Cs Φs` gives `FlatW 7 (Ycheck α Φs) (Cs·α)` for

`Ŷ := Ycheck α Φs = ((z+1)/z)·(Φ̃_*/σ)`,   `Φ̃_* = PhiTs α Φs = PhiTil α (Fstar α) Φs`,  `σ = sin 2θ`.

The transport coefficients `ℛ, 𝒱, 𝒰` of `Work.Construction` are, on the open quadrant `Q0`,
*linear* combinations of `Ŷ` and the two blocks `D_zŶ`, `D_θŶ` — this is the content of the
substitution identities of `Work.FTS.H2.StarPkg.Subst` together with
`Φ̌ := Φ̃_*/σ = (z/(z+1))·Ŷ`.  Explicitly (all on `Q0`):

* `((z+1)/z)·ℛ(Φ̃_*) = 2Ŷ + 2α sin²θ·(Ŷ/(z+1) + D_zŶ) + D_θŶ`  (`EH`);
* `((z+1)/z)·𝒱(Φ̃_*) = 2(cos²θ − 2 sin²θ)·Ŷ + D_θŶ`  (`EVz`),  `𝒱 = (z/(z+1))·EVz`  (`EV`);
* `((z+1)/z)·𝒰(Φ̃_*)/σ = −(3Ŷ + α(Ŷ/(z+1) + D_zŶ))`  (`EUz`),  `𝒰/σ = (z/(z+1))·EUz`  (`EU`);
* `∂_θ𝒰(Φ̃_*) = −(2 cos 2θ·(z/(z+1))·W₁ + σ·(z/(z+1))·(3∂_θŶ + α(∂_θŶ/(z+1) + z∂_z∂_θŶ)))` (`EPU`),

where `D_zŶ = z∂_zŶ` (`Yblk`), `D_θŶ = σ·∂_θŶ` (`Tblk`) and `W₁ = 3Ŷ + α(Ŷ/(z+1) + D_zŶ)`.

This file only *defines* those expressions (and the two blocks); the identities with the
transport coefficients, the flat bounds and the boundary vanishing are proved in
`CoreAux/Fields.lean`.
-/
import Mathlib.Analysis.Complex.Trigonometric
import Submission.Work.FTS.PhiStar.CoreAux.Defs

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

noncomputable section

open scoped Real Topology
open MeasureTheory Set Filter

namespace Work.FTS.PhiStar

set_option autoImplicit false
set_option linter.unusedVariables false

/-- The radial block `D_zŶ = z ∂_zŶ`. -/
def Yblk (Y : ℝ → ℝ → ℝ) : ℝ → ℝ → ℝ := fun z θ => z * Work.Spaces.pz Y z θ

/-- The angular block `D_θŶ = sin(2θ)·∂_θŶ`. -/
def Tblk (Y : ℝ → ℝ → ℝ) : ℝ → ℝ → ℝ :=
  fun z θ => Work.Construction.s2 θ * Work.Spaces.pth Y z θ

/-- The combination `W₁ = 3Ŷ + α(Ŷ/(z+1) + D_zŶ)` appearing in `𝒰` and `∂_θ𝒰`. -/
def Wone (α : ℝ) (Y : ℝ → ℝ → ℝ) : ℝ → ℝ → ℝ :=
  fun z θ => 3 * Y z θ + α * (Y z θ / (z + 1) + Yblk Y z θ)

/-- `((z+1)/z)·ℛ(Φ̃_*)` in terms of `Ŷ`. -/
def EH (α : ℝ) (Y : ℝ → ℝ → ℝ) : ℝ → ℝ → ℝ :=
  fun z θ => 2 * Y z θ + 2 * α * Real.sin θ ^ 2 * (Y z θ / (z + 1) + Yblk Y z θ)
    + Tblk Y z θ

/-- `((z+1)/z)·𝒱(Φ̃_*)` in terms of `Ŷ`. -/
def EVz (Y : ℝ → ℝ → ℝ) : ℝ → ℝ → ℝ :=
  fun z θ => 2 * (Real.cos θ ^ 2 - 2 * Real.sin θ ^ 2) * Y z θ + Tblk Y z θ

/-- `𝒱(Φ̃_*)` in terms of `Ŷ`. -/
def EV (Y : ℝ → ℝ → ℝ) : ℝ → ℝ → ℝ := fun z θ => z / (z + 1) * EVz Y z θ

/-- `𝒰(Φ̃_*)/σ` in terms of `Ŷ`. -/
def EU (α : ℝ) (Y : ℝ → ℝ → ℝ) : ℝ → ℝ → ℝ :=
  fun z θ => -(z / (z + 1)) * Wone α Y z θ

/-- `((z+1)/z)·𝒰(Φ̃_*)/σ` in terms of `Ŷ`. -/
def EUz (α : ℝ) (Y : ℝ → ℝ → ℝ) : ℝ → ℝ → ℝ := fun z θ => -Wone α Y z θ

/-- `∂_θ𝒰(Φ̃_*)` in terms of `Ŷ`. -/
def EPU (α : ℝ) (Y : ℝ → ℝ → ℝ) : ℝ → ℝ → ℝ :=
  fun z θ => -(2 * Real.cos (2 * θ) * (z / (z + 1)) * Wone α Y z θ
    + Work.Construction.s2 θ * (z / (z + 1))
      * (3 * Work.Spaces.pth Y z θ
        + α * (Work.Spaces.pth Y z θ / (z + 1) + z * Work.Spaces.pz (Work.Spaces.pth Y) z θ)))

end Work.FTS.PhiStar
