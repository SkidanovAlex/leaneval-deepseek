/-
Copyright (c) 2026. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: FatouCoord team
-/
import Submission.Work.FatouCoord.Setup

-- Lean v4.35.0-rc3 / Mathlib 5e0c4e5 made `isDefEq` respect transparency when unifying instances; with it,
-- `ZMod.instField` and `ZMod.commRing` (and `Neg (ZMod p)` via `SubtractionMonoid`) no longer unify, which
-- breaks `ring`/`rw`/module-instance search on `ZMod p`. Restore the v4.34 behaviour for this file.
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false


/-!
# The parabolic flower (Leau–Fatou) — interface for the EL / F areas

This file contains the *interface* requested by the lead in
`Submission/Work/NOTES_LEAD_mandelbar_EL_F_contracts.md` §4: the structure `ParabolicFlower`
collecting the Leau–Fatou flower of a simple parabolic fixed point `z₀` of a holomorphic map
`F` that admits an antiholomorphic square root `g` (`g ∘ g = F`), together with the
intermediate predicate `IsRepellingCoord` used to build the entire repelling coordinate `Ψ`.

Conventions (as in the rest of the `FatouCoord` area):
* `star` is complex conjugation;
* the chart at `z₀` is `w = -1/(z - z₀)`, so `Ψ w ≈ z₀ - 1/w` for `Re w → -∞` (repelling side)
  and the attracting petal lives at `Re w → +∞`;
* `IsAntiholomorphicFatouOn g φa Pa` says `φa (g z) = star (φa z) + 1/2` on `Pa`, which is
  Hubbard–Schleicher Lemma 2.3 in local form.
-/

open scoped Topology
open Set Filter Metric Function

set_option linter.unusedVariables false
set_option linter.unusedSimpArgs false
set_option linter.unreachableTactic false
set_option linter.unusedTactic false

namespace Work.FatouCoord

noncomputable section

variable {F g Ψ φa : ℂ → ℂ} {z₀ : ℂ} {R : ℝ}

/-- A **repelling coordinate** at `z₀`: a holomorphic function on the left half-plane
`{Re w < -R}` which is equivariant for `F` (so that it descends to the repelling part of the
Ecalle cylinder) and which converges to `z₀` at the far end `Re w → -∞`.  This is the local
object out of which the entire coordinate `Ψ` of `ParabolicFlower` is built. -/
structure IsRepellingCoord (F : ℂ → ℂ) (z₀ : ℂ) (R : ℝ) (Ψ : ℂ → ℂ) : Prop where
  R_pos : 0 < R
  diff : DifferentiableOn ℂ Ψ {w : ℂ | w.re < -R}
  shift : ∀ w : ℂ, w.re < -R → Ψ (w + 1) = F (Ψ w)
  inj : Set.InjOn Ψ {w : ℂ | w.re < -R}
  ne_zero : ∀ w : ℂ, w.re < -R → Ψ w ≠ z₀
  small : ∀ ε : ℝ, 0 < ε → ∃ R' : ℝ, ∀ w : ℂ, w.re < -R' → ‖Ψ w - z₀‖ < ε

/-- **Leau–Fatou flower** of a simple parabolic fixed point `z₀` of a holomorphic map `F` that
has an antiholomorphic square root `g` (`g ∘ g = F`), as used by the EL and F areas
(Hubbard–Schleicher Lemma 2.3 and §4 of the lead's contracts).

All the fields are consumed downstream:
* `Pa`, `φa` — the (wide) attracting petal and its antiholomorphic Fatou coordinate
  `φa ∘ g = star ∘ φa + 1/2`;
* `Ψ` — the *entire* repelling coordinate, equivariant for the shift (`Ψ_shift`) and for the
  antiholomorphic involution (`Ψ_anti`);
* `enters_Pa` and `cover` — every point that converges to `z₀` eventually enters `Pa`, and the
  petal together with every repelling half-plane level covers a punctured neighbourhood of
  `z₀`. -/
structure ParabolicFlower (F g : ℂ → ℂ) (z₀ : ℂ) where
  /-- attracting petal (wide: opening `3π/2` in the chart) -/
  Pa : Set ℂ
  /-- attracting antiholomorphic Fatou coordinate on `Pa` -/
  φa : ℂ → ℂ
  /-- inverse repelling coordinate, defined on all of `ℂ` -/
  Ψ : ℂ → ℂ
  isOpen_Pa : IsOpen Pa
  isPreconnected_Pa : IsPreconnected Pa
  z₀_not_mem : z₀ ∉ Pa
  mapsTo_Pa : MapsTo F Pa Pa
  tendsto_Pa : ∀ z ∈ Pa, Tendsto (fun n : ℕ => F^[n] z) atTop (nhds z₀)
  enters_Pa : ∀ z : ℂ, Tendsto (fun n : ℕ => F^[n] z) atTop (nhds z₀) →
    (∀ n : ℕ, F^[n] z ≠ z₀) → ∃ n : ℕ, F^[n] z ∈ Pa
  φa_fatou : IsAntiholomorphicFatouOn g φa Pa ∧ Set.InjOn φa Pa
  Ψ_diff : Differentiable ℂ Ψ
  Ψ_shift : ∀ w : ℂ, Ψ (w + 1) = F (Ψ w)
  Ψ_anti : ∀ w : ℂ, Ψ (star w + 1 / 2) = g (Ψ w)
  /-- at the far repelling end `Ψ` is as small as we like -/
  Ψ_small : ∀ ε : ℝ, 0 < ε → ∃ R : ℝ, ∀ w : ℂ, w.re < -R → Ψ w ≠ z₀ ∧ ‖Ψ w - z₀‖ < ε
  /-- `Ψ` is injective on a far left half-plane -/
  Ψ_inj : ∃ R₀ : ℝ, Set.InjOn Ψ {w : ℂ | w.re < -R₀}
  /-- the far ends (large `|Im|`) of the repelling half-planes lie in the attracting petal -/
  Ψ_ends : ∃ R₀ : ℝ, ∀ w : ℂ, w.re < -R₀ → R₀ < |w.im| → Ψ w ∈ Pa
  /-- every level `{Re w < -R}` of `Ψ`, together with `Pa`, covers a punctured neighbourhood of `z₀` -/
  cover : ∀ R : ℝ, ∃ r : ℝ, 0 < r ∧ ∀ z : ℂ, 0 < ‖z - z₀‖ → ‖z - z₀‖ < r →
    z ∈ Pa ∨ ∃ w : ℂ, w.re < -R ∧ Ψ w = z

theorem ParabolicFlower.isOpen (h : ParabolicFlower F g z₀) : IsOpen h.Pa := h.isOpen_Pa

end

end Work.FatouCoord
