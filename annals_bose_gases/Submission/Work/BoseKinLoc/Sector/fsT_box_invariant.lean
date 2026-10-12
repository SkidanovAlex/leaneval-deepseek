import Mathlib.Analysis.InnerProductSpace.PiL2
import Submission.Work.BoseKinLoc.Sector.bsOneBody_eq_of_lamBox_eq
import Submission.Work.BoseKinLoc.Sector.momForm_eq_of_lamBox_eq
-- PORT435-BEGIN (v4.35 isDefEq respectTransparency compat)
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- PORT435-END

/-!
# `Work.BoseKinLoc.Sector.fsT_box_invariant` — `fsT` only sees the state on the moving box

FS `eq:DefT`'s localised kinetic word `fsT ℓ d s εT b u ψ` (`Work.BoseKinLoc.Defs`) is a
one-body quadratic form built from the *restriction of the state to the sliding box*
`Λ(u) = lamBox ℓ u = ℓu + [−ℓ/2,ℓ/2]³`:

    `ψ = ψ'` on `Λ(u)`  ⟹  `fsT ℓ d s εT b u ψ = fsT ℓ d s εT b u ψ'`.

This is the "box locality" of the word, and it is exactly what the localisation assembly
consumes: the slot-`i` fibres of an `N`-body state are only defined on the box, so a one-body
form may only depend on the state there.

The word is a sum of four pieces (`fsT_eq_sum`), each of which sees `ψ` only through
`Q_uψ = ψ − m_u(ψ)` and the box `Λ(u)`:

* `neuWord` — `neuFrac` is the `sInf` of trial values that are integrals over `Λ(u)` of
  `Q_uψ` (`NeuFrac.neuFrac_eq_of_lamBox_eq`);
* `gapWord` — the mean-free `L²`-mass `∫_{Λ(u)}(Q_uψ)²` (`gapBare_eq_of_lamBox_eq`);
* `momWord` — the Fourier form of the *windowed* state `θ_u·Q_uψ`, with `θ_u = 1_{Λ(u)}`
  (`momForm_eq_of_lamBox_eq`);
* `mainWord` — the windowed `bsOneBody` form of `χ_u·Q_uψ`, with `χ_u` supported in `Λ(u)`
  (`bsOneBody_eq_of_lamBox_eq`).

All four are proved in the sibling modules of `Work.BoseKinLoc.Sector`; this file assembles
them.  (The hypothesis `0 < ℓ` is used by the windowed pieces: it is what makes the support
of `χ_u` lie in `Λ(u)`.)
-/

noncomputable section

open MeasureTheory
open scoped Real Topology BigOperators

namespace Work.BoseKinLoc.Sector

open Work.BoseKinLoc Work.BSKinetic

set_option autoImplicit false
set_option linter.unusedVariables false

theorem fsT_box_invariant {ℓ d s εT b : ℝ} (hℓ : 0 < ℓ) {u : ℝ³} {ψ ψ' : ℝ³ → ℝ}
    (h : ∀ z : ℝ³, z ∈ Work.BoseKinLoc.lamBox ℓ u → ψ z = ψ' z) :
    Work.BoseKinLoc.fsT ℓ d s εT b u ψ = Work.BoseKinLoc.fsT ℓ d s εT b u ψ' := by
  -- the mean-free state agrees on the box
  have hQ : ∀ z : ℝ³, z ∈ lamBox ℓ u → Qfree ℓ u ψ z = Qfree ℓ u ψ' z :=
    Qfree_eq_of_lamBox_eq hℓ u h
  have hneu : neuWord ℓ d εT u ψ = neuWord ℓ d εT u ψ' := by
    unfold neuWord
    rw [neuFrac_eq_of_lamBox_eq u hQ]
  have hgap : gapWord ℓ b u ψ = gapWord ℓ b u ψ' := by
    unfold gapWord
    rw [gapBare_eq_of_lamBox_eq hℓ u h]
  have hmom : momWord ℓ d εT b u ψ = momWord ℓ d εT b u ψ' := by
    unfold momWord
    rw [momForm_eq_of_lamBox_eq hℓ u h]
  have hmain : mainWord ℓ d s εT u ψ = mainWord ℓ d s εT u ψ' := by
    unfold mainWord
    rw [bsOneBody_eq_of_lamBox_eq (F := Submission.BoseGases.fsKinCoeff ((2 * (s * ℓ))⁻¹))
          hℓ u h,
        bsOneBody_eq_of_lamBox_eq (F := Submission.BoseGases.fsKinCoeff ((2 * (d * s * ℓ))⁻¹))
          hℓ u h]
  rw [fsT_eq_sum, fsT_eq_sum, hneu, hgap, hmom, hmain]

end Work.BoseKinLoc.Sector
