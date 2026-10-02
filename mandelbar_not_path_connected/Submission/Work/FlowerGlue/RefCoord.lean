/-
Copyright (c) 2026. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: FlowerGlue team
-/
import Mathlib
import Submission.Work.FQC.Defs

-- Lean v4.35.0-rc3 / Mathlib 5e0c4e5 made `isDefEq` respect transparency when unifying instances; with it,
-- `ZMod.instField` and `ZMod.commRing` (and `Neg (ZMod p)` via `SubtractionMonoid`) no longer unify, which
-- breaks `ring`/`rw`/module-instance search on `ZMod p`. Restore the v4.34 behaviour for this file.
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false


/-!
# `Work.FlowerGlue.RefCoord` — a reference attracting coordinate whose image saturates the cylinder

This is the interface of the lead's design `Submission/Work/NOTES_LEAD_mandelbar_gaps2.md` §1.2 for
the proof that `Work.FQC.FatouUnique` is **true as stated** (the perturbation family of
`NOTES_FALSE_FatouUnique.md` §3 has to be injective on `φa '' Pa`, and that injectivity is what
forces it to be a translation).

`RefCoord d` is an attracting coordinate of the germ at `d.z₁` (the chart coordinate
`fatouCoordW f (1-a) ∘ chart` of the normalised germ, restricted to a half-plane petal) with the
crucial extra field `sat`: its image is **ℤ-saturating**, i.e. every point of the cylinder `ℂ/ℤ`
is reached by the image after a finite number of translations.  `sat` is what turns the
comparison map between two coordinates into an entire `1`-equivariant injection of `ℂ` — the
hypothesis of `Work.FlowerGlue.cyl_rigid`.

The structure is stated here (so that the delegated lemmas `exists_refCoord` and
`ecalle_eq_ref_add_const` can be stated against it); its instantiation is the lemma
`exists_refCoord` of the same name, and the transfer to an arbitrary `EcalleData` is
`ecalle_eq_ref_add_const`.
-/

open scoped Topology
open Filter Set Function
open Classical

namespace Work.FlowerGlue

open LeanEval.ComplexAnalysis (Tantibar Mandelbar)
open Work.EL (RootParabolic F)

noncomputable section

/-- A **reference attracting coordinate** whose image saturates the cylinder `ℂ/ℤ`. -/
structure RefCoord {c : ℂ} (d : RootParabolic c) where
  /-- the half-plane petal on which the coordinate is defined -/
  P : Set ℂ
  /-- the attracting Fatou coordinate -/
  φ : ℂ → ℂ
  isOpen : IsOpen P
  mapsTo : MapsTo (F c) P P
  z₁_not_mem : d.z₁ ∉ P
  tendsto : ∀ z ∈ P, Tendsto (fun n : ℕ => (F c)^[n] z) atTop (nhds d.z₁)
  /-- every orbit converging to `z₁` without hitting it enters the petal -/
  enters : ∀ z : ℂ, Tendsto (fun n : ℕ => (F c)^[n] z) atTop (nhds d.z₁) →
    (∀ n : ℕ, (F c)^[n] z ≠ d.z₁) → ∃ n : ℕ, (F c)^[n] z ∈ P
  diff : DifferentiableOn ℂ φ P
  inj : Set.InjOn φ P
  deriv_ne : ∀ z ∈ P, deriv φ z ≠ 0
  /-- the Abel equation -/
  shift : ∀ z ∈ P, φ (F c z) = φ z + 1
  /-- **ℤ-saturation of the cylinder**: every `ζ` reaches the image of `φ` after finitely many
  translations -/
  sat : ∀ ζ : ℂ, ∃ N : ℕ, ∀ n ≥ N, ζ + n ∈ φ '' P

end

end Work.FlowerGlue
