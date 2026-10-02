/-
# `Work.FQC.Petal` — the petal inputs of the deformation

`Work.FQC.PetalInput` collects what the deformation needs to know about the attracting petal of a
root-parabolic parameter, beyond the fields of `Work.FatouCoord.ParabolicFlower`; the fundamental
domain `Pg` of the dynamics is carried as data because the petal of the constructed flower is not
invariant under the half-return `g = (Tantibar c)^[5]` in general.
-/
import Mathlib
import Submission.Work.FQC.Defs

-- Lean v4.35.0-rc3 / Mathlib 5e0c4e5 made `isDefEq` respect transparency when unifying instances; with it,
-- `ZMod.instField` and `ZMod.commRing` (and `Neg (ZMod p)` via `SubtractionMonoid`) no longer unify, which
-- breaks `ring`/`rw`/module-instance search on `ZMod p`. Restore the v4.34 behaviour for this file.
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false


open scoped Topology ComplexConjugate
open MeasureTheory Filter Set Function
open Classical

set_option maxHeartbeats 4000000

noncomputable section

namespace Work.FQC

open LeanEval.ComplexAnalysis (Tantibar Mandelbar)
open Work.EL (RootParabolic F K)

/-- **The petal inputs.**  What the deformation needs to know about the attracting petal of a
root-parabolic parameter, beyond the fields of `ParabolicFlower`:

* `Pg` — a `g`-invariant sub-petal (`g = (Tantibar c)^[5]`), contained in the petal `fl.Pa` and open.
  The petal of the constructed flower is *not* `g`-invariant in general, so the fundamental domain
  of the dynamics is carried as data;
* the `T_c`-orbit of a point of `Pg` does not return to `Pg` in fewer than `5` steps;
* the Fatou coordinate, restricted to `Pg`, is measurable (`fl.φa` is a junk extension off `fl.Pa`,
  so only its indicator on `Pg` can be measurable);
* the Abel equation `φa (F z) = φa z + 1` on the petal (`F c = (Tantibar c)^[10]`), which holds for
  the constructed flower and is what lets the height be read off at the entry into `Pg`;
* every orbit converging to `z₁` without attaining it enters `Pg`. -/
structure PetalInput {c : ℂ} (d : RootParabolic c)
    (fl : Work.FatouCoord.ParabolicFlower (F c) ((Tantibar c)^[5]) d.z₁) where
  /-- the `g`-invariant fundamental domain -/
  Pg : Set ℂ
  /-- it lies inside the petal of the flower -/
  Pg_sub : Pg ⊆ fl.Pa
  /-- it is open -/
  Pg_open : IsOpen Pg
  /-- it is preconnected (this is the field that the *transported* Écalle data of the
  quasiconformal deformation needs: its petal is `theta '' Pg`) -/
  Pg_preconnected : IsPreconnected Pg
  /-- it is invariant under the half-return `g = T_c^[5]` -/
  mapsTo_g_Pg : ∀ z ∈ Pg, (Tantibar c)^[5] z ∈ Pg
  /-- no return to `Pg` in fewer than `5` steps -/
  no_early : ∀ z ∈ Pg, ∀ r : ℕ, 1 ≤ r → r < 5 → (Tantibar c)^[r] z ∉ Pg
  /-- the indicator of `Pg` times the Fatou coordinate is measurable -/
  indicator_measurable : Measurable (Pg.indicator fl.φa)
  /-- the Abel equation for the holomorphic return map `F c = (Tantibar c)^[10]` on the petal -/
  φa_shift : ∀ z ∈ fl.Pa, fl.φa ((F c) z) = fl.φa z + 1
  /-- every orbit converging to `z₁` without attaining it enters `Pg` -/
  enters_Pg : ∀ z : ℂ, Filter.Tendsto (fun n : ℕ => (F c)^[n] z) Filter.atTop (nhds d.z₁) →
    (∀ n : ℕ, (F c)^[n] z ≠ d.z₁) → ∃ n : ℕ, (F c)^[n] z ∈ Pg


end Work.FQC

end
