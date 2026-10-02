/-
Copyright (c) 2026. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: FlowerGlue team
-/
import Mathlib
import Submission.Work.FlowerGlue.FatouUnique
import Submission.Work.FlowerGlue.RefCoord
import Submission.Work.FlowerGlue.exists_refCoord
import Submission.Work.FlowerGlue.ecalle_eq_ref_add_const

-- Lean v4.35.0-rc3 / Mathlib 5e0c4e5 made `isDefEq` respect transparency when unifying instances; with it,
-- `ZMod.instField` and `ZMod.commRing` (and `Neg (ZMod p)` via `SubtractionMonoid`) no longer unify, which
-- breaks `ring`/`rw`/module-instance search on `ZMod p`. Restore the v4.34 behaviour for this file.
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false


/-!
# `Work.FlowerGlue.FatouUniqueProof` — `Work.FQC.FatouUnique` is a theorem

This assembles the lead's design (`Submission/Work/NOTES_LEAD_mandelbar_gaps2.md` §1.1–§1.2):

* `Work.FlowerGlue.cyl_rigid` — an injective entire `T` with `T (ζ+1) = T ζ + 1` is a
  translation;
* `Work.FlowerGlue.exists_refCoord` — a reference coordinate `R` with `ℤ`-**saturating** image;
* `Work.FlowerGlue.ecalle_eq_ref_add_const` — every `EcalleData` coordinate equals `R.φ + n + s`
  along the orbit;
* hence two `EcalleData` coordinates of the same germ differ by the constant `s - s'` on the
  intersection of their petals, and `Work.FlowerGlue.FatouUnique_of_const` gives

  **`Work.FlowerGlue.fatouUnique : Work.FQC.FatouUnique`**.

This is the *proof* of the statement whose failure modes are analysed in
`Submission/Work/FlowerGlue/NOTES_FALSE_FatouUnique.md`: the fields of `EcalleData` do pin the
Écalle height, because the injectivity field `φa_inj` forces every perturbation of the coordinate
that preserves the fields to be a translation (`cyl_rigid`).  §4 of that note is therefore retired.
-/

open scoped Topology ComplexConjugate
open Filter Set Function
open Classical

set_option linter.unusedVariables false

namespace Work.FlowerGlue

open LeanEval.ComplexAnalysis (Tantibar Mandelbar)
open Work.EL (RootParabolic F)
open Work.FQC (EcalleData FatouUnique critHeightAt)

noncomputable section

variable {c : ℂ} {d : RootParabolic c}

/-- **`Work.FQC.FatouUnique` holds**: two Écalle data of the same germ have the same critical
Écalle height.  The proof pushes a point of the intersection of the two petals into the reference
petal along the orbit (`RefCoord.enters`), compares both coordinates there with the reference
coordinate (`ecalle_eq_ref_add_const`) and uses that both are Fatou coordinates (the Abel
equation, iterated). -/
theorem fatouUnique : FatouUnique := by
  refine FatouUnique_of_const ?_
  intro c d E E'
  obtain ⟨R⟩ := exists_refCoord d
  obtain ⟨s, hs⟩ := ecalle_eq_ref_add_const R E
  obtain ⟨s', hs'⟩ := ecalle_eq_ref_add_const R E'
  refine ⟨s - s', ?_⟩
  intro z hz
  obtain ⟨hzE, hzE'⟩ := hz
  -- the orbit of `z` converges to `z₁` and never hits it (it stays in the petal)
  have hconv : Tendsto (fun n : ℕ => (F c)^[n] z) atTop (nhds d.z₁) := E.tendsto_Pa z hzE
  have hne : ∀ n : ℕ, (F c)^[n] z ≠ d.z₁ := by
    intro n hn
    exact E.z₁_not_mem_Pa
      (hn ▸ Work.FatouCoord.mapsTo_iterate_of_mapsTo E.mapsTo_Pa n hzE)
  -- the orbit enters the reference petal
  obtain ⟨n₀, hn₀⟩ := R.enters z hconv hne
  have hnE : (F c)^[n₀] z ∈ E.Pa :=
    Work.FatouCoord.mapsTo_iterate_of_mapsTo E.mapsTo_Pa n₀ hzE
  have hnE' : (F c)^[n₀] z ∈ E'.Pa :=
    Work.FatouCoord.mapsTo_iterate_of_mapsTo E'.mapsTo_Pa n₀ hzE'
  -- both coordinates at the reference point, and the Abel equation backwards to `z`
  have h1 : E.φa ((F c)^[n₀] z) = R.φ ((F c)^[n₀] z) + s := by
    simpa using hs _ hn₀ 0 (by simpa using hnE)
  have h2 : E'.φa ((F c)^[n₀] z) = R.φ ((F c)^[n₀] z) + s' := by
    simpa using hs' _ hn₀ 0 (by simpa using hnE')
  have h3 := φa_shift_iterate E hzE n₀
  have h4 := φa_shift_iterate E' hzE' n₀
  have hz1 : E.φa z = E.φa ((F c)^[n₀] z) - (n₀ : ℂ) := by rw [h3]; ring
  have hz2 : E'.φa z = E'.φa ((F c)^[n₀] z) - (n₀ : ℂ) := by rw [h4]; ring
  rw [hz1, hz2, h1, h2]
  ring

end

end Work.FlowerGlue
