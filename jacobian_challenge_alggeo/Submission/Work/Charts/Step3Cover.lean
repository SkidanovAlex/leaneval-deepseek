/-
Copyright (c) 2026. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.

# Area CH — route B: the `Ω_E` cover `Sym^g C`, and COV′

This file assembles route B of `Submission/Work/NOTES_LEAD_jacobian_charts3.md` §4.

* `iSup_omega_eq_top` — the opens `Ω_E`, for `E` running over the points of `Sym^g C` defined
  over a *finite* extension of `K` contained in `SeparableClosure K`, cover `Sym^g C`: a
  hypothetical point of the complement is closed (quasi-compactness of `Sym^g C` + `T0`), hence
  lies in some `Ω_E` by `exists_centre_of_isClosed`.
* `exists_orbit_cover` — the hypothesis `hcover` of `galCharts_of_orbit_cover`, over the normal
  closure `k'` of the compositum of the finitely many fields of definition of a finite subcover,
  using `rep_of_rochData`, the ORBIT and POINT properties of `W′` (`Wp`).
This file contains only `iSup_omega_eq_top`; the assembly `exists_orbit_cover` and COV′
(`exists_galCharts`, `exists_galCharts_of_inputs`, the main theorems of route B) are in
`Submission.Work.Charts.exists_orbit_cover` and `Submission.Work.Charts.Step3Main`.
-/
import Submission.Work.Charts.Step3Defs
import Submission.Work.Charts.exists_centre_of_isClosed
import Submission.Work.Charts.step3Data_of_inputs
import Submission.Work.Charts.rep_of_rochData
import Submission.Work.Charts.galCharts_of_orbit_cover

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false

-- Lean v4.35.0-rc3 / Mathlib 5e0c4e5 made `isDefEq` respect transparency when unifying instances; with it,
-- `ZMod.instField` and `ZMod.commRing` (and `Neg (ZMod p)` via `SubtractionMonoid`) no longer unify, which
-- breaks `ring`/`rw`/module-instance search on `ZMod p`. Restore the v4.34 behaviour for this file.


set_option autoImplicit false
set_option maxHeartbeats 1000000
set_option linter.style.haveILetI false

universe u

open CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory AlgebraicGeometry
open scoped Classical AlgebraicGeometry MonoidalCategory
open scoped Work.GCBasics

namespace Work.Charts

open Work.CurveBasics
open Work.GCBasics

noncomputable section

variable {K : Type u} [Field K] {C : Curve K} [Work.SpecLin.DivBase C] (R : RochData C)
  (I : Step3Data R)

/-- **The opens `Ω_E` cover `Sym^g C`**: for `E` running over the points of `Sym^g C` rational
over a finite extension of `K` inside `SeparableClosure K`. -/
theorem iSup_omega_eq_top :
    (⨆ (E : Σ k₁ : {k₁ : IntermediateField K (SeparableClosure K) // FiniteDimensional K ↥k₁},
        FPt ((I.symGeom R.g).S) ↥k₁.1),
      (haveI := E.1.2; omegaOpen R I.symGeom I.resid I.geo E.2 I.a I.d)) = ⊤ := by
  by_contra hne
  set Ω : (Σ k₁ : {k₁ : IntermediateField K (SeparableClosure K) // FiniteDimensional K ↥k₁},
      FPt ((I.symGeom R.g).S) ↥k₁.1) → ((I.symGeom R.g).S).left.Opens :=
    fun E => (haveI := E.1.2; omegaOpen R I.symGeom I.resid I.geo E.2 I.a I.d) with hΩ
  have hproper : ((⨆ E, Ω E : ((I.symGeom R.g).S).left.Opens) :
      Set ((I.symGeom R.g).S).left) ≠ Set.univ := by
    intro h
    refine hne (le_antisymm le_top fun y _ => ?_)
    have h2 : y ∈ (Set.univ : Set ((I.symGeom R.g).S).left) := Set.mem_univ y
    rw [← h] at h2
    exact h2
  haveI : QuasiCompact ((I.symGeom R.g).S).hom := I.geo.quasiCompact_g
  haveI : CompactSpace ((I.symGeom R.g).S).left :=
    QuasiCompact.compactSpace_of_compactSpace ((I.symGeom R.g).S).hom
  haveI : T0Space ((I.symGeom R.g).S).left := inferInstance
  have hcl : IsClosed (((⨆ E, Ω E : ((I.symGeom R.g).S).left.Opens) :
      Set ((I.symGeom R.g).S).left)ᶜ) :=
    ((⨆ E, Ω E : ((I.symGeom R.g).S).left.Opens)).2.isClosed_compl
  obtain ⟨x, hx, hxcl⟩ := hcl.exists_closed_singleton (by rw [Set.nonempty_compl]; exact hproper)
  haveI : LocallyOfFiniteType ((I.symGeom R.g).S).hom := I.geo.locallyOfFiniteType_g
  haveI := finiteDimensional_resField_of_isClosed (X := (I.symGeom R.g).S) x hxcl
  obtain ⟨k₁, hfin, E, hxE⟩ := exists_centre_of_isClosed R I x hxcl
  exact hx (TopologicalSpace.Opens.mem_iSup.mpr ⟨⟨⟨k₁, hfin⟩, E⟩, hxE⟩)

end

end Work.Charts
