/-
# SeedExist — the `FSeed.RootParabolicInput` bundle

The lead's contract (`NOTES_LEAD_mandelbar_seed.md` §6.2) asks for *all* fields of
`Work.FSeed.RootParabolicInput` except `portrait`, which is the business of the sibling area
`SeedSimple2`.  This file packages the seed data, the Böttcher homeomorphism, the parameter-ray
limit condition `ray_limit`, the (hypothesised) local portrait, the wake field and the
critical-orbit field into that bundle.

`ray_limit` is *not* produced by the certified-seed route
(`NOTES_LEAD_mandelbar_noncusp.md` §0.5: route E yields `∃ c, Nonempty (RootParabolic c)` but no
`ray_limit`); it is therefore a hypothesis here, together with `portrait`.
-/
import Submission.Work.SeedExist.Assembly
import Submission.Work.FSeed.Inputs

-- Lean v4.35.0-rc3 / Mathlib 5e0c4e5 made `isDefEq` respect transparency when unifying instances; with it,
-- `ZMod.instField` and `ZMod.commRing` (and `Neg (ZMod p)` via `SubtractionMonoid`) no longer unify, which
-- breaks `ring`/`rw`/module-instance search on `ZMod p`. Restore the v4.34 behaviour for this file.
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false


open Classical Filter Function Set
open scoped Topology

noncomputable section

namespace Work.SeedExist

open LeanEval.ComplexAnalysis (Tantibar Mandelbar)

/-- **The `RootParabolicInput` bundle from the seed data and the two extra facts.** -/
theorem rootParabolicInput_of_facts (S : RootSeedData)
    (hdyn : Work.ParamRays.DynBottcherHomeo S.c)
    (hray : S.c ∈ closure (Work.ParamRays.paramRay Work.FSeed.α₁) ∧
      S.c ∉ Work.ParamRays.paramRay Work.FSeed.α₁)
    (hportrait : Work.FSeed.LocalRayPortrait S.c S.z₁)
    (hwake : ∀ k : ℕ, 1 ≤ k →
      (Tantibar S.c)^[k] 0 ∈
        Work.EL.wakeSide (φ := Work.ParamRays.dynPhiOf S.c)
          (Work.ParamRays.dynNakane hdyn) S.z₁ ((k - 1) % 5))
    (hcrit : Filter.Tendsto (fun n : ℕ => (Work.FSeed.F S.c)^[n] S.c) Filter.atTop
        (nhds S.z₁) ∧
      ∀ n : ℕ, (Work.FSeed.F S.c)^[n] S.c ≠ S.z₁) :
    Nonempty (Work.FSeed.RootParabolicInput S.c) :=
  ⟨{ dyn := hdyn
     z₁ := S.z₁
     ray_limit := hray
     odd_per := ⟨5, by norm_num, S.g_fix, S.exact_period, S.mult_one⟩
     ray₁ := S.lands_α₁
     portrait := hportrait
     simple := S.simple
     crit := hcrit
     wake := hwake }⟩

/-- The `∃ c` form. -/
theorem exists_rootParabolicInput_of_facts (S : RootSeedData)
    (hdyn : Work.ParamRays.DynBottcherHomeo S.c)
    (hray : S.c ∈ closure (Work.ParamRays.paramRay Work.FSeed.α₁) ∧
      S.c ∉ Work.ParamRays.paramRay Work.FSeed.α₁)
    (hportrait : Work.FSeed.LocalRayPortrait S.c S.z₁)
    (hwake : ∀ k : ℕ, 1 ≤ k →
      (Tantibar S.c)^[k] 0 ∈
        Work.EL.wakeSide (φ := Work.ParamRays.dynPhiOf S.c)
          (Work.ParamRays.dynNakane hdyn) S.z₁ ((k - 1) % 5))
    (hcrit : Filter.Tendsto (fun n : ℕ => (Work.FSeed.F S.c)^[n] S.c) Filter.atTop
        (nhds S.z₁) ∧
      ∀ n : ℕ, (Work.FSeed.F S.c)^[n] S.c ≠ S.z₁) :
    ∃ c : ℂ, Nonempty (Work.FSeed.RootParabolicInput c) :=
  ⟨S.c, rootParabolicInput_of_facts S hdyn hray hportrait hwake hcrit⟩

end Work.SeedExist

end
