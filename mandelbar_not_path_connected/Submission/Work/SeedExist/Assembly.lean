/-
# SeedExist — the assembly of `Work.EL.RootParabolic`

From a `RootSeedData`, the Böttcher data, the wake field and the critical-orbit data, this file
assembles the structure `Work.EL.RootParabolic` — the input bundle of the EL areas.  The fields
`per_half`, `ne_per`, `mult`, `simple`, `rays` are the seed data itself; only `crit` and `wake`
are supplied by the W-lemmas of the area.
-/
import Submission.Work.SeedExist.Flower

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

/-- **The assembly**: the root-parabolic bundle from the seed data, the Böttcher data, the wake
field and the critical-orbit field. -/
theorem rootParabolicEL_of_facts (S : RootSeedData)
    (hN : Work.EL.DynB S.c (Work.ParamRays.dynPhiOf S.c))
    (hbott : Work.ParamRays.IsDynBottcher S.c (Work.ParamRays.dynPhiOf S.c))
    (hwake : ∀ k : ℕ, 1 ≤ k →
      (Tantibar S.c)^[k] 0 ∈ wakeSide hN S.z₁ ((k - 1) % 5))
    (hcrit : Filter.Tendsto (fun n : ℕ => (Work.FSeed.F S.c)^[n] S.c) Filter.atTop
        (nhds S.z₁) ∧
      ∀ n : ℕ, (Work.FSeed.F S.c)^[n] S.c ≠ S.z₁) :
    Nonempty (Work.EL.RootParabolic S.c) :=
  ⟨{ φ := Work.ParamRays.dynPhiOf S.c
     bottcher := hbott
     hN := hN
     z₁ := S.z₁
     per_half := S.g_fix
     ne_per := fun j hj => S.exact_period j (Finset.mem_Ioo.mp hj).1 (Finset.mem_Ioo.mp hj).2
     mult := S.mult_one
     simple := S.simple
     rays := ⟨S.lands_α₁, S.lands_α₂⟩
     crit := hcrit
     wake := hwake }⟩

/-- The assembled bundle, in the form `∃ c, Nonempty (RootParabolic c)`. -/
theorem exists_rootParabolic_of_facts (S : RootSeedData)
    (hN : Work.EL.DynB S.c (Work.ParamRays.dynPhiOf S.c))
    (hbott : Work.ParamRays.IsDynBottcher S.c (Work.ParamRays.dynPhiOf S.c))
    (hwake : ∀ k : ℕ, 1 ≤ k →
      (Tantibar S.c)^[k] 0 ∈ wakeSide hN S.z₁ ((k - 1) % 5))
    (hcrit : Filter.Tendsto (fun n : ℕ => (Work.FSeed.F S.c)^[n] S.c) Filter.atTop
        (nhds S.z₁) ∧
      ∀ n : ℕ, (Work.FSeed.F S.c)^[n] S.c ≠ S.z₁) :
    ∃ c : ℂ, Nonempty (Work.EL.RootParabolic c) :=
  ⟨S.c, rootParabolicEL_of_facts S hN hbott hwake hcrit⟩

end Work.SeedExist

end
