/-
# SeedExist — from the cited clause `NonCuspRootLimit` to the seed data

`Work.SeedExist.NonCuspRootLimit` (the single cited clause of
`NOTES_LEAD_mandelbar_seed.md` §3.1) supplies a parameter `c` which is a limit point of the
parameter ray `R(α₁)` and at which `R_c(α₁)` and `R_c(α₂)` co-land at a simple parabolic point
`z₁`.  This file derives from it

* `c ∈ Mandelbar` — the mandelbar is closed and a limit point of a parameter ray cannot lie off
  it (`mem_mandelbar_of_mem_closure_paramRay`, proved in the sibling file);
* `(T_c)^[5] z₁ = z₁` — the ray-image lemma applied five times, since `T^5 α₁ = α₂`.

The remaining fields of the seed (`multiplier2 c 5 z₁ = 1` and the exactness of the period) are
*not* derived here: they are the E3/E5 lemmas of `NOTES_LEAD_mandelbar_seed.md` §3.2, which the
lead's amendment `NOTES_LEAD_mandelbar_noncusp.md` §4.3 replaces by the fields of the certified
seed `Work.SeedCert.ExplicitRootSeed`.
-/
import Submission.Work.SeedExist.Setup

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

/-- `Work.EL.T` is `Work.Landing.angDouble`. -/
theorem T_eq_angDouble (θ : ℝ) : Work.EL.T θ = Work.Landing.angDouble θ := rfl

/-- **The period condition from the co-landing of the two root rays**: if `R_c(α₁)` and `R_c(α₂)`
co-land at `z₁`, then `T_c^[5] z₁ = z₁`, because `T^5 α₁ = α₂` and the landing point of a ray is
unique. -/
theorem five_fix_of_landsAt {c z₁ : ℂ}
    (h1 : Work.Landing.landsAt c Work.EL.alpha1 z₁)
    (h2 : Work.Landing.landsAt c Work.EL.alpha2 z₁) :
    (Tantibar c)^[5] z₁ = z₁ := by
  have h := Work.Landing.landsAt_iterate h1 5
  rw [show (Work.Landing.angDouble^[5]) Work.EL.alpha1 = Work.EL.alpha2 from
    (T_five_α₁ : (Work.EL.T^[5]) Work.EL.alpha1 = Work.EL.alpha2)] at h
  exact Work.Landing.landsAt_unique h h2

/-- The two root rays land at the same point of the seed. -/
theorem coLands_of_nonCusp {c z₁ : ℂ}
    (h1 : Work.Landing.landsAt c Work.EL.alpha1 z₁)
    (h2 : Work.Landing.landsAt c Work.EL.alpha2 z₁) :
    Work.Landing.coLands c Work.EL.alpha1 Work.EL.alpha2 :=
  ⟨z₁, h1, h2⟩

end Work.SeedExist

end
