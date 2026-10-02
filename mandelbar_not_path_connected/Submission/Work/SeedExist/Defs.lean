/-
# SeedExist — the seed existence bundle

This area builds `Work.EL.RootParabolic c` (and, modulo `portrait`, the bundle
`Work.FSeed.RootParabolicInput c`) from **one** cited clause.  It is the area
`NOTES_LEAD_mandelbar_seed.md` §3 describes, with the amendment of
`NOTES_LEAD_mandelbar_noncusp.md` §2.1/§2.6: the cited clause is now
`Work.SeedExist.ExplicitRootSeed`, a `Prop` with no cited content (it is a theorem about an
explicit certified parameter, built in the sibling area `SeedCert`).

## Contents

* `Work.SeedExist.NonCuspRootLimit` — the original single cited clause (seed §0.5, §3.1), kept
  for the record and for the `gm`/`hatt` route (E0–E5 of seed §3.2);
* `Work.SeedExist.ExplicitRootSeed` — the replacement clause of the amendment;
* `Work.SeedExist.FatouCritInBasin c z Pg` — Fatou's theorem in the strong form exported by the
  `FatouParabolic` area: the critical point lies in the immediate basin of the parabolic cycle.
-/
import Submission.Work.ELTop.Defs
import Submission.Work.FSeed.Defs
import Submission.Work.FSeed.Inputs
import Submission.Work.ParamRays.DynBottcher
import Submission.Work.Top.Jordan

-- Lean v4.35.0-rc3 / Mathlib 5e0c4e5 made `isDefEq` respect transparency when unifying instances; with it,
-- `ZMod.instField` and `ZMod.commRing` (and `Neg (ZMod p)` via `SubtractionMonoid`) no longer unify, which
-- breaks `ring`/`rw`/module-instance search on `ZMod p`. Restore the v4.34 behaviour for this file.
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false


open Classical Filter Function
open scoped Topology

noncomputable section

namespace Work.SeedExist

open LeanEval.ComplexAnalysis (Tantibar Mandelbar)

/-! ## The two cited clauses -/

/-- **The single cited clause of the seed** (`NOTES_LEAD_mandelbar_seed.md` §0.5, §3.1): a
parameter `c` which is a limit point of the parameter ray `R(α₁)` but not on it, at which the
dynamical rays `R_c(α₁)`, `R_c(α₂)` co-land at a point `z₁` that is a **simple** parabolic point
of `F c = (T_c)^[10]`.

Provenance (seed §5): MNS arXiv:1404.5031 L. 5.6 together with L. 4.4(2) give the co-landing at
every limit point; IM arXiv:1406.3428 Thm 1.1 together with MNS L. 2.9 give a limit point which
is not a cusp, i.e. `iteratedDeriv 2 (F c) z₁ ≠ 0`. -/
def NonCuspRootLimit : Prop :=
  ∃ c z₁ : ℂ, c ∈ closure (Work.ParamRays.paramRay Work.FSeed.α₁) ∧
    c ∉ Work.ParamRays.paramRay Work.FSeed.α₁ ∧
    Work.Landing.landsAt c Work.FSeed.α₁ z₁ ∧
    Work.Landing.landsAt c Work.FSeed.α₂ z₁ ∧
    iteratedDeriv 2 (Work.FSeed.F c) z₁ ≠ 0

/-- **The replacement clause of the amendment** (`NOTES_LEAD_mandelbar_noncusp.md` §2.1): an
explicit parameter `c ∈ Mandelbar` at which `F c = (T_c)^[10]` has a **simple** parabolic fixed
point `z₁` of exact `T_c`-period `5`, and both root rays `α₁`, `α₂` land at `z₁`.

This is `NonCuspRootLimit` minus the parameter-ray limit condition, plus the three facts that the
`gm`/`hatt` route used to *derive* (`(T_c)^[5] z₁ = z₁`, exact period `5`, multiplier `1`).  It is
a theorem (the certified seed of the area `SeedCert`), not a cited clause; until `SeedCert` lands
it is carried as a hypothesis. -/
def ExplicitRootSeed : Prop :=
  ∃ c z₁ : ℂ, c ∈ Mandelbar ∧ (Tantibar c)^[5] z₁ = z₁ ∧
    (∀ j : ℕ, 0 < j → j < 5 → (Tantibar c)^[j] z₁ ≠ z₁) ∧
    Work.Landing.multiplier2 c 5 z₁ = 1 ∧
    iteratedDeriv 2 (Work.FSeed.F c) z₁ ≠ 0 ∧
    Work.Landing.landsAt c Work.FSeed.α₁ z₁ ∧
    Work.Landing.landsAt c Work.FSeed.α₂ z₁

/-! ## Fatou's theorem, strong form -/

/-- **Fatou's theorem, strong form, for the simple parabolic 5-cycle of `z` with petal `Pg`**
(the export requested from the `FatouParabolic` area, seed §3.1 and §6.4):

* (i) some `F c`-iterate of a point of `Pg` lies in the connected component of `0` in the interior
  of the filled Julia set — i.e. the critical point lies in the immediate basin of the cycle;
* (ii) some `F c`-iterate of the critical value `c` lies in some `T_c`-iterate of `Pg`.

This is the datum from which SeedExist derives (a) the critical orbit converges to `z₁`
(`crit`, W9) and (b) `c` and `0` lie in the interior of the filled Julia set (E10). -/
def FatouCritInBasin (c z : ℂ) (Pg : Set ℂ) : Prop :=
  (∃ i : ℕ, i < 5 ∧ ∃ x ∈ Pg,
      (Tantibar c)^[i] x ∈ connectedComponentIn (interior (Work.EL.K c)) 0) ∧
  (∃ N j : ℕ, j < 5 ∧ (Work.FSeed.F c)^[N] c ∈ (Tantibar c)^[j] '' Pg)

/-! ## Bridges between the several copies of the root angles -/

theorem fseed_alpha1_eq_el : Work.FSeed.α₁ = Work.EL.alpha1 := rfl

theorem fseed_alpha2_eq_el : Work.FSeed.α₂ = Work.EL.alpha2 := rfl

theorem fseed_F_eq_el_F (c : ℂ) : Work.FSeed.F c = Work.EL.F c := rfl

end Work.SeedExist
