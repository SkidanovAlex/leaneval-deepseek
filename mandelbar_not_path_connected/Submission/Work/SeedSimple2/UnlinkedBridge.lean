/-
Copyright: subproject `Submission/Work/SeedSimple2/` of `mandelbar_not_path_connected`.

# SeedSimple2 — the unlinked lemma `U` discharged

`Unlinked/unlinked_of_coLands.lean` proves the unlinked lemma `U` of §4.2.  This file packages it
as the standing hypothesis `Work.SeedSimple2.unlinkedLemma` of the assembly, and restates the
assembly `fSeedInput_of_hypotheses` with `U` discharged.
-/
import Submission.Work.SeedSimple2.Main
import Submission.Work.SeedSimple2.Unlinked.unlinked_of_coLands

-- Lean v4.35.0-rc3 / Mathlib 5e0c4e5 made `isDefEq` respect transparency when unifying instances; with it,
-- `ZMod.instField` and `ZMod.commRing` (and `Neg (ZMod p)` via `SubtractionMonoid`) no longer unify, which
-- breaks `ring`/`rw`/module-instance search on `ZMod p`. Restore the v4.34 behaviour for this file.
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false


open Filter Set Function
open scoped Topology

noncomputable section

namespace Work.SeedSimple2

open LeanEval.ComplexAnalysis (Tantibar Mandelbar)

/-- The unlinked lemma `U` of §4.2, discharged. -/
theorem unlinkedLemma_proved (hJ : Work.Top.JordanForm) : unlinkedLemma hJ :=
  fun {c φ} hN {a b a' b'} {w w'} hw ha hb ha' hb' l1 l2 l3 l4 hd =>
    Work.SeedSimple2.Unlinked.unlinked_of_coLands hN hJ hw ha hb ha' hb' l1 l2 l3 l4 hd

/-- **The assembly, with `U` discharged.**  The remaining inputs are the two geometric
statements `rotationZero` (`RN0`) and `gfixedAvoid` (`GF`) of §4.2, the Jordan form, and the
SeedExist bundle produced from the cited clause. -/
theorem fSeedInput_of_nonCusp' (hJ : Work.Top.JordanForm)
    (hRN0 : rotationZero) (hGF : gfixedAvoid)
    (H : ∀ c z₁ : ℂ, c ∈ closure (Work.ParamRays.paramRay Work.EL.alpha1) →
      c ∉ Work.ParamRays.paramRay Work.EL.alpha1 →
      Work.Landing.landsAt c Work.EL.alpha1 z₁ → Work.Landing.landsAt c Work.EL.alpha2 z₁ →
      iteratedDeriv 2 (Work.FSeed.F c) z₁ ≠ 0 → ∃ S : SeedData c, S.input.z₁ = z₁)
    (h : NonCuspRootLimit) : Work.FSeed.FSeedInput :=
  fSeedInput_of_hypotheses hJ (unlinkedLemma_proved hJ) hRN0 hGF H h

end Work.SeedSimple2

end
