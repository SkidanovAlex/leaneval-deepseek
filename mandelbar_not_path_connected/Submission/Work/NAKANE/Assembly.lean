/-
# Nakane's homeomorphism theorem, from the local-homeomorphism input alone

This file assembles the results of the area into the strongest available form:

* `Work.NAKANE.phi_far_injective` : `Φ` is injective on an outer annulus `{R ≤ ‖c‖}` — **unconditional**
  (from the diagonal Lipschitz estimate `Work.NAKANE.FarInj.exists_diagonal_lipschitz` for the
  Böttcher series via `Work.NAKANE.far_injOn_of_lipschitz`);
* `Work.NAKANE.injOn_of_localHomeo` : **(R2) from (R1) alone** — `Φ` is injective on the whole
  exterior of the mandelbar (via `Work.NAKANE.InjOfFar.injOn_of_localHomeo_of_farInj`, which uses
  the properness of `phiExt` and the local constancy of the fibre cardinality over the preconnected
  exterior disc);
* `Work.NAKANE.nakaneHomeo_of_localHomeo` : **`Work.ParamRays.NakaneHomeo` from (R1) alone**;
* `Work.NAKANE.phi_bijOn_of_localHomeo` : `Φ` is a bijection of `Mbᶜ` onto `extDisc`.

Consequently, the single classical input of the whole area is

  `Work.NAKANE.PhiLocalHomeo` (R1), i.e. `IsLocalHomeomorphOn Φ Mbᶜ`

— Nakane's 1993 regularity of the parameter Böttcher map (`c ↦ Φ c` real-analytic with nonvanishing
Jacobian).  The uniform asymptotic `Work.ParamRays.UniformBottcherAsymptotic` was already
discharged unconditionally (`Work.NAKANE.uniformBottcherAsymptotic`), so

  `Work.Final.nakane_of_homeo_asymptotic (nakaneHomeo_of_localHomeo hloc) uniformBottcherAsymptotic`

produces the endgame's `Work.ParamRays.NakaneInput` from `hloc` alone.
-/
import Submission.Work.NAKANE.FarInjective
import Submission.Work.NAKANE.NakaneHomeo
import Submission.Work.NAKANE.FarInj.exists_diagonal_lipschitz
import Submission.Work.NAKANE.InjOfFar.injOn_of_localHomeo_of_farInj

-- Lean v4.35.0-rc3 / Mathlib 5e0c4e5 made `isDefEq` respect transparency when unifying instances; with it,
-- `ZMod.instField` and `ZMod.commRing` (and `Neg (ZMod p)` via `SubtractionMonoid`) no longer unify, which
-- breaks `ring`/`rw`/module-instance search on `ZMod p`. Restore the v4.34 behaviour for this file.
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false


open Classical Filter Set
open scoped Topology ComplexConjugate

set_option autoImplicit false
set_option maxHeartbeats 1000000

noncomputable section

namespace Work.NAKANE

open LeanEval.ComplexAnalysis (Tantibar Mandelbar)

/-- **`Φ` is injective on an outer annulus**, unconditionally. -/
theorem phi_far_injective : ∃ R : ℝ, Set.InjOn Work.ParamRays.Phi {c : ℂ | R ≤ ‖c‖} := by
  obtain ⟨r, C, hr, hC, hlip⟩ := Work.NAKANE.FarInj.exists_diagonal_lipschitz
  exact far_injOn_of_lipschitz hr hC hlip

/-- **(R2) from (R1) alone: `Φ` is injective on the exterior of the mandelbar.** -/
theorem injOn_of_localHomeo (hloc : PhiLocalHomeo) : PhiInjOn := by
  obtain ⟨R, hR⟩ := phi_far_injective
  exact Work.NAKANE.InjOfFar.injOn_of_localHomeo_of_farInj hloc hR

/-- **Nakane's homeomorphism theorem from the local-homeomorphism input alone.** -/
theorem nakaneHomeo_of_localHomeo (hloc : PhiLocalHomeo) : Work.ParamRays.NakaneHomeo :=
  nakaneHomeo_of_localHomeo_of_injOn hloc (injOn_of_localHomeo hloc)

/-- **`Φ` is a bijection of `Mbᶜ` onto the exterior disc**, from (R1) alone. -/
theorem phi_bijOn_of_localHomeo (hloc : PhiLocalHomeo) :
    Set.BijOn Work.ParamRays.Phi Mbᶜ extDisc := by
  refine ⟨fun c hc => one_lt_norm_Phi hc, injOn_of_localHomeo hloc, fun w hw => ?_⟩
  exact mem_image_Phi_of_localHomeo_of_one_lt hloc hw

end Work.NAKANE
