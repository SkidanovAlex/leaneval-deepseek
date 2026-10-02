/-
Copyright: subproject `Submission/Work/PARIMPL2/` of `mandelbar_not_path_connected`.

# `Work.PARIMPL2.Lavaurs.RepNorm` — the repelling normalisation bundle (N2)

Design: `Submission/Work/NOTES_LEAD_mandelbar_implosion.md` §3.3 (N2).  The exit step of the
lock-step assembly needs, for a point `z` of the outgoing window `WoutG P R H`, a **level** `u` of
the flower's repelling coordinate with `Ψ u = z` and the quantitative identification

  `u = approxCoordRep (P.κ c₀) (w0 P z) + sr + O((1 + H)(1 + log R)/R)`,  `Re u < -R/2`,

`sr` being the repelling phase constant.  The flower's `cover` field only gives the *existence* of
a level, with no control, so the quantitative form is a genuine theorem about the flower.

**This definition is exactly the conclusion of the delivered sibling**
`Work.FlowerGlue2.rep_norm_transfer` (see also that area's
`NOTES_FALSE_mandelbar_implosion_N2.md` §2):

* the honest error is `Θ(log R / R)`, **not** `O(1/R)` — the form `K (1+H)/R` of the design note
  is false for `H` fixed and `R → ∞` (the preimage `v = w - (1-a)Λ w + e` misses by
  `O((1+log‖w‖)/‖w‖)`);
* the regime is `R ≥ 8 (H+1)` and the level satisfies the explicit far-left bound `Re u < -R/2`;
* the *surjectivity* half needs `Re(1 - a) > 0`.

In the regime of `L4` (`H = O(log R)`) the error `K(1+H)(1+log R)/R` is still `o(1)`, which is all
the transit consumes.

The hypothesis `hVinv` of `repNorm_of_transfer` (the quantitative inverse of the germ conjugacy
`V`) is supplied by FlowerGlue2; per `NOTES_LEAD_mandelbar_gaps3.md` §1 the supplier is the
sign-free Stolz-sector version `Work.FlowerGlue2.exists_rep_inverse_stolz`, *not*
`exists_rep_inverse_sector_fatou2` (which assumed the unproved `Re κ₀ > 0`).  Nothing here depends
on the sign of `Re κ₀`.  `RepNorm` is the *named sibling hypothesis* of `lockstep_complex`; it is
instanced by `Work.FlowerGlue2.rep_norm_transfer` for the flower whose `Ψ` is in transfer form
(`∀ w, fl.Ψ w = d.z₁ + P.s c₀ * (-1 / V (w + sh))`, the FG-c route).
-/
import Submission.Work.PARIMPL2.Lavaurs.Defs
import Submission.Work.PARIMPL2.Lavaurs.Windows
import Submission.Work.FlowerGlue2.Defs
import Submission.Work.FlowerGlue2.rep_norm_transfer

-- Lean v4.35.0-rc3 / Mathlib 5e0c4e5 made `isDefEq` respect transparency when unifying instances; with it,
-- `ZMod.instField` and `ZMod.commRing` (and `Neg (ZMod p)` via `SubtractionMonoid`) no longer unify, which
-- breaks `ring`/`rw`/module-instance search on `ZMod p`. Restore the v4.34 behaviour for this file.
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false


set_option autoImplicit false
set_option linter.unusedVariables false
set_option maxHeartbeats 1000000

open Classical Filter Set Metric
open scoped Topology

noncomputable section

namespace Work.PARIMPL2.Lavaurs

open Work.PARIMPL (ParNormal)

variable {c₀ : ℂ} {d : Work.EL.RootParabolic c₀}

/-- **N2 (repelling normalisation)**, in the *surjective* form the exit step needs, with the
constants and side conditions of the delivered `Work.FlowerGlue2.rep_norm_transfer`. -/
def RepNorm (P : ParNormal d) (Ψ : ℂ → ℂ) : Prop :=
  ∃ sr : ℂ, ∃ N K : ℝ, 0 < N ∧ 0 ≤ K ∧
    ∀ R ≥ N, ∀ H : ℝ, R ≥ 8 * (H + 1) → ∀ z ∈ Work.PARIMPL2.WoutG P R H,
      ∃ u : ℂ, u.re < -(R / 2) ∧ Ψ u = z ∧
        ‖u - (Work.PARIMPL2.approxCoordRep (P.κ c₀) (Work.PARIMPL2.w0 P z) + sr)‖
          ≤ K * (1 + H) * (1 + Real.log R) / R

/-- **The instantiation of `RepNorm` from FlowerGlue2.**  This is the delivered sibling
`Work.FlowerGlue2.rep_norm_transfer`, restated in this area's vocabulary (`Work.PARIMPL2.w0`,
`Work.PARIMPL2.WoutG` are literally the same functions as `Work.FlowerGlue2.w0`,
`Work.FlowerGlue2.WoutG`).  It applies to the flower whose repelling coordinate is in *transfer
form* `Ψ w = z₁ + s c₀·(-1 / V (w + sh))` — the FG-c preferred route of the design.

Note this is *not* an unconditional statement about an arbitrary `ParabolicFlowerFix`; the
transfer form of `fl.Ψ` is a genuine hypothesis (it selects the flower). -/
theorem repNorm_of_transfer {P : ParNormal d}
    (fl : Work.FatouCoordFix.ParabolicFlowerFix (Work.PARIMPL.Ft c₀) (Work.PARIMPL.gtc c₀) d.z₁)
    (hτ : P.h c₀ 0 = 1) (sh : ℂ) {V : ℂ → ℂ} {R₀ K₀ : ℝ} (hR₀ : 0 < R₀) (hK₀ : 0 < K₀)
    (hVinv : ∀ w : ℂ, w.re < -R₀ → ∃ v : ℂ, v.re < -R₀ ∧ V v = w ∧
      ‖v - (w - (1 - P.h1 c₀) * Work.FatouCoord.Petal.Lambda w)‖
        ≤ K₀ * (1 + Real.log ‖w‖) / ‖w‖)
    (hΨ : ∀ w : ℂ, fl.Ψ w = d.z₁ + P.s c₀ * (-1 / V (w + sh))) :
    RepNorm P fl.Ψ := by
  obtain ⟨sr, N, K, hN, hK, h⟩ :=
    Work.FlowerGlue2.rep_norm_transfer P hτ fl sh hR₀ hK₀ hVinv hΨ
  refine ⟨sr, N, K, hN, hK, fun R hR H hRH z hz => ?_⟩
  exact h R hR H hRH z hz

end Work.PARIMPL2.Lavaurs

end
