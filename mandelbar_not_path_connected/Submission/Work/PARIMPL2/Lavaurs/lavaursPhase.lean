/-
Copyright: subproject `Submission/Work/PARIMPL2/` of `mandelbar_not_path_connected`.

# `Work.PARIMPL2.Lavaurs.lavaursPhase` — from the complex lock-step to `LavaursPhase`

Design: `Submission/Work/NOTES_LEAD_mandelbar_implosion.md` §3.6 (L4).  The lock-step assembly
`Work.PARIMPL2.Lavaurs.lockstep_complex` produces a **complex** phase constant `θc` (the Lavaurs
constant `s_r - s_a`, whose imaginary part is not yet known to vanish).  The antiholomorphic
symmetry of the flower (`Work.PARIMPL2.Lavaurs.phase_im_zero`) forces `Im θc = 0`, and then the
definition `Work.PARIMPL2.LavaursPhase` — whose phase is **real** by construction
(`Work.PARIMPL2.transPh`) — follows.  This file performs that last step; it is conditional on the
`LockstepAll` conclusion of `lockstep_complex`, so that it carries no residue of its own.
-/
import Submission.Work.PARIMPL2.Lavaurs.Defs
import Submission.Work.PARIMPL2.Lavaurs.phase_im_zero

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

open Work.PARIMPL (ParNormal entryPt Ft gtc)

variable {c₀ : ℂ} {d : Work.EL.RootParabolic c₀}

/-- **The single analytic export, from the complex lock-step.**  Given the `LockstepAll` conclusion
of `lockstep_complex` with the complex phase `θc`, the imaginary part of `θc` vanishes
(`phase_im_zero`), so `θc = θc.re` and the lock-step holds for the *real* phase
`transPh P x₀ θc.re`: this is `Work.PARIMPL2.LavaursPhase`. -/
theorem lavaursPhase_of_lockstep (P : ParNormal d)
    (fl : Work.FatouCoordFix.ParabolicFlowerFix (Ft c₀) (gtc c₀) d.z₁) (nIn : ℕ)
    (hL : ∃ θc : ℂ, LockstepAll c₀ P.Nm
      (fun c => (((fl.φa (entryPt P nIn c₀)).re - Real.pi / P.lam c : ℝ) : ℂ) + θc)
      nIn (fun c z => Ft c z) fl.Pa fl.φa fl.Ψ
      ((fl.φa (entryPt P nIn c₀)).re - (nIn : ℝ))) :
    LavaursPhase d P fl.Pa fl.φa fl.Ψ nIn := by
  obtain ⟨θc, hθc⟩ := hL
  have him : θc.im = 0 := phase_im_zero d P fl hθc rfl
  refine ⟨θc.re, ?_⟩
  have htrans : (fun c => (((fl.φa (entryPt P nIn c₀)).re - Real.pi / P.lam c : ℝ) : ℂ) + θc)
      = transPh P (fl.φa (entryPt P nIn c₀)).re θc.re := by
    funext c
    rw [transPh_apply]
    have hre : θc = ((θc.re : ℝ) : ℂ) := by
      apply Complex.ext <;> simp [him]
    rw [hre]
    simp only [Complex.ofReal_re]
    push_cast
    ring
  rw [htrans] at hθc
  exact hθc

end Work.PARIMPL2.Lavaurs

end
