import Mathlib
import Submission.Work.Cusp.Basic
import Submission.Work.Cusp.nrm_bnd
import Submission.Work.Cusp.smul_bnd
import Submission.Work.Cusp.uPerim_mem
import Submission.Work.Cusp.nrm_u_injOn

-- Lean v4.35.0-rc3 / Mathlib 5e0c4e5 made `isDefEq` respect transparency when unifying instances; with it,
-- `ZMod.instField` and `ZMod.commRing` (and `Neg (ZMod p)` via `SubtractionMonoid`) no longer unify, which
-- breaks `ring`/`rw`/module-instance search on `ZMod p`. Restore the v4.34 behaviour for this file.
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false


namespace Work.Cusp

/-- **Every point of `E2` is recovered from its layer parameter and its perimeter parameter:**
`p = ‖p‖∞ • bndOfU (u p)`.

For `p ≠ 0` the radial projection `bnd p = (nrm p)⁻¹ • p` has sup norm `1` (`nrm_bnd`), i.e. it
lies on the boundary `∂Sq`; there `bndOfU` inverts `uPerim` (`nrmu_bndOfU_uPerim`).  Combining with
`p = nrm p • bnd p` (`smul_bnd`) gives the claim.  At `p = 0` both sides vanish.

Note that the hypothesis `p ∈ Sq` of `nrm_u_injOn` is *not* needed here: `bnd p` is on `∂Sq` for
**any** nonzero `p`, so the reconstruction works on all of `E2`. -/
theorem self_eq_nrm_smul_bndOfU (p : E2) : p = nrm p • bndOfU (u p) := by
  rcases eq_or_ne p 0 with h | h
  · subst h
    simp [nrm]
  · rw [u, nrmu_bndOfU_uPerim (nrm_bnd h), smul_bnd]

/-- **The layer parameter `‖p‖∞` together with the perimeter parameter `u(p)` determine the point,
on the whole plane `E2 = ℝ²`.**  (The restricted version on the filling square `Sq` is
`nrm_u_injOn`; removing the hypothesis `p ∈ Sq` costs nothing, since the radial projection `bnd p`
of any nonzero point of `E2` lies on the boundary `∂Sq`, where `uPerim` is a coordinate.) -/
theorem nrm_u_injOn_univ : Set.InjOn (fun p : Work.Cusp.E2 => (Work.Cusp.nrm p, Work.Cusp.u p)) Set.univ := by
  intro p _ q _ hpq
  have hn : nrm p = nrm q := congrArg Prod.fst hpq
  have hu : u p = u q := congrArg Prod.snd hpq
  rw [self_eq_nrm_smul_bndOfU p, self_eq_nrm_smul_bndOfU q, hn, hu]

end Work.Cusp
