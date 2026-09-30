/-
# Continuity of the polar chart `ThetaPolar` on the wedges

`ThetaPolar v` (`Basic.lean`) is the inner (polar) chart of the `v`-th cusp,
`ThetaPolar v p y = (r, θ, w₁, w₂)` with

* `r = radial v p y` (`2 r_J ‖p‖∞` inside, `R₀ − log (collarHeight ‖p‖∞ (β (u p • σ_v + y)))` in the
  collar),
* `θ = thetaAng v p y = 2π u p + 2π⟪y₂λ₂ + y₃λ₃, σ_v⟫/‖σ_v‖²` (the perimeter parameter `u p` plus
  the phase correction),
* `w = wOf v y = (⟪y₂λ₂+y₃λ₃, frame2 v⟫, ⟪…, frame3 v⟫)`, linear in `y`.

As a function of `p` the angle coordinate involves the perimeter parameter `u p = uPerim (bnd p)`,
which jumps by `1` on the ray through the corner `(1,1)` of the square.  It is therefore continuous
only on the four open wedges

`wedge k = {p | 0 < nrm p ∧ u p ∈ (k/4, (k+1)/4)}`

of directions, and continuous *there* — the same regularity statement as for the `c`-shifted polar
chart `ThetaPolarS v c` on the shifted wedges `wedgeS c k`, of which the present theorem is the
case `c = 0`: on a wedge the values of `u` already lie in `[0,1)`, so the fractional part defining
the lift `uS 0` is trivial, and hence

* `wedge k ⊆ wedgeS 0 k` (`Int.fract (u p) = u p` because `u p ∈ [0,1)` by `u_mem_of_nrm_pos`),
* `ThetaPolarS v 0 p y = ThetaPolar v p y` on it (`ThetaPolarS_zero`).

So the statement follows from `ThetaPolarS_continuousOn v 0 k` by monotonicity of `ContinuousOn`
and `ContinuousOn.congr`.
-/
import Mathlib
import Submission.Work.Cusp.Basic
import Submission.Work.Cusp.Charts
import Submission.Work.Cusp.ThetaPolarS_continuousOn
import Submission.Work.Cusp.ThetaPolarS_zero

-- Lean v4.35.0-rc3 / Mathlib 5e0c4e5 made `isDefEq` respect transparency when unifying instances; with it,
-- `ZMod.instField` and `ZMod.commRing` (and `Neg (ZMod p)` via `SubtractionMonoid`) no longer unify, which
-- breaks `ring`/`rw`/module-instance search on `ZMod p`. Restore the v4.34 behaviour for this file.
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false


noncomputable section

namespace Work.Cusp

open scoped Real InnerProductSpace

/-- The unshifted wedge `wedge k` is the `0`-shifted wedge `wedgeS 0 k`: on `wedge k` the perimeter
parameter already lies in `[0,1)`, so its fractional part is itself. -/
theorem wedge_subset_wedgeS_zero (k : Fin 4) : wedge k ⊆ wedgeS 0 k := by
  intro p hp
  rw [wedge] at hp
  refine ⟨hp.1, ?_⟩
  have hf : Int.fract (u p) = u p := Int.fract_eq_self.mpr (u_mem_of_nrm_pos hp.1)
  simp only [sub_zero, hf]
  exact hp.2

/-- **The polar chart `ThetaPolar v` is continuous on each wedge.**  This is the standing regularity
fact for the polar chart of the cusp piece: the only discontinuity of `ThetaPolar v p y` in `p` is
the jump of the perimeter parameter `u` on the corner ray, and a wedge misses that ray. -/
theorem ThetaPolar_continuousOn_wedge (v : Fin 5) (k : Fin 4) :
    ContinuousOn (fun z : E2 × E2 => ThetaPolar v z.1 z.2) {z | z.1 ∈ wedge k} := by
  have hsub : {z : E2 × E2 | z.1 ∈ wedge k} ⊆ {z : E2 × E2 | z.1 ∈ wedgeS 0 k} :=
    fun z hz => wedge_subset_wedgeS_zero k hz
  have hcont : ContinuousOn (fun z : E2 × E2 => ThetaPolarS v 0 z.1 z.2)
      {z : E2 × E2 | z.1 ∈ wedge k} :=
    (ThetaPolarS_continuousOn v 0 k).mono hsub
  refine hcont.congr ?_
  intro z hz
  rw [wedge] at hz
  exact (ThetaPolarS_zero v z.1 z.2 hz.1).symm

end Work.Cusp
