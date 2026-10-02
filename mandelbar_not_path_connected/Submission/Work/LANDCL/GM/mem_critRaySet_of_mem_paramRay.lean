import Mathlib
import Submission.Work.LANDCL.Defs
import Submission.Work.ParamRays.PhiUnique

-- Lean v4.35.0-rc3 / Mathlib 5e0c4e5 made `isDefEq` respect transparency when unifying instances; with it,
-- `ZMod.instField` and `ZMod.commRing` (and `Neg (ZMod p)` via `SubtractionMonoid`) no longer unify, which
-- breaks `ring`/`rw`/module-instance search on `ZMod p`. Restore the v4.34 behaviour for this file.
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false


namespace Work.LANDCL.GM

/-- A parameter on the parameter ray `R(θ)` lies on the critical ray of `T_c` at angle `θ`:
`Φ c = r · e^{2πiθ}` with `r > 1` says exactly that the critical value `c` — which lies in the
critical domain and whose critical Böttcher coordinate value at `c` is `Φ c` — is a point of
`critRaySet c θ`. -/
theorem mem_critRaySet_of_mem_paramRay (hB : Work.ParamRays.BottcherExists) {θ : ℝ} {c : ℂ}
    (hc : c ∈ Work.ParamRays.paramRay θ) : c ∈ Work.LANDCL.critRaySet c θ := by
  rw [Work.ParamRays.mem_paramRay] at hc
  obtain ⟨hcMb, r, hr, hPhi⟩ := hc
  obtain ⟨φ, hφ⟩ := hB c hcMb
  exact ⟨φ, r, hφ, Work.ParamRays.self_mem_critDomain hcMb, hr,
    by rw [← hPhi, Work.ParamRays.Phi_eq_of_isCritBottcher hcMb hφ]⟩

end Work.LANDCL.GM
