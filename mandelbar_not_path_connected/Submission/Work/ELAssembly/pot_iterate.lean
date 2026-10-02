import Mathlib
import Submission.Work.ELAssembly.Defs
import Submission.Work.ELNest.Qp_shift

-- Lean v4.35.0-rc3 / Mathlib 5e0c4e5 made `isDefEq` respect transparency when unifying instances; with it,
-- `ZMod.instField` and `ZMod.commRing` (and `Neg (ZMod p)` via `SubtractionMonoid`) no longer unify, which
-- breaks `ring`/`rw`/module-instance search on `ZMod p`. Restore the v4.34 behaviour for this file.
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false


namespace Work.ELAssembly

open LeanEval.ComplexAnalysis (Tantibar)

/-- The modulus of the Böttcher coordinate is squared by one application of `T_c`:
`‖φ (T_c z)‖ = ‖φ z‖ ^ 2` on the escaping set. -/
theorem norm_phi_Tantibar' {c : ℂ} {φ : ℂ → ℂ} (h : Work.ParamRays.IsDynBottcher c φ) {z : ℂ}
    (hz : Work.ParamRays.Escaping c z) :
    ‖φ (Tantibar c z)‖ = ‖φ z‖ ^ 2 := by
  rw [h.2.1 z hz, norm_pow, starRingEnd_apply, norm_star]

/-- The potential is doubled by one application of `T_c`:
`pot (T_c z) = 2 * pot z`, at *every* point `z`, escaping or not. -/
theorem pot_Tantibar {c : ℂ} (d : Work.EL.RootParabolic c) (z : ℂ) :
    Work.EL.pot d.hN (Tantibar c z) = 2 * Work.EL.pot d.hN z := by
  by_cases hz : z ∈ Work.EL.K c
  · -- `z` has a bounded orbit, hence so does `T_c z`; both potentials vanish.
    have hzb : Work.ParamRays.BoundedOrbit c z := hz
    have hTcb : Work.ParamRays.BoundedOrbit c (Tantibar c z) := by
      have h := Work.ParamRays.BoundedOrbit.shift (c := c) (z := z) hzb 1
      simpa [Work.ParamRays.orbit] using h
    have hTc : Tantibar c z ∈ Work.EL.K c := hTcb
    rw [Work.EL.pot_of_mem d.hN hz, Work.EL.pot_of_mem d.hN hTc]
    ring
  · -- `z` escapes; `T_c z` escapes too and the Böttcher moduli square.
    have hznb : ¬ Work.ParamRays.BoundedOrbit c z := hz
    have hzE : Work.ParamRays.Escaping c z :=
      (Work.ParamRays.escaping_iff_not_bounded c z).mpr hznb
    have hTcE : Work.ParamRays.Escaping c (Tantibar c z) := by
      have h := Work.ParamRays.Escaping.iterate hzE 1
      simpa [Work.ParamRays.orbit] using h
    have hTc : Tantibar c z ∉ Work.EL.K c := by
      show ¬ Work.ParamRays.BoundedOrbit c (Tantibar c z)
      rw [← Work.ParamRays.escaping_iff_not_bounded]
      exact hTcE
    rw [Work.EL.pot_of_notMem d.hN hTc, Work.EL.pot_of_notMem d.hN hz,
      Work.EL.dynPhi_of_notMem hTc, Work.EL.dynPhi_of_notMem hz]
    have hnorm : ‖d.φ (Tantibar c z)‖ = ‖d.φ z‖ ^ 2 :=
      norm_phi_Tantibar' d.bottcher hzE
    rw [hnorm, Real.log_pow]
    norm_num

theorem pot_iterate {c : ℂ} (d : Work.EL.RootParabolic c) (n : ℕ) (z : ℂ) : Work.EL.pot d.hN ((LeanEval.ComplexAnalysis.Tantibar c)^[n] z) = (2 : ℝ) ^ n * Work.EL.pot d.hN z := by
  induction n with
  | zero => simp
  | succ n ih =>
    rw [Function.iterate_succ_apply', pot_Tantibar d, ih, pow_succ]
    ring

end Work.ELAssembly
