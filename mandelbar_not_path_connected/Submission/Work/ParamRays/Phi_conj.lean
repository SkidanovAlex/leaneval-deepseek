import Mathlib
import Submission.Work.ParamRays.Basic
import Submission.Work.ParamRays.Interface
import Submission.Work.ParamRays.PhiUnique
import Submission.Work.ParamRaysCrit.CritTransport.isCritBottcher_conj

-- Lean v4.35.0-rc3 / Mathlib 5e0c4e5 made `isDefEq` respect transparency when unifying instances; with it,
-- `ZMod.instField` and `ZMod.commRing` (and `Neg (ZMod p)` via `SubtractionMonoid`) no longer unify, which
-- breaks `ring`/`rw`/module-instance search on `ZMod p`. Restore the v4.34 behaviour for this file.
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false


open Filter
open scoped Real Topology ComplexConjugate

namespace Work.ParamRays

open LeanEval.ComplexAnalysis (Tantibar)

/-- Complex conjugation transports the escaping set: the orbit of `conj w` under `T_{conj c}` is
the conjugate of the orbit of `w` under `T_c` (`orbit_conj`), hence the two orbits have the same
norms and one escapes if and only if the other does. -/
theorem escaping_conj_conj {c w : ℂ} : Escaping (conj c) w ↔ Escaping c (conj w) := by
  simp only [Escaping]
  rw [show (fun n : ℕ => ‖orbit (conj c) w n‖) = fun n : ℕ => ‖orbit c (conj w) n‖ from by
    funext n
    have h := orbit_conj c (conj w) n
    rw [Complex.conj_conj] at h
    rw [h, Complex.norm_conj]]

 /-- The parameter Böttcher map commutes with complex conjugation:
`Φ (conj c) = conj (Φ c)`.

Route.  If `c ∈ Mb` then `conj c ∈ Mb` (`mandelbar_conj`), so both sides are `0`.  For `c ∉ Mb`,
let `φ` be a critical Böttcher coordinate of `T_c` (a Böttcher coordinate on `critDomain c`,
which contains the critical value); then `ψ w := conj (φ (conj w))` is a critical Böttcher
coordinate of `T_{conj c}` (`isCritBottcher_conj`).  The bridge `Phi_eq_of_isCritBottcher` at
`c` and at `conj c` gives `Phi (conj c) = ψ (conj c) = conj (φ c) = conj (Phi c)`. -/
theorem Phi_conj (hB : Work.ParamRays.BottcherExists) (c : ℂ) :
    Work.ParamRays.Phi ((starRingEnd ℂ) c) = (starRingEnd ℂ) (Work.ParamRays.Phi c) := by
  by_cases hc : c ∈ Mb
  · rw [Phi_eq_zero_of_mem (mandelbar_conj hc), Phi_eq_zero_of_mem hc, map_zero]
  · have hc' : conj c ∉ Mb := fun h => hc (by simpa using mandelbar_conj h)
    obtain ⟨φ, hφ⟩ := hB c hc
    have hψ : IsCritBottcher (conj c) (fun w : ℂ => conj (φ (conj w))) :=
      Work.ParamRaysCrit.CritTransport.isCritBottcher_conj hφ
    rw [Phi_eq_of_isCritBottcher hc' hψ, Phi_eq_of_isCritBottcher hc hφ]
    rw [Complex.conj_conj]

end Work.ParamRays
