import Mathlib
import Submission.Work.ParamRaysCrit.CritTransport

-- Lean v4.35.0-rc3 / Mathlib 5e0c4e5 made `isDefEq` respect transparency when unifying instances; with it,
-- `ZMod.instField` and `ZMod.commRing` (and `Neg (ZMod p)` via `SubtractionMonoid`) no longer unify, which
-- breaks `ring`/`rw`/module-instance search on `ZMod p`. Restore the v4.34 behaviour for this file.
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false


namespace Work.ParamRaysCrit.CritTransport

open Filter
open scoped ComplexConjugate

/-- The rotation `c ↦ ω c` transports critical Böttcher coordinates: if `φ` is a critical Böttcher coordinate of `T_c`, then `w ↦ ω * φ (w / ω)` is a critical Böttcher coordinate of `T_{ω c}`, where `Work.ParamRays.omega = exp (2πi/3)`. Copy the proof of `Work.ParamRays.isDynBottcher_smul_omega` (`Submission/Work/ParamRays/Phi_smul_omega.lean`), using `Work.ParamRays.Tantibar_omega`, `Work.ParamRays.orbit_omega` and the transport of the domain `Work.ParamRays.mem_critDomain_smul_omega` (in `Submission.Work.ParamRaysCrit.CritTransport`). -/
theorem isCritBottcher_smul_omega {c : ℂ} {φ : ℂ → ℂ} (hφ : Work.ParamRays.IsCritBottcher c φ) :
    Work.ParamRays.IsCritBottcher (Work.ParamRays.omega * c)
      (fun w : ℂ => Work.ParamRays.omega * φ (w / Work.ParamRays.omega)) := by
  refine ⟨?_, ?_, ?_⟩
  · have hmaps : Set.MapsTo (fun w : ℂ => w / Work.ParamRays.omega)
        (Work.ParamRays.critDomain (Work.ParamRays.omega * c)) (Work.ParamRays.critDomain c) :=
      fun w hw => Work.ParamRays.mem_critDomain_smul_omega.mp hw
    have hcont : ContinuousOn (fun w : ℂ => φ (w / Work.ParamRays.omega))
        (Work.ParamRays.critDomain (Work.ParamRays.omega * c)) :=
      hφ.1.comp (continuous_id.div_const Work.ParamRays.omega).continuousOn hmaps
    exact hcont.const_mul Work.ParamRays.omega
  · intro w hw
    have hw' : w / Work.ParamRays.omega ∈ Work.ParamRays.critDomain c :=
      Work.ParamRays.mem_critDomain_smul_omega.mp hw
    have hw_eq : Work.ParamRays.omega * (w / Work.ParamRays.omega) = w :=
      mul_div_cancel₀ w Work.ParamRays.omega_ne_zero
    have hT : LeanEval.ComplexAnalysis.Tantibar (Work.ParamRays.omega * c) w
        = Work.ParamRays.omega * LeanEval.ComplexAnalysis.Tantibar c (w / Work.ParamRays.omega) := by
      conv_lhs => rw [← hw_eq]
      exact Work.ParamRays.Tantibar_omega c (w / Work.ParamRays.omega)
    calc Work.ParamRays.omega
            * φ (LeanEval.ComplexAnalysis.Tantibar (Work.ParamRays.omega * c) w / Work.ParamRays.omega)
        = Work.ParamRays.omega
            * φ (LeanEval.ComplexAnalysis.Tantibar c (w / Work.ParamRays.omega)) := by
          rw [hT, mul_div_cancel_left₀ _ Work.ParamRays.omega_ne_zero]
      _ = Work.ParamRays.omega * conj (φ (w / Work.ParamRays.omega)) ^ 2 := by
          rw [hφ.2.1 _ hw']
      _ = conj (Work.ParamRays.omega * φ (w / Work.ParamRays.omega)) ^ 2 := by
          have hω : conj Work.ParamRays.omega ^ 2 = Work.ParamRays.omega := by
            rw [pow_two, ← map_mul, ← pow_two, Work.ParamRays.omega_sq_eq_conj, Complex.conj_conj]
          conv_rhs => rw [map_mul, mul_pow, hω]
  · intro ε hε
    have hdiv : Tendsto (fun z : ℂ => z / Work.ParamRays.omega) (cocompact ℂ) (cocompact ℂ) := by
      simpa [div_eq_mul_inv] using
        (Filter.tendsto_cocompact_mul_right₀ (K := ℂ) (a := Work.ParamRays.omega⁻¹)
          (inv_ne_zero Work.ParamRays.omega_ne_zero))
    filter_upwards [hdiv.eventually (hφ.2.2 ε hε)] with z hz
    have hz_eq : Work.ParamRays.omega * (z / Work.ParamRays.omega) = z :=
      mul_div_cancel₀ z Work.ParamRays.omega_ne_zero
    have h1 : Work.ParamRays.omega * φ (z / Work.ParamRays.omega) - z
        = Work.ParamRays.omega * (φ (z / Work.ParamRays.omega) - z / Work.ParamRays.omega) := by
      rw [mul_sub, hz_eq]
    rw [h1, norm_mul, Work.ParamRays.norm_omega, one_mul]
    calc ‖φ (z / Work.ParamRays.omega) - z / Work.ParamRays.omega‖
          ≤ ε * ‖z / Work.ParamRays.omega‖ := hz
      _ = ε * ‖z‖ := by rw [norm_div, Work.ParamRays.norm_omega, div_one]

end Work.ParamRaysCrit.CritTransport
