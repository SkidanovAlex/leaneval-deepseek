import Mathlib
import Submission.Work.ParamRays.Basic
import Submission.Work.ParamRays.Interface
import Submission.Work.ParamRays.PhiUnique
import Submission.Work.ParamRaysCrit.CritTransport.isCritBottcher_smul_omega

-- Lean v4.35.0-rc3 / Mathlib 5e0c4e5 made `isDefEq` respect transparency when unifying instances; with it,
-- `ZMod.instField` and `ZMod.commRing` (and `Neg (ZMod p)` via `SubtractionMonoid`) no longer unify, which
-- breaks `ring`/`rw`/module-instance search on `ZMod p`. Restore the v4.34 behaviour for this file.
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false


open Filter
open scoped Real Topology ComplexConjugate

namespace Work.ParamRays

open LeanEval.ComplexAnalysis (Tantibar Mandelbar)

/-! ## Auxiliary lemmas on the rotation `z ↦ ω z`

The rotation `ω = exp (2πi/3)` is a cube root of unity (`omega_cube`) of modulus `1`
(`norm_omega`); it therefore acts as a bijection of `ℂ` and of every dynamical plane.
Everything here is a purely elementary transport of `Work.ParamRays.Basic`. -/

/-- `ω ^ 2` is the inverse of `ω`: `ω * (ω * (ω * c)) = c`. -/
theorem omega_mul_omega_mul_omega (c : ℂ) : omega * (omega * (omega * c)) = c := by
  have h : omega * (omega * (omega * c)) = omega ^ 3 * c := by ring
  rw [h, omega_cube, one_mul]

/-- `conj ω ^ 2 = ω`, the identity making `ψ w = ω * φ (w / ω)` satisfy the Böttcher equation. -/
theorem conj_omega_sq : conj omega ^ 2 = omega := by
  rw [pow_two, ← map_mul, ← pow_two, omega_sq_eq_conj, Complex.conj_conj]

/-- Off the mandelbar stays off the mandelbar under `c ↦ ω c`. -/
theorem not_mem_mandelbar_smul_omega {c : ℂ} (hc : c ∉ Mb) : omega * c ∉ Mb := by
  intro h
  refine hc ?_
  have h2 : omega * (omega * c) ∈ Mb := mandelbar_smul_omega (c := omega * c) h
  have h3 : omega * (omega * (omega * c)) ∈ Mb :=
    mandelbar_smul_omega (c := omega * (omega * c)) h2
  rwa [omega_mul_omega_mul_omega c] at h3

/-- The escaping set is transported by the rotation: `ω z` escapes for `T_{ω c}` if and only if
`z` escapes for `T_c`. -/
theorem escaping_smul_omega (c z : ℂ) : Escaping (omega * c) (omega * z) ↔ Escaping c z := by
  have h : (fun n : ℕ => ‖orbit (omega * c) (omega * z) n‖) = fun n : ℕ => ‖orbit c z n‖ := by
    funext n
    rw [orbit_omega, norm_mul, norm_omega, one_mul]
  simp only [Escaping, h]

/-- The escaping set is transported by the rotation, in the form used below: `w` escapes for
`T_{ω c}` if and only if `w / ω` escapes for `T_c`. -/
theorem escaping_div_omega (c w : ℂ) : Escaping (omega * c) w ↔ Escaping c (w / omega) := by
  have h : omega * (w / omega) = w := mul_div_cancel₀ w omega_ne_zero
  conv_lhs => rw [← h]
  exact escaping_smul_omega c (w / omega)

/-! ## Transport of Böttcher coordinates -/

/-- If `φ` is a Böttcher coordinate of `T_c`, then `ψ w = ω * φ (w / ω)` is a Böttcher coordinate
of the rotated antipolynomial `T_{ω c}`.  This is the dynamical content of the equivariance of the
parameter Böttcher map under `c ↦ ω c`. -/
theorem isDynBottcher_smul_omega {c : ℂ} {φ : ℂ → ℂ} (hφ : IsDynBottcher c φ) :
    IsDynBottcher (omega * c) (fun w => omega * φ (w / omega)) := by
  refine ⟨?_, ?_, ?_⟩
  · have hmaps : Set.MapsTo (fun w : ℂ => w / omega) (escapingSet (omega * c)) (escapingSet c) :=
      fun w hw => (escaping_div_omega c w).mp hw
    have hcont : ContinuousOn (fun w : ℂ => φ (w / omega)) (escapingSet (omega * c)) :=
      hφ.1.comp (continuous_id.div_const omega).continuousOn hmaps
    exact hcont.const_mul omega
  · intro w hw
    have hw' : Escaping c (w / omega) := (escaping_div_omega c w).mp hw
    have hw_eq : omega * (w / omega) = w := mul_div_cancel₀ w omega_ne_zero
    have hT : Tantibar (omega * c) w = omega * Tantibar c (w / omega) := by
      conv_lhs => rw [← hw_eq]
      exact Tantibar_omega c (w / omega)
    calc omega * φ (Tantibar (omega * c) w / omega)
        = omega * φ (Tantibar c (w / omega)) := by
          rw [hT, mul_div_cancel_left₀ _ omega_ne_zero]
      _ = omega * conj (φ (w / omega)) ^ 2 := by rw [hφ.2.1 _ hw']
      _ = conj (omega * φ (w / omega)) ^ 2 := by
          conv_rhs => rw [map_mul, mul_pow, conj_omega_sq]
  · intro ε hε
    have hdiv : Tendsto (fun z : ℂ => z / omega) (cocompact ℂ) (cocompact ℂ) := by
      simpa [div_eq_mul_inv] using
        (Filter.tendsto_cocompact_mul_right₀ (K := ℂ) (a := omega⁻¹) (inv_ne_zero omega_ne_zero))
    filter_upwards [hdiv.eventually (hφ.2.2 ε hε)] with z hz
    have hz_eq : omega * (z / omega) = z := mul_div_cancel₀ z omega_ne_zero
    have h1 : omega * φ (z / omega) - z = omega * (φ (z / omega) - z / omega) := by
      rw [mul_sub, hz_eq]
    rw [h1, norm_mul, norm_omega, one_mul]
    calc ‖φ (z / omega) - z / omega‖ ≤ ε * ‖z / omega‖ := hz
      _ = ε * ‖z‖ := by rw [norm_div, norm_omega, div_one]

 /-- The parameter Böttcher map is equivariant under the rotation `c ↦ ω c`:
`Φ (ω c) = ω Φ c`, with `ω = exp (2 π i / 3)`.

Route.  If `c ∈ Mb` then `ω c ∈ Mb` (`mandelbar_smul_omega`) and both sides are `0`.  For
`c ∉ Mb` (then also `ω c ∉ Mb`), let `φ` be a critical Böttcher coordinate of `T_c`; then
`ψ w := ω * φ (w / ω)` is a critical Böttcher coordinate of `T_{ω c}`
(`isCritBottcher_smul_omega`), and the bridge `Phi_eq_of_isCritBottcher` gives
`Phi (ω c) = ψ (ω c) = ω * φ c = ω * Phi c`. -/
theorem Phi_smul_omega (hB : Work.ParamRays.BottcherExists) (c : ℂ) :
    Work.ParamRays.Phi (Work.ParamRays.omega * c) = Work.ParamRays.omega * Work.ParamRays.Phi c := by
  by_cases hc : c ∈ Mb
  · rw [Phi_eq_zero_of_mem hc,
      Phi_eq_zero_of_mem (mandelbar_smul_omega (c := c) hc), mul_zero]
  · have hωc : omega * c ∉ Mb := not_mem_mandelbar_smul_omega hc
    obtain ⟨φ, hφ⟩ := hB c hc
    have hψ : IsCritBottcher (omega * c) (fun w => omega * φ (w / omega)) :=
      Work.ParamRaysCrit.CritTransport.isCritBottcher_smul_omega hφ
    rw [Phi_eq_of_isCritBottcher hωc hψ, Phi_eq_of_isCritBottcher hc hφ]
    show omega * φ (omega * c / omega) = omega * φ c
    rw [mul_div_cancel_left₀ c omega_ne_zero]

end Work.ParamRays
