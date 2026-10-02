import Mathlib
import Submission.Work.ParamRaysCrit.CritTransport

-- Lean v4.35.0-rc3 / Mathlib 5e0c4e5 made `isDefEq` respect transparency when unifying instances; with it,
-- `ZMod.instField` and `ZMod.commRing` (and `Neg (ZMod p)` via `SubtractionMonoid`) no longer unify, which
-- breaks `ring`/`rw`/module-instance search on `ZMod p`. Restore the v4.34 behaviour for this file.
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false


open Filter
open scoped Real Topology ComplexConjugate

namespace Work.ParamRaysCrit.CritTransport

open LeanEval.ComplexAnalysis (Tantibar Mandelbar)

open Work.ParamRays

/-- Complex conjugation transports critical Böttcher coordinates: if `φ` is a critical Böttcher coordinate of `T_c`, then `w ↦ conj (φ (conj w))` is a critical Böttcher coordinate of `T_{conj c}`. Copy the proof of `Work.ParamRays.isDynBottcher_smul_omega` (conjugation version in `Submission/Work/ParamRays/Phi_conj.lean`), using `Work.ParamRays.Tantibar_conj`, `Work.ParamRays.orbit_conj` and the transport of the domain `Work.ParamRays.mem_critDomain_conj` (in `Submission.Work.ParamRaysCrit.CritTransport`). -/
theorem isCritBottcher_conj {c : ℂ} {φ : ℂ → ℂ} (hφ : Work.ParamRays.IsCritBottcher c φ) :
    Work.ParamRays.IsCritBottcher ((starRingEnd ℂ) c) (fun w : ℂ => (starRingEnd ℂ) (φ ((starRingEnd ℂ) w))) := by
  refine ⟨?_, ?_, ?_⟩
  · -- continuity: `conj ∘ φ ∘ conj`, with `conj` mapping `critDomain (conj c)` into `critDomain c`
    have h1 : ContinuousOn (fun w : ℂ => φ (conj w)) (critDomain (conj c)) :=
      hφ.1.comp Complex.continuous_conj.continuousOn
        (fun w hw => (mem_critDomain_conj.mp hw : conj w ∈ critDomain c))
    simpa [Function.comp_def] using Complex.continuous_conj.comp_continuousOn h1
  · -- functional equation
    intro z hz
    have hz' : conj z ∈ critDomain c := mem_critDomain_conj.mp hz
    have hT : conj (Tantibar (conj c) z) = Tantibar c (conj z) := by
      have h := Tantibar_conj c (conj z)
      simp only [Complex.conj_conj] at h
      rw [h, Complex.conj_conj]
    show conj (φ (conj (Tantibar (conj c) z))) = conj (conj (φ (conj z))) ^ 2
    rw [hT, hφ.2.1 (conj z) hz']
    simp only [map_pow, Complex.conj_conj]
  · -- asymptotic to the identity: `‖conj (φ (conj z)) - z‖ = ‖φ (conj z) - conj z‖`
    intro ε hε
    have htend : Tendsto (starRingEnd ℂ) (Filter.cocompact ℂ) (Filter.cocompact ℂ) :=
      Filter.tendsto_cocompact_cocompact_of_norm (f := starRingEnd ℂ)
        (fun ε => ⟨ε, fun x hx => by rwa [Complex.norm_conj]⟩)
    have h3 : ∀ᶠ z : ℂ in Filter.cocompact ℂ, ‖φ (conj z) - conj z‖ ≤ ε * ‖conj z‖ :=
      htend.eventually (hφ.2.2 ε hε)
    filter_upwards [h3] with z hz
    have hz'' : ‖conj (φ (conj z)) - z‖ = ‖φ (conj z) - conj z‖ := by
      rw [show conj (φ (conj z)) - z = conj (φ (conj z) - conj z) by
        rw [map_sub, Complex.conj_conj], Complex.norm_conj]
    rw [hz'']
    simpa only [Complex.norm_conj] using hz

end Work.ParamRaysCrit.CritTransport
