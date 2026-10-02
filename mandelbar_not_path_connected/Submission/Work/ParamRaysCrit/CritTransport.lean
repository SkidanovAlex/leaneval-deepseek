/-
# Transport of the critical domain under the symmetries `c ↦ conj c` and `c ↦ ω c`

The parameter-plane Böttcher theory uses the two symmetries of the mandelbar:

* complex conjugation `c ↦ conj c`, which conjugates `T_c` to `T_{conj c}`
  (`orbit_conj`) and hence transports the Green function,
  `G_{conj c} w = G_c (conj w)` (`greenFun_conj`);
* the rotation `c ↦ ω c` with `ω = exp (2πi/3)`, for which `G_{ω c} (ω w) = G_c w`
  (`greenFun_omega`, in the sibling file `ParamRays/greenFun_omega.lean`).

Since `paramPotential c = G_c 0` is invariant under both (`0` is fixed by both symmetries), the
critical domain is transported as well:

* `z ∈ critDomain (conj c) ↔ conj z ∈ critDomain c`
  (`mem_critDomain_conj`, with the image form `critDomain_conj`);
* `z ∈ critDomain (ω c) ↔ z / ω ∈ critDomain c`
  (`mem_critDomain_smul_omega`, with the image form `critDomain_smul_omega`).

These are the geometric inputs of `Phi_conj` and `Phi_smul_omega`
(`ParamRays/Phi_conj.lean`, `ParamRays/Phi_smul_omega.lean`), which transport the Böttcher
coordinate itself.

## Main results

* `Work.ParamRays.greenFun_conj`, `Work.ParamRays.paramPotential_conj`,
  `Work.ParamRays.mem_critDomain_conj`, `Work.ParamRays.critDomain_conj`.
* `Work.ParamRays.paramPotential_smul_omega`, `Work.ParamRays.mem_critDomain_smul_omega`,
  `Work.ParamRays.critDomain_smul_omega`.
-/
import Submission.Work.ParamRaysCrit.CritDomain
import Submission.Work.ParamRays.greenFun_omega

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

/-! ## Complex conjugation -/

/-- Complex conjugation transports the Green function:
`G_{conj c} w = G_c (conj w)`. -/
theorem greenFun_conj (c w : ℂ) : greenFun (conj c) w = greenFun c (conj w) := by
  have h : greenSeq (conj c) w = greenSeq c (conj w) := by
    funext n
    have horb := orbit_conj c (conj w) n
    simp only [Complex.conj_conj] at horb
    rw [greenSeq, greenSeq, horb, Complex.norm_conj]
  rw [greenFun, greenFun, h]

/-- The parameter potential is invariant under complex conjugation. -/
theorem paramPotential_conj (c : ℂ) : paramPotential (conj c) = paramPotential c := by
  rw [paramPotential, paramPotential, greenFun_conj, map_zero]

/-- The critical domain is transported by complex conjugation. -/
theorem mem_critDomain_conj {c z : ℂ} : z ∈ critDomain (conj c) ↔ conj z ∈ critDomain c := by
  rw [mem_critDomain, mem_critDomain, greenFun_conj, paramPotential_conj]

/-- As a set, `critDomain (conj c)` is the conjugate of `critDomain c`. -/
theorem critDomain_conj (c : ℂ) : critDomain (conj c) = (starRingEnd ℂ) '' critDomain c := by
  ext z
  rw [mem_critDomain_conj, Set.mem_image]
  constructor
  · intro hz
    exact ⟨conj z, hz, Complex.conj_conj z⟩
  · rintro ⟨y, hy, hyz⟩
    rw [← hyz, Complex.conj_conj]
    exact hy

/-! ## The rotation `c ↦ ω c` -/

/-- The parameter potential is invariant under the rotation `c ↦ ω c`. -/
theorem paramPotential_smul_omega (c : ℂ) : paramPotential (omega * c) = paramPotential c := by
  have h := greenFun_omega c 0
  rw [mul_zero] at h
  exact h

/-- The critical domain is transported by the rotation `c ↦ ω c`. -/
theorem mem_critDomain_smul_omega {c z : ℂ} :
    z ∈ critDomain (omega * c) ↔ z / omega ∈ critDomain c := by
  rw [mem_critDomain, mem_critDomain, paramPotential_smul_omega]
  conv_lhs => rw [← mul_div_cancel₀ z omega_ne_zero]
  rw [greenFun_omega]

/-- As a set, `critDomain (ω c)` is the rotation of `critDomain c`. -/
theorem critDomain_smul_omega (c : ℂ) :
    critDomain (omega * c) = (fun z : ℂ => omega * z) '' critDomain c := by
  ext z
  rw [mem_critDomain_smul_omega, Set.mem_image]
  constructor
  · intro hz
    exact ⟨z / omega, hz, mul_div_cancel₀ z omega_ne_zero⟩
  · rintro ⟨y, hy, rfl⟩
    rwa [mul_div_cancel_left₀ y omega_ne_zero]

end Work.ParamRays
