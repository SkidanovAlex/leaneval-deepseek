/-
# `E5Aux3/L12_slice_eq_zero_of_hkMem.lean` — conservation of the unmollified zero mode from
`ℋ⁴` data alone (PROVED)

curric-46 lead install (2026-10-11), `cbc/fts_strongeps_c1c5_ruling.md` §2 (C2: no clause).
Replaces the majorant inputs `hval/hderi/hmaj/hae/hint/hcont0` of `E5Aux3.hl12_of_supply`; every
hypothesis is read off `EpsUniformMem` + `epsRHSP_hkMem_fam` / `epsWP_hkMem4_bnd_unif` +
`HkMem_Jeps_*` (6 → 4 by `HkMem_mono_of_contDiffOn`; uniform `B` from
`EpsE4Thr/HkNorm_epsRHSP_le`).  Route: Volterra identity on `Qd`; Fubini on
`[0,τ] × (0,∞) × Iθ` with `∫∫ |K Y|/r ≤ C·HkNorm α 4 Y` (Cauchy–Schwarz of
`integrableOn_L12dens_of_SmoothOpen_HkMem`) and joint measurability from `hc1`; then
`L₁₂(epsRHSP s)(0) = L₁₂(Pz (J_ε epsWP))(0) = 0` (`PZeroAux.Pz_l12`, its `hint/hae` from `hWm`
+ `SmoothOpen (J_ε ·)`).

**Status: PROVED** (owner session 18).  The proof is in the separate module
`E5Aux3/L12_slice_eq_zero_of_hkMem_proof.lean` (`Work.FTS.StrongEps.E5Aux3.L12_slice_eq_zero_of_hkMem_proof`,
axioms `[propext, Classical.choice, Quot.sound]`), which also carries the four Fubini/measurability
bricks `epsRHSP_dens_aesm_slice`, `epsRHSP_dens_aesm_prod`, `integrable_angleDens_of_hkMem`,
`integrableOn_L12dens_of_aem`.  This file is the frozen statement plus the one-line transplant.
-/
import Mathlib.Analysis.Calculus.ContDiff.Defs
import Mathlib.Analysis.InnerProductSpace.Basic
import Mathlib.Analysis.SpecialFunctions.Trigonometric.Basic
import Submission.Work.FTS.StrongEps.EpsCorrTendsto
import Submission.Work.FTS.StrongEps.E5Aux3.L12_slice_eq_zero_of_hkMem_proof

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

noncomputable section

open scoped Real Topology
open MeasureTheory Set Filter

namespace Work.FTS.StrongEps

open Work.FTS.Galerkin (Fn Fam slice)

set_option autoImplicit false

/-- **`L₁₂(slice g τ)(0) = 0` along an ε-solution, from `ℋ⁴` data**. -/
theorem L12_slice_eq_zero_of_hkMem {α ε T : ℝ} {ρ : ℝ × ℝ → ℝ} {Φs : Fn} {E : Fn → Fn}
    {g₀ : Fn} {g : Fam} {B : ℝ}
    (hα : α ∈ Set.Ioc 0 1) (hρ : IsSmoothKernel ρ) (hε : 0 < ε) (hT : 0 < T)
    (hsol : IsEpsSolP α ρ ε T Φs E g₀ g)
    (hc1 : ContDiffOn ℝ 1 (fun p : ℝ × ℝ × ℝ => g p.1 p.2.1 p.2.2)
      (Set.Ioi 0 ×ˢ Set.Ioo 0 (π / 2) ×ˢ Set.Icc 0 T))
    (hsm : ∀ τ ∈ Set.Icc 0 T, Work.FTS.EllipticEst.SmoothOpen (slice g τ))
    (hmem : ∀ τ ∈ Set.Icc 0 T, Work.Spaces.HkMem α 4 (slice g τ))
    (hRm : ∀ τ ∈ Set.Icc 0 T, Work.Spaces.HkMem α 4 (epsRHSP α ρ ε Φs E g τ) ∧
      Work.Spaces.HkNorm α 4 (epsRHSP α ρ ε Φs E g τ) ≤ B)
    (hWm : ∀ τ ∈ Set.Icc 0 T, Work.Spaces.HkMem α 4 (Jeps ρ ε (epsWP α ρ ε Φs E g τ)))
    (h0 : Work.Construction.L12 g₀ 0 = 0) :
    ∀ τ ∈ Set.Icc 0 T, Work.Construction.L12 (slice g τ) 0 = 0 :=
  Work.FTS.StrongEps.E5Aux3.L12_slice_eq_zero_of_hkMem_proof hα hρ hε hT hsol hc1 hsm hmem hRm
    hWm h0

end Work.FTS.StrongEps
