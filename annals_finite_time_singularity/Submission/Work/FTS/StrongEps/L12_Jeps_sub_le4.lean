/-
# `StrongEps/L12_Jeps_sub_le4.lean` — the zero-mode mollifier error at level 4 (PROVED)

curric-46 lead install (2026-10-11), `cbc/fts_strongeps_c1c5_ruling.md` §3 (C3, Gap 2: level-4
re-route; no `ℋ⁵`, no StarPkg6).  Consumer: `EpsCorrTendsto4.EpsCorr_tendsto_zero4` (proved).
Proof sketch: in log coordinates `(s, ζ) = (log z, log tan θ)`, `L₁₂(f)(0) = ∫∫ (K·w)(ζ) f̃ ds dζ`
with `w = sin θ cos θ = 1/(2 cosh ζ)`; Fubini moves the convolution onto the `s`-independent weight
`K·w`, the `s`-part of the kernel integrates out, and `|ρ̌_ε *_ζ (Kw) − Kw| ≤ C ε w`; the remaining
`∫∫ |f|/z` is bounded by `HkNorm α 4 f` (Cauchy–Schwarz as in
`GalBasis.cc.integrableOn_L12dens_of_SmoothOpen_HkMem`, weight `Wlam`; `C` independent of α).

**Status: PROVED** (owner session 18).  The proof is in
`L12_Jeps_sub_le4_proof.lean` (`Work.FTS.StrongEps.L12_Jeps_sub_le4_proof`, constant
`C = 32 e^8`, axioms `[propext, Classical.choice, Quot.sound]`), which also carries the elementary
transport/marginal bricks of the computation.  This file is the frozen statement plus the one-line
transplant.
-/
import Mathlib.Basic.Real.Basic
import Mathlib.Order.Filter.Defs
import Submission.Work.FTS.StrongEps.L12_Jeps_sub_le
import Submission.Work.FTS.StrongEps.L12_Jeps_sub_le4_proof

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

/-- **`|L₁₂(J_ε f)(0) − L₁₂(f)(0)| ≤ C ε ‖f‖_{ℋ⁴}`**. -/
theorem L12_Jeps_sub_le4 (ρ : ℝ × ℝ → ℝ) (hρ : IsSmoothKernel ρ) :
    ∃ C : ℝ, 0 < C ∧ ∀ (α : ℝ), α ∈ Set.Ioc 0 1 → ∀ (f : Fn),
      Work.FTS.EllipticEst.SmoothOpen f → Work.Spaces.HkMem α 4 f →
      ∀ ε : ℝ, ε ∈ Set.Ioc 0 1 →
        |Work.Construction.L12 (Jeps ρ ε f) 0 - Work.Construction.L12 f 0|
          ≤ C * ε * Work.Spaces.HkNorm α 4 f :=
  L12_Jeps_sub_le4_proof ρ hρ

end Work.FTS.StrongEps
