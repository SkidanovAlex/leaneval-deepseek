import Mathlib.MeasureTheory.Integral.IntervalIntegral.Basic
import Submission.Work.FTS.StrongEps.EpsE4Thr.RegFromVolterraD
import Submission.Work.FTS.StrongEps.EpsE4Thr.XStep

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

/-!
# `EpsE4Thr/RegDataOfXBall.lean` — OPEN LEAF-D2 `regData_of_xball`

curric-46 install 2026-10-12 (REVIEW F2; `cbc/fts_regularity_interface.md` §2 last bullet).  The
producer of `RegDataD` (the hypotheses of LEAF-D `regFromVolterra'`) for `F = Feps` along the
Picard limit family, given its slices in the `X`-ball and its Volterra identity.  TRUE at fixed `ε`
(research-low; the hardest regularity item — dispatch first).

Route (mollified form `Feps w_σ = J_ε Φ_σ − c_σ • bump`, `Φ_σ = profRHS(P₀ J_ε w_σ)`):
* curve `EpsSq`-Lipschitz: `hvol` + the `hbd` gate of `EpsRHSPLipX_Sq` at radius `2 C₀`
  (`EpsSq_intervalIntegral_le_gen`);
* `hAy` (per-slice `C¹`): `smoothOpen_Feps_of_classC` (or `continuousOn_Feps_of_XBall` / `Feps_data_of_xball8`);
* `hAc` (joint continuity): per-slice continuity + the uniform-in-`y` difference bound
  `profRHS_sub_sup_le_Sq` / `profRHS_pre_sub_pt_le_Sq` + the `EpsSq`-Lipschitz bound
  (`EpsEngine.continuous_logPull_family`);
* `hB` (the real work): `∂_y J_ε Φ_σ = ∇Jker ⋆ Φ_σ` jointly continuous (`conv_intervalIntegral_swap`),
  and `c_σ` continuous (evaluate at a point where `bump ≠ 0`, use `hpt`).
No `σ`-derivative of the right-hand side is needed.
-/

noncomputable section
open scoped Real Topology
open MeasureTheory Set Filter

namespace Work.FTS.StrongEps.EpsE4Thr.E4R5

open Work.FTS.Galerkin (Fn Fam slice)
open Work.FTS.EpsEngine (XBall Feps)
open Work.FTS.StrongEps.EpsLocalPStar (limFam)

set_option autoImplicit false
set_option linter.unusedVariables false

/-- **OPEN LEAF-D2**: the regularity data of the scheme's right-hand side along the Picard limit
curve, from the `X`-ball invariant of its slices and its Volterra identity (fixed `ε`). -/
theorem regData_of_xball {α C₀ Ce Cs R ε δ : ℝ} {ρ : ℝ × ℝ → ℝ} {Φs : Fn} {E : Fn → Fn}
    {h₀ : Fn}
    (hα : α ∈ Ioc (0 : ℝ) 1) (hρ : Work.FTS.StrongEps.IsSmoothKernel ρ) (hε : 0 < ε)
    (hε1 : ε ≤ 1) (hC₀ : 0 < C₀)
    (hEll : ∀ u : Fn, Work.FTS.ClassC.ClassC α u →
      Work.FTS.VocabO.EllPkgGo α Ce u (E u) ∧ Work.FTS.ClassC.EllPkgK α 6 Ce u (E u))
    (hstar : Work.FTS.VocabO2.StarPkgo2 α Cs Φs) (hml : MuLamOK α (2 * C₀) Φs E)
    (hδ : 0 < δ) (hR : 0 < R) (hsm0 : Work.FTS.EllipticEst.SmoothOpen h₀)
    (hlim : ∀ τ ∈ Icc 0 δ, XBall α ρ ε R (2 * C₀) (slice (limFam (Feps α ρ ε Φs E) h₀) τ))
    (hvol : ∀ z θ τ : ℝ, 0 < z → θ ∈ Ioo 0 (Real.pi / 2) → τ ∈ Icc 0 δ →
      limFam (Feps α ρ ε Φs E) h₀ z θ τ
        = h₀ z θ + ∫ s in (0 : ℝ)..τ,
            Feps α ρ ε Φs E (slice (limFam (Feps α ρ ε Φs E) h₀) s) z θ) :
    RegDataD (Feps α ρ ε Φs E) h₀ δ := by
  sorry

end Work.FTS.StrongEps.EpsE4Thr.E4R5
