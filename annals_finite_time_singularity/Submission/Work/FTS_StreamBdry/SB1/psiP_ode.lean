import Mathlib.Analysis.Calculus.ContDiff.Defs
import Mathlib.Analysis.Calculus.Deriv.Mul
import Mathlib.Analysis.LocallyConvex.AbsConvexOpen
import Mathlib.MeasureTheory.Integral.IntervalIntegral.Basic
import Submission.Work.FTS_StreamBdry.Basic
import Submission.Work.FTS_StreamBdry.SB1.contDiffOn_uncurry_Uprime
import Submission.Work.FTS_StreamBdry.SB1.rpow_ode_aux

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

/-!
# `Work.FTS_StreamBdry.SB1.psiP_ode` — the level-0 ODE for the `U`-slot part `psiP`

`psiP αG Ψ = -(s2/αG)·∫₀¹ v^{3/αG-1}·U'(Ψ)(zv,θ) dv` is the particular solution of the
level-0 ODE `αG·D_z P + 3P = -s2·U'(Ψ)`; this file proves that it *is* a solution:

`αG·z·∂_z psiP + 3·psiP = -s2·U'(Ψ)` on the open quadrant `Qd`.

## Route

Write `k = 3/αG > 0`, fix `θ` and let `h u = U'(Ψ)(u,θ)`.  For `z' > 0` the substitution
`u = z'v` gives `z'^k·∫₀¹ v^{k-1} h(z'v) dv = ∫₀^{z'} u^{k-1} h(u) du`; the right-hand side
is the primitive of the continuous function `u ↦ u^{k-1}h u`, so the FTC and the product
rule give

`z·∂_z (∫₀¹ v^{k-1} h(zv) dv) = h z - k·∫₀¹ v^{k-1} h(zv) dv`   (`rpow_ode_aux`).

Multiplying by the constant `-(s2 θ/αG)` produces exactly `αG·z·∂_z psiP + 3·psiP = -s2·h z`.

## Inputs

* `Work.Spaces.pz (psiP αG Ψ) z θ = -(s2 θ/αG)·deriv (fun z' => Iint αG Ψ z' θ) z`, since
  `psiP = -(s2/αG)·Iint` definitionally (`psiP_eq_Iint`);
* the slice `u ↦ U'(Ψ)(u,θ)` is continuous on `(0,∞)` (`contDiffOn_uncurry_Uprime`, from
  `h3`) and bounded by `M` there (`SlotBd.Uprime_le`, from `hslot`);
* the analytic core `rpow_ode_aux`.
-/

noncomputable section
open scoped Real Topology
open Set Filter

namespace Work.FTS_StreamBdry.SB1

open Work.FTS.StreamBdryIface (Uprime SlotBd psiP gaugeMode)

theorem psiP_ode {αG M : ℝ} (hαG : 0 < αG) {Ψ : ℝ → ℝ → ℝ}
    (h3 : ContDiffOn ℝ 3 (Function.uncurry Ψ) Work.Construction.Qd)
    (hslot : Work.FTS.StreamBdryIface.SlotBd αG Ψ M) :
    Work.FTS_StreamBdry.PsiPOde αG M Ψ := by
  intro z θ hmem
  obtain ⟨hz, hθ0, hθ1⟩ := Work.FTS_StreamBdry.mem_Qd.mp hmem
  have hkpos : 0 < (3 : ℝ) / αG := div_pos (by norm_num) hαG
  -- the `θ`-slice of `U'(Ψ)` is continuous on `(0,∞)`
  have hU1 : ContDiffOn ℝ 1 (Function.uncurry (Uprime αG Ψ)) Work.Construction.Qd :=
    contDiffOn_uncurry_Uprime h3
  have hcontSlice : ContinuousOn (fun u => Uprime αG Ψ u θ) (Set.Ioi 0) := by
    have hcomp : ContinuousOn (fun u : ℝ => (u, θ)) (Set.Ioi 0) :=
      (continuous_id.prodMk continuous_const).continuousOn
    have hmap : MapsTo (fun u : ℝ => (u, θ)) (Set.Ioi 0) Work.Construction.Qd :=
      fun u hu => ⟨hu, hθ0, hθ1⟩
    have h := hU1.continuousOn.comp hcomp hmap
    exact h
  have hcont : ContinuousOn (fun u => Uprime αG Ψ u θ) (Set.Ioo 0 (z + 1)) :=
    hcontSlice.mono Set.Ioo_subset_Ioi_self
  have hbdd : ∀ u ∈ Set.Ioo (0 : ℝ) (z + 1), |Uprime αG Ψ u θ| ≤ M := by
    intro u hu
    exact Work.FTS_StreamBdry.SlotBd.Uprime_le hslot ⟨hu.1, hθ0, hθ1⟩
  -- the analytic core: the ODE for the integral
  have hA : HasDerivAt (fun z' => ∫ v in (0 : ℝ)..1,
        v ^ ((3 : ℝ) / αG - 1) * Uprime αG Ψ (z' * v) θ)
      ((Uprime αG Ψ z θ - ((3 : ℝ) / αG) * (∫ v in (0 : ℝ)..1,
          v ^ ((3 : ℝ) / αG - 1) * Uprime αG Ψ (z * v) θ)) / z) z :=
    rpow_ode_aux (k := (3 : ℝ) / αG) (M := M) (z := z) hkpos hz hcont hbdd
  have hIdiff : DifferentiableAt ℝ (fun z' => Work.FTS_StreamBdry.Iint αG Ψ z' θ) z := by
    simpa only [Work.FTS_StreamBdry.Iint] using hA.differentiableAt
  have hIderiv : deriv (fun z' => Work.FTS_StreamBdry.Iint αG Ψ z' θ) z
      = (Uprime αG Ψ z θ - ((3 : ℝ) / αG) * Work.FTS_StreamBdry.Iint αG Ψ z θ) / z := by
    simpa only [Work.FTS_StreamBdry.Iint] using hA.deriv
  have hpz : Work.Spaces.pz (psiP αG Ψ) z θ
      = -(Work.Construction.s2 θ / αG) * ((Uprime αG Ψ z θ
          - ((3 : ℝ) / αG) * Work.FTS_StreamBdry.Iint αG Ψ z θ) / z) := by
    have hfun : (fun z' => psiP αG Ψ z' θ)
        = fun z' => -(Work.Construction.s2 θ / αG) * Work.FTS_StreamBdry.Iint αG Ψ z' θ := by
      funext z'
      rw [Work.FTS_StreamBdry.psiP_eq_Iint]
    rw [Work.Spaces.pz, hfun, deriv_const_mul _ hIdiff, hIderiv]
  rw [hpz, Work.FTS_StreamBdry.psiP_eq_Iint]
  have hαGne : αG ≠ 0 := ne_of_gt hαG
  have hzne : z ≠ 0 := ne_of_gt hz
  field_simp
  ring

end Work.FTS_StreamBdry.SB1
