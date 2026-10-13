import Mathlib.Analysis.InnerProductSpace.Basic
import Mathlib.Analysis.LocallyConvex.AbsConvexOpen
import Mathlib.Analysis.SpecialFunctions.Pow.Deriv
import Mathlib.Topology.Algebra.Module.ModuleTopology
import Submission.Work.FTS_StreamBdry.Basic
import Submission.Work.FTS_StreamBdry.SB25.Defs
import Submission.Work.FTS.StrongPersist.Degen.bslOpZeroOfUopVopZero

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

/-!
# `Work.FTS_StreamBdry.SB25.gaugeMode_facts` — the gauge mode is slot-invisible (C1 of SB2/SB5)

`gaugeMode αG = z^{-3/αG}/cos θ` is the mode left by the level-0 ODE
`αG·D_zΨ + 3Ψ = -s2·U'(Ψ)`; SB1′ shows it is the *only* ambiguity in a stream function, and
SB0 that it is invisible to `Cyl.psiField`.  This file supplies the analytic part of that
statement:

* `contDiffOn_uncurry_gaugeMode` : `uncurry (gaugeMode αG)` is analytic (`C^⊤`) on the open
  quadrant `Qd = (0,∞) × (0,π/2)`;
* `differentiableAt_gaugeMode_z`, `differentiableAt_gaugeMode_θ` : its one-variable slices are
  differentiable in the interior of `Qd`;
* `gaugeMode_facts` : `GaugeModeFacts αG`, i.e. analyticity together with
  `V(gaugeMode αG) = 0` and `L(gaugeMode αG) = bslOp αG (gaugeMode αG) = 0` on `Qd`.

The vanishing of `V` and `U` is proved in `Work.FTS_StreamBdry.Basic` by direct computation
(`Vop_gaugeMode`, `Uop_gaugeMode`); the vanishing of `L` then follows from the *algebraic*
identity `L(Ξ) = α z ∂_z(U Ξ) + 2 U Ξ - ∂_θ(V Ξ)` established in
`Work.FTS.StrongPersist.Degen.bslOpZeroOfUopVopZero`, which needs only the differentiability of
the slices, supplied here.  Concretely, the radial part of `L(gauge)` is `6·gauge` and the
angular part (`Lzero`) is `-6·gauge`, and they cancel.

Note the order of `ContDiffOn ℝ ⊤`: in this Mathlib `⊤ : WithTop ℕ∞ = ω` is the *analytic*
order, so the statement asks for analyticity, not merely `C^∞`
(`contDiffOn_omega_iff_analyticOn`).  Here `z ↦ z^{-3/αG}` is analytic on `z ≠ 0`
(`Real.contDiffAt_rpow_const_of_ne`) and `θ ↦ 1/cos θ` is analytic where `cos θ ≠ 0`.
-/

noncomputable section
open scoped Real Topology NNReal
open Set Filter MeasureTheory

namespace Work.FTS_StreamBdry.SB25

open Work.FTS.StreamBdryIface (Uprime SlotBd SrcOK gaugeMode psiP psiHatP SB5Barrier oddPerS)
open Work.FTS.Galerkin (Fn Fam slice)

set_option autoImplicit false

/-! ## §1 The open quadrant is open -/

lemma qd_isOpen : IsOpen Work.Construction.Qd := by
  rw [Work.Construction.Qd]
  exact isOpen_Ioi.prod isOpen_Ioo

/-! ## §2 Analyticity of the gauge mode on the open quadrant -/

/-- **The gauge mode is analytic on the open quadrant.**  `uncurry (gaugeMode αG)` is
`(z,θ) ↦ z^{-3/αG}/cos θ`, a quotient of an analytic function of `z` on `z ≠ 0` by an analytic
function of `θ` on `cos θ ≠ 0`. -/
theorem contDiffOn_uncurry_gaugeMode (αG : ℝ) :
    ContDiffOn ℝ ⊤ (Function.uncurry (gaugeMode αG)) Work.Construction.Qd := by
  have hfun : Function.uncurry (gaugeMode αG)
      = fun p : ℝ × ℝ => p.1 ^ (-(3 / αG)) / Real.cos p.2 := by
    funext p
    simp only [Function.uncurry, gaugeMode]
  rw [hfun]
  rw [qd_isOpen.contDiffOn_iff]
  rintro ⟨z, θ⟩ hp
  rw [Work.FTS_StreamBdry.mem_Qd] at hp
  obtain ⟨hz, hθ1, hθ2⟩ := hp
  have hzn : z ≠ 0 := ne_of_gt hz
  have hc : Real.cos θ ≠ 0 :=
    ne_of_gt (Work.FTS_StreamBdry.cos_pos_of_Ioo ⟨hθ1, hθ2⟩)
  have h1 : ContDiffAt ℝ ⊤ (fun p : ℝ × ℝ => p.1 ^ (-(3 / αG))) (z, θ) :=
    (Real.contDiffAt_rpow_const_of_ne (x := z) (p := -(3 / αG)) hzn).comp (z, θ)
      contDiffAt_fst
  have h2 : ContDiffAt ℝ ⊤ (fun p : ℝ × ℝ => Real.cos p.2) (z, θ) :=
    (Real.contDiff_cos.contDiffAt).comp (z, θ) contDiffAt_snd
  have h3 : ContDiffAt ℝ ⊤ (fun p : ℝ × ℝ => p.1 ^ (-(3 / αG)) / Real.cos p.2) (z, θ) :=
    h1.div h2 (by simpa using hc)
  exact h3

/-! ## §3 Interior differentiability of the slices

These are the two differentiability hypotheses of `bslOpZeroOfUopVopZero` (its other two
hypotheses — `U = 0` and `V = 0` — are `Uop_gaugeMode`, `Vop_gaugeMode` of
`Work.FTS_StreamBdry.Basic`). -/

lemma differentiableAt_gaugeMode_z {αG z θ : ℝ} (hz : 0 < z) :
    DifferentiableAt ℝ (fun z' => gaugeMode αG z' θ) z := by
  have h : HasDerivAt (fun z' : ℝ => z' ^ (-(3 / αG)))
      ((-(3 / αG)) * z ^ (-(3 / αG) - 1)) z :=
    Real.hasDerivAt_rpow_const (Or.inl (ne_of_gt hz))
  simpa only [gaugeMode] using (h.div_const (Real.cos θ)).differentiableAt

lemma differentiableAt_gaugeMode_θ {αG z θ : ℝ} (hc : Real.cos θ ≠ 0) :
    DifferentiableAt ℝ (fun θ' => gaugeMode αG z θ') θ := by
  have h : DifferentiableAt ℝ (fun θ' : ℝ => (Real.cos θ')⁻¹) θ :=
    Real.differentiableAt_cos.inv hc
  simpa only [gaugeMode, div_eq_mul_inv] using h.const_mul (z ^ (-(3 / αG)))

/-! ## §4 The leaf `gaugeMode_facts` -/

theorem gaugeMode_facts {αG : ℝ} (hαG : 0 < αG) : Work.FTS_StreamBdry.SB25.GaugeModeFacts αG := by
  refine ⟨contDiffOn_uncurry_gaugeMode αG, ?_⟩
  intro z θ hmem
  rw [Work.FTS_StreamBdry.mem_Qd] at hmem
  obtain ⟨hz, hθ1, hθ2⟩ := hmem
  have hc : Real.cos θ ≠ 0 :=
    ne_of_gt (Work.FTS_StreamBdry.cos_pos_of_Ioo ⟨hθ1, hθ2⟩)
  refine ⟨Work.FTS_StreamBdry.Vop_gaugeMode hc, ?_⟩
  exact Work.FTS.StrongPersist.Degen.bslOpZeroOfUopVopZero (Ξ := gaugeMode αG) hαG
    (fun z' θ' hz' _ _ => Work.FTS_StreamBdry.Uop_gaugeMode hαG (ne_of_gt hz'))
    (fun z' θ' _ hθ1' hθ2' => Work.FTS_StreamBdry.Vop_gaugeMode
      (ne_of_gt (Work.FTS_StreamBdry.cos_pos_of_Ioo ⟨hθ1', hθ2'⟩)))
    (fun z' _ hz' _ _ => differentiableAt_gaugeMode_z hz')
    (fun _ θ' _ hθ1' hθ2' => differentiableAt_gaugeMode_θ
      (ne_of_gt (Work.FTS_StreamBdry.cos_pos_of_Ioo ⟨hθ1', hθ2'⟩)))
    z θ hz hθ1 hθ2

end Work.FTS_StreamBdry.SB25
