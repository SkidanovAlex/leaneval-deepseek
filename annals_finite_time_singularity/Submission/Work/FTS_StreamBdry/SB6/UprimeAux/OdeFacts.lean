import Mathlib.Algebra.Order.Star.Real
import Mathlib.Algebra.Ring.IsFormallyReal
import Mathlib.Analysis.Calculus.ContDiff.Defs
import Mathlib.Analysis.Calculus.ContDiff.Deriv
import Mathlib.Analysis.Calculus.ContDiff.FiniteDimension
import Mathlib.Analysis.Calculus.ContDiff.Operations
import Mathlib.Analysis.Calculus.Deriv.Basic
import Mathlib.Analysis.Calculus.Deriv.CompMul
import Mathlib.Analysis.Calculus.Deriv.Mul
import Mathlib.Analysis.Calculus.FDeriv.Extend
import Mathlib.Analysis.Calculus.FDeriv.Partial
import Mathlib.Analysis.Calculus.IteratedDeriv.Lemmas
import Mathlib.Analysis.Calculus.LocalExtr.Basic
import Mathlib.Analysis.Calculus.MeanValue
import Mathlib.Analysis.Calculus.ParametricIntervalIntegral
import Mathlib.Analysis.Complex.Trigonometric
import Mathlib.Analysis.InnerProductSpace.Basic
import Mathlib.Analysis.LocallyConvex.AbsConvexOpen
import Mathlib.Analysis.RCLike.Lemmas
import Mathlib.Analysis.Real.Pi.Bounds
import Mathlib.Analysis.SpecialFunctions.ExpDeriv
import Mathlib.Analysis.SpecialFunctions.Integrability.Basic
import Mathlib.Analysis.SpecialFunctions.Integrals.Basic
import Mathlib.Analysis.SpecialFunctions.Pow.Deriv
import Mathlib.Analysis.SpecialFunctions.Trigonometric.ArctanDeriv
import Mathlib.Analysis.SpecialFunctions.Trigonometric.Basic
import Mathlib.MeasureTheory.Integral.IntervalIntegral.Basic
import Mathlib.MeasureTheory.Integral.IntervalIntegral.FundThmCalculus
import Mathlib.Order.CompletePartialOrder
import Mathlib.RingTheory.Etale.Weakly
import Mathlib.RingTheory.Finiteness.Prod
import Mathlib.RingTheory.Flat.TorsionFree
import Mathlib.RingTheory.TotallySplit
import Mathlib.Topology.Algebra.Module.ModuleTopology
import Mathlib.Topology.GDelta.MetrizableSpace
import Submission.Work.FTS_RegExport.RXR1.HJ.AKBounds
import Submission.Work.FTS_StreamBdry.Basic
import Submission.Work.FTS_StreamBdry.SBpsiP.SelfUprime
import Submission.Work.Spaces.uncurry_partial_c1
import Submission.Work.Stability.mul_rpow_le
-- ===== merged: Submission.Work.FTS_StreamBdry.SB1.psiP_Vop_bnd =====
section

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

/-!
# `Work.FTS_StreamBdry.SB1.psiP_Vop_bnd` — `V(psiP)` is bounded at each fixed `θ` near `z = 0`

`VopPsiPBnd αG M Ψ` says: for every `θ ∈ (0,π/2)` there is `C` with
`|V(psiP αG Ψ) z θ| ≤ C` for all `z ∈ (0,1)`, where `V(Ψ) = ∂_θΨ - tan θ·Ψ`.

This is the "regularity at the origin" input of SB1′ (`sb1_gauge`): the ODE
`αG·D_zP + 3P = -s2·U'(Ψ)` forces `z^{3/αG}(Ψ - psiP)` to be independent of `z`, and its
`θ`-derivative is `z^{3/αG}V(Ψ - psiP)`; the `Ψ`-part is bounded by the slot hypothesis
`SlotBd` (which bounds `V(Ψ)` itself), so the vanishing of `V(psiP)` at a single `z` gives the
`θ`-ODE `c' = tan θ·c` for the constant of integration.

## The proof of the bound

With `I(z,θ) = ∫₀¹ v^{3/αG-1}U'(Ψ)(zv,θ) dv` and `psiP = -(s2 θ/αG)·I`, differentiating under
the integral sign in `θ` (dominated by the *mixed slot* `|sin(2θ)∂_θU'| ≤ M` of `SlotBd`,
which bounds `∂_θU'` on every compact subinterval of `(0,π/2)`) gives

`∂_θ psiP = -(2cos 2θ/αG)·I - (s2 θ/αG)·J`,  `J = ∫₀¹ v^{3/αG-1}∂_θU'(Ψ)(zv,θ) dv`.

Since `|I| ≤ M·αG/3` and `|J| ≤ M·αG/(3 sin 2θ)` (the kernel `v^{3/αG-1}` integrates to
`αG/3` on `(0,1)`), and `tan θ·sin 2θ = 2 sin²θ`, one gets
`|V(psiP)| ≤ 2M/3 + M/3 + 2M/3 = 5M/3` uniformly on `z ∈ (0,1)`.
-/

noncomputable section
open scoped Real Topology
open Set Filter MeasureTheory

namespace Work.FTS_StreamBdry.SB1

open Work.FTS.StreamBdryIface (Uprime SlotBd psiP)

set_option autoImplicit false

/-! ## §0 Elementary helpers -/

private lemma isOpen_QdVB : IsOpen Work.Construction.Qd := isOpen_Ioi.prod isOpen_Ioo

/-- `mixed 0 1 g = D_θ g = sin(2θ)·∂_θg`. -/
private lemma mixed_zero_one_eq_VB (g : ℝ → ℝ → ℝ) (z θ : ℝ) :
    Work.Spaces.mixed 0 1 g z θ = Work.Construction.s2 θ * Work.Spaces.pth g z θ := by
  simp [Work.Spaces.mixed, Work.Spaces.DthIter, Work.Spaces.Dth]

/-- `M ≥ 0` whenever `SlotBd αG Ψ M` holds (evaluate the slot bound at an interior point). -/
private lemma slotM_nonneg_VB {αG M : ℝ} {Ψ : ℝ → ℝ → ℝ} (hslot : SlotBd αG Ψ M) : 0 ≤ M := by
  have h1 : (((1 : ℝ), π / 4) ∈ Work.Construction.Qd) := by
    refine Work.FTS_StreamBdry.mem_Qd.mpr ⟨by norm_num, ?_, ?_⟩ <;> linarith [Real.pi_pos]
  exact le_trans (abs_nonneg _) (Work.FTS_StreamBdry.SlotBd.Uprime_le hslot h1)

/-- The `θ`-partial of a `C¹` function on the open quadrant is continuous on it. -/
private lemma continuousOn_uncurry_pth_of_c1_VB {g : ℝ → ℝ → ℝ}
    (h : ContDiffOn ℝ 1 (Function.uncurry g) Work.Construction.Qd) :
    ContinuousOn (Function.uncurry (Work.Spaces.pth g)) Work.Construction.Qd := by
  have hfd : ContinuousOn (fun p : ℝ × ℝ => fderiv ℝ (Function.uncurry g) p)
      Work.Construction.Qd := h.continuousOn_fderiv_of_isOpen isOpen_QdVB le_rfl
  have h2 : ContinuousOn (fun p : ℝ × ℝ => (fderiv ℝ (Function.uncurry g) p) (0, 1))
      Work.Construction.Qd := hfd.clm_apply continuousOn_const
  refine h2.congr (fun p hp => ?_)
  obtain ⟨z, θ⟩ := p
  exact Work.Spaces.pth_eq_fderiv ((h.differentiableOn (by norm_num)).differentiableAt
    (isOpen_QdVB.mem_nhds hp))

/-- `∫₀¹ v^c dv = 1/(c+1)` for `c > -1`. -/
private lemma rpow_integral_zero_one_VB {c : ℝ} (hc : -1 < c) :
    ∫ v in (0 : ℝ)..1, v ^ c = 1 / (c + 1) := by
  rw [integral_rpow (Or.inl hc), Real.one_rpow, Real.zero_rpow (by linarith : c + 1 ≠ 0)]
  ring

/-- `|∫₀¹ v^c·φ v dv| ≤ B/(c+1)` for `c > -1` and `|φ| ≤ B` on `(0,1]` (with `φ` continuous
there).  The `v = 0` endpoint is measure-zero, so no continuity of `φ` at `0` is needed. -/
private lemma abs_rpow_mul_integral_le_VB {c B : ℝ} (hc : -1 < c)
    {φ : ℝ → ℝ} (hcont : ContinuousOn φ (Set.Ioc (0:ℝ) 1))
    (hφ : ∀ v ∈ Set.Ioc (0:ℝ) 1, |φ v| ≤ B) :
    |∫ v in (0:ℝ)..1, v ^ c * φ v| ≤ B / (c + 1) := by
  have hmaj : IntegrableOn (fun v : ℝ => v ^ c * B) (Set.Ioc (0:ℝ) 1) volume :=
    (intervalIntegrable_iff_integrableOn_Ioc_of_le (by norm_num : (0:ℝ) ≤ 1)).mp
      ((intervalIntegral.intervalIntegrable_rpow' hc (a := (0:ℝ)) (b := 1)).mul_const B)
  have hpowcont : ContinuousOn (fun v : ℝ => v ^ c) (Set.Ioc (0:ℝ) 1) :=
    continuousOn_id.rpow_const (fun v hv => Or.inl (ne_of_gt hv.1))
  have hint : IntegrableOn (fun v : ℝ => v ^ c * φ v) (Set.Ioc (0:ℝ) 1) volume := by
    refine hmaj.mono' ((hpowcont.mul hcont).aestronglyMeasurable measurableSet_Ioc) ?_
    filter_upwards [MeasureTheory.self_mem_ae_restrict measurableSet_Ioc] with v hv
    rw [Real.norm_eq_abs, abs_mul, abs_of_nonneg (Real.rpow_nonneg hv.1.le _)]
    exact mul_le_mul_of_nonneg_left (hφ v hv) (Real.rpow_nonneg hv.1.le _)
  calc |∫ v in (0:ℝ)..1, v ^ c * φ v|
      = |∫ v in Set.Ioc (0:ℝ) 1, v ^ c * φ v| := by
          rw [intervalIntegral.integral_of_le (by norm_num : (0:ℝ) ≤ 1)]
    _ ≤ ∫ v in Set.Ioc (0:ℝ) 1, |v ^ c * φ v| := by
          simpa only [Real.norm_eq_abs] using
            MeasureTheory.norm_integral_le_integral_norm (fun v : ℝ => v ^ c * φ v)
    _ ≤ ∫ v in Set.Ioc (0:ℝ) 1, v ^ c * B := by
          refine integral_mono_ae hint.abs hmaj ?_
          filter_upwards [MeasureTheory.self_mem_ae_restrict measurableSet_Ioc] with v hv
          rw [abs_mul, abs_of_nonneg (Real.rpow_nonneg hv.1.le _)]
          exact mul_le_mul_of_nonneg_left (hφ v hv) (Real.rpow_nonneg hv.1.le _)
    _ = B / (c + 1) := by
          rw [← intervalIntegral.integral_of_le (by norm_num : (0:ℝ) ≤ 1)]
          rw [show (fun v : ℝ => v ^ c * B) = fun v => B * v ^ c from by funext v; ring]
          rw [intervalIntegral.integral_const_mul, rpow_integral_zero_one_VB hc]
          ring

/-! ## §1 The `θ`-derivative of the level-0 integral -/

/-- **Differentiation under the integral sign in `θ`**: the level-0 integral
`∫₀¹ v^{3/αG-1}·U'(Ψ)(zv,θ) dv` is differentiable in `θ` with derivative
`∫₀¹ v^{3/αG-1}·∂_θU'(Ψ)(zv,θ) dv`.

The domination is uniform on the `θ`-neighbourhood `s = (0,π/2) ∩ {s2 θ/2 < s2 ·}` of `θ`
(where `|∂_θU'| ≤ M/(s2 θ/2)` by the mixed slot of `SlotBd`) and by the integrable kernel
`v^{3/αG-1}` (`αG > 0`). -/
private theorem Iint_theta_hasDerivAt_VB {αG M : ℝ} (hαG : 0 < αG) {Ψ : ℝ → ℝ → ℝ}
    (h3 : ContDiffOn ℝ 3 (Function.uncurry Ψ) Work.Construction.Qd)
    (hslot : SlotBd αG Ψ M) :
    ∀ z θ, (z, θ) ∈ Work.Construction.Qd →
      HasDerivAt (fun θ' => Work.FTS_StreamBdry.Iint αG Ψ z θ')
        (∫ v in (0 : ℝ)..1, v ^ (3 / αG - 1) *
          Work.Spaces.pth (Uprime αG Ψ) (z * v) θ) θ := by
  intro z θ hmem
  obtain ⟨hz, hθ0, hθ1⟩ := Work.FTS_StreamBdry.mem_Qd.mp hmem
  have hθmem : θ ∈ Ioo (0 : ℝ) (π / 2) := ⟨hθ0, hθ1⟩
  have hce : (-1 : ℝ) < 3 / αG - 1 := by
    have hp : (0 : ℝ) < 3 / αG := div_pos (by norm_num) hαG
    linarith
  have hM : 0 ≤ M := slotM_nonneg_VB hslot
  have hG1 : ContDiffOn ℝ 1 (Function.uncurry (Uprime αG Ψ)) Work.Construction.Qd :=
    contDiffOn_uncurry_Uprime h3
  have hGc : ContinuousOn (Function.uncurry (Uprime αG Ψ)) Work.Construction.Qd :=
    hG1.continuousOn
  have hpthc : ContinuousOn (Function.uncurry (Work.Spaces.pth (Uprime αG Ψ)))
      Work.Construction.Qd := continuousOn_uncurry_pth_of_c1_VB hG1
  have hGd : ∀ u x, (u, x) ∈ Work.Construction.Qd →
      DifferentiableAt ℝ (Function.uncurry (Uprime αG Ψ)) (u, x) :=
    fun u x h => (hG1.differentiableOn (by norm_num)).differentiableAt (isOpen_QdVB.mem_nhds h)
  have hs2pos : 0 < Work.Construction.s2 θ := Work.FTS_StreamBdry.s2_pos_of_Ioo hθmem
  let s : Set ℝ := Ioo (0 : ℝ) (π / 2) ∩ {x | Work.Construction.s2 θ / 2 < Work.Construction.s2 x}
  have hsnh : s ∈ 𝓝 θ := by
    have hcont : Continuous fun θ' : ℝ => Work.Construction.s2 θ' := by
      rw [show (fun θ' : ℝ => Work.Construction.s2 θ')
          = fun θ' => Real.sin (2 * θ') from by
        funext θ'
        rw [Work.Construction.s2_eq]]
      fun_prop
    exact Filter.inter_mem (isOpen_Ioo.mem_nhds hθmem)
      ((isOpen_lt continuous_const hcont).mem_nhds
        (show Work.Construction.s2 θ / 2 < Work.Construction.s2 θ by linarith))
  have hKs : ∀ x ∈ s, ∀ v ∈ Set.Ioc (0 : ℝ) 1,
      |v ^ (3 / αG - 1) * Work.Spaces.pth (Uprime αG Ψ) (z * v) x| ≤
        v ^ (3 / αG - 1) * (2 * M / Work.Construction.s2 θ) := by
    intro x hx v hv
    have hx1 : 0 < x := hx.1.1
    have hx2 : x < π / 2 := hx.1.2
    have hsxb : Work.Construction.s2 θ / 2 ≤ Work.Construction.s2 x := le_of_lt hx.2
    have hmem2 : (z * v, x) ∈ Work.Construction.Qd :=
      Work.FTS_StreamBdry.mem_Qd.mpr ⟨mul_pos hz hv.1, hx1, hx2⟩
    have hb := Work.FTS_StreamBdry.SlotBd.mixed_le hslot hmem2
    rw [mixed_zero_one_eq_VB] at hb
    have hsxpos : 0 < Work.Construction.s2 x := by linarith [hs2pos, hx.2]
    have h1 : |Work.Spaces.pth (Uprime αG Ψ) (z * v) x| ≤ M / Work.Construction.s2 x := by
      rw [le_div_iff₀ hsxpos]
      rw [mul_comm, ← abs_of_pos hsxpos, ← abs_mul]
      exact hb
    have h2 : M / Work.Construction.s2 x ≤ M / (Work.Construction.s2 θ / 2) :=
      div_le_div_of_nonneg_left hM (by linarith [hs2pos] : (0 : ℝ) < Work.Construction.s2 θ / 2)
        hsxb
    have h3 : |Work.Spaces.pth (Uprime αG Ψ) (z * v) x|
        ≤ 2 * M / Work.Construction.s2 θ := by
      refine h1.trans (h2.trans ?_)
      rw [div_div_eq_mul_div]
      exact le_of_eq (by ring)
    have hvnn : (0 : ℝ) ≤ v ^ (3 / αG - 1) := Real.rpow_nonneg hv.1.le _
    rw [abs_mul, abs_of_nonneg hvnn]
    exact mul_le_mul_of_nonneg_left h3 hvnn
  have hF_meas : ∀ᶠ x in 𝓝 θ, AEStronglyMeasurable
      (fun v : ℝ => v ^ (3 / αG - 1) * Uprime αG Ψ (z * v) x)
      (volume.restrict (Set.uIoc (0 : ℝ) 1)) := by
    filter_upwards [hsnh] with x hx
    have hcont1 : ContinuousOn (fun v : ℝ => v ^ (3 / αG - 1)) (Ioo (0 : ℝ) 2) :=
      continuousOn_id.rpow_const (fun v hv => Or.inl (ne_of_gt hv.1))
    have hcont2 : ContinuousOn (fun v : ℝ => Uprime αG Ψ (z * v) x) (Ioo (0 : ℝ) 2) :=
      (Work.FTS_StreamBdry.SB3.continuousOn_scaled_slice hGc hz hx.1).mono (fun v hv => hv.1)
    have hcont : ContinuousOn (fun v : ℝ => v ^ (3 / αG - 1) * Uprime αG Ψ (z * v) x)
        (Ioo (0 : ℝ) 2) := hcont1.mul hcont2
    have hcontIoc : ContinuousOn (fun v : ℝ => v ^ (3 / αG - 1) * Uprime αG Ψ (z * v) x)
        (Ioc (0 : ℝ) 1) := hcont.mono (fun v hv => ⟨hv.1, by linarith [hv.2]⟩)
    have hmeas : AEStronglyMeasurable (fun v : ℝ => v ^ (3 / αG - 1) * Uprime αG Ψ (z * v) x)
        (volume.restrict (Ioc (0 : ℝ) 1)) := hcontIoc.aestronglyMeasurable measurableSet_Ioc
    simpa only [Set.uIoc_of_le (show (0 : ℝ) ≤ 1 by norm_num)] using hmeas
  have hF_int : IntervalIntegrable
      (fun v : ℝ => v ^ (3 / αG - 1) * Uprime αG Ψ (z * v) θ) volume (0 : ℝ) 1 := by
    rw [intervalIntegrable_iff_integrableOn_Ioc_of_le (show (0 : ℝ) ≤ 1 by norm_num)]
    have hcont1 : ContinuousOn (fun v : ℝ => v ^ (3 / αG - 1)) (Ioo (0 : ℝ) 2) :=
      continuousOn_id.rpow_const (fun v hv => Or.inl (ne_of_gt hv.1))
    have hcont2 : ContinuousOn (fun v : ℝ => Uprime αG Ψ (z * v) θ) (Ioo (0 : ℝ) 2) :=
      (Work.FTS_StreamBdry.SB3.continuousOn_scaled_slice hGc hz hθmem).mono (fun v hv => hv.1)
    have hcont : ContinuousOn (fun v : ℝ => v ^ (3 / αG - 1) * Uprime αG Ψ (z * v) θ)
        (Ioo (0 : ℝ) 2) := hcont1.mul hcont2
    have hcontIoc : ContinuousOn (fun v : ℝ => v ^ (3 / αG - 1) * Uprime αG Ψ (z * v) θ)
        (Ioc (0 : ℝ) 1) := hcont.mono (fun v hv => ⟨hv.1, by linarith [hv.2]⟩)
    have hmeas : AEStronglyMeasurable
        (fun v : ℝ => v ^ (3 / αG - 1) * Uprime αG Ψ (z * v) θ)
        (volume.restrict (Ioc (0 : ℝ) 1)) := hcontIoc.aestronglyMeasurable measurableSet_Ioc
    have hg : IntegrableOn (fun v : ℝ => v ^ (3 / αG - 1) * M) (Ioc (0 : ℝ) 1) volume :=
      (intervalIntegrable_iff_integrableOn_Ioc_of_le (show (0 : ℝ) ≤ 1 by norm_num)).mp
        ((intervalIntegral.intervalIntegrable_rpow' hce (a := (0 : ℝ)) (b := 1)).mul_const M)
    refine hg.mono' hmeas ?_
    rw [ae_restrict_iff' measurableSet_Ioc]
    refine Filter.Eventually.of_forall (fun v hv => ?_)
    have hmem2 : (z * v, θ) ∈ Work.Construction.Qd :=
      Work.FTS_StreamBdry.mem_Qd.mpr ⟨mul_pos hz hv.1, hθ0, hθ1⟩
    have hb := Work.FTS_StreamBdry.SlotBd.Uprime_le hslot hmem2
    rw [Real.norm_eq_abs, abs_mul, abs_of_nonneg (Real.rpow_nonneg hv.1.le _)]
    exact mul_le_mul_of_nonneg_left hb (Real.rpow_nonneg hv.1.le _)
  have hF'_meas : AEStronglyMeasurable
      (fun v : ℝ => v ^ (3 / αG - 1) * Work.Spaces.pth (Uprime αG Ψ) (z * v) θ)
      (volume.restrict (Set.uIoc (0 : ℝ) 1)) := by
    have hcont1 : ContinuousOn (fun v : ℝ => v ^ (3 / αG - 1)) (Ioo (0 : ℝ) 2) :=
      continuousOn_id.rpow_const (fun v hv => Or.inl (ne_of_gt hv.1))
    have hcont2 : ContinuousOn (fun v : ℝ => Work.Spaces.pth (Uprime αG Ψ) (z * v) θ)
        (Ioo (0 : ℝ) 2) :=
      (Work.FTS_StreamBdry.SB3.continuousOn_scaled_slice hpthc hz hθmem).mono (fun v hv => hv.1)
    have hcont : ContinuousOn
        (fun v : ℝ => v ^ (3 / αG - 1) * Work.Spaces.pth (Uprime αG Ψ) (z * v) θ)
        (Ioo (0 : ℝ) 2) := hcont1.mul hcont2
    have hcontIoc : ContinuousOn
        (fun v : ℝ => v ^ (3 / αG - 1) * Work.Spaces.pth (Uprime αG Ψ) (z * v) θ)
        (Ioc (0 : ℝ) 1) := hcont.mono (fun v hv => ⟨hv.1, by linarith [hv.2]⟩)
    have hmeas : AEStronglyMeasurable
        (fun v : ℝ => v ^ (3 / αG - 1) * Work.Spaces.pth (Uprime αG Ψ) (z * v) θ)
        (volume.restrict (Ioc (0 : ℝ) 1)) := hcontIoc.aestronglyMeasurable measurableSet_Ioc
    simpa only [Set.uIoc_of_le (show (0 : ℝ) ≤ 1 by norm_num)] using hmeas
  have h_bound : ∀ᵐ t ∂volume, t ∈ Set.uIoc (0 : ℝ) 1 → ∀ x ∈ s,
      ‖(fun x v => v ^ (3 / αG - 1) * Work.Spaces.pth (Uprime αG Ψ) (z * v) x) x t‖ ≤
        (fun v => v ^ (3 / αG - 1) * (2 * M / Work.Construction.s2 θ)) t := by
    refine Filter.Eventually.of_forall (fun t ht x hx => ?_)
    rw [Set.uIoc_of_le (show (0 : ℝ) ≤ 1 by norm_num)] at ht
    simpa only [Real.norm_eq_abs] using hKs x hx t ht
  have hbound_int : IntervalIntegrable
      (fun v : ℝ => v ^ (3 / αG - 1) * (2 * M / Work.Construction.s2 θ)) volume (0 : ℝ) 1 :=
    (intervalIntegral.intervalIntegrable_rpow' hce (a := (0 : ℝ)) (b := 1)).mul_const _
  have h_diff : ∀ᵐ t ∂volume, t ∈ Set.uIoc (0 : ℝ) 1 → ∀ x ∈ s,
      HasDerivAt (fun x' => t ^ (3 / αG - 1) * Uprime αG Ψ (z * t) x')
        (t ^ (3 / αG - 1) * Work.Spaces.pth (Uprime αG Ψ) (z * t) x) x := by
    refine Filter.Eventually.of_forall (fun t ht x hx => ?_)
    rw [Set.uIoc_of_le (show (0 : ℝ) ≤ 1 by norm_num)] at ht
    have hmem2 : (z * t, x) ∈ Work.Construction.Qd :=
      Work.FTS_StreamBdry.mem_Qd.mpr ⟨mul_pos hz ht.1, hx.1.1, hx.1.2⟩
    have hd : DifferentiableAt ℝ (Function.uncurry (Uprime αG Ψ)) (z * t, x) :=
      hGd (z * t) x hmem2
    have hcurve : HasDerivAt (fun x' : ℝ => (z * t, x')) (0, 1) x :=
      (hasDerivAt_const x (z * t)).prodMk (hasDerivAt_id x)
    have h1 : HasDerivAt (fun x' : ℝ => Function.uncurry (Uprime αG Ψ) (z * t, x'))
        (fderiv ℝ (Function.uncurry (Uprime αG Ψ)) (z * t, x) (0, 1)) x :=
      hd.hasFDerivAt.comp_hasDerivAt x hcurve
    rw [Work.Spaces.pth_eq_fderiv hd]
    exact h1.const_mul _
  exact (intervalIntegral.hasDerivAt_integral_of_dominated_loc_of_deriv_le
    (F := fun x v => v ^ (3 / αG - 1) * Uprime αG Ψ (z * v) x)
    (F' := fun x v => v ^ (3 / αG - 1) * Work.Spaces.pth (Uprime αG Ψ) (z * v) x)
    (x₀ := θ) (s := s)
    (bound := fun v => v ^ (3 / αG - 1) * (2 * M / Work.Construction.s2 θ))
    (μ := volume) (a := (0 : ℝ)) (b := 1)
    hsnh hF_meas hF_int hF'_meas h_bound hbound_int h_diff).2

/-- **The `θ`-derivative of `psiP`**: the product rule on `-(s2 θ/αG)·I(z,θ)`. -/
private theorem psiP_pth_eq_VB {αG M : ℝ} (hαG : 0 < αG) {Ψ : ℝ → ℝ → ℝ}
    (h3 : ContDiffOn ℝ 3 (Function.uncurry Ψ) Work.Construction.Qd)
    (hslot : SlotBd αG Ψ M) :
    ∀ z θ, (z, θ) ∈ Work.Construction.Qd →
      Work.Spaces.pth (psiP αG Ψ) z θ
        = -(2 * Real.cos (2 * θ) / αG) * Work.FTS_StreamBdry.Iint αG Ψ z θ
          - (Work.Construction.s2 θ / αG) *
            ∫ v in (0 : ℝ)..1, v ^ (3 / αG - 1) *
              Work.Spaces.pth (Uprime αG Ψ) (z * v) θ := by
  intro z θ hmem
  have hI := Iint_theta_hasDerivAt_VB hαG h3 hslot z θ hmem
  have hs2 : HasDerivAt (fun θ' : ℝ => Work.Construction.s2 θ')
      (Real.cos (2 * θ) * 2) θ := by
    have h2 : HasDerivAt (fun θ' : ℝ => (2:ℝ) * θ') (2:ℝ) θ := by
      have h : HasDerivAt (fun θ' : ℝ => (2:ℝ) * θ') (2 * 1) θ :=
        (hasDerivAt_id θ).const_mul (2:ℝ)
      simpa using h
    have h3' : HasDerivAt (fun θ' : ℝ => Real.sin (2 * θ')) (Real.cos (2 * θ) * 2) θ :=
      (Real.hasDerivAt_sin (2 * θ)).comp θ h2
    exact h3'
  have hd : HasDerivAt (fun θ' : ℝ => -(Work.Construction.s2 θ' / αG))
      (-(Real.cos (2 * θ) * 2 / αG)) θ := (hs2.div_const αG).neg
  have hprod := hd.mul hI
  have hfun : (fun θ' => psiP αG Ψ z θ')
      = fun θ' => -(Work.Construction.s2 θ' / αG) * Work.FTS_StreamBdry.Iint αG Ψ z θ' := by
    funext θ'
    rw [Work.FTS_StreamBdry.psiP_eq_Iint]
  rw [Work.Spaces.pth, hfun]
  rw [show (fun θ' => -(Work.Construction.s2 θ' / αG) * Work.FTS_StreamBdry.Iint αG Ψ z θ')
      = (fun θ' => -(Work.Construction.s2 θ' / αG)) *
        (fun θ' => Work.FTS_StreamBdry.Iint αG Ψ z θ') from rfl]
  rw [hprod.deriv]
  ring

/-! ## §2 The target -/

theorem psiP_Vop_bnd {αG M : ℝ} (hαG : 0 < αG) {Ψ : ℝ → ℝ → ℝ}
    (h3 : ContDiffOn ℝ 3 (Function.uncurry Ψ) Work.Construction.Qd)
    (hslot : Work.FTS.StreamBdryIface.SlotBd αG Ψ M) :
    Work.FTS_StreamBdry.VopPsiPBnd αG M Ψ := by
  intro θ hθmem
  have hθ0 : 0 < θ := hθmem.1
  have hθ1 : θ < π / 2 := hθmem.2
  have hs2pos : 0 < Work.Construction.s2 θ := Work.FTS_StreamBdry.s2_pos_of_Ioo hθmem
  have hcos : 0 < Real.cos θ := Work.FTS_StreamBdry.cos_pos_of_Ioo hθmem
  have hsin : 0 < Real.sin θ := Real.sin_pos_of_pos_of_lt_pi hθ0 (by linarith [Real.pi_pos])
  have hM : 0 ≤ M := slotM_nonneg_VB hslot
  have hGc : ContinuousOn (Function.uncurry (Uprime αG Ψ)) Work.Construction.Qd :=
    (contDiffOn_uncurry_Uprime h3).continuousOn
  have hpthc : ContinuousOn (Function.uncurry (Work.Spaces.pth (Uprime αG Ψ)))
      Work.Construction.Qd := continuousOn_uncurry_pth_of_c1_VB (contDiffOn_uncurry_Uprime h3)
  have hc : (-1 : ℝ) < 3 / αG - 1 := by
    have : (0 : ℝ) < 3 / αG := div_pos (by norm_num) hαG
    linarith
  refine ⟨5 * M / 3 + 1, fun z hz => ?_⟩
  obtain ⟨hz0, hz1⟩ := hz
  have hmem : (z, θ) ∈ Work.Construction.Qd :=
    Work.FTS_StreamBdry.mem_Qd.mpr ⟨hz0, hθ0, hθ1⟩
  have hpos : (0 : ℝ) ≤ Work.Construction.s2 θ / αG :=
    div_nonneg (le_of_lt hs2pos) (le_of_lt hαG)
  have hIc : |Work.FTS_StreamBdry.Iint αG Ψ z θ| ≤ M * αG / 3 := by
    have hcont : ContinuousOn (fun v : ℝ => Uprime αG Ψ (z * v) θ) (Set.Ioc (0:ℝ) 1) :=
      (Work.FTS_StreamBdry.SB3.continuousOn_scaled_slice hGc hz0 hθmem).mono
        (fun v hv => hv.1)
    have hφ : ∀ v ∈ Set.Ioc (0:ℝ) 1, |Uprime αG Ψ (z * v) θ| ≤ M := fun v hv =>
      Work.FTS_StreamBdry.SlotBd.Uprime_le hslot
        (Work.FTS_StreamBdry.mem_Qd.mpr ⟨mul_pos hz0 hv.1, hθ0, hθ1⟩)
    have h := abs_rpow_mul_integral_le_VB (c := 3 / αG - 1) (B := M) hc hcont hφ
    change |∫ v in (0:ℝ)..1, v ^ (3 / αG - 1) * Uprime αG Ψ (z * v) θ| ≤ M * αG / 3
    have hkey : M / (3 / αG - 1 + 1) = M * αG / 3 := by
      field_simp
      ring
    linarith [h, hkey]
  have hJc : |∫ v in (0:ℝ)..1, v ^ (3 / αG - 1) *
        Work.Spaces.pth (Uprime αG Ψ) (z * v) θ|
      ≤ M * αG / (3 * Work.Construction.s2 θ) := by
    have hcont : ContinuousOn (fun v : ℝ => Work.Spaces.pth (Uprime αG Ψ) (z * v) θ)
        (Set.Ioc (0:ℝ) 1) :=
      (Work.FTS_StreamBdry.SB3.continuousOn_scaled_slice hpthc hz0 hθmem).mono
        (fun v hv => hv.1)
    have hφ : ∀ v ∈ Set.Ioc (0:ℝ) 1,
        |Work.Spaces.pth (Uprime αG Ψ) (z * v) θ| ≤ M / Work.Construction.s2 θ := by
      intro v hv
      have hmem2 : (z * v, θ) ∈ Work.Construction.Qd :=
        Work.FTS_StreamBdry.mem_Qd.mpr ⟨mul_pos hz0 hv.1, hθ0, hθ1⟩
      have hb := Work.FTS_StreamBdry.SlotBd.mixed_le hslot hmem2
      rw [mixed_zero_one_eq_VB] at hb
      rw [le_div_iff₀ hs2pos, mul_comm, ← abs_of_pos hs2pos, ← abs_mul]
      exact hb
    have h := abs_rpow_mul_integral_le_VB (c := 3 / αG - 1)
      (B := M / Work.Construction.s2 θ) hc hcont hφ
    have hkey : (M / Work.Construction.s2 θ) / (3 / αG - 1 + 1)
        = M * αG / (3 * Work.Construction.s2 θ) := by
      field_simp
      ring
    linarith [h, hkey]
  have hpsi : |psiP αG Ψ z θ| ≤ M * Work.Construction.s2 θ / 3 := by
    rw [Work.FTS_StreamBdry.psiP_eq_Iint, abs_mul, abs_neg, abs_of_nonneg hpos]
    calc Work.Construction.s2 θ / αG * |Work.FTS_StreamBdry.Iint αG Ψ z θ|
        ≤ Work.Construction.s2 θ / αG * (M * αG / 3) :=
          mul_le_mul_of_nonneg_left hIc hpos
      _ = M * Work.Construction.s2 θ / 3 := by
          field_simp
  have hIpiece : |-(2 * Real.cos (2 * θ) / αG) * Work.FTS_StreamBdry.Iint αG Ψ z θ|
      ≤ 2 * M / 3 := by
    have h1 : |-(2 * Real.cos (2 * θ) / αG)| = 2 * |Real.cos (2 * θ)| / αG := by
      rw [abs_neg, abs_div, abs_mul, abs_of_pos hαG, abs_of_pos (by norm_num : (0:ℝ) < 2)]
    rw [abs_mul, h1]
    have h2 : 2 * |Real.cos (2 * θ)| / αG ≤ 2 / αG := by
      have hcl := Real.abs_cos_le_one (2 * θ)
      gcongr
      linarith
    have h3 : 2 * |Real.cos (2 * θ)| / αG * |Work.FTS_StreamBdry.Iint αG Ψ z θ|
        ≤ 2 / αG * (M * αG / 3) :=
      mul_le_mul h2 hIc (abs_nonneg _) (by positivity)
    have h4 : 2 / αG * (M * αG / 3) = 2 * M / 3 := by
      field_simp
    linarith [h3, h4]
  have hJpiece : |(Work.Construction.s2 θ / αG) *
        (∫ v in (0:ℝ)..1, v ^ (3 / αG - 1) * Work.Spaces.pth (Uprime αG Ψ) (z * v) θ)|
      ≤ M / 3 := by
    rw [abs_mul, abs_of_nonneg hpos]
    calc Work.Construction.s2 θ / αG *
          |∫ v in (0:ℝ)..1, v ^ (3 / αG - 1) * Work.Spaces.pth (Uprime αG Ψ) (z * v) θ|
        ≤ Work.Construction.s2 θ / αG * (M * αG / (3 * Work.Construction.s2 θ)) :=
          mul_le_mul_of_nonneg_left hJc hpos
      _ = M / 3 := by
          field_simp
  have hpth_bd : |Work.Spaces.pth (psiP αG Ψ) z θ| ≤ 2 * M / 3 + M / 3 := by
    rw [psiP_pth_eq_VB hαG h3 hslot z θ hmem]
    calc |-(2 * Real.cos (2 * θ) / αG) * Work.FTS_StreamBdry.Iint αG Ψ z θ
            - (Work.Construction.s2 θ / αG) *
              (∫ v in (0:ℝ)..1, v ^ (3 / αG - 1) *
                Work.Spaces.pth (Uprime αG Ψ) (z * v) θ)|
        ≤ |-(2 * Real.cos (2 * θ) / αG) * Work.FTS_StreamBdry.Iint αG Ψ z θ|
          + |(Work.Construction.s2 θ / αG) *
              (∫ v in (0:ℝ)..1, v ^ (3 / αG - 1) *
                Work.Spaces.pth (Uprime αG Ψ) (z * v) θ)| := by
          rw [sub_eq_add_neg]
          exact (abs_add_le _ _).trans (le_of_eq (by rw [abs_neg]))
      _ ≤ 2 * M / 3 + M / 3 := add_le_add hIpiece hJpiece
  have htanbd : |Real.tan θ| * |psiP αG Ψ z θ| ≤ 2 * M / 3 := by
    have htan_abs : |Real.tan θ| = Real.sin θ / Real.cos θ := by
      rw [Real.tan_eq_sin_div_cos,
        abs_of_nonneg (div_nonneg (le_of_lt hsin) (le_of_lt hcos))]
    calc |Real.tan θ| * |psiP αG Ψ z θ|
        = Real.sin θ / Real.cos θ * |psiP αG Ψ z θ| := by rw [htan_abs]
      _ ≤ Real.sin θ / Real.cos θ * (M * Work.Construction.s2 θ / 3) :=
          mul_le_mul_of_nonneg_left hpsi (div_nonneg (le_of_lt hsin) (le_of_lt hcos))
      _ = 2 * M * Real.sin θ ^ 2 / 3 := by
          rw [Work.FTS_StreamBdry.s2_eq_two_sin_cos]
          field_simp
      _ ≤ 2 * M / 3 := by
          have hsin2 : Real.sin θ ^ 2 ≤ 1 := by
            nlinarith [Real.sin_le_one θ, le_of_lt hsin]
          nlinarith [hM, hsin2]
  show |Work.Construction.Vop (psiP αG Ψ) z θ| ≤ 5 * M / 3 + 1
  rw [Work.Construction.Vop]
  calc |Work.Spaces.pth (psiP αG Ψ) z θ - Real.tan θ * psiP αG Ψ z θ|
      ≤ |Work.Spaces.pth (psiP αG Ψ) z θ| + |Real.tan θ * psiP αG Ψ z θ| := by
        simpa [sub_eq_add_neg] using (abs_add_le (Work.Spaces.pth (psiP αG Ψ) z θ)
          (-(Real.tan θ * psiP αG Ψ z θ)))
    _ = |Work.Spaces.pth (psiP αG Ψ) z θ| + |Real.tan θ| * |psiP αG Ψ z θ| := by rw [abs_mul]
    _ ≤ (2 * M / 3 + M / 3) + 2 * M / 3 := add_le_add hpth_bd htanbd
    _ ≤ 5 * M / 3 + 1 := by linarith

end Work.FTS_StreamBdry.SB1
end
end
-- ===== merged: Submission.Work.FTS_StreamBdry.SB1.psiP_diff =====
section

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

/-!
# `Work.FTS_StreamBdry.SB1.psiP_diff` — differentiability of the level-0 `U`-slot part

`psiP αG Ψ = -(s2/αG)·∫₀¹ v^{3/αG-1}·U'(Ψ)(zv,θ) dv` is differentiable in each variable on the
open quadrant `Qd = (0,∞) × (0,π/2)`, which is the engine hypothesis `PsiPDiff` consumed by
`SB1/Engine.lean` (`sb1_gauge`: the constant of integration is `κ/cos θ`).

## Route

* **the `z`-derivative** is the FTC/scaling computation of `rpow_ode_aux` (`SB1/psiP_ode`): for
  fixed `θ` the slice `u ↦ U'(Ψ)(u,θ)` is continuous on `(0,z+1)` and bounded by `M`
  (`SlotBd.Uprime_le`), so `z ↦ ∫₀¹ v^{3/αG-1}U'(Ψ)(zv,θ) dv` has a derivative at `z`; the
  constant factor `-(s2 θ/αG)` is pulled out.
* **the `θ`-derivative** is differentiation under the integral sign
  (`intervalIntegral.hasDerivAt_integral_of_dominated_loc_of_deriv_le`).  The slot `U'(Ψ)` is `C¹`
  on `Qd` (`contDiffOn_uncurry_Uprime`), so each slice `θ' ↦ U'(Ψ)(zv,θ')` is differentiable with
  derivative `∂_θU'(Ψ)(zv,θ')` (`pth_eq_fderiv`); the domination comes from the *mixed* slot of
  `SlotBd`: `|sin(2θ)·∂_θU'| ≤ M` bounds `∂_θU'` on the θ-neighbourhood
  `{x : sin(2θ)/2 < sin(2x)} ∩ (0,π/2)` of `θ` by `2M/sin(2θ)`, and the majorant
  `v^{3/αG-1}·2M/sin(2θ)` is interval-integrable on `(0,1]` because `αG > 0` gives
  `3/αG - 1 > -1`.
-/

noncomputable section
open scoped Real Topology
open Set Filter MeasureTheory

namespace Work.FTS_StreamBdry.SB1

open Work.FTS.StreamBdryIface (Uprime SlotBd psiP)

set_option autoImplicit false

/-! ## §0 Helpers -/

private lemma isOpen_QdPS : IsOpen Work.Construction.Qd := isOpen_Ioi.prod isOpen_Ioo

/-- `mixed 0 1 g = sin(2θ)·∂_θg`. -/
private lemma mixed_zero_one_eq (g : ℝ → ℝ → ℝ) (z θ : ℝ) :
    Work.Spaces.mixed 0 1 g z θ = Work.Construction.s2 θ * Work.Spaces.pth g z θ := by
  simp [Work.Spaces.mixed, Work.Spaces.DthIter, Work.Spaces.Dth]

/-- `M ≥ 0` whenever `SlotBd αG Ψ M` holds (evaluate the slot bound at an interior point). -/
private lemma slotM_nonneg {αG M : ℝ} {Ψ : ℝ → ℝ → ℝ} (hslot : SlotBd αG Ψ M) : 0 ≤ M := by
  have h1 : (((1 : ℝ), π / 4) ∈ Work.Construction.Qd) := by
    refine mem_Qd.mpr ⟨by norm_num, ?_, ?_⟩ <;> linarith [Real.pi_pos]
  exact le_trans (abs_nonneg _) (SlotBd.Uprime_le hslot h1)

/-- The `θ`-partial of a `C¹` function on the open quadrant is continuous on it. -/
private lemma continuousOn_uncurry_pth_of_c1 {g : ℝ → ℝ → ℝ}
    (h : ContDiffOn ℝ 1 (Function.uncurry g) Work.Construction.Qd) :
    ContinuousOn (Function.uncurry (Work.Spaces.pth g)) Work.Construction.Qd := by
  have hfd : ContinuousOn (fun p : ℝ × ℝ => fderiv ℝ (Function.uncurry g) p)
      Work.Construction.Qd := h.continuousOn_fderiv_of_isOpen isOpen_QdPS le_rfl
  have h2 : ContinuousOn (fun p : ℝ × ℝ => (fderiv ℝ (Function.uncurry g) p) (0, 1))
      Work.Construction.Qd := hfd.clm_apply continuousOn_const
  refine h2.congr (fun p hp => ?_)
  obtain ⟨z, θ⟩ := p
  exact Work.Spaces.pth_eq_fderiv ((h.differentiableOn (by norm_num)).differentiableAt
    (isOpen_QdPS.mem_nhds hp))

/-- Continuity of the `v`-slice `v ↦ g (x v) θ` for `x > 0`, `θ ∈ (0,π/2)`. -/
private lemma continuousOn_scaled_slice' {g : ℝ → ℝ → ℝ}
    (hg : ContinuousOn (Function.uncurry g) Work.Construction.Qd) {x : ℝ} (hx : 0 < x)
    {θ : ℝ} (hθ : θ ∈ Ioo (0 : ℝ) (π / 2)) :
    ContinuousOn (fun v => g (x * v) θ) (Ioi 0) :=
  Work.FTS_StreamBdry.SB3.continuousOn_scaled_slice hg hx hθ

/-! ## §1 The `θ`-derivative of the level-0 integral -/

/-- **Differentiation under the integral sign in `θ`**: the level-0 integral
`∫₀¹ v^{3/αG-1}·U'(Ψ)(zv,θ) dv` is differentiable in `θ` with derivative
`∫₀¹ v^{3/αG-1}·∂_θU'(Ψ)(zv,θ) dv`. -/
private theorem Iint_theta_hasDerivAt {αG M : ℝ} (hαG : 0 < αG) {Ψ : ℝ → ℝ → ℝ}
    (h3 : ContDiffOn ℝ 3 (Function.uncurry Ψ) Work.Construction.Qd)
    (hslot : SlotBd αG Ψ M) :
    ∀ z θ, (z, θ) ∈ Work.Construction.Qd →
      HasDerivAt (fun θ' => Work.FTS_StreamBdry.Iint αG Ψ z θ')
        (∫ v in (0 : ℝ)..1, v ^ (3 / αG - 1) *
          Work.Spaces.pth (Uprime αG Ψ) (z * v) θ) θ := by
  intro z θ hmem
  obtain ⟨hz, hθ0, hθ1⟩ := mem_Qd.mp hmem
  have hθmem : θ ∈ Ioo (0 : ℝ) (π / 2) := ⟨hθ0, hθ1⟩
  have hce : (-1 : ℝ) < 3 / αG - 1 := by
    have hp : (0 : ℝ) < 3 / αG := div_pos (by norm_num) hαG
    linarith
  have hM : 0 ≤ M := slotM_nonneg hslot
  have hG1 : ContDiffOn ℝ 1 (Function.uncurry (Uprime αG Ψ)) Work.Construction.Qd :=
    contDiffOn_uncurry_Uprime h3
  have hGc : ContinuousOn (Function.uncurry (Uprime αG Ψ)) Work.Construction.Qd :=
    hG1.continuousOn
  have hpthc : ContinuousOn (Function.uncurry (Work.Spaces.pth (Uprime αG Ψ)))
      Work.Construction.Qd := continuousOn_uncurry_pth_of_c1 hG1
  have hGd : ∀ u x, (u, x) ∈ Work.Construction.Qd →
      DifferentiableAt ℝ (Function.uncurry (Uprime αG Ψ)) (u, x) :=
    fun u x h => (hG1.differentiableOn (by norm_num)).differentiableAt (isOpen_QdPS.mem_nhds h)
  -- the `θ`-neighbourhood on which `∂_θU'` is controlled by `M`
  have hs2pos : 0 < Work.Construction.s2 θ := s2_pos_of_Ioo hθmem
  let s : Set ℝ := Ioo (0 : ℝ) (π / 2) ∩
    {x | Work.Construction.s2 θ / 2 < Work.Construction.s2 x}
  have hsnh : s ∈ 𝓝 θ := by
    have hcont : Continuous fun θ' : ℝ => Work.Construction.s2 θ' := by
      rw [show (fun θ' : ℝ => Work.Construction.s2 θ')
          = fun θ' => Real.sin (2 * θ') from by
        funext θ'
        rw [Work.Construction.s2_eq]]
      fun_prop
    exact Filter.inter_mem (isOpen_Ioo.mem_nhds hθmem)
      ((isOpen_lt continuous_const hcont).mem_nhds
        (show Work.Construction.s2 θ / 2 < Work.Construction.s2 θ by linarith))
  -- the uniform bound on the derivative
  have hKs : ∀ x ∈ s, ∀ v ∈ Set.Ioc (0 : ℝ) 1,
      |v ^ (3 / αG - 1) * Work.Spaces.pth (Uprime αG Ψ) (z * v) x| ≤
        v ^ (3 / αG - 1) * (2 * M / Work.Construction.s2 θ) := by
    intro x hx v hv
    have hx1 : 0 < x := hx.1.1
    have hx2 : x < π / 2 := hx.1.2
    have hsxb : Work.Construction.s2 θ / 2 ≤ Work.Construction.s2 x := le_of_lt hx.2
    have hmem2 : (z * v, x) ∈ Work.Construction.Qd :=
      mem_Qd.mpr ⟨mul_pos hz hv.1, hx1, hx2⟩
    have hb := SlotBd.mixed_le hslot hmem2
    rw [mixed_zero_one_eq] at hb
    have hsxpos : 0 < Work.Construction.s2 x := by linarith [hs2pos, hx.2]
    have h1 : |Work.Spaces.pth (Uprime αG Ψ) (z * v) x| ≤ M / Work.Construction.s2 x := by
      rw [le_div_iff₀ hsxpos]
      rw [mul_comm, ← abs_of_pos hsxpos, ← abs_mul]
      exact hb
    have h2 : M / Work.Construction.s2 x ≤ M / (Work.Construction.s2 θ / 2) :=
      div_le_div_of_nonneg_left hM (by linarith [hs2pos] : (0 : ℝ) < Work.Construction.s2 θ / 2)
        hsxb
    have h3 : |Work.Spaces.pth (Uprime αG Ψ) (z * v) x|
        ≤ 2 * M / Work.Construction.s2 θ := by
      refine h1.trans (h2.trans ?_)
      rw [div_div_eq_mul_div]
      exact le_of_eq (by ring)
    have hvnn : (0 : ℝ) ≤ v ^ (3 / αG - 1) := Real.rpow_nonneg hv.1.le _
    rw [abs_mul, abs_of_nonneg hvnn]
    exact mul_le_mul_of_nonneg_left h3 hvnn
  -- measurability of `F x`
  have hF_meas : ∀ᶠ x in 𝓝 θ, AEStronglyMeasurable
      (fun v : ℝ => v ^ (3 / αG - 1) * Uprime αG Ψ (z * v) x)
      (volume.restrict (Set.uIoc (0 : ℝ) 1)) := by
    filter_upwards [hsnh] with x hx
    have hcont1 : ContinuousOn (fun v : ℝ => v ^ (3 / αG - 1)) (Ioo (0 : ℝ) 2) :=
      continuousOn_id.rpow_const (fun v hv => Or.inl (ne_of_gt hv.1))
    have hcont2 : ContinuousOn (fun v : ℝ => Uprime αG Ψ (z * v) x) (Ioo (0 : ℝ) 2) :=
      (continuousOn_scaled_slice' hGc hz hx.1).mono (fun v hv => hv.1)
    have hcont : ContinuousOn (fun v : ℝ => v ^ (3 / αG - 1) * Uprime αG Ψ (z * v) x)
        (Ioo (0 : ℝ) 2) := hcont1.mul hcont2
    have hcontIoc : ContinuousOn (fun v : ℝ => v ^ (3 / αG - 1) * Uprime αG Ψ (z * v) x)
        (Ioc (0 : ℝ) 1) := hcont.mono (fun v hv => ⟨hv.1, by linarith [hv.2]⟩)
    have hmeas : AEStronglyMeasurable (fun v : ℝ => v ^ (3 / αG - 1) * Uprime αG Ψ (z * v) x)
        (volume.restrict (Ioc (0 : ℝ) 1)) := hcontIoc.aestronglyMeasurable measurableSet_Ioc
    simpa only [Set.uIoc_of_le (show (0 : ℝ) ≤ 1 by norm_num)] using hmeas
  -- integrability of `F x₀`
  have hF_int : IntervalIntegrable
      (fun v : ℝ => v ^ (3 / αG - 1) * Uprime αG Ψ (z * v) θ) volume (0 : ℝ) 1 := by
    rw [intervalIntegrable_iff_integrableOn_Ioc_of_le (show (0 : ℝ) ≤ 1 by norm_num)]
    have hcont1 : ContinuousOn (fun v : ℝ => v ^ (3 / αG - 1)) (Ioo (0 : ℝ) 2) :=
      continuousOn_id.rpow_const (fun v hv => Or.inl (ne_of_gt hv.1))
    have hcont2 : ContinuousOn (fun v : ℝ => Uprime αG Ψ (z * v) θ) (Ioo (0 : ℝ) 2) :=
      (continuousOn_scaled_slice' hGc hz hθmem).mono (fun v hv => hv.1)
    have hcont : ContinuousOn (fun v : ℝ => v ^ (3 / αG - 1) * Uprime αG Ψ (z * v) θ)
        (Ioo (0 : ℝ) 2) := hcont1.mul hcont2
    have hcontIoc : ContinuousOn (fun v : ℝ => v ^ (3 / αG - 1) * Uprime αG Ψ (z * v) θ)
        (Ioc (0 : ℝ) 1) := hcont.mono (fun v hv => ⟨hv.1, by linarith [hv.2]⟩)
    have hmeas : AEStronglyMeasurable
        (fun v : ℝ => v ^ (3 / αG - 1) * Uprime αG Ψ (z * v) θ)
        (volume.restrict (Ioc (0 : ℝ) 1)) := hcontIoc.aestronglyMeasurable measurableSet_Ioc
    have hg : IntegrableOn (fun v : ℝ => v ^ (3 / αG - 1) * M) (Ioc (0 : ℝ) 1) volume :=
      (intervalIntegrable_iff_integrableOn_Ioc_of_le (show (0 : ℝ) ≤ 1 by norm_num)).mp
        ((intervalIntegral.intervalIntegrable_rpow' hce (a := (0 : ℝ)) (b := 1)).mul_const M)
    refine hg.mono' hmeas ?_
    rw [ae_restrict_iff' measurableSet_Ioc]
    refine Filter.Eventually.of_forall (fun v hv => ?_)
    have hmem2 : (z * v, θ) ∈ Work.Construction.Qd :=
      mem_Qd.mpr ⟨mul_pos hz hv.1, hθ0, hθ1⟩
    have hb := SlotBd.Uprime_le hslot hmem2
    rw [Real.norm_eq_abs, abs_mul, abs_of_nonneg (Real.rpow_nonneg hv.1.le _)]
    exact mul_le_mul_of_nonneg_left hb (Real.rpow_nonneg hv.1.le _)
  -- measurability of `F' x₀`
  have hF'_meas : AEStronglyMeasurable
      (fun v : ℝ => v ^ (3 / αG - 1) * Work.Spaces.pth (Uprime αG Ψ) (z * v) θ)
      (volume.restrict (Set.uIoc (0 : ℝ) 1)) := by
    have hcont1 : ContinuousOn (fun v : ℝ => v ^ (3 / αG - 1)) (Ioo (0 : ℝ) 2) :=
      continuousOn_id.rpow_const (fun v hv => Or.inl (ne_of_gt hv.1))
    have hcont2 : ContinuousOn (fun v : ℝ => Work.Spaces.pth (Uprime αG Ψ) (z * v) θ)
        (Ioo (0 : ℝ) 2) :=
      (continuousOn_scaled_slice' hpthc hz hθmem).mono (fun v hv => hv.1)
    have hcont : ContinuousOn
        (fun v : ℝ => v ^ (3 / αG - 1) * Work.Spaces.pth (Uprime αG Ψ) (z * v) θ)
        (Ioo (0 : ℝ) 2) := hcont1.mul hcont2
    have hcontIoc : ContinuousOn
        (fun v : ℝ => v ^ (3 / αG - 1) * Work.Spaces.pth (Uprime αG Ψ) (z * v) θ)
        (Ioc (0 : ℝ) 1) := hcont.mono (fun v hv => ⟨hv.1, by linarith [hv.2]⟩)
    have hmeas : AEStronglyMeasurable
        (fun v : ℝ => v ^ (3 / αG - 1) * Work.Spaces.pth (Uprime αG Ψ) (z * v) θ)
        (volume.restrict (Ioc (0 : ℝ) 1)) := hcontIoc.aestronglyMeasurable measurableSet_Ioc
    simpa only [Set.uIoc_of_le (show (0 : ℝ) ≤ 1 by norm_num)] using hmeas
  -- the uniform bound
  have h_bound : ∀ᵐ t ∂volume, t ∈ Set.uIoc (0 : ℝ) 1 → ∀ x ∈ s,
      ‖(fun x v => v ^ (3 / αG - 1) * Work.Spaces.pth (Uprime αG Ψ) (z * v) x) x t‖ ≤
        (fun v => v ^ (3 / αG - 1) * (2 * M / Work.Construction.s2 θ)) t := by
    refine Filter.Eventually.of_forall (fun t ht x hx => ?_)
    rw [Set.uIoc_of_le (show (0 : ℝ) ≤ 1 by norm_num)] at ht
    simpa only [Real.norm_eq_abs] using hKs x hx t ht
  -- integrability of the majorant
  have hbound_int : IntervalIntegrable
      (fun v : ℝ => v ^ (3 / αG - 1) * (2 * M / Work.Construction.s2 θ)) volume (0 : ℝ) 1 :=
    (intervalIntegral.intervalIntegrable_rpow' hce (a := (0 : ℝ)) (b := 1)).mul_const _
  -- the derivative of the integrand in `θ`
  have h_diff : ∀ᵐ t ∂volume, t ∈ Set.uIoc (0 : ℝ) 1 → ∀ x ∈ s,
      HasDerivAt (fun x' => t ^ (3 / αG - 1) * Uprime αG Ψ (z * t) x')
        (t ^ (3 / αG - 1) * Work.Spaces.pth (Uprime αG Ψ) (z * t) x) x := by
    refine Filter.Eventually.of_forall (fun t ht x hx => ?_)
    rw [Set.uIoc_of_le (show (0 : ℝ) ≤ 1 by norm_num)] at ht
    have hmem2 : (z * t, x) ∈ Work.Construction.Qd :=
      mem_Qd.mpr ⟨mul_pos hz ht.1, hx.1.1, hx.1.2⟩
    have hd : DifferentiableAt ℝ (Function.uncurry (Uprime αG Ψ)) (z * t, x) :=
      hGd (z * t) x hmem2
    have hcurve : HasDerivAt (fun x' : ℝ => (z * t, x')) (0, 1) x :=
      (hasDerivAt_const x (z * t)).prodMk (hasDerivAt_id x)
    have h1 : HasDerivAt (fun x' : ℝ => Function.uncurry (Uprime αG Ψ) (z * t, x'))
        (fderiv ℝ (Function.uncurry (Uprime αG Ψ)) (z * t, x) (0, 1)) x :=
      hd.hasFDerivAt.comp_hasDerivAt x hcurve
    rw [Work.Spaces.pth_eq_fderiv hd]
    exact h1.const_mul _
  exact (intervalIntegral.hasDerivAt_integral_of_dominated_loc_of_deriv_le
    (F := fun x v => v ^ (3 / αG - 1) * Uprime αG Ψ (z * v) x)
    (F' := fun x v => v ^ (3 / αG - 1) * Work.Spaces.pth (Uprime αG Ψ) (z * v) x)
    (x₀ := θ) (s := s)
    (bound := fun v => v ^ (3 / αG - 1) * (2 * M / Work.Construction.s2 θ))
    (μ := volume) (a := (0 : ℝ)) (b := 1)
    hsnh hF_meas hF_int hF'_meas h_bound hbound_int h_diff).2

/-! ## §2 The theorem -/

theorem psiP_diff {αG M : ℝ} (hαG : 0 < αG) {Ψ : ℝ → ℝ → ℝ}
    (h3 : ContDiffOn ℝ 3 (Function.uncurry Ψ) Work.Construction.Qd)
    (hslot : Work.FTS.StreamBdryIface.SlotBd αG Ψ M) :
    Work.FTS_StreamBdry.PsiPDiff αG M Ψ := by
  intro z θ hmem
  obtain ⟨hz, hθ0, hθ1⟩ := mem_Qd.mp hmem
  have hkpos : 0 < (3 : ℝ) / αG := div_pos (by norm_num) hαG
  constructor
  · -- the `z`-derivative: `rpow_ode_aux`
    have hU1 : ContDiffOn ℝ 1 (Function.uncurry (Uprime αG Ψ)) Work.Construction.Qd :=
      contDiffOn_uncurry_Uprime h3
    have hcontSlice : ContinuousOn (fun u : ℝ => Uprime αG Ψ u θ) (Ioi 0) := by
      have hcomp : ContinuousOn (fun u : ℝ => (u, θ)) (Ioi (0 : ℝ)) :=
        (continuous_id.prodMk continuous_const).continuousOn
      have hmap : MapsTo (fun u : ℝ => (u, θ)) (Ioi (0 : ℝ)) Work.Construction.Qd :=
        fun u hu => ⟨hu, hθ0, hθ1⟩
      exact hU1.continuousOn.comp hcomp hmap
    have hcont : ContinuousOn (fun u : ℝ => Uprime αG Ψ u θ) (Ioo (0 : ℝ) (z + 1)) :=
      hcontSlice.mono (fun u hu => hu.1)
    have hbdd : ∀ u ∈ Ioo (0 : ℝ) (z + 1), |Uprime αG Ψ u θ| ≤ M :=
      fun u hu => SlotBd.Uprime_le hslot ⟨hu.1, hθ0, hθ1⟩
    have hA := rpow_ode_aux (k := (3 : ℝ) / αG) (M := M) (z := z) hkpos hz hcont hbdd
    have hfun : (fun z' => psiP αG Ψ z' θ)
        = fun z' => -(Work.Construction.s2 θ / αG) *
            (∫ v in (0 : ℝ)..1, v ^ ((3 : ℝ) / αG - 1) * Uprime αG Ψ (z' * v) θ) := by
      funext z'
      rw [Work.FTS_StreamBdry.psiP_eq_Iint]
      rfl
    rw [hfun]
    exact (hA.const_mul _).differentiableAt
  · -- the `θ`-derivative: differentiation under the integral sign
    have hI : DifferentiableAt ℝ (fun θ' => Work.FTS_StreamBdry.Iint αG Ψ z θ') θ :=
      (Iint_theta_hasDerivAt hαG h3 hslot z θ hmem).differentiableAt
    have hs2d : DifferentiableAt ℝ
        (fun θ' => -(Work.Construction.s2 θ' / αG)) θ := by
      have h1 : DifferentiableAt ℝ (fun θ' : ℝ => Work.Construction.s2 θ') θ := by
        have heq : (fun θ' : ℝ => Real.sin (2 * θ')) = fun θ' => Work.Construction.s2 θ' := by
          funext θ'
          rw [Work.Construction.s2_eq]
        rw [← heq]
        exact (Real.differentiableAt_sin (x := 2 * θ)).comp θ
          (differentiableAt_id.const_mul 2)
      exact (h1.div_const αG).neg
    have hfun : (fun θ' => psiP αG Ψ z θ')
        = fun θ' => -(Work.Construction.s2 θ' / αG) * Work.FTS_StreamBdry.Iint αG Ψ z θ' := by
      funext θ'
      rw [Work.FTS_StreamBdry.psiP_eq_Iint]
    rw [hfun]
    exact hs2d.mul hI

end Work.FTS_StreamBdry.SB1
end
end
-- ===== merged: Submission.Work.FTS_StreamBdry.SB1.psiP_ode =====
section

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
end
end
-- ===== merged: Submission.Work.FTS_StreamBdry.SB25.Lgs_barrier =====
section

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

/-!
# `Work.FTS_StreamBdry.SB25.Lgs_barrier` — E4b: `Lgs` of the barrier `(M + δφ)(z/L)^{-k} + η`

`Lgs α` is the ground-state-transformed operator of `Defs.lean`,
`Lgs α u = -α² D_z²u - 5α D_zu - ∂_θ²u - (4cot 2θ - tan θ)∂_θu`; it is *Euler-homogeneous*
in `z` and, applied to the separated barrier `u = A(θ)·(z/L)^{-k} + η` with `A = M + δφ`, it
returns `(z/L)^{-k}` times the one-dimensional expression

`α k (5 - αk)·A(θ) + δ·(𝓐φ(θ))`,  `𝓐φ = -φ'' - (4cot 2θ - tan θ)φ'`.

This is the exact computation `E4b` of the SB2/SB5 leaf plan: it identifies `Lgs` on the
barrier with `αk(5-αk)(M+δφ) + δ𝓐φ` and is what allows the maximum principle
(`Lgs_nonneg_of_max`) to be applied to a barrier built from a super-solution `φ` of
`𝓐φ ≥ -C` (`phiB_barrier`/`sb5_barrier`).

The only calculus input is that `z ↦ (z/L)^{-k}` is an eigenfunction of the Euler operator
with eigenvalue `-k` (`z·(z/L)^{-k}' = -k (z/L)^{-k}`) — here in the form
`x ∂_x` and `(x∂_x)²`, i.e. the two lemmas `mul_deriv_rpow_div_const` and
`mul_deriv_mul_deriv_rpow_div_const`.  **No differentiability of `φ` is used**: Mathlib's
`deriv` is totalised, and `∂_θ` sees only the factor `A(θ) = M + δφ(θ)`, so all the
angular identities hold unconditionally (`deriv_const_add`, `deriv_const_mul_field`).
-/

namespace Work.FTS_StreamBdry.SB25

set_option autoImplicit false

/-! ## The Euler eigenfunction `z ↦ (z / L) ^ (-k)` -/

/-- `∂_x (x/L)^{-k} = -k (x/L)^{-k-1}/L` for `x ≠ 0`, `L ≠ 0` (chain rule). -/
private lemma deriv_rpow_div_const (k L x : ℝ) (hL : L ≠ 0) (hx : x ≠ 0) :
    deriv (fun y : ℝ => (y / L) ^ (-k)) x = (-k) * (x / L) ^ (-k - 1) / L := by
  have hx' : x / L ≠ 0 := div_ne_zero hx hL
  have h1 : HasDerivAt (fun y : ℝ => y ^ (-k)) ((-k) * (x / L) ^ (-k - 1)) (x / L) :=
    Real.hasDerivAt_rpow_const (Or.inl hx')
  have h2 : HasDerivAt (fun y : ℝ => y / L) (1 / L) x := (hasDerivAt_id x).div_const L
  have h3 := h1.comp x h2
  have h4 : deriv (fun y : ℝ => (y / L) ^ (-k)) x
      = ((-k) * (x / L) ^ (-k - 1)) * (1 / L) := by
    simpa [Function.comp_def] using h3.deriv
  rw [h4]; ring

/-- **`D_z`-eigenfunction**: `x · ∂_x (x/L)^{-k} = -k (x/L)^{-k}` for `x ≠ 0`, `L ≠ 0`. -/
lemma mul_deriv_rpow_div_const (k L x : ℝ) (hL : L ≠ 0) (hx : x ≠ 0) :
    x * deriv (fun y : ℝ => (y / L) ^ (-k)) x = -k * (x / L) ^ (-k) := by
  rw [deriv_rpow_div_const k L x hL hx,
    show x * ((-k) * (x / L) ^ (-k - 1) / L) = -k * ((x / L) ^ (-k - 1) * (x / L)) from by
      field_simp]
  have hq : x / L ≠ 0 := div_ne_zero hx hL
  rw [show (x / L) ^ (-k - 1) * (x / L) = (x / L) ^ (-k) from by
    rw [← Real.rpow_add_one hq (-k - 1)]; norm_num]

/-- **`D_z²`-eigenfunction**: `x · ∂_x (x ∂_x (x/L)^{-k}) = k² (x/L)^{-k}` for `x ≠ 0`,
`L ≠ 0`.  (Away from `0` the function `x ∂_x (x/L)^{-k}` agrees with `-k (x/L)^{-k}`,
which is differentiable there.) -/
lemma mul_deriv_mul_deriv_rpow_div_const (k L x : ℝ) (hL : L ≠ 0) (hx : x ≠ 0) :
    x * deriv (fun y : ℝ => y * deriv (fun y' : ℝ => (y' / L) ^ (-k)) y) x
      = k ^ 2 * (x / L) ^ (-k) := by
  have hev : (fun y : ℝ => y * deriv (fun y' : ℝ => (y' / L) ^ (-k)) y)
      =ᶠ[nhds x] (fun y : ℝ => -k * (y / L) ^ (-k)) := by
    filter_upwards [isOpen_compl_singleton.mem_nhds (by simpa using hx)] with y hy
    exact mul_deriv_rpow_div_const k L y hL hy
  rw [hev.deriv_eq, deriv_const_mul_field]
  rw [show x * (-k * deriv (fun y' : ℝ => (y' / L) ^ (-k)) x)
      = -k * (x * deriv (fun y' : ℝ => (y' / L) ^ (-k)) x) from by ring,
    mul_deriv_rpow_div_const k L x hL hx]
  ring

/-! ## The statement -/

/-- **E4b `Lgs_barrier`**: the ground-state-transformed operator on the barrier
`u = (M + δφ(θ))(z/L)^{-k} + η` equals `(z/L)^{-k}` times `αk(5-αk)(M+δφ) + δ𝓐φ`. -/
theorem Lgs_barrier (α k L M δ η : ℝ) :
    Work.FTS_StreamBdry.SB25.LgsBarrier α k L M δ η := by
  intro φ hφ hL z θ hQd
  have hz : 0 < z := Qd_pos hQd
  have hz0 : z ≠ 0 := ne_of_gt hz
  have hL0 : L ≠ 0 := ne_of_gt hL
  unfold Work.FTS_StreamBdry.SB25.Lgs
  -- angular derivative of the barrier: only the factor `A θ = M + δφθ` reacts
  have hpth : ∀ t : ℝ,
      Work.Spaces.pth (fun z' θ' => (M + δ * φ θ') * (z' / L) ^ (-k) + η) z t
        = (δ * (z / L) ^ (-k)) * deriv φ t := by
    intro t
    change deriv (fun t' : ℝ => (M + δ * φ t') * (z / L) ^ (-k) + η) t
      = (δ * (z / L) ^ (-k)) * deriv φ t
    rw [show (fun t' : ℝ => (M + δ * φ t') * (z / L) ^ (-k) + η)
        = (fun t' : ℝ => (η + M * (z / L) ^ (-k)) + (δ * (z / L) ^ (-k)) * φ t') from by
          funext t'; ring,
      deriv_const_add, deriv_const_mul_field]
  have hpth2 : Work.Spaces.pthIter 2 (fun z' θ' => (M + δ * φ θ') * (z' / L) ^ (-k) + η) z θ
      = (δ * (z / L) ^ (-k)) * deriv (deriv φ) θ := by
    change deriv (fun t : ℝ =>
      Work.Spaces.pth (fun z' θ' => (M + δ * φ θ') * (z' / L) ^ (-k) + η) z t) θ = _
    rw [show (fun t : ℝ =>
          Work.Spaces.pth (fun z' θ' => (M + δ * φ θ') * (z' / L) ^ (-k) + η) z t)
        = (fun t : ℝ => (δ * (z / L) ^ (-k)) * deriv φ t) from by funext t; exact hpth t,
      deriv_const_mul_field]
  -- radial derivative: only the factor `B z = (z/L)^{-k}` reacts
  have hpz : ∀ x : ℝ,
      Work.Spaces.pz (fun z' θ' => (M + δ * φ θ') * (z' / L) ^ (-k) + η) x θ
        = (M + δ * φ θ) * deriv (fun y : ℝ => (y / L) ^ (-k)) x := by
    intro x
    change deriv (fun x' : ℝ => (M + δ * φ θ) * (x' / L) ^ (-k) + η) x = _
    rw [show (fun x' : ℝ => (M + δ * φ θ) * (x' / L) ^ (-k) + η)
        = (fun x' : ℝ => η + (M + δ * φ θ) * (x' / L) ^ (-k)) from by funext x'; ring,
      deriv_const_add, deriv_const_mul_field]
  have hDz : Work.Spaces.Dz (fun z' θ' => (M + δ * φ θ') * (z' / L) ^ (-k) + η) z θ
      = -k * (M + δ * φ θ) * (z / L) ^ (-k) := by
    change z * Work.Spaces.pz (fun z' θ' => (M + δ * φ θ') * (z' / L) ^ (-k) + η) z θ = _
    rw [hpz z]
    rw [show z * ((M + δ * φ θ) * deriv (fun y : ℝ => (y / L) ^ (-k)) z)
        = (M + δ * φ θ) * (z * deriv (fun y : ℝ => (y / L) ^ (-k)) z) from by ring,
      mul_deriv_rpow_div_const k L z hL0 hz0]
    ring
  have hDz2 : Work.Spaces.DzIter 2 (fun z' θ' => (M + δ * φ θ') * (z' / L) ^ (-k) + η) z θ
      = k ^ 2 * (M + δ * φ θ) * (z / L) ^ (-k) := by
    change z * Work.Spaces.pz
      (Work.Spaces.Dz (fun z' θ' => (M + δ * φ θ') * (z' / L) ^ (-k) + η)) z θ = _
    have hfun : (fun y : ℝ => Work.Spaces.Dz
          (fun z' θ' => (M + δ * φ θ') * (z' / L) ^ (-k) + η) y θ)
        = (fun y : ℝ => (M + δ * φ θ) * (y * deriv (fun y' : ℝ => (y' / L) ^ (-k)) y)) := by
      funext y
      change y * Work.Spaces.pz (fun z' θ' => (M + δ * φ θ') * (z' / L) ^ (-k) + η) y θ = _
      rw [hpz y]; ring
    change z * deriv (fun y : ℝ => Work.Spaces.Dz
      (fun z' θ' => (M + δ * φ θ') * (z' / L) ^ (-k) + η) y θ) z = _
    rw [hfun, deriv_const_mul_field]
    rw [show z * ((M + δ * φ θ) * deriv
          (fun y : ℝ => y * deriv (fun y' : ℝ => (y' / L) ^ (-k)) y) z)
        = (M + δ * φ θ) * (z * deriv
          (fun y : ℝ => y * deriv (fun y' : ℝ => (y' / L) ^ (-k)) y) z) from by ring,
      mul_deriv_mul_deriv_rpow_div_const k L z hL0 hz0]
    ring
  rw [hDz, hDz2, hpth θ, hpth2]
  ring

end Work.FTS_StreamBdry.SB25
end
-- ===== merged: Submission.Work.FTS_StreamBdry.SB25.Lgs_nonneg_of_max =====
section

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

/-!
# `Work.FTS_StreamBdry.SB25.Lgs_nonneg_of_max` (leaf E4a of the SB2/SB5 plan)

The coordinatewise maximum principle for the ground-state-transformed operator

`Lgs α u = -(α²) ∂_z²u - 5α ∂_z u - ∂_θ²u - (4cos 2θ / sin 2θ - tan θ) ∂_θu`
(here `DzIter 2 u = z ∂_z u + z² ∂_z²u`, since `D_z = z ∂_z`),

in the form used in the SB5 comparison argument: if `v` is `C²` at an interior point `(z₀,θ₀)` of
the quadrant which is a local maximum of both one-dimensional slices, then `0 ≤ Lgs α v z₀ θ₀`.

The pointwise proof is the classical Fermat argument: at a local maximum each first partial
vanishes and each pure second partial is `≤ 0`; the second-order fact
`Work.FTS.PressureOn.secondDerivTest` supplies `∂_z²v ≤ 0`, `∂_θ²v ≤ 0`, hence every term of
`Lgs α v z₀ θ₀` is `≥ 0` independently of the sign (or vanishing) of `α`.
-/

namespace Work.FTS_StreamBdry.SB25

/-- The operator `DzIter 2 = D_z ∘ D_z` evaluated at a point, in terms of the `z`-slice and its
first two derivatives: `DzIter 2 v z θ = z ∂_zv + z² ∂_z²v`.

The only hypothesis is the differentiability at `z` of `∂_zv(·,θ)`, which is exactly what the
product rule for `z ↦ z · ∂_zv(z,θ)` needs. -/
lemma dzIter_two_eq (v : ℝ → ℝ → ℝ) (z θ : ℝ)
    (h : DifferentiableAt ℝ (fun z' => deriv (fun z'' => v z'' θ) z') z) :
    Work.Spaces.DzIter 2 v z θ
      = z * deriv (fun z' => v z' θ) z + z ^ 2 * deriv (deriv (fun z' => v z' θ)) z := by
  have hd : HasDerivAt (fun z' => deriv (fun z'' => v z'' θ) z')
      (deriv (deriv (fun z' => v z' θ)) z) z := h.hasDerivAt
  have hp : HasDerivAt (fun z' => z' * deriv (fun z'' => v z'' θ) z')
      (deriv (fun z' => v z' θ) z + z * deriv (deriv (fun z' => v z' θ)) z) z := by
    have h1 : HasDerivAt (fun x : ℝ => x) 1 z := hasDerivAt_id z
    have h2 := h1.mul hd
    have hc : (fun x : ℝ => x) * (fun z' => deriv (fun z'' => v z'' θ) z')
        = (fun z' => z' * deriv (fun z'' => v z'' θ) z') := by
      funext x; rfl
    rw [hc] at h2
    simpa using h2
  have hfun : Work.Spaces.DzIter 2 v z θ
      = z * deriv (fun z' => z' * deriv (fun z'' => v z'' θ) z') z := by
    simp only [Work.Spaces.DzIter_succ, Work.Spaces.DzIter_zero, Work.Spaces.Dz, Work.Spaces.pz]
  rw [hfun, hp.deriv]
  ring

theorem Lgs_nonneg_of_max (α : ℝ) (v : ℝ → ℝ → ℝ) :
    Work.FTS_StreamBdry.SB25.LgsNonnegOfMax α v := by
  intro z0 θ0 hz0 hθ0 hv hmz0 hmθ0
  -- rename the slice variables so that the statements below match syntactically
  have hmz : IsLocalMax (fun z' => v z' θ0) z0 := hmz0
  have hmθ : IsLocalMax (fun θ' => v z0 θ') θ0 := hmθ0
  -- the two slices are `C²` at the maximum point
  have hcz : ContDiffAt ℝ 2 (fun z' => v z' θ0) z0 := by
    have h1 : ContDiffAt ℝ 2 (fun z : ℝ => (z, θ0)) z0 :=
      contDiffAt_id.prodMk contDiffAt_const
    have h2 := hv.comp z0 h1
    simpa [Function.comp_def] using h2
  have hct : ContDiffAt ℝ 2 (fun θ' => v z0 θ') θ0 := by
    have h1 : ContDiffAt ℝ 2 (fun θ : ℝ => (z0, θ)) θ0 :=
      contDiffAt_const.prodMk contDiffAt_id
    have h2 := hv.comp θ0 h1
    simpa [Function.comp_def] using h2
  -- Fermat: the first derivatives vanish
  have hdz : deriv (fun z' => v z' θ0) z0 = 0 := hmz.deriv_eq_zero
  have hdt : deriv (fun θ' => v z0 θ') θ0 = 0 := hmθ.deriv_eq_zero
  -- the pure second derivatives are nonpositive at a local maximum
  have hzz : deriv (deriv (fun z' => v z' θ0)) z0 ≤ 0 :=
    Work.FTS.PressureOn.secondDerivTest hmz hcz
  have htt : deriv (deriv (fun θ' => v z0 θ')) θ0 ≤ 0 :=
    Work.FTS.PressureOn.secondDerivTest hmθ hct
  -- the `z`-slice derivative is differentiable at `z0` (needed for the product rule)
  have hdiff : DifferentiableAt ℝ (fun z' => deriv (fun z'' => v z'' θ0) z') z0 :=
    (hcz.derivWithin (m := 1) (by norm_num)).differentiableAt (by norm_num)
  -- evaluate the four operators appearing in `Lgs`
  have hDzIter := dzIter_two_eq v z0 θ0 hdiff
  have hDz : Work.Spaces.Dz v z0 θ0 = 0 := by
    simp only [Work.Spaces.Dz, Work.Spaces.pz]
    rw [hdz, mul_zero]
  have hpth : Work.Spaces.pth v z0 θ0 = 0 := by
    simpa only [Work.Spaces.pth] using hdt
  have hpthIter : Work.Spaces.pthIter 2 v z0 θ0 = deriv (deriv (fun θ' => v z0 θ')) θ0 := by
    simp only [Work.Spaces.pthIter_succ, Work.Spaces.pthIter_zero, Work.Spaces.pth]
  -- every term of `Lgs` is nonnegative: `-α² z₀² ∂_z²v ≥ 0`, the first-order terms vanish, and
  -- `-∂_θ²v ≥ 0`.
  simp only [Work.FTS_StreamBdry.SB25.Lgs]
  rw [hDzIter, hDz, hpthIter, hpth, hdz]
  nlinarith [hzz, htt, sq_nonneg (α * z0)]

end Work.FTS_StreamBdry.SB25
end
-- ===== merged: Submission.Work.FTS_StreamBdry.SB25.Lgs_sub =====
section

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

/-!
# `Work.FTS_StreamBdry.SB25.Lgs_sub` — additivity of the ground-state operator `Lgs`

`Lgs α u = -α²·D_z²u - 5α·D_z u - ∂_θ²u - (4 cos 2θ / sin 2θ - tan θ)·∂_θu` is a linear
combination of four (totalized) partial derivatives; the point of this file is that it is
therefore **additive**, `Lgs α (f - g) = Lgs α f - Lgs α g`, at every point where both
arguments are jointly `C²`.  (Nothing beyond `C²` is needed: `Lgs` itself contains no
derivative of the coefficient `4 cos 2θ / sin 2θ - tan θ`, so the failure of the
differentiability of `tan` at `θ = π/2`, which makes the `bslOp` version of this statement
false at `π/2`, is irrelevant here.)

The auxiliary lemmas below are stated generically and are reused by any later file that
needs linearity of the operators `∂_z, ∂_θ, D_z, ∂_z^i, ∂_θ^i` at a point of joint `C²`.
-/

noncomputable section

open scoped Real

namespace Work.FTS_StreamBdry.SB25

set_option autoImplicit false

/-! ## Slices of a jointly smooth function -/

theorem Lgs_aux_slice_fst {f : ℝ → ℝ → ℝ} {z θ : ℝ} {n : ℕ}
    (hf : ContDiffAt ℝ n (Function.uncurry f) (z, θ)) :
    ContDiffAt ℝ n (fun z' => f z' θ) z := by
  have h1 : ContDiffAt ℝ n (fun z' : ℝ => (z', θ)) z := by fun_prop
  exact hf.comp z h1

theorem Lgs_aux_slice_snd {f : ℝ → ℝ → ℝ} {z θ : ℝ} {n : ℕ}
    (hf : ContDiffAt ℝ n (Function.uncurry f) (z, θ)) :
    ContDiffAt ℝ n (fun θ' => f z θ') θ := by
  have h1 : ContDiffAt ℝ n (fun θ' : ℝ => (z, θ')) θ := by fun_prop
  exact hf.comp θ h1

/-! ## The definition of `Lgs`, unfolded -/

theorem Lgs_apply_expand (α : ℝ) (u : ℝ → ℝ → ℝ) (z θ : ℝ) :
    Work.FTS_StreamBdry.SB25.Lgs α u z θ
      = -(α ^ 2) * Work.Spaces.DzIter 2 u z θ - 5 * α * Work.Spaces.Dz u z θ
        - Work.Spaces.pthIter 2 u z θ
        - (4 * Real.cos (2 * θ) / Real.sin (2 * θ) - Real.tan θ) * Work.Spaces.pth u z θ :=
  rfl

/-! ## Linearity of the first order operators -/

theorem Lgs_aux_pz_sub {X Y : ℝ → ℝ → ℝ} {z θ : ℝ}
    (hX : DifferentiableAt ℝ (fun z' => X z' θ) z)
    (hY : DifferentiableAt ℝ (fun z' => Y z' θ) z) :
    Work.Spaces.pz (fun z θ => X z θ - Y z θ) z θ
      = Work.Spaces.pz X z θ - Work.Spaces.pz Y z θ := by
  simp only [Work.Spaces.pz]
  have h : (fun z' => X z' θ - Y z' θ) = (fun z' => X z' θ) - (fun z' => Y z' θ) := rfl
  rw [h, deriv_sub hX hY]

theorem Lgs_aux_pth_sub {X Y : ℝ → ℝ → ℝ} {z θ : ℝ}
    (hX : DifferentiableAt ℝ (fun θ' => X z θ') θ)
    (hY : DifferentiableAt ℝ (fun θ' => Y z θ') θ) :
    Work.Spaces.pth (fun z θ => X z θ - Y z θ) z θ
      = Work.Spaces.pth X z θ - Work.Spaces.pth Y z θ := by
  simp only [Work.Spaces.pth]
  have h : (fun θ' => X z θ' - Y z θ') = (fun θ' => X z θ') - (fun θ' => Y z θ') := rfl
  rw [h, deriv_sub hX hY]

theorem Lgs_aux_Dz_sub {X Y : ℝ → ℝ → ℝ} {z θ : ℝ}
    (hX : DifferentiableAt ℝ (fun z' => X z' θ) z)
    (hY : DifferentiableAt ℝ (fun z' => Y z' θ) z) :
    Work.Spaces.Dz (fun z θ => X z θ - Y z θ) z θ
      = Work.Spaces.Dz X z θ - Work.Spaces.Dz Y z θ := by
  simp only [Work.Spaces.Dz]
  rw [Lgs_aux_pz_sub hX hY]
  ring

/-! ## Linearity of the iterated operators -/

theorem Lgs_aux_pzIter_sub {i : ℕ} {X Y : ℝ → ℝ → ℝ} {z θ : ℝ}
    (hX : ContDiffAt ℝ i (fun z' => X z' θ) z)
    (hY : ContDiffAt ℝ i (fun z' => Y z' θ) z) :
    Work.Spaces.pzIter i (fun z θ => X z θ - Y z θ) z θ
      = Work.Spaces.pzIter i X z θ - Work.Spaces.pzIter i Y z θ := by
  rw [Work.Spaces.pzIter_eq_iteratedDeriv, Work.Spaces.pzIter_eq_iteratedDeriv,
    Work.Spaces.pzIter_eq_iteratedDeriv]
  have h : (fun z' => X z' θ - Y z' θ) = (fun z' => X z' θ) - (fun z' => Y z' θ) := rfl
  rw [h, iteratedDeriv_sub hX hY]

/-- `pthIter` is the iterated derivative of the `θ`-slice (the `θ`-analogue of
`Work.Spaces.pzIter_eq_iteratedDeriv`, which is only stated for `∂_z`). -/
theorem Lgs_aux_pthIter_eq_iteratedDeriv (k : ℕ) (h : ℝ → ℝ → ℝ) (z θ : ℝ) :
    Work.Spaces.pthIter k h z θ = iteratedDeriv k (fun θ' => h z θ') θ := by
  rw [iteratedDeriv_eq_iterate]
  induction k generalizing θ with
  | zero => rfl
  | succ n ih =>
      simp only [Work.Spaces.pthIter_succ, Work.Spaces.pth]
      have hh : (fun θ' => Work.Spaces.pthIter n h z θ') = deriv^[n] (fun θ' => h z θ') := by
        funext θ'; exact ih θ'
      rw [hh, Function.iterate_succ_apply']

theorem Lgs_aux_pthIter_sub {i : ℕ} {X Y : ℝ → ℝ → ℝ} {z θ : ℝ}
    (hX : ContDiffAt ℝ i (fun θ' => X z θ') θ)
    (hY : ContDiffAt ℝ i (fun θ' => Y z θ') θ) :
    Work.Spaces.pthIter i (fun z θ => X z θ - Y z θ) z θ
      = Work.Spaces.pthIter i X z θ - Work.Spaces.pthIter i Y z θ := by
  rw [Lgs_aux_pthIter_eq_iteratedDeriv, Lgs_aux_pthIter_eq_iteratedDeriv,
    Lgs_aux_pthIter_eq_iteratedDeriv]
  have h : (fun θ' => X z θ' - Y z θ') = (fun θ' => X z θ') - (fun θ' => Y z θ') := rfl
  rw [h, iteratedDeriv_sub hX hY]

/-- The second iterate of `D_z = z ∂_z`, expanded:
`D_z²h = z ∂_z h + z² ∂_z²h` (the Stirling numbers `S(2,1) = S(2,2) = 1`). -/
theorem Lgs_aux_DzIter_two_eq {h : ℝ → ℝ → ℝ} {z θ : ℝ}
    (h2 : ContDiffAt ℝ 2 (fun z' => h z' θ) z) :
    Work.Spaces.DzIter 2 h z θ
      = z * Work.Spaces.pz h z θ + z ^ 2 * Work.Spaces.pzIter 2 h z θ := by
  have hd : ContDiffAt ℝ 1 (deriv (fun z' => h z' θ)) z :=
    h2.derivWithin (m := 1) (by norm_num)
  have hdif : DifferentiableAt ℝ (fun z' : ℝ => Work.Spaces.pz h z' θ) z := by
    have hh := hd.differentiableAt (by norm_num)
    simpa [Work.Spaces.pz] using hh
  have hmul : deriv (fun z' : ℝ => z' * Work.Spaces.pz h z' θ) z
      = Work.Spaces.pz h z θ + z * Work.Spaces.pzIter 2 h z θ := by
    have h1 := deriv_mul (c := fun z' : ℝ => z') (d := fun z' : ℝ => Work.Spaces.pz h z' θ)
      differentiableAt_id hdif
    have hid : deriv (fun z' : ℝ => z') z = 1 := by simpa using deriv_id z
    rw [hid] at h1
    have hfun : (fun z' : ℝ => z' * Work.Spaces.pz h z' θ)
        = (fun z' : ℝ => z') * (fun z' : ℝ => Work.Spaces.pz h z' θ) := rfl
    rw [hfun, h1]
    simp [Work.Spaces.pzIter_succ, Work.Spaces.pzIter_zero, Work.Spaces.pz]
  show z * deriv (fun z' : ℝ => z' * Work.Spaces.pz h z' θ) z
      = z * Work.Spaces.pz h z θ + z ^ 2 * Work.Spaces.pzIter 2 h z θ
  rw [hmul]
  ring

/-! ## The target -/

theorem Lgs_sub (α : ℝ) {f g : ℝ → ℝ → ℝ} {z θ : ℝ}
    (hf : ContDiffAt ℝ 2 (Function.uncurry f) (z, θ))
    (hg : ContDiffAt ℝ 2 (Function.uncurry g) (z, θ)) :
    Work.FTS_StreamBdry.SB25.Lgs α (fun z' θ' => f z' θ' - g z' θ') z θ
      = Work.FTS_StreamBdry.SB25.Lgs α f z θ - Work.FTS_StreamBdry.SB25.Lgs α g z θ := by
  have hfz := Lgs_aux_slice_fst hf
  have hgz := Lgs_aux_slice_fst hg
  have hfθ := Lgs_aux_slice_snd hf
  have hgθ := Lgs_aux_slice_snd hg
  have hdfz : DifferentiableAt ℝ (fun z' => f z' θ) z := hfz.differentiableAt (by norm_num)
  have hdgz : DifferentiableAt ℝ (fun z' => g z' θ) z := hgz.differentiableAt (by norm_num)
  have hdfθ : DifferentiableAt ℝ (fun θ' => f z θ') θ := hfθ.differentiableAt (by norm_num)
  have hdgθ : DifferentiableAt ℝ (fun θ' => g z θ') θ := hgθ.differentiableAt (by norm_num)
  have hD2 : Work.Spaces.DzIter 2 (fun z' θ' => f z' θ' - g z' θ') z θ
      = Work.Spaces.DzIter 2 f z θ - Work.Spaces.DzIter 2 g z θ := by
    rw [Lgs_aux_DzIter_two_eq (h := fun z' θ' => f z' θ' - g z' θ') (hfz.sub hgz),
      Lgs_aux_DzIter_two_eq (h := f) hfz, Lgs_aux_DzIter_two_eq (h := g) hgz,
      Lgs_aux_pz_sub hdfz hdgz, Lgs_aux_pzIter_sub hfz hgz]
    ring
  have hD1 : Work.Spaces.Dz (fun z' θ' => f z' θ' - g z' θ') z θ
      = Work.Spaces.Dz f z θ - Work.Spaces.Dz g z θ :=
    Lgs_aux_Dz_sub hdfz hdgz
  have hT2 : Work.Spaces.pthIter 2 (fun z' θ' => f z' θ' - g z' θ') z θ
      = Work.Spaces.pthIter 2 f z θ - Work.Spaces.pthIter 2 g z θ :=
    Lgs_aux_pthIter_sub hfθ hgθ
  have hT1 : Work.Spaces.pth (fun z' θ' => f z' θ' - g z' θ') z θ
      = Work.Spaces.pth f z θ - Work.Spaces.pth g z θ :=
    Lgs_aux_pth_sub hdfθ hdgθ
  rw [Lgs_apply_expand, Lgs_apply_expand, Lgs_apply_expand]
  rw [hD2, hD1, hT2, hT1]
  ring

end Work.FTS_StreamBdry.SB25
end
end
-- ===== merged: Submission.Work.FTS_StreamBdry.SB25.Sb5CmpAux =====
section

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

/-!
# `Sb5CmpAux` — calculus helpers for the SB5 barrier comparison

Auxiliary lemmas used by `Sb5CmpCore`/`sb5_compare`: openness of the quadrant, smoothness of the
explicit barrier `(M + δφ θ)(z/L)^{-k} + σ`, the identity `(z/L)^{-k} = (L/z)^k`, the endpoint
estimate for the barrier, and the negation rules for the ground-state operator `Lgs`.
-/

noncomputable section
open scoped Real Topology
open Set Filter MeasureTheory

namespace Work.FTS_StreamBdry.SB25

set_option autoImplicit false
set_option maxHeartbeats 1600000

lemma sb5c_Qd_isOpen : IsOpen Work.Construction.Qd := by
  rw [Work.Construction.Qd]
  exact isOpen_Ioi.prod isOpen_Ioo

lemma sb5c_Qd_mem_nhds {z θ : ℝ} (h : (z, θ) ∈ Work.Construction.Qd) :
    Work.Construction.Qd ∈ 𝓝 (z, θ) := sb5c_Qd_isOpen.mem_nhds h



lemma sb5c_barrier_contDiffAt (k L M δ σ : ℝ) (φ : ℝ → ℝ)
    (hφ : ContDiffOn ℝ 2 φ (Ioo 0 (Real.pi / 2)))
    (hL : L ≠ 0) {z θ : ℝ} (hz : 0 < z) (hθ : θ ∈ Ioo 0 (Real.pi / 2)) :
    ContDiffAt ℝ 2 (fun p : ℝ × ℝ => (M + δ * φ p.2) * (p.1 / L) ^ (-k) + σ) (z, θ) := by
  have hφθ : ContDiffAt ℝ 2 φ θ := hφ.contDiffAt (isOpen_Ioo.mem_nhds hθ)
  have h1 : ContDiffAt ℝ 2 (fun p : ℝ × ℝ => δ * φ p.2) (z, θ) := by
    have := (hφθ.comp (z, θ) contDiffAt_snd).const_smul δ
    simpa [smul_eq_mul] using this
  have h2 : ContDiffAt ℝ 2 (fun p : ℝ × ℝ => M + δ * φ p.2) (z, θ) :=
    (contDiffAt_const (c := M) (x := (z, θ))).add h1
  have h3 : ContDiffAt ℝ 2 (fun p : ℝ × ℝ => p.1 / L) (z, θ) :=
    contDiffAt_fst.div_const L
  have h4 : ContDiffAt ℝ 2 (fun p : ℝ × ℝ => (p.1 / L) ^ (-k)) (z, θ) :=
    h3.rpow_const_of_ne (div_ne_zero (ne_of_gt hz) hL)
  exact (h2.mul h4).add contDiffAt_const

/-- `(z/L)^{-k} = (L/z)^k` for `z,L > 0`. -/
lemma sb5c_rpow_neg_div_eq (k L z : ℝ) (hL : 0 < L) (hz : 0 < z) :
    (z / L) ^ (-k) = (L / z) ^ k := by
  rw [Real.rpow_neg (le_of_lt (div_pos hz hL)), Real.div_rpow (le_of_lt hz) (le_of_lt hL),
    Real.div_rpow (le_of_lt hL) (le_of_lt hz), inv_div]

/-- The endpoint estimate for the barrier. -/
lemma sb5c_endpoint_ineq {Mb ρ δ φa k z R L : ℝ}
    (hδφ : (Mb + 1) * (R / L) ^ k ≤ δ * φa) (hL : 0 < L) (hR : 0 < R) (hz : 0 < z)
    (hzR : z ≤ R) (hk : 0 ≤ k) (hρ : 0 ≤ ρ) (hMb : 0 ≤ Mb) (hδ : 0 < δ) (hφa : 0 ≤ φa) :
    Mb + 1 ≤ (Mb + ρ + δ * φa) * (L / z) ^ k := by
  have hRL : 0 < R / L := div_pos hR hL
  have hLR : 0 < L / R := div_pos hL hR
  have hLz : 0 < L / z := div_pos hL hz
  have hpow : (R / L) ^ k * (L / R) ^ k = 1 := by
    rw [← Real.mul_rpow (le_of_lt hRL) (le_of_lt hLR)]
    have h : R / L * (L / R) = 1 := by field_simp
    rw [h, Real.one_rpow]
  have hLRz : L / R ≤ L / z := by
    have h1 : L / R = L * R⁻¹ := by ring
    have h2 : L / z = L * z⁻¹ := by ring
    rw [h1, h2]
    exact mul_le_mul_of_nonneg_left (inv_anti₀ hz hzR) (le_of_lt hL)
  calc Mb + 1 = (Mb + 1) * ((R / L) ^ k * (L / R) ^ k) := by rw [hpow, mul_one]
    _ = (Mb + 1) * (R / L) ^ k * (L / R) ^ k := by ring
    _ ≤ (δ * φa) * (L / R) ^ k := mul_le_mul_of_nonneg_right hδφ (le_of_lt (Real.rpow_pos_of_pos hLR k))
    _ ≤ (Mb + ρ + δ * φa) * (L / R) ^ k := by
        refine mul_le_mul_of_nonneg_right (by linarith) (le_of_lt (Real.rpow_pos_of_pos hLR k))
    _ ≤ (Mb + ρ + δ * φa) * (L / z) ^ k :=
        mul_le_mul_of_nonneg_left (Real.rpow_le_rpow (le_of_lt hLR) hLRz hk)
          (by linarith [mul_nonneg hρ (le_of_lt (Real.rpow_pos_of_pos hLz k)),
                        mul_nonneg (le_of_lt hδ) hφa, hMb])


lemma sb5c_pz_neg (v : ℝ → ℝ → ℝ) :
    Work.Spaces.pz (fun z θ => -v z θ) = fun z θ => -Work.Spaces.pz v z θ := by
  funext z θ
  simp only [Work.Spaces.pz]
  exact deriv.neg

lemma sb5c_pth_neg (v : ℝ → ℝ → ℝ) :
    Work.Spaces.pth (fun z θ => -v z θ) = fun z θ => -Work.Spaces.pth v z θ := by
  funext z θ
  simp only [Work.Spaces.pth]
  exact deriv.neg

lemma sb5c_Dz_neg (v : ℝ → ℝ → ℝ) :
    Work.Spaces.Dz (fun z θ => -v z θ) = fun z θ => -Work.Spaces.Dz v z θ := by
  funext z θ
  simp only [Work.Spaces.Dz, sb5c_pz_neg, Pi.neg_apply]
  ring

lemma sb5c_DzIter_neg (n : ℕ) (v : ℝ → ℝ → ℝ) :
    Work.Spaces.DzIter n (fun z θ => -v z θ) = fun z θ => -Work.Spaces.DzIter n v z θ := by
  induction n with
  | zero => rfl
  | succ n ih => rw [Work.Spaces.DzIter_succ, ih, sb5c_Dz_neg, Work.Spaces.DzIter_succ]

lemma sb5c_pthIter_neg (n : ℕ) (v : ℝ → ℝ → ℝ) :
    Work.Spaces.pthIter n (fun z θ => -v z θ) = fun z θ => -Work.Spaces.pthIter n v z θ := by
  induction n with
  | zero => rfl
  | succ n ih => rw [Work.Spaces.pthIter_succ, ih, sb5c_pth_neg, Work.Spaces.pthIter_succ]

lemma sb5c_Lgs_neg (α : ℝ) (v : ℝ → ℝ → ℝ) :
    Lgs α (fun z θ => -v z θ) = fun z θ => -Lgs α v z θ := by
  funext z θ
  simp only [Lgs, sb5c_DzIter_neg, sb5c_Dz_neg, sb5c_pthIter_neg, sb5c_pth_neg, Pi.neg_apply]
  ring

lemma sb5c_s2_pos_of_Ioo {θ : ℝ} (h : θ ∈ Ioo (0 : ℝ) (Real.pi / 2)) :
    0 < Work.Construction.s2 θ := by
  rw [Work.Construction.s2]
  exact Real.sin_pos_of_pos_of_lt_pi (by linarith [h.1]) (by linarith [h.2])

end Work.FTS_StreamBdry.SB25
end
end
-- ===== merged: Submission.Work.FTS_StreamBdry.SB25.axis_d2_bound =====
section

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

/-!
# `Work.FTS_StreamBdry.SB25.axis_d2_bound` — leaf B4 of the SB2/SB5 plan

The 1-D axis expansion to second order: if `V := f' - tan·f` satisfies
`|V - v₀| ≤ ε (π/2 - t)` and `|V'| ≤ ε` on `[θ₀, π/2)`, and `f` is bounded on `(0, π/2)`,
then `|f''(θ₀)| ≤ 6ε + |v₀|(π/2 - θ₀)`.

Route (the leaf plan's decomposition).  With `W := f·cos` (so that `W' = cos·V`) one has

  `f'' = V' + tan θ₀·(V - v₀) + (1 + sin²θ₀)(W + v₀(1 - sin θ₀)) / cos³θ₀
          - v₀(1 - sin θ₀)²/cos³θ₀`,

whose four terms are bounded by `ε`, `ε π/2`, `ε π³/12` and `|v₀|(π/2 - θ₀)`.  The second
bound is `tan θ₀·(π/2 - θ₀) ≤ π/2` (Jordan's inequality), the third combines the tail bound
`|W + v₀(1 - sin θ₀)| ≤ ε(sin δ - δ cos δ) ≤ ε δ³/3` with `1 + sin² ≤ 2` and
`δ/sin δ ≤ π/2`, and the fourth is `(1 - sin θ₀)²/cos³θ₀ = cos θ₀/(1 + sin θ₀)² ≤ sin δ ≤ δ`.
The total is `ε(1 + π/2 + π³/12) + |v₀|δ ≤ 6ε + |v₀|δ` since `π ≤ 3.15`.
-/

noncomputable section
open scoped Real Topology NNReal
open Set Filter MeasureTheory

namespace Work.FTS_StreamBdry.SB25

/-- The numerical constant: `1 + π/2 + π³/12 ≤ 6`. -/
lemma pi_cubic_le : 1 + Real.pi / 2 + Real.pi ^ 3 / 12 ≤ (6 : ℝ) := by
  have h1 : Real.pi ≤ 3.15 := le_of_lt Real.pi_lt_d2
  have h0 : 0 ≤ Real.pi := le_of_lt Real.pi_pos
  have h2 : Real.pi ^ 2 ≤ 3.15 ^ 2 := by nlinarith
  have h3 : Real.pi ^ 3 ≤ 3.15 ^ 3 := by nlinarith
  nlinarith [h3]

theorem axis_d2_bound (f : ℝ → ℝ) (v0 B ε θ0 : ℝ) :
    Work.FTS_StreamBdry.SB25.AxisD2Bound f v0 B ε θ0 := by
  rw [Work.FTS_StreamBdry.SB25.AxisD2Bound]
  intro hθ0 hf2 hb hV hV'
  have hlt : θ0 < Real.pi / 2 := hθ0.2
  have hδ : 0 < Real.pi / 2 - θ0 := by linarith [hθ0.2]
  have hc : Real.cos θ0 ≠ 0 :=
    ne_of_gt (Real.cos_pos_of_mem_Ioo ⟨by linarith [Real.pi_pos, hθ0.1], hθ0.2⟩)
  by_cases hε : 0 ≤ ε
  swap
  · -- if `ε < 0` the hypothesis `hV` is contradictory
    exfalso
    have h0 := hV θ0 ⟨le_rfl, hlt⟩
    have h1 : ε * (Real.pi / 2 - θ0) < 0 := mul_neg_of_neg_of_pos (by linarith) hδ
    linarith [abs_nonneg (deriv f θ0 - Real.tan θ0 * f θ0 - v0), h0, h1]
  have hB : 0 ≤ B := le_trans (abs_nonneg _) (hb θ0 hθ0)
  have hident := Work.FTS_StreamBdry.SB25Aux.axisD2_ident f hθ0 (hf2 θ0 hθ0).1 (hf2 θ0 hθ0).2
  have htail := Work.FTS_StreamBdry.SB25Aux2.axisTail_bound f v0 B ε θ0 hθ0 hB hε
    (fun θ hθ => (hf2 θ hθ).1) (fun θ hθ => hb θ hθ) hV
  set A := deriv (fun s => deriv f s - Real.tan s * f s) θ0 with hAdef
  set Bt := Real.tan θ0 * (deriv f θ0 - Real.tan θ0 * f θ0 - v0) with hBdef
  set Ct := (f θ0 * Real.cos θ0 + v0 * (1 - Real.sin θ0)) * (1 + Real.sin θ0 ^ 2)
    / Real.cos θ0 ^ 3 with hCdef
  set Dt := v0 * (1 - Real.sin θ0) ^ 2 / Real.cos θ0 ^ 3 with hDdef
  have hA : |A| ≤ ε := by rw [hAdef]; exact hV' θ0 ⟨le_rfl, hlt⟩
  have hw : |deriv f θ0 - Real.tan θ0 * f θ0 - v0| ≤ ε * (Real.pi / 2 - θ0) :=
    hV θ0 ⟨le_rfl, hlt⟩
  have hBnd : |Bt| ≤ ε * (Real.pi / 2) := by
    rw [hBdef]; exact Work.FTS_StreamBdry.SB25Aux.axisBterm_le θ0 _ v0 ε hθ0 hε hw
  have hDnd : |Dt| ≤ |v0| * (Real.pi / 2 - θ0) := by
    rw [hDdef]; exact Work.FTS_StreamBdry.SB25Aux.axisDterm_le θ0 v0 hθ0
  have hJnd : |Ct| ≤ ε * (Real.pi ^ 3 / 12) := by
    rw [hCdef]; exact Work.FTS_StreamBdry.SB25Aux.axisJterm_le θ0 _ ε hθ0 hε htail
  have hdecomp : deriv (deriv f) θ0 = A + Bt + Ct - Dt := by
    rw [hident, hAdef, hBdef, hCdef, hDdef]
    rw [show Real.tan θ0 = Real.sin θ0 / Real.cos θ0 from Real.tan_eq_sin_div_cos θ0]
    field_simp
    ring_nf
    linear_combination (v0 * Real.sin θ0) * Real.sin_sq_add_cos_sq θ0
  rw [hdecomp]
  have htri : |A + Bt + Ct - Dt| ≤ |A| + |Bt| + |Ct| + |Dt| := by
    have h1 : |A + Bt + Ct - Dt| = |(A + Bt + Ct) + (-Dt)| := by ring_nf
    rw [h1]
    calc |(A + Bt + Ct) + (-Dt)| ≤ |A + Bt + Ct| + |-Dt| := abs_add_le _ _
      _ = |A + Bt + Ct| + |Dt| := by rw [abs_neg]
      _ ≤ (|A| + |Bt| + |Ct|) + |Dt| := by linarith [abs_add_three A Bt Ct]
  have hnum : |A| + |Bt| + |Ct| + |Dt| ≤ 6 * ε + |v0| * (Real.pi / 2 - θ0) := by
    have hp := pi_cubic_le
    nlinarith [hA, hBnd, hJnd, hDnd, hε, hp]
  linarith [htri, hnum]

end Work.FTS_StreamBdry.SB25
end
end
-- ===== merged: Submission.Work.FTS_StreamBdry.SB25.axis_tan_bound =====
section

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

/-!
# `Work.FTS_StreamBdry.SB25.axis_tan_bound` — leaf B3 (`AxisTanBound`)

## What is proved

Let `f : ℝ → ℝ`, `v0 A B : ℝ`.  Assume

* `f` is differentiable on `(0, π/2)`,
* `|f θ| ≤ B` there,
* `V(θ) := f' θ - tan θ · f θ` satisfies `|V θ - v0| ≤ A (π/2 - θ)` there.

Then for every `θ ∈ (0, π/2)`,

`|tan θ · f θ + v0/2| ≤ |v0| * (π/2 - θ)^2 + 3 * A * (π/2 - θ)`.

This is leaf **B3** of the lead's per-leaf plan `sources/ftsV2/fts_sb25_leafplans.md`
(the one-dimensional axis expansion at `θ = π/2`, used to compute the edge trace of `ψP`).

## The idea (and why the plan's `x³/3` comparison is replaced by `J`)

Put `G t = f t · cos t + v0 (1 - sin t)`, so that `G' t = cos t · (V t - v0)` on
`(0, π/2)` and `G (π/2) = 0` (this is where `|f| ≤ B` is used: the value at `π/2` is
independent of `f (π/2)`, because `cos (π/2) = 0`).  The sharp bound is
`|G θ| ≤ A · J θ` with `J t = cos t - (π/2 - t) sin t`; indeed `J' t = -(π/2 - t) cos t`,
so `W₁ := G - A J` has `W₁' = cos t (V - v0) + A (π/2 - t) cos t ≥ 0` and
`W₂ := G + A J` has `W₂' ≤ 0`; both vanish at `π/2`, whence `-A J θ ≤ G θ ≤ A J θ`.
(Comparing with `±A (π/2 - t)³/3` as suggested in the plan fails, since
`(π/2 - t) cos t` is *not* dominated by `(π/2 - t)²` near `t = π/2`; `J` is the correct
primitive.)  Finally `J θ = sin u - u cos u` and `cos²θ = sin²u` with `u = π/2 - θ`,
which turns the conclusion into the elementary estimates `sin u - u cos u ≤ u³/3`
and `u² ≤ 9 sin²u`.
-/

noncomputable section
open scoped Real Topology
open Set Filter

namespace Work.FTS_StreamBdry.SB25

/-! ## Elementary trigonometric estimates -/

/-- `sin u - u cos u ≤ u³/3` for `u ≥ 0`: the function `u³/3 - sin u + u cos u` has
derivative `u (u - sin u) ≥ 0` and vanishes at `0`. -/
theorem axis_aux_sincos_cube (u : ℝ) (hu : 0 ≤ u) :
    Real.sin u - u * Real.cos u ≤ u ^ 3 / 3 := by
  have hcont : ContinuousOn (fun x : ℝ => x ^ 3 / 3 - Real.sin x + x * Real.cos x) (Icc 0 u) :=
    (((continuous_id.pow 3).div_const 3).sub Real.continuous_sin).add
      (continuous_id.mul Real.continuous_cos) |>.continuousOn
  have hdiff : DifferentiableOn ℝ (fun x : ℝ => x ^ 3 / 3 - Real.sin x + x * Real.cos x)
      (interior (Icc 0 u)) := fun x _ =>
    (by fun_prop : DifferentiableAt ℝ
      (fun x : ℝ => x ^ 3 / 3 - Real.sin x + x * Real.cos x) x).differentiableWithinAt
  have hderiv : ∀ x ∈ interior (Icc 0 u),
      0 ≤ deriv (fun x : ℝ => x ^ 3 / 3 - Real.sin x + x * Real.cos x) x := by
    intro x hx
    rw [interior_Icc] at hx
    have hd : HasDerivAt (fun y : ℝ => y ^ 3 / 3 - Real.sin y + y * Real.cos y)
        (x ^ 2 - x * Real.sin x) x := by
      have hA : HasDerivAt (fun y : ℝ => y ^ 3 / 3) (x ^ 2) x := by
        convert (hasDerivAt_pow 3 x).div_const 3 using 1
        ring
      have hC : HasDerivAt (fun y : ℝ => y * Real.cos y) (Real.cos x - x * Real.sin x) x := by
        have h := (hasDerivAt_id x).mul (Real.hasDerivAt_cos x)
        convert h using 1
        · ext y; rfl
        · simp only [id_eq]; ring
      convert (hA.sub (Real.hasDerivAt_sin x)).add hC using 1
      ring
    rw [hd.deriv]
    have hx0 : 0 ≤ x := le_of_lt hx.1
    nlinarith [Real.sin_le hx0]
  have hmono := monotoneOn_of_deriv_nonneg (convex_Icc (0:ℝ) u) hcont hdiff hderiv
  have h0u : (fun x : ℝ => x ^ 3 / 3 - Real.sin x + x * Real.cos x) 0
      ≤ (fun x : ℝ => x ^ 3 / 3 - Real.sin x + x * Real.cos x) u :=
    hmono (left_mem_Icc.mpr hu) (right_mem_Icc.mpr hu) hu
  simp only at h0u
  norm_num at h0u
  linarith

/-- `u² ≤ 9 sin²u` on `[0, π/2]` (Jordan's inequality `sin u ≥ 2u/π ≥ u/3`). -/
theorem axis_aux_sq_le_nine_sin_sq (u : ℝ) (hu0 : 0 ≤ u) (hu1 : u ≤ π / 2) :
    u ^ 2 ≤ 9 * Real.sin u ^ 2 := by
  have hpi : (1 / 3 : ℝ) ≤ 2 / π := by
    rw [le_div_iff₀ Real.pi_pos]
    linarith [Real.pi_lt_four]
  have h1 : 2 / π * u ≤ Real.sin u := Real.mul_le_sin hu0 hu1
  have hs : u / 3 ≤ Real.sin u := by
    have h2 : (1 / 3 : ℝ) * u ≤ 2 / π * u := mul_le_mul_of_nonneg_right hpi hu0
    linarith
  have hsq : (u / 3) ^ 2 ≤ (Real.sin u) ^ 2 := by
    apply sq_le_sq'
    · have : 0 ≤ u / 3 := by positivity
      linarith [le_trans this hs]
    · exact hs
  nlinarith [hsq]

/-- `1 - sin θ ≤ (π/2 - θ)²` on `(0, π/2)`. -/
theorem axis_aux_one_sub_sin_le_sq (θ : ℝ) (hθ : θ ∈ Ioo (0 : ℝ) (π / 2)) :
    1 - Real.sin θ ≤ (π / 2 - θ) ^ 2 := by
  have hθ' : θ = π / 2 - (π / 2 - θ) := by ring
  rw [hθ', Real.sin_pi_div_two_sub]
  have h := Real.one_sub_sq_div_two_le_cos (x := π / 2 - θ)
  nlinarith [h]

/-! ## The algebraic rewriting of `tan θ · f θ + v0/2` -/

/-- With `G t = f t cos t + v0 (1 - sin t)`, the identity
`tan θ · f θ + v0/2 = sin θ · G θ / cos²θ + v0 (1 - sin θ)/(2 (1 + sin θ))`. -/
theorem axis_aux_tan_axis_algebra (f : ℝ → ℝ) (v0 θ : ℝ)
    (hθ : θ ∈ Ioo (0 : ℝ) (π / 2)) :
    Real.tan θ * f θ + v0 / 2
      = Real.sin θ * (f θ * Real.cos θ + v0 * (1 - Real.sin θ)) / Real.cos θ ^ 2
        + v0 * (1 - Real.sin θ) / (2 * (1 + Real.sin θ)) := by
  have hc : Real.cos θ ≠ 0 :=
    ne_of_gt (Real.cos_pos_of_mem_Ioo ⟨by linarith [Real.pi_pos, hθ.1], hθ.2⟩)
  have hsinpos : 0 < Real.sin θ :=
    Real.sin_pos_of_pos_of_lt_pi hθ.1 (by linarith [hθ.2, Real.pi_pos])
  have hlt1 : Real.sin θ < 1 := by
    have hc' : 0 < Real.cos θ := Real.cos_pos_of_mem_Ioo ⟨by linarith [Real.pi_pos, hθ.1], hθ.2⟩
    nlinarith [Real.sin_sq_add_cos_sq θ]
  have h1s : 1 - Real.sin θ ≠ 0 := by linarith
  have hs : 1 + Real.sin θ ≠ 0 := by linarith
  have hcos2 : Real.cos θ ^ 2 = (1 - Real.sin θ) * (1 + Real.sin θ) := by
    nlinarith [Real.sin_sq_add_cos_sq θ]
  have hA : Real.tan θ * f θ = Real.sin θ * (f θ * Real.cos θ) / Real.cos θ ^ 2 := by
    rw [Real.tan_eq_sin_div_cos]
    field_simp
  have hB : v0 / 2 = Real.sin θ * (v0 * (1 - Real.sin θ)) / Real.cos θ ^ 2
      + v0 * (1 - Real.sin θ) / (2 * (1 + Real.sin θ)) := by
    rw [hcos2]
    field_simp
    ring
  have hsplit : Real.sin θ * (f θ * Real.cos θ + v0 * (1 - Real.sin θ)) / Real.cos θ ^ 2
      = Real.sin θ * (f θ * Real.cos θ) / Real.cos θ ^ 2
        + Real.sin θ * (v0 * (1 - Real.sin θ)) / Real.cos θ ^ 2 := by
    rw [mul_add, add_div]
  rw [hA, hB, hsplit]
  ring

/-! ## Continuity of `G` on the closed interval `[θ, π/2]`

The endpoint `π/2` is not covered by differentiability; there boundedness of `f` gives
`f t · cos t → 0`. -/

/-- `t ↦ f t cos t + v0 (1 - sin t)` is continuous on `[θ, π/2]` when `f` is differentiable
on `(0,π/2)` and bounded there. -/
theorem axis_aux_G_continuousOn (f : ℝ → ℝ) (v0 B θ : ℝ)
    (hθ : θ ∈ Ioo (0 : ℝ) (π / 2))
    (hdiff : ∀ t ∈ Ioo (0 : ℝ) (π / 2), DifferentiableAt ℝ f t)
    (hbd : ∀ t ∈ Ioo (0 : ℝ) (π / 2), |f t| ≤ B) :
    ContinuousOn (fun t => f t * Real.cos t + v0 * (1 - Real.sin t)) (Icc θ (π / 2)) := by
  intro x hx
  rcases lt_or_eq_of_le hx.2 with hlt | heq
  · have hx0 : 0 < x := lt_of_lt_of_le hθ.1 hx.1
    have h1 : ContinuousAt f x := (hdiff x ⟨hx0, hlt⟩).continuousAt
    have h2 : ContinuousAt (fun t : ℝ => Real.cos t) x := Real.continuous_cos.continuousAt
    have h3 : ContinuousAt (fun t : ℝ => Real.sin t) x := Real.continuous_sin.continuousAt
    have h4 : ContinuousAt (fun t : ℝ => v0 * (1 - Real.sin t)) x :=
      (continuousAt_const.sub h3).const_mul v0
    exact ((h1.mul h2).add h4).continuousWithinAt
  · subst heq
    have hG0 : f (π / 2) * Real.cos (π / 2) + v0 * (1 - Real.sin (π / 2)) = 0 := by
      simp [Real.cos_pi_div_two, Real.sin_pi_div_two]
    show Tendsto (fun t => f t * Real.cos t + v0 * (1 - Real.sin t))
      (𝓝[Icc θ (π / 2)] (π / 2))
      (𝓝 (f (π / 2) * Real.cos (π / 2) + v0 * (1 - Real.sin (π / 2))))
    rw [hG0]
    rw [tendsto_zero_iff_norm_tendsto_zero]
    have hc : Tendsto (fun t : ℝ => Real.cos t) (𝓝[Icc θ (π / 2)] (π / 2)) (𝓝 0) := by
      have := (Real.continuous_cos.tendsto (π / 2)).mono_left
        (nhdsWithin_le_nhds (s := Icc θ (π / 2)) (a := π / 2))
      rwa [Real.cos_pi_div_two] at this
    have hss : Tendsto (fun t : ℝ => Real.sin t) (𝓝[Icc θ (π / 2)] (π / 2)) (𝓝 1) := by
      have := (Real.continuous_sin.tendsto (π / 2)).mono_left
        (nhdsWithin_le_nhds (s := Icc θ (π / 2)) (a := π / 2))
      rwa [Real.sin_pi_div_two] at this
    have hg : Tendsto (fun t : ℝ => B * |Real.cos t| + |v0| * |1 - Real.sin t|)
        (𝓝[Icc θ (π / 2)] (π / 2)) (𝓝 0) := by
      have h1 : Tendsto (fun t : ℝ => B * |Real.cos t|) (𝓝[Icc θ (π / 2)] (π / 2)) (𝓝 0) := by
        simpa using hc.abs.const_mul B
      have h2 : Tendsto (fun t : ℝ => |v0| * |1 - Real.sin t|)
          (𝓝[Icc θ (π / 2)] (π / 2)) (𝓝 0) := by
        have hsub : Tendsto (fun t : ℝ => 1 - Real.sin t)
            (𝓝[Icc θ (π / 2)] (π / 2)) (𝓝 0) := by
          have h0 : Tendsto (fun _ : ℝ => (1:ℝ)) (𝓝[Icc θ (π / 2)] (π / 2)) (𝓝 1) :=
            tendsto_const_nhds
          simpa using h0.sub hss
        simpa using hsub.abs.const_mul |v0|
      simpa using h1.add h2
    refine squeeze_zero' ?_ ?_ hg
    · filter_upwards with t using abs_nonneg _
    · filter_upwards [self_mem_nhdsWithin] with t ht
      rcases lt_or_eq_of_le ht.2 with hlt | hqq
      · have hx0 : 0 < t := lt_of_lt_of_le hθ.1 ht.1
        have hb := hbd t ⟨hx0, hlt⟩
        have hb' : |f t| * |Real.cos t| ≤ B * |Real.cos t| :=
          mul_le_mul_of_nonneg_right hb (abs_nonneg _)
        calc ‖f t * Real.cos t + v0 * (1 - Real.sin t)‖
            = |f t * Real.cos t + v0 * (1 - Real.sin t)| := rfl
          _ ≤ |f t * Real.cos t| + |v0 * (1 - Real.sin t)| := abs_add_le _ _
          _ = |f t| * |Real.cos t| + |v0| * |1 - Real.sin t| := by rw [abs_mul, abs_mul]
          _ ≤ B * |Real.cos t| + |v0| * |1 - Real.sin t| := by linarith
      · subst hqq
        simp [Real.cos_pi_div_two, Real.sin_pi_div_two]

/-! ## The final numerical chain -/

/-- If `|Gval| ≤ A (sin u - u cos u)`, `A ≥ 0` and `0 < u ≤ π/2`, then
`|cos u · Gval / sin²u| ≤ 3 A u`. -/
theorem axis_aux_final_bound (A u Gval : ℝ) (hA : 0 ≤ A) (hu : 0 < u) (hu1 : u ≤ π / 2)
    (hG : |Gval| ≤ A * (Real.sin u - u * Real.cos u)) :
    |Real.cos u * Gval / Real.sin u ^ 2| ≤ 3 * A * u := by
  have hu0 : 0 ≤ u := le_of_lt hu
  have hsinpos : 0 < Real.sin u := Real.sin_pos_of_pos_of_lt_pi hu (by linarith [hu1, Real.pi_pos])
  have hcosnn : 0 ≤ Real.cos u := Real.cos_nonneg_of_mem_Icc ⟨by linarith [Real.pi_pos], hu1⟩
  have hAJnn : 0 ≤ A * (Real.sin u - u * Real.cos u) := le_trans (abs_nonneg _) hG
  have h1 : |Real.cos u * Gval / Real.sin u ^ 2| = Real.cos u * |Gval| / Real.sin u ^ 2 := by
    rw [abs_div, abs_mul, abs_of_nonneg hcosnn, abs_of_pos (pow_pos hsinpos 2)]
  rw [h1]
  have hJle : Real.sin u - u * Real.cos u ≤ u ^ 3 / 3 := axis_aux_sincos_cube u hu0
  have h2 : Real.cos u * |Gval| ≤ Real.cos u * (A * (Real.sin u - u * Real.cos u)) :=
    mul_le_mul_of_nonneg_left hG hcosnn
  have h3 : Real.cos u * (A * (Real.sin u - u * Real.cos u)) ≤ A * (u ^ 3 / 3) := by
    have hc1 : Real.cos u * (A * (Real.sin u - u * Real.cos u))
        ≤ 1 * (A * (Real.sin u - u * Real.cos u)) :=
      mul_le_mul_of_nonneg_right (Real.cos_le_one u) hAJnn
    have h4 := mul_le_mul_of_nonneg_left hJle hA
    linarith
  have h5 : A * (u ^ 3 / 3) / Real.sin u ^ 2 ≤ 3 * A * u := by
    have hsq : u ^ 2 ≤ 9 * Real.sin u ^ 2 := axis_aux_sq_le_nine_sin_sq u hu0 hu1
    rw [div_le_iff₀ (pow_pos hsinpos 2)]
    have hcube : u ^ 3 ≤ 9 * u * Real.sin u ^ 2 := by
      have := mul_le_mul_of_nonneg_left hsq hu0
      nlinarith [this]
    have hcube' : u ^ 3 / 3 ≤ 3 * (u * Real.sin u ^ 2) := by linarith
    nlinarith [mul_le_mul_of_nonneg_left hcube' hA]
  calc Real.cos u * |Gval| / Real.sin u ^ 2
      ≤ Real.cos u * (A * (Real.sin u - u * Real.cos u)) / Real.sin u ^ 2 :=
        div_le_div_of_nonneg_right h2 (sq_nonneg _)
    _ ≤ A * (u ^ 3 / 3) / Real.sin u ^ 2 := div_le_div_of_nonneg_right h3 (sq_nonneg _)
    _ ≤ 3 * A * u := h5

/-! ## The leaf -/

theorem axis_tan_bound (f : ℝ → ℝ) (v0 A B : ℝ) :
    Work.FTS_StreamBdry.SB25.AxisTanBound f v0 A B := by
  intro hdiff hbd hclose θ hθ
  -- `0 ≤ A` is forced by the rate hypothesis.
  have hA : 0 ≤ A := by
    have h := hclose (π / 4) (by constructor <;> linarith [Real.pi_pos])
    have hp : (0:ℝ) < π / 2 - π / 4 := by linarith [Real.pi_pos]
    nlinarith [h, abs_nonneg (deriv f (π / 4) - Real.tan (π / 4) * f (π / 4) - v0)]
  set u : ℝ := π / 2 - θ with hu
  have hu_pos : 0 < u := by rw [hu]; linarith [hθ.2]
  have hu_le : u ≤ π / 2 := by rw [hu]; linarith [hθ.1]
  have hθ_eq : θ = π / 2 - u := by rw [hu]; ring
  set G : ℝ → ℝ := fun t => f t * Real.cos t + v0 * (1 - Real.sin t) with hG
  set J : ℝ → ℝ := fun t => Real.cos t - (π / 2 - t) * Real.sin t with hJ
  set W1 : ℝ → ℝ := fun t => G t - A * J t with hW1
  set W2 : ℝ → ℝ := fun t => G t + A * J t with hW2
  have hGc : ContinuousOn G (Icc θ (π / 2)) := by
    rw [hG]; exact axis_aux_G_continuousOn f v0 B θ hθ hdiff hbd
  have hJc : ContinuousOn J (Icc θ (π / 2)) := by
    rw [hJ]; fun_prop
  have hW1c : ContinuousOn W1 (Icc θ (π / 2)) := by
    rw [hW1]; exact hGc.sub (hJc.const_mul A)
  have hW2c : ContinuousOn W2 (Icc θ (π / 2)) := by
    rw [hW2]; exact hGc.add (hJc.const_mul A)
  -- derivatives of `G`, `J`, `W₁`, `W₂`
  have hGd : ∀ x ∈ Ioo θ (π / 2),
      HasDerivAt G (Real.cos x * (deriv f x - Real.tan x * f x - v0)) x := by
    intro x hx
    rw [hG]
    have hx0 : x ∈ Ioo (0:ℝ) (π / 2) := ⟨lt_trans hθ.1 hx.1, hx.2⟩
    have hcx : Real.cos x ≠ 0 :=
      ne_of_gt (Real.cos_pos_of_mem_Ioo ⟨by linarith [Real.pi_pos, hx0.1], hx0.2⟩)
    have hfx : HasDerivAt f (deriv f x) x := (hdiff x hx0).hasDerivAt
    have h1 : HasDerivAt (fun t : ℝ => f t * Real.cos t)
        (deriv f x * Real.cos x + f x * (-Real.sin x)) x := hfx.mul (Real.hasDerivAt_cos x)
    have h2 : HasDerivAt (fun t : ℝ => v0 * (1 - Real.sin t)) (v0 * (-(Real.cos x))) x := by
      have h0 : HasDerivAt (fun _ : ℝ => (1:ℝ)) 0 x := hasDerivAt_const x 1
      have hh := (h0.sub (Real.hasDerivAt_sin x)).const_mul v0
      convert hh using 1
      ring
    refine (h1.add h2).congr_deriv ?_
    rw [Real.tan_eq_sin_div_cos]
    field_simp
    ring
  have hJd : ∀ x ∈ Ioo θ (π / 2), HasDerivAt J (-(π / 2 - x) * Real.cos x) x := by
    intro x hx
    rw [hJ]
    have hid : HasDerivAt (fun t : ℝ => π / 2 - t) (-1) x := by
      have h0 : HasDerivAt (fun _ : ℝ => (π / 2:ℝ)) 0 x := hasDerivAt_const x (π / 2)
      have hh := h0.sub (hasDerivAt_id x)
      convert hh using 1
      · ext t; rfl
      · ring
    have hprod : HasDerivAt (fun t : ℝ => (π / 2 - t) * Real.sin t)
        ((-1) * Real.sin x + (π / 2 - x) * Real.cos x) x := hid.mul (Real.hasDerivAt_sin x)
    refine ((Real.hasDerivAt_cos x).sub hprod).congr_deriv ?_
    ring
  have hW1d : ∀ x ∈ Ioo θ (π / 2), HasDerivAt W1
      (Real.cos x * (deriv f x - Real.tan x * f x - v0) + A * (π / 2 - x) * Real.cos x) x := by
    intro x hx
    rw [hW1]
    refine ((hGd x hx).sub ((hJd x hx).const_mul A)).congr_deriv ?_
    ring
  have hW2d : ∀ x ∈ Ioo θ (π / 2), HasDerivAt W2
      (Real.cos x * (deriv f x - Real.tan x * f x - v0) - A * (π / 2 - x) * Real.cos x) x := by
    intro x hx
    rw [hW2]
    refine ((hGd x hx).add ((hJd x hx).const_mul A)).congr_deriv ?_
    ring
  -- monotonicity signs
  have hW1deriv : ∀ x ∈ Ioo θ (π / 2), 0 ≤ deriv W1 x := by
    intro x hx
    have hx0 : x ∈ Ioo (0:ℝ) (π / 2) := ⟨lt_trans hθ.1 hx.1, hx.2⟩
    rw [(hW1d x hx).deriv]
    have hcosx : 0 ≤ Real.cos x :=
      le_of_lt (Real.cos_pos_of_mem_Ioo ⟨by linarith [Real.pi_pos, hx0.1], hx0.2⟩)
    have hVle : -(A * (π / 2 - x)) ≤ deriv f x - Real.tan x * f x - v0 := by
      have := neg_abs_le (deriv f x - Real.tan x * f x - v0)
      linarith [hclose x hx0]
    have hmul := mul_le_mul_of_nonneg_left hVle hcosx
    nlinarith [hmul]
  have hW2deriv : ∀ x ∈ Ioo θ (π / 2), deriv W2 x ≤ 0 := by
    intro x hx
    have hx0 : x ∈ Ioo (0:ℝ) (π / 2) := ⟨lt_trans hθ.1 hx.1, hx.2⟩
    rw [(hW2d x hx).deriv]
    have hcosx : 0 ≤ Real.cos x :=
      le_of_lt (Real.cos_pos_of_mem_Ioo ⟨by linarith [Real.pi_pos, hx0.1], hx0.2⟩)
    have hVle : deriv f x - Real.tan x * f x - v0 ≤ A * (π / 2 - x) := by
      have := le_abs_self (deriv f x - Real.tan x * f x - v0)
      linarith [hclose x hx0]
    have hmul := mul_le_mul_of_nonneg_left hVle hcosx
    nlinarith [hmul]
  have hW1mono : MonotoneOn W1 (Icc θ (π / 2)) := by
    have hd : DifferentiableOn ℝ W1 (interior (Icc θ (π / 2))) := by
      rw [interior_Icc]; exact fun x hx => (hW1d x hx).differentiableAt.differentiableWithinAt
    have hd' : ∀ x ∈ interior (Icc θ (π / 2)), 0 ≤ deriv W1 x := by
      intro x hx; rw [interior_Icc] at hx; exact hW1deriv x hx
    exact monotoneOn_of_deriv_nonneg (convex_Icc θ (π / 2)) hW1c hd hd'
  have hW2anti : AntitoneOn W2 (Icc θ (π / 2)) := by
    have hd : DifferentiableOn ℝ W2 (interior (Icc θ (π / 2))) := by
      rw [interior_Icc]; exact fun x hx => (hW2d x hx).differentiableAt.differentiableWithinAt
    have hd' : ∀ x ∈ interior (Icc θ (π / 2)), deriv W2 x ≤ 0 := by
      intro x hx; rw [interior_Icc] at hx; exact hW2deriv x hx
    exact antitoneOn_of_deriv_nonpos (convex_Icc θ (π / 2)) hW2c hd hd'
  have hW1pi : W1 (π / 2) = 0 := by
    rw [hW1, hG, hJ]; norm_num [Real.cos_pi_div_two, Real.sin_pi_div_two]
  have hW2pi : W2 (π / 2) = 0 := by
    rw [hW2, hG, hJ]; norm_num [Real.cos_pi_div_two, Real.sin_pi_div_two]
  have hθmem : θ ∈ Icc θ (π / 2) := ⟨le_refl _, le_of_lt hθ.2⟩
  have hπmem : π / 2 ∈ Icc θ (π / 2) := ⟨le_of_lt hθ.2, le_refl _⟩
  have hle1 : G θ ≤ A * J θ := by
    have h := hW1mono hθmem hπmem (le_of_lt hθ.2)
    rw [hW1pi, hW1] at h
    linarith
  have hge2 : -(A * J θ) ≤ G θ := by
    have h := hW2anti hθmem hπmem (le_of_lt hθ.2)
    rw [hW2pi, hW2] at h
    linarith
  have hGabs : |G θ| ≤ A * J θ := abs_le.mpr ⟨hge2, hle1⟩
  -- rewrite `G θ`, `sin θ`, `cos θ` in terms of `u`
  have hJval : J θ = Real.sin u - u * Real.cos u := by
    have h2 : (π / 2 - θ) = u := by linarith [hu]
    have h3 : Real.cos θ = Real.sin u := by rw [hθ_eq, Real.cos_pi_div_two_sub]
    have h4 : Real.sin θ = Real.cos u := by rw [hθ_eq, Real.sin_pi_div_two_sub]
    simp only [hJ, h2, h3, h4]
  have hGabs' : |G θ| ≤ A * (Real.sin u - u * Real.cos u) := by
    rw [← hJval]; exact hGabs
  have hsin_eq : Real.sin θ = Real.cos u := by rw [hθ_eq, Real.sin_pi_div_two_sub]
  have hcos_eq : Real.cos θ = Real.sin u := by rw [hθ_eq, Real.cos_pi_div_two_sub]
  -- the two terms of the rewriting
  have hb1 : |Real.sin θ * G θ / Real.cos θ ^ 2| ≤ 3 * A * u := by
    have hratio : Real.sin θ * G θ / Real.cos θ ^ 2 = Real.cos u * G θ / Real.sin u ^ 2 := by
      rw [hsin_eq, hcos_eq]
    rw [hratio]
    exact axis_aux_final_bound A u (G θ) hA hu_pos hu_le hGabs'
  have hb2 : |v0 * (1 - Real.sin θ) / (2 * (1 + Real.sin θ))| ≤ |v0| * u ^ 2 := by
    have h1u : 1 - Real.sin θ ≤ u ^ 2 := by
      have h := axis_aux_one_sub_sin_le_sq θ hθ
      simpa [hu] using h
    have h2 : 0 ≤ 1 - Real.sin θ := by linarith [Real.sin_le_one θ]
    have hsinθnn : 0 ≤ Real.sin θ :=
      Real.sin_nonneg_of_mem_Icc ⟨le_of_lt hθ.1, by linarith [hθ.2, Real.pi_pos]⟩
    have hpos : 0 < 2 * (1 + Real.sin θ) := by linarith
    have h3 : (1 - Real.sin θ) / (2 * (1 + Real.sin θ)) ≤ u ^ 2 := by
      rw [div_le_iff₀ hpos]
      nlinarith [h1u, h2, sq_nonneg u, hsinθnn]
    rw [abs_div, abs_mul, abs_of_nonneg h2, abs_of_pos hpos]
    have := mul_le_mul_of_nonneg_left h3 (abs_nonneg v0)
    calc |v0| * (1 - Real.sin θ) / (2 * (1 + Real.sin θ))
        = |v0| * ((1 - Real.sin θ) / (2 * (1 + Real.sin θ))) := by ring
      _ ≤ |v0| * u ^ 2 := this
  have hfinal : |Real.sin θ * G θ / Real.cos θ ^ 2
      + v0 * (1 - Real.sin θ) / (2 * (1 + Real.sin θ))| ≤ 3 * A * u + |v0| * u ^ 2 :=
    (abs_add_le _ _).trans (add_le_add hb1 hb2)
  rw [axis_aux_tan_axis_algebra f v0 θ hθ]
  have hfin : 3 * A * u + |v0| * u ^ 2 = |v0| * (π / 2 - θ) ^ 2 + 3 * A * (π / 2 - θ) := by
    rw [hu]; ring
  rw [hfin] at hfinal
  exact hfinal

end Work.FTS_StreamBdry.SB25
end
end
-- ===== merged: Submission.Work.FTS_StreamBdry.SB25.bslOp_dilate =====
section

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

/-!
# `Work.FTS_StreamBdry.SB25.bslOp_dilate` — `bslOp` commutes with dilations of `z`

`bslOp α` is an *Euler-type* operator: its coefficients involve the weight `z` (and `z ^ 2`) next
to one (resp. two) radial derivatives, together with the purely angular operator `Lzero`.  Hence
the dilation `z ↦ lam * z` of the self-similar variable maps the operator into itself, with no
smoothness hypothesis whatsoever.

The proof is unconditional: Mathlib's `deriv` is totalised (junk value `0` where the function is
not differentiable), and the chain rule `deriv_comp_mul_left` holds for *every* `lam`, so the
identities `pz (P(lam·)) = lam · pz P (lam·)`, `pzIter 2 (P(lam·)) = lam^2 · pzIter 2 P (lam·)`
hold pointwise, while `Lzero` and the angular derivatives do not see the dilation at all
(definitionally).
-/

noncomputable section

namespace Work.FTS_StreamBdry.SB25

set_option autoImplicit false

/-! ## The radial derivatives and the dilation -/

/-- The plain radial derivative of a dilated datum.  Unconditional in `lam` (including `lam = 0`,
where both sides are the junk value `0`), because `deriv_comp_mul_left` is unconditional. -/
lemma pz_dilate_z (P : ℝ → ℝ → ℝ) (lam : ℝ) :
    Work.Spaces.pz (fun z θ => P (lam * z) θ)
      = fun z θ => lam * Work.Spaces.pz P (lam * z) θ := by
  funext z θ
  simp only [Work.Spaces.pz]
  simpa [smul_eq_mul] using deriv_comp_mul_left lam (fun ζ => P ζ θ) z

/-- `∂_z` of a constant multiple of a dilated datum. -/
lemma pz_const_mul_dilate_z (P : ℝ → ℝ → ℝ) (c lam : ℝ) :
    Work.Spaces.pz (fun z θ => c * P (lam * z) θ)
      = fun z θ => c * (lam * Work.Spaces.pz P (lam * z) θ) := by
  funext z θ
  simp only [Work.Spaces.pz]
  rw [deriv_const_mul_field (x := z) (v := fun z' => P (lam * z') θ) c]
  congr 1
  simpa [smul_eq_mul] using deriv_comp_mul_left lam (fun ζ => P ζ θ) z

/-- The iterated radial derivative of a dilated datum picks up `lam ^ n`. -/
lemma pzIter_dilate_z (P : ℝ → ℝ → ℝ) (lam : ℝ) (n : ℕ) :
    Work.Spaces.pzIter n (fun z θ => P (lam * z) θ)
      = fun z θ => lam ^ n * Work.Spaces.pzIter n P (lam * z) θ := by
  induction n with
  | zero => funext z θ; simp
  | succ n ih =>
      rw [Work.Spaces.pzIter_succ, ih, pz_const_mul_dilate_z]
      funext z θ
      rw [Work.Spaces.pzIter_succ, pow_succ]
      ring

/-- `Lzero` is a purely angular operator, so it does not see the dilation (definitional). -/
lemma Lzero_dilate_z (P : ℝ → ℝ → ℝ) (lam : ℝ) :
    Work.Elliptic.Lzero (fun z θ => P (lam * z) θ)
      = fun z θ => Work.Elliptic.Lzero P (lam * z) θ := by
  funext z θ
  rfl

/-! ## The statement -/

/-- **E2a `bslOp_dilate`**: `bslOp` commutes with dilations in `z` (unconditional). -/
theorem bslOp_dilate (α lam : ℝ) (P : ℝ → ℝ → ℝ) :
    Work.FTS_StreamBdry.SB25.BslOpDilate α lam P := by
  intro z θ
  simp only [Work.Elliptic.bslOp]
  rw [show Work.Spaces.pzIter 2 (fun z θ => P (lam * z) θ) z θ
        = lam ^ 2 * Work.Spaces.pzIter 2 P (lam * z) θ from
      congrFun (congrFun (pzIter_dilate_z P lam 2) z) θ,
      show Work.Spaces.pz (fun z θ => P (lam * z) θ) z θ
        = lam * Work.Spaces.pz P (lam * z) θ from
      congrFun (congrFun (pz_dilate_z P lam) z) θ,
      show Work.Elliptic.Lzero (fun z θ => P (lam * z) θ) z θ
        = Work.Elliptic.Lzero P (lam * z) θ from
      congrFun (congrFun (Lzero_dilate_z P lam) z) θ]
  ring

end Work.FTS_StreamBdry.SB25
end
end
-- ===== merged: Submission.Work.FTS_StreamBdry.SB25.bslOp_eq_s2_Lgs =====
section

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

noncomputable section
open scoped Real Topology
open Set Filter

namespace Work.FTS_StreamBdry.SB25

set_option autoImplicit false
set_option maxHeartbeats 1600000

/-! ### Auxiliary calculus -/

/-- Slice derivatives of a `C²` function. -/
private lemma p_slice_derivs {F : ℝ → ℝ → ℝ} {z θ : ℝ}
    (h : ContDiffAt ℝ 2 (Function.uncurry F) (z, θ)) :
    HasDerivAt (fun z' => F z' θ) (Work.Spaces.pz F z θ) z ∧
      HasDerivAt (fun θ' => F z θ') (Work.Spaces.pth F z θ) θ ∧
      HasDerivAt (fun z' => Work.Spaces.pz F z' θ) (Work.Spaces.pzIter 2 F z θ) z ∧
      HasDerivAt (fun θ' => Work.Spaces.pth F z θ') (Work.Spaces.pthIter 2 F z θ) θ := by
  have hd : DifferentiableAt ℝ (Function.uncurry F) (z, θ) := h.differentiableAt (by norm_num)
  have hsl2 : ContDiffAt ℝ 2 (fun z' => F z' θ) z := by
    have h2 := h.comp z (ContDiffAt.prodMk contDiffAt_id contDiffAt_const)
    convert h2 using 1
    funext x; rfl
  have hsl2' : ContDiffAt ℝ 2 (fun θ' => F z θ') θ := by
    have h2 := h.comp θ (ContDiffAt.prodMk contDiffAt_const contDiffAt_id)
    convert h2 using 1
    funext x; rfl
  refine ⟨?_, ?_, ?_, ?_⟩
  · have h1 : HasDerivAt (fun z' : ℝ => Function.uncurry F (z', θ))
        ((fderiv ℝ (Function.uncurry F) (z, θ)) (1, 0)) z :=
      Work.Spaces.hasDerivAt_slice_fst hd.hasFDerivAt
    rw [Work.Spaces.pz_eq_fderiv hd]
    simpa only [Function.uncurry] using h1
  · have h1 : HasDerivAt (fun θ' : ℝ => Function.uncurry F (z, θ'))
        ((fderiv ℝ (Function.uncurry F) (z, θ)) (0, 1)) θ :=
      Work.Spaces.hasDerivAt_slice_snd hd.hasFDerivAt
    rw [Work.Spaces.pth_eq_fderiv hd]
    simpa only [Function.uncurry] using h1
  · have hder : ContDiffAt ℝ 1 (deriv (fun z' => F z' θ)) z :=
      hsl2.derivWithin (m := 1) (by norm_num)
    have h3 := (hder.differentiableAt (by norm_num)).hasDerivAt
    simpa only [Work.Spaces.pz, Work.Spaces.pzIter_succ, Work.Spaces.pzIter_zero] using h3
  · have hder : ContDiffAt ℝ 1 (deriv (fun θ' => F z θ')) θ :=
      hsl2'.derivWithin (m := 1) (by norm_num)
    have h3 := (hder.differentiableAt (by norm_num)).hasDerivAt
    simpa only [Work.Spaces.pth, Work.Spaces.pthIter_succ, Work.Spaces.pthIter_zero] using h3

/-- `pth` of `tan θ · F`. -/
private lemma p_pth_tan_mul {F : ℝ → ℝ → ℝ} {z θ : ℝ}
    (h : DifferentiableAt ℝ (Function.uncurry F) (z, θ)) (hc : Real.cos θ ≠ 0) :
    Work.Spaces.pth (fun z' θ' => Real.tan θ' * F z' θ') z θ
      = (1 / Real.cos θ ^ 2) * F z θ + Real.tan θ * Work.Spaces.pth F z θ := by
  have hslice : HasDerivAt (fun θ' => F z θ') (Work.Spaces.pth F z θ) θ := by
    have h1 : HasDerivAt (fun θ' : ℝ => Function.uncurry F (z, θ'))
        ((fderiv ℝ (Function.uncurry F) (z, θ)) (0, 1)) θ :=
      Work.Spaces.hasDerivAt_slice_snd h.hasFDerivAt
    rw [Work.Spaces.pth_eq_fderiv h]
    simpa only [Function.uncurry] using h1
  have htan : HasDerivAt Real.tan (1 / Real.cos θ ^ 2) θ := by
    have h1 : HasDerivAt Real.tan (deriv Real.tan θ) θ :=
      ((Real.differentiableAt_tan (x := θ)).mpr hc).hasDerivAt
    rwa [Real.deriv_tan] at h1
  have hmul : HasDerivAt (fun θ' => Real.tan θ' * F z θ')
      ((1 / Real.cos θ ^ 2) * F z θ + Real.tan θ * Work.Spaces.pth F z θ) θ :=
    htan.mul hslice
  rw [show Work.Spaces.pth (fun z' θ' => Real.tan θ' * F z' θ') z θ
      = deriv (fun θ' => Real.tan θ' * F z θ') θ from rfl, hmul.deriv]

/-! ### The factor `sin(2θ)⁻¹` and its derivatives -/

private def gs (θ : ℝ) : ℝ := (Real.sin (2 * θ))⁻¹
private def gs1 (θ : ℝ) : ℝ := -(2 * Real.cos (2 * θ)) / (Real.sin (2 * θ)) ^ 2
private def gs2 (θ : ℝ) : ℝ :=
  4 / Real.sin (2 * θ) + 8 * Real.cos (2 * θ) ^ 2 / (Real.sin (2 * θ)) ^ 3

private lemma sinSin {θ : ℝ} : HasDerivAt (fun θ' : ℝ => Real.sin (2 * θ'))
    (2 * Real.cos (2 * θ)) θ := by
  have h2 : HasDerivAt (fun θ' : ℝ => 2 * θ') 2 θ := by
    simpa using (hasDerivAt_id θ).const_mul (2 : ℝ)
  have h3 : HasDerivAt (Real.sin ∘ fun θ' : ℝ => 2 * θ') (Real.cos (2 * θ) * 2) θ :=
    (Real.hasDerivAt_sin (2 * θ)).comp θ h2
  have h4 : Real.cos (2 * θ) * 2 = 2 * Real.cos (2 * θ) := by ring
  rw [h4] at h3
  convert h3 using 1
  funext x; rfl

private lemma cosCos {θ : ℝ} : HasDerivAt (fun θ' : ℝ => Real.cos (2 * θ'))
    (-2 * Real.sin (2 * θ)) θ := by
  have h2 : HasDerivAt (fun θ' : ℝ => 2 * θ') 2 θ := by
    simpa using (hasDerivAt_id θ).const_mul (2 : ℝ)
  have h3 : HasDerivAt (Real.cos ∘ fun θ' : ℝ => 2 * θ') (-Real.sin (2 * θ) * 2) θ :=
    (Real.hasDerivAt_cos (2 * θ)).comp θ h2
  have h4 : -Real.sin (2 * θ) * 2 = -2 * Real.sin (2 * θ) := by ring
  rw [h4] at h3
  convert h3 using 1
  funext x; rfl

private lemma hasDerivAt_gs {θ : ℝ} (h : Real.sin (2 * θ) ≠ 0) : HasDerivAt gs (gs1 θ) θ := by
  have hinv : HasDerivAt (fun θ' : ℝ => (Real.sin (2 * θ'))⁻¹)
      (-(2 * Real.cos (2 * θ)) / (Real.sin (2 * θ)) ^ 2) θ := sinSin.inv h
  show HasDerivAt (fun θ' : ℝ => (Real.sin (2 * θ'))⁻¹)
      (-(2 * Real.cos (2 * θ)) / (Real.sin (2 * θ)) ^ 2) θ
  exact hinv

private lemma hasDerivAt_gs1 {θ : ℝ} (h : Real.sin (2 * θ) ≠ 0) : HasDerivAt gs1 (gs2 θ) θ := by
  have hnum : HasDerivAt (fun θ' : ℝ => -(2 * Real.cos (2 * θ'))) (4 * Real.sin (2 * θ)) θ := by
    have h3 : HasDerivAt (fun y : ℝ => -2 * Real.cos (2 * y))
        (-2 * (-2 * Real.sin (2 * θ))) θ := cosCos.const_mul (-2 : ℝ)
    have h4 : -2 * (-2 * Real.sin (2 * θ)) = 4 * Real.sin (2 * θ) := by ring
    rw [h4] at h3
    convert h3 using 1
    funext y; ring
  have hden : HasDerivAt (fun θ' : ℝ => (Real.sin (2 * θ')) ^ 2)
      (2 * (Real.sin (2 * θ)) ^ (2 - 1) * (2 * Real.cos (2 * θ))) θ := sinSin.pow 2
  have hdenne : (Real.sin (2 * θ)) ^ 2 ≠ 0 := pow_ne_zero 2 h
  have hdiv := hnum.div hden hdenne
  have key : (4 * Real.sin (2 * θ) * (Real.sin (2 * θ)) ^ 2
        - (-(2 * Real.cos (2 * θ))) * (2 * (Real.sin (2 * θ)) ^ (2 - 1) * (2 * Real.cos (2 * θ))))
        / ((Real.sin (2 * θ)) ^ 2) ^ 2 = gs2 θ := by
    rw [gs2]
    field_simp
    ring
  rw [key] at hdiv
  show HasDerivAt (fun θ' : ℝ => -(2 * Real.cos (2 * θ')) / (Real.sin (2 * θ')) ^ 2) (gs2 θ) θ
  exact hdiv

private lemma sin2_mul_gs (θ : ℝ) (h : Real.sin (2 * θ) ≠ 0) : Real.sin (2 * θ) * gs θ = 1 := by
  rw [gs]
  exact mul_inv_cancel₀ h

private lemma sin2_mul_gs1 (θ : ℝ) (h : Real.sin (2 * θ) ≠ 0) :
    Real.sin (2 * θ) * gs1 θ = -(2 * Real.cos (2 * θ)) / Real.sin (2 * θ) := by
  rw [gs1, div_eq_mul_inv]
  field_simp

private lemma sin2_mul_gs2 (θ : ℝ) (h : Real.sin (2 * θ) ≠ 0) :
    Real.sin (2 * θ) * gs2 θ
      = 4 + 8 * Real.cos (2 * θ) ^ 2 / Real.sin (2 * θ) ^ 2 := by
  rw [gs2, div_eq_mul_inv, div_eq_mul_inv]
  field_simp

/-! ### The main identity -/

theorem bslOp_eq_s2_Lgs (α : ℝ) (Q : ℝ → ℝ → ℝ) :
    Work.FTS_StreamBdry.SB25.BslOpEqS2Lgs α Q := by
  intro z θ hQd hQ
  rw [Work.Construction.Qd, Set.mem_prod] at hQd
  obtain ⟨hz, hθ⟩ := hQd
  simp only [Work.Construction.s2]
  have hsin : Real.sin (2 * θ) ≠ 0 := by
    refine ne_of_gt (Real.sin_pos_of_pos_of_lt_pi (by linarith [hθ.1]) ?_)
    linarith [hθ.2, Real.pi_pos]
  have hcos : Real.cos θ ≠ 0 := by
    refine ne_of_gt (Real.cos_pos_of_mem_Ioo ⟨by linarith [Real.pi_pos, hθ.1], by linarith [hθ.2]⟩)
  have hsinθ : Real.sin θ ≠ 0 := by
    intro h0
    apply hsin
    rw [Real.sin_two_mul, h0]; ring
  have hcosθ : Real.cos θ ≠ 0 := by
    intro h0
    apply hsin
    rw [Real.sin_two_mul, h0]; ring
  obtain ⟨hQz, hQθ, hQzz, hQθθ⟩ := p_slice_derivs hQ
  have hQdiff : DifferentiableAt ℝ (Function.uncurry Q) (z, θ) := hQ.differentiableAt (by norm_num)
  have htan : Work.Spaces.pth (fun z' θ' => Real.tan θ' * Q z' θ') z θ
      = (1 / Real.cos θ ^ 2) * Q z θ + Real.tan θ * Work.Spaces.pth Q z θ :=
    p_pth_tan_mul hQdiff hcos
  set u : ℝ → ℝ → ℝ := fun z' θ' => Q z' θ' / Real.sin (2 * θ') with hu
  have hgs := hasDerivAt_gs hsin
  have hgs1 := hasDerivAt_gs1 hsin
  have hpzu : ∀ z' θ',
      Work.Spaces.pz u z' θ' = Work.Spaces.pz Q z' θ' / Real.sin (2 * θ') := by
    intro z' θ'
    rw [hu]
    simp only [Work.Spaces.pz]
    rw [deriv_div_const]
  have hpz2u : ∀ z' θ',
      Work.Spaces.pzIter 2 u z' θ' = Work.Spaces.pzIter 2 Q z' θ' / Real.sin (2 * θ') := by
    intro z' θ'
    show deriv (fun z'' => Work.Spaces.pz u z'' θ') z'
        = deriv (fun z'' => Work.Spaces.pz Q z'' θ') z' / Real.sin (2 * θ')
    rw [show (fun z'' => Work.Spaces.pz u z'' θ')
        = (fun z'' => Work.Spaces.pz Q z'' θ' / Real.sin (2 * θ')) from
      funext (fun z'' => hpzu z'' θ'), deriv_div_const]
  have hpthu_gen : ∀ θ', Real.sin (2 * θ') ≠ 0 → ContDiffAt ℝ 2 (Function.uncurry Q) (z, θ') →
      Work.Spaces.pth u z θ' = gs θ' * Work.Spaces.pth Q z θ' + Q z θ' * gs1 θ' := by
    intro θ' h' hQ'
    have hd' : DifferentiableAt ℝ (fun θ'' => Q z θ'') θ' :=
      ((p_slice_derivs hQ').2.1).differentiableAt
    rw [hu]
    show deriv (fun θ'' => Q z θ'' / Real.sin (2 * θ'')) θ'
        = gs θ' * Work.Spaces.pth Q z θ' + Q z θ' * gs1 θ'
    rw [show (fun θ'' => Q z θ'' / Real.sin (2 * θ'')) = (fun θ'' => gs θ'' * Q z θ'') from by
      funext θ''
      rw [gs, div_eq_mul_inv, mul_comm]]
    rw [show Work.Spaces.pth Q z θ' = deriv (fun θ'' => Q z θ'') θ' from rfl]
    rw [show (fun θ'' => gs θ'' * Q z θ'') = gs * (fun θ'' => Q z θ'') from rfl]
    rw [deriv_mul (hasDerivAt_gs h').differentiableAt hd', (hasDerivAt_gs h').deriv]
    ring
  have hpthu : Work.Spaces.pth u z θ
      = gs θ * Work.Spaces.pth Q z θ + Q z θ * gs1 θ := hpthu_gen θ hsin hQ
  have hpth2u : Work.Spaces.pthIter 2 u z θ
      = gs1 θ * Work.Spaces.pth Q z θ + gs θ * Work.Spaces.pthIter 2 Q z θ
        + (Work.Spaces.pth Q z θ * gs1 θ + Q z θ * gs2 θ) := by
    have hev : (fun θ' => Work.Spaces.pth u z θ') =ᶠ[𝓝 θ]
        (fun θ' => gs θ' * Work.Spaces.pth Q z θ' + Q z θ' * gs1 θ') := by
      have hQev : ∀ᶠ θ' in 𝓝 θ, ContDiffAt ℝ 2 (Function.uncurry Q) (z, θ') :=
        (ContinuousAt.prodMk continuousAt_const continuousAt_id).tendsto.eventually
          (hQ.eventually (by norm_num))
      have hnev : ∀ᶠ θ' in 𝓝 θ, Real.sin (2 * θ') ≠ 0 :=
        (Real.continuous_sin.continuousAt.comp
          (continuousAt_const.mul continuousAt_id)).eventually_ne hsin
      filter_upwards [hQev, hnev] with θ' h1 h2
      exact hpthu_gen θ' h2 h1
    have hd : HasDerivAt (fun θ' => gs θ' * Work.Spaces.pth Q z θ' + Q z θ' * gs1 θ')
        (gs1 θ * Work.Spaces.pth Q z θ + gs θ * Work.Spaces.pthIter 2 Q z θ
          + (Work.Spaces.pth Q z θ * gs1 θ + Q z θ * gs2 θ)) θ :=
      (hgs.mul hQθθ).add (hQθ.mul hgs1)
    show deriv (fun θ' => Work.Spaces.pth u z θ') θ = _
    rw [hev.deriv_eq, hd.deriv]
  have hC1 : Real.sin (2 * θ) * Work.Spaces.pz u z θ = Work.Spaces.pz Q z θ := by
    rw [hpzu z θ]
    exact mul_div_cancel₀ _ hsin
  have hC2 : Real.sin (2 * θ) * Work.Spaces.pzIter 2 u z θ = Work.Spaces.pzIter 2 Q z θ := by
    rw [hpz2u z θ]
    exact mul_div_cancel₀ _ hsin
  have hC3 : Real.sin (2 * θ) * Work.Spaces.pth u z θ
      = Work.Spaces.pth Q z θ - Q z θ * (2 * Real.cos (2 * θ)) / Real.sin (2 * θ) := by
    rw [hpthu, mul_add]
    rw [show Real.sin (2 * θ) * (gs θ * Work.Spaces.pth Q z θ)
        = (Real.sin (2 * θ) * gs θ) * Work.Spaces.pth Q z θ from by ring,
      sin2_mul_gs θ hsin, one_mul]
    rw [show Real.sin (2 * θ) * (Q z θ * gs1 θ)
        = Q z θ * (Real.sin (2 * θ) * gs1 θ) from by ring, sin2_mul_gs1 θ hsin]
    ring
  have hC4 : Real.sin (2 * θ) * Work.Spaces.pthIter 2 u z θ
      = Work.Spaces.pthIter 2 Q z θ
        - (2 * Real.cos (2 * θ) / Real.sin (2 * θ)) * Work.Spaces.pth Q z θ
        - (2 * Real.cos (2 * θ) / Real.sin (2 * θ)) * Work.Spaces.pth Q z θ
        + (4 + 8 * Real.cos (2 * θ) ^ 2 / Real.sin (2 * θ) ^ 2) * Q z θ := by
    rw [hpth2u]
    rw [show Real.sin (2 * θ) * (gs1 θ * Work.Spaces.pth Q z θ
          + gs θ * Work.Spaces.pthIter 2 Q z θ
          + (Work.Spaces.pth Q z θ * gs1 θ + Q z θ * gs2 θ))
        = (Real.sin (2 * θ) * gs1 θ) * Work.Spaces.pth Q z θ
          + (Real.sin (2 * θ) * gs θ) * Work.Spaces.pthIter 2 Q z θ
          + (Work.Spaces.pth Q z θ * (Real.sin (2 * θ) * gs1 θ)
            + Q z θ * (Real.sin (2 * θ) * gs2 θ)) from by ring]
    rw [sin2_mul_gs θ hsin, sin2_mul_gs1 θ hsin, sin2_mul_gs2 θ hsin]
    ring
  have key_z : Real.sin (2 * θ) * (-(α ^ 2) * Work.Spaces.DzIter 2 u z θ
        - 5 * α * Work.Spaces.Dz u z θ)
      = -(α ^ 2 * z ^ 2) * Work.Spaces.pzIter 2 Q z θ
        - α * (5 + α) * z * Work.Spaces.pz Q z θ := by
    have hDzu : Work.Spaces.Dz u z θ = z * Work.Spaces.pz u z θ := rfl
    have hDzI : Work.Spaces.DzIter 2 u z θ
        = z * (Work.Spaces.pz u z θ + z * Work.Spaces.pzIter 2 u z θ) := by
      have hslice : HasDerivAt (fun z' => Work.Spaces.pz u z' θ)
          (Work.Spaces.pzIter 2 u z θ) z := by
        have h1 : (fun z' => Work.Spaces.pz u z' θ)
            = (fun z' => Work.Spaces.pz Q z' θ / Real.sin (2 * θ)) :=
          funext (fun z' => hpzu z' θ)
        rw [h1, hpz2u z θ]
        exact hQzz.div_const (Real.sin (2 * θ))
      have hprod : HasDerivAt (fun z' => z' * Work.Spaces.pz u z' θ)
          (1 * Work.Spaces.pz u z θ + z * Work.Spaces.pzIter 2 u z θ) z :=
        (hasDerivAt_id z).mul hslice
      show z * deriv (fun z' => z' * Work.Spaces.pz u z' θ) z
          = z * (Work.Spaces.pz u z θ + z * Work.Spaces.pzIter 2 u z θ)
      rw [hprod.deriv]
      ring
    rw [hDzI, hDzu]
    rw [show Real.sin (2 * θ) * (-(α ^ 2) * (z * (Work.Spaces.pz u z θ
            + z * Work.Spaces.pzIter 2 u z θ)) - 5 * α * (z * Work.Spaces.pz u z θ))
        = -(α ^ 2) * (z * (Real.sin (2 * θ) * Work.Spaces.pz u z θ)
            + z ^ 2 * (Real.sin (2 * θ) * Work.Spaces.pzIter 2 u z θ))
          - 5 * α * (z * (Real.sin (2 * θ) * Work.Spaces.pz u z θ)) from by ring]
    rw [hC1, hC2]
    ring
  have key_t : Real.sin (2 * θ) * (-(Work.Spaces.pthIter 2 u z θ)
        - (4 * Real.cos (2 * θ) / Real.sin (2 * θ) - Real.tan θ) * Work.Spaces.pth u z θ)
      = -(Work.Spaces.pthIter 2 Q z θ)
        + Work.Spaces.pth (fun z' θ' => Real.tan θ' * Q z' θ') z θ - 6 * Q z θ := by
    rw [htan]
    rw [show Real.sin (2 * θ) * (-(Work.Spaces.pthIter 2 u z θ)
          - (4 * Real.cos (2 * θ) / Real.sin (2 * θ) - Real.tan θ) * Work.Spaces.pth u z θ)
        = -(Real.sin (2 * θ) * Work.Spaces.pthIter 2 u z θ)
          - (4 * Real.cos (2 * θ) / Real.sin (2 * θ) - Real.tan θ)
            * (Real.sin (2 * θ) * Work.Spaces.pth u z θ) from by ring]
    rw [hC3, hC4]
    have ht2 : 1 / Real.cos θ ^ 2 = 1 + Real.tan θ ^ 2 := by
      rw [Real.tan_eq_sin_div_cos]
      field_simp
      rw [← Real.sin_sq_add_cos_sq θ]
      ring
    rw [ht2]
    rw [Real.tan_eq_sin_div_cos, Real.sin_two_mul, Real.cos_two_mul]
    field_simp
    ring_nf
    have hpyth : Real.cos θ ^ 2 = 1 - Real.sin θ ^ 2 := by
      have := Real.sin_sq_add_cos_sq θ
      linarith
    rw [hpyth]
    ring
  rw [Work.Elliptic.bslOp_apply, Work.Elliptic.Lzero, Lgs]
  rw [show Real.sin (2 * θ) * (-(α ^ 2) * Work.Spaces.DzIter 2 u z θ
        - 5 * α * Work.Spaces.Dz u z θ - Work.Spaces.pthIter 2 u z θ
        - (4 * Real.cos (2 * θ) / Real.sin (2 * θ) - Real.tan θ) * Work.Spaces.pth u z θ)
      = Real.sin (2 * θ) * (-(α ^ 2) * Work.Spaces.DzIter 2 u z θ
          - 5 * α * Work.Spaces.Dz u z θ)
        + Real.sin (2 * θ) * (-(Work.Spaces.pthIter 2 u z θ)
          - (4 * Real.cos (2 * θ) / Real.sin (2 * θ) - Real.tan θ)
            * Work.Spaces.pth u z θ) from by ring]
  rw [key_z, key_t]

end Work.FTS_StreamBdry.SB25
end
end
-- ===== merged: Submission.Work.FTS_StreamBdry.SB25.bslOp_lincombQd =====
section

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

namespace Work.FTS_StreamBdry.SB25

/-! ## Linearity of `bslOp` on the open quadrant

`Work.Elliptic.bslOp α = -α²z²∂_zz - α(5+α)z∂_z + L₀` with
`L₀ = -∂_θθ + ∂_θ(tan θ · ·) - 6` is a linear differential operator.  Its additivity is
`Work.Elliptic.bslOp_add` (hypotheses: `Real.cos θ ≠ 0` and `C²` at the point for both summands)
and its homogeneity is `Work.FTS.BSIdent.OddExt.bslOp_const_mul` (no differentiability needed:
`deriv` commutes with a constant unconditionally).  The two combine into
`BslOpLincomb α a b P Q`, the statement needed by the SB2/SB5 chain.

The `Qd`-restriction and the `C²` hypotheses are not decoration: `Real.tan` is not
differentiable at `θ = π/2`, and `deriv` is totalised, so both additivity and (in the
non-constant-coefficient slots) homogeneity genuinely fail without them — see
`Submission/Work/FTS_StreamBdry/SB25/bslOp_lincomb.lean` and `_counter.lean`. -/

/-- `Function.uncurry` of a constant multiple. -/
private lemma uncurry_const_mul (c : ℝ) (P : ℝ → ℝ → ℝ) :
    Function.uncurry (fun z' θ' => c * P z' θ')
      = fun y : ℝ × ℝ => c * Function.uncurry P y := by
  funext y
  rcases y with ⟨z, θ⟩
  rfl

/-- Multiplication by a constant preserves `C^n` at a point, in the `Function.uncurry` shape in
which the hypotheses of `BslOpLincomb` are phrased. -/
private lemma contDiffAt_uncurry_const_mul {P : ℝ → ℝ → ℝ} {z θ c : ℝ} {n : WithTop ℕ∞}
    (hP : ContDiffAt ℝ n (Function.uncurry P) (z, θ)) :
    ContDiffAt ℝ n (Function.uncurry (fun z' θ' => c * P z' θ')) (z, θ) := by
  have h : ContDiffAt ℝ n (fun y : ℝ × ℝ => c * Function.uncurry P y) (z, θ) := by
    simpa only [smul_eq_mul] using hP.const_smul c
  simpa only [uncurry_const_mul] using h

theorem bslOp_lincombQd (α a b : ℝ) (P Q : ℝ → ℝ → ℝ) :
    Work.FTS_StreamBdry.SB25.BslOpLincomb α a b P Q := by
  intro z θ hmem hP hQ
  have hcos : Real.cos θ ≠ 0 := ne_of_gt (Work.FTS_StreamBdry.cos_pos_of_Qd hmem)
  rw [Work.Elliptic.bslOp_add α (fun z' θ' => a * P z' θ') (fun z' θ' => b * Q z' θ') z θ hcos
      (contDiffAt_uncurry_const_mul (c := a) hP) (contDiffAt_uncurry_const_mul (c := b) hQ),
    Work.FTS.BSIdent.OddExt.bslOp_const_mul α a P z θ,
    Work.FTS.BSIdent.OddExt.bslOp_const_mul α b Q z θ]

end Work.FTS_StreamBdry.SB25
end
-- ===== merged: Submission.Work.FTS_StreamBdry.SB25.contDiffOn_two_of_partials =====
section

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

/-!
# `Work.FTS_StreamBdry.SB25.contDiffOn_two_of_partials` (leaf B7b)

`ContDiffTwoOfPartials h U` says: on an **open** set `U ⊆ ℝ × ℝ`, if `uncurry h` is `C¹` and
both plain partial derivatives `uncurry (pz h)` and `uncurry (pth h)` are `C¹`, then `uncurry h`
is `C²`.

This is the standard "`C¹` with `C¹` partials gives `C²`" statement, in the form needed by the
`θ`-gluing argument (`glue_line_C2`).  The proof:

* the candidate second-order derivative of `f := uncurry h` at `u = (a, b)` is the continuous
  linear map `A u := ∂_z h (a,b) • ε₁ + ∂_θ h (a,b) • ε₂`, i.e.
  `(toSpanSingleton ℝ (pz h a b)).coprod (toSpanSingleton ℝ (pth h a b))`;
* `A` is `C¹` on `U`, because for every fixed `y : ℝ × ℝ` the function
  `u ↦ A u y = ∂_z h u * y.1 + ∂_θ h u * y.2` is a linear combination of the two hypotheses
  (and `contDiffOn_clm_apply` reduces the `C¹`-ness of a continuous-linear-map-valued function
  to the `C¹`-ness of all its applications);
* `f` has Fréchet derivative `A u` at every `u ∈ U`, by `hasStrictFDerivAt_uncurry_coprod`: the
  `z`-slice of `f` near `u` is differentiable with derivative `∂_z h` (its Fréchet derivative in
  the direction `(1,0)`, and `pz h` is by definition the slice derivative), the `θ`-slice
  similarly, and both partial-derivative families are continuous at `u` because `pz h`, `pth h`
  are `C¹` (hence continuous) there;
* the criterion `contDiffOn_succ_iff_hasFDerivWithinAt_of_uniqueDiffOn` with `n = 1` (and
  `U` open, so `UniqueDiffOn ℝ U`) then concludes.
-/

noncomputable section

open Set Filter
open scoped Topology ContDiff

namespace Work.FTS_StreamBdry.SB25

set_option autoImplicit false

/-- On `ℝ`, the "span of `c`" linear functional is `c` times the identity. -/
private lemma toSpanSingleton_eq_smul_one (c : ℝ) :
    ContinuousLinearMap.toSpanSingleton ℝ c = c • (1 : ℝ →L[ℝ] ℝ) := by
  apply ContinuousLinearMap.ext
  intro t
  simp [ContinuousLinearMap.toSpanSingleton_apply, smul_eq_mul, mul_comm]

theorem contDiffOn_two_of_partials (h : ℝ → ℝ → ℝ) (U : Set (ℝ × ℝ)) :
    Work.FTS_StreamBdry.SB25.ContDiffTwoOfPartials h U := by
  intro hU h1 hz hθ
  -- the candidate second derivative of `uncurry h`
  let f₁ : ℝ → ℝ → (ℝ →L[ℝ] ℝ) := fun a b =>
    ContinuousLinearMap.toSpanSingleton ℝ (Work.Spaces.pz h a b)
  let f₂ : ℝ → ℝ → (ℝ →L[ℝ] ℝ) := fun a b =>
    ContinuousLinearMap.toSpanSingleton ℝ (Work.Spaces.pth h a b)
  let A : ℝ × ℝ → (ℝ × ℝ →L[ℝ] ℝ) := fun u => (f₁ u.1 u.2).coprod (f₂ u.1 u.2)
  -- `A` is `C¹`, componentwise
  have hA : ContDiffOn ℝ 1 A U := by
    rw [contDiffOn_clm_apply]
    intro y
    have hz' : ContDiffOn ℝ 1 (fun u : ℝ × ℝ => Work.Spaces.pz h u.1 u.2) U := hz
    have hθ' : ContDiffOn ℝ 1 (fun u : ℝ × ℝ => Work.Spaces.pth h u.1 u.2) U := hθ
    have hsum : ContDiffOn ℝ 1 (fun u : ℝ × ℝ =>
        Work.Spaces.pz h u.1 u.2 • (y.1 : ℝ) + Work.Spaces.pth h u.1 u.2 • (y.2 : ℝ)) U :=
      (hz'.smul_const y.1).add (hθ'.smul_const y.2)
    refine hsum.congr (fun u hu => ?_)
    simp only [A, f₁, f₂, ContinuousLinearMap.coprod_apply,
      ContinuousLinearMap.toSpanSingleton_apply, smul_eq_mul]
    ring
  -- `uncurry h` has Fréchet derivative `A u` at every `u ∈ U`
  have hderiv : ∀ u ∈ U, HasFDerivAt (Function.uncurry h) (A u) u := by
    intro u hu
    have hf₁ : ∀ᶠ v in 𝓝 u, HasFDerivAt (fun z : ℝ => h z v.2) (↿f₁ v) v.1 := by
      filter_upwards [hU.mem_nhds hu] with v hv
      have hc : ContDiffAt ℝ 1 (Function.uncurry h) v := h1.contDiffAt (hU.mem_nhds hv)
      have hd : DifferentiableAt ℝ (fun p : ℝ × ℝ => h p.1 p.2) v :=
        hc.differentiableAt (by norm_num)
      have hpair : HasFDerivAt (fun z : ℝ => ((z, v.2) : ℝ × ℝ))
          ((1 : ℝ →L[ℝ] ℝ).prod (0 : ℝ →L[ℝ] ℝ)) v.1 :=
        (hasFDerivAt_id (x := v.1)).prodMk (hasFDerivAt_const (x := v.1) v.2)
      have hcomp := (hd.hasFDerivAt.comp v.1 hpair).hasDerivAt
      -- the slice derivative is `pz h v.1 v.2` by definition of `pz`
      have hder : HasDerivAt (fun z : ℝ => h z v.2) (Work.Spaces.pz h v.1 v.2) v.1 := by
        have hval : Work.Spaces.pz h v.1 v.2
            = ((fderiv ℝ (fun p : ℝ × ℝ => h p.1 p.2) v).comp
                ((1 : ℝ →L[ℝ] ℝ).prod (0 : ℝ →L[ℝ] ℝ))) 1 := by
          simp only [Work.Spaces.pz]
          exact hcomp.deriv
        rw [hval]
        exact hcomp
      exact hder.hasFDerivAt
    have hf₂ : ∀ᶠ v in 𝓝 u, HasFDerivAt (fun z : ℝ => h v.1 z) (↿f₂ v) v.2 := by
      filter_upwards [hU.mem_nhds hu] with v hv
      have hc : ContDiffAt ℝ 1 (Function.uncurry h) v := h1.contDiffAt (hU.mem_nhds hv)
      have hd : DifferentiableAt ℝ (fun p : ℝ × ℝ => h p.1 p.2) v :=
        hc.differentiableAt (by norm_num)
      have hpair : HasFDerivAt (fun z : ℝ => ((v.1, z) : ℝ × ℝ))
          ((0 : ℝ →L[ℝ] ℝ).prod (1 : ℝ →L[ℝ] ℝ)) v.2 :=
        (hasFDerivAt_const (x := v.2) v.1).prodMk (hasFDerivAt_id (x := v.2))
      have hcomp := (hd.hasFDerivAt.comp v.2 hpair).hasDerivAt
      have hder : HasDerivAt (fun z : ℝ => h v.1 z) (Work.Spaces.pth h v.1 v.2) v.2 := by
        have hval : Work.Spaces.pth h v.1 v.2
            = ((fderiv ℝ (fun p : ℝ × ℝ => h p.1 p.2) v).comp
                ((0 : ℝ →L[ℝ] ℝ).prod (1 : ℝ →L[ℝ] ℝ))) 1 := by
          simp only [Work.Spaces.pth]
          exact hcomp.deriv
        rw [hval]
        exact hcomp
      exact hder.hasFDerivAt
    -- the two partial-derivative families are continuous at `u`
    have hcf₁ : ContinuousAt (↿f₁) u := by
      have hcont : ContinuousAt (fun v : ℝ × ℝ => Work.Spaces.pz h v.1 v.2) u :=
        hz.continuousOn.continuousAt (hU.mem_nhds hu)
      have heq : (↿f₁) = fun v : ℝ × ℝ => (Work.Spaces.pz h v.1 v.2) • (1 : ℝ →L[ℝ] ℝ) := by
        funext v
        exact toSpanSingleton_eq_smul_one _
      exact (hcont.smul continuousAt_const).congr (Filter.EventuallyEq.of_eq heq.symm)
    have hcf₂ : ContinuousAt (↿f₂) u := by
      have hcont : ContinuousAt (fun v : ℝ × ℝ => Work.Spaces.pth h v.1 v.2) u :=
        hθ.continuousOn.continuousAt (hU.mem_nhds hu)
      have heq : (↿f₂) = fun v : ℝ × ℝ => (Work.Spaces.pth h v.1 v.2) • (1 : ℝ →L[ℝ] ℝ) := by
        funext v
        exact toSpanSingleton_eq_smul_one _
      exact (hcont.smul continuousAt_const).congr (Filter.EventuallyEq.of_eq heq.symm)
    exact (hasStrictFDerivAt_uncurry_coprod (𝕜 := ℝ) (u := u) (f := h)
      (f₁ := f₁) (f₂ := f₂) hf₁ hf₂ hcf₁ hcf₂).hasFDerivAt
  -- `C¹` with `C¹` first derivative is `C²`
  have key := contDiffOn_succ_iff_hasFDerivWithinAt_of_uniqueDiffOn (𝕜 := ℝ)
    (s := U) (f := Function.uncurry h) (n := 1) hU.uniqueDiffOn
  rw [show (2 : ℕ∞ω) = 1 + 1 from rfl]
  refine key.2 ⟨?_, A, hA, ?_⟩
  · intro hh
    exact absurd hh (by simp)
  · intro x hx
    exact (hderiv x hx).hasFDerivWithinAt

end Work.FTS_StreamBdry.SB25
end
end
-- ===== merged: Submission.Work.FTS_StreamBdry.SB25.dq1_facts =====
section

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

/-!
# `Work.FTS_StreamBdry.SB25.dq1_facts` — the first log-difference quotient

`Dq1Facts g L B` says: if `g` is differentiable on `[L, ∞)` (`L > 0`) and `|z g'(z)| ≤ B`
there, then for every `h > 0` the first difference quotient along the multiplicative ray
`z ↦ z e^h` is bounded by `B`, and it converges to `z g'(z)` as `h → 0⁺`.

The proof is the mean value theorem applied to the one-variable function
`t ↦ g (z e^t)`, whose derivative is `g'(z e^t) · z e^t`; the hypothesis `|z g'(z)| ≤ B`
controls it along the whole ray (since `e^t ≥ 1` for `t ≥ 0`).  The endpoint limit is
exactly the statement that this derivative at `t = 0` is `z g'(z)`.
-/

namespace Work.FTS_StreamBdry.SB25

theorem dq1_facts (g : ℝ → ℝ) (L B : ℝ) :
    Work.FTS_StreamBdry.SB25.Dq1Facts g L B := by
  unfold Work.FTS_StreamBdry.SB25.Dq1Facts
  intro hL hdiff hbnd
  refine ⟨?_, ?_⟩
  · -- first conjunct: the difference quotient is bounded by `B`
    intro h hh z hz
    have hz' : 0 < z := lt_of_lt_of_le hL hz
    -- the ray function `t ↦ g (z e^t)`
    let F : ℝ → ℝ := fun t => g (Real.exp t * z)
    have hFdiff : ∀ t ∈ Set.Icc (0 : ℝ) h, DifferentiableAt ℝ F t := by
      intro t ht
      have hle : L ≤ Real.exp t * z :=
        le_trans hz (le_mul_of_one_le_left hz'.le (Real.one_le_exp ht.1))
      exact (hdiff _ hle).comp t (Real.differentiableAt_exp.mul_const z)
    have hFderiv : ∀ t : ℝ, 0 ≤ t →
        deriv F t = deriv g (Real.exp t * z) * (Real.exp t * z) := by
      intro t ht
      have hle : L ≤ Real.exp t * z :=
        le_trans hz (le_mul_of_one_le_left hz'.le (Real.one_le_exp ht))
      have h1 : HasDerivAt (fun s : ℝ => Real.exp s * z) (Real.exp t * z) t := by
        simpa using (Real.hasDerivAt_exp t).mul_const z
      have h2 : DifferentiableAt ℝ g (Real.exp t * z) := hdiff _ hle
      have h3 : HasDerivAt F (deriv g (Real.exp t * z) * (Real.exp t * z)) t := by
        simpa [F, Function.comp_def] using (h2.hasDerivAt).comp t h1
      exact h3.deriv
    have hbound : ∀ t ∈ Set.Icc (0 : ℝ) h, ‖deriv F t‖ ≤ B := by
      intro t ht
      rw [hFderiv t ht.1, Real.norm_eq_abs]
      have hle : L ≤ Real.exp t * z :=
        le_trans hz (le_mul_of_one_le_left hz'.le (Real.one_le_exp ht.1))
      have hb := hbnd (Real.exp t * z) hle
      rw [mul_comm (Real.exp t * z) (deriv g (Real.exp t * z))] at hb
      exact hb
    have hMVT := Convex.norm_image_sub_le_of_norm_deriv_le (f := F) (s := Set.Icc (0 : ℝ) h)
      (x := 0) (y := h) (C := B) hFdiff hbound (convex_Icc 0 h)
      ⟨le_rfl, hh.le⟩ ⟨hh.le, le_rfl⟩
    have hmain : |F h - F 0| ≤ B * h := by
      simpa [Real.norm_eq_abs, sub_zero, Real.norm_of_nonneg hh.le] using hMVT
    have hFh : F h = g (Real.exp h * z) := rfl
    have hF0 : F 0 = g z := by simp [F]
    rw [hFh, hF0] at hmain
    rw [abs_div, abs_of_pos hh]
    exact (div_le_iff₀ hh).mpr hmain
  · -- second conjunct: the difference quotient tends to `z g'(z)` as `h → 0⁺`
    intro z hz
    have hd : HasDerivAt (fun t : ℝ => g (Real.exp t * z)) (z * deriv g z) 0 := by
      have h1 : HasDerivAt (fun s : ℝ => Real.exp s * z) (Real.exp 0 * z) 0 := by
        simpa using (Real.hasDerivAt_exp 0).mul_const z
      have h2 : DifferentiableAt ℝ g (Real.exp 0 * z) := by
        simpa using hdiff z hz.le
      have hgoal : HasDerivAt (fun t : ℝ => g (Real.exp t * z))
          (deriv g (Real.exp 0 * z) * (Real.exp 0 * z)) 0 := by
        simpa [Function.comp_def] using (h2.hasDerivAt).comp 0 h1
      convert hgoal using 1
      rw [Real.exp_zero, one_mul, mul_comm]
    -- `hd.tendsto_slope_zero_right` is the limit of `h ↦ h⁻¹ • (g (z e^h) - g z)`; rewrite
    -- it into the stated division form.
    have key := hd.tendsto_slope_zero_right
    convert key using 1
    · ext h
      simp [div_eq_mul_inv, mul_comm]

end Work.FTS_StreamBdry.SB25
end
-- ===== merged: Submission.Work.FTS_StreamBdry.SB25.dq2_facts =====
section

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

/-!
# `Work.FTS_StreamBdry.SB25.dq2_facts` — the second log-difference quotient (leaf E6b)

For `g : ℝ → ℝ` with `Dg z := z ∂_z g z` differentiable on `[L, ∞)` (`0 < L`), its
logarithmic derivative `D²g z := z ∂_z (Dg) z` bounded by `B` there and `D²g` continuous on
`[L, ∞)`:

* `|(g (e^{2h} z) - 2 g (e^h z) + g z) / h²| ≤ B` for every `h > 0`, `z ≥ L`;
* `(g (e^{2h} z) - 2 g (e^h z) + g z) / h² → D²g z` as `h → 0⁺`, for `z > L`.

## Route

Fix `z` and put `ψ s = g (z e^s)`.  Then `ψ' = Dg ∘ (z e^·)` and `ψ'' = D²g ∘ (z e^·)`, so
the difference considered is the second difference of the one-variable function `ψ`, and the
two conclusions are the two halves of §2 below:

`dq2_secondDiff_sub_le` — the sharp second-difference bound
`|ψ (2h) - 2 ψ h + ψ 0 - d h²| ≤ C h²` whenever `|c - d| ≤ C` on `[0, 2h]`, where `b = ψ'`
and `c = b'`.  The proof is integration by parts free: writing
`ψ (2h) - 2 ψ h + ψ 0 = ∫₀ʰ (b (u + h) - b u) du` (two applications of the fundamental
theorem, the substitution `∫_h^{2h} b = ∫₀ʰ b (· + h)`, and additivity of the interval
integral), the `d`-correction is an integral of the constant `d h` over `[0, h]`, and each
increment `b (u+h) - b u - d h = ∫_u^{u+h} (c - d)` is bounded by `C h` using
`|c - d| ≤ C`.

`dq2_secondDiff_tendsto` — the limit `(ψ (2h) - 2 ψ h + ψ 0)/h² → c 0` as `h → 0⁺`, which
follows from the bound applied with `d := c 0` and `C := ε/2`, the continuity of `c` at `0`
supplying `|c t - c 0| ≤ ε/2` on `[0, 2h]` for small `h`.

The passage from the hypotheses of `Dq2Facts` to those of the two lemmas needs the continuity
of `Dg` on `[L, ∞)`; that is `dq2_Dg_cont` below (mean value theorem: `|∂_z(Dg) u| ≤ B / L`),
the chain rule `dq2_psi_hasDerivAt` / `dq2_b_hasDerivAt`, and the two continuity statements
`dq2_b_cont` / `dq2_c_cont`.
-/

noncomputable section
open scoped Real Topology
open Set Filter MeasureTheory

namespace Work.FTS_StreamBdry.SB25

set_option autoImplicit false

/-! ## §0 Elementary consequences of the hypotheses -/

/-- The exponential map `s ↦ z e^s` sends the strip `[0,T]` (`T ≥ 0`) into `[L, ∞)` for
`z ≥ L > 0`. -/
private lemma dq2_mapsTo (z L : ℝ) (hL : 0 < L) (hz : L ≤ z) (T : ℝ) :
    Set.MapsTo (fun s : ℝ => z * Real.exp s) (Set.Icc 0 T) (Set.Ici L) := by
  intro s hs
  have hs0 : 0 ≤ s := hs.1
  have hexp : 1 ≤ Real.exp s := Real.one_le_exp hs0
  have hz0 : 0 ≤ z := le_trans (le_of_lt hL) hz
  have hmono : z * 1 ≤ z * Real.exp s := mul_le_mul_of_nonneg_left hexp hz0
  calc L ≤ z := hz
    _ = z * 1 := (mul_one z).symm
    _ ≤ z * Real.exp s := hmono

/-- **`Dg = z ∂_z g` is continuous on `[L, ∞)`**: it is `(B/L)`-Lipschitz there as soon as
`|z ∂_z(Dg) z| ≤ B` on `[L, ∞)`. -/
private lemma dq2_Dg_cont (g : ℝ → ℝ) (L B : ℝ) (hL : 0 < L)
    (hd : ∀ z, L ≤ z → DifferentiableAt ℝ g z ∧
      DifferentiableAt ℝ (fun z' => z' * deriv g z') z)
    (hB : ∀ z, L ≤ z → |z * deriv (fun z' => z' * deriv g z') z| ≤ B) :
    ContinuousOn (fun z => z * deriv g z) (Set.Ici L) := by
  have hB0 : 0 ≤ B := le_trans (abs_nonneg _) (hB L le_rfl)
  have hbnd : ∀ x ∈ Set.Ici L, ‖deriv (fun z => z * deriv g z) x‖ ≤ B / L := by
    intro x hx
    have hxpos : 0 < x := lt_of_lt_of_le hL hx
    have hxne : x ≠ 0 := ne_of_gt hxpos
    have h2 : |deriv (fun z => z * deriv g z) x|
        = |x * deriv (fun z' => z' * deriv g z') x| / x := by
      have hthis : deriv (fun z => z * deriv g z) x
          = x * deriv (fun z' => z' * deriv g z') x / x :=
        (mul_div_cancel_left₀ _ hxne).symm
      conv_lhs => rw [hthis]
      rw [abs_div, abs_of_pos hxpos]
    calc ‖deriv (fun z => z * deriv g z) x‖
        = |deriv (fun z => z * deriv g z) x| := by rw [Real.norm_eq_abs]
      _ = |x * deriv (fun z' => z' * deriv g z') x| / x := h2
      _ ≤ B / x := div_le_div_of_nonneg_right (hB x hx) (le_of_lt hxpos)
      _ ≤ B / L := div_le_div_of_nonneg_left hB0 hL hx
  have hlip : ∀ a b : ℝ, L ≤ a → L ≤ b →
      |b * deriv g b - a * deriv g a| ≤ (B / L) * |b - a| := by
    intro a b ha hb
    have hmain := Convex.norm_image_sub_le_of_norm_deriv_le
      (f := fun z => z * deriv g z) (s := Set.Ici L)
      (fun x hx => (hd x hx).2) hbnd (convex_Ici L) ha hb
    simpa only [Real.norm_eq_abs] using hmain
  rw [Metric.continuousOn_iff]
  intro x hx ε hε
  refine ⟨ε / (B / L + 1), by positivity, ?_⟩
  intro y hy hxy
  have hC1 : 0 < B / L + 1 := by positivity
  have h : |y * deriv g y - x * deriv g x| ≤ (B / L + 1) * dist y x := by
    have h1 : |y * deriv g y - x * deriv g x| ≤ (B / L) * |y - x| := hlip x y hx hy
    have h2 : |y - x| = dist y x := (Real.dist_eq y x).symm
    calc |y * deriv g y - x * deriv g x| ≤ (B / L) * |y - x| := h1
      _ = (B / L) * dist y x := by rw [h2]
      _ ≤ (B / L + 1) * dist y x := by nlinarith [dist_nonneg (x := y) (y := x)]
  calc dist (y * deriv g y) (x * deriv g x) = |y * deriv g y - x * deriv g x| :=
        Real.dist_eq _ _
    _ ≤ (B / L + 1) * dist y x := h
    _ < (B / L + 1) * (ε / (B / L + 1)) := mul_lt_mul_of_pos_left hxy hC1
    _ = ε := by field_simp

/-! ## §1 The chain rule for the two composite functions -/

/-- `ψ s = g (z e^s)` has derivative `Dg (z e^s)` for `s ≥ 0`, `z ≥ L`. -/
private lemma dq2_psi_hasDerivAt (g : ℝ → ℝ) (L : ℝ) (hL : 0 < L)
    (hd : ∀ z, L ≤ z → DifferentiableAt ℝ g z ∧
      DifferentiableAt ℝ (fun z' => z' * deriv g z') z)
    {z : ℝ} (hz : L ≤ z) {s : ℝ} (hs : 0 ≤ s) :
    HasDerivAt (fun s' : ℝ => g (z * Real.exp s'))
      ((z * Real.exp s) * deriv g (z * Real.exp s)) s := by
  have hzL : L ≤ z * Real.exp s := dq2_mapsTo z L hL hz s ⟨hs, le_refl s⟩
  have h1 : HasDerivAt g (deriv g (z * Real.exp s)) (z * Real.exp s) :=
    (hd (z * Real.exp s) hzL).1.hasDerivAt
  have h2 : HasDerivAt (fun s' : ℝ => z * Real.exp s') (z * Real.exp s) s :=
    (Real.hasDerivAt_exp s).const_mul z
  have h3 := h1.comp s h2
  simpa only [Function.comp_def, mul_comm] using h3

/-- `b s = Dg (z e^s)` has derivative `D²g (z e^s)` (i.e. `z e^s ∂_z(Dg) (z e^s)`) for
`s ≥ 0`, `z ≥ L`. -/
private lemma dq2_b_hasDerivAt (g : ℝ → ℝ) (L : ℝ) (hL : 0 < L)
    (hd : ∀ z, L ≤ z → DifferentiableAt ℝ g z ∧
      DifferentiableAt ℝ (fun z' => z' * deriv g z') z)
    {z : ℝ} (hz : L ≤ z) {s : ℝ} (hs : 0 ≤ s) :
    HasDerivAt (fun s' : ℝ => (z * Real.exp s') * deriv g (z * Real.exp s'))
      ((z * Real.exp s) * deriv (fun z' => z' * deriv g z') (z * Real.exp s)) s := by
  have hzL : L ≤ z * Real.exp s := dq2_mapsTo z L hL hz s ⟨hs, le_refl s⟩
  have h1 : HasDerivAt (fun z' : ℝ => z' * deriv g z')
      (deriv (fun z' : ℝ => z' * deriv g z') (z * Real.exp s)) (z * Real.exp s) :=
    (hd (z * Real.exp s) hzL).2.hasDerivAt
  have h2 : HasDerivAt (fun s' : ℝ => z * Real.exp s') (z * Real.exp s) s :=
    (Real.hasDerivAt_exp s).const_mul z
  have h3 := h1.comp s h2
  simpa only [Function.comp_def, mul_comm] using h3

/-- Continuity of `s ↦ Dg (z e^s)` on `[0,T]`. -/
private lemma dq2_b_cont (g : ℝ → ℝ) (L B : ℝ) (hL : 0 < L)
    (hd : ∀ z, L ≤ z → DifferentiableAt ℝ g z ∧
      DifferentiableAt ℝ (fun z' => z' * deriv g z') z)
    (hB : ∀ z, L ≤ z → |z * deriv (fun z' => z' * deriv g z') z| ≤ B)
    {z : ℝ} (hz : L ≤ z) (T : ℝ) :
    ContinuousOn (fun s : ℝ => (z * Real.exp s) * deriv g (z * Real.exp s)) (Set.Icc 0 T) := by
  have hDg : ContinuousOn (fun z' : ℝ => z' * deriv g z') (Set.Ici L) :=
    dq2_Dg_cont g L B hL hd hB
  have h1 : ContinuousOn (fun s : ℝ => z * Real.exp s) (Set.Icc 0 T) :=
    (continuous_const.mul Real.continuous_exp).continuousOn
  exact hDg.comp h1 (dq2_mapsTo z L hL hz T)

/-- Continuity of `s ↦ D²g (z e^s)` on `[0,T]`. -/
private lemma dq2_c_cont (g : ℝ → ℝ) (L : ℝ) (hL : 0 < L)
    (hc : ContinuousOn (fun z => z * deriv (fun z' => z' * deriv g z') z) (Set.Ici L))
    {z : ℝ} (hz : L ≤ z) (T : ℝ) :
    ContinuousOn
      (fun s : ℝ => (z * Real.exp s) * deriv (fun z' => z' * deriv g z') (z * Real.exp s))
      (Set.Icc 0 T) := by
  have h1 : ContinuousOn (fun s : ℝ => z * Real.exp s) (Set.Icc 0 T) :=
    (continuous_const.mul Real.continuous_exp).continuousOn
  exact hc.comp h1 (dq2_mapsTo z L hL hz T)

/-! ## §2 The two one-variable second-difference lemmas -/

/-- **Second-difference bound.**  If `b = ψ'` and `c = b'` on `[0, 2h]` and `c` is
`C`-close to the constant `d` there, then `ψ (2h) - 2 ψ h + ψ 0` is `C h²`-close to `d h²`.

Proof: `ψ (2h) - 2 ψ h + ψ 0 = ∫₀ʰ (b (u + h) - b u) du`, and each increment is
`∫_u^{u+h} (c - d)` up to the correction `d h`. -/
private lemma dq2_secondDiff_sub_le (ψ b c : ℝ → ℝ) (h C d : ℝ) (hh : 0 < h)
    (hψ : ∀ t ∈ Set.Icc (0:ℝ) (2 * h), HasDerivAt ψ (b t) t)
    (hb : ∀ t ∈ Set.Icc (0:ℝ) (2 * h), HasDerivAt b (c t) t)
    (hbc : ContinuousOn b (Set.Icc (0:ℝ) (2 * h)))
    (hcc : ContinuousOn c (Set.Icc (0:ℝ) (2 * h)))
    (hcd : ∀ t ∈ Set.Icc (0:ℝ) (2 * h), |c t - d| ≤ C) :
    |ψ (2 * h) - 2 * ψ h + ψ 0 - d * h ^ 2| ≤ C * h ^ 2 := by
  have h2h : (0:ℝ) ≤ 2 * h := by linarith
  -- (A) the increments of `b`
  have hincr : ∀ u ∈ Set.Icc (0:ℝ) h, |b (u + h) - b u - d * h| ≤ C * h := by
    intro u hu
    obtain ⟨hu1, hu2⟩ := hu
    have hmemu : ∀ x ∈ Set.uIcc u (u + h), x ∈ Set.Icc (0:ℝ) (2 * h) := by
      intro x hx
      rw [Set.uIcc_of_le (by linarith : u ≤ u + h)] at hx
      exact ⟨le_trans hu1 hx.1, by linarith [hx.2, hu2]⟩
    have hint : IntervalIntegrable c volume u (u + h) :=
      (hcc.mono (fun x hx => hmemu x hx)).intervalIntegrable
    have hftc : (∫ x in u..(u + h), c x) = b (u + h) - b u :=
      intervalIntegral.integral_eq_sub_of_hasDerivAt (fun x hx => hb x (hmemu x hx)) hint
    have hsub : (∫ x in u..(u + h), (c x - d)) = (b (u + h) - b u) - d * h := by
      rw [intervalIntegral.integral_sub hint intervalIntegrable_const, hftc,
        intervalIntegral.integral_const, smul_eq_mul]
      ring
    have hbd : ∀ x ∈ Set.uIoc u (u + h), ‖c x - d‖ ≤ C := by
      intro x hx
      rw [Real.norm_eq_abs]
      exact hcd x (hmemu x (Set.uIoc_subset_uIcc hx))
    have hbnd := intervalIntegral.norm_integral_le_of_norm_le_const hbd
    rw [Real.norm_eq_abs, hsub, show u + h - u = h by ring, abs_of_pos hh] at hbnd
    simpa using hbnd
  -- (B) the fundamental theorem pieces
  have hbcI : IntervalIntegrable b volume (0:ℝ) (2 * h) :=
    (hbc.mono (fun x hx => by rwa [Set.uIcc_of_le h2h] at hx)).intervalIntegrable
  have hbcIh : IntervalIntegrable b volume (0:ℝ) h :=
    (hbc.mono (fun x hx => by
      rw [Set.uIcc_of_le (le_of_lt hh)] at hx
      exact ⟨hx.1, by linarith [hx.2]⟩)).intervalIntegrable
  have hbch : IntervalIntegrable b volume h (2 * h) :=
    (hbc.mono (fun x hx => by
      rw [Set.uIcc_of_le (by linarith : h ≤ 2 * h)] at hx
      exact ⟨by linarith [hx.1], hx.2⟩)).intervalIntegrable
  have hψ1 : (∫ x in (0:ℝ)..(2 * h), b x) = ψ (2 * h) - ψ 0 :=
    intervalIntegral.integral_eq_sub_of_hasDerivAt
      (fun x hx => hψ x (by rwa [Set.uIcc_of_le h2h] at hx)) hbcI
  have hψ2 : (∫ x in (0:ℝ)..h, b x) = ψ h - ψ 0 :=
    intervalIntegral.integral_eq_sub_of_hasDerivAt
      (fun x hx => hψ x (by
        rw [Set.uIcc_of_le (le_of_lt hh)] at hx
        exact ⟨hx.1, by linarith [hx.2]⟩)) hbcIh
  have hsplit : (∫ x in (0:ℝ)..h, b x) + (∫ x in h..(2 * h), b x)
      = ∫ x in (0:ℝ)..(2 * h), b x :=
    intervalIntegral.integral_add_adjacent_intervals hbcIh hbch
  have hcomp : (∫ u in (0:ℝ)..h, b (u + h)) = ∫ x in h..(2 * h), b x := by
    have hh' := intervalIntegral.integral_comp_add_right (f := b) (a := (0:ℝ)) (b := h) (d := h)
    rw [show (0:ℝ) + h = h by ring, show h + h = 2 * h by ring] at hh'
    exact hh'
  have hck : IntervalIntegrable (fun u : ℝ => b (u + h)) volume (0:ℝ) h := by
    have hcont : ContinuousOn (fun u : ℝ => b (u + h)) (Set.uIcc (0:ℝ) h) := by
      rw [Set.uIcc_of_le (le_of_lt hh)]
      exact hbc.comp (continuous_id.add continuous_const).continuousOn
        (fun x hx => ⟨by linarith [hx.1], by linarith [hx.2]⟩)
    exact hcont.intervalIntegrable
  have hkey : (∫ u in (0:ℝ)..h, (b (u + h) - b u - d * h))
      = (ψ (2 * h) - 2 * ψ h + ψ 0) - d * h ^ 2 := by
    have e : (∫ x in h..(2 * h), b x) = ψ (2 * h) - ψ h := by
      have h1 : (∫ x in h..(2 * h), b x)
          = (∫ x in (0:ℝ)..(2 * h), b x) - (∫ x in (0:ℝ)..h, b x) := by
        calc (∫ x in h..(2 * h), b x)
            = ((∫ x in (0:ℝ)..h, b x) + (∫ x in h..(2 * h), b x))
                - (∫ x in (0:ℝ)..h, b x) := by ring
          _ = (∫ x in (0:ℝ)..(2 * h), b x) - (∫ x in (0:ℝ)..h, b x) := by rw [hsplit]
      rw [h1, hψ1, hψ2]
      ring
    rw [intervalIntegral.integral_sub (hck.sub hbcIh) intervalIntegrable_const,
      intervalIntegral.integral_sub hck hbcIh, intervalIntegral.integral_const, smul_eq_mul,
      hcomp, hψ2, e]
    ring
  have hbd : ∀ x ∈ Set.uIoc (0:ℝ) h, ‖b (x + h) - b x - d * h‖ ≤ C * h := by
    intro x hx
    rw [Real.norm_eq_abs]
    have hxI : x ∈ Set.Icc (0:ℝ) h := by
      have := Set.uIoc_subset_uIcc hx
      rwa [Set.uIcc_of_le (le_of_lt hh)] at this
    exact hincr x hxI
  calc |ψ (2 * h) - 2 * ψ h + ψ 0 - d * h ^ 2|
      = ‖∫ u in (0:ℝ)..h, (b (u + h) - b u - d * h)‖ := by rw [Real.norm_eq_abs, hkey]
    _ ≤ (C * h) * |h - 0| := intervalIntegral.norm_integral_le_of_norm_le_const hbd
    _ = C * h ^ 2 := by rw [sub_zero, abs_of_pos hh]; ring

/-- **Second-difference limit.**  If `b = ψ'` and `c = b'` on `[0,2]` with `c` continuous
there, then `(ψ (2h) - 2 ψ h + ψ 0)/h² → c 0` as `h → 0⁺`. -/
private lemma dq2_secondDiff_tendsto (ψ b c : ℝ → ℝ)
    (hψ : ∀ t ∈ Set.Icc (0:ℝ) 2, HasDerivAt ψ (b t) t)
    (hb : ∀ t ∈ Set.Icc (0:ℝ) 2, HasDerivAt b (c t) t)
    (hbc : ContinuousOn b (Set.Icc (0:ℝ) 2))
    (hcc : ContinuousOn c (Set.Icc (0:ℝ) 2)) :
    Filter.Tendsto (fun h => (ψ (2 * h) - 2 * ψ h + ψ 0) / h ^ 2)
      (nhdsWithin (0:ℝ) (Set.Ioi 0)) (nhds (c 0)) := by
  rw [Metric.tendsto_nhdsWithin_nhds]
  intro ε hε
  have h0 : (0:ℝ) ∈ Set.Icc (0:ℝ) 2 := ⟨le_rfl, by norm_num⟩
  have hcont : ContinuousWithinAt c (Set.Icc (0:ℝ) 2) 0 := hcc 0 h0
  rw [Metric.continuousWithinAt_iff] at hcont
  obtain ⟨δ1, hδ1pos, hδ1⟩ := hcont (ε / 2) (by linarith)
  refine ⟨min 1 (δ1 / 2), lt_min one_pos (by linarith), ?_⟩
  intro h hh hdist
  have hdist' : h < min 1 (δ1 / 2) := by
    rwa [Real.dist_eq, sub_zero, abs_of_pos hh] at hdist
  have hh1 : h < 1 := lt_of_lt_of_le hdist' (min_le_left _ _)
  have hhδ : h < δ1 / 2 := lt_of_lt_of_le hdist' (min_le_right _ _)
  have hhpos : 0 < h := hh
  have hsub : ∀ t ∈ Set.Icc (0:ℝ) (2 * h), t ∈ Set.Icc (0:ℝ) 2 := fun t ht =>
    ⟨ht.1, by linarith [ht.2]⟩
  have hbd : ∀ t ∈ Set.Icc (0:ℝ) (2 * h), |c t - c 0| ≤ ε / 2 := by
    intro t ht
    have ht2 : dist t 0 < δ1 := by
      rw [Real.dist_eq, sub_zero, abs_of_nonneg (hsub t ht).1]
      linarith [ht.2, hhδ]
    have hlt : |c t - c 0| < ε / 2 := by
      have := hδ1 (hsub t ht) ht2
      rwa [Real.dist_eq] at this
    exact le_of_lt hlt
  have hkey := dq2_secondDiff_sub_le ψ b c h (ε / 2) (c 0) hhpos
    (fun t ht => hψ t (hsub t ht)) (fun t ht => hb t (hsub t ht))
    (hbc.mono (fun t ht => hsub t ht)) (hcc.mono (fun t ht => hsub t ht)) hbd
  rw [show dist ((ψ (2 * h) - 2 * ψ h + ψ 0) / h ^ 2) (c 0)
        = |(ψ (2 * h) - 2 * ψ h + ψ 0) / h ^ 2 - c 0| from Real.dist_eq _ _]
  have hfac : |(ψ (2 * h) - 2 * ψ h + ψ 0) / h ^ 2 - c 0|
      = |ψ (2 * h) - 2 * ψ h + ψ 0 - c 0 * h ^ 2| / h ^ 2 := by
    have hA : (ψ (2 * h) - 2 * ψ h + ψ 0) / h ^ 2 - c 0
        = (ψ (2 * h) - 2 * ψ h + ψ 0 - c 0 * h ^ 2) / h ^ 2 := by
      field_simp
    rw [hA, abs_div, abs_of_pos (pow_pos hhpos 2)]
  rw [hfac]
  have hpos : 0 < h ^ 2 := pow_pos hhpos 2
  calc |ψ (2 * h) - 2 * ψ h + ψ 0 - c 0 * h ^ 2| / h ^ 2
      ≤ (ε / 2 * h ^ 2) / h ^ 2 := div_le_div_of_nonneg_right hkey (le_of_lt hpos)
    _ = ε / 2 := by field_simp
    _ < ε := by linarith

/-! ## §3 The leaf `E6b` -/

theorem dq2_facts (g : ℝ → ℝ) (L B : ℝ) :
    Work.FTS_StreamBdry.SB25.Dq2Facts g L B := by
  unfold Work.FTS_StreamBdry.SB25.Dq2Facts
  intro hL hd hc hB
  constructor
  · -- the bound, from `dq2_secondDiff_sub_le` with `d = 0`, `C = B`
    intro h hh z hz
    have hbound := dq2_secondDiff_sub_le
      (fun s : ℝ => g (z * Real.exp s))
      (fun s : ℝ => (z * Real.exp s) * deriv g (z * Real.exp s))
      (fun s : ℝ => (z * Real.exp s) * deriv (fun z' => z' * deriv g z') (z * Real.exp s))
      h B 0 hh
      (fun t ht => dq2_psi_hasDerivAt g L hL hd hz ht.1)
      (fun t ht => dq2_b_hasDerivAt g L hL hd hz ht.1)
      (dq2_b_cont g L B hL hd hB hz (2 * h))
      (dq2_c_cont g L hL hc hz (2 * h))
      (fun t ht => by
        rw [sub_zero]
        exact hB (z * Real.exp t) (dq2_mapsTo z L hL hz (2 * h) ht))
    have hS : |g (Real.exp (2 * h) * z) - 2 * g (Real.exp h * z) + g z| ≤ B * h ^ 2 := by
      simp only [Real.exp_zero, mul_one, zero_mul, sub_zero] at hbound
      rw [mul_comm z (Real.exp (2 * h)), mul_comm z (Real.exp h)] at hbound
      exact hbound
    have hdiv : |(g (Real.exp (2 * h) * z) - 2 * g (Real.exp h * z) + g z) / h ^ 2|
        = |g (Real.exp (2 * h) * z) - 2 * g (Real.exp h * z) + g z| / h ^ 2 := by
      rw [abs_div, abs_of_pos (pow_pos hh 2)]
    rw [hdiv]
    calc |g (Real.exp (2 * h) * z) - 2 * g (Real.exp h * z) + g z| / h ^ 2
        ≤ (B * h ^ 2) / h ^ 2 := div_le_div_of_nonneg_right hS (le_of_lt (pow_pos hh 2))
      _ = B := by field_simp
  · -- the limit, from `dq2_secondDiff_tendsto`
    intro z hz
    have hz' : L ≤ z := le_of_lt hz
    have htend := dq2_secondDiff_tendsto
      (fun s : ℝ => g (z * Real.exp s))
      (fun s : ℝ => (z * Real.exp s) * deriv g (z * Real.exp s))
      (fun s : ℝ => (z * Real.exp s) * deriv (fun z' => z' * deriv g z') (z * Real.exp s))
      (fun t ht => dq2_psi_hasDerivAt g L hL hd hz' ht.1)
      (fun t ht => dq2_b_hasDerivAt g L hL hd hz' ht.1)
      (dq2_b_cont g L B hL hd hB hz' 2)
      (dq2_c_cont g L hL hc hz' 2)
    have htend' : Filter.Tendsto
        (fun h : ℝ => (g (z * Real.exp (2 * h)) - 2 * g (z * Real.exp h) + g z) / h ^ 2)
        (nhdsWithin 0 (Set.Ioi 0)) (nhds (z * deriv (fun z' => z' * deriv g z') z)) := by
      simpa only [Real.exp_zero, mul_one] using htend
    rw [show (fun h : ℝ => (g (z * Real.exp (2 * h)) - 2 * g (z * Real.exp h) + g z) / h ^ 2)
        = (fun h : ℝ => (g (Real.exp (2 * h) * z) - 2 * g (Real.exp h * z) + g z) / h ^ 2)
        from by
          funext h
          rw [mul_comm z (Real.exp (2 * h)), mul_comm z (Real.exp h)]] at htend'
    exact htend'

end Work.FTS_StreamBdry.SB25
end
end
-- ===== merged: Submission.Work.FTS_StreamBdry.SB25.exists_phi_ge_near_ends =====
section

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

namespace Work.FTS_StreamBdry.SB25

theorem exists_phi_ge_near_ends (φ : ℝ → ℝ) (C : ℝ)
    (h0 : ∀ B : ℝ, ∃ ε : ℝ, 0 < ε ∧ ∀ θ : ℝ, 0 < θ → θ < ε → B ≤ φ θ)
    (h1 : ∀ B : ℝ, ∃ ε : ℝ, 0 < ε ∧ ∀ θ : ℝ, Real.pi / 2 - ε < θ → θ < Real.pi / 2 → B ≤ φ θ) :
    ∃ a : ℝ, 0 < a ∧ a < Real.pi / 2 ∧
      ∀ θ : ℝ, θ ∈ Set.Ioo 0 (Real.pi / 2) → (θ < a ∨ Real.pi / 2 - a < θ) → C ≤ φ θ := by
  obtain ⟨e0, he0pos, he0⟩ := h0 C
  obtain ⟨e1, he1pos, he1⟩ := h1 C
  refine ⟨min (e0 / 2) (min (e1 / 2) (Real.pi / 4)), ?_, ?_, ?_⟩
  · exact lt_min (by linarith) (lt_min (by linarith) (by positivity))
  · have hle : min (e0 / 2) (min (e1 / 2) (Real.pi / 4)) ≤ Real.pi / 4 :=
      le_trans (min_le_right _ _) (min_le_right _ _)
    have hpi : (0 : ℝ) < Real.pi := Real.pi_pos
    linarith
  · intro θ hθ hcase
    rcases hcase with hcase | hcase
    · have hlt : θ < e0 := by
        have h2 : θ < e0 / 2 := lt_of_lt_of_le hcase (min_le_left _ _)
        linarith
      exact he0 θ hθ.1 hlt
    · have hlt : Real.pi / 2 - e1 < θ := by
        have ha : min (e0 / 2) (min (e1 / 2) (Real.pi / 4)) ≤ e1 / 2 :=
          le_trans (min_le_right _ _) (min_le_left _ _)
        linarith
      exact he1 θ hlt hθ.2

end Work.FTS_StreamBdry.SB25
end
-- ===== merged: Submission.Work.FTS_StreamBdry.SB25.gaugeMode_facts =====
section

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
end
end
-- ===== merged: Submission.Work.FTS_StreamBdry.SB25.glue_line_C1 =====
section

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

/-!
# `Work.FTS_StreamBdry.SB25.glue_line_C1` (leaf B7a)

`GlueLineC1 h c r` states that a function `h : ℝ → ℝ → ℝ` which is `C¹` on the two open
half-strips `θ < c` and `θ > c`, continuous on the full strip `(0,∞) × (c-r,c+r)`, and whose
two partial derivatives have limits at every point `(z₀, c)` of the seam (approached along
the punctured strip), is `C¹` on the full strip and has continuous partial derivatives there.

The proof is the standard gluing-across-a-hypersurface argument.

* At a point of the seam one applies Mathlib's
  `hasFDerivWithinAt_closure_of_tendsto_fderiv` on the two convex open boxes lying below and
  above the seam; the two one-sided conclusions are merged with `HasFDerivWithinAt.union`.
  The union contains an open neighbourhood of the seam point, so the conclusion upgrades to
  an honest `HasFDerivAt`.
* Continuity of the derivative field is then: on the punctured strip it is Mathlib's
  continuity of `fderiv`, and at a seam point a closed-neighbourhood argument shows that the
  derivative-field's limit along the punctured strip at the seam point matches the
  (already established) value there, giving continuity along the whole strip.
-/

noncomputable section

open scoped Real Topology NNReal
open Set Filter

namespace Work.FTS_StreamBdry.SB25

set_option autoImplicit false

/-! ## §1 The two strips -/

/-- The punctured strip `(0,∞) × ((c-r,c) ∪ (c,c+r))` on which `h` is assumed `C¹`. -/
def glueS (c r : ℝ) : Set (ℝ × ℝ) :=
  Ioi (0 : ℝ) ×ˢ (Ioo (c - r) c ∪ Ioo c (c + r))

/-- The full strip `(0,∞) × (c-r,c+r)`. -/
def glueU (c r : ℝ) : Set (ℝ × ℝ) :=
  Ioi (0 : ℝ) ×ˢ Ioo (c - r) (c + r)

theorem mem_glueU {c r z θ : ℝ} :
    (z, θ) ∈ glueU c r ↔ 0 < z ∧ c - r < θ ∧ θ < c + r := by
  simp [glueU, Set.mem_prod]

theorem mem_glueS {c r z θ : ℝ} :
    (z, θ) ∈ glueS c r ↔ 0 < z ∧ (c - r < θ ∧ θ < c ∨ c < θ ∧ θ < c + r) := by
  unfold glueS
  simp only [Set.mem_prod, Set.mem_Ioi, Set.mem_union, Set.mem_Ioo]

theorem glueS_subset_glueU {c r : ℝ} (hr : 0 < r) : glueS c r ⊆ glueU c r := by
  rintro ⟨z, θ⟩ hp
  rw [mem_glueS] at hp
  rw [mem_glueU]
  refine ⟨hp.1, ?_, ?_⟩
  · rcases hp.2 with ⟨h, _⟩ | ⟨h, _⟩
    · exact h
    · linarith
  · rcases hp.2 with ⟨_, h⟩ | ⟨_, h⟩
    · linarith
    · exact h

theorem isOpen_glueS (c r : ℝ) : IsOpen (glueS c r) :=
  isOpen_Ioi.prod (isOpen_Ioo.union isOpen_Ioo)

theorem isOpen_glueU (c r : ℝ) : IsOpen (glueU c r) :=
  isOpen_Ioi.prod isOpen_Ioo

theorem mem_glueS_of_mem_glueU_of_ne {c r : ℝ} {p : ℝ × ℝ} (hp : p ∈ glueU c r)
    (h : p.2 ≠ c) : p ∈ glueS c r := by
  rw [mem_glueU] at hp
  rw [mem_glueS]
  refine ⟨hp.1, ?_⟩
  rcases lt_trichotomy p.2 c with hlt | heq | hlt
  · exact Or.inl ⟨hp.2.1, hlt⟩
  · exact absurd heq h
  · exact Or.inr ⟨hlt, hp.2.2⟩

/-- The seam point `(z,c)`, `z > 0`, lies in the closure of the punctured strip. -/
theorem seam_mem_closure_glueS {c r : ℝ} (hr : 0 < r) {z : ℝ} (hz : 0 < z) :
    (z, c) ∈ closure (glueS c r) := by
  have hsub : Ioi (0 : ℝ) ×ˢ Ioo c (c + r) ⊆ glueS c r := by
    rintro ⟨z', θ'⟩ hp
    rw [Set.mem_prod] at hp
    rw [mem_glueS]
    exact ⟨hp.1, Or.inr hp.2⟩
  have hmem : (z, c) ∈ closure (Ioi (0 : ℝ) ×ˢ Ioo c (c + r)) := by
    rw [closure_prod_eq, closure_Ioi, closure_Ioo (by linarith : c ≠ c + r)]
    exact ⟨le_of_lt hz, ⟨le_rfl, by linarith⟩⟩
  exact closure_mono hsub hmem

/-! ## §2 The Fréchet derivative versus the two partial derivatives -/

theorem clm_prod_eq_smul_fst_add_smul_snd (L : ℝ × ℝ →L[ℝ] ℝ) :
    L = (L (1, 0)) • ContinuousLinearMap.fst ℝ ℝ ℝ
      + (L (0, 1)) • ContinuousLinearMap.snd ℝ ℝ ℝ := by
  apply ContinuousLinearMap.ext
  intro v
  have hv : v = v.1 • (1, 0) + v.2 • ((0 : ℝ), 1) := by ext <;> simp
  conv_lhs => rw [hv]
  simp only [map_add, map_smul, add_apply, smul_apply, smul_eq_mul]
  simp
  ring

theorem fderiv_eq_combo {F : ℝ → ℝ → ℝ} {p : ℝ × ℝ}
    (hp : DifferentiableAt ℝ (Function.uncurry F) p) :
    fderiv ℝ (Function.uncurry F) p
      = (Work.Spaces.pz F p.1 p.2) • ContinuousLinearMap.fst ℝ ℝ ℝ
        + (Work.Spaces.pth F p.1 p.2) • ContinuousLinearMap.snd ℝ ℝ ℝ := by
  rw [clm_prod_eq_smul_fst_add_smul_snd (fderiv ℝ (Function.uncurry F) p),
    ← Work.Spaces.pz_eq_fderiv hp, ← Work.Spaces.pth_eq_fderiv hp]

theorem tendsto_fderiv_of_tendsto_partials {F : ℝ → ℝ → ℝ} {s : Set (ℝ × ℝ)} {x : ℝ × ℝ}
    {a b : ℝ} (hdiff : ∀ p ∈ s, DifferentiableAt ℝ (Function.uncurry F) p)
    (h1 : Tendsto (fun p : ℝ × ℝ => Work.Spaces.pz F p.1 p.2) (𝓝[s] x) (𝓝 a))
    (h2 : Tendsto (fun p : ℝ × ℝ => Work.Spaces.pth F p.1 p.2) (𝓝[s] x) (𝓝 b)) :
    Tendsto (fun p : ℝ × ℝ => fderiv ℝ (Function.uncurry F) p) (𝓝[s] x)
      (𝓝 (a • ContinuousLinearMap.fst ℝ ℝ ℝ + b • ContinuousLinearMap.snd ℝ ℝ ℝ)) := by
  refine Tendsto.congr' ?_ ((h1.smul tendsto_const_nhds).add (h2.smul tendsto_const_nhds))
  filter_upwards [self_mem_nhdsWithin] with p hp
  exact (fderiv_eq_combo (hdiff p hp)).symm

/-! ## §3 Gluing along a convex piece of the strip -/

theorem hasFDerivWithinAt_closure_of_glue {F : ℝ → ℝ → ℝ} {c r : ℝ} {T : Set (ℝ × ℝ)}
    {x : ℝ × ℝ} {L' : ℝ × ℝ →L[ℝ] ℝ} (hTopen : IsOpen T) (hTconv : Convex ℝ T)
    (hTsub : T ⊆ glueS c r) (hTsubU : T ⊆ glueU c r) (hTclU : closure T ⊆ glueU c r)
    (hcont : ContinuousOn (Function.uncurry F) (glueU c r))
    (hdiff : DifferentiableOn ℝ (Function.uncurry F) (glueS c r))
    (htend : Tendsto (fun p : ℝ × ℝ => fderiv ℝ (Function.uncurry F) p) (𝓝[T] x) (𝓝 L')) :
    HasFDerivWithinAt (Function.uncurry F) L' (closure T) x :=
  hasFDerivWithinAt_closure_of_tendsto_fderiv (hdiff.mono hTsub) hTconv hTopen
    (fun y hy => (hcont.continuousWithinAt (hTclU hy)).mono hTsubU) htend

/-! ## §4 The leaf -/

theorem glue_line_C1 (h : ℝ → ℝ → ℝ) (c r : ℝ) :
    Work.FTS_StreamBdry.SB25.GlueLineC1 h c r := by
  classical
  intro hr hScd hUcont hzlim htlim
  have hSopen : IsOpen (glueS c r) := isOpen_glueS c r
  have hUopen : IsOpen (glueU c r) := isOpen_glueU c r
  have hSU : glueS c r ⊆ glueU c r := glueS_subset_glueU hr
  have hDiffOnS : DifferentiableOn ℝ (Function.uncurry h) (glueS c r) :=
    hScd.differentiableOn (by norm_num)
  have hdiffS : ∀ p ∈ glueS c r, DifferentiableAt ℝ (Function.uncurry h) p := fun p hp =>
    hDiffOnS.differentiableAt (hSopen.mem_nhds hp)
  have hfdcontS : ContinuousOn (fun p : ℝ × ℝ => fderiv ℝ (Function.uncurry h) p) (glueS c r) :=
    hScd.continuousOn_fderiv_of_isOpen hSopen le_rfl
  -- ### the two boundary limits
  let Lz : ℝ → ℝ := fun z => if hz : 0 < z then Classical.choose (hzlim z hz) else 0
  let Lt : ℝ → ℝ := fun z => if hz : 0 < z then Classical.choose (htlim z hz) else 0
  have hLz : ∀ z (hz : 0 < z), Tendsto (fun p : ℝ × ℝ => Work.Spaces.pz h p.1 p.2)
      (𝓝[glueS c r] (z, c)) (𝓝 (Lz z)) := by
    intro z hz
    have hval : Lz z = Classical.choose (hzlim z hz) := by
      dsimp only [Lz]
      rw [dite_eq_left hz]
    rw [hval]
    exact Classical.choose_spec (hzlim z hz)
  have hLt : ∀ z (hz : 0 < z), Tendsto (fun p : ℝ × ℝ => Work.Spaces.pth h p.1 p.2)
      (𝓝[glueS c r] (z, c)) (𝓝 (Lt z)) := by
    intro z hz
    have hval : Lt z = Classical.choose (htlim z hz) := by
      dsimp only [Lt]
      rw [dite_eq_left hz]
    rw [hval]
    exact Classical.choose_spec (htlim z hz)
  let L : ℝ → ℝ × ℝ →L[ℝ] ℝ := fun z =>
    Lz z • ContinuousLinearMap.fst ℝ ℝ ℝ + Lt z • ContinuousLinearMap.snd ℝ ℝ ℝ
  have hlimfd : ∀ z (hz : 0 < z),
      Tendsto (fun p : ℝ × ℝ => fderiv ℝ (Function.uncurry h) p)
        (𝓝[glueS c r] (z, c)) (𝓝 (L z)) := by
    intro z hz
    exact tendsto_fderiv_of_tendsto_partials hdiffS (hLz z hz) (hLt z hz)
  -- ### differentiability at a seam point
  have hseam : ∀ z (hz : 0 < z), HasFDerivAt (Function.uncurry h) (L z) (z, c) := by
    intro z hz
    have hz3 : z / 2 < 2 * z := by linarith
    have hrl : c - r < c - r / 2 := by linarith
    have hr2 : c - r / 2 < c + r / 2 := by linarith
    have hrr : c + r / 2 < c + r := by linarith
    have hTcleq : ∀ A B : ℝ, A < B →
        closure (Ioo (z / 2) (2 * z) ×ˢ Ioo A B)
          = Icc (z / 2) (2 * z) ×ˢ Icc A B := by
      intro A B hAB
      rw [closure_prod_eq, closure_Ioo (ne_of_lt hz3), closure_Ioo (ne_of_lt hAB)]
    -- one-sided gluing on an arbitrary convex box
    have hside : ∀ A B : ℝ, c - r < A → A < B → B < c + r → A ≤ c → c ≤ B →
        Ioo A B ⊆ Ioo (c - r) c ∪ Ioo c (c + r) →
        HasFDerivWithinAt (Function.uncurry h) (L z)
          (closure (Ioo (z / 2) (2 * z) ×ˢ Ioo A B)) (z, c) := by
      intro A B hA hAB hB hAc hcB hsub
      have hTsub : Ioo (z / 2) (2 * z) ×ˢ Ioo A B ⊆ glueS c r := by
        rintro ⟨z', θ'⟩ hp
        rw [Set.mem_prod] at hp
        rw [mem_glueS]
        exact ⟨by linarith [hp.1.1], hsub hp.2⟩
      have hTclU : closure (Ioo (z / 2) (2 * z) ×ˢ Ioo A B) ⊆ glueU c r := by
        rw [hTcleq A B hAB]
        rintro ⟨z', θ'⟩ hp
        rw [Set.mem_prod] at hp
        rw [mem_glueU]
        exact ⟨by linarith [hp.1.1], by linarith [hp.2.1, hA], by linarith [hp.2.2, hB]⟩
      have hTsubU : Ioo (z / 2) (2 * z) ×ˢ Ioo A B ⊆ glueU c r := Subset.trans hTsub hSU
      exact hasFDerivWithinAt_closure_of_glue (isOpen_Ioo.prod isOpen_Ioo)
        ((convex_Ioo _ _).prod (convex_Ioo _ _)) hTsub hTsubU hTclU hUcont hDiffOnS
        ((hlimfd z hz).mono_left (nhdsWithin_mono _ hTsub))
    have hm := hside (c - r / 2) c hrl (by linarith) (by linarith) (by linarith) le_rfl
      (fun θ hθ => Or.inl ⟨by linarith [hθ.1], hθ.2⟩)
    have hp := hside c (c + r / 2) (by linarith) (by linarith) hrr le_rfl (by linarith)
      (fun θ hθ => Or.inr ⟨hθ.1, by linarith [hθ.2]⟩)
    have hunion := hm.union hp
    have hVsub : Ioo (z / 2) (2 * z) ×ˢ Ioo (c - r / 2) (c + r / 2)
        ⊆ closure (Ioo (z / 2) (2 * z) ×ˢ Ioo (c - r / 2) c)
          ∪ closure (Ioo (z / 2) (2 * z) ×ˢ Ioo c (c + r / 2)) := by
      rintro ⟨z', θ'⟩ hpV
      rw [Set.mem_prod] at hpV
      rcases le_or_gt θ' c with hle | hlt
      · exact Or.inl (by
          rw [hTcleq (c - r / 2) c (by linarith), Set.mem_prod]
          exact ⟨⟨le_of_lt hpV.1.1, le_of_lt hpV.1.2⟩, ⟨le_of_lt hpV.2.1, hle⟩⟩)
      · exact Or.inr (by
          rw [hTcleq c (c + r / 2) (by linarith), Set.mem_prod]
          exact ⟨⟨le_of_lt hpV.1.1, le_of_lt hpV.1.2⟩, ⟨le_of_lt hlt, le_of_lt hpV.2.2⟩⟩)
    have hVnhds : Ioo (z / 2) (2 * z) ×ˢ Ioo (c - r / 2) (c + r / 2) ∈ 𝓝 (z, c) :=
      (isOpen_Ioo.prod isOpen_Ioo).mem_nhds
        ⟨⟨by linarith, by linarith⟩, ⟨by linarith, by linarith⟩⟩
    exact (hunion.mono hVsub).hasFDerivAt hVnhds
  -- ### differentiability on the whole strip
  have hDiffOnU : DifferentiableOn ℝ (Function.uncurry h) (glueU c r) := by
    intro p hp
    by_cases hpc : p.2 = c
    · have hp1 : 0 < p.1 := (mem_glueU.mp hp).1
      have hpeq : p = (p.1, c) := by ext <;> simp [hpc]
      rw [hpeq]
      exact (hseam p.1 hp1).differentiableAt.differentiableWithinAt
    · exact (hdiffS p (mem_glueS_of_mem_glueU_of_ne hp hpc)).differentiableWithinAt
  -- ### the limit field along the seam is continuous
  have hseamcont : ContinuousOn L (Ioi (0 : ℝ)) := by
    intro z0 hz0
    refine (Metric.tendsto_nhds).2 ?_
    intro ε hε
    change {z : ℝ | dist (L z) (L z0) < ε} ∈ 𝓝[Ioi (0 : ℝ)] z0
    rw [Metric.mem_nhdsWithin_iff]
    set W : Set (ℝ × ℝ →L[ℝ] ℝ) := {M | dist M (L z0) ≤ ε / 2} with hWdef
    have hWclosed : IsClosed W := by
      rw [hWdef]
      exact isClosed_le (continuous_id.dist continuous_const) continuous_const
    have hWnhds : W ∈ 𝓝 (L z0) := by
      refine Filter.mem_of_superset
        (Metric.ball_mem_nhds (L z0) (by linarith : (0 : ℝ) < ε / 2)) ?_
      intro M hM
      rw [hWdef, Set.mem_setOf_eq]
      exact le_of_lt (Metric.mem_ball.mp hM)
    obtain ⟨δ', hδ'pos, hδ'sub⟩ := Metric.mem_nhdsWithin_iff.mp ((hlimfd z0 hz0) hWnhds)
    refine ⟨δ' / 2, by linarith, ?_⟩
    rintro z ⟨hzball, hzpos⟩
    change dist (L z) (L z0) < ε
    have hzdist : dist z z0 < δ' / 2 := Metric.mem_ball.mp hzball
    have hne : NeBot (𝓝[glueS c r] (z, c)) :=
      mem_closure_iff_nhdsWithin_neBot.mp (seam_mem_closure_glueS hr hzpos)
    haveI := hne
    have hLzW : L z ∈ W := by
      refine hWclosed.mem_of_tendsto (hlimfd z hzpos) ?_
      change {x : ℝ × ℝ | fderiv ℝ (Function.uncurry h) x ∈ W} ∈ 𝓝[glueS c r] (z, c)
      rw [Metric.mem_nhdsWithin_iff]
      refine ⟨δ' / 2, by linarith, ?_⟩
      rintro y ⟨hyball, hyS⟩
      have hy1 : dist y (z0, c) < δ' := by
        have hy2 : dist y (z, c) < δ' / 2 := Metric.mem_ball.mp hyball
        calc dist y (z0, c) ≤ dist y (z, c) + dist (z, c) (z0, c) := dist_triangle _ _ _
          _ = dist y (z, c) + dist z z0 := by simp [Prod.dist_eq, dist_comm]
          _ < δ' / 2 + δ' / 2 := by linarith
          _ = δ' := by ring
      exact hδ'sub ⟨Metric.mem_ball.mpr hy1, hyS⟩
    rw [hWdef, Set.mem_setOf_eq] at hLzW
    linarith
  -- ### continuity of the derivative field on the whole strip
  have hfdcontU : ContinuousOn (fun p : ℝ × ℝ => fderiv ℝ (Function.uncurry h) p) (glueU c r) := by
    intro p hp
    by_cases hpc : p.2 = c
    · have hp1 : 0 < p.1 := (mem_glueU.mp hp).1
      have hpeq : p = (p.1, c) := by ext <;> simp [hpc]
      have hval : fderiv ℝ (Function.uncurry h) (p.1, c) = L p.1 := (hseam p.1 hp1).fderiv
      rw [hpeq]
      change Tendsto (fun p : ℝ × ℝ => fderiv ℝ (Function.uncurry h) p) (𝓝[glueU c r] (p.1, c))
        (𝓝 (fderiv ℝ (Function.uncurry h) (p.1, c)))
      rw [hval]
      refine (Metric.tendsto_nhds).2 ?_
      intro ε hε
      change {y : ℝ × ℝ | dist (fderiv ℝ (Function.uncurry h) y) (L p.1) < ε} ∈
        𝓝[glueU c r] (p.1, c)
      rw [Metric.mem_nhdsWithin_iff]
      have h1 : ∀ᶠ y in 𝓝[glueS c r] (p.1, c),
          dist (fderiv ℝ (Function.uncurry h) y) (L p.1) < ε / 2 :=
        (hlimfd p.1 hp1) (Metric.ball_mem_nhds (L p.1) (by linarith : (0 : ℝ) < ε / 2))
      have h2 : ∀ᶠ z in 𝓝[Ioi (0 : ℝ)] p.1, dist (L z) (L p.1) < ε / 2 :=
        (hseamcont.continuousWithinAt hp1) (Metric.ball_mem_nhds (L p.1) (by linarith : (0 : ℝ) < ε / 2))
      obtain ⟨δ₁, hδ₁pos, hδ₁sub⟩ := Metric.mem_nhdsWithin_iff.mp h1
      obtain ⟨δ₂, hδ₂pos, hδ₂sub⟩ := Metric.mem_nhdsWithin_iff.mp h2
      refine ⟨min δ₁ δ₂, lt_min hδ₁pos hδ₂pos, ?_⟩
      rintro y ⟨hyball, hyU⟩
      change dist (fderiv ℝ (Function.uncurry h) y) (L p.1) < ε
      have hydist : dist y (p.1, c) < min δ₁ δ₂ := Metric.mem_ball.mp hyball
      have hyU' := mem_glueU.mp hyU
      by_cases hyc : y.2 = c
      · have hyeq : y = (y.1, c) := by ext <;> simp [hyc]
        have hy1 : 0 < y.1 := hyU'.1
        have hyd : dist y.1 p.1 < δ₂ := by
          have h : dist y (p.1, c) < δ₂ := lt_of_lt_of_le hydist (min_le_right _ _)
          rw [hyeq] at h
          simpa [Prod.dist_eq, dist_comm] using h
        have hval2 : fderiv ℝ (Function.uncurry h) y = L y.1 := by
          rw [hyeq]
          exact (hseam y.1 hy1).fderiv
        rw [hval2]
        exact lt_of_lt_of_le (hδ₂sub ⟨Metric.mem_ball.mpr hyd, hy1⟩) (le_of_lt (by linarith))
      · have hyS : y ∈ glueS c r := mem_glueS_of_mem_glueU_of_ne hyU hyc
        have hb : dist (fderiv ℝ (Function.uncurry h) y) (L p.1) < ε / 2 :=
          hδ₁sub ⟨Metric.mem_ball.mpr (lt_of_lt_of_le hydist (min_le_left _ _)), hyS⟩
        linarith
    · have hpS : p ∈ glueS c r := mem_glueS_of_mem_glueU_of_ne hp hpc
      exact ((hfdcontS.continuousWithinAt hpS).continuousAt
        (hSopen.mem_nhds hpS)).continuousWithinAt
  -- ### assemble
  have hC1 : ContDiffOn ℝ 1 (Function.uncurry h) (glueU c r) := by
    have hfd0 : ContDiffOn ℝ 0 (fun p : ℝ × ℝ => fderiv ℝ (Function.uncurry h) p) (glueU c r) :=
      contDiffOn_zero.2 hfdcontU
    have hiff := contDiffOn_succ_iff_fderiv_of_isOpen (𝕜 := ℝ)
      (f := Function.uncurry h) (s := glueU c r) (n := 0) hUopen
    rw [show (0 : WithTop ℕ∞) + 1 = 1 from by simp] at hiff
    exact hiff.2 ⟨hDiffOnU, fun h0 => absurd h0 (by simp), hfd0⟩
  refine ⟨hC1, ?_, ?_⟩
  · have hfdc : ContinuousOn (fun p : ℝ × ℝ => fderiv ℝ (Function.uncurry h) p) (glueU c r) :=
      hC1.continuousOn_fderiv_of_isOpen hUopen le_rfl
    have hcomp : ContinuousOn
        (fun p : ℝ × ℝ => (fderiv ℝ (Function.uncurry h) p) ((1 : ℝ), (0 : ℝ))) (glueU c r) :=
      hfdc.clm_apply continuousOn_const
    refine hcomp.congr ?_
    intro p hp
    show Work.Spaces.pz h p.1 p.2 = fderiv ℝ (Function.uncurry h) p (1, 0)
    exact Work.Spaces.pz_eq_fderiv ((hDiffOnU p hp).differentiableAt (hUopen.mem_nhds hp))
  · have hfdc : ContinuousOn (fun p : ℝ × ℝ => fderiv ℝ (Function.uncurry h) p) (glueU c r) :=
      hC1.continuousOn_fderiv_of_isOpen hUopen le_rfl
    have hcomp : ContinuousOn
        (fun p : ℝ × ℝ => (fderiv ℝ (Function.uncurry h) p) ((0 : ℝ), (1 : ℝ))) (glueU c r) :=
      hfdc.clm_apply continuousOn_const
    refine hcomp.congr ?_
    intro p hp
    show Work.Spaces.pth h p.1 p.2 = fderiv ℝ (Function.uncurry h) p (0, 1)
    exact Work.Spaces.pth_eq_fderiv ((hDiffOnU p hp).differentiableAt (hUopen.mem_nhds hp))

end Work.FTS_StreamBdry.SB25
end
end
-- ===== merged: Submission.Work.FTS_StreamBdry.SB25.law_Dform =====
section

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

/-!
# `Work.FTS_StreamBdry.SB25.law_Dform` — the elliptic law in `D`-form

C3 of the SB2/SB5 leaf interface (`Submission/Work/FTS_StreamBdry/SB25/Defs.lean`):
on the open quadrant,
`∂_θ V(P) = -(α² D_z²P + 5α D_zP + 6P) - F` whenever `bslOp α P = F` and `P` is `C²`.

The content is the algebraic rearrangement of

* `bslOp α P = -(α²z²)∂_zzP - (α(5+α)z)∂_zP + Lzero P`,
* `Lzero P = -∂_θθP + ∂_θ(tan θ·P) - 6P = -∂_θ(V(P)) - 6P` (the product rule in `θ`),
* `D_z²P = D_zP + z²∂_zzP` (the product rule in `z`).

Nothing here is specific to `bslOp`; the only analytic input is that the `θ`- and `z`-slices of
`P` and of its first partials are differentiable at an interior point, which is what
`ContDiffOn ℝ 2` on the open quadrant supplies (`Work.Spaces.uncurry_partial_c1`).
-/

noncomputable section
open scoped Real Topology
open Set Filter

namespace Work.FTS_StreamBdry.SB25

/-- **C3, the elliptic law in `D`-form.**  For `P` of class `C²` on the open quadrant with
`bslOp α P = F` there, one has `∂_θV(P) = -(α²D_z²P + 5αD_zP + 6P) - F` pointwise on the
quadrant. -/
theorem law_Dform (α : ℝ) (F P : ℝ → ℝ → ℝ) : Work.FTS_StreamBdry.SB25.LawDform α F P := by
  intro hP hlaw z θ hzθ
  have hQd : IsOpen Work.Construction.Qd := isOpen_Ioi.prod isOpen_Ioo
  have hmem : Work.Construction.Qd ∈ 𝓝 (z, θ) := hQd.mem_nhds hzθ
  obtain ⟨_, hθ1, hθ2⟩ := Work.FTS_StreamBdry.mem_Qd.mp hzθ
  have hcos : Real.cos θ ≠ 0 :=
    ne_of_gt (Real.cos_pos_of_mem_Ioo ⟨by linarith [Real.pi_pos, hθ1], hθ2⟩)
  -- differentiability of the slices of `P`, `∂_zP`, `∂_θP` (from `C²` on the open quadrant)
  have hAt2 : ContDiffAt ℝ 2 (Function.uncurry P) (z, θ) := hP.contDiffAt hmem
  have hdP : DifferentiableAt ℝ (Function.uncurry P) (z, θ) :=
    hAt2.differentiableAt (by norm_num)
  have hd1θ : DifferentiableAt ℝ (fun θ' => P z θ') θ :=
    Work.Spaces.differentiableAt_curry_right hdP
  obtain ⟨hpz1, hpth1⟩ := Work.Spaces.uncurry_partial_c1 hQd hP
  have hd2z : DifferentiableAt ℝ (fun z' => Work.Spaces.pz P z' θ) z :=
    Work.Spaces.differentiableAt_curry_left
      ((hpz1.contDiffAt hmem).differentiableAt (by norm_num))
  have hd2θ : DifferentiableAt ℝ (fun θ' => Work.Spaces.pth P z θ') θ :=
    Work.Spaces.differentiableAt_curry_right
      ((hpth1.contDiffAt hmem).differentiableAt (by norm_num))
  have hdtan : DifferentiableAt ℝ (fun θ' => Real.tan θ' * P z θ') θ :=
    (Real.differentiableAt_tan.mpr hcos).mul hd1θ
  -- (A) `∂_θ(V(P)) = ∂_θ²P - ∂_θ(tan θ·P)`
  have hpthVop : Work.Spaces.pth (Work.Construction.Vop P) z θ
      = Work.Spaces.pthIter 2 P z θ
        - Work.Spaces.pth (fun z θ => Real.tan θ * P z θ) z θ := by
    have hB : Work.Spaces.pth (Work.Construction.Vop P) z θ
        = deriv ((fun θ' => Work.Spaces.pth P z θ')
            - fun θ' => Real.tan θ' * P z θ') θ := rfl
    have hb : deriv (fun θ' => Work.Spaces.pth P z θ') θ = Work.Spaces.pthIter 2 P z θ := rfl
    rw [hB, deriv_sub hd2θ hdtan, hb]
    rfl
  -- (B) `D_z²P = D_zP + z²∂_zzP`
  have hkey : deriv (fun z' => z' * Work.Spaces.pz P z' θ) z
      = Work.Spaces.pz P z θ + z * Work.Spaces.pzIter 2 P z θ := by
    have hd1 : deriv (fun t => t * Work.Spaces.pz P t θ) z
        = deriv (fun t : ℝ => t) z * Work.Spaces.pz P z θ
          + z * deriv (fun t => Work.Spaces.pz P t θ) z := by
      exact deriv_mul differentiableAt_id hd2z
    have hb : deriv (fun t => Work.Spaces.pz P t θ) z = Work.Spaces.pzIter 2 P z θ := rfl
    rw [hd1, deriv_id'', hb]
    ring
  have hDz2 : Work.Spaces.DzIter 2 P z θ
      = Work.Spaces.Dz P z θ + z ^ 2 * Work.Spaces.pzIter 2 P z θ := by
    have h1 : Work.Spaces.DzIter 2 P z θ
        = z * deriv (fun z' => z' * Work.Spaces.pz P z' θ) z := rfl
    rw [h1, hkey]
    simp only [Work.Spaces.Dz]
    ring
  -- (C) `bslOp` expanded and `Lzero` with the product rule already substituted
  have hLz : Work.Elliptic.Lzero P z θ
      = - Work.Spaces.pthIter 2 P z θ
        + Work.Spaces.pth (fun z θ => Real.tan θ * P z θ) z θ - 6 * P z θ := rfl
  have hbsl : Work.Elliptic.bslOp α P z θ
      = -(α ^ 2 * z ^ 2) * Work.Spaces.pzIter 2 P z θ
        - α * (5 + α) * z * Work.Spaces.pz P z θ
        - Work.Spaces.pthIter 2 P z θ
        + Work.Spaces.pth (fun z θ => Real.tan θ * P z θ) z θ - 6 * P z θ := by
    rw [Work.Elliptic.bslOp_apply, hLz]
    ring
  -- (D) assembly
  have hh : Work.Elliptic.bslOp α P z θ = F z θ := hlaw z θ hzθ
  rw [hpthVop, ← hh, hbsl, hDz2]
  simp only [Work.Spaces.Dz]
  ring

end Work.FTS_StreamBdry.SB25
end
end
-- ===== merged: Submission.Work.FTS_StreamBdry.SB25.lip_edge_trace =====
section

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

/-!
# `Work.FTS_StreamBdry.SB25.lip_edge_trace`

Leaf **B2** of the SB2/SB5 plan (`sources/ftsV2/fts_sb25_leafplans.md`): a function on the strip
`z > 0`, `a < θ < b` whose slices are `θ`-Lipschitz with constant `K` has continuous edge traces
`fa` (at `θ = a`) and `fb` (at `θ = b`), approached at the linear rate `K·(θ - a)` resp.
`K·(b - θ)`.

The proof has three ingredients.

* **Lipschitz slices** (here, `slice_lipschitzOnWith`). For `0 < z` the mean value inequality
  (`Convex.norm_image_sub_le_of_norm_deriv_le`) turns the pointwise bound `|∂_θ f| ≤ K` into
  `LipschitzOnWith K (f z ·) (Ioo a b)`.
* **Extension** (here, `exists_lip_ext`). `LipschitzOnWith.extend_real` extends each slice to a
  globally `K`-Lipschitz function `G z : ℝ → ℝ`; the traces are `fa z = G z a`, `fb z = G z b`, and
  the rate bounds are the Lipschitz estimate read at the endpoints.
* **Continuity in `z`** (`cont_rate_left`, `cont_rate_right`, in their own modules).
  `G z a = lim_{θ→a⁺} f z θ` is a *uniform* (in `z`) limit of the continuous slices
  `z ↦ f z θ`, hence continuous on `Ioi 0`; likewise `G z b = lim_{θ→b⁻} f z θ` at the other end.

For `K < 0` the rate hypothesis is unsatisfiable (`|·| ≥ 0`), so the statement is vacuous; that
branch is discharged by `linarith` at a single interior point.
-/

noncomputable section
open Set

namespace Work.FTS_StreamBdry.SB25

set_option autoImplicit false

/-! ## §1 Lipschitz slices and their extension -/

/-- A slice of `f` is `K`-Lipschitz on `(a,b)` as soon as `|∂_θ f| ≤ K` there (mean value
inequality). -/
lemma slice_lipschitzOnWith {f : ℝ → ℝ → ℝ} {a b K z : ℝ} (hK : 0 ≤ K)
    (hd : ∀ θ ∈ Ioo a b, DifferentiableAt ℝ (fun θ' => f z θ') θ)
    (hB : ∀ θ ∈ Ioo a b, |Work.Spaces.pth f z θ| ≤ K) :
    LipschitzOnWith (Real.toNNReal K) (fun θ => f z θ) (Ioo a b) := by
  refine LipschitzOnWith.of_dist_le_mul fun x hx y hy => ?_
  have key := (convex_Ioo a b).norm_image_sub_le_of_norm_deriv_le (f := fun θ => f z θ)
    (x := y) (y := x) (C := K)
    (fun t ht => hd t ht) (fun t ht => by rw [Real.norm_eq_abs]; exact hB t ht) hy hx
  simpa [Real.dist_eq, Real.norm_eq_abs, Real.coe_toNNReal K hK] using key

/-- Each slice `f z ·` (`0 < z`) extends to a globally `K`-Lipschitz function `G z`. -/
lemma exists_lip_ext {f : ℝ → ℝ → ℝ} {a b K : ℝ} (hK : 0 ≤ K)
    (hd : ∀ z θ, 0 < z → θ ∈ Ioo a b → DifferentiableAt ℝ (fun θ' => f z θ') θ)
    (hB : ∀ z θ, 0 < z → θ ∈ Ioo a b → |Work.Spaces.pth f z θ| ≤ K) :
    ∃ G : ℝ → ℝ → ℝ, ∀ z, 0 < z →
      LipschitzWith (Real.toNNReal K) (G z) ∧ EqOn (fun θ => f z θ) (G z) (Ioo a b) := by
  refine ⟨fun z => if hz : 0 < z then
      Classical.choose ((slice_lipschitzOnWith hK (fun θ hθ => hd z θ hz hθ)
        (fun θ hθ => hB z θ hz hθ)).extend_real) else fun _ => 0, ?_⟩
  intro z hz
  simp only [dite_eq_left hz]
  exact Classical.choose_spec ((slice_lipschitzOnWith hK (fun θ hθ => hd z θ hz hθ)
        (fun θ hθ => hB z θ hz hθ)).extend_real)

/-! ## §2 The leaf -/

theorem lip_edge_trace (f : ℝ → ℝ → ℝ) (a b K : ℝ) :
    Work.FTS_StreamBdry.SB25.LipEdgeTrace f a b K := by
  intro hab hcont hd hB
  by_cases hK0 : 0 ≤ K
  · obtain ⟨G, hG⟩ := exists_lip_ext (f := f) (a := a) (b := b) (K := K) hK0 hd hB
    have hfa : ∀ z θ, 0 < z → θ ∈ Ioo a b → |f z θ - G z a| ≤ K * (θ - a) := by
      intro z θ hz hθ
      obtain ⟨hlip, heq⟩ := hG z hz
      have heqθ : f z θ = G z θ := heq hθ
      have h := hlip.dist_le_mul θ a
      rw [Real.dist_eq, Real.dist_eq, Real.coe_toNNReal K hK0] at h
      rw [abs_of_pos (by linarith [hθ.1] : (0 : ℝ) < θ - a)] at h
      calc |f z θ - G z a| = |G z θ - G z a| := by rw [heqθ]
        _ ≤ K * (θ - a) := h
    have hfb : ∀ z θ, 0 < z → θ ∈ Ioo a b → |f z θ - G z b| ≤ K * (b - θ) := by
      intro z θ hz hθ
      obtain ⟨hlip, heq⟩ := hG z hz
      have heqθ : f z θ = G z θ := heq hθ
      have h := hlip.dist_le_mul θ b
      rw [Real.dist_eq, Real.dist_eq, Real.coe_toNNReal K hK0] at h
      rw [abs_of_neg (by linarith [hθ.2] : θ - b < 0), neg_sub] at h
      calc |f z θ - G z b| = |G z θ - G z b| := by rw [heqθ]
        _ ≤ K * (b - θ) := h
    exact ⟨fun z => G z a, fun z => G z b,
      cont_rate_left (f := f) (g := fun z => G z a) (a := a) (b := b) (K := K)
        hab hK0 hcont hfa,
      cont_rate_right (f := f) (g := fun z => G z b) (a := a) (b := b) (K := K)
        hab hK0 hcont hfb,
      fun z θ hz hθ => ⟨hfa z θ hz hθ, hfb z θ hz hθ⟩⟩
  · -- `K < 0`: the rate hypothesis is unsatisfiable, so the statement is vacuous.
    exfalso
    have hKlt : K < 0 := not_le.mp hK0
    have hmid : (a + b) / 2 ∈ Ioo a b := ⟨by linarith, by linarith⟩
    have h1 := hB 1 ((a + b) / 2) one_pos hmid
    have h2 : (0 : ℝ) ≤ |Work.Spaces.pth f 1 ((a + b) / 2)| := abs_nonneg _
    linarith

end Work.FTS_StreamBdry.SB25
end
end
-- ===== merged: Submission.Work.FTS_StreamBdry.SB25.oddPerS_pieces =====
section

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

/-!
# B8a `oddPerS_pieces`

`Work.FTS_StreamBdry.SB25.OddPerSPieces P`: the odd `π`-periodic extension `oddPerS P` of the
`θ > 0` piece of `P` (`Work.FTS.StreamBdryIface.oddPerS`,

`oddPerS P w θ = if θ < -π/2 then -oddCore(-π-θ) else if θ ≤ π/2 then oddCore θ else -oddCore(π-θ)`

with `oddCore` the odd extension across `θ = 0`) is odd on the strip and agrees with `P`,
`-P(-·)`, `-P(π-·)` on the three pieces `(0,π/2]`, `[-π/2,0)`, `(π/2,π)`.

The argument is a pure case analysis in `θ`: no smoothness, decay or boundary information about
`P` is used, and the hypothesis `P · (π/2) = 0` is in fact not needed for any of the five
conjuncts (it only records that the pieces glue continously at `θ = π/2`).
-/

noncomputable section
open scoped Real

namespace Work.FTS_StreamBdry.SB25

open Work.FTS.StreamBdryIface (oddPerS)

/-- The `θ > 0` piece of `oddPerS`, odd-extended across `θ = 0`:
`oddCore P w θ = P w θ` for `θ > 0`, `= -P w (-θ)` for `θ < 0`, `= 0` at `θ = 0`. -/
def oddCore (P : ℝ → ℝ → ℝ) (w θ : ℝ) : ℝ :=
  if 0 < θ then P w θ else if θ < 0 then -P w (-θ) else 0

/-- `oddCore` on the positive half-line. -/
lemma oddCore_of_pos (P : ℝ → ℝ → ℝ) (w θ : ℝ) (h : 0 < θ) : oddCore P w θ = P w θ := by
  simp only [oddCore]; rw [ite_eq_left h]

/-- `oddCore` on the negative half-line. -/
lemma oddCore_of_neg (P : ℝ → ℝ → ℝ) (w θ : ℝ) (h : θ < 0) : oddCore P w θ = -P w (-θ) := by
  simp only [oddCore]
  rw [ite_eq_right (not_lt.mpr (le_of_lt h)), ite_eq_left h]

/-- `oddCore` at the origin. -/
lemma oddCore_of_zero (P : ℝ → ℝ → ℝ) (w : ℝ) : oddCore P w 0 = 0 := by
  simp [oddCore]

/-- `oddCore` is odd. -/
lemma oddCore_neg (P : ℝ → ℝ → ℝ) (w θ : ℝ) : oddCore P w (-θ) = -oddCore P w θ := by
  rcases lt_trichotomy θ 0 with h | h | h
  · rw [oddCore_of_pos P w (-θ) (by linarith), oddCore_of_neg P w θ h]; ring
  · subst h; simp [oddCore_of_zero]
  · rw [oddCore_of_neg P w (-θ) (by linarith), oddCore_of_pos P w θ h, neg_neg]

/-- The definition of `oddPerS`, unfolded (definitional). -/
lemma oddPerS_eq (P : ℝ → ℝ → ℝ) (w θ : ℝ) :
    oddPerS P w θ =
      (if θ < -(π / 2) then -oddCore P w (-π - θ)
       else if θ ≤ π / 2 then oddCore P w θ else -oddCore P w (π - θ)) := rfl

/-- `oddPerS` below the strip. -/
lemma oddPerS_of_lt {P : ℝ → ℝ → ℝ} {w θ : ℝ} (h : θ < -(π / 2)) :
    oddPerS P w θ = -oddCore P w (-π - θ) := by
  rw [oddPerS_eq, ite_eq_left h]

/-- `oddPerS` inside the strip `[-π/2, π/2]`. -/
lemma oddPerS_of_mid {P : ℝ → ℝ → ℝ} {w θ : ℝ} (h1 : -(π / 2) ≤ θ) (h2 : θ ≤ π / 2) :
    oddPerS P w θ = oddCore P w θ := by
  rw [oddPerS_eq, ite_eq_right (by linarith : ¬ θ < -(π / 2)), ite_eq_left h2]

/-- `oddPerS` above the strip. -/
lemma oddPerS_of_gt {P : ℝ → ℝ → ℝ} {w θ : ℝ} (h : π / 2 < θ) :
    oddPerS P w θ = -oddCore P w (π - θ) := by
  rw [oddPerS_eq, ite_eq_right (by linarith [Real.pi_pos] : ¬ θ < -(π / 2)),
    ite_eq_right (by linarith : ¬ θ ≤ π / 2)]

theorem oddPerS_pieces (P : ℝ → ℝ → ℝ) :
    Work.FTS_StreamBdry.SB25.OddPerSPieces P := by
  intro _h
  refine ⟨?_, ?_, ?_, ?_, ?_⟩
  · -- oddness on the strip
    intro w θ
    rcases lt_trichotomy θ (-(π / 2)) with hlt | heq | hge
    · -- `θ < -π/2`: the reflection lands above the strip
      have hgt' : π / 2 < -θ := by linarith
      rw [oddPerS_of_gt hgt', oddPerS_of_lt hlt,
        show π - -θ = -(-π - θ) by ring, oddCore_neg]
    · -- `θ = -π/2`
      subst heq
      rw [oddPerS_of_mid (by linarith [Real.pi_pos]) (by linarith [Real.pi_pos]),
        oddPerS_of_mid (by linarith [Real.pi_pos]) (by linarith [Real.pi_pos]),
        show -(-(π / 2)) = π / 2 by ring, oddCore_neg]
      ring
    · -- `-π/2 < θ`
      by_cases hle : θ ≤ π / 2
      · rw [oddPerS_of_mid (by linarith) (by linarith),
          oddPerS_of_mid (le_of_lt hge) hle, oddCore_neg]
      · -- `π/2 < θ`: the reflection lands below the strip
        have hgt : π / 2 < θ := lt_of_not_ge hle
        have hlt' : -θ < -(π / 2) := by linarith
        rw [oddPerS_of_lt hlt', oddPerS_of_gt hgt,
          show -π - -θ = -(π - θ) by ring, oddCore_neg]
  · -- the `θ > 0` piece
    intro w θ hpos hle
    rw [oddPerS_of_mid (by linarith) hle, oddCore_of_pos P w θ hpos]
  · -- the `θ < 0` piece
    intro w θ hge hneg
    rw [oddPerS_of_mid hge (by linarith), oddCore_of_neg P w θ hneg]
  · -- the `θ > π/2` piece
    intro w θ hgt hlt
    rw [oddPerS_of_gt hgt, oddCore_of_pos P w (π - θ) (by linarith : 0 < π - θ)]
  · -- the origin
    intro w
    rw [oddPerS_of_mid (by linarith [Real.pi_pos]) (by linarith [Real.pi_pos]),
      oddCore_of_zero P w]

end Work.FTS_StreamBdry.SB25
end
end
-- ===== merged: Submission.Work.FTS_StreamBdry.SB6.UprimeAux.OdeFacts =====
section

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

/-!
# `Work.FTS_StreamBdry.SB6.UprimeAux.OdeFacts` — elementary facts about the weight `wfun`

The quotient `wfun θ / sin 2θ = sin θ cos²θ / 2` is *unconditional* (Lean's `x / 0 = 0`
convention agrees with the trigonometric value at the zeros of `sin 2θ`), whence `gwt A C` is
continuous on all of `ℝ`.  We also record the abbreviations `u1fun`, `Gfun` used throughout the
ODE bound.
-/

noncomputable section
open scoped Real Topology
open Set Filter MeasureTheory

namespace Work.FTS_StreamBdry.SB6.UprimeAux

set_option autoImplicit false
set_option linter.unusedVariables false

/-- `wfun θ / sin 2θ = sin θ cos²θ / 2`, with no side condition (both sides vanish where
`sin 2θ` does, and Lean's `x / 0 = 0` convention makes this an equality everywhere). -/
lemma wfun_div_s2_eq (θ : ℝ) : wfun θ / Real.sin (2 * θ) = Real.sin θ * Real.cos θ ^ 2 / 2 := by
  rw [wfun, Real.sin_two_mul]
  rcases eq_or_ne (Real.sin θ) 0 with hs | hs
  · simp [hs]
  rcases eq_or_ne (Real.cos θ) 0 with hc | hc
  · simp [hc]
  · field_simp

/-- `gwt A C` is continuous: it equals `A · sin θ cos²θ / 2 + C · sin²θ cos³θ`. -/
lemma continuous_gwt (A C : ℝ) : Continuous (gwt A C) := by
  have h : gwt A C = fun t : ℝ =>
      A * (Real.sin t * Real.cos t ^ 2 / 2)
        + C * (Real.sin t ^ 2 * Real.cos t ^ 3) := by
    funext t
    rw [gwt_def, wfun_div_s2_eq t, wfun]
  rw [h]
  fun_prop


/-- `gwt A C ≥ 0` on `[0, π/2]`. -/
lemma gwt_nonneg_Icc {A C θ : ℝ} (hA : 0 ≤ A) (hC : 0 ≤ C)
    (hθ : θ ∈ Set.Icc (0 : ℝ) (Real.pi / 2)) : 0 ≤ gwt A C θ := by
  have hs : 0 ≤ Real.sin θ :=
    Real.sin_nonneg_of_mem_Icc ⟨hθ.1, by linarith [hθ.2, Real.pi_pos]⟩
  have hc : 0 ≤ Real.cos θ :=
    Real.cos_nonneg_of_mem_Icc ⟨by linarith [Real.pi_pos, hθ.1], by linarith [hθ.2]⟩
  rw [gwt_def, wfun_div_s2_eq]
  have h1 : 0 ≤ Real.sin θ * Real.cos θ ^ 2 / 2 := by
    have := sq_nonneg (Real.cos θ); positivity
  have h2 : 0 ≤ wfun θ := by
    rw [wfun]
    have hc2 : 0 ≤ Real.cos θ ^ 2 := sq_nonneg _
    have hc3 : 0 ≤ Real.cos θ ^ 3 := by
      rw [show Real.cos θ ^ 3 = Real.cos θ * Real.cos θ ^ 2 by ring]
      exact mul_nonneg hc hc2
    exact mul_nonneg (sq_nonneg _) hc3
  exact add_nonneg (mul_nonneg hA h1) (mul_nonneg hC h2)

/-- The `θ`-slice derivative `u'(θ) = ∂_θ u z θ`, as a function of `θ`. -/
def u1fun (u : ℝ → ℝ → ℝ) (z : ℝ) : ℝ → ℝ := fun θ => deriv (fun θ' => u z θ') θ

/-- `G = wfun · u'`, the quantity whose derivative is `wfun · H`. -/
def Gfun (u : ℝ → ℝ → ℝ) (z : ℝ) : ℝ → ℝ := fun θ => wfun θ * u1fun u z θ

@[simp] lemma u1fun_apply (u : ℝ → ℝ → ℝ) (z θ : ℝ) :
    u1fun u z θ = deriv (fun θ' => u z θ') θ := rfl

@[simp] lemma Gfun_apply (u : ℝ → ℝ → ℝ) (z θ : ℝ) :
    Gfun u z θ = wfun θ * deriv (fun θ' => u z θ') θ := rfl

end Work.FTS_StreamBdry.SB6.UprimeAux
end
end
