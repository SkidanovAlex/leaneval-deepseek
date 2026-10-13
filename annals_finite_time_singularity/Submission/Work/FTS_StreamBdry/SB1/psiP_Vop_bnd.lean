import Mathlib.Algebra.Order.Star.Real
import Mathlib.Analysis.Calculus.ParametricIntervalIntegral
import Mathlib.Analysis.LocallyConvex.AbsConvexOpen
import Mathlib.Analysis.SpecialFunctions.Integrals.Basic
import Submission.Work.FTS_StreamBdry.Basic
import Submission.Work.FTS_StreamBdry.SB1.contDiffOn_uncurry_Uprime
import Submission.Work.FTS_StreamBdry.SB3.DzJDefs

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
