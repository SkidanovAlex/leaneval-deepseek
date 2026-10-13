import Mathlib.Analysis.Calculus.ParametricIntervalIntegral
import Mathlib.Analysis.LocallyConvex.AbsConvexOpen
import Mathlib.Analysis.SpecialFunctions.Integrability.Basic
import Submission.Work.FTS_StreamBdry.Basic
import Submission.Work.FTS_StreamBdry.SB1.rpow_ode_aux
import Submission.Work.FTS_StreamBdry.SB1.contDiffOn_uncurry_Uprime
import Submission.Work.FTS_StreamBdry.SB3.DzJDefs

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
