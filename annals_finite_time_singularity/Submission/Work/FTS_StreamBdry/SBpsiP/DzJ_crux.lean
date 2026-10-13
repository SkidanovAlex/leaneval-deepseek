import Mathlib.Analysis.Calculus.ParametricIntervalIntegral
import Mathlib.Analysis.LocallyConvex.AbsConvexOpen
import Mathlib.Analysis.SpecialFunctions.Integrability.Basic
import Mathlib.Order.Interval.Basic
import Submission.Work.FTS_StreamBdry.Basic
import Submission.Work.FTS_StreamBdry.SB3.DzJDefs

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

/-!
# `Work.FTS_StreamBdry.SBpsiP.DzJ_crux` — differentiating the scaled parameter integral

The level-0 representation of the stream function is
`psiP αG Ψ = -(s2 θ/αG)·J c (U'(Ψ))` with `c = 3/αG - 1` and the *scaled parameter integral*

  `J c h z θ = ∫₀¹ v^c · h (z v) θ dv`.

This file proves that `D_z = z ∂_z` may be moved inside that integral:

  `D_z (J c h) z θ = J c (D_z h) z θ`   on the open quadrant `Qd = (0,∞) × (0,π/2)`,

together with the differentiability of the `z`-slice of `J c h`, which is what makes the
identity iterable.  The proof is the standard differentiation under the interval integral
`intervalIntegral.hasDerivAt_integral_of_dominated_loc_of_deriv_le`, with the domination
`|v^c·(v·∂_z h(zv,θ))| = v^c·|D_z h (zv,θ)|/z ≤ (2M/z)·v^c`, integrable on `(0,1)`
because `-1 < c`.  The point of using the *interval* version is that its measurability
hypotheses are stated for `volume.restrict (uIoc 0 1) = volume.restrict (Ioc 0 1)`, on
which — unlike on `Icc 0 1` — every integrand is continuous, so no measurability
bookkeeping at `v = 0` is needed.

Everything is stated with hypotheses on the whole open quadrant, as they arise from
`SlotBd` for `h = D_z^j (U'(Ψ))`, `j ≤ 2`.
-/

noncomputable section
open scoped Real Topology Interval
open Set Filter MeasureTheory

namespace Work.FTS_StreamBdry.SBpsiP

open Work.FTS.StreamBdryIface (Uprime SlotBd)

set_option autoImplicit false

/-- The open quadrant is open. -/
theorem isOpen_Qd' : IsOpen Work.Construction.Qd := isOpen_Ioi.prod isOpen_Ioo

/-- **Differentiation of the scaled parameter integral.**  Under the slot-type hypotheses
(continuity of `h` and `D_z h` on `Qd`, differentiability of the `z`-slices, and the uniform
bounds `|h| ≤ M`, `|D_z h| ≤ M`), the parametric integral `J c h` is differentiable in `z` and
`D_z (J c h) = J c (D_z h)`. -/
theorem J_Dz_eq {c M : ℝ} (hc : -1 < c) {h : ℝ → ℝ → ℝ}
    (hcont : ContinuousOn (Function.uncurry h) Work.Construction.Qd)
    (hcontD : ContinuousOn (Function.uncurry (Work.Spaces.Dz h)) Work.Construction.Qd)
    (hslice : ∀ z θ, (z, θ) ∈ Work.Construction.Qd →
      DifferentiableAt ℝ (fun z' => h z' θ) z)
    (hbdd : ∀ z θ, (z, θ) ∈ Work.Construction.Qd → |h z θ| ≤ M)
    (hbnd : ∀ z θ, (z, θ) ∈ Work.Construction.Qd → |Work.Spaces.Dz h z θ| ≤ M) :
    ∀ z θ, (z, θ) ∈ Work.Construction.Qd →
      DifferentiableAt ℝ (fun x => Work.FTS_StreamBdry.SB3.J c h x θ) z ∧
      Work.Spaces.Dz (Work.FTS_StreamBdry.SB3.J c h) z θ
        = Work.FTS_StreamBdry.SB3.J c (Work.Spaces.Dz h) z θ := by
  intro z θ hmem
  obtain ⟨hz, hθ0, hθ1⟩ := Work.FTS_StreamBdry.mem_Qd.mp hmem
  have hθ : θ ∈ Ioo (0 : ℝ) (π / 2) := ⟨hθ0, hθ1⟩
  -- `M ≥ 0`
  have hM : 0 ≤ M := by
    have h1 : ((1 : ℝ), π / 4) ∈ Work.Construction.Qd :=
      Work.FTS_StreamBdry.mem_Qd.mpr
        ⟨by norm_num, by linarith [Real.pi_pos], by linarith [Real.pi_pos]⟩
    exact le_trans (abs_nonneg _) (hbdd _ _ h1)
  -- `pz h` is continuous on the open quadrant
  have hpzcont : ContinuousOn (fun p : ℝ × ℝ => Work.Spaces.pz h p.1 p.2)
      Work.Construction.Qd := by
    have hdiv : ContinuousOn
        (fun p : ℝ × ℝ => Function.uncurry (Work.Spaces.Dz h) p / p.1)
        Work.Construction.Qd :=
      hcontD.div continuousOn_fst (fun p hp => ne_of_gt (Work.FTS_StreamBdry.Qd_pos hp))
    refine hdiv.congr (fun p hp => ?_)
    show Work.Spaces.pz h p.1 p.2 = Work.Spaces.Dz h p.1 p.2 / p.1
    rw [Work.Spaces.Dz,
      mul_div_cancel_left₀ _ (ne_of_gt (Work.FTS_StreamBdry.Qd_pos hp))]
  -- continuity of the two integrands on `(0,1]`
  have hcontF : ∀ x : ℝ, 0 < x →
      ContinuousOn (fun v : ℝ => v ^ c * h (x * v) θ) (Set.Ioc (0 : ℝ) 1) := by
    intro x hx
    have h1 : ContinuousOn (fun v : ℝ => v ^ c) (Set.Ioc (0 : ℝ) 1) :=
      continuousOn_id.rpow_const (fun v hv => Or.inl (ne_of_gt hv.1))
    have h2 : ContinuousOn (fun v : ℝ => h (x * v) θ) (Set.Ioc (0 : ℝ) 1) := by
      have hlin : ContinuousOn (fun v : ℝ => (x * v, θ)) (Set.Ioc (0 : ℝ) 1) :=
        ((continuous_const.mul continuous_id).prodMk continuous_const).continuousOn
      have hcomp := hcont.comp hlin (fun v hv => ⟨mul_pos hx hv.1, hθ0, hθ1⟩)
      simpa [Function.comp_def, Function.uncurry] using hcomp
    convert h1.mul h2 using 1
  have hcontF' : ∀ x : ℝ, 0 < x → ContinuousOn
      (fun v : ℝ => v ^ c * (v * Work.Spaces.pz h (x * v) θ)) (Set.Ioc (0 : ℝ) 1) := by
    intro x hx
    have h1 : ContinuousOn (fun v : ℝ => v ^ c) (Set.Ioc (0 : ℝ) 1) :=
      continuousOn_id.rpow_const (fun v hv => Or.inl (ne_of_gt hv.1))
    have h2 : ContinuousOn (fun v : ℝ => v) (Set.Ioc (0 : ℝ) 1) := continuousOn_id
    have h3 : ContinuousOn (fun v : ℝ => Work.Spaces.pz h (x * v) θ) (Set.Ioc (0 : ℝ) 1) := by
      have hlin : ContinuousOn (fun v : ℝ => (x * v, θ)) (Set.Ioc (0 : ℝ) 1) :=
        ((continuous_const.mul continuous_id).prodMk continuous_const).continuousOn
      have hcomp := hpzcont.comp hlin (fun v hv => ⟨mul_pos hx hv.1, hθ0, hθ1⟩)
      simpa [Function.comp_def, Function.uncurry] using hcomp
    convert h1.mul (h2.mul h3) using 1
  -- the neighbourhood of `z` on which everything is differentiable; on it `x > z/2`
  have hs : Set.Ioo (z / 2) (z + 1) ∈ 𝓝 z :=
    isOpen_Ioo.mem_nhds ⟨by linarith, by linarith⟩
  -- measurability of `F x` and of `F' z`
  have hF_meas : ∀ᶠ x in 𝓝 z, AEStronglyMeasurable
      (fun v : ℝ => v ^ c * h (x * v) θ) (volume.restrict (Set.uIoc (0 : ℝ) 1)) := by
    filter_upwards [hs] with x hx
    rw [Set.uIoc_of_le (by norm_num : (0 : ℝ) ≤ 1)]
    exact (hcontF x (by linarith [hx.1, hz])).aestronglyMeasurable measurableSet_Ioc
  have hF'_meas : AEStronglyMeasurable
      (fun v : ℝ => v ^ c * (v * Work.Spaces.pz h (z * v) θ))
      (volume.restrict (Set.uIoc (0 : ℝ) 1)) := by
    rw [Set.uIoc_of_le (by norm_num : (0 : ℝ) ≤ 1)]
    exact (hcontF' z hz).aestronglyMeasurable measurableSet_Ioc
  -- integrability of `F z`
  have hF_int : IntervalIntegrable (fun v : ℝ => v ^ c * h (z * v) θ) volume 0 1 := by
    have hle : ∀ᵐ u ∂volume.restrict (Set.Ioc (0 : ℝ) 1),
        ‖u ^ c * h (z * u) θ‖ ≤ M * u ^ c := by
      rw [ae_restrict_iff' measurableSet_Ioc]
      refine Filter.Eventually.of_forall (fun u hu => ?_)
      have hu' : (z * u, θ) ∈ Work.Construction.Qd := ⟨mul_pos hz hu.1, hθ0, hθ1⟩
      have hbu : |h (z * u) θ| ≤ M := hbdd _ _ hu'
      have hx : (0 : ℝ) ≤ u ^ c := Real.rpow_nonneg hu.1.le c
      rw [Real.norm_eq_abs, abs_mul, abs_of_nonneg hx]
      calc u ^ c * |h (z * u) θ| ≤ u ^ c * M := mul_le_mul_of_nonneg_left hbu hx
        _ = M * u ^ c := by ring
    have hmeas : AEStronglyMeasurable (fun u : ℝ => u ^ c * h (z * u) θ)
        (volume.restrict (Set.Ioc (0 : ℝ) 1)) :=
      (hcontF z hz).aestronglyMeasurable measurableSet_Ioc
    have hg : IntegrableOn (fun u : ℝ => M * u ^ c) (Set.Ioc (0 : ℝ) 1) volume :=
      (intervalIntegrable_iff_integrableOn_Ioc_of_le (by norm_num : (0 : ℝ) ≤ 1)).mp
        ((intervalIntegral.intervalIntegrable_rpow' (a := 0) (b := 1) hc).const_mul M)
    exact (intervalIntegrable_iff_integrableOn_Ioc_of_le (by norm_num : (0 : ℝ) ≤ 1)).mpr
      (hg.mono' hmeas hle)
  -- integrability of the dominating function
  have hbnd_int : IntervalIntegrable (fun v : ℝ => (2 * M / z) * v ^ c) volume 0 1 :=
    (intervalIntegral.intervalIntegrable_rpow' (a := 0) (b := 1) hc).const_mul (2 * M / z)
  -- the domination of `F'`
  have h_bound : ∀ᵐ t ∂volume, t ∈ Set.uIoc (0 : ℝ) 1 → ∀ x ∈ Set.Ioo (z / 2) (z + 1),
      ‖t ^ c * (t * Work.Spaces.pz h (x * t) θ)‖ ≤ (2 * M / z) * t ^ c := by
    refine Filter.Eventually.of_forall (fun t ht => ?_)
    rw [Set.uIoc_of_le (by norm_num : (0 : ℝ) ≤ 1)] at ht
    intro x hx
    have ht0 : 0 < t := ht.1
    have hxpos : 0 < x := by linarith [hx.1, hz]
    have hxtpos : 0 < x * t := mul_pos hxpos ht0
    have hxne : x ≠ 0 := ne_of_gt hxpos
    have hb := hbnd (x * t) θ
      (show (x * t, θ) ∈ Work.Construction.Qd from ⟨hxtpos, hθ0, hθ1⟩)
    have htcpow : (0 : ℝ) ≤ t ^ c := Real.rpow_nonneg (le_of_lt ht0) c
    have hnorm : |t ^ c * (t * Work.Spaces.pz h (x * t) θ)|
        = t ^ c * (t * |Work.Spaces.pz h (x * t) θ|) := by
      rw [abs_mul, abs_of_nonneg htcpow, abs_mul, abs_of_pos ht0]
    have hD : t * |Work.Spaces.pz h (x * t) θ| = |Work.Spaces.Dz h (x * t) θ| / x := by
      rw [Work.Spaces.Dz, abs_mul, abs_of_pos hxtpos]
      field_simp
    have h2 : |Work.Spaces.Dz h (x * t) θ| / x ≤ 2 * M / z := by
      have h3 : |Work.Spaces.Dz h (x * t) θ| / x ≤ M / x := by
        gcongr
      have h4 : M / x ≤ 2 * M / z := by
        have h5 : M / x ≤ M / (z / 2) :=
          div_le_div_of_nonneg_left hM (by linarith [hz]) (by linarith [hx.1])
        have h6 : M / (z / 2) = 2 * M / z := by
          rw [div_eq_mul_inv, inv_div, div_eq_mul_inv]
          ring
        linarith [h5, h6]
      linarith
    rw [Real.norm_eq_abs, hnorm, hD]
    calc t ^ c * (|Work.Spaces.Dz h (x * t) θ| / x) ≤ t ^ c * (2 * M / z) :=
          mul_le_mul_of_nonneg_left h2 htcpow
      _ = 2 * M / z * t ^ c := by ring
  -- the differentiability of `F · t`
  have h_diff : ∀ᵐ t ∂volume, t ∈ Set.uIoc (0 : ℝ) 1 → ∀ x ∈ Set.Ioo (z / 2) (z + 1),
      HasDerivAt (fun x' : ℝ => t ^ c * h (x' * t) θ)
        (t ^ c * (t * Work.Spaces.pz h (x * t) θ)) x := by
    refine Filter.Eventually.of_forall (fun t ht => ?_)
    rw [Set.uIoc_of_le (by norm_num : (0 : ℝ) ≤ 1)] at ht
    intro x hx
    have ht0 : 0 < t := ht.1
    have hxpos : 0 < x := by linarith [hx.1, hz]
    have hxmem : (x * t, θ) ∈ Work.Construction.Qd :=
      ⟨mul_pos hxpos ht0, hθ0, hθ1⟩
    have h1 : HasDerivAt (fun y : ℝ => h y θ) (Work.Spaces.pz h (x * t) θ) (x * t) :=
      (hslice (x * t) θ hxmem).hasDerivAt
    have h2 : HasDerivAt (fun x' : ℝ => x' * t) t x := by
      simpa using (hasDerivAt_id x).mul_const t
    have h3 : HasDerivAt (fun x' : ℝ => h (x' * t) θ)
        (Work.Spaces.pz h (x * t) θ * t) x := by
      simpa [Function.comp_def] using h1.comp x h2
    have h4 : HasDerivAt (fun x' : ℝ => h (x' * t) θ) (t * Work.Spaces.pz h (x * t) θ) x :=
      h3.congr_deriv (by ring)
    exact h4.const_mul (t ^ c)
  obtain ⟨-, hderiv⟩ := intervalIntegral.hasDerivAt_integral_of_dominated_loc_of_deriv_le
    (μ := volume) (a := (0 : ℝ)) (b := 1)
    (bound := fun v : ℝ => (2 * M / z) * v ^ c)
    (F := fun x v => v ^ c * h (x * v) θ)
    (F' := fun x v => v ^ c * (v * Work.Spaces.pz h (x * v) θ))
    (x₀ := z) (s := Set.Ioo (z / 2) (z + 1)) hs hF_meas hF_int hF'_meas h_bound hbnd_int h_diff
  refine ⟨?_, ?_⟩
  · simpa only [Work.FTS_StreamBdry.SB3.J_apply] using hderiv.differentiableAt
  · have hpzJ : Work.Spaces.pz (Work.FTS_StreamBdry.SB3.J c h) z θ
        = ∫ v in (0 : ℝ)..1, v ^ c * (v * Work.Spaces.pz h (z * v) θ) := by
      simpa only [Work.FTS_StreamBdry.SB3.J_apply, Work.Spaces.pz] using hderiv.deriv
    rw [Work.Spaces.Dz, hpzJ]
    have hpoint : ∀ v : ℝ, z * (v ^ c * (v * Work.Spaces.pz h (z * v) θ))
        = v ^ c * (Work.Spaces.Dz h (z * v) θ) := by
      intro v
      rw [Work.Spaces.Dz]
      ring
    calc z * ∫ v in (0 : ℝ)..1, v ^ c * (v * Work.Spaces.pz h (z * v) θ)
        = ∫ v in (0 : ℝ)..1, z * (v ^ c * (v * Work.Spaces.pz h (z * v) θ)) :=
          (intervalIntegral.integral_const_mul _ _).symm
      _ = ∫ v in (0 : ℝ)..1, v ^ c * (Work.Spaces.Dz h (z * v) θ) := by
          refine intervalIntegral.integral_congr (fun v _ => ?_)
          exact hpoint v
      _ = Work.FTS_StreamBdry.SB3.J c (Work.Spaces.Dz h) z θ := rfl

end Work.FTS_StreamBdry.SBpsiP
