/-
# `Work.FTS.EllSol.EllPkgAux.MollDom.slice_data`

The *slice data* of a trace-class datum `G` (`Work.FTS.EllSol.EllPkgAux.TraceClass G`):

* the angular slices `s ↦ G w s` and `s ↦ D_zG w s` are continuous on `Iθ = [0, π/2]`
  (for `w > 0`);
* `D_zG` and `D_z²G` vanish at the two endpoints `θ = 0, π/2` (the two Dirichlet conditions
  are *structural*: `G` itself vanishes there as a function of `z`, hence so does every
  `z`-derivative of the `θ`-slice);
* the slice `s ↦ D_z²G w s` is integrable on `Iθ` for `w > 0`.

The only non-structural ingredient is the last one: `SliceHonestOpen G` (part of `TraceClass`)
supplies the integrability of `(D_z²G w θ)² (w w)² σ_η(θ)` on `Iθ`, and on `Iθ` the weight
`(w w)² σ_η(θ)` is `≥ 1` almost everywhere (both factors being `≥ 1` on the open interval),
so `|D_z²G| ≤ 1 + (D_z²G)² (w w)² σ_η` a.e.; adding the integrable constant `1` on the
compact interval `Iθ` gives the conclusion.

For the continuity of the slice of `D_zG` the endpoint *traces* of `TraceClass` (the two
one-sided limits of `D_zG` at `0⁺` and `(π/2)⁻`, which vanish) are used at the endpoints and
`SmoothOpen.pz` at the interior points.
-/
import Mathlib.Algebra.Order.Star.Real
import Mathlib.Analysis.Calculus.ContDiff.Defs
import Mathlib.MeasureTheory.Integral.IntegrableOn
import Mathlib.MeasureTheory.Measure.Lebesgue.Basic
import Submission.Work.FTS.EllSol.EllPkgAux.MollBase
import Submission.Work.FTS.EllipticEst.OpenQDefs
import Submission.Work.EllipticEst.Core.i0Aux.InterpDefs

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

namespace Work.FTS.EllSol.EllPkgAux.MollDom

open scoped Real Topology
open MeasureTheory Set Filter

/-! ## Elementary one-dimensional and angular facts -/

/-- `√a ≤ 1 + a` for `a ≥ 0`. -/
private theorem sqrt_le_one_add_self {a : ℝ} (ha : 0 ≤ a) : Real.sqrt a ≤ 1 + a := by
  have h : a ≤ (1 + a) ^ 2 := by nlinarith
  calc Real.sqrt a ≤ Real.sqrt ((1 + a) ^ 2) := Real.sqrt_le_sqrt h
    _ = 1 + a := Real.sqrt_sq (by linarith)

/-- The squared radial weight is at least `1`. -/
private theorem one_le_w_sq {w : ℝ} (hw : 0 < w) : 1 ≤ (Work.Spaces.w w) ^ 2 := by
  have h : 1 ≤ Work.Spaces.w w := by
    rw [Work.Spaces.w, one_le_div (by positivity : (0 : ℝ) < w ^ 2)]
    nlinarith
  calc (1 : ℝ) = 1 ^ 2 := by norm_num
    _ ≤ (Work.Spaces.w w) ^ 2 := pow_le_pow_left₀ (by norm_num) h 2

/-- On the open angular interval the weight `σ_η` is at least `1`. -/
private theorem one_le_thEta_of_mem_Ioo {θ : ℝ} (hθ : θ ∈ Set.Ioo (0 : ℝ) (Real.pi / 2)) :
    1 ≤ Work.FTS.EllipticEst.thEta θ := by
  have hs0 : 0 < Real.sin (2 * θ) :=
    Real.sin_pos_of_pos_of_lt_pi (by linarith [hθ.1]) (by linarith [hθ.2, Real.pi_pos])
  have hs1 : Real.sin (2 * θ) ≤ 1 := Real.sin_le_one _
  have hneg : -(Work.Spaces.eta) ≤ 0 := by rw [Work.Spaces.eta]; norm_num
  have h := Real.rpow_le_rpow_of_nonpos hs0 hs1 hneg
  rw [Real.one_rpow] at h
  simpa [Work.FTS.EllipticEst.thEta] using h

/-- Almost every point of `Iθ` is an interior point. -/
private theorem ae_mem_Ioo_Iθ : ∀ᵐ θ ∂(volume.restrict Work.Spaces.Iθ),
    θ ∈ Set.Ioo (0 : ℝ) (Real.pi / 2) := by
  rw [Work.Spaces.Iθ, ← MeasureTheory.Measure.restrict_congr_set
    (MeasureTheory.Ioo_ae_eq_Icc (μ := volume) (a := (0 : ℝ)) (b := Real.pi / 2))]
  exact MeasureTheory.ae_restrict_mem measurableSet_Ioo

/-- The angular weight is at least `1` almost everywhere on `Iθ`. -/
private theorem one_le_thEta_ae : ∀ᵐ θ ∂(volume.restrict Work.Spaces.Iθ),
    1 ≤ Work.FTS.EllipticEst.thEta θ := by
  filter_upwards [ae_mem_Ioo_Iθ] with θ hθ
  exact one_le_thEta_of_mem_Ioo hθ

/-! ## Continuity of a slice from interior continuity and the two endpoint traces -/

/-- A slice which is continuous on the open interval `(0, π/2)`, vanishes at both endpoints
and has vanishing one-sided traces there, is continuous on the closed interval `Iθ`. -/
private theorem continuousOn_Iθ_of_traces {F : ℝ → ℝ → ℝ} {w : ℝ}
    (hopen : ContinuousOn (fun s : ℝ => F w s) (Set.Ioo 0 (Real.pi / 2)))
    (hval0 : F w 0 = 0)
    (htr0 : Tendsto (fun θ : ℝ => F w θ) (nhdsWithin (0 : ℝ) (Set.Ioi 0)) (nhds 0))
    (hvalpi : F w (Real.pi / 2) = 0)
    (htrpi : Tendsto (fun θ : ℝ => F w θ)
      (nhdsWithin (Real.pi / 2) (Set.Iio (Real.pi / 2))) (nhds 0)) :
    ContinuousOn (fun s : ℝ => F w s) Work.Spaces.Iθ := by
  show ContinuousOn (fun s : ℝ => F w s) (Set.Icc 0 (Real.pi / 2))
  have hL0 : ContinuousWithinAt (fun θ : ℝ => F w θ) (Set.Ioi 0) 0 := by
    rw [ContinuousWithinAt, hval0]
    exact htr0
  have hLpi : ContinuousWithinAt (fun θ : ℝ => F w θ) (Set.Iio (Real.pi / 2)) (Real.pi / 2) := by
    rw [ContinuousWithinAt, hvalpi]
    exact htrpi
  have hj0 : ContinuousWithinAt (fun s : ℝ => F w s) (Set.Icc 0 (Real.pi / 2)) 0 :=
    (continuousWithinAt_Ioi_iff_Ici.mp hL0).mono (fun x hx => hx.1)
  have hjpi : ContinuousWithinAt (fun s : ℝ => F w s) (Set.Icc 0 (Real.pi / 2)) (Real.pi / 2) :=
    (continuousWithinAt_Iio_iff_Iic.mp hLpi).mono (fun x hx => hx.2)
  intro θ hθ
  rcases lt_trichotomy θ 0 with h | h | h
  · exact absurd hθ.1 (not_le.mpr h)
  · subst h; exact hj0
  · rcases lt_trichotomy θ (Real.pi / 2) with h2 | h2 | h2
    · exact (hopen.continuousAt (isOpen_Ioo.mem_nhds ⟨h, h2⟩)).continuousWithinAt
    · subst h2; exact hjpi
    · exact absurd hθ.2 (not_le.mpr h2)

/-! ## The vanishing endpoint values of `D_z`-derivatives -/

/-- If a datum vanishes identically at `θ = 0`, then so does `D_z` of it: the `θ = 0` slice is
the constant `0` in the radial variable, so its radial derivative vanishes. -/
private theorem dz_zero_of_slice_zero {F : ℝ → ℝ → ℝ} (hF : ∀ z : ℝ, F z 0 = 0) (z : ℝ) :
    Work.Spaces.Dz F z 0 = 0 := by
  have hslice : (fun z' : ℝ => F z' 0) = fun _ : ℝ => (0 : ℝ) := funext hF
  have hpz : Work.Spaces.pz F z 0 = 0 := by
    show deriv (fun z' : ℝ => F z' 0) z = 0
    rw [hslice, deriv_const]
  rw [Work.Spaces.Dz, hpz, mul_zero]

/-- The `θ = π/2` analogue. -/
private theorem dz_zero_pi_of_slice_zero {F : ℝ → ℝ → ℝ} (hF : ∀ z : ℝ, F z (Real.pi / 2) = 0)
    (z : ℝ) : Work.Spaces.Dz F z (Real.pi / 2) = 0 := by
  have hslice : (fun z' : ℝ => F z' (Real.pi / 2)) = fun _ : ℝ => (0 : ℝ) := funext hF
  have hpz : Work.Spaces.pz F z (Real.pi / 2) = 0 := by
    show deriv (fun z' : ℝ => F z' (Real.pi / 2)) z = 0
    rw [hslice, deriv_const]
  rw [Work.Spaces.Dz, hpz, mul_zero]

/-! ## The target -/

theorem slice_data {G : ℝ → ℝ → ℝ} (hT : Work.FTS.EllSol.EllPkgAux.TraceClass G) :
    (∀ w : ℝ, 0 < w → ContinuousOn (fun s : ℝ => G w s) Work.Spaces.Iθ) ∧
    (∀ w : ℝ, 0 < w → ContinuousOn (fun s : ℝ => Work.Spaces.Dz G w s) Work.Spaces.Iθ) ∧
    (∀ w : ℝ, Work.Spaces.Dz G w 0 = 0) ∧ (∀ w : ℝ, Work.Spaces.Dz G w (Real.pi / 2) = 0) ∧
    (∀ w : ℝ, Work.Spaces.Dz (Work.Spaces.Dz G) w 0 = 0) ∧
    (∀ w : ℝ, Work.Spaces.Dz (Work.Spaces.Dz G) w (Real.pi / 2) = 0) ∧
    (∀ w : ℝ, 0 < w → MeasureTheory.IntegrableOn (fun s : ℝ => Work.Spaces.Dz (Work.Spaces.Dz G) w s) Work.Spaces.Iθ) := by
  obtain ⟨hsm, h0, hpi, htr0, htrpi, hdz0, hdzpi, hhon⟩ := hT
  -- the endpoint *values* of the two `D_z`-derivatives (structural, from `G z 0 = G z (π/2) = 0`)
  have hDz0' : ∀ z : ℝ, Work.Spaces.Dz G z 0 = 0 := fun z => dz_zero_of_slice_zero h0 z
  have hDzpi' : ∀ z : ℝ, Work.Spaces.Dz G z (Real.pi / 2) = 0 :=
    fun z => dz_zero_pi_of_slice_zero hpi z
  have hD2_0 : ∀ z : ℝ, Work.Spaces.Dz (Work.Spaces.Dz G) z 0 = 0 :=
    fun z => dz_zero_of_slice_zero hDz0' z
  have hD2_pi : ∀ z : ℝ, Work.Spaces.Dz (Work.Spaces.Dz G) z (Real.pi / 2) = 0 :=
    fun z => dz_zero_pi_of_slice_zero hDzpi' z
  refine ⟨?_, ?_, hDz0', hDzpi', hD2_0, hD2_pi, ?_⟩
  · -- continuity of the slice of `G` itself
    intro w hw
    exact continuousOn_Iθ_of_traces ((hsm.curry_θ hw).continuousOn) (h0 w) (htr0 w hw) (hpi w)
      (htrpi w hw)
  · -- continuity of the slice of `D_zG`: the trace hypotheses of `TraceClass` give the endpoints
    intro w hw
    refine continuousOn_Iθ_of_traces ?_ (hDz0' w) (hdz0 w hw) (hDzpi' w) (hdzpi w hw)
    have h := ((hsm.pz).curry_θ hw).continuousOn
    simpa only [Work.Spaces.Dz] using h.const_mul w
  · -- integrability of the slice of `D_z²G`, from the honest second-order slice energy
    intro w hw
    have hone : IntegrableOn (fun _ : ℝ => (1 : ℝ)) Work.Spaces.Iθ := by
      rw [Work.Spaces.Iθ]
      exact MeasureTheory.integrableOn_const (by rw [Real.volume_Icc]; exact ENNReal.ofReal_ne_top)
        (by simp)
    have hbulk : IntegrableOn (fun θ : ℝ => (Work.Spaces.Dz (Work.Spaces.Dz G) w θ) ^ 2
        * (Work.Spaces.w w) ^ 2 * Work.FTS.EllipticEst.thEta θ) Work.Spaces.Iθ := hhon.2.1 w hw
    have hdom : IntegrableOn (fun θ : ℝ => 1 + (Work.Spaces.Dz (Work.Spaces.Dz G) w θ) ^ 2
        * (Work.Spaces.w w) ^ 2 * Work.FTS.EllipticEst.thEta θ) Work.Spaces.Iθ := hone.add hbulk
    have haesm : AEStronglyMeasurable (fun θ : ℝ => Work.Spaces.Dz (Work.Spaces.Dz G) w θ)
        (volume.restrict Work.Spaces.Iθ) :=
      Work.Spaces.aesm_slice_of_continuousOn_Qd
        (fun p : ℝ × ℝ => Work.Spaces.Dz (Work.Spaces.Dz G) p.1 p.2)
        (hsm.DzIter 2).continuousOn hw
    refine hdom.mono' haesm ?_
    filter_upwards [one_le_thEta_ae] with θ hθ1
    have hA0 : 0 ≤ (Work.Spaces.Dz (Work.Spaces.Dz G) w θ) ^ 2 := sq_nonneg _
    have hc1 : 1 ≤ (Work.Spaces.w w) ^ 2 := one_le_w_sq hw
    have hB0 : 0 ≤ (Work.Spaces.Dz (Work.Spaces.Dz G) w θ) ^ 2 * (Work.Spaces.w w) ^ 2
        * Work.FTS.EllipticEst.thEta θ := mul_nonneg (mul_nonneg hA0 (by linarith)) (by linarith)
    have hkey : (Work.Spaces.Dz (Work.Spaces.Dz G) w θ) ^ 2
        ≤ (Work.Spaces.Dz (Work.Spaces.Dz G) w θ) ^ 2 * (Work.Spaces.w w) ^ 2
          * Work.FTS.EllipticEst.thEta θ := by
      calc (Work.Spaces.Dz (Work.Spaces.Dz G) w θ) ^ 2
          ≤ (Work.Spaces.Dz (Work.Spaces.Dz G) w θ) ^ 2 * (Work.Spaces.w w) ^ 2 :=
            le_mul_of_one_le_right hA0 hc1
        _ ≤ (Work.Spaces.Dz (Work.Spaces.Dz G) w θ) ^ 2 * (Work.Spaces.w w) ^ 2
              * Work.FTS.EllipticEst.thEta θ :=
            le_mul_of_one_le_right (mul_nonneg hA0 (by linarith)) hθ1
    have hbd : |Work.Spaces.Dz (Work.Spaces.Dz G) w θ|
        ≤ 1 + (Work.Spaces.Dz (Work.Spaces.Dz G) w θ) ^ 2 * (Work.Spaces.w w) ^ 2
          * Work.FTS.EllipticEst.thEta θ := by
      calc |Work.Spaces.Dz (Work.Spaces.Dz G) w θ|
          = Real.sqrt ((Work.Spaces.Dz (Work.Spaces.Dz G) w θ) ^ 2) := by
            rw [Real.sqrt_sq_eq_abs]
        _ ≤ Real.sqrt ((Work.Spaces.Dz (Work.Spaces.Dz G) w θ) ^ 2 * (Work.Spaces.w w) ^ 2
              * Work.FTS.EllipticEst.thEta θ) := Real.sqrt_le_sqrt hkey
        _ ≤ 1 + (Work.Spaces.Dz (Work.Spaces.Dz G) w θ) ^ 2 * (Work.Spaces.w w) ^ 2
              * Work.FTS.EllipticEst.thEta θ := sqrt_le_one_add_self hB0
    simpa only [Pi.add_apply, Real.norm_eq_abs] using hbd

end Work.FTS.EllSol.EllPkgAux.MollDom
