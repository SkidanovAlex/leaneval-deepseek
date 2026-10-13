import Mathlib.Algebra.Order.Star.Real
import Mathlib.Analysis.Real.Pi.Bounds
import Mathlib.MeasureTheory.Integral.Bochner.Set
import Mathlib.MeasureTheory.Measure.Lebesgue.Basic
import Submission.Work.FTS.StrongPersist.Clauses
import Submission.Work.FTS.NonlinRows.Rl1.tools
import Submission.Work.FTS.NonlinRows.Rl1.ssBounds
import Submission.Work.Spaces.sin_two_rpow

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

namespace Work.FTS.StrongPersist.H6Rows.NZaux

open scoped Real Topology ENNReal
open MeasureTheory Set Filter

/-!
# The three `F_*`-slots of the `r⁻¹`-density, with their `α`-rates

The singular part `F_*(z,θ) = α (Γ(θ)/c(α)) · 2z/(1+z)²` of the modulation profile is
`O(α z/(1+z)²)`, its angular derivative is `O(α² z/(1+z)²)` *because*
`D_θ Γ = α q(θ) Γ` carries an extra factor `α`, and its radial derivative is again
`O(α z/(1+z)²)` since `|z ∂_z F_*| ≤ F_*`.  Integrating against the angular measure
(measure `dθ`, so `∫_{Iθ} dθ = π/2`) and then against the `L₁₂`-weight `r⁻¹` — which is
absorbed by `r⁻¹·hKer r = 1/(1+r)²`, integrable on `(0,∞)` with integral `≤ 2` — gives the
three rates `α`, `α²`, `α`, uniformly in `0 < α ≤ 1`.

The proof is a single template (`slot_le`): a pointwise bound `|f r θ| ≤ c·hKer r` on
`r > 0`, `θ ∈ Iθ` yields
`∫⁻_r r⁻¹ ∫⁻_θ |f r θ| ≤ ofReal (π c)`.
The three pointwise bounds are the existing profile estimates of `rl¹`
(`Pss_Fstar_le`, `DthFstar_pt`, `DzFstar_pt`); `DthFstar_pt` is stated on the *open*
angular interval, so the two endpoints (where `sin 2θ = 0` and hence `D_θF_* = 0`) are
handled separately.
-/

/-- `hKer r = r/(1+r)²` is nonnegative on `r ≥ 0`. -/
private theorem hker_nonneg {r : ℝ} (hr : 0 ≤ r) : 0 ≤ Work.Spaces.hKer r := by
  rw [Work.Spaces.hKer_apply]; exact div_nonneg hr (by positivity)

/-- The `1/r` weight of `L₁₂` eats the numerator of `hKer r`. -/
private theorem inv_mul_hKer_eq {r : ℝ} (hr : 0 < r) :
    r⁻¹ * Work.Spaces.hKer r = (1 / (1 + r)) ^ 2 := by
  rw [Work.Spaces.hKer_apply]
  field_simp

/-- `r ↦ r⁻¹ hKer r` is integrable on `(0,∞)` (it equals `(1/(1+r))²` there). -/
private theorem integrableOn_inv_hKer :
    IntegrableOn (fun r : ℝ => r⁻¹ * Work.Spaces.hKer r) (Set.Ioi (0 : ℝ)) :=
  (Work.FTS.NonlinRows.Rl1.integrableOn_inv_one_add_sq').1 |>.congr_fun
    (fun _ hr => (inv_mul_hKer_eq hr).symm) measurableSet_Ioi

/-- **The slot template.**  A pointwise bound `|f r θ| ≤ c·hKer r` on the quadrant
(`r > 0`, `θ ∈ Iθ`) gives `∫⁻_r r⁻¹ ∫⁻_θ |f| ≤ ofReal (π c)`: the angular measure is `π/2`
and `∫_0^∞ r⁻¹ hKer r = ∫_0^∞ (1/(1+r))² ≤ 2`. -/
private theorem slot_le {c : ℝ} (hc : 0 ≤ c) {f : ℝ → ℝ → ℝ}
    (hbd : ∀ r, 0 < r → ∀ θ ∈ Work.Spaces.Iθ, |f r θ| ≤ c * Work.Spaces.hKer r) :
    ∫⁻ r in Set.Ioi (0 : ℝ), ENNReal.ofReal r⁻¹
        * (∫⁻ θ in Work.Spaces.Iθ, ENNReal.ofReal |f r θ|)
      ≤ ENNReal.ofReal (Real.pi * c) := by
  have hinnerae : ∀ᵐ r ∂(volume.restrict (Set.Ioi (0:ℝ))),
      (∫⁻ θ in Work.Spaces.Iθ, ENNReal.ofReal |f r θ|)
        ≤ ENNReal.ofReal (c * Work.Spaces.hKer r * (Real.pi/2)) := by
    filter_upwards [MeasureTheory.ae_restrict_mem measurableSet_Ioi] with r hr
    have h1 : ∀ θ ∈ Work.Spaces.Iθ,
        ENNReal.ofReal |f r θ| ≤ ENNReal.ofReal (c * Work.Spaces.hKer r) :=
      fun θ hθ => ENNReal.ofReal_le_ofReal (hbd r hr θ hθ)
    calc (∫⁻ θ in Work.Spaces.Iθ, ENNReal.ofReal |f r θ|)
        ≤ ∫⁻ θ in Work.Spaces.Iθ, ENNReal.ofReal (c * Work.Spaces.hKer r) :=
          setLIntegral_mono measurable_const h1
      _ = ENNReal.ofReal (c * Work.Spaces.hKer r) * volume Work.Spaces.Iθ :=
          setLIntegral_const _ _
      _ = ENNReal.ofReal (c * Work.Spaces.hKer r) * ENNReal.ofReal (Real.pi / 2) := by
          rw [Work.Spaces.Iθ, Real.volume_Icc, sub_zero]
      _ = ENNReal.ofReal (c * Work.Spaces.hKer r * (Real.pi / 2)) :=
          (ENNReal.ofReal_mul (mul_nonneg hc (hker_nonneg hr.le))).symm
  have hInt : IntegrableOn (fun r : ℝ => r⁻¹ * (c * Work.Spaces.hKer r * (Real.pi / 2)))
      (Set.Ioi (0:ℝ)) := by
    have hbase := integrableOn_inv_hKer
    have h2 : IntegrableOn (fun r : ℝ => (c * (Real.pi/2)) * (r⁻¹ * Work.Spaces.hKer r))
        (Set.Ioi 0) :=
      hbase.const_mul _
    refine h2.congr_fun (fun r _ => ?_) measurableSet_Ioi
    ring
  have hnn : 0 ≤ᵐ[volume.restrict (Set.Ioi (0:ℝ))]
      fun r : ℝ => r⁻¹ * (c * Work.Spaces.hKer r * (Real.pi / 2)) :=
    MeasureTheory.ae_restrict_of_forall_mem measurableSet_Ioi (fun r hr =>
      mul_nonneg (inv_nonneg.mpr hr.le)
        (mul_nonneg (mul_nonneg hc (hker_nonneg hr.le)) (by positivity)))
  have hval : ∫ r in Set.Ioi (0:ℝ), r⁻¹ * (c * Work.Spaces.hKer r * (Real.pi/2))
      ≤ Real.pi * c := by
    have hpull : (c * (Real.pi/2)) * ∫ r in Set.Ioi (0:ℝ), r⁻¹ * Work.Spaces.hKer r
        = ∫ r in Set.Ioi (0:ℝ), r⁻¹ * (c * Work.Spaces.hKer r * (Real.pi/2)) := by
      rw [← MeasureTheory.integral_const_mul]
      refine MeasureTheory.setIntegral_congr_fun measurableSet_Ioi (fun r _ => ?_)
      ring
    rw [← hpull]
    have h2 : ∫ r in Set.Ioi (0:ℝ), r⁻¹ * Work.Spaces.hKer r ≤ 2 := by
      rw [MeasureTheory.setIntegral_congr_fun measurableSet_Ioi (fun r hr => inv_mul_hKer_eq hr)]
      exact (Work.FTS.NonlinRows.Rl1.integrableOn_inv_one_add_sq').2
    calc (c * (Real.pi/2)) * ∫ r in Set.Ioi (0:ℝ), r⁻¹ * Work.Spaces.hKer r
        ≤ (c * (Real.pi/2)) * 2 := mul_le_mul_of_nonneg_left h2 (by positivity)
      _ = Real.pi * c := by ring
  calc ∫⁻ r in Set.Ioi 0, ENNReal.ofReal r⁻¹ * (∫⁻ θ in Work.Spaces.Iθ, ENNReal.ofReal |f r θ|)
      ≤ ∫⁻ r in Set.Ioi 0,
          ENNReal.ofReal r⁻¹ * ENNReal.ofReal (c * Work.Spaces.hKer r * (Real.pi/2)) :=
        MeasureTheory.lintegral_mono_ae (hinnerae.mono (fun r hr => mul_le_mul_right hr _))
    _ = ∫⁻ r in Set.Ioi 0, ENNReal.ofReal (r⁻¹ * (c * Work.Spaces.hKer r * (Real.pi/2))) := by
        rw [MeasureTheory.lintegral_congr_ae]
        filter_upwards [MeasureTheory.ae_restrict_mem measurableSet_Ioi] with r hr
        exact (ENNReal.ofReal_mul (inv_nonneg.mpr hr.le)).symm
    _ = ENNReal.ofReal (∫ r in Set.Ioi 0, r⁻¹ * (c * Work.Spaces.hKer r * (Real.pi/2))) := by
        rw [MeasureTheory.ofReal_integral_eq_lintegral_ofReal hInt hnn]
    _ ≤ ENNReal.ofReal (Real.pi * c) := ENNReal.ofReal_le_ofReal hval

/-- The angular-derivative slot: `|D_θF_*| ≤ (80/3)α² hKer r` on the closed angular
interval.  The estimate `DthFstar_pt` is on the open interval; at `θ = 0, π/2` one has
`sin 2θ = 0`, so `D_θF_* = 0` there. -/
private theorem DthFstar_slot {α : ℝ} (hα : 0 < α) (hα1 : α ≤ 1) :
    ∀ r, 0 < r → ∀ θ ∈ Work.Spaces.Iθ,
      |Work.Spaces.Dth (Work.Construction.Fstar α) r θ| ≤ (80/3) * α^2 * Work.Spaces.hKer r := by
  intro r hr θ hθ
  obtain ⟨hθ0, hθ1⟩ := hθ
  rcases eq_or_lt_of_le hθ0 with h0 | h0
  · have hz : Real.sin (2 * θ) = 0 := by rw [← h0]; simp
    rw [Work.Spaces.Dth, hz, zero_mul, abs_zero]
    exact mul_nonneg (mul_nonneg (by norm_num) (sq_nonneg α)) (hker_nonneg hr.le)
  rcases lt_or_eq_of_le hθ1 with h1 | h1
  · exact Work.FTS.NonlinRows.Rl1.DthFstar_pt hα hα1 hr h0 h1
  · have hz : Real.sin (2 * θ) = 0 := by
      rw [h1, show 2 * (Real.pi/2) = Real.pi by ring, Real.sin_pi]
    rw [Work.Spaces.Dth, hz, zero_mul, abs_zero]
    exact mul_nonneg (mul_nonneg (by norm_num) (sq_nonneg α)) (hker_nonneg hr.le)

/-- **The three `F_*`-slots.**  There is a universal `C` with, for every `0 < α ≤ 1`,
`∫⁻_r r⁻¹ (∫⁻_θ |F_*|) ≤ Cα`, `∫⁻_r r⁻¹ (∫⁻_θ |D_θF_*|) ≤ Cα²` and
`∫⁻_r r⁻¹ (∫⁻_θ |D_zF_*|) ≤ Cα`. -/
theorem FstarSlotsFa : ∃ C : ℝ, 0 < C ∧ ∀ α : ℝ, 0 < α → α ≤ 1 →
    (∫⁻ r in Set.Ioi (0 : ℝ), ENNReal.ofReal r⁻¹
        * (∫⁻ θ in Work.Spaces.Iθ, ENNReal.ofReal |Work.Construction.Fstar α r θ|))
      ≤ ENNReal.ofReal (C * α) ∧
    (∫⁻ r in Set.Ioi (0 : ℝ), ENNReal.ofReal r⁻¹
        * (∫⁻ θ in Work.Spaces.Iθ,
            ENNReal.ofReal |Work.Spaces.Dth (Work.Construction.Fstar α) r θ|))
      ≤ ENNReal.ofReal (C * α ^ 2) ∧
    (∫⁻ r in Set.Ioi (0 : ℝ), ENNReal.ofReal r⁻¹
        * (∫⁻ θ in Work.Spaces.Iθ,
            ENNReal.ofReal |Work.Spaces.Dz (Work.Construction.Fstar α) r θ|))
      ≤ ENNReal.ofReal (C * α) := by
  refine ⟨200, by norm_num, fun α hα hα1 => ⟨?_, ?_, ?_⟩⟩
  · have h := slot_le (c := 20 * α) (by positivity) (f := Work.Construction.Fstar α)
      (fun r hr θ hθ => Work.FTS.Nonlinear.Pieces.rl1Pieces.Pss_Fstar_le α r θ hα hα1 hr.le hθ)
    refine le_trans h (ENNReal.ofReal_le_ofReal ?_)
    nlinarith [Real.pi_lt_four, hα]
  · have h := slot_le (c := (80/3) * α^2) (by positivity)
      (f := Work.Spaces.Dth (Work.Construction.Fstar α)) (DthFstar_slot hα hα1)
    refine le_trans h (ENNReal.ofReal_le_ofReal ?_)
    have h1 : Real.pi * ((80/3) * α^2) ≤ 4 * ((80/3) * α^2) :=
      mul_le_mul_of_nonneg_right (le_of_lt Real.pi_lt_four) (by positivity)
    have h2 : (4:ℝ) * ((80/3) * α^2) ≤ 200 * α^2 := by nlinarith [sq_nonneg α]
    linarith
  · have h := slot_le (c := 20 * α) (by positivity)
      (f := Work.Spaces.Dz (Work.Construction.Fstar α))
      (fun r hr θ hθ => Work.FTS.NonlinRows.Rl1.DzFstar_pt hα hα1 hr hθ)
    refine le_trans h (ENNReal.ofReal_le_ofReal ?_)
    nlinarith [Real.pi_lt_four, hα]

end Work.FTS.StrongPersist.H6Rows.NZaux
