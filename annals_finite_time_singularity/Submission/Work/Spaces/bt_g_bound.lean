import Mathlib.Algebra.Order.Ring.Star
import Mathlib.Algebra.Order.Star.Real
import Mathlib.MeasureTheory.Integral.Prod
import Submission.Work.Spaces.Defs
import Submission.Work.Spaces.bt_aux
import Submission.Work.Spaces.HardyZ
import Submission.Work.Spaces.mixed_comm
import Submission.Work.Spaces.pth_integral

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

namespace Work.Spaces

open MeasureTheory Set Filter
open scoped Real Topology

/-- **The `θ`-Hardy bound for the bad term of §H2.**

For a.e. angle `θ ∈ [0,π/2]` and every `z ≥ 0`,

`(D_θ g(z,θ))² · sin(2θ)^{-γ} ≤ ∫₀^∞ (D_z D_θ g(s,θ) · W(s,θ))² ds`,

i.e. the squared first angular derivative, carrying the singular angular weight,
is controlled by the weighted `L²`-norm of `mixed 1 1 g = D_z D_θ g` along the
radial half-line.

The proof is the radial Hardy inequality `HardyZ` applied to the θ-slice of
`D_θ g`: `D_z (D_θ g) = mixed 1 1 g`, and the angular weight `wTheta(θ)² = sin(2θ)^{-γ}`
is constant in `z`, so it may be pulled out of the radial integral.  The
integrability hypothesis needed by `HardyZ` is obtained from the given product-measure
integrability via Fubini (`Integrable.prod_left_ae`). -/
theorem bt_g_bound (α : ℝ) (hα : 0 < α) (hα1 : α ≤ 1) (g : ℝ → ℝ → ℝ)
    (hsm : Work.Spaces.SmoothNbhd g) (hdec : Work.Spaces.DecayInZ 4 g)
    (hint : MeasureTheory.Integrable
        (fun p : ℝ × ℝ => (Work.Spaces.mixed 1 1 g p.1 p.2 * Work.Spaces.Wt α p.1 p.2) ^ 2)
        ((MeasureTheory.volume.restrict Work.Spaces.Iz).prod (MeasureTheory.volume.restrict Work.Spaces.Iθ))) :
    ∀ᵐ θ ∂(MeasureTheory.volume.restrict Work.Spaces.Iθ), ∀ z ∈ Work.Spaces.Iz,
      (Work.Spaces.Dth g z θ) ^ 2 * (Real.sin (2 * θ)) ^ (-(Work.Spaces.gam α))
        ≤ MeasureTheory.integral (MeasureTheory.volume.restrict Work.Spaces.Iz)
            (fun z' => (Work.Spaces.mixed 1 1 g z' θ * Work.Spaces.Wt α z' θ) ^ 2) := by
  -- For a.e. angle the radial slice of the weighted mixed derivative is integrable.
  have hsliceae : ∀ᵐ θ ∂(MeasureTheory.volume.restrict Work.Spaces.Iθ),
      MeasureTheory.Integrable
        (fun z => (mixed 1 1 g z θ * Wt α z θ) ^ 2) (MeasureTheory.volume.restrict Iz) :=
    hint.prod_left_ae
  filter_upwards [hsliceae, MeasureTheory.ae_restrict_mem measurableSet_Icc] with θ hintθ hθ
  intro z hz
  by_cases hzero : Real.sin (2 * θ) = 0
  · -- Degenerate angle: `D_θ g · sin(2θ) = 0`, and the integral of a square is `≥ 0`.
    have hDth : Dth g z θ = 0 := by
      show Real.sin (2 * θ) * pth g z θ = 0
      rw [hzero, zero_mul]
    rw [hDth]
    simp only [zero_pow (by norm_num : (2 : ℕ) ≠ 0), zero_mul]
    exact integral_nonneg fun z' => sq_nonneg _
  · have hsinpos : 0 < Real.sin (2 * θ) := lt_of_le_of_ne (bt_sin_nonneg hθ) (Ne.symm hzero)
    set c : ℝ := (Real.sin (2 * θ)) ^ (-(gam α)) with hcdef
    have hcpos : 0 < c := Real.rpow_pos_of_pos hsinpos _
    -- Pointwise factorisation: `(D_z D_θ g · W)² = sin(2θ)^{-γ} · (D_z D_θ g)² w²`.
    have hpoint : ∀ s : ℝ, (mixed 1 1 g s θ * Wt α s θ) ^ 2
        = c * ((Dz (Dth g) s θ) ^ 2 * (w s) ^ 2) := by
      intro s
      rw [hcdef]
      have h := bt_Wt_sq α s θ hα hθ
      show (Dz (Dth g) s θ * Wt α s θ) ^ 2 = _
      rw [mul_pow, h]
      ring
    -- The integrability hypothesis of `HardyZ`, obtained by scaling the slice.
    have hint' : MeasureTheory.Integrable
        (fun z' => (Dz (Dth g) z' θ) ^ 2 * (w z') ^ 2) (MeasureTheory.volume.restrict Iz) := by
      have h1 : MeasureTheory.Integrable
          (fun z' => c⁻¹ * (mixed 1 1 g z' θ * Wt α z' θ) ^ 2)
          (MeasureTheory.volume.restrict Iz) :=
        hintθ.const_mul _
      refine h1.congr ?_
      filter_upwards with z'
      rw [hpoint z']
      field_simp
    -- Decay of the θ-slice at infinity, from `DecayInZ 4 g`.
    have hdecθ : Filter.Tendsto (fun z => Dth g z θ) Filter.atTop (nhds 0) := by
      have h := hdec 0 1 (by norm_num) θ hθ
      have h2 : Filter.Tendsto (fun z => Real.sin (2 * θ) * pth g z θ) Filter.atTop
          (nhds (Real.sin (2 * θ) * 0)) :=
        h.const_mul (Real.sin (2 * θ))
      simp only [mul_zero] at h2
      refine h2.congr' ?_
      filter_upwards with z
      rfl
    -- The radial Hardy inequality applied to the slice of `D_θ g`.
    have hH := HardyZ (Dth g) θ (SmoothNbhd.Dth hsm) hθ hdecθ hint'
    -- Identify the target integral with `c` times the Hardy integral.
    have hRHS : MeasureTheory.integral (MeasureTheory.volume.restrict Iz)
          (fun z' => (mixed 1 1 g z' θ * Wt α z' θ) ^ 2)
        = c * MeasureTheory.integral (MeasureTheory.volume.restrict Iz)
            (fun s => (Dz (Dth g) s θ) ^ 2 * (w s) ^ 2) := by
      rw [← integral_const_mul]
      refine integral_congr_ae ?_
      filter_upwards with s
      exact hpoint s
    rw [hRHS]
    calc (Dth g z θ) ^ 2 * c = c * (Dth g z θ) ^ 2 := by ring
      _ ≤ c * MeasureTheory.integral (MeasureTheory.volume.restrict Iz)
            (fun s => (Dz (Dth g) s θ) ^ 2 * (w s) ^ 2) :=
          mul_le_mul_of_nonneg_left (hH z hz) hcpos.le

end Work.Spaces
