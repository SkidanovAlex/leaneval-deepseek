/-
Angular integration by parts with the singular weight `σ θ = sin(2θ)^{-η}` (`η = 99/100`),
in the form needed by the mixed weighted interpolation estimate:

  `∫_{Iθ} (f')² σ = -∫_{Iθ} f f'' σ + 2η ∫_{Iθ} f f' cot(2θ) σ`

for `f` of class `C²` on an *open neighbourhood* of `Iθ` with `f 0 = f (π/2) = 0`.  The
primitive is `Ψ θ = σ θ · f θ · f' θ`, whose endpoint limits `0` come from
`|f θ| ≤ M θ` near `0` (resp. `|f θ| ≤ M (π/2 - θ)` near `π/2`) together with
`σ(θ)·θ → 0` (resp. `σ(θ)(π/2 - θ) → 0`), the latter following from `sin u ≥ 2u/π`.
-/
import Mathlib.Algebra.Order.Star.Real
import Mathlib.Analysis.LocallyConvex.AbsConvexOpen
import Mathlib.Analysis.Real.Pi.Bounds
import Mathlib.Analysis.SpecialFunctions.Pow.Deriv
import Mathlib.MeasureTheory.Integral.IntervalIntegral.FundThmCalculus
import Mathlib.Order.CompletePartialOrder
import Submission.Work.Spaces.Defs
import Submission.Work.FTS.EllipticEst.ThetaPoincareDefs
import Submission.Work.FTS.EllipticEst.ThetaU.OpenAux
import Submission.Work.Elliptic.contDiffOn_one_bounds
import Submission.Work.Elliptic.integrableOn_of_rpow_majorant
import Submission.Work.Spaces.sin_rpow_le_majorant_pi

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

noncomputable section

open scoped Real Topology
open MeasureTheory Set Filter

namespace Work.FTS.EllipticEst.ThetaU

set_option autoImplicit false
set_option maxHeartbeats 1000000

/-! ## The two endpoint limits of the weight -/

/-- `θ ↦ θ ^ (1 - η)` tends to `0` as `θ → 0⁺` (since `1 - η = 1/100 > 0`). -/
theorem tendsto_rpow_one_sub_eta_nhdsGT_zero :
    Tendsto (fun θ : ℝ => θ ^ (1 - Work.Spaces.eta)) (𝓝[>] (0 : ℝ)) (𝓝 0) := by
  have hp : Work.Spaces.eta - 1 < 0 := by
    have := Work.Spaces.eta_lt_one
    linarith
  have h1 := (tendsto_rpow_neg_nhdsGT_zero hp).inv_tendsto_atTop
  refine h1.congr' ?_
  filter_upwards [self_mem_nhdsWithin] with θ hθ
  have hθ0 : 0 < θ := hθ
  show (θ ^ (Work.Spaces.eta - 1))⁻¹ = θ ^ (1 - Work.Spaces.eta)
  rw [show Work.Spaces.eta - 1 = -(1 - Work.Spaces.eta) by ring, Real.rpow_neg hθ0.le,
    inv_inv]

/-- `σ θ · θ → 0` as `θ → 0⁺`, `σ θ = sin(2θ)^{-η}`. -/
theorem tendsto_thEta_mul_self :
    Tendsto (fun θ : ℝ => thEta θ * θ) (𝓝[>] (0 : ℝ)) (𝓝 0) := by
  refine squeeze_zero' ?_ ?_ tendsto_rpow_one_sub_eta_nhdsGT_zero
  · filter_upwards [Ioo_mem_nhdsGT (by linarith [Real.pi_pos] : (0 : ℝ) < Real.pi / 2)]
      with θ hθ
    refine mul_nonneg (thEta_nonneg ?_) hθ.1.le
    rw [Work.Spaces.Iθ, Set.mem_Icc]
    exact ⟨hθ.1.le, hθ.2.le⟩
  · filter_upwards [Ioo_mem_nhdsGT (by linarith [Real.pi_pos] : (0 : ℝ) < Real.pi / 4)]
      with θ hθ
    have hθpos : 0 < θ := hθ.1
    have hsin : (4 / Real.pi) * θ ≤ Real.sin (2 * θ) := by
      have h2θ : (2 : ℝ) * θ ≤ Real.pi / 2 := by linarith [hθ.2, Real.pi_pos]
      have h2θ0 : (0 : ℝ) ≤ 2 * θ := by linarith [hθpos]
      have hcoef : (2 / Real.pi) * (2 * θ) = (4 / Real.pi) * θ := by ring
      have := Real.mul_le_sin h2θ0 h2θ
      linarith [hcoef ▸ this]
    have hθle : θ ≤ Real.sin (2 * θ) := by
      have hpi : Real.pi ≤ 4 := by linarith [Real.pi_lt_four]
      have h2 : θ ≤ (4 / Real.pi) * θ := by
        rw [div_mul_eq_mul_div, le_div_iff₀ (by linarith [Real.pi_pos])]
        nlinarith
      linarith
    have hsinpos : 0 < Real.sin (2 * θ) := lt_of_lt_of_le hθpos hθle
    have hb : Real.sin (2 * θ) ^ (-(Work.Spaces.eta)) ≤ θ ^ (-(Work.Spaces.eta)) := by
      rw [Real.rpow_neg hsinpos.le, Real.rpow_neg hθpos.le, ← one_div, ← one_div]
      exact one_div_le_one_div_of_le (Real.rpow_pos_of_pos hθpos _)
        (Real.rpow_le_rpow hθpos.le hθle (le_of_lt Work.Spaces.eta_pos))
    calc thEta θ * θ = Real.sin (2 * θ) ^ (-(Work.Spaces.eta)) * θ := rfl
      _ ≤ θ ^ (-(Work.Spaces.eta)) * θ := mul_le_mul_of_nonneg_right hb hθpos.le
      _ = θ ^ (1 - Work.Spaces.eta) := by
            rw [show (1 : ℝ) - Work.Spaces.eta = 1 + (-(Work.Spaces.eta)) by ring,
              Real.rpow_add hθpos 1 (-(Work.Spaces.eta)), Real.rpow_one]
            ring

/-- `θ ↦ (π/2 - θ) ^ (1 - η)` tends to `0` as `θ → (π/2)⁻`. -/
theorem tendsto_pi_sub_rpow_nhdsLT :
    Tendsto (fun θ : ℝ => (Real.pi / 2 - θ) ^ (1 - Work.Spaces.eta))
      (𝓝[<] (Real.pi / 2)) (𝓝 0) := by
  refine tendsto_rpow_one_sub_eta_nhdsGT_zero.comp ?_
  rw [tendsto_nhdsWithin_iff]
  refine ⟨?_, ?_⟩
  · have h : Tendsto (fun θ : ℝ => Real.pi / 2 - θ) (𝓝 (Real.pi / 2))
        (𝓝 (Real.pi / 2 - Real.pi / 2)) := tendsto_const_nhds.sub tendsto_id
    simpa using h.mono_left nhdsWithin_le_nhds
  · filter_upwards [self_mem_nhdsWithin] with θ hθ
    exact sub_pos.mpr (Set.mem_Iio.mp hθ)

/-- `σ θ · (π/2 - θ) → 0` as `θ → (π/2)⁻`, `σ θ = sin(2θ)^{-η}`. -/
theorem tendsto_thEta_mul_pi_sub :
    Tendsto (fun θ : ℝ => thEta θ * (Real.pi / 2 - θ)) (𝓝[<] (Real.pi / 2)) (𝓝 0) := by
  refine squeeze_zero' ?_ ?_ tendsto_pi_sub_rpow_nhdsLT
  · filter_upwards [Ioo_mem_nhdsLT (by linarith [Real.pi_pos] : (0:ℝ) < Real.pi / 2)]
      with θ hθ
    refine mul_nonneg (thEta_nonneg ?_) (by linarith [hθ.2])
    rw [Work.Spaces.Iθ, Set.mem_Icc]
    exact ⟨hθ.1.le, hθ.2.le⟩
  · filter_upwards [Ioo_mem_nhdsLT (by linarith [Real.pi_pos] : Real.pi / 4 < Real.pi / 2)]
      with θ hθ
    have hθ4 : Real.pi / 4 < θ := hθ.1
    have hθ2 : θ < Real.pi / 2 := hθ.2
    have hpos : 0 < Real.pi / 2 - θ := by linarith
    have hsin : (4 / Real.pi) * (Real.pi / 2 - θ) ≤ Real.sin (2 * θ) := by
      have h := Real.mul_le_sin (x := 2 * (Real.pi / 2 - θ)) (by linarith)
        (by linarith [Real.pi_pos])
      have hcoef : (2 / Real.pi) * (2 * (Real.pi / 2 - θ)) = (4 / Real.pi) * (Real.pi / 2 - θ) := by
        ring
      have harg : 2 * θ = Real.pi - 2 * (Real.pi / 2 - θ) := by ring
      rw [harg, Real.sin_pi_sub]
      linarith [hcoef ▸ h]
    have hle : Real.pi / 2 - θ ≤ Real.sin (2 * θ) := by
      have hpi : Real.pi ≤ 4 := by linarith [Real.pi_lt_four]
      have h2 : Real.pi / 2 - θ ≤ (4 / Real.pi) * (Real.pi / 2 - θ) := by
        rw [div_mul_eq_mul_div, le_div_iff₀ (by linarith [Real.pi_pos])]
        nlinarith
      linarith
    have hsinpos : 0 < Real.sin (2 * θ) := lt_of_lt_of_le hpos hle
    have hb : Real.sin (2 * θ) ^ (-(Work.Spaces.eta))
        ≤ (Real.pi / 2 - θ) ^ (-(Work.Spaces.eta)) := by
      rw [Real.rpow_neg hsinpos.le, Real.rpow_neg hpos.le, ← one_div, ← one_div]
      exact one_div_le_one_div_of_le (Real.rpow_pos_of_pos hpos _)
        (Real.rpow_le_rpow hpos.le hle (le_of_lt Work.Spaces.eta_pos))
    calc thEta θ * (Real.pi / 2 - θ)
        = Real.sin (2 * θ) ^ (-(Work.Spaces.eta)) * (Real.pi / 2 - θ) := rfl
      _ ≤ (Real.pi / 2 - θ) ^ (-(Work.Spaces.eta)) * (Real.pi / 2 - θ) :=
            mul_le_mul_of_nonneg_right hb hpos.le
      _ = (Real.pi / 2 - θ) ^ (1 - Work.Spaces.eta) := by
            rw [show (1 : ℝ) - Work.Spaces.eta = 1 + (-(Work.Spaces.eta)) by ring,
              Real.rpow_add hpos 1 (-(Work.Spaces.eta)), Real.rpow_one]
            ring


/-! ## Elementary rpow algebra at a positive point -/

theorem mul_rpow_neg_one_add {x : ℝ} (hx : 0 < x) (p : ℝ) :
    x * x ^ (-(1 + p)) = x ^ (-p) := by
  rw [show -p = 1 + -(1 + p) by ring, Real.rpow_add hx, Real.rpow_one]

theorem rpow_neg_one {x : ℝ} (hx : 0 < x) : x ^ (-1 : ℝ) = x⁻¹ := by
  rw [Real.rpow_neg hx.le, Real.rpow_one]

theorem cot_mul_thEta {θ : ℝ} (hsin : 0 < Real.sin (2 * θ)) :
    Real.cot (2 * θ) * thEta θ = Real.cos (2 * θ) * Real.sin (2 * θ) ^ (-(1 + Work.Spaces.eta)) := by
  have hsinne : Real.sin (2 * θ) ≠ 0 := ne_of_gt hsin
  have hkey : Real.sin (2 * θ) ^ (-(Work.Spaces.eta)) * (Real.sin (2 * θ))⁻¹
      = Real.sin (2 * θ) ^ (-(1 + Work.Spaces.eta)) := by
    rw [← rpow_neg_one hsin, ← Real.rpow_add hsin]
    ring_nf
  rw [Real.cot_eq_cos_div_sin, thEta, div_mul_eq_mul_div, div_eq_mul_inv, mul_assoc, hkey]

/-! ## Bounds for a `C²` slice vanishing at the endpoints -/

/-- The three bounds on a `C²` slice vanishing at `0` and `π/2` that the arguments below use:
the minimum bound on the slice itself (`Iθ`), and the bounds on the first and second derivative
on the open interval `(0,π/2)`. -/
theorem slice_bounds {f : ℝ → ℝ} (hf : ContDiffOn ℝ 2 f (Set.Ioo (-1) (Real.pi / 2 + 1)))
    (h0 : f 0 = 0) (h1 : f (Real.pi / 2) = 0) :
    ∃ C M₃ : ℝ, 0 ≤ C ∧ 0 ≤ M₃ ∧
      (∀ θ ∈ Work.Spaces.Iθ, |f θ| ≤ C * min θ (Real.pi / 2 - θ)) ∧
      (∀ θ ∈ Set.Ioo (0 : ℝ) (Real.pi / 2), |deriv f θ| ≤ C) ∧
      (∀ θ ∈ Set.Ioo (0 : ℝ) (Real.pi / 2), |deriv (deriv f) θ| ≤ M₃) := by
  have hpi : (0 : ℝ) < Real.pi / 2 := by positivity
  have hsub : Set.Icc (0 : ℝ) (Real.pi / 2) ⊆ Set.Ioo (-1) (Real.pi / 2 + 1) := by
    intro θ hθ
    exact ⟨by linarith [hθ.1], by linarith [hθ.2, Real.pi_pos]⟩
  have hf1 : ContDiffOn ℝ 1 f (Set.Icc 0 (Real.pi / 2)) := (hf.mono hsub).of_le (by norm_num)
  obtain ⟨C, hC0, hb1, hb2⟩ := Work.Elliptic.contDiffOn_one_bounds hf1 h0 h1
  have h2 : ContDiffOn ℝ 1 (deriv f) (Set.Ioo (-1) (Real.pi / 2 + 1)) :=
    hf.deriv_of_isOpen isOpen_Ioo (m := 1) (by norm_num)
  have h3 : ContinuousOn (deriv (deriv f)) (Set.Ioo (-1) (Real.pi / 2 + 1)) :=
    h2.continuousOn_deriv_of_isOpen isOpen_Ioo le_rfl
  have h3' : ContinuousOn (deriv (deriv f)) (Set.Icc 0 (Real.pi / 2)) := h3.mono hsub
  obtain ⟨x₀, -, hmax⟩ := isCompact_Icc.exists_isMaxOn ⟨0, ⟨le_rfl, hpi.le⟩⟩
    (f := fun θ => |deriv (deriv f) θ|) h3'.abs
  refine ⟨C, |deriv (deriv f) x₀|, hC0, abs_nonneg _, ?_, ?_, ?_⟩
  · intro θ hθ
    exact hb1 θ hθ
  · intro θ hθ
    rw [← Real.norm_eq_abs]
    exact hb2 θ hθ
  · intro θ hθ
    exact isMaxOn_iff.mp hmax θ (Set.Ioo_subset_Icc_self hθ)

/-! ## Integrability of the three pieces of the `η`-weighted angular IBP -/

theorem integrableOn_ang_pieces {f : ℝ → ℝ} (hf : ContDiffOn ℝ 2 f (Set.Ioo (-1) (Real.pi / 2 + 1)))
    (h0 : f 0 = 0) (h1 : f (Real.pi / 2) = 0) :
    MeasureTheory.IntegrableOn (fun θ => (deriv f θ) ^ 2 * thEta θ) Work.Spaces.Iθ ∧
    MeasureTheory.IntegrableOn (fun θ => f θ * deriv (deriv f) θ * thEta θ) Work.Spaces.Iθ ∧
    MeasureTheory.IntegrableOn
      (fun θ => f θ * deriv f θ * Real.cot (2 * θ) * thEta θ) Work.Spaces.Iθ := by
  obtain ⟨C, M₃, hC0, hM₃0, hfb, hdb, hddb⟩ := slice_bounds hf h0 h1
  have hη0 : (0 : ℝ) ≤ Work.Spaces.eta := Work.Spaces.eta_pos.le
  have hη1 : Work.Spaces.eta < 1 := Work.Spaces.eta_lt_one
  have hIoo : Set.Ioo (0 : ℝ) (Real.pi / 2) ⊆ Work.Spaces.Iθ := Set.Ioo_subset_Icc_self
  have hsub : Set.Ioo (0 : ℝ) (Real.pi / 2) ⊆ Set.Ioo (-1) (Real.pi / 2 + 1) :=
    fun θ hθ => ⟨by linarith [hθ.1], by linarith [hθ.2, Real.pi_pos]⟩
  -- continuity of the three integrands on the open interval
  have hcont_f : ContinuousOn f (Set.Ioo (0 : ℝ) (Real.pi / 2)) :=
    hf.continuousOn.mono hsub
  have hcont_f' : ContinuousOn (deriv f) (Set.Ioo (0 : ℝ) (Real.pi / 2)) :=
    (ContDiffOn.continuousOn_deriv_of_isOpen (n := 2) hf isOpen_Ioo (by norm_num)).mono hsub
  have hderiv_f : ContDiffOn ℝ 1 (deriv f) (Set.Ioo (-1) (Real.pi / 2 + 1)) :=
    hf.deriv_of_isOpen isOpen_Ioo (m := 1) (by norm_num)
  have hcont_f'' : ContinuousOn (deriv (deriv f)) (Set.Ioo (0 : ℝ) (Real.pi / 2)) :=
    (hderiv_f.continuousOn_deriv_of_isOpen isOpen_Ioo (le_refl 1)).mono hsub
  have hsin_c : ContinuousOn (fun θ : ℝ => Real.sin (2 * θ)) (Set.Ioo (0 : ℝ) (Real.pi / 2)) :=
    (Real.continuous_sin.comp (continuous_const.mul continuous_id)).continuousOn
  have hsinne : ∀ θ ∈ Set.Ioo (0 : ℝ) (Real.pi / 2), Real.sin (2 * θ) ≠ 0 := fun θ hθ =>
    ne_of_gt (Real.sin_pos_of_pos_of_lt_pi (by linarith [hθ.1]) (by linarith [hθ.2, Real.pi_pos]))
  have hthEta_c : ContinuousOn thEta (Set.Ioo (0 : ℝ) (Real.pi / 2)) :=
    hsin_c.rpow_const (fun θ hθ => Or.inl (hsinne θ hθ))
  -- the three majorant bounds on `(0,π/2)`
  have hbA : ∀ θ ∈ Set.Ioo (0 : ℝ) (Real.pi / 2),
      ‖(deriv f θ) ^ 2 * thEta θ‖
        ≤ C ^ 2 * (Real.pi / 4) ^ Work.Spaces.eta
            * (θ ^ (-(Work.Spaces.eta)) + (Real.pi / 2 - θ) ^ (-(Work.Spaces.eta))) := by
    intro θ hθ
    have hs : (Real.sin (2 * θ)) ^ (-(Work.Spaces.eta))
        ≤ (Real.pi / 4) ^ Work.Spaces.eta
            * (θ ^ (-(Work.Spaces.eta)) + (Real.pi / 2 - θ) ^ (-(Work.Spaces.eta))) :=
      Work.Spaces.sin_rpow_le_majorant_pi Work.Spaces.eta θ Work.Spaces.eta_pos (hIoo hθ)
    have hd : (deriv f θ) ^ 2 ≤ C ^ 2 := by
      have h := abs_le.mp (hdb θ hθ)
      nlinarith [h.1, h.2]
    have hthEta_nn : 0 ≤ thEta θ := thEta_nonneg (hIoo hθ)
    rw [Real.norm_eq_abs, abs_of_nonneg (mul_nonneg (sq_nonneg _) hthEta_nn)]
    calc (deriv f θ) ^ 2 * thEta θ ≤ C ^ 2 * thEta θ :=
          mul_le_mul_of_nonneg_right hd hthEta_nn
      _ ≤ C ^ 2 * ((Real.pi / 4) ^ Work.Spaces.eta
            * (θ ^ (-(Work.Spaces.eta)) + (Real.pi / 2 - θ) ^ (-(Work.Spaces.eta)))) :=
          mul_le_mul_of_nonneg_left hs (sq_nonneg C)
      _ = C ^ 2 * (Real.pi / 4) ^ Work.Spaces.eta
            * (θ ^ (-(Work.Spaces.eta)) + (Real.pi / 2 - θ) ^ (-(Work.Spaces.eta))) := by ring
  have hbB : ∀ θ ∈ Set.Ioo (0 : ℝ) (Real.pi / 2),
      ‖f θ * deriv (deriv f) θ * thEta θ‖
        ≤ C * M₃ * (Real.pi / 2) * (Real.pi / 4) ^ Work.Spaces.eta
            * (θ ^ (-(Work.Spaces.eta)) + (Real.pi / 2 - θ) ^ (-(Work.Spaces.eta))) := by
    intro θ hθ
    have hs : (Real.sin (2 * θ)) ^ (-(Work.Spaces.eta))
        ≤ (Real.pi / 4) ^ Work.Spaces.eta
            * (θ ^ (-(Work.Spaces.eta)) + (Real.pi / 2 - θ) ^ (-(Work.Spaces.eta))) :=
      Work.Spaces.sin_rpow_le_majorant_pi Work.Spaces.eta θ Work.Spaces.eta_pos (hIoo hθ)
    have hmin_nn : 0 ≤ min θ (Real.pi / 2 - θ) :=
      le_min hθ.1.le (by linarith [hθ.2])
    have hmin_le : min θ (Real.pi / 2 - θ) ≤ Real.pi / 2 :=
      le_trans (min_le_left _ _) hθ.2.le
    have hfa : |f θ| ≤ C * (Real.pi / 2) := by
      have := hfb θ (hIoo hθ)
      calc |f θ| ≤ C * min θ (Real.pi / 2 - θ) := this
        _ ≤ C * (Real.pi / 2) := mul_le_mul_of_nonneg_left hmin_le hC0
    have hda : |deriv (deriv f) θ| ≤ M₃ := hddb θ hθ
    have hthEta_nn : 0 ≤ thEta θ := thEta_nonneg (hIoo hθ)
    have hK : 0 ≤ C * M₃ * (Real.pi / 2) * (Real.pi / 4) ^ Work.Spaces.eta :=
      mul_nonneg (mul_nonneg (mul_nonneg hC0 hM₃0) (by linarith [Real.pi_pos]))
        (Real.rpow_nonneg (by positivity) _)
    rw [Real.norm_eq_abs, abs_mul, abs_mul, abs_of_nonneg hthEta_nn]
    have h1 : |f θ| * |deriv (deriv f) θ| * thEta θ ≤ (C * (Real.pi / 2)) * M₃ * thEta θ :=
      mul_le_mul_of_nonneg_right
        (mul_le_mul hfa hda (abs_nonneg _) (mul_nonneg hC0 (by linarith [Real.pi_pos])))
        hthEta_nn
    have h2 : (C * (Real.pi / 2)) * M₃ * thEta θ
        ≤ (C * (Real.pi / 2)) * M₃ * ((Real.pi / 4) ^ Work.Spaces.eta
            * (θ ^ (-(Work.Spaces.eta)) + (Real.pi / 2 - θ) ^ (-(Work.Spaces.eta)))) :=
      mul_le_mul_of_nonneg_left hs (mul_nonneg (mul_nonneg hC0 (by linarith [Real.pi_pos])) hM₃0)
    calc |f θ| * |deriv (deriv f) θ| * thEta θ ≤ (C * (Real.pi / 2)) * M₃ * thEta θ := h1
      _ ≤ (C * (Real.pi / 2)) * M₃ * ((Real.pi / 4) ^ Work.Spaces.eta
            * (θ ^ (-(Work.Spaces.eta)) + (Real.pi / 2 - θ) ^ (-(Work.Spaces.eta)))) := h2
      _ = C * M₃ * (Real.pi / 2) * (Real.pi / 4) ^ Work.Spaces.eta
            * (θ ^ (-(Work.Spaces.eta)) + (Real.pi / 2 - θ) ^ (-(Work.Spaces.eta))) := by ring
  have hcot_le : ∀ θ ∈ Set.Ioo (0 : ℝ) (Real.pi / 2),
      |Real.cot (2 * θ)| * thEta θ ≤ Real.sin (2 * θ) ^ (-(1 + Work.Spaces.eta)) := by
    intro θ hθ
    have hsin : 0 < Real.sin (2 * θ) := Real.sin_pos_of_pos_of_lt_pi (by linarith [hθ.1])
      (by linarith [hθ.2, Real.pi_pos])
    have h1 : Real.cot (2 * θ) * thEta θ = Real.cos (2 * θ) * Real.sin (2 * θ) ^ (-(1 + Work.Spaces.eta)) :=
      cot_mul_thEta hsin
    have h2 : |Real.cot (2 * θ)| * thEta θ
        = |Real.cos (2 * θ)| * Real.sin (2 * θ) ^ (-(1 + Work.Spaces.eta)) := by
      rw [← abs_of_nonneg (thEta_nonneg (hIoo hθ)), ← abs_mul, h1, abs_mul,
        abs_of_nonneg (Real.rpow_nonneg hsin.le _)]
    rw [h2]
    exact mul_le_of_le_one_left (Real.rpow_nonneg hsin.le _) (Real.abs_cos_le_one _)
  have hbC : ∀ θ ∈ Set.Ioo (0 : ℝ) (Real.pi / 2),
      ‖f θ * deriv f θ * Real.cot (2 * θ) * thEta θ‖
        ≤ C ^ 2 * (Real.pi / 4) ^ (1 + Work.Spaces.eta)
            * (θ ^ (-(Work.Spaces.eta)) + (Real.pi / 2 - θ) ^ (-(Work.Spaces.eta))) := by
    intro θ hθ
    have hsin : 0 < Real.sin (2 * θ) := Real.sin_pos_of_pos_of_lt_pi (by linarith [hθ.1])
      (by linarith [hθ.2, Real.pi_pos])
    have hsin_nn : 0 ≤ Real.sin (2 * θ) := hsin.le
    have hθp : 0 < θ := hθ.1
    have hπp : 0 < Real.pi / 2 - θ := by linarith [hθ.2]
    have hs : (Real.sin (2 * θ)) ^ (-(1 + Work.Spaces.eta))
        ≤ (Real.pi / 4) ^ (1 + Work.Spaces.eta)
            * (θ ^ (-(1 + Work.Spaces.eta)) + (Real.pi / 2 - θ) ^ (-(1 + Work.Spaces.eta))) :=
      Work.Spaces.sin_rpow_le_majorant_pi (1 + Work.Spaces.eta) θ (by linarith) (hIoo hθ)
    have hcot := hcot_le θ hθ
    have hfa : |f θ| ≤ C * min θ (Real.pi / 2 - θ) := hfb θ (hIoo hθ)
    have hda : |deriv f θ| ≤ C := hdb θ hθ
    have hmin_nn : 0 ≤ min θ (Real.pi / 2 - θ) := le_min hθp.le hπp.le
    have hthEta_nn : 0 ≤ thEta θ := thEta_nonneg (hIoo hθ)
    have hx1 : min θ (Real.pi / 2 - θ) * θ ^ (-(1 + Work.Spaces.eta)) ≤ θ ^ (-(Work.Spaces.eta)) := by
      calc min θ (Real.pi / 2 - θ) * θ ^ (-(1 + Work.Spaces.eta))
          ≤ θ * θ ^ (-(1 + Work.Spaces.eta)) :=
            mul_le_mul_of_nonneg_right (min_le_left _ _) (Real.rpow_nonneg hθp.le _)
        _ = θ ^ (-(Work.Spaces.eta)) := mul_rpow_neg_one_add hθp Work.Spaces.eta
    have hx2 : min θ (Real.pi / 2 - θ) * (Real.pi / 2 - θ) ^ (-(1 + Work.Spaces.eta))
        ≤ (Real.pi / 2 - θ) ^ (-(Work.Spaces.eta)) := by
      calc min θ (Real.pi / 2 - θ) * (Real.pi / 2 - θ) ^ (-(1 + Work.Spaces.eta))
          ≤ (Real.pi / 2 - θ) * (Real.pi / 2 - θ) ^ (-(1 + Work.Spaces.eta)) :=
            mul_le_mul_of_nonneg_right (min_le_right _ _) (Real.rpow_nonneg hπp.le _)
        _ = (Real.pi / 2 - θ) ^ (-(Work.Spaces.eta)) := mul_rpow_neg_one_add hπp Work.Spaces.eta
    have hK : 0 ≤ C ^ 2 * (Real.pi / 4) ^ (1 + Work.Spaces.eta) :=
      mul_nonneg (sq_nonneg C) (Real.rpow_nonneg (by positivity) _)
    have hK2 : 0 ≤ C ^ 2 := sq_nonneg C
    rw [Real.norm_eq_abs, abs_mul, abs_mul, abs_mul, abs_of_nonneg hthEta_nn]
    -- now: `|f θ| * |deriv f θ| * |cot| * thEta θ ≤ ...`
    have step1 : |f θ| * |deriv f θ| * |Real.cot (2 * θ)| * thEta θ
        = |f θ| * |deriv f θ| * (|Real.cot (2 * θ)| * thEta θ) := by ring
    rw [step1]
    have step2 : |f θ| * |deriv f θ| * (|Real.cot (2 * θ)| * thEta θ)
        ≤ (C * min θ (Real.pi / 2 - θ)) * C * Real.sin (2 * θ) ^ (-(1 + Work.Spaces.eta)) := by
      refine mul_le_mul (mul_le_mul hfa hda (abs_nonneg _) (mul_nonneg hC0 hmin_nn)) hcot
        (mul_nonneg (abs_nonneg _) hthEta_nn) (mul_nonneg (mul_nonneg hC0 hmin_nn) hC0)
    have step3 : (C * min θ (Real.pi / 2 - θ)) * C * Real.sin (2 * θ) ^ (-(1 + Work.Spaces.eta))
        ≤ (C * min θ (Real.pi / 2 - θ)) * C * ((Real.pi / 4) ^ (1 + Work.Spaces.eta)
            * (θ ^ (-(1 + Work.Spaces.eta)) + (Real.pi / 2 - θ) ^ (-(1 + Work.Spaces.eta)))) :=
      mul_le_mul_of_nonneg_left hs (mul_nonneg (mul_nonneg hC0 hmin_nn) hC0)
    have step4 : (C * min θ (Real.pi / 2 - θ)) * C * ((Real.pi / 4) ^ (1 + Work.Spaces.eta)
          * (θ ^ (-(1 + Work.Spaces.eta)) + (Real.pi / 2 - θ) ^ (-(1 + Work.Spaces.eta))))
        = C ^ 2 * (Real.pi / 4) ^ (1 + Work.Spaces.eta)
          * (min θ (Real.pi / 2 - θ) * θ ^ (-(1 + Work.Spaces.eta))
            + min θ (Real.pi / 2 - θ) * (Real.pi / 2 - θ) ^ (-(1 + Work.Spaces.eta))) := by
      ring
    have step5 : C ^ 2 * (Real.pi / 4) ^ (1 + Work.Spaces.eta)
          * (min θ (Real.pi / 2 - θ) * θ ^ (-(1 + Work.Spaces.eta))
            + min θ (Real.pi / 2 - θ) * (Real.pi / 2 - θ) ^ (-(1 + Work.Spaces.eta)))
        ≤ C ^ 2 * (Real.pi / 4) ^ (1 + Work.Spaces.eta)
          * (θ ^ (-(Work.Spaces.eta)) + (Real.pi / 2 - θ) ^ (-(Work.Spaces.eta))) :=
      mul_le_mul_of_nonneg_left (add_le_add hx1 hx2) hK
    calc |f θ| * |deriv f θ| * (|Real.cot (2 * θ)| * thEta θ)
        ≤ (C * min θ (Real.pi / 2 - θ)) * C * Real.sin (2 * θ) ^ (-(1 + Work.Spaces.eta)) := step2
      _ ≤ (C * min θ (Real.pi / 2 - θ)) * C * ((Real.pi / 4) ^ (1 + Work.Spaces.eta)
            * (θ ^ (-(1 + Work.Spaces.eta)) + (Real.pi / 2 - θ) ^ (-(1 + Work.Spaces.eta)))) := step3
      _ = C ^ 2 * (Real.pi / 4) ^ (1 + Work.Spaces.eta)
          * (min θ (Real.pi / 2 - θ) * θ ^ (-(1 + Work.Spaces.eta))
            + min θ (Real.pi / 2 - θ) * (Real.pi / 2 - θ) ^ (-(1 + Work.Spaces.eta))) := step4
      _ ≤ C ^ 2 * (Real.pi / 4) ^ (1 + Work.Spaces.eta)
          * (θ ^ (-(Work.Spaces.eta)) + (Real.pi / 2 - θ) ^ (-(Work.Spaces.eta))) := step5
  refine ⟨?_, ?_, ?_⟩
  · exact Work.Elliptic.integrableOn_of_rpow_majorant hη0 hη1
      (C := C ^ 2 * (Real.pi / 4) ^ Work.Spaces.eta)
      (mul_nonneg (sq_nonneg C) (Real.rpow_nonneg (by positivity) _))
      (hcont_f'.pow 2 |>.mul hthEta_c) (fun θ hθ => by
        rw [Real.norm_eq_abs]; exact hbA θ hθ)
  · exact Work.Elliptic.integrableOn_of_rpow_majorant hη0 hη1
      (C := C * M₃ * (Real.pi / 2) * (Real.pi / 4) ^ Work.Spaces.eta)
      (mul_nonneg (mul_nonneg (mul_nonneg hC0 hM₃0) (by linarith [Real.pi_pos]))
        (Real.rpow_nonneg (by positivity) _))
      ((hcont_f.mul hcont_f'').mul hthEta_c) hbB
  · refine Work.Elliptic.integrableOn_of_rpow_majorant hη0 hη1
      (C := C ^ 2 * (Real.pi / 4) ^ (1 + Work.Spaces.eta))
      (mul_nonneg (sq_nonneg C) (Real.rpow_nonneg (by positivity) _)) ?_ hbC
    have hcos_c : ContinuousOn (fun θ : ℝ => Real.cos (2 * θ)) (Set.Ioo (0 : ℝ) (Real.pi / 2)) :=
      (Real.continuous_cos.comp (continuous_const.mul continuous_id)).continuousOn
    have hcot_c : ContinuousOn (fun θ : ℝ => Real.cot (2 * θ)) (Set.Ioo (0 : ℝ) (Real.pi / 2)) := by
      refine ContinuousOn.congr (hcos_c.div hsin_c (fun θ hθ => hsinne θ hθ)) (fun θ hθ => ?_)
      simpa using Real.cot_eq_cos_div_sin (2 * θ)
    exact ((hcont_f.mul hcont_f').mul hcot_c).mul hthEta_c

/-! ## The endpoint limits of the primitive -/

theorem tendsto_primitive_nhdsGT_zero {f : ℝ → ℝ}
    (hf : ContDiffOn ℝ 2 f (Set.Ioo (-1) (Real.pi / 2 + 1))) (h0 : f 0 = 0)
    (h1 : f (Real.pi / 2) = 0) :
    Tendsto (fun θ => thEta θ * (f θ * deriv f θ)) (𝓝[>] (0 : ℝ)) (𝓝 0) := by
  obtain ⟨C, M₃, hC0, hM₃0, hfb, hdb, hddb⟩ := slice_bounds hf h0 h1
  have hpi : (0 : ℝ) < Real.pi / 2 := by positivity
  rw [tendsto_zero_iff_norm_tendsto_zero]
  refine squeeze_zero' (g := fun θ => C ^ 2 * (thEta θ * θ)) ?_ ?_ ?_
  · filter_upwards with θ
    exact norm_nonneg _
  · filter_upwards [Ioo_mem_nhdsGT hpi] with θ hθ
    have hthEta_nn : 0 ≤ thEta θ := thEta_nonneg (Set.Ioo_subset_Icc_self hθ)
    have hfa : |f θ| ≤ C * min θ (Real.pi / 2 - θ) := hfb θ (Set.Ioo_subset_Icc_self hθ)
    have hda : |deriv f θ| ≤ C := hdb θ hθ
    have hmin : min θ (Real.pi / 2 - θ) ≤ θ := min_le_left _ _
    have hmin_nn : 0 ≤ min θ (Real.pi / 2 - θ) := le_min hθ.1.le (by linarith [hθ.2])
    rw [Real.norm_eq_abs, abs_mul, abs_of_nonneg hthEta_nn, abs_mul]
    have h1 : |f θ| * |deriv f θ| ≤ C * θ * C := by
      refine mul_le_mul (le_trans hfa (mul_le_mul_of_nonneg_left hmin hC0)) hda (abs_nonneg _)
        (mul_nonneg hC0 hθ.1.le)
    calc thEta θ * (|f θ| * |deriv f θ|) ≤ thEta θ * (C * θ * C) :=
          mul_le_mul_of_nonneg_left h1 hthEta_nn
      _ = C ^ 2 * (thEta θ * θ) := by ring
  · simpa using tendsto_thEta_mul_self.const_mul (C ^ 2)

theorem tendsto_primitive_nhdsLT_pi {f : ℝ → ℝ}
    (hf : ContDiffOn ℝ 2 f (Set.Ioo (-1) (Real.pi / 2 + 1))) (h0 : f 0 = 0)
    (h1 : f (Real.pi / 2) = 0) :
    Tendsto (fun θ => thEta θ * (f θ * deriv f θ)) (𝓝[<] (Real.pi / 2)) (𝓝 0) := by
  obtain ⟨C, M₃, hC0, hM₃0, hfb, hdb, hddb⟩ := slice_bounds hf h0 h1
  have hpi : (0 : ℝ) < Real.pi / 2 := by positivity
  rw [tendsto_zero_iff_norm_tendsto_zero]
  refine squeeze_zero' (g := fun θ => C ^ 2 * (thEta θ * (Real.pi / 2 - θ))) ?_ ?_ ?_
  · filter_upwards with θ
    exact norm_nonneg _
  · filter_upwards [Ioo_mem_nhdsLT hpi] with θ hθ
    have hthEta_nn : 0 ≤ thEta θ := thEta_nonneg (Set.Ioo_subset_Icc_self hθ)
    have hfa : |f θ| ≤ C * min θ (Real.pi / 2 - θ) := hfb θ (Set.Ioo_subset_Icc_self hθ)
    have hda : |deriv f θ| ≤ C := hdb θ hθ
    have hmin : min θ (Real.pi / 2 - θ) ≤ Real.pi / 2 - θ := min_le_right _ _
    have hmin_nn : 0 ≤ min θ (Real.pi / 2 - θ) := le_min hθ.1.le (by linarith [hθ.2])
    rw [Real.norm_eq_abs, abs_mul, abs_of_nonneg hthEta_nn, abs_mul]
    have h1 : |f θ| * |deriv f θ| ≤ C * (Real.pi / 2 - θ) * C := by
      refine mul_le_mul (le_trans hfa (mul_le_mul_of_nonneg_left hmin hC0)) hda (abs_nonneg _)
        (mul_nonneg hC0 (by linarith [hθ.2]))
    calc thEta θ * (|f θ| * |deriv f θ|) ≤ thEta θ * (C * (Real.pi / 2 - θ) * C) :=
          mul_le_mul_of_nonneg_left h1 hthEta_nn
      _ = C ^ 2 * (thEta θ * (Real.pi / 2 - θ)) := by ring
  · simpa using tendsto_thEta_mul_pi_sub.const_mul (C ^ 2)

/-! ## The angular integration by parts -/

theorem ang_ibp_eta {f : ℝ → ℝ} (hf : ContDiffOn ℝ 2 f (Set.Ioo (-1) (Real.pi / 2 + 1)))
    (h0 : f 0 = 0) (h1 : f (Real.pi / 2) = 0) :
    (∫ θ in Work.Spaces.Iθ, (deriv f θ) ^ 2 * thEta θ)
      = - (∫ θ in Work.Spaces.Iθ, f θ * deriv (deriv f) θ * thEta θ)
        + 2 * Work.Spaces.eta
            * (∫ θ in Work.Spaces.Iθ, f θ * deriv f θ * Real.cot (2 * θ) * thEta θ) := by
  have hpi : (0 : ℝ) < Real.pi / 2 := by positivity
  obtain ⟨hA, hB, hC⟩ := integrableOn_ang_pieces hf h0 h1
  -- the derivative of the primitive
  have hderiv : ∀ θ ∈ Set.Ioo (0 : ℝ) (Real.pi / 2),
      HasDerivAt (fun θ => thEta θ * (f θ * deriv f θ))
        ((deriv f θ) ^ 2 * thEta θ + (f θ * deriv (deriv f) θ * thEta θ
          - 2 * Work.Spaces.eta * (f θ * deriv f θ * Real.cot (2 * θ) * thEta θ))) θ := by
    intro θ hθ
    have hsin : 0 < Real.sin (2 * θ) := Real.sin_pos_of_pos_of_lt_pi (by linarith [hθ.1])
      (by linarith [hθ.2, Real.pi_pos])
    have hmem : (θ : ℝ) ∈ Set.Ioo (-1) (Real.pi / 2 + 1) :=
      ⟨by linarith [hθ.1], by linarith [hθ.2, Real.pi_pos]⟩
    have hs2 : HasDerivAt (fun θ' : ℝ => Real.sin (2 * θ')) (2 * Real.cos (2 * θ)) θ := by
      have h1' : HasDerivAt (fun θ' : ℝ => 2 * θ') (2 : ℝ) θ := by
        simpa using (hasDerivAt_id θ).const_mul (2 : ℝ)
      simpa [Function.comp_def, mul_comm] using (Real.hasDerivAt_sin (2 * θ)).comp θ h1'
    have hsig : HasDerivAt (fun θ' : ℝ => (Real.sin (2 * θ')) ^ (-(Work.Spaces.eta)))
        (-(2 * Work.Spaces.eta) * (Real.cot (2 * θ) * thEta θ)) θ := by
      have hbase := (Real.hasDerivAt_rpow_const (x := Real.sin (2 * θ)) (p := -(Work.Spaces.eta))
        (Or.inl hsin.ne')).comp θ hs2
      refine hbase.congr_deriv ?_
      rw [cot_mul_thEta hsin]
      rw [show -(Work.Spaces.eta) - 1 = -(1 + Work.Spaces.eta) by ring]
      ring
    have hdf : HasDerivAt f (deriv f θ) θ :=
      ((hf.contDiffAt (isOpen_Ioo.mem_nhds hmem)).differentiableAt two_ne_zero).hasDerivAt
    have hdf' : HasDerivAt (deriv f) (deriv (deriv f) θ) θ := by
      have hcd : ContDiffAt ℝ 1 (deriv f) θ :=
        (hf.deriv_of_isOpen isOpen_Ioo (m := 1) (by norm_num)).contDiffAt (isOpen_Ioo.mem_nhds hmem)
      exact (hcd.differentiableAt one_ne_zero).hasDerivAt
    have hall := hsig.mul (hdf.mul hdf')
    have hfun : (fun θ : ℝ => thEta θ * (f θ * deriv f θ))
        = (fun θ' : ℝ => Real.sin (2 * θ') ^ (-(Work.Spaces.eta))) * (f * deriv f) := by
      funext θ'
      simp only [thEta, Pi.mul_apply]
    rw [hfun]
    have hval : ((deriv f θ) ^ 2 * thEta θ + (f θ * deriv (deriv f) θ * thEta θ
          - 2 * Work.Spaces.eta * (f θ * deriv f θ * Real.cot (2 * θ) * thEta θ)))
        = (-(2 * Work.Spaces.eta) * (Real.cot (2 * θ) * thEta θ) * (f * deriv f) θ
            + Real.sin (2 * θ) ^ (-(Work.Spaces.eta))
              * (deriv f θ * deriv f θ + f θ * deriv (deriv f) θ)) := by
      simp only [Pi.mul_apply, thEta]
      ring
    rw [hval]
    exact hall
  -- interval integrability of the derivative
  have hintA : IntervalIntegrable (fun θ => (deriv f θ) ^ 2 * thEta θ) volume 0 (Real.pi / 2) :=
    (intervalIntegrable_iff_integrableOn_Ioc_of_le hpi.le).mpr
      (hA.mono_set Set.Ioc_subset_Icc_self)
  have hintB : IntervalIntegrable (fun θ => f θ * deriv (deriv f) θ * thEta θ) volume 0 (Real.pi / 2) :=
    (intervalIntegrable_iff_integrableOn_Ioc_of_le hpi.le).mpr
      (hB.mono_set Set.Ioc_subset_Icc_self)
  have hintC : IntervalIntegrable
      (fun θ => f θ * deriv f θ * Real.cot (2 * θ) * thEta θ) volume 0 (Real.pi / 2) :=
    (intervalIntegrable_iff_integrableOn_Ioc_of_le hpi.le).mpr
      (hC.mono_set Set.Ioc_subset_Icc_self)
  have hint : IntervalIntegrable (fun θ => (deriv f θ) ^ 2 * thEta θ
      + (f θ * deriv (deriv f) θ * thEta θ
        - 2 * Work.Spaces.eta * (f θ * deriv f θ * Real.cot (2 * θ) * thEta θ)))
      volume 0 (Real.pi / 2) :=
    hintA.add (hintB.sub (hintC.const_mul _))
  -- the fundamental theorem of calculus
  have hFTC : ∫ θ in (0 : ℝ)..(Real.pi / 2), ((deriv f θ) ^ 2 * thEta θ
      + (f θ * deriv (deriv f) θ * thEta θ
        - 2 * Work.Spaces.eta * (f θ * deriv f θ * Real.cot (2 * θ) * thEta θ))) = 0 := by
    have h := intervalIntegral.integral_eq_sub_of_hasDerivAt_of_tendsto (a := (0 : ℝ))
      (b := Real.pi / 2) hpi hderiv hint
      (tendsto_primitive_nhdsGT_zero hf h0 h1) (tendsto_primitive_nhdsLT_pi hf h0 h1)
    simpa using h
  -- convert the three set integrals to interval integrals
  have hconv : ∀ g : ℝ → ℝ, (∫ θ in Work.Spaces.Iθ, g θ) = ∫ θ in (0 : ℝ)..(Real.pi / 2), g θ := by
    intro g
    rw [show Work.Spaces.Iθ = Set.Icc 0 (Real.pi / 2) from rfl,
      MeasureTheory.integral_Icc_eq_integral_Ioc, ← intervalIntegral.integral_of_le hpi.le]
  rw [hconv (fun θ => (deriv f θ) ^ 2 * thEta θ),
    hconv (fun θ => f θ * deriv (deriv f) θ * thEta θ),
    hconv (fun θ => f θ * deriv f θ * Real.cot (2 * θ) * thEta θ)]
  -- split the integral
  have hsplit : (∫ θ in (0 : ℝ)..(Real.pi / 2), ((deriv f θ) ^ 2 * thEta θ
      + (f θ * deriv (deriv f) θ * thEta θ
        - 2 * Work.Spaces.eta * (f θ * deriv f θ * Real.cot (2 * θ) * thEta θ))))
      = (∫ θ in (0 : ℝ)..(Real.pi / 2), (deriv f θ) ^ 2 * thEta θ)
        + (∫ θ in (0 : ℝ)..(Real.pi / 2), f θ * deriv (deriv f) θ * thEta θ)
        - 2 * Work.Spaces.eta
            * (∫ θ in (0 : ℝ)..(Real.pi / 2), f θ * deriv f θ * Real.cot (2 * θ) * thEta θ) := by
    rw [intervalIntegral.integral_add hintA (hintB.sub (hintC.const_mul _)),
      intervalIntegral.integral_sub hintB (hintC.const_mul _),
      intervalIntegral.integral_const_mul]
    ring
  linarith [hFTC, hsplit]

end Work.FTS.EllipticEst.ThetaU
