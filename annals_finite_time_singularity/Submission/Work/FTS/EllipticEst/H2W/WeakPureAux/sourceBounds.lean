import Mathlib.Algebra.Order.Star.Real
import Mathlib.Analysis.Real.Pi.Bounds
import Mathlib.Analysis.SpecialFunctions.Integrals.Basic
import Submission.Work.FTS.EllipticEst.H2W.lzero1SliceGrowth
import Submission.Work.FTS.EllipticEst.H2W.lzeroGrowthSlice
import Submission.Work.FTS.EllipticEst.StraightDefs
import Submission.Work.FTS.EllipticEst.H2W.WeakPureAux.poleBoundOfSourcePointwise

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

noncomputable section

open scoped Real Topology
open MeasureTheory Set

namespace Work.FTS.EllipticEst.H2W.WeakPureAux

/-!
# `sourceBounds`: the weighted `L¹` mass of a source with an inverse-power bound

For `u` of class `C²` on the open interval `(0, π/2)` with `Lzero1 u = g` there and

  `|g θ| ≤ C (θ^{-(R+2)} + (π/2 - θ)^{-(R+2)})`,   `R > 1`,

the weighted mass `∫ sin s cos²s |Lzero1 u s| ds` of the source over the two halves adjacent
to `π/4` obeys the *inverse-power* bounds

* `∫_θ^{π/4} sin s cos²s |Lzero1 u s| ds ≤ C (1/R + (4/π)^{R+2}(π/4)) θ^{-R}` for
  `θ ∈ (0, π/4]` (the weight `sin s cos²s ≤ s` cancels one power at `s = 0`, and the
  remaining source term `(π/2 - s)^{-(R+2)}` is bounded by `(4/π)^{R+2}` on the half);
* `∫_{π/4}^{θ} sin s cos²s |Lzero1 u s| ds ≤ C ((π²/16)(4/π)^{R+2}(π/2) + 1/(R-1))
  (π/2 - θ)^{1-R}` for `θ ∈ [π/4, π/2)` (at `s = π/2` the weight `sin s cos²s ≤ (π/2-s)²`
  cancels two powers of the second-order pole exactly, leaving the integrable
  `(π/2-s)^{-R}`; the printed constant is deliberately generous).

The four elementary interval integrals are isolated as `sinCos2_int_pow_left`,
`sinCos2_int_tsq_pow_left`, `sinCos2_int_pow_right` and `sinCos2_int_tsq_pow_right`.
-/

/-! ## The four elementary interval integrals -/

/-- `∫_θ^{π/4} sin s cos²s · s^{-(R+2)} ds ≤ θ^{-R}/R` for `0 < θ ≤ π/4`, `R > 1`:
the weight `sin s cos²s ≤ s` cancels one power of the `s = 0` pole. -/
theorem sinCos2_int_pow_left {R θ : ℝ} (hR : 1 < R)
    (hθ : θ ∈ Set.Ioc (0:ℝ) (Real.pi / 4)) :
    ∫ s in θ..(Real.pi / 4), Work.Elliptic.sinCos2 s * s ^ (-(R + 2)) ≤ θ ^ (-R) / R := by
  have hπ : 0 < Real.pi := Real.pi_pos
  obtain ⟨hθ0, hθ4⟩ := hθ
  have hRpos : 0 < R := lt_trans zero_lt_one hR
  have hsub : Set.uIcc θ (Real.pi/4) ⊆ Set.Ioi (0:ℝ) := by
    rw [Set.uIcc_of_le hθ4]; exact fun s hs => lt_of_lt_of_le hθ0 hs.1
  have hle : ∀ s ∈ Set.Icc θ (Real.pi/4),
      Work.Elliptic.sinCos2 s * s ^ (-(R+2)) ≤ s ^ (-(R+1)) := by
    intro s hs
    have hs0 : 0 < s := lt_of_lt_of_le hθ0 hs.1
    have h1 : Work.Elliptic.sinCos2 s ≤ s := sinCos2_le_self hs0.le
    have h2 : 0 ≤ s ^ (-(R+2)) := Real.rpow_nonneg hs0.le _
    refine le_trans (mul_le_mul_of_nonneg_right h1 h2) ?_
    rw [show (-(R+1) : ℝ) = 1 + -(R+2) by ring, Real.rpow_add hs0, Real.rpow_one]
  have hInt1 : IntervalIntegrable (fun s : ℝ => Work.Elliptic.sinCos2 s * s ^ (-(R+2)))
      volume θ (Real.pi/4) := by
    apply ContinuousOn.intervalIntegrable
    exact (Work.FTS.EllipticEst.H2W.LzeroGrowth.continuous_sinCos2.continuousOn).mul
      (continuousOn_id.rpow_const (p := -(R+2)) (fun s hs => Or.inl (ne_of_gt (hsub hs))))
  have hInt2 : IntervalIntegrable (fun s : ℝ => s ^ (-(R+1))) volume θ (Real.pi/4) := by
    apply ContinuousOn.intervalIntegrable
    exact continuousOn_id.rpow_const (p := -(R+1)) (fun s hs => Or.inl (ne_of_gt (hsub hs)))
  have hmono := intervalIntegral.integral_mono_on hθ4 hInt1 hInt2 hle
  have h0 : (0:ℝ) ∉ Set.uIcc θ (Real.pi/4) := by
    rw [Set.uIcc_of_le hθ4]
    exact fun h => absurd h.1 (not_le.mpr hθ0)
  have hval : (∫ s in θ..(Real.pi/4), s ^ (-(R+1))) = (θ ^ (-R) - (Real.pi/4) ^ (-R)) / R := by
    rw [integral_rpow (Or.inr ⟨by linarith, h0⟩)]
    rw [show (-(R+1) + 1 : ℝ) = -R by ring]
    field_simp
    ring
  rw [hval] at hmono
  have hb : 0 ≤ (Real.pi/4) ^ (-R) := Real.rpow_nonneg (by positivity) _
  have hfin : (θ ^ (-R) - (Real.pi/4) ^ (-R)) / R ≤ θ ^ (-R) / R := by
    apply div_le_div_of_nonneg_right _ hRpos.le
    linarith
  linarith

/-- `∫_θ^{π/4} sin s cos²s · (π/2 - s)^{-(R+2)} ds ≤ (4/π)^{R+2}(π/4) θ^{-R}`:
on `[θ, π/4]` the second-order pole is bounded by its value at `π/4`. -/
theorem sinCos2_int_tsq_pow_left {R θ : ℝ} (hR : 1 < R)
    (hθ : θ ∈ Set.Ioc (0:ℝ) (Real.pi / 4)) :
    ∫ s in θ..(Real.pi / 4), Work.Elliptic.sinCos2 s * (Real.pi/2 - s) ^ (-(R+2))
      ≤ (4/Real.pi) ^ (R+2) * (Real.pi/4) * θ ^ (-R) := by
  have hπ : 0 < Real.pi := Real.pi_pos
  obtain ⟨hθ0, hθ4⟩ := hθ
  have hRpos : 0 < R := lt_trans zero_lt_one hR
  have hmem : ∀ s ∈ Set.uIcc θ (Real.pi/4), 0 < s ∧ s ≤ Real.pi/4 := by
    intro s hs
    rw [Set.uIcc_of_le hθ4] at hs
    exact ⟨lt_of_lt_of_le hθ0 hs.1, hs.2⟩
  have hkey : (Real.pi/4) ^ (-(R+2)) = (4/Real.pi) ^ (R+2) := by
    rw [Real.rpow_neg (by positivity), ← Real.inv_rpow (by positivity : (0:ℝ) ≤ Real.pi/4)]
    congr 1
    field_simp
  have hle : ∀ s ∈ Set.Icc θ (Real.pi/4),
      Work.Elliptic.sinCos2 s * (Real.pi/2 - s) ^ (-(R+2)) ≤ (4/Real.pi) ^ (R+2) := by
    intro s hs
    have hts : Real.pi/4 ≤ Real.pi/2 - s := by linarith [hs.2]
    have h1 : (Real.pi/2 - s) ^ (-(R+2)) ≤ (Real.pi/4) ^ (-(R+2)) :=
      Real.rpow_le_rpow_of_nonpos (by positivity) hts (by linarith)
    rw [hkey] at h1
    have h2 : Work.Elliptic.sinCos2 s ≤ 1 := sinCos2_le_one s
    have h3 : 0 ≤ (Real.pi/2 - s) ^ (-(R+2)) := Real.rpow_nonneg (by linarith) _
    calc Work.Elliptic.sinCos2 s * (Real.pi/2 - s) ^ (-(R+2))
        ≤ 1 * (Real.pi/2 - s) ^ (-(R+2)) := mul_le_mul_of_nonneg_right h2 h3
      _ ≤ (4/Real.pi) ^ (R+2) := by rw [one_mul]; exact h1
  have hInt1 : IntervalIntegrable (fun s : ℝ => Work.Elliptic.sinCos2 s * (Real.pi/2 - s) ^ (-(R+2)))
      volume θ (Real.pi/4) := by
    apply ContinuousOn.intervalIntegrable
    refine (Work.FTS.EllipticEst.H2W.LzeroGrowth.continuous_sinCos2.continuousOn).mul ?_
    refine ContinuousOn.rpow_const (continuousOn_const.sub continuousOn_id) (fun s hs => Or.inl ?_)
    obtain ⟨hs0, hs1⟩ := hmem s hs
    exact (by linarith : (0:ℝ) < Real.pi/2 - s).ne'
  have hInt2 : IntervalIntegrable (fun _ : ℝ => (4/Real.pi) ^ (R+2)) volume θ (Real.pi/4) :=
    intervalIntegrable_const
  have hmono := intervalIntegral.integral_mono_on hθ4 hInt1 hInt2 hle
  rw [intervalIntegral.integral_const] at hmono
  simp only [smul_eq_mul] at hmono
  have hθ1 : θ ≤ 1 := by linarith [Real.pi_lt_four, hθ4]
  have hge1 : 1 ≤ θ ^ (-R) := by
    have hinv : θ ^ (-R) = θ⁻¹ ^ R := by
      rw [Real.rpow_neg hθ0.le R, Real.inv_rpow hθ0.le R]
    rw [hinv]
    exact Real.one_le_rpow ((one_le_inv₀ hθ0).mpr hθ1) hRpos.le
  have hstep : (Real.pi/4 - θ) * (4/Real.pi) ^ (R+2) ≤ (Real.pi/4) * (4/Real.pi) ^ (R+2) := by
    apply mul_le_mul_of_nonneg_right _ (Real.rpow_nonneg (by positivity) _)
    linarith
  have hc : 0 ≤ (Real.pi/4) * (4/Real.pi) ^ (R+2) := by positivity
  have hstep2 : (Real.pi/4) * (4/Real.pi) ^ (R+2)
      ≤ (Real.pi/4) * (4/Real.pi) ^ (R+2) * θ ^ (-R) := by
    calc (Real.pi/4) * (4/Real.pi) ^ (R+2)
        = (Real.pi/4) * (4/Real.pi) ^ (R+2) * 1 := by ring
      _ ≤ (Real.pi/4) * (4/Real.pi) ^ (R+2) * θ ^ (-R) := mul_le_mul_of_nonneg_left hge1 hc
  calc (∫ s in θ..(Real.pi/4), Work.Elliptic.sinCos2 s * (Real.pi/2 - s) ^ (-(R+2)))
      ≤ (Real.pi/4 - θ) * (4/Real.pi) ^ (R+2) := hmono
    _ ≤ (Real.pi/4) * (4/Real.pi) ^ (R+2) := hstep
    _ ≤ (Real.pi/4) * (4/Real.pi) ^ (R+2) * θ ^ (-R) := hstep2
    _ = (4/Real.pi) ^ (R+2) * (Real.pi/4) * θ ^ (-R) := by ring

/-- `∫_{π/4}^{θ} sin s cos²s · s^{-(R+2)} ds ≤ (π²/16)(4/π)^{R+2}(π/2) (π/2-θ)^{1-R}`:
on `[π/4, θ]` both factors are bounded by their value at `π/4`, and the source is estimated
by the (generous) constant of the statement. -/
theorem sinCos2_int_pow_right {R θ : ℝ} (hR : 1 < R)
    (hθ : θ ∈ Set.Ico (Real.pi/4) (Real.pi / 2)) :
    ∫ s in (Real.pi/4)..θ, Work.Elliptic.sinCos2 s * s ^ (-(R+2))
      ≤ (Real.pi^2/16) * (4/Real.pi)^(R+2) * (Real.pi/2) * (Real.pi/2 - θ)^(1-R) := by
  have hπ : 0 < Real.pi := Real.pi_pos
  obtain ⟨hθ1, hθ2⟩ := hθ
  have hRpos : 0 < R := lt_trans zero_lt_one hR
  have hmem : ∀ s ∈ Set.uIcc (Real.pi/4) θ, Real.pi/4 ≤ s ∧ 0 < s := by
    intro s hs
    rw [Set.uIcc_of_le hθ1] at hs
    exact ⟨hs.1, by linarith [hπ, hs.1]⟩
  have hkey : (Real.pi/4) ^ (-(R+2)) = (4/Real.pi) ^ (R+2) := by
    rw [Real.rpow_neg (by positivity), ← Real.inv_rpow (by positivity : (0:ℝ) ≤ Real.pi/4)]
    congr 1
    field_simp
  have hle : ∀ s ∈ Set.Icc (Real.pi/4) θ,
      Work.Elliptic.sinCos2 s * s ^ (-(R+2)) ≤ (4/Real.pi) ^ (R+2) := by
    intro s hs
    have hs0 : 0 < s := by linarith [hπ, hs.1]
    have h1 : s ^ (-(R+2)) ≤ (Real.pi/4) ^ (-(R+2)) :=
      Real.rpow_le_rpow_of_nonpos (by positivity) hs.1 (by linarith)
    rw [hkey] at h1
    have h2 : Work.Elliptic.sinCos2 s ≤ 1 := sinCos2_le_one s
    have h3 : 0 ≤ s ^ (-(R+2)) := Real.rpow_nonneg hs0.le _
    calc Work.Elliptic.sinCos2 s * s ^ (-(R+2)) ≤ 1 * s ^ (-(R+2)) :=
          mul_le_mul_of_nonneg_right h2 h3
      _ ≤ (4/Real.pi) ^ (R+2) := by rw [one_mul]; exact h1
  have hInt1 : IntervalIntegrable (fun s : ℝ => Work.Elliptic.sinCos2 s * s ^ (-(R+2)))
      volume (Real.pi/4) θ := by
    apply ContinuousOn.intervalIntegrable
    refine (Work.FTS.EllipticEst.H2W.LzeroGrowth.continuous_sinCos2.continuousOn).mul ?_
    exact ContinuousOn.rpow_const continuousOn_id (fun s hs => Or.inl (ne_of_gt (hmem s hs).2))
  have hInt2 : IntervalIntegrable (fun _ : ℝ => (4/Real.pi) ^ (R+2)) volume (Real.pi/4) θ :=
    intervalIntegrable_const
  have hmono := intervalIntegral.integral_mono_on hθ1 hInt1 hInt2 hle
  rw [intervalIntegral.integral_const] at hmono
  simp only [smul_eq_mul] at hmono
  have hdel : 1 ≤ (Real.pi/2 - θ) ^ (1-R) := by
    have hd0 : 0 < Real.pi/2 - θ := by linarith
    have hdle1 : Real.pi/2 - θ ≤ 1 := by linarith [Real.pi_lt_four]
    have hinv : (Real.pi/2 - θ) ^ (1-R) = (Real.pi/2 - θ)⁻¹ ^ (R-1) := by
      rw [show (1-R:ℝ) = -(R-1) by ring, Real.rpow_neg hd0.le, Real.inv_rpow hd0.le]
    rw [hinv]
    exact Real.one_le_rpow ((one_le_inv₀ hd0).mpr hdle1) (by linarith)
  have hstep : (θ - Real.pi/4) * (4/Real.pi)^(R+2) ≤ (Real.pi/4) * (4/Real.pi)^(R+2) := by
    apply mul_le_mul_of_nonneg_right _ (Real.rpow_nonneg (by positivity) _)
    linarith
  have hbd : (Real.pi/4) * (4/Real.pi)^(R+2)
      ≤ (Real.pi^2/16) * (4/Real.pi)^(R+2) * (Real.pi/2) * (Real.pi/2-θ)^(1-R) := by
    have hπ4 : Real.pi/4 ≤ (Real.pi^2/16) * (Real.pi/2) := by nlinarith [Real.pi_gt_three]
    have hmono2 : (Real.pi/4) * (4/Real.pi)^(R+2)
        ≤ ((Real.pi^2/16) * (Real.pi/2)) * (4/Real.pi)^(R+2) :=
      mul_le_mul_of_nonneg_right hπ4 (Real.rpow_nonneg (by positivity) _)
    have hc : 0 ≤ ((Real.pi^2/16) * (Real.pi/2)) * (4/Real.pi)^(R+2) := by positivity
    have hmono3 : ((Real.pi^2/16) * (Real.pi/2)) * (4/Real.pi)^(R+2)
        ≤ ((Real.pi^2/16) * (Real.pi/2)) * (4/Real.pi)^(R+2) * (Real.pi/2-θ)^(1-R) := by
      calc ((Real.pi^2/16) * (Real.pi/2)) * (4/Real.pi)^(R+2)
          = ((Real.pi^2/16) * (Real.pi/2)) * (4/Real.pi)^(R+2) * 1 := by ring
        _ ≤ ((Real.pi^2/16) * (Real.pi/2)) * (4/Real.pi)^(R+2) * (Real.pi/2-θ)^(1-R) :=
            mul_le_mul_of_nonneg_left hdel hc
    calc (Real.pi/4) * (4/Real.pi)^(R+2)
        ≤ ((Real.pi^2/16) * (Real.pi/2)) * (4/Real.pi)^(R+2) := hmono2
      _ ≤ ((Real.pi^2/16) * (Real.pi/2)) * (4/Real.pi)^(R+2) * (Real.pi/2-θ)^(1-R) := hmono3
      _ = (Real.pi^2/16) * (4/Real.pi)^(R+2) * (Real.pi/2) * (Real.pi/2-θ)^(1-R) := by ring
  calc (∫ s in (Real.pi/4)..θ, Work.Elliptic.sinCos2 s * s ^ (-(R+2)))
      ≤ (θ - Real.pi/4) * (4/Real.pi)^(R+2) := hmono
    _ ≤ (Real.pi/4) * (4/Real.pi)^(R+2) := hstep
    _ ≤ (Real.pi^2/16) * (4/Real.pi)^(R+2) * (Real.pi/2) * (Real.pi/2 - θ)^(1-R) := hbd

/-- `∫_{π/4}^{θ} sin s cos²s · (π/2 - s)^{-(R+2)} ds ≤ (1/(R-1)) (π/2-θ)^{1-R}`:
the weight `sin s cos²s ≤ (π/2-s)²` cancels the pole and the substitution `x = π/2 - s`
leaves the integrable `x^{-R}`. -/
theorem sinCos2_int_tsq_pow_right {R θ : ℝ} (hR : 1 < R)
    (hθ : θ ∈ Set.Ico (Real.pi/4) (Real.pi / 2)) :
    ∫ s in (Real.pi/4)..θ, Work.Elliptic.sinCos2 s * (Real.pi/2 - s) ^ (-(R+2))
      ≤ (1/(R-1)) * (Real.pi/2 - θ) ^ (1-R) := by
  have hπ : 0 < Real.pi := Real.pi_pos
  obtain ⟨hθ1, hθ2⟩ := hθ
  have hRpos : 0 < R := lt_trans zero_lt_one hR
  have hR1 : 0 < R - 1 := by linarith
  have hd0 : 0 < Real.pi/2 - θ := by linarith
  have hle : ∀ s ∈ Set.Icc (Real.pi/4) θ,
      Work.Elliptic.sinCos2 s * (Real.pi/2 - s) ^ (-(R+2)) ≤ (Real.pi/2 - s) ^ (-R) := by
    intro s hs
    have hs2 : s < Real.pi/2 := lt_of_le_of_lt hs.2 hθ2
    have hts : 0 < Real.pi/2 - s := by linarith
    have h1 : Work.Elliptic.sinCos2 s ≤ (Real.pi/2 - s)^2 := sinCos2_le_tsq s
    have h2 : 0 ≤ (Real.pi/2 - s) ^ (-(R+2)) := Real.rpow_nonneg hts.le _
    refine le_trans (mul_le_mul_of_nonneg_right h1 h2) (le_of_eq ?_)
    rw [← Real.rpow_natCast (Real.pi/2 - s) 2, ← Real.rpow_add hts]
    congr 1
    ring
  have hmem : ∀ s ∈ Set.uIcc (Real.pi/4) θ, 0 < Real.pi/2 - s := by
    intro s hs
    rw [Set.uIcc_of_le hθ1] at hs
    have : s < Real.pi/2 := lt_of_le_of_lt hs.2 hθ2
    linarith
  have hInt1 : IntervalIntegrable (fun s : ℝ => Work.Elliptic.sinCos2 s * (Real.pi/2 - s)^(-(R+2)))
      volume (Real.pi/4) θ := by
    apply ContinuousOn.intervalIntegrable
    refine (Work.FTS.EllipticEst.H2W.LzeroGrowth.continuous_sinCos2.continuousOn).mul ?_
    refine ContinuousOn.rpow_const (continuousOn_const.sub continuousOn_id) (fun s hs => Or.inl ?_)
    exact (hmem s hs).ne'
  have hInt2 : IntervalIntegrable (fun s : ℝ => (Real.pi/2 - s)^(-R)) volume (Real.pi/4) θ := by
    apply ContinuousOn.intervalIntegrable
    refine ContinuousOn.rpow_const (continuousOn_const.sub continuousOn_id) (fun s hs => Or.inl ?_)
    exact (hmem s hs).ne'
  have hmono := intervalIntegral.integral_mono_on hθ1 hInt1 hInt2 hle
  have hsubst : (∫ s in (Real.pi/4)..θ, (Real.pi/2 - s) ^ (-R))
      = ∫ x in (Real.pi/2 - θ)..(Real.pi/2 - Real.pi/4), x ^ (-R) :=
    intervalIntegral.integral_comp_sub_left (fun x : ℝ => x ^ (-R)) (Real.pi/2)
  have h0u : (0:ℝ) ∉ Set.uIcc (Real.pi/2 - θ) (Real.pi/4) := by
    intro h
    rw [Set.mem_uIcc] at h
    rcases h with h | h
    · linarith [h.1]
    · linarith [h.1, hπ]
  have hval : (∫ x in (Real.pi/2 - θ)..(Real.pi/2 - Real.pi/4), x ^ (-R))
      = ((Real.pi/4) ^ (1-R) - (Real.pi/2 - θ) ^ (1-R)) / (1-R) := by
    rw [show Real.pi/2 - Real.pi/4 = Real.pi/4 by ring]
    rw [integral_rpow (Or.inr ⟨by linarith, h0u⟩)]
    rw [show (-R + 1 : ℝ) = 1 - R by ring]
  have hfin : ((Real.pi/4)^(1-R) - (Real.pi/2 - θ)^(1-R))/(1-R)
      ≤ (1/(R-1)) * (Real.pi/2 - θ)^(1-R) := by
    have hA : ((Real.pi/4)^(1-R) - (Real.pi/2 - θ)^(1-R))/(1-R)
        = ((Real.pi/2 - θ)^(1-R) - (Real.pi/4)^(1-R))/(R-1) := by
      rw [show (1-R : ℝ) = -(R-1) by ring, div_neg]
      ring
    rw [hA]
    rw [div_le_iff₀ hR1]
    have hcancel : (1/(R-1)) * (Real.pi/2 - θ)^(1-R) * (R-1) = (Real.pi/2 - θ)^(1-R) := by
      field_simp
    rw [hcancel]
    have hP : 0 ≤ (Real.pi/4)^(1-R) := Real.rpow_nonneg (by positivity) _
    linarith
  rw [hsubst, hval] at hmono
  linarith

/-! ## The main bound -/

theorem sourceBounds {u g : ℝ → ℝ} {R C : ℝ} (hR : 1 < R) (hC : 0 < C)
    (hu : ContDiffOn ℝ 2 u (Set.Ioo 0 (Real.pi / 2)))
    (h : ∀ θ ∈ Set.Ioo (0:ℝ) (Real.pi / 2), Work.FTS.EllipticEst.Lzero1 u θ = g θ)
    (hb : ∀ θ ∈ Set.Ioo (0:ℝ) (Real.pi / 2),
      |g θ| ≤ C * (θ ^ (-(R + 2)) + (Real.pi / 2 - θ) ^ (-(R + 2)))) :
    (∀ θ ∈ Set.Ioc (0:ℝ) (Real.pi / 4),
        ∫ s in θ..(Real.pi / 4), Work.Elliptic.sinCos2 s * |Work.FTS.EllipticEst.Lzero1 u s|
          ≤ (C * (1 / R + (4 / Real.pi) ^ (R + 2) * (Real.pi / 4))) * θ ^ (-R))
    ∧ (∀ θ ∈ Set.Ico (Real.pi / 4) (Real.pi / 2),
        ∫ s in (Real.pi / 4)..θ, Work.Elliptic.sinCos2 s * |Work.FTS.EllipticEst.Lzero1 u s|
          ≤ (C * ((Real.pi ^ 2 / 16) * (4 / Real.pi) ^ (R + 2) * (Real.pi / 2) + 1 / (R - 1)))
              * (Real.pi / 2 - θ) ^ (1 - R)) := by
  have hπ : 0 < Real.pi := Real.pi_pos
  have hg : ContinuousOn g (Set.Ioo 0 (Real.pi/2)) := cont_g hu h
  -- the two summands of the right-hand side and their interval integrability
  have hIntA : ∀ {a b : ℝ}, Set.uIcc a b ⊆ Set.Ioi (0:ℝ) →
      IntervalIntegrable (fun s : ℝ => Work.Elliptic.sinCos2 s * s ^ (-(R+2))) volume a b := by
    intro a b hsub
    apply ContinuousOn.intervalIntegrable
    refine (Work.FTS.EllipticEst.H2W.LzeroGrowth.continuous_sinCos2.continuousOn).mul ?_
    exact ContinuousOn.rpow_const continuousOn_id (fun s hs => Or.inl (ne_of_gt (hsub hs)))
  have hIntB : ∀ {a b : ℝ}, Set.uIcc a b ⊆ Set.Ioo (0:ℝ) (Real.pi/2) →
      IntervalIntegrable (fun s : ℝ => Work.Elliptic.sinCos2 s * (Real.pi/2 - s) ^ (-(R+2)))
        volume a b := by
    intro a b hsub
    apply ContinuousOn.intervalIntegrable
    refine (Work.FTS.EllipticEst.H2W.LzeroGrowth.continuous_sinCos2.continuousOn).mul ?_
    refine ContinuousOn.rpow_const (continuousOn_const.sub continuousOn_id) (fun s hs => Or.inl ?_)
    have hsI := hsub hs
    exact (by linarith [hsI.2] : (0:ℝ) < Real.pi/2 - s).ne'
  constructor
  · intro θ hθ
    obtain ⟨hθ0, hθ4⟩ := hθ
    have hsub : Set.uIcc θ (Real.pi/4) ⊆ Set.Ioo 0 (Real.pi/2) := by
      rw [Set.uIcc_of_le hθ4]
      intro s hs
      exact ⟨by linarith [hs.1], by linarith [hπ, hs.2]⟩
    have hsub0 : Set.uIcc θ (Real.pi/4) ⊆ Set.Ioi (0:ℝ) := fun s hs => (hsub hs).1
    have hcongr : (∫ s in θ..(Real.pi/4),
          Work.Elliptic.sinCos2 s * |Work.FTS.EllipticEst.Lzero1 u s|)
        = ∫ s in θ..(Real.pi/4), Work.Elliptic.sinCos2 s * |g s| :=
      intervalIntegral.integral_congr (fun s hs => by rw [h s (hsub hs)])
    rw [hcongr]
    have hpt : ∀ s ∈ Set.Icc θ (Real.pi/4),
        Work.Elliptic.sinCos2 s * |g s| ≤ C * (Work.Elliptic.sinCos2 s * s ^ (-(R+2))
          + Work.Elliptic.sinCos2 s * (Real.pi/2 - s) ^ (-(R+2))) := by
      intro s hs
      have hs0 : 0 < s := lt_of_lt_of_le hθ0 hs.1
      have hsI : s ∈ Set.Ioo (0:ℝ) (Real.pi/2) := ⟨hs0, by linarith [hπ, hs.2]⟩
      have h2 := hb s hsI
      have h1 : 0 ≤ Work.Elliptic.sinCos2 s :=
        Work.FTS.EllipticEst.H2W.LzeroGrowth.sinCos2_nonneg_of_mem hsI
      calc Work.Elliptic.sinCos2 s * |g s|
          ≤ Work.Elliptic.sinCos2 s
              * (C * (s ^ (-(R+2)) + (Real.pi/2 - s) ^ (-(R+2)))) :=
            mul_le_mul_of_nonneg_left h2 h1
        _ = C * (Work.Elliptic.sinCos2 s * s ^ (-(R+2))
              + Work.Elliptic.sinCos2 s * (Real.pi/2 - s) ^ (-(R+2))) := by ring
    have hIntF : IntervalIntegrable (fun s : ℝ => Work.Elliptic.sinCos2 s * |g s|)
        volume θ (Real.pi/4) := by
      apply ContinuousOn.intervalIntegrable
      exact (Work.FTS.EllipticEst.H2W.LzeroGrowth.continuous_sinCos2.continuousOn).mul
        ((hg.mono hsub).abs)
    have hIntG : IntervalIntegrable (fun s : ℝ => C * (Work.Elliptic.sinCos2 s * s ^ (-(R+2))
        + Work.Elliptic.sinCos2 s * (Real.pi/2 - s) ^ (-(R+2)))) volume θ (Real.pi/4) :=
      ((hIntA hsub0).add (hIntB hsub)).const_mul C
    have hmono := intervalIntegral.integral_mono_on hθ4 hIntF hIntG hpt
    have hsplit : (∫ s in θ..(Real.pi/4), C * (Work.Elliptic.sinCos2 s * s ^ (-(R+2))
          + Work.Elliptic.sinCos2 s * (Real.pi/2 - s) ^ (-(R+2))))
        = C * ((∫ s in θ..(Real.pi/4), Work.Elliptic.sinCos2 s * s ^ (-(R+2)))
            + (∫ s in θ..(Real.pi/4), Work.Elliptic.sinCos2 s * (Real.pi/2 - s) ^ (-(R+2)))) := by
      rw [intervalIntegral.integral_const_mul, intervalIntegral.integral_add (hIntA hsub0) (hIntB hsub)]
    rw [hsplit] at hmono
    have hA := sinCos2_int_pow_left hR ⟨hθ0, hθ4⟩
    have hB := sinCos2_int_tsq_pow_left hR ⟨hθ0, hθ4⟩
    have hsum := add_le_add hA hB
    have hC1 : C * ((∫ s in θ..(Real.pi/4), Work.Elliptic.sinCos2 s * s ^ (-(R+2)))
        + (∫ s in θ..(Real.pi/4), Work.Elliptic.sinCos2 s * (Real.pi/2 - s) ^ (-(R+2))))
        ≤ C * (θ ^ (-R) / R + (4/Real.pi) ^ (R+2) * (Real.pi/4) * θ ^ (-R)) :=
      mul_le_mul_of_nonneg_left hsum hC.le
    have harith : C * (θ ^ (-R) / R + (4/Real.pi) ^ (R+2) * (Real.pi/4) * θ ^ (-R))
        = (C * (1 / R + (4 / Real.pi) ^ (R + 2) * (Real.pi / 4))) * θ ^ (-R) := by ring
    linarith
  · intro θ hθ
    obtain ⟨hθ1, hθ2⟩ := hθ
    have hsub : Set.uIcc (Real.pi/4) θ ⊆ Set.Ioo 0 (Real.pi/2) := by
      rw [Set.uIcc_of_le hθ1]
      intro s hs
      exact ⟨by linarith [hπ, hs.1], by linarith [hs.2, hθ2]⟩
    have hsub0 : Set.uIcc (Real.pi/4) θ ⊆ Set.Ioi (0:ℝ) := fun s hs => (hsub hs).1
    have hcongr : (∫ s in (Real.pi/4)..θ,
          Work.Elliptic.sinCos2 s * |Work.FTS.EllipticEst.Lzero1 u s|)
        = ∫ s in (Real.pi/4)..θ, Work.Elliptic.sinCos2 s * |g s| :=
      intervalIntegral.integral_congr (fun s hs => by rw [h s (hsub hs)])
    rw [hcongr]
    have hpt : ∀ s ∈ Set.Icc (Real.pi/4) θ,
        Work.Elliptic.sinCos2 s * |g s| ≤ C * (Work.Elliptic.sinCos2 s * s ^ (-(R+2))
          + Work.Elliptic.sinCos2 s * (Real.pi/2 - s) ^ (-(R+2))) := by
      intro s hs
      have hs0 : 0 < s := by linarith [hπ, hs.1]
      have hsI : s ∈ Set.Ioo (0:ℝ) (Real.pi/2) := ⟨hs0, lt_of_le_of_lt hs.2 hθ2⟩
      have h2 := hb s hsI
      have h1 : 0 ≤ Work.Elliptic.sinCos2 s :=
        Work.FTS.EllipticEst.H2W.LzeroGrowth.sinCos2_nonneg_of_mem hsI
      calc Work.Elliptic.sinCos2 s * |g s|
          ≤ Work.Elliptic.sinCos2 s
              * (C * (s ^ (-(R+2)) + (Real.pi/2 - s) ^ (-(R+2)))) :=
            mul_le_mul_of_nonneg_left h2 h1
        _ = C * (Work.Elliptic.sinCos2 s * s ^ (-(R+2))
              + Work.Elliptic.sinCos2 s * (Real.pi/2 - s) ^ (-(R+2))) := by ring
    have hIntF : IntervalIntegrable (fun s : ℝ => Work.Elliptic.sinCos2 s * |g s|)
        volume (Real.pi/4) θ := by
      apply ContinuousOn.intervalIntegrable
      exact (Work.FTS.EllipticEst.H2W.LzeroGrowth.continuous_sinCos2.continuousOn).mul
        ((hg.mono hsub).abs)
    have hIntG : IntervalIntegrable (fun s : ℝ => C * (Work.Elliptic.sinCos2 s * s ^ (-(R+2))
        + Work.Elliptic.sinCos2 s * (Real.pi/2 - s) ^ (-(R+2)))) volume (Real.pi/4) θ :=
      ((hIntA hsub0).add (hIntB hsub)).const_mul C
    have hmono := intervalIntegral.integral_mono_on hθ1 hIntF hIntG hpt
    have hsplit : (∫ s in (Real.pi/4)..θ, C * (Work.Elliptic.sinCos2 s * s ^ (-(R+2))
          + Work.Elliptic.sinCos2 s * (Real.pi/2 - s) ^ (-(R+2))))
        = C * ((∫ s in (Real.pi/4)..θ, Work.Elliptic.sinCos2 s * s ^ (-(R+2)))
            + (∫ s in (Real.pi/4)..θ, Work.Elliptic.sinCos2 s * (Real.pi/2 - s) ^ (-(R+2)))) := by
      rw [intervalIntegral.integral_const_mul, intervalIntegral.integral_add (hIntA hsub0) (hIntB hsub)]
    rw [hsplit] at hmono
    have hA := sinCos2_int_pow_right hR ⟨hθ1, hθ2⟩
    have hB := sinCos2_int_tsq_pow_right hR ⟨hθ1, hθ2⟩
    have hsum := add_le_add hA hB
    have hC1 : C * ((∫ s in (Real.pi/4)..θ, Work.Elliptic.sinCos2 s * s ^ (-(R+2)))
        + (∫ s in (Real.pi/4)..θ, Work.Elliptic.sinCos2 s * (Real.pi/2 - s) ^ (-(R+2))))
        ≤ C * ((Real.pi^2/16) * (4/Real.pi)^(R+2) * (Real.pi/2) * (Real.pi/2 - θ)^(1-R)
            + (1/(R-1)) * (Real.pi/2 - θ)^(1-R)) :=
      mul_le_mul_of_nonneg_left hsum hC.le
    have harith : C * ((Real.pi^2/16) * (4/Real.pi)^(R+2) * (Real.pi/2) * (Real.pi/2 - θ)^(1-R)
          + (1/(R-1)) * (Real.pi/2 - θ)^(1-R))
        = (C * ((Real.pi ^ 2 / 16) * (4 / Real.pi) ^ (R + 2) * (Real.pi / 2) + 1 / (R - 1)))
            * (Real.pi / 2 - θ) ^ (1 - R) := by ring
    linarith

end Work.FTS.EllipticEst.H2W.WeakPureAux
