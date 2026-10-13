/-
  Elementary tools for the Łojasiewicz-from-gradient-inequality development
  (`Work.WilE3.Loj.loj_of_gradient_bound`).

  Nothing here is specific to the Łojasiewicz statement; these are the small pieces of calculus
  and functional analysis the descent argument needs.
-/
import Mathlib

namespace Work.WilE3.Loj

set_option autoImplicit false
open Classical Topology Metric Filter
open scoped Topology

/-! ### An element of the dual of norm at least `ν`, pointing "down" -/

/-- In a proper normed space, if `ν ≤ ‖L‖` and `σ = ±1`, there is a vector `d` with `‖d‖ ≤ 1`
and `σ * (L d) ≤ -(1 - ε) * ν`.  (Take a maximiser `v` of `|L ·|` on the closed unit ball; then
`|L v| ≥ ‖L‖ ≥ ν`, and the sign is adjusted by multiplying by `±1`.) -/
theorem exists_mul_apply_le_neg {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    [ProperSpace E] {L : E →L[ℝ] ℝ} {ν ε σ : ℝ} (hε : 0 < ε) (hν : 0 < ν) (hL : ν ≤ ‖L‖)
    (hσ : σ = 1 ∨ σ = -1) : ∃ d : E, ‖d‖ ≤ 1 ∧ σ * (L d) ≤ -(1 - ε) * ν := by
  have hne : (Metric.closedBall (0 : E) 1).Nonempty := ⟨0, by simp⟩
  obtain ⟨v, hv, hvmax⟩ :=
    (isCompact_closedBall (0 : E) 1).exists_isMaxOn hne
      (continuous_abs.comp L.continuous).continuousOn
  have hvball : ‖v‖ ≤ 1 := by simpa [Metric.mem_closedBall, dist_eq_norm] using hv
  have hmax : ∀ y ∈ Metric.closedBall (0 : E) 1, |L y| ≤ |L v| := isMaxOn_iff.mp hvmax
  -- `‖L‖ ≤ |L v|`
  have hnorm_le : ‖L‖ ≤ |L v| := by
    refine ContinuousLinearMap.opNorm_le_bound L (abs_nonneg _) (fun x => ?_)
    rcases eq_or_ne x 0 with rfl | hx
    · simp
    · have hxpos : 0 < ‖x‖ := norm_pos_iff.mpr hx
      have hmem : ‖x‖⁻¹ • x ∈ Metric.closedBall (0 : E) 1 := by
        simp only [Metric.mem_closedBall, dist_eq_norm, sub_zero, norm_smul, Real.norm_eq_abs,
          abs_inv, abs_of_pos hxpos]
        rw [inv_mul_cancel₀ (ne_of_gt hxpos)]
      have h2 : |L (‖x‖⁻¹ • x)| ≤ |L v| := hmax _ hmem
      have h3 : L x = ‖x‖ * L (‖x‖⁻¹ • x) := by
        rw [map_smul, smul_eq_mul]
        field_simp
      calc ‖L x‖ = ‖x‖ * ‖L (‖x‖⁻¹ • x)‖ := by
            rw [h3, norm_mul, Real.norm_of_nonneg hxpos.le]
        _ = ‖x‖ * |L (‖x‖⁻¹ • x)| := by rw [Real.norm_eq_abs]
        _ ≤ ‖x‖ * |L v| := mul_le_mul_of_nonneg_left h2 hxpos.le
        _ = |L v| * ‖x‖ := by ring
  have hav : (1 - ε) * ν ≤ |L v| :=
    le_trans (mul_le_of_le_one_left hν.le (by linarith)) (le_trans hL hnorm_le)
  -- choose the sign so that `σ * L d = -|L v|`
  set e : E := if 0 < L v then v else -v with he
  have heval : L e = |L v| := by
    rw [he]
    by_cases h : 0 < L v
    · simp only [h, ite_true, abs_of_pos h]
    · have h' : L v ≤ 0 := le_of_not_gt h
      simp only [h, ite_false, map_neg]
      rw [abs_of_nonpos h']
  have he_norm : ‖e‖ = ‖v‖ := by
    rw [he]
    split_ifs with h <;> simp [norm_neg]
  refine ⟨-σ • e, ?_, ?_⟩
  · rw [norm_smul, he_norm, Real.norm_eq_abs]
    rcases hσ with rfl | rfl <;> simpa using hvball
  · have hkey : σ * (L (-σ • e)) = -|L v| := by
      rw [map_smul, smul_eq_mul, ← heval]
      rcases hσ with rfl | rfl <;> ring
    rw [hkey]
    linarith

/-! ### The derivative of `t ↦ |t| ^ r` away from `0` -/

/-- For `t ≠ 0`, the function `t ↦ |t| ^ r` has derivative `r * |t| ^ (r - 1) * sign t`. -/
theorem hasDerivAt_abs_rpow {r t : ℝ} (ht : t ≠ 0) :
    HasDerivAt (fun t : ℝ => |t| ^ r) (r * |t| ^ (r - 1) * (SignType.sign t : ℝ)) t := by
  rcases lt_or_gt_of_ne ht with hlt | hgt
  · -- `t < 0`: `|t| = -t` near `t`
    have hneg : (fun u : ℝ => |u| ^ r) =ᶠ[𝓝 t] (fun u : ℝ => (-u) ^ r) := by
      filter_upwards [Iio_mem_nhds hlt] with u hu
      rw [abs_of_neg hu]
    have hpt : (-t) ≠ 0 := by linarith
    have h1 : HasDerivAt (fun u : ℝ => (-u) ^ r) ((r * (-t) ^ (r - 1)) * (-1)) t :=
      (Real.hasDerivAt_rpow_const (Or.inl hpt)).comp t (hasDerivAt_neg' (x := t))
    have hs : (SignType.sign t : ℝ) = -1 := by
      have := sign_eq_neg_one_iff.mpr hlt
      simpa using congrArg (fun s : SignType => (s : ℝ)) this
    have h2 : (r * (-t) ^ (r - 1)) * (-1) = r * |t| ^ (r - 1) * (SignType.sign t : ℝ) := by
      rw [hs, abs_of_neg hlt]
    exact (h1.congr_deriv h2).congr_of_eventuallyEq hneg
  · -- `t > 0`: `|t| = t` near `t`
    have hpos : (fun u : ℝ => |u| ^ r) =ᶠ[𝓝 t] (fun u : ℝ => u ^ r) := by
      filter_upwards [Ioi_mem_nhds hgt] with u hu
      rw [abs_of_pos hu]
    have hs : (SignType.sign t : ℝ) = 1 := by
      have := sign_eq_one_iff.mpr hgt
      simpa using congrArg (fun s : SignType => (s : ℝ)) this
    have h2 : r * t ^ (r - 1) = r * |t| ^ (r - 1) * (SignType.sign t : ℝ) := by
      rw [hs, abs_of_pos hgt]
      ring
    have h1 : HasDerivAt (fun u : ℝ => u ^ r) (r * |t| ^ (r - 1) * (SignType.sign t : ℝ)) t :=
      (Real.hasDerivAt_rpow_const (x := t) (p := r) (Or.inl (ne_of_gt hgt))).congr_deriv h2
    exact h1.congr_of_eventuallyEq hpos

/-- `sign t = ±1` for `t ≠ 0`. -/
theorem sign_eq_one_or_neg_one {t : ℝ} (ht : t ≠ 0) :
    (SignType.sign t : ℝ) = 1 ∨ (SignType.sign t : ℝ) = -1 := by
  rcases lt_or_gt_of_ne ht with hlt | hgt
  · refine Or.inr ?_
    have := sign_eq_neg_one_iff.mpr hlt
    simpa using congrArg (fun s : SignType => (s : ℝ)) this
  · refine Or.inl ?_
    have := sign_eq_one_iff.mpr hgt
    simpa using congrArg (fun s : SignType => (s : ℝ)) this

/-! ### Fencing: a function with derivative at least `-K` drops at most linearly -/

/-- If `φ` is continuous on `[a,b]` (with `a ≤ b`) and has right derivative `≤ -K` there, then
`φ b - φ a ≤ -K * (b - a)`. -/
theorem sub_le_mul_of_hasDerivWithinAt_le {φ φ' : ℝ → ℝ} {a b K : ℝ} (hab : a ≤ b)
    (hcont : ContinuousOn φ (Set.Icc a b))
    (hder : ∀ s ∈ Set.Ico a b, HasDerivWithinAt φ (φ' s) (Set.Ici s) s)
    (hbound : ∀ s ∈ Set.Ico a b, φ' s ≤ -K) : φ b - φ a ≤ -K * (b - a) := by
  have hB : ContinuousOn (fun s : ℝ => φ a - K * (s - a)) (Set.Icc a b) := by fun_prop
  have hB' : ∀ s ∈ Set.Ico a b,
      HasDerivWithinAt (fun s : ℝ => φ a - K * (s - a)) (0 - K * 1) (Set.Ici s) s := by
    intro s _
    have hKm := HasDerivWithinAt.const_mul K ((hasDerivWithinAt_id s (Set.Ici s)).sub
        (hasDerivWithinAt_const (x := s) (s := Set.Ici s) (c := a)))
    have h2 := (hasDerivWithinAt_const (x := s) (s := Set.Ici s) (c := φ a)).sub hKm
    convert h2 using 1
    ext x
    simp only [Pi.sub_apply, id_eq]
    ring
  have h := image_le_of_deriv_right_le_deriv_boundary (B := fun s : ℝ => φ a - K * (s - a))
    (B' := fun _ => 0 - K * 1) hcont hder (by simp) hB hB' (by
      intro s hs
      have := hbound s hs
      linarith)
  have hb := h (Set.right_mem_Icc.mpr hab)
  linarith

end Work.WilE3.Loj
