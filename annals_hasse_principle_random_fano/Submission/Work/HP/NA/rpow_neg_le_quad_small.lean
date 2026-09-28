import Mathlib

/-!
# A quadratic lower bound for `x ↦ x ^ (-κ)` on `[1/2, ∞)`

For `0 < κ ≤ 1/12` and `x ≥ 1/2` we prove
`x ^ (-κ) ≤ 1 - κ * (x - 1) + (x - 1) ^ 2`.

The auxiliary function `φ(y) = 1 - κ * (y - 1) + (y - 1) ^ 2 - y ^ (-κ)` is convex on
`[1/2, ∞)` (its second derivative is `2 - κ * (κ + 1) * y ^ (-κ - 2) ≥ 0` there) and has
`φ 1 = 0` and `φ' 1 = 0`, so its minimum over `[1/2, ∞)` is attained at `1`.  Convexity is
established from the second derivative via `convexOn_of_hasDerivWithinAt2_nonneg`, and the
minimum at `1` from the secant-slope bounds `ConvexOn.le_slope_of_hasDerivAt` /
`ConvexOn.slope_le_of_hasDerivAt`.
-/

namespace Work.HP.NA

/-- The auxiliary function `φ(y) = 1 - κ * (y - 1) + (y - 1) ^ 2 - y ^ (-κ)`. -/
noncomputable def phi (κ : ℝ) : ℝ → ℝ := fun x => 1 - κ * (x - 1) + (x - 1) ^ 2 - x ^ (-κ)

theorem phi_eq (κ : ℝ) :
    phi κ = fun x : ℝ => 1 - κ * (x - 1) + (x - 1) ^ 2 - x ^ (-κ) := rfl

/-- First derivative of `φ` at a positive point. -/
theorem hasDerivAt_phi (κ x : ℝ) (hx : 0 < x) :
    HasDerivAt (phi κ) (-κ + 2 * (x - 1) + κ * x ^ (-κ - 1)) x := by
  rw [phi_eq]
  have h1 : HasDerivAt (fun x : ℝ => (1 : ℝ)) 0 x := hasDerivAt_const x 1
  have h2 : HasDerivAt (fun x : ℝ => κ * (x - 1)) κ x := by
    simpa using ((hasDerivAt_id x).sub_const 1).const_mul κ
  have h3 : HasDerivAt (fun x : ℝ => (x - 1) ^ 2) (2 * (x - 1)) x := by
    have hh : HasDerivAt (fun x : ℝ => (x - 1) * (x - 1)) (1 * (x - 1) + (x - 1) * 1) x :=
      ((hasDerivAt_id x).sub_const 1).mul ((hasDerivAt_id x).sub_const 1)
    convert hh using 1 <;> ring_nf
  have h4 : HasDerivAt (fun x : ℝ => x ^ (-κ)) ((-κ) * x ^ (-κ - 1)) x :=
    Real.hasDerivAt_rpow_const (Or.inl (ne_of_gt hx))
  have H : HasDerivAt (fun x : ℝ => 1 - κ * (x - 1) + (x - 1) ^ 2 - x ^ (-κ))
      ((0 - κ + 2 * (x - 1)) - ((-κ) * x ^ (-κ - 1))) x := ((h1.sub h2).add h3).sub h4
  convert H using 1
  ring_nf

/-- Second derivative of `φ` at a positive point. -/
theorem hasDerivAt_phi' (κ x : ℝ) (hx : 0 < x) :
    HasDerivAt (fun x : ℝ => -κ + 2 * (x - 1) + κ * x ^ (-κ - 1))
      (2 - κ * (κ + 1) * x ^ (-κ - 2)) x := by
  have h1 : HasDerivAt (fun x : ℝ => (-κ : ℝ)) 0 x := hasDerivAt_const x (-κ)
  have h2 : HasDerivAt (fun x : ℝ => 2 * (x - 1)) 2 x := by
    simpa using ((hasDerivAt_id x).sub_const 1).const_mul 2
  have h4 : HasDerivAt (fun x : ℝ => x ^ (-κ - 1)) ((-κ - 1) * x ^ (-κ - 1 - 1)) x :=
    Real.hasDerivAt_rpow_const (Or.inl (ne_of_gt hx))
  have h5 : HasDerivAt (fun x : ℝ => κ * x ^ (-κ - 1)) (κ * ((-κ - 1) * x ^ (-κ - 1 - 1))) x :=
    h4.const_mul κ
  have H : HasDerivAt (fun x : ℝ => -κ + 2 * (x - 1) + κ * x ^ (-κ - 1))
      ((0 + 2) + κ * ((-κ - 1) * x ^ (-κ - 1 - 1))) x := (h1.add h2).add h5
  convert H using 1
  ring_nf

/-- `φ` is continuous on `[1/2, ∞)`. -/
theorem continuousOn_phi (κ : ℝ) : ContinuousOn (phi κ) (Set.Ici (1/2)) := by
  rw [phi_eq]
  have hpoly : ContinuousOn (fun x : ℝ => 1 - κ * (x - 1) + (x - 1) ^ 2) (Set.Ici (1/2)) := by
    fun_prop
  have hrpow : ContinuousOn (fun x : ℝ => x ^ (-κ)) (Set.Ici (1/2)) := by
    refine ContinuousOn.rpow_const (f := fun x : ℝ => x) continuousOn_id ?_
    intro x hx
    left
    have : (1 : ℝ) / 2 ≤ x := hx
    linarith
  exact hpoly.sub hrpow

/-- The second derivative of `φ` is nonnegative on `[1/2, ∞)` (for `0 < κ ≤ 1/12`). -/
theorem rpow_d2_nonneg (κ x : ℝ) (hκ0 : 0 < κ) (hκ : κ ≤ 1/12) (hx : 1/2 ≤ x) :
    0 ≤ 2 - κ * (κ + 1) * x ^ (-κ - 2) := by
  have hxpos : 0 < x := by linarith
  have hmul : κ * (κ + 1) ≤ (1/6 : ℝ) := by
    have h := mul_le_mul hκ (by linarith : κ + 1 ≤ (2:ℝ)) (by linarith : (0:ℝ) ≤ κ + 1)
      (by norm_num : (0:ℝ) ≤ 1/12)
    exact h.trans (by norm_num : (1/12 : ℝ) * 2 ≤ 1/6)
  have hinv : x ^ (-κ - 2) = x⁻¹ ^ (κ + 2) := by
    rw [show (-κ - 2 : ℝ) = -(κ + 2) by ring, Real.rpow_neg (le_of_lt hxpos) (κ + 2)]
    exact (Real.inv_rpow (le_of_lt hxpos) (κ + 2)).symm
  have hxinv : x⁻¹ ≤ 2 := by
    rw [inv_le_iff_one_le_mul₀ hxpos]
    nlinarith
  have h8 : x ^ (-κ - 2) ≤ 8 := by
    rw [hinv]
    calc x⁻¹ ^ (κ + 2) ≤ (2:ℝ) ^ (κ + 2) :=
          Real.rpow_le_rpow (inv_nonneg.mpr (le_of_lt hxpos)) hxinv (by linarith)
      _ ≤ 8 := by
          have h : (2:ℝ) ^ (κ + 2) ≤ (2:ℝ) ^ (3:ℝ) :=
            Real.rpow_le_rpow_of_exponent_le (by norm_num) (by linarith)
          have h2 : (2:ℝ) ^ (3:ℝ) = 8 := by norm_num
          linarith
  have hprod : κ * (κ + 1) * x ^ (-κ - 2) ≤ 2 := by
    have hle : κ * (κ + 1) * x ^ (-κ - 2) ≤ (1/6 : ℝ) * 8 :=
      mul_le_mul hmul h8 (Real.rpow_nonneg (le_of_lt hxpos) _) (by norm_num)
    exact hle.trans (by norm_num : (1/6 : ℝ) * 8 ≤ 2)
  linarith

/-- `slope f x y ≤ 0` with `x < y` gives `f y ≤ f x`. -/
theorem of_slope_nonpos {f : ℝ → ℝ} {x y : ℝ} (hxy : x < y) (h : slope f x y ≤ 0) :
    f y ≤ f x := by
  rw [slope_def_field] at h
  have hyx : (0:ℝ) < y - x := by linarith
  have hmul := mul_le_mul_of_nonneg_right h hyx.le
  rw [div_mul_cancel₀ _ hyx.ne', zero_mul] at hmul
  linarith

/-- `0 ≤ slope f x y` with `x < y` gives `f x ≤ f y`. -/
theorem of_slope_nonneg {f : ℝ → ℝ} {x y : ℝ} (hxy : x < y) (h : 0 ≤ slope f x y) :
    f x ≤ f y := by
  rw [slope_def_field] at h
  have hyx : (0:ℝ) < y - x := by linarith
  have hmul := mul_le_mul_of_nonneg_right h hyx.le
  rw [div_mul_cancel₀ _ hyx.ne', zero_mul] at hmul
  linarith

theorem rpow_neg_le_quad_small (κ x : ℝ) (hκ0 : 0 < κ) (hκ : κ ≤ 1/12) (hx : 1/2 ≤ x) :
    x ^ (-κ) ≤ 1 - κ * (x - 1) + (x - 1) ^ 2 := by
  have hconv : ConvexOn ℝ (Set.Ici (1/2)) (phi κ) := by
    refine convexOn_of_hasDerivWithinAt2_nonneg (D := Set.Ici (1/2)) (f := phi κ)
      (f' := fun x : ℝ => -κ + 2 * (x - 1) + κ * x ^ (-κ - 1))
      (f'' := fun x : ℝ => 2 - κ * (κ + 1) * x ^ (-κ - 2))
      (convex_Ici (1/2)) (continuousOn_phi κ) ?_ ?_ ?_
    · intro y hy
      rw [interior_Ici] at hy ⊢
      have hy' : (1:ℝ)/2 < y := hy
      exact (hasDerivAt_phi κ y (by linarith)).hasDerivWithinAt
    · intro y hy
      rw [interior_Ici] at hy ⊢
      have hy' : (1:ℝ)/2 < y := hy
      exact (hasDerivAt_phi' κ y (by linarith)).hasDerivWithinAt
    · intro y hy
      rw [interior_Ici] at hy
      exact rpow_d2_nonneg κ y hκ0 hκ (le_of_lt hy)
  have hderiv1 : (-κ + 2 * ((1:ℝ) - 1) + κ * (1:ℝ) ^ (-κ - 1)) = 0 := by
    have h1 : (1:ℝ) ^ (-κ - 1) = 1 := by simp
    rw [h1]; ring
  have hphi1 : phi κ 1 = 0 := by
    have h1 : (1:ℝ) ^ (-κ) = 1 := by simp
    rw [phi_eq]
    simp only [h1]
    ring
  have hmem1 : (1:ℝ) ∈ Set.Ici (1/2) := by norm_num
  have hmemx : x ∈ Set.Ici (1/2) := hx
  have key : 0 ≤ 1 - κ * (x - 1) + (x - 1) ^ 2 - x ^ (-κ) := by
    rcases lt_trichotomy x 1 with hlt | heq | hgt
    · have hsl := ConvexOn.slope_le_of_hasDerivAt hconv hmemx hmem1 hlt
          (hasDerivAt_phi κ 1 (by norm_num))
      rw [hderiv1] at hsl
      have hle := of_slope_nonpos hlt hsl
      have h2 : 0 ≤ phi κ x := by rw [hphi1] at hle; linarith
      exact h2
    · rw [heq]; simp
    · have hsl := ConvexOn.le_slope_of_hasDerivAt hconv hmem1 hmemx hgt
          (hasDerivAt_phi κ 1 (by norm_num))
      rw [hderiv1] at hsl
      have hle := of_slope_nonneg hgt hsl
      have h2 : 0 ≤ phi κ x := by rw [hphi1] at hle; linarith
      exact h2
  linarith

end Work.HP.NA
