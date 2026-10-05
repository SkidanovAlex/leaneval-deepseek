import Mathlib
import Submission.Work.RPB.B1a.HalfBallRegion
import Submission.Work.RPB.B1a.abs_le_sq_of_hasDerivAt
import Submission.Work.RPB.B1a.abs_mul_sub_le_of
import Submission.Work.RPB.B1a.nocap_of_sq_bounds

namespace Work.RPB.B1a

/-- The numerical core of the sign analysis: under `M r ≤ 1/8`, `|x| ≤ 2 r`, `y ≤ r`,
the quantity `2 M |x| + M y + 2 M^2 x^2` is strictly below `1`. -/
lemma two_Mabsx_add_My_add_sq_lt_one {M r x y : ℝ} (hM : 0 ≤ M) (hr : 0 < r)
    (hMr : M * r ≤ 1 / 8) (hx : |x| ≤ 2 * r) (hy : y ≤ r) :
    2 * M * |x| + M * y + 2 * M ^ 2 * x ^ 2 < 1 := by
  have hMr0 : 0 ≤ M * r := mul_nonneg hM (le_of_lt hr)
  have hMr2 : (M * r) ^ 2 ≤ (1 / 8) ^ 2 := by
    rw [pow_two, pow_two]; exact mul_self_le_mul_self hMr0 hMr
  have hx2 : x ^ 2 ≤ (2 * r) ^ 2 := by
    have h := mul_self_le_mul_self (abs_nonneg x) hx
    simpa [pow_two, sq_abs] using h
  nlinarith [hMr, hMr0, hx2, hMr2, hM, hr, hy, hx, abs_nonneg x, sq_nonneg x]

/-- Derivative sign on the right of `0`: with the integrated bounds
`|P x| ≤ M x^2`, `|Q x - σ x| ≤ M x^2`, `|P' x| ≤ M |x|`, `|Q' x - σ| ≤ M |x|`, and
`y > 0`, `|x| ≤ 2 r`, `0 ≤ x`, the derivative `-2 (y - P x) P' x + 2 Q x Q' x` of
`x ↦ (y - P x)^2 + (Q x)^2` is nonnegative. -/
lemma deriv_nonneg_of_bounds {P Q P' Q' : ℝ → ℝ} {σ M r y x : ℝ}
    (hM : 0 ≤ M) (hr : 0 < r) (hMr : M * r ≤ 1 / 8) (hσ : σ = 1 ∨ σ = -1)
    (hy0 : 0 ≤ y) (hyr : y ≤ r) (hx0 : 0 ≤ x) (hx : |x| ≤ 2 * r)
    (hPx : |P x| ≤ M * x ^ 2) (hQx : |Q x - σ * x| ≤ M * x ^ 2)
    (hPdx : |P' x| ≤ M * |x|) (hQdx : |Q' x - σ| ≤ M * |x|) :
    0 ≤ -(2 * (y - P x) * (P' x)) + 2 * (Q x) * (Q' x) := by
  have hkey := abs_mul_sub_le_of hσ hQx hQdx
  have hQl : x - (2 * M * x ^ 2 + M ^ 2 * |x| ^ 3) ≤ Q x * Q' x := by
    have h := (abs_le.mp hkey).1; linarith
  have hPxb := abs_le.mp hPx
  have hPy : |y - P x| ≤ y + M * x ^ 2 := by
    rw [abs_le]; constructor <;> nlinarith [hPxb, hy0, hM, sq_nonneg x]
  have hb0 : 0 ≤ y + M * x ^ 2 := by nlinarith [hy0, hM, sq_nonneg x]
  have habs : |(y - P x) * (P' x)| ≤ (y + M * x ^ 2) * (M * |x|) := by
    rw [abs_mul]
    exact mul_le_mul hPy hPdx (abs_nonneg (P' x)) hb0
  have hPl : (y - P x) * (P' x) ≤ (y + M * x ^ 2) * (M * |x|) :=
    le_trans (le_abs_self _) habs
  have hnum := two_Mabsx_add_My_add_sq_lt_one hM hr hMr hx hyr
  have hxabs : |x| = x := abs_of_nonneg hx0
  rw [hxabs] at hQl hPl hnum
  have hkey2 : 2 * x * (2 * M * x + M * y + 2 * M ^ 2 * x ^ 2) ≤ 2 * x := by
    have := mul_le_mul_of_nonneg_left (le_of_lt hnum) (by linarith : (0 : ℝ) ≤ 2 * x)
    simpa using this
  nlinarith [hkey2, hQl, hPl]

/-- Derivative sign on the left of `0`: same bounds, but now `x ≤ 0`, and the derivative
is nonpositive. -/
lemma deriv_nonpos_of_bounds {P Q P' Q' : ℝ → ℝ} {σ M r y x : ℝ}
    (hM : 0 ≤ M) (hr : 0 < r) (hMr : M * r ≤ 1 / 8) (hσ : σ = 1 ∨ σ = -1)
    (hy0 : 0 ≤ y) (hyr : y ≤ r) (hx0 : x ≤ 0) (hx : |x| ≤ 2 * r)
    (hPx : |P x| ≤ M * x ^ 2) (hQx : |Q x - σ * x| ≤ M * x ^ 2)
    (hPdx : |P' x| ≤ M * |x|) (hQdx : |Q' x - σ| ≤ M * |x|) :
    -(2 * (y - P x) * (P' x)) + 2 * (Q x) * (Q' x) ≤ 0 := by
  have hkey := abs_mul_sub_le_of hσ hQx hQdx
  have hQu : Q x * Q' x ≤ x + (2 * M * x ^ 2 + M ^ 2 * |x| ^ 3) := by
    have h := (abs_le.mp hkey).2; linarith
  have hPxb := abs_le.mp hPx
  have hPy : |y - P x| ≤ y + M * x ^ 2 := by
    rw [abs_le]; constructor <;> nlinarith [hPxb, hy0, hM, sq_nonneg x]
  have hb0 : 0 ≤ y + M * x ^ 2 := by nlinarith [hy0, hM, sq_nonneg x]
  have habs : |(y - P x) * (P' x)| ≤ (y + M * x ^ 2) * (M * |x|) := by
    rw [abs_mul]
    exact mul_le_mul hPy hPdx (abs_nonneg (P' x)) hb0
  have hPu : -((y - P x) * (P' x)) ≤ (y + M * x ^ 2) * (M * |x|) :=
    le_trans (neg_le_abs _) habs
  have hnum := two_Mabsx_add_My_add_sq_lt_one hM hr hMr hx hyr
  have hxabs : |x| = -x := abs_of_nonpos hx0
  rw [hxabs] at hQu hPu hnum
  have h2 : (0 : ℝ) ≤ 2 * (-x) := by linarith
  have hkey2 : 2 * (-x) * (2 * M * (-x) + M * y + 2 * M ^ 2 * x ^ 2) ≤ 2 * (-x) := by
    have := mul_le_mul_of_nonneg_left (le_of_lt hnum) h2
    simpa using this
  ring_nf at hkey2 hQu hPu ⊢
  nlinarith [hkey2, hQu, hPu]

theorem mono_and_nocap_of_bounds (P Q P' Q' : ℝ → ℝ) {σ M r : ℝ}
    (hr : 0 < r) (hM : 0 ≤ M) (hMr : M * r ≤ 1 / 8) (hσ : σ = 1 ∨ σ = -1)
    (hP0 : P 0 = 0) (hQ0 : Q 0 = 0)
    (hPd : ∀ x, |x| ≤ 2 * r → HasDerivAt P (P' x) x)
    (hQd : ∀ x, |x| ≤ 2 * r → HasDerivAt Q (Q' x) x)
    (hPb : ∀ x, |x| ≤ 2 * r → |P' x| ≤ M * |x|)
    (hQb : ∀ x, |x| ≤ 2 * r → |Q' x - σ| ≤ M * |x|) :
    (∀ y ∈ Set.Ioo 0 r,
      MonotoneOn (fun x => (y - P x) ^ 2 + (Q x) ^ 2) (Set.Icc 0 (2 * r)) ∧
      AntitoneOn (fun x => (y - P x) ^ 2 + (Q x) ^ 2) (Set.Icc (-2 * r) 0)) ∧
    (∀ x, |x| ≤ 2 * r → |Q x| < r → P x + Real.sqrt (r ^ 2 - (Q x) ^ 2) ≤ r) := by
  -- Integrated bounds `|P x| ≤ M x^2` and `|Q x - σ x| ≤ M x^2` for `|x| ≤ 2 r`.
  have hPx : ∀ x, |x| ≤ 2 * r → |P x| ≤ M * x ^ 2 := by
    intro x hx
    exact abs_le_sq_of_hasDerivAt hM hP0 (fun t ht => hPd t ht) (fun t ht => hPb t ht) hx
  have hQx : ∀ x, |x| ≤ 2 * r → |Q x - σ * x| ≤ M * x ^ 2 := by
    intro x hx
    have h0 : (fun t => Q t - σ * t) 0 = 0 := by simp [hQ0]
    have hd : ∀ t, |t| ≤ 2 * r → HasDerivAt (fun t => Q t - σ * t) (Q' t - σ) t := by
      intro t ht
      have hlin : HasDerivAt (fun t => σ * t) σ t := by
        simpa using (hasDerivAt_id t).const_mul σ
      exact (hQd t ht).sub hlin
    exact abs_le_sq_of_hasDerivAt hM h0 hd (fun t ht => hQb t ht) hx
  constructor
  · intro y hy
    have hy0 : 0 < y := hy.1
    have hyr : y < r := hy.2
    -- Derivative of `x ↦ (y - P x)^2 + (Q x)^2` on `|x| ≤ 2 r`.
    have hdf : ∀ x, |x| ≤ 2 * r →
        HasDerivAt (fun z => (y - P z) ^ 2 + (Q z) ^ 2)
          (-(2 * (y - P x) * (P' x)) + 2 * (Q x) * (Q' x)) x := by
      intro x hx
      have h1 : HasDerivAt (fun z => y - P z) (-(P' x)) x := by
        simpa using (hPd x hx).const_sub y
      have h2 : HasDerivAt ((fun z => y - P z) ^ 2) (2 * (y - P x) ^ (2 - 1) * (-(P' x))) x :=
        h1.pow 2
      have h3 : HasDerivAt ((fun z => Q z) ^ 2) (2 * (Q x) ^ (2 - 1) * (Q' x)) x :=
        (hQd x hx).pow 2
      have h4 := h2.add h3
      convert h4 using 1
      ring
    constructor
    · apply monotoneOn_of_deriv_nonneg (f := fun z => (y - P z) ^ 2 + (Q z) ^ 2)
        (convex_Icc (0 : ℝ) (2 * r))
      · intro x hx
        have hx' : |x| ≤ 2 * r := by rw [abs_of_nonneg hx.1]; exact hx.2
        exact (hdf x hx').continuousAt.continuousWithinAt
      · intro x hx
        have hxI : x ∈ Set.Icc (0 : ℝ) (2 * r) := interior_subset hx
        have hx' : |x| ≤ 2 * r := by rw [abs_of_nonneg hxI.1]; exact hxI.2
        exact (hdf x hx').differentiableAt.differentiableWithinAt
      · intro x hx
        have hxI : x ∈ Set.Icc (0 : ℝ) (2 * r) := interior_subset hx
        have hx' : |x| ≤ 2 * r := by rw [abs_of_nonneg hxI.1]; exact hxI.2
        rw [(hdf x hx').deriv]
        exact deriv_nonneg_of_bounds hM hr hMr hσ (le_of_lt hy0) (le_of_lt hyr) hxI.1 hx'
          (hPx x hx') (hQx x hx') (hPb x hx') (hQb x hx')
    · apply antitoneOn_of_deriv_nonpos (f := fun z => (y - P z) ^ 2 + (Q z) ^ 2)
        (convex_Icc (-2 * r) 0)
      · intro x hx
        have hx' : |x| ≤ 2 * r := by rw [abs_of_nonpos hx.2]; linarith [hx.1, hr]
        exact (hdf x hx').continuousAt.continuousWithinAt
      · intro x hx
        have hxI : x ∈ Set.Icc (-2 * r) 0 := interior_subset hx
        have hx' : |x| ≤ 2 * r := by rw [abs_of_nonpos hxI.2]; linarith [hxI.1, hr]
        exact (hdf x hx').differentiableAt.differentiableWithinAt
      · intro x hx
        have hxI : x ∈ Set.Icc (-2 * r) 0 := interior_subset hx
        have hx' : |x| ≤ 2 * r := by rw [abs_of_nonpos hxI.2]; linarith [hxI.1, hr]
        rw [(hdf x hx').deriv]
        exact deriv_nonpos_of_bounds hM hr hMr hσ (le_of_lt hy0) (le_of_lt hyr) hxI.2 hx'
          (hPx x hx') (hQx x hx') (hPb x hx') (hQb x hx')
  · intro x hx hQ
    exact nocap_of_sq_bounds P Q hr hM hMr hσ hPx hQx x hx hQ

end Work.RPB.B1a
