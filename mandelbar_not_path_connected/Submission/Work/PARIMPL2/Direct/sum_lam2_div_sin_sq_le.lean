import Mathlib
import Submission.Work.PARIMPL2.Direct.sum_inv_sq_le_of_sep
import Submission.Work.PARIMPL2.Direct.sumInvSqLe
import Submission.Work.PARIMPL2.Direct.one_term_le

-- Lean v4.35.0-rc3 / Mathlib 5e0c4e5 made `isDefEq` respect transparency when unifying instances; with it,
-- `ZMod.instField` and `ZMod.commRing` (and `Neg (ZMod p)` via `SubtractionMonoid`) no longer unify, which
-- breaks `ring`/`rw`/module-instance search on `ZMod p`. Restore the v4.34 behaviour for this file.
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false


namespace Work.PARIMPL2.Direct

/-!
# Sum of `λ² / sin²(λ x_j)` along a `1/3`-separated sequence

Let `λ > 0`, `R ≥ 128` with `λ R² ≤ 1`, and let `x_j = Re u_j` be a sequence of real
parts which stays in the window `[R/4 + 2, π/λ - R/4]` and decreases by at least `1/3`
at each step.  Then

`∑_{j<n} λ² / sin²(λ x_j) ≤ 24/R`.

The proof has three elementary ingredients.

* **One term.**  For `0 < t < π` the classical bound
  `1/sin² t ≤ 1/t² + 1/(π-t)² + 1` (from `u ≤ tan u` on `[0, π/2]`) gives
  `λ²/sin²(λ x) ≤ 1/x² + 1/(π/λ - x)² + λ²`.
* **The `1/x²` sum.**  The `x_j` are `1/3`-separated and bounded below by `R/4+2`, so
  telescoping gives `∑_{j<n} 1/x_j² ≤ 3/(R/4+2) = 12/(R+8)`.
* **The `1/(π/λ - x)²` sum.**  Dually, `d_j = π/λ - x_j ≥ R/4 + j/3`, so
  `∑_{j<n} 1/d_j² ≤ 16/R² + 12/R`.
* Finally `n λ² ≤ 3π/R²`, because the `1/3`-decrease forces `n/3 ≤ π/λ - R/2 - 2 ≤ π/λ`
  while `λ ≤ 1/R²`.

Adding up, `12/(R+8) + 16/R² + 12/R + 3π/R² ≤ 24/R` for `R ≥ 128`.
-/

/-- `1/sin² u ≤ 1 + 1/u²` for `0 < u ≤ π/2`, from `tan u ≥ u` (equivalently `sin u ≥ u cos u`). -/
private lemma inv_sin_sq_le_one_add (u : ℝ) (hu0 : 0 < u) (hu : u ≤ Real.pi / 2) :
    1 / (Real.sin u) ^ 2 ≤ 1 + 1 / u ^ 2 := by
  have hsin_pos : 0 < Real.sin u := Real.sin_pos_of_pos_of_lt_pi hu0 (by linarith [hu, Real.pi_pos])
  have hcos_nn : 0 ≤ Real.cos u := Real.cos_nonneg_of_mem_Icc ⟨by linarith [Real.pi_pos], hu⟩
  have hkey : u * Real.cos u ≤ Real.sin u := by
    rcases lt_or_eq_of_le hu with hlt | heq
    · have htan : u ≤ Real.tan u := Real.le_tan (le_of_lt hu0) hlt
      rw [Real.tan_eq_sin_div_cos] at htan
      rw [le_div_iff₀ (Real.cos_pos_of_mem_Ioo ⟨by linarith [Real.pi_pos], hlt⟩)] at htan
      linarith
    · rw [heq, Real.cos_pi_div_two, mul_zero, Real.sin_pi_div_two]
      norm_num
  have hsquare : (u * Real.cos u) ^ 2 ≤ (Real.sin u) ^ 2 := by
    have h1 : 0 ≤ u * Real.cos u := mul_nonneg hu0.le hcos_nn
    have h2 := mul_self_le_mul_self h1 hkey
    simpa [sq] using h2
  have hcs := Real.sin_sq_add_cos_sq u
  have hsq : u ^ 2 ≤ (Real.sin u) ^ 2 * (u ^ 2 + 1) := by nlinarith [hsquare, hcs]
  rw [div_le_iff₀ (pow_pos hsin_pos 2)]
  have h1 : (1 + 1 / u ^ 2) * (Real.sin u) ^ 2 = ((u ^ 2 + 1) * (Real.sin u) ^ 2) / u ^ 2 := by
    field_simp
  rw [h1, le_div_iff₀ (by positivity : (0:ℝ) < u ^ 2)]
  linarith [hsq]

/-- `1/sin² t ≤ 1/t² + 1/(π-t)² + 1` for `0 < t < π`. -/
private lemma inv_sin_sq_le (t : ℝ) (ht0 : 0 < t) (ht : t < Real.pi) :
    1 / (Real.sin t) ^ 2 ≤ 1 / t ^ 2 + 1 / (Real.pi - t) ^ 2 + 1 := by
  by_cases hle : t ≤ Real.pi / 2
  · have h1 := inv_sin_sq_le_one_add t ht0 hle
    have h2 : 0 ≤ 1 / (Real.pi - t) ^ 2 := by positivity
    linarith
  · push Not at hle
    have hpos : 0 < Real.pi - t := by linarith
    have hle' : Real.pi - t ≤ Real.pi / 2 := by linarith
    have h1 := inv_sin_sq_le_one_add (Real.pi - t) hpos hle'
    rw [Real.sin_pi_sub t] at h1
    have h2 : 0 ≤ 1 / t ^ 2 := by positivity
    linarith

/-- One term of the sum: `λ²/sin²(λx) ≤ 1/x² + 1/(π/λ-x)² + λ²` in the window. -/
private lemma one_term_sin (lam R x : ℝ) (hlam : 0 < lam) (hR : 128 ≤ R)
    (hx1 : R / 4 + 2 ≤ x) (hx2 : x ≤ Real.pi / lam - R / 4) :
    lam ^ 2 / (Real.sin (lam * x)) ^ 2 ≤ 1 / x ^ 2 + 1 / (Real.pi / lam - x) ^ 2 + lam ^ 2 := by
  have hxpos : 0 < x := by linarith
  have ht0 : 0 < lam * x := mul_pos hlam hxpos
  have htpi : lam * x < Real.pi := by
    have h1 : lam * x ≤ lam * (Real.pi / lam - R / 4) := mul_le_mul_of_nonneg_left hx2 hlam.le
    have h1' : lam * (Real.pi / lam - R / 4) = Real.pi - lam * (R / 4) := by field_simp
    rw [h1'] at h1
    have h2 : 0 < lam * (R / 4) := by positivity
    linarith
  have hpd : 0 < Real.pi / lam - x := by
    have h2 : 0 < R / 4 := by linarith
    linarith [hx2]
  have hkey := inv_sin_sq_le (lam * x) ht0 htpi
  have hsin_ne : Real.sin (lam * x) ≠ 0 := ne_of_gt (Real.sin_pos_of_pos_of_lt_pi ht0 htpi)
  have hlx_ne : lam * x ≠ 0 := ne_of_gt ht0
  have hmul : lam ^ 2 * (1 / (Real.sin (lam * x)) ^ 2) ≤
      lam ^ 2 * (1 / (lam * x) ^ 2 + 1 / (Real.pi - lam * x) ^ 2 + 1) :=
    mul_le_mul_of_nonneg_left hkey (by positivity)
  have e0 : lam ^ 2 / (Real.sin (lam * x)) ^ 2
      = lam ^ 2 * (1 / (Real.sin (lam * x)) ^ 2) := by rw [mul_one_div]
  rw [e0]
  refine le_trans hmul ?_
  have e1 : lam ^ 2 * (1 / (lam * x) ^ 2) = 1 / x ^ 2 := by
    rw [mul_one_div, div_eq_div_iff (pow_ne_zero 2 hlx_ne) (pow_ne_zero 2 (ne_of_gt hxpos))]
    ring
  have e2 : lam ^ 2 * (1 / (Real.pi - lam * x) ^ 2) = 1 / (Real.pi / lam - x) ^ 2 := by
    have h : Real.pi - lam * x = lam * (Real.pi / lam - x) := by field_simp
    rw [h, mul_one_div]
    rw [div_eq_div_iff (pow_ne_zero 2 (mul_ne_zero (ne_of_gt hlam) (ne_of_gt hpd)))
      (pow_ne_zero 2 (ne_of_gt hpd))]
    ring
  rw [mul_add, mul_add, e1, e2, mul_one]

/-- The final numerical inequality: `12/(R+8)+16/R²+12/R+3π/R² ≤ 24/R` for `R ≥ 128`. -/
private lemma arith_final (R : ℝ) (hR : 128 ≤ R) :
    12 / (R + 8) + 16 / R ^ 2 + 12 / R + 3 * Real.pi / R ^ 2 ≤ 24 / R := by
  have hnum : 0 ≤ (80 - 3 * Real.pi) * R - 128 - 24 * Real.pi := by
    nlinarith [hR, Real.pi_lt_four]
  rw [← sub_nonneg]
  rw [show 24 / R - (12 / (R + 8) + 16 / R ^ 2 + 12 / R + 3 * Real.pi / R ^ 2)
       = ((80 - 3 * Real.pi) * R - 128 - 24 * Real.pi) / (R ^ 2 * (R + 8)) by
        field_simp; ring]
  exact div_nonneg hnum (by positivity)

theorem sum_lam2_div_sin_sq_le (lam R : ℝ) (u : ℕ → ℂ) (n : ℕ)
    (hlam : 0 < lam) (hR : 128 ≤ R) (hlamR : lam * R ^ 2 ≤ 1)
    (hx1 : ∀ j ≤ n, R / 4 + 2 ≤ (u j).re)
    (hx2 : ∀ j ≤ n, (u j).re ≤ Real.pi / lam - R / 4)
    (hdec : ∀ j < n, (u (j + 1)).re ≤ (u j).re - 1 / 3) :
    (∑ j ∈ Finset.range n,
        lam ^ 2 / (Real.sin (lam * (u j).re)) ^ 2) ≤ 24 / R := by
  have hRpos : (0:ℝ) < R := by linarith
  -- Per-term bound.
  have hper : (∑ j ∈ Finset.range n, lam^2/(Real.sin (lam*(u j).re))^2)
      ≤ ∑ j ∈ Finset.range n, (1/((u j).re)^2 + 1/(Real.pi/lam - (u j).re)^2 + lam^2) := by
    apply Finset.sum_le_sum; intro j hj
    have hjlt : j < n := Finset.mem_range.mp hj
    exact one_term_sin lam R ((u j).re) hlam hR (hx1 j (le_of_lt hjlt)) (hx2 j (le_of_lt hjlt))
  -- Split the bounding sum into its three parts.
  have hsplit : (∑ j ∈ Finset.range n, (1/((u j).re)^2 + 1/(Real.pi/lam - (u j).re)^2 + lam^2))
      = (∑ j ∈ Finset.range n, 1/((u j).re)^2)
      + (∑ j ∈ Finset.range n, 1/(Real.pi/lam - (u j).re)^2)
      + (∑ j ∈ Finset.range n, lam^2) := by
    rw [Finset.sum_add_distrib, Finset.sum_add_distrib]
  -- The `1/x²` sum.
  have hx_le : ∑ j ∈ Finset.range n, 1/((u j).re)^2 ≤ 12/(R+8) := by
    have h := sum_inv_sq_le_of_sep (fun j => (u j).re) (R/4+2) (1/3) n (by linarith) (by norm_num)
                (fun j hj => hx1 j hj) (fun j hj => hdec j hj)
    have he : (1:ℝ)/((1/3)*(R/4+2)) = 12/(R+8) := by field_simp; ring
    rwa [he] at h
  -- `d_j = π/λ - x_j` grows at least like `R/4 + j/3`.
  have hdlow : ∀ j ≤ n, R/4 + (j:ℝ)*(1/3) ≤ Real.pi/lam - (u j).re := by
    intro j hj
    induction j with
    | zero => simp only [Nat.cast_zero, zero_mul, add_zero]; linarith [hx2 0 (Nat.zero_le n)]
    | succ j ih =>
      have hjn : j ≤ n := le_trans (Nat.le_succ j) hj
      have ih' := ih hjn
      have hjlt : j < n := lt_of_lt_of_le (Nat.lt_succ_self j) hj
      have hd := hdec j hjlt
      have hgoal : R/4 + ((j:ℝ)+1)*(1/3) ≤ Real.pi/lam - (u (j+1)).re := by
        have h2 : ((j:ℝ)+1)*(1/3) = (j:ℝ)*(1/3) + 1/3 := by ring
        rw [h2]; linarith [ih', hd]
      simpa [Nat.cast_add, Nat.cast_one] using hgoal
  -- The `1/(π/λ-x)²` sum.
  have hd_le : ∑ j ∈ Finset.range n, 1/(Real.pi/lam - (u j).re)^2 ≤ 16/R^2 + 12/R := by
    have h1 : ∑ j ∈ Finset.range n, 1/(Real.pi/lam - (u j).re)^2
            ≤ ∑ j ∈ Finset.range n, 1/(R/4 + (j:ℝ)*(1/3))^2 := by
      apply Finset.sum_le_sum; intro j hj
      have hjlt : j < n := Finset.mem_range.mp hj
      have hge := hdlow j (le_of_lt hjlt)
      have hpos : 0 < R/4 + (j:ℝ)*(1/3) := by positivity
      have hdpos : 0 < Real.pi/lam - (u j).re := lt_of_lt_of_le hpos hge
      rw [one_div, one_div, inv_le_inv₀ (pow_pos hdpos 2) (pow_pos hpos 2)]
      exact pow_le_pow_left₀ hpos.le hge 2
    refine le_trans h1 ?_
    have := sumInvSqLe (R/4) (1/3) n (by linarith) (by norm_num)
    have e1 : (1:ℝ)/(R/4)^2 = 16/R^2 := by field_simp; ring
    have e2 : (1:ℝ)/((1/3)*(R/4)) = 12/R := by field_simp; ring
    rw [e1, e2] at this; exact this
  -- Monotonicity of the real parts.
  have hu0n : ∀ k ≤ n, (u k).re + (k:ℝ)*(1/3) ≤ (u 0).re := by
    intro k hk
    induction k with
    | zero => simp
    | succ k ih =>
      have hkn : k ≤ n := le_trans (Nat.le_succ k) hk
      have ih' := ih hkn
      have hklt : k < n := lt_of_lt_of_le (Nat.lt_succ_self k) hk
      have hd := hdec k hklt
      have hgoal : (u (k+1)).re + ((k:ℝ)+1)*(1/3) ≤ (u 0).re := by
        have h2 : ((k:ℝ)+1)*(1/3) = (k:ℝ)*(1/3) + 1/3 := by ring
        rw [h2]; linarith [ih', hd]
      simpa [Nat.cast_add, Nat.cast_one] using hgoal
  have hlam_le : lam ≤ 1/R^2 := by
    rw [le_div_iff₀ (pow_pos hRpos 2)]; exact hlamR
  -- The `∑ λ² = n λ²` term.
  have hn_le : ∑ j ∈ Finset.range n, lam^2 ≤ 3*Real.pi/R^2 := by
    rw [Finset.sum_const, Finset.card_range, nsmul_eq_mul]
    have hnb : (n:ℝ)*(1/3) ≤ Real.pi/lam - R/2 - 2 := by
      have h1 : (u 0).re - (u n).re ≤ Real.pi/lam - R/4 - (R/4+2) := by
        have a := hx2 0 (Nat.zero_le n); have b := hx1 n le_rfl; linarith
      have c := hu0n n le_rfl; linarith
    have hn3 : (n:ℝ) ≤ 3*(Real.pi/lam) := by linarith [hnb]
    have h1 : (n:ℝ)*lam^2 ≤ (3*(Real.pi/lam))*lam^2 := mul_le_mul_of_nonneg_right hn3 (by positivity)
    have h2 : (3*(Real.pi/lam))*lam^2 = 3*Real.pi*lam := by field_simp
    have h3 : 3*Real.pi*lam ≤ 3*Real.pi*(1/R^2) := mul_le_mul_of_nonneg_left hlam_le (by positivity)
    have h4 : 3*Real.pi*(1/R^2) = 3*Real.pi/R^2 := by ring
    linarith [h1, h2, h3, h4]
  calc (∑ j ∈ Finset.range n, lam^2/(Real.sin (lam*(u j).re))^2)
      ≤ ∑ j ∈ Finset.range n, (1/((u j).re)^2 + 1/(Real.pi/lam - (u j).re)^2 + lam^2) := hper
    _ = (∑ j ∈ Finset.range n, 1/((u j).re)^2) + (∑ j ∈ Finset.range n, 1/(Real.pi/lam - (u j).re)^2)
        + (∑ j ∈ Finset.range n, lam^2) := hsplit
    _ ≤ 12/(R+8) + (16/R^2 + 12/R) + 3*Real.pi/R^2 := by linarith [hx_le, hd_le, hn_le]
    _ ≤ 24/R := by linarith [arith_final R hR]

end Work.PARIMPL2.Direct
