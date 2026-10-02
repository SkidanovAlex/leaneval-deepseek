import Mathlib

-- Lean v4.35.0-rc3 / Mathlib 5e0c4e5 made `isDefEq` respect transparency when unifying instances; with it,
-- `ZMod.instField` and `ZMod.commRing` (and `Neg (ZMod p)` via `SubtractionMonoid`) no longer unify, which
-- breaks `ring`/`rw`/module-instance search on `ZMod p`. Restore the v4.34 behaviour for this file.
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false


namespace Work.PARIMPL2.Direct

/-- Telescoping bound: for `c ≥ 4`,
`∑_{k<n} 1/(c + k/3)^2 ≤ 3/(c - 1/3)`.
Since `k ↦ c + k/3` increases in steps of `1/3` and `c ≥ 4`, the sequence
`g k = 1/(c - 1/3 + k/3)` telescopes with `1/(c + k/3)^2 ≤ 3 (g k - g (k+1))`. -/
private lemma sum_inv_sq_shift_le (c : ℝ) (hc : 4 ≤ c) (n : ℕ) :
    ∑ k ∈ Finset.range n, (1:ℝ)/(c + (k:ℝ)/3)^2 ≤ 3/(c - 1/3) := by
  have hc1 : (0:ℝ) < c - 1/3 := by linarith
  set g : ℕ → ℝ := fun k => 1/(c - 1/3 + (k:ℝ)/3) with hg
  have key : ∀ k : ℕ, (1:ℝ)/(c + (k:ℝ)/3)^2 ≤ 3*(g k - g (k+1)) := by
    intro k
    have hA : 0 < c - 1/3 + (k:ℝ)/3 := by
      have : (0:ℝ) ≤ (k:ℝ)/3 := by positivity
      linarith
    have hB : 0 < c + (k:ℝ)/3 := by
      have : (0:ℝ) ≤ (k:ℝ)/3 := by positivity
      linarith
    have hAB : c - 1/3 + (k:ℝ)/3 ≤ c + (k:ℝ)/3 := by linarith
    have hcast : c - 1/3 + ((k+1 : ℕ):ℝ)/3 = c + (k:ℝ)/3 := by
      push_cast; ring
    have hkey : 3*(g k - g (k+1)) = 1/((c - 1/3 + (k:ℝ)/3)*(c+(k:ℝ)/3)) := by
      rw [hg]; simp only; rw [hcast]
      have hBA : c + (k:ℝ)/3 - (c - 1/3 + (k:ℝ)/3) = 1/3 := by ring
      have h1 : (1:ℝ)/(c - 1/3 + (k:ℝ)/3) - 1/(c + (k:ℝ)/3)
          = ((c + (k:ℝ)/3) - (c - 1/3 + (k:ℝ)/3))/((c - 1/3 + (k:ℝ)/3)*(c + (k:ℝ)/3)) := by
        rw [div_sub_div (1:ℝ) (1:ℝ) hA.ne' hB.ne', one_mul, mul_one]
      rw [h1, hBA]
      ring
    rw [hkey]
    apply one_div_le_one_div_of_le (by positivity)
    nlinarith [hAB, hB]
  have hsum : ∑ k ∈ Finset.range n, (g k - g (k+1)) = g 0 - g n := Finset.sum_range_sub' g n
  calc ∑ k ∈ Finset.range n, (1:ℝ)/(c + (k:ℝ)/3)^2
      ≤ ∑ k ∈ Finset.range n, 3*(g k - g (k+1)) := Finset.sum_le_sum (fun k _ => key k)
    _ = 3 * ∑ k ∈ Finset.range n, (g k - g (k+1)) := by rw [Finset.mul_sum]
    _ = 3 * (g 0 - g n) := by rw [hsum]
    _ ≤ 3/(c - 1/3) := by
        rw [hg]; simp only
        have hgn : (0:ℝ) ≤ 1/(c - 1/3 + ((n:ℕ):ℝ)/3) := by positivity
        have h0 : (1:ℝ)/(c - 1/3 + ((0:ℕ):ℝ)/3) = 1/(c-1/3) := by norm_num
        rw [h0]
        have step1 : 3 * ((1:ℝ)/(c - 1/3) - 1/(c - 1/3 + ((n:ℕ):ℝ)/3)) ≤ 3 * (1/(c-1/3)) := by
          nlinarith [hgn]
        have step2 : 3 * (1/(c-1/3)) = 3/(c-1/3) := by ring
        linarith [step1, step2]

/-- Sum bound for the tricorn (Mandelbar) parameter rays: for a decreasing sequence
`x_0 > x_1 > … > x_n` lying in `[R/4 + 2, π/lam − R/4]` with steps of at least `1/3`,
the reciprocals of `min(x_{j+1}, π/lam − x_j)` are summable with a uniform bound
`∑_{j<n} (π²/4) / min(x_{j+1}, π/lam − x_j)² ≤ 64/R` for `R ≥ 128`. -/
theorem sum_min_inv_sq_le (lam R : ℝ) (x : ℕ → ℝ) (n : ℕ) (hlam : 0 < lam) (hR : 128 ≤ R)
    (hlamR : lam * R^2 ≤ 1) (hx1 : ∀ j ≤ n, R/4 + 2 ≤ x j) (hx2 : ∀ j ≤ n, x j ≤ Real.pi/lam - R/4)
    (hdec : ∀ j < n, x (j+1) ≤ x j - 1/3) :
    ∑ j ∈ Finset.range n, (Real.pi^2/4) / (min (x (j+1)) (Real.pi/lam - x j))^2 ≤ 64/R := by
  have hR0 : (0:ℝ) < R := by linarith
  rcases Nat.eq_zero_or_pos n with hn | hn1
  · subst hn
    simp only [Finset.range_zero, Finset.sum_empty]
    exact div_nonneg (by norm_num) hR0.le
  have hdec' : ∀ k < n, x (k+1) - x k ≤ -(1/3:ℝ) := by
    intro k hk; have := hdec k hk; linarith
  -- `x i ≤ x 0 - i/3`
  have hkey1 : ∀ i ≤ n, x i ≤ x 0 - (i:ℝ)/3 := by
    intro i hi
    have hsum : ∑ k ∈ Finset.range i, (x (k+1) - x k) = x i - x 0 := Finset.sum_range_sub x i
    have hle : ∑ k ∈ Finset.range i, (x (k+1) - x k) ≤ ∑ _k ∈ Finset.range i, (-(1/3:ℝ)) := by
      apply Finset.sum_le_sum; intro k hk
      exact hdec' k (lt_of_lt_of_le (Finset.mem_range.mp hk) hi)
    have hconst : ∑ _k ∈ Finset.range i, (-(1/3:ℝ)) = -(i:ℝ)/3 := by
      rw [Finset.sum_const, Finset.card_range, nsmul_eq_mul]; ring
    rw [hsum, hconst] at hle; linarith
  -- `x n + (n - i)/3 ≤ x i`
  have hkey2 : ∀ i ≤ n, x n + ((n - i : ℕ):ℝ)/3 ≤ x i := by
    intro i hi
    have hsum : ∑ k ∈ Finset.range (n - i), (x (i + (k+1)) - x (i + k)) = x (i + (n-i)) - x (i+0) :=
      Finset.sum_range_sub (fun k => x (i + k)) (n - i)
    have hiat : i + (n - i) = n := Nat.add_sub_cancel' hi
    have hle : ∑ k ∈ Finset.range (n - i), (x (i + (k+1)) - x (i + k))
        ≤ ∑ _k ∈ Finset.range (n - i), (-(1/3:ℝ)) := by
      apply Finset.sum_le_sum; intro k hk
      have hklt : k < n - i := Finset.mem_range.mp hk
      have hik : i + k < n := by omega
      have := hdec' (i + k) hik
      have hidx : i + (k+1) = i + k + 1 := by omega
      rw [hidx]; exact this
    have hconst : ∑ _k ∈ Finset.range (n - i), (-(1/3:ℝ)) = -(((n-i:ℕ):ℝ))/3 := by
      rw [Finset.sum_const, Finset.card_range, nsmul_eq_mul]; ring
    rw [hsum, hiat, hconst] at hle
    simp only [Nat.add_zero] at hle
    linarith
  -- per-term bound
  have hterm : ∀ j < n, (Real.pi^2/4) / (min (x (j+1)) (Real.pi/lam - x j))^2 ≤
      (Real.pi^2/4)/(R/4 + ((n - 1 - j : ℕ):ℝ)/3)^2 + (Real.pi^2/4)/(R/4 + (j:ℝ)/3)^2 := by
    intro j hj
    have hu : R/4 + ((n - 1 - j : ℕ):ℝ)/3 ≤ x (j+1) := by
      have hk2 := hkey2 (j+1) hj
      have hxn : R/4 + 2 ≤ x n := hx1 n le_rfl
      have hcast : ((n - (j+1) : ℕ):ℝ) = ((n - 1 - j : ℕ):ℝ) := by congr 1; omega
      rw [hcast] at hk2
      linarith
    have hv : R/4 + (j:ℝ)/3 ≤ Real.pi/lam - x j := by
      have hk1 := hkey1 j (le_of_lt hj)
      have hx0 : x 0 ≤ Real.pi/lam - R/4 := hx2 0 (by omega)
      linarith
    have hA : 0 < R/4 + ((n - 1 - j : ℕ):ℝ)/3 := by
      have : (0:ℝ) ≤ ((n - 1 - j : ℕ):ℝ)/3 := by positivity
      linarith
    have hB : 0 < R/4 + (j:ℝ)/3 := by
      have : (0:ℝ) ≤ (j:ℝ)/3 := by positivity
      linarith
    have hmain : (1:ℝ)/(min (x (j+1)) (Real.pi/lam - x j))^2 ≤
        1/(R/4 + ((n-1-j:ℕ):ℝ)/3)^2 + 1/(R/4 + (j:ℝ)/3)^2 := by
      rcases le_total (x (j+1)) (Real.pi/lam - x j) with huv | hvu
      · rw [min_eq_left huv]
        have h1 : (1:ℝ)/(x (j+1))^2 ≤ 1/(R/4 + ((n-1-j:ℕ):ℝ)/3)^2 := by
          apply one_div_le_one_div_of_le (by positivity)
          exact pow_le_pow_left₀ hA.le hu 2
        have h2 : (0:ℝ) ≤ 1/(R/4 + (j:ℝ)/3)^2 := by positivity
        linarith
      · rw [min_eq_right hvu]
        have h1 : (1:ℝ)/(Real.pi/lam - x j)^2 ≤ 1/(R/4 + (j:ℝ)/3)^2 := by
          apply one_div_le_one_div_of_le (by positivity)
          exact pow_le_pow_left₀ hB.le hv 2
        have h2 : (0:ℝ) ≤ 1/(R/4 + ((n-1-j:ℕ):ℝ)/3)^2 := by positivity
        linarith
    have hpi4 : (0:ℝ) ≤ Real.pi^2/4 := by positivity
    calc (Real.pi^2/4)/(min (x (j+1)) (Real.pi/lam - x j))^2
        = (Real.pi^2/4)*(1/(min (x (j+1)) (Real.pi/lam - x j))^2) := by rw [div_eq_mul_inv]; ring
      _ ≤ (Real.pi^2/4)*(1/(R/4 + ((n-1-j:ℕ):ℝ)/3)^2 + 1/(R/4 + (j:ℝ)/3)^2) :=
          mul_le_mul_of_nonneg_left hmain hpi4
      _ = (Real.pi^2/4)/(R/4 + ((n - 1 - j : ℕ):ℝ)/3)^2 + (Real.pi^2/4)/(R/4 + (j:ℝ)/3)^2 := by
          rw [mul_add, div_eq_mul_inv, div_eq_mul_inv]; ring
  have hF_le : ∑ j ∈ Finset.range n, (Real.pi^2/4)/(min (x (j+1)) (Real.pi/lam - x j))^2
      ≤ (∑ j ∈ Finset.range n, (Real.pi^2/4)/(R/4 + ((n-1-j:ℕ):ℝ)/3)^2)
        + ∑ j ∈ Finset.range n, (Real.pi^2/4)/(R/4 + (j:ℝ)/3)^2 := by
    calc ∑ j ∈ Finset.range n, (Real.pi^2/4)/(min (x (j+1)) (Real.pi/lam - x j))^2
        ≤ ∑ j ∈ Finset.range n, ((Real.pi^2/4)/(R/4 + ((n-1-j:ℕ):ℝ)/3)^2
            + (Real.pi^2/4)/(R/4 + (j:ℝ)/3)^2) :=
          Finset.sum_le_sum (fun j hj => hterm j (Finset.mem_range.mp hj))
      _ = (∑ j ∈ Finset.range n, (Real.pi^2/4)/(R/4 + ((n-1-j:ℕ):ℝ)/3)^2)
            + ∑ j ∈ Finset.range n, (Real.pi^2/4)/(R/4 + (j:ℝ)/3)^2 := Finset.sum_add_distrib
  have hA_eq : ∑ j ∈ Finset.range n, (Real.pi^2/4)/(R/4 + ((n-1-j:ℕ):ℝ)/3)^2
      = ∑ k ∈ Finset.range n, (Real.pi^2/4)/(R/4 + (k:ℝ)/3)^2 :=
    Finset.sum_range_reflect (fun k => (Real.pi^2/4)/(R/4 + (k:ℝ)/3)^2) n
  have hT_split : ∑ k ∈ Finset.range n, (Real.pi^2/4)/(R/4 + (k:ℝ)/3)^2
      = (Real.pi^2/4) * ∑ k ∈ Finset.range n, (1:ℝ)/(R/4 + (k:ℝ)/3)^2 := by
    rw [Finset.mul_sum]
    apply Finset.sum_congr rfl
    intro k _
    rw [div_eq_mul_inv]; ring
  have hS_bound : ∑ k ∈ Finset.range n, (1:ℝ)/(R/4 + (k:ℝ)/3)^2 ≤ 3/(R/4 - 1/3) :=
    sum_inv_sq_shift_le (R/4) (by linarith) n
  have hnum : 18*Real.pi^2/(3*R-4) ≤ 64/R := by
    have hpi2 : Real.pi^2 < 10 := by nlinarith [Real.pi_lt_d2, Real.pi_pos]
    rw [div_le_div_iff₀ (by linarith : (0:ℝ) < 3*R-4) hR0]
    nlinarith [hpi2, hR]
  calc ∑ j ∈ Finset.range n, (Real.pi^2/4)/(min (x (j+1)) (Real.pi/lam - x j))^2
      ≤ (∑ j ∈ Finset.range n, (Real.pi^2/4)/(R/4 + ((n-1-j:ℕ):ℝ)/3)^2)
          + ∑ j ∈ Finset.range n, (Real.pi^2/4)/(R/4 + (j:ℝ)/3)^2 := hF_le
    _ = 2 * (∑ k ∈ Finset.range n, (Real.pi^2/4)/(R/4 + (k:ℝ)/3)^2) := by rw [hA_eq]; ring
    _ = 2 * ((Real.pi^2/4) * ∑ k ∈ Finset.range n, (1:ℝ)/(R/4 + (k:ℝ)/3)^2) := by rw [hT_split]
    _ ≤ 2 * ((Real.pi^2/4) * (3/(R/4 - 1/3))) := by
        apply mul_le_mul_of_nonneg_left
        · exact mul_le_mul_of_nonneg_left hS_bound (by positivity)
        · norm_num
    _ = 18*Real.pi^2/(3*R-4) := by field_simp; ring
    _ ≤ 64/R := hnum

end Work.PARIMPL2.Direct
