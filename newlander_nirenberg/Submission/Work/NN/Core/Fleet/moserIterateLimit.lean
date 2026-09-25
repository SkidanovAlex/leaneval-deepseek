import Mathlib

namespace Work.NN.Core.Fleet

open Filter
open scoped Topology

/-- **Iterated affine-geometric bound.** If a real sequence `x` satisfies
`x j ≤ (a + b·j) + r·x (j+1)` with `0 ≤ r < 1`, and `x` is bounded above by `L`, then
`x 0 ≤ a/(1-r) + b·r/(1-r)^2`.

The proof sets `d = b/(1-r)` and `c = (a + r·d)/(1-r)`, so that the potential
`y j = x j - c - d·j` satisfies `y j ≤ r·y (j+1)` *exactly*, and then lets `j → ∞`
using that `r^j → 0` and `j·r^j → 0`. -/
theorem geom_iter_le {r : ℝ} (hr0 : 0 ≤ r) (hr1 : r < 1)
    {x : ℕ → ℝ} {L a b : ℝ}
    (hx : ∀ j, x j ≤ a + b * (j:ℝ) + r * x (j + 1))
    (hL : ∀ j, x j ≤ L) :
    x 0 ≤ a / (1 - r) + b * r / (1 - r) ^ 2 := by
  have h1r : 0 < 1 - r := by linarith
  set d : ℝ := b / (1 - r) with hd
  set c : ℝ := (a + r * d) / (1 - r) with hc
  have hcd : c = a / (1 - r) + b * r / (1 - r) ^ 2 := by
    rw [hc, hd]; field_simp
  set y : ℕ → ℝ := fun j => x j - c - d * (j:ℝ) with hy
  have hyrec : ∀ j, y j ≤ r * y (j + 1) := by
    intro j
    have hid : a + b * (j:ℝ) + r * (c + d * ((j:ℝ) + 1)) - (c + d * (j:ℝ)) = 0 := by
      rw [hc, hd]; field_simp; ring
    have h2 : y (j+1) = x (j+1) - c - d * ((j:ℝ)+1) := by
      simp only [hy]; push_cast; ring
    calc y j = x j - c - d * (j:ℝ) := by simp only [hy]
      _ ≤ (a + b * (j:ℝ) + r * x (j + 1)) - c - d * (j:ℝ) := by linarith [hx j]
      _ = (a + b * (j:ℝ) + r * (c + d * ((j:ℝ) + 1)) - (c + d * (j:ℝ))) + r * y (j+1) := by
            rw [h2]; ring
      _ = r * y (j + 1) := by rw [hid]; ring
  have hy_ge : ∀ J : ℕ, y 0 ≤ r^J * y J := by
    intro J
    induction J with
    | zero => simp
    | succ J ih =>
      have hpow : 0 ≤ r^J := pow_nonneg hr0 J
      calc y 0 ≤ r^J * y J := ih
        _ ≤ r^J * (r * y (J+1)) := mul_le_mul_of_nonneg_left (hyrec J) hpow
        _ = r^(J+1) * y (J+1) := by rw [pow_succ]; ring
  have hbound : ∀ J : ℕ, y 0 ≤ r^J * (L - c - d * (J:ℝ)) := by
    intro J
    have hpow : 0 ≤ r^J := pow_nonneg hr0 J
    have hJ : y J ≤ L - c - d * (J:ℝ) := by
      have := hL J; simp only [hy]; linarith
    calc y 0 ≤ r^J * y J := hy_ge J
      _ ≤ r^J * (L - c - d * (J:ℝ)) := mul_le_mul_of_nonneg_left hJ hpow
  have hrnorm : ‖r‖ < 1 := by rwa [Real.norm_eq_abs, abs_of_nonneg hr0]
  have hsum : Summable (fun J : ℕ => (J:ℝ) * r^J) := by
    simpa only [pow_one] using summable_pow_mul_geometric_of_norm_lt_one 1 (r := r) hrnorm
  have hlim1 : Tendsto (fun J : ℕ => r^J) atTop (𝓝 0) :=
    tendsto_pow_atTop_nhds_zero_of_lt_one hr0 hr1
  have hlim2 : Tendsto (fun J : ℕ => (J:ℝ) * r^J) atTop (𝓝 0) := hsum.tendsto_atTop_zero
  have hlimg : Tendsto (fun J : ℕ => r^J * (L - c - d * (J:ℝ))) atTop (𝓝 0) := by
    have hA : Tendsto (fun J : ℕ => (L - c) * r^J) atTop (𝓝 ((L - c) * 0)) :=
      hlim1.const_mul (L - c)
    have hB : Tendsto (fun J : ℕ => d * ((J:ℝ) * r^J)) atTop (𝓝 (d * 0)) :=
      hlim2.const_mul d
    have hsub := hA.sub hB
    have : (fun J : ℕ => r^J * (L - c - d*(J:ℝ))) = (fun J : ℕ => (L-c)*r^J - d*((J:ℝ)*r^J)) := by
      funext J; ring
    rw [this]; simpa using hsub
  have hy0 : y 0 ≤ 0 := ge_of_tendsto' hlimg hbound
  have hxc : x 0 ≤ c := by
    have : y 0 = x 0 - c := by simp only [hy]; ring
    linarith [hy0]
  rw [← hcd]; exact hxc

/-- Moser-iteration limit: a sequence satisfying the sublinear recursion
`m j ≤ cA · cB^j · q^{1/k} · (m (j+1))^r` with `r = 1 - 1/k` (`k ≥ 1`) and bounded above by `K`
satisfies `m 0 ≤ cA^k · cB^{r·k^2} · q`. -/
theorem moserIterateLimit {r : ℝ} (hr0 : 0 ≤ r) (hr1 : r < 1)
    {m : ℕ → ℝ} (hmpos : ∀ j, 0 < m j) {K : ℝ} (hK : 0 < K) (hmK : ∀ j, m j ≤ K)
    {cA cB q : ℝ} (hcA : 0 < cA) (hcB : 0 < cB) (hq : 0 < q)
    {k : ℕ} (hk : 1 ≤ k) (hrk : r = 1 - 1 / (k : ℝ))
    (hrec : ∀ j, m j ≤ cA * cB ^ j * q ^ (1 / (k : ℝ)) * (m (j + 1)) ^ r) :
    m 0 ≤ cA ^ k * cB ^ (r * (k : ℝ) ^ 2) * q := by
  have h1r : 1 - r = 1 / (k:ℝ) := by linarith [hrk]
  have hx : ∀ j, Real.log (m j) ≤ (Real.log cA + (1/(k:ℝ))*Real.log q)
      + Real.log cB * (j:ℝ) + r * Real.log (m (j+1)) := by
    intro j
    have h1 : Real.log (m j) ≤ Real.log (cA * cB^j * q^(1/(k:ℝ)) * (m (j+1))^r) :=
      Real.log_le_log (hmpos j) (hrec j)
    have h2 : Real.log (cA * cB^j * q^(1/(k:ℝ)) * (m (j+1))^r)
        = (Real.log cA + (1/(k:ℝ))*Real.log q) + Real.log cB * (j:ℝ)
          + r*Real.log (m (j+1)) := by
      have e1 : (m (j+1))^r ≠ 0 := ne_of_gt (Real.rpow_pos_of_pos (hmpos (j+1)) r)
      have e2 : q^(1/(k:ℝ)) ≠ 0 := ne_of_gt (Real.rpow_pos_of_pos hq _)
      have e3 : cB^j ≠ 0 := pow_ne_zero _ (ne_of_gt hcB)
      have e4 : cA * cB^j ≠ 0 := mul_ne_zero (ne_of_gt hcA) e3
      have e5 : cA * cB^j * q^(1/(k:ℝ)) ≠ 0 := mul_ne_zero e4 e2
      rw [Real.log_mul e5 e1, Real.log_mul e4 e2, Real.log_mul (ne_of_gt hcA) e3,
          Real.log_pow, Real.log_rpow hq, Real.log_rpow (hmpos (j+1))]
      ring
    rw [h2] at h1; exact h1
  have hL : ∀ j, Real.log (m j) ≤ Real.log K := fun j => Real.log_le_log (hmpos j) (hmK j)
  have hg := geom_iter_le (a := Real.log cA + (1/(k:ℝ))*Real.log q) (b := Real.log cB)
      hr0 hr1 hx hL
  have hb : Real.log (m 0) ≤ (k:ℝ)*Real.log cA + Real.log q + (r*(k:ℝ)^2)*Real.log cB := by
    have hval : (Real.log cA + (1/(k:ℝ))*Real.log q)/(1/(k:ℝ))
        + Real.log cB * r/(1/(k:ℝ))^2
        = (k:ℝ)*Real.log cA + Real.log q + (r*(k:ℝ)^2)*Real.log cB := by
      have hkpos : (0:ℝ) < (k:ℝ) := by exact_mod_cast hk
      field_simp
      try ring
    rw [h1r] at hg
    linarith [hg, hval]
  have hexp := Real.exp_le_exp.mpr hb
  rw [Real.exp_log (hmpos 0)] at hexp
  have hexpv : Real.exp ((k:ℝ)*Real.log cA + Real.log q + (r*(k:ℝ)^2)*Real.log cB)
      = cA^k * cB^(r*(k:ℝ)^2) * q := by
    rw [Real.exp_add, Real.exp_add]
    rw [Real.exp_nat_mul, Real.exp_log hcA, Real.exp_log hq]
    rw [mul_comm (r * (k:ℝ)^2) (Real.log cB), ← Real.rpow_def_of_pos hcB]
    ring
  rwa [hexpv] at hexp

end Work.NN.Core.Fleet
