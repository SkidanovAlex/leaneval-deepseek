/-
# The second-order bound for the `θ₀₀` `q`-series `bSeries`

`bSeries z = 1 + 2 ∑_{m ≥ 0} z^{(m+1)²} = ∑_{n ∈ ℤ} z^{n²}` has `bSeries z = 1 + 2 z + O(z²)`,
and here we make the `O(z²)` uniform and Lipschitz in the form needed for the local inverse
function argument: on the disc of radius `r ≤ 1/2`,

  `‖bSeries x - bSeries y - 2 (x - y)‖ ≤ 32 r ‖x - y‖`.

Writing `bSeries z = 1 + 2 z + 2 T z` with `T z = ∑_{m ≥ 0} z^{(m+2)²}`, the difference is
`2 (T x - T y)`, and each term obeys `‖x^K - y^K‖ ≤ K r^{K-1} ‖x-y‖`.  The exponents `K = (m+2)²`
are so large that `K r^{K-1} ≤ 16 r³ (1/2)^{m+1}`, whose sum is `16 r³ ≤ 4 r`.
-/
import Mathlib
import Submission.Work.Rigidity.LambdaSeries

noncomputable section

namespace Work.Rigidity

open Finset

/-- The power difference bound: for `‖x‖, ‖y‖ ≤ r`, `‖xⁿ - yⁿ‖ ≤ n r^{n-1} ‖x - y‖`. -/
lemma bSeries_norm_pow_sub_pow_le (x y : ℂ) (n : ℕ) (r : ℝ) (hx : ‖x‖ ≤ r) (hy : ‖y‖ ≤ r) :
    ‖x ^ n - y ^ n‖ ≤ (n:ℝ) * r ^ (n - 1) * ‖x - y‖ := by
  have hry : (0:ℝ) ≤ r := (norm_nonneg x).trans hx
  rw [← geom_sum₂_mul x y n, norm_mul]
  have hsum : ‖∑ i ∈ Finset.range n, x ^ i * y ^ (n - 1 - i)‖ ≤ (n:ℝ) * r ^ (n-1) := by
    calc ‖∑ i ∈ Finset.range n, x ^ i * y ^ (n - 1 - i)‖
        ≤ ∑ i ∈ Finset.range n, ‖x ^ i * y ^ (n - 1 - i)‖ := norm_sum_le _ _
      _ ≤ ∑ i ∈ Finset.range n, r ^ (n-1) := by
          refine Finset.sum_le_sum ?_
          intro i hi
          rw [norm_mul, norm_pow, norm_pow]
          have hi' : i ≤ n - 1 := Nat.le_sub_one_of_lt (Finset.mem_range.mp hi)
          have h1 : ‖x‖^i ≤ r^i := pow_le_pow_left₀ (norm_nonneg x) hx i
          have h2 : ‖y‖^(n-1-i) ≤ r^(n-1-i) := pow_le_pow_left₀ (norm_nonneg y) hy _
          calc ‖x‖^i * ‖y‖^(n-1-i) ≤ r^i * r^(n-1-i) :=
                mul_le_mul h1 h2 (by positivity) (pow_nonneg hry i)
            _ = r^(i + (n-1-i)) := (pow_add ..).symm
            _ = r^(n-1) := by rw [Nat.add_sub_cancel' hi']
      _ = (n:ℝ) * r^(n-1) := by simp
  calc ‖(∑ i ∈ Finset.range n, x ^ i * y ^ (n - 1 - i))‖ * ‖x - y‖
      ≤ ((n:ℝ) * r^(n-1)) * ‖x - y‖ := by gcongr
    _ = (n:ℝ) * r^(n-1) * ‖x-y‖ := by ring

/-- `N² ≤ 2^{N+1}` for `N ≥ 2`. -/
lemma bSeries_sq_le_two_pow (N : ℕ) (hN : 2 ≤ N) : N^2 ≤ 2^(N+1) := by
  induction N, hN using Nat.le_induction with
  | base => norm_num
  | succ N hN ih =>
      rcases eq_or_lt_of_le hN with h | h
      · subst h; norm_num
      · have h3 : 3 ≤ N := h
        have hsq : (N+1)^2 ≤ 2 * N^2 := by
          have hx : (N+1)^2 = N^2 + 2*N + 1 := by ring
          nlinarith [h3]
        calc (N+1)^2 ≤ 2 * N^2 := hsq
          _ ≤ 2 * 2^(N+1) := by nlinarith
          _ = 2^(N+2) := by ring

/-- The key numeric estimate: `N² (1/2)^{N²} ≤ (1/2)^{N-1}` for `N ≥ 2`. -/
lemma bSeries_num_bound (N : ℕ) (hN : 2 ≤ N) : (N:ℝ)^2 * (1/2:ℝ)^(N*N) ≤ (1/2:ℝ)^(N-1) := by
  have hsq : (N:ℝ)^2 ≤ (2:ℝ)^(N+1) := by exact_mod_cast bSeries_sq_le_two_pow N hN
  have h2N : 2*N ≤ N*N := by nlinarith
  have h1 : (2:ℝ)^(N+1) / 2^(N*N) ≤ 1 / 2^(N-1) := by
    rw [div_le_div_iff₀ (by positivity) (by positivity)]
    rw [← pow_add, one_mul]
    exact pow_le_pow_right₀ (by norm_num) (by omega)
  calc (N:ℝ)^2 * (1/2:ℝ)^(N*N) = (N:ℝ)^2 / 2^(N*N) := by rw [one_div_pow]; ring
    _ ≤ (2:ℝ)^(N+1) / 2^(N*N) := by gcongr
    _ ≤ 1 / 2^(N-1) := h1
    _ = (1/2:ℝ)^(N-1) := by rw [one_div_pow]

/-- Term bound for the majorant series: `K r^{K-1} ≤ 16 r³ (1/2)^{m+1}` with `K = (m+2)²`. -/
lemma bSeries_term_bound (r : ℝ) (hr : 0 < r) (hr1 : r ≤ 1/2) (m : ℕ) :
    (((m+2)*(m+2) : ℕ) : ℝ) * r ^ ((m+2)*(m+2) - 1) ≤ 16 * r^3 * (1/2:ℝ)^(m+1) := by
  set N := m + 2 with hNd
  have hN2 : 2 ≤ N := by omega
  have hm1 : N - 1 = m + 1 := by omega
  have hexp : (m+2)*(m+2) = N*N := by rw [hNd]
  have hcast : (((m+2)*(m+2) : ℕ) : ℝ) = (N:ℝ)^2 := by
    rw [hexp]; push_cast; ring
  rw [hexp, hcast, ← hm1]
  have h4 : 4 ≤ N*N := by nlinarith
  have h1 : r ^ (N*N - 1) ≤ 16 * r^3 * (1/2:ℝ)^(N*N) := by
    have hsplit : r ^ (N*N - 1) = r^3 * r^(N*N - 4) := by
      rw [← pow_add]
      congr 1
      omega
    rw [hsplit]
    have h2 : r^(N*N-4) ≤ (1/2:ℝ)^(N*N-4) := pow_le_pow_left₀ hr.le hr1 _
    have h3 : (1/2:ℝ)^(N*N-4) = 16 * (1/2)^(N*N) := by
      have hh : (1/2:ℝ)^(N*N) = (1/2)^(N*N-4) * (1/2)^4 := by
        rw [← pow_add, Nat.sub_add_cancel h4]
      rw [hh]
      ring_nf
    calc r^3 * r^(N*N-4) ≤ r^3 * (1/2:ℝ)^(N*N-4) := by gcongr
      _ = r^3 * (16 * (1/2:ℝ)^(N*N)) := by rw [h3]
      _ = 16 * r^3 * (1/2:ℝ)^(N*N) := by ring
  calc (N:ℝ)^2 * r ^ (N*N - 1) ≤ (N:ℝ)^2 * (16 * r^3 * (1/2:ℝ)^(N*N)) := by gcongr
    _ = 16 * r^3 * ((N:ℝ)^2 * (1/2:ℝ)^(N*N)) := by ring
    _ ≤ 16 * r^3 * (1/2:ℝ)^(N-1) := by
        gcongr
        exact bSeries_num_bound N hN2

/-- `∑_{m} (1/2)^{m+1} = 1`. -/
lemma bSeries_hasSum_geom_half_shift : HasSum (fun m : ℕ => (1/2:ℝ)^(m+1)) 1 := by
  have h0 := hasSum_geometric_of_norm_lt_one (ξ := (1:ℝ)/2) (by norm_num)
  have h0' : HasSum (fun n : ℕ => ((1:ℝ)/2)^n) 2 := by
    rw [show (1 - (1:ℝ)/2)⁻¹ = 2 by norm_num] at h0
    exact h0
  have h2 := (hasSum_nat_add_iff' (f := fun n : ℕ => ((1:ℝ)/2)^n) 1).mpr h0'
  rw [show (2:ℝ) - ∑ i ∈ range 1, ((1:ℝ)/2)^i = 1 by norm_num [Finset.sum_range_one]] at h2
  exact h2

/-- A power series with exponents growing at least linearly converges on the disc `‖z‖ ≤ 1/2`. -/
lemma bSeries_summable_exp (z : ℂ) (hz : ‖z‖ ≤ 1/2) (E : ℕ → ℕ) (hE : ∀ n, n + 1 ≤ E n) :
    Summable (fun n : ℕ => z ^ E n) := by
  refine Summable.of_norm_bounded bSeries_hasSum_geom_half_shift.summable ?_
  intro n
  rw [norm_pow]
  have h1 : ‖z‖ ^ E n ≤ (1/2:ℝ) ^ (E n) := pow_le_pow_left₀ (norm_nonneg z) hz _
  have h2 : (1/2:ℝ) ^ (E n) ≤ (1/2:ℝ) ^ (n+1) :=
    pow_le_pow_of_le_one (by norm_num) (by norm_num) (hE n)
  linarith

/-- Splitting off the constant and linear terms of `bCore`:
`bCore z = z + ∑_{m ≥ 0} z^{(m+2)²}`. -/
lemma bSeries_bCore_split (z : ℂ) (hz : ‖z‖ ≤ 1/2) :
    bCore z = z + ∑' m : ℕ, z ^ ((m+2)*(m+2)) := by
  have hs : Summable (fun n : ℕ => z ^ ((n+1)*(n+1))) :=
    bSeries_summable_exp z hz _ (fun n => by nlinarith)
  rw [bCore_apply, hs.tsum_eq_zero_add]
  simp only [zero_add, mul_one, pow_one]

theorem bSeries_sub_bound (r : ℝ) (hr : 0 < r) (hr1 : r ≤ 1 / 2) (x y : ℂ)
    (hx : ‖x‖ ≤ r) (hy : ‖y‖ ≤ r) :
    ‖Work.Rigidity.bSeries x - Work.Rigidity.bSeries y - 2 * (x - y)‖ ≤ 32 * r * ‖x - y‖ := by
  have hx2 : ‖x‖ ≤ 1/2 := hx.trans hr1
  have hy2 : ‖y‖ ≤ 1/2 := hy.trans hr1
  have hxs : Summable (fun m : ℕ => x ^ ((m+2)*(m+2))) :=
    bSeries_summable_exp x hx2 _ (fun n => by nlinarith)
  have hys : Summable (fun m : ℕ => y ^ ((m+2)*(m+2))) :=
    bSeries_summable_exp y hy2 _ (fun n => by nlinarith)
  have hmain : Work.Rigidity.bSeries x - Work.Rigidity.bSeries y - 2 * (x - y)
      = 2 * ((∑' m : ℕ, x ^ ((m+2)*(m+2))) - (∑' m : ℕ, y ^ ((m+2)*(m+2)))) := by
    rw [bSeries_apply, bSeries_apply, bSeries_bCore_split x hx2, bSeries_bCore_split y hy2]
    ring
  rw [hmain, norm_mul]
  have h2 : ‖(2:ℂ)‖ = 2 := by simp
  rw [h2]
  have hdiff : (∑' m : ℕ, x ^ ((m+2)*(m+2))) - (∑' m : ℕ, y ^ ((m+2)*(m+2)))
      = ∑' m : ℕ, (x ^ ((m+2)*(m+2)) - y ^ ((m+2)*(m+2))) :=
    (Summable.tsum_sub hxs hys).symm
  rw [hdiff]
  have hb : ‖∑' m : ℕ, (x ^ ((m+2)*(m+2)) - y ^ ((m+2)*(m+2)))‖ ≤ 16 * r^3 * ‖x - y‖ := by
    have hg : HasSum (fun m : ℕ => (16 * r^3 * ‖x - y‖) * (1/2:ℝ)^(m+1))
        (16 * r^3 * ‖x - y‖) := by
      have hh := bSeries_hasSum_geom_half_shift.mul_left (16 * r^3 * ‖x - y‖)
      simpa using hh
    refine tsum_of_norm_bounded (g := fun m : ℕ => (16 * r^3 * ‖x - y‖) * (1/2:ℝ)^(m+1)) hg ?_
    intro m
    have h1 := bSeries_norm_pow_sub_pow_le x y ((m+2)*(m+2)) r hx hy
    have h2 := bSeries_term_bound r hr hr1 m
    calc ‖x ^ ((m+2)*(m+2)) - y ^ ((m+2)*(m+2))‖
        ≤ (((m+2)*(m+2) : ℕ) : ℝ) * r ^ ((m+2)*(m+2) - 1) * ‖x - y‖ := h1
      _ ≤ (16 * r^3 * (1/2:ℝ)^(m+1)) * ‖x - y‖ := by gcongr
      _ = (16 * r^3 * ‖x - y‖) * (1/2:ℝ)^(m+1) := by ring
  have hr3 : r^3 ≤ r := by nlinarith [sq_nonneg r]
  have hle : r^3 * ‖x - y‖ ≤ r * ‖x - y‖ := mul_le_mul_of_nonneg_right hr3 (norm_nonneg _)
  linarith

end Work.Rigidity
