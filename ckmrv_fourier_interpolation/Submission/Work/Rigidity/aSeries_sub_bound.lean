import Mathlib
import Submission.Work.Rigidity.LambdaSeries

noncomputable section

namespace Work.Rigidity

/-- Coefficient `m (m+1) r^{m(m+1)-1}`: the bound for the difference quotient of `z ↦ z^{m(m+1)}`. -/
private def acoeff (r : ℝ) (m : ℕ) : ℝ := (m : ℝ) * (m + 1) * r ^ (m * (m + 1) - 1)

/-- Difference of `a`-th powers: for `‖x‖, ‖y‖ ≤ r` one has
`‖x^a - y^a‖ ≤ a r^{a-1} ‖x - y‖`. -/
lemma norm_pow_sub_pow_le (r : ℝ) (hr : 0 ≤ r) (x y : ℂ)
    (hx : ‖x‖ ≤ r) (hy : ‖y‖ ≤ r) (a : ℕ) :
    ‖x ^ a - y ^ a‖ ≤ (a : ℝ) * r ^ (a - 1) * ‖x - y‖ := by
  have hxy : x ^ a - y ^ a
      = (∑ i ∈ Finset.range a, x ^ i * y ^ (a - 1 - i)) * (x - y) :=
    (geom_sum₂_mul x y a).symm
  rw [hxy, norm_mul]
  have hsum : ‖∑ i ∈ Finset.range a, x ^ i * y ^ (a - 1 - i)‖
      ≤ ∑ i ∈ Finset.range a, r ^ (a - 1) := by
    refine (norm_sum_le _ _).trans ?_
    refine Finset.sum_le_sum ?_
    intro i hi
    have hi' : i ≤ a - 1 := Nat.le_sub_one_of_lt (Finset.mem_range.mp hi)
    rw [norm_mul, norm_pow, norm_pow]
    have h1 : ‖x‖ ^ i ≤ r ^ i := pow_le_pow_left₀ (norm_nonneg x) hx i
    have h2 : ‖y‖ ^ (a - 1 - i) ≤ r ^ (a - 1 - i) :=
      pow_le_pow_left₀ (norm_nonneg y) hy _
    calc ‖x‖ ^ i * ‖y‖ ^ (a - 1 - i) ≤ r ^ i * r ^ (a - 1 - i) := by
          apply mul_le_mul h1 h2
          · positivity
          · positivity
      _ = r ^ (a - 1) := by rw [← pow_add]; congr 1; omega
  rw [Finset.sum_const, Finset.card_range, nsmul_eq_mul] at hsum
  calc ‖∑ i ∈ Finset.range a, x ^ i * y ^ (a - 1 - i)‖ * ‖x - y‖
      ≤ ((a : ℝ) * r ^ (a - 1)) * ‖x - y‖ :=
        mul_le_mul_of_nonneg_right hsum (norm_nonneg _)
    _ = (a : ℝ) * r ^ (a - 1) * ‖x - y‖ := by ring

/-- Elementary bound `(i+1)(i+2) ≤ 4 · 3^i`. -/
private lemma quad_le (i : ℕ) : (i + 1) * (i + 2) ≤ 4 * 3 ^ i := by
  induction i with
  | zero => norm_num
  | succ k ih =>
    have h1 : Nat.succ k + 1 = k + 2 := by omega
    have h2 : Nat.succ k + 2 = k + 3 := by omega
    rw [h1, h2]
    have hle : k + 3 ≤ 3 * (k + 1) := by omega
    calc (k + 2) * (k + 3) ≤ (k + 2) * (3 * (k + 1)) := Nat.mul_le_mul_left _ hle
      _ = 3 * ((k + 1) * (k + 2)) := by ring
      _ ≤ 3 * (4 * 3 ^ k) := Nat.mul_le_mul_left 3 ih
      _ = 4 * 3 ^ (k + 1) := by rw [pow_succ]; ring

/-- Real version of `quad_le`. -/
private lemma quad_le_real (i : ℕ) : ((i : ℝ) + 1) * ((i : ℝ) + 2) ≤ 4 * (3 : ℝ) ^ i := by
  have h := quad_le i
  have h2 : (((i + 1) * (i + 2) : ℕ) : ℝ) ≤ ((4 * 3 ^ i : ℕ) : ℝ) := by exact_mod_cast h
  simpa using h2

/-- The `i`-th coefficient of the difference series, after the substitution `m = i+1`,
is dominated by `4 r (3/4)^i`. -/
private lemma acoeff_shift_le (r : ℝ) (hr : 0 ≤ r) (hr1 : r ≤ 1 / 2) (i : ℕ) :
    acoeff r (i + 1) ≤ 4 * r * (3/4)^i := by
  have hr_le1 : r ≤ 1 := by linarith
  have hcast : acoeff r (i+1)
      = ((i:ℝ)+1) * ((i:ℝ)+2) * r ^ ((i+1)*(i+2) - 1) := by
    simp only [acoeff]
    have : (i+1:ℕ) + 1 = i + 2 := by omega
    rw [this]
    push_cast
    ring
  rw [hcast]
  have hE : 2*i + 1 ≤ (i+1)*(i+2) - 1 := by
    have hlt : 2*i + 1 < (i+1)*(i+2) := by
      have h2 : 2*(i+1) ≤ (i+1)*(i+2) := by
        rw [Nat.mul_comm 2 (i+1)]
        exact Nat.mul_le_mul_left (i+1) (by omega : 2 ≤ i+2)
      omega
    exact Nat.le_sub_one_of_lt hlt
  have hpow1 : r ^ ((i+1)*(i+2) - 1) ≤ r ^ (2*i+1) :=
    pow_le_pow_of_le_one hr hr_le1 hE
  have hpow2 : r ^ (2*i+1) = r * (r^2)^i := by
    rw [show 2*i+1 = 1 + 2*i by omega, pow_add, pow_one, ← pow_mul]
  have hpow3 : (r^2)^i ≤ ((1/4):ℝ)^i :=
    pow_le_pow_left₀ (sq_nonneg r) (by nlinarith) i
  have hstep : r ^ ((i+1)*(i+2) - 1) ≤ r * (1/4)^i := by
    rw [hpow2] at hpow1
    exact hpow1.trans (mul_le_mul_of_nonneg_left hpow3 hr)
  have hcoef : ((i:ℝ)+1)*((i:ℝ)+2) ≤ 4*(3:ℝ)^i := quad_le_real i
  calc ((i:ℝ)+1)*((i:ℝ)+2) * r ^ ((i+1)*(i+2) - 1)
      ≤ ((i:ℝ)+1)*((i:ℝ)+2) * (r * (1/4)^i) :=
        mul_le_mul_of_nonneg_left hstep (by positivity)
    _ ≤ 4*(3:ℝ)^i * (r * (1/4)^i) :=
        mul_le_mul_of_nonneg_right hcoef (by positivity)
    _ = 4 * r * (3/4)^i := by
        rw [show (4:ℝ)*(3:ℝ)^i*(r*(1/4)^i) = 4*r*((3:ℝ)^i*(1/4)^i) by ring, ← mul_pow]
        norm_num

/-- The coefficient series `∑ m(m+1) r^{m(m+1)-1}` is summable for `0 ≤ r ≤ 1/2`. -/
private lemma acoeff_summable (r : ℝ) (hr : 0 ≤ r) (hr1 : r ≤ 1 / 2) : Summable (acoeff r) := by
  have hgeo : Summable (fun i : ℕ => (3/4:ℝ)^i) :=
    summable_geometric_of_norm_lt_one (by rw [Real.norm_eq_abs]; norm_num)
  have hs : Summable (fun i : ℕ => acoeff r (i+1)) := by
    apply Summable.of_nonneg_of_le (f := fun i : ℕ => 4 * r * (3/4)^i)
    · intro i; simp only [acoeff]; positivity
    · intro i; exact acoeff_shift_le r hr hr1 i
    · exact hgeo.mul_left (4*r)
  exact (summable_nat_add_iff 1).1 hs

/-- The coefficient series is bounded by `16 r` on `0 ≤ r ≤ 1/2`. -/
private lemma acoeff_sum_le (r : ℝ) (hr : 0 ≤ r) (hr1 : r ≤ 1 / 2) :
    ∑' m : ℕ, acoeff r m ≤ 16 * r := by
  have hgeo : Summable (fun i : ℕ => (3/4:ℝ)^i) :=
    summable_geometric_of_norm_lt_one (by rw [Real.norm_eq_abs]; norm_num)
  have hs : Summable (fun i : ℕ => acoeff r (i+1)) :=
    (summable_nat_add_iff 1).2 (acoeff_summable r hr hr1)
  have h0 : acoeff r 0 = 0 := by simp [acoeff]
  have hsplit : ∑' m : ℕ, acoeff r m = ∑' i : ℕ, acoeff r (i+1) := by
    have := (acoeff_summable r hr hr1).sum_add_tsum_nat_add 1
    rw [Finset.sum_range_one, h0, zero_add] at this
    exact this.symm
  have hle : ∑' i : ℕ, acoeff r (i+1) ≤ ∑' i : ℕ, 4 * r * (3/4)^i :=
    hs.tsum_le_tsum (fun i => acoeff_shift_le r hr hr1 i) (hgeo.mul_left (4*r))
  have hval : ∑' i : ℕ, 4 * r * (3/4)^i = 16 * r := by
    rw [tsum_mul_left, tsum_geometric_of_norm_lt_one (by rw [Real.norm_eq_abs]; norm_num)]
    ring
  rw [hsplit]
  calc ∑' i : ℕ, acoeff r (i+1) ≤ ∑' i : ℕ, 4 * r * (3/4)^i := hle
    _ = 16 * r := hval

theorem aSeries_sub_bound (r : ℝ) (hr : 0 < r) (hr1 : r ≤ 1 / 2) (x y : ℂ)
    (hx : ‖x‖ ≤ r) (hy : ‖y‖ ≤ r) :
    ‖Work.Rigidity.aSeries x - Work.Rigidity.aSeries y‖ ≤ 16 * r * ‖x - y‖ := by
  have hr0 : 0 ≤ r := le_of_lt hr
  have hr_le1 : r ≤ 1 := by linarith
  have hmono : ∀ m : ℕ, r ^ (m*(m+1)) ≤ r ^ m := by
    intro m
    have hm : m ≤ m*(m+1) := by
      have h := Nat.mul_le_mul_left m (show 1 ≤ m + 1 by omega)
      rwa [Nat.mul_one] at h
    exact pow_le_pow_of_le_one hr0 hr_le1 hm
  have hgeo : Summable (fun m : ℕ => r^m) :=
    summable_geometric_of_norm_lt_one (by rw [Real.norm_eq_abs, abs_of_nonneg hr0]; linarith)
  have hxs : Summable (fun m : ℕ => x ^ (m*(m+1))) := by
    apply Summable.of_norm_bounded (g := fun m : ℕ => r^m) hgeo
    intro m
    rw [norm_pow]
    exact le_trans (pow_le_pow_left₀ (norm_nonneg x) hx _) (hmono m)
  have hys : Summable (fun m : ℕ => y ^ (m*(m+1))) := by
    apply Summable.of_norm_bounded (g := fun m : ℕ => r^m) hgeo
    intro m
    rw [norm_pow]
    exact le_trans (pow_le_pow_left₀ (norm_nonneg y) hy _) (hmono m)
  have htermx : ∀ m : ℕ, ‖x ^ (m*(m+1))‖ ≤ r^m := by
    intro m; rw [norm_pow]
    exact le_trans (pow_le_pow_left₀ (norm_nonneg x) hx _) (hmono m)
  have htermy : ∀ m : ℕ, ‖y ^ (m*(m+1))‖ ≤ r^m := by
    intro m; rw [norm_pow]
    exact le_trans (pow_le_pow_left₀ (norm_nonneg y) hy _) (hmono m)
  have hnorm : Summable (fun m : ℕ => ‖x^(m*(m+1)) - y^(m*(m+1))‖) := by
    apply Summable.of_nonneg_of_le (f := fun m : ℕ => 2*r^m)
    · intro m; positivity
    · intro m
      calc ‖x^(m*(m+1)) - y^(m*(m+1))‖ ≤ ‖x^(m*(m+1))‖ + ‖y^(m*(m+1))‖ := norm_sub_le _ _
        _ ≤ r^m + r^m := add_le_add (htermx m) (htermy m)
        _ = 2*r^m := by ring
    · exact hgeo.mul_left 2
  have hdiff : aSeries x - aSeries y = ∑' m : ℕ, (x^(m*(m+1)) - y^(m*(m+1))) := by
    simp only [aSeries_apply]
    exact (hxs.tsum_sub hys).symm
  calc ‖aSeries x - aSeries y‖
      = ‖∑' m : ℕ, (x^(m*(m+1)) - y^(m*(m+1)))‖ := by rw [hdiff]
    _ ≤ ∑' m : ℕ, ‖x^(m*(m+1)) - y^(m*(m+1))‖ := norm_tsum_le_tsum_norm hnorm
    _ ≤ ∑' m : ℕ, acoeff r m * ‖x - y‖ := by
          apply Summable.tsum_le_tsum
          · intro m
            have := norm_pow_sub_pow_le r hr0 x y hx hy (m*(m+1))
            simpa [acoeff, Nat.cast_mul, Nat.cast_add, Nat.cast_one] using this
          · exact hnorm
          · exact (acoeff_summable r hr0 hr1).mul_right _
    _ = (∑' m : ℕ, acoeff r m) * ‖x - y‖ := by rw [tsum_mul_right]
    _ ≤ (16*r) * ‖x - y‖ := mul_le_mul_of_nonneg_right (acoeff_sum_le r hr0 hr1) (norm_nonneg _)
    _ = 16 * r * ‖x - y‖ := by ring

end Work.Rigidity
