import Mathlib

namespace Work.RHContract.Helper

/-- Reindexing: a sum over `Icc 1 e` is a sum over `range e` of the shifted terms. -/
lemma sum_Icc_one_eq_sum_range (f : ℕ → ℝ) (e : ℕ) :
    ∑ k ∈ Finset.Icc 1 e, f k = ∑ i ∈ Finset.range e, f (i + 1) := by
  induction e with
  | zero => simp
  | succ n ih =>
    rw [Finset.sum_Icc_succ_top (by omega) f, ih, Finset.sum_range_succ]

/-- Tail bound for the logarithm series: for `0 ≤ x < 1`,
`-log(1-x) - ∑_{k=1}^{e} x^k/k ≤ x^{e+1}/((e+1)(1-x))`. -/
lemma log_tail_le (x : ℝ) (hx0 : 0 ≤ x) (hx1 : x < 1) (e : ℕ) :
    -Real.log (1 - x) - ∑ k ∈ Finset.Icc 1 e, x ^ k / (k : ℝ)
      ≤ x ^ (e + 1) / (((e : ℝ) + 1) * (1 - x)) := by
  have habs : |x| < 1 := abs_lt.mpr ⟨by linarith, hx1⟩
  have hlog := Real.hasSum_pow_div_log_of_abs_lt_one habs
  set g : ℕ → ℝ := fun n => x ^ (n + 1) / ((n : ℝ) + 1) with hgdef
  have hlog_g : HasSum g (-Real.log (1 - x)) := by simpa only [hgdef] using hlog
  have hg_sum : Summable g := hlog_g.summable
  have hsplit := hg_sum.sum_add_tsum_nat_add e
  have htsum : ∑' i, g i = -Real.log (1 - x) := hlog_g.tsum_eq
  have hreindex : ∑ i ∈ Finset.range e, g i = ∑ k ∈ Finset.Icc 1 e, x ^ k / (k : ℝ) := by
    rw [sum_Icc_one_eq_sum_range (fun k => x ^ k / (k : ℝ)) e]
    apply Finset.sum_congr rfl
    intro i _
    simp only [hgdef]
    push_cast
    ring
  set c : ℝ := x ^ (e + 1) / ((e : ℝ) + 1) with hcdef
  have hterm : ∀ i : ℕ, g (i + e) ≤ c * x ^ i := by
    intro i
    have hxe : (0 : ℝ) ≤ x ^ (e + 1) := pow_nonneg hx0 _
    have hxi : (0 : ℝ) ≤ x ^ i := pow_nonneg hx0 _
    have hpow : x ^ (i + e + 1) = x ^ (e + 1) * x ^ i := by
      rw [show i + e + 1 = (e + 1) + i by omega, pow_add]
    have hden : ((e : ℝ) + 1) ≤ ((i + e + 1 : ℕ) : ℝ) := by
      rw [← Nat.cast_add_one]
      exact_mod_cast (show e + 1 ≤ i + e + 1 by omega)
    have hdenpos : (0 : ℝ) < (e : ℝ) + 1 := by positivity
    have hcast : (((i + e : ℕ) : ℝ) + 1) = ((i + e + 1 : ℕ) : ℝ) :=
      (Nat.cast_add_one (i + e)).symm
    simp only [hgdef, hcdef]
    rw [hpow, hcast, div_mul_eq_mul_div]
    exact div_le_div_of_nonneg_left (mul_nonneg hxe hxi) hdenpos hden
  have hg_tail : Summable (fun i => g (i + e)) :=
    hg_sum.comp_injective (fun a b h => Nat.add_right_cancel h)
  have hgeom_sum : Summable (fun i : ℕ => x ^ i) := summable_geometric_of_lt_one hx0 hx1
  have hh_sum : Summable (fun i : ℕ => c * x ^ i) := hgeom_sum.mul_left c
  have hle : ∑' i, g (i + e) ≤ ∑' i, c * x ^ i :=
    Summable.tsum_le_tsum hterm hg_tail hh_sum
  have hLHS : -Real.log (1 - x) - ∑ k ∈ Finset.Icc 1 e, x ^ k / (k : ℝ)
      = ∑' i, g (i + e) := by
    rw [← htsum, ← hreindex]
    linarith [hsplit]
  rw [hLHS]
  calc ∑' i, g (i + e) ≤ ∑' i, c * x ^ i := hle
    _ = c * (1 - x)⁻¹ := by
        rw [Summable.tsum_mul_left c hgeom_sum, tsum_geometric_of_lt_one hx0 hx1]
    _ = x ^ (e + 1) / (((e : ℝ) + 1) * (1 - x)) := by
        rw [hcdef, div_eq_mul_inv, div_eq_mul_inv, mul_inv, mul_assoc]

theorem primeTailSummand_le (p e : ℕ) (hp : 2 ≤ p) :
    -Real.log (1 - 1 / (p : ℝ)) - ∑ k ∈ Finset.Icc 1 e, 1 / ((k : ℝ) * (p : ℝ) ^ k)
      ≤ (p : ℝ) ^ (-((e : ℝ) + 1)) / (((e : ℝ) + 1) * (1 - 1 / (p : ℝ))) := by
  set x : ℝ := 1 / (p : ℝ) with hxdef
  have hp0 : (0 : ℝ) < (p : ℝ) := by exact_mod_cast (show 0 < p by omega)
  have hp1 : (1 : ℝ) < (p : ℝ) := by exact_mod_cast (show 1 < p by omega)
  have hx0 : 0 ≤ x := by rw [hxdef]; positivity
  have hx1 : x < 1 := by
    rw [hxdef, div_lt_one hp0]
    exact hp1
  have hkey := log_tail_le x hx0 hx1 e
  have hsum_eq : ∑ k ∈ Finset.Icc 1 e, x ^ k / (k : ℝ)
      = ∑ k ∈ Finset.Icc 1 e, 1 / ((k : ℝ) * (p : ℝ) ^ k) := by
    apply Finset.sum_congr rfl
    intro k _
    rw [hxdef, one_div_pow, div_div, mul_comm]
  have hrpow : (p : ℝ) ^ (-((e : ℝ) + 1)) = x ^ (e + 1) := by
    have hcast : ((e : ℝ) + 1) = ((e + 1 : ℕ) : ℝ) := (Nat.cast_add_one e).symm
    rw [hcast, Real.rpow_neg hp0.le, Real.rpow_natCast, hxdef, one_div_pow, inv_eq_one_div]
  have hgoal_eq : x ^ (e + 1) / (((e : ℝ) + 1) * (1 - x))
      = (p : ℝ) ^ (-((e : ℝ) + 1)) / (((e : ℝ) + 1) * (1 - 1 / (p : ℝ))) := by
    rw [← hrpow, hxdef]
  rw [hgoal_eq, hsum_eq, hxdef] at hkey
  exact hkey

end Work.RHContract.Helper
