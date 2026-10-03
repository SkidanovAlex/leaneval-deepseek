import Mathlib

set_option maxHeartbeats 1000000

namespace Work.Repel.Koebe

/-- **Geometric growth from summability at every radius.**  If a coefficient sequence `c` satisfies
`∑_k ‖c k‖ / ρ ^ k < ∞` for every `ρ > 1`, then for every `r > 1` the series
`∑_m m * ‖c m‖² / r ^ (2m)` is summable.

Proof route: fix `1 < ρ < r` and let `S := ∑' k, ‖c k‖ / ρ ^ k < ∞`; since all terms are
nonnegative, `‖c m‖ / ρ ^ m ≤ S` for every `m`, hence `m * ‖c m‖² / r ^ (2m) ≤ S² * m * ((ρ/r)²)^m`,
which is summable because `(ρ/r)² < 1`
(`summable_pow_mul_geometric_of_norm_lt_one` + `Summable.mul_left`), and apply
`Summable.of_nonneg_of_le`. -/
theorem summable_mul_normSq_div {c : ℕ → ℂ}
    (hc : ∀ ρ : ℝ, 1 < ρ → Summable (fun k : ℕ => ‖c k‖ / ρ ^ k)) {r : ℝ} (hr : 1 < r) :
    Summable (fun m : ℕ => (m : ℝ) * ‖c m‖ ^ 2 / r ^ (2 * m)) := by
  -- pick an auxiliary radius strictly between `1` and `r`
  obtain ⟨ρ, hρ1, hρr⟩ := exists_between hr
  have hρpos : 0 < ρ := lt_trans zero_lt_one hρ1
  have hrpos : 0 < r := lt_trans zero_lt_one hr
  have hS := hc ρ hρ1
  set S : ℝ := ∑' k, ‖c k‖ / ρ ^ k with hSdef
  have hSnn : 0 ≤ S := tsum_nonneg fun k => by positivity
  -- each nonnegative term is bounded by the total sum
  have hle_S : ∀ m : ℕ, ‖c m‖ / ρ ^ m ≤ S :=
    fun m => hS.le_tsum m (fun j hj => by positivity)
  -- the ratio `(ρ/r)²` is strictly less than one, so `m * ((ρ/r)²)^m` is summable
  have hratio_lt : (ρ / r) ^ 2 < 1 := by
    have h1 : ρ / r < 1 := (div_lt_one hrpos).mpr hρr
    have h2 : 0 ≤ ρ / r := div_nonneg hρpos.le hrpos.le
    nlinarith [sq_nonneg (ρ / r)]
  have hgeom : Summable (fun m : ℕ => (m : ℝ) * ((ρ / r) ^ 2) ^ m) := by
    have h := summable_pow_mul_geometric_of_norm_lt_one (R := ℝ) 1 (r := (ρ / r) ^ 2) (by
      rw [Real.norm_eq_abs, abs_of_nonneg (sq_nonneg _)]; exact hratio_lt)
    simpa using h
  have hmain : Summable (fun m : ℕ => S ^ 2 * ((m : ℝ) * ((ρ / r) ^ 2) ^ m)) :=
    hgeom.mul_left (S ^ 2)
  refine Summable.of_nonneg_of_le (fun m => by positivity) (fun m => ?_) hmain
  -- the exact algebraic identity `‖c m‖² / r ^ (2m) = (‖c m‖/ρ^m)² * ((ρ/r)²)^m`
  have hkey : ∀ m : ℕ, ‖c m‖ ^ 2 / r ^ (2 * m)
      = (‖c m‖ / ρ ^ m) ^ 2 * ((ρ / r) ^ 2) ^ m := by
    intro m
    have h1 : (‖c m‖ / ρ ^ m) ^ 2 = ‖c m‖ ^ 2 / ρ ^ (2 * m) := by
      rw [div_pow, ← pow_mul, mul_comm m 2]
    have h2 : ((ρ / r) ^ 2) ^ m = ρ ^ (2 * m) / r ^ (2 * m) := by
      rw [← pow_mul, div_pow]
    rw [h1, h2]
    field_simp
  rw [mul_div_assoc, hkey m]
  have ht : (‖c m‖ / ρ ^ m) ^ 2 ≤ S ^ 2 := by
    have ht0 : 0 ≤ ‖c m‖ / ρ ^ m := by positivity
    nlinarith [hle_S m, ht0, hSnn]
  calc (m : ℝ) * ((‖c m‖ / ρ ^ m) ^ 2 * ((ρ / r) ^ 2) ^ m)
      = (m : ℝ) * (‖c m‖ / ρ ^ m) ^ 2 * ((ρ / r) ^ 2) ^ m := by ring
    _ ≤ (m : ℝ) * S ^ 2 * ((ρ / r) ^ 2) ^ m := by
        apply mul_le_mul_of_nonneg_right _ (by positivity)
        exact mul_le_mul_of_nonneg_left ht (Nat.cast_nonneg m)
    _ = S ^ 2 * ((m : ℝ) * ((ρ / r) ^ 2) ^ m) := by ring

end Work.Repel.Koebe
