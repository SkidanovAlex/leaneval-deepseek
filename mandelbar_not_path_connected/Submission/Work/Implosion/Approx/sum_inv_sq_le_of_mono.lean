import Mathlib

-- Lean v4.35.0-rc3 / Mathlib 5e0c4e5 made `isDefEq` respect transparency when unifying instances; with it,
-- `ZMod.instField` and `ZMod.commRing` (and `Neg (ZMod p)` via `SubtractionMonoid`) no longer unify, which
-- breaks `ring`/`rw`/module-instance search on `ZMod p`. Restore the v4.34 behaviour for this file.
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false


namespace Work.Implosion.Approx

/-- Elementary inequality: for `0 < c`, `0 < a` one has
`1/(a+c)² ≤ (1/c)·(1/a − 1/(a+c))`.  Indeed the right hand side equals `1/(a(a+c))`
and `a ≤ a + c`. -/
private lemma inv_sq_succ_le (a c : ℝ) (hc : 0 < c) (ha : 0 < a) :
    1 / (a + c) ^ 2 ≤ (1 / c) * (1 / a - 1 / (a + c)) := by
  have hac : 0 < a + c := by linarith
  have h1 : (1 / c) * (1 / a - 1 / (a + c)) = 1 / (a * (a + c)) := by
    field_simp
    ring
  rw [h1]
  exact one_div_le_one_div_of_le (mul_pos ha hac) (by nlinarith [hc, ha])

/-- Anti-tonicity of `t ↦ 1/t²` on the positive reals. -/
private lemma one_div_sq_antitone (a b : ℝ) (ha : 0 < a) (hab : a ≤ b) :
    1 / b ^ 2 ≤ 1 / a ^ 2 :=
  one_div_le_one_div_of_le (pow_pos ha 2) (pow_le_pow_left₀ (le_of_lt ha) hab 2)

/-- The model geometric bound: with `u_j = R + j·c` the sum of the `1/u_j²` over
`j = 0, …, n` is bounded by `1/R² + 1/(cR)`, uniformly in `n`.  The proof telescopes
`1/u_{j+1}² ≤ (1/c)(1/u_j − 1/u_{j+1})`. -/
private lemma geom_sum_inv_sq_le (c R : ℝ) (hc : 0 < c) (hR : 0 < R) (n : ℕ) :
    ∑ j ∈ Finset.range (n + 1), (1 / (R + (j : ℝ) * c) ^ 2 : ℝ) ≤ 1 / R ^ 2 + 1 / (c * R) := by
  rw [Finset.sum_range_succ']
  have hf0 : (1 / (R + ((0 : ℕ) : ℝ) * c) ^ 2 : ℝ) = 1 / R ^ 2 := by norm_num
  rw [hf0]
  have hpt : ∀ j ∈ Finset.range n,
      (1 / (R + ((j + 1 : ℕ) : ℝ) * c) ^ 2 : ℝ)
        ≤ (1 / c) * (1 / (R + (j : ℝ) * c) - 1 / (R + ((j + 1 : ℕ) : ℝ) * c)) := by
    intro j _
    have hcast : R + ((j + 1 : ℕ) : ℝ) * c = R + (j : ℝ) * c + c := by push_cast; ring
    rw [hcast]
    exact inv_sq_succ_le (R + (j : ℝ) * c) c hc (by positivity)
  have htel : ∑ j ∈ Finset.range n,
        ((1 / (R + (j : ℝ) * c)) - 1 / (R + ((j + 1 : ℕ) : ℝ) * c))
          = 1 / R - 1 / (R + (n : ℝ) * c) := by
    have hsub := Finset.sum_range_sub (fun j : ℕ => (1 / (R + (j : ℝ) * c) : ℝ)) n
    have h2 : ∑ j ∈ Finset.range n,
          ((1 / (R + (j : ℝ) * c)) - 1 / (R + ((j + 1 : ℕ) : ℝ) * c))
        = - ∑ j ∈ Finset.range n,
            ((1 / (R + ((j + 1 : ℕ) : ℝ) * c)) - (1 / (R + (j : ℝ) * c))) := by
      rw [← Finset.sum_neg_distrib]
      apply Finset.sum_congr rfl
      intro j _
      ring
    rw [h2, hsub]
    simp only [Nat.cast_zero, zero_mul, add_zero]
    ring
  calc ∑ j ∈ Finset.range n, (1 / (R + ((j + 1 : ℕ) : ℝ) * c) ^ 2 : ℝ) + 1 / R ^ 2
      ≤ (∑ j ∈ Finset.range n,
            (1 / c) * (1 / (R + (j : ℝ) * c) - 1 / (R + ((j + 1 : ℕ) : ℝ) * c)))
          + 1 / R ^ 2 :=
        add_le_add (Finset.sum_le_sum hpt) le_rfl
    _ = (1 / c) * ∑ j ∈ Finset.range n,
            (1 / (R + (j : ℝ) * c) - 1 / (R + ((j + 1 : ℕ) : ℝ) * c)) + 1 / R ^ 2 := by
        rw [Finset.mul_sum]
    _ = (1 / c) * (1 / R - 1 / (R + (n : ℝ) * c)) + 1 / R ^ 2 := by rw [htel]
    _ ≤ 1 / (c * R) + 1 / R ^ 2 := by
        have hmul : (1 / c) * (1 / R - 1 / (R + (n : ℝ) * c)) ≤ (1 / c) * (1 / R) := by
          apply mul_le_mul_of_nonneg_left _ (by positivity)
          have : 0 ≤ 1 / (R + (n : ℝ) * c) := by positivity
          linarith
        have hval : (1 / c) * (1 / R) = 1 / (c * R) := by rw [div_mul_div_comm, one_mul]
        linarith [hmul, hval]
    _ = 1 / R ^ 2 + 1 / (c * R) := by ring

/-- A sequence that increases by at least `c` at every step stays above the
arithmetic progression starting at `x 0`. -/
private lemma lower_of_increasing (x : ℕ → ℝ) (c : ℝ) (n : ℕ)
    (h : ∀ k : ℕ, k < n → x k + c ≤ x (k + 1)) :
    ∀ k : ℕ, k ≤ n → x 0 + (k : ℝ) * c ≤ x k := by
  intro k
  induction k with
  | zero => intro _; simp
  | succ k ih =>
    intro hk
    have hkn : k < n := Nat.lt_of_succ_le hk
    have h1 := h k hkn
    have h2 := ih (Nat.le_of_lt hkn)
    have hcast : ((k + 1 : ℕ) : ℝ) = (k : ℝ) + 1 := by push_cast; ring
    rw [hcast]
    have hcast2 : ((k : ℝ) + 1) * c = (k : ℝ) * c + c := by ring
    rw [hcast2]
    linarith

/-- A sequence that decreases by at least `c` at every step stays above the
arithmetic progression ending at `x n`. -/
private lemma lower_of_decreasing (x : ℕ → ℝ) (c : ℝ) (n : ℕ)
    (h : ∀ k : ℕ, k < n → x (k + 1) ≤ x k - c) :
    ∀ d : ℕ, d ≤ n → x n + (d : ℝ) * c ≤ x (n - d) := by
  intro d
  induction d with
  | zero => intro _; simp
  | succ d ih =>
    intro hd
    have hdn : d ≤ n := Nat.le_of_succ_le hd
    have hlt : n - (d + 1) < n := by omega
    have hstep := h (n - (d + 1)) hlt
    have heq : n - (d + 1) + 1 = n - d := by omega
    rw [heq] at hstep
    have hprev := ih hdn
    have hcast : ((d + 1 : ℕ) : ℝ) = (d : ℝ) + 1 := by push_cast; ring
    rw [hcast]
    have hcast2 : ((d : ℝ) + 1) * c = (d : ℝ) * c + c := by ring
    rw [hcast2]
    linarith

/-- **Sum of inverse squares along a monotone sequence.**  If `x` runs through
`x 0, …, x n`, all of them `≥ R > 0`, and consecutive terms differ by at least `c > 0`
in a fixed direction, then `∑_{k=0}^n 1/(x k)² ≤ 1/R² + 1/(cR)`.  The bound is
uniform in `n`: the summands are dominated by the arithmetic progression
`R, R+c, R+2c, …` (reversed in the decreasing case), whose inverse squares
telescope. -/
theorem sum_inv_sq_le_of_mono (x : ℕ → ℝ) (c R : ℝ) (n : ℕ) (hc : 0 < c) (hR : 0 < R)
    (hmono : (∀ k : ℕ, k < n → x (k+1) ≤ x k - c) ∨ (∀ k : ℕ, k < n → x k + c ≤ x (k+1)))
    (hbound : ∀ k : ℕ, k ≤ n → R ≤ x k) :
    ∑ k ∈ Finset.range (n+1), (1 / (x k)^2) ≤ 1 / R^2 + 1 / (c * R) := by
  have hgeom := geom_sum_inv_sq_le c R hc hR n
  have hone := one_div_sq_antitone
  rcases hmono with hdec | hinc
  · -- decreasing: `x k` dominates `R + (n-k)·c`
    have hlow : ∀ k : ℕ, k ≤ n → R + ((n - k : ℕ) : ℝ) * c ≤ x k := by
      intro k hk
      have h1 := lower_of_decreasing x c n hdec (n - k) (Nat.sub_le n k)
      rw [Nat.sub_sub_self hk] at h1
      have h2 : R ≤ x n := hbound n le_rfl
      linarith
    have hpt : ∀ k ∈ Finset.range (n + 1),
        1 / (x k) ^ 2 ≤ (1 / (R + ((n - k : ℕ) : ℝ) * c) ^ 2 : ℝ) := by
      intro k hk
      exact hone _ _ (by positivity) (hlow k (Nat.lt_succ_iff.mp (Finset.mem_range.mp hk)))
    calc ∑ k ∈ Finset.range (n + 1), 1 / (x k) ^ 2
        ≤ ∑ k ∈ Finset.range (n + 1), (1 / (R + ((n - k : ℕ) : ℝ) * c) ^ 2 : ℝ) :=
          Finset.sum_le_sum hpt
      _ = ∑ j ∈ Finset.range (n + 1), (1 / (R + (j : ℝ) * c) ^ 2 : ℝ) := by
          have h := Finset.sum_range_reflect (fun j => (1 / (R + (j : ℝ) * c) ^ 2 : ℝ)) (n + 1)
          simpa only [Nat.add_sub_cancel] using h
      _ ≤ 1 / R ^ 2 + 1 / (c * R) := hgeom
  · -- increasing: `x k` dominates `R + k·c`
    have hlow : ∀ k : ℕ, k ≤ n → R + (k : ℝ) * c ≤ x k := by
      intro k hk
      have h1 := lower_of_increasing x c n hinc k hk
      have h2 : R ≤ x 0 := hbound 0 (Nat.zero_le n)
      linarith
    have hpt : ∀ k ∈ Finset.range (n + 1),
        1 / (x k) ^ 2 ≤ (1 / (R + (k : ℝ) * c) ^ 2 : ℝ) := by
      intro k hk
      exact hone _ _ (by positivity) (hlow k (Nat.lt_succ_iff.mp (Finset.mem_range.mp hk)))
    calc ∑ k ∈ Finset.range (n + 1), 1 / (x k) ^ 2
        ≤ ∑ k ∈ Finset.range (n + 1), (1 / (R + (k : ℝ) * c) ^ 2 : ℝ) :=
          Finset.sum_le_sum hpt
      _ ≤ 1 / R ^ 2 + 1 / (c * R) := hgeom

end Work.Implosion.Approx
