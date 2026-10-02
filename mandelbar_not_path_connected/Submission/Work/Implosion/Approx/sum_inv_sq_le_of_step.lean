import Mathlib

-- Lean v4.35.0-rc3 / Mathlib 5e0c4e5 made `isDefEq` respect transparency when unifying instances; with it,
-- `ZMod.instField` and `ZMod.commRing` (and `Neg (ZMod p)` via `SubtractionMonoid`) no longer unify, which
-- breaks `ring`/`rw`/module-instance search on `ZMod p`. Restore the v4.34 behaviour for this file.
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false


namespace Work.Implosion.Approx

/-- A pure inequality: if `0 < a`, `0 < b`, `b ≤ a - c` with `c > 0`, then
`1/a² ≤ (1/b - 1/a)/c`. -/
private lemma inv_sq_le_sub_inv (a b c : ℝ) (hc : 0 < c) (ha : 0 < a) (hb : 0 < b)
    (h : b ≤ a - c) : 1 / a ^ 2 ≤ (1 / b - 1 / a) / c := by
  have h1 : c ≤ a - b := by linarith
  have h2 : b ≤ a := by linarith
  rw [div_sub_div _ _ (ne_of_gt hb) (ne_of_gt ha)]
  rw [div_div]
  rw [le_div_iff₀ (by positivity : (0:ℝ) < b * a * c)]
  have hrw : 1 / a ^ 2 * (b * a * c) = b * a * c / a ^ 2 := by ring
  rw [hrw]
  rw [div_le_iff₀ (by positivity : (0:ℝ) < a ^ 2)]
  have hfinal : b * a * c ≤ (a - b) * a ^ 2 := by
    calc b * a * c = a * (b * c) := by ring
      _ ≤ a * (a * (a - b)) := mul_le_mul_of_nonneg_left (by
            calc b * c ≤ b * (a - b) := mul_le_mul_of_nonneg_left h1 (le_of_lt hb)
              _ ≤ a * (a - b) := mul_le_mul_of_nonneg_right h2 (by linarith)) (le_of_lt ha)
      _ = (a - b) * a ^ 2 := by ring
  linarith [hfinal]

theorem sum_inv_sq_le_of_step (x : ℕ → ℝ) (c R : ℝ) (n : ℕ) (hc : 0 < c) (hR : 0 < R)
    (hstep : ∀ k : ℕ, k < n → x (k+1) ≤ x k - c) (hn : R ≤ x n) :
    ∑ k ∈ Finset.range n, (1 / (x (k+1))^2) ≤ 1 / R^2 + 1 / (c * R) := by
  -- Downward lower bound along the recursion.
  have hkey : ∀ d, d ≤ n → R + (d : ℝ) * c ≤ x (n - d) := by
    intro d
    induction d with
    | zero => intro _; simpa using hn
    | succ d ih =>
      intro hd
      have hdle : d ≤ n := Nat.le_of_succ_le hd
      have ih' := ih hdle
      have hlt : n - (d + 1) < n := by omega
      have hs := hstep (n - (d + 1)) hlt
      have heq : n - (d + 1) + 1 = n - d := by omega
      rw [heq] at hs
      push_cast
      linarith
  have hxR : ∀ j, j ≤ n → R ≤ x j := by
    intro j hj
    have h := hkey (n - j) (Nat.sub_le n j)
    rw [Nat.sub_sub_self hj] at h
    have hnn : (0:ℝ) ≤ ((n - j : ℕ) : ℝ) * c :=
      mul_nonneg (Nat.cast_nonneg _) (le_of_lt hc)
    linarith
  have hxpos : ∀ j, j ≤ n → 0 < x j := fun j hj => lt_of_lt_of_le hR (hxR j hj)
  rcases Nat.eq_zero_or_pos n with hn0 | hnpos
  · subst hn0
    simp only [Finset.range_zero, Finset.sum_empty]
    positivity
  · obtain ⟨m, hm⟩ : ∃ m, n = m + 1 := ⟨n - 1, by omega⟩
    subst hm
    rw [Finset.sum_range_succ]
    have hlast : 1 / (x (m + 1))^2 ≤ 1 / R^2 := by
      have hx1 : R ≤ x (m + 1) := hxR (m + 1) (by omega)
      refine one_div_le_one_div_of_le (by positivity : (0:ℝ) < R ^ 2) ?_
      exact pow_le_pow_left₀ (le_of_lt hR) hx1 2
    have hsum : ∑ k ∈ Finset.range m, 1 / (x (k+1))^2 ≤ 1 / (c * R) := by
      have htel : ∑ k ∈ Finset.range m, 1 / (x (k+1))^2
            ≤ (1 / x (m+1)) / c - (1 / x (0+1)) / c := by
        calc ∑ k ∈ Finset.range m, 1 / (x (k+1))^2
            ≤ ∑ k ∈ Finset.range m, ((1 / x (k+1+1)) / c - (1 / x (k+1)) / c) := by
              apply Finset.sum_le_sum
              intro k hk
              have hkm : k < m := Finset.mem_range.mp hk
              have ha : 0 < x (k+1) := hxpos (k+1) (by omega)
              have hb : 0 < x (k+1+1) := hxpos (k+1+1) (by omega)
              have hst : x (k+1+1) ≤ x (k+1) - c := hstep (k+1) (by omega)
              have key := inv_sq_le_sub_inv (x (k+1)) (x (k+1+1)) c hc ha hb hst
              rw [sub_div] at key
              exact key
          _ = (1 / x (m+1)) / c - (1 / x (0+1)) / c :=
              Finset.sum_range_sub (fun j => (1 / x (j+1)) / c) m
      have hum : (1 / x (m + 1)) / c ≤ 1 / (c * R) := by
        have hx1 : R ≤ x (m + 1) := hxR (m + 1) (by omega)
        have hrw : (1 / x (m + 1)) / c = 1 / (x (m + 1) * c) := by rw [div_div]
        rw [hrw]
        have hle : 1 / (x (m+1) * c) ≤ 1 / (R * c) :=
          one_div_le_one_div_of_le (by positivity : (0:ℝ) < R * c)
            (mul_le_mul_of_nonneg_right hx1 (le_of_lt hc))
        rwa [mul_comm R c] at hle
      have h0 : 0 ≤ (1 / x (0 + 1)) / c := by
        have hx : 0 < x (0 + 1) := hxpos 1 (by omega)
        positivity
      linarith [htel, hum, h0]
    linarith [hlast, hsum]

end Work.Implosion.Approx
