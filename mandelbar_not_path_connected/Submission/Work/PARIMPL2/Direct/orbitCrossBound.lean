import Mathlib
import Submission.Work.PARIMPL2.Direct.inbound_bounds
import Submission.Work.PARIMPL2.Direct.sum_lam2_div_sin_sq_le

-- Lean v4.35.0-rc3 / Mathlib 5e0c4e5 made `isDefEq` respect transparency when unifying instances; with it,
-- `ZMod.instField` and `ZMod.commRing` (and `Neg (ZMod p)` via `SubtractionMonoid`) no longer unify, which
-- breaks `ring`/`rw`/module-instance search on `ZMod p`. Restore the v4.34 behaviour for this file.
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false


set_option maxHeartbeats 2000000

namespace Work.PARIMPL2.Direct

/-! ## Elementary telescoping tools for `orbitCrossBound`

The proof of `orbitCrossBound` bounds `∑_j w_j |S_j|`, where `S_j` is the `j`-th partial
sum of the sequence `a_i = λ sin(λx_i) cos(λx_i)/D_i` and `w_j = μψλ²/D_j`.
Away from the middle of the window `|S_j| = ∑_{i<j}|a_i|`, near it we use
`|S_j| ≤ |S_n| + ∑_{i≥j}|a_i|`.  Both require telescoping bounds for sums of
`1/sin²` along sequences that move by at least `h` per step, which is what the lemmas
below provide.
-/

/-- `t cos t ≤ sin t` for `0 ≤ t ≤ π/2` (from `t ≤ tan t`). -/
theorem mul_cos_le_sin_of_le (t : ℝ) (h0 : 0 ≤ t) (hπ : t ≤ Real.pi / 2) :
    t * Real.cos t ≤ Real.sin t := by
  rcases lt_or_eq_of_le hπ with hlt | heq
  · rcases eq_or_lt_of_le h0 with h | h
    · subst h; simp
    · have htan : t ≤ Real.tan t := Real.le_tan (le_of_lt h) hlt
      rw [Real.tan_eq_sin_div_cos] at htan
      have hcos : 0 < Real.cos t := Real.cos_pos_of_mem_Ioo ⟨by linarith [Real.pi_pos], hlt⟩
      rw [le_div_iff₀ hcos] at htan
      linarith
  · subst heq
    rw [Real.cos_pi_div_two, mul_zero]
    exact Real.sin_nonneg_of_nonneg_of_le_pi (by positivity) (by linarith [Real.pi_pos])

/-- One telescoping step: for `0 < x`, `x + h ≤ y ≤ π/2`,
`1/sin²y ≤ (1/h)(cos x / sin x - cos y / sin y)`. -/
theorem one_div_sin_sq_le_cot_diff (x y h : ℝ) (hh : 0 < h) (hx : 0 < x)
    (hgap : x + h ≤ y) (hy : y ≤ Real.pi / 2) :
    1 / (Real.sin y) ^ 2
      ≤ (1 / h) * (Real.cos x / Real.sin x - Real.cos y / Real.sin y) := by
  have hy0 : 0 < y := by linarith
  have hxp : 0 < Real.sin x := Real.sin_pos_of_pos_of_lt_pi hx (by linarith [hy, Real.pi_pos])
  have hyp : 0 < Real.sin y := Real.sin_pos_of_pos_of_lt_pi hy0 (by linarith [hy, Real.pi_pos])
  have hcosy : 0 ≤ Real.cos y :=
    Real.cos_nonneg_of_mem_Icc ⟨by linarith [Real.pi_pos], hy⟩
  have ht0 : 0 ≤ y - x := by linarith
  have htle : y - x ≤ Real.pi / 2 := by linarith
  have hA : (y - x) * Real.cos (y - x) ≤ Real.sin (y - x) :=
    mul_cos_le_sin_of_le (y - x) ht0 htle
  have hsinx : Real.sin x
      = Real.sin y * Real.cos (y - x) - Real.cos y * Real.sin (y - x) := by
    have h := Real.sin_sub y (y - x)
    have hid : y - (y - x) = x := by ring
    rw [hid] at h; exact h
  have hstep : (y - x) * Real.sin x ≤ Real.sin (y - x) * Real.sin y := by
    have h1 : Real.sin x ≤ Real.sin y * Real.cos (y - x) := by
      have h2 : 0 ≤ Real.cos y * Real.sin (y - x) :=
        mul_nonneg hcosy
          (Real.sin_nonneg_of_nonneg_of_le_pi ht0 (by linarith [htle, Real.pi_pos]))
      linarith [hsinx, h2]
    calc (y - x) * Real.sin x ≤ (y - x) * (Real.sin y * Real.cos (y - x)) :=
          mul_le_mul_of_nonneg_left h1 ht0
      _ = ((y - x) * Real.cos (y - x)) * Real.sin y := by ring
      _ ≤ Real.sin (y - x) * Real.sin y := mul_le_mul_of_nonneg_right hA hyp.le
  have hsin_yx : Real.sin (y - x)
      = Real.sin y * Real.cos x - Real.cos y * Real.sin x := by
    rw [Real.sin_sub]
  have hcot : Real.cos x / Real.sin x - Real.cos y / Real.sin y
      = Real.sin (y - x) / (Real.sin x * Real.sin y) := by
    rw [div_sub_div _ _ hxp.ne' hyp.ne', hsin_yx]
    ring
  have hkey : h / (Real.sin y) ^ 2
      ≤ Real.cos x / Real.sin x - Real.cos y / Real.sin y := by
    rw [hcot, div_le_div_iff₀ (pow_pos hyp 2) (mul_pos hxp hyp)]
    have hsyn : 0 ≤ Real.sin x * Real.sin y := (mul_pos hxp hyp).le
    have hp1 : h * (Real.sin x * Real.sin y) ≤ (y - x) * (Real.sin x * Real.sin y) :=
      mul_le_mul_of_nonneg_right (by linarith) hsyn
    have hp2 : (y - x) * (Real.sin x * Real.sin y)
        ≤ Real.sin (y - x) * (Real.sin y) ^ 2 := by
      have h := mul_le_mul_of_nonneg_right hstep hyp.le
      nlinarith [h]
    linarith [hp1, hp2]
  have hgoal : (1 / h) * (Real.cos x / Real.sin x - Real.cos y / Real.sin y)
      = (Real.cos x / Real.sin x - Real.cos y / Real.sin y) / h := by ring
  rw [hgoal, le_div_iff₀ hh]
  have : (1 / (Real.sin y) ^ 2) * h = h / (Real.sin y) ^ 2 := by ring
  rw [this]; exact hkey

/-- Increasing telescoping: for `w` increasing with steps `≥ h` inside `(0, π/2]`,
`∑_{k<m} 1/sin²(w (k+1)) ≤ (1/h)(cot (w 0) - cot (w m))`. -/
theorem sum_one_div_sin_sq_le_cot_sub (h : ℝ) (hh : 0 < h) (w : ℕ → ℝ) (m : ℕ)
    (hstep : ∀ k < m, w k + h ≤ w (k + 1))
    (hpos : ∀ k ≤ m, 0 < w k) (hle : ∀ k ≤ m, w k ≤ Real.pi / 2) :
    (∑ k ∈ Finset.range m, 1 / (Real.sin (w (k + 1))) ^ 2)
      ≤ (1 / h) * (Real.cos (w 0) / Real.sin (w 0)
          - Real.cos (w m) / Real.sin (w m)) := by
  have key : ∀ k < m, 1 / (Real.sin (w (k + 1))) ^ 2
      ≤ (1 / h) * (Real.cos (w k) / Real.sin (w k)
          - Real.cos (w (k + 1)) / Real.sin (w (k + 1))) := by
    intro k hk
    exact one_div_sin_sq_le_cot_diff (w k) (w (k + 1)) h hh
      (hpos k (le_of_lt hk)) (hstep k hk) (hle (k + 1) (by omega))
  calc (∑ k ∈ Finset.range m, 1 / (Real.sin (w (k + 1))) ^ 2)
      ≤ ∑ k ∈ Finset.range m, (1 / h) * (Real.cos (w k) / Real.sin (w k)
          - Real.cos (w (k + 1)) / Real.sin (w (k + 1))) :=
        Finset.sum_le_sum (fun k hk => key k (Finset.mem_range.mp hk))
    _ = (1 / h) * ∑ k ∈ Finset.range m, (Real.cos (w k) / Real.sin (w k)
          - Real.cos (w (k + 1)) / Real.sin (w (k + 1))) := by rw [Finset.mul_sum]
    _ = (1 / h) * (Real.cos (w 0) / Real.sin (w 0)
          - Real.cos (w m) / Real.sin (w m)) := by rw [Finset.sum_range_sub']

/-- Decreasing telescoping: for `w` decreasing with steps `≥ h` inside `(0, π/2]`,
`∑_{k<m} 1/sin²(w k) ≤ (1/h)(cot (w m) - cot (w 0))`. -/
theorem sum_one_div_sin_sq_le_cot_sub' (h : ℝ) (hh : 0 < h) (w : ℕ → ℝ) (m : ℕ)
    (hstep : ∀ k < m, w (k + 1) + h ≤ w k)
    (hpos : ∀ k ≤ m, 0 < w k) (hle : ∀ k ≤ m, w k ≤ Real.pi / 2) :
    (∑ k ∈ Finset.range m, 1 / (Real.sin (w k)) ^ 2)
      ≤ (1 / h) * (Real.cos (w m) / Real.sin (w m)
          - Real.cos (w 0) / Real.sin (w 0)) := by
  have key : ∀ k < m, 1 / (Real.sin (w k)) ^ 2
      ≤ (1 / h) * (Real.cos (w (k + 1)) / Real.sin (w (k + 1))
          - Real.cos (w k) / Real.sin (w k)) := by
    intro k hk
    exact one_div_sin_sq_le_cot_diff (w (k + 1)) (w k) h hh
      (hpos (k + 1) (by omega)) (by linarith [hstep k hk]) (hle k (le_of_lt hk))
  calc (∑ k ∈ Finset.range m, 1 / (Real.sin (w k)) ^ 2)
      ≤ ∑ k ∈ Finset.range m, (1 / h) * (Real.cos (w (k + 1)) / Real.sin (w (k + 1))
          - Real.cos (w k) / Real.sin (w k)) :=
        Finset.sum_le_sum (fun k hk => key k (Finset.mem_range.mp hk))
    _ = (1 / h) * ∑ k ∈ Finset.range m, (Real.cos (w (k + 1)) / Real.sin (w (k + 1))
          - Real.cos (w k) / Real.sin (w k)) := by rw [Finset.mul_sum]
    _ = (1 / h) * (Real.cos (w m) / Real.sin (w m)
          - Real.cos (w 0) / Real.sin (w 0)) := by
        rw [Finset.sum_range_sub (fun i => Real.cos (w i) / Real.sin (w i))]

/-- Double-sum swap (strict triangular form):
`∑_{j<K} ∑_{i<j} f i j = ∑_{i<K} ∑_{i<j<K} f i j`. -/
theorem sum_range_sum_range_lt (f : ℕ → ℕ → ℝ) (K : ℕ) :
    (∑ j ∈ Finset.range K, ∑ i ∈ Finset.range j, f i j)
      = ∑ i ∈ Finset.range K, ∑ j ∈ Finset.Ico (i + 1) K, f i j := by
  induction K with
  | zero => simp
  | succ K ih =>
    have hL : (∑ j ∈ Finset.range (K + 1), ∑ i ∈ Finset.range j, f i j)
        = (∑ j ∈ Finset.range K, ∑ i ∈ Finset.range j, f i j)
          + ∑ i ∈ Finset.range K, f i K := by
      rw [Finset.sum_range_succ]
    have hR : (∑ i ∈ Finset.range (K + 1), ∑ j ∈ Finset.Ico (i + 1) (K + 1), f i j)
        = (∑ i ∈ Finset.range K, ∑ j ∈ Finset.Ico (i + 1) K, f i j)
          + ∑ i ∈ Finset.range K, f i K := by
      rw [Finset.sum_range_succ, Finset.Ico_self, Finset.sum_empty, add_zero]
      rw [← Finset.sum_add_distrib]
      apply Finset.sum_congr rfl
      intro i hi
      have hlt : i < K := Finset.mem_range.mp hi
      exact Finset.sum_Ico_succ_top (by omega) (fun j => f i j)
    calc (∑ j ∈ Finset.range (K + 1), ∑ i ∈ Finset.range j, f i j)
        = (∑ j ∈ Finset.range K, ∑ i ∈ Finset.range j, f i j)
          + ∑ i ∈ Finset.range K, f i K := hL
      _ = (∑ i ∈ Finset.range K, ∑ j ∈ Finset.Ico (i + 1) K, f i j)
          + ∑ i ∈ Finset.range K, f i K := by rw [ih]
      _ = (∑ i ∈ Finset.range (K + 1), ∑ j ∈ Finset.Ico (i + 1) (K + 1), f i j) := hR.symm

/-- Double-sum swap (upper triangular form):
`∑_{j<N} ∑_{j≤i<N} f i j = ∑_{i<N} ∑_{j≤i} f i j`. -/
theorem sum_range_sum_Ico (f : ℕ → ℕ → ℝ) (N : ℕ) :
    (∑ j ∈ Finset.range N, ∑ i ∈ Finset.Ico j N, f i j)
      = ∑ i ∈ Finset.range N, ∑ j ∈ Finset.Ico 0 (i + 1), f i j := by
  induction N with
  | zero => simp
  | succ N ih =>
    have hL : (∑ j ∈ Finset.range (N + 1), ∑ i ∈ Finset.Ico j (N + 1), f i j)
        = (∑ j ∈ Finset.range N, ∑ i ∈ Finset.Ico j N, f i j)
          + ∑ j ∈ Finset.range N, f N j + f N N := by
      rw [Finset.sum_range_succ]
      have hinner : ∀ j ∈ Finset.range N,
          (∑ i ∈ Finset.Ico j (N + 1), f i j) = (∑ i ∈ Finset.Ico j N, f i j) + f N j := by
        intro j hj
        exact Finset.sum_Ico_succ_top (by have := Finset.mem_range.mp hj; omega) (fun i => f i j)
      rw [Finset.sum_congr rfl hinner, Finset.sum_add_distrib]
      rw [show (∑ i ∈ Finset.Ico N (N + 1), f i N) = f N N from by
        have h1 : Finset.Ico N (N + 1) = {N} := by
          ext i; simp only [Finset.mem_Ico, Finset.mem_singleton]; omega
        rw [h1, Finset.sum_singleton]]
    have hR : (∑ i ∈ Finset.range (N + 1), ∑ j ∈ Finset.Ico 0 (i + 1), f i j)
        = (∑ i ∈ Finset.range N, ∑ j ∈ Finset.Ico 0 (i + 1), f i j)
          + ∑ j ∈ Finset.range N, f N j + f N N := by
      rw [Finset.sum_range_succ]
      rw [show (∑ j ∈ Finset.Ico 0 (N + 1), f N j)
          = (∑ j ∈ Finset.range N, f N j) + f N N from by
        rw [← Finset.range_eq_Ico (N + 1), Finset.sum_range_succ]]
      ring
    calc (∑ j ∈ Finset.range (N + 1), ∑ i ∈ Finset.Ico j (N + 1), f i j)
        = (∑ j ∈ Finset.range N, ∑ i ∈ Finset.Ico j N, f i j)
          + ∑ j ∈ Finset.range N, f N j + f N N := hL
      _ = (∑ i ∈ Finset.range N, ∑ j ∈ Finset.Ico 0 (i + 1), f i j)
          + ∑ j ∈ Finset.range N, f N j + f N N := by rw [ih]
      _ = (∑ i ∈ Finset.range (N + 1), ∑ j ∈ Finset.Ico 0 (i + 1), f i j) := hR.symm

end Work.PARIMPL2.Direct

namespace Work.PARIMPL2.Direct

/-- `sin²(λxᵢ) + sinh²(λyᵢ)`. -/
noncomputable def ocDen (lam : ℝ) (x y : ℕ → ℝ) (i : ℕ) : ℝ :=
  Real.sin (lam * x i) ^ 2 + Real.sinh (lam * y i) ^ 2

/-- `λ sin(λxᵢ) cos(λxᵢ) / Dᵢ`. -/
noncomputable def ocA (lam : ℝ) (x y : ℕ → ℝ) (i : ℕ) : ℝ :=
  lam * Real.sin (lam * x i) * Real.cos (lam * x i) / ocDen lam x y i

/-- `μψλ²/Dᵢ`. -/
noncomputable def ocW (mu psi lam : ℝ) (x y : ℕ → ℝ) (i : ℕ) : ℝ :=
  mu * psi * lam ^ 2 / ocDen lam x y i

/-- `∑_{j∈[K,n)} ∑_{i∈[j,n)} f i j = ∑_{i∈[K,n)} ∑_{j∈[K,i+1)} f i j`. -/
theorem sum_Ico_Ico_swap (f : ℕ → ℕ → ℝ) :
    ∀ n K : ℕ, K ≤ n →
      (∑ j ∈ Finset.Ico K n, ∑ i ∈ Finset.Ico j n, f i j)
        = ∑ i ∈ Finset.Ico K n, ∑ j ∈ Finset.Ico K (i + 1), f i j := by
  intro n
  induction n with
  | zero =>
    intro K hK
    have h0 : K = 0 := Nat.le_zero.mp hK
    subst h0; simp
  | succ n ih =>
    intro K hK
    rcases eq_or_lt_of_le hK with h | h
    · subst h; simp
    · have hKn : K ≤ n := Nat.lt_succ_iff.mp h
      have hL : (∑ j ∈ Finset.Ico K (n + 1), ∑ i ∈ Finset.Ico j (n + 1), f i j)
          = (∑ j ∈ Finset.Ico K n, ∑ i ∈ Finset.Ico j n, f i j)
            + (∑ j ∈ Finset.Ico K n, f n j) + f n n := by
        have h1 : (∑ j ∈ Finset.Ico K (n + 1), ∑ i ∈ Finset.Ico j (n + 1), f i j)
            = (∑ j ∈ Finset.Ico K n, ∑ i ∈ Finset.Ico j (n + 1), f i j)
              + ∑ i ∈ Finset.Ico n (n + 1), f i n :=
          Finset.sum_Ico_succ_top hKn (fun j => ∑ i ∈ Finset.Ico j (n + 1), f i j)
        have h2 : (∑ i ∈ Finset.Ico n (n + 1), f i n) = f n n := by
          rw [Finset.sum_Ico_succ_top (le_rfl : n ≤ n), Finset.Ico_self, Finset.sum_empty,
            zero_add]
        have h3 : (∑ j ∈ Finset.Ico K n, ∑ i ∈ Finset.Ico j (n + 1), f i j)
            = (∑ j ∈ Finset.Ico K n, ∑ i ∈ Finset.Ico j n, f i j)
              + ∑ j ∈ Finset.Ico K n, f n j := by
          rw [← Finset.sum_add_distrib]
          apply Finset.sum_congr rfl
          intro j hj
          exact Finset.sum_Ico_succ_top (le_of_lt (Finset.mem_Ico.mp hj).2) (fun i => f i j)
        rw [h1, h2, h3]
      have hR : (∑ i ∈ Finset.Ico K (n + 1), ∑ j ∈ Finset.Ico K (i + 1), f i j)
          = (∑ i ∈ Finset.Ico K n, ∑ j ∈ Finset.Ico K (i + 1), f i j)
            + ∑ j ∈ Finset.Ico K (n + 1), f n j :=
        Finset.sum_Ico_succ_top hKn (fun i => ∑ j ∈ Finset.Ico K (i + 1), f i j)
      have hR2 : (∑ j ∈ Finset.Ico K (n + 1), f n j)
          = (∑ j ∈ Finset.Ico K n, f n j) + f n n :=
        Finset.sum_Ico_succ_top hKn (fun j => f n j)
      calc (∑ j ∈ Finset.Ico K (n + 1), ∑ i ∈ Finset.Ico j (n + 1), f i j)
          = (∑ j ∈ Finset.Ico K n, ∑ i ∈ Finset.Ico j n, f i j)
            + (∑ j ∈ Finset.Ico K n, f n j) + f n n := hL
        _ = (∑ i ∈ Finset.Ico K n, ∑ j ∈ Finset.Ico K (i + 1), f i j)
            + (∑ j ∈ Finset.Ico K n, f n j) + f n n := by rw [ih K hKn]
        _ = (∑ i ∈ Finset.Ico K n, ∑ j ∈ Finset.Ico K (i + 1), f i j)
            + ∑ j ∈ Finset.Ico K (n + 1), f n j := by rw [hR2]; ring
        _ = (∑ i ∈ Finset.Ico K (n + 1), ∑ j ∈ Finset.Ico K (i + 1), f i j) := hR.symm

end Work.PARIMPL2.Direct

namespace Work.PARIMPL2.Direct

theorem orbitCrossBound (lam R : ℝ) (hlam : 0 < lam) (hR : 128 ≤ R) (hlamR : lam * R ^ 2 ≤ 1)
    (n : ℕ) (x y : ℕ → ℝ) (mu psi : ℝ) (hmu : 0 ≤ mu) (hpsi : 1 ≤ psi) (hpsi2 : psi ≤ 2)
    (hx1 : ∀ j ≤ n, R / 4 + 2 ≤ x j) (hx2 : ∀ j ≤ n, x j ≤ Real.pi / lam - R / 4)
    (hdec : ∀ j < n, x (j + 1) ≤ x j - 1 / 3)
    (hy : ∀ j ≤ n, lam * |y j| ≤ 1 / 2)
    (hSn : |∑ i ∈ Finset.range n,
        lam * Real.sin (lam * x i) * Real.cos (lam * x i)
          / (Real.sin (lam * x i) ^ 2 + Real.sinh (lam * y i) ^ 2)| ≤ 8 * (1 + Real.log R)) :
    ∑ j ∈ Finset.range n,
        (mu * psi * lam ^ 2 / (Real.sin (lam * x j) ^ 2 + Real.sinh (lam * y j) ^ 2)) *
          |∑ i ∈ Finset.range j,
            lam * Real.sin (lam * x i) * Real.cos (lam * x i)
              / (Real.sin (lam * x i) ^ 2 + Real.sinh (lam * y i) ^ 2)|
      ≤ 500 * mu * psi * (1 + Real.log R) / R := by
  have hRpos : (0:ℝ) < R := by linarith
  have hlogR : 0 ≤ Real.log R := Real.log_nonneg (by linarith)
  show (∑ j ∈ Finset.range n, ocW mu psi lam x y j
        * |∑ i ∈ Finset.range j, ocA lam x y i|)
      ≤ 500 * mu * psi * (1 + Real.log R) / R
  set A : ℕ → ℝ := ocA lam x y with hA
  set W : ℕ → ℝ := ocW mu psi lam x y with hW
  set Den : ℕ → ℝ := ocDen lam x y with hDen
  have hDeneq : ∀ i, Den i = Real.sin (lam * x i) ^ 2 + Real.sinh (lam * y i) ^ 2 :=
    fun i => by rw [hDen, ocDen]
  have hAeq : ∀ i, A i
      = lam * Real.sin (lam * x i) * Real.cos (lam * x i) / Den i :=
    fun i => by rw [hA, ocA, ← hDen]
  have hWeq : ∀ i, W i = mu * psi * lam ^ 2 / Den i :=
    fun i => by rw [hW, ocW, ← hDen]
  have hAexp : ∀ i, A i = lam * Real.sin (lam * x i) * Real.cos (lam * x i)
      / (Real.sin (lam * x i) ^ 2 + Real.sinh (lam * y i) ^ 2) := by
    intro i; rw [hAeq i, hDeneq i]
  have hWexp : ∀ i, W i = mu * psi * lam ^ 2
      / (Real.sin (lam * x i) ^ 2 + Real.sinh (lam * y i) ^ 2) := by
    intro i; rw [hWeq i, hDeneq i]
  have hSnA : |∑ i ∈ Finset.range n, A i| ≤ 8 * (1 + Real.log R) := by
    have := hSn
    rwa [Finset.sum_congr rfl (fun i _ => (hAexp i).symm)] at this
  -- basic facts
  have htxlow : ∀ i ≤ n, lam * (R / 4) ≤ lam * x i := by
    intro i hi
    have := hx1 i hi
    nlinarith [hlam]
  have htxpi : ∀ i ≤ n, lam * x i < Real.pi := by
    intro i hi
    have h3 := hx2 i hi
    have h1 : lam * x i ≤ lam * (Real.pi / lam - R / 4) :=
      mul_le_mul_of_nonneg_left h3 hlam.le
    have h2 : lam * (Real.pi / lam - R / 4) = Real.pi - lam * R / 4 := by field_simp
    have h4 : 0 < lam * R / 4 := by positivity
    rw [h2] at h1; linarith
  have hsinpos : ∀ i ≤ n, 0 < Real.sin (lam * x i) := by
    intro i hi
    have h0 : 0 < lam * (R / 4) := mul_pos hlam (by linarith)
    exact Real.sin_pos_of_pos_of_lt_pi (by linarith [htxlow i hi, h0]) (htxpi i hi)
  have hDenpos : ∀ i ≤ n, 0 < Den i := by
    intro i hi
    rw [hDeneq i]
    have h1 := hsinpos i hi
    have h2 : 0 ≤ Real.sinh (lam * y i) ^ 2 := sq_nonneg _
    nlinarith [h1, h2]
  have hxmono : ∀ i j, j ≤ i → i ≤ n → x i ≤ x j := by
    intro i
    induction i with
    | zero => intro j hj _; simp only [Nat.le_zero] at hj; subst hj; exact le_rfl
    | succ i ih =>
      intro j hj hin
      rcases eq_or_lt_of_le hj with h | h
      · subst h; exact le_rfl
      · have h1 : j ≤ i := Nat.lt_succ_iff.mp h
        have h2 : i ≤ n := by omega
        have h3 : x (i + 1) ≤ x i - 1 / 3 := hdec i (by omega)
        have h4 := ih j h1 h2
        linarith
  have htxmono : ∀ i j, j ≤ i → i ≤ n → lam * x i ≤ lam * x j := by
    intro i j hji hin
    exact mul_le_mul_of_nonneg_left (hxmono i j hji hin) hlam.le
  have hdec_t : ∀ j < n, lam * x (j + 1) + lam / 3 ≤ lam * x j := by
    intro j hj
    have := hdec j hj
    have h1 : lam * x (j + 1) ≤ lam * (x j - 1 / 3) := mul_le_mul_of_nonneg_left this hlam.le
    have h2 : lam * (x j - 1 / 3) = lam * x j - lam / 3 := by ring
    rw [h2] at h1; linarith
  have hA_abs : ∀ i ≤ n, |A i| ≤ lam / Real.sin (lam * x i) := by
    intro i hi
    rw [hAeq i]
    have hsp := hsinpos i hi
    have hdp := hDenpos i hi
    have hDge : Real.sin (lam * x i) ^ 2 ≤ Den i := by
      rw [hDeneq i]; nlinarith [sq_nonneg (Real.sinh (lam * y i))]
    have h1 : |lam * Real.sin (lam * x i) * Real.cos (lam * x i)| ≤ lam * Real.sin (lam * x i) := by
      rw [abs_mul, abs_mul, abs_of_pos hlam, abs_of_pos hsp]
      have hpos2 : 0 < lam * Real.sin (lam * x i) := mul_pos hlam hsp
      calc lam * Real.sin (lam * x i) * |Real.cos (lam * x i)|
          ≤ lam * Real.sin (lam * x i) * 1 :=
            mul_le_mul_of_nonneg_left (Real.abs_cos_le_one _) hpos2.le
        _ = lam * Real.sin (lam * x i) := by ring
    have h2 : |lam * Real.sin (lam * x i) * Real.cos (lam * x i)| * Real.sin (lam * x i)
        ≤ lam * (Real.sin (lam * x i)) ^ 2 := by
      have h2' := mul_le_mul_of_nonneg_right h1 hsp.le
      nlinarith [h2']
    have h3 : lam * (Real.sin (lam * x i)) ^ 2 ≤ lam * Den i :=
      mul_le_mul_of_nonneg_left hDge hlam.le
    rw [abs_div, abs_of_pos hdp, div_le_div_iff₀ hdp hsp]
    linarith [h2, h3]
  have hW_le : ∀ i ≤ n, W i ≤ mu * psi * lam ^ 2 / (Real.sin (lam * x i)) ^ 2 := by
    intro i hi
    rw [hWeq i, hDeneq i]
    have hsp := hsinpos i hi
    have h1 : Real.sin (lam * x i) ^ 2
        ≤ Real.sin (lam * x i) ^ 2 + Real.sinh (lam * y i) ^ 2 := by
      have := sq_nonneg (Real.sinh (lam * y i)); linarith
    exact div_le_div_of_nonneg_left (by positivity) (pow_pos hsp 2) h1
  have hW_nn : ∀ i, 0 ≤ W i := by
    intro i
    have hd : 0 ≤ Den i := by
      rw [hDeneq i]; have := sq_nonneg (Real.sinh (lam * y i)); nlinarith [sq_nonneg (Real.sin (lam * x i))]
    rw [hWeq i]
    exact div_nonneg (by positivity) hd
  -- the base sum bound
  have hbase : ∑ i ∈ Finset.range n, lam ^ 2 / (Real.sin (lam * x i)) ^ 2 ≤ 24 / R := by
    have := sum_lam2_div_sin_sq_le lam R (fun j => ((x j : ℝ) : ℂ)) n hlam hR hlamR
      (fun j hj => by simpa using hx1 j hj)
      (fun j hj => by simpa using hx2 j hj)
      (fun j hj => by simpa using hdec j hj)
    simpa using this
  -- the crossing index
  set K : ℕ := ((Finset.range n).filter (fun j => Real.pi / 2 ≤ lam * x j)).card with hK
  have hKn : K ≤ n := by
    rw [hK]
    calc ((Finset.range n).filter (fun j => Real.pi / 2 ≤ lam * x j)).card
        ≤ (Finset.range n).card := Finset.card_filter_le _ _
      _ = n := Finset.card_range n
  have hKL : ∀ j < K, Real.pi / 2 ≤ lam * x j := by
    intro j hj
    by_contra hcon
    push Not at hcon
    have hjn : j < n := lt_of_lt_of_le hj hKn
    have hsub : (Finset.range n).filter (fun i => Real.pi / 2 ≤ lam * x i) ⊆ Finset.range j := by
      intro i hi
      rw [Finset.mem_filter, Finset.mem_range] at hi
      rw [Finset.mem_range]
      by_contra hlt
      push Not at hlt
      have h1 : lam * x i ≤ lam * x j := htxmono i j hlt (le_of_lt hi.1)
      linarith [hi.2]
    have := Finset.card_le_card hsub
    rw [Finset.card_range, ← hK] at this
    omega
  have hKR : ∀ j, K ≤ j → j < n → lam * x j < Real.pi / 2 := by
    intro j hKj hjn
    by_contra hcon
    push Not at hcon
    have hmem : j ∈ (Finset.range n).filter (fun i => Real.pi / 2 ≤ lam * x i) := by
      rw [Finset.mem_filter, Finset.mem_range]; exact ⟨hjn, hcon⟩
    have hsub : Finset.range (j + 1) ⊆ (Finset.range n).filter (fun i => Real.pi / 2 ≤ lam * x i) := by
      intro i hi
      rw [Finset.mem_range] at hi
      rw [Finset.mem_filter, Finset.mem_range]
      exact ⟨by omega, le_trans hcon (htxmono j i (by omega) (le_of_lt hjn))⟩
    have := Finset.card_le_card hsub
    rw [Finset.card_range, ← hK] at this
    omega
  -- ==================== the left region ====================
  have hAneg : ∀ i, i < K → A i ≤ 0 := by
    intro i hi
    have hin : i ≤ n := le_trans (le_of_lt hi) hKn
    have hsp := hsinpos i hin
    have hdp := hDenpos i hin
    have hcosp : -(Real.pi / 2) ≤ lam * x i := by linarith [hKL i hi, Real.pi_pos]
    have hcos : Real.cos (lam * x i) ≤ 0 :=
      Real.cos_nonpos_of_pi_div_two_le_of_le (hKL i hi) (by linarith [htxpi i hin])
    rw [hAeq i]
    have h1 : lam * Real.sin (lam * x i) * Real.cos (lam * x i) ≤ 0 :=
      mul_nonpos_of_nonneg_of_nonpos (mul_pos hlam hsp).le hcos
    exact div_nonpos_of_nonpos_of_nonneg h1 hdp.le
  have hLabs : ∀ j ∈ Finset.range K,
      |∑ i ∈ Finset.range j, A i| = ∑ i ∈ Finset.range j, |A i| := by
    intro j hj
    have hjK : j < K := Finset.mem_range.mp hj
    have hneg : ∀ i ∈ Finset.range j, A i ≤ 0 :=
      fun i hi => hAneg i (lt_trans (Finset.mem_range.mp hi) hjK)
    have h1 : (∑ i ∈ Finset.range j, A i) = - ∑ i ∈ Finset.range j, (-A i) := by
      rw [Finset.sum_neg_distrib, neg_neg]
    rw [h1, abs_neg, Finset.abs_sum_of_nonneg (f := fun i => -A i) (s := Finset.range j)
      (fun i hi => neg_nonneg.mpr (hneg i hi))]
    apply Finset.sum_congr rfl
    intro i hi
    rw [abs_of_nonpos (hneg i hi)]
  have hLswap : ∑ j ∈ Finset.range K, W j * (∑ i ∈ Finset.range j, |A i|)
      = ∑ i ∈ Finset.range K, |A i| * ∑ j ∈ Finset.Ico (i + 1) K, W j := by
    have h1 : ∑ j ∈ Finset.range K, W j * (∑ i ∈ Finset.range j, |A i|)
        = ∑ j ∈ Finset.range K, ∑ i ∈ Finset.range j, (|A i| * W j) := by
      apply Finset.sum_congr rfl
      intro j hj
      rw [Finset.mul_sum]
      apply Finset.sum_congr rfl
      intro i hi
      ring
    rw [h1, sum_range_sum_range_lt]
    apply Finset.sum_congr rfl
    intro i hi
    rw [Finset.mul_sum]
  have hUbound : ∀ i ∈ Finset.range K,
      (∑ j ∈ Finset.Ico (i + 1) K, W j)
        ≤ mu * psi * lam ^ 2 * ((1 / (lam / 3)) / Real.sin (lam * x i)) := by
    intro i hi
    have hiK : i < K := Finset.mem_range.mp hi
    have hin : i ≤ n := le_trans (le_of_lt hiK) hKn
    have h1 : ∑ j ∈ Finset.Ico (i + 1) K, W j
        ≤ ∑ j ∈ Finset.Ico (i + 1) K, mu * psi * lam ^ 2 / (Real.sin (lam * x j)) ^ 2 := by
      apply Finset.sum_le_sum
      intro j hj
      exact hW_le j (le_trans (le_of_lt (Finset.mem_Ico.mp hj).2) hKn)
    refine h1.trans ?_
    set w : ℕ → ℝ := fun k => Real.pi - lam * x (i + k) with hw
    have hmm : K - 1 - i = K - 1 - i := rfl
    have hstepw : ∀ k < K - 1 - i, w k + lam / 3 ≤ w (k + 1) := by
      intro k hk
      have hi1 : i + k < n := by omega
      have h2 := hdec_t (i + k) hi1
      have hidx : i + (k + 1) = i + k + 1 := by omega
      simp only [hw]
      rw [hidx]
      linarith
    have hposw : ∀ k ≤ K - 1 - i, 0 < w k := by
      intro k hk
      have hi1 : i + k ≤ n := by omega
      simp only [hw]
      linarith [htxpi (i + k) hi1]
    have hlew : ∀ k ≤ K - 1 - i, w k ≤ Real.pi / 2 := by
      intro k hk
      have h1 : Real.pi / 2 ≤ lam * x (i + k) := by
        apply hKL
        omega
      simp only [hw]
      linarith
    have htel := sum_one_div_sin_sq_le_cot_sub (lam / 3) (by positivity) w (K - 1 - i)
      hstepw hposw hlew
    have hw0sin : Real.sin (w 0) = Real.sin (lam * x i) := by
      simp only [hw, Nat.add_zero, Real.sin_pi_sub]
    have hw0pos : 0 < Real.sin (lam * x i) := hsinpos i hin
    have hwXcos : 0 ≤ Real.cos (w (K - 1 - i)) := by
      have hidx : i + (K - 1 - i) = K - 1 := by omega
      simp only [hw]
      rw [hidx]
      have h1 : Real.pi / 2 ≤ lam * x (K - 1) := hKL (K - 1) (by omega)
      have h2 : lam * x (K - 1) ≤ Real.pi := le_of_lt (htxpi (K - 1) (by omega))
      exact Real.cos_nonneg_of_mem_Icc ⟨by linarith, by linarith⟩
    have hwXsin : 0 < Real.sin (w (K - 1 - i)) := by
      have hidx : i + (K - 1 - i) = K - 1 := by omega
      simp only [hw]
      rw [hidx, Real.sin_pi_sub]
      exact hsinpos (K - 1) (by omega)
    have hb1 : 0 ≤ Real.cos (w (K - 1 - i)) / Real.sin (w (K - 1 - i)) :=
      div_nonneg hwXcos hwXsin.le
    have hb2 : Real.cos (w 0) / Real.sin (w 0) ≤ 1 / Real.sin (lam * x i) := by
      rw [hw0sin, div_le_div_iff₀ hw0pos hw0pos]
      exact mul_le_mul_of_nonneg_right (Real.cos_le_one (w 0)) hw0pos.le
    have hb3 : Real.cos (w 0) / Real.sin (w 0) - Real.cos (w (K - 1 - i)) / Real.sin (w (K - 1 - i))
        ≤ 1 / Real.sin (lam * x i) := by linarith
    have hconv : ∑ k ∈ Finset.range (K - 1 - i), 1 / (Real.sin (w (k + 1))) ^ 2
        = ∑ j ∈ Finset.Ico (i + 1) K, 1 / (Real.sin (lam * x j)) ^ 2 := by
      rw [Finset.sum_Ico_eq_sum_range]
      have hidxa : K - (i + 1) = K - 1 - i := by omega
      rw [hidxa]
      apply Finset.sum_congr rfl
      intro k hk
      have hidx : i + 1 + k = i + (k + 1) := by omega
      simp only [hw]
      rw [hidx, Real.sin_pi_sub]
    calc (∑ j ∈ Finset.Ico (i + 1) K, mu * psi * lam ^ 2 / (Real.sin (lam * x j)) ^ 2)
        = mu * psi * lam ^ 2 * ∑ j ∈ Finset.Ico (i + 1) K, 1 / (Real.sin (lam * x j)) ^ 2 := by
          rw [Finset.mul_sum]
          apply Finset.sum_congr rfl
          intro j hj
          ring
      _ = mu * psi * lam ^ 2 * ∑ k ∈ Finset.range (K - 1 - i), 1 / (Real.sin (w (k + 1))) ^ 2 := by
          rw [hconv]
      _ ≤ mu * psi * lam ^ 2 * ((1 / (lam / 3)) * (Real.cos (w 0) / Real.sin (w 0)
            - Real.cos (w (K - 1 - i)) / Real.sin (w (K - 1 - i)))) :=
          mul_le_mul_of_nonneg_left htel (by positivity)
      _ ≤ mu * psi * lam ^ 2 * ((1 / (lam / 3)) / Real.sin (lam * x i)) := by
          apply mul_le_mul_of_nonneg_left _ (by positivity)
          calc (1 / (lam / 3)) * (Real.cos (w 0) / Real.sin (w 0)
                - Real.cos (w (K - 1 - i)) / Real.sin (w (K - 1 - i)))
              ≤ (1 / (lam / 3)) * (1 / Real.sin (lam * x i)) :=
                mul_le_mul_of_nonneg_left hb3 (by positivity)
            _ = (1 / (lam / 3)) / Real.sin (lam * x i) := by ring
  have hLpart : ∑ j ∈ Finset.range K, W j * |∑ i ∈ Finset.range j, A i| ≤ 72 * mu * psi / R := by
    have h1 : ∑ j ∈ Finset.range K, W j * |∑ i ∈ Finset.range j, A i|
        = ∑ j ∈ Finset.range K, W j * (∑ i ∈ Finset.range j, |A i|) := by
      apply Finset.sum_congr rfl
      intro j hj
      rw [hLabs j hj]
    rw [h1, hLswap]
    have h2 : ∑ i ∈ Finset.range K, |A i| * ∑ j ∈ Finset.Ico (i + 1) K, W j
        ≤ ∑ i ∈ Finset.range K, (lam / Real.sin (lam * x i))
            * (mu * psi * lam ^ 2 * ((1 / (lam / 3)) / Real.sin (lam * x i))) := by
      apply Finset.sum_le_sum
      intro i hi
      have hiK : i < K := Finset.mem_range.mp hi
      have hin : i ≤ n := le_trans (le_of_lt hiK) hKn
      have hU := hUbound i hi
      have hA' := hA_abs i hin
      have hVnn : 0 ≤ ∑ j ∈ Finset.Ico (i + 1) K, W j := Finset.sum_nonneg (fun j _ => hW_nn j)
      have hAnnn : 0 ≤ lam / Real.sin (lam * x i) :=
        div_nonneg hlam.le (hsinpos i hin).le
      nlinarith [hA', hU, hVnn, hAnnn]
    refine h2.trans ?_
    have h3 : ∑ i ∈ Finset.range K, (lam / Real.sin (lam * x i))
          * (mu * psi * lam ^ 2 * ((1 / (lam / 3)) / Real.sin (lam * x i)))
        = 3 * mu * psi * lam ^ 2 * ∑ i ∈ Finset.range K, 1 / (Real.sin (lam * x i)) ^ 2 := by
      rw [Finset.mul_sum]
      apply Finset.sum_congr rfl
      intro i hi
      have hsp := hsinpos i (le_trans (le_of_lt (Finset.mem_range.mp hi)) hKn)
      field_simp
    rw [h3]
    have hbaseK : ∑ i ∈ Finset.range K, lam ^ 2 / (Real.sin (lam * x i)) ^ 2 ≤ 24 / R := by
      refine le_trans ?_ hbase
      apply Finset.sum_le_sum_of_subset_of_nonneg
      · intro i hi
        exact Finset.mem_range.mpr (lt_of_lt_of_le (Finset.mem_range.mp hi) hKn)
      · intro i hi _
        positivity
    have h4 : ∑ i ∈ Finset.range K, 1 / (Real.sin (lam * x i)) ^ 2 ≤ 24 / (lam ^ 2 * R) := by
      have h5 : ∑ i ∈ Finset.range K, 1 / (Real.sin (lam * x i)) ^ 2
          = (1 / lam ^ 2) * ∑ i ∈ Finset.range K, lam ^ 2 / (Real.sin (lam * x i)) ^ 2 := by
        rw [Finset.mul_sum]
        apply Finset.sum_congr rfl
        intro i hi
        have hsp := hsinpos i (le_trans (le_of_lt (Finset.mem_range.mp hi)) hKn)
        field_simp
      calc ∑ i ∈ Finset.range K, 1 / (Real.sin (lam * x i)) ^ 2
          = (1 / lam ^ 2) * ∑ i ∈ Finset.range K, lam ^ 2 / (Real.sin (lam * x i)) ^ 2 := h5
        _ ≤ (1 / lam ^ 2) * (24 / R) := mul_le_mul_of_nonneg_left hbaseK (by positivity)
        _ = 24 / (lam ^ 2 * R) := by field_simp
    calc 3 * mu * psi * lam ^ 2 * ∑ i ∈ Finset.range K, 1 / (Real.sin (lam * x i)) ^ 2
        ≤ 3 * mu * psi * lam ^ 2 * (24 / (lam ^ 2 * R)) :=
          mul_le_mul_of_nonneg_left h4 (by positivity)
      _ = 72 * mu * psi / R := by field_simp; ring
  -- ==================== the right region ====================
  have hsinR : 0 < Real.sin (lam * (R / 4)) := by
    have h1 : 0 < lam * (R / 4) := mul_pos hlam (by linarith)
    have h2 : lam * (R / 4) < Real.pi := by
      have h3 : lam * (R / 4) ≤ 1 / 4 := by nlinarith [hlamR, hR, hlam]
      linarith [Real.pi_gt_three]
    exact Real.sin_pos_of_pos_of_lt_pi h1 h2
  have hRpart : ∑ j ∈ Finset.Ico K n, W j * |∑ i ∈ Finset.range j, A i|
      ≤ 192 * mu * psi * (1 + Real.log R) / R
        + 3 * mu * psi * lam ^ 2
            * ((1 / (lam / 3)) / Real.sin (lam * (R / 4))
              + 1 / (Real.sin (lam * (R / 4))) ^ 2) := by
    rcases eq_or_lt_of_le hKn with hKeq | hKlt
    · rw [hKeq, Finset.Ico_self, Finset.sum_empty]
      have h2 : (0:ℝ) ≤ 3 * mu * psi * lam ^ 2
          * ((1 / (lam / 3)) / Real.sin (lam * (R / 4))
            + 1 / (Real.sin (lam * (R / 4))) ^ 2) := by
        have h3 : (0:ℝ) ≤ (1 / (lam / 3)) / Real.sin (lam * (R / 4)) :=
          div_nonneg (by positivity) hsinR.le
        have h4 : (0:ℝ) ≤ 1 / (Real.sin (lam * (R / 4))) ^ 2 := by positivity
        positivity
      have h1 : (0:ℝ) ≤ 192 * mu * psi * (1 + Real.log R) / R := by positivity
      linarith
    · have hKRn : ∀ j, K ≤ j → j ≤ n → lam * x j < Real.pi / 2 := by
        intro j hKj hjn
        rcases lt_or_eq_of_le hjn with h | h
        · exact hKR j hKj h
        · rw [h]
          have h1 : lam * x n ≤ lam * x K := htxmono n K hKn le_rfl
          exact lt_of_le_of_lt h1 (hKR K le_rfl hKlt)
      have hsinmonoR : ∀ i j, K ≤ i → i ≤ j → j ≤ n →
          Real.sin (lam * x j) ≤ Real.sin (lam * x i) := by
        intro i j hKi hij hjn
        have hin : i ≤ n := le_trans hij hjn
        have h1 : lam * x j ≤ lam * x i := htxmono j i hij hjn
        have h2 : lam * x i < Real.pi / 2 := hKRn i hKi hin
        have h3 : -(Real.pi / 2) ≤ lam * x j := by
          have h4 := htxlow j hjn
          have h5 : 0 ≤ lam * (R / 4) := (mul_pos hlam (by linarith)).le
          linarith [Real.pi_pos]
        rcases lt_or_eq_of_le h1 with hlt | heq
        · exact (Real.sin_lt_sin_of_lt_of_le_pi_div_two h3 (le_of_lt h2) hlt).le
        · rw [heq]
      have hWR : ∑ j ∈ Finset.Ico K n, W j ≤ 24 * mu * psi / R := by
        have h1 : ∑ j ∈ Finset.Ico K n, W j
            ≤ ∑ j ∈ Finset.Ico K n, mu * psi * lam ^ 2 / (Real.sin (lam * x j)) ^ 2 := by
          apply Finset.sum_le_sum
          intro j hj
          exact hW_le j (le_of_lt (Finset.mem_Ico.mp hj).2)
        have h2 : ∑ j ∈ Finset.Ico K n, mu * psi * lam ^ 2 / (Real.sin (lam * x j)) ^ 2
            ≤ ∑ j ∈ Finset.range n, mu * psi * lam ^ 2 / (Real.sin (lam * x j)) ^ 2 := by
          apply Finset.sum_le_sum_of_subset_of_nonneg
          · intro j hj
            exact Finset.mem_range.mpr (Finset.mem_Ico.mp hj).2
          · intro j hj _
            positivity
        have h3 : ∑ j ∈ Finset.range n, mu * psi * lam ^ 2 / (Real.sin (lam * x j)) ^ 2
            = mu * psi * ∑ j ∈ Finset.range n, lam ^ 2 / (Real.sin (lam * x j)) ^ 2 := by
          rw [Finset.mul_sum]
          apply Finset.sum_congr rfl
          intro j hj
          ring
        calc ∑ j ∈ Finset.Ico K n, W j
            ≤ ∑ j ∈ Finset.range n, mu * psi * lam ^ 2 / (Real.sin (lam * x j)) ^ 2 :=
              h1.trans h2
          _ = mu * psi * ∑ j ∈ Finset.range n, lam ^ 2 / (Real.sin (lam * x j)) ^ 2 := h3
          _ ≤ mu * psi * (24 / R) := mul_le_mul_of_nonneg_left hbase (by positivity)
          _ = 24 * mu * psi / R := by ring
      have hswap : ∑ j ∈ Finset.Ico K n, W j * (∑ i ∈ Finset.Ico j n, |A i|)
          = ∑ i ∈ Finset.Ico K n, |A i| * ∑ j ∈ Finset.Ico K (i + 1), W j := by
        have h1 : ∑ j ∈ Finset.Ico K n, W j * (∑ i ∈ Finset.Ico j n, |A i|)
            = ∑ j ∈ Finset.Ico K n, ∑ i ∈ Finset.Ico j n, (|A i| * W j) := by
          apply Finset.sum_congr rfl
          intro j hj
          rw [Finset.mul_sum]
          apply Finset.sum_congr rfl
          intro i hi
          ring
        rw [h1, sum_Ico_Ico_swap (fun i j => |A i| * W j) n K hKn]
        apply Finset.sum_congr rfl
        intro i hi
        rw [Finset.mul_sum]
      have hVbound : ∀ i ∈ Finset.Ico K n,
          (∑ j ∈ Finset.Ico K (i + 1), W j)
            ≤ mu * psi * lam ^ 2 * ((1 / (lam / 3)) / Real.sin (lam * x (i + 1))) := by
        intro i hi
        have hKi : K ≤ i := (Finset.mem_Ico.mp hi).1
        have hin : i < n := (Finset.mem_Ico.mp hi).2
        have h1 : ∑ j ∈ Finset.Ico K (i + 1), W j
            ≤ ∑ j ∈ Finset.Ico K (i + 1), mu * psi * lam ^ 2 / (Real.sin (lam * x j)) ^ 2 := by
          apply Finset.sum_le_sum
          intro j hj
          have hjn : j ≤ n := by
            have := (Finset.mem_Ico.mp hj).2; omega
          exact hW_le j hjn
        refine h1.trans ?_
        set w : ℕ → ℝ := fun k => lam * x (K + k) with hw
        have hstepw : ∀ k < i + 1 - K, w (k + 1) + lam / 3 ≤ w k := by
          intro k hk
          have h2 : K + k < i + 1 := (Nat.lt_sub_iff_add_lt').mp hk
          have h5 : K + k < n := by omega
          have h3 := hdec_t (K + k) h5
          have hidx : K + (k + 1) = K + k + 1 := by omega
          simp only [hw]
          rw [hidx]
          linarith
        have hposw : ∀ k ≤ i + 1 - K, 0 < w k := by
          intro k hk
          have h2 : K + k ≤ i + 1 := (Nat.le_sub_iff_add_le' (Nat.le_succ_of_le hKi)).mp hk
          have h5 : K + k ≤ n := by omega
          have h4 := htxlow (K + k) h5
          have h6 : 0 < lam * (R / 4) := mul_pos hlam (by linarith)
          simp only [hw]
          linarith
        have hlew : ∀ k ≤ i + 1 - K, w k ≤ Real.pi / 2 := by
          intro k hk
          have h2 : K + k ≤ i + 1 := (Nat.le_sub_iff_add_le' (Nat.le_succ_of_le hKi)).mp hk
          have h5 : K + k ≤ n := by omega
          have h3 : K ≤ K + k := Nat.le_add_right K k
          simp only [hw]
          exact le_of_lt (hKRn (K + k) h3 h5)
        have htel := sum_one_div_sin_sq_le_cot_sub' (lam / 3) (by positivity) w (i + 1 - K)
          hstepw hposw hlew
        have hwm : w (i + 1 - K) = lam * x (i + 1) := by
          simp only [hw]
          congr 1
          rw [Nat.add_comm, Nat.sub_add_cancel (Nat.le_succ_of_le hKi)]
        have hw0cos : 0 ≤ Real.cos (w 0) := by
          have h1 : lam * x (K + 0) < Real.pi / 2 := hKRn K (le_refl K) (le_of_lt hKlt)
          have h4 := htxlow K (le_of_lt hKlt)
          have h5 : 0 ≤ lam * (R / 4) := (mul_pos hlam (by linarith)).le
          simp only [hw, Nat.add_zero]
          exact Real.cos_nonneg_of_mem_Icc ⟨by linarith [Real.pi_pos], le_of_lt h1⟩
        have hw0sin : 0 < Real.sin (w 0) := by
          have h4 := hsinpos K (le_of_lt hKlt)
          simpa only [hw, Nat.add_zero] using h4
        have hmsin : 0 < Real.sin (lam * x (i + 1)) := hsinpos (i + 1) (by omega)
        have hconv : ∑ k ∈ Finset.range (i + 1 - K), 1 / (Real.sin (w k)) ^ 2
            = ∑ j ∈ Finset.Ico K (i + 1), 1 / (Real.sin (lam * x j)) ^ 2 := by
          have h1 : ∀ k ∈ Finset.range (i + 1 - K),
              (1:ℝ) / (Real.sin (w k)) ^ 2 = 1 / (Real.sin (lam * x (K + k))) ^ 2 := by
            intro k hk
            simp only [hw]
          rw [Finset.sum_congr rfl h1, Finset.sum_Ico_eq_sum_range]
        have hb2 : Real.cos (lam * x (i+1)) / Real.sin (lam * x (i+1))
            ≤ 1 / Real.sin (lam * x (i+1)) := by
          rw [div_le_div_iff₀ hmsin hmsin]
          exact mul_le_mul_of_nonneg_right (Real.cos_le_one _) hmsin.le
        calc ∑ j ∈ Finset.Ico K (i + 1), mu * psi * lam ^ 2 / (Real.sin (lam * x j)) ^ 2
            = mu * psi * lam ^ 2
              * ∑ j ∈ Finset.Ico K (i + 1), 1 / (Real.sin (lam * x j)) ^ 2 := by
              rw [Finset.mul_sum]
              apply Finset.sum_congr rfl
              intro j hj
              ring
          _ = mu * psi * lam ^ 2
              * ∑ k ∈ Finset.range (i + 1 - K), 1 / (Real.sin (w k)) ^ 2 := by rw [hconv]
          _ ≤ mu * psi * lam ^ 2 * ((1 / (lam / 3))
              * (Real.cos (w (i + 1 - K)) / Real.sin (w (i + 1 - K))
                  - Real.cos (w 0) / Real.sin (w 0))) :=
              mul_le_mul_of_nonneg_left htel (by positivity)
          _ ≤ mu * psi * lam ^ 2 * ((1 / (lam / 3)) / Real.sin (lam * x (i + 1))) := by
              rw [hwm]
              apply mul_le_mul_of_nonneg_left _ (by positivity)
              have hb1 : (0:ℝ) ≤ Real.cos (w 0) / Real.sin (w 0) := div_nonneg hw0cos hw0sin.le
              have hb3 : Real.cos (lam * x (i + 1)) / Real.sin (lam * x (i + 1))
                  - Real.cos (w 0) / Real.sin (w 0) ≤ 1 / Real.sin (lam * x (i + 1)) := by
                linarith
              calc (1 / (lam / 3)) * (Real.cos (lam * x (i + 1)) / Real.sin (lam * x (i + 1))
                    - Real.cos (w 0) / Real.sin (w 0))
                  ≤ (1 / (lam / 3)) * (1 / Real.sin (lam * x (i + 1))) :=
                    mul_le_mul_of_nonneg_left hb3 (by positivity)
                _ = (1 / (lam / 3)) / Real.sin (lam * x (i + 1)) := by ring
      have hSj : ∀ j ∈ Finset.Ico K n,
          |∑ i ∈ Finset.range j, A i| ≤ 8 * (1 + Real.log R) + ∑ i ∈ Finset.Ico j n, |A i| := by
        intro j hj
        have hjn : j ≤ n := le_of_lt (Finset.mem_Ico.mp hj).2
        have hsum : (∑ i ∈ Finset.range j, A i) + ∑ i ∈ Finset.Ico j n, A i
            = ∑ i ∈ Finset.range n, A i := by
          have := Finset.sum_Ico_consecutive (f := A) (Nat.zero_le j) hjn
          rwa [← Finset.range_eq_Ico j, ← Finset.range_eq_Ico n] at this
        have h1 : (∑ i ∈ Finset.range j, A i)
            = (∑ i ∈ Finset.range n, A i) - ∑ i ∈ Finset.Ico j n, A i := by linarith
        calc |∑ i ∈ Finset.range j, A i|
            = |(∑ i ∈ Finset.range n, A i) - ∑ i ∈ Finset.Ico j n, A i| := by rw [h1]
          _ ≤ |∑ i ∈ Finset.range n, A i| + |∑ i ∈ Finset.Ico j n, A i| := by
              have h := abs_sub_le (∑ i ∈ Finset.range n, A i) 0 (∑ i ∈ Finset.Ico j n, A i)
              simpa using h
          _ ≤ 8 * (1 + Real.log R) + ∑ i ∈ Finset.Ico j n, |A i| := by
              have h2 := Finset.abs_sum_le_sum_abs A (Finset.Ico j n)
              linarith [hSnA, h2]
      have hIco_sub : ∑ j ∈ Finset.Ico (K + 1) n, 1 / (Real.sin (lam * x j)) ^ 2
          ≤ ∑ j ∈ Finset.Ico K n, 1 / (Real.sin (lam * x j)) ^ 2 := by
        apply Finset.sum_le_sum_of_subset_of_nonneg
        · intro j hj
          rw [Finset.mem_Ico] at hj ⊢
          exact ⟨le_trans (Nat.le_succ K) hj.1, hj.2⟩
        · intro j hj _
          positivity
      have htelR : ∑ j ∈ Finset.Ico K n, 1 / (Real.sin (lam * x j)) ^ 2
          ≤ (1 / (lam / 3)) / Real.sin (lam * x n) := by
        set w : ℕ → ℝ := fun k => lam * x (K + k) with hw
        have hstepw : ∀ k < n - K, w (k + 1) + lam / 3 ≤ w k := by
          intro k hk
          have h2 : K + k < n := (Nat.lt_sub_iff_add_lt').mp hk
          have h3 := hdec_t (K + k) h2
          have hidx : K + (k + 1) = K + k + 1 := by omega
          simp only [hw]
          rw [hidx]
          linarith
        have hposw : ∀ k ≤ n - K, 0 < w k := by
          intro k hk
          have h2 : K + k ≤ n := (Nat.le_sub_iff_add_le' hKn).mp hk
          have h4 := htxlow (K + k) h2
          have h6 : 0 < lam * (R / 4) := mul_pos hlam (by linarith)
          simp only [hw]
          linarith
        have hlew : ∀ k ≤ n - K, w k ≤ Real.pi / 2 := by
          intro k hk
          have h2 : K + k ≤ n := (Nat.le_sub_iff_add_le' hKn).mp hk
          have h3 : K ≤ K + k := Nat.le_add_right K k
          simp only [hw]
          exact le_of_lt (hKRn (K + k) h3 h2)
        have htel := sum_one_div_sin_sq_le_cot_sub' (lam / 3) (by positivity) w (n - K)
          hstepw hposw hlew
        have hwm : w (n - K) = lam * x n := by
          simp only [hw]
          congr 1
          rw [Nat.add_comm, Nat.sub_add_cancel hKn]
        have hw0cos : 0 ≤ Real.cos (w 0) := by
          have h1 : lam * x (K + 0) < Real.pi / 2 := hKRn K (le_refl K) (le_of_lt hKlt)
          have h4 := htxlow K (le_of_lt hKlt)
          have h5 : 0 ≤ lam * (R / 4) := (mul_pos hlam (by linarith)).le
          simp only [hw, Nat.add_zero]
          exact Real.cos_nonneg_of_mem_Icc ⟨by linarith [Real.pi_pos], le_of_lt h1⟩
        have hw0sin : 0 < Real.sin (w 0) := by
          have h4 := hsinpos K (le_of_lt hKlt)
          simpa only [hw, Nat.add_zero] using h4
        have hconv : ∑ k ∈ Finset.range (n - K), 1 / (Real.sin (w k)) ^ 2
            = ∑ j ∈ Finset.Ico K n, 1 / (Real.sin (lam * x j)) ^ 2 := by
          have h1 : ∀ k ∈ Finset.range (n - K),
              (1:ℝ) / (Real.sin (w k)) ^ 2 = 1 / (Real.sin (lam * x (K + k))) ^ 2 := by
            intro k hk
            simp only [hw]
          rw [Finset.sum_congr rfl h1, Finset.sum_Ico_eq_sum_range]
        rw [← hconv]
        have hb1 : (0:ℝ) ≤ Real.cos (w (n - K)) / Real.sin (w (n - K)) := by
          rw [hwm]
          refine div_nonneg ?_ (hsinpos n le_rfl).le
          have h1 : lam * x n < Real.pi / 2 := hKRn n hKn le_rfl
          have h4 := htxlow n le_rfl
          have h5 : 0 ≤ lam * (R / 4) := (mul_pos hlam (by linarith)).le
          exact Real.cos_nonneg_of_mem_Icc ⟨by linarith [Real.pi_pos], le_of_lt h1⟩
        have hb0 : (0:ℝ) ≤ Real.cos (w 0) / Real.sin (w 0) := div_nonneg hw0cos hw0sin.le
        calc ∑ k ∈ Finset.range (n - K), 1 / (Real.sin (w k)) ^ 2
            ≤ (1 / (lam / 3)) * (Real.cos (w (n - K)) / Real.sin (w (n - K))
                - Real.cos (w 0) / Real.sin (w 0)) := htel
          _ ≤ (1 / (lam / 3)) * (Real.cos (w (n - K)) / Real.sin (w (n - K))) := by
              have h := mul_le_mul_of_nonneg_left
                (by linarith : Real.cos (w (n - K)) / Real.sin (w (n - K))
                    - Real.cos (w 0) / Real.sin (w 0)
                    ≤ Real.cos (w (n - K)) / Real.sin (w (n - K)))
                (by positivity : (0:ℝ) ≤ 1 / (lam / 3))
              linarith [h]
          _ = (1 / (lam / 3)) * (Real.cos (lam * x n) / Real.sin (lam * x n)) := by rw [hwm]
          _ ≤ (1 / (lam / 3)) * (1 / Real.sin (lam * x n)) := by
              apply mul_le_mul_of_nonneg_left _ (by positivity)
              rw [div_le_div_iff₀ (hsinpos n le_rfl) (hsinpos n le_rfl)]
              exact mul_le_mul_of_nonneg_right (Real.cos_le_one _) (hsinpos n le_rfl).le
          _ = (1 / (lam / 3)) / Real.sin (lam * x n) := by ring
      have htail : ∑ j ∈ Finset.Ico K n, W j * (∑ i ∈ Finset.Ico j n, |A i|)
          ≤ 3 * mu * psi * lam ^ 2
              * ((1 / (lam / 3)) / Real.sin (lam * (R / 4))
                + 1 / (Real.sin (lam * (R / 4))) ^ 2) := by
        rw [hswap]
        have hstep1 : ∑ i ∈ Finset.Ico K n, |A i| * ∑ j ∈ Finset.Ico K (i + 1), W j
            ≤ ∑ i ∈ Finset.Ico K n, (lam / Real.sin (lam * x i))
                * (mu * psi * lam ^ 2 * ((1 / (lam / 3)) / Real.sin (lam * x (i + 1)))) := by
          apply Finset.sum_le_sum
          intro i hi
          have hin : i ≤ n := le_of_lt (Finset.mem_Ico.mp hi).2
          have hA' := hA_abs i hin
          have hVv := hVbound i hi
          have hVnn : 0 ≤ ∑ j ∈ Finset.Ico K (i + 1), W j :=
            Finset.sum_nonneg (fun j _ => hW_nn j)
          have hAnn : 0 ≤ lam / Real.sin (lam * x i) := div_nonneg hlam.le (hsinpos i hin).le
          exact mul_le_mul hA' hVv hVnn hAnn
        have hstep2 : ∑ i ∈ Finset.Ico K n, (lam / Real.sin (lam * x i))
              * (mu * psi * lam ^ 2 * ((1 / (lam / 3)) / Real.sin (lam * x (i + 1))))
            = 3 * mu * psi * lam ^ 2 * ∑ i ∈ Finset.Ico K n,
                1 / (Real.sin (lam * x i) * Real.sin (lam * x (i + 1))) := by
          rw [Finset.mul_sum]
          apply Finset.sum_congr rfl
          intro i hi
          have hin : i < n := (Finset.mem_Ico.mp hi).2
          have h1 : 0 < Real.sin (lam * x i) := hsinpos i (le_of_lt hin)
          have h2 : 0 < Real.sin (lam * x (i + 1)) := hsinpos (i + 1) (by omega)
          field_simp
        have hstep3 : ∑ i ∈ Finset.Ico K n,
              1 / (Real.sin (lam * x i) * Real.sin (lam * x (i + 1)))
            ≤ ∑ i ∈ Finset.Ico K n, 1 / (Real.sin (lam * x (i + 1))) ^ 2 := by
          apply Finset.sum_le_sum
          intro i hi
          have hKi : K ≤ i := (Finset.mem_Ico.mp hi).1
          have hin : i < n := (Finset.mem_Ico.mp hi).2
          have h1 : Real.sin (lam * x (i + 1)) ≤ Real.sin (lam * x i) :=
            hsinmonoR i (i + 1) hKi (by omega) (by omega)
          have h2 : 0 < Real.sin (lam * x (i + 1)) := hsinpos (i + 1) (by omega)
          have h4 : Real.sin (lam * x (i + 1)) * Real.sin (lam * x (i + 1))
              ≤ Real.sin (lam * x i) * Real.sin (lam * x (i + 1)) :=
            mul_le_mul_of_nonneg_right h1 h2.le
          have hp1 : 0 < Real.sin (lam * x i) * Real.sin (lam * x (i + 1)) :=
            mul_pos (hsinpos i (le_of_lt hin)) h2
          rw [one_div, one_div, inv_le_inv₀ hp1 (pow_pos h2 2)]
          linarith [h4]
        have hsin_n : Real.sin (lam * (R / 4)) ≤ Real.sin (lam * x n) := by
          have h3 : lam * (R / 4) ≤ lam * x n := htxlow n le_rfl
          have h4 : -(Real.pi / 2) ≤ lam * (R / 4) := by
            have h5 := mul_pos hlam (by linarith : (0:ℝ) < R / 4)
            linarith [Real.pi_pos]
          have h6 : lam * x n < Real.pi / 2 := hKRn n hKn le_rfl
          rcases lt_or_eq_of_le h3 with hlt | heq
          · exact (Real.sin_lt_sin_of_lt_of_le_pi_div_two h4 (le_of_lt h6) hlt).le
          · rw [heq]
        have hfinal : ∑ j ∈ Finset.Ico (K + 1) n, 1 / (Real.sin (lam * x j)) ^ 2
              + 1 / (Real.sin (lam * x n)) ^ 2
            ≤ (1 / (lam / 3)) / Real.sin (lam * (R / 4))
              + 1 / (Real.sin (lam * (R / 4))) ^ 2 := by
          have h1 : ∑ j ∈ Finset.Ico (K + 1) n, 1 / (Real.sin (lam * x j)) ^ 2
              ≤ (1 / (lam / 3)) / Real.sin (lam * x n) := hIco_sub.trans htelR
          have h2 : 1 / (Real.sin (lam * x n)) ^ 2
              ≤ 1 / (Real.sin (lam * (R / 4))) ^ 2 := by
            have hpos_n : 0 < Real.sin (lam * x n) := hsinpos n le_rfl
            rw [one_div, one_div, inv_le_inv₀ (pow_pos hpos_n 2) (pow_pos hsinR 2)]
            exact pow_le_pow_left₀ hsinR.le hsin_n 2
          have h3 : 1 / Real.sin (lam * x n) ≤ 1 / Real.sin (lam * (R / 4)) :=
            one_div_le_one_div_of_le hsinR hsin_n
          have h5 : 0 < (1:ℝ) / (lam / 3) := by positivity
          have h7 := mul_le_mul_of_nonneg_left h3 (le_of_lt h5)
          have h8 : (1/(lam/3)) / Real.sin (lam * x n)
              = (1/(lam/3)) * (1 / Real.sin (lam * x n)) := by ring
          have h9 : (1/(lam/3)) / Real.sin (lam * (R/4))
              = (1/(lam/3)) * (1 / Real.sin (lam * (R/4))) := by ring
          linarith [h1, h2, h7, h8, h9]
        have hge : (0:ℝ) ≤ 3 * mu * psi * lam ^ 2 := by positivity
        calc ∑ i ∈ Finset.Ico K n, |A i| * ∑ j ∈ Finset.Ico K (i + 1), W j
            ≤ ∑ i ∈ Finset.Ico K n, (lam / Real.sin (lam * x i))
                * (mu * psi * lam ^ 2 * ((1 / (lam / 3)) / Real.sin (lam * x (i + 1)))) :=
              hstep1
          _ = 3 * mu * psi * lam ^ 2 * ∑ i ∈ Finset.Ico K n,
                1 / (Real.sin (lam * x i) * Real.sin (lam * x (i + 1))) := hstep2
          _ ≤ 3 * mu * psi * lam ^ 2 * ∑ i ∈ Finset.Ico K n,
                1 / (Real.sin (lam * x (i + 1))) ^ 2 :=
              mul_le_mul_of_nonneg_left hstep3 hge
          _ = 3 * mu * psi * lam ^ 2 * ∑ j ∈ Finset.Ico (K + 1) (n + 1),
                1 / (Real.sin (lam * x j)) ^ 2 := by
              congr 1
              rw [Finset.sum_Ico_add' (fun j => 1 / (Real.sin (lam * x j)) ^ 2) K n 1]
          _ = 3 * mu * psi * lam ^ 2 * (∑ j ∈ Finset.Ico (K + 1) n,
                1 / (Real.sin (lam * x j)) ^ 2 + 1 / (Real.sin (lam * x n)) ^ 2) := by
              congr 1
              rw [← Finset.sum_Ico_consecutive (f := fun j => 1 / (Real.sin (lam * x j)) ^ 2)
                (by omega : K + 1 ≤ n) (by omega : n ≤ n + 1)]
              rw [Finset.sum_Ico_succ_top (le_rfl : n ≤ n), Finset.Ico_self, Finset.sum_empty,
                zero_add]
          _ ≤ 3 * mu * psi * lam ^ 2 * ((1 / (lam / 3)) / Real.sin (lam * (R / 4))
                + 1 / (Real.sin (lam * (R / 4))) ^ 2) :=
              mul_le_mul_of_nonneg_left hfinal hge
      calc ∑ j ∈ Finset.Ico K n, W j * |∑ i ∈ Finset.range j, A i|
          ≤ ∑ j ∈ Finset.Ico K n, W j
              * (8 * (1 + Real.log R) + ∑ i ∈ Finset.Ico j n, |A i|) := by
            apply Finset.sum_le_sum
            intro j hj
            exact mul_le_mul_of_nonneg_left (hSj j hj) (hW_nn j)
        _ = 8 * (1 + Real.log R) * (∑ j ∈ Finset.Ico K n, W j)
              + ∑ j ∈ Finset.Ico K n, W j * (∑ i ∈ Finset.Ico j n, |A i|) := by
            have hs : ∑ j ∈ Finset.Ico K n, W j
                * (8 * (1 + Real.log R) + ∑ i ∈ Finset.Ico j n, |A i|)
                = ∑ j ∈ Finset.Ico K n, (8 * (1 + Real.log R) * W j
                    + W j * (∑ i ∈ Finset.Ico j n, |A i|)) := by
              apply Finset.sum_congr rfl
              intro j hj
              ring
            rw [hs, Finset.sum_add_distrib, ← Finset.mul_sum]
        _ ≤ 8 * (1 + Real.log R) * (24 * mu * psi / R)
              + 3 * mu * psi * lam ^ 2
                * ((1 / (lam / 3)) / Real.sin (lam * (R / 4))
                  + 1 / (Real.sin (lam * (R / 4))) ^ 2) := by
            have h1 := mul_le_mul_of_nonneg_left hWR
              (by positivity : (0:ℝ) ≤ 8 * (1 + Real.log R))
            linarith [h1, htail]
        _ = 192 * mu * psi * (1 + Real.log R) / R
              + 3 * mu * psi * lam ^ 2
                * ((1 / (lam / 3)) / Real.sin (lam * (R / 4))
                  + 1 / (Real.sin (lam * (R / 4))) ^ 2) := by ring

  -- ==================== assembly ====================
  have hdisj : Disjoint (Finset.range K) (Finset.Ico K n) := by
    rw [Finset.disjoint_left]
    intro a ha hb
    rw [Finset.mem_range] at ha
    rw [Finset.mem_Ico] at hb
    omega
  have hset : Finset.range K ∪ Finset.Ico K n = Finset.range n := by
    rw [Finset.range_eq_Ico K, Finset.range_eq_Ico n]
    exact Finset.Ico_union_Ico_eq_Ico (Nat.zero_le K) hKn
  have hsplitT : ∑ j ∈ Finset.range n, W j * |∑ i ∈ Finset.range j, A i|
      = (∑ j ∈ Finset.range K, W j * |∑ i ∈ Finset.range j, A i|)
        + ∑ j ∈ Finset.Ico K n, W j * |∑ i ∈ Finset.range j, A i| := by
    rw [← hset, Finset.sum_union hdisj]
  have htotal : ∑ j ∈ Finset.range n, W j * |∑ i ∈ Finset.range j, A i|
      ≤ 72 * mu * psi / R + (192 * mu * psi * (1 + Real.log R) / R
        + 3 * mu * psi * lam ^ 2 * ((1 / (lam / 3)) / Real.sin (lam * (R / 4))
              + 1 / (Real.sin (lam * (R / 4))) ^ 2)) := by
    rw [hsplitT]
    linarith [hLpart, hRpart]
  have hx0 : 0 < lam * (R / 4) := mul_pos hlam (by linarith)
  have hxp : lam * (R / 4) ≤ Real.pi / 2 := by
    have h1 : lam * (R / 4) ≤ 1 / 4 := by nlinarith [hlamR, hR, hlam]
    linarith [Real.pi_gt_three]
  have hsin_ge : (2 / Real.pi) * (lam * (R / 4)) ≤ Real.sin (lam * (R / 4)) :=
    Real.mul_le_sin hx0.le hxp
  have h2p : 0 < (2 / Real.pi) * (lam * (R / 4)) := by positivity
  have h1div : 1 / Real.sin (lam * (R / 4)) ≤ 2 * Real.pi / (lam * R) := by
    have := one_div_le_one_div_of_le h2p hsin_ge
    rwa [show (1:ℝ) / ((2 / Real.pi) * (lam * (R / 4))) = 2 * Real.pi / (lam * R) from by
      field_simp; ring] at this
  have h2div : 1 / (Real.sin (lam * (R / 4))) ^ 2 ≤ (2 * Real.pi / (lam * R)) ^ 2 := by
    have h1' : (0:ℝ) ≤ 1 / Real.sin (lam * (R / 4)) := by positivity
    have h3 : (1 / Real.sin (lam * (R / 4))) ^ 2 ≤ (2 * Real.pi / (lam * R)) ^ 2 :=
      pow_le_pow_left₀ h1' h1div 2
    rwa [one_div_pow] at h3
  have hsum3 : 3 * mu * psi * lam ^ 2 * ((1 / (lam / 3)) / Real.sin (lam * (R / 4))
        + 1 / (Real.sin (lam * (R / 4))) ^ 2)
      ≤ 18 * Real.pi * mu * psi / R + 12 * Real.pi ^ 2 * mu * psi / R ^ 2 := by
    have h3 : (0:ℝ) ≤ 3 * mu * psi * lam ^ 2 := by positivity
    have h4 : (1 / (lam / 3)) / Real.sin (lam * (R / 4))
          + 1 / (Real.sin (lam * (R / 4))) ^ 2
        ≤ (1 / (lam / 3)) * (2 * Real.pi / (lam * R)) + (2 * Real.pi / (lam * R)) ^ 2 := by
      have e1 : (1 / (lam / 3)) / Real.sin (lam * (R / 4))
          = (1 / (lam / 3)) * (1 / Real.sin (lam * (R / 4))) := by ring
      have e2 : (1 / (lam / 3)) * (1 / Real.sin (lam * (R / 4)))
          ≤ (1 / (lam / 3)) * (2 * Real.pi / (lam * R)) :=
        mul_le_mul_of_nonneg_left h1div (by positivity)
      linarith [e1, e2, h2div]
    calc 3 * mu * psi * lam ^ 2 * ((1 / (lam / 3)) / Real.sin (lam * (R / 4))
            + 1 / (Real.sin (lam * (R / 4))) ^ 2)
        ≤ 3 * mu * psi * lam ^ 2
            * ((1 / (lam / 3)) * (2 * Real.pi / (lam * R)) + (2 * Real.pi / (lam * R)) ^ 2) :=
          mul_le_mul_of_nonneg_left h4 h3
      _ = 18 * Real.pi * mu * psi / R + 12 * Real.pi ^ 2 * mu * psi / R ^ 2 := by
          field_simp; ring
  have harith : 72 * mu * psi / R + (192 * mu * psi * (1 + Real.log R) / R
        + 3 * mu * psi * lam ^ 2 * ((1 / (lam / 3)) / Real.sin (lam * (R / 4))
              + 1 / (Real.sin (lam * (R / 4))) ^ 2))
      ≤ 500 * mu * psi * (1 + Real.log R) / R := by
    have hp2 : Real.pi ^ 2 < 10 := by nlinarith [Real.pi_lt_d2, Real.pi_pos]
    have h12 : 12 * Real.pi ^ 2 / R ≤ 1 := by
      rw [div_le_one hRpos]
      nlinarith [hp2, hR]
    have hkey : 72 + 192 * (1 + Real.log R) + 18 * Real.pi + 12 * Real.pi ^ 2 / R
        ≤ 500 * (1 + Real.log R) := by
      linarith [hlogR, Real.pi_lt_d2, h12]
    have hmp : 0 ≤ mu * psi / R := by positivity
    have hX : 3 * mu * psi * lam ^ 2 * ((1 / (lam / 3)) / Real.sin (lam * (R / 4))
          + 1 / (Real.sin (lam * (R / 4))) ^ 2)
        ≤ (mu * psi / R) * (18 * Real.pi + 12 * Real.pi ^ 2 / R) := by
      have e : 18 * Real.pi * mu * psi / R + 12 * Real.pi ^ 2 * mu * psi / R ^ 2
          = (mu * psi / R) * (18 * Real.pi + 12 * Real.pi ^ 2 / R) := by field_simp
      linarith [hsum3, e]
    have hkey2 : (mu * psi / R) * (72 + 192 * (1 + Real.log R))
        + (mu * psi / R) * (18 * Real.pi + 12 * Real.pi ^ 2 / R)
        ≤ (mu * psi / R) * (500 * (1 + Real.log R)) := by
      have h1 := mul_le_mul_of_nonneg_left hkey hmp
      have h2 : (mu * psi / R) * (72 + 192 * (1 + Real.log R) + 18 * Real.pi
            + 12 * Real.pi ^ 2 / R)
          = (mu * psi / R) * (72 + 192 * (1 + Real.log R))
            + (mu * psi / R) * (18 * Real.pi + 12 * Real.pi ^ 2 / R) := by ring
      linarith [h1, h2]
    have e0 : 72 * mu * psi / R + (192 * mu * psi * (1 + Real.log R) / R
          + 3 * mu * psi * lam ^ 2 * ((1 / (lam / 3)) / Real.sin (lam * (R / 4))
                + 1 / (Real.sin (lam * (R / 4))) ^ 2))
        = (mu * psi / R) * (72 + 192 * (1 + Real.log R))
          + 3 * mu * psi * lam ^ 2 * ((1 / (lam / 3)) / Real.sin (lam * (R / 4))
                + 1 / (Real.sin (lam * (R / 4))) ^ 2) := by ring
    have e1 : (mu * psi / R) * (500 * (1 + Real.log R))
        = 500 * mu * psi * (1 + Real.log R) / R := by field_simp
    linarith [e0, hX, hkey2, e1]
  linarith [htotal, harith]


end Work.PARIMPL2.Direct
