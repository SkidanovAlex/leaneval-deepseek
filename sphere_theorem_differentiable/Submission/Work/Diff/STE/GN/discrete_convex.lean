import Mathlib

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false

set_option linter.unusedVariables false

namespace Work.Diff.STE.GN

/-! ## Discrete log-convexity

This file proves `Work.Diff.STE.GN.discrete_convex`.  The mathematical content is the classical
Hadamard-three-lines / log-convexity statement for a finite sequence, with a `C`-twisting that
accounts for the growth factors.

The proof is organised as follows.

* `mul_sum_range_le` : for a nondecreasing sequence `d`, the prefix average is at most the full
  average, `m * ∑_{k<j} d k ≤ j * ∑_{k<m} d k`.
* `chord_of_convex` : a discretely convex sequence `u` (`2 u k ≤ u (k-1) + u (k+1)`) lies below
  the chord through its endpoints, `m * u j ≤ (m-j) u 0 + j u m`.
* `interp_of_logconvex` : a positive sequence `b` with `b k ^ 2 ≤ b (k-1) * b (k+1)` has a
  convex logarithm, hence `b j ≤ (b 0)^(1-j/m) (b m)^(j/m)`.
* `interp_of_logconvex_nonneg` : the same without positivity, by perturbing `b` to `b + ε` and
  passing to the limit `ε → 0⁺`.
* `interp_logconvex_shift` : if moreover `a k ^ 2 ≤ D * a (k-1) * a (k+1)` with `D ≥ 1`, the
  interpolation carries an extra factor `D ^ (j (m-j)/2)` (the sequence `k ↦ a k * D^(k²/2)` is
  log-convex).
* `discrete_convex` : the constant `D := max 1 (max_{k ≤ m} C k)` converts the hypothesis on `C`
  into the previous form, and `j (m-j)/2 ≤ m²/8` bounds the extra factor. -/

/-- Arithmetic–geometric mean in the form needed to keep the perturbation `b + ε` log-convex. -/
lemma two_mul_le_add_of_sq_le_mul {x y z : ℝ} (hx : 0 ≤ x) (hy : 0 ≤ y) (hz : 0 ≤ z)
    (h : z ^ 2 ≤ x * y) : 2 * z ≤ x + y := by
  have h1 : z ≤ Real.sqrt (x * y) := by
    have hz' : Real.sqrt (z ^ 2) = z := by rw [Real.sqrt_sq_eq_abs, abs_of_nonneg hz]
    rw [← hz']
    exact Real.sqrt_le_sqrt h
  have h2 : 2 * Real.sqrt (x * y) ≤ x + y := by
    rw [Real.sqrt_mul hx]
    nlinarith [sq_nonneg (Real.sqrt x - Real.sqrt y), Real.sq_sqrt hx, Real.sq_sqrt hy]
  linarith

/-- Monotonicity of a sequence on an initial segment. -/
lemma le_of_mono_range {d : ℕ → ℝ} {m : ℕ} (h : ∀ k, k + 2 ≤ m → d k ≤ d (k + 1)) :
    ∀ i j : ℕ, i ≤ j → j + 1 ≤ m → d i ≤ d j := by
  intro i j hij hj
  exact Nat.le_induction (fun _ => le_rfl)
    (fun n _ ih hnm => le_trans (ih (by omega)) (h n (by omega))) j hij hj

/-- For a sequence nondecreasing up to index `m - 1`, every prefix average is at most the full
average. -/
lemma mul_sum_range_le (d : ℕ → ℝ) (m : ℕ)
    (hmono : ∀ i j : ℕ, i ≤ j → j + 1 ≤ m → d i ≤ d j) :
    ∀ j : ℕ, j ≤ m →
      (m : ℝ) * (∑ k ∈ Finset.range j, d k) ≤ (j : ℝ) * (∑ k ∈ Finset.range m, d k) := by
  induction m with
  | zero => intro j _; simp
  | succ m ih =>
    intro j hj
    rcases Nat.lt_or_ge j (m + 1) with hlt | hge
    · have hj' : j ≤ m := Nat.lt_succ_iff.mp hlt
      have hmono' : ∀ i j' : ℕ, i ≤ j' → j' + 1 ≤ m → d i ≤ d j' :=
        fun i j' hij hj' => hmono i j' hij (by omega)
      have hIH := ih hmono' j hj'
      have hP : (∑ k ∈ Finset.range j, d k) ≤ (j : ℝ) * d m := by
        calc (∑ k ∈ Finset.range j, d k) ≤ ∑ k ∈ Finset.range j, d m :=
              Finset.sum_le_sum (fun k hk => hmono k m (by
                have hk' := Finset.mem_range.mp hk; omega) le_rfl)
          _ = (j : ℝ) * d m := by simp
      rw [Finset.sum_range_succ]
      push_cast
      nlinarith [hIH, hP]
    · have hje : j = m + 1 := by omega
      subst hje
      exact le_rfl

/-- A discretely convex sequence lies below the chord joining its endpoints. -/
lemma chord_of_convex (m : ℕ) (u : ℕ → ℝ)
    (h : ∀ k, 1 ≤ k → k + 1 ≤ m → 2 * u k ≤ u (k - 1) + u (k + 1)) :
    ∀ j : ℕ, j ≤ m → (m : ℝ) * u j ≤ ((m - j : ℕ) : ℝ) * u 0 + (j : ℝ) * u m := by
  intro j hj
  rcases Nat.eq_zero_or_pos m with hm0 | hmpos
  · subst hm0
    have : j = 0 := by omega
    subst this
    simp
  · set w : ℕ → ℝ := fun k => (m : ℝ) * u k - ((m - (k : ℝ)) * u 0 + (k : ℝ) * u m) with hw
    have hmR : (0 : ℝ) < (m : ℝ) := by exact_mod_cast hmpos
    have hw0 : w 0 = 0 := by simp [hw]
    have hwm : w m = 0 := by
      simp only [hw]
      ring
    have hwconv : ∀ k, 1 ≤ k → k + 1 ≤ m → 2 * w k ≤ w (k - 1) + w (k + 1) := by
      intro k h1 h2
      have hk := h k h1 h2
      have hc1 : ((k - 1 : ℕ) : ℝ) = (k : ℝ) - 1 := by
        rw [Nat.cast_sub h1]; norm_num
      have hc2 : ((k + 1 : ℕ) : ℝ) = (k : ℝ) + 1 := by push_cast; ring
      simp only [hw]
      rw [hc1, hc2]
      have hA : 0 ≤ u (k - 1) + u (k + 1) - 2 * u k := by linarith [hk]
      have hmul : 0 ≤ (m : ℝ) * (u (k - 1) + u (k + 1) - 2 * u k) :=
        mul_nonneg hmR.le hA
      linarith [hmul]
    have hwstep : ∀ k, k + 2 ≤ m →
        w (k + 1) - w k ≤ w ((k + 1) + 1) - w (k + 1) := by
      intro k hk
      have hc := hwconv (k + 1) (by omega) (by omega)
      have hsub : (k + 1) - 1 = k := by omega
      rw [hsub] at hc
      linarith [hc]
    have hmono : ∀ i j' : ℕ, i ≤ j' → j' + 1 ≤ m →
        w (i + 1) - w i ≤ w (j' + 1) - w j' := le_of_mono_range hwstep
    have hkey := mul_sum_range_le (fun k => w (k + 1) - w k) m hmono j hj
    have hsumj : (∑ k ∈ Finset.range j, (w (k + 1) - w k)) = w j - w 0 :=
      Finset.sum_range_sub w j
    have hsumm : (∑ k ∈ Finset.range m, (w (k + 1) - w k)) = w m - w 0 :=
      Finset.sum_range_sub w m
    rw [hsumj, hsumm, hw0, hwm] at hkey
    have hwj : w j ≤ 0 := by
      have h1 : (m : ℝ) * w j ≤ 0 := by linarith [hkey]
      have h2 : ((m : ℝ) * w j) / m = w j := by
        rw [mul_comm (m : ℝ) (w j)]
        exact mul_div_cancel_right₀ _ hmR.ne'
      calc w j = ((m : ℝ) * w j) / m := h2.symm
        _ ≤ 0 := div_nonpos_of_nonpos_of_nonneg h1 hmR.le
    simp only [hw] at hwj
    rw [Nat.cast_sub hj]
    linarith

/-- A positive sequence with `b k ^ 2 ≤ b (k-1) * b (k+1)` interpolates between its endpoints. -/
lemma interp_of_logconvex (m : ℕ) (b : ℕ → ℝ) (hb : ∀ k, 0 < b k)
    (h : ∀ k, 1 ≤ k → k + 1 ≤ m → (b k) ^ 2 ≤ b (k - 1) * b (k + 1)) :
    ∀ j : ℕ, j ≤ m →
      b j ≤ (b 0) ^ (1 - (j : ℝ) / m) * (b m) ^ ((j : ℝ) / m) := by
  intro j hj
  rcases Nat.eq_zero_or_pos m with hm0 | hmpos
  · subst hm0
    have hj0 : j = 0 := by omega
    subst hj0
    simp [Real.rpow_one, Real.rpow_zero]
  · have hmR : (0 : ℝ) < (m : ℝ) := by exact_mod_cast hmpos
    have hconv : ∀ k, 1 ≤ k → k + 1 ≤ m →
        2 * Real.log (b k) ≤ Real.log (b (k - 1)) + Real.log (b (k + 1)) := by
      intro k h1 h2
      have hk := h k h1 h2
      have hlog := Real.log_le_log (pow_pos (hb k) 2) hk
      rw [Real.log_pow, Real.log_mul (ne_of_gt (hb (k - 1))) (ne_of_gt (hb (k + 1)))] at hlog
      simpa using hlog
    have hchord := chord_of_convex m (fun k => Real.log (b k)) hconv j hj
    have hstep : Real.log (b j) ≤
        (1 - (j : ℝ) / m) * Real.log (b 0) + ((j : ℝ) / m) * Real.log (b m) := by
      have h : Real.log (b j) ≤
          (((m - j : ℕ) : ℝ) * Real.log (b 0) + (j : ℝ) * Real.log (b m)) / m := by
        have hc := hchord
        rw [Nat.cast_sub hj] at hc
        rw [le_div_iff₀ hmR, Nat.cast_sub hj]
        linarith
      have hrw : (((m - j : ℕ) : ℝ) * Real.log (b 0) + (j : ℝ) * Real.log (b m)) / m
          = (1 - (j : ℝ) / m) * Real.log (b 0) + ((j : ℝ) / m) * Real.log (b m) := by
        rw [Nat.cast_sub hj]
        field_simp
      rw [hrw] at h
      exact h
    have e1 : Real.exp ((1 - (j : ℝ) / m) * Real.log (b 0)) =
        (b 0) ^ (1 - (j : ℝ) / m) := by
      rw [Real.rpow_def_of_pos (hb 0)]
      congr 1
      ring
    have e2 : Real.exp (((j : ℝ) / m) * Real.log (b m)) = (b m) ^ ((j : ℝ) / m) := by
      rw [Real.rpow_def_of_pos (hb m)]
      congr 1
      ring
    calc b j = Real.exp (Real.log (b j)) := (Real.exp_log (hb j)).symm
      _ ≤ Real.exp ((1 - (j : ℝ) / m) * Real.log (b 0) + ((j : ℝ) / m) * Real.log (b m)) :=
            Real.exp_le_exp.mpr hstep
      _ = Real.exp ((1 - (j : ℝ) / m) * Real.log (b 0)) *
            Real.exp (((j : ℝ) / m) * Real.log (b m)) := Real.exp_add _ _
      _ = (b 0) ^ (1 - (j : ℝ) / m) * (b m) ^ ((j : ℝ) / m) := by rw [e1, e2]

/-- The same interpolation for a merely nonnegative sequence, obtained by perturbing `b` to
`b + ε` (`ε > 0`) and letting `ε → 0⁺`. -/
lemma interp_of_logconvex_nonneg (m : ℕ) (b : ℕ → ℝ) (hb : ∀ k, 0 ≤ b k)
    (h : ∀ k, 1 ≤ k → k + 1 ≤ m → (b k) ^ 2 ≤ b (k - 1) * b (k + 1)) :
    ∀ j : ℕ, j ≤ m →
      b j ≤ (b 0) ^ (1 - (j : ℝ) / m) * (b m) ^ ((j : ℝ) / m) := by
  intro j hj
  rcases Nat.eq_zero_or_pos m with hm0 | hmpos
  · subst hm0
    have hj0 : j = 0 := by omega
    subst hj0
    simp [Real.rpow_one, Real.rpow_zero]
  · have hmR : (0 : ℝ) < (m : ℝ) := by exact_mod_cast hmpos
    set t : ℝ := 1 - (j : ℝ) / m with ht
    set s : ℝ := (j : ℝ) / m with hs
    have ht0 : 0 ≤ t := by
      rw [ht]
      have : (j : ℝ) / m ≤ 1 := by
        rw [div_le_one hmR]
        exact_mod_cast hj
      linarith
    have hs0 : 0 ≤ s := by
      rw [hs]
      positivity
    have hseq : ∀ n : ℕ,
        b j ≤ (b 0 + 1 / ((n : ℝ) + 1)) ^ t * (b m + 1 / ((n : ℝ) + 1)) ^ s := by
      intro n
      have hε0 : (0 : ℝ) < 1 / ((n : ℝ) + 1) := by positivity
      have hbpos : ∀ k, 0 < b k + 1 / ((n : ℝ) + 1) := fun k => by linarith [hb k]
      have hpert : ∀ k, 1 ≤ k → k + 1 ≤ m →
          (b k + 1 / ((n : ℝ) + 1)) ^ 2 ≤
            (b (k - 1) + 1 / ((n : ℝ) + 1)) * (b (k + 1) + 1 / ((n : ℝ) + 1)) := by
        intro k h1 h2
        have hk := h k h1 h2
        have ham : 2 * b k ≤ b (k - 1) + b (k + 1) :=
          two_mul_le_add_of_sq_le_mul (hb (k - 1)) (hb (k + 1)) (hb k) hk
        have hkey : (1 / ((n : ℝ) + 1)) * (2 * b k - (b (k - 1) + b (k + 1))) ≤ 0 :=
          mul_nonpos_of_nonneg_of_nonpos hε0.le (by linarith)
        nlinarith [hk, hkey]
      have hint := interp_of_logconvex m (fun k => b k + 1 / ((n : ℝ) + 1)) hbpos hpert j hj
      have hle : b j ≤ (b 0 + 1 / ((n : ℝ) + 1)) ^ (1 - (j : ℝ) / m) *
          (b m + 1 / ((n : ℝ) + 1)) ^ ((j : ℝ) / m) := by linarith
      simpa [ht, hs] using hle
    have htend : Filter.Tendsto
        (fun n : ℕ => (b 0 + 1 / ((n : ℝ) + 1)) ^ t * (b m + 1 / ((n : ℝ) + 1)) ^ s)
        Filter.atTop (nhds ((b 0) ^ t * (b m) ^ s)) := by
      have h0 : Filter.Tendsto (fun n : ℕ => (1 : ℝ) / ((n : ℝ) + 1)) Filter.atTop (nhds 0) :=
        tendsto_one_div_add_atTop_nhds_zero_nat
      have h1 : Filter.Tendsto (fun n : ℕ => b 0 + 1 / ((n : ℝ) + 1)) Filter.atTop
          (nhds (b 0)) := by
        simpa using tendsto_const_nhds.add h0
      have h2 : Filter.Tendsto (fun n : ℕ => (b 0 + 1 / ((n : ℝ) + 1)) ^ t) Filter.atTop
          (nhds ((b 0) ^ t)) :=
        (Real.continuousAt_rpow_const (b 0) t (Or.inr ht0)).tendsto.comp h1
      have h1' : Filter.Tendsto (fun n : ℕ => b m + 1 / ((n : ℝ) + 1)) Filter.atTop
          (nhds (b m)) := by
        simpa using tendsto_const_nhds.add h0
      have h3 : Filter.Tendsto (fun n : ℕ => (b m + 1 / ((n : ℝ) + 1)) ^ s) Filter.atTop
          (nhds ((b m) ^ s)) :=
        (Real.continuousAt_rpow_const (b m) s (Or.inr hs0)).tendsto.comp h1'
      exact h2.mul h3
    exact le_of_tendsto_of_tendsto' tendsto_const_nhds htend hseq

/-- If `a ≥ 0` satisfies `a k ^ 2 ≤ D * a (k-1) * a (k+1)` with `D ≥ 1`, the interpolation gains
the correction factor `D ^ (j (m-j) / 2)`: the sequence `k ↦ a k * D ^ (k²/2)` is log-convex. -/
lemma interp_logconvex_shift (m : ℕ) (D : ℝ) (hD : 1 ≤ D) (a : ℕ → ℝ) (ha : ∀ k, 0 ≤ a k)
    (h : ∀ k, 1 ≤ k → k + 1 ≤ m → (a k) ^ 2 ≤ D * a (k - 1) * a (k + 1)) :
    ∀ j : ℕ, j ≤ m →
      a j ≤ (a 0) ^ (1 - (j : ℝ) / m) * (a m) ^ ((j : ℝ) / m) *
        D ^ ((j : ℝ) * ((m - j : ℕ) : ℝ) / 2) := by
  intro j hj
  rcases Nat.eq_zero_or_pos m with hm0 | hmpos
  · subst hm0
    have hj0 : j = 0 := by omega
    subst hj0
    simp [Real.rpow_one, Real.rpow_zero]
  · have hDpos : (0 : ℝ) < D := lt_of_lt_of_le zero_lt_one hD
    have hmR : (0 : ℝ) < (m : ℝ) := by exact_mod_cast hmpos
    set B : ℕ → ℝ := fun k => a k * D ^ ((k : ℝ) ^ 2 / 2) with hB
    have hBnn : ∀ k, 0 ≤ B k := fun k => mul_nonneg (ha k) (Real.rpow_nonneg hDpos.le _)
    have hBcond : ∀ k, 1 ≤ k → k + 1 ≤ m → (B k) ^ 2 ≤ B (k - 1) * B (k + 1) := by
      intro k h1 h2
      have hk := h k h1 h2
      have hc1 : ((k - 1 : ℕ) : ℝ) = (k : ℝ) - 1 := by
        rw [Nat.cast_sub h1]; norm_num
      have hc2 : ((k + 1 : ℕ) : ℝ) = (k : ℝ) + 1 := by push_cast; ring
      have hpow : (D ^ ((k : ℝ) ^ 2 / 2)) ^ 2 = D ^ ((k : ℝ) ^ 2) := by
        rw [← Real.rpow_natCast (D ^ ((k : ℝ) ^ 2 / 2)) 2, ← Real.rpow_mul hDpos.le]
        congr 1
        push_cast
        ring
      have hp : D ^ (((k : ℝ) - 1) ^ 2 / 2) * D ^ (((k : ℝ) + 1) ^ 2 / 2) =
          D ^ ((k : ℝ) ^ 2 + 1) := by
        rw [← Real.rpow_add hDpos]
        congr 1
        ring
      have e1 : (B k) ^ 2 = (a k) ^ 2 * D ^ ((k : ℝ) ^ 2) := by
        simp only [hB]
        rw [mul_pow, hpow]
      have e2 : B (k - 1) * B (k + 1) =
          (a (k - 1) * a (k + 1)) * D ^ ((k : ℝ) ^ 2 + 1) := by
        simp only [hB, hc1, hc2]
        rw [← hp]
        ring
      rw [e1, e2]
      have haux : (a k) ^ 2 ≤ D * (a (k - 1) * a (k + 1)) := by
        calc (a k) ^ 2 ≤ D * a (k - 1) * a (k + 1) := hk
          _ = D * (a (k - 1) * a (k + 1)) := by ring
      calc (a k) ^ 2 * D ^ ((k : ℝ) ^ 2)
          ≤ (D * (a (k - 1) * a (k + 1))) * D ^ ((k : ℝ) ^ 2) :=
            mul_le_mul_of_nonneg_right haux (Real.rpow_nonneg hDpos.le _)
        _ = (a (k - 1) * a (k + 1)) * D ^ ((k : ℝ) ^ 2 + 1) := by
            rw [Real.rpow_add hDpos, Real.rpow_one]; ring
    have hint := interp_of_logconvex_nonneg m B hBnn hBcond j hj
    have hB0 : B 0 = a 0 := by simp [hB]
    have hBm : B m = a m * D ^ ((m : ℝ) ^ 2 / 2) := by simp [hB]
    have hBms : (B m) ^ ((j : ℝ) / m) =
        (a m) ^ ((j : ℝ) / m) * D ^ (((m : ℝ) ^ 2 / 2) * ((j : ℝ) / m)) := by
      rw [hBm, Real.mul_rpow (ha m) (Real.rpow_nonneg hDpos.le _), ← Real.rpow_mul hDpos.le]
    have hkey : a j * D ^ ((j : ℝ) ^ 2 / 2) ≤
        ((a 0) ^ (1 - (j : ℝ) / m) * (a m) ^ ((j : ℝ) / m)) *
          D ^ (((m : ℝ) ^ 2 / 2) * ((j : ℝ) / m)) := by
      have hBj : B j = a j * D ^ ((j : ℝ) ^ 2 / 2) := by simp [hB]
      calc a j * D ^ ((j : ℝ) ^ 2 / 2) = B j := hBj.symm
        _ ≤ (B 0) ^ (1 - (j : ℝ) / m) * (B m) ^ ((j : ℝ) / m) := hint
        _ = ((a 0) ^ (1 - (j : ℝ) / m)) *
              ((a m) ^ ((j : ℝ) / m) * D ^ (((m : ℝ) ^ 2 / 2) * ((j : ℝ) / m))) := by
              rw [hB0, hBms]
        _ = ((a 0) ^ (1 - (j : ℝ) / m) * (a m) ^ ((j : ℝ) / m)) *
              D ^ (((m : ℝ) ^ 2 / 2) * ((j : ℝ) / m)) := by ring
    have hexp_eq : ((m : ℝ) ^ 2 / 2) * ((j : ℝ) / m) =
        (j : ℝ) * ((m - j : ℕ) : ℝ) / 2 + (j : ℝ) ^ 2 / 2 := by
      rw [Nat.cast_sub hj]
      field_simp
      ring
    have hDpowpos : 0 < D ^ ((j : ℝ) ^ 2 / 2) := Real.rpow_pos_of_pos hDpos _
    refine (mul_le_mul_iff_of_pos_right hDpowpos).mp ?_
    calc a j * D ^ ((j : ℝ) ^ 2 / 2)
        ≤ ((a 0) ^ (1 - (j : ℝ) / m) * (a m) ^ ((j : ℝ) / m)) *
            D ^ (((m : ℝ) ^ 2 / 2) * ((j : ℝ) / m)) := hkey
      _ = ((a 0) ^ (1 - (j : ℝ) / m) * (a m) ^ ((j : ℝ) / m)) *
            (D ^ ((j : ℝ) * ((m - j : ℕ) : ℝ) / 2) * D ^ ((j : ℝ) ^ 2 / 2)) := by
            rw [hexp_eq, Real.rpow_add hDpos]
      _ = (((a 0) ^ (1 - (j : ℝ) / m) * (a m) ^ ((j : ℝ) / m)) *
            D ^ ((j : ℝ) * ((m - j : ℕ) : ℝ) / 2)) * D ^ ((j : ℝ) ^ 2 / 2) := by ring

/-- **Discrete log-convexity.**  There is a constant `K`, depending only on `m` and the sequence
`C : ℕ → ℝ`, such that for every nonnegative sequence `a` with
`a k ^ 2 ≤ C k * a (k-1) * a (k+1)` for `1 ≤ k ≤ m-1`, one has
`a j ≤ K * (a 0)^(1 - j/m) * (a m)^(j/m)` for every `j ≤ m`

Proof: with `D := max 1 (max_{k ≤ m} C k)` the sequence `b k := a k * D^(k²/2)` satisfies
`b k ^ 2 ≤ b (k-1) * b (k+1)` (because `a k ^ 2 ≤ D * a (k-1) * a (k+1)` and
`(k-1)²/2 + (k+1)²/2 = k² + 1`), so `k ↦ log (b k)` is convex and hence lies below its chord,
giving `b j ≤ b 0^(1-j/m) b m^(j/m)`, i.e. `a j ≤ a 0^(1-j/m) a m^(j/m) D^(j(m-j)/2)`, and
`j (m-j)/2 ≤ m²/8`. -/
theorem discrete_convex (m : ℕ) (C : ℕ → ℝ) (hC : ∀ k, 0 ≤ C k) :
    ∃ K : ℝ, 0 ≤ K ∧ ∀ (a : ℕ → ℝ), (∀ k, 0 ≤ a k) →
      (∀ k, 1 ≤ k → k + 1 ≤ m → (a k) ^ 2 ≤ C k * a (k - 1) * a (k + 1)) →
      ∀ j : ℕ, j ≤ m →
        a j ≤ K * (a 0) ^ (1 - (j : ℝ) / m) * (a m) ^ ((j : ℝ) / m) := by
  rcases Nat.eq_zero_or_pos m with hm0 | hmpos
  · subst hm0
    refine ⟨1, zero_le_one, ?_⟩
    intro a ha hcond j hj
    have hj0 : j = 0 := by omega
    subst hj0
    simp [Real.rpow_one, Real.rpow_zero]
  · obtain ⟨D, hD1, hDC⟩ : ∃ D : ℝ, 1 ≤ D ∧ ∀ k ≤ m, C k ≤ D := by
      refine ⟨max 1 ((Finset.range (m + 1)).sup' ⟨0, by simp⟩ C), le_max_left _ _, ?_⟩
      intro k hk
      exact le_trans (Finset.le_sup' C (Finset.mem_range.mpr (by omega))) (le_max_right _ _)
    refine ⟨D ^ ((m : ℝ) ^ 2 / 8), Real.rpow_nonneg (by linarith) _, ?_⟩
    intro a ha hcond j hj
    have hshift := interp_logconvex_shift m D hD1 a ha (fun k h1 h2 => by
      have hle : C k ≤ D := hDC k (by omega)
      calc (a k) ^ 2 ≤ C k * a (k - 1) * a (k + 1) := hcond k h1 h2
        _ ≤ D * a (k - 1) * a (k + 1) :=
            mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_right hle (ha (k - 1)))
              (ha (k + 1))) j hj
    calc a j ≤ (a 0) ^ (1 - (j : ℝ) / m) * (a m) ^ ((j : ℝ) / m) *
              D ^ ((j : ℝ) * ((m - j : ℕ) : ℝ) / 2) := hshift
      _ ≤ (a 0) ^ (1 - (j : ℝ) / m) * (a m) ^ ((j : ℝ) / m) * D ^ ((m : ℝ) ^ 2 / 8) := by
            apply mul_le_mul_of_nonneg_left _
              (mul_nonneg (Real.rpow_nonneg (ha 0) _) (Real.rpow_nonneg (ha m) _))
            apply Real.rpow_le_rpow_of_exponent_le hD1
            rw [Nat.cast_sub hj]
            nlinarith [sq_nonneg ((m : ℝ) - 2 * (j : ℝ))]
      _ = D ^ ((m : ℝ) ^ 2 / 8) * (a 0) ^ (1 - (j : ℝ) / m) * (a m) ^ ((j : ℝ) / m) := by
            ring

end Work.Diff.STE.GN
