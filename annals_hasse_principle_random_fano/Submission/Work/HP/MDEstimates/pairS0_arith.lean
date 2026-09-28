import Mathlib
import Submission.Work.HP.Defs
import Submission.Work.HP.Lat.card_Mon

set_option autoImplicit false

noncomputable section

namespace Work.HP.MDEstimates

open Work.HP

/-- `N_{d,n}` is the binomial coefficient `(n+d).choose d`. -/
lemma NN_eq_choose (d n : ℕ) : (NN d n : ℝ) = ((n + d).choose d : ℝ) := by
  rw [NN, Lat.card_Mon]

/-- Two terms of Vandermonde give `(n+d).choose d ≥ n·d + (n.choose 2)(d.choose 2)`. -/
lemma choose_lower (d n : ℕ) (hd : 2 ≤ d) :
    (n : ℝ) * d + ((n.choose 2 : ℕ) : ℝ) * ((d.choose 2 : ℕ) : ℝ)
      ≤ ((n + d).choose d : ℝ) := by
  have hsub : ({(1, d - 1), (2, d - 2)} : Finset (ℕ × ℕ)) ⊆
      Finset.HasAntidiagonal.antidiagonal d := by
    intro ij hij
    simp only [Finset.mem_insert, Finset.mem_singleton] at hij
    rcases hij with h | h
    · rw [h]; exact Finset.HasAntidiagonal.mem_antidiagonal.mpr (by omega)
    · rw [h]; exact Finset.HasAntidiagonal.mem_antidiagonal.mpr (by omega)
  have hle : (∑ i ∈ ({(1, d - 1), (2, d - 2)} : Finset (ℕ × ℕ)),
        n.choose i.1 * d.choose i.2) ≤ (n + d).choose d := by
    rw [Nat.add_choose_eq n d d]
    exact Finset.sum_le_sum_of_subset_of_nonneg hsub
      (fun ij _ _ => Nat.zero_le (n.choose ij.1 * d.choose ij.2))
  rw [Finset.sum_insert (by rintro h; simp at h), Finset.sum_singleton] at hle
  have h1 : n.choose 1 * d.choose (d - 1) = n * d := by
    rw [Nat.choose_one_right, Nat.choose_symm (n := d) (k := 1) (by omega),
      Nat.choose_one_right]
  have h2 : n.choose 2 * d.choose (d - 2) = n.choose 2 * d.choose 2 := by
    rw [Nat.choose_symm (n := d) (k := 2) (by omega)]
  rw [h1, h2] at hle
  exact_mod_cast hle

/-- The exponent gap `N_{d,n} - 4 - 2d/(n+1-d)` is positive for `2 ≤ d ≤ n` and `(d,n) ≠ (2,2)`. -/
lemma arith_gap (d n : ℕ) (hd : 2 ≤ d) (hdn : d ≤ n) (h22 : (d, n) ≠ (2, 2)) :
    4 + 2 * (d : ℝ) / ((n : ℝ) + 1 - d) < (NN d n : ℝ) := by
  have hc : (0 : ℝ) < (n : ℝ) + 1 - d := by
    have : (d : ℝ) ≤ (n : ℝ) := by exact_mod_cast hdn
    linarith
  have hlow := choose_lower d n hd
  have h2d : (0 : ℝ) ≤ ((n.choose 2 : ℕ) : ℝ) * ((d.choose 2 : ℕ) : ℝ) := by positivity
  have hdR : (2 : ℝ) ≤ (d : ℝ) := by exact_mod_cast hd
  have hgoal : 2 * (d : ℝ) < ((NN d n : ℝ) - 4) * ((n : ℝ) + 1 - d) := by
    rw [NN_eq_choose]
    by_cases h1 : n = d
    · -- `n = d`, hence `d ≥ 3`
      have hnd : (n : ℝ) = (d : ℝ) := by rw [h1]
      have hd3 : 3 ≤ d := by
        by_contra h
        have hd2 : d = 2 := by omega
        have hn2 : n = 2 := by omega
        exact h22 (by rw [hd2, hn2])
      have hc2 : 3 ≤ d.choose 2 := by
        have h := Nat.choose_le_choose 2 hd3
        norm_num at h
        exact h
      have hn2le : d.choose 2 ≤ n.choose 2 := by rw [h1]
      have h2pos : (9 : ℝ) ≤ ((n.choose 2 : ℕ) : ℝ) * ((d.choose 2 : ℕ) : ℝ) := by
        have h1' : (3 : ℝ) ≤ (n.choose 2 : ℕ) := by
          have : 3 ≤ n.choose 2 := le_trans hc2 hn2le
          exact_mod_cast this
        have h2' : (3 : ℝ) ≤ (d.choose 2 : ℕ) := by exact_mod_cast hc2
        nlinarith [h1', h2']
      nlinarith [hlow, h2pos, hnd, hdR]
    · by_cases h2 : n = d + 1
      · -- `n = d + 1`
        have hnd : (n : ℝ) = (d : ℝ) + 1 := by rw [h2]; push_cast; ring
        have h2pos : (1 : ℝ) ≤ ((n.choose 2 : ℕ) : ℝ) * ((d.choose 2 : ℕ) : ℝ) := by
          have h1' : 1 ≤ n.choose 2 := by
            rw [h2]
            exact Nat.choose_pos (by omega)
          have h2' : 1 ≤ d.choose 2 := Nat.choose_pos hd
          have hm := Nat.mul_le_mul h1' h2'
          exact_mod_cast hm
        nlinarith [hlow, h2pos, hnd, hdR]
      · -- `n ≥ d + 2`
        have hnd : (d : ℝ) + 2 ≤ (n : ℝ) := by
          have : d + 2 ≤ n := by omega
          exact_mod_cast this
        have hb : (d : ℝ) * (d + 2) ≤ (n : ℝ) * d := by nlinarith [hnd, hdR]
        have hC4 : (d : ℝ) * (d + 2) - 4 ≤ ((n + d).choose d : ℝ) - 4 := by
          linarith [hlow, hb, h2d]
        have hnd3 : (3 : ℝ) ≤ (n : ℝ) + 1 - d := by linarith
        have hC4nn : (0 : ℝ) ≤ (d : ℝ) * (d + 2) - 4 := by nlinarith
        have hb4 : (0 : ℝ) ≤ ((n + d).choose d : ℝ) - 4 := le_trans hC4nn hC4
        have hmul : ((d : ℝ) * (d + 2) - 4) * 3
            ≤ (((n + d).choose d : ℝ) - 4) * ((n : ℝ) + 1 - d) :=
          mul_le_mul hC4 hnd3 (by norm_num) hb4
        nlinarith [hmul, hdR]
  have h1' : 2 * (d : ℝ) / ((n : ℝ) + 1 - d) < (NN d n : ℝ) - 4 := by
    rw [div_lt_iff₀ hc]
    exact hgoal
  linarith

/-- `(log B)^k` is eventually bounded by `C * B^δ` for any `δ > 0` (logarithms grow slower than
any positive power). -/
lemma log_pow_le_rpow (k : ℕ) (C δ : ℝ) (hC : 0 < C) (hδ : 0 < δ) :
    ∃ B₀ : ℝ, 0 < B₀ ∧ ∀ B : ℝ, B₀ ≤ B → (Real.log B) ^ k ≤ C * B ^ δ := by
  rcases Nat.eq_zero_or_pos k with hk | hk
  · subst hk
    refine ⟨max 1 ((1 / C) ^ (1 / δ)), lt_of_lt_of_le one_pos (le_max_left _ _), fun B hB => ?_⟩
    have hB1 : (1 : ℝ) ≤ B := le_trans (le_max_left _ _) hB
    have h1 : (1 / C) ^ (1 / δ) ≤ B := le_trans (le_max_right _ _) hB
    have h2 : ((1 / C) ^ (1 / δ)) ^ δ ≤ B ^ δ :=
      Real.rpow_le_rpow (by positivity) h1 (le_of_lt hδ)
    have h3 : ((1 / C) ^ (1 / δ)) ^ δ = 1 / C := by
      rw [← Real.rpow_mul (by positivity : (0 : ℝ) ≤ 1 / C)]
      have hδ1 : 1 / δ * δ = 1 := by field_simp
      rw [hδ1, Real.rpow_one]
    rw [h3] at h2
    have h5 : C * (1 / C) = 1 := by field_simp
    have h4 := mul_le_mul_of_nonneg_left h2 (le_of_lt hC)
    rw [h5] at h4
    simpa using h4
  · have hr : 0 < δ / ((k : ℝ) + 1) := by positivity
    have h1 : (fun x : ℝ => Real.log x) =o[Filter.atTop]
        (fun x : ℝ => x ^ (δ / ((k : ℝ) + 1))) := isLittleO_log_rpow_atTop hr
    have hev : (fun x : ℝ => (x ^ (δ / ((k : ℝ) + 1))) ^ k)
        =ᶠ[Filter.atTop] (fun x : ℝ => x ^ (δ / ((k : ℝ) + 1) * k)) := by
      filter_upwards [Filter.eventually_ge_atTop (0 : ℝ)] with x hx
      rw [← Real.rpow_natCast (x ^ (δ / ((k : ℝ) + 1))) k, ← Real.rpow_mul hx]
    have h2 : (fun x : ℝ => (Real.log x) ^ k) =o[Filter.atTop]
        (fun x : ℝ => x ^ (δ / ((k : ℝ) + 1) * k)) :=
      (h1.pow hk).congr' Filter.EventuallyEq.rfl hev
    have hev2 := h2.def hC
    rw [Filter.eventually_atTop] at hev2
    obtain ⟨a, ha⟩ := hev2
    refine ⟨max a 1, lt_of_lt_of_le one_pos (le_max_right _ _), fun B hB => ?_⟩
    have hB1 : (1 : ℝ) ≤ B := le_trans (le_max_right _ _) hB
    have hBa : a ≤ B := le_trans (le_max_left _ _) hB
    have hbz : (0 : ℝ) < B := lt_of_lt_of_le one_pos hB1
    have h := ha B hBa
    have h' : (Real.log B) ^ k ≤ C * B ^ (δ / ((k : ℝ) + 1) * k) := by
      have h3 : ‖B ^ (δ / ((k : ℝ) + 1) * k)‖ = B ^ (δ / ((k : ℝ) + 1) * k) := by
        rw [Real.norm_eq_abs, abs_of_nonneg (Real.rpow_nonneg (le_of_lt hbz) _)]
      calc (Real.log B) ^ k ≤ |(Real.log B) ^ k| := le_abs_self _
        _ = ‖(Real.log B) ^ k‖ := (Real.norm_eq_abs _).symm
        _ ≤ C * ‖B ^ (δ / ((k : ℝ) + 1) * k)‖ := h
        _ = C * B ^ (δ / ((k : ℝ) + 1) * k) := by rw [h3]
    have hak : δ / ((k : ℝ) + 1) * k ≤ δ := by
      rw [div_mul_eq_mul_div, div_le_iff₀ (by positivity : (0 : ℝ) < (k : ℝ) + 1)]
      nlinarith [hδ, (show (0 : ℝ) ≤ (k : ℝ) from Nat.cast_nonneg k)]
    calc (Real.log B) ^ k ≤ C * B ^ (δ / ((k : ℝ) + 1) * k) := h'
      _ ≤ C * B ^ δ := by
          have hle := Real.rpow_le_rpow_of_exponent_le hB1 hak
          exact mul_le_mul_of_nonneg_left hle (le_of_lt hC)

end Work.HP.MDEstimates

namespace Work.HP.MDEstimates

open Work.HP

/-- The `ζ`-series at `R` is positive for `2 ≤ R` (its `k = 0` term is `1`). -/
lemma zeta_series_pos (R : ℕ) (hR : 2 ≤ R) : 0 < ∑' k : ℕ, 1 / ((k : ℝ) + 1) ^ R := by
  have hsum : Summable (fun k : ℕ => (1 : ℝ) / ((k : ℝ) + 1) ^ R) := by
    have hf : Summable (fun j : ℕ => (1 : ℝ) / (j : ℝ) ^ R) :=
      Real.summable_one_div_nat_pow.mpr (by omega)
    have := (summable_nat_add_iff (f := fun j : ℕ => (1 : ℝ) / (j : ℝ) ^ R) 1).mpr hf
    simpa [Nat.cast_add, Nat.cast_one] using this
  exact Summable.tsum_pos hsum (fun i => by positivity) 0 (by norm_num)

end Work.HP.MDEstimates
