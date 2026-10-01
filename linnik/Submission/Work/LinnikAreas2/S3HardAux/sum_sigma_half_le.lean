import Mathlib

/-!
# The divisor-sum estimate `∑_{r ≤ T} σ_{1/2}(r) ≤ 4T`

This file proves `Work.LinnikAreas2.S3HardAux.sum_sigma_half_le`, the elementary
estimate used in the `S3` ("hard") part of the Linnik argument:

  `∑_{r = 1}^{T} ∑_{d | r} 1/√d ≤ 4T`.

The proof has three independent ingredients.

* A **divisor swap** (counting multiples): for every `T` and every `f : ℕ → ℝ`,
  `∑_{r ≤ T} ∑_{d | r} f d = ∑_{d ≤ T} f d · ⌊T/d⌋`.
  The number of multiples of `d` in `[1,T]` is `T/d` (`Nat.card_multiples'`).

* The **analytic bound** `∑_{d ≤ T} 1/(d·√d) ≤ 4`, obtained from the pointwise
  telescoping estimate
  `1/(d·√d) ≤ 4·(1/√d - 1/√(d+1))`  (`d ≥ 1`),
  whose sum over `1 ≤ d ≤ T` is `4(1 - 1/√(T+1)) ≤ 4`.

* Chaining: `⌊T/d⌋ ≤ T/d` for the swapped sum.

The exact bound `4T` is far from optimal (the true size is `≈ 2.612·T`); the
loose constant `4` is what the caller needs.
-/

namespace Work.LinnikAreas2.S3HardAux

/-- The number of multiples of `d` in `{1, …, T}` is `T / d`. -/
private lemma card_filter_dvd_Icc (T d : ℕ) :
    ((Finset.Icc 1 T).filter (fun r => d ∣ r)).card = T / d := by
  rw [← Nat.card_multiples' T d]
  congr 1
  ext k
  simp only [Finset.mem_filter, Finset.mem_Icc, Finset.mem_range]
  omega

/-- Divisor-sum swap: interchanging the order of summation replaces "divide `r`"
by the number of multiples of `d`, which is `⌊T/d⌋`. -/
private lemma sum_Icc_divisors_swap (T : ℕ) (f : ℕ → ℝ) :
    (∑ r ∈ Finset.Icc 1 T, ∑ d ∈ r.divisors, f d)
      = ∑ d ∈ Finset.Icc 1 T, f d * ((T / d : ℕ) : ℝ) := by
  have key : ∀ r ∈ Finset.Icc 1 T,
      ∑ d ∈ r.divisors, f d = ∑ d ∈ Finset.Icc 1 T, (if d ∣ r then f d else 0) := by
    intro r hr
    obtain ⟨hr1, hrT⟩ := Finset.mem_Icc.mp hr
    have hset : r.divisors = (Finset.Icc 1 T).filter (fun d => d ∣ r) := by
      ext d
      rw [Nat.mem_divisors, Finset.mem_filter, Finset.mem_Icc]
      constructor
      · rintro ⟨hdvd, -⟩
        exact ⟨⟨Nat.pos_of_dvd_of_pos hdvd (by omega),
                le_trans (Nat.le_of_dvd (by omega) hdvd) hrT⟩, hdvd⟩
      · rintro ⟨⟨hd1, hdT⟩, hdvd⟩
        exact ⟨hdvd, by omega⟩
    rw [hset, Finset.sum_filter]
  calc ∑ r ∈ Finset.Icc 1 T, ∑ d ∈ r.divisors, f d
      = ∑ r ∈ Finset.Icc 1 T, ∑ d ∈ Finset.Icc 1 T, (if d ∣ r then f d else 0) :=
        Finset.sum_congr rfl key
    _ = ∑ d ∈ Finset.Icc 1 T, ∑ r ∈ Finset.Icc 1 T, (if d ∣ r then f d else 0) :=
        Finset.sum_comm
    _ = ∑ d ∈ Finset.Icc 1 T, f d * ((T / d : ℕ) : ℝ) := by
        apply Finset.sum_congr rfl
        intro d hd
        rw [← Finset.sum_filter, Finset.sum_const, card_filter_dvd_Icc, nsmul_eq_mul]
        ring

/-- Pointwise telescoping estimate: for `d ≥ 1`,
`1/(d·√d) ≤ 4·(1/√d - 1/√(d+1))`. -/
private lemma one_div_d_mul_sqrt_le (d : ℕ) (hd : 1 ≤ d) :
    (1 : ℝ) / ((d : ℝ) * Real.sqrt (d : ℝ))
      ≤ 4 * (1 / Real.sqrt (d : ℝ) - 1 / Real.sqrt ((d + 1 : ℕ) : ℝ)) := by
  have hd0 : (0 : ℝ) < (d : ℝ) := by exact_mod_cast (show 0 < d by omega)
  have hd10 : (0 : ℝ) < ((d + 1 : ℕ) : ℝ) := by
    have : 0 < d + 1 := by omega
    exact_mod_cast this
  set a : ℝ := Real.sqrt (d : ℝ) with haeq
  set c : ℝ := Real.sqrt ((d + 1 : ℕ) : ℝ) with hceq
  have ha : 0 < a := by rw [haeq]; exact Real.sqrt_pos.2 hd0
  have hc : 0 < c := by rw [hceq]; exact Real.sqrt_pos.2 hd10
  have hda : (d : ℝ) = a * a := by rw [haeq, Real.mul_self_sqrt (le_of_lt hd0)]
  have hdc : ((d + 1 : ℕ) : ℝ) = c * c := by
    rw [hceq, Real.mul_self_sqrt (le_of_lt hd10)]
  have hcsq : c * c = (d : ℝ) + 1 := by rw [← hdc, Nat.cast_add, Nat.cast_one]
  have hac : a ≤ c := by
    rw [haeq, hceq]
    exact Real.sqrt_le_sqrt (by push_cast; linarith)
  have hstep : (a + c) * c ≤ 4 * a * a := by
    have h1 : a * c ≤ c * c := mul_le_mul_of_nonneg_right hac (le_of_lt hc)
    have hd1 : (1 : ℝ) ≤ (d : ℝ) := by exact_mod_cast hd
    have h2 : (2 : ℝ) * ((d : ℝ) + 1) ≤ 4 * (d : ℝ) := by linarith
    nlinarith [h1, hcsq, h2]
  have hkey : 4 * (1 / a - 1 / c) = 4 / (a * c * (a + c)) := by
    have h1 : c * c - a * a = 1 := by rw [hcsq, hda]; ring
    field_simp
    nlinarith [h1]
  have hL : (1 : ℝ) / ((d : ℝ) * a) = 1 / (a * a * a) := by rw [hda]
  rw [hL, hkey, div_le_div_iff₀ (by positivity) (by positivity)]
  calc 1 * (a * c * (a + c)) = a * ((a + c) * c) := by ring
    _ ≤ a * (4 * a * a) := mul_le_mul_of_nonneg_left hstep (le_of_lt ha)
    _ = 4 * (a * a * a) := by ring

/-- `∑_{d=1}^{T} (1/√d - 1/√(d+1)) = 1 - 1/√(T+1)`. -/
private lemma sum_telescope_sqrt (T : ℕ) (h1T : 1 ≤ T) :
    (∑ d ∈ Finset.Icc 1 T, (1 / Real.sqrt (d : ℝ) - 1 / Real.sqrt ((d + 1 : ℕ) : ℝ)))
      = 1 - 1 / Real.sqrt ((T + 1 : ℕ) : ℝ) := by
  have hsub := Finset.sum_Icc_sub (m := 1) (n := T) h1T
    (fun i : ℕ => -(1 / Real.sqrt (i : ℝ)))
  simp only [Nat.cast_one, Real.sqrt_one] at hsub
  rw [show (∑ i ∈ Finset.Icc 1 T,
          (-(1 / Real.sqrt ((i + 1 : ℕ) : ℝ)) - -(1 / Real.sqrt (i : ℝ))))
        = ∑ i ∈ Finset.Icc 1 T,
            (1 / Real.sqrt (i : ℝ) - 1 / Real.sqrt ((i + 1 : ℕ) : ℝ)) from
          Finset.sum_congr rfl (fun i _ => by ring)] at hsub
  rw [hsub]
  ring

/-- `∑_{d=1}^{T} 1/(d·√d) ≤ 4`. -/
private lemma sum_inv_d_mul_sqrt_le (T : ℕ) :
    (∑ d ∈ Finset.Icc 1 T, (1 : ℝ) / ((d : ℝ) * Real.sqrt (d : ℝ))) ≤ 4 := by
  rcases Nat.eq_zero_or_pos T with hT | hT
  · subst hT; simp
  · calc ∑ d ∈ Finset.Icc 1 T, (1 : ℝ) / ((d : ℝ) * Real.sqrt (d : ℝ))
        ≤ ∑ d ∈ Finset.Icc 1 T,
            4 * (1 / Real.sqrt (d : ℝ) - 1 / Real.sqrt ((d + 1 : ℕ) : ℝ)) := by
          apply Finset.sum_le_sum
          intro d hd
          exact one_div_d_mul_sqrt_le d (Finset.mem_Icc.mp hd).1
      _ = 4 * ∑ d ∈ Finset.Icc 1 T,
            (1 / Real.sqrt (d : ℝ) - 1 / Real.sqrt ((d + 1 : ℕ) : ℝ)) := by
          rw [← Finset.mul_sum]
      _ = 4 * (1 - 1 / Real.sqrt ((T + 1 : ℕ) : ℝ)) := by rw [sum_telescope_sqrt T hT]
      _ ≤ 4 := by
          have hsp : (0 : ℝ) < Real.sqrt ((T + 1 : ℕ) : ℝ) := Real.sqrt_pos.2 (by positivity)
          have : (0 : ℝ) < 1 / Real.sqrt ((T + 1 : ℕ) : ℝ) := by positivity
          nlinarith

/-- The analytic estimate obtained after swapping: `∑_{d ≤ T} (1/√d)·(T/d) ≤ 4T`. -/
private lemma sum_inv_sqrt_div_le (T : ℕ) :
    (∑ d ∈ Finset.Icc 1 T, (1 : ℝ) / Real.sqrt (d : ℝ) * ((T : ℝ) / d))
      ≤ 4 * (T : ℝ) := by
  have hterm : ∀ d ∈ Finset.Icc 1 T,
      (1 : ℝ) / Real.sqrt (d : ℝ) * ((T : ℝ) / d)
        = (T : ℝ) * (1 / ((d : ℝ) * Real.sqrt (d : ℝ))) := by
    intro d hd
    have hd1 : (0 : ℝ) < (d : ℝ) := by
      have : 1 ≤ d := (Finset.mem_Icc.mp hd).1
      exact_mod_cast (show 0 < d by omega)
    have hs : (0 : ℝ) < Real.sqrt (d : ℝ) := Real.sqrt_pos.2 hd1
    field_simp
    try ring
  rw [Finset.sum_congr rfl hterm, ← Finset.mul_sum]
  have h := sum_inv_d_mul_sqrt_le T
  have hT0 : (0 : ℝ) ≤ (T : ℝ) := by positivity
  calc (T : ℝ) * ∑ d ∈ Finset.Icc 1 T, 1 / ((d : ℝ) * Real.sqrt (d : ℝ))
      ≤ (T : ℝ) * 4 := mul_le_mul_of_nonneg_left h hT0
    _ = 4 * (T : ℝ) := by ring

/-- `∑_{r ≤ T} σ_{1/2}(r) ≤ 4T`, where `σ_{1/2}(r) = ∑_{d | r} 1/√d`. -/
theorem sum_sigma_half_le (T : ℕ) :
    (∑ r ∈ Finset.Icc 1 T, ∑ d ∈ r.divisors, (1 : ℝ) / Real.sqrt (d : ℝ)) ≤ 4 * (T : ℝ) := by
  rw [sum_Icc_divisors_swap T (fun d => (1 : ℝ) / Real.sqrt (d : ℝ))]
  calc ∑ d ∈ Finset.Icc 1 T, (1 : ℝ) / Real.sqrt (d : ℝ) * ((T / d : ℕ) : ℝ)
      ≤ ∑ d ∈ Finset.Icc 1 T, (1 : ℝ) / Real.sqrt (d : ℝ) * ((T : ℝ) / d) := by
        apply Finset.sum_le_sum
        intro d _
        exact mul_le_mul_of_nonneg_left Nat.cast_div_le (by positivity)
    _ ≤ 4 * (T : ℝ) := sum_inv_sqrt_div_le T

end Work.LinnikAreas2.S3HardAux
