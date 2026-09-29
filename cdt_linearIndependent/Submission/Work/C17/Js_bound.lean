import Mathlib
import Submission.Work.C17.Bsubst_deps

/-!
# `Js_bound` — polynomial growth of the coefficients of `Jps`

`Jps = x·₃F₂(1/2,1,1;3/2,3/2; y/4)` (`y = x²/(x−1)`, `Submission/Work/C7/xdefs.lean`) satisfies, by
`Work.C7.J_ode`, the first order ODE

`2·x(x−1)·J' − x·J = 2(1−x)·log(1−x)`.

This module shows that *any* power series `J ∈ ℚ⟦x⟧` satisfying that ODE has polynomially bounded
coefficients (the bound is in fact linear: `|aₙ| ≤ (|a₀| + |a₁| + 1)·(n+1)`).

The proof is the coefficient extraction of the ODE.  Taking the coefficient of `x^{k+2}` and writing
`aₙ = [xⁿ]J`, `lₙ = [xⁿ]log(1−x)` gives, for every `k`,

`(2k+4)·a_{k+2} = (2k+1)·a_{k+1} + 2·(l_{k+1} − l_{k+2})`,

i.e. `a_{k+2} = ((2k+1)/(2k+4))·a_{k+1} + (l_{k+1} − l_{k+2})/(k+2)`.  Since `(2k+1)/(2k+4) < 1` and
`|l_{k+1} − l_{k+2}| ≤ 1`, the coefficients grow at most linearly (`Js_arith`).
-/

open PowerSeries

namespace Work.C17

noncomputable section

/-- Coefficient of `2·f` for a power series over `ℚ`. -/
private lemma coeff_two_mul (k : ℕ) (f : PowerSeries ℚ) :
    PowerSeries.coeff k ((2 : PowerSeries ℚ) * f) = 2 * PowerSeries.coeff k f := by
  rw [show (2 : PowerSeries ℚ) * f = f + f by ring, map_add]
  ring

/-- A sequence obeying the recurrence `(2k+4)A_{k+2} = (2k+1)A_{k+1} + 2(L_{k+1} - L_{k+2})` with
`|L_m − L_{m+1}| ≤ 1` grows at most linearly. -/
private lemma Js_arith (A L : ℕ → ℝ)
    (hrec : ∀ k : ℕ, (2*(k:ℝ)+4) * A (k+2) = (2*(k:ℝ)+1) * A (k+1) + 2 * (L (k+1) - L (k+2)))
    (hL : ∀ m : ℕ, |L m - L (m+1)| ≤ 1) :
    ∀ n : ℕ, |A n| ≤ (|A 0| + |A 1| + 1) * ((n:ℝ)+1) := by
  intro n
  induction n using Nat.strong_induction_on with
  | _ n ih =>
    rcases n with _ | _ | k
    · norm_num
      linarith [abs_nonneg (A 0), abs_nonneg (A 1)]
    · norm_num
      linarith [abs_nonneg (A 0), abs_nonneg (A 1)]
    · have h2k4 : (0:ℝ) < 2*(k:ℝ)+4 := by positivity
      have hA : A (k+2) = ((2*(k:ℝ)+1) * A (k+1) + 2*(L (k+1) - L (k+2))) / (2*(k:ℝ)+4) := by
        rw [eq_div_iff (ne_of_gt h2k4)]
        linarith [hrec k]
      rw [hA]
      have h1 : |A (k+1)| ≤ (|A 0| + |A 1| + 1) * ((k:ℝ)+2) := by
        have h := ih (k+1) (by omega)
        rw [show (((k+1 : ℕ)) : ℝ) + 1 = (k:ℝ)+2 by push_cast; ring] at h
        exact h
      have h3 : |((2*(k:ℝ)+1) * A (k+1) + 2*(L (k+1) - L (k+2))) / (2*(k:ℝ)+4)|
          ≤ |A (k+1)| + 1 := by
        rw [abs_div, abs_of_pos h2k4]
        have hb : |(2*(k:ℝ)+1) * A (k+1) + 2*(L (k+1) - L (k+2))|
            ≤ (2*(k:ℝ)+1) * |A (k+1)| + 2 * |L (k+1) - L (k+2)| := by
          calc |(2*(k:ℝ)+1) * A (k+1) + 2*(L (k+1) - L (k+2))|
              ≤ |(2*(k:ℝ)+1) * A (k+1)| + |2*(L (k+1) - L (k+2))| := abs_add_le _ _
            _ = (2*(k:ℝ)+1) * |A (k+1)| + 2 * |L (k+1) - L (k+2)| := by
                rw [abs_mul, abs_mul, abs_of_nonneg (by positivity : (0:ℝ) ≤ 2*(k:ℝ)+1),
                  abs_of_nonneg (by norm_num : (0:ℝ) ≤ 2)]
        calc |(2*(k:ℝ)+1) * A (k+1) + 2*(L (k+1) - L (k+2))| / (2*(k:ℝ)+4)
            ≤ ((2*(k:ℝ)+1) * |A (k+1)| + 2 * |L (k+1) - L (k+2)|) / (2*(k:ℝ)+4) :=
              div_le_div_of_nonneg_right hb h2k4.le
          _ ≤ |A (k+1)| + |L (k+1) - L (k+2)| := by
              rw [div_le_iff₀ h2k4]
              nlinarith [abs_nonneg (A (k+1)), abs_nonneg (L (k+1) - L (k+2))]
          _ ≤ |A (k+1)| + 1 := by linarith [hL (k+1)]
      calc |((2*(k:ℝ)+1) * A (k+1) + 2*(L (k+1) - L (k+2))) / (2*(k:ℝ)+4)|
          ≤ |A (k+1)| + 1 := h3
        _ ≤ (|A 0| + |A 1| + 1) * ((k:ℝ)+2) + 1 := by linarith [h1]
        _ ≤ (|A 0| + |A 1| + 1) * ((k:ℝ)+3) := by
            nlinarith [abs_nonneg (A 0), abs_nonneg (A 1)]
        _ = (|A 0| + |A 1| + 1) * ((↑(k+2) : ℝ)+1) := by push_cast; ring

/-- The coefficient recurrence `(2k+4)a_{k+2} = (2k+1)a_{k+1} + 2(l_{k+1} − l_{k+2})` for `Jps`. -/
private lemma Jps_rec (h : 2 * PowerSeries.X * (PowerSeries.X - 1) * PowerSeries.derivative (R := ℚ) Work.C7.Jps
      - PowerSeries.X * Work.C7.Jps = 2 * (1 - PowerSeries.X) * Work.C7.Lps) (k : ℕ) :
    (2*(k:ℚ)+4) * PowerSeries.coeff (k+2) Work.C7.Jps
      = (2*(k:ℚ)+1) * PowerSeries.coeff (k+1) Work.C7.Jps
        + 2 * (PowerSeries.coeff (k+1) Work.C7.Lps - PowerSeries.coeff (k+2) Work.C7.Lps) := by
  have hc := congrArg (PowerSeries.coeff (k+2)) h
  have hL : PowerSeries.coeff (k+2) (2 * (PowerSeries.X:PowerSeries ℚ) * (PowerSeries.X-1) * PowerSeries.derivative (R := ℚ) Work.C7.Jps - PowerSeries.X * Work.C7.Jps)
      = (2*(k:ℚ)+1) * PowerSeries.coeff (k+1) Work.C7.Jps - (2*(k:ℚ)+4) * PowerSeries.coeff (k+2) Work.C7.Jps := by
    rw [show (2 * (PowerSeries.X:PowerSeries ℚ) * (PowerSeries.X-1) * PowerSeries.derivative (R := ℚ) Work.C7.Jps - PowerSeries.X * Work.C7.Jps)
        = 2 * ((PowerSeries.X:PowerSeries ℚ)^2 * PowerSeries.derivative (R := ℚ) Work.C7.Jps) - 2 * ((PowerSeries.X:PowerSeries ℚ) * PowerSeries.derivative (R := ℚ) Work.C7.Jps) - (PowerSeries.X:PowerSeries ℚ) * Work.C7.Jps by ring]
    rw [map_sub, map_sub, coeff_two_mul, coeff_two_mul]
    rw [PowerSeries.coeff_X_pow_mul]
    simp only [show k+2 = (k+1)+1 by omega]
    rw [PowerSeries.coeff_succ_X_mul, PowerSeries.coeff_succ_X_mul]
    rw [PowerSeries.coeff_derivative, PowerSeries.coeff_derivative]
    push_cast
    ring
  have hR : PowerSeries.coeff (k+2) (2 * (1 - PowerSeries.X:PowerSeries ℚ) * Work.C7.Lps)
      = 2 * (PowerSeries.coeff (k+2) Work.C7.Lps - PowerSeries.coeff (k+1) Work.C7.Lps) := by
    rw [show 2 * (1 - (PowerSeries.X:PowerSeries ℚ)) * Work.C7.Lps = 2 * ((1 - (PowerSeries.X:PowerSeries ℚ)) * Work.C7.Lps) by ring]
    rw [coeff_two_mul]
    rw [show (1 - (PowerSeries.X:PowerSeries ℚ)) * Work.C7.Lps = Work.C7.Lps - (PowerSeries.X:PowerSeries ℚ) * Work.C7.Lps by ring]
    rw [map_sub, show k+2 = (k+1)+1 by omega, PowerSeries.coeff_succ_X_mul]
  rw [hL, hR] at hc
  linarith

/-- `|l_m − l_{m+1}| ≤ 1` for `l` the coefficients of `Lps = log(1−x)`. -/
private lemma Lps_diff_bound (m : ℕ) :
    |((PowerSeries.coeff m Work.C7.Lps : ℚ) : ℝ)
        - ((PowerSeries.coeff (m+1) Work.C7.Lps : ℚ) : ℝ)| ≤ 1 := by
  rcases m with _ | k
  · norm_num [Work.C7.coeff_Lps]
  · rw [Work.C7.coeff_Lps (k+1), Work.C7.coeff_Lps (k+2),
      if_neg (by omega : ¬ (k + 1 = 0)), if_neg (by omega : ¬ (k + 2 = 0))]
    simp only [Rat.cast_neg, Rat.cast_inv, Rat.cast_natCast]
    have hval : -(↑(k+1) : ℝ)⁻¹ - -((↑(k+2) : ℝ)⁻¹) = -(1/((↑(k+1) : ℝ)*(↑(k+2) : ℝ))) := by
      field_simp
      push_cast
      ring
    rw [hval, abs_neg, abs_of_nonneg (by positivity : (0:ℝ) ≤ 1/((↑(k+1) : ℝ)*(↑(k+2) : ℝ)))]
    rw [div_le_one (by positivity : (0:ℝ) < (↑(k+1) : ℝ)*(↑(k+2) : ℝ))]
    have ha : (1:ℝ) ≤ (↑(k+1) : ℝ) := by exact_mod_cast (by omega : 1 ≤ k+1)
    have hb : (1:ℝ) ≤ (↑(k+2) : ℝ) := by exact_mod_cast (by omega : 1 ≤ k+2)
    nlinarith [ha, hb]

theorem Js_bound (h : 2 * PowerSeries.X * (PowerSeries.X - 1) * PowerSeries.derivative (R := ℚ) Work.C7.Jps
      - PowerSeries.X * Work.C7.Jps = 2 * (1 - PowerSeries.X) * Work.C7.Lps) :
    ∃ C : ℝ, ∃ k : ℕ, ∀ n : ℕ,
      |(((PowerSeries.coeff n Work.C7.Jps : ℚ) : ℝ))| ≤ C * ((n : ℝ) + 1) ^ k := by
  have hrecR : ∀ k : ℕ, (2*(k:ℝ)+4) * ((PowerSeries.coeff (k+2) Work.C7.Jps : ℚ) : ℝ)
      = (2*(k:ℝ)+1) * ((PowerSeries.coeff (k+1) Work.C7.Jps : ℚ) : ℝ)
        + 2 * (((PowerSeries.coeff (k+1) Work.C7.Lps : ℚ) : ℝ)
            - ((PowerSeries.coeff (k+2) Work.C7.Lps : ℚ) : ℝ)) := by
    intro k
    have hh := congrArg (fun x : ℚ => (x : ℝ)) (Jps_rec h k)
    push_cast at hh
    simpa using hh
  refine ⟨|(((PowerSeries.coeff 0 Work.C7.Jps : ℚ)) : ℝ)|
      + |(((PowerSeries.coeff 1 Work.C7.Jps : ℚ)) : ℝ)| + 1, 1, fun n => ?_⟩
  have hk := Js_arith (fun n => ((PowerSeries.coeff n Work.C7.Jps : ℚ) : ℝ))
    (fun n => ((PowerSeries.coeff n Work.C7.Lps : ℚ) : ℝ)) hrecR Lps_diff_bound n
  simpa [pow_one] using hk

end

end Work.C17
