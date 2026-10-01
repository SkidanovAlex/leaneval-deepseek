import Mathlib
import Submission.Work.LinnikAreas.Density4.SqfreeCoprimeDefs
import Submission.Work.LinnikAreas.Density4.moebU_eq_inv_prod
import Submission.Work.LinnikAreas.Density4.moebU_abs_le
import Submission.Work.LinnikAreas.Density4.moebUtrunc_close
import Submission.Work.LinnikAreas.Density4.sqfree_moebius_double_sum
import Submission.Work.LinnikAreas.Density4.inner_moebius_sum_close
import Submission.Work.LinnikAreas.Density4.totient_div_mul_moebU

/-!
# Counting squarefree integers coprime to `r`

The main theorem of this file is

`#{n ≤ Q : (n,r) = 1, n squarefree} = (Q/ζ(2))·∏_{p ∣ r} p/(p+1) + O(Q^{1/2+ε} σ_{-1/3}(r))`,

with `ζ(2) = π²/6` and `σ_{-1/3}(r) = Σ_{d ∣ r} d^{-1/3}` (arXiv:2206.10104, Lemma 0108 for `k = ℚ`).

The route is elementary and gives the sharper error `O(√Q · σ_{-1/2}(r))`:

* `sqfree_moebius_double_sum` expands the count as `Σ_{m₀ ∣ r} μ(m₀) Σ_{(m₂,r)=1} μ(m₂)⌊Q/(m₀m₂²)⌋`;
* `inner_moebius_sum_close` evaluates each inner sum against `(Q/m₀)·moebU r` up to `3√(Q/m₀)`,
  where `moebU r = Σ_{(m,r)=1} μ(m)/m²`;
* summing over `m₀ ∣ r` costs `Σ_{m₀ ∣ r} m₀^{-1/2} = σ_{-1/2}(r)`;
* `totient_div_mul_moebU` identifies `(φ(r)/r)·moebU r` with the density constant
  `ζ(2)⁻¹·∏_{p ∣ r} p/(p+1)`.
-/

namespace Work.LinnikAreas.Density4

open Finset

lemma sum_moebius_div_eq_totient_div (r : ℕ) (hr : 1 ≤ r) :
    (∑ d ∈ r.divisors, (ArithmeticFunction.moebius d : ℝ) / (d : ℝ)) = (r.totient : ℝ) / (r : ℝ) := by
  have hinv := (ArithmeticFunction.sum_eq_iff_sum_mul_moebius_eq (R := ℝ)
      (f := fun n : ℕ => (n.totient : ℝ)) (g := fun n : ℕ => (n : ℝ))).mp
      (fun n _ => by exact_mod_cast Nat.sum_totient n)
  have h := hinv r (by omega)
  have h2 := Nat.sum_divisorsAntidiagonal (n := r)
      (fun a b : ℕ => (ArithmeticFunction.moebius a : ℝ) * (b : ℝ))
  rw [h2] at h
  have hr0 : (r : ℝ) ≠ 0 := by positivity
  have hterm : ∀ d ∈ r.divisors, ((r / d : ℕ) : ℝ) = (r : ℝ) / (d : ℝ) := by
    intro d hd
    have hdvd : d ∣ r := (Nat.mem_divisors.mp hd).1
    have hd0 : d ≠ 0 := fun h0 => by
      have := Nat.zero_dvd.mp (h0 ▸ hdvd); omega
    exact Nat.cast_div hdvd (by exact_mod_cast hd0)
  have h4 : (∑ d ∈ r.divisors, (ArithmeticFunction.moebius d : ℝ) * ((r / d : ℕ) : ℝ))
      = ∑ d ∈ r.divisors, (ArithmeticFunction.moebius d : ℝ) * ((r : ℝ) / (d : ℝ)) :=
    Finset.sum_congr rfl (fun d hd => by rw [hterm d hd])
  rw [h4] at h
  have h3 : (∑ d ∈ r.divisors, (ArithmeticFunction.moebius d : ℝ) * ((r : ℝ) / (d : ℝ)))
      = (r : ℝ) * ∑ d ∈ r.divisors, (ArithmeticFunction.moebius d : ℝ) / (d : ℝ) := by
    rw [Finset.mul_sum]
    exact Finset.sum_congr rfl (fun d _ => by ring)
  rw [h3] at h
  rw [eq_div_iff hr0, mul_comm]
  exact h

lemma divisors_pos {r d : ℕ} (hr : 1 ≤ r) (hd : d ∈ r.divisors) : 1 ≤ d := by
  have hdvd : d ∣ r := (Nat.mem_divisors.mp hd).1
  have hd0 : d ≠ 0 := fun h0 => by have := Nat.zero_dvd.mp (h0 ▸ hdvd); omega
  omega

theorem sqfree_count_main_est (X r : ℕ) (hX : 1 ≤ X) (hr : 1 ≤ r) :
    |(∑ n ∈ (Finset.Icc 1 X).filter (fun n => Nat.Coprime n r ∧ Squarefree n), (1 : ℝ))
      - (X : ℝ) * (((r.totient : ℝ) / (r : ℝ)) * moebU r)|
    ≤ 3 * Real.sqrt (X : ℝ) * (∑ d ∈ r.divisors, 1 / Real.sqrt (d : ℝ)) := by
  rw [sqfree_moebius_double_sum X r hr]
  have hmain : (X : ℝ) * (((r.totient : ℝ) / (r : ℝ)) * moebU r)
      = ∑ m₀ ∈ r.divisors,
          (ArithmeticFunction.moebius m₀ : ℝ) * ((X : ℝ) / (m₀ : ℝ) * moebU r) := by
    rw [← sum_moebius_div_eq_totient_div r hr, Finset.sum_mul, Finset.mul_sum]
    exact Finset.sum_congr rfl (fun d _ => by ring)
  rw [hmain]
  have hsplit : (∑ m₀ ∈ r.divisors,
        (ArithmeticFunction.moebius m₀ : ℝ) *
          (∑ m₂ ∈ (Finset.Icc 1 X).filter (fun m₂ => Nat.Coprime m₂ r),
            (ArithmeticFunction.moebius m₂ : ℝ) * (((X / (m₀ * m₂ ^ 2)) : ℕ) : ℝ)))
      - (∑ m₀ ∈ r.divisors,
          (ArithmeticFunction.moebius m₀ : ℝ) * ((X : ℝ) / (m₀ : ℝ) * moebU r))
      = ∑ m₀ ∈ r.divisors,
          (ArithmeticFunction.moebius m₀ : ℝ) *
          ((∑ m₂ ∈ (Finset.Icc 1 X).filter (fun m₂ => Nat.Coprime m₂ r),
            (ArithmeticFunction.moebius m₂ : ℝ) * (((X / (m₀ * m₂ ^ 2)) : ℕ) : ℝ))
          - ((X : ℝ) / (m₀ : ℝ) * moebU r)) := by
    rw [← Finset.sum_sub_distrib]
    exact Finset.sum_congr rfl (fun m₀ _ => by ring)
  rw [hsplit]
  have hstep : ∀ m₀ ∈ r.divisors,
      |(ArithmeticFunction.moebius m₀ : ℝ) *
          ((∑ m₂ ∈ (Finset.Icc 1 X).filter (fun m₂ => Nat.Coprime m₂ r),
            (ArithmeticFunction.moebius m₂ : ℝ) * (((X / (m₀ * m₂ ^ 2)) : ℕ) : ℝ))
          - ((X : ℝ) / (m₀ : ℝ) * moebU r))|
      ≤ 3 * Real.sqrt ((X : ℝ) / (m₀ : ℝ)) := by
    intro m₀ hm₀
    have hm₀1 : 1 ≤ m₀ := divisors_pos hr hm₀
    have h := inner_moebius_sum_close X m₀ r hX hm₀1
    rw [abs_mul]
    have hμ : |(ArithmeticFunction.moebius m₀ : ℝ)| ≤ 1 := by
      rw [← Int.cast_abs]; exact_mod_cast ArithmeticFunction.abs_moebius_le_one (n := m₀)
    calc |(ArithmeticFunction.moebius m₀ : ℝ)| *
            |((∑ m₂ ∈ (Finset.Icc 1 X).filter (fun m₂ => Nat.Coprime m₂ r),
              (ArithmeticFunction.moebius m₂ : ℝ) * (((X / (m₀ * m₂ ^ 2)) : ℕ) : ℝ))
              - ((X : ℝ) / (m₀ : ℝ) * moebU r))|
        ≤ 1 * (3 * Real.sqrt ((X : ℝ) / (m₀ : ℝ))) :=
          mul_le_mul hμ h (abs_nonneg _) (by norm_num)
      _ = 3 * Real.sqrt ((X : ℝ) / (m₀ : ℝ)) := by ring
  have hsum : (∑ m₀ ∈ r.divisors, 3 * Real.sqrt ((X : ℝ) / (m₀ : ℝ)))
      ≤ 3 * Real.sqrt (X : ℝ) * (∑ d ∈ r.divisors, 1 / Real.sqrt (d : ℝ)) := by
    rw [Finset.mul_sum]
    apply Finset.sum_le_sum
    intro d hd
    have hd1 : 1 ≤ d := divisors_pos hr hd
    have hd0 : (0:ℝ) < (d:ℝ) := by exact_mod_cast hd1
    rw [show Real.sqrt ((X:ℝ)/(d:ℝ)) = Real.sqrt (X:ℝ)/Real.sqrt (d:ℝ) from
      Real.sqrt_div' (X:ℝ) hd0.le]
    exact le_of_eq (by ring)
  exact le_trans (Finset.abs_sum_le_sum_abs _ _) (le_trans (Finset.sum_le_sum hstep) hsum)

theorem sqfree_coprime_count :
    ∀ ε : ℝ, 0 < ε → ∃ C : ℝ, 0 < C ∧ ∀ (Q r : ℕ), 1 ≤ Q → 1 ≤ r →
      |((∑ n ∈ (Finset.Icc 1 Q).filter (fun n => Nat.Coprime n r ∧ Squarefree n), (1 : ℝ)))
        - (Q : ℝ) / ((riemannZeta (2 : ℂ)).re) *
            ((r : ℝ) / (r * ∏ p ∈ r.primeFactors, (1 + (1 : ℝ) / (p : ℝ))))|
      ≤ C * (Q : ℝ) ^ ((1 : ℝ) / 2 + ε) *
          (∑ d ∈ r.divisors, (1 : ℝ) / (d : ℝ) ^ ((1 : ℝ) / 3)) := by
  intro ε hε
  refine ⟨3, by norm_num, ?_⟩
  intro Q r hQ hr
  have hmain := sqfree_count_main_est Q r hQ hr
  have hconst := totient_div_mul_moebU r hr
  have heq : (Q : ℝ) * (((r.totient : ℝ) / (r : ℝ)) * moebU r)
      = (Q : ℝ) / ((riemannZeta (2 : ℂ)).re) *
          ((r : ℝ) / (r * ∏ p ∈ r.primeFactors, (1 + (1 : ℝ) / (p : ℝ)))) := by
    rw [hconst]; unfold zeta2; ring
  have hQ1 : (1 : ℝ) ≤ (Q : ℝ) := by exact_mod_cast hQ
  have hsqrt_le : Real.sqrt (Q : ℝ) ≤ (Q : ℝ) ^ ((1 : ℝ) / 2 + ε) := by
    rw [Real.sqrt_eq_rpow]
    exact Real.rpow_le_rpow_of_exponent_le hQ1 (by linarith)
  have hsum_le : (∑ d ∈ r.divisors, 1 / Real.sqrt (d : ℝ))
      ≤ ∑ d ∈ r.divisors, 1 / (d : ℝ) ^ ((1 : ℝ) / 3) := by
    apply Finset.sum_le_sum
    intro d hd
    have hd1 : (1 : ℝ) ≤ (d : ℝ) := by exact_mod_cast divisors_pos hr hd
    have hpos : 0 < (d : ℝ) := by linarith
    have hroot : (d : ℝ) ^ ((1 : ℝ) / 3) ≤ Real.sqrt (d : ℝ) := by
      rw [Real.sqrt_eq_rpow]
      exact Real.rpow_le_rpow_of_exponent_le hd1 (by norm_num)
    rw [one_div, one_div, inv_le_inv₀ (Real.sqrt_pos.mpr hpos) (Real.rpow_pos_of_pos hpos _)]
    exact hroot
  have hsum0 : 0 ≤ ∑ d ∈ r.divisors, 1 / Real.sqrt (d : ℝ) := by
    apply Finset.sum_nonneg
    intro d hd
    have hd1 : (1 : ℝ) ≤ (d : ℝ) := by exact_mod_cast divisors_pos hr hd
    positivity
  have hsqrt0 : 0 ≤ Real.sqrt (Q : ℝ) := Real.sqrt_nonneg _
  have hgoal : 0 ≤ ∑ d ∈ r.divisors, 1 / (d : ℝ) ^ ((1 : ℝ) / 3) := by
    apply Finset.sum_nonneg
    intro d hd
    have hd1 : (1 : ℝ) ≤ (d : ℝ) := by exact_mod_cast divisors_pos hr hd
    positivity
  calc |(∑ n ∈ (Finset.Icc 1 Q).filter (fun n => Nat.Coprime n r ∧ Squarefree n), (1 : ℝ))
        - (Q : ℝ) / ((riemannZeta (2 : ℂ)).re) *
            ((r : ℝ) / (r * ∏ p ∈ r.primeFactors, (1 + (1 : ℝ) / (p : ℝ))))|
      = |(∑ n ∈ (Finset.Icc 1 Q).filter (fun n => Nat.Coprime n r ∧ Squarefree n), (1 : ℝ))
        - (Q : ℝ) * (((r.totient : ℝ) / (r : ℝ)) * moebU r)| := by rw [heq]
    _ ≤ 3 * Real.sqrt (Q : ℝ) * (∑ d ∈ r.divisors, 1 / Real.sqrt (d : ℝ)) := hmain
    _ ≤ 3 * (Q : ℝ) ^ ((1 : ℝ) / 2 + ε) * (∑ d ∈ r.divisors, 1 / (d : ℝ) ^ ((1 : ℝ) / 3)) := by
        exact mul_le_mul (mul_le_mul_of_nonneg_left hsqrt_le (by norm_num)) hsum_le hsum0
          (mul_nonneg (by norm_num) (Real.rpow_nonneg (by positivity) _))

end Work.LinnikAreas.Density4
