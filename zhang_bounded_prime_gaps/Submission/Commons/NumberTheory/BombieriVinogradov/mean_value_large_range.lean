import Mathlib
import Submission.Commons.NumberTheory.ArithmeticFunction.sum_vonMangoldt_sq_le
import Submission.Commons.NumberTheory.BombieriVinogradov.maximal_bilinear_char_large_sieve_sSup

namespace Commons.NumberTheory.BombieriVinogradov

open scoped BigOperators

private lemma mean_value_large_range_inner_eq (q x y : ℕ) (b : ℕ → ℂ) (χ : DirichletCharacter ℂ q) (hyx : y ≤ x) :
    (∑ m ∈ Finset.Icc 1 1, ∑ n ∈ Finset.Icc 1 x,
        (if m * n ≤ y then (1 : ℂ) else 0) * (1 : ℂ) * b n * χ ((m * n : ℕ) : ZMod q))
      = ∑ n ∈ Finset.Icc 1 y, b n * χ (n : ZMod q) := by
  rw [Finset.Icc_self, Finset.sum_singleton]
  simp only [one_mul, mul_one]
  have hsub : Finset.Icc 1 y ⊆ Finset.Icc 1 x := Finset.Icc_subset_Icc_right hyx
  have hzero : ∀ n ∈ Finset.Icc 1 x, n ∉ Finset.Icc 1 y →
      (if n ≤ y then (1 : ℂ) else 0) * b n * χ (n : ZMod q) = 0 := by
    intro n hn hnnot
    have hny : ¬ n ≤ y := fun h => hnnot (Finset.mem_Icc.mpr ⟨(Finset.mem_Icc.mp hn).1, h⟩)
    simp [hny]
  rw [(Finset.sum_subset hsub hzero).symm]
  refine Finset.sum_congr rfl (fun n hn => ?_)
  have hny : n ≤ y := (Finset.mem_Icc.mp hn).2
  simp [hny]

theorem mean_value_large_range :
    ∃ C : ℝ, 0 < C ∧ ∀ x Q : ℕ, 2 ≤ x → 1 ≤ Q → x ≤ Q ^ 2 →
      (∑ q ∈ Finset.Icc 1 Q, ((q : ℝ) / (q.totient : ℝ)) *
        ∑ χ ∈ (@Finset.filter (DirichletCharacter ℂ q) (fun χ => χ.IsPrimitive)
                (Classical.decPred _) Finset.univ),
          sSup ((fun y : ℕ => ‖∑ n ∈ Finset.Icc 1 y,
              ((ArithmeticFunction.vonMangoldt n : ℝ) : ℂ) * χ (n : ZMod q)‖) '' Set.Icc 1 x))
      ≤ C * ((x : ℝ) + (x : ℝ) ^ (1 / 2 : ℝ) * (Q : ℝ) ^ 2
              + (x : ℝ) ^ (2 / 3 : ℝ) * (Q : ℝ) ^ (3 / 2 : ℝ)
              + (x : ℝ) ^ (5 / 6 : ℝ) * (Q : ℝ))
          * (Real.log ((x : ℝ) * (Q : ℝ) + 2)) ^ (7 / 2 : ℝ) := by
  obtain ⟨c, hc, H⟩ := maximal_bilinear_char_large_sieve_sSup
  obtain ⟨D, hD, HD⟩ := Commons.NumberTheory.ArithmeticFunction.sum_vonMangoldt_sq_le
  refine ⟨4 * c * Real.sqrt D, by positivity, ?_⟩
  intro x Q hx hQ hxQ
  set b : ℕ → ℂ := fun n => ((ArithmeticFunction.vonMangoldt n : ℝ) : ℂ) with hbdef
  have hx1 : 1 ≤ x := by omega
  have hQ2 : 2 ≤ Q := by
    by_contra h
    have h1 : Q ≤ 1 := by omega
    interval_cases Q <;> omega
  have hH := H Q 1 x hQ (le_refl 1) hx1 (fun _ => (1 : ℂ)) b
  have hLHS_eq : (∑ q ∈ Finset.Icc 1 Q, ((q : ℝ) / (q.totient : ℝ)) *
        ∑ χ ∈ (@Finset.filter (DirichletCharacter ℂ q) (fun χ => χ.IsPrimitive)
                (Classical.decPred _) Finset.univ),
          sSup ((fun y : ℕ => ‖∑ n ∈ Finset.Icc 1 y,
              ((ArithmeticFunction.vonMangoldt n : ℝ) : ℂ) * χ (n : ZMod q)‖) '' Set.Icc 1 x))
      = (∑ q ∈ Finset.Icc 1 Q, ((q : ℝ) / (q.totient : ℝ)) *
          ∑ χ ∈ (@Finset.filter (DirichletCharacter ℂ q) (fun χ => χ.IsPrimitive)
                  (Classical.decPred _) Finset.univ),
            sSup ((fun y : ℕ => ‖∑ m ∈ Finset.Icc 1 1, ∑ n ∈ Finset.Icc 1 x,
              (if m * n ≤ y then (1 : ℂ) else 0) * (fun _ => (1 : ℂ)) m * b n * χ ((m * n : ℕ) : ZMod q)‖)
                '' Set.Icc 1 (1 * x))) := by
    rw [one_mul]
    refine Finset.sum_congr rfl (fun q hq => ?_)
    refine congrArg (fun t => ((q : ℝ) / (q.totient : ℝ)) * t) ?_
    refine Finset.sum_congr rfl (fun χ hχ => ?_)
    apply congrArg sSup
    apply Set.image_congr
    intro y hy
    rw [mean_value_large_range_inner_eq q x y b χ hy.2]
  rw [← hLHS_eq] at hH
  have hxr : (0:ℝ) < x := by exact_mod_cast (by omega : 0 < x)
  have hx2r : (2:ℝ) ≤ x := by exact_mod_cast hx
  have hQr : (0:ℝ) < Q := by exact_mod_cast (by omega : 0 < Q)
  have hQ1r : (1:ℝ) ≤ Q := by exact_mod_cast hQ
  have hQ2r : (2:ℝ) ≤ Q := by exact_mod_cast hQ2
  have hxQr : (x:ℝ) ≤ (Q:ℝ)^2 := by exact_mod_cast hxQ
  have hlog4 : (1:ℝ) < Real.log 4 := by
    rw [Real.lt_log_iff_exp_lt (by norm_num)]
    linarith [Real.exp_one_lt_d9]
  have hT1 : (1:ℝ) ≤ Real.log (2*(x:ℝ)+2) := by
    have h4 : (4:ℝ) ≤ 2*(x:ℝ)+2 := by linarith
    exact le_of_lt (lt_of_lt_of_le hlog4 (Real.log_le_log (by norm_num) h4))
  have hL1 : (1:ℝ) ≤ Real.log ((x:ℝ)*(Q:ℝ)+2) := by
    have h4 : (4:ℝ) ≤ (x:ℝ)*(Q:ℝ)+2 := by nlinarith [hx2r, hQ2r]
    exact le_of_lt (lt_of_lt_of_le hlog4 (Real.log_le_log (by norm_num) h4))
  have hlog_le : Real.log (2*(x:ℝ)+2) ≤ Real.log ((x:ℝ)*(Q:ℝ)+2) := by
    apply Real.log_le_log (by linarith)
    nlinarith [hQ2r, hxr]
  have hS1 : (∑ m ∈ Finset.Icc 1 1, ‖(1:ℂ)‖^2) = 1 := by
    rw [Finset.Icc_self, Finset.sum_singleton, norm_one]; norm_num
  have hS2 : (∑ n ∈ Finset.Icc 1 x, ‖b n‖^2) ≤ D * (x:ℝ) * Real.log (2*(x:ℝ)+2) := by
    have heq : (∑ n ∈ Finset.Icc 1 x, ‖b n‖^2)
        = ∑ n ∈ Finset.Icc 1 x, (ArithmeticFunction.vonMangoldt n)^2 := by
      refine Finset.sum_congr rfl (fun n hn => ?_)
      simp only [hbdef, Complex.norm_real, Real.norm_eq_abs,
        abs_of_nonneg ArithmeticFunction.vonMangoldt_nonneg]
    rw [heq]; exact HD x
  have hA : Real.sqrt (1 + (Q:ℝ)^2) ≤ 2 * Q := by
    rw [Real.sqrt_le_left (by positivity)]
    nlinarith [hQ1r]
  have hB2 : Real.sqrt ((x:ℝ) + (Q:ℝ)^2) ≤ 2 * Q := by
    rw [Real.sqrt_le_left (by positivity)]
    nlinarith [hxQr]
  have hT32 : Real.sqrt (Real.log (2*(x:ℝ)+2)) * Real.log (2*(x:ℝ)+2)
      ≤ (Real.log ((x:ℝ)*(Q:ℝ)+2))^(7/2:ℝ) := by
    have hsqrt_le : Real.sqrt (Real.log (2*(x:ℝ)+2)) ≤ Real.log ((x:ℝ)*(Q:ℝ)+2) := by
      rw [Real.sqrt_le_left (by linarith)]
      nlinarith [hlog_le, hL1]
    have hTpos : (0:ℝ) < Real.log (2*(x:ℝ)+2) := lt_of_lt_of_le one_pos hT1
    calc Real.sqrt (Real.log (2*(x:ℝ)+2)) * Real.log (2*(x:ℝ)+2)
        ≤ Real.log ((x:ℝ)*(Q:ℝ)+2) * Real.log ((x:ℝ)*(Q:ℝ)+2) :=
          mul_le_mul hsqrt_le hlog_le (le_of_lt hTpos) (by linarith [hL1])
      _ = (Real.log ((x:ℝ)*(Q:ℝ)+2))^2 := by ring
      _ ≤ (Real.log ((x:ℝ)*(Q:ℝ)+2))^(7/2:ℝ) := by
          rw [← Real.rpow_natCast]
          exact Real.rpow_le_rpow_of_exponent_le hL1 (by norm_num)
  have hb : Real.sqrt (((x:ℝ) + (Q:ℝ)^2) * (∑ n ∈ Finset.Icc 1 x, ‖b n‖^2))
      ≤ (2*Q) * Real.sqrt D * Real.sqrt (x:ℝ) * Real.sqrt (Real.log (2*(x:ℝ)+2)) := by
    have hb1 : Real.sqrt (((x:ℝ) + (Q:ℝ)^2) * (∑ n ∈ Finset.Icc 1 x, ‖b n‖^2))
        ≤ Real.sqrt (((x:ℝ) + (Q:ℝ)^2) * (D * (x:ℝ) * Real.log (2*(x:ℝ)+2))) :=
      Real.sqrt_le_sqrt (mul_le_mul_of_nonneg_left hS2 (by positivity))
    have hb2 : Real.sqrt (((x:ℝ) + (Q:ℝ)^2) * (D * (x:ℝ) * Real.log (2*(x:ℝ)+2)))
        = Real.sqrt ((x:ℝ) + (Q:ℝ)^2) * Real.sqrt D * Real.sqrt (x:ℝ)
            * Real.sqrt (Real.log (2*(x:ℝ)+2)) := by
      rw [show D * (x:ℝ) * Real.log (2*(x:ℝ)+2)
            = D * ((x:ℝ) * Real.log (2*(x:ℝ)+2)) by ring]
      rw [Real.sqrt_mul (by positivity : (0:ℝ) ≤ (x:ℝ)+(Q:ℝ)^2)]
      rw [Real.sqrt_mul (by positivity : (0:ℝ) ≤ D)]
      rw [Real.sqrt_mul (by positivity : (0:ℝ) ≤ (x:ℝ))]
      ring
    have hb3 : Real.sqrt ((x:ℝ) + (Q:ℝ)^2) * Real.sqrt D * Real.sqrt (x:ℝ)
          * Real.sqrt (Real.log (2*(x:ℝ)+2))
        ≤ (2*Q) * Real.sqrt D * Real.sqrt (x:ℝ) * Real.sqrt (Real.log (2*(x:ℝ)+2)) := by
      apply mul_le_mul_of_nonneg_right _ (Real.sqrt_nonneg _)
      apply mul_le_mul_of_nonneg_right _ (Real.sqrt_nonneg _)
      apply mul_le_mul_of_nonneg_right _ (Real.sqrt_nonneg _)
      exact hB2
    exact le_trans hb1 (le_trans (le_of_eq hb2) hb3)
  refine le_trans hH ?_
  simp only [Nat.cast_one]
  have h2x : 2 * (1:ℝ) * (x:ℝ) + 2 = 2 * (x:ℝ) + 2 := by ring
  rw [h2x]
  have hS1' : (∑ m ∈ Finset.Icc 1 1, ‖(1:ℂ)‖^2) = 1 := hS1
  have hb1g : Real.sqrt ((1 + (Q:ℝ)^2) * (∑ m ∈ Finset.Icc 1 1, ‖(1:ℂ)‖^2))
      = Real.sqrt (1 + (Q:ℝ)^2) := by rw [hS1, mul_one]
  rw [hb1g]
  have hca : c * Real.sqrt (1 + (Q:ℝ)^2) ≤ c * (2*Q) := mul_le_mul_of_nonneg_left hA hc.le
  have hcb : (c * Real.sqrt (1 + (Q:ℝ)^2)) * Real.sqrt (((x:ℝ)+(Q:ℝ)^2) * (∑ n ∈ Finset.Icc 1 x, ‖b n‖^2))
      ≤ (c * (2*Q)) * ((2*Q) * Real.sqrt D * Real.sqrt (x:ℝ) * Real.sqrt (Real.log (2*(x:ℝ)+2))) :=
    mul_le_mul hca hb (Real.sqrt_nonneg _) (by positivity)
  have hstep := mul_le_mul_of_nonneg_right hcb (le_of_lt (lt_of_lt_of_le one_pos hT1))
  refine le_trans hstep ?_
  have heq : c*(2*Q)*((2*Q)*Real.sqrt D*Real.sqrt (x:ℝ)*Real.sqrt (Real.log (2*(x:ℝ)+2)))*(Real.log (2*(x:ℝ)+2))
      = 4*c*Real.sqrt D*Real.sqrt (x:ℝ)*(Q:ℝ)^2*(Real.sqrt (Real.log (2*(x:ℝ)+2))*(Real.log (2*(x:ℝ)+2))) := by ring
  rw [heq]
  have h1 : 4*c*Real.sqrt D*Real.sqrt (x:ℝ)*(Q:ℝ)^2*(Real.sqrt (Real.log (2*(x:ℝ)+2))*(Real.log (2*(x:ℝ)+2)))
      ≤ 4*c*Real.sqrt D*Real.sqrt (x:ℝ)*(Q:ℝ)^2*((Real.log ((x:ℝ)*(Q:ℝ)+2))^(7/2:ℝ)) := by
    apply mul_le_mul_of_nonneg_left hT32
    positivity
  refine le_trans h1 ?_
  have hpoly : Real.sqrt (x:ℝ) * (Q:ℝ)^2
      ≤ (x:ℝ) + (x:ℝ)^(1/2:ℝ)*(Q:ℝ)^2 + (x:ℝ)^(2/3:ℝ)*(Q:ℝ)^(3/2:ℝ) + (x:ℝ)^(5/6:ℝ)*(Q:ℝ) := by
    rw [Real.sqrt_eq_rpow]
    nlinarith [show (0:ℝ) ≤ (x:ℝ)^(2/3:ℝ) by positivity,
      show (0:ℝ) ≤ (x:ℝ)^(5/6:ℝ) by positivity, show (0:ℝ) ≤ (x:ℝ) by positivity,
      show (0:ℝ) ≤ (Q:ℝ) by positivity, show (0:ℝ) ≤ (Q:ℝ)^(3/2:ℝ) by positivity]
  have hLnn : (0:ℝ) ≤ (Real.log ((x:ℝ)*(Q:ℝ)+2))^(7/2:ℝ) := by positivity
  have h3 : 4*c*Real.sqrt D*Real.sqrt (x:ℝ)*(Q:ℝ)^2*((Real.log ((x:ℝ)*(Q:ℝ)+2))^(7/2:ℝ))
      ≤ (4*c*Real.sqrt D) * ((x:ℝ) + (x:ℝ)^(1/2:ℝ)*(Q:ℝ)^2
            + (x:ℝ)^(2/3:ℝ)*(Q:ℝ)^(3/2:ℝ) + (x:ℝ)^(5/6:ℝ)*(Q:ℝ))
          * ((Real.log ((x:ℝ)*(Q:ℝ)+2))^(7/2:ℝ)) := by
    calc 4*c*Real.sqrt D*Real.sqrt (x:ℝ)*(Q:ℝ)^2*((Real.log ((x:ℝ)*(Q:ℝ)+2))^(7/2:ℝ))
        = (4*c*Real.sqrt D) * (Real.sqrt (x:ℝ)*(Q:ℝ)^2*((Real.log ((x:ℝ)*(Q:ℝ)+2))^(7/2:ℝ))) := by ring
      _ ≤ (4*c*Real.sqrt D) * (((x:ℝ) + (x:ℝ)^(1/2:ℝ)*(Q:ℝ)^2
            + (x:ℝ)^(2/3:ℝ)*(Q:ℝ)^(3/2:ℝ) + (x:ℝ)^(5/6:ℝ)*(Q:ℝ)) * ((Real.log ((x:ℝ)*(Q:ℝ)+2))^(7/2:ℝ))) := by
          apply mul_le_mul_of_nonneg_left _ (by positivity)
          exact mul_le_mul_of_nonneg_right hpoly hLnn
      _ = (4*c*Real.sqrt D) * ((x:ℝ) + (x:ℝ)^(1/2:ℝ)*(Q:ℝ)^2
            + (x:ℝ)^(2/3:ℝ)*(Q:ℝ)^(3/2:ℝ) + (x:ℝ)^(5/6:ℝ)*(Q:ℝ))
          * ((Real.log ((x:ℝ)*(Q:ℝ)+2))^(7/2:ℝ)) := by ring
  exact h3


end Commons.NumberTheory.BombieriVinogradov
