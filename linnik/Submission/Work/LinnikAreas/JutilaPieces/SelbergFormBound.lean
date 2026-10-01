import Mathlib
import Submission.Work.ZeroDensity.Jutila.sieveSymbolDefs
import Submission.Work.ZeroDensity.Jutila.sieveA_diag
import Submission.Work.LinnikAreas.Density4.SelbergDefs
import Submission.Work.LinnikAreas.Density4.selRadSum_le_totient
import Submission.Work.LinnikAreas.Density4.sum_Icc_div_reindex
import Submission.Commons.NumberTheory.Moebius.log_weighted_moebius_recip_bound
import Submission.Work.LinnikAreas.Density4.sum_inv_exp_neg_sqrt_log_div
import Submission.Work.LinnikAreas.JutilaPieces.U_eq
import Submission.Work.LinnikAreas.JutilaPieces.W_eq
import Submission.Work.LinnikAreas.JutilaPieces.reindex_bound
import Submission.Work.LinnikAreas.JutilaPieces.sum_muRecipSq_div_le

namespace Work.LinnikAreas.JutilaPieces

open Finset
open scoped BigOperators

noncomputable section

/-! ## Auxiliary lemmas (some delegated) -/

/-- Weighted Cauchy–Schwarz: for `f ≥ 0`, `(Σ f·b)² ≤ (Σ f)·(Σ f·b²)`. -/
lemma sq_sum_mul_le (s : Finset ℕ) (f b : ℕ → ℝ) (hf : ∀ d ∈ s, 0 ≤ f d) :
    (∑ d ∈ s, f d * b d) ^ 2 ≤ (∑ d ∈ s, f d) * (∑ d ∈ s, f d * (b d) ^ 2) := by
  have key := Finset.sum_mul_sq_le_sq_mul_sq s (fun d => Real.sqrt (f d))
    (fun d => Real.sqrt (f d) * b d)
  have h1 : (∑ d ∈ s, Real.sqrt (f d) * (Real.sqrt (f d) * b d))
      = ∑ d ∈ s, f d * b d := by
    apply Finset.sum_congr rfl; intro d hd
    have hs : Real.sqrt (f d) * Real.sqrt (f d) = f d := by
      rw [← sq, Real.sq_sqrt (hf d hd)]
    rw [← mul_assoc, hs]
  have h2 : (∑ d ∈ s, (Real.sqrt (f d)) ^ 2) = ∑ d ∈ s, f d := by
    apply Finset.sum_congr rfl; intro d hd
    rw [Real.sq_sqrt (hf d hd)]
  have h3 : (∑ d ∈ s, (Real.sqrt (f d) * b d) ^ 2) = ∑ d ∈ s, f d * (b d) ^ 2 := by
    apply Finset.sum_congr rfl; intro d hd
    rw [mul_pow, Real.sq_sqrt (hf d hd)]
  rwa [h1, h2, h3] at key

/-! ## The main theorem -/

theorem SelbergFormBound :
    ∃ C : ℝ, 0 < C ∧ ∀ V : ℕ, 1 ≤ V →
      (∑ d ∈ Finset.Icc 1 V, ∑ e ∈ Finset.Icc 1 V,
        (ArithmeticFunction.moebius d : ℝ) * (ArithmeticFunction.moebius e : ℝ)
          / (Nat.lcm d e : ℝ)) ≤ C := by
  obtain ⟨K, hKpos, hK⟩ := sum_muRecipSq_div_le
  refine ⟨K, hKpos, fun V hV => ?_⟩
  have hgoal : (∑ d ∈ Finset.Icc 1 V, ∑ e ∈ Finset.Icc 1 V,
        (ArithmeticFunction.moebius d : ℝ) * (ArithmeticFunction.moebius e : ℝ)
          / (Nat.lcm d e : ℝ)) = Work.ZeroDensity.Jutila.A V := rfl
  rw [hgoal, Work.ZeroDensity.Jutila.sieveA_diag V]
  let h : ℕ → ℝ := fun n => (Commons.NumberTheory.Moebius.muRecipSum (V / n)) ^ 2
  have hhnn : ∀ n, 0 ≤ h n := fun n => sq_nonneg _
  have hterm : ∀ l ∈ Finset.Icc 1 V,
      (Nat.totient l : ℝ) * (Work.ZeroDensity.Jutila.W V l) ^ 2
        ≤ ((ArithmeticFunction.moebius l : ℝ)) ^ 2 / (l : ℝ) *
          (∑ d ∈ (Finset.Icc 1 (V / l)).filter (fun d => Work.LinnikAreas.Density4.SmoothOf d l),
            (1 / (d : ℝ)) * h (l * d)) := by
    intro l hl
    obtain ⟨hl1, hlV⟩ := Finset.mem_Icc.mp hl
    have hlR : (0 : ℝ) < (l : ℝ) := by exact_mod_cast (show 0 < l by omega)
    have hphiR : (0 : ℝ) < (Nat.totient l : ℝ) :=
      by exact_mod_cast (Nat.totient_pos.mpr (show 0 < l by omega))
    have hU' : Work.ZeroDensity.Jutila.U (V / l) l
        = ∑ d ∈ (Finset.Icc 1 (V / l)).filter
              (fun d => Work.LinnikAreas.Density4.SmoothOf d l),
            (1 / (d : ℝ)) *
              Commons.NumberTheory.Moebius.muRecipSum (V / (l * d)) := by
      rw [U_eq (V / l) l hl1]
      apply Finset.sum_congr rfl
      intro d hd
      rw [Nat.div_div_eq_div_mul]
    rw [W_eq V l hl1, hU']
    set D : Finset ℕ := (Finset.Icc 1 (V / l)).filter
        (fun d => Work.LinnikAreas.Density4.SmoothOf d l) with hDdef
    by_cases hsf : Squarefree l
    · have hset : (∑ d ∈ D, (1 / (d : ℝ)))
          = Work.LinnikAreas.Density4.selRadSum ((V / l : ℕ) : ℝ) l := by
        rw [hDdef]; simp [Work.LinnikAreas.Density4.selRadSum]
      have hS : (∑ d ∈ D, (1 / (d : ℝ))) ≤ (l : ℝ) / (Nat.totient l : ℝ) := by
        rw [hset]
        exact Work.LinnikAreas.Density4.selRadSum_le_totient _ l hsf
      have hCS : (∑ d ∈ D, (1 / (d : ℝ)) *
              Commons.NumberTheory.Moebius.muRecipSum (V / (l * d))) ^ 2
            ≤ (∑ d ∈ D, (1 / (d : ℝ))) *
              (∑ d ∈ D, (1 / (d : ℝ)) *
                (Commons.NumberTheory.Moebius.muRecipSum (V / (l * d))) ^ 2) :=
        sq_sum_mul_le D (fun d => 1 / (d : ℝ))
          (fun d => Commons.NumberTheory.Moebius.muRecipSum (V / (l * d)))
          (fun d hd => by positivity)
      have hTnn : 0 ≤ ∑ d ∈ D, (1 / (d : ℝ)) * h (l * d) :=
        Finset.sum_nonneg (fun d hd => mul_nonneg (by positivity) (hhnn _))
      have hchain :
          (Nat.totient l : ℝ) *
              ((ArithmeticFunction.moebius l : ℝ) / (l : ℝ) *
                (∑ d ∈ D, (1 / (d : ℝ)) *
                  Commons.NumberTheory.Moebius.muRecipSum (V / (l * d)))) ^ 2
            ≤ ((ArithmeticFunction.moebius l : ℝ)) ^ 2 / (l : ℝ) *
              (∑ d ∈ D, (1 / (d : ℝ)) * h (l * d)) := by
        calc (Nat.totient l : ℝ) *
                ((ArithmeticFunction.moebius l : ℝ) / (l : ℝ) *
                  (∑ d ∈ D, (1 / (d : ℝ)) *
                    Commons.NumberTheory.Moebius.muRecipSum (V / (l * d)))) ^ 2
            = (Nat.totient l : ℝ) * ((ArithmeticFunction.moebius l : ℝ)) ^ 2 / (l : ℝ) ^ 2 *
                (∑ d ∈ D, (1 / (d : ℝ)) *
                  Commons.NumberTheory.Moebius.muRecipSum (V / (l * d))) ^ 2 := by
              ring
          _ ≤ (Nat.totient l : ℝ) * ((ArithmeticFunction.moebius l : ℝ)) ^ 2 / (l : ℝ) ^ 2 *
                ((∑ d ∈ D, (1 / (d : ℝ))) *
                  (∑ d ∈ D, (1 / (d : ℝ)) *
                    (Commons.NumberTheory.Moebius.muRecipSum (V / (l * d))) ^ 2)) := by
              apply mul_le_mul_of_nonneg_left hCS
              positivity
          _ ≤ (Nat.totient l : ℝ) * ((ArithmeticFunction.moebius l : ℝ)) ^ 2 / (l : ℝ) ^ 2 *
                (((l : ℝ) / (Nat.totient l : ℝ)) *
                  (∑ d ∈ D, (1 / (d : ℝ)) * h (l * d))) := by
              apply mul_le_mul_of_nonneg_left
              · apply mul_le_mul_of_nonneg_right hS
                exact Finset.sum_nonneg (fun d hd => mul_nonneg (by positivity) (sq_nonneg _))
              · positivity
          _ = ((ArithmeticFunction.moebius l : ℝ)) ^ 2 / (l : ℝ) *
                (∑ d ∈ D, (1 / (d : ℝ)) * h (l * d)) := by
              field_simp
      exact hchain
    · have hmu0 : (ArithmeticFunction.moebius l : ℝ) = 0 := by
        have hz : ArithmeticFunction.moebius l = 0 :=
          ArithmeticFunction.moebius_eq_zero_of_not_squarefree hsf
        rw [hz]; simp
      rw [hmu0]; simp
  calc ∑ l ∈ Finset.Icc 1 V, (Nat.totient l : ℝ) * (Work.ZeroDensity.Jutila.W V l) ^ 2
      ≤ ∑ l ∈ Finset.Icc 1 V, ((ArithmeticFunction.moebius l : ℝ)) ^ 2 / (l : ℝ) *
          (∑ d ∈ (Finset.Icc 1 (V / l)).filter (fun d => Work.LinnikAreas.Density4.SmoothOf d l),
            (1 / (d : ℝ)) * h (l * d)) := Finset.sum_le_sum hterm
    _ = ∑ l ∈ Finset.Icc 1 V,
          ∑ d ∈ (Finset.Icc 1 (V / l)).filter (fun d => Work.LinnikAreas.Density4.SmoothOf d l),
            ((ArithmeticFunction.moebius l : ℝ)) ^ 2 *
              ((1 / ((l * d : ℕ) : ℝ)) * h (l * d)) := by
        apply Finset.sum_congr rfl
        intro l hl
        rw [Finset.mul_sum]
        apply Finset.sum_congr rfl
        intro d hd
        have hlne : ((l : ℕ) : ℝ) ≠ 0 := by
          have : 0 < l := (Finset.mem_Icc.mp hl).1
          positivity
        have hdne : ((d : ℕ) : ℝ) ≠ 0 := by
          have : 0 < d := (Finset.mem_Icc.mp (Finset.mem_filter.mp hd).1).1
          positivity
        rw [Nat.cast_mul]
        field_simp
    _ ≤ ∑ n ∈ Finset.Icc 1 V, (1 / (n : ℝ)) * h n := reindex_bound V h hhnn
    _ ≤ K := hK V hV

end

end Work.LinnikAreas.JutilaPieces
