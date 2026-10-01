import Mathlib
import Submission.Work.LinnikAreas.Density4.BzS3.s3esb_defs
import Submission.Work.LinnikAreas.Density4.BzS3.sigma_half_sqrt_sum
import Submission.Work.LinnikAreas2.S3HardAux.sigma_half_supermul
import Submission.Work.LinnikAreas2.S3HardAux.sum_sigma_half_le
import Submission.Work.LinnikAreas2.S3HardAux.sum_inv_sqrt_three_halves_le
import Submission.Work.LinnikAreas2.S3HardAux.sqrt_natdiv_log_pair_bound
import Submission.Work.LinnikAreas2.S3HardAux.sqrt_max_log_pair_bound

open Finset
open scoped BigOperators

namespace Work.LinnikAreas2

noncomputable section

open Work.LinnikAreas.Density4.BzS3
open Work.LinnikAreas2.S3HardAux


theorem phi_sigma_sum_le : ∃ C : ℝ, 0 < C ∧ ∀ T : ℕ, 1 ≤ T →
    (∑ r ∈ Finset.Icc 1 T, (1 / Real.sqrt (r : ℝ))
        * (1 + Real.log ((T : ℝ) / (r : ℝ)))
        * (∑ d ∈ r.divisors, (1 : ℝ) / Real.sqrt (d : ℝ))) ≤ C * Real.sqrt (T : ℝ) := by
  obtain ⟨C0, hC0pos, hC0⟩ := sigma_half_sqrt_sum
  refine ⟨C0, hC0pos, ?_⟩
  intro T hT1
  refine le_trans (Finset.sum_le_sum ?_) (hC0 T hT1)
  intro r hr
  obtain ⟨hr1, hrT⟩ := Finset.mem_Icc.mp hr
  have hlog : Real.log ((T:ℝ)/(r:ℝ)) ≤ Real.log (2 * (T:ℝ)/(r:ℝ)) := by
    apply Real.log_le_log (by positivity)
    have hx : (0:ℝ) ≤ (T:ℝ)/(r:ℝ) := by positivity
    have h2 : 2 * (T:ℝ) / (r:ℝ) = (T:ℝ)/(r:ℝ) + (T:ℝ)/(r:ℝ) := by ring
    rw [h2]; linarith
  have hgoal : (1 / Real.sqrt (r : ℝ)) * (1 + Real.log ((T : ℝ) / (r : ℝ)))
              * (∑ d ∈ r.divisors, (1 : ℝ) / Real.sqrt (d : ℝ))
      ≤ (1 / Real.sqrt (r : ℝ)) * (∑ d ∈ r.divisors, (1 : ℝ) / Real.sqrt (d : ℝ))
        * (1 + Real.log (2 * (T : ℝ) / (r : ℝ))) := by
    have h := mul_le_mul_of_nonneg_left hlog
      (by positivity : (0:ℝ) ≤ (1 / Real.sqrt (r:ℝ)) * (∑ d ∈ r.divisors, (1:ℝ)/Real.sqrt (d:ℝ)))
    nlinarith [h]
  exact hgoal

theorem esbA_le : ∃ C : ℝ, 0 < C ∧ ∀ (z N q : ℕ), 2 ≤ z → z ≤ N → N < z * z → 1 ≤ q →
    q ≤ N / z →
      Work.LinnikAreas.Density4.BzS3.esbA z N q
        ≤ C * (Real.sqrt ((N : ℝ) / (q : ℝ)) * ((N / (q * z) : ℕ) : ℝ)) := by
  obtain ⟨Cp, hCppos, hCp⟩ := phi_sigma_sum_le
  refine ⟨16 * Cp ^ 2, by positivity, ?_⟩
  intro z N q hz hzN hNz hq hqQ
  have hqz : q * z ≤ N := by
    calc q * z ≤ (N / z) * z := Nat.mul_le_mul_right z hqQ
      _ ≤ N := Nat.div_mul_le_self N z
  have hqz0 : 0 < q * z := by positivity
  rw [esbA]
  set T : ℕ := N / (q * z) with hT
  have hT1 : 1 ≤ T := by
    rw [hT]
    rw [Nat.le_div_iff_mul_le hqz0]
    simpa using hqz
  have hpt : ∀ r ∈ Finset.Icc 1 T, ∀ t ∈ Finset.Icc 1 T,
      (Real.sqrt (((N / (q * r * t) : ℕ) : ℝ))
          * (1 + |Real.log (2 * (((N / (q * r * t) : ℕ) : ℝ)) * (t : ℝ) / (z : ℝ))|)
          * (1 + |Real.log (2 * (((N / (q * r * t) : ℕ) : ℝ)) * (r : ℝ) / (z : ℝ))|))
        * (∑ d ∈ (r * t).divisors, (1 : ℝ) / Real.sqrt (d : ℝ))
      ≤ 16 * (Real.sqrt (N : ℝ) / Real.sqrt (q : ℝ))
          * ((1 / Real.sqrt (r : ℝ)) * (1 + Real.log ((T : ℝ) / (r : ℝ))))
          * ((1 / Real.sqrt (t : ℝ)) * (1 + Real.log ((T : ℝ) / (t : ℝ))))
          * ((∑ d ∈ r.divisors, (1 : ℝ) / Real.sqrt (d : ℝ))
              * (∑ d ∈ t.divisors, (1 : ℝ) / Real.sqrt (d : ℝ))) := by
    intro r hr t ht
    obtain ⟨hr1, hrT⟩ := Finset.mem_Icc.mp hr
    obtain ⟨ht1, htT⟩ := Finset.mem_Icc.mp ht
    have hrT' : r ≤ N / (q * z) := by rw [← hT]; exact hrT
    have htT' : t ≤ N / (q * z) := by rw [← hT]; exact htT
    have h1 := sqrt_natdiv_log_pair_bound z N q r t hz hzN hNz hq hr1 hrT' ht1 htT'
    rw [← hT] at h1
    have h2 := sigma_half_supermul r t
    have hb : (0:ℝ) ≤ 16 * (Real.sqrt (N : ℝ) / Real.sqrt (q : ℝ))
          * ((1 / Real.sqrt (r : ℝ)) * (1 + Real.log ((T : ℝ) / (r : ℝ))))
          * ((1 / Real.sqrt (t : ℝ)) * (1 + Real.log ((T : ℝ) / (t : ℝ)))) := by
      have hl1 : (1:ℝ) ≤ (T:ℝ)/(r:ℝ) := by
        rw [one_le_div (by exact_mod_cast (by omega : 0 < r))]
        exact_mod_cast hrT
      have hl2 : (1:ℝ) ≤ (T:ℝ)/(t:ℝ) := by
        rw [one_le_div (by exact_mod_cast (by omega : 0 < t))]
        exact_mod_cast htT
      have h3 : 0 ≤ Real.log ((T:ℝ)/(r:ℝ)) := Real.log_nonneg hl1
      have h4 : 0 ≤ Real.log ((T:ℝ)/(t:ℝ)) := Real.log_nonneg hl2
      positivity
    have hσ : (0:ℝ) ≤ ∑ d ∈ (r * t).divisors, (1 : ℝ) / Real.sqrt (d : ℝ) :=
      Finset.sum_nonneg (fun d _ => by positivity)
    exact mul_le_mul h1 h2 hσ hb
  have hstep : (∑ r ∈ Finset.Icc 1 T, ∑ t ∈ Finset.Icc 1 T,
      (Real.sqrt (((N / (q * r * t) : ℕ) : ℝ))
          * (1 + |Real.log (2 * (((N / (q * r * t) : ℕ) : ℝ)) * (t : ℝ) / (z : ℝ))|)
          * (1 + |Real.log (2 * (((N / (q * r * t) : ℕ) : ℝ)) * (r : ℝ) / (z : ℝ))|))
        * (∑ d ∈ (r * t).divisors, (1 : ℝ) / Real.sqrt (d : ℝ)))
      ≤ ∑ r ∈ Finset.Icc 1 T, ∑ t ∈ Finset.Icc 1 T,
          16 * (Real.sqrt (N : ℝ) / Real.sqrt (q : ℝ))
          * ((1 / Real.sqrt (r : ℝ)) * (1 + Real.log ((T : ℝ) / (r : ℝ))))
          * ((1 / Real.sqrt (t : ℝ)) * (1 + Real.log ((T : ℝ) / (t : ℝ))))
          * ((∑ d ∈ r.divisors, (1 : ℝ) / Real.sqrt (d : ℝ))
              * (∑ d ∈ t.divisors, (1 : ℝ) / Real.sqrt (d : ℝ))) := by
    apply Finset.sum_le_sum
    intro r hr
    apply Finset.sum_le_sum
    intro t ht
    exact hpt r hr t ht
  have hkey : (∑ r ∈ Finset.Icc 1 T, ∑ t ∈ Finset.Icc 1 T,
          16 * (Real.sqrt (N : ℝ) / Real.sqrt (q : ℝ))
          * ((1 / Real.sqrt (r : ℝ)) * (1 + Real.log ((T : ℝ) / (r : ℝ))))
          * ((1 / Real.sqrt (t : ℝ)) * (1 + Real.log ((T : ℝ) / (t : ℝ))))
          * ((∑ d ∈ r.divisors, (1 : ℝ) / Real.sqrt (d : ℝ))
              * (∑ d ∈ t.divisors, (1 : ℝ) / Real.sqrt (d : ℝ))))
      = 16 * (Real.sqrt (N : ℝ) / Real.sqrt (q : ℝ))
          * ((∑ r ∈ Finset.Icc 1 T, (1 / Real.sqrt (r : ℝ))
                * (1 + Real.log ((T : ℝ) / (r : ℝ)))
                * (∑ d ∈ r.divisors, (1 : ℝ) / Real.sqrt (d : ℝ)))
             * (∑ t ∈ Finset.Icc 1 T, (1 / Real.sqrt (t : ℝ))
                * (1 + Real.log ((T : ℝ) / (t : ℝ)))
                * (∑ d ∈ t.divisors, (1 : ℝ) / Real.sqrt (d : ℝ)))) := by
    have e : (∑ r ∈ Finset.Icc 1 T, ∑ t ∈ Finset.Icc 1 T,
          16 * (Real.sqrt (N : ℝ) / Real.sqrt (q : ℝ))
          * ((1 / Real.sqrt (r : ℝ)) * (1 + Real.log ((T : ℝ) / (r : ℝ))))
          * ((1 / Real.sqrt (t : ℝ)) * (1 + Real.log ((T : ℝ) / (t : ℝ))))
          * ((∑ d ∈ r.divisors, (1 : ℝ) / Real.sqrt (d : ℝ))
              * (∑ d ∈ t.divisors, (1 : ℝ) / Real.sqrt (d : ℝ))))
        = ∑ r ∈ Finset.Icc 1 T, ∑ t ∈ Finset.Icc 1 T,
            (16 * (Real.sqrt (N : ℝ) / Real.sqrt (q : ℝ))
              * ((1 / Real.sqrt (r : ℝ)) * (1 + Real.log ((T : ℝ) / (r : ℝ)))
                 * (∑ d ∈ r.divisors, (1 : ℝ) / Real.sqrt (d : ℝ))))
            * ((1 / Real.sqrt (t : ℝ)) * (1 + Real.log ((T : ℝ) / (t : ℝ)))
                 * (∑ d ∈ t.divisors, (1 : ℝ) / Real.sqrt (d : ℝ))) := by
      apply Finset.sum_congr rfl; intro r hr
      apply Finset.sum_congr rfl; intro t ht
      ring
    rw [e, ← Finset.sum_mul_sum, ← Finset.mul_sum]
    ring
  have hA : (∑ r ∈ Finset.Icc 1 T, (1 / Real.sqrt (r : ℝ))
                * (1 + Real.log ((T : ℝ) / (r : ℝ)))
                * (∑ d ∈ r.divisors, (1 : ℝ) / Real.sqrt (d : ℝ))) ≤ Cp * Real.sqrt (T : ℝ) :=
    hCp T hT1
  have hA2 : (∑ r ∈ Finset.Icc 1 T, (1 / Real.sqrt (r : ℝ))
                * (1 + Real.log ((T : ℝ) / (r : ℝ)))
                * (∑ d ∈ r.divisors, (1 : ℝ) / Real.sqrt (d : ℝ))) ≤ Cp * Real.sqrt (T : ℝ) :=
    hCp T hT1
  have hAnn : (0:ℝ) ≤ ∑ r ∈ Finset.Icc 1 T, (1 / Real.sqrt (r : ℝ))
                * (1 + Real.log ((T : ℝ) / (r : ℝ)))
                * (∑ d ∈ r.divisors, (1 : ℝ) / Real.sqrt (d : ℝ)) := by
    apply Finset.sum_nonneg
    intro r hr
    obtain ⟨hr1, hrT⟩ := Finset.mem_Icc.mp hr
    have hl : (1:ℝ) ≤ (T:ℝ)/(r:ℝ) := by
      rw [one_le_div (by exact_mod_cast (by omega : 0 < r))]
      exact_mod_cast hrT
    have h3 : 0 ≤ Real.log ((T:ℝ)/(r:ℝ)) := Real.log_nonneg hl
    positivity
  calc (∑ r ∈ Finset.Icc 1 T, ∑ t ∈ Finset.Icc 1 T,
      (Real.sqrt (((N / (q * r * t) : ℕ) : ℝ))
          * (1 + |Real.log (2 * (((N / (q * r * t) : ℕ) : ℝ)) * (t : ℝ) / (z : ℝ))|)
          * (1 + |Real.log (2 * (((N / (q * r * t) : ℕ) : ℝ)) * (r : ℝ) / (z : ℝ))|))
        * (∑ d ∈ (r * t).divisors, (1 : ℝ) / Real.sqrt (d : ℝ)))
      ≤ 16 * (Real.sqrt (N : ℝ) / Real.sqrt (q : ℝ))
          * ((∑ r ∈ Finset.Icc 1 T, (1 / Real.sqrt (r : ℝ))
                * (1 + Real.log ((T : ℝ) / (r : ℝ)))
                * (∑ d ∈ r.divisors, (1 : ℝ) / Real.sqrt (d : ℝ)))
             * (∑ t ∈ Finset.Icc 1 T, (1 / Real.sqrt (t : ℝ))
                * (1 + Real.log ((T : ℝ) / (t : ℝ)))
                * (∑ d ∈ t.divisors, (1 : ℝ) / Real.sqrt (d : ℝ)))) := by
        rw [← hkey]; exact hstep
    _ ≤ 16 * (Real.sqrt (N : ℝ) / Real.sqrt (q : ℝ))
          * ((Cp * Real.sqrt (T : ℝ)) * (Cp * Real.sqrt (T : ℝ))) := by
        apply mul_le_mul_of_nonneg_left _ (by positivity)
        exact mul_le_mul hA hA2 hAnn (mul_nonneg (le_of_lt hCppos) (Real.sqrt_nonneg _))
    _ = 16 * Cp ^ 2 * (Real.sqrt (N : ℝ) / Real.sqrt (q : ℝ)) * (T : ℝ) := by
        have hs : Real.sqrt (T:ℝ) * Real.sqrt (T:ℝ) = (T:ℝ) := by
          rw [← pow_two]; exact Real.sq_sqrt (by positivity)
        have hsq : (Cp * Real.sqrt (T:ℝ)) * (Cp * Real.sqrt (T:ℝ))
            = Cp^2 * (Real.sqrt (T:ℝ) * Real.sqrt (T:ℝ)) := by ring
        rw [hsq, hs]; ring
    _ = 16 * Cp ^ 2 * (Real.sqrt ((N : ℝ) / (q : ℝ)) * ((T : ℕ) : ℝ)) := by
        rw [Real.sqrt_div (by positivity : (0:ℝ) ≤ (N:ℝ))]; ring

theorem esbB_le : ∃ C : ℝ, 0 < C ∧ ∀ (z N q : ℕ), 2 ≤ z → z ≤ N → N < z * z → 1 ≤ q →
    q ≤ N / z →
      Work.LinnikAreas.Density4.BzS3.esbB z N q
        ≤ C * (Real.sqrt (z : ℝ) * (((N / (q * z) : ℕ) : ℝ) * Real.sqrt (((N / (q * z) : ℕ) : ℝ)))) := by
  obtain ⟨Cp, hCppos, hCp⟩ := phi_sigma_sum_le
  refine ⟨32 * Cp, by positivity, ?_⟩
  intro z N q hz hzN hNz hq hqQ
  have hqz : q * z ≤ N := by
    calc q * z ≤ (N / z) * z := Nat.mul_le_mul_right z hqQ
      _ ≤ N := Nat.div_mul_le_self N z
  have hqz0 : 0 < q * z := by positivity
  rw [esbB]
  set T : ℕ := N / (q * z) with hT
  have hT1 : 1 ≤ T := by
    rw [hT]
    rw [Nat.le_div_iff_mul_le hqz0]
    simpa using hqz
  have hpt : ∀ r ∈ Finset.Icc 1 T, ∀ t ∈ Finset.Icc 1 T,
      (Real.sqrt (((max (z / t) (z / r) : ℕ) : ℝ))
          * (1 + |Real.log (2 * (((max (z / t) (z / r) : ℕ) : ℝ)) * (t : ℝ) / (z : ℝ))|)
          * (1 + |Real.log (2 * (((max (z / t) (z / r) : ℕ) : ℝ)) * (r : ℝ) / (z : ℝ))|))
        * (∑ d ∈ (r * t).divisors, (1 : ℝ) / Real.sqrt (d : ℝ))
      ≤ 4 * Real.sqrt (z : ℝ)
          * ((1 / Real.sqrt (r : ℝ)) * (1 + Real.log ((T : ℝ) / (r : ℝ)))
             + (1 / Real.sqrt (t : ℝ)) * (1 + Real.log ((T : ℝ) / (t : ℝ))))
          * ((∑ d ∈ r.divisors, (1 : ℝ) / Real.sqrt (d : ℝ))
              * (∑ d ∈ t.divisors, (1 : ℝ) / Real.sqrt (d : ℝ))) := by
    intro r hr t ht
    obtain ⟨hr1, hrT⟩ := Finset.mem_Icc.mp hr
    obtain ⟨ht1, htT⟩ := Finset.mem_Icc.mp ht
    have hrT' : r ≤ N / (q * z) := by rw [← hT]; exact hrT
    have htT' : t ≤ N / (q * z) := by rw [← hT]; exact htT
    have h1 := sqrt_max_log_pair_bound z N q r t hz hzN hNz hq hr1 hrT' ht1 htT'
    rw [← hT] at h1
    have h2 := sigma_half_supermul r t
    have hb : (0:ℝ) ≤ 4 * Real.sqrt (z : ℝ)
          * ((1 / Real.sqrt (r : ℝ)) * (1 + Real.log ((T : ℝ) / (r : ℝ)))
             + (1 / Real.sqrt (t : ℝ)) * (1 + Real.log ((T : ℝ) / (t : ℝ)))) := by
      have hl1 : (1:ℝ) ≤ (T:ℝ)/(r:ℝ) := by
        rw [one_le_div (by exact_mod_cast (by omega : 0 < r))]
        exact_mod_cast hrT
      have hl2 : (1:ℝ) ≤ (T:ℝ)/(t:ℝ) := by
        rw [one_le_div (by exact_mod_cast (by omega : 0 < t))]
        exact_mod_cast htT
      have h3 : 0 ≤ Real.log ((T:ℝ)/(r:ℝ)) := Real.log_nonneg hl1
      have h4 : 0 ≤ Real.log ((T:ℝ)/(t:ℝ)) := Real.log_nonneg hl2
      positivity
    have hσ : (0:ℝ) ≤ ∑ d ∈ (r * t).divisors, (1 : ℝ) / Real.sqrt (d : ℝ) :=
      Finset.sum_nonneg (fun d _ => by positivity)
    exact mul_le_mul h1 h2 hσ hb
  have hstep : (∑ r ∈ Finset.Icc 1 T, ∑ t ∈ Finset.Icc 1 T,
      (Real.sqrt (((max (z / t) (z / r) : ℕ) : ℝ))
          * (1 + |Real.log (2 * (((max (z / t) (z / r) : ℕ) : ℝ)) * (t : ℝ) / (z : ℝ))|)
          * (1 + |Real.log (2 * (((max (z / t) (z / r) : ℕ) : ℝ)) * (r : ℝ) / (z : ℝ))|))
        * (∑ d ∈ (r * t).divisors, (1 : ℝ) / Real.sqrt (d : ℝ)))
      ≤ ∑ r ∈ Finset.Icc 1 T, ∑ t ∈ Finset.Icc 1 T,
          4 * Real.sqrt (z : ℝ)
          * ((1 / Real.sqrt (r : ℝ)) * (1 + Real.log ((T : ℝ) / (r : ℝ)))
             + (1 / Real.sqrt (t : ℝ)) * (1 + Real.log ((T : ℝ) / (t : ℝ))))
          * ((∑ d ∈ r.divisors, (1 : ℝ) / Real.sqrt (d : ℝ))
              * (∑ d ∈ t.divisors, (1 : ℝ) / Real.sqrt (d : ℝ))) := by
    apply Finset.sum_le_sum
    intro r hr
    apply Finset.sum_le_sum
    intro t ht
    exact hpt r hr t ht
  have hkey : (∑ r ∈ Finset.Icc 1 T, ∑ t ∈ Finset.Icc 1 T,
          4 * Real.sqrt (z : ℝ)
          * ((1 / Real.sqrt (r : ℝ)) * (1 + Real.log ((T : ℝ) / (r : ℝ)))
             + (1 / Real.sqrt (t : ℝ)) * (1 + Real.log ((T : ℝ) / (t : ℝ))))
          * ((∑ d ∈ r.divisors, (1 : ℝ) / Real.sqrt (d : ℝ))
              * (∑ d ∈ t.divisors, (1 : ℝ) / Real.sqrt (d : ℝ))))
      = 4 * Real.sqrt (z : ℝ)
          * ((∑ r ∈ Finset.Icc 1 T, (1 / Real.sqrt (r : ℝ))
                * (1 + Real.log ((T : ℝ) / (r : ℝ)))
                * (∑ d ∈ r.divisors, (1 : ℝ) / Real.sqrt (d : ℝ)))
             * (∑ t ∈ Finset.Icc 1 T, (∑ d ∈ t.divisors, (1 : ℝ) / Real.sqrt (d : ℝ)))
            + (∑ r ∈ Finset.Icc 1 T, (∑ d ∈ r.divisors, (1 : ℝ) / Real.sqrt (d : ℝ)))
             * (∑ t ∈ Finset.Icc 1 T, (1 / Real.sqrt (t : ℝ))
                * (1 + Real.log ((T : ℝ) / (t : ℝ)))
                * (∑ d ∈ t.divisors, (1 : ℝ) / Real.sqrt (d : ℝ)))) := by
    have e : (∑ r ∈ Finset.Icc 1 T, ∑ t ∈ Finset.Icc 1 T,
          4 * Real.sqrt (z : ℝ)
          * ((1 / Real.sqrt (r : ℝ)) * (1 + Real.log ((T : ℝ) / (r : ℝ)))
             + (1 / Real.sqrt (t : ℝ)) * (1 + Real.log ((T : ℝ) / (t : ℝ))))
          * ((∑ d ∈ r.divisors, (1 : ℝ) / Real.sqrt (d : ℝ))
              * (∑ d ∈ t.divisors, (1 : ℝ) / Real.sqrt (d : ℝ))))
        = 4 * Real.sqrt (z : ℝ)
          * (∑ r ∈ Finset.Icc 1 T, ∑ t ∈ Finset.Icc 1 T,
              ( ((1 / Real.sqrt (r : ℝ)) * (1 + Real.log ((T : ℝ) / (r : ℝ)))
                 * (∑ d ∈ r.divisors, (1 : ℝ) / Real.sqrt (d : ℝ)))
                * (∑ d ∈ t.divisors, (1 : ℝ) / Real.sqrt (d : ℝ))
              + (∑ d ∈ r.divisors, (1 : ℝ) / Real.sqrt (d : ℝ))
                * ((1 / Real.sqrt (t : ℝ)) * (1 + Real.log ((T : ℝ) / (t : ℝ)))
                   * (∑ d ∈ t.divisors, (1 : ℝ) / Real.sqrt (d : ℝ))))) := by
      rw [Finset.mul_sum]
      apply Finset.sum_congr rfl; intro r hr
      rw [Finset.mul_sum]
      apply Finset.sum_congr rfl; intro t ht
      ring
    have hA1 : ∀ r : ℕ, (∑ t ∈ Finset.Icc 1 T, ( ((1 / Real.sqrt (r : ℝ)) * (1 + Real.log ((T : ℝ) / (r : ℝ))) * (∑ d ∈ r.divisors, (1 : ℝ) / Real.sqrt (d : ℝ))) * (∑ d ∈ t.divisors, (1 : ℝ) / Real.sqrt (d : ℝ)) + (∑ d ∈ r.divisors, (1 : ℝ) / Real.sqrt (d : ℝ)) * ((1 / Real.sqrt (t : ℝ)) * (1 + Real.log ((T : ℝ) / (t : ℝ))) * (∑ d ∈ t.divisors, (1 : ℝ) / Real.sqrt (d : ℝ))) ))
        = (∑ t ∈ Finset.Icc 1 T, ((1 / Real.sqrt (r : ℝ)) * (1 + Real.log ((T : ℝ) / (r : ℝ))) * (∑ d ∈ r.divisors, (1 : ℝ) / Real.sqrt (d : ℝ))) * (∑ d ∈ t.divisors, (1 : ℝ) / Real.sqrt (d : ℝ))) + (∑ t ∈ Finset.Icc 1 T, (∑ d ∈ r.divisors, (1 : ℝ) / Real.sqrt (d : ℝ)) * ((1 / Real.sqrt (t : ℝ)) * (1 + Real.log ((T : ℝ) / (t : ℝ))) * (∑ d ∈ t.divisors, (1 : ℝ) / Real.sqrt (d : ℝ)))) :=
      fun r => Finset.sum_add_distrib
    have hA11 : (∑ r ∈ Finset.Icc 1 T, ∑ t ∈ Finset.Icc 1 T, ( ((1 / Real.sqrt (r : ℝ)) * (1 + Real.log ((T : ℝ) / (r : ℝ))) * (∑ d ∈ r.divisors, (1 : ℝ) / Real.sqrt (d : ℝ))) * (∑ d ∈ t.divisors, (1 : ℝ) / Real.sqrt (d : ℝ)) + (∑ d ∈ r.divisors, (1 : ℝ) / Real.sqrt (d : ℝ)) * ((1 / Real.sqrt (t : ℝ)) * (1 + Real.log ((T : ℝ) / (t : ℝ))) * (∑ d ∈ t.divisors, (1 : ℝ) / Real.sqrt (d : ℝ))) ))
        = ∑ r ∈ Finset.Icc 1 T, ((∑ t ∈ Finset.Icc 1 T, ((1 / Real.sqrt (r : ℝ)) * (1 + Real.log ((T : ℝ) / (r : ℝ))) * (∑ d ∈ r.divisors, (1 : ℝ) / Real.sqrt (d : ℝ))) * (∑ d ∈ t.divisors, (1 : ℝ) / Real.sqrt (d : ℝ))) + (∑ t ∈ Finset.Icc 1 T, (∑ d ∈ r.divisors, (1 : ℝ) / Real.sqrt (d : ℝ)) * ((1 / Real.sqrt (t : ℝ)) * (1 + Real.log ((T : ℝ) / (t : ℝ))) * (∑ d ∈ t.divisors, (1 : ℝ) / Real.sqrt (d : ℝ))))) :=
      Finset.sum_congr rfl (fun r _ => hA1 r)
    have hA12 : (∑ r ∈ Finset.Icc 1 T, ((∑ t ∈ Finset.Icc 1 T, ((1 / Real.sqrt (r : ℝ)) * (1 + Real.log ((T : ℝ) / (r : ℝ))) * (∑ d ∈ r.divisors, (1 : ℝ) / Real.sqrt (d : ℝ))) * (∑ d ∈ t.divisors, (1 : ℝ) / Real.sqrt (d : ℝ))) + (∑ t ∈ Finset.Icc 1 T, (∑ d ∈ r.divisors, (1 : ℝ) / Real.sqrt (d : ℝ)) * ((1 / Real.sqrt (t : ℝ)) * (1 + Real.log ((T : ℝ) / (t : ℝ))) * (∑ d ∈ t.divisors, (1 : ℝ) / Real.sqrt (d : ℝ))))))
        = (∑ r ∈ Finset.Icc 1 T, ∑ t ∈ Finset.Icc 1 T, ((1 / Real.sqrt (r : ℝ)) * (1 + Real.log ((T : ℝ) / (r : ℝ))) * (∑ d ∈ r.divisors, (1 : ℝ) / Real.sqrt (d : ℝ))) * (∑ d ∈ t.divisors, (1 : ℝ) / Real.sqrt (d : ℝ)))
          + (∑ r ∈ Finset.Icc 1 T, ∑ t ∈ Finset.Icc 1 T, (∑ d ∈ r.divisors, (1 : ℝ) / Real.sqrt (d : ℝ)) * ((1 / Real.sqrt (t : ℝ)) * (1 + Real.log ((T : ℝ) / (t : ℝ))) * (∑ d ∈ t.divisors, (1 : ℝ) / Real.sqrt (d : ℝ)))) :=
      Finset.sum_add_distrib
    have hA13 : (∑ r ∈ Finset.Icc 1 T, ∑ t ∈ Finset.Icc 1 T, ((1 / Real.sqrt (r : ℝ)) * (1 + Real.log ((T : ℝ) / (r : ℝ))) * (∑ d ∈ r.divisors, (1 : ℝ) / Real.sqrt (d : ℝ))) * (∑ d ∈ t.divisors, (1 : ℝ) / Real.sqrt (d : ℝ)))
        = (∑ r ∈ Finset.Icc 1 T, (1 / Real.sqrt (r : ℝ)) * (1 + Real.log ((T : ℝ) / (r : ℝ))) * (∑ d ∈ r.divisors, (1 : ℝ) / Real.sqrt (d : ℝ))) * (∑ t ∈ Finset.Icc 1 T, (∑ d ∈ t.divisors, (1 : ℝ) / Real.sqrt (d : ℝ))) := by
      rw [Finset.sum_mul_sum]
    have hA14 : (∑ r ∈ Finset.Icc 1 T, ∑ t ∈ Finset.Icc 1 T, (∑ d ∈ r.divisors, (1 : ℝ) / Real.sqrt (d : ℝ)) * ((1 / Real.sqrt (t : ℝ)) * (1 + Real.log ((T : ℝ) / (t : ℝ))) * (∑ d ∈ t.divisors, (1 : ℝ) / Real.sqrt (d : ℝ))))
        = (∑ r ∈ Finset.Icc 1 T, (∑ d ∈ r.divisors, (1 : ℝ) / Real.sqrt (d : ℝ))) * (∑ t ∈ Finset.Icc 1 T, (1 / Real.sqrt (t : ℝ)) * (1 + Real.log ((T : ℝ) / (t : ℝ))) * (∑ d ∈ t.divisors, (1 : ℝ) / Real.sqrt (d : ℝ))) := by
      rw [Finset.sum_mul_sum]
    rw [e, hA11, hA12, hA13, hA14]
  have hA : (∑ r ∈ Finset.Icc 1 T, (1 / Real.sqrt (r : ℝ))
                * (1 + Real.log ((T : ℝ) / (r : ℝ)))
                * (∑ d ∈ r.divisors, (1 : ℝ) / Real.sqrt (d : ℝ))) ≤ Cp * Real.sqrt (T : ℝ) :=
    hCp T hT1
  have hA2 : (∑ r ∈ Finset.Icc 1 T, (1 / Real.sqrt (r : ℝ))
                * (1 + Real.log ((T : ℝ) / (r : ℝ)))
                * (∑ d ∈ r.divisors, (1 : ℝ) / Real.sqrt (d : ℝ))) ≤ Cp * Real.sqrt (T : ℝ) :=
    hCp T hT1
  have hBd : (∑ r ∈ Finset.Icc 1 T, (∑ d ∈ r.divisors, (1 : ℝ) / Real.sqrt (d : ℝ))) ≤ 4 * (T:ℝ) :=
    sum_sigma_half_le T
  have hBd2 : (∑ r ∈ Finset.Icc 1 T, (∑ d ∈ r.divisors, (1 : ℝ) / Real.sqrt (d : ℝ))) ≤ 4 * (T:ℝ) :=
    sum_sigma_half_le T
  have hAnn : (0:ℝ) ≤ ∑ r ∈ Finset.Icc 1 T, (1 / Real.sqrt (r : ℝ))
                * (1 + Real.log ((T : ℝ) / (r : ℝ)))
                * (∑ d ∈ r.divisors, (1 : ℝ) / Real.sqrt (d : ℝ)) := by
    apply Finset.sum_nonneg
    intro r hr
    obtain ⟨hr1, hrT⟩ := Finset.mem_Icc.mp hr
    have hl : (1:ℝ) ≤ (T:ℝ)/(r:ℝ) := by
      rw [one_le_div (by exact_mod_cast (by omega : 0 < r))]
      exact_mod_cast hrT
    have h3 : 0 ≤ Real.log ((T:ℝ)/(r:ℝ)) := Real.log_nonneg hl
    positivity
  have hBnn : (0:ℝ) ≤ ∑ r ∈ Finset.Icc 1 T, (∑ d ∈ r.divisors, (1 : ℝ) / Real.sqrt (d : ℝ)) :=
    Finset.sum_nonneg (fun d _ => Finset.sum_nonneg (fun e _ => by positivity))
  calc (∑ r ∈ Finset.Icc 1 T, ∑ t ∈ Finset.Icc 1 T,
      (Real.sqrt (((max (z / t) (z / r) : ℕ) : ℝ))
          * (1 + |Real.log (2 * (((max (z / t) (z / r) : ℕ) : ℝ)) * (t : ℝ) / (z : ℝ))|)
          * (1 + |Real.log (2 * (((max (z / t) (z / r) : ℕ) : ℝ)) * (r : ℝ) / (z : ℝ))|))
        * (∑ d ∈ (r * t).divisors, (1 : ℝ) / Real.sqrt (d : ℝ)))
      ≤ 4 * Real.sqrt (z : ℝ)
          * ((∑ r ∈ Finset.Icc 1 T, (1 / Real.sqrt (r : ℝ))
                * (1 + Real.log ((T : ℝ) / (r : ℝ)))
                * (∑ d ∈ r.divisors, (1 : ℝ) / Real.sqrt (d : ℝ)))
             * (∑ t ∈ Finset.Icc 1 T, (∑ d ∈ t.divisors, (1 : ℝ) / Real.sqrt (d : ℝ)))
            + (∑ r ∈ Finset.Icc 1 T, (∑ d ∈ r.divisors, (1 : ℝ) / Real.sqrt (d : ℝ)))
             * (∑ t ∈ Finset.Icc 1 T, (1 / Real.sqrt (t : ℝ))
                * (1 + Real.log ((T : ℝ) / (t : ℝ)))
                * (∑ d ∈ t.divisors, (1 : ℝ) / Real.sqrt (d : ℝ)))) := by
        rw [← hkey]; exact hstep
    _ ≤ 4 * Real.sqrt (z : ℝ)
          * ((Cp * Real.sqrt (T : ℝ)) * (4 * (T:ℝ)) + (4 * (T:ℝ)) * (Cp * Real.sqrt (T : ℝ))) := by
        apply mul_le_mul_of_nonneg_left _ (by positivity)
        apply add_le_add
        · exact mul_le_mul hA hBd hBnn (mul_nonneg (le_of_lt hCppos) (Real.sqrt_nonneg _))
        · exact mul_le_mul hBd2 hA2 hAnn (by positivity)
    _ = 32 * Cp * (Real.sqrt (z : ℝ) * ((T:ℝ) * Real.sqrt (T : ℝ))) := by ring

-- ======================= final assembly =======================

theorem sum_q_A (z N : ℕ) (hz : 2 ≤ z) (hzN : z ≤ N) (hNz : N < z * z) :
    (∑ q ∈ Finset.Icc 1 (N / z), Real.sqrt ((N : ℝ) / (q : ℝ)) * ((N / (q * z) : ℕ) : ℝ))
      ≤ 4 * (N : ℝ) := by
  have hNpos : (0:ℝ) < (N:ℝ) := by
    have : 0 < N := by omega
    exact_mod_cast this
  have hzpos : (0:ℝ) < (z:ℝ) := by
    have : 0 < z := by omega
    exact_mod_cast this
  have hsqrtNz : Real.sqrt (N:ℝ) ≤ (z:ℝ) := by
    have hzz : (N:ℝ) ≤ (z:ℝ)^2 := by
      have h : N ≤ z^2 := by simpa [pow_two] using (le_of_lt hNz)
      exact_mod_cast h
    calc Real.sqrt (N:ℝ) ≤ Real.sqrt ((z:ℝ)^2) := Real.sqrt_le_sqrt hzz
      _ = (z:ℝ) := Real.sqrt_sq (le_of_lt hzpos)
  have hterm : ∀ q ∈ Finset.Icc 1 (N / z),
      Real.sqrt ((N:ℝ)/(q:ℝ)) * ((N/(q*z):ℕ):ℝ)
      ≤ Real.sqrt (N:ℝ) * ((N:ℝ)/(z:ℝ)) * (1/((q:ℝ)*Real.sqrt (q:ℝ))) := by
    intro q hq
    obtain ⟨hq1, hqQ⟩ := Finset.mem_Icc.mp hq
    have hqpos : (0:ℝ) < (q:ℝ) := by exact_mod_cast (by omega : 0 < q)
    have hcast : ((N/(q*z):ℕ):ℝ) ≤ (N:ℝ)/((q:ℝ)*(z:ℝ)) := by
      have h : ((N/(q*z):ℕ):ℝ) ≤ (N:ℝ)/(((q*z : ℕ)):ℝ) := Nat.cast_div_le
      simpa using h
    have hid : Real.sqrt ((N:ℝ)/(q:ℝ)) * ((N:ℝ)/((q:ℝ)*(z:ℝ)))
        = Real.sqrt (N:ℝ) * ((N:ℝ)/(z:ℝ)) * (1/((q:ℝ)*Real.sqrt (q:ℝ))) := by
      rw [Real.sqrt_div (le_of_lt hNpos)]
      rw [show (1:ℝ)/((q:ℝ)*Real.sqrt (q:ℝ)) = (1/(q:ℝ))*(1/Real.sqrt (q:ℝ))
            by rw [← one_div_mul_one_div]]
      ring
    calc Real.sqrt ((N:ℝ)/(q:ℝ)) * ((N/(q*z):ℕ):ℝ)
        ≤ Real.sqrt ((N:ℝ)/(q:ℝ)) * ((N:ℝ)/((q:ℝ)*(z:ℝ))) :=
          mul_le_mul_of_nonneg_left hcast (Real.sqrt_nonneg _)
      _ = Real.sqrt (N:ℝ) * ((N:ℝ)/(z:ℝ)) * (1/((q:ℝ)*Real.sqrt (q:ℝ))) := hid
  calc (∑ q ∈ Finset.Icc 1 (N/z), Real.sqrt ((N:ℝ)/(q:ℝ)) * ((N/(q*z):ℕ):ℝ))
      ≤ ∑ q ∈ Finset.Icc 1 (N/z), Real.sqrt (N:ℝ) * ((N:ℝ)/(z:ℝ)) * (1/((q:ℝ)*Real.sqrt (q:ℝ))) :=
          Finset.sum_le_sum hterm
    _ = Real.sqrt (N:ℝ) * ((N:ℝ)/(z:ℝ)) * (∑ q ∈ Finset.Icc 1 (N/z), 1/((q:ℝ)*Real.sqrt (q:ℝ))) := by
          rw [Finset.mul_sum]
    _ ≤ Real.sqrt (N:ℝ) * ((N:ℝ)/(z:ℝ)) * 4 := by
          apply mul_le_mul_of_nonneg_left (sum_inv_sqrt_three_halves_le (N/z)) (by positivity)
    _ = 4 * (Real.sqrt (N:ℝ) * ((N:ℝ)/(z:ℝ))) := by ring
    _ ≤ 4 * (N:ℝ) := by
          apply mul_le_mul_of_nonneg_left _ (by norm_num)
          calc Real.sqrt (N:ℝ) * ((N:ℝ)/(z:ℝ)) = (N:ℝ) * (Real.sqrt (N:ℝ)/(z:ℝ)) := by ring
            _ ≤ (N:ℝ) * 1 := by
                apply mul_le_mul_of_nonneg_left _ (le_of_lt hNpos)
                rw [div_le_one hzpos]
                exact hsqrtNz
            _ = (N:ℝ) := by ring

theorem sum_q_B (z N : ℕ) (hz : 2 ≤ z) (hzN : z ≤ N) (hNz : N < z * z) :
    (∑ q ∈ Finset.Icc 1 (N / z), Real.sqrt (z : ℝ)
        * (((N / (q * z) : ℕ) : ℝ) * Real.sqrt (((N / (q * z) : ℕ) : ℝ)))) ≤ 4 * (N : ℝ) := by
  have hNpos : (0:ℝ) < (N:ℝ) := by
    have : 0 < N := by omega
    exact_mod_cast this
  have hzpos : (0:ℝ) < (z:ℝ) := by
    have : 0 < z := by omega
    exact_mod_cast this
  have hsqrtNz : Real.sqrt (N:ℝ) ≤ (z:ℝ) := by
    have hzz : (N:ℝ) ≤ (z:ℝ)^2 := by
      have h : N ≤ z^2 := by simpa [pow_two] using (le_of_lt hNz)
      exact_mod_cast h
    calc Real.sqrt (N:ℝ) ≤ Real.sqrt ((z:ℝ)^2) := Real.sqrt_le_sqrt hzz
      _ = (z:ℝ) := Real.sqrt_sq (le_of_lt hzpos)
  have hterm : ∀ q ∈ Finset.Icc 1 (N / z),
      Real.sqrt (z:ℝ) * (((N/(q*z):ℕ):ℝ) * Real.sqrt (((N/(q*z):ℕ):ℝ)))
      ≤ Real.sqrt (N:ℝ) * ((N:ℝ)/(z:ℝ)) * (1/((q:ℝ)*Real.sqrt (q:ℝ))) := by
    intro q hq
    obtain ⟨hq1, hqQ⟩ := Finset.mem_Icc.mp hq
    have hqpos : (0:ℝ) < (q:ℝ) := by exact_mod_cast (by omega : 0 < q)
    have hcast : ((N/(q*z):ℕ):ℝ) ≤ (N:ℝ)/((q:ℝ)*(z:ℝ)) := by
      have h : ((N/(q*z):ℕ):ℝ) ≤ (N:ℝ)/(((q*z : ℕ)):ℝ) := Nat.cast_div_le
      simpa using h
    have hsqle : Real.sqrt (((N/(q*z):ℕ):ℝ)) ≤ Real.sqrt ((N:ℝ)/((q:ℝ)*(z:ℝ))) :=
      Real.sqrt_le_sqrt hcast
    have hstep1 : ((N/(q*z):ℕ):ℝ) * Real.sqrt (((N/(q*z):ℕ):ℝ))
        ≤ ((N:ℝ)/((q:ℝ)*(z:ℝ))) * Real.sqrt ((N:ℝ)/((q:ℝ)*(z:ℝ))) :=
      mul_le_mul hcast hsqle (Real.sqrt_nonneg _) (by positivity)
    have hid : Real.sqrt (z:ℝ) * (((N:ℝ)/((q:ℝ)*(z:ℝ))) * Real.sqrt ((N:ℝ)/((q:ℝ)*(z:ℝ))))
        = Real.sqrt (N:ℝ) * ((N:ℝ)/(z:ℝ)) * (1/((q:ℝ)*Real.sqrt (q:ℝ))) := by
      rw [Real.sqrt_div (le_of_lt hNpos), Real.sqrt_mul (le_of_lt hqpos)]
      rw [show (1:ℝ)/((q:ℝ)*Real.sqrt (q:ℝ)) = (1/(q:ℝ))*(1/Real.sqrt (q:ℝ))
            by rw [← one_div_mul_one_div]]
      have hqne : (q:ℝ) ≠ 0 := ne_of_gt hqpos
      have hz0 : (z:ℝ) ≠ 0 := ne_of_gt hzpos
      have hsqne : Real.sqrt (q:ℝ) ≠ 0 := (Real.sqrt_pos_of_pos hqpos).ne'
      have hszne : Real.sqrt (z:ℝ) ≠ 0 := (Real.sqrt_pos_of_pos hzpos).ne'
      field_simp
    calc Real.sqrt (z:ℝ) * (((N/(q*z):ℕ):ℝ) * Real.sqrt (((N/(q*z):ℕ):ℝ)))
        ≤ Real.sqrt (z:ℝ) * (((N:ℝ)/((q:ℝ)*(z:ℝ))) * Real.sqrt ((N:ℝ)/((q:ℝ)*(z:ℝ)))) :=
          mul_le_mul_of_nonneg_left hstep1 (Real.sqrt_nonneg _)
      _ = Real.sqrt (N:ℝ) * ((N:ℝ)/(z:ℝ)) * (1/((q:ℝ)*Real.sqrt (q:ℝ))) := hid
  calc (∑ q ∈ Finset.Icc 1 (N/z), Real.sqrt (z:ℝ) * (((N/(q*z):ℕ):ℝ) * Real.sqrt (((N/(q*z):ℕ):ℝ))))
      ≤ ∑ q ∈ Finset.Icc 1 (N/z), Real.sqrt (N:ℝ) * ((N:ℝ)/(z:ℝ)) * (1/((q:ℝ)*Real.sqrt (q:ℝ))) :=
          Finset.sum_le_sum hterm
    _ = Real.sqrt (N:ℝ) * ((N:ℝ)/(z:ℝ)) * (∑ q ∈ Finset.Icc 1 (N/z), 1/((q:ℝ)*Real.sqrt (q:ℝ))) := by
          rw [Finset.mul_sum]
    _ ≤ Real.sqrt (N:ℝ) * ((N:ℝ)/(z:ℝ)) * 4 := by
          apply mul_le_mul_of_nonneg_left (sum_inv_sqrt_three_halves_le (N/z)) (by positivity)
    _ = 4 * (Real.sqrt (N:ℝ) * ((N:ℝ)/(z:ℝ))) := by ring
    _ ≤ 4 * (N:ℝ) := by
          apply mul_le_mul_of_nonneg_left _ (by norm_num)
          calc Real.sqrt (N:ℝ) * ((N:ℝ)/(z:ℝ)) = (N:ℝ) * (Real.sqrt (N:ℝ)/(z:ℝ)) := by ring
            _ ≤ (N:ℝ) * 1 := by
                apply mul_le_mul_of_nonneg_left _ (le_of_lt hNpos)
                rw [div_le_one hzpos]
                exact hsqrtNz
            _ = (N:ℝ) := by ring

theorem s3_hard_error_sum_bound : ∃ C : ℝ, 0 < C ∧ ∀ (z N : ℕ), 2 ≤ z → z ≤ N → N < z * z →
    (∑ q ∈ Finset.Icc 1 (N / z), ∑ r ∈ Finset.Icc 1 (N / (q * z)),
      ∑ t ∈ Finset.Icc 1 (N / (q * z)),
        (Real.sqrt (((N / (q * r * t) : ℕ) : ℝ))
            * (1 + |Real.log (2 * (((N / (q * r * t) : ℕ) : ℝ)) * (t : ℝ) / (z : ℝ))|)
            * (1 + |Real.log (2 * (((N / (q * r * t) : ℕ) : ℝ)) * (r : ℝ) / (z : ℝ))|)
          + Real.sqrt (((max (z / t) (z / r) : ℕ) : ℝ))
            * (1 + |Real.log (2 * (((max (z / t) (z / r) : ℕ) : ℝ)) * (t : ℝ) / (z : ℝ))|)
            * (1 + |Real.log (2 * (((max (z / t) (z / r) : ℕ) : ℝ)) * (r : ℝ) / (z : ℝ))|))
        * (∑ d ∈ (r * t).divisors, 1 / Real.sqrt (d : ℝ))) ≤ C * (N : ℝ) := by
  obtain ⟨CA, hCApos, hA⟩ := esbA_le
  obtain ⟨CB, hCBpos, hB⟩ := esbB_le
  refine ⟨4 * (CA + CB), by positivity, ?_⟩
  intro z N hz hzN hNz
  have hsplit : (∑ q ∈ Finset.Icc 1 (N / z), ∑ r ∈ Finset.Icc 1 (N / (q * z)),
      ∑ t ∈ Finset.Icc 1 (N / (q * z)),
        (Real.sqrt (((N / (q * r * t) : ℕ) : ℝ))
            * (1 + |Real.log (2 * (((N / (q * r * t) : ℕ) : ℝ)) * (t : ℝ) / (z : ℝ))|)
            * (1 + |Real.log (2 * (((N / (q * r * t) : ℕ) : ℝ)) * (r : ℝ) / (z : ℝ))|)
          + Real.sqrt (((max (z / t) (z / r) : ℕ) : ℝ))
            * (1 + |Real.log (2 * (((max (z / t) (z / r) : ℕ) : ℝ)) * (t : ℝ) / (z : ℝ))|)
            * (1 + |Real.log (2 * (((max (z / t) (z / r) : ℕ) : ℝ)) * (r : ℝ) / (z : ℝ))|))
        * (∑ d ∈ (r * t).divisors, 1 / Real.sqrt (d : ℝ)))
      = ∑ q ∈ Finset.Icc 1 (N / z),
          (Work.LinnikAreas.Density4.BzS3.esbA z N q + Work.LinnikAreas.Density4.BzS3.esbB z N q) := by
    apply Finset.sum_congr rfl
    intro q hq
    exact esbA_add_esbB z N q
  rw [hsplit]
  have hstep : ∑ q ∈ Finset.Icc 1 (N / z),
        (Work.LinnikAreas.Density4.BzS3.esbA z N q + Work.LinnikAreas.Density4.BzS3.esbB z N q)
      ≤ ∑ q ∈ Finset.Icc 1 (N / z),
          (CA * (Real.sqrt ((N : ℝ) / (q : ℝ)) * ((N / (q * z) : ℕ) : ℝ))
           + CB * (Real.sqrt (z : ℝ)
               * (((N / (q * z) : ℕ) : ℝ) * Real.sqrt (((N / (q * z) : ℕ) : ℝ))))) := by
    apply Finset.sum_le_sum
    intro q hq
    obtain ⟨hq1, hqQ⟩ := Finset.mem_Icc.mp hq
    have h1 := hA z N q hz hzN hNz hq1 hqQ
    have h2 := hB z N q hz hzN hNz hq1 hqQ
    linarith
  refine le_trans hstep ?_
  rw [Finset.sum_add_distrib, ← Finset.mul_sum, ← Finset.mul_sum]
  have hSA := sum_q_A z N hz hzN hNz
  have hSB := sum_q_B z N hz hzN hNz
  have e1 : CA * (∑ q ∈ Finset.Icc 1 (N / z),
        Real.sqrt ((N : ℝ) / (q : ℝ)) * ((N / (q * z) : ℕ) : ℝ)) ≤ CA * (4 * (N : ℝ)) :=
    mul_le_mul_of_nonneg_left hSA (le_of_lt hCApos)
  have e2 : CB * (∑ q ∈ Finset.Icc 1 (N / z), Real.sqrt (z : ℝ)
        * (((N / (q * z) : ℕ) : ℝ) * Real.sqrt (((N / (q * z) : ℕ) : ℝ)))) ≤ CB * (4 * (N : ℝ)) :=
    mul_le_mul_of_nonneg_left hSB (le_of_lt hCBpos)
  linarith

end

end Work.LinnikAreas2
