import Mathlib
import Submission.Work.LinnikAreas.JutilaPieces.S3PhiAsymptotic
import Submission.Work.LinnikAreas.JutilaPieces.S3HarmonicSum
import Submission.Work.LinnikAreas.JutilaPieces.S3RouteAux
import Submission.Work.LinnikAreas.JutilaPieces.S3RouteEstimates
import Submission.Work.ZeroDensity.Jutila.Bz3Defs

/-!
# The continuous `S₃` model equals `N·log(N/z) + O(N)`
-/

namespace Work.LinnikAreas2.S3Hard2

open Finset
open Work.LinnikAreas.JutilaPieces

noncomputable section

/-- `1 - x⁻¹ ≤ log x` for `x > 0`. -/
lemma one_sub_inv_le_log' {x : ℝ} (hx : 0 < x) : 1 - x⁻¹ ≤ Real.log x := by
  have h := Real.log_le_sub_one_of_pos (inv_pos.mpr hx)
  rw [Real.log_inv] at h
  linarith

/-- `1/(q+1) ≤ log((q+1)/q)` for `q ≥ 1`. -/
lemma inv_succ_le_log_ratio (q : ℕ) (hq : 1 ≤ q) :
    (1:ℝ)/((q:ℝ)+1) ≤ Real.log (((q:ℝ)+1)/(q:ℝ)) := by
  have hq0 : (0:ℝ) < (q:ℝ) := by exact_mod_cast (by omega : 0 < q)
  have hq1 : (0:ℝ) < (q:ℝ)+1 := by positivity
  have h1 : Real.log ((q:ℝ)/((q:ℝ)+1)) = - Real.log (((q:ℝ)+1)/(q:ℝ)) := by
    rw [Real.log_div hq0.ne' hq1.ne', Real.log_div hq1.ne' hq0.ne']
    ring
  have h2 : Real.log ((q:ℝ)/((q:ℝ)+1)) ≤ (q:ℝ)/((q:ℝ)+1) - 1 :=
    Real.log_le_sub_one_of_pos (by positivity)
  have h3 : (q:ℝ)/((q:ℝ)+1) - 1 = -(1/((q:ℝ)+1)) := by
    field_simp
    ring
  rw [h1, h3] at h2
  linarith

/-- **The `q`-error sum.**  `Σ_{q ≤ A, 2q ≤ A} (1/q)/log(A/q)² ≤ 30`. -/
lemma SumInvDivLogSq :
    ∃ C : ℝ, 0 < C ∧ ∀ A : ℕ, 1 ≤ A →
      (∑ q ∈ Finset.Icc 1 A,
          if 2 * q ≤ A then (1 / (q : ℝ)) / (Real.log ((A : ℝ) / (q : ℝ))) ^ 2 else 0) ≤ C := by
  have hlog2 : (0.69 : ℝ) ≤ Real.log 2 := by linarith [Real.log_two_gt_d9]
  refine ⟨30, by norm_num, ?_⟩
  intro A hA
  have hrewrite :
      (∑ q ∈ Finset.Icc 1 A,
          if 2 * q ≤ A then (1 / (q : ℝ)) / (Real.log ((A : ℝ) / (q : ℝ))) ^ 2 else 0)
        = ∑ q ∈ Finset.Icc 1 (A / 2), (1 / (q : ℝ)) / (Real.log ((A : ℝ) / (q : ℝ))) ^ 2 := by
    rw [← Finset.sum_filter]
    apply Finset.sum_congr _ (fun q _ => rfl)
    ext q
    simp only [Finset.mem_filter, Finset.mem_Icc]
    constructor
    · rintro ⟨⟨h1, _⟩, h2⟩
      exact ⟨h1, (Nat.le_div_iff_mul_le (by norm_num : 0 < 2)).mpr (by linarith : q * 2 ≤ A)⟩
    · rintro ⟨h1, h2⟩
      have h3 : 2 * q ≤ A := by
        have := (Nat.le_div_iff_mul_le (by norm_num : 0 < 2)).mp h2
        linarith
      exact ⟨⟨h1, le_trans h2 (Nat.div_le_self A 2)⟩, h3⟩
  rw [hrewrite]
  by_cases hA12 : A ≤ 12
  · -- few terms, each at most `3`
    have hterm : ∀ q ∈ Finset.Icc 1 (A / 2),
        (1 / (q : ℝ)) / (Real.log ((A : ℝ) / (q : ℝ))) ^ 2 ≤ 3 := by
      intro q hq
      have hq1 : 1 ≤ q := (Finset.mem_Icc.mp hq).1
      have hq2 : q ≤ A / 2 := (Finset.mem_Icc.mp hq).2
      have hqR : (0:ℝ) < (q:ℝ) := by exact_mod_cast (by omega : 0 < q)
      have hA2 : 2 * q ≤ A := by
        have := (Nat.le_div_iff_mul_le (by norm_num : 0 < 2)).mp hq2
        omega
      have hAq : (2:ℝ) ≤ (A:ℝ)/(q:ℝ) := by
        rw [le_div_iff₀ hqR]
        have : (2:ℝ) * (q:ℝ) ≤ (A:ℝ) := by exact_mod_cast hA2
        linarith
      have hlog : (0.69 : ℝ) ≤ Real.log ((A:ℝ)/(q:ℝ)) :=
        le_trans hlog2 (Real.log_le_log (by norm_num) hAq)
      have hpos : 0 < Real.log ((A:ℝ)/(q:ℝ)) := lt_of_lt_of_le (by norm_num) hlog
      have hq1R : (1:ℝ) ≤ (q:ℝ) := by exact_mod_cast hq1
      have h1 : (1:ℝ)/(q:ℝ) ≤ 1 := by
        rw [div_le_one hqR]; exact hq1R
      have h2 : (1:ℝ) ≤ 3 * (Real.log ((A:ℝ)/(q:ℝ)))^2 := by nlinarith [hlog]
      rw [div_le_iff₀ (by positivity)]
      linarith [h1, h2]
    calc (∑ q ∈ Finset.Icc 1 (A / 2), (1 / (q : ℝ)) / (Real.log ((A : ℝ) / (q : ℝ))) ^ 2)
        ≤ ∑ _q ∈ Finset.Icc 1 (A / 2), (3:ℝ) := Finset.sum_le_sum hterm
      _ = ((Finset.Icc 1 (A / 2)).card : ℝ) * 3 := by rw [Finset.sum_const, nsmul_eq_mul]
      _ ≤ 6 * 3 := by
          apply mul_le_mul_of_nonneg_right _ (by norm_num)
          have h : (Finset.Icc 1 (A/2)).card ≤ 6 := by
            rw [Nat.card_Icc]; omega
          exact_mod_cast h
      _ ≤ 30 := by norm_num
  · -- telescoping with `f q = 1/log(A/q)`
    have hA13 : 13 ≤ A := by omega
    set f : ℕ → ℝ := fun q => 1 / Real.log ((A:ℝ)/(q:ℝ)) with hf
    have hstep : ∀ q ∈ Finset.Icc 1 (A / 2),
        (1 / (q : ℝ)) / (Real.log ((A : ℝ) / (q : ℝ))) ^ 2 ≤ 2 * (f (q+1) - f q) := by
      intro q hq
      have hq1 : 1 ≤ q := (Finset.mem_Icc.mp hq).1
      have hq2 : q ≤ A / 2 := (Finset.mem_Icc.mp hq).2
      have hqR : (0:ℝ) < (q:ℝ) := by exact_mod_cast (by omega : 0 < q)
      have hq1R : (1:ℝ) ≤ (q:ℝ) := by exact_mod_cast hq1
      have hA2 : 2 * q ≤ A := by
        have := (Nat.le_div_iff_mul_le (by norm_num : 0 < 2)).mp hq2
        omega
      have hA2R : (2:ℝ) * (q:ℝ) ≤ (A:ℝ) := by exact_mod_cast hA2
      have hq2R : (q:ℝ) ≤ (A:ℝ)/2 := by linarith
      have hA13R : (13:ℝ) ≤ (A:ℝ) := by exact_mod_cast hA13
      set P := Real.log ((A:ℝ)/(q:ℝ)) with hPdef
      set Q := Real.log ((A:ℝ)/((q:ℝ)+1)) with hQdef
      have hPpos : 0 < P := by
        rw [hPdef]; apply Real.log_pos; rw [lt_div_iff₀ hqR]; linarith
      have hQpos : 0 < Q := by
        rw [hQdef]
        apply Real.log_pos
        rw [lt_div_iff₀ (by positivity : (0:ℝ) < (q:ℝ)+1)]
        have h3a : (q:ℝ) + 1 ≤ (A:ℝ)/2 + 1 := by linarith
        have h3b : (A:ℝ)/2 + 1 < (A:ℝ) := by linarith
        linarith
      have hQP : Q ≤ P := by
        rw [hPdef, hQdef]; apply Real.log_le_log (by positivity)
        rw [div_le_div_iff₀ (by positivity) (by positivity)]; nlinarith [hqR]
      have hdiff : 1/((q:ℝ)+1) ≤ P - Q := by
        have hsub : P - Q = Real.log (((q:ℝ)+1)/(q:ℝ)) := by
          rw [hPdef, hQdef, ← Real.log_div (by positivity) (by positivity)]
          congr 1
          field_simp
        rw [hsub]
        exact inv_succ_le_log_ratio q hq1
      have hkey : Q ≤ 2*(q:ℝ)*P*(P-Q) := by
        have h1 : (1:ℝ) ≤ 2*(q:ℝ)*(P-Q) := by
          have h3 : (1:ℝ) ≤ 2*(q:ℝ)*(1/((q:ℝ)+1)) := by
            rw [mul_one_div, le_div_iff₀ (by positivity)]
            linarith
          have h4 : 2*(q:ℝ)*(1/((q:ℝ)+1)) ≤ 2*(q:ℝ)*(P-Q) :=
            mul_le_mul_of_nonneg_left hdiff (by positivity)
          linarith
        have h5 : P * (1:ℝ) ≤ P * (2*(q:ℝ)*(P-Q)) := mul_le_mul_of_nonneg_left h1 hPpos.le
        calc Q ≤ P := hQP
          _ = P * 1 := by ring
          _ ≤ P * (2*(q:ℝ)*(P-Q)) := h5
          _ = 2*(q:ℝ)*P*(P-Q) := by ring
      have hgoal : 1/((q:ℝ)*P^2) ≤ 2*(P-Q)/(P*Q) := by
        rw [div_le_div_iff₀ (by positivity) (by positivity)]
        nlinarith [hkey, hPpos]
      have hconv1 : (1 / (q : ℝ)) / (Real.log ((A : ℝ) / (q : ℝ))) ^ 2 = 1/((q:ℝ)*P^2) := by
        rw [hPdef, div_div]
      have hconv2 : 2 * (f (q+1) - f q) = 2*(P-Q)/(P*Q) := by
        have h1 : f (q+1) = 1/Q := by
          rw [hf, hQdef]
          congr 1
          push_cast
          ring
        have h2 : f q = 1/P := by rw [hf, hPdef]
        rw [h1, h2, div_sub_div _ _ hQpos.ne' hPpos.ne']
        ring
      rw [hconv1, hconv2]
      exact hgoal
    have htel : ∀ M : ℕ, (∑ q ∈ Finset.Icc 1 M, (f (q+1) - f q)) = f (M+1) - f 1 := by
      intro M
      induction M with
      | zero => simp
      | succ N ih =>
          rw [Finset.sum_Icc_succ_top (by omega : 1 ≤ N + 1), ih]
          ring
    have hf1 : 0 ≤ f 1 := by
      rw [hf]
      apply div_nonneg one_pos.le
      apply Real.log_nonneg
      have h2 : (1:ℝ) ≤ (A:ℝ) := by exact_mod_cast (by omega : 1 ≤ A)
      simpa using h2
    have hfin : (∑ q ∈ Finset.Icc 1 (A / 2), (1 / (q : ℝ)) / (Real.log ((A : ℝ) / (q : ℝ))) ^ 2)
        ≤ 2 * f (A/2 + 1) := by
      calc (∑ q ∈ Finset.Icc 1 (A / 2), (1 / (q : ℝ)) / (Real.log ((A : ℝ) / (q : ℝ))) ^ 2)
          ≤ ∑ q ∈ Finset.Icc 1 (A / 2), 2 * (f (q+1) - f q) := Finset.sum_le_sum hstep
        _ = 2 * (f (A/2 + 1) - f 1) := by rw [← Finset.mul_sum, htel]
        _ ≤ 2 * f (A/2 + 1) := by
            have h2 : f (A/2+1) - f 1 ≤ f (A/2+1) := by linarith [hf1]
            linarith
    have hfbound : f (A/2 + 1) ≤ 3 := by
      have hcast : ((A/2:ℕ):ℝ) ≤ (A:ℝ)/2 := by
        have := Nat.cast_div_le (α := ℝ) (m := A) (n := 2)
        simpa using this
      have hA13R : (13:ℝ) ≤ (A:ℝ) := by exact_mod_cast hA13
      have hden : (0:ℝ) < ((A/2:ℕ):ℝ) + 1 := by positivity
      have hden' : ((A:ℝ)/↑(A / 2 + 1)) = (A:ℝ)/(((A/2:ℕ):ℝ)+1) := by push_cast; ring
      have hQpos : 0 < Real.log ((A:ℝ)/↑(A / 2 + 1)) := by
        rw [hden']
        apply Real.log_pos
        rw [lt_div_iff₀ hden]
        nlinarith [hcast, hA13R]
      have harg : Real.sqrt 2 ≤ (A:ℝ)/↑(A / 2 + 1) := by
        rw [hden', le_div_iff₀ hden]
        have hs : Real.sqrt 2 ≤ 1.42 := by
          rw [Real.sqrt_le_iff]; exact ⟨by norm_num, by norm_num⟩
        nlinarith [hs, hcast, hA13R]
      have hlog : Real.log (Real.sqrt 2) ≤ Real.log ((A:ℝ)/↑(A / 2 + 1)) :=
        Real.log_le_log (Real.sqrt_pos.mpr (by norm_num)) harg
      rw [Real.log_sqrt (by norm_num : (0:ℝ) ≤ 2)] at hlog
      have hlog2' : (2/3 : ℝ) ≤ Real.log 2 := by linarith [hlog2]
      rw [hf]
      simp only
      rw [div_le_iff₀ hQpos]
      linarith
    linarith [hfin, hfbound]

/-! ## The `q`-error sum and the model evaluation -/

/-- For the `q ≤ A` outside the asymptotic range `2q ≤ A`, the reciprocal sum is `≤ 2`. -/
lemma sum_compl_inv_le_two (A : ℕ) (hA : 1 ≤ A) :
    (∑ q ∈ (Finset.Icc 1 A).filter (fun q => ¬ 2 * q ≤ A), (1:ℝ)/(q:ℝ)) ≤ 2 := by
  have hpt : ∀ q ∈ (Finset.Icc 1 A).filter (fun q => ¬ 2 * q ≤ A),
      (1:ℝ)/(q:ℝ) ≤ (2:ℝ)/(A:ℝ) := by
    intro q hq
    rw [Finset.mem_filter, Finset.mem_Icc] at hq
    obtain ⟨⟨hq1, hqA⟩, hq2⟩ := hq
    have hq0 : (0:ℝ) < (q:ℝ) := by exact_mod_cast (by omega : 0 < q)
    have hA0 : (0:ℝ) < (A:ℝ) := by exact_mod_cast (by omega : 0 < A)
    have h2q : (A:ℝ) ≤ 2*(q:ℝ) := by
      have : A ≤ 2*q := by omega
      exact_mod_cast this
    rw [div_le_div_iff₀ hq0 hA0]
    linarith
  calc (∑ q ∈ (Finset.Icc 1 A).filter (fun q => ¬ 2 * q ≤ A), (1:ℝ)/(q:ℝ))
      ≤ (∑ q ∈ (Finset.Icc 1 A).filter (fun q => ¬ 2 * q ≤ A), (2:ℝ)/(A:ℝ)) :=
        Finset.sum_le_sum hpt
    _ = (((Finset.Icc 1 A).filter (fun q => ¬ 2 * q ≤ A)).card : ℝ) * ((2:ℝ)/(A:ℝ)) := by
        rw [Finset.sum_const, nsmul_eq_mul]
    _ ≤ (A:ℝ) * ((2:ℝ)/(A:ℝ)) := by
        apply mul_le_mul_of_nonneg_right _ (by positivity)
        have h : ((Finset.Icc 1 A).filter (fun q => ¬ 2 * q ≤ A)).card ≤ A := by
          calc ((Finset.Icc 1 A).filter (fun q => ¬ 2 * q ≤ A)).card ≤ (Finset.Icc 1 A).card :=
                Finset.card_filter_le _ _
            _ = A := by rw [Nat.card_Icc]; omega
        exact_mod_cast h
    _ = 2 := by
        have hA0 : (A:ℝ) ≠ 0 := by positivity
        field_simp

/-- **The `s3cont` model evaluation**: `s3cont z N = N·log(N/z) + O(N)`, `2 ≤ z ≤ N < z²`,
from `|Φ(x) − 1| ≤ C/log²x` (`S3PhiAsymptotic`, `S3PhiSmall`) and the harmonic sum
(`S3HarmonicSum`). -/
theorem s3cont_model : ∃ C : ℝ, 0 < C ∧ ∀ (z N : ℕ), 2 ≤ z → z ≤ N → N < z * z →
    |Work.ZeroDensity.Jutila.s3cont z N - (N : ℝ) * Real.log ((N : ℝ) / (z : ℝ))| ≤ C * (N : ℝ) := by
  obtain ⟨CΦ, hCΦ, hΦ⟩ := Work.LinnikAreas.JutilaPieces.S3PhiAsymptotic
  obtain ⟨Ch, hCh, hH⟩ := Work.LinnikAreas.JutilaPieces.S3HarmonicSum
  obtain ⟨Cl, hCl, hSum⟩ := SumInvDivLogSq
  refine ⟨Ch + Cl * CΦ + 2, by positivity, ?_⟩
  intro z N hz hzN hNz
  have hz0 : 0 < z := by omega
  have hNnn : (0:ℝ) ≤ (N:ℝ) := Nat.cast_nonneg N
  have hA1 : 1 ≤ N / z := (Nat.le_div_iff_mul_le hz0).mpr (by simpa using hzN)
  rw [Work.LinnikAreas.JutilaPieces.s3cont_eq_phi_sum z N hz0]
  have hkey : (∑ q ∈ Finset.Icc 1 (N / z), (N : ℝ) / (q : ℝ) * s3Phi ((N : ℝ) / ((q : ℝ) * (z : ℝ))))
        - (N : ℝ) * Real.log ((N : ℝ) / (z : ℝ))
      = (N : ℝ) * ((∑ q ∈ Finset.Icc 1 (N / z), (1 : ℝ) / (q : ℝ)) - Real.log ((N : ℝ) / (z : ℝ)))
        + ∑ q ∈ Finset.Icc 1 (N / z),
            (N : ℝ) / (q : ℝ) * (s3Phi ((N : ℝ) / ((q : ℝ) * (z : ℝ))) - 1) := by
    have h1 : (∑ q ∈ Finset.Icc 1 (N / z),
          (N : ℝ) / (q : ℝ) * (s3Phi ((N : ℝ) / ((q : ℝ) * (z : ℝ))) - 1))
        = (∑ q ∈ Finset.Icc 1 (N / z), (N : ℝ) / (q : ℝ) * s3Phi ((N : ℝ) / ((q : ℝ) * (z : ℝ))))
          - (N : ℝ) * (∑ q ∈ Finset.Icc 1 (N / z), (1 : ℝ) / (q : ℝ)) := by
      rw [Finset.mul_sum, ← Finset.sum_sub_distrib]
      apply Finset.sum_congr rfl
      intro q hq
      ring
    rw [h1]
    ring
  rw [hkey]
  have h1 : |(N : ℝ) * ((∑ q ∈ Finset.Icc 1 (N / z), (1 : ℝ) / (q : ℝ))
        - Real.log ((N : ℝ) / (z : ℝ)))| ≤ Ch * (N : ℝ) := by
    rw [abs_mul, abs_of_nonneg hNnn]
    have hh := hH N z hz hzN
    nlinarith [hh, hNnn]
  have h2 : |∑ q ∈ Finset.Icc 1 (N / z),
        (N : ℝ) / (q : ℝ) * (s3Phi ((N : ℝ) / ((q : ℝ) * (z : ℝ))) - 1)|
      ≤ (Cl * CΦ + 2) * (N : ℝ) := by
    have hpt : ∀ q ∈ Finset.Icc 1 (N / z),
        |(N : ℝ) / (q : ℝ) * (s3Phi ((N : ℝ) / ((q : ℝ) * (z : ℝ))) - 1)|
          ≤ (N : ℝ) * ((1 : ℝ) / (q : ℝ) *
              (if 2 * q ≤ N / z then CΦ / (Real.log (((N / z : ℕ) : ℝ) / (q : ℝ))) ^ 2 else 1)) := by
      intro q hq
      rw [Finset.mem_Icc] at hq
      obtain ⟨hq1, hqA⟩ := hq
      have hq0 : (0:ℝ) < (q:ℝ) := by exact_mod_cast (by omega : 0 < q)
      have hNq : (0:ℝ) ≤ (N : ℝ) / (q : ℝ) := by positivity
      rw [abs_mul, abs_of_nonneg hNq]
      have hxr : (N : ℝ) / ((q : ℝ) * (z : ℝ)) = ((N : ℝ) / (z : ℝ)) / (q : ℝ) := by
        rw [div_div]; ring_nf
      have hstep : |s3Phi ((N : ℝ) / ((q : ℝ) * (z : ℝ))) - 1|
          ≤ (if 2 * q ≤ N / z then CΦ / (Real.log (((N / z : ℕ) : ℝ) / (q : ℝ))) ^ 2 else 1) := by
        by_cases h2q : 2 * q ≤ N / z
        · rw [if_pos h2q]
          have hcast : (((N / z : ℕ)) : ℝ) ≤ (N : ℝ) / (z : ℝ) := Nat.cast_div_le
          have h2qR : (2:ℝ) * (q:ℝ) ≤ (((N / z : ℕ)) : ℝ) := by exact_mod_cast h2q
          have hx2 : (2:ℝ) ≤ (N : ℝ) / ((q : ℝ) * (z : ℝ)) := by
            rw [hxr, le_div_iff₀ hq0]; linarith
          have hlog : Real.log ((((N / z : ℕ)) : ℝ) / (q : ℝ))
              ≤ Real.log ((N : ℝ) / ((q : ℝ) * (z : ℝ))) := by
            apply Real.log_le_log (by positivity)
            rw [hxr]
            exact div_le_div_of_nonneg_right hcast hq0.le
          have hposA : 0 < Real.log ((((N / z : ℕ)) : ℝ) / (q : ℝ)) := by
            apply Real.log_pos
            rw [lt_div_iff₀ hq0]; linarith
          have hposx : 0 < Real.log ((N : ℝ) / ((q : ℝ) * (z : ℝ))) := lt_of_lt_of_le hposA hlog
          calc |s3Phi ((N : ℝ) / ((q : ℝ) * (z : ℝ))) - 1|
              ≤ CΦ / (Real.log ((N : ℝ) / ((q : ℝ) * (z : ℝ)))) ^ 2 := hΦ _ hx2
            _ ≤ CΦ / (Real.log ((((N / z : ℕ)) : ℝ) / (q : ℝ))) ^ 2 := by
                have hsq : Real.log ((((N / z : ℕ)) : ℝ) / (q : ℝ)) ^ 2
                    ≤ (Real.log ((N : ℝ) / ((q : ℝ) * (z : ℝ)))) ^ 2 := by nlinarith [hlog, hposA]
                have hinv : (1:ℝ) / (Real.log ((N : ℝ) / ((q : ℝ) * (z : ℝ)))) ^ 2
                    ≤ 1 / (Real.log ((((N / z : ℕ)) : ℝ) / (q : ℝ))) ^ 2 :=
                  one_div_le_one_div_of_le (by positivity) hsq
                calc CΦ / (Real.log ((N : ℝ) / ((q : ℝ) * (z : ℝ)))) ^ 2
                    = CΦ * (1 / (Real.log ((N : ℝ) / ((q : ℝ) * (z : ℝ)))) ^ 2) := by ring
                  _ ≤ CΦ * (1 / (Real.log ((((N / z : ℕ)) : ℝ) / (q : ℝ))) ^ 2) :=
                      mul_le_mul_of_nonneg_left hinv hCΦ.le
                  _ = CΦ / (Real.log ((((N / z : ℕ)) : ℝ) / (q : ℝ))) ^ 2 := by ring
        · rw [if_neg h2q]
          have hcast : (((N / z : ℕ)) : ℝ) ≤ (N : ℝ) / (z : ℝ) := Nat.cast_div_le
          have hqAr : (q:ℝ) ≤ (((N / z : ℕ)) : ℝ) := by exact_mod_cast hqA
          have hx1 : (1:ℝ) ≤ (N : ℝ) / ((q : ℝ) * (z : ℝ)) := by
            rw [hxr, le_div_iff₀ hq0]; linarith
          have hxlt2 : (N : ℝ) / ((q : ℝ) * (z : ℝ)) < 2 := by
            have hzR : (0:ℝ) < (z:ℝ) := by exact_mod_cast hz0
            have hlt : (N : ℝ) / (z : ℝ) < (((N / z : ℕ)) : ℝ) + 1 := by
              have h1 : N < (N / z + 1) * z := (Nat.div_lt_iff_lt_mul hz0).mp (Nat.lt_succ_self _)
              have h2 : (N:ℝ) < (((N / z + 1) * z : ℕ) : ℝ) := by exact_mod_cast h1
              push_cast at h2
              rw [div_lt_iff₀ hzR]
              linarith
            have h2q' : (((N / z : ℕ)) : ℝ) + 1 ≤ 2 * (q:ℝ) := by
              have : N / z + 1 ≤ 2 * q := by omega
              exact_mod_cast this
            rw [hxr, div_lt_iff₀ hq0]; linarith
          exact Work.LinnikAreas.JutilaPieces.S3PhiSmall _ hx1 hxlt2
      calc (N : ℝ) / (q : ℝ) * |s3Phi ((N : ℝ) / ((q : ℝ) * (z : ℝ))) - 1|
          ≤ (N : ℝ) / (q : ℝ) *
              (if 2 * q ≤ N / z then CΦ / (Real.log (((N / z : ℕ) : ℝ) / (q : ℝ))) ^ 2 else 1) :=
            mul_le_mul_of_nonneg_left hstep hNq
        _ = (N : ℝ) * ((1 : ℝ) / (q : ℝ) *
              (if 2 * q ≤ N / z then CΦ / (Real.log (((N / z : ℕ) : ℝ) / (q : ℝ))) ^ 2 else 1)) := by
            rw [div_eq_mul_inv]; ring
    calc |∑ q ∈ Finset.Icc 1 (N / z),
          (N : ℝ) / (q : ℝ) * (s3Phi ((N : ℝ) / ((q : ℝ) * (z : ℝ))) - 1)|
        ≤ ∑ q ∈ Finset.Icc 1 (N / z),
            |(N : ℝ) / (q : ℝ) * (s3Phi ((N : ℝ) / ((q : ℝ) * (z : ℝ))) - 1)| :=
          Finset.abs_sum_le_sum_abs _ _
      _ ≤ ∑ q ∈ Finset.Icc 1 (N / z), (N : ℝ) * ((1 : ℝ) / (q : ℝ) *
              (if 2 * q ≤ N / z then CΦ / (Real.log (((N / z : ℕ) : ℝ) / (q : ℝ))) ^ 2 else 1)) :=
          Finset.sum_le_sum hpt
      _ = (N : ℝ) * (∑ q ∈ Finset.Icc 1 (N / z), (1 : ℝ) / (q : ℝ) *
              (if 2 * q ≤ N / z then CΦ / (Real.log (((N / z : ℕ) : ℝ) / (q : ℝ))) ^ 2 else 1)) := by
          rw [Finset.mul_sum]
      _ ≤ (N : ℝ) * (Cl * CΦ + 2) := by
          apply mul_le_mul_of_nonneg_left _ hNnn
          have hsplit : (∑ q ∈ Finset.Icc 1 (N / z), (1 : ℝ) / (q : ℝ) *
                (if 2 * q ≤ N / z then CΦ / (Real.log (((N / z : ℕ) : ℝ) / (q : ℝ))) ^ 2 else 1))
              = (∑ q ∈ Finset.Icc 1 (N / z), (1 : ℝ) / (q : ℝ) *
                  (if 2 * q ≤ N / z then CΦ / (Real.log (((N / z : ℕ) : ℝ) / (q : ℝ))) ^ 2 else 0))
                + (∑ q ∈ Finset.Icc 1 (N / z), (1 : ℝ) / (q : ℝ) *
                    (if 2 * q ≤ N / z then 0 else 1)) := by
            rw [← Finset.sum_add_distrib]
            apply Finset.sum_congr rfl
            intro q hq
            by_cases hp : 2 * q ≤ N / z
            · simp [hp]
            · simp [hp]
          rw [hsplit]
          have hbig : (∑ q ∈ Finset.Icc 1 (N / z), (1 : ℝ) / (q : ℝ) *
                (if 2 * q ≤ N / z then CΦ / (Real.log (((N / z : ℕ) : ℝ) / (q : ℝ))) ^ 2 else 0))
              ≤ CΦ * Cl := by
            have hsum := hSum (N / z) hA1
            calc (∑ q ∈ Finset.Icc 1 (N / z), (1 : ℝ) / (q : ℝ) *
                  (if 2 * q ≤ N / z then CΦ / (Real.log (((N / z : ℕ) : ℝ) / (q : ℝ))) ^ 2 else 0))
                = CΦ * (∑ q ∈ Finset.Icc 1 (N / z),
                    if 2 * q ≤ N / z then (1 / (q : ℝ)) / (Real.log (((N / z : ℕ) : ℝ) / (q : ℝ))) ^ 2 else 0) := by
                  rw [Finset.mul_sum]
                  apply Finset.sum_congr rfl
                  intro q hq
                  by_cases hp : 2 * q ≤ N / z
                  · rw [if_pos hp, if_pos hp]; ring
                  · rw [if_neg hp, if_neg hp]; ring
              _ ≤ CΦ * Cl := mul_le_mul_of_nonneg_left hsum hCΦ.le
          have hsl : (∑ q ∈ Finset.Icc 1 (N / z), (1 : ℝ) / (q : ℝ) *
                (if 2 * q ≤ N / z then 0 else 1))
              ≤ 2 := by
            have hconv : (∑ q ∈ Finset.Icc 1 (N / z), (1 : ℝ) / (q : ℝ) *
                  (if 2 * q ≤ N / z then 0 else 1))
                = ∑ q ∈ (Finset.Icc 1 (N / z)).filter (fun q => ¬ 2 * q ≤ N / z), (1:ℝ)/(q:ℝ) := by
              rw [Finset.sum_filter]
              apply Finset.sum_congr rfl
              intro q hq
              by_cases hp : 2 * q ≤ N / z
              · simp [hp]
              · simp [hp]
            rw [hconv]
            exact sum_compl_inv_le_two (N / z) hA1
          linarith
      _ = (Cl * CΦ + 2) * (N : ℝ) := by ring
  calc |(N : ℝ) * ((∑ q ∈ Finset.Icc 1 (N / z), (1 : ℝ) / (q : ℝ))
          - Real.log ((N : ℝ) / (z : ℝ)))
        + ∑ q ∈ Finset.Icc 1 (N / z),
            (N : ℝ) / (q : ℝ) * (s3Phi ((N : ℝ) / ((q : ℝ) * (z : ℝ))) - 1)|
      ≤ |(N : ℝ) * ((∑ q ∈ Finset.Icc 1 (N / z), (1 : ℝ) / (q : ℝ))
            - Real.log ((N : ℝ) / (z : ℝ)))|
        + |∑ q ∈ Finset.Icc 1 (N / z),
            (N : ℝ) / (q : ℝ) * (s3Phi ((N : ℝ) / ((q : ℝ) * (z : ℝ))) - 1)| := abs_add_le _ _
    _ ≤ Ch * (N : ℝ) + (Cl * CΦ + 2) * (N : ℝ) := add_le_add h1 h2
    _ = (Ch + Cl * CΦ + 2) * (N : ℝ) := by ring

end

end Work.LinnikAreas2.S3Hard2
