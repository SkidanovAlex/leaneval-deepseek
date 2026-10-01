import Mathlib
import Submission.Commons.NumberTheory.DirichletCharacter.LSeries_partial_sums_tendsto
import Submission.Commons.NumberTheory.DirichletCharacter.polya_vinogradov
import Submission.Commons.Algebra.BigOperators.abel_window
import Submission.Commons.Analysis.Asymptotics.abel_tail_bound_finite
import Submission.Commons.Analysis.Real.log_pow_le_mul_rpow
import Submission.Commons.NumberTheory.DivisorBound.card_divisors_le_rpow

open scoped BigOperators
open Finset MeasureTheory intervalIntegral

set_option autoImplicit false

namespace Commons.NumberTheory.DirichletCharacter

lemma norm_natCast_cpow_eq (s : ℂ) {n : ℕ} (hn : 1 ≤ n) :
    ‖(n:ℂ)^(-s)‖ = (n:ℝ)^(-s.re) := by
  have hn0 : (0:ℝ) < (n:ℝ) := by exact_mod_cast (by omega : 0 < n)
  rw [show ((n:ℂ)) = (((n:ℝ)):ℂ) by push_cast; ring]
  rw [Complex.norm_cpow_eq_rpow_re_of_pos hn0]
  simp

lemma sum_Ioc_inv_le_log {Q M : ℕ} :
    ∑ i ∈ Finset.Ioc Q M, (i:ℝ)⁻¹ ≤ 1 + Real.log (M:ℝ) := by
  calc ∑ i ∈ Finset.Ioc Q M, (i:ℝ)⁻¹
      ≤ ∑ i ∈ Finset.Ioc 0 M, (i:ℝ)⁻¹ := by
        apply Finset.sum_le_sum_of_subset_of_nonneg
        · intro i hi; rw [Finset.mem_Ioc] at hi ⊢; omega
        · intro i hi _; positivity
    _ = ∑ i ∈ Finset.Icc 1 M, (i:ℝ)⁻¹ := by
        rw [show Finset.Ioc 0 M = Finset.Icc 1 M from by
          ext i; simp only [Finset.mem_Ioc, Finset.mem_Icc]; omega]
    _ = (harmonic M : ℝ) := by
        simp [harmonic_eq_sum_Icc, Rat.cast_sum]
    _ ≤ 1 + Real.log (M:ℝ) := harmonic_le_one_add_log M


lemma sum_Icc_one_rpow_le {Q : ℕ} (hQ : 1 ≤ Q) {μ : ℝ} (hμ : 0 ≤ μ) :
    ∑ n ∈ Finset.Icc 1 Q, (n:ℝ)^(μ-1) ≤ 1 + (Q:ℝ)^μ * (1 + Real.log (Q:ℝ)) := by
  have hmem : Finset.Icc 1 Q = insert 1 (Finset.Ioc 1 Q) := by
    ext n; simp only [Finset.mem_Icc, Finset.mem_insert, Finset.mem_Ioc]; omega
  have hnotin : (1:ℕ) ∉ Finset.Ioc 1 Q := by simp [Finset.mem_Ioc]
  rw [hmem, Finset.sum_insert hnotin]
  rw [show (((1:ℕ):ℝ)^(μ-1)) = 1 from by simp]
  have hstep : ∀ n ∈ Finset.Ioc 1 Q, (n:ℝ)^(μ-1) ≤ (Q:ℝ)^μ * (n:ℝ)⁻¹ := by
    intro n hn
    rw [Finset.mem_Ioc] at hn
    have hnQ : (n:ℝ) ≤ (Q:ℝ) := by exact_mod_cast hn.2
    have hnμ : (n:ℝ)^μ ≤ (Q:ℝ)^μ := Real.rpow_le_rpow (Nat.cast_nonneg n) hnQ hμ
    have hnpos : (0:ℝ) < (n:ℝ) := by exact_mod_cast (by omega : 0 < n)
    rw [show (n:ℝ)^(μ-1) = (n:ℝ)^μ * (n:ℝ)⁻¹ by
      rw [← Real.rpow_neg_one, ← Real.rpow_add hnpos]; ring_nf]
    exact mul_le_mul_of_nonneg_right hnμ (by positivity)
  calc 1 + ∑ n ∈ Finset.Ioc 1 Q, (n:ℝ)^(μ-1)
      ≤ 1 + ∑ n ∈ Finset.Ioc 1 Q, (Q:ℝ)^μ * (n:ℝ)⁻¹ := add_le_add le_rfl (Finset.sum_le_sum hstep)
    _ = 1 + (Q:ℝ)^μ * ∑ n ∈ Finset.Ioc 1 Q, (n:ℝ)⁻¹ := by rw [Finset.mul_sum]
    _ ≤ 1 + (Q:ℝ)^μ * (1 + Real.log (Q:ℝ)) := by
        apply add_le_add le_rfl
        exact mul_le_mul_of_nonneg_left sum_Ioc_inv_le_log (Real.rpow_nonneg (by positivity) _)

lemma sum_Ioc_split {Q R M : ℕ} (hQR : Q ≤ R) (hRM : R ≤ M) (f : ℕ → ℂ) :
    ∑ n ∈ Finset.Ioc Q M, f n = ∑ n ∈ Finset.Ioc Q R, f n + ∑ n ∈ Finset.Ioc R M, f n := by
  have hun : Finset.Ioc Q M = Finset.Ioc Q R ∪ Finset.Ioc R M := by
    ext n; simp only [Finset.mem_Ioc, Finset.mem_union]; omega
  have hdisj : Disjoint (Finset.Ioc Q R) (Finset.Ioc R M) := by
    rw [Finset.disjoint_left]; intro n h1 h2
    rw [Finset.mem_Ioc] at h1 h2; omega
  rw [hun, Finset.sum_union hdisj]

lemma sum_Icc_split {Q M : ℕ} (hQM : Q ≤ M) (f : ℕ → ℂ) :
    ∑ n ∈ Finset.Icc 1 M, f n = ∑ n ∈ Finset.Icc 1 Q, f n + ∑ n ∈ Finset.Ioc Q M, f n := by
  have hun : Finset.Icc 1 M = Finset.Icc 1 Q ∪ Finset.Ioc Q M := by
    ext n; simp only [Finset.mem_Icc, Finset.mem_union, Finset.mem_Ioc]; omega
  have hdisj : Disjoint (Finset.Icc 1 Q) (Finset.Ioc Q M) := by
    rw [Finset.disjoint_left]; intro n h1 h2
    rw [Finset.mem_Icc] at h1; rw [Finset.mem_Ioc] at h2; omega
  rw [hun, Finset.sum_union hdisj]

theorem abel_two_thirds_log_tail {a : ℕ → ℂ} {s : ℂ} (hs : 0 < s.re)
    {B : ℝ} (hB : ∀ x y : ℕ, x ≤ y → ‖∑ n ∈ Finset.Icc x y, a n‖ ≤ B)
    {N M : ℕ} (hN1 : 1 ≤ N) (hNM : N ≤ M) :
    ‖∑ k ∈ Finset.Icc N M, a k * (k:ℂ)^(-s)‖ ≤ B * (N:ℝ)^(-s.re) * (1 + ‖s‖/s.re) :=
  Commons.Analysis.Asymptotics.abel_tail_bound_finite B hB s hs hNM hN1

theorem abel_two_thirds_log {a : ℕ → ℂ} {A : ℝ} (hA : 0 ≤ A)
    {s : ℂ} (hσ0 : 0 < s.re) (hσ1 : (2:ℝ)/3 ≤ s.re)
    {Q M : ℕ} (hQ : 1 ≤ Q) (hQM : Q + 1 ≤ M)
    (hPre : ∀ m : ℕ, Q ≤ m → m ≤ M →
        ‖∑ k ∈ Finset.Icc 1 m, a k‖ ≤ A * (m:ℝ)^((2:ℝ)/3)) :
    ‖∑ k ∈ Finset.Icc (Q+1) M, a k * (k:ℂ)^(-s)‖
      ≤ A * (Q:ℝ)^((2:ℝ)/3 - s.re) * (2 + ‖s‖ * (1 + Real.log (M:ℝ))) := by
  set w : ℕ → ℂ := fun n => (n:ℂ)^(-s) with hw
  have hnw : ∀ n : ℕ, 1 ≤ n → ‖w n‖ = (n:ℝ)^(-s.re) := by
    intro n hn; rw [hw]; exact norm_natCast_cpow_eq s hn
  have hdiff : ∀ n : ℕ, 1 ≤ n → ‖w n - w (n+1)‖ ≤ ‖s‖ * (n:ℝ)^(-(s.re+1)) := by
    intro n hn; rw [hw]; exact norm_cpow_nat_sub_succ_cpow_le s hσ0 hn
  have hQpos : (0:ℝ) < (Q:ℝ) := by exact_mod_cast (by omega : 0 < Q)
  rw [Commons.Algebra.BigOperators.abel_window a w (by omega) hQM]
  have hMQ : (Q:ℝ) ≤ (M:ℝ) := by exact_mod_cast (by omega : Q ≤ M)
  -- term 1
  have hT1 : ‖(∑ m ∈ Finset.Icc 1 M, a m) * w M‖
      ≤ A * (Q:ℝ)^((2:ℝ)/3 - s.re) := by
    have h1 := hPre M (by omega) le_rfl
    rw [norm_mul, hnw M (by omega)]
    have hMpos : (0:ℝ) < (M:ℝ) := by exact_mod_cast (by omega : 0 < M)
    calc ‖∑ m ∈ Finset.Icc 1 M, a m‖ * (M:ℝ)^(-s.re)
        ≤ (A * (M:ℝ)^((2:ℝ)/3)) * (M:ℝ)^(-s.re) :=
          mul_le_mul_of_nonneg_right h1 (Real.rpow_nonneg (Nat.cast_nonneg M) _)
      _ = A * (M:ℝ)^((2:ℝ)/3 - s.re) := by
          rw [mul_assoc, ← Real.rpow_add hMpos]; simp only [sub_eq_add_neg]
      _ ≤ A * (Q:ℝ)^((2:ℝ)/3 - s.re) :=
          mul_le_mul_of_nonneg_left (Real.rpow_le_rpow_of_nonpos hQpos hMQ (by linarith)) hA
  -- term 2
  have hT2 : ‖(∑ m ∈ Finset.Icc 1 (Q+1-1), a m) * w (Q+1)‖
      ≤ A * (Q:ℝ)^((2:ℝ)/3 - s.re) := by
    rw [show (Q+1-1 : ℕ) = Q by omega, norm_mul, hnw (Q+1) (by omega)]
    have h1 := hPre Q le_rfl (by omega)
    have hstep : ((Q+1:ℕ):ℝ)^(-s.re) ≤ (Q:ℝ)^(-s.re) :=
      Real.rpow_le_rpow_of_nonpos hQpos (by exact_mod_cast (by omega : Q ≤ Q+1)) (by linarith)
    calc ‖∑ m ∈ Finset.Icc 1 Q, a m‖ * ((Q+1:ℕ):ℝ)^(-s.re)
        ≤ (A * (Q:ℝ)^((2:ℝ)/3)) * ((Q+1:ℕ):ℝ)^(-s.re) :=
          mul_le_mul_of_nonneg_right h1 (Real.rpow_nonneg (by positivity) _)
      _ ≤ (A * (Q:ℝ)^((2:ℝ)/3)) * (Q:ℝ)^(-s.re) :=
          mul_le_mul_of_nonneg_left hstep (by positivity)
      _ = A * (Q:ℝ)^((2:ℝ)/3 - s.re) := by
          rw [mul_assoc, ← Real.rpow_add hQpos]; simp only [sub_eq_add_neg]
  -- term 3
  have hT3 : ‖∑ n ∈ Finset.Icc (Q+1) (M-1),
        (∑ m ∈ Finset.Icc 1 n, a m) * (w n - w (n+1))‖
      ≤ A * ‖s‖ * (Q:ℝ)^((2:ℝ)/3 - s.re) * (1 + Real.log (M:ℝ)) := by
    calc ‖∑ n ∈ Finset.Icc (Q+1) (M-1),
            (∑ m ∈ Finset.Icc 1 n, a m) * (w n - w (n+1))‖
        ≤ ∑ n ∈ Finset.Icc (Q+1) (M-1),
            ‖(∑ m ∈ Finset.Icc 1 n, a m) * (w n - w (n+1))‖ := norm_sum_le _ _
      _ ≤ ∑ n ∈ Finset.Icc (Q+1) (M-1),
            (A * (n:ℝ)^((2:ℝ)/3)) * (‖s‖ * (n:ℝ)^(-(s.re+1))) := by
          apply Finset.sum_le_sum
          intro n hn
          rw [Finset.mem_Icc] at hn
          rw [norm_mul]
          exact mul_le_mul (hPre n (by omega) (by omega)) (hdiff n (by omega))
            (norm_nonneg _) (by positivity)
      _ = ∑ n ∈ Finset.Icc (Q+1) (M-1), A * ‖s‖ * (n:ℝ)^((2:ℝ)/3 - (s.re+1)) := by
          apply Finset.sum_congr rfl
          intro n hn
          rw [Finset.mem_Icc] at hn
          have hnpos : (0:ℝ) < (n:ℝ) := by exact_mod_cast (by omega : 0 < n)
          rw [show (A * (n:ℝ)^((2:ℝ)/3)) * (‖s‖ * (n:ℝ)^(-(s.re+1)))
              = A * ‖s‖ * ((n:ℝ)^((2:ℝ)/3) * (n:ℝ)^(-(s.re+1))) by ring,
            ← Real.rpow_add hnpos]
          simp only [sub_eq_add_neg, neg_add_rev]
      _ = ∑ n ∈ Finset.Ioc Q (M-1), A * ‖s‖ * (n:ℝ)^((2:ℝ)/3 - (s.re+1)) := by
          rw [show Finset.Icc (Q+1) (M-1) = Finset.Ioc Q (M-1) from by
            ext n; simp only [Finset.mem_Icc, Finset.mem_Ioc]; omega]
      _ ≤ A * ‖s‖ * (Q:ℝ)^((2:ℝ)/3 - s.re) * (1 + Real.log (M:ℝ)) := by
          have hsum_eq : ∑ n ∈ Finset.Ioc Q (M-1), A * ‖s‖ * (n:ℝ)^((2:ℝ)/3 - (s.re+1))
              = A * ‖s‖ * (∑ n ∈ Finset.Ioc Q (M-1), (n:ℝ)^((2:ℝ)/3 - s.re - 1)) := by
            rw [Finset.mul_sum]
            apply Finset.sum_congr rfl; intro n hn
            rw [show (2:ℝ)/3 - (s.re+1) = (2:ℝ)/3 - s.re - 1 by ring]
          rw [hsum_eq]
          have hsplit : ∑ n ∈ Finset.Ioc Q (M-1), (n:ℝ)^((2:ℝ)/3 - s.re - 1)
              ≤ ∑ n ∈ Finset.Ioc Q (M-1), (Q:ℝ)^((2:ℝ)/3 - s.re) * (n:ℝ)⁻¹ := by
            apply Finset.sum_le_sum
            intro n hn
            rw [Finset.mem_Ioc] at hn
            have hnpos : (0:ℝ) < (n:ℝ) := by exact_mod_cast (by omega : 0 < n)
            have hle : (n:ℝ)^((2:ℝ)/3 - s.re) ≤ (Q:ℝ)^((2:ℝ)/3 - s.re) :=
              Real.rpow_le_rpow_of_nonpos hQpos (by exact_mod_cast (by omega : Q ≤ n)) (by linarith)
            rw [show (n:ℝ)^((2:ℝ)/3 - s.re - 1) = (n:ℝ)^((2:ℝ)/3 - s.re) * (n:ℝ)⁻¹ by
              rw [← Real.rpow_neg_one]; rw [← Real.rpow_add hnpos]; ring_nf]
            exact mul_le_mul_of_nonneg_right hle (by positivity)
          have hsum_inv : ∑ n ∈ Finset.Ioc Q (M-1), (n:ℝ)⁻¹ ≤ 1 + Real.log (M:ℝ) := by
            refine (sum_Ioc_inv_le_log (Q := Q) (M := M-1)).trans ?_
            have hle : Real.log ((M-1:ℕ):ℝ) ≤ Real.log (M:ℝ) :=
              Real.log_le_log (by exact_mod_cast (by omega : 0 < M - 1))
                (by exact_mod_cast (by omega : M - 1 ≤ M))
            exact add_le_add le_rfl hle
          calc A * ‖s‖ * (∑ n ∈ Finset.Ioc Q (M-1), (n:ℝ)^((2:ℝ)/3 - s.re - 1))
              ≤ A * ‖s‖ * ((Q:ℝ)^((2:ℝ)/3 - s.re) * (1 + Real.log (M:ℝ))) := by
                apply mul_le_mul_of_nonneg_left _ (by positivity)
                calc ∑ n ∈ Finset.Ioc Q (M-1), (n:ℝ)^((2:ℝ)/3 - s.re - 1)
                    ≤ ∑ n ∈ Finset.Ioc Q (M-1), (Q:ℝ)^((2:ℝ)/3 - s.re) * (n:ℝ)⁻¹ := hsplit
                  _ = (Q:ℝ)^((2:ℝ)/3 - s.re) * ∑ n ∈ Finset.Ioc Q (M-1), (n:ℝ)⁻¹ := by
                      rw [Finset.mul_sum]
                  _ ≤ (Q:ℝ)^((2:ℝ)/3 - s.re) * (1 + Real.log (M:ℝ)) :=
                      mul_le_mul_of_nonneg_left hsum_inv (Real.rpow_nonneg (le_of_lt hQpos) _)
            _ = A * ‖s‖ * (Q:ℝ)^((2:ℝ)/3 - s.re) * (1 + Real.log (M:ℝ)) := by ring
  have hfin : (A * (Q:ℝ)^((2:ℝ)/3 - s.re)
        + A * ‖s‖ * (Q:ℝ)^((2:ℝ)/3 - s.re) * (1 + Real.log (M:ℝ)))
        + A * (Q:ℝ)^((2:ℝ)/3 - s.re)
      = A * (Q:ℝ)^((2:ℝ)/3 - s.re) * (2 + ‖s‖ * (1 + Real.log (M:ℝ))) := by ring
  calc ‖(∑ m ∈ Finset.Icc 1 M, a m) * w M
          + (∑ n ∈ Finset.Icc (Q+1) (M-1), (∑ m ∈ Finset.Icc 1 n, a m) * (w n - w (n+1)))
          - (∑ m ∈ Finset.Icc 1 (Q+1-1), a m) * w (Q+1)‖
      ≤ ‖(∑ m ∈ Finset.Icc 1 M, a m) * w M
          + (∑ n ∈ Finset.Icc (Q+1) (M-1), (∑ m ∈ Finset.Icc 1 n, a m) * (w n - w (n+1)))‖
        + ‖(∑ m ∈ Finset.Icc 1 (Q+1-1), a m) * w (Q+1)‖ := norm_sub_le _ _
    _ ≤ (‖(∑ m ∈ Finset.Icc 1 M, a m) * w M‖
          + ‖∑ n ∈ Finset.Icc (Q+1) (M-1),
              (∑ m ∈ Finset.Icc 1 n, a m) * (w n - w (n+1))‖)
        + ‖(∑ m ∈ Finset.Icc 1 (Q+1-1), a m) * w (Q+1)‖ :=
          add_le_add (norm_add_le _ _) le_rfl
    _ ≤ (A * (Q:ℝ)^((2:ℝ)/3 - s.re)
          + A * ‖s‖ * (Q:ℝ)^((2:ℝ)/3 - s.re) * (1 + Real.log (M:ℝ)))
        + A * (Q:ℝ)^((2:ℝ)/3 - s.re) :=
          add_le_add (add_le_add hT1 hT3) hT2
    _ = A * (Q:ℝ)^((2:ℝ)/3 - s.re) * (2 + ‖s‖ * (1 + Real.log (M:ℝ))) := hfin

end Commons.NumberTheory.DirichletCharacter

namespace Commons.NumberTheory.DirichletCharacter

set_option maxHeartbeats 4000000

theorem primitive_LFunction_bound (k : ℕ) (hk : 3 ≤ k)
    {ε δ : ℝ} (hε : 0 < ε) (hδ : 0 < δ) (hδε : δ ≤ ε/2) (hδk : δ ≤ 1/(48*(k:ℝ)))
    {CB : ℝ} (hCB : 0 < CB) :
    ∃ C : ℝ, 0 < C ∧ ∀ (q : ℕ) [NeZero q] (χ : DirichletCharacter ℂ q),
        χ.IsPrimitive → χ ≠ 1 →
        (∀ {N H : ℕ}, 1 ≤ N → 1 ≤ H → H ≤ q →
          ‖∑ n ∈ Finset.Ioc N (N + H), χ n‖ ≤ CB * (q:ℝ)^((1:ℝ)/9+ε) * (H:ℝ)^((2:ℝ)/3)) →
        ∀ σ t : ℝ, 1 - 1/(k:ℝ) ≤ σ → σ ≤ 1 →
          ‖DirichletCharacter.LFunction χ ((σ:ℂ)+(t:ℂ)*Complex.I)‖
            ≤ C * (q:ℝ)^(((1:ℝ)/3)*(1-σ)*(1+1/(k:ℝ)) + ε - δ) * (1 + |t|) := by
  have hkR : (3:ℝ) ≤ (k:ℝ) := by exact_mod_cast hk
  have hkpos : (0:ℝ) < (k:ℝ) := by linarith
  obtain ⟨Clog, hClogpos, hClog⟩ :=
    Commons.Analysis.Real.log_pow_le_mul_rpow (show (0:ℝ) < ε/2 by positivity) 1
  obtain ⟨Clog2, hClog2pos, hClog2⟩ :=
    Commons.Analysis.Real.log_pow_le_mul_rpow (show (0:ℝ) < 1/(48*(k:ℝ)) by positivity) 1
  obtain ⟨CPV, hCPVpos, hCPV⟩ := Commons.NumberTheory.DirichletCharacter.polya_vinogradov
  have hC1pos : (0:ℝ) < 1 + Clog := by linarith
  have hC2pos : (0:ℝ) < 1 + Clog2 := by linarith
  have hCpos : (0:ℝ) < 3 * (3*(1+Clog) + 4*(1+Clog2)*(CB+1) + 14*CPV*(1+Clog2)) + 1 := by
    have h1 : (0:ℝ) < 1 + Clog := by linarith
    have h2 : (0:ℝ) < 1 + Clog2 := by linarith
    have h3 : (0:ℝ) < CB + 1 := by linarith
    positivity
  refine ⟨3 * (3*(1+Clog) + 4*(1+Clog2)*(CB+1) + 14*CPV*(1+Clog2)) + 1, hCpos, ?_⟩
  intro q _inst χ hprim hχ hB σ t hσ1 hσle
  have hq2 : 2 ≤ q := by
    by_contra h
    rcases (by omega : q = 0 ∨ q = 1) with h0 | h1
    · exact NeZero.ne q h0
    · exact hχ (DirichletCharacter.level_one' (χ := χ) h1)
  set θ : ℝ := (1:ℝ)/3 + 1/(4*(k:ℝ)) with hθdef
  have hθpos : 0 < θ := by rw [hθdef]; positivity
  have hθle : θ ≤ 5/12 := by
    have h4k : (12:ℝ) ≤ 4*(k:ℝ) := by linarith [hkR]
    have h : 1/(4*(k:ℝ)) ≤ 1/12 := one_div_le_one_div_of_le (by norm_num : (0:ℝ) < 12) h4k
    rw [hθdef]; linarith
  have hθlt1 : θ ≤ 1 := by linarith
  set μ : ℝ := 1 - σ with hμdef
  have hμ0 : 0 ≤ μ := by rw [hμdef]; linarith
  have h1k : 1/(k:ℝ) ≤ 1/3 := one_div_le_one_div_of_le (by norm_num : (0:ℝ) < 3) hkR
  have hμ13 : μ ≤ 1/3 := by rw [hμdef]; linarith
  set Q : ℕ := Nat.ceil ((q:ℝ)^θ) with hQdef
  have hqR1 : (1:ℝ) ≤ (q:ℝ) := by exact_mod_cast (by omega : 1 ≤ q)
  have hqRpos : (0:ℝ) < (q:ℝ) := lt_of_lt_of_le one_pos hqR1
  have hQge : (q:ℝ)^θ ≤ (Q:ℝ) := Nat.le_ceil _
  have hqpow1 : (1:ℝ) ≤ (q:ℝ)^θ := Real.one_le_rpow hqR1 (le_of_lt hθpos)
  have hQ1 : 1 ≤ Q := by
    have : (1:ℝ) ≤ (Q:ℝ) := le_trans hqpow1 hQge
    exact_mod_cast this
  have hQq : Q ≤ q := by
    rw [hQdef]
    refine Nat.ceil_le.mpr ?_
    have := Real.rpow_le_rpow_of_exponent_le hqR1 hθlt1
    rwa [Real.rpow_one] at this
  have hQle : (Q:ℝ) ≤ 2*(q:ℝ)^θ := by
    have h := Nat.ceil_lt_add_one (le_of_lt (Real.rpow_pos_of_pos hqRpos θ))
    linarith [h, hqpow1]
  -- prefix bound
  set A : ℝ := (CB+1) * (q:ℝ)^((1:ℝ)/9+ε) with hAdef
  have hApos : 0 < A := by rw [hAdef]; positivity
  have hPre : ∀ m : ℕ, 1 ≤ m → m ≤ q →
      ‖∑ n ∈ Finset.Icc 1 m, χ n‖ ≤ A * (m:ℝ)^((2:ℝ)/3) := by
    intro m hm1 hmq
    rcases Nat.lt_or_ge 1 m with hm2 | hm2
    · have hmem : Finset.Icc 1 m = insert 1 (Finset.Ioc 1 m) := by
        ext n; simp only [Finset.mem_Icc, Finset.mem_insert, Finset.mem_Ioc]; omega
      have hnotin : (1:ℕ) ∉ Finset.Ioc 1 m := by simp [Finset.mem_Ioc]
      rw [hmem, Finset.sum_insert hnotin]
      have hb := hB (N:=1) (H:=m-1) le_rfl (by omega) (by omega)
      rw [show (1:ℕ)+(m-1) = m by omega] at hb
      have hmR : (1:ℝ) ≤ (m:ℝ) := by exact_mod_cast hm1
      have hm23 : (1:ℝ) ≤ (m:ℝ)^((2:ℝ)/3) := Real.one_le_rpow hmR (by norm_num)
      have hχ1 : ‖χ ((1:ℕ):ZMod q)‖ ≤ 1 := DirichletCharacter.norm_le_one χ _
      have hA1 : (1:ℝ) ≤ (q:ℝ)^((1:ℝ)/9+ε) * (m:ℝ)^((2:ℝ)/3) := by
        have h1 : (1:ℝ) ≤ (q:ℝ)^((1:ℝ)/9+ε) := Real.one_le_rpow hqR1 (by positivity)
        have := mul_le_mul h1 hm23 (by norm_num) (Real.rpow_nonneg (le_of_lt hqRpos) _)
        simpa using this
      have hfin : 1 + CB * (q:ℝ)^((1:ℝ)/9+ε) * (m:ℝ)^((2:ℝ)/3) ≤ A * (m:ℝ)^((2:ℝ)/3) := by
        rw [hAdef]
        have hqnn : (0:ℝ) ≤ (q:ℝ)^((1:ℝ)/9+ε) := Real.rpow_nonneg (le_of_lt hqRpos) _
        nlinarith [hA1, hqnn, Real.rpow_nonneg (by positivity : (0:ℝ) ≤ (m:ℝ)) ((2:ℝ)/3), hCB.le]
      calc ‖χ ((1:ℕ):ZMod q) + ∑ n ∈ Finset.Ioc 1 m, χ n‖
          ≤ 1 + CB * (q:ℝ)^(1/9+ε) * ((m-1:ℕ):ℝ)^((2:ℝ)/3) := by
            refine (norm_add_le _ _).trans ?_
            exact add_le_add hχ1 hb
        _ ≤ 1 + CB * (q:ℝ)^((1:ℝ)/9+ε) * (m:ℝ)^((2:ℝ)/3) := by
            have hHm : ((m-1:ℕ):ℝ)^((2:ℝ)/3) ≤ (m:ℝ)^((2:ℝ)/3) :=
              Real.rpow_le_rpow (by positivity) (by exact_mod_cast (by omega : m-1 ≤ m)) (by norm_num)
            have hh := mul_le_mul_of_nonneg_left hHm (by positivity : (0:ℝ) ≤ CB * (q:ℝ)^((1:ℝ)/9+ε))
            linarith [hh]
        _ ≤ A * (m:ℝ)^((2:ℝ)/3) := hfin
    · have hm1' : m = 1 := by omega
      subst hm1'
      have hmem : Finset.Icc 1 1 = {1} := by ext n; simp only [Finset.mem_Icc, Finset.mem_singleton]; omega
      rw [hmem, Finset.sum_singleton]
      have hχ1 : ‖χ ((1:ℕ):ZMod q)‖ ≤ 1 := DirichletCharacter.norm_le_one χ _
      refine hχ1.trans ?_
      rw [show (((1:ℕ):ℝ))^((2:ℝ)/3) = 1 by simp]
      rw [mul_one, hAdef]
      have h1 : (1:ℝ) ≤ (q:ℝ)^((1:ℝ)/9+ε) := Real.one_le_rpow hqR1 (by positivity)
      have h2 : (1:ℝ) ≤ CB + 1 := by linarith
      nlinarith [h1, h2, mul_le_mul h1 (le_refl (1:ℝ)) (by norm_num) (Real.rpow_nonneg (le_of_lt hqRpos) _)]
  -- s
  set s : ℂ := (σ:ℂ) + (t:ℂ)*Complex.I with hsdef
  have hsre : s.re = σ := by simp [hsdef]
  have hs0 : 0 < s.re := by rw [hsre]; linarith
  have hsnorm : ‖s‖ ≤ 2 + |t| := by
    have h := Complex.norm_le_abs_re_add_abs_im s
    rw [hsre] at h
    have h1 : |s.im| = |t| := by simp [hsdef]
    have h2 : |σ| ≤ 1 := by rw [abs_of_nonneg (by linarith)]; exact hσle
    rw [h1] at h; linarith
  -- head
  have hQpow : (Q:ℝ)^μ ≤ 2*(q:ℝ)^(θ*μ) := by
    have h1 : (Q:ℝ)^μ ≤ (2*(q:ℝ)^θ)^μ := Real.rpow_le_rpow (by positivity) hQle hμ0
    have h2 : (2*(q:ℝ)^θ)^μ = 2^μ * (q:ℝ)^(θ*μ) := by
      rw [Real.mul_rpow (by norm_num) (by positivity), ← Real.rpow_mul (le_of_lt hqRpos)]
    have h3 : (2:ℝ)^μ ≤ 2 := by
      have := Real.rpow_le_rpow_of_exponent_le (show (1:ℝ) ≤ 2 by norm_num) (show μ ≤ 1 by linarith)
      simpa using this
    rw [h2] at h1
    exact h1.trans (mul_le_mul_of_nonneg_right h3 (Real.rpow_nonneg (by positivity) _))
  have hQlog : 1 + Real.log (Q:ℝ) ≤ (1+Clog) * (q:ℝ)^(ε/2) := by
    have h1 : Real.log (Q:ℝ) ≤ Clog * (Q:ℝ)^(ε/2) := by
      simpa using hClog (Q:ℝ) (by exact_mod_cast hQ1)
    have h2 : (Q:ℝ)^(ε/2) ≤ (q:ℝ)^(ε/2) := Real.rpow_le_rpow (by positivity) (by exact_mod_cast hQq) (by positivity)
    have h3 : (1:ℝ) ≤ (q:ℝ)^(ε/2) := Real.one_le_rpow hqR1 (by positivity)
    have h4 : Real.log (Q:ℝ) ≤ Clog * (q:ℝ)^(ε/2) :=
      le_trans h1 (mul_le_mul_of_nonneg_left h2 (le_of_lt hClogpos))
    nlinarith [h3, h4]
  have hhead : ∑ n ∈ Finset.Icc 1 Q, (n:ℝ)^(-σ) ≤ (3+2*Clog) * (q:ℝ)^(θ*μ + ε/2) := by
    have h1 := sum_Icc_one_rpow_le hQ1 hμ0
    have hQμ1 : (1:ℝ) ≤ (Q:ℝ)^μ := Real.one_le_rpow (by exact_mod_cast hQ1) hμ0
    have hqexp : (1:ℝ) ≤ (q:ℝ)^(θ*μ + ε/2) := Real.one_le_rpow hqR1 (by positivity)
    have hpw : (q:ℝ)^(θ*μ) * (q:ℝ)^(ε/2) = (q:ℝ)^(θ*μ+ε/2) := (Real.rpow_add hqRpos _ _).symm
    calc ∑ n ∈ Finset.Icc 1 Q, (n:ℝ)^(-σ)
        = ∑ n ∈ Finset.Icc 1 Q, (n:ℝ)^(μ-1) := by
          apply Finset.sum_congr rfl; intro n hn; congr 1; rw [hμdef]; ring
      _ ≤ 1 + (Q:ℝ)^μ * (1 + Real.log (Q:ℝ)) := h1
      _ ≤ 1 + (2*(q:ℝ)^(θ*μ)) * ((1+Clog) * (q:ℝ)^(ε/2)) := by
          apply add_le_add le_rfl
          exact mul_le_mul hQpow hQlog (by positivity) (by positivity)
      _ = 1 + 2*(1+Clog) * ((q:ℝ)^(θ*μ) * (q:ℝ)^(ε/2)) := by ring
      _ = 1 + 2*(1+Clog) * (q:ℝ)^(θ*μ+ε/2) := by rw [hpw]
      _ ≤ (3+2*Clog) * (q:ℝ)^(θ*μ + ε/2) := by
          have hqnn : (0:ℝ) ≤ (q:ℝ)^(θ*μ+ε/2) := Real.rpow_nonneg (le_of_lt hqRpos) _
          have hClognn : (0:ℝ) ≤ Clog := le_of_lt hClogpos
          nlinarith [hqexp, hqnn, hClognn, mul_le_mul_of_nonneg_left hqexp hClognn]
  -- Chead
  have hhead2 : ∑ n ∈ Finset.Icc 1 Q, (n:ℝ)^(-σ) ≤ 3*(1+Clog) * (q:ℝ)^(θ*μ + ε/2) := by
    refine hhead.trans ?_
    apply mul_le_mul_of_nonneg_right _ (Real.rpow_nonneg (le_of_lt hqRpos) _)
    linarith [hClogpos]
  have hqn1 : (0:ℝ) ≤ (q:ℝ) := le_of_lt hqRpos
  have hσeq : σ = 1 - μ := by rw [hμdef]; ring
  have hb_slack : θ - (1+1/(k:ℝ))/3 = -1/(12*(k:ℝ)) := by rw [hθdef]; field_simp; ring
  have hμ_div : (0:ℝ) ≤ μ/(12*(k:ℝ)) := by positivity
  have hslack1 : θ*μ + ε/2 ≤ μ*(1+1/(k:ℝ))/3 + ε - δ := by
    have hk12 : (0:ℝ) < 12*(k:ℝ) := by positivity
    apply le_of_mul_le_mul_left _ hk12
    rw [hθdef]
    field_simp
    ring_nf
    nlinarith [hkR, hμ0, hδε, hδ, hkpos]
  have hhead3 : ‖∑ n ∈ Finset.Icc 1 Q, χ n * (n:ℂ)^(-s)‖
      ≤ (3*(1+Clog)) * (q:ℝ)^(μ*(1+1/(k:ℝ))/3 + ε - δ) * (1+|t|) := by
    have h1 : ‖∑ n ∈ Finset.Icc 1 Q, χ n * (n:ℂ)^(-s)‖ ≤ ∑ n ∈ Finset.Icc 1 Q, (n:ℝ)^(-σ) := by
      refine le_trans (norm_sum_le _ _) ?_
      apply Finset.sum_le_sum; intro n hn
      rw [norm_mul, norm_natCast_cpow_eq s (by rw [Finset.mem_Icc] at hn; omega), hsre]
      exact mul_le_of_le_one_left (by positivity) (DirichletCharacter.norm_le_one χ _)
    have hqle1 : (q:ℝ)^(θ*μ+ε/2) ≤ (q:ℝ)^(μ*(1+1/(k:ℝ))/3+ε-δ) :=
      Real.rpow_le_rpow_of_exponent_le hqR1 hslack1
    have h2 : (3+2*Clog) * (q:ℝ)^(θ*μ+ε/2) ≤ (3*(1+Clog)) * (q:ℝ)^(μ*(1+1/(k:ℝ))/3+ε-δ) := by
      have hx : (0:ℝ) ≤ (q:ℝ)^(θ*μ+ε/2) := Real.rpow_nonneg hqn1 _
      have hcoef : (3+2*Clog) ≤ 3*(1+Clog) := by linarith [hClogpos]
      have hrhs : (0:ℝ) ≤ 3*(1+Clog) := by linarith [hClogpos]
      exact mul_le_mul hcoef hqle1 hx hrhs
    have ht1 : (1:ℝ) ≤ 1+|t| := by have := abs_nonneg t; linarith
    calc ‖∑ n ∈ Finset.Icc 1 Q, χ n * (n:ℂ)^(-s)‖ ≤ ∑ n ∈ Finset.Icc 1 Q, (n:ℝ)^(-σ) := h1
      _ ≤ (3+2*Clog) * (q:ℝ)^(θ*μ + ε/2) := hhead
      _ ≤ (3*(1+Clog)) * (q:ℝ)^(μ*(1+1/(k:ℝ))/3 + ε - δ) := h2
      _ ≤ (3*(1+Clog)) * (q:ℝ)^(μ*(1+1/(k:ℝ))/3 + ε - δ) * (1+|t|) := by
          rw [mul_assoc]; exact le_mul_of_one_le_right (by positivity) ht1
  have hσ23 : (2:ℝ)/3 ≤ s.re := by rw [hsre]; linarith [hσ1, hkR]
  have hδ' : (0:ℝ) < 1/(48*(k:ℝ)) := by positivity
  -- middle bound
  have hmid : ∀ R : ℕ, Q+1 ≤ R → R ≤ q →
      ‖∑ n ∈ Finset.Icc (Q+1) R, χ n * (n:ℂ)^(-s)‖
        ≤ (4*(1+Clog2)*(CB+1)) * (q:ℝ)^(μ*(1+1/(k:ℝ))/3 + ε - δ) * (1+|t|) := by
    intro R hQR hRq
    have hPreR : ∀ m : ℕ, Q ≤ m → m ≤ R → ‖∑ k ∈ Finset.Icc 1 m, χ k‖ ≤ A * (m:ℝ)^((2:ℝ)/3) :=
      fun m hm1 hm2 => hPre m (by omega) (by omega)
    have hh := abel_two_thirds_log (le_of_lt hApos) hs0 hσ23 hQ1 hQR
      (a := fun n => χ n) hPreR
    have hQpow : (Q:ℝ)^((2:ℝ)/3 - s.re) ≤ (q:ℝ)^(θ*((2:ℝ)/3 - σ)) := by
      rw [hsre]
      have hle := Real.rpow_le_rpow_of_nonpos (Real.rpow_pos_of_pos hqRpos θ) hQge
        (show (2:ℝ)/3 - σ ≤ 0 by linarith [hσ23])
      rwa [← Real.rpow_mul hqn1] at hle
    have hlogR : (1:ℝ) + Real.log (R:ℝ) ≤ (1+Clog2) * (q:ℝ)^(1/(48*(k:ℝ))) := by
      have h1 : Real.log (R:ℝ) ≤ Clog2 * (R:ℝ)^(1/(48*(k:ℝ))) := by
        simpa using hClog2 (R:ℝ) (by exact_mod_cast (by omega : 1 ≤ R))
      have h2 : (R:ℝ)^(1/(48*(k:ℝ))) ≤ (q:ℝ)^(1/(48*(k:ℝ))) :=
        Real.rpow_le_rpow (by positivity) (by exact_mod_cast hRq) (by positivity)
      have h3 : (1:ℝ) ≤ (q:ℝ)^(1/(48*(k:ℝ))) := Real.one_le_rpow hqR1 (le_of_lt hδ')
      have h4 : Real.log (R:ℝ) ≤ Clog2 * (q:ℝ)^(1/(48*(k:ℝ))) :=
        h1.trans (mul_le_mul_of_nonneg_left h2 (le_of_lt hClog2pos))
      nlinarith [h3, h4, hClog2pos, Real.rpow_nonneg hqn1 (1/(48*(k:ℝ)))]
    have hY1 : (1:ℝ) ≤ (1+Clog2)*(q:ℝ)^(1/(48*(k:ℝ))) := by
      have h3 : (1:ℝ) ≤ (q:ℝ)^(1/(48*(k:ℝ))) := Real.one_le_rpow hqR1 (le_of_lt hδ')
      nlinarith [h3, hClog2pos]
    have hY0 : (0:ℝ) ≤ (1+Clog2)*(q:ℝ)^(1/(48*(k:ℝ))) := by positivity
    have hsn' : ‖s‖ ≤ 2*(1+|t|) := by linarith [hsnorm, abs_nonneg t]
    have hYbound : (2:ℝ) + ‖s‖*((1+Clog2)*(q:ℝ)^(1/(48*(k:ℝ))))
        ≤ 4*(1+Clog2)*(q:ℝ)^(1/(48*(k:ℝ)))*(1+|t|) := by
      have h4 : ‖s‖*((1+Clog2)*(q:ℝ)^(1/(48*(k:ℝ)))) ≤ 2*(1+|t|)*((1+Clog2)*(q:ℝ)^(1/(48*(k:ℝ)))) :=
        mul_le_mul_of_nonneg_right hsn' hY0
      have ht1 : (1:ℝ) ≤ 1+|t| := by have := abs_nonneg t; linarith
      have hY2 : (0:ℝ) ≤ (q:ℝ)^(1/(48*(k:ℝ))) := Real.rpow_nonneg hqn1 _
      nlinarith [h4, hY1, hY0, ht1, hsn', hClog2pos, hY2, le_of_lt hδ']
    have hE : (1:ℝ)/9 + ε + θ*((2:ℝ)/3 - σ) + 1/(48*(k:ℝ))
        ≤ μ*(1+1/(k:ℝ))/3 + ε - δ := by
      have hk48 : (0:ℝ) < 48*(k:ℝ) := by positivity
      have h48 : 48*(k:ℝ)*δ ≤ 1 := by rw [mul_comm]; exact (le_div_iff₀ hk48).mp hδk
      apply le_of_mul_le_mul_left _ hk48
      rw [hσeq, hθdef]
      field_simp
      ring_nf
      nlinarith [hkR, hμ0, hδε, hδ, hkpos, h48, hμ13]
    have hcomb : A * (q:ℝ)^(θ*((2:ℝ)/3 - σ))
        = (CB+1) * (q:ℝ)^((1:ℝ)/9+ε+θ*((2:ℝ)/3-σ)) := by
      rw [hAdef, mul_assoc, ← Real.rpow_add hqRpos]
    have hrr : A * (q:ℝ)^(θ*((2:ℝ)/3 - σ)) * (4*(1+Clog2)*(q:ℝ)^(1/(48*(k:ℝ)))*(1+|t|))
        = (4*(1+Clog2)*(CB+1)) * (q:ℝ)^((1:ℝ)/9+ε+θ*((2:ℝ)/3 - σ) + 1/(48*(k:ℝ))) * (1+|t|) := by
      calc A * (q:ℝ)^(θ*((2:ℝ)/3 - σ)) * (4*(1+Clog2)*(q:ℝ)^(1/(48*(k:ℝ)))*(1+|t|))
          = (CB+1) * (q:ℝ)^((1:ℝ)/9+ε+θ*((2:ℝ)/3-σ)) * (4*(1+Clog2)*(q:ℝ)^(1/(48*(k:ℝ)))*(1+|t|)) := by
            rw [hcomb]
        _ = (CB+1) * ((q:ℝ)^((1:ℝ)/9+ε+θ*((2:ℝ)/3-σ)) * (q:ℝ)^(1/(48*(k:ℝ)))) * (4*(1+Clog2)*(1+|t|)) := by ring
        _ = (CB+1) * (q:ℝ)^((1:ℝ)/9+ε+θ*((2:ℝ)/3-σ) + 1/(48*(k:ℝ))) * (4*(1+Clog2)*(1+|t|)) := by
            rw [← Real.rpow_add hqRpos]
        _ = (4*(1+Clog2)*(CB+1)) * (q:ℝ)^((1:ℝ)/9+ε+θ*((2:ℝ)/3-σ) + 1/(48*(k:ℝ))) * (1+|t|) := by ring
    have hstep : A * (q:ℝ)^(θ*((2:ℝ)/3 - σ)) * (2 + ‖s‖*((1+Clog2)*(q:ℝ)^(1/(48*(k:ℝ)))))
        ≤ (4*(1+Clog2)*(CB+1)) * (q:ℝ)^((1:ℝ)/9+ε+θ*((2:ℝ)/3 - σ) + 1/(48*(k:ℝ))) * (1+|t|) := by
      calc A * (q:ℝ)^(θ*((2:ℝ)/3 - σ)) * (2 + ‖s‖*((1+Clog2)*(q:ℝ)^(1/(48*(k:ℝ)))))
          ≤ A * (q:ℝ)^(θ*((2:ℝ)/3 - σ)) * (4*(1+Clog2)*(q:ℝ)^(1/(48*(k:ℝ)))*(1+|t|)) :=
            mul_le_mul le_rfl hYbound (by positivity) (by positivity)
        _ = _ := hrr
    calc ‖∑ n ∈ Finset.Icc (Q+1) R, χ n * (n:ℂ)^(-s)‖
        ≤ A * (Q:ℝ)^((2:ℝ)/3 - s.re) * (2 + ‖s‖*(1+Real.log (R:ℝ))) := hh
      _ ≤ A * (q:ℝ)^(θ*((2:ℝ)/3 - σ)) * (2 + ‖s‖*((1+Clog2)*(q:ℝ)^(1/(48*(k:ℝ))))) :=
          mul_le_mul (mul_le_mul_of_nonneg_left hQpow (le_of_lt hApos))
            (add_le_add le_rfl (mul_le_mul_of_nonneg_left hlogR (norm_nonneg s))) (by positivity) (by positivity)
      _ ≤ (4*(1+Clog2)*(CB+1)) * (q:ℝ)^((1:ℝ)/9+ε+θ*((2:ℝ)/3 - σ) + 1/(48*(k:ℝ))) * (1+|t|) := hstep
      _ ≤ (4*(1+Clog2)*(CB+1)) * (q:ℝ)^(μ*(1+1/(k:ℝ))/3 + ε - δ) * (1+|t|) := by
          have hq2 := Real.rpow_le_rpow_of_exponent_le hqR1 hE
          exact mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_left hq2 (by positivity)) (by positivity)
  -- tail bound
  have hPV : ∀ x y : ℕ, x ≤ y → ‖∑ n ∈ Finset.Icc x y, χ n‖ ≤ 2*CPV*Real.sqrt (q:ℝ)*Real.log (q:ℝ) := by
    intro x y hxy
    have h1 : ‖∑ n ∈ Finset.range (y+1), χ n‖ ≤ CPV*Real.sqrt (q:ℝ)*Real.log (q:ℝ) := hCPV q hq2 χ hχ y
    have h2 : ‖∑ n ∈ Finset.range x, χ n‖ ≤ CPV*Real.sqrt (q:ℝ)*Real.log (q:ℝ) := by
      rcases Nat.eq_zero_or_pos x with hx | hx
      · subst hx; simp; positivity
      · have h := hCPV q hq2 χ hχ (x-1)
        rwa [show x-1+1 = x by omega] at h
    have hsplit : ∑ n ∈ Finset.Icc x y, χ n = (∑ n ∈ Finset.range (y+1), χ n) - ∑ n ∈ Finset.range x, χ n := by
      have hun : Finset.range (y+1) = Finset.range x ∪ Finset.Icc x y := by
        ext n; simp only [Finset.mem_range, Finset.mem_union, Finset.mem_Icc]; omega
      have hdisj : Disjoint (Finset.range x) (Finset.Icc x y) := by
        rw [Finset.disjoint_left]; intro n h1 h2
        rw [Finset.mem_range] at h1; rw [Finset.mem_Icc] at h2; omega
      rw [hun, Finset.sum_union hdisj]; ring
    rw [hsplit]
    exact (norm_sub_le _ _).trans (by linarith [h1, h2])
  have hlogqq : Real.log (q:ℝ) ≤ (1+Clog2)*(q:ℝ)^(1/(48*(k:ℝ))) := by
    have h1 : Real.log (q:ℝ) ≤ Clog2 * (q:ℝ)^(1/(48*(k:ℝ))) := by simpa using hClog2 (q:ℝ) hqR1
    nlinarith [h1, hClog2pos, Real.rpow_nonneg hqn1 (1/(48*(k:ℝ)))]
  have hσinv : (1:ℝ) + ‖s‖/σ ≤ 4*(1+|t|) := by
    have h2 : ‖s‖/s.re ≤ (2+|t|)/(2/3) :=
      div_le_div₀ (by positivity) hsnorm (by norm_num) (by linarith [hσ23])
    rw [hsre] at h2
    nlinarith [h2, hsnorm, abs_nonneg t]
  have htail : ∀ M : ℕ, q < M →
      ‖∑ n ∈ Finset.Icc (q+1) M, χ n * (n:ℂ)^(-s)‖
        ≤ (14*CPV*(1+Clog2)) * (q:ℝ)^(μ*(1+1/(k:ℝ))/3 + ε - δ) * (1+|t|) := by
    intro M hqM
    have hh := Commons.Analysis.Asymptotics.abel_tail_bound_finite
      (2*CPV*Real.sqrt (q:ℝ)*Real.log (q:ℝ)) hPV s hs0 (N := q+1) (M := M) (by omega) (by omega)
    have hBnn : (0:ℝ) ≤ 2*CPV*Real.sqrt (q:ℝ)*Real.log (q:ℝ) := by
      have h1 : (0:ℝ) ≤ Real.log (q:ℝ) := Real.log_nonneg hqR1
      positivity
    have hstep0 : (2*CPV*Real.sqrt (q:ℝ)*Real.log (q:ℝ)) * ((q+1:ℕ):ℝ)^(-s.re)
        ≤ (2*CPV*Real.sqrt (q:ℝ)*Real.log (q:ℝ)) * (q:ℝ)^(-s.re) :=
      mul_le_mul_of_nonneg_left
        (Real.rpow_le_rpow_of_nonpos hqRpos (by exact_mod_cast (by omega : q ≤ q+1)) (by rw [hsre]; linarith [hs0])) hBnn
    have hexp_t : (1:ℝ)/2 - σ + 1/(48*(k:ℝ)) ≤ μ*(1+1/(k:ℝ))/3 + ε - δ := by
      have h1 : (1:ℝ)/2 - σ ≤ -1/6 := by linarith [h1k, hσ1]
      have h2 : 1/(48*(k:ℝ)) ≤ 1/144 := one_div_le_one_div_of_le (by norm_num) (by linarith [hkR])
      have h3 : (0:ℝ) ≤ μ*(1+1/(k:ℝ))/3 := by positivity
      have h4 : ε/2 ≤ ε - δ := by linarith [hδε]
      linarith [h1, h2, h3, h4]
    have hq3 : (q:ℝ)^((1:ℝ)/2 - σ + 1/(48*(k:ℝ))) ≤ (q:ℝ)^(μ*(1+1/(k:ℝ))/3 + ε - δ) :=
      Real.rpow_le_rpow_of_exponent_le hqR1 hexp_t
    have hstep1 : (2*CPV*Real.sqrt (q:ℝ)*Real.log (q:ℝ)) * (q:ℝ)^(-s.re) * (1+‖s‖/s.re)
        ≤ 8*CPV*(1+Clog2)*(q:ℝ)^((1:ℝ)/2 - σ + 1/(48*(k:ℝ)))*(1+|t|) := by
      rw [hsre, Real.sqrt_eq_rpow]
      have hAq : 2*CPV*(q:ℝ)^((1:ℝ)/2)*Real.log (q:ℝ)
          ≤ 2*CPV*(q:ℝ)^((1:ℝ)/2)*((1+Clog2)*(q:ℝ)^(1/(48*(k:ℝ)))) :=
        mul_le_mul_of_nonneg_left hlogqq (by positivity)
      have h5 : 2*CPV*(q:ℝ)^((1:ℝ)/2)*Real.log (q:ℝ)*(q:ℝ)^(-σ)
          ≤ 2*CPV*(q:ℝ)^((1:ℝ)/2)*((1+Clog2)*(q:ℝ)^(1/(48*(k:ℝ))))*(q:ℝ)^(-σ) :=
        mul_le_mul_of_nonneg_right hAq (Real.rpow_nonneg hqn1 _)
      have h6 : (0:ℝ) ≤ 2*CPV*(q:ℝ)^((1:ℝ)/2)*((1+Clog2)*(q:ℝ)^(1/(48*(k:ℝ))))*(q:ℝ)^(-σ) := by positivity
      have h7 := mul_le_mul h5 hσinv (by
        have hσpos : (0:ℝ) < σ := by linarith [hσ23]
        positivity) h6
      have hrr : (q:ℝ)^((1:ℝ)/2) * (q:ℝ)^(1/(48*(k:ℝ))) * (q:ℝ)^(-σ)
          = (q:ℝ)^((1:ℝ)/2 - σ + 1/(48*(k:ℝ))) := by
        rw [← Real.rpow_add hqRpos, ← Real.rpow_add hqRpos]
        congr 1; ring
      calc 2*CPV*(q:ℝ)^((1:ℝ)/2)*Real.log (q:ℝ)*(q:ℝ)^(-σ)*(1+‖s‖/σ)
          ≤ 2*CPV*(q:ℝ)^((1:ℝ)/2)*((1+Clog2)*(q:ℝ)^(1/(48*(k:ℝ))))*(q:ℝ)^(-σ)*(4*(1+|t|)) := h7
        _ = 8*CPV*(1+Clog2)*((q:ℝ)^((1:ℝ)/2)*(q:ℝ)^(1/(48*(k:ℝ)))*(q:ℝ)^(-σ))*(1+|t|) := by ring
        _ = 8*CPV*(1+Clog2)*(q:ℝ)^((1:ℝ)/2 - σ + 1/(48*(k:ℝ)))*(1+|t|) := by rw [hrr]
    calc ‖∑ n ∈ Finset.Icc (q+1) M, χ n * (n:ℂ)^(-s)‖
        ≤ (2*CPV*Real.sqrt (q:ℝ)*Real.log (q:ℝ)) * ((q+1:ℕ):ℝ)^(-s.re) * (1+‖s‖/s.re) := hh
      _ ≤ (2*CPV*Real.sqrt (q:ℝ)*Real.log (q:ℝ)) * (q:ℝ)^(-s.re) * (1+‖s‖/s.re) :=
          mul_le_mul_of_nonneg_right hstep0 (by positivity)
      _ ≤ 8*CPV*(1+Clog2)*(q:ℝ)^((1:ℝ)/2 - σ + 1/(48*(k:ℝ)))*(1+|t|) := hstep1
      _ ≤ 8*CPV*(1+Clog2)*(q:ℝ)^(μ*(1+1/(k:ℝ))/3 + ε - δ)*(1+|t|) := by
          exact mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_left hq3 (by positivity)) (by positivity)
      _ ≤ (14*CPV*(1+Clog2)) * (q:ℝ)^(μ*(1+1/(k:ℝ))/3 + ε - δ) * (1+|t|) := by
          have h4 : (0:ℝ) ≤ (q:ℝ)^(μ*(1+1/(k:ℝ))/3 + ε - δ) * (1+|t|) := by positivity
          have h5 : (8:ℝ)*CPV*(1+Clog2) ≤ 14*CPV*(1+Clog2) := by
            nlinarith [hCPVpos, hClog2pos]
          calc 8*CPV*(1+Clog2)*(q:ℝ)^(μ*(1+1/(k:ℝ))/3 + ε - δ)*(1+|t|)
              = (8*CPV*(1+Clog2)) * ((q:ℝ)^(μ*(1+1/(k:ℝ))/3 + ε - δ)*(1+|t|)) := by ring
            _ ≤ (14*CPV*(1+Clog2)) * ((q:ℝ)^(μ*(1+1/(k:ℝ))/3 + ε - δ)*(1+|t|)) :=
                mul_le_mul_of_nonneg_right h5 h4
            _ = (14*CPV*(1+Clog2)) * (q:ℝ)^(μ*(1+1/(k:ℝ))/3 + ε - δ) * (1+|t|) := by ring
  -- per-M bound
  have hBig : (3*(1+Clog) + 4*(1+Clog2)*(CB+1) + 14*CPV*(1+Clog2))
      ≤ 3 * (3*(1+Clog) + 4*(1+Clog2)*(CB+1) + 14*CPV*(1+Clog2)) + 1 := by
    have h4 : (0:ℝ) ≤ 3*(1+Clog) + 4*(1+Clog2)*(CB+1) + 14*CPV*(1+Clog2) := by positivity
    linarith
  have hPerM : ∀ M : ℕ, ‖∑ n ∈ Finset.Icc 1 M, χ n * (n:ℂ)^(-s)‖
      ≤ (3*(1+Clog) + 4*(1+Clog2)*(CB+1) + 14*CPV*(1+Clog2))
          * (q:ℝ)^(μ*(1+1/(k:ℝ))/3 + ε - δ) * (1+|t|) := by
    intro M
    have hTpos : (0:ℝ) ≤ (q:ℝ)^(μ*(1+1/(k:ℝ))/3 + ε - δ) * (1+|t|) := by positivity
    by_cases hMQ : M ≤ Q
    · have h1 : ‖∑ n ∈ Finset.Icc 1 M, χ n * (n:ℂ)^(-s)‖ ≤ ∑ n ∈ Finset.Icc 1 Q, (n:ℝ)^(-σ) := by
        refine le_trans (norm_sum_le _ _) ?_
        calc ∑ n ∈ Finset.Icc 1 M, ‖χ n * (n:ℂ)^(-s)‖
            ≤ ∑ n ∈ Finset.Icc 1 M, (n:ℝ)^(-σ) := by
              apply Finset.sum_le_sum; intro n hn
              rw [norm_mul, norm_natCast_cpow_eq s (by rw [Finset.mem_Icc] at hn; omega), hsre]
              exact mul_le_of_le_one_left (by positivity) (DirichletCharacter.norm_le_one χ _)
          _ ≤ ∑ n ∈ Finset.Icc 1 Q, (n:ℝ)^(-σ) := by
              apply Finset.sum_le_sum_of_subset_of_nonneg
              · intro n hn; rw [Finset.mem_Icc] at hn ⊢; omega
              · intro n hn _; positivity
      have h2 : ∑ n ∈ Finset.Icc 1 Q, (n:ℝ)^(-σ) ≤ (3*(1+Clog)) * (q:ℝ)^(μ*(1+1/(k:ℝ))/3 + ε - δ) := by
        refine hhead2.trans ?_
        have hqle1 : (q:ℝ)^(θ*μ+ε/2) ≤ (q:ℝ)^(μ*(1+1/(k:ℝ))/3+ε-δ) :=
          Real.rpow_le_rpow_of_exponent_le hqR1 hslack1
        exact mul_le_mul_of_nonneg_left hqle1 (by positivity)
      refine (h1.trans h2).trans ?_
      have hk1 : (3*(1+Clog)) ≤ 3*(1+Clog) + 4*(1+Clog2)*(CB+1) + 14*CPV*(1+Clog2) := by
        have h2 : (0:ℝ) ≤ 4*(1+Clog2)*(CB+1) + 14*CPV*(1+Clog2) := by positivity
        linarith
      calc (3*(1+Clog)) * (q:ℝ)^(μ*(1+1/(k:ℝ))/3 + ε - δ)
          ≤ (3*(1+Clog) + 4*(1+Clog2)*(CB+1) + 14*CPV*(1+Clog2)) * (q:ℝ)^(μ*(1+1/(k:ℝ))/3 + ε - δ) :=
            mul_le_mul_of_nonneg_right hk1 (Real.rpow_nonneg hqn1 _)
        _ ≤ (3*(1+Clog) + 4*(1+Clog2)*(CB+1) + 14*CPV*(1+Clog2))
            * (q:ℝ)^(μ*(1+1/(k:ℝ))/3 + ε - δ) * (1+|t|) := by
            have ht1 : (1:ℝ) ≤ 1+|t| := by have := abs_nonneg t; linarith
            rw [mul_assoc]; exact le_mul_of_one_le_right (by positivity) ht1
    · have hMQ' : Q ≤ M := le_of_lt (lt_of_not_ge hMQ)
      have hsplit1 : ∑ n ∈ Finset.Icc 1 M, χ n * (n:ℂ)^(-s)
          = ∑ n ∈ Finset.Icc 1 Q, χ n * (n:ℂ)^(-s) + ∑ n ∈ Finset.Ioc Q M, χ n * (n:ℂ)^(-s) :=
        sum_Icc_split hMQ' _
      rw [hsplit1]
      have hQR : Q ≤ min M q := le_min hMQ' hQq
      have hRM : min M q ≤ M := min_le_left _ _
      have hsplit2 : ∑ n ∈ Finset.Ioc Q M, χ n * (n:ℂ)^(-s)
          = ∑ n ∈ Finset.Ioc Q (min M q), χ n * (n:ℂ)^(-s)
            + ∑ n ∈ Finset.Ioc (min M q) M, χ n * (n:ℂ)^(-s) :=
        sum_Ioc_split hQR hRM _
      rw [hsplit2]
      have hmid' : ‖∑ n ∈ Finset.Ioc Q (min M q), χ n * (n:ℂ)^(-s)‖
          ≤ (4*(1+Clog2)*(CB+1)) * (q:ℝ)^(μ*(1+1/(k:ℝ))/3 + ε - δ) * (1+|t|) := by
        rcases lt_or_ge Q (min M q) with hQR' | hQR'
        · have hIcc : Finset.Ioc Q (min M q) = Finset.Icc (Q+1) (min M q) := by
            ext n; simp only [Finset.mem_Ioc, Finset.mem_Icc]; omega
          rw [hIcc]; exact hmid (min M q) (by omega) (min_le_right _ _)
        · have hz : ∑ n ∈ Finset.Ioc Q (min M q), χ n * (n:ℂ)^(-s) = 0 :=
            Finset.sum_eq_zero (fun n hn => by rw [Finset.mem_Ioc] at hn; omega)
          rw [hz, norm_zero]; positivity
      have htail' : ‖∑ n ∈ Finset.Ioc (min M q) M, χ n * (n:ℂ)^(-s)‖
          ≤ (14*CPV*(1+Clog2)) * (q:ℝ)^(μ*(1+1/(k:ℝ))/3 + ε - δ) * (1+|t|) := by
        rcases lt_or_ge (min M q) M with hRM' | hRM'
        · have hRq : min M q = q := by omega
          rw [hRq] at hRM'
          rw [hRq]
          have hIcc : Finset.Ioc q M = Finset.Icc (q+1) M := by
            ext n; simp only [Finset.mem_Ioc, Finset.mem_Icc]; omega
          rw [hIcc]; exact htail M hRM'
        · have hz : ∑ n ∈ Finset.Ioc (min M q) M, χ n * (n:ℂ)^(-s) = 0 :=
            Finset.sum_eq_zero (fun n hn => by rw [Finset.mem_Ioc] at hn; omega)
          rw [hz, norm_zero]; positivity
      calc ‖(∑ n ∈ Finset.Icc 1 Q, χ n * (n:ℂ)^(-s))
            + ((∑ n ∈ Finset.Ioc Q (min M q), χ n * (n:ℂ)^(-s))
              + ∑ n ∈ Finset.Ioc (min M q) M, χ n * (n:ℂ)^(-s))‖
          ≤ ‖∑ n ∈ Finset.Icc 1 Q, χ n * (n:ℂ)^(-s)‖
            + ‖(∑ n ∈ Finset.Ioc Q (min M q), χ n * (n:ℂ)^(-s))
              + ∑ n ∈ Finset.Ioc (min M q) M, χ n * (n:ℂ)^(-s)‖ := norm_add_le _ _
        _ ≤ ‖∑ n ∈ Finset.Icc 1 Q, χ n * (n:ℂ)^(-s)‖
            + (‖∑ n ∈ Finset.Ioc Q (min M q), χ n * (n:ℂ)^(-s)‖
              + ‖∑ n ∈ Finset.Ioc (min M q) M, χ n * (n:ℂ)^(-s)‖) :=
              add_le_add le_rfl (norm_add_le _ _)
        _ ≤ (3*(1+Clog)) * (q:ℝ)^(μ*(1+1/(k:ℝ))/3 + ε - δ) * (1+|t|)
            + ((4*(1+Clog2)*(CB+1)) * (q:ℝ)^(μ*(1+1/(k:ℝ))/3 + ε - δ) * (1+|t|)
              + (14*CPV*(1+Clog2)) * (q:ℝ)^(μ*(1+1/(k:ℝ))/3 + ε - δ) * (1+|t|)) :=
              add_le_add hhead3 (add_le_add hmid' htail')
        _ ≤ (3*(1+Clog) + 4*(1+Clog2)*(CB+1) + 14*CPV*(1+Clog2))
            * (q:ℝ)^(μ*(1+1/(k:ℝ))/3 + ε - δ) * (1+|t|) := by
              nlinarith [hTpos, hClogpos, hClog2pos, hCPVpos]
  have hlim := LSeries_partial_sums_tendsto χ hχ hs0
  have hnormlim : Filter.Tendsto (fun M : ℕ => ‖∑ n ∈ Finset.Icc 1 M, χ n * (n:ℂ)^(-s)‖)
      Filter.atTop (nhds ‖χ.LFunction s‖) := hlim.norm
  have hfin := le_of_tendsto' hnormlim hPerM
  rw [show ((1:ℝ)/3)*(1-σ)*(1+1/(k:ℝ)) + ε - δ = μ*(1+1/(k:ℝ))/3 + ε - δ by
    rw [hμdef]; ring]
  refine hfin.trans ?_
  have h4 : (0:ℝ) ≤ (q:ℝ)^(μ*(1+1/(k:ℝ))/3 + ε - δ) * (1+|t|) := by positivity
  nlinarith [h4, mul_le_mul_of_nonneg_right hBig h4]


set_option maxHeartbeats 1000000

/-- Bound `∏_{p | q} (1 + p^{-σ}) ≤ C q^δ` for any `δ > 0`, `σ ≥ 1/2`. -/
theorem prod_primeFactors_one_add_rpow_le' {σ δ : ℝ} (hσ : 1/2 ≤ σ) (hδ : 0 < δ) :
    ∃ C : ℝ, 0 < C ∧ ∀ q : ℕ, q ≠ 0 →
      ∏ p ∈ q.primeFactors, (1 + (p:ℝ)^(-σ)) ≤ C * (q:ℝ)^δ := by
  obtain ⟨Cd, hCdpos, hCd⟩ := Commons.NumberTheory.DivisorBound.card_divisors_le_rpow δ hδ
  refine ⟨2 * Cd, by positivity, ?_⟩
  intro q hq
  have hd : (2:ℕ) ^ q.primeFactors.card ≤ q.divisors.card := by
    rw [Nat.card_divisors hq]
    calc (2:ℕ) ^ q.primeFactors.card = ∏ _p ∈ q.primeFactors, (2:ℕ) := (Finset.prod_const _).symm
      _ ≤ ∏ p ∈ q.primeFactors, (q.factorization p + 1) := by
          apply Finset.prod_le_prod₀
          · intro p hp; norm_num
          · intro p hp
            rw [Nat.mem_primeFactors] at hp
            have := Nat.Prime.factorization_pos_of_dvd hp.1 hp.2.2 hp.2.1
            omega
  have hdR : (2:ℝ) ^ q.primeFactors.card ≤ ((q.divisors.card : ℕ) : ℝ) := by exact_mod_cast hd
  calc ∏ p ∈ q.primeFactors, (1 + (p:ℝ)^(-σ))
      ≤ ∏ _p ∈ q.primeFactors, (2:ℝ) := by
        apply Finset.prod_le_prod₀
        · intro p hp; positivity
        · intro p hp
          rw [Nat.mem_primeFactors] at hp
          have hp1 : (1:ℝ) ≤ (p:ℝ) := by exact_mod_cast hp.1.one_le
          have h1 : (p:ℝ)^(-σ) ≤ 1 := by
            have h := Real.rpow_le_rpow_of_exponent_le hp1 (show -σ ≤ (0:ℝ) by linarith)
            rwa [Real.rpow_zero] at h
          linarith
    _ = (2:ℝ) ^ q.primeFactors.card := Finset.prod_const _
    _ ≤ Cd * (q:ℝ)^δ := le_trans hdR (hCd q)
    _ ≤ 2 * Cd * (q:ℝ)^δ := by
        have h2 : (0:ℝ) ≤ (q:ℝ)^δ := Real.rpow_nonneg (by positivity) _
        nlinarith [h2, hCdpos]

theorem primitiveCharacter_ne_one {q : ℕ} [NeZero q] (χ : DirichletCharacter ℂ q) (hχ : χ ≠ 1) :
    χ.primitiveCharacter ≠ 1 := by
  intro h
  apply hχ
  rw [← DirichletCharacter.changeLevel_primitiveCharacter (χ := χ), h]
  exact DirichletCharacter.changeLevel_one χ.conductor_dvd_level

/-- Reducing a non-primitive character to its primitive one. -/
theorem LFunction_nonprimitive_le {q : ℕ} [NeZero q] (χ : DirichletCharacter ℂ q) (hχ : χ ≠ 1)
    {σ : ℝ} (hσ : 1/2 ≤ σ) {t : ℝ} :
    ‖DirichletCharacter.LFunction χ ((σ:ℂ) + (t:ℂ)*Complex.I)‖
      ≤ (∏ p ∈ q.primeFactors, (1 + (p:ℝ)^(-σ)))
          * ‖@DirichletCharacter.LFunction χ.conductor (⟨χ.conductor_ne_zero⟩ : NeZero χ.conductor)
              χ.primitiveCharacter ((σ:ℂ) + (t:ℂ)*Complex.I)‖ := by
  haveI hcond : NeZero χ.conductor := ⟨χ.conductor_ne_zero⟩
  set s : ℂ := (σ:ℂ) + (t:ℂ)*Complex.I with hsdef
  have hcl := DirichletCharacter.LFunction_changeLevel (M := χ.conductor) (N := q)
      χ.conductor_dvd_level χ.primitiveCharacter (s := s) (Or.inl (primitiveCharacter_ne_one χ hχ))
  rw [DirichletCharacter.changeLevel_primitiveCharacter] at hcl
  have hprod : ‖∏ p ∈ q.primeFactors,
        ((1:ℂ) - χ.primitiveCharacter (p : ZMod χ.conductor) * (p:ℂ)^(-s))‖
      ≤ ∏ p ∈ q.primeFactors, (1 + (p:ℝ)^(-σ)) := by
    rw [norm_prod]
    apply Finset.prod_le_prod₀
    · intro p hp; positivity
    · intro p hp
      rw [Nat.mem_primeFactors] at hp
      have hpR : (1:ℝ) ≤ (p:ℝ) := by exact_mod_cast hp.1.one_le
      have hpow : (p:ℝ)^(-σ) ≤ (p:ℝ)^(-(1/2:ℝ)) :=
        Real.rpow_le_rpow_of_exponent_le hpR (by linarith)
      calc ‖(1:ℂ) - χ.primitiveCharacter (p : ZMod χ.conductor) * (p:ℂ)^(-s)‖
          ≤ ‖(1:ℂ)‖ + ‖χ.primitiveCharacter (p : ZMod χ.conductor) * (p:ℂ)^(-s)‖ := norm_sub_le _ _
        _ ≤ 1 + (p:ℝ)^(-σ) := by
            have h1 : ‖χ.primitiveCharacter (p : ZMod χ.conductor) * (p:ℂ)^(-s)‖ ≤ (p:ℝ)^(-σ) := by
              rw [norm_mul]
              have hbase : (p:ℂ) = ((p:ℝ):ℂ) := by push_cast; ring
              rw [hbase, Complex.norm_cpow_eq_rpow_re_of_pos (by exact_mod_cast hp.1.pos)]
              have hre : (-s).re = -σ := by simp [hsdef]
              rw [hre]
              exact mul_le_of_le_one_left (Real.rpow_nonneg (by positivity) _) (DirichletCharacter.norm_le_one _ _)
            rw [show ‖(1:ℂ)‖ = 1 by norm_num]; linarith
  calc ‖DirichletCharacter.LFunction χ s‖
      = ‖DirichletCharacter.LFunction χ.primitiveCharacter s
          * ∏ p ∈ q.primeFactors,
              ((1:ℂ) - χ.primitiveCharacter (p : ZMod χ.conductor) * (p:ℂ)^(-s))‖ := by rw [hcl]
    _ = ‖DirichletCharacter.LFunction χ.primitiveCharacter s‖
          * ‖∏ p ∈ q.primeFactors,
              ((1:ℂ) - χ.primitiveCharacter (p : ZMod χ.conductor) * (p:ℂ)^(-s))‖ := norm_mul _ _
    _ ≤ ‖DirichletCharacter.LFunction χ.primitiveCharacter s‖
          * (∏ p ∈ q.primeFactors, (1 + (p:ℝ)^(-σ))) :=
        mul_le_mul_of_nonneg_left hprod (norm_nonneg _)
    _ = (∏ p ∈ q.primeFactors, (1 + (p:ℝ)^(-σ)))
          * ‖DirichletCharacter.LFunction χ.primitiveCharacter s‖ := by ring

/-- Crude bound: for `1 ≤ σ`, `‖L(σ+it,χ)‖ ≤ C (1+log q)(1+|t|)` for `χ` non-principal. -/
theorem LFunction_crude_bound :
    ∃ C : ℝ, 0 < C ∧ ∀ (q : ℕ) [NeZero q] (χ : DirichletCharacter ℂ q), χ ≠ 1 →
      ∀ σ t : ℝ, 1 ≤ σ →
        ‖DirichletCharacter.LFunction χ ((σ:ℂ) + (t:ℂ)*Complex.I)‖
          ≤ C * (1 + Real.log (q:ℝ)) * (1 + |t|) := by
  obtain ⟨CPV, hCPVpos, hCPV⟩ := Commons.NumberTheory.DirichletCharacter.polya_vinogradov
  refine ⟨4 + 4*CPV, by positivity, ?_⟩
  intro q _inst χ hχ σ t hσ1
  have hq2 : 2 ≤ q := by
    by_contra h
    rcases (by omega : q = 0 ∨ q = 1) with h0 | h1
    · exact NeZero.ne q h0
    · exact hχ (DirichletCharacter.level_one' (χ := χ) h1)
  set s : ℂ := (σ:ℂ) + (t:ℂ)*Complex.I with hsdef
  have hsre : s.re = σ := by simp [hsdef]
  have hs0 : 0 < s.re := by rw [hsre]; linarith
  have hqR1 : (1:ℝ) ≤ (q:ℝ) := by exact_mod_cast (by omega : 1 ≤ q)
  have hlogq1 : (1:ℝ) ≤ 1 + Real.log (q:ℝ) := by have := Real.log_nonneg hqR1; linarith
  have hsn : ‖s‖ ≤ σ + |t| := by
    have h := Complex.norm_le_abs_re_add_abs_im s
    rw [hsre, abs_of_nonneg (by linarith)] at h
    have him : |s.im| = |t| := by simp [hsdef]
    rw [him] at h; exact h
  have hσinv : (1:ℝ) + ‖s‖/s.re ≤ 2*(1+|t|) := by
    rw [hsre]
    have h1 : ‖s‖/σ ≤ 1 + |t| := by
      rw [div_le_iff₀ (by linarith)]
      nlinarith [hsn, hσ1, abs_nonneg t]
    have h2 : (1:ℝ) + (1+|t|) ≤ 2*(1+|t|) := by linarith [abs_nonneg t]
    linarith [h1, h2]
  have hPV : ∀ x y : ℕ, x ≤ y → ‖∑ n ∈ Finset.Icc x y, χ n‖ ≤ 2*CPV*Real.sqrt (q:ℝ)*Real.log (q:ℝ) := by
    intro x y hxy
    have h1 : ‖∑ n ∈ Finset.range (y+1), χ n‖ ≤ CPV*Real.sqrt (q:ℝ)*Real.log (q:ℝ) := hCPV q hq2 χ hχ y
    have h2 : ‖∑ n ∈ Finset.range x, χ n‖ ≤ CPV*Real.sqrt (q:ℝ)*Real.log (q:ℝ) := by
      rcases Nat.eq_zero_or_pos x with hx | hx
      · subst hx; simp; positivity
      · have h := hCPV q hq2 χ hχ (x-1)
        rwa [show x-1+1 = x by omega] at h
    have hsplit : ∑ n ∈ Finset.Icc x y, χ n = (∑ n ∈ Finset.range (y+1), χ n) - ∑ n ∈ Finset.range x, χ n := by
      have hun : Finset.range (y+1) = Finset.range x ∪ Finset.Icc x y := by
        ext n; simp only [Finset.mem_range, Finset.mem_union, Finset.mem_Icc]; omega
      have hdisj : Disjoint (Finset.range x) (Finset.Icc x y) := by
        rw [Finset.disjoint_left]; intro n h1 h2
        rw [Finset.mem_range] at h1; rw [Finset.mem_Icc] at h2; omega
      rw [hun, Finset.sum_union hdisj]; ring
    rw [hsplit]
    exact (norm_sub_le _ _).trans (by linarith [h1, h2])
  have hqRpos : (0:ℝ) < (q:ℝ) := by exact_mod_cast (by omega : 0 < q)
  have hheadM : ∀ M : ℕ, ‖∑ n ∈ Finset.Icc 1 M, χ n * (n:ℂ)^(-s)‖
      ≤ ∑ n ∈ Finset.Icc 1 M, (n:ℝ)⁻¹ := by
    intro M
    refine le_trans (norm_sum_le _ _) ?_
    apply Finset.sum_le_sum; intro n hn
    rw [norm_mul, norm_natCast_cpow_eq s (by rw [Finset.mem_Icc] at hn; omega), hsre]
    calc ‖χ n‖ * (n:ℝ)^(-σ) ≤ 1 * (n:ℝ)^(-σ) :=
          mul_le_mul_of_nonneg_right (DirichletCharacter.norm_le_one χ _) (by positivity)
      _ ≤ (n:ℝ)⁻¹ := by
          rw [one_mul]
          calc (n:ℝ)^(-σ) ≤ (n:ℝ)^(-(1:ℝ)) :=
                Real.rpow_le_rpow_of_exponent_le (by exact_mod_cast (by rw [Finset.mem_Icc] at hn; omega : 1 ≤ n))
                  (show -σ ≤ -(1:ℝ) by linarith)
            _ = (n:ℝ)⁻¹ := Real.rpow_neg_one (n:ℝ)
  have hheadq : ∑ n ∈ Finset.Icc 1 q, (n:ℝ)⁻¹ ≤ 1 + Real.log (q:ℝ) := by
    calc ∑ n ∈ Finset.Icc 1 q, (n:ℝ)⁻¹ = (harmonic q : ℝ) := by
          simp [harmonic_eq_sum_Icc, Rat.cast_sum]
      _ ≤ 1 + Real.log (q:ℝ) := harmonic_le_one_add_log q
  have hstep : ∀ M : ℕ, ‖∑ n ∈ Finset.Icc 1 M, χ n * (n:ℂ)^(-s)‖
      ≤ (4 + 4*CPV) * (1 + Real.log (q:ℝ)) * (1 + |t|) := by
    intro M
    have ht1 : (1:ℝ) ≤ 1 + |t| := by have := abs_nonneg t; linarith
    have hA : (1:ℝ) ≤ 4 + 4*CPV := by linarith [hCPVpos]
    have hgoal : (1 + Real.log (q:ℝ)) ≤ (4 + 4*CPV) * (1 + Real.log (q:ℝ)) * (1 + |t|) := by
      calc 1 + Real.log (q:ℝ) ≤ (4 + 4*CPV) * (1 + Real.log (q:ℝ)) := by nlinarith [hlogq1, hA]
        _ = (4 + 4*CPV) * (1 + Real.log (q:ℝ)) * 1 := by ring
        _ ≤ (4 + 4*CPV) * (1 + Real.log (q:ℝ)) * (1 + |t|) :=
            mul_le_mul_of_nonneg_left ht1 (by positivity)
    by_cases hMq : M ≤ q
    · refine (hheadM M).trans ?_
      calc ∑ n ∈ Finset.Icc 1 M, (n:ℝ)⁻¹ ≤ ∑ n ∈ Finset.Icc 1 q, (n:ℝ)⁻¹ := by
            apply Finset.sum_le_sum_of_subset_of_nonneg
            · intro n hn; rw [Finset.mem_Icc] at hn ⊢; exact ⟨hn.1, le_trans hn.2 hMq⟩
            · intro n hn _; positivity
        _ ≤ 1 + Real.log (q:ℝ) := hheadq
        _ ≤ (4 + 4*CPV) * (1 + Real.log (q:ℝ)) * (1 + |t|) := hgoal
    · have hqM : q ≤ M := le_of_lt (lt_of_not_ge hMq)
      have hsplit : ∑ n ∈ Finset.Icc 1 M, χ n * (n:ℂ)^(-s)
          = ∑ n ∈ Finset.Icc 1 q, χ n * (n:ℂ)^(-s) + ∑ n ∈ Finset.Ioc q M, χ n * (n:ℂ)^(-s) :=
        sum_Icc_split hqM _
      rw [hsplit]
      have h1 : ‖∑ n ∈ Finset.Icc 1 q, χ n * (n:ℂ)^(-s)‖ ≤ 1 + Real.log (q:ℝ) :=
        (hheadM q).trans hheadq
      have h2 : ‖∑ n ∈ Finset.Ioc q M, χ n * (n:ℂ)^(-s)‖
          ≤ 4*CPV*(1 + Real.log (q:ℝ)) * (1 + |t|) := by
        have hIcc : Finset.Ioc q M = Finset.Icc (q+1) M := by
          ext n; simp only [Finset.mem_Ioc, Finset.mem_Icc]; omega
        rw [hIcc]
        have hh := Commons.Analysis.Asymptotics.abel_tail_bound_finite
          (2*CPV*Real.sqrt (q:ℝ)*Real.log (q:ℝ)) hPV s hs0 (N := q+1) (M := M) (by omega) (by omega)
        have hBnn : (0:ℝ) ≤ 2*CPV*Real.sqrt (q:ℝ)*Real.log (q:ℝ) := by
          have h1 : (0:ℝ) ≤ Real.log (q:ℝ) := Real.log_nonneg hqR1
          positivity
        have hres : ((q+1:ℕ):ℝ)^(-s.re) ≤ (q:ℝ)^(-s.re) :=
          Real.rpow_le_rpow_of_nonpos hqRpos (by exact_mod_cast (by omega : q ≤ q+1)) (by rw [hsre]; linarith [hs0])
        have hneg : (q:ℝ)^(-s.re) ≤ (q:ℝ)⁻¹ := by
          rw [hsre, ← Real.rpow_neg_one]
          exact Real.rpow_le_rpow_of_exponent_le hqR1 (show -σ ≤ -(1:ℝ) by linarith)
        have hsq : Real.sqrt (q:ℝ) ≤ q := by
          rw [Real.sqrt_le_iff]; constructor <;> nlinarith [hqR1]
        calc ‖∑ n ∈ Finset.Icc (q+1) M, χ n * (n:ℂ)^(-s)‖
            ≤ (2*CPV*Real.sqrt (q:ℝ)*Real.log (q:ℝ)) * ((q+1:ℕ):ℝ)^(-s.re) * (1+‖s‖/s.re) := hh
          _ ≤ (2*CPV*Real.sqrt (q:ℝ)*Real.log (q:ℝ)) * (q:ℝ)^(-s.re) * (1+‖s‖/s.re) :=
              mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_left hres hBnn) (by positivity)
          _ ≤ (2*CPV*Real.sqrt (q:ℝ)*Real.log (q:ℝ)) * (q:ℝ)⁻¹ * (2*(1 + |t|)) := by
              apply mul_le_mul
              · exact mul_le_mul_of_nonneg_left hneg hBnn
              · exact hσinv
              · positivity
              · positivity
          _ ≤ 4*CPV*(1 + Real.log (q:ℝ)) * (1 + |t|) := by
              have hlog1 : (0:ℝ) ≤ Real.log (q:ℝ) := Real.log_nonneg hqR1
              have ht1' : (0:ℝ) ≤ 1 + |t| := by positivity
              have hsqnn : (0:ℝ) ≤ Real.sqrt (q:ℝ) := Real.sqrt_nonneg _
              have hsq2 : Real.sqrt (q:ℝ) * (q:ℝ)⁻¹ ≤ 1 := by
                rw [← div_eq_mul_inv, div_le_one hqRpos]; exact hsq
              have h3 : Real.sqrt (q:ℝ)*(q:ℝ)⁻¹*Real.log (q:ℝ) ≤ 1*(1+Real.log (q:ℝ)) := by
                nlinarith [hsq2, hlog1, hsqnn, mul_nonneg hsqnn (by positivity : (0:ℝ) ≤ (q:ℝ)⁻¹)]
              calc (2*CPV*Real.sqrt (q:ℝ)*Real.log (q:ℝ)) * (q:ℝ)⁻¹ * (2*(1 + |t|))
                  = 4*CPV*((Real.sqrt (q:ℝ)*(q:ℝ)⁻¹)*Real.log (q:ℝ))*(1 + |t|) := by ring
                _ ≤ 4*CPV*(1*(1+Real.log (q:ℝ)))*(1 + |t|) :=
                    mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_left h3 (by positivity)) (by positivity)
                _ = 4*CPV*(1 + Real.log (q:ℝ)) * (1 + |t|) := by ring
      calc ‖(∑ n ∈ Finset.Icc 1 q, χ n * (n:ℂ)^(-s)) + ∑ n ∈ Finset.Ioc q M, χ n * (n:ℂ)^(-s)‖
          ≤ ‖∑ n ∈ Finset.Icc 1 q, χ n * (n:ℂ)^(-s)‖ + ‖∑ n ∈ Finset.Ioc q M, χ n * (n:ℂ)^(-s)‖ :=
            norm_add_le _ _
        _ ≤ (1 + Real.log (q:ℝ)) + 4*CPV*(1 + Real.log (q:ℝ)) * (1 + |t|) := add_le_add h1 h2
        _ ≤ (4 + 4*CPV) * (1 + Real.log (q:ℝ)) * (1 + |t|) := by
            have ht1' : (1:ℝ) ≤ 1 + |t| := by have := abs_nonneg t; linarith
            have hlog1 : (0:ℝ) ≤ Real.log (q:ℝ) := Real.log_nonneg hqR1
            have hB : (1 + Real.log (q:ℝ)) ≤ (1 + Real.log (q:ℝ)) * (1 + |t|) :=
              le_mul_of_one_le_right (by linarith) ht1'
            have hEP : (0:ℝ) ≤ 4*CPV*(1 + Real.log (q:ℝ)) * (1 + |t|) := by positivity
            nlinarith [hB, hlog1, hCPVpos, ht1', hEP]
  have hlim := LSeries_partial_sums_tendsto χ hχ hs0
  have hnormlim : Filter.Tendsto (fun M : ℕ => ‖∑ n ∈ Finset.Icc 1 M, χ n * (n:ℂ)^(-s)‖)
      Filter.atTop (nhds ‖χ.LFunction s‖) := hlim.norm
  exact le_of_tendsto' hnormlim hstep

/-- Absorbing `log q` into the target exponent for `σ ≥ 1`. -/
lemma crude_absorb {k : ℕ} (hk : 3 ≤ k) {ε : ℝ} (hε : 0 < ε) :
    ∃ Cf : ℝ, 0 < Cf ∧ ∀ q : ℕ, 1 ≤ q → ∀ σ : ℝ, 1 ≤ σ →
      σ ≤ 1 + Real.log (Real.log (q:ℝ))/Real.log (q:ℝ) →
      (1 + Real.log (q:ℝ)) ≤ Cf * (q:ℝ)^(((1:ℝ)/3)*(1-σ)*(1+1/(k:ℝ)) + ε) := by
  obtain ⟨Cl, hClpos, hCl⟩ := Commons.Analysis.Real.log_pow_le_mul_rpow hε 3
  have hkR : (1:ℝ) ≤ (k:ℝ) := by exact_mod_cast (by omega : 1 ≤ k)
  refine ⟨8*(1+Cl) + 8, by positivity, ?_⟩
  intro q hq1 σ hσge hσle
  rcases eq_or_lt_of_le hq1 with hq | hq
  · subst hq
    simp only [Nat.cast_one, Real.log_one, Real.one_rpow, mul_one]
    nlinarith [hClpos]
  have hqR1 : (1:ℝ) ≤ (q:ℝ) := by exact_mod_cast (le_of_lt hq)
  have hqRpos : (0:ℝ) < (q:ℝ) := by exact_mod_cast (by omega : 0 < q)
  have hlogq0 : (0:ℝ) ≤ Real.log (q:ℝ) := Real.log_nonneg hqR1
  have hlogqpos : 0 < Real.log (q:ℝ) := Real.log_pos (by exact_mod_cast hq)
  have hqe1 : (1:ℝ) ≤ (q:ℝ)^ε := Real.one_le_rpow hqR1 (le_of_lt hε)
  set e : ℝ := (1:ℝ)/3 + 1/(3*(k:ℝ)) with hedef
  have hepos : 0 < e := by rw [hedef]; positivity
  have hee : (1+1/(k:ℝ))/3 = e := by rw [hedef]; ring
  have hsq : (1 + Real.log (q:ℝ))^3 ≤ (8*(1+Cl)+8) * (q:ℝ)^ε := by
    have h1 : (Real.log (q:ℝ))^3 ≤ Cl * (q:ℝ)^ε := hCl (q:ℝ) hqR1
    have h2 : (1:ℝ) ≤ 1 + Real.log (q:ℝ) := by linarith
    have h3 : (1 + Real.log (q:ℝ))^3 = 1 + 3*Real.log (q:ℝ) + 3*(Real.log (q:ℝ))^2 + (Real.log (q:ℝ))^3 := by ring
    have h4 : 3*Real.log (q:ℝ) + 3*(Real.log (q:ℝ))^2 ≤ 3 + 6*(Real.log (q:ℝ))^2 := by
      nlinarith [hlogq0, h2, pow_nonneg hlogq0 2, sq_nonneg (Real.log (q:ℝ) - 1)]
    nlinarith [h1, h4, hlogq0, hqe1, hClpos, Real.rpow_nonneg (by positivity) ε, pow_nonneg hlogq0 2]
  have hloge : (Real.log (q:ℝ))^e ≤ (1 + Real.log (q:ℝ))^(2:ℕ) := by
    have h1 : (Real.log (q:ℝ))^e ≤ (1 + Real.log (q:ℝ))^e :=
      Real.rpow_le_rpow hlogq0 (by linarith) (le_of_lt hepos)
    have h2 : e ≤ 2 := by
      rw [hedef]
      have h : (3:ℝ) ≤ 3*(k:ℝ) := by linarith [hkR]
      have h3 : 1/(3*(k:ℝ)) ≤ 1/3 := one_div_le_one_div_of_le (by norm_num : (0:ℝ)<3) h
      linarith
    have h3 : (1 + Real.log (q:ℝ))^e ≤ (1 + Real.log (q:ℝ))^((2:ℕ):ℝ) :=
      Real.rpow_le_rpow_of_exponent_le (le_add_of_nonneg_right (Real.log_nonneg hqR1)) h2
    exact h1.trans (by simpa only [Real.rpow_natCast] using h3)
  have hprod : (1 + Real.log (q:ℝ)) * (Real.log (q:ℝ))^e ≤ (8*(1+Cl)+8) * (q:ℝ)^ε := by
    calc (1 + Real.log (q:ℝ)) * (Real.log (q:ℝ))^e
        ≤ (1 + Real.log (q:ℝ)) * (1 + Real.log (q:ℝ))^2 :=
          mul_le_mul_of_nonneg_left hloge (by linarith)
      _ = (1 + Real.log (q:ℝ))^3 := by ring
      _ ≤ (8*(1+Cl)+8) * (q:ℝ)^ε := hsq
  set L : ℝ := Real.log (Real.log (q:ℝ))/Real.log (q:ℝ) with hLdef
  have hexp_eq : Real.log (q:ℝ) = (q:ℝ)^L := by
    rw [hLdef, Real.rpow_def_of_pos hqRpos]
    rw [show Real.log (q:ℝ) * (Real.log (Real.log (q:ℝ))/Real.log (q:ℝ)) = Real.log (Real.log (q:ℝ)) by field_simp]
    exact (Real.exp_log hlogqpos).symm
  have hlogeq : (q:ℝ)^(e * L) = (Real.log (q:ℝ))^e := by
    conv_rhs => rw [hexp_eq, ← Real.rpow_mul (le_of_lt hqRpos)]
    rw [mul_comm]
  have hqe : (q:ℝ)^ε ≤ (q:ℝ)^(((1:ℝ)/3)*(1-σ)*(1+1/(k:ℝ)) + ε) * (Real.log (q:ℝ))^e := by
    rw [← hlogeq, ← Real.rpow_add hqRpos]
    apply Real.rpow_le_rpow_of_exponent_le hqR1
    have h1 : (1:ℝ) - σ + Real.log (Real.log (q:ℝ))/Real.log (q:ℝ) ≥ 0 := by linarith [hσle]
    have h2 := mul_le_mul_of_nonneg_left h1 (show (0:ℝ) ≤ 1+1/(k:ℝ) by positivity)
    rw [← hee]
    nlinarith [h2]
  have hloge_pos : 0 < (Real.log (q:ℝ))^e := Real.rpow_pos_of_pos hlogqpos e
  have hfinal : (1 + Real.log (q:ℝ)) ≤ (8*(1+Cl)+8) * (q:ℝ)^(((1:ℝ)/3)*(1-σ)*(1+1/(k:ℝ)) + ε) := by
    have h1 : (1 + Real.log (q:ℝ)) * (Real.log (q:ℝ))^e
        ≤ ((8*(1+Cl)+8) * (q:ℝ)^(((1:ℝ)/3)*(1-σ)*(1+1/(k:ℝ)) + ε)) * (Real.log (q:ℝ))^e := by
      calc (1 + Real.log (q:ℝ)) * (Real.log (q:ℝ))^e
          ≤ (8*(1+Cl)+8) * (q:ℝ)^ε := hprod
        _ ≤ (8*(1+Cl)+8) * ((q:ℝ)^(((1:ℝ)/3)*(1-σ)*(1+1/(k:ℝ)) + ε) * (Real.log (q:ℝ))^e) :=
            mul_le_mul_of_nonneg_left hqe (by positivity)
        _ = ((8*(1+Cl)+8) * (q:ℝ)^(((1:ℝ)/3)*(1-σ)*(1+1/(k:ℝ)) + ε)) * (Real.log (q:ℝ))^e := by ring
    exact le_of_mul_le_mul_right h1 hloge_pos
  exact hfinal

set_option maxHeartbeats 2000000

theorem LFunction_bound_third_of_burgess {ε : ℝ} (hε : 0 < ε) (k : ℕ) (hk : 3 ≤ k)
    {CB : ℝ} (hCB : 0 < CB)
    (hB : ∀ {q : ℕ} [NeZero q] (χ : DirichletCharacter ℂ q), χ.IsPrimitive → χ ≠ 1 →
      ∀ {N H : ℕ}, 1 ≤ N → 1 ≤ H → H ≤ q →
        ‖∑ n ∈ Finset.Ioc N (N + H), χ n‖ ≤
          CB * (q : ℝ) ^ ((1 : ℝ) / 9 + ε) * (H : ℝ) ^ ((2 : ℝ) / 3)) :
    ∃ C : ℝ, 0 < C ∧ ∀ {q : ℕ} [NeZero q] (χ : DirichletCharacter ℂ q), χ ≠ 1 →
      ∀ σ t : ℝ, 1 - 1 / (k : ℝ) ≤ σ →
        σ ≤ 1 + Real.log (Real.log (q : ℝ)) / Real.log (q : ℝ) →
        ‖DirichletCharacter.LFunction χ ((σ : ℂ) + (t : ℂ) * Complex.I)‖ ≤
          C * (q : ℝ) ^ (((1 : ℝ) / 3) * (1 - σ) * (1 + 1 / (k : ℝ)) + ε)
            * (1 + |t|) := by
  have hkR : (1:ℝ) ≤ (k:ℝ) := by exact_mod_cast (by omega : 1 ≤ k)
  set δ : ℝ := min (ε/2) (1/(48*(k:ℝ))) with hδdef
  have hδ : 0 < δ := lt_min (by positivity) (by positivity)
  have hδε : δ ≤ ε/2 := min_le_left _ _
  have hδk : δ ≤ 1/(48*(k:ℝ)) := min_le_right _ _
  obtain ⟨Cp, hCppos, hCp⟩ := primitive_LFunction_bound k hk hε hδ hδε hδk hCB
  obtain ⟨Cpd, hCpdpos, hCpd⟩ := prod_primeFactors_one_add_rpow_le' (by norm_num : (1/2:ℝ) ≤ 1/2) hδ
  obtain ⟨Cc, hCcpos, hCc⟩ := LFunction_crude_bound
  obtain ⟨Cf, hCfpos, hCf⟩ := crude_absorb hk hε
  refine ⟨max (Cp * Cpd) (Cc * Cf) + 1, by positivity, ?_⟩
  intro q _inst χ hχ σ t hσ hσle
  have hσ12 : (1:ℝ)/2 ≤ σ := by
    have h3k : (3:ℝ) ≤ (k:ℝ) := by exact_mod_cast hk
    have h1k : 1/(k:ℝ) ≤ 1/3 := one_div_le_one_div_of_le (by norm_num : (0:ℝ)<3) h3k
    linarith
  by_cases hσ1 : σ ≤ 1
  · have hχprim : χ.primitiveCharacter.IsPrimitive := DirichletCharacter.primitiveCharacter_isPrimitive χ
    have hχprim_ne : χ.primitiveCharacter ≠ 1 := primitiveCharacter_ne_one χ hχ
    have hcond : NeZero χ.conductor := ⟨χ.conductor_ne_zero⟩
    have hB' : ∀ {N H : ℕ}, 1 ≤ N → 1 ≤ H → H ≤ χ.conductor →
        ‖∑ n ∈ Finset.Ioc N (N + H), χ.primitiveCharacter n‖ ≤
          CB * (χ.conductor : ℝ)^((1:ℝ)/9+ε) * (H:ℝ)^((2:ℝ)/3) := by
      intro N H hN hH hHq
      exact hB (q := χ.conductor) (χ := χ.primitiveCharacter) hχprim hχprim_ne hN hH hHq
    have hpb := hCp χ.conductor χ.primitiveCharacter hχprim hχprim_ne hB' σ t hσ hσ1
    have hred := LFunction_nonprimitive_le χ hχ (σ := σ) hσ12 (t := t)
    have hprod_le : (∏ p ∈ q.primeFactors, (1 + (p:ℝ)^(-σ))) ≤ Cpd * (q:ℝ)^δ := by
      refine (Finset.prod_le_prod₀ (fun p hp => by positivity) ?_).trans (hCpd q (NeZero.ne q))
      intro p hp
      rw [Nat.mem_primeFactors] at hp
      have hp1 : (1:ℝ) ≤ (p:ℝ) := by exact_mod_cast hp.1.one_le
      have h := Real.rpow_le_rpow_of_exponent_le hp1 (show -σ ≤ -(1/2:ℝ) by linarith)
      linarith
    have hE0 : 0 ≤ ((1:ℝ)/3)*(1-σ)*(1+1/(k:ℝ)) + ε - δ := by
      have : (0:ℝ) ≤ (1-σ)*(1+1/(k:ℝ))/3 := by
        apply div_nonneg (mul_nonneg (by linarith) (by positivity)) (by norm_num)
      linarith [hδε, hε]
    have hqstar : (χ.conductor : ℝ)^(((1:ℝ)/3)*(1-σ)*(1+1/(k:ℝ)) + ε - δ)
        ≤ (q:ℝ)^(((1:ℝ)/3)*(1-σ)*(1+1/(k:ℝ)) + ε - δ) := by
      apply Real.rpow_le_rpow
      · positivity
      · exact_mod_cast (Nat.le_of_dvd (NeZero.pos q) χ.conductor_dvd_level)
      · exact hE0
    calc ‖DirichletCharacter.LFunction χ ((σ:ℂ) + (t:ℂ)*Complex.I)‖
        ≤ (∏ p ∈ q.primeFactors, (1 + (p:ℝ)^(-σ)))
            * ‖@DirichletCharacter.LFunction χ.conductor hcond χ.primitiveCharacter ((σ:ℂ) + (t:ℂ)*Complex.I)‖ := hred
      _ ≤ (Cpd * (q:ℝ)^δ) * (Cp * (χ.conductor:ℝ)^(((1:ℝ)/3)*(1-σ)*(1+1/(k:ℝ)) + ε - δ) * (1+|t|)) := by
          apply mul_le_mul hprod_le hpb (norm_nonneg _) (by positivity)
      _ = (Cp * Cpd) * ((χ.conductor:ℝ)^(((1:ℝ)/3)*(1-σ)*(1+1/(k:ℝ)) + ε - δ) * (q:ℝ)^δ) * (1+|t|) := by ring
      _ ≤ (Cp * Cpd) * ((q:ℝ)^(((1:ℝ)/3)*(1-σ)*(1+1/(k:ℝ)) + ε - δ) * (q:ℝ)^δ) * (1+|t|) := by
          have h2 : (0:ℝ) ≤ (q:ℝ)^δ := Real.rpow_nonneg (by positivity) _
          have h3 : (0:ℝ) ≤ (1+|t|) := by positivity
          have h4 := mul_le_mul_of_nonneg_right hqstar h2
          have h5 := mul_le_mul_of_nonneg_right h4 (by positivity : (0:ℝ) ≤ Cp*Cpd*(1+|t|))
          linarith [h5]
      _ = (Cp * Cpd) * (q:ℝ)^(((1:ℝ)/3)*(1-σ)*(1+1/(k:ℝ)) + ε) * (1+|t|) := by
          rw [← Real.rpow_add (by exact_mod_cast (NeZero.pos q) : (0:ℝ) < (q:ℝ))]
          rw [show ((1:ℝ)/3)*(1-σ)*(1+1/(k:ℝ)) + ε - δ + δ = ((1:ℝ)/3)*(1-σ)*(1+1/(k:ℝ)) + ε by ring]
      _ ≤ (max (Cp * Cpd) (Cc * Cf) + 1) * (q:ℝ)^(((1:ℝ)/3)*(1-σ)*(1+1/(k:ℝ)) + ε) * (1+|t|) := by
          have h4 : (0:ℝ) ≤ (q:ℝ)^(((1:ℝ)/3)*(1-σ)*(1+1/(k:ℝ)) + ε) * (1+|t|) := by positivity
          have h5 : Cp * Cpd ≤ max (Cp * Cpd) (Cc * Cf) + 1 := by
            have := le_max_left (Cp*Cpd) (Cc*Cf); linarith
          nlinarith [h4, h5, hCppos, hCpdpos]
  · have hσge : 1 ≤ σ := le_of_lt (lt_of_not_ge hσ1)
    have hcb := hCc q χ hχ σ t hσge
    have hca := hCf q (Nat.one_le_iff_ne_zero.mpr (NeZero.ne q)) σ hσge hσle
    calc ‖DirichletCharacter.LFunction χ ((σ:ℂ) + (t:ℂ)*Complex.I)‖
        ≤ Cc * (1 + Real.log (q:ℝ)) * (1 + |t|) := hcb
      _ ≤ Cc * (Cf * (q:ℝ)^(((1:ℝ)/3)*(1-σ)*(1+1/(k:ℝ)) + ε)) * (1 + |t|) := by
          apply mul_le_mul_of_nonneg_right _ (by positivity)
          exact mul_le_mul_of_nonneg_left hca (le_of_lt hCcpos)
      _ = (Cc * Cf) * (q:ℝ)^(((1:ℝ)/3)*(1-σ)*(1+1/(k:ℝ)) + ε) * (1 + |t|) := by ring
      _ ≤ (max (Cp * Cpd) (Cc * Cf) + 1) * (q:ℝ)^(((1:ℝ)/3)*(1-σ)*(1+1/(k:ℝ)) + ε) * (1 + |t|) := by
          have h4 : (0:ℝ) ≤ (q:ℝ)^(((1:ℝ)/3)*(1-σ)*(1+1/(k:ℝ)) + ε) * (1+|t|) := by positivity
          have h5 : Cc * Cf ≤ max (Cp * Cpd) (Cc * Cf) + 1 := by
            have := le_max_right (Cp*Cpd) (Cc*Cf); linarith
          nlinarith [h4, h5, hCcpos, hCfpos]

end Commons.NumberTheory.DirichletCharacter
