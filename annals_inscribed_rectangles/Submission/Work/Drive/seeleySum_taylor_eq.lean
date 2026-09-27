import Mathlib
import Submission.Work.Drive.seeleyDefs
import Submission.Work.Drive.seeleyEpsDefs

/-!
# The exact form of `seeleySum a b (seeleyTaylor F N) - seeleyTaylor F N`

Expanding the Taylor polynomial and interchanging the two summations, the moment identities
`Σ_j a_j b_j^q = (-1)^q` cancel the "bulk" of the expansion and leave only the tail sums `ε_n`.
-/

set_option maxHeartbeats 1000000

namespace Work.Drive

lemma seeleyRho_nonneg (t : ℝ) : 0 ≤ seeleyRho t := ContDiffBump.nonneg seeleyBump (x := t)

lemma abs_one_sub_seeleyRho (t : ℝ) : |1 - seeleyRho t| ≤ 1 :=
  abs_le.mpr ⟨by linarith [seeleyRho_le_one t], by linarith [seeleyRho_nonneg t]⟩

lemma seeleyRho_abs_le_one (t : ℝ) : |seeleyRho t| ≤ 1 :=
  abs_le.mpr ⟨by linarith [seeleyRho_nonneg t], seeleyRho_le_one t⟩

/-- `Σ_j |a_j| |b_j|^n` converges whenever all absolute moments `Σ_j |a_j| b_j^q` do. -/
lemma summable_abs_abs_pow {a b : ℕ → ℝ}
    (hsum : ∀ q : ℕ, Summable (fun j : ℕ => |a j| * (b j) ^ q)) (n : ℕ) :
    Summable (fun j : ℕ => |a j| * |b j| ^ n) := by
  have h0 : Summable (fun j : ℕ => |a j|) := by simpa [pow_zero] using hsum 0
  have hd : Summable (fun j : ℕ => |a j| + |a j| * (b j) ^ (2 * n)) := h0.add (hsum (2 * n))
  refine Summable.of_nonneg_of_le (fun j => mul_nonneg (abs_nonneg _) (pow_nonneg (abs_nonneg _) n))
    (fun j => ?_) hd
  have hb : |b j| ^ n ≤ 1 + (b j) ^ (2 * n) := by
    have h2n : (0 : ℝ) ≤ (b j) ^ (2 * n) := by
      rw [pow_mul]; positivity
    by_cases h : |b j| ≤ 1
    · calc |b j| ^ n ≤ 1 := pow_le_one₀ (abs_nonneg _) h
        _ ≤ 1 + (b j) ^ (2 * n) := le_add_of_nonneg_right h2n
    · have h1 : 1 ≤ |b j| := le_of_lt (not_le.mp h)
      have h2 : |b j| ^ n ≤ |b j| ^ (2 * n) := pow_le_pow_right₀ h1 (by omega)
      have h3 : |b j| ^ (2 * n) = (b j) ^ (2 * n) := by
        rw [← abs_pow, abs_of_nonneg h2n]
      rw [h3] at h2
      calc |b j| ^ n ≤ (b j) ^ (2 * n) := h2
        _ ≤ 1 + (b j) ^ (2 * n) := le_add_of_nonneg_left zero_le_one
  calc |a j| * |b j| ^ n ≤ |a j| * (1 + (b j) ^ (2 * n)) := by gcongr
    _ = |a j| + |a j| * (b j) ^ (2 * n) := by ring

lemma summable_mul_pow {a b : ℕ → ℝ}
    (hsum : ∀ q : ℕ, Summable (fun j : ℕ => |a j| * (b j) ^ q)) (n : ℕ) :
    Summable (fun j : ℕ => a j * (b j) ^ n) :=
  Summable.of_norm_bounded (summable_abs_abs_pow hsum n) (fun j => by
    rw [Real.norm_eq_abs, abs_mul, abs_pow])

private lemma norm_bound_pos (a b u : ℝ) (hu : |u| ≤ 1) (n : ℕ) (s : ℝ) :
    ‖a * u * (b * s) ^ n‖ ≤ |a| * |b| ^ n * |s| ^ n := by
  rw [Real.norm_eq_abs, abs_mul, abs_mul, abs_pow, abs_mul, mul_pow]
  calc |a| * |u| * (|b| ^ n * |s| ^ n) ≤ |a| * 1 * (|b| ^ n * |s| ^ n) := by
        apply mul_le_mul_of_nonneg_right _ (mul_nonneg (pow_nonneg (abs_nonneg _) n)
          (pow_nonneg (abs_nonneg _) n))
        exact mul_le_mul_of_nonneg_left hu (abs_nonneg _)
    _ = |a| * |b| ^ n * |s| ^ n := by ring

private lemma norm_bound_neg (a b u : ℝ) (hu : |u| ≤ 1) (n : ℕ) (s : ℝ) :
    ‖a * u * (-(b * s)) ^ n‖ ≤ |a| * |b| ^ n * |s| ^ n := by
  rw [Real.norm_eq_abs, abs_mul, abs_mul, abs_pow, abs_neg, abs_mul, mul_pow]
  calc |a| * |u| * (|b| ^ n * |s| ^ n) ≤ |a| * 1 * (|b| ^ n * |s| ^ n) := by
        apply mul_le_mul_of_nonneg_right _ (mul_nonneg (pow_nonneg (abs_nonneg _) n)
          (pow_nonneg (abs_nonneg _) n))
        exact mul_le_mul_of_nonneg_left hu (abs_nonneg _)
    _ = |a| * |b| ^ n * |s| ^ n := by ring

lemma summable_rho_pow {a b : ℕ → ℝ}
    (hsum : ∀ q : ℕ, Summable (fun j : ℕ => |a j| * (b j) ^ q)) (n : ℕ) (s : ℝ) :
    Summable (fun j : ℕ => a j * seeleyRho (b j * s) * (b j * s) ^ n) :=
  Summable.of_norm_bounded ((summable_abs_abs_pow hsum n).mul_right (|s| ^ n))
    (fun j => by simpa [mul_assoc] using norm_bound_pos (a j) (b j) _ (seeleyRho_abs_le_one _) n s)

lemma summable_oneSubRho_pow {a b : ℕ → ℝ}
    (hsum : ∀ q : ℕ, Summable (fun j : ℕ => |a j| * (b j) ^ q)) (n : ℕ) (s : ℝ) :
    Summable (fun j : ℕ => a j * (1 - seeleyRho (b j * s)) * (b j * s) ^ n) :=
  Summable.of_norm_bounded ((summable_abs_abs_pow hsum n).mul_right (|s| ^ n))
    (fun j => by
      simpa [mul_assoc] using norm_bound_pos (a j) (b j) _ (abs_one_sub_seeleyRho _) n s)

lemma summable_pow {a b : ℕ → ℝ}
    (hsum : ∀ q : ℕ, Summable (fun j : ℕ => |a j| * (b j) ^ q)) (n : ℕ) (s : ℝ) :
    Summable (fun j : ℕ => a j * (b j * s) ^ n) :=
  Summable.of_norm_bounded ((summable_abs_abs_pow hsum n).mul_right (|s| ^ n))
    (fun j => by
      have := norm_bound_pos (a j) (b j) 1 (by simp) n s
      simpa [mul_assoc] using this)

lemma summable_rho_negpow {a b : ℕ → ℝ}
    (hsum : ∀ q : ℕ, Summable (fun j : ℕ => |a j| * (b j) ^ q)) (n : ℕ) (s : ℝ) :
    Summable (fun j : ℕ => a j * seeleyRho (b j * s) * (-(b j * s)) ^ n) :=
  Summable.of_norm_bounded ((summable_abs_abs_pow hsum n).mul_right (|s| ^ n))
    (fun j => by
      simpa [mul_assoc] using norm_bound_neg (a j) (b j) _ (seeleyRho_abs_le_one _) n s)

theorem seeleySum_taylor_eq {X E : Type*} [NormedAddCommGroup X] [NormedSpace ℝ X]
    [NormedAddCommGroup E] [NormedSpace ℝ E] {a b : ℕ → ℝ}
    (hmom : ∀ q : ℕ, ∑' j : ℕ, a j * (b j) ^ q = (-1 : ℝ) ^ q)
    (hsum : ∀ q : ℕ, Summable (fun j : ℕ => |a j| * (b j) ^ q))
    {F : X × ℝ → E} (N : ℕ) (x : X) (s : ℝ) :
    seeleySum a b (seeleyTaylor F N) (x, s) - seeleyTaylor F N (x, s)
      = - ∑ n ∈ Finset.range (N + 1),
          ((-s) ^ n * seeleyEps a b n s) • seeleyCoeff F n x := by
  have hterm : ∀ j : ℕ, a j • (seeleyRho (b j * s) • seeleyTaylor F N (x, -(b j * s)))
      = ∑ n ∈ Finset.range (N + 1),
          (a j * seeleyRho (b j * s) * (-(b j * s)) ^ n) • seeleyCoeff F n x := by
    intro j
    show a j • (seeleyRho (b j * s) •
        ∑ n ∈ Finset.range (N + 1), (-(b j * s)) ^ n • seeleyCoeff F n x) = _
    rw [Finset.smul_sum, Finset.smul_sum]
    refine Finset.sum_congr rfl (fun n _ => ?_)
    rw [smul_smul, smul_smul]
  have hsmul : ∀ n : ℕ,
      (∑' j : ℕ, (a j * seeleyRho (b j * s) * (-(b j * s)) ^ n) • seeleyCoeff F n x)
        = (∑' j : ℕ, a j * seeleyRho (b j * s) * (-(b j * s)) ^ n)
            • seeleyCoeff F n x :=
    fun n => (summable_rho_negpow hsum n s).tsum_smul_const (seeleyCoeff F n x)
  have hswap : seeleySum a b (seeleyTaylor F N) (x, s)
      = ∑ n ∈ Finset.range (N + 1),
          ∑' j : ℕ, (a j * seeleyRho (b j * s) * (-(b j * s)) ^ n) • seeleyCoeff F n x := by
    show (∑' j : ℕ, a j • (seeleyRho (b j * s) • seeleyTaylor F N (x, -(b j * s)))) = _
    rw [tsum_congr hterm]
    exact Summable.tsum_finsetSum (fun n _ =>
      (summable_rho_negpow hsum n s).smul_const _)
  have hkey : ∀ n : ℕ, (∑' j : ℕ, a j * seeleyRho (b j * s) * (-(b j * s)) ^ n)
      = s ^ n - (-s) ^ n * seeleyEps a b n s := by
    intro n
    have hsumP := summable_rho_pow hsum n s
    have hsumR := summable_oneSubRho_pow hsum n s
    have hsumQ := summable_pow hsum n s
    have h1 : (∑' j : ℕ, a j * (b j * s) ^ n)
        = (∑' j : ℕ, a j * seeleyRho (b j * s) * (b j * s) ^ n)
          + (∑' j : ℕ, a j * (1 - seeleyRho (b j * s)) * (b j * s) ^ n) := by
      rw [← hsumP.tsum_add hsumR]
      exact tsum_congr (fun j => by ring)
    have h2 : (∑' j : ℕ, a j * (b j * s) ^ n) = s ^ n * (-1 : ℝ) ^ n := by
      rw [show (fun j : ℕ => a j * (b j * s) ^ n)
          = (fun j : ℕ => (a j * (b j) ^ n) * s ^ n) from funext (fun j => by ring)]
      rw [tsum_mul_right, hmom n]
      ring
    have h3 : (∑' j : ℕ, a j * (1 - seeleyRho (b j * s)) * (b j * s) ^ n)
        = s ^ n * seeleyEps a b n s := by
      rw [show (fun j : ℕ => a j * (1 - seeleyRho (b j * s)) * (b j * s) ^ n)
          = (fun j : ℕ => (a j * (b j) ^ n * (1 - seeleyRho (b j * s))) * s ^ n)
            from funext (fun j => by ring)]
      rw [tsum_mul_right]
      exact mul_comm _ _
    have h4 : (∑' j : ℕ, a j * seeleyRho (b j * s) * (b j * s) ^ n)
        = (∑' j : ℕ, a j * (b j * s) ^ n)
          - (∑' j : ℕ, a j * (1 - seeleyRho (b j * s)) * (b j * s) ^ n) := by
      rw [h1]; ring
    have hP : (∑' j : ℕ, a j * seeleyRho (b j * s) * (-(b j * s)) ^ n)
        = (-1 : ℝ) ^ n * (∑' j : ℕ, a j * seeleyRho (b j * s) * (b j * s) ^ n) := by
      rw [← tsum_mul_left]
      exact tsum_congr (fun j => by rw [neg_pow]; ring)
    have hsq : (-1 : ℝ) ^ n * (-1) ^ n = 1 := by
      rw [← pow_add, show n + n = 2 * n by ring, pow_mul]
      norm_num
    rw [hP, h4, h2, h3]
    linear_combination (s ^ n) * hsq
  have hmain : seeleySum a b (seeleyTaylor F N) (x, s)
      = ∑ n ∈ Finset.range (N + 1),
          (s ^ n - (-s) ^ n * seeleyEps a b n s) • seeleyCoeff F n x := by
    rw [hswap]
    exact Finset.sum_congr rfl (fun n _ => by rw [hsmul n, hkey n])
  rw [hmain]
  show _ - (∑ n ∈ Finset.range (N + 1), s ^ n • seeleyCoeff F n x)
      = - ∑ n ∈ Finset.range (N + 1),
          ((-s) ^ n * seeleyEps a b n s) • seeleyCoeff F n x
  rw [show (∑ n ∈ Finset.range (N + 1),
        (s ^ n - (-s) ^ n * seeleyEps a b n s) • seeleyCoeff F n x)
      = ∑ n ∈ Finset.range (N + 1),
        (s ^ n • seeleyCoeff F n x
          - ((-s) ^ n * seeleyEps a b n s) • seeleyCoeff F n x) from
    Finset.sum_congr rfl (fun n _ => sub_smul _ _ _)]
  rw [Finset.sum_sub_distrib]
  abel

end Work.Drive
