import Mathlib
import Submission.Commons.NumberTheory.Zeta.zeta_eq_emN
import Submission.Commons.NumberTheory.Zeta.emTerm_tsum_le
import Submission.Commons.Analysis.ExponentialSums.second_derivative_test
import Submission.Work.BMF.abel_identity
import Submission.Work.BMF.zeta_approx.sdt_ioc_partial_sum

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false

set_option maxHeartbeats 1600000
open scoped BigOperators
open Finset

namespace Work.BMF

/-! ### Euler–Maclaurin truncation for ζ -/
theorem zeta_sub_Icc_sum_le {σ t : ℝ} (hσ : 0 < σ) (ht : t ≠ 0) (N : ℕ) (hN : 1 ≤ N) :
    ‖riemannZeta ((σ : ℂ) + (t : ℂ) * Complex.I) -
        ∑ n ∈ Finset.Icc 1 N, ((n : ℕ) : ℂ) ^ (-((σ : ℂ) + (t : ℂ) * Complex.I))‖
      ≤ (N : ℝ) ^ (1 - σ) / |t| + (‖((σ : ℂ) + (t : ℂ) * Complex.I)‖ / σ) * (N : ℝ) ^ (-σ) := by
  set s : ℂ := (σ : ℂ) + (t : ℂ) * Complex.I with hs
  have hsr : s.re = σ := by simp [s]
  have hsi : s.im = t := by simp [s]
  have hs0 : 0 < s.re := by rw [hsr]; exact hσ
  have hs1 : s ≠ 1 := by
    intro h
    have h2 : s.im = 0 := by simp [h]
    rw [hsi] at h2
    exact ht h2
  have hid := Commons.NumberTheory.Zeta.zeta_eq_emN (s := s) hs0 hs1 N hN
  have hsum := Commons.NumberTheory.Zeta.emTerm_tsum_le N hN s hs0 hs1
  set T : ℂ := ∑' m : ℕ, ((((N + m + 1 : ℕ) : ℂ) ^ (-s)) -
          (((((N + m + 1 : ℕ) : ℂ) ^ (1 - s)) - (((N + m : ℕ) : ℂ) ^ (1 - s))) / (1 - s))) with hT
  have hsplit : riemannZeta s - ∑ n ∈ Finset.Icc 1 N, ((n : ℕ) : ℂ) ^ (-s)
      = ((N : ℕ) : ℂ) ^ (1 - s) / (s - 1) + T := by
    rw [hid]; simp only [hT]; ring
  have htail : ‖T‖ ≤ (‖s‖ / s.re) * ((N : ℝ) ^ (-s.re)) := by
    rw [hT]
    calc ‖∑' m : ℕ, ((((N + m + 1 : ℕ) : ℂ) ^ (-s)) - (((((N + m + 1 : ℕ) : ℂ) ^ (1 - s)) - (((N + m : ℕ) : ℂ) ^ (1 - s))) / (1 - s)))‖
        ≤ ∑' m : ℕ, ‖((((N + m + 1 : ℕ) : ℂ) ^ (-s)) - (((((N + m + 1 : ℕ) : ℂ) ^ (1 - s)) - (((N + m : ℕ) : ℂ) ^ (1 - s))) / (1 - s)))‖ :=
          norm_tsum_le_tsum_norm hsum.1.norm
      _ ≤ (‖s‖ / s.re) * ((N : ℝ) ^ (-s.re)) := hsum.2
  have hNpos : (0 : ℝ) < (N : ℝ) := by exact_mod_cast (by omega : 0 < N)
  have hpow : ‖((N : ℕ) : ℂ) ^ (1 - s)‖ = (N : ℝ) ^ (1 - σ) := by
    have hcast : ((N : ℕ) : ℂ) = ((N : ℝ) : ℂ) := by push_cast; norm_num
    rw [hcast, Complex.norm_cpow_eq_rpow_re_of_pos hNpos (1 - s)]
    simp [Complex.sub_re, hsr]
  have hden : |t| ≤ ‖s - 1‖ := by
    have h1 : |(s - 1).im| ≤ ‖s - 1‖ := Complex.abs_im_le_norm (s - 1)
    have h2 : (s - 1).im = t := by simp [hsi]
    rwa [h2] at h1
  have hfirst : ‖((N : ℕ) : ℂ) ^ (1 - s) / (s - 1)‖ ≤ (N : ℝ) ^ (1 - σ) / |t| := by
    rw [norm_div, hpow]
    exact div_le_div_of_nonneg_left (Real.rpow_nonneg (le_of_lt hNpos) (1 - σ)) (abs_pos.mpr ht) hden
  rw [hsplit]
  calc ‖((N : ℕ) : ℂ) ^ (1 - s) / (s - 1) + T‖
      ≤ ‖((N : ℕ) : ℂ) ^ (1 - s) / (s - 1)‖ + ‖T‖ := norm_add_le _ _
    _ ≤ (N : ℝ) ^ (1 - σ) / |t| + (‖s‖ / s.re) * ((N : ℝ) ^ (-s.re)) := add_le_add hfirst htail
    _ = (N : ℝ) ^ (1 - σ) / |t| + (‖((σ : ℂ) + (t : ℂ) * Complex.I)‖ / σ) * (N : ℝ) ^ (-σ) := by
        rw [hsr, hs]

/-! ### Abel summation by parts on a dyadic block -/
lemma sum_Ioc_eq_sum_Icc_shift (M K : ℕ) (g : ℕ → ℂ) :
    ∑ n ∈ Finset.Ioc M (M + K), g n = ∑ h ∈ Finset.Icc 1 K, g (M + h) := by
  induction K with
  | zero => simp
  | succ K ih =>
      rw [Finset.sum_Icc_succ_top (by omega : 1 ≤ K + 1) (f := fun h => g (M + h)),
        show M + (K + 1) = (M + K) + 1 by omega,
        Finset.sum_Ioc_succ_top (by omega : M ≤ M + K) (f := g), ih]

theorem abel_ioc_block (M L : ℕ) (a : ℕ → ℂ) (b : ℕ → ℝ) (V : ℝ)
    (hML : M < L) (hV0 : 0 ≤ V)
    (hbmono : ∀ h, M ≤ h → b (h + 1) ≤ b h)
    (hbL : 0 ≤ b L) (hbM : 0 ≤ b M)
    (hV : ∀ h, M ≤ h → h ≤ L → ‖∑ h' ∈ Finset.Ioc M h, a h'‖ ≤ V) :
    ‖∑ n ∈ Finset.Ioc M L, a n * (b n : ℂ)‖ ≤ V * b M := by
  obtain ⟨K, hK⟩ : ∃ K : ℕ, M + K = L := ⟨L - M, by omega⟩
  rw [show (∑ n ∈ Finset.Ioc M L, a n * (b n : ℂ))
      = ∑ h ∈ Finset.Icc 1 K, a (M + h) * ((b (M + h) : ℝ) : ℂ) by
        rw [← hK]
        exact sum_Ioc_eq_sum_Icc_shift M K (fun n => a n * (b n : ℂ))]
  rw [abel_identity K (fun h => a (M + h)) (fun h => ((b (M + h) : ℝ) : ℂ))]
  have hbound1 : ‖(∑ h ∈ Finset.Icc 1 K, a (M + h)) * ((b (M + K) : ℝ) : ℂ)‖ ≤ V * b L := by
    rw [norm_mul, hK]
    have hsum : (∑ h ∈ Finset.Icc 1 K, a (M + h)) = ∑ n ∈ Finset.Ioc M L, a n := by
      rw [← hK]; exact (sum_Ioc_eq_sum_Icc_shift M K a).symm
    rw [hsum]
    have hnorm : ‖(((b L : ℝ)) : ℂ)‖ = b L := by simp [abs_of_nonneg hbL]
    rw [hnorm]
    exact mul_le_mul_of_nonneg_right (hV L (by omega) le_rfl) hbL
  have hbound2 : ‖∑ h ∈ Finset.range K,
      (∑ h' ∈ Finset.Icc 1 h, a (M + h')) * (((b (M + h + 1) : ℝ) : ℂ) - ((b (M + h) : ℝ) : ℂ))‖
      ≤ V * (b M - b L) := by
    have hterm : ∀ h ∈ Finset.range K,
        ‖(∑ h' ∈ Finset.Icc 1 h, a (M + h')) * (((b (M + h + 1) : ℝ) : ℂ) - ((b (M + h) : ℝ) : ℂ))‖
          ≤ V * (b (M + h) - b (M + h + 1)) := by
      intro h hh
      have hhK : h < K := Finset.mem_range.mp hh
      have hMhM : M ≤ M + h := by omega
      have hMhL : M + h ≤ L := by omega
      have hmono : b (M + h + 1) ≤ b (M + h) := hbmono (M + h) hMhM
      have hsum : (∑ h' ∈ Finset.Icc 1 h, a (M + h')) = ∑ n ∈ Finset.Ioc M (M + h), a n :=
        (sum_Ioc_eq_sum_Icc_shift M h a).symm
      rw [norm_mul, hsum]
      have h2 : ‖(((b (M + h + 1) : ℝ) : ℂ) - ((b (M + h) : ℝ) : ℂ))‖
          = b (M + h) - b (M + h + 1) := by
        have hle : b (M + h + 1) - b (M + h) ≤ 0 := by linarith
        rw [← Complex.ofReal_sub]
        rw [show ‖(((b (M + h + 1) - b (M + h) : ℝ)) : ℂ)‖
            = |b (M + h + 1) - b (M + h)| from RCLike.norm_ofReal _]
        rw [abs_of_nonpos hle]
        ring
      rw [h2]
      exact mul_le_mul_of_nonneg_right (hV (M + h) hMhM hMhL) (by linarith)
    have htel : ∑ h ∈ Finset.range K, (b (M + h) - b (M + h + 1)) = b M - b (M + K) := by
      have h1 : (∑ h ∈ Finset.range K, (b (M + h) - b (M + h + 1)))
          = ∑ h ∈ Finset.range K, (-(b (M + (h + 1))) - (-(b (M + h)))) := by
        apply Finset.sum_congr rfl
        intro h _
        ring
      rw [h1, Finset.sum_range_sub (f := fun i : ℕ => -b (M + i))]
      simp only [Nat.add_zero]
      ring
    calc ‖∑ h ∈ Finset.range K, _‖ ≤ ∑ h ∈ Finset.range K, _ := norm_sum_le _ _
      _ ≤ ∑ h ∈ Finset.range K, V * (b (M + h) - b (M + h + 1)) := Finset.sum_le_sum hterm
      _ = V * ∑ h ∈ Finset.range K, (b (M + h) - b (M + h + 1)) := by rw [Finset.mul_sum]
      _ = V * (b M - b (M + K)) := by rw [htel]
      _ = V * (b M - b L) := by rw [hK]
  calc ‖(∑ h ∈ Finset.Icc 1 K, a (M + h)) * ((b (M + K) : ℝ) : ℂ)
          - ∑ h ∈ Finset.range K, (∑ h' ∈ Finset.Icc 1 h, a (M + h')) *
              (((b (M + h + 1) : ℝ) : ℂ) - ((b (M + h) : ℝ) : ℂ))‖
        ≤ ‖(∑ h ∈ Finset.Icc 1 K, a (M + h)) * ((b (M + K) : ℝ) : ℂ)‖
          + ‖∑ h ∈ Finset.range K, (∑ h' ∈ Finset.Icc 1 h, a (M + h')) *
              (((b (M + h + 1) : ℝ) : ℂ) - ((b (M + h) : ℝ) : ℂ))‖ := norm_sub_le _ _
    _ ≤ V * b L + V * (b M - b L) := add_le_add hbound1 hbound2
    _ = V * b M := by ring

end Work.BMF

namespace Work.BMF

/-! ### pointwise identities for the complex powers -/
lemma cpow_real_split (n : ℕ) (hn : 1 ≤ n) (σ τ : ℝ) :
    ((n : ℂ) ^ (-((σ : ℂ) + (τ : ℂ) * Complex.I)))
      = (((n : ℝ) ^ (-σ) : ℝ) : ℂ) * ((n : ℂ) ^ (-(Complex.I * (τ : ℂ)))) := by
  have hc : ((n : ℂ)) ≠ 0 := by simp [Nat.cast_eq_zero]; omega
  rw [show (-((σ : ℂ) + (τ : ℂ) * Complex.I)) = (-σ : ℂ) + (-(Complex.I * (τ : ℂ))) by ring]
  rw [Complex.cpow_add _ _ hc]
  congr 1
  rw [← Complex.ofReal_natCast, ← Complex.ofReal_neg]
  exact (Complex.ofReal_cpow (Nat.cast_nonneg n) (-σ)).symm

lemma cpow_conj_of_neg (n : ℕ) (hn : 1 ≤ n) (σ τ : ℝ) (hτ : 0 < τ) :
    ((n : ℂ) ^ (-((σ : ℂ) + ((-τ : ℝ) : ℂ) * Complex.I)))
      = (starRingEnd ℂ) (((n : ℂ) ^ (-((σ : ℂ) + (τ : ℂ) * Complex.I)))) := by
  have hc : ((n : ℂ)).arg ≠ Real.pi := by
    have h2 : ((n : ℂ)) = (((n : ℝ)) : ℂ) := by simp
    rw [h2, Complex.arg_ofReal_of_nonneg (Nat.cast_nonneg n)]
    exact Real.pi_ne_zero.symm
  have h := Complex.conj_cpow ((n : ℂ)) (-((σ : ℂ) + ((-τ : ℝ) : ℂ) * Complex.I)) hc
  rw [Complex.conj_natCast] at h
  have hexp : (starRingEnd ℂ) (-((σ : ℂ) + ((-τ : ℝ) : ℂ) * Complex.I))
      = -((σ : ℂ) + (τ : ℂ) * Complex.I) := by
    rw [show (((-τ : ℝ)) : ℂ) = -((τ : ℝ) : ℂ) by simp]
    simp only [map_neg, map_add, map_mul, Complex.conj_ofReal, Complex.conj_I]
    ring
  rw [h, hexp]

/-! ### the block bound -/
theorem zeta_approx_block :
    ∃ K₁ : ℝ, 0 < K₁ ∧ ∀ (M L : ℕ) (σ τ : ℝ), 0 ≤ σ → σ ≤ 1 → 1 ≤ τ → 1 ≤ M → M < L → L ≤ 2 * M →
      ‖∑ n ∈ Finset.Ioc M L, ((n : ℂ) ^ (-((σ : ℂ) + (τ : ℂ) * Complex.I)))‖
        ≤ K₁ * (M : ℝ) ^ (-σ) * (Real.sqrt τ + (M : ℝ) / Real.sqrt τ) := by
  obtain ⟨C0, hC0pos, hC0⟩ := Commons.Analysis.ExponentialSums.second_derivative_test (B := 4) (by norm_num)
  obtain ⟨Cs, hCspos, hs⟩ :=
    zeta_approx.sdt_ioc_partial_sum ⟨C0, hC0pos, fun {a} {n} hn f r hr hf hpp => hC0 hn f hr hf hpp⟩
  refine ⟨8 * Cs, by positivity, ?_⟩
  intro M L σ τ hσ0 hσ1 hτ1 hM1 hML hL2M
  have hτ0 : 0 < τ := by linarith
  set V : ℝ := Cs * (Real.sqrt (τ / (8 * Real.pi)) + (M : ℝ) * Real.sqrt (8 * Real.pi / τ)) with hVdef
  have hV0 : 0 ≤ V := by rw [hVdef]; positivity
  have hVhyp : ∀ h, M ≤ h → h ≤ L →
      ‖∑ h' ∈ Finset.Ioc M h, ((h' : ℂ) ^ (-(Complex.I * (τ : ℂ))))‖ ≤ V := by
    intro h hMh hhL
    rcases eq_or_lt_of_le hMh with hh | hlt
    · subst hh; simp [hV0]
    · rw [hVdef]; exact hs M h τ hM1 hlt (le_trans hhL hL2M) hτ0
  have hbmono : ∀ h, M ≤ h → ((h + 1 : ℕ) : ℝ) ^ (-σ) ≤ (h : ℝ) ^ (-σ) := by
    intro h hMh
    have h1 : (0:ℝ) < (h:ℝ) := by exact_mod_cast (by omega : 0 < h)
    have h2 : (h:ℝ) ≤ ((h+1:ℕ):ℝ) := by push_cast; linarith
    exact Real.rpow_le_rpow_of_nonpos h1 h2 (by linarith)
  have hmain := abel_ioc_block M L (fun n => ((n : ℂ) ^ (-(Complex.I * (τ : ℂ)))))
      (fun n => ((n : ℝ) ^ (-σ))) V hML hV0 hbmono (by positivity) (by positivity) hVhyp
  have hpt : ∀ n ∈ Finset.Ioc M L, ((n : ℂ) ^ (-((σ : ℂ) + (τ : ℂ) * Complex.I)))
      = (((n : ℝ) ^ (-σ) : ℝ) : ℂ) * ((n : ℂ) ^ (-(Complex.I * (τ : ℂ)))) := by
    intro n hn
    have hn1 : 1 ≤ n := by have := Finset.mem_Ioc.mp hn; omega
    exact cpow_real_split n hn1 σ τ
  have hswap : ∀ n ∈ Finset.Ioc M L, (((n : ℝ) ^ (-σ) : ℝ) : ℂ) * ((n : ℂ) ^ (-(Complex.I * (τ : ℂ))))
      = ((n : ℂ) ^ (-(Complex.I * (τ : ℂ)))) * (((n : ℝ) ^ (-σ) : ℝ) : ℂ) := by
    intro n hn; ring
  have hsqrt1 : Real.sqrt (τ / (8 * Real.pi)) ≤ Real.sqrt τ := by
    apply Real.sqrt_le_sqrt
    rw [div_le_iff₀ (by positivity)]
    nlinarith [Real.pi_gt_three, hτ0]
  have hsqrt2 : Real.sqrt (8 * Real.pi / τ) ≤ 8 / Real.sqrt τ := by
    rw [Real.sqrt_div' (8 * Real.pi) (le_of_lt hτ0)]
    have h8 : Real.sqrt (8 * Real.pi) ≤ 8 := by
      nlinarith [Real.sq_sqrt (by positivity : (0:ℝ) ≤ 8 * Real.pi), Real.sqrt_nonneg (8 * Real.pi),
        Real.pi_lt_four]
    exact div_le_div_of_nonneg_right h8 (Real.sqrt_nonneg τ)
  have hlast : V * (((M : ℝ) ^ (-σ))) ≤ 8 * Cs * (M : ℝ) ^ (-σ) * (Real.sqrt τ + (M : ℝ) / Real.sqrt τ) := by
    rw [hVdef]
    have hMs : 0 ≤ (M : ℝ) ^ (-σ) := by positivity
    have hsum : Real.sqrt (τ / (8 * Real.pi)) + (M : ℝ) * Real.sqrt (8 * Real.pi / τ)
        ≤ 8 * (Real.sqrt τ + (M : ℝ) / Real.sqrt τ) := by
      have h3 : (M : ℝ) * Real.sqrt (8 * Real.pi / τ) ≤ (M : ℝ) * (8 / Real.sqrt τ) :=
        mul_le_mul_of_nonneg_left hsqrt2 (by positivity)
      have h4 : Real.sqrt τ ≤ 8 * Real.sqrt τ := by linarith [Real.sqrt_nonneg τ]
      have h5 : ((M : ℝ) * (8 / Real.sqrt τ)) = 8 * (M : ℝ) / Real.sqrt τ := by ring
      have h6 : 8 * (Real.sqrt τ + (M:ℝ)/Real.sqrt τ) = 8 * Real.sqrt τ + 8 * (M:ℝ)/Real.sqrt τ := by ring
      rw [h6]; linarith
    have h7 : Cs * (Real.sqrt (τ / (8 * Real.pi)) + (M:ℝ) * Real.sqrt (8 * Real.pi / τ))
        ≤ Cs * (8 * (Real.sqrt τ + (M:ℝ)/Real.sqrt τ)) :=
      mul_le_mul_of_nonneg_left hsum (le_of_lt hCspos)
    nlinarith [h7, hMs]
  calc ‖∑ n ∈ Finset.Ioc M L, ((n : ℂ) ^ (-((σ : ℂ) + (τ : ℂ) * Complex.I)))‖
      = ‖∑ n ∈ Finset.Ioc M L, ((((n : ℝ) ^ (-σ) : ℝ) : ℂ) * ((n : ℂ) ^ (-(Complex.I * (τ : ℂ)))))‖ := by
        congr 1; exact Finset.sum_congr rfl hpt
    _ = ‖∑ n ∈ Finset.Ioc M L, (((n : ℂ) ^ (-(Complex.I * (τ : ℂ)))) * (((n : ℝ) ^ (-σ) : ℝ) : ℂ))‖ := by
        congr 1; exact Finset.sum_congr rfl hswap
    _ ≤ V * (((M : ℝ) ^ (-σ))) := hmain
    _ ≤ 8 * Cs * (M : ℝ) ^ (-σ) * (Real.sqrt τ + (M : ℝ) / Real.sqrt τ) := hlast

end Work.BMF

namespace Work.BMF

lemma sum_Ioc_dyadic (N J : ℕ) (g : ℕ → ℂ) :
    ∑ n ∈ Finset.Ioc N (2^J * N), g n
      = ∑ k ∈ Finset.range J, ∑ n ∈ Finset.Ioc (2^k*N) (2^(k+1)*N), g n := by
  induction J with
  | zero => simp
  | succ J ih =>
    have hA : 2 ^ (J + 1) * N = 2^J*N + 2^J*N := by rw [pow_succ]; ring
    have hdisj : Disjoint (Finset.Ioc N (2^J*N)) (Finset.Ioc (2^J*N) (2^J*N + 2^J*N)) := by
      rw [Finset.disjoint_left]
      intro x hx hy
      simp only [Finset.mem_Ioc] at hx hy
      omega
    have hunion : Finset.Ioc N (2^J*N) ∪ Finset.Ioc (2^J*N) (2^J*N + 2^J*N)
        = Finset.Ioc N (2^J*N + 2^J*N) :=
      Finset.Ioc_union_Ioc_eq_Ioc (Nat.le_mul_of_pos_left N (pow_pos (by norm_num) J))
        (Nat.le_add_right _ _)
    rw [hA, Finset.sum_range_succ, ← ih, ← hunion, Finset.sum_union hdisj, hA]

lemma J_bound_of_pow_le {J : ℕ} {τ : ℝ} (hτ : 1 ≤ τ) (h : (2:ℝ)^J ≤ 32*τ) :
    (J:ℝ) ≤ 5 + 6 * τ^(3/8:ℝ) := by
  have hτ0 : 0 < τ := by linarith
  have hlog2pos : 0 < Real.log 2 := Real.log_pos (by norm_num)
  have hlog2half : (1/2:ℝ) ≤ Real.log 2 := by
    rw [Real.le_log_iff_exp_le (by norm_num : (0:ℝ) < 2)]
    have hsq : Real.exp (1/2)^2 = Real.exp 1 := by rw [pow_two, ← Real.exp_add]; norm_num
    nlinarith [Real.exp_pos (1/2), Real.exp_one_lt_three]
  have h1 : Real.log ((2:ℝ)^J) ≤ Real.log (32*τ) := Real.log_le_log (by positivity) h
  rw [Real.log_pow] at h1
  rw [Real.log_mul (by norm_num) (ne_of_gt hτ0)] at h1
  rw [show (32:ℝ) = 2^5 by norm_num, Real.log_pow] at h1
  simp only [Nat.cast_ofNat] at h1
  have h2 : Real.log τ ≤ (8/3) * τ^(3/8:ℝ) := by
    have hh := Real.log_le_rpow_div (le_of_lt hτ0) (show (0:ℝ) < 3/8 by norm_num)
    rwa [show τ ^ ((3:ℝ)/8) / ((3:ℝ)/8) = (8/3) * τ^((3:ℝ)/8) by ring] at hh
  have hX : 0 ≤ τ^(3/8:ℝ) := Real.rpow_nonneg (le_of_lt hτ0) (3/8:ℝ)
  have h3 : (J:ℝ) ≤ (5 * Real.log 2 + Real.log τ)/Real.log 2 := by
    rw [le_div_iff₀ hlog2pos]; linarith
  have h4 : (5 * Real.log 2 + Real.log τ)/Real.log 2 ≤ 5 + 6 * τ^(3/8:ℝ) := by
    rw [div_le_iff₀ hlog2pos]
    have h5 : (8/3) * τ^(3/8:ℝ) ≤ 6 * τ^(3/8:ℝ) * Real.log 2 := by nlinarith [hlog2half, hX]
    linarith
  linarith

theorem dyadic_tail_aux (K₁ : ℝ) (hK₁ : 0 < K₁)
    (hblock : ∀ (M L : ℕ) (σ τ : ℝ), 0 ≤ σ → σ ≤ 1 → 1 ≤ τ → 1 ≤ M → M < L → L ≤ 2 * M →
      ‖∑ n ∈ Finset.Ioc M L, ((n : ℂ) ^ (-((σ : ℂ) + (τ : ℂ) * Complex.I)))‖
        ≤ K₁ * (M : ℝ) ^ (-σ) * (Real.sqrt τ + (M : ℝ) / Real.sqrt τ)) :
    ∀ (σ τ : ℝ) (N J : ℕ), 15/16 ≤ σ → σ ≤ 1 → 1 ≤ τ →
      τ / 2 ≤ (N : ℝ) → (N : ℝ) ≤ τ → (2 : ℝ) ^ J ≤ 32 * τ →
      ‖∑ n ∈ Finset.Ioc N (2 ^ J * N), ((n : ℂ) ^ (-((σ : ℂ) + (τ : ℂ) * Complex.I)))‖ ≤ 400 * K₁ := by
  intro σ τ N J hσ15 hσ1 hτ1 hNge hNle h2J
  have hτ0 : 0 < τ := by linarith
  have hN1 : 1 ≤ N := by
    have h : (0:ℝ) < (N:ℝ) := by linarith
    exact Nat.one_le_iff_ne_zero.mpr (by exact_mod_cast h.ne')
  have hN0 : (0:ℝ) < (N:ℝ) := by exact_mod_cast hN1
  have hJb : (J:ℝ) ≤ 5 + 6 * τ^(3/8:ℝ) := J_bound_of_pow_le hτ1 h2J
  have hJ11 : (J:ℝ) * τ^(-(3/8:ℝ)) ≤ 11 := by
    have hpos : 0 < τ^(-(3/8:ℝ)) := Real.rpow_pos_of_pos hτ0 _
    have hmul : τ^(3/8:ℝ) * τ^(-(3/8:ℝ)) = 1 := by
      rw [← Real.rpow_add hτ0]; norm_num
    have hnonneg : 0 ≤ τ^(3/8:ℝ) := Real.rpow_nonneg (le_of_lt hτ0) _
    have hle1 : τ^(-(3/8:ℝ)) ≤ 1 := by
      calc τ^(-(3/8:ℝ)) ≤ τ^(0:ℝ) := Real.rpow_le_rpow_of_exponent_le hτ1 (by norm_num)
        _ = 1 := Real.rpow_zero τ
    nlinarith [hJb, hpos, hmul, hnonneg, hle1]
  have hblk : ∀ k, k < J →
      ‖∑ n ∈ Finset.Ioc (2^k*N) (2^(k+1)*N), ((n : ℂ) ^ (-((σ : ℂ) + (τ : ℂ) * Complex.I)))‖
        ≤ K₁ * (((2^k*N : ℕ)):ℝ)^(-σ) * (Real.sqrt τ + (((2^k*N : ℕ)):ℝ)/Real.sqrt τ) := by
    intro k hk
    have hM1 : 1 ≤ 2^k*N := Nat.one_le_iff_ne_zero.mpr (by positivity)
    have hlt : 2^k*N < 2^(k+1)*N := by
      have h : 2^k < 2^(k+1) := by
        calc 2^k < 2^k * 2 := by nlinarith [pow_pos (by norm_num : (0:ℕ) < 2) k]
          _ = 2^(k+1) := by rw [pow_succ]
      exact Nat.mul_lt_mul_of_pos_right h (by omega)
    have hle : 2^(k+1)*N ≤ 2*(2^k*N) := by
      rw [pow_succ]; nlinarith
    exact hblock (2^k*N) (2^(k+1)*N) σ τ (by linarith) hσ1 hτ1 hM1 hlt hle
  have hsum1 : (∑ k ∈ Finset.range J, (((2^k*N : ℕ)):ℝ)^(-σ)) ≤ (J:ℝ) * (N:ℝ)^(-σ) := by
    calc ∑ k ∈ Finset.range J, (((2^k*N : ℕ)):ℝ)^(-σ)
        ≤ ∑ k ∈ Finset.range J, (N:ℝ)^(-σ) := by
          apply Finset.sum_le_sum
          intro k hk
          have hle : N ≤ 2^k * N := Nat.le_mul_of_pos_left N (pow_pos (by norm_num) k)
          have hle' : (N:ℝ) ≤ (((2^k*N : ℕ)):ℝ) := by exact_mod_cast hle
          exact Real.rpow_le_rpow_of_nonpos hN0 hle' (by linarith)
      _ = (J:ℝ) * (N:ℝ)^(-σ) := by rw [Finset.sum_const, Finset.card_range, nsmul_eq_mul]
  have hsum2 : (∑ k ∈ Finset.range J, (((2^k*N : ℕ)):ℝ)^(1-σ)) ≤ (J:ℝ) * (32 * τ^2)^(1-σ) := by
    have h2JN : (((2^J*N : ℕ)):ℝ) ≤ 32 * τ^2 := by
      have h1 : (((2^J*N : ℕ)):ℝ) = (2:ℝ)^J * (N:ℝ) := by push_cast; ring
      rw [h1]; nlinarith [h2J, hNle, hτ0]
    calc ∑ k ∈ Finset.range J, (((2^k*N : ℕ)):ℝ)^(1-σ)
        ≤ ∑ k ∈ Finset.range J, (32 * τ^2)^(1-σ) := by
          apply Finset.sum_le_sum
          intro k hk
          have hkJ : k < J := Finset.mem_range.mp hk
          have hle : 2^k*N ≤ 2^J*N := by
            have : 2^k ≤ 2^J := Nat.pow_le_pow_right (by norm_num) (le_of_lt hkJ)
            exact Nat.mul_le_mul_right N this
          have hle' : (((2^k*N : ℕ)):ℝ) ≤ (((2^J*N : ℕ)):ℝ) := by exact_mod_cast hle
          exact le_trans (Real.rpow_le_rpow (by positivity) hle' (by linarith))
            (Real.rpow_le_rpow (by positivity) h2JN (by linarith))
      _ = (J:ℝ) * (32 * τ^2)^(1-σ) := by rw [Finset.sum_const, Finset.card_range, nsmul_eq_mul]
  -- numerics
  have hnum1 : Real.sqrt τ * (N:ℝ)^(-σ) ≤ 2 * τ^(-(3/8:ℝ)) := by
    have hstep : (N:ℝ)^(-σ) ≤ (τ/2)^(-σ) :=
      Real.rpow_le_rpow_of_nonpos (by linarith) hNge (by linarith)
    have h1 : Real.sqrt τ * (N:ℝ)^(-σ) ≤ Real.sqrt τ * (τ/2)^(-σ) :=
      mul_le_mul_of_nonneg_left hstep (Real.sqrt_nonneg τ)
    have h2 : Real.sqrt τ * (τ/2)^(-σ) = (2:ℝ)^σ * τ^(1/2 - σ) := by
      rw [Real.sqrt_eq_rpow, Real.div_rpow (le_of_lt hτ0) (by norm_num : (0:ℝ) ≤ 2),
        Real.rpow_neg (by norm_num : (0:ℝ) ≤ 2) σ, div_inv_eq_mul]
      rw [show τ^(1/2:ℝ) * (τ^(-σ) * (2:ℝ)^σ) = (τ^(1/2:ℝ) * τ^(-σ)) * (2:ℝ)^σ by ring]
      rw [← Real.rpow_add hτ0]
      ring
    have h3 : (2:ℝ)^σ * τ^(1/2 - σ) ≤ 2 * τ^(-(3/8:ℝ)) := by
      have h2s : (2:ℝ)^σ ≤ 2 := by
        calc (2:ℝ)^σ ≤ (2:ℝ)^(1:ℝ) := Real.rpow_le_rpow_of_exponent_le (by norm_num) hσ1
          _ = 2 := Real.rpow_one 2
      have hτe : τ^(1/2 - σ) ≤ τ^(-(3/8:ℝ)) :=
        Real.rpow_le_rpow_of_exponent_le hτ1 (by linarith)
      exact mul_le_mul h2s hτe (Real.rpow_nonneg (le_of_lt hτ0) _) (by norm_num)
    linarith
  have hnum2 : (32 * τ^2)^(1-σ) / Real.sqrt τ ≤ 32 * τ^(-(3/8:ℝ)) := by
    have hA : (32 * τ^2)^(1-σ) = (32:ℝ)^(1-σ) * τ^(2*(1-σ)) := by
      rw [Real.mul_rpow (by norm_num) (by positivity : (0:ℝ) ≤ τ^2)]
      congr 1
      rw [← Real.rpow_natCast τ 2, ← Real.rpow_mul (le_of_lt hτ0),
        show ((2:ℕ):ℝ) * (1-σ) = 2*(1-σ) by push_cast; ring]
    rw [hA, Real.sqrt_eq_rpow, div_le_iff₀ (Real.rpow_pos_of_pos hτ0 _)]
    have h32 : (32:ℝ)^(1-σ) ≤ 32 := by
      calc (32:ℝ)^(1-σ) ≤ (32:ℝ)^(1:ℝ) := Real.rpow_le_rpow_of_exponent_le (by norm_num) (by linarith)
        _ = 32 := Real.rpow_one 32
    have hτe : τ^(2*(1-σ)) ≤ τ^(-(3/8:ℝ) + 1/2) :=
      Real.rpow_le_rpow_of_exponent_le hτ1 (by linarith)
    calc (32:ℝ)^(1-σ) * τ^(2*(1-σ)) ≤ 32 * τ^(-(3/8:ℝ) + 1/2) :=
          mul_le_mul h32 hτe (Real.rpow_nonneg (le_of_lt hτ0) _) (by norm_num)
      _ = 32 * τ^(-(3/8:ℝ)) * τ^(1/2:ℝ) := by rw [Real.rpow_add hτ0]; ring
  have hpt : ∀ k, K₁ * (((2^k*N : ℕ)):ℝ)^(-σ)
        * (Real.sqrt τ + (((2^k*N : ℕ)):ℝ)/Real.sqrt τ)
      = K₁ * (Real.sqrt τ * (((2^k*N : ℕ)):ℝ)^(-σ)
        + (((2^k*N : ℕ)):ℝ)^(1-σ)/Real.sqrt τ) := by
    intro k
    have hpos : (0:ℝ) < (((2^k*N : ℕ)):ℝ) := by
      have : 0 < 2^k*N := by positivity
      exact_mod_cast this
    have hrw : (((2^k*N : ℕ)):ℝ)^(-σ) * (((2^k*N : ℕ)):ℝ) = (((2^k*N : ℕ)):ℝ)^(1-σ) := by
      calc (((2^k*N : ℕ)):ℝ)^(-σ) * (((2^k*N : ℕ)):ℝ)
          = (((2^k*N : ℕ)):ℝ)^(-σ) * (((2^k*N : ℕ)):ℝ)^(1:ℝ) := by rw [Real.rpow_one]
        _ = (((2^k*N : ℕ)):ℝ)^((-σ) + 1) :=
            (Real.rpow_add hpos (-σ) 1).symm
        _ = (((2^k*N : ℕ)):ℝ)^(1-σ) := by congr 1; ring
    have hL : (((2^k*N : ℕ)):ℝ)^(-σ) * ((((2^k*N : ℕ)):ℝ)/Real.sqrt τ)
        = (((2^k*N : ℕ)):ℝ)^(1-σ)/Real.sqrt τ := by
      rw [show (((2^k*N : ℕ)):ℝ)^(-σ) * ((((2^k*N : ℕ)):ℝ)/Real.sqrt τ)
          = ((((2^k*N : ℕ)):ℝ)^(-σ) * (((2^k*N : ℕ)):ℝ))/Real.sqrt τ by ring, hrw]
    calc K₁ * (((2^k*N : ℕ)):ℝ)^(-σ)
            * (Real.sqrt τ + (((2^k*N : ℕ)):ℝ)/Real.sqrt τ)
        = K₁ * ((((2^k*N : ℕ)):ℝ)^(-σ) * Real.sqrt τ)
          + K₁ * ((((2^k*N : ℕ)):ℝ)^(-σ) * ((((2^k*N : ℕ)):ℝ)/Real.sqrt τ)) := by ring
      _ = K₁ * (Real.sqrt τ * (((2^k*N : ℕ)):ℝ)^(-σ))
          + K₁ * ((((2^k*N : ℕ)):ℝ)^(1-σ)/Real.sqrt τ) := by rw [hL]; ring
      _ = K₁ * (Real.sqrt τ * (((2^k*N : ℕ)):ℝ)^(-σ)
          + (((2^k*N : ℕ)):ℝ)^(1-σ)/Real.sqrt τ) := by ring
  rw [sum_Ioc_dyadic N J (fun n => ((n : ℂ) ^ (-((σ : ℂ) + (τ : ℂ) * Complex.I))))]
  calc ‖∑ k ∈ Finset.range J, ∑ n ∈ Finset.Ioc (2^k*N) (2^(k+1)*N),
          ((n : ℂ) ^ (-((σ : ℂ) + (τ : ℂ) * Complex.I)))‖
      ≤ ∑ k ∈ Finset.range J, ‖∑ n ∈ Finset.Ioc (2^k*N) (2^(k+1)*N),
          ((n : ℂ) ^ (-((σ : ℂ) + (τ : ℂ) * Complex.I)))‖ := norm_sum_le _ _
    _ ≤ ∑ k ∈ Finset.range J, K₁ * (((2^k*N : ℕ)):ℝ)^(-σ)
          * (Real.sqrt τ + (((2^k*N : ℕ)):ℝ)/Real.sqrt τ) :=
        Finset.sum_le_sum (fun k hk => hblk k (Finset.mem_range.mp hk))
    _ = K₁ * ∑ k ∈ Finset.range J, (Real.sqrt τ * (((2^k*N : ℕ)):ℝ)^(-σ)
          + (((2^k*N : ℕ)):ℝ)^(1-σ)/Real.sqrt τ) := by
        rw [Finset.mul_sum]
        exact Finset.sum_congr rfl (fun k hk => hpt k)
    _ = K₁ * (Real.sqrt τ * (∑ k ∈ Finset.range J, (((2^k*N : ℕ)):ℝ)^(-σ))
          + (∑ k ∈ Finset.range J, (((2^k*N : ℕ)):ℝ)^(1-σ))/Real.sqrt τ) := by
        rw [Finset.sum_add_distrib, Finset.mul_sum, Finset.sum_div]
    _ ≤ K₁ * (Real.sqrt τ * ((J:ℝ) * (N:ℝ)^(-σ))
          + ((J:ℝ) * (32 * τ^2)^(1-σ))/Real.sqrt τ) := by
        have h1 := mul_le_mul_of_nonneg_left hsum1 (Real.sqrt_nonneg τ)
        have h2 := div_le_div_of_nonneg_right hsum2 (Real.sqrt_nonneg τ)
        nlinarith [h1, h2, hK₁]
    _ ≤ K₁ * ((J:ℝ) * (2 * τ^(-(3/8:ℝ))) + (J:ℝ) * (32 * τ^(-(3/8:ℝ)))) := by
        have h1 : Real.sqrt τ * ((J:ℝ) * (N:ℝ)^(-σ)) ≤ (J:ℝ) * (2 * τ^(-(3/8:ℝ))) := by
          rw [show Real.sqrt τ * ((J:ℝ) * (N:ℝ)^(-σ)) = (J:ℝ) * ((N:ℝ)^(-σ) * Real.sqrt τ) by ring]
          exact mul_le_mul_of_nonneg_left (by rw [mul_comm]; exact hnum1) (Nat.cast_nonneg J)
        have h2 : ((J:ℝ) * (32 * τ^2)^(1-σ))/Real.sqrt τ ≤ (J:ℝ) * (32 * τ^(-(3/8:ℝ))) := by
          rw [show ((J:ℝ) * (32 * τ^2)^(1-σ))/Real.sqrt τ
              = (J:ℝ) * ((32 * τ^2)^(1-σ)/Real.sqrt τ) by ring]
          exact mul_le_mul_of_nonneg_left hnum2 (Nat.cast_nonneg J)
        nlinarith [h1, h2, hK₁]
    _ = K₁ * (J:ℝ) * 34 * τ^(-(3/8:ℝ)) := by ring
    _ ≤ K₁ * 11 * 34 := by
        have hpos : 0 < τ^(-(3/8:ℝ)) := Real.rpow_pos_of_pos hτ0 _
        nlinarith [hJ11, hK₁]
    _ ≤ 400 * K₁ := by nlinarith [hK₁]

/-- Dyadic block decomposition of the tail sum, assembled from `dyadic_tail_aux`. -/
theorem dyadic_tail (K₁ : ℝ) (hK₁ : 0 < K₁)
    (hblock : ∀ (M L : ℕ) (σ τ : ℝ), 0 ≤ σ → σ ≤ 1 → 1 ≤ τ → 1 ≤ M → M < L → L ≤ 2 * M →
      ‖∑ n ∈ Finset.Ioc M L, ((n : ℂ) ^ (-((σ : ℂ) + (τ : ℂ) * Complex.I)))‖
        ≤ K₁ * (M : ℝ) ^ (-σ) * (Real.sqrt τ + (M : ℝ) / Real.sqrt τ)) :
    ∃ K : ℝ, 0 < K ∧ ∀ (σ τ : ℝ) (N J : ℕ), 15 / 16 ≤ σ → σ ≤ 1 → 1 ≤ τ →
      τ / 2 ≤ (N : ℝ) → (N : ℝ) ≤ τ → (2 : ℝ) ^ J ≤ 32 * τ →
      ‖∑ n ∈ Finset.Ioc N (2 ^ J * N), ((n : ℂ) ^ (-((σ : ℂ) + (τ : ℂ) * Complex.I)))‖ ≤ K :=
  ⟨400 * K₁, by positivity, dyadic_tail_aux K₁ hK₁ hblock⟩

end Work.BMF

namespace Work.BMF

theorem zeta_approx_functional_eq :
    ∃ C T₀ : ℝ, 0 < C ∧ 0 < T₀ ∧ ∀ σ t : ℝ, 15/16 ≤ σ → σ ≤ 1 → T₀ ≤ |t| →
      ‖riemannZeta ((σ : ℂ) + (t : ℂ) * Complex.I)
        - ∑ n ∈ Finset.Icc 1 ⌊|t|⌋₊, ((n : ℂ) ^ (-((σ : ℂ) + (t : ℂ) * Complex.I)))‖ ≤ C := by
  classical
  obtain ⟨K₁, hK₁pos, hblock⟩ := zeta_approx_block
  obtain ⟨K, hKpos, htail⟩ := dyadic_tail K₁ hK₁pos hblock
  refine ⟨K + 18, 100, by positivity, by norm_num, ?_⟩
  intro σ t hσ15 hσ1 hT
  have hσpos : 0 < σ := by linarith
  set τ : ℝ := |t| with hτdef
  have hτ1 : 1 ≤ τ := by rw [hτdef]; linarith
  have hτ0 : 0 < τ := by linarith
  have ht0 : t ≠ 0 := by intro h; rw [h, abs_zero] at hτdef; linarith
  set N : ℕ := ⌊|t|⌋₊ with hNdef
  have hNle : (N : ℝ) ≤ τ := by rw [hNdef, hτdef]; exact Nat.floor_le (abs_nonneg t)
  have hN1 : 1 ≤ N := by
    have h100 : 100 ≤ N := by
      rw [hNdef]
      exact Nat.le_floor (by rw [hτdef] at hT; exact_mod_cast hT)
    omega
  have hN1r : (1:ℝ) ≤ (N:ℝ) := by exact_mod_cast hN1
  have hNge : τ / 2 ≤ (N : ℝ) := by
    have h := Nat.lt_floor_add_one |t|
    rw [← hNdef] at h
    have h1 : (1:ℝ) ≤ (N:ℝ) := by exact_mod_cast hN1
    rw [hτdef]
    linarith
  set X : ℝ := 4 * (σ^2 + τ^2) with hXdef
  have hex : ∃ J : ℕ, X ≤ (N : ℝ) * 2 ^ J := by
    obtain ⟨J, hJ⟩ := pow_unbounded_of_one_lt X (show (1:ℝ) < 2 by norm_num)
    refine ⟨J, le_trans (le_of_lt hJ) ?_⟩
    have h2J0 : (0:ℝ) ≤ (2:ℝ)^J := by positivity
    nlinarith [hN1r, h2J0]
  let J := Nat.find hex
  have hJspec : X ≤ (N : ℝ) * 2 ^ J := Nat.find_spec hex
  have hJprev : ∀ k < J, ¬ (X ≤ (N : ℝ) * 2 ^ k) := fun k hk => Nat.find_min hex hk
  have hJ1 : 1 ≤ J := by
    rw [Nat.one_le_iff_ne_zero]
    intro hJ0
    have h1 : X ≤ (N : ℝ) := by simpa [hJ0] using hJspec
    have h2 : 4 * τ^2 ≤ X := by rw [hXdef]; nlinarith [sq_nonneg σ]
    have h3 : 4 * τ^2 ≤ (N:ℝ) := le_trans h2 h1
    nlinarith [h3, hNle, hτ1]
  set N₀ : ℕ := 2 ^ J * N with hN₀def
  have hN₀cast : (N₀ : ℝ) = (N : ℝ) * 2 ^ J := by
    rw [hN₀def]; push_cast; ring
  have hN₀min : X ≤ (N₀ : ℝ) := by rw [hN₀cast]; exact hJspec
  have hN₀max : (N₀ : ℝ) ≤ 8 * (σ^2 + τ^2) := by
    have hprev := hJprev (J - 1) (by omega)
    have hlt : (N : ℝ) * (2:ℝ) ^ (J - 1) < X := lt_of_not_ge hprev
    have hJeq : (2:ℝ)^J = 2 * (2:ℝ)^(J-1) := by
      conv_lhs => rw [show J = (J-1)+1 by omega]
      rw [pow_succ]
      ring
    rw [hXdef] at hlt
    rw [hN₀cast, hJeq]
    nlinarith [hlt]
  have h2J : (2:ℝ)^J ≤ 32 * τ := by
    have h1 : (N:ℝ) * (2:ℝ)^J ≤ 16 * τ^2 := by
      have hσ2 : σ^2 ≤ τ^2 := by nlinarith [hσ1, hτ1]
      linarith [hN₀max]
    have h2 : (τ/2) * (2:ℝ)^J ≤ (N:ℝ) * (2:ℝ)^J := by
      have h2J0 : (0:ℝ) ≤ (2:ℝ)^J := by positivity
      nlinarith [hNge, h2J0]
    nlinarith [h1, h2, hτ0]
  -- the tail sum, with the parameter τ = |t|
  have htail' : ‖∑ n ∈ Finset.Ioc N (2 ^ J * N),
      ((n : ℂ) ^ (-((σ : ℂ) + (τ : ℂ) * Complex.I)))‖ ≤ K :=
    htail σ τ N J hσ15 hσ1 hτ1 hNge hNle h2J
  have hN₀N : N₀ = 2 ^ J * N := hN₀def
  -- switch the parameter back to `t`
  have hconj : ‖∑ n ∈ Finset.Ioc N (2 ^ J * N), ((n : ℂ) ^ (-((σ : ℂ) + (t : ℂ) * Complex.I)))‖
      = ‖∑ n ∈ Finset.Ioc N (2 ^ J * N), ((n : ℂ) ^ (-((σ : ℂ) + (τ : ℂ) * Complex.I)))‖ := by
    by_cases ht : 0 ≤ t
    · have hτt : τ = t := by rw [hτdef, abs_of_nonneg ht]
      rw [hτt]
    · have htlt : t < 0 := lt_of_not_ge ht
      have hτt : τ = -t := by rw [hτdef, abs_of_neg htlt]
      have key : ∀ n ∈ Finset.Ioc N (2 ^ J * N),
          ((n : ℂ) ^ (-((σ : ℂ) + (t : ℂ) * Complex.I)))
            = (starRingEnd ℂ) (((n : ℂ) ^ (-((σ : ℂ) + (τ : ℂ) * Complex.I)))) := by
        intro n hn
        have hn1 : 1 ≤ n := by have := Finset.mem_Ioc.mp hn; omega
        have h := cpow_conj_of_neg n hn1 σ τ hτ0
        rw [hτt] at h ⊢
        simpa [Complex.ofReal_neg] using h
      have hkey2 : (∑ x ∈ Finset.Ioc N (2 ^ J * N), (starRingEnd ℂ)
            (((x : ℂ) ^ (-((σ : ℂ) + (τ : ℂ) * Complex.I)))))
          = (starRingEnd ℂ) (∑ x ∈ Finset.Ioc N (2 ^ J * N),
            ((x : ℂ) ^ (-((σ : ℂ) + (τ : ℂ) * Complex.I)))) :=
        (map_sum (starRingEnd ℂ)
          (fun x : ℕ => ((x : ℂ) ^ (-((σ : ℂ) + (τ : ℂ) * Complex.I))))
          (Finset.Ioc N (2 ^ J * N))).symm
      rw [Finset.sum_congr rfl key, hkey2, Complex.norm_conj]
  have htail'' : ‖∑ n ∈ Finset.Ioc N N₀, ((n : ℂ) ^ (-((σ : ℂ) + (t : ℂ) * Complex.I)))‖ ≤ K := by
    rw [hN₀N, hconj]; exact htail'
  -- Euler–Maclaurin
  have hN₀1 : 1 ≤ N₀ := by rw [hN₀def]; exact Nat.one_le_iff_ne_zero.mpr (by positivity)
  have hEM := zeta_sub_Icc_sum_le (σ := σ) (t := t) hσpos ht0 N₀ hN₀1
  -- numeric bounds
  have hmid : (N₀ : ℝ) ^ (1 - σ) / |t| ≤ 16 := by
    rw [← hτdef]
    have hσ2 : σ^2 ≤ τ^2 := by nlinarith [hσ1, hτ1]
    have h1 : (N₀:ℝ)^(1-σ) ≤ (16 * τ^2)^(1-σ) :=
      Real.rpow_le_rpow (by positivity) (by linarith [hN₀max]) (by linarith)
    have h2 : (16 * τ^2 : ℝ)^(1-σ) = 16^(1-σ) * τ^(2*(1-σ)) := by
      rw [Real.mul_rpow (by norm_num) (by positivity : (0:ℝ) ≤ τ^2)]
      congr 1
      rw [← Real.rpow_natCast τ 2, ← Real.rpow_mul (le_of_lt hτ0),
        show ((2:ℕ):ℝ) * (1-σ) = 2*(1-σ) by push_cast; ring]
    have h3 : (16:ℝ)^(1-σ) ≤ 16 := by
      simpa using Real.rpow_le_rpow_of_exponent_le (show (1:ℝ) ≤ 16 by norm_num) (show 1 - σ ≤ 1 by linarith)
    have h4 : τ^(2*(1-σ)) / τ ≤ 1 := by
      rw [← Real.rpow_sub_one (ne_of_gt hτ0) (2*(1-σ))]
      have he : 2*(1-σ) - 1 = 1 - 2*σ := by ring
      rw [he]
      calc τ^(1-2*σ) ≤ τ^0 := Real.rpow_le_rpow_of_exponent_le hτ1 (by linarith)
        _ = 1 := Real.rpow_zero τ
    calc (N₀:ℝ)^(1-σ)/τ ≤ (16*τ^2)^(1-σ)/τ := div_le_div_of_nonneg_right h1 (le_of_lt hτ0)
      _ = 16^(1-σ) * (τ^(2*(1-σ))/τ) := by rw [h2]; ring
      _ ≤ 16 * 1 := mul_le_mul h3 h4 (div_nonneg (Real.rpow_nonneg (le_of_lt hτ0) _) (le_of_lt hτ0)) (by norm_num)
      _ = 16 := by norm_num
  have htailb : (‖((σ : ℂ) + (t : ℂ) * Complex.I)‖ / σ) * (N₀ : ℝ) ^ (-σ) ≤ 2 := by
    have hsnorm_nonneg : (0:ℝ) ≤ ‖((σ : ℂ) + (t : ℂ) * Complex.I)‖ := norm_nonneg _
    have hs2 : ‖((σ : ℂ) + (t : ℂ) * Complex.I)‖^2 = σ^2 + τ^2 := by
      rw [Complex.sq_norm, Complex.normSq_apply]
      simp only [Complex.add_re, Complex.add_im, Complex.ofReal_re, Complex.ofReal_im,
        Complex.mul_re, Complex.mul_im, Complex.I_re, Complex.I_im, hτdef, sq_abs]
      ring
    have hu1 : 1 ≤ σ^2 + τ^2 := by nlinarith [sq_nonneg σ, hτ1]
    have hsge1 : 1 ≤ ‖((σ : ℂ) + (t : ℂ) * Complex.I)‖ := by
      nlinarith [hsnorm_nonneg, hs2, hu1]
    have hN₀ge : 4 * (σ^2 + τ^2) ≤ (N₀ : ℝ) := by rw [hXdef] at hN₀min; linarith
    have h1 : (N₀:ℝ)^(-σ) ≤ (4*(σ^2+τ^2))^(-σ) :=
      Real.rpow_le_rpow_of_nonpos (by positivity) hN₀ge (by linarith)
    have hkey : ‖((σ : ℂ) + (t : ℂ) * Complex.I)‖ * (σ^2+τ^2)^(-σ) ≤ 1 := by
      have hu : (σ^2+τ^2) = ‖((σ : ℂ) + (t : ℂ) * Complex.I)‖^2 := hs2.symm
      have hu0 : 0 < σ^2+τ^2 := by linarith
      have hroot : (σ^2+τ^2)^((1:ℝ)/2) = ‖((σ : ℂ) + (t : ℂ) * Complex.I)‖ := by
        rw [hu, ← Real.sqrt_eq_rpow, Real.sqrt_sq (norm_nonneg _)]
      rw [← hroot]
      calc (σ^2+τ^2)^((1:ℝ)/2) * (σ^2+τ^2)^(-σ)
          = (σ^2+τ^2)^((1:ℝ)/2 + (-σ)) := by rw [Real.rpow_add hu0]
        _ ≤ (σ^2+τ^2)^(0:ℝ) :=
            Real.rpow_le_rpow_of_exponent_le hu1 (by linarith)
        _ = 1 := Real.rpow_zero _
    have h4 : (4:ℝ)^(-σ) ≤ 1 := by
      calc (4:ℝ)^(-σ) ≤ (4:ℝ)^(0:ℝ) := Real.rpow_le_rpow_of_exponent_le (by norm_num) (by linarith)
        _ = 1 := Real.rpow_zero 4
    have hprod : (4*(σ^2+τ^2))^(-σ) = (4:ℝ)^(-σ) * (σ^2+τ^2)^(-σ) :=
      Real.mul_rpow (by norm_num) (by positivity)
    calc (‖((σ : ℂ) + (t : ℂ) * Complex.I)‖ / σ) * (N₀ : ℝ) ^ (-σ)
        ≤ (‖((σ : ℂ) + (t : ℂ) * Complex.I)‖ / σ) * (4*(σ^2+τ^2))^(-σ) :=
          mul_le_mul_of_nonneg_left h1 (by positivity)
      _ = (1/σ) * ((4:ℝ)^(-σ) * (‖((σ : ℂ) + (t : ℂ) * Complex.I)‖ * (σ^2+τ^2)^(-σ))) := by
          rw [hprod]; field_simp
      _ ≤ (1/σ) * (1 * 1) := by
          apply mul_le_mul_of_nonneg_left _ (by positivity)
          exact mul_le_mul h4 hkey (by positivity) (by norm_num)
      _ ≤ 2 := by
          rw [mul_one, mul_one]
          have : (1:ℝ)/σ ≤ 16/15 := by rw [div_le_iff₀ hσpos]; linarith
          linarith
  have hEM' : ‖riemannZeta ((σ : ℂ) + (t : ℂ) * Complex.I)
      - ∑ n ∈ Finset.Icc 1 N₀, ((n : ℂ) ^ (-((σ : ℂ) + (t : ℂ) * Complex.I)))‖ ≤ 18 := by
    refine le_trans hEM ?_
    linarith [hmid, htailb]
  -- split the finite sums
  have hNN₀ : N ≤ N₀ := by
    rw [hN₀def]
    exact Nat.le_mul_of_pos_left N (pow_pos (by norm_num) J)
  have hIcc : Finset.Icc 1 N₀ = Finset.Icc 1 N ∪ Finset.Ioc N N₀ := by
    ext n
    simp only [Finset.mem_Icc, Finset.mem_union, Finset.mem_Ioc]
    constructor <;> intro h <;> omega
  have hdisj : Disjoint (Finset.Icc 1 N) (Finset.Ioc N N₀) := by
    rw [Finset.disjoint_left]
    intro x hx hy
    simp only [Finset.mem_Icc] at hx
    simp only [Finset.mem_Ioc] at hy
    omega
  have hsumsplit : (∑ n ∈ Finset.Icc 1 N₀, ((n : ℂ) ^ (-((σ : ℂ) + (t : ℂ) * Complex.I))))
      = (∑ n ∈ Finset.Icc 1 N, ((n : ℂ) ^ (-((σ : ℂ) + (t : ℂ) * Complex.I))))
        + ∑ n ∈ Finset.Ioc N N₀, ((n : ℂ) ^ (-((σ : ℂ) + (t : ℂ) * Complex.I))) := by
    rw [hIcc, Finset.sum_union hdisj]
  have hdecomp : riemannZeta ((σ : ℂ) + (t : ℂ) * Complex.I)
        - ∑ n ∈ Finset.Icc 1 N, ((n : ℂ) ^ (-((σ : ℂ) + (t : ℂ) * Complex.I)))
      = (riemannZeta ((σ : ℂ) + (t : ℂ) * Complex.I)
          - ∑ n ∈ Finset.Icc 1 N₀, ((n : ℂ) ^ (-((σ : ℂ) + (t : ℂ) * Complex.I))))
        + ∑ n ∈ Finset.Ioc N N₀, ((n : ℂ) ^ (-((σ : ℂ) + (t : ℂ) * Complex.I))) := by
    rw [hsumsplit]; ring
  calc ‖riemannZeta ((σ : ℂ) + (t : ℂ) * Complex.I)
        - ∑ n ∈ Finset.Icc 1 N, ((n : ℂ) ^ (-((σ : ℂ) + (t : ℂ) * Complex.I)))‖
      = ‖(riemannZeta ((σ : ℂ) + (t : ℂ) * Complex.I)
          - ∑ n ∈ Finset.Icc 1 N₀, ((n : ℂ) ^ (-((σ : ℂ) + (t : ℂ) * Complex.I))))
        + ∑ n ∈ Finset.Ioc N N₀, ((n : ℂ) ^ (-((σ : ℂ) + (t : ℂ) * Complex.I)))‖ := by
        rw [hdecomp]
    _ ≤ ‖riemannZeta ((σ : ℂ) + (t : ℂ) * Complex.I)
          - ∑ n ∈ Finset.Icc 1 N₀, ((n : ℂ) ^ (-((σ : ℂ) + (t : ℂ) * Complex.I)))‖
        + ‖∑ n ∈ Finset.Ioc N N₀, ((n : ℂ) ^ (-((σ : ℂ) + (t : ℂ) * Complex.I)))‖ :=
        norm_add_le _ _
    _ ≤ 18 + K := add_le_add hEM' htail''
    _ ≤ K + 18 := by linarith

end Work.BMF

