import Mathlib
import Submission.Work.ZeroDensity.LogFree.Defs
import Submission.Work.LinnikAreas.JutilaPieces.LFunctionCritLineBound
import Submission.Commons.NumberTheory.Zeta.zeta_eq_emN
import Submission.Commons.NumberTheory.Zeta.emTerm_tsum_le
import Submission.Commons.Analysis.SpecialFunctions.Gamma.gamma_one_add_mul_I_prod_norm

open DirichletCharacter Complex
open scoped BigOperators

noncomputable section

namespace Work.ZeroDensity.LogFree

/-- `ζ` is bounded on the compact segment `{iy : |y| ≤ 1}`. -/
theorem zetaImagAxis_small_bound :
    ∃ C : ℝ, ∀ y : ℝ, |y| ≤ 1 → ‖riemannZeta ((y : ℂ) * Complex.I)‖ ≤ C := by
  have hK : IsCompact ((fun y : ℝ => (y : ℂ) * Complex.I) '' Set.Icc (-1) 1) :=
    isCompact_Icc.image (by fun_prop)
  have hsub : ((fun y : ℝ => (y : ℂ) * Complex.I) '' Set.Icc (-1) 1) ⊆ ({1} : Set ℂ)ᶜ := by
    rintro z ⟨y, hy, rfl⟩
    simp only [Set.mem_compl_iff, Set.mem_singleton_iff]
    intro hz
    have hre : (0 : ℝ) = 1 := by
      have := congrArg Complex.re hz
      simpa using this
    exact zero_ne_one hre
  obtain ⟨C, hC⟩ := hK.exists_bound_of_continuousOn
    ((differentiableOn_riemannZeta.mono hsub).continuousOn)
  exact ⟨C, fun y hy => hC ((y : ℂ) * Complex.I) ⟨y, abs_le.mp hy, rfl⟩⟩

/-- `‖Γ(1 - iy)‖² = π|y|/sinh(π|y|)` for `y ≠ 0`. -/
theorem gammaOneSubI_normSq (y : ℝ) (hy : y ≠ 0) :
    ‖Complex.Gamma (1 - (y : ℂ) * Complex.I)‖ ^ 2 =
      Real.pi * |y| / Real.sinh (Real.pi * |y|) := by
  have h := Commons.Analysis.SpecialFunctions.Gamma.gamma_one_add_mul_I_prod_norm y hy
  have h' : ‖Complex.Gamma ((1 : ℂ) + (y : ℂ) * Complex.I)‖
      * ‖Complex.Gamma ((1 : ℂ) - (y : ℂ) * Complex.I)‖
      = Real.pi * |y| / Real.sinh (Real.pi * |y|) := by
    rw [show (1:ℂ) + (y:ℂ) * Complex.I = (1:ℂ) + I * (y:ℂ) by ring,
      show (1:ℂ) - (y:ℂ) * Complex.I = (1:ℂ) - I * (y:ℂ) by ring]
    exact h
  have hstar : (starRingEnd ℂ) ((1 : ℂ) + (y : ℂ) * Complex.I) = (1 : ℂ) - (y : ℂ) * Complex.I := by
    rw [sub_eq_add_neg, map_add, map_mul, map_one, Complex.conj_I, Complex.conj_ofReal]
    ring
  have hconj : ‖Complex.Gamma ((1 : ℂ) + (y : ℂ) * Complex.I)‖
      = ‖Complex.Gamma ((1 : ℂ) - (y : ℂ) * Complex.I)‖ := by
    have hg := Complex.Gamma_conj ((1 : ℂ) + (y : ℂ) * Complex.I)
    rw [hstar] at hg
    rw [hg, Complex.norm_conj]
  rw [hconj] at h'
  rw [sq]
  exact h'

/-- `‖cos(π(1-iy)/2)‖ = sinh(π|y|/2)`. -/
theorem cosHalf_norm (y : ℝ) :
    ‖Complex.cos ((Real.pi : ℂ) * (1 - (y : ℂ) * Complex.I) / 2)‖
      = Real.sinh (Real.pi * |y| / 2) := by
  have harg : (Real.pi : ℂ) * (1 - (y : ℂ) * Complex.I) / 2
      = (Real.pi : ℂ) / 2 - (((Real.pi * y / 2 : ℝ)) : ℂ) * Complex.I := by
    push_cast
    ring
  rw [harg]
  have h1 : Complex.cos ((Real.pi : ℂ) / 2 - (((Real.pi * y / 2 : ℝ)) : ℂ) * Complex.I)
      = Complex.sin ((((Real.pi * y / 2 : ℝ)) : ℂ) * Complex.I) := by
    rw [sub_eq_add_neg, Complex.cos_add, Complex.cos_pi_div_two, Complex.sin_pi_div_two,
      zero_mul, one_mul, zero_sub, Complex.sin_neg, neg_neg]
  rw [h1, Complex.sin_mul_I, ← Complex.ofReal_sinh]
  rw [norm_mul, Complex.norm_I, mul_one, Complex.norm_real, Real.norm_eq_abs, Real.abs_sinh]
  congr 1
  have h2 : |Real.pi * y / 2| = Real.pi * |y| / 2 := by
    rw [abs_div, abs_mul, abs_of_pos Real.pi_pos]
    norm_num
  exact h2

/-- The functional-equation factor `2(2π)^{-s}Γ(s)cos(πs/2)` at `s = 1 - iy` is `≤ √|y|`. -/
theorem feFactorBound (y : ℝ) (hy : 1 ≤ |y|) :
    ‖(2 : ℂ) * (2 * (Real.pi : ℂ)) ^ (-(1 - (y : ℂ) * Complex.I))
        * Complex.Gamma (1 - (y : ℂ) * Complex.I)
        * Complex.cos ((Real.pi : ℂ) * (1 - (y : ℂ) * Complex.I) / 2)‖ ≤ Real.sqrt |y| := by
  have hy0 : y ≠ 0 := by
    intro h; rw [h] at hy; norm_num at hy
  have habs : (0 : ℝ) < |y| := abs_pos.mpr hy0
  have hΓ := gammaOneSubI_normSq y hy0
  have hcos := cosHalf_norm y
  have hbase : (((2 * Real.pi : ℝ)) : ℂ) = (2 : ℂ) * (Real.pi : ℂ) := by
    rw [Complex.ofReal_mul, Complex.ofReal_ofNat]
  have hsre : (-(1 - (y : ℂ) * Complex.I)).re = -1 := by simp
  have hpow : ‖(2 * (Real.pi : ℂ)) ^ (-(1 - (y : ℂ) * Complex.I))‖
      = (2 * Real.pi)⁻¹ := by
    rw [← hbase, Complex.norm_cpow_eq_rpow_re_of_pos (by positivity : (0:ℝ) < 2*Real.pi),
      hsre, Real.rpow_neg_one]
  have hnorm : ‖(2 : ℂ) * (2 * (Real.pi : ℂ)) ^ (-(1 - (y : ℂ) * Complex.I))
        * Complex.Gamma (1 - (y : ℂ) * Complex.I)
        * Complex.cos ((Real.pi : ℂ) * (1 - (y : ℂ) * Complex.I) / 2)‖
      = (1 / Real.pi) * ‖Complex.Gamma (1 - (y : ℂ) * Complex.I)‖
        * Real.sinh (Real.pi * |y| / 2) := by
    rw [norm_mul, norm_mul, norm_mul, Complex.norm_ofNat, hpow, hcos]
    have h2 : (2 : ℝ) * (2 * Real.pi)⁻¹ = 1 / Real.pi := by
      rw [show (2:ℝ) * (2*Real.pi)⁻¹ = 2 / (2*Real.pi) by rw [div_eq_mul_inv]]
      rw [div_eq_div_iff (by positivity : (2*Real.pi:ℝ) ≠ 0) (ne_of_gt Real.pi_pos)]
      ring
    rw [h2]
  have hSnn : 0 ≤ Real.sinh (Real.pi * |y| / 2) :=
    Real.sinh_nonneg_iff.mpr (by positivity)
  have hTval : Real.sinh (Real.pi * |y|)
      = 2 * Real.sinh (Real.pi * |y| / 2) * Real.cosh (Real.pi * |y| / 2) := by
    have h := Real.sinh_two_mul (Real.pi * |y| / 2)
    rw [show 2 * (Real.pi * |y| / 2) = Real.pi * |y| by ring] at h
    rw [h]
  have hS2T : Real.sinh (Real.pi * |y| / 2) ^ 2 ≤ Real.sinh (Real.pi * |y|) := by
    have hSC : Real.sinh (Real.pi * |y| / 2) < Real.cosh (Real.pi * |y| / 2) :=
      Real.sinh_lt_cosh _
    have h2C : Real.sinh (Real.pi * |y| / 2) ≤ 2 * Real.cosh (Real.pi * |y| / 2) := by
      linarith
    calc Real.sinh (Real.pi * |y| / 2) ^ 2
        = Real.sinh (Real.pi * |y| / 2) * Real.sinh (Real.pi * |y| / 2) := by ring
      _ ≤ Real.sinh (Real.pi * |y| / 2) * (2 * Real.cosh (Real.pi * |y| / 2)) :=
            mul_le_mul_of_nonneg_left h2C hSnn
      _ = 2 * Real.sinh (Real.pi * |y| / 2) * Real.cosh (Real.pi * |y| / 2) := by ring
      _ = Real.sinh (Real.pi * |y|) := hTval.symm
  have hTpos : 0 < Real.sinh (Real.pi * |y|) :=
    Real.sinh_pos_iff.mpr (by positivity)
  have hLHS2 : ‖(2 : ℂ) * (2 * (Real.pi : ℂ)) ^ (-(1 - (y : ℂ) * Complex.I))
        * Complex.Gamma (1 - (y : ℂ) * Complex.I)
        * Complex.cos ((Real.pi : ℂ) * (1 - (y : ℂ) * Complex.I) / 2)‖ ^ 2
      = |y| * Real.sinh (Real.pi * |y| / 2) ^ 2
          / (Real.pi * Real.sinh (Real.pi * |y|)) := by
    rw [hnorm]
    have hexp : ((1 / Real.pi) * ‖Complex.Gamma (1 - (y : ℂ) * Complex.I)‖
          * Real.sinh (Real.pi * |y| / 2)) ^ 2
        = (1 / Real.pi) ^ 2 * ‖Complex.Gamma (1 - (y : ℂ) * Complex.I)‖ ^ 2
          * Real.sinh (Real.pi * |y| / 2) ^ 2 := by ring
    rw [hexp, hΓ]
    have hpne : (Real.pi : ℝ) ≠ 0 := ne_of_gt Real.pi_pos
    have hTne : Real.sinh (Real.pi * |y|) ≠ 0 := ne_of_gt hTpos
    field_simp
  have hbound : ‖(2 : ℂ) * (2 * (Real.pi : ℂ)) ^ (-(1 - (y : ℂ) * Complex.I))
        * Complex.Gamma (1 - (y : ℂ) * Complex.I)
        * Complex.cos ((Real.pi : ℂ) * (1 - (y : ℂ) * Complex.I) / 2)‖ ^ 2 ≤ |y| := by
    rw [hLHS2, div_le_iff₀ (mul_pos Real.pi_pos hTpos)]
    calc |y| * Real.sinh (Real.pi * |y| / 2) ^ 2
        ≤ |y| * Real.sinh (Real.pi * |y|) := mul_le_mul_of_nonneg_left hS2T (abs_nonneg y)
      _ ≤ |y| * (Real.pi * Real.sinh (Real.pi * |y|)) := by
            apply mul_le_mul_of_nonneg_left _ (abs_nonneg y)
            nlinarith [hTpos, Real.pi_gt_three]
  exact (Real.le_sqrt (norm_nonneg _) (abs_nonneg y)).mpr hbound

/-- `‖ζ(1+it)‖ ≪ log(2+|t|)` on the line `Re s = 1`. -/
theorem zetaReOneLogBound :
    ∃ C : ℝ, 0 < C ∧ ∀ t : ℝ, 1 ≤ |t| →
      ‖riemannZeta ((1 : ℂ) + (t : ℂ) * Complex.I)‖ ≤ C * (Real.log (2 + |t|) + 1) := by
  refine ⟨101, by norm_num, ?_⟩
  intro t ht
  set s : ℂ := (1 : ℂ) + (t : ℂ) * Complex.I with hs
  have hsre : s.re = 1 := by simp [hs]
  have hsim : s.im = t := by simp [hs]
  have hs0 : 0 < s.re := by rw [hsre]; norm_num
  have hs1 : s ≠ 1 := by
    intro h
    have him := congrArg Complex.im h
    simp [hs] at him
    have : |t| = 0 := by rw [him]; simp
    linarith
  set N : ℕ := Nat.floor |t| + 4 with hN
  have hN1 : 1 ≤ N := by dsimp [N]; omega
  have hNge : |t| + 3 ≤ (N : ℝ) := by
    have hfl : |t| < (Nat.floor |t| : ℝ) + 1 := Nat.lt_floor_add_one |t|
    have hcast : (N : ℝ) = (Nat.floor |t| : ℝ) + 4 := by simp [N]
    linarith
  have hNpos : (0 : ℝ) < (N : ℝ) := by
    have : (1 : ℝ) ≤ (N : ℝ) := by exact_mod_cast hN1
    linarith
  obtain ⟨hsum, htail⟩ := Commons.NumberTheory.Zeta.emTerm_tsum_le N hN1 s hs0 hs1
  have hid := Commons.NumberTheory.Zeta.zeta_eq_emN (s := s) hs0 hs1 N hN1
  have hhead : ‖∑ n ∈ Finset.Icc 1 N, ((n : ℕ) : ℂ) ^ (-s)‖ ≤ (harmonic N : ℝ) := by
    calc ‖∑ n ∈ Finset.Icc 1 N, ((n : ℕ) : ℂ) ^ (-s)‖
        ≤ ∑ n ∈ Finset.Icc 1 N, ‖((n : ℕ) : ℂ) ^ (-s)‖ := norm_sum_le _ _
      _ = ∑ n ∈ Finset.Icc 1 N, ((n : ℕ) : ℝ)⁻¹ := by
            apply Finset.sum_congr rfl
            intro n hn
            have hn1 : 1 ≤ n := (Finset.mem_Icc.mp hn).1
            have hnpos : (0 : ℝ) < (n : ℝ) := by exact_mod_cast hn1
            have hnne : ((n : ℕ) : ℂ) = (((n : ℕ) : ℝ) : ℂ) := by simp
            rw [hnne, Complex.norm_cpow_eq_rpow_re_of_pos hnpos,
              show (-s).re = -1 by rw [Complex.neg_re, hsre], Real.rpow_neg_one]
      _ = (harmonic N : ℝ) := by
            rw [harmonic_eq_sum_Icc]; push_cast; rfl
  have hpole : ‖(((N : ℕ) : ℂ) ^ (1 - s) / (s - 1))‖ ≤ 1 := by
    have hsne : s - 1 ≠ 0 := by
      intro h
      have him := congrArg Complex.im h
      simp [hs] at him
      have ht0 : t = 0 := by linarith
      have : |t| = 0 := by rw [ht0]; simp
      linarith
    have hden : 1 ≤ ‖s - 1‖ := by
      have h1 : |(s - 1).im| ≤ ‖s - 1‖ := abs_im_le_norm (s - 1)
      have h2 : (s - 1).im = t := by simp [hs]
      rw [h2] at h1; exact le_trans ht h1
    calc ‖(((N : ℕ) : ℂ) ^ (1 - s) / (s - 1))‖
        = ‖(((N : ℕ) : ℂ) ^ (1 - s))‖ / ‖s - 1‖ := norm_div _ _
      _ = ((N : ℝ)) ^ (1 - s).re / ‖s - 1‖ := by
            rw [show ((N : ℕ) : ℂ) = (((N : ℕ) : ℝ) : ℂ) by simp,
              Complex.norm_cpow_eq_rpow_re_of_pos hNpos]
      _ = ((N : ℝ)) ^ (0 : ℝ) / ‖s - 1‖ := by
            rw [show (1 - s).re = 0 by simp [hs]]
      _ = 1 / ‖s - 1‖ := by rw [Real.rpow_zero]
      _ ≤ 1 := by
            rw [div_le_iff₀ (by positivity : (0:ℝ) < ‖s - 1‖)]
            linarith
  have htailb : ‖∑' m : ℕ,
      (((N + m + 1 : ℕ) : ℂ) ^ (-s) -
        ((((N + m + 1 : ℕ) : ℂ) ^ (1 - s) - (((N + m : ℕ) : ℂ) ^ (1 - s))) / (1 - s)))‖ ≤ 1 := by
    have hnorm_s : ‖s‖ ≤ (N : ℝ) := by
      have h1 : ‖s‖ ≤ 1 + |t| := by
        calc ‖s‖ = ‖(1 : ℂ) + (t : ℂ) * Complex.I‖ := by rw [hs]
          _ ≤ ‖(1 : ℂ)‖ + ‖(t : ℂ) * Complex.I‖ := norm_add_le _ _
          _ = 1 + |t| := by
                rw [norm_one, Complex.norm_mul, Complex.norm_I, mul_one, Complex.norm_real,
                  Real.norm_eq_abs]
      linarith
    calc ‖∑' m : ℕ, (((N + m + 1 : ℕ) : ℂ) ^ (-s) -
          ((((N + m + 1 : ℕ) : ℂ) ^ (1 - s) - (((N + m : ℕ) : ℂ) ^ (1 - s))) / (1 - s)))‖
        ≤ ∑' m : ℕ, ‖(((N + m + 1 : ℕ) : ℂ) ^ (-s) -
          ((((N + m + 1 : ℕ) : ℂ) ^ (1 - s) - (((N + m : ℕ) : ℂ) ^ (1 - s))) / (1 - s)))‖ :=
            norm_tsum_le_tsum_norm hsum.norm
      _ ≤ ‖s‖ / s.re * ((N : ℝ)) ^ (-s.re) := htail
      _ = ‖s‖ / (N : ℝ) := by rw [hsre, Real.rpow_neg_one]; ring
      _ ≤ 1 := by
            rw [div_le_iff₀ hNpos]; linarith
  have htri : ‖(∑ n ∈ Finset.Icc 1 N, ((n : ℕ) : ℂ) ^ (-s))
        + (((N : ℕ) : ℂ) ^ (1 - s) / (s - 1))
        + (∑' m : ℕ, (((N + m + 1 : ℕ) : ℂ) ^ (-s) -
            ((((N + m + 1 : ℕ) : ℂ) ^ (1 - s) - (((N + m : ℕ) : ℂ) ^ (1 - s))) / (1 - s))))‖
      ≤ (harmonic N : ℝ) + 1 + 1 := by
    have h1 : ‖(∑ n ∈ Finset.Icc 1 N, ((n : ℕ) : ℂ) ^ (-s))
        + (((N : ℕ) : ℂ) ^ (1 - s) / (s - 1))
        + (∑' m : ℕ, (((N + m + 1 : ℕ) : ℂ) ^ (-s) -
            ((((N + m + 1 : ℕ) : ℂ) ^ (1 - s) - (((N + m : ℕ) : ℂ) ^ (1 - s))) / (1 - s))))‖
        ≤ ‖(∑ n ∈ Finset.Icc 1 N, ((n : ℕ) : ℂ) ^ (-s))
            + (((N : ℕ) : ℂ) ^ (1 - s) / (s - 1))‖
          + ‖∑' m : ℕ, (((N + m + 1 : ℕ) : ℂ) ^ (-s) -
            ((((N + m + 1 : ℕ) : ℂ) ^ (1 - s) - (((N + m : ℕ) : ℂ) ^ (1 - s))) / (1 - s)))‖ :=
          norm_add_le _ _
    linarith [norm_add_le (∑ n ∈ Finset.Icc 1 N, ((n : ℕ) : ℂ) ^ (-s))
      (((N : ℕ) : ℂ) ^ (1 - s) / (s - 1)), h1, hhead, hpole, htailb]
  have hlogN : Real.log (N : ℝ) ≤ Real.log (2 + |t|) + 1 := by
    have hNle : (N : ℝ) ≤ 2 * (2 + |t|) := by
      have hcast : (N : ℝ) = (Nat.floor |t| : ℝ) + 4 := by simp [N]
      have hfl : (Nat.floor |t| : ℝ) ≤ |t| := Nat.floor_le (abs_nonneg t)
      linarith [abs_nonneg t]
    have hpos : (0 : ℝ) < (N : ℝ) := hNpos
    have h2pos : (0 : ℝ) < 2 * (2 + |t|) := by linarith [abs_nonneg t]
    have h1 : Real.log (N : ℝ) ≤ Real.log (2 * (2 + |t|)) := Real.log_le_log hpos hNle
    have h2 : Real.log (2 * (2 + |t|)) = Real.log 2 + Real.log (2 + |t|) :=
      Real.log_mul (by norm_num) (by linarith [abs_nonneg t])
    have h3 : Real.log 2 + Real.log (2 + |t|) ≤ 1 + Real.log (2 + |t|) := by
      linarith [Real.log_two_lt_d9]
    linarith
  have hhn : (harmonic N : ℝ) ≤ 1 + Real.log (N : ℝ) := harmonic_le_one_add_log N
  have hlogineq : (harmonic N : ℝ) + 1 + 1 ≤ 101 * (Real.log (2 + |t|) + 1) := by
    have hnonneg : 0 ≤ Real.log (2 + |t|) :=
      Real.log_nonneg (by linarith [abs_nonneg t])
    have h1 : (harmonic N : ℝ) ≤ Real.log (2 + |t|) + 2 := by linarith
    nlinarith [h1, hnonneg]
  calc ‖riemannZeta ((1 : ℂ) + (t : ℂ) * Complex.I)‖ = ‖riemannZeta s‖ := by rw [hs]
    _ = ‖(∑ n ∈ Finset.Icc 1 N, ((n : ℕ) : ℂ) ^ (-s))
          + (((N : ℕ) : ℂ) ^ (1 - s) / (s - 1))
          + (∑' m : ℕ, (((N + m + 1 : ℕ) : ℂ) ^ (-s) -
              ((((N + m + 1 : ℕ) : ℂ) ^ (1 - s) - (((N + m : ℕ) : ℂ) ^ (1 - s))) / (1 - s))))‖ := by
          rw [hid]
    _ ≤ (harmonic N : ℝ) + 1 + 1 := htri
    _ ≤ 101 * (Real.log (2 + |t|) + 1) := hlogineq

/-- Convexity bound for `ζ` on the imaginary axis. -/
theorem zetaImagAxisBound (η : ℝ) (hη : 0 < η) :
    ∃ C : ℝ, 0 < C ∧ ∀ y : ℝ,
      ‖riemannZeta ((y : ℂ) * Complex.I)‖ ≤ C * (2 + |y|) ^ ((1 : ℝ) / 2 + η) := by
  obtain ⟨Cs, hCs⟩ := zetaImagAxis_small_bound
  obtain ⟨CA, hCApos, hCA⟩ := zetaReOneLogBound
  obtain ⟨CK, hCKpos, hCK⟩ := Work.LinnikAreas.JutilaPieces.log_add_two_le_mul_rpow hη
  refine ⟨max Cs (CA * CK) + 1, by positivity, ?_⟩
  intro y
  by_cases hy : |y| ≤ 1
  · have hge1 : (1 : ℝ) ≤ (2 + |y|) ^ ((1 : ℝ) / 2 + η) :=
      Real.one_le_rpow (by linarith [abs_nonneg y]) (by linarith)
    have hCsC : Cs ≤ max Cs (CA * CK) + 1 := by linarith [le_max_left Cs (CA * CK)]
    have hposC : 0 ≤ max Cs (CA * CK) + 1 := by
      have : (0:ℝ) < CA * CK := mul_pos hCApos hCKpos
      linarith [le_max_right Cs (CA * CK)]
    calc ‖riemannZeta ((y:ℂ)*Complex.I)‖ ≤ Cs := hCs y hy
      _ ≤ (max Cs (CA * CK) + 1) * (2 + |y|) ^ ((1:ℝ)/2 + η) := by
            calc Cs ≤ max Cs (CA * CK) + 1 := hCsC
              _ = (max Cs (CA * CK) + 1) * 1 := by ring
              _ ≤ (max Cs (CA * CK) + 1) * (2 + |y|) ^ ((1:ℝ)/2 + η) :=
                    mul_le_mul_of_nonneg_left hge1 hposC
  · have hy1 : 1 ≤ |y| := le_of_lt (not_le.mp hy)
    have hy0 : y ≠ 0 := by
      intro h0; rw [h0] at hy1; norm_num at hy1
    have hs1 : (1 : ℂ) - (y:ℂ)*Complex.I ≠ 1 := by
      intro h
      have him := congrArg Complex.im h
      simp [Complex.sub_im] at him
      exact hy0 (by linarith)
    have hne : ∀ n : ℕ, (1:ℂ) - (y:ℂ)*Complex.I ≠ -(n:ℂ) := by
      intro n hn
      have hre := congrArg Complex.re hn
      simp at hre
      have : (0:ℝ) ≤ (n:ℝ) := Nat.cast_nonneg n
      linarith
    have hFE := riemannZeta_one_sub (s := (1:ℂ) - (y:ℂ)*Complex.I) hne hs1
    have harg : (1:ℂ) - ((1:ℂ) - (y:ℂ)*Complex.I) = (y:ℂ)*Complex.I := by ring
    rw [harg] at hFE
    have hz := hCA (-y) (by rwa [abs_neg])
    have harg2 : (1:ℂ) + ((-y:ℝ):ℂ)*Complex.I = (1:ℂ) - (y:ℂ)*Complex.I := by push_cast; ring
    rw [harg2, abs_neg] at hz
    have hfe := feFactorBound y hy1
    have hprod : ‖riemannZeta ((y:ℂ)*Complex.I)‖
        ≤ Real.sqrt |y| * (CA * (Real.log (2 + |y|) + 1)) := by
      calc ‖riemannZeta ((y:ℂ)*Complex.I)‖
          = ‖((2:ℂ) * (2*(Real.pi:ℂ))^(-(1-(y:ℂ)*Complex.I)) * Complex.Gamma (1-(y:ℂ)*Complex.I)
              * Complex.cos ((Real.pi:ℂ)*(1-(y:ℂ)*Complex.I)/2)) * riemannZeta (1-(y:ℂ)*Complex.I)‖ := by
              rw [hFE]
        _ = ‖(2:ℂ) * (2*(Real.pi:ℂ))^(-(1-(y:ℂ)*Complex.I)) * Complex.Gamma (1-(y:ℂ)*Complex.I)
              * Complex.cos ((Real.pi:ℂ)*(1-(y:ℂ)*Complex.I)/2)‖
            * ‖riemannZeta (1-(y:ℂ)*Complex.I)‖ := norm_mul _ _
        _ ≤ Real.sqrt |y| * (CA * (Real.log (2 + |y|) + 1)) :=
              mul_le_mul hfe hz (norm_nonneg _) (Real.sqrt_nonneg _)
    have hfinal : Real.sqrt |y| * (CA * (Real.log (2 + |y|) + 1))
        ≤ (max Cs (CA * CK) + 1) * (2 + |y|) ^ ((1:ℝ)/2 + η) := by
      have hx1 : (1:ℝ) ≤ 2 + |y| := by linarith [abs_nonneg y]
      have hlogb : Real.log (2 + |y|) + 1 ≤ CK * (2 + |y|) ^ η := by
        have := hCK (2 + |y|) hx1
        linarith
      have hsq : Real.sqrt |y| ≤ (2 + |y|) ^ ((1:ℝ)/2) := by
        rw [Real.sqrt_eq_rpow]
        exact Real.rpow_le_rpow (abs_nonneg y) (by linarith [abs_nonneg y]) (by norm_num)
      have hCAC : CA * CK ≤ max Cs (CA * CK) + 1 := by linarith [le_max_right Cs (CA*CK)]
      have hstep : Real.sqrt |y| * (CA * (Real.log (2+|y|)+1))
          ≤ (CA * CK) * (2 + |y|) ^ ((1:ℝ)/2 + η) := by
        calc Real.sqrt |y| * (CA * (Real.log (2+|y|)+1))
            = CA * (Real.sqrt |y| * (Real.log (2+|y|)+1)) := by ring
          _ ≤ CA * ((2 + |y|)^((1:ℝ)/2) * (CK * (2+|y|)^η)) := by
                apply mul_le_mul_of_nonneg_left _ hCApos.le
                have hcnn : 0 ≤ Real.log (2 + |y|) + 1 := by
                  have := Real.log_nonneg hx1; linarith
                exact mul_le_mul hsq hlogb hcnn
                  (Real.rpow_nonneg (by linarith [abs_nonneg y]) _)
          _ = (CA * CK) * ((2+|y|)^((1:ℝ)/2) * (2+|y|)^η) := by ring
          _ = (CA * CK) * (2 + |y|) ^ ((1:ℝ)/2 + η) := by
                rw [← Real.rpow_add (by linarith [abs_nonneg y] : (0:ℝ) < 2 + |y|)]
      calc Real.sqrt |y| * (CA * (Real.log (2 + |y|) + 1))
          ≤ (CA * CK) * (2 + |y|) ^ ((1:ℝ)/2 + η) := hstep
        _ ≤ (max Cs (CA * CK) + 1) * (2 + |y|) ^ ((1:ℝ)/2 + η) :=
              mul_le_mul_of_nonneg_right hCAC (Real.rpow_nonneg (by linarith [abs_nonneg y]) _)
    linarith [hprod, hfinal]

/-- L0 of JUTILA_UNIFIED_LEAD.md section 3, the **principal-character** half of the convexity bound on the imaginary axis. For every `eta > 0` there is `C > 0` such that for all `q >= 2` and all real `y`,

  `||L(iy, 1_q)|| <= C * (q * (2 + |y|))^(1/2 + eta)`,

where `1_q` is the principal Dirichlet character mod `q`, so `L(s, 1_q) = zeta(s) * prod_{p | q} (1 - p^(-s))`. The companion non-principal case `||L(iy, chi)|| <= C (q(1+|y|))^(1/2+eps)` for `chi != 1` (all imprimitive characters included) is ALREADY PROVED in the workspace as `Commons...LFunctionCritLineBound` in `Submission/Work/LinnikAreas/JutilaPieces/LFunctionCritLineBound.lean`, so only the principal character is missing. Route: on `Re s = 0` the Euler factors satisfy `||1 - p^(-iy)|| <= 2`, so `2^(omega q) <= C_eta q^eta` (as in the proved `lfunction_at_zero_le_primitive` in the same file), reducing to `||zeta(iy)|| <= C (2 + |y|)^(1/2+eta)`; the latter follows from the functional equation for `zeta` together with `||zeta(1 + iy)|| <= C log(2 + |y|)` on the line `Re s = 1`. This is Jutila (1977) section 2 preliminary estimate for the principal character, and it is what makes the right-hand side of the hybrid zero detector's Mellin representation `<< 1` at the principal character. -/
theorem principalImagAxisBound (η : ℝ) (hη : 0 < η) :
    ∃ C : ℝ, 0 < C ∧ ∀ q : ℕ, 2 ≤ q → ∀ [NeZero q] (y : ℝ),
      ‖DirichletCharacter.LFunction (1 : DirichletCharacter ℂ q) ((y : ℂ) * Complex.I)‖
        ≤ C * ((q : ℝ) * (2 + |y|)) ^ ((1 : ℝ) / 2 + η) := by
  obtain ⟨Cζ, hCζpos, hCζ⟩ := zetaImagAxisBound η hη
  obtain ⟨Cω, hCωpos, hCω⟩ := Commons.NumberTheory.Nat.two_pow_omega_le_const_mul_rpow η hη
  refine ⟨Cζ * Cω, mul_pos hCζpos hCωpos, ?_⟩
  intro q hq _ y
  have hq1 : 1 ≤ q := le_trans (by norm_num) hq
  have hq1R : (1 : ℝ) ≤ (q : ℝ) := by exact_mod_cast hq1
  have hqpos : (0 : ℝ) < (q : ℝ) := lt_of_lt_of_le one_pos hq1R
  have hy2 : (1 : ℝ) ≤ 2 + |y| := by linarith [abs_nonneg y]
  have hbasepos : (0 : ℝ) < (q : ℝ) * (2 + |y|) := mul_pos hqpos (by linarith [abs_nonneg y])
  have hsne : ((y : ℂ) * Complex.I) ≠ 1 := by
    intro h
    have hre : (0:ℝ) = 1 := by have := congrArg Complex.re h; simpa using this
    exact zero_ne_one hre
  have hprod : ‖∏ p ∈ q.primeFactors, ((1:ℂ) - ((p:ℂ)) ^ (-((y:ℂ)*Complex.I)))‖
      ≤ (2:ℝ) ^ (q.primeFactors.card) := by
    rw [norm_prod]
    have hconst : (∏ _p ∈ q.primeFactors, (2:ℝ)) = (2:ℝ) ^ q.primeFactors.card :=
      Finset.prod_const (s := q.primeFactors) (2:ℝ)
    rw [← hconst]
    apply Finset.prod_le_prod₀ (fun p _ => norm_nonneg _)
    intro p hp
    have hp2 : 0 < p := (Nat.prime_of_mem_primeFactors hp).pos
    have hnorm : ‖(p:ℂ) ^ (-((y:ℂ)*Complex.I))‖ = 1 := by
      rw [Complex.norm_natCast_cpow_of_pos hp2]
      have hre : (-((y:ℂ)*Complex.I)).re = 0 := by simp
      rw [hre, Real.rpow_zero]
    calc ‖(1:ℂ) - ((p:ℂ)) ^ (-((y:ℂ)*Complex.I))‖
        ≤ ‖(1:ℂ)‖ + ‖((p:ℂ)) ^ (-((y:ℂ)*Complex.I))‖ := norm_sub_le _ _
      _ ≤ 2 := by rw [norm_one, hnorm]; norm_num
  have homega : (2:ℝ) ^ (q.primeFactors.card) ≤ Cω * (q:ℝ) ^ η := hCω q hq1
  have hLz : ‖riemannZeta ((y:ℂ)*Complex.I)‖ ≤ Cζ * (2 + |y|) ^ ((1:ℝ)/2 + η) := hCζ y
  have hstep1 : ‖DirichletCharacter.LFunction (1 : DirichletCharacter ℂ q) ((y:ℂ)*Complex.I)‖
      ≤ (2:ℝ)^(q.primeFactors.card) * (Cζ * (2+|y|)^((1:ℝ)/2+η)) := by
    have hid : DirichletCharacter.LFunction (1 : DirichletCharacter ℂ q) ((y:ℂ)*Complex.I)
        = (∏ p ∈ q.primeFactors, ((1:ℂ) - (p:ℂ)^(-((y:ℂ)*Complex.I))))
            * riemannZeta ((y:ℂ)*Complex.I) :=
      DirichletCharacter.LFunctionTrivChar_eq_mul_riemannZeta hsne
    rw [hid, norm_mul]
    exact mul_le_mul hprod hLz (norm_nonneg _) (by positivity)
  calc ‖DirichletCharacter.LFunction (1 : DirichletCharacter ℂ q) ((y:ℂ)*Complex.I)‖
      ≤ (2:ℝ)^(q.primeFactors.card) * (Cζ * (2+|y|)^((1:ℝ)/2+η)) := hstep1
    _ ≤ (Cω * (q:ℝ)^η) * (Cζ * (2+|y|)^((1:ℝ)/2+η)) := by
        apply mul_le_mul_of_nonneg_right homega
        positivity
    _ = Cζ * Cω * ((q:ℝ)^η * (2+|y|)^((1:ℝ)/2+η)) := by ring
    _ ≤ Cζ * Cω * (((q:ℝ) * (2+|y|))^((1:ℝ)/2+η)) := by
        apply mul_le_mul_of_nonneg_left _ (by positivity)
        rw [Real.mul_rpow hqpos.le (by linarith [abs_nonneg y])]
        exact mul_le_mul_of_nonneg_right
          (Real.rpow_le_rpow_of_exponent_le hq1R (by linarith)) (by positivity)

end Work.ZeroDensity.LogFree
