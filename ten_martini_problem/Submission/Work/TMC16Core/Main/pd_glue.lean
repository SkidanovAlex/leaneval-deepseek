import Mathlib
import Submission.Work.TMC16Core.Defs
import Submission.Work.TMC16Core.Assembly.Consts
import Submission.Work.TMC16Core.Assembly.NrParamsDefs
import Submission.Work.TMC16Core.Core.nr_ladder
import Submission.Work.TMC16Core.CF.cf_data_bridge
import Submission.Work.TMC16Core.Assembly.nr_case1_full
import Submission.Work.TMC16Core.Assembly.nr_case1_i1win
import Submission.Work.TMC16Core.Core.irrat_blk_nr
import Submission.Work.TMC16Core.Main.theta_charge_nr
import Submission.Work.TMC16Core.Core.setup
import Submission.Work.TMC16Core.Main.rate_main_bound
import Submission.Work.TMC16Core.Main.level_data
import Submission.Work.TMC16Core.Assembly.nr_case1_ge2
import Submission.Work.TMC16Core.Main.nr_data_eventual

/-!
# The glue of `Main.pd_window_reg_dioph`

This file assembles AJ §9 (Lemmas 9.4, 9.5 and the patching) from the branch estimates.
The pieces it provides here are the *bookkeeping*: monotonicity of `IsRegularBig` in the
prescribed length, the numerical side conditions of the non-resonant branch, and (later)
the continued-fraction level selection and the case dispatch.
-/

namespace Work.TMC16Core.Main

open Work.TMC16Core
open Work.TMC16Core.Assembly

noncomputable section

/-! ## Monotonicity in the prescribed length -/

/-- `IsRegularBig` is monotone in the prescribed lower bound `q`: the same witnessing interval
works. -/
theorem IsRegularBig_mono {α lam θ : ℝ} {E : ℂ} {L₁ q q' : ℝ} {y : ℤ} (hq : q' ≤ q)
    (h : IsRegularBig α lam θ E L₁ q y) : IsRegularBig α lam θ E L₁ q' y := by
  obtain ⟨x₁, x₂, h1, h2, hlen, hd1, hd2, hdet, hg1, hg2⟩ := h
  exact ⟨x₁, x₂, h1, h2, le_trans hq hlen, hd1, hd2, hdet, hg1, hg2⟩

/-! ## The numerical side conditions of the non-resonant branch -/

/-- The three purely numerical hypotheses of `Assembly.nr_case1_full` hold for all
sufficiently large scales `K`, uniformly in the uniformity rate `r ≤ L/8 + L/100`. -/
theorem nr_side_conditions {L : ℝ} (hL : 0 < L) :
    ∃ K₀ : ℕ, ∀ r : ℝ, r ≤ L / 8 + L / 100 → ∀ K : ℕ, K₀ ≤ K →
      40 ≤ K ∧ 1 ≤ (K : ℝ) * (cdelta L r - 1 / 40) ∧
      4 * ((K : ℝ) + 1) * Real.exp (L - epsA L r) <
        Real.exp ((K : ℝ) * (epsA L r - eps2 L)) := by
  refine ⟨max 100 (max (Nat.ceil ((2000 / L) ^ 2)) (Nat.ceil (L ^ 2))), ?_⟩
  intro r hr K hK
  have hK100 : 100 ≤ K := le_trans (le_max_left _ _) hK
  have hKA : Nat.ceil ((2000 / L) ^ 2) ≤ K :=
    le_trans (le_trans (le_max_left _ _) (le_max_right _ _)) hK
  have hKB : Nat.ceil (L ^ 2) ≤ K :=
    le_trans (le_trans (le_max_right _ _) (le_max_right _ _)) hK
  have hK40 : 40 ≤ K := by omega
  have hK90 : 90 ≤ K := by omega
  have hKpos : (0 : ℝ) < (K : ℝ) := by
    have : (0:ℕ) < K := by omega
    exact_mod_cast this
  have hK1 : (1 : ℝ) ≤ (K : ℝ) := by exact_mod_cast (by omega : 1 ≤ K)
  have hK90R : (90 : ℝ) ≤ (K : ℝ) := by exact_mod_cast hK90
  have hKa : (2000 / L) ^ 2 ≤ (K : ℝ) := le_trans (Nat.le_ceil _) (by exact_mod_cast hKA)
  have hKb : L ^ 2 ≤ (K : ℝ) := le_trans (Nat.le_ceil _) (by exact_mod_cast hKB)
  have hcs : 0 < csing L := csing_pos hL
  have hcsne : csing L ≠ 0 := ne_of_gt hcs
  have hcsval : csing L = 99 * L / 100 := by simp only [csing]; ring
  have heps2 : eps2 L = L / 100 := rfl
  have hAL : csing L / 40 + L / 1000 ≤ epsA L r := by
    simp only [epsA]; linarith [le_max_right r (csing L / 40)]
  have hsqrtK : 0 < Real.sqrt (K : ℝ) := Real.sqrt_pos.mpr hKpos
  have hLsqrt : L ≤ Real.sqrt (K : ℝ) := by
    have h1 : Real.sqrt (L ^ 2) ≤ Real.sqrt (K : ℝ) := Real.sqrt_le_sqrt hKb
    rwa [Real.sqrt_sq (le_of_lt hL)] at h1
  have hLK : 2000 * Real.sqrt (K : ℝ) ≤ L * (K : ℝ) := by
    have h100 : 2000 / L ≤ Real.sqrt (K : ℝ) := by
      have h := Real.sqrt_le_sqrt hKa
      rwa [Real.sqrt_sq (by positivity : (0:ℝ) ≤ 2000 / L)] at h
    have h2 : 2000 ≤ L * Real.sqrt (K : ℝ) := by
      have := mul_le_mul_of_nonneg_left h100 (le_of_lt hL)
      rwa [mul_div_cancel₀ _ (ne_of_gt hL)] at this
    calc 2000 * Real.sqrt (K : ℝ) ≤ (L * Real.sqrt (K : ℝ)) * Real.sqrt (K : ℝ) := by
          nlinarith [h2, hsqrtK]
      _ = L * (Real.sqrt (K : ℝ)) ^ 2 := by ring
      _ = L * (K : ℝ) := by rw [Real.sq_sqrt (le_of_lt hKpos)]
  have hlog : Real.log (4 * ((K : ℝ) + 1)) ≤ 6 * Real.sqrt (K : ℝ) := by
    have hx : (0 : ℝ) ≤ 4 * ((K : ℝ) + 1) := by linarith
    have h1 : Real.log (4 * ((K : ℝ) + 1)) ≤ 4 * Real.sqrt ((K : ℝ) + 1) := by
      have h := Real.log_le_rpow_div hx (by norm_num : (0:ℝ) < 1 / 2)
      rw [← Real.sqrt_eq_rpow] at h
      have h2 : Real.sqrt (4 * ((K : ℝ) + 1)) = 2 * Real.sqrt ((K : ℝ) + 1) := by
        rw [show (4:ℝ) * ((K:ℝ) + 1) = 4 * ((K:ℝ) + 1) from rfl,
          Real.sqrt_mul (by norm_num : (0:ℝ) ≤ 4)]
        norm_num [Real.sqrt_sq (by norm_num : (0:ℝ) ≤ 2)]
      have h3 : Real.sqrt (4 * ((K : ℝ) + 1)) / (1 / 2)
          = 2 * Real.sqrt (4 * ((K : ℝ) + 1)) := by ring
      linarith [h, h2.le, h2.ge, h3.le, h3.ge]
    have h3 : Real.sqrt ((K : ℝ) + 1) ≤ (3 / 2) * Real.sqrt (K : ℝ) := by
      have h31 : Real.sqrt ((K : ℝ) + 1) ≤ Real.sqrt (2 * (K : ℝ)) :=
        Real.sqrt_le_sqrt (by linarith)
      rw [Real.sqrt_mul (by norm_num : (0:ℝ) ≤ 2)] at h31
      have h32 : Real.sqrt 2 ≤ 3 / 2 := by
        rw [Real.sqrt_le_iff]
        exact ⟨by norm_num, by nlinarith [Real.sq_sqrt (by norm_num : (0:ℝ) ≤ 2)]⟩
      nlinarith [h31, h32, hsqrtK]
    nlinarith [h1, h3, hsqrtK]
  have hA2 : 103 * L / 4000 ≤ epsA L r := by
    have h := hAL; rw [hcsval] at h; linarith
  have hsub : L - epsA L r ≤ 3897 * L / 4000 := by linarith [hA2]
  have hgap2 : (63 : ℝ) * L * (K : ℝ) / 4000 ≤ (K : ℝ) * (epsA L r - eps2 L) := by
    have h2 : (63 : ℝ) * L / 4000 ≤ epsA L r - eps2 L := by
      rw [heps2]; linarith [hA2]
    nlinarith [h2, hKpos]
  have hLb : 3897 * L / 4000 ≤ Real.sqrt (K : ℝ) := by
    have h1 : (3897 : ℝ) / 4000 ≤ 1 := by norm_num
    nlinarith [hLsqrt, hL]
  have hstrict : 7 * Real.sqrt (K : ℝ) < (63 : ℝ) * L * (K : ℝ) / 4000 := by
    nlinarith [hLK, hsqrtK]
  refine ⟨hK40, ?_, ?_⟩
  · -- (b) `1 ≤ K * (cdelta L r - 1/40)`
    have hbase : (1 : ℝ) / 90 ≤ cdelta L r - 1 / 40 := by
      have hstep : cdelta L r - 1 / 40
          = (epsA L r + eps2 L - csing L * (1 / 40)) / csing L := by
        rw [cdelta]; field_simp
      rw [hstep]
      have hnum : (11 : ℝ) * L / 1000 ≤ epsA L r + eps2 L - csing L * (1 / 40) := by
        have h := hAL; rw [hcsval] at h
        rw [heps2]; linarith
      have hstep2 := div_le_div_of_nonneg_right hnum (le_of_lt hcs)
      have heq : ((11 : ℝ) * L / 1000) / csing L = 1 / 90 := by
        rw [hcsval]; field_simp; ring
      linarith [hstep2, heq.le, heq.ge]
    nlinarith [hbase, hK90R]
  · -- (c) the non-generation gap
    rw [← Real.log_lt_log_iff (by positivity : (0:ℝ) < 4 * ((K : ℝ) + 1) * Real.exp (L - epsA L r))
      (Real.exp_pos ((K : ℝ) * (epsA L r - eps2 L)))]
    rw [Real.log_mul (by positivity : (4:ℝ) * ((K : ℝ) + 1) ≠ 0) (Real.exp_ne_zero _),
      Real.log_exp, Real.log_exp]
    linarith [hlog, hsub, hLb, hstrict, hgap2]

/-! ## The `s >= 3` non-resonant branch

We now assemble `Assembly.nr_case1_full` (AJ Lemma 9.4(1)) with the charge `c` supplied by
`Main.theta_charge_nr`: the hypothesis `hθ` of `nr_case1_full` (over the *unrefolded* range
`2|y| + 6 s q(n-1) + 4`) is produced by the refolding lemma, whose charge
`log (1/c) = O (log (q n))` is small enough for the rate bound `hεuub`. -/

theorem two_mul_rpow_le {A c : ℝ} (hA : 0 < A) (hc : 0 < c) (h : (2 * c) ^ 9 ≤ A) :
    2 * A ^ (8 / 9 : ℝ) ≤ A / c := by
  have h2c0 : 0 ≤ 2 * c := by linarith
  have hb : ((2 * c) ^ 9 : ℝ) = (2 * c) ^ (9 : ℝ) := (Real.rpow_natCast (2 * c) 9).symm
  have hpow : ((2 * c) ^ 9 : ℝ) ^ ((1 : ℝ) / 9) = 2 * c := by
    rw [hb, ← Real.rpow_mul h2c0 9 (1 / 9),
      show (9 : ℝ) * (1 / 9) = 1 by norm_num, Real.rpow_one]
  have h1 : 2 * c ≤ A ^ (1 / 9 : ℝ) := by
    have h' : ((2 * c) ^ 9 : ℝ) ^ ((1 : ℝ) / 9) ≤ A ^ ((1 : ℝ) / 9) :=
      Real.rpow_le_rpow (by positivity) h (by norm_num)
    rwa [hpow] at h'
  have hadd : A ^ ((1 : ℝ) / 9) * A ^ ((8 : ℝ) / 9) = A := by
    have hh : A ^ ((1 : ℝ) / 9 + (8 : ℝ) / 9) = A ^ ((1 : ℝ) / 9) * A ^ ((8 : ℝ) / 9) :=
      Real.rpow_add hA _ _
    rw [show ((1 : ℝ) / 9 + (8 : ℝ) / 9) = 1 by norm_num, Real.rpow_one] at hh
    exact hh.symm
  have h3 : 0 ≤ A ^ ((8 : ℝ) / 9) := Real.rpow_nonneg (le_of_lt hA) _
  have h4 : (2 * c) * A ^ ((8 : ℝ) / 9) ≤ A := by
    conv_rhs => rw [← hadd]
    exact mul_le_mul_of_nonneg_right h1 h3
  rw [le_div_iff₀ hc]
  linarith [h4]


/-! ## Two `rpow` bookkeeping lemmas for the case split -/

/-- `A^(8/9) ≤ (4c)^8` when `A < (4c)^9`. -/
theorem rpow_eight_ninths_le {A c : ℝ} (hA : 0 ≤ A) (hc : 0 ≤ c)
    (h : A < (4 * c) ^ 9) :
    A ^ (8 / 9 : ℝ) ≤ (4 * c) ^ 8 := by
  have h4c : 0 ≤ 4 * c := by linarith
  have hb2 : ((4 * c) ^ 9 : ℝ) = (4 * c) ^ (9 : ℝ) := (Real.rpow_natCast (4 * c) 9).symm
  have hb3 : ((4 * c) ^ 8 : ℝ) = (4 * c) ^ (8 : ℝ) := (Real.rpow_natCast (4 * c) 8).symm
  have h1 : A ^ (8 / 9 : ℝ) ≤ ((4 * c) ^ 9 : ℝ) ^ (8 / 9 : ℝ) :=
    Real.rpow_le_rpow hA (le_of_lt h) (by norm_num)
  have h2 : ((4 * c) ^ 9 : ℝ) ^ (8 / 9 : ℝ) = (4 * c) ^ 8 := by
    rw [hb2, ← Real.rpow_mul h4c 9 (8 / 9),
      show (9 : ℝ) * (8 / 9) = 8 by norm_num, ← hb3]
  linarith [h1, h2.le, h2.ge]


/-! ## The `s ≥ 3` non-resonant branch (AJ Lemma 9.4(1)) -/

/-- **The `s ≥ 3` non-resonant branch of AJ Lemma 9.4(1)**, with the charge `c` produced by
`Main.theta_charge_nr` (so that `hθ` holds over the *unrefolded* range of `nr_uniform`) and the
numerical side conditions of `nr_case1_full` supplied by `nr_side_conditions`. -/
theorem nr_branch_ge3 {α lam L b₀ ε' δ : ℝ} {q : ℕ → ℕ} {Δ : ℕ → ℝ}
    {n s m : ℕ} {y : ℤ} {θ : ℝ} {E : ℂ} {K₀z : ℤ} {csm : ℝ}
    (hlam : 1 < lam) (hLlog : L = Real.log lam) (hL : 0 < L)
    (hqpos : ∀ i, 0 < q i) (hmono : StrictMono q) (hΔpos : ∀ i, 0 < Δ i)
    (hΔeq : ∀ i, Δ i = fracDist ((q i : ℝ) * α))
    (hΔup : ∀ i, Δ i < 1 / ((q (i + 1) : ℝ)))
    (hΔlo : ∀ i, 1 / (((q (i + 1) : ℝ)) + (q i : ℝ)) < Δ i)
    (hbest : ∀ i j : ℕ, q i ≤ j → j < q (i + 1) → Δ i ≤ fracDist ((j : ℝ) * α))
    (hn : 2 ≤ n) (hq1 : 1 ≤ q (n - 1)) (hs : 2 ≤ s) (hy1 : 1 ≤ y)
    (hyΔ : (y : ℝ) * Δ n ≤ 3 / 4)
    (hyb : (y : ℝ) ≤ max (Real.rpow (q (n + 1) : ℝ) (8 / 9)) ((q n : ℝ) / 20))
    (hym : (m : ℤ) * (q n : ℤ) ≤ y) (hym' : y < ((m : ℤ) + 1) * (q n : ℤ))
    (hnres : ∀ ℓ : ℤ, (s : ℤ) * (q (n - 1) : ℤ) ≤ |y - (ℓ : ℤ) * (q n : ℤ)|)
    (hsL : (2 * (s : ℤ)) * (q (n - 1) : ℤ) < (q n : ℤ))
    (hK₀1 : 1 ≤ K₀z) (hcsm : 0 < csm) (hcsm1 : csm ≤ 1 / 2)
    (h1 : ∀ k : ℤ, |k| < K₀z → csm ≤ fracDist (2 * θ + (k : ℝ) * α))
    (h2 : ∀ k : ℤ, K₀z ≤ |k| → ((((k.natAbs : ℕ) : ℝ))⁻¹) ^ 2 ≤
      fracDist (2 * θ + (k : ℝ) * α))
    (hbig : 10 ^ 6 ≤ csm * (q n : ℝ) ^ 2)
    (hside : ∃ K₀ : ℕ, K₀ ≤ Core.Knr q n s ∧ ∀ r : ℝ, r ≤ L / 8 + L / 100 → ∀ K : ℕ, K₀ ≤ K →
      40 ≤ K ∧ 1 ≤ (K : ℝ) * (cdelta L r - 1 / 40) ∧
      4 * ((K : ℝ) + 1) * Real.exp (L - epsA L r) <
        Real.exp ((K : ℝ) * (epsA L r - eps2 L)))
    (hmain : 2 * Real.log ((q n : ℝ) / (s : ℝ)) / (q (n - 1) : ℝ)
      ≤ (2 / 9) * (b₀ + ε') + 2 * Real.log 2 / (q (n - 1) : ℝ)
        + 2 * Real.log (q (n - 1) : ℝ) / (q (n - 1) : ℝ))
    (hδ : 0 < δ) (hδb : (2 / 9) * (b₀ + ε') ≤ L / 8 - δ)
    (hrest : 2 * Real.log 2 / (q (n - 1) : ℝ)
        + 2 * Real.log (q (n - 1) : ℝ) / (q (n - 1) : ℝ)
        + 200 * Real.log (q (n - 1) : ℝ) / (q (n - 1) : ℝ)
        + 2 * (Real.log (1 / csm) + 100 + 20 * Real.log ((q n : ℝ) + 2))
          / ((s : ℝ) * (q (n - 1) : ℝ))
        + 200 / (q (n - 1) : ℝ) ≤ δ + L / 100)
    (hsin : IsSingular α lam θ E (L - csing L) (Core.Knr q n s) 0)
    (hbd : ∀ N : ℕ, Core.Knr q n s / 40 ≤ N → N ≤ Core.Knr q n s → ∀ ζ : ℝ,
      ‖pd α lam ζ E (N + 1)‖ ≤ Real.exp ((N : ℝ) * (L + eps2 L))) :
    IsRegularBig α lam θ E (cL1 L) ((Core.Knr q n s : ℕ) : ℝ) y := by
  have hn1 : 1 ≤ n := by omega
  have hQ1 : (1 : ℝ) ≤ (q (n - 1) : ℝ) := by exact_mod_cast hq1
  have hQpos : (0 : ℝ) < (q (n - 1) : ℝ) := by linarith
  have hqn1 : (1 : ℝ) ≤ (q n : ℝ) := by
    have hlt : q (n - 1) < q n := hmono (by omega)
    have h2' : (q (n - 1) : ℝ) + 1 ≤ (q n : ℝ) := by exact_mod_cast hlt
    linarith
  have hqnn : (0 : ℝ) ≤ (q n : ℝ) := le_trans (by norm_num) hqn1
  have hy0 : (0 : ℤ) ≤ y := by omega
  have hy0R : (0 : ℝ) ≤ (y : ℝ) := by exact_mod_cast hy0
  have hyabs : |y| = y := abs_of_nonneg hy0
  have hqnp1 : (1 : ℝ) ≤ (q (n + 1) : ℝ) := by
    have : 1 ≤ q (n + 1) := hqpos (n + 1)
    exact_mod_cast this
  have hcase : ((4 * (q n : ℝ)) ^ 9 ≤ (q (n + 1) : ℝ) ∧
        2 * (y : ℝ) ≤ (q (n + 1) : ℝ) / (q n : ℝ)) ∨
      (2 * (y : ℝ) ≤ 10 ^ 6 * ((q n : ℝ) + 1) ^ 10) := by
    by_cases h : (4 * (q n : ℝ)) ^ 9 ≤ (q (n + 1) : ℝ)
    · refine Or.inl ⟨h, ?_⟩
      have h2qn : (2 * (q n : ℝ)) ^ 9 ≤ (q (n + 1) : ℝ) := by
        have hstep : (2 * (q n : ℝ)) ^ 9 = (2:ℝ)^9 * (q n : ℝ)^9 := by ring
        have hstep2 : (4 * (q n : ℝ)) ^ 9 = (4:ℝ)^9 * (q n : ℝ)^9 := by ring
        have hh := h
        rw [hstep2] at hh
        rw [hstep]
        exact le_trans (mul_le_mul_of_nonneg_right (by norm_num : (2:ℝ)^9 ≤ (4:ℝ)^9)
          (by positivity)) hh
      have hkey : 2 * Real.rpow (q (n + 1) : ℝ) (8 / 9) ≤ (q (n + 1) : ℝ) / (q n : ℝ) :=
        two_mul_rpow_le (A := (q (n+1) : ℝ)) (c := (q n : ℝ)) (by linarith) (by linarith) h2qn
      have hkey2 : (q n : ℝ) / 10 ≤ (q (n + 1) : ℝ) / (q n : ℝ) := by
        have hqn2 : (q n : ℝ) ^ 2 ≤ 10 * (q (n + 1) : ℝ) := by
          have h1 : (q n : ℝ)^2 ≤ (q n : ℝ)^9 := pow_le_pow_right₀ hqn1 (by norm_num)
          have h2 : (q n : ℝ)^9 ≤ (2 * (q n : ℝ))^9 := pow_le_pow_left₀ hqnn (by linarith) 9
          linarith
        rw [div_le_iff₀ (by norm_num : (0:ℝ) < 10), div_mul_eq_mul_div,
          le_div_iff₀ (by linarith : (0:ℝ) < (q n : ℝ))]
        linarith
      have hma : 2 * max (Real.rpow (q (n + 1) : ℝ) (8 / 9)) ((q n : ℝ) / 20)
          = max (2 * Real.rpow (q (n + 1) : ℝ) (8 / 9)) (2 * ((q n : ℝ) / 20)) :=
        mul_max_of_nonneg _ _ (by norm_num)
      have hml : max (2 * Real.rpow (q (n + 1) : ℝ) (8 / 9)) (2 * ((q n : ℝ) / 20))
          ≤ (q (n + 1) : ℝ) / (q n : ℝ) := max_le hkey (by linarith [hkey2])
      linarith [hyb, hma, hml]
    · push_neg at h
      refine Or.inr ?_
      have hqnp1nn : (0 : ℝ) ≤ (q (n + 1) : ℝ) := le_of_lt (lt_of_lt_of_le one_pos hqnp1)
      have hq8 : Real.rpow (q (n + 1) : ℝ) (8 / 9) ≤ (4 * (q n : ℝ)) ^ 8 :=
        rpow_eight_ninths_le hqnp1nn hqnn h
      have hkey3 : (q n : ℝ) / 20 ≤ (4 * (q n : ℝ)) ^ 8 := by
        have h3 : (q n : ℝ) ≤ (4 * (q n : ℝ)) ^ 8 := by
          have h4 : (q n : ℝ) ≤ (q n : ℝ)^8 := by
            have hh := pow_le_pow_right₀ hqn1 (show (1:ℕ) ≤ 8 by norm_num)
            simpa using hh
          have h5 : (q n : ℝ)^8 ≤ (4 * (q n : ℝ))^8 := pow_le_pow_left₀ hqnn (by linarith) 8
          linarith
        linarith [h3]
      have hE : 2 * (4 * (q n : ℝ)) ^ 8 ≤ 10 ^ 6 * ((q n : ℝ) + 1) ^ 10 := by
        have hfour : (4 * (q n : ℝ)) ^ 8 = 65536 * (q n : ℝ) ^ 8 := by ring
        rw [hfour]
        have h1 : (q n : ℝ) ^ 8 ≤ ((q n : ℝ) + 1) ^ 10 := by
          have h2 : (q n : ℝ) ^ 8 ≤ ((q n : ℝ) + 1) ^ 8 := pow_le_pow_left₀ hqnn (by linarith) 8
          have h3 : ((q n : ℝ) + 1) ^ 8 ≤ ((q n : ℝ) + 1) ^ 10 :=
            pow_le_pow_right₀ (by linarith) (by norm_num)
          linarith
        nlinarith [h1]
      have hma : 2 * max (Real.rpow (q (n + 1) : ℝ) (8 / 9)) ((q n : ℝ) / 20)
          = max (2 * Real.rpow (q (n + 1) : ℝ) (8 / 9)) (2 * ((q n : ℝ) / 20)) :=
        mul_max_of_nonneg _ _ (by norm_num)
      have hml : max (2 * Real.rpow (q (n + 1) : ℝ) (8 / 9)) (2 * ((q n : ℝ) / 20))
          ≤ 10 ^ 6 * ((q n : ℝ) + 1) ^ 10 :=
        max_le (by linarith [hq8, hE]) (by linarith [hkey3, hE])
      linarith [hyb, hma, hml]

  have hBz : (((2 * |y| + 6 * (s:ℤ) * (q (n-1) : ℤ) + 4 : ℤ)) : ℝ) ≤
      2 * (y:ℝ) + 8 * (q n : ℝ) + 4 := by
    have heq : (((2 * |y| + 6 * (s:ℤ) * (q (n-1) : ℤ) + 4 : ℤ)) : ℝ)
        = 2*(y:ℝ) + 6*(s:ℝ)*(q (n-1):ℝ) + 4 := by
      rw [hyabs]; push_cast; ring
    rw [heq]
    have h2 : 6 * (s:ℝ) * (q (n-1) : ℝ) < 3 * (q n : ℝ) := by
      have hh : (6 * (s:ℤ) * (q (n-1) : ℤ) : ℤ) < 3 * (q n : ℤ) := by
        have h := hsL
        push_cast
        nlinarith [h]
      have h3 : ((6 * (s:ℤ) * (q (n-1) : ℤ) : ℤ) : ℝ) < ((3 * (q n : ℤ) : ℤ) : ℝ) := by
        exact_mod_cast hh
      push_cast at h3
      linarith
    linarith
  obtain ⟨c, hcpos, hc2, hcθ', hclog⟩ :=
    theta_charge_nr (α := α) (θ := θ) (K₀ := K₀z) (csm := csm) (q := q) (Δ := Δ)
      (n := n) (Bz := 2 * |y| + 6 * (s:ℤ) * (q (n-1) : ℤ) + 4) (B0 := 2 * (y : ℝ))
      hK₀1 hcsm hcsm1 h1 h2 hqpos hΔeq hΔup hn1 hbig (by linarith) hBz hcase
  have hcθ : ∀ j : ℤ, |j| ≤ 2 * |y| + 6 * (s : ℤ) * (q (n - 1) : ℤ) + 4 →
      c ≤ fracDist (2 * θ + (j : ℝ) * α) := hcθ'
  have hclog' : 2 * Real.log (1 / c) / ((s : ℝ) * (q (n-1) : ℝ))
      ≤ 2 * (Real.log (1 / csm) + 100 + 20 * Real.log ((q n : ℝ) + 2))
        / ((s : ℝ) * (q (n-1) : ℝ)) := by
    apply div_le_div_of_nonneg_right _ (by positivity)
    linarith [hclog]
  have hεuub : rateNR1 q n s c ≤ L / 8 + L / 100 := by
    simp only [rateNR1]
    linarith [hmain, hclog', hrest, hδb]
  have hblk : ∀ (p : ℤ) (ξ : ℝ) (k₀ : ℤ),
      k₀ ∈ Finset.Icc p (p + (q (n - 1) : ℤ) - 1) →
      (∀ k ∈ Finset.Icc p (p + (q (n - 1) : ℤ) - 1),
        |Real.sin (Real.pi * (ξ + (k : ℝ) * α))| ≥
          |Real.sin (Real.pi * (ξ + (k₀ : ℝ) * α))|) →
      |∑ k ∈ (Finset.Icc p (p + (q (n - 1) : ℤ) - 1)).erase k₀,
          Real.log |Real.sin (Real.pi * (ξ + (k : ℝ) * α))|
        + ((q (n - 1) : ℝ) - 1) * Real.log 2| ≤ 32 * Real.log (q (n - 1) : ℝ) :=
    fun p ξ k₀ hk hmin =>
      Core.irrat_blk_nr hqpos hmono hΔpos hΔeq hΔup hΔlo hbest hn1 hk hmin
  obtain ⟨Ksd, hKsd, hside'⟩ := hside
  obtain ⟨hK40, hKδ, hgap⟩ := hside' (rateNR1 q n s c) hεuub (Core.Knr q n s) hKsd
  exact Assembly.nr_case1_ge2 hlam hLlog hL hqpos hmono hΔpos hΔeq hΔup hΔlo hbest hblk
    hn hq1 hs hy1 hyΔ hym hym' hnres hsL hcpos hc2 hcθ hεuub hsin hbd hK40 hKδ hgap

/-! ## The `RegFamily` reduction

The output form: it suffices to produce, for every large `y`, a scale `K y → ∞` at which `y`
is `(L₁, K y)`-regular. -/

/-- **`RegFamily` from an eventual regularity statement at an unbounded scale.** -/
theorem regFamily_of_eventual {α lam θ E L₁ : ℝ} {K : ℤ → ℕ}
    (hL₁ : 0 < L₁)
    (hK : ∀ q : ℝ, 0 < q → ∃ b : ℝ, ∀ y : ℤ, b < (y : ℝ) → q ≤ (K y : ℝ))
    (hreg : ∃ Y : ℝ, ∀ y : ℤ, Y ≤ (y : ℝ) → IsRegularBig α lam θ E L₁ (K y : ℝ) y) :
    RegFamily α lam θ E := by
  refine ⟨L₁, hL₁, fun q hq => ?_⟩
  obtain ⟨b, hb⟩ := hK q hq
  obtain ⟨Y, hY⟩ := hreg
  refine ⟨max b Y, fun y hy => ?_⟩
  have h1 : b < (y : ℝ) := lt_of_le_of_lt (le_max_left _ _) hy
  have h2 : Y ≤ (y : ℝ) := le_trans (le_max_right _ _) hy.le
  exact IsRegularBig_mono (hb y h1) (hY y h2)

/-! ## Wrappers for the eventual inputs -/

/-- `Core.sing_zero` in `atTop`-threshold form. -/
theorem sing_zero_at {α lam θ : ℝ} {E : ℝ} {u : ℤ → ℂ}
    (hu : IsGenEigen α lam θ E u) (hu0 : u 0 ≠ 0) {m : ℝ} (hm : 0 < m) :
    ∃ N : ℕ, ∀ k : ℕ, N ≤ k → IsSingular α lam θ (E : ℂ) m k 0 :=
  Filter.eventually_atTop.mp (Core.sing_zero hu hu0 hm)

/-- `Core.pd_eventually_bound_dioph` in `atTop`-threshold form. -/
theorem pd_bound_at (h4 : P_LEBasics) (h7 : P_BJ_dioph) {α b₀ lam : ℝ}
    (hα : Irrational α) (hb₀ : 0 < b₀) (hD : DiophBelow α b₀)
    (hlam : Real.exp (16 * b₀ / 9) < lam) {E : ℝ} (hE : E ∈ amoSpec α lam) {ε : ℝ}
    (hε : 0 < ε) :
    ∃ N : ℕ, ∀ n : ℕ, N ≤ n → ∀ ζ : ℝ,
      ‖pd α lam ζ (E : ℂ) (n + 1)‖ ≤ Real.exp ((n : ℝ) * (Real.log lam + ε)) :=
  Filter.eventually_atTop.mp (Core.pd_eventually_bound_dioph h4 h7 hα hb₀ hD hlam hE hε)

/-- The numerical data of `cf_data_bridge` in named form. -/
theorem cf_data_of_dioph {α b₀ : ℝ} (hα : Irrational α) (hb₀ : 0 ≤ b₀)
    (hDioph : DiophBelow α b₀) {ε : ℝ} (hε : 0 < ε) :
    ∃ q : ℕ → ℕ, ∃ Δ : ℕ → ℝ,
      (∀ m, 0 < q m) ∧ StrictMono q ∧
      (∀ m, 1 ≤ m → q (m - 1) + 1 ≤ q m) ∧
      (∀ m, 0 < Δ m) ∧
      (∀ m, Δ m = fracDist ((q m : ℝ) * α)) ∧
      (∀ m, Δ m < 1 / ((q (m + 1) : ℝ))) ∧
      (∀ m, 1 / (((q (m + 1) : ℝ)) + (q m : ℝ)) < Δ m) ∧
      (∀ m k : ℕ, q m ≤ k → k < q (m + 1) →
        Δ m ≤ fracDist ((k : ℝ) * α)) ∧
      (∀ m j : ℕ, 1 ≤ j → 2 * j * q m ≤ q (m + 1) →
        (j : ℝ) * Δ m ≤ fracDist (((j * q m : ℕ) : ℝ) * α)) ∧
      (∀ᶠ m : ℕ in Filter.atTop,
        ((q (m + 1) : ℕ) : ℝ) ≤ Real.exp ((b₀ + ε) * (q m : ℝ))) :=
  CF.cf_data_bridge hα hb₀ hDioph hε

/-! ## The integrated `s ≥ 3` branch

`nr_branch_ge3` with its four "external" hypothesis groups discharged: the rate bound `hmain`
by `Main.rate_main_bound`, the numerical side conditions `hside` by `nr_side_conditions`
(in `∀`-form), and the singularity / Furman bounds `hsin`, `hbd` by their `atTop` thresholds.
The remaining hypotheses are all data at the level `n`. -/

/-- **The integrated `s ≥ 3` non-resonant branch of AJ Lemma 9.4(1).** -/
theorem nr_regular_ge3 {α lam L b₀ ε' δ : ℝ} {q : ℕ → ℕ} {Δ : ℕ → ℝ} {u : ℤ → ℂ}
    {n s m : ℕ} {y : ℤ} {θ : ℝ} {E : ℝ} {K₀z : ℤ} {csm : ℝ} {Ksd Nsin Nbd : ℕ}
    (h4 : P_LEBasics) (h7 : P_BJ_dioph) (hα : Irrational α) (hb₀ : 0 < b₀)
    (hD : DiophBelow α b₀) (hlam : Real.exp (16 * b₀ / 9) < lam) (hE : E ∈ amoSpec α lam)
    (hu : IsGenEigen α lam θ E u) (hu0 : u 0 ≠ 0)
    (hLlog : L = Real.log lam) (hL : 0 < L)
    (hqpos : ∀ i, 0 < q i) (hmono : StrictMono q) (hΔpos : ∀ i, 0 < Δ i)
    (hΔeq : ∀ i, Δ i = fracDist ((q i : ℝ) * α))
    (hΔup : ∀ i, Δ i < 1 / ((q (i + 1) : ℝ)))
    (hΔlo : ∀ i, 1 / (((q (i + 1) : ℝ)) + (q i : ℝ)) < Δ i)
    (hbest : ∀ i j : ℕ, q i ≤ j → j < q (i + 1) → Δ i ≤ fracDist ((j : ℝ) * α))
    (hn : 2 ≤ n) (hq1 : 1 ≤ q (n - 1)) (hs : 2 ≤ s) (hy1 : 1 ≤ y)
    (hyΔ : (y : ℝ) * Δ n ≤ 3 / 4)
    (hyb : (y : ℝ) ≤ max (Real.rpow (q (n + 1) : ℝ) (8 / 9)) ((q n : ℝ) / 20))
    (hym : (m : ℤ) * (q n : ℤ) ≤ y) (hym' : y < ((m : ℤ) + 1) * (q n : ℤ))
    (hnres : ∀ ℓ : ℤ, (s : ℤ) * (q (n - 1) : ℤ) ≤ |y - (ℓ : ℤ) * (q n : ℤ)|)
    (hsL : (2 * (s : ℤ)) * (q (n - 1) : ℤ) < (q n : ℤ))
    (hK₀1 : 1 ≤ K₀z) (hcsm : 0 < csm) (hcsm1 : csm ≤ 1 / 2)
    (h1 : ∀ k : ℤ, |k| < K₀z → csm ≤ fracDist (2 * θ + (k : ℝ) * α))
    (h2 : ∀ k : ℤ, K₀z ≤ |k| → ((((k.natAbs : ℕ) : ℝ))⁻¹) ^ 2 ≤
      fracDist (2 * θ + (k : ℝ) * α))
    (hbig : 10 ^ 6 ≤ csm * (q n : ℝ) ^ 2)
    (hKKsd : Ksd ≤ Core.Knr q n s)
    (hside0 : ∀ r : ℝ, r ≤ L / 8 + L / 100 → ∀ K : ℕ, Ksd ≤ K →
      40 ≤ K ∧ 1 ≤ (K : ℝ) * (cdelta L r - 1 / 40) ∧
      4 * ((K : ℝ) + 1) * Real.exp (L - epsA L r) <
        Real.exp ((K : ℝ) * (epsA L r - eps2 L)))
    (hsQ8 : (q n : ℝ) ^ (8 / 9 : ℝ) ≤ 2 * (s : ℝ) * (q (n - 1) : ℝ))
    (hlogq : Real.log (q n : ℝ) ≤ (b₀ + ε') * (q (n - 1) : ℝ))
    (hδ : 0 < δ) (hδb : (2 / 9) * (b₀ + ε') ≤ L / 8 - δ)
    (hrest : 2 * Real.log 2 / (q (n - 1) : ℝ)
        + 2 * Real.log (q (n - 1) : ℝ) / (q (n - 1) : ℝ)
        + 200 * Real.log (q (n - 1) : ℝ) / (q (n - 1) : ℝ)
        + 2 * (Real.log (1 / csm) + 100 + 20 * Real.log ((q n : ℝ) + 2))
          / ((s : ℝ) * (q (n - 1) : ℝ))
        + 200 / (q (n - 1) : ℝ) ≤ δ + L / 100)
    (hKNsin : Nsin ≤ Core.Knr q n s)
    (hsin0 : ∀ k : ℕ, Nsin ≤ k → IsSingular α lam θ (E : ℂ) (L - csing L) k 0)
    (hKNbd : Nbd ≤ Core.Knr q n s / 40)
    (hbd0 : ∀ N : ℕ, Nbd ≤ N → ∀ ζ : ℝ,
      ‖pd α lam ζ (E : ℂ) (N + 1)‖ ≤ Real.exp ((N : ℝ) * (L + eps2 L))) :
    IsRegularBig α lam θ (E : ℂ) (cL1 L) ((Core.Knr q n s : ℕ) : ℝ) y := by
  have hQpos : (0 : ℝ) < (q (n - 1) : ℝ) := by
    have := hq1
    exact_mod_cast (by omega : 0 < q (n - 1))
  have hqn1 : (1 : ℝ) ≤ (q n : ℝ) := by
    have hlt : q (n - 1) < q n := hmono (by omega)
    have h2' : (q (n - 1) : ℝ) + 1 ≤ (q n : ℝ) := by exact_mod_cast hlt
    linarith
  have hmain := rate_main_bound (b₀ := b₀) (ε' := ε') (q := q) (n := n) (s := s)
    (by omega) hsQ8 hqn1 hQpos hlogq
  exact nr_branch_ge3 (Core.one_lt_lam hb₀.le hlam) hLlog hL hqpos hmono hΔpos hΔeq hΔup hΔlo hbest hn hq1 hs hy1
    hyΔ hyb hym hym' hnres hsL hK₀1 hcsm hcsm1 h1 h2 hbig
    ⟨Ksd, hKKsd, hside0⟩ hmain hδ hδb hrest (hsin0 _ hKNsin)
    (fun N h1 h2 ζ => hbd0 N (le_trans hKNbd h1) ζ)

/-! ## Deriving `hsQ8` from non-resonance

`hsQ8 : q_n^{8/9} ≤ 2 s q(n-1)` is the input of `rate_main_bound`, i.e. of the main term of
the uniformity rate.  It is a consequence of the *non-resonance* lower bound
`q_n^{8/9} < k₀ = dist (y, q_n ℤ)`, of `s ≥ 1`, and of the defining property
`s q(n-1) ≤ k₀ < (s+1) q(n-1)`. -/

/-- **`hsQ8` from non-resonance.** -/
theorem hsQ8_of_nonres {q : ℕ → ℕ} {n s : ℕ} {k₀ : ℤ}
    (hs : 1 ≤ s)
    (hsle : ((s : ℤ)) * (q (n - 1) : ℤ) ≤ k₀)
    (hslt : k₀ < ((s : ℤ) + 1) * (q (n - 1) : ℤ))
    (hk0lo : Real.rpow (q n : ℝ) (8 / 9) < (k₀ : ℝ)) :
    (q n : ℝ) ^ (8 / 9 : ℝ) ≤ 2 * (s : ℝ) * (q (n - 1) : ℝ) := by
  have hsR : (1 : ℝ) ≤ (s : ℝ) := by exact_mod_cast hs
  have hQnn : (0 : ℝ) ≤ (q (n - 1) : ℝ) := by positivity
  have h1 : (k₀ : ℝ) < ((s : ℝ) + 1) * (q (n - 1) : ℝ) := by
    have h := hslt
    have h' : ((k₀ : ℤ) : ℝ) < (((s : ℤ) + 1) * (q (n - 1) : ℤ) : ℝ) := by exact_mod_cast h
    push_cast at h'
    linarith
  have h2 : ((s : ℝ) + 1) * (q (n - 1) : ℝ) ≤ 2 * (s : ℝ) * (q (n - 1) : ℝ) := by
    nlinarith [hsR, hQnn]
  exact le_trans hk0lo.le (le_trans h1.le h2)

/-! ## `K = 2 s q(n-1) - 1` grows -/

/-- For every bound `M`, the scale `Knr q n s = 2 s q(n-1) - 1` exceeds `M` for all large `n`,
uniformly in `s ≥ 3`. -/
theorem knr_ge_of_large {q : ℕ → ℕ} (hqpos : ∀ i, 0 < q i) (hmono : StrictMono q)
    (M : ℕ) : ∃ N : ℕ, ∀ n : ℕ, N ≤ n → ∀ s : ℕ, 3 ≤ s → M ≤ Core.Knr q n s := by
  have h1 : ∀ᶠ m : ℕ in Filter.atTop, ((M : ℝ) + 1) / 6 ≤ (q m : ℝ) :=
    (tendsto_natCast_atTop_atTop.comp hmono.tendsto_atTop).eventually_ge_atTop _
  obtain ⟨N, hN⟩ := Filter.eventually_atTop.mp h1
  refine ⟨N + 1, fun n hn s hs => ?_⟩
  have hQ : ((M : ℝ) + 1) / 6 ≤ (q (n - 1) : ℝ) := hN (n - 1) (by omega)
  have hq1 : 1 ≤ q (n - 1) := hqpos (n - 1)
  have hs1 : 1 ≤ s := by omega
  have hcast : (Core.Knr q n s : ℝ) = 2 * (s : ℝ) * (q (n - 1) : ℝ) - 1 :=
    knr_castR hs1 hq1
  have hsR : (3 : ℝ) ≤ (s : ℝ) := by exact_mod_cast hs
  have hQ6 : (M : ℝ) + 1 ≤ 6 * (q (n - 1) : ℝ) := by
    have h := (div_le_iff₀ (by norm_num : (0:ℝ) < 6)).mp hQ
    linarith [h]
  have hQnn : (0 : ℝ) ≤ (q (n - 1) : ℝ) := by positivity
  have hbig : (M : ℝ) ≤ 2 * (s : ℝ) * (q (n - 1) : ℝ) - 1 := by
    have h6 : 6 * (q (n - 1) : ℝ) ≤ 2 * (s : ℝ) * (q (n - 1) : ℝ) := by
      have h2s : (6:ℝ) ≤ 2 * (s : ℝ) := by linarith
      have hc := mul_le_mul_of_nonneg_right h2s hQnn
      calc 6 * (q (n - 1) : ℝ) ≤ (2 * (s : ℝ)) * (q (n - 1) : ℝ) := hc
        _ = 2 * (s : ℝ) * (q (n - 1) : ℝ) := by ring
    linarith [hQ6, h6]
  have hgoal : (M : ℝ) ≤ (Core.Knr q n s : ℝ) := by rw [hcast]; exact hbig
  exact_mod_cast hgoal

/-! ## The `s ≥ 3` branch with the eventual data supplied -/

/-- **`nr_regular_ge3` with the "for large `n`" data supplied by a single hypothesis**
(`nr_data_eventual`'s conclusion form) and the threshold inequalities `Ksd, Nsin, Nbd ≤ Knr`
replaced by one bound. -/
theorem nr_regular_ge3_large {α lam L b₀ ε' δ : ℝ} {q : ℕ → ℕ} {Δ : ℕ → ℝ} {u : ℤ → ℂ}
    {n s m : ℕ} {y : ℤ} {θ : ℝ} {E : ℝ} {K₀z : ℤ} {csm : ℝ} {Ksd Nsin Nbd Ndata : ℕ}
    (h4 : P_LEBasics) (h7 : P_BJ_dioph) (hα : Irrational α) (hb₀ : 0 < b₀)
    (hD : DiophBelow α b₀) (hlam : Real.exp (16 * b₀ / 9) < lam) (hE : E ∈ amoSpec α lam)
    (hu : IsGenEigen α lam θ E u) (hu0 : u 0 ≠ 0)
    (hLlog : L = Real.log lam) (hL : 0 < L)
    (hqpos : ∀ i, 0 < q i) (hmono : StrictMono q) (hΔpos : ∀ i, 0 < Δ i)
    (hΔeq : ∀ i, Δ i = fracDist ((q i : ℝ) * α))
    (hΔup : ∀ i, Δ i < 1 / ((q (i + 1) : ℝ)))
    (hΔlo : ∀ i, 1 / (((q (i + 1) : ℝ)) + (q i : ℝ)) < Δ i)
    (hbest : ∀ i j : ℕ, q i ≤ j → j < q (i + 1) → Δ i ≤ fracDist ((j : ℝ) * α))
    (hn : 2 ≤ n) (hq1 : 1 ≤ q (n - 1)) (hs : 2 ≤ s) (hy1 : 1 ≤ y)
    (hyΔ : (y : ℝ) * Δ n ≤ 3 / 4)
    (hyb : (y : ℝ) ≤ max (Real.rpow (q (n + 1) : ℝ) (8 / 9)) ((q n : ℝ) / 20))
    (hym : (m : ℤ) * (q n : ℤ) ≤ y) (hym' : y < ((m : ℤ) + 1) * (q n : ℤ))
    (hnres : ∀ ℓ : ℤ, (s : ℤ) * (q (n - 1) : ℤ) ≤ |y - (ℓ : ℤ) * (q n : ℤ)|)
    (hsL : (2 * (s : ℤ)) * (q (n - 1) : ℤ) < (q n : ℤ))
    (hK₀1 : 1 ≤ K₀z) (hcsm : 0 < csm) (hcsm1 : csm ≤ 1 / 2)
    (h1 : ∀ k : ℤ, |k| < K₀z → csm ≤ fracDist (2 * θ + (k : ℝ) * α))
    (h2 : ∀ k : ℤ, K₀z ≤ |k| → ((((k.natAbs : ℕ) : ℝ))⁻¹) ^ 2 ≤
      fracDist (2 * θ + (k : ℝ) * α))
    (hKbig : max Ksd (max Nsin (40 * Nbd)) ≤ Core.Knr q n s)
    (hside0 : ∀ r : ℝ, r ≤ L / 8 + L / 100 → ∀ K : ℕ, Ksd ≤ K →
      40 ≤ K ∧ 1 ≤ (K : ℝ) * (cdelta L r - 1 / 40) ∧
      4 * ((K : ℝ) + 1) * Real.exp (L - epsA L r) <
        Real.exp ((K : ℝ) * (epsA L r - eps2 L)))
    (hdata : ∀ n' : ℕ, Ndata ≤ n' → ∀ s' : ℕ, 1 ≤ s' →
      (q n' : ℝ) ^ (8 / 9 : ℝ) ≤ 2 * (s' : ℝ) * (q (n' - 1) : ℝ) →
      10 ^ 6 ≤ csm * (q n' : ℝ) ^ 2 ∧
      Real.log (q n' : ℝ) ≤ (b₀ + ε') * (q (n' - 1) : ℝ) ∧
      2 * Real.log 2 / (q (n' - 1) : ℝ)
        + 2 * Real.log (q (n' - 1) : ℝ) / (q (n' - 1) : ℝ)
        + 200 * Real.log (q (n' - 1) : ℝ) / (q (n' - 1) : ℝ)
        + 2 * (Real.log (1 / csm) + 100 + 20 * Real.log ((q n' : ℝ) + 2))
          / ((s' : ℝ) * (q (n' - 1) : ℝ))
        + 200 / (q (n' - 1) : ℝ) ≤ δ + L / 100)
    (hNdata : Ndata ≤ n)
    (hsQ8 : (q n : ℝ) ^ (8 / 9 : ℝ) ≤ 2 * (s : ℝ) * (q (n - 1) : ℝ))
    (hδ : 0 < δ) (hδb : (2 / 9) * (b₀ + ε') ≤ L / 8 - δ)
    (hsin0 : ∀ k : ℕ, Nsin ≤ k → IsSingular α lam θ (E : ℂ) (L - csing L) k 0)
    (hbd0 : ∀ N : ℕ, Nbd ≤ N → ∀ ζ : ℝ,
      ‖pd α lam ζ (E : ℂ) (N + 1)‖ ≤ Real.exp ((N : ℝ) * (L + eps2 L))) :
    IsRegularBig α lam θ (E : ℂ) (cL1 L) ((Core.Knr q n s : ℕ) : ℝ) y := by
  obtain ⟨hbig, hlogq, hrest⟩ := hdata n hNdata s (by omega) hsQ8
  have hKKsd : Ksd ≤ Core.Knr q n s := le_trans (le_max_left _ _) hKbig
  have hKNsin : Nsin ≤ Core.Knr q n s :=
    le_trans (le_trans (le_max_left _ _) (le_max_right _ _)) hKbig
  have hKNbd : Nbd ≤ Core.Knr q n s / 40 := by
    have h40 : 40 * Nbd ≤ Core.Knr q n s :=
      le_trans (le_trans (le_max_right _ _) (le_max_right _ _)) hKbig
    omega
  exact nr_regular_ge3 h4 h7 hα hb₀ hD hlam hE hu hu0 hLlog hL hqpos hmono hΔpos hΔeq
    hΔup hΔlo hbest hn hq1 hs hy1 hyΔ hyb hym hym' hnres hsL hK₀1 hcsm hcsm1 h1 h2 hbig
    hKKsd hside0 hsQ8 hlogq hδ hδb hrest hKNsin hsin0 hKNbd hbd0

/-! ## The `s = 1` windows (AJ Lemma 9.4(1), odd-cardinality case)

For `s = 1` AJ's two windows have `q(n-1)` *sites* each (not `2a' q(n-1)`), so they are not
representable by `Core.I1nr`/`I2nr`: `J1s1 Q` is the block of `Q` sites centred at `0`, and
`J2s1 Q y` its translate by `y`.  The scale is `2 Q - 1 = 2 q(n-1) - 1`. -/

/-- The left `s = 1` window: `Q` sites centred at `0`. -/
def J1s1 (Q : ℕ) : Finset ℤ :=
  Finset.Icc (-(((Q / 2 : ℕ)) : ℤ)) ((Q : ℤ) - (((Q / 2 : ℕ)) : ℤ) - 1)

/-- The right `s = 1` window: the translate of `J1s1 Q` by `y`. -/
def J2s1 (Q : ℕ) (y : ℤ) : Finset ℤ :=
  Finset.Icc (y - (((Q / 2 : ℕ)) : ℤ)) (y + (Q : ℤ) - (((Q / 2 : ℕ)) : ℤ) - 1)

/-- `J1s1 Q` has `Q` elements. -/
theorem card_J1s1 (Q : ℕ) : (J1s1 Q).card = Q := by
  rw [J1s1, Int.card_Icc]
  have h : ((Q : ℤ) - (((Q / 2 : ℕ)) : ℤ) - 1 + 1 - (-(((Q / 2 : ℕ)) : ℤ)) : ℤ) = (Q : ℤ) := by
    ring
  rw [h, Int.toNat_natCast]

/-- `J2s1 Q y` has `Q` elements. -/
theorem card_J2s1 (Q : ℕ) (y : ℤ) : (J2s1 Q y).card = Q := by
  rw [J2s1, Int.card_Icc]
  have h : (y + (Q : ℤ) - (((Q / 2 : ℕ)) : ℤ) - 1 + 1 - (y - (((Q / 2 : ℕ)) : ℤ)) : ℤ) = (Q : ℤ) := by
    ring
  rw [h, Int.toNat_natCast]

/-! ## The non-resonant `s ≥ 2` branch, fully assembled

All the "for large `n`" data of `nr_regular_ge3_large` is derived here: `hdata` from
`Main.nr_data_eventual`, `hsQ8` from `Main.hsQ8_of_nonres` (using the non-resonance
`q_n^{8/9} < k₀`), and `hnres` from the distance comparison `k₀ ≤ |y - ℓ q_n|`. -/

/-- **AJ Lemma 9.4(1) for `s ≥ 2`, non-resonant, with the level data as hypotheses.** -/
theorem nr_nonres_ge2 {α lam L b₀ ε' δ : ℝ} {q : ℕ → ℕ} {Δ : ℕ → ℝ} {u : ℤ → ℂ}
    {n s m : ℕ} {y : ℤ} {k₀ : ℤ} {θ : ℝ} {E : ℝ} {K₀z : ℤ} {csm : ℝ}
    {Ksd Nsin Nbd : ℕ}
    (h4 : P_LEBasics) (h7 : P_BJ_dioph) (hα : Irrational α) (hb₀ : 0 < b₀)
    (hD : DiophBelow α b₀) (hlam : Real.exp (16 * b₀ / 9) < lam) (hE : E ∈ amoSpec α lam)
    (hu : IsGenEigen α lam θ E u) (hu0 : u 0 ≠ 0)
    (hLlog : L = Real.log lam) (hL : 0 < L)
    (hqpos : ∀ i, 0 < q i) (hmono : StrictMono q) (hΔpos : ∀ i, 0 < Δ i)
    (hΔeq : ∀ i, Δ i = fracDist ((q i : ℝ) * α))
    (hΔup : ∀ i, Δ i < 1 / ((q (i + 1) : ℝ)))
    (hΔlo : ∀ i, 1 / (((q (i + 1) : ℝ)) + (q i : ℝ)) < Δ i)
    (hbest : ∀ i j : ℕ, q i ≤ j → j < q (i + 1) → Δ i ≤ fracDist ((j : ℝ) * α))
    (hgr : ∀ᶠ m : ℕ in Filter.atTop, (q (m + 1) : ℝ) ≤ Real.exp ((b₀ + ε') * (q m : ℝ)))
    (hn : 2 ≤ n) (hq1 : 1 ≤ q (n - 1)) (hs : 2 ≤ s) (hy1 : 1 ≤ y)
    (hyΔ : (y : ℝ) * Δ n ≤ 3 / 4)
    (hyb : (y : ℝ) ≤ max (Real.rpow (q (n + 1) : ℝ) (8 / 9)) ((q n : ℝ) / 20))
    (hym : (m : ℤ) * (q n : ℤ) ≤ y) (hym' : y < ((m : ℤ) + 1) * (q n : ℤ))
    (hk0nn : 0 ≤ k₀) (hk0le : k₀ ≤ (q n : ℤ) / 2)
    (hk0le2 : ((s : ℤ)) * (q (n - 1) : ℤ) ≤ k₀)
    (hk0lt : k₀ < ((s : ℤ) + 1) * (q (n - 1) : ℤ))
    (hk0lo : Real.rpow (q n : ℝ) (8 / 9) < (k₀ : ℝ))
    (hk0dist : ∀ ℓ : ℤ, k₀ ≤ |y - (ℓ : ℤ) * (q n : ℤ)|)
    (hsL : (2 * (s : ℤ)) * (q (n - 1) : ℤ) < (q n : ℤ))
    (hK₀1 : 1 ≤ K₀z) (hcsm : 0 < csm) (hcsm1 : csm ≤ 1 / 2)
    (h1 : ∀ k : ℤ, |k| < K₀z → csm ≤ fracDist (2 * θ + (k : ℝ) * α))
    (h2 : ∀ k : ℤ, K₀z ≤ |k| → ((((k.natAbs : ℕ) : ℝ))⁻¹) ^ 2 ≤
      fracDist (2 * θ + (k : ℝ) * α))
    (hKbig : max Ksd (max Nsin (40 * Nbd)) ≤ Core.Knr q n s)
    (hside0 : ∀ r : ℝ, r ≤ L / 8 + L / 100 → ∀ K : ℕ, Ksd ≤ K →
      40 ≤ K ∧ 1 ≤ (K : ℝ) * (cdelta L r - 1 / 40) ∧
      4 * ((K : ℝ) + 1) * Real.exp (L - epsA L r) <
        Real.exp ((K : ℝ) * (epsA L r - eps2 L)))
    (hδ : 0 < δ) (hδb : (2 / 9) * (b₀ + ε') ≤ L / 8 - δ)
    (hsin0 : ∀ k : ℕ, Nsin ≤ k → IsSingular α lam θ (E : ℂ) (L - csing L) k 0)
    (hbd0 : ∀ N : ℕ, Nbd ≤ N → ∀ ζ : ℝ,
      ‖pd α lam ζ (E : ℂ) (N + 1)‖ ≤ Real.exp ((N : ℝ) * (L + eps2 L)))
    (Ndat : ℕ) (hNdat : Ndat ≤ n)
    (hdata : ∀ n' : ℕ, Ndat ≤ n' → ∀ s' : ℕ, 1 ≤ s' →
      (q n' : ℝ) ^ (8 / 9 : ℝ) ≤ 2 * (s' : ℝ) * (q (n' - 1) : ℝ) →
      10 ^ 6 ≤ csm * (q n' : ℝ) ^ 2 ∧
      Real.log (q n' : ℝ) ≤ (b₀ + ε') * (q (n' - 1) : ℝ) ∧
      2 * Real.log 2 / (q (n' - 1) : ℝ)
        + 2 * Real.log (q (n' - 1) : ℝ) / (q (n' - 1) : ℝ)
        + 200 * Real.log (q (n' - 1) : ℝ) / (q (n' - 1) : ℝ)
        + 2 * (Real.log (1 / csm) + 100 + 20 * Real.log ((q n' : ℝ) + 2))
          / ((s' : ℝ) * (q (n' - 1) : ℝ))
        + 200 / (q (n' - 1) : ℝ) ≤ δ + L / 100) :
    IsRegularBig α lam θ (E : ℂ) (cL1 L) ((Core.Knr q n s : ℕ) : ℝ) y := by
  have hsQ8 : (q n : ℝ) ^ (8 / 9 : ℝ) ≤ 2 * (s : ℝ) * (q (n - 1) : ℝ) :=
    hsQ8_of_nonres (by omega : 1 ≤ s) hk0le2 hk0lt hk0lo
  have hnres : ∀ ℓ : ℤ, (s : ℤ) * (q (n - 1) : ℤ) ≤ |y - (ℓ : ℤ) * (q n : ℤ)| :=
    fun ℓ => le_trans hk0le2 (hk0dist ℓ)
  exact nr_regular_ge3_large h4 h7 hα hb₀ hD hlam hE hu hu0 hLlog hL hqpos hmono hΔpos
    hΔeq hΔup hΔlo hbest hn hq1 hs hy1 hyΔ hyb hym hym' hnres hsL hK₀1 hcsm hcsm1 h1 h2
    hKbig hside0 hdata hNdat hsQ8 hδ hδb hsin0 hbd0

end

end Work.TMC16Core.Main
