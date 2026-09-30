import Mathlib
import Submission.Work.BMF.Defs
import Submission.Work.BMF.vk_L_lower
import Submission.Work.BMF.vk_L_upper

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false

/-!
# Shared preliminaries for the Vinogradov–Korobov log-derivative bound (V4)

Vocabulary used by `Work.BMF.logDeriv_LFunction_VK` and by the auxiliary lemmas it is
assembled from:

* `VKA t = log(|t|+3)`, `VKE N t = log(N+2) + log log(|t|+3)`,
  `VKD N t = VKA t ^ (5/6) * VKE N t` — the only combination of logarithms that occurs in the
  Vinogradov–Korobov zero-free region and in the target bound.

* `riemannZeta_re_le_one_add_inv` — the elementary bound `ζ(σ) ≤ 1 + 1/(σ-1)` for `1 < σ`,
  which gives both `|L(1+h+it,χ)| ≫ h` (lower bound at the centre of the disc) and
  `|L(w,χ)| ≤ 2` for `Re w ≥ 2` (growth bound on the far right of the disc).
-/

namespace Work.BMF

open Complex

/-- `A(t) = log(|t|+3)`, the height logarithm. -/
noncomputable def VKA (t : ℝ) : ℝ := Real.log (|t| + 3)

/-- `E(N,t) = log(N+2) + log log(|t|+3)`. -/
noncomputable def VKE (N : ℕ) (t : ℝ) : ℝ := Real.log ((N : ℝ) + 2) + Real.log (VKA t)

/-- `D(N,t) = (log(|t|+3))^{5/6} · (log(N+2) + log log(|t|+3))`, the Vinogradov–Korobov
denominator of the region. -/
noncomputable def VKD (N : ℕ) (t : ℝ) : ℝ := VKA t ^ (5 / 6 : ℝ) * VKE N t

lemma VKA_eq (t : ℝ) : VKA t = Real.log (|t| + 3) := rfl

lemma VKE_eq (N : ℕ) (t : ℝ) :
    VKE N t = Real.log ((N : ℝ) + 2) + Real.log (Real.log (|t| + 3)) := rfl

lemma VKE_eq' (N : ℕ) (t : ℝ) : VKE N t = Real.log ((N : ℝ) + 2) + Real.log (VKA t) := rfl

lemma VKD_eq' (N : ℕ) (t : ℝ) : VKD N t = VKA t ^ (5 / 6 : ℝ) * VKE N t := rfl

lemma VKD_eq (N : ℕ) (t : ℝ) :
    VKD N t = Real.log (|t| + 3) ^ (5 / 6 : ℝ) *
      (Real.log ((N : ℝ) + 2) + Real.log (Real.log (|t| + 3))) := rfl

/-- `log 3 ≥ 1`. -/
lemma log_three_ge_one : (1 : ℝ) ≤ Real.log 3 := by
  rw [Real.le_log_iff_exp_le (by norm_num : (0 : ℝ) < 3)]
  exact Real.exp_one_lt_three.le

/-- For `|t| ≥ 3` the height logarithm is at least `1`. -/
lemma one_le_VKA {t : ℝ} (ht : 3 ≤ |t|) : (1 : ℝ) ≤ VKA t := by
  rw [VKA_eq]
  exact le_trans log_three_ge_one (Real.log_le_log (by norm_num) (by linarith))

lemma VKA_pos {t : ℝ} (ht : 3 ≤ |t|) : 0 < VKA t := lt_of_lt_of_le zero_lt_one (one_le_VKA ht)

lemma VKA_nonneg {t : ℝ} (ht : 3 ≤ |t|) : 0 ≤ VKA t := (VKA_pos ht).le

/-- `E(N,t) ≥ 1` in the whole range of the statement. -/
lemma one_le_VKE (N : ℕ) [NeZero N] {t : ℝ} (ht : 3 ≤ |t|) : (1 : ℝ) ≤ VKE N t := by
  have h1 : (1 : ℝ) ≤ Real.log ((N : ℝ) + 2) := by
    refine le_trans log_three_ge_one ?_
    refine Real.log_le_log (by norm_num) ?_
    have : (1 : ℝ) ≤ (N : ℝ) := by exact_mod_cast Nat.one_le_iff_ne_zero.mpr (NeZero.ne N)
    linarith
  have h2 : 0 ≤ Real.log (Real.log (|t| + 3)) :=
    Real.log_nonneg (by rw [← VKA_eq]; exact one_le_VKA ht)
  rw [VKE_eq]
  linarith

lemma VKE_pos (N : ℕ) [NeZero N] {t : ℝ} (ht : 3 ≤ |t|) : 0 < VKE N t :=
  lt_of_lt_of_le zero_lt_one (one_le_VKE N ht)

lemma VKE_nonneg (N : ℕ) [NeZero N] {t : ℝ} (ht : 3 ≤ |t|) : 0 ≤ VKE N t :=
  (VKE_pos N ht).le

lemma VKD_pos (N : ℕ) [NeZero N] {t : ℝ} (ht : 3 ≤ |t|) : 0 < VKD N t := by
  rw [VKD_eq]
  exact mul_pos (Real.rpow_pos_of_pos (VKA_pos ht) _) (VKE_pos N ht)

lemma VKD_nonneg (N : ℕ) [NeZero N] {t : ℝ} (ht : 3 ≤ |t|) : 0 ≤ VKD N t :=
  (VKD_pos N ht).le

lemma one_le_VKD (N : ℕ) [NeZero N] {t : ℝ} (ht : 3 ≤ |t|) : 1 ≤ VKD N t := by
  rw [VKD_eq']
  have h1 : (1 : ℝ) ≤ VKA t ^ (5 / 6 : ℝ) := Real.one_le_rpow (one_le_VKA ht) (by norm_num)
  have h2 : (1 : ℝ) ≤ VKE N t := one_le_VKE N ht
  calc (1 : ℝ) = 1 * 1 := by ring
    _ ≤ VKA t ^ (5 / 6 : ℝ) * VKE N t :=
        mul_le_mul h1 h2 (by linarith) (Real.rpow_nonneg (VKA_nonneg ht) _)

/-! ## Shifting the height -/

/-- `|v| ≤ |t| + 1` when `|v - t| ≤ 1`. -/
lemma abs_le_abs_add_one {t v : ℝ} (hv : |v - t| ≤ 1) : |v| ≤ |t| + 1 := by
  have h : |v| = |(v - t) + t| := by ring_nf
  rw [h]
  linarith [abs_add_le (v - t) t]

/-- For `|v - t| ≤ 1` and `4 ≤ |t|` one has `3 ≤ |v|`. -/
lemma three_le_abs_of_shift {t v : ℝ} (ht : 4 ≤ |t|) (hv : |v - t| ≤ 1) : 3 ≤ |v| := by
  have h1 : |t| - |v| ≤ |t - v| := abs_sub_abs_le_abs_sub t v
  have h2 : |t - v| = |v - t| := abs_sub_comm t v
  rw [h2] at h1
  linarith

/-- Shifting the height by at most `1` (below `|t| ≥ 4`) changes `VKA` by at most a factor `2`. -/
lemma VKA_shift_le {t v : ℝ} (ht : 4 ≤ |t|) (htv : |v - t| ≤ 1) : VKA v ≤ 2 * VKA t := by
  rw [VKA_eq, VKA_eq]
  have h1 : |v| + 3 ≤ 2 * (|t| + 3) := by linarith [abs_le_abs_add_one htv, abs_nonneg t]
  have h3 : 0 < |v| + 3 := by linarith [abs_nonneg v]
  have hpos : 0 < |t| + 3 := by linarith [abs_nonneg t]
  have h4 : Real.log 2 ≤ Real.log (|t| + 3) := by
    refine Real.log_le_log (by norm_num) ?_
    linarith [one_le_VKA (by linarith : (3:ℝ) ≤ |t|)]
  calc Real.log (|v| + 3) ≤ Real.log (2 * (|t| + 3)) := Real.log_le_log h3 h1
    _ = Real.log 2 + Real.log (|t| + 3) := Real.log_mul (by norm_num) (ne_of_gt hpos)
    _ ≤ Real.log (|t| + 3) + Real.log (|t| + 3) := by linarith
    _ = 2 * Real.log (|t| + 3) := by ring

/-- Shifting the height by at most `1` changes `VKE` by at most a factor `2`. -/
lemma VKE_shift_le (N : ℕ) [NeZero N] {t v : ℝ} (ht : 4 ≤ |t|) (htv : |v - t| ≤ 1) :
    VKE N v ≤ 2 * VKE N t := by
  have hvt : 3 ≤ |v| := three_le_abs_of_shift ht htv
  have hA : VKA v ≤ 2 * VKA t := VKA_shift_le ht htv
  have hAv : 0 < VKA v := VKA_pos hvt
  have hAt : 0 < VKA t := VKA_pos (by linarith)
  have hAt0 : 0 ≤ Real.log (VKA t) := Real.log_nonneg (one_le_VKA (by linarith))
  have hlogA : Real.log (VKA v) ≤ Real.log 2 + Real.log (VKA t) := by
    calc Real.log (VKA v) ≤ Real.log (2 * VKA t) := Real.log_le_log hAv hA
      _ = Real.log 2 + Real.log (VKA t) := Real.log_mul (by norm_num) (ne_of_gt hAt)
  have hlog2 : Real.log 2 ≤ Real.log ((N : ℝ) + 2) := by
    refine Real.log_le_log (by norm_num) ?_
    have h : (1 : ℝ) ≤ (N : ℝ) := by exact_mod_cast Nat.one_le_iff_ne_zero.mpr (NeZero.ne N)
    linarith
  rw [VKE_eq', VKE_eq']
  linarith

/-- Shifting the height by at most `1` changes the Vinogradov–Korobov denominator `VKD` by at
most a factor `4`. -/
lemma VKD_shift_le (N : ℕ) [NeZero N] {t v : ℝ} (ht : 4 ≤ |t|) (htv : |v - t| ≤ 1) :
    VKD N v ≤ 4 * VKD N t := by
  have hvt : 3 ≤ |v| := three_le_abs_of_shift ht htv
  have hA : VKA v ≤ 2 * VKA t := VKA_shift_le ht htv
  have hE : VKE N v ≤ 2 * VKE N t := VKE_shift_le N ht htv
  have hAv : 0 ≤ VKA v := (VKA_pos hvt).le
  have hAt : 0 ≤ VKA t := (VKA_pos (by linarith)).le
  have hEv : 0 ≤ VKE N v := (VKE_pos N hvt).le
  have hEt : 0 ≤ VKE N t := (VKE_pos N (by linarith)).le
  have hpow : VKA v ^ (5 / 6 : ℝ) ≤ (2 * VKA t) ^ (5 / 6 : ℝ) :=
    Real.rpow_le_rpow hAv hA (by norm_num)
  have hmul : (2 * VKA t) ^ (5 / 6 : ℝ) = (2 : ℝ) ^ (5 / 6 : ℝ) * VKA t ^ (5 / 6 : ℝ) :=
    Real.mul_rpow (by norm_num) hAt
  have h2 : (2 : ℝ) ^ (5 / 6 : ℝ) ≤ 2 := by
    have h := Real.rpow_le_rpow_of_exponent_le (x := (2 : ℝ)) (by norm_num)
      (y := (5 / 6 : ℝ)) (z := (1 : ℝ)) (by norm_num)
    simpa using h
  have hVt : 0 ≤ VKA t ^ (5 / 6 : ℝ) * VKE N t :=
    mul_nonneg (Real.rpow_nonneg hAt _) hEt
  rw [VKD_eq', VKD_eq']
  calc VKA v ^ (5 / 6 : ℝ) * VKE N v
      ≤ ((2 : ℝ) ^ (5 / 6 : ℝ) * VKA t ^ (5 / 6 : ℝ)) * (2 * VKE N t) := by
        refine mul_le_mul ?_ hE hEv (by positivity)
        rwa [hmul] at hpow
    _ = ((2 : ℝ) ^ (5 / 6 : ℝ) * 2) * (VKA t ^ (5 / 6 : ℝ) * VKE N t) := by ring
    _ ≤ 4 * (VKA t ^ (5 / 6 : ℝ) * VKE N t) := by
        refine mul_le_mul_of_nonneg_right ?_ hVt
        linarith

/-! ## The elementary upper bound for `ζ` to the right of `1` -/

/-- The shifted real series `Σ_{n} 1/(n+1)^σ` is summable for `σ > 1`. -/
private lemma summable_shifted (σ : ℝ) (hσ : 1 < σ) :
    Summable (fun n : ℕ => (1 : ℝ) / (((n + 1 : ℕ) : ℝ) ^ σ)) := by
  have hs : Summable (fun n : ℕ => ((n : ℝ) ^ σ)⁻¹) := (Real.summable_nat_rpow_inv (p := σ)).2 hσ
  have hshift : Summable (fun n : ℕ => ((n + 1 : ℕ) : ℝ) ^ (-σ)) := by
    have h := (summable_nat_add_iff 1).mpr hs
    refine h.congr (fun n => ?_)
    rw [Real.rpow_neg (Nat.cast_nonneg (n + 1))]
  refine hshift.congr (fun n => ?_)
  rw [Real.rpow_neg (Nat.cast_nonneg (n + 1))]
  simp [one_div]

/-- Norm of the `n`-th summand of the shifted series, as a complex number. -/
private lemma norm_summand (n : ℕ) (σ : ℝ) :
    ‖(1 : ℂ) / ((((n : ℕ) : ℂ) + 1) ^ (σ : ℂ))‖ = (1 : ℝ) / (((n + 1 : ℕ) : ℝ) ^ σ) := by
  have hbase : (((n : ℕ) : ℂ) + 1) = (((n + 1 : ℕ) : ℂ)) := by norm_num
  rw [hbase, norm_div, norm_one]
  have hnormpow : ‖(((n + 1 : ℕ) : ℂ) ^ (σ : ℂ))‖ = (((n + 1 : ℕ) : ℝ) ^ σ) := by
    have hn := Complex.norm_natCast_cpow_of_pos (by omega : 0 < n + 1) (σ : ℂ)
    have hre : ((σ : ℂ)).re = σ := by simp
    rwa [hre] at hn
  rw [hnormpow]

/-- **The elementary bound `ζ(σ) ≤ 1 + 1/(σ-1)` for real `σ > 1`.** -/
theorem riemannZeta_norm_le_one_add_inv (σ : ℝ) (hσ : 1 < σ) :
    ‖riemannZeta ((σ : ℝ) : ℂ)‖ ≤ 1 + 1 / (σ - 1) := by
  let Zσ : ℝ := ∑' n : ℕ, (1 : ℝ) / (((n + 1 : ℕ) : ℝ) ^ σ)
  have hsC : 1 < (((σ : ℝ) : ℂ)).re := by simpa using hσ
  have hze := zeta_eq_tsum_one_div_nat_add_one_cpow (s := (σ : ℂ)) hsC
  have hsumNorm : Summable (fun n : ℕ => ‖(1 : ℂ) / ((((n : ℕ) : ℂ) + 1) ^ (σ : ℂ))‖) := by
    exact (summable_shifted σ hσ).congr (fun n => (norm_summand n σ).symm)
  have hnorm : ‖riemannZeta (σ : ℂ)‖ ≤ Zσ := by
    calc
      ‖riemannZeta (σ : ℂ)‖ = ‖(∑' n : ℕ, (1 : ℂ) / ((((n : ℕ) : ℂ) + 1) ^ (σ : ℂ)))‖ := by
            rw [hze]
      _ ≤ ∑' n : ℕ, ‖(1 : ℂ) / ((((n : ℕ) : ℂ) + 1) ^ (σ : ℂ))‖ :=
            norm_tsum_le_tsum_norm hsumNorm
      _ = Zσ := by
            dsimp [Zσ]
            exact tsum_congr (fun n => norm_summand n σ)
  have hσpos : (0 : ℝ) < σ := by linarith
  have hT : 0 ≤ σ * ZetaAsymptotics.termTSum σ :=
    mul_nonneg (le_of_lt hσpos) (by
      rw [ZetaAsymptotics.termTSum]
      exact tsum_nonneg (fun n => ZetaAsymptotics.term_nonneg (n + 1) σ))
  have hconv : Zσ = (∑' n : ℕ, (1 : ℝ) / (((n : ℝ) + 1) ^ σ)) := by
    dsimp [Zσ]
    exact tsum_congr (fun n => by norm_num)
  have h := ZetaAsymptotics.zeta_limit_aux1 (s := σ) hσ
  have haux : Zσ - 1 / (σ - 1) = 1 - σ * ZetaAsymptotics.termTSum σ := by
    calc
      Zσ - 1 / (σ - 1) = ((∑' n : ℕ, (1 : ℝ) / (((n : ℝ) + 1) ^ σ)) - 1 / (σ - 1)) := by
            rw [hconv]
      _ = 1 - σ * ZetaAsymptotics.termTSum σ := h
  have hZle : Zσ ≤ 1 + 1 / (σ - 1) := by linarith
  exact le_trans hnorm hZle

/-- Real-part form of the elementary bound. -/
theorem riemannZeta_re_le_one_add_inv (σ : ℝ) (hσ : 1 < σ) :
    (riemannZeta ((σ : ℝ) : ℂ)).re ≤ 1 + 1 / (σ - 1) :=
  le_trans (Complex.re_le_norm _) (riemannZeta_norm_le_one_add_inv σ hσ)

/-- For real part at least `2` the value is bounded by `2`. -/
theorem riemannZeta_re_le_two {σ : ℝ} (hσ : 2 ≤ σ) :
    (riemannZeta ((σ : ℝ) : ℂ)).re ≤ 2 := by
  have h1 : (1 : ℝ) < σ := by linarith
  have h := riemannZeta_re_le_one_add_inv σ h1
  have hpos : 0 < σ - 1 := by linarith
  have h2 : 1 / (σ - 1) ≤ 1 := by
    rw [div_le_one hpos]
    linarith
  linarith

end Work.BMF
