import Mathlib
import Submission.Work.BMF.liouville.vkbl_defs

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false

set_option maxHeartbeats 1000000

/-!
# Numeric core of the bounded-`λ` Vinogradov–Korobov bound
-/

open Finset

namespace Work.BMF.liouville

noncomputable section

lemma log_N_pos (N : ℕ) (hN : 2 ≤ N) : 0 < Real.log (N : ℝ) :=
  Real.log_pos (by exact_mod_cast (by omega : 1 < N))

lemma rpow_vlam (N : ℕ) (t : ℝ) (hN : 2 ≤ N) (ht : 0 < t) :
    (N : ℝ) ^ (vlam (N : ℝ) t) = t := by
  have hlogN : Real.log (N : ℝ) ≠ 0 := ne_of_gt (log_N_pos N hN)
  rw [vlam, Real.rpow_def_of_pos (by positivity : (0:ℝ) < (N:ℝ))]
  rw [show Real.log (N : ℝ) * (Real.log t / Real.log (N : ℝ)) = Real.log t by field_simp]
  exact Real.exp_log ht

lemma t_le_rpow88 (N : ℕ) (t : ℝ) (hN : 2 ≤ N) (hNt : (N : ℝ) ≤ t)
    (hlogt : Real.log t ≤ 88 * Real.log (N : ℝ)) : t ≤ (N : ℝ) ^ 88 := by
  have hNpos : (0 : ℝ) < (N : ℝ) := by positivity
  have hNpos' : (0 : ℝ) < (N : ℝ) ^ 88 := by positivity
  have htpos : 0 < t := lt_of_lt_of_le (by exact_mod_cast (by omega : 0 < N)) hNt
  calc t = Real.exp (Real.log t) := (Real.exp_log htpos).symm
    _ ≤ Real.exp (88 * Real.log (N : ℝ)) := Real.exp_le_exp.mpr hlogt
    _ = (N : ℝ) ^ 88 := by
        rw [← Real.exp_log hNpos']
        congr 1
        rw [Real.log_pow]
        norm_num

lemma vlam_ge_one (N : ℕ) (t : ℝ) (hN : 2 ≤ N) (hNt : (N : ℝ) ≤ t) :
    1 ≤ vlam (N : ℝ) t := by
  have hlogN : 0 < Real.log (N : ℝ) := log_N_pos N hN
  have hNpos : (0 : ℝ) < (N : ℝ) := by positivity
  have htpos : 0 < t := lt_of_lt_of_le (by exact_mod_cast (by omega : 0 < N)) hNt
  rw [vlam, le_div_iff₀ hlogN]
  simpa using Real.log_le_log hNpos hNt

lemma vlam_le_88 (N : ℕ) (t : ℝ) (hN : 2 ≤ N)
    (hlogt : Real.log t ≤ 88 * Real.log (N : ℝ)) : vlam (N : ℝ) t ≤ 88 := by
  have hlogN : 0 < Real.log (N : ℝ) := log_N_pos N hN
  rw [vlam, div_le_iff₀ hlogN]; linarith

lemma vmu_nonneg (N : ℕ) (t : ℝ) (hN : 2 ≤ N) (hlogt : Real.log t ≤ 88 * Real.log (N : ℝ)) :
    0 ≤ vmu (N : ℝ) t := by
  have h88 : vlam (N : ℝ) t ≤ 88 := vlam_le_88 N t hN hlogt
  rw [vmu, vd2]
  have : vlam (N : ℝ) t + vlam (N : ℝ) t / 178 ≤ 90 := by linarith
  linarith

lemma vtv_le_one (N : ℕ) (t : ℝ) (hN : 2 ≤ N)
    (hlogt : Real.log t ≤ 88 * Real.log (N : ℝ)) : vtv (N : ℝ) t ≤ 1 := by
  have h88 : vlam (N : ℝ) t ≤ 88 := vlam_le_88 N t hN hlogt
  calc vtv (N : ℝ) t ≤ vlam (N : ℝ) t / 180 := min_le_left _ _
    _ ≤ 88 / 180 := by linarith
    _ ≤ 1 := by norm_num

/-- `|γ_89| = t/(2π·89·(n+u)^89)`. -/
lemma abs_gam_eq (t u : ℝ) (n : ℕ) (ht : 0 < t) (hu : 0 < u) :
    |Work.BMF.zpt.gam 89 t (n : ℝ) u| = t / (2 * Real.pi * 89 * ((n : ℝ) + u) ^ 89) := by
  have hgam : Work.BMF.zpt.gam 89 t (n : ℝ) u
      = -(t / (2 * Real.pi * 89 * ((n : ℝ) + u) ^ 89)) := by
    simp only [Work.BMF.zpt.gam]
    norm_num
    ring
  rw [hgam, abs_neg, abs_of_pos (by positivity)]

theorem gam_abs_bounds (N : ℕ) (t u : ℝ) (n : ℕ) (hN : 2 ≤ N) (hNt : (N : ℝ) ≤ t)
    (hlogt : Real.log t ≤ 88 * Real.log (N : ℝ)) (hu0 : 0 < u) (hu1 : u ≤ 1)
    (hn : (N : ℝ) ≤ (n : ℝ)) (hn2 : (n : ℝ) ≤ 2 * (N : ℝ) + 1) :
    |Work.BMF.zpt.gam 89 t (n : ℝ) u| ≤ 1 ∧
    |Work.BMF.zpt.gam 89 t (n : ℝ) u| ≤ 1 / (2 * Real.pi * 89 * (N : ℝ)) ∧
    1 / (2 * Real.pi * 89 * 3 ^ 89 * (N : ℝ) ^ 88) ≤ |Work.BMF.zpt.gam 89 t (n : ℝ) u| := by
  have hNpos : (0 : ℝ) < (N : ℝ) := by positivity
  have hN2 : (2 : ℝ) ≤ (N : ℝ) := by exact_mod_cast hN
  have htpos : 0 < t := lt_of_lt_of_le (by linarith) hNt
  have ht88 : t ≤ (N : ℝ) ^ 88 := t_le_rpow88 N t hN hNt hlogt
  have hnupos : (0 : ℝ) < (n : ℝ) + u := by positivity
  have hnulo : (N : ℝ) ≤ (n : ℝ) + u := by linarith
  have hnuhi : (n : ℝ) + u ≤ 3 * (N : ℝ) := by linarith
  have hgam := abs_gam_eq t u n htpos hu0
  have hnum : t * (N : ℝ) ≤ ((n : ℝ) + u) ^ 89 := by
    calc t * (N : ℝ) ≤ (N : ℝ) ^ 88 * (N : ℝ) := mul_le_mul_of_nonneg_right ht88 hNpos.le
      _ = (N : ℝ) ^ 89 := by ring
      _ ≤ ((n : ℝ) + u) ^ 89 := pow_le_pow_left₀ (by positivity) hnulo 89
  have hnum3 : ((n : ℝ) + u) ^ 89 ≤ 3 ^ 89 * (N : ℝ) ^ 88 * t := by
    calc ((n : ℝ) + u) ^ 89 ≤ (3 * (N : ℝ)) ^ 89 := pow_le_pow_left₀ (by positivity) hnuhi 89
      _ = 3 ^ 89 * (N : ℝ) ^ 89 := by rw [mul_pow]
      _ = 3 ^ 89 * (N : ℝ) ^ 88 * (N : ℝ) := by ring
      _ ≤ 3 ^ 89 * (N : ℝ) ^ 88 * t := mul_le_mul_of_nonneg_left hNt (by positivity)
  have hub : |Work.BMF.zpt.gam 89 t (n : ℝ) u| ≤ 1 / (2 * Real.pi * 89 * (N : ℝ)) := by
    rw [hgam, div_le_div_iff₀ (by positivity) (by positivity)]
    calc t * (2 * Real.pi * 89 * (N : ℝ)) = (2 * Real.pi * 89) * (t * (N : ℝ)) := by ring
      _ ≤ (2 * Real.pi * 89) * ((n : ℝ) + u) ^ 89 :=
          mul_le_mul_of_nonneg_left hnum (by positivity)
      _ = 1 * (2 * Real.pi * 89 * ((n : ℝ) + u) ^ 89) := by ring
  have hlb : 1 / (2 * Real.pi * 89 * 3 ^ 89 * (N : ℝ) ^ 88) ≤ |Work.BMF.zpt.gam 89 t (n : ℝ) u| := by
    rw [hgam, div_le_div_iff₀ (by positivity) (by positivity)]
    calc 1 * (2 * Real.pi * 89 * ((n : ℝ) + u) ^ 89) = (2 * Real.pi * 89) * ((n : ℝ) + u) ^ 89 := by ring
      _ ≤ (2 * Real.pi * 89) * (3 ^ 89 * (N : ℝ) ^ 88 * t) :=
          mul_le_mul_of_nonneg_left hnum3 (by positivity)
      _ = t * (2 * Real.pi * 89 * 3 ^ 89 * (N : ℝ) ^ 88) := by ring
  refine ⟨?_, hub, hlb⟩
  calc |Work.BMF.zpt.gam 89 t (n : ℝ) u| ≤ 1 / (2 * Real.pi * 89 * (N : ℝ)) := hub
    _ ≤ 1 := by
        rw [div_le_one (by positivity)]
        nlinarith [Real.pi_gt_three, hN2]

lemma vtv_nonneg (N : ℕ) (t : ℝ) (hN : 2 ≤ N) (hNt : (N : ℝ) ≤ t)
    (hlogt : Real.log t ≤ 88 * Real.log (N : ℝ)) : 0 ≤ vtv (N : ℝ) t :=
  le_min (by have := vlam_ge_one N t hN hNt; linarith) (vmu_nonneg N t hN hlogt)

/-- `89·(1 - μ) = 179λ/180`, equivalently `89 - λ - 89μ = -λ/180`. -/
lemma exp_identity (N : ℝ) (t : ℝ) :
    89 - vlam N t - 89 * vmu N t = -(vlam N t) / 180 := by
  rw [vmu, vd2]
  ring

lemma rpow_sub_mul_vlam (N : ℕ) (t : ℝ) (hN : 2 ≤ N) (ht : 0 < t) (x : ℝ)
    (hx : x = vlam (N : ℝ) t) : (N : ℝ) ^ (89 - x) * t = (N : ℝ) ^ 89 := by
  calc (N : ℝ) ^ (89 - x) * t = (N : ℝ) ^ (89 - x) * (N : ℝ) ^ x := by
        rw [show t = (N : ℝ) ^ (vlam (N : ℝ) t) from (rpow_vlam N t hN ht).symm, ← hx]
    _ = (N : ℝ) ^ 89 := by
        rw [← Real.rpow_natCast (N : ℝ) 89, ← Real.rpow_add (by positivity : (0 : ℝ) < (N : ℝ))]
        congr 1
        ring

theorem bracket_le (N : ℕ) (t u : ℝ) (n : ℕ) (M : ℕ) (hN : 2 ≤ N) (hNt : (N : ℝ) ≤ t)
    (hlogt : Real.log t ≤ 88 * Real.log (N : ℝ)) (hu0 : 0 < u) (hu1 : u ≤ 1)
    (hn : (N : ℝ) ≤ (n : ℝ)) (hn2 : (n : ℝ) ≤ 2 * (N : ℝ) + 1)
    (hMlo : (N : ℝ) ^ (vmu (N : ℝ) t) / 2 ≤ (M : ℝ))
    (hMhi : (M : ℝ) ≤ (N : ℝ) ^ (vmu (N : ℝ) t)) (hM1 : 1 ≤ M) :
    1 / ((⌊1 / |Work.BMF.zpt.gam 89 t (n : ℝ) u|⌋₊ : ℝ)) + 1 / (M : ℝ) + 1 / (M : ℝ) ^ 88
        + ((⌊1 / |Work.BMF.zpt.gam 89 t (n : ℝ) u|⌋₊ : ℝ)) / (M : ℝ) ^ 89
      ≤ ((2 : ℝ) ^ 89 * (2 * Real.pi * 89) * 3 ^ 89 * 4 + 4) * (N : ℝ) ^ (-(vtv (N : ℝ) t)) := by
  obtain ⟨_, hAub, hAlb⟩ := gam_abs_bounds N t u n hN hNt hlogt hu0 hu1 hn hn2
  have hNpos : (0 : ℝ) < (N : ℝ) := by positivity
  have hN1 : (1 : ℝ) ≤ (N : ℝ) := by exact_mod_cast (by omega : 1 ≤ N)
  have hN2' : (2 : ℝ) ≤ (N : ℝ) := by exact_mod_cast hN
  have htpos : 0 < t := lt_of_lt_of_le (by linarith) hNt
  have hMpos : (0 : ℝ) < (M : ℝ) := by exact_mod_cast hM1
  have hmu0 : 0 ≤ vmu (N : ℝ) t := vmu_nonneg N t hN hlogt
  have hθ1 : vtv (N : ℝ) t ≤ 1 := vtv_le_one N t hN hlogt
  have hθmu : vtv (N : ℝ) t ≤ vmu (N : ℝ) t := min_le_right _ _
  have hθlam : vtv (N : ℝ) t ≤ vlam (N : ℝ) t / 180 := min_le_left _ _
  set A : ℝ := |Work.BMF.zpt.gam 89 t (n : ℝ) u| with hA
  have hA0 : 0 < A := by
    rw [hA]; exact abs_pos.mpr (gam_ne_zero 89 (by norm_num) t u n htpos hu0)
  have hAub' : A ≤ 1 / (2 * Real.pi * 89 * (N : ℝ)) := by rw [hA]; exact hAub
  have hA12 : A ≤ 1 / 2 := by
    have h1 : 1 / (2 * Real.pi * 89 * (N : ℝ)) ≤ 1 / 2 := by
      rw [div_le_div_iff₀ (by positivity) (by norm_num)]
      nlinarith [Real.pi_gt_three, hN2']
    linarith
  set q : ℕ := ⌊1 / A⌋₊ with hq
  have hq1 : 1 ≤ q := by
    rw [hq]; apply Nat.le_floor
    rw [le_div_iff₀ hA0]
    simp only [Nat.cast_one, one_mul]
    linarith [hA12]
  have hqpos : (0 : ℝ) < (q : ℝ) := by exact_mod_cast hq1
  have hqle : (q : ℝ) ≤ 1 / A := by rw [hq]; exact Nat.floor_le (by positivity)
  have hqlt : 1 / A < (q : ℝ) + 1 := by rw [hq]; exact Nat.lt_floor_add_one (1 / A)
  have ha : 1 / (q : ℝ) ≤ (N : ℝ) ^ (-(vtv (N : ℝ) t)) := by
    have h2 : A * (1 / A - 1) < A * (q : ℝ) :=
      mul_lt_mul_of_pos_left (by linarith [hqlt]) hA0
    rw [mul_sub, mul_one_div_cancel (ne_of_gt hA0), mul_one] at h2
    have h3 : 1 / (q : ℝ) ≤ 2 * A := by
      rw [div_le_iff₀ hqpos]; linarith [h2, hA12]
    have h4 : 2 * A ≤ (N : ℝ) ^ (-1 : ℝ) := by
      rw [Real.rpow_neg hNpos.le, Real.rpow_one]
      have h5 : 2 * A ≤ 2 * (1 / (2 * Real.pi * 89 * (N : ℝ))) := by linarith [hAub']
      have h6 : 2 * (1 / (2 * Real.pi * 89 * (N : ℝ))) = 1 / (Real.pi * 89 * (N : ℝ)) := by ring
      rw [h6] at h5
      refine le_trans h5 ?_
      rw [inv_eq_one_div, div_le_div_iff₀ (by positivity) hNpos]
      nlinarith [Real.pi_gt_three, hNpos]
    have h7 : (N : ℝ) ^ (-1 : ℝ) ≤ (N : ℝ) ^ (-(vtv (N : ℝ) t)) :=
      Real.rpow_le_rpow_of_exponent_le hN1 (by linarith)
    linarith
  have hb : 1 / (M : ℝ) ≤ 2 * (N : ℝ) ^ (-(vtv (N : ℝ) t)) := by
    have h2 : 1 / (M : ℝ) ≤ 1 / ((N : ℝ) ^ (vmu (N : ℝ) t) / 2) :=
      one_div_le_one_div_of_le (by positivity) hMlo
    have h3 : 1 / ((N : ℝ) ^ (vmu (N : ℝ) t) / 2) = 2 * (N : ℝ) ^ (-(vmu (N : ℝ) t)) := by
      rw [Real.rpow_neg hNpos.le]; field_simp
    have h4 : (N : ℝ) ^ (-(vmu (N : ℝ) t)) ≤ (N : ℝ) ^ (-(vtv (N : ℝ) t)) :=
      Real.rpow_le_rpow_of_exponent_le hN1 (by linarith [hθmu])
    rw [h3] at h2
    linarith
  have hc : 1 / (M : ℝ) ^ 88 ≤ 2 ^ 88 * (N : ℝ) ^ (-(vtv (N : ℝ) t)) := by
    have h2 : 1 / (M : ℝ) ^ 88 ≤ 1 / ((N : ℝ) ^ (vmu (N : ℝ) t) / 2) ^ 88 :=
      one_div_le_one_div_of_le (by positivity) (pow_le_pow_left₀ (by positivity) hMlo 88)
    have h3 : ((N : ℝ) ^ (vmu (N : ℝ) t) / 2) ^ 88
        = (N : ℝ) ^ (88 * vmu (N : ℝ) t) / 2 ^ 88 := by
      rw [div_pow, ← Real.rpow_natCast ((N : ℝ) ^ (vmu (N : ℝ) t)) 88, ← Real.rpow_mul hNpos.le,
        show vmu (N : ℝ) t * ((88 : ℕ) : ℝ) = 88 * vmu (N : ℝ) t by push_cast; ring]
    have h4 : 1 / ((N : ℝ) ^ (88 * vmu (N : ℝ) t) / 2 ^ 88)
        = 2 ^ 88 * (N : ℝ) ^ (-(88 * vmu (N : ℝ) t)) := by
      rw [Real.rpow_neg hNpos.le]; field_simp
    rw [h3, h4] at h2
    have h5 : (N : ℝ) ^ (-(88 * vmu (N : ℝ) t)) ≤ (N : ℝ) ^ (-(vtv (N : ℝ) t)) :=
      Real.rpow_le_rpow_of_exponent_le hN1 (by linarith [hθmu, hmu0])
    linarith
  have hd : (q : ℝ) / (M : ℝ) ^ 89
      ≤ 2 ^ 89 * (2 * Real.pi * 89) * 3 ^ 89 * (N : ℝ) ^ (-(vtv (N : ℝ) t)) := by
    have h1 : (q : ℝ) ≤ 2 * Real.pi * 89 * 3 ^ 89 * (N : ℝ) ^ (89 - vlam (N : ℝ) t) := by
      have hA' : 1 / A = 2 * Real.pi * 89 * ((n : ℝ) + u) ^ 89 / t := by
        rw [hA, abs_gam_eq t u n htpos hu0, one_div_div]
      have hnum : 2 * Real.pi * 89 * ((n : ℝ) + u) ^ 89 ≤ 2 * Real.pi * 89 * 3 ^ 89 * (N : ℝ) ^ 89 := by
        have hpu : ((n : ℝ) + u) ^ 89 ≤ 3 ^ 89 * (N : ℝ) ^ 89 := by
          calc ((n : ℝ) + u) ^ 89 ≤ (3 * (N : ℝ)) ^ 89 :=
                pow_le_pow_left₀ (by positivity) (by linarith) 89
            _ = 3 ^ 89 * (N : ℝ) ^ 89 := by rw [mul_pow]
        nlinarith [hpu, Real.pi_pos]
      have hkey : 2 * Real.pi * 89 * 3 ^ 89 * (N : ℝ) ^ 89 / t
          = 2 * Real.pi * 89 * 3 ^ 89 * (N : ℝ) ^ (89 - vlam (N : ℝ) t) := by
        rw [div_eq_iff (ne_of_gt htpos)]
        rw [show 2 * Real.pi * 89 * 3 ^ 89 * (N : ℝ) ^ (89 - vlam (N : ℝ) t) * t
            = (2 * Real.pi * 89 * 3 ^ 89) * ((N : ℝ) ^ (89 - vlam (N : ℝ) t) * t) by ring]
        rw [rpow_sub_mul_vlam N t hN htpos (vlam (N : ℝ) t) rfl]
      calc (q : ℝ) ≤ 1 / A := hqle
        _ = 2 * Real.pi * 89 * ((n : ℝ) + u) ^ 89 / t := hA'
        _ ≤ 2 * Real.pi * 89 * 3 ^ 89 * (N : ℝ) ^ 89 / t :=
            div_le_div_of_nonneg_right hnum htpos.le
        _ = 2 * Real.pi * 89 * 3 ^ 89 * (N : ℝ) ^ (89 - vlam (N : ℝ) t) := hkey
    have h2 : (N : ℝ) ^ (89 * vmu (N : ℝ) t) / 2 ^ 89 ≤ (M : ℝ) ^ 89 := by
      have h2' : ((N : ℝ) ^ (vmu (N : ℝ) t) / 2) ^ 89 ≤ (M : ℝ) ^ 89 :=
        pow_le_pow_left₀ (by positivity) hMlo 89
      have h3 : ((N : ℝ) ^ (vmu (N : ℝ) t) / 2) ^ 89
          = (N : ℝ) ^ (89 * vmu (N : ℝ) t) / 2 ^ 89 := by
        rw [div_pow, ← Real.rpow_natCast ((N : ℝ) ^ (vmu (N : ℝ) t)) 89, ← Real.rpow_mul hNpos.le,
          show vmu (N : ℝ) t * ((89 : ℕ) : ℝ) = 89 * vmu (N : ℝ) t by push_cast; ring]
      rwa [h3] at h2'
    have h6 : (q : ℝ) / (M : ℝ) ^ 89
        ≤ 2 * Real.pi * 89 * 3 ^ 89 * (N : ℝ) ^ (89 - vlam (N : ℝ) t)
            / ((N : ℝ) ^ (89 * vmu (N : ℝ) t) / 2 ^ 89) :=
      div_le_div₀ (by positivity) h1 (by positivity) h2
    have h7 : 2 * Real.pi * 89 * 3 ^ 89 * (N : ℝ) ^ (89 - vlam (N : ℝ) t)
            / ((N : ℝ) ^ (89 * vmu (N : ℝ) t) / 2 ^ 89)
        = 2 ^ 89 * (2 * Real.pi * 89) * 3 ^ 89 * (N : ℝ) ^ (-(vlam (N : ℝ) t) / 180) := by
      have hkey : (N : ℝ) ^ (89 - vlam (N : ℝ) t) / (N : ℝ) ^ (89 * vmu (N : ℝ) t)
          = (N : ℝ) ^ (-(vlam (N : ℝ) t) / 180) := by
        rw [← Real.rpow_sub hNpos]
        congr 1
        have := exp_identity (N : ℝ) t
        linarith
      rw [div_div_eq_mul_div]
      rw [show 2 * Real.pi * 89 * 3 ^ 89 * (N : ℝ) ^ (89 - vlam (N : ℝ) t) * 2 ^ 89
              / (N : ℝ) ^ (89 * vmu (N : ℝ) t)
            = 2 * Real.pi * 89 * 3 ^ 89 * 2 ^ 89
              * ((N : ℝ) ^ (89 - vlam (N : ℝ) t) / (N : ℝ) ^ (89 * vmu (N : ℝ) t)) by ring]
      rw [hkey]
      ring
    rw [h7] at h6
    have h8 : (N : ℝ) ^ (-(vlam (N : ℝ) t) / 180) ≤ (N : ℝ) ^ (-(vtv (N : ℝ) t)) :=
      Real.rpow_le_rpow_of_exponent_le hN1 (by linarith [hθlam])
    calc (q : ℝ) / (M : ℝ) ^ 89
        ≤ 2 ^ 89 * (2 * Real.pi * 89) * 3 ^ 89 * (N : ℝ) ^ (-(vlam (N : ℝ) t) / 180) := h6
      _ ≤ 2 ^ 89 * (2 * Real.pi * 89) * 3 ^ 89 * (N : ℝ) ^ (-(vtv (N : ℝ) t)) :=
          mul_le_mul_of_nonneg_left h8 (by positivity)
  have hP : (0 : ℝ) < (N : ℝ) ^ (-(vtv (N : ℝ) t)) := Real.rpow_pos_of_pos hNpos _
  have hsum : 1 / (q : ℝ) + 1 / (M : ℝ) + 1 / (M : ℝ) ^ 88 + (q : ℝ) / (M : ℝ) ^ 89
      ≤ (1 + 2 + 2 ^ 88 + 2 ^ 89 * (2 * Real.pi * 89) * 3 ^ 89) * (N : ℝ) ^ (-(vtv (N : ℝ) t)) := by
    have h1 := add_le_add (add_le_add (add_le_add ha hb) hc) hd
    rw [show (1 + 2 + 2 ^ 88 + 2 ^ 89 * (2 * Real.pi * 89) * 3 ^ 89) * (N : ℝ) ^ (-(vtv (N : ℝ) t))
        = (N : ℝ) ^ (-(vtv (N : ℝ) t)) + 2 * (N : ℝ) ^ (-(vtv (N : ℝ) t))
          + 2 ^ 88 * (N : ℝ) ^ (-(vtv (N : ℝ) t))
          + 2 ^ 89 * (2 * Real.pi * 89) * 3 ^ 89 * (N : ℝ) ^ (-(vtv (N : ℝ) t)) by ring]
    exact h1
  have hfin : (1 + 2 + 2 ^ 88 + 2 ^ 89 * (2 * Real.pi * 89) * 3 ^ 89) * (N : ℝ) ^ (-(vtv (N : ℝ) t))
      ≤ ((2 : ℝ) ^ 89 * (2 * Real.pi * 89) * 3 ^ 89 * 4 + 4) * (N : ℝ) ^ (-(vtv (N : ℝ) t)) := by
    apply mul_le_mul_of_nonneg_right _ hP.le
    nlinarith [Real.pi_gt_three]
  linarith [hsum, hfin]

lemma mul_rpow_one (x : ℝ) (hx : 0 < x) (y : ℝ) : x * x ^ y = x ^ (1 + y) := by
  conv_lhs => enter [1]; rw [← Real.rpow_one x]
  rw [← Real.rpow_add hx]

lemma rpow_vlam_mul_cancel (N : ℕ) (t : ℝ) (hN : 2 ≤ N) (ht : 0 < t) (y : ℝ) :
    (N : ℝ) ^ (vlam (N : ℝ) t) * (N : ℝ) ^ (-(vlam (N : ℝ) t) + y) = (N : ℝ) ^ y := by
  rw [← Real.rpow_add (by positivity : (0 : ℝ) < (N : ℝ))]
  congr 1
  ring

theorem taylor_err_le (N : ℕ) (t u : ℝ) (n : ℕ) (M : ℕ) (hN : 2 ^ 90 ≤ N)
    (hNt : (N : ℝ) ≤ t) (hlogt : Real.log t ≤ 88 * Real.log (N : ℝ)) (hu0 : 0 < u)
    (hn : (N : ℝ) ≤ (n : ℝ)) (hMhi : (M : ℝ) ≤ (N : ℝ) ^ (vmu (N : ℝ) t)) :
    t * ((M : ℝ) / ((n : ℝ) + u)) ^ 90 / (1 - (M : ℝ) / ((n : ℝ) + u))
      ≤ 2 * (N : ℝ) ^ (-(vd2 (N : ℝ) t)) := by
  have hN2 : 2 ≤ N := by omega
  have hNpos : 0 < (N : ℝ) := by positivity
  have hN1 : (1 : ℝ) ≤ (N : ℝ) := by exact_mod_cast (by omega : 1 ≤ N)
  have hNbig : (2 : ℝ) ^ 90 ≤ (N : ℝ) := by exact_mod_cast hN
  have htpos : 0 < t := lt_of_lt_of_le (by linarith) hNt
  have hden : 0 < (n : ℝ) + u := by positivity
  have hlam1 : 1 ≤ vlam (N : ℝ) t := vlam_ge_one N t hN2 hNt
  have hd20 : 0 ≤ vd2 (N : ℝ) t := by rw [vd2]; linarith
  have hmu1 : vmu (N : ℝ) t ≤ 1 := by
    rw [vmu, vd2]
    have h2 : 0 ≤ vlam (N : ℝ) t + vlam (N : ℝ) t / 178 := by linarith
    linarith
  -- x ≤ N^{μ-1} ≤ 1/2
  have hxle : (M : ℝ) / ((n : ℝ) + u) ≤ (N : ℝ) ^ (vmu (N : ℝ) t - 1) := by
    have h1 : (M : ℝ) / ((n : ℝ) + u) ≤ (N : ℝ) ^ (vmu (N : ℝ) t) / ((n : ℝ) + u) :=
      div_le_div_of_nonneg_right hMhi hden.le
    have h2 : (N : ℝ) ^ (vmu (N : ℝ) t) / ((n : ℝ) + u) ≤ (N : ℝ) ^ (vmu (N : ℝ) t) / (N : ℝ) := by
      rw [div_le_div_iff₀ hden hNpos]
      exact mul_le_mul_of_nonneg_left (by linarith [hn]) (by positivity)
    have h3 : (N : ℝ) ^ (vmu (N : ℝ) t) / (N : ℝ) = (N : ℝ) ^ (vmu (N : ℝ) t - 1) := by
      have h4 : (N : ℝ) ^ (vmu (N : ℝ) t - 1) * (N : ℝ)
          = (N : ℝ) ^ (vmu (N : ℝ) t - 1) * (N : ℝ) ^ (1 : ℝ) := by rw [Real.rpow_one]
      rw [div_eq_iff (ne_of_gt hNpos), h4, ← Real.rpow_add hNpos]
      congr 1
      ring
    linarith
  have hx_half : (M : ℝ) / ((n : ℝ) + u) ≤ 1 / 2 := by
    refine le_trans hxle ?_
    have h4 : vmu (N : ℝ) t - 1 ≤ (-1 : ℝ) / 90 := by
      rw [vmu, vd2]
      linarith [hlam1]
    have h7 : (N : ℝ) ^ (vmu (N : ℝ) t - 1) ≤ (N : ℝ) ^ ((-1 : ℝ) / 90) :=
      Real.rpow_le_rpow_of_exponent_le hN1 h4
    have h8 : (2 : ℝ) ≤ (N : ℝ) ^ ((1 : ℝ) / 90) := by
      have h9 : (2 : ℝ) ≤ ((2 : ℝ) ^ 90) ^ ((1 : ℝ) / 90) := by
        rw [show ((2 : ℝ) ^ 90) = (2 : ℝ) ^ ((90 : ℕ) : ℝ) by rw [Real.rpow_natCast],
          ← Real.rpow_mul (by norm_num : (0 : ℝ) ≤ 2),
          show (((90 : ℕ) : ℝ)) * (1 / 90) = 1 by push_cast; ring, Real.rpow_one]
      exact le_trans h9 (Real.rpow_le_rpow (by positivity) hNbig (by norm_num))
    refine le_trans h7 ?_
    rw [show (-1 : ℝ) / 90 = -((1 : ℝ) / 90) by ring, Real.rpow_neg hNpos.le,
      show (1 : ℝ) / 2 = (2 : ℝ)⁻¹ by norm_num]
    exact (inv_le_inv₀ (by positivity) (by norm_num)).mpr h8
  have hx0 : 0 ≤ (M : ℝ) / ((n : ℝ) + u) := by positivity
  -- x^90 ≤ N^{(μ-1)*90}
  have h90 : ((M : ℝ) / ((n : ℝ) + u)) ^ 90 ≤ (N : ℝ) ^ ((vmu (N : ℝ) t - 1) * 90) := by
    calc ((M : ℝ) / ((n : ℝ) + u)) ^ 90 ≤ ((N : ℝ) ^ (vmu (N : ℝ) t - 1)) ^ 90 :=
          pow_le_pow_left₀ hx0 hxle 90
      _ = (N : ℝ) ^ ((vmu (N : ℝ) t - 1) * 90) := by
          rw [← Real.rpow_natCast ((N : ℝ) ^ (vmu (N : ℝ) t - 1)) 90, ← Real.rpow_mul hNpos.le,
            show (vmu (N : ℝ) t - 1) * ((90 : ℕ) : ℝ) = (vmu (N : ℝ) t - 1) * 90 by push_cast; ring]
  -- t * x^90 ≤ N^{-δ₂}
  have htx : t * ((M : ℝ) / ((n : ℝ) + u)) ^ 90 ≤ (N : ℝ) ^ (-(vd2 (N : ℝ) t)) := by
    have ht' : t = (N : ℝ) ^ (vlam (N : ℝ) t) := (rpow_vlam N t hN2 htpos).symm
    conv_lhs => rw [ht']
    calc (N : ℝ) ^ (vlam (N : ℝ) t) * ((M : ℝ) / ((n : ℝ) + u)) ^ 90
        ≤ (N : ℝ) ^ (vlam (N : ℝ) t) * (N : ℝ) ^ ((vmu (N : ℝ) t - 1) * 90) :=
          mul_le_mul_of_nonneg_left h90 (by positivity)
      _ = (N : ℝ) ^ (vlam (N : ℝ) t) * (N : ℝ) ^ (-(vlam (N : ℝ) t) + (-(vd2 (N : ℝ) t))) := by
          congr 2
          rw [vmu, vd2]; ring
      _ = (N : ℝ) ^ (-(vd2 (N : ℝ) t)) := rpow_vlam_mul_cancel N t hN2 htpos (-(vd2 (N : ℝ) t))
  have hden2 : 2 * (1 - (M : ℝ) / ((n : ℝ) + u)) ≥ 1 := by linarith [hx_half]
  have hnonneg : 0 ≤ t * ((M : ℝ) / ((n : ℝ) + u)) ^ 90 := by positivity
  calc t * ((M : ℝ) / ((n : ℝ) + u)) ^ 90 / (1 - (M : ℝ) / ((n : ℝ) + u))
      ≤ 2 * (t * ((M : ℝ) / ((n : ℝ) + u)) ^ 90) := by
        rw [div_le_iff₀ (by linarith : (0:ℝ) < 1 - (M : ℝ) / ((n : ℝ) + u))]
        nlinarith [hden2, hnonneg]
    _ ≤ 2 * (N : ℝ) ^ (-(vd2 (N : ℝ) t)) := by linarith [htx]

end

end Work.BMF.liouville
