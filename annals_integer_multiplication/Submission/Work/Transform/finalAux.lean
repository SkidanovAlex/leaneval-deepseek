import Mathlib
import Submission.HvdH.Interfaces
import Submission.Work.Transform.Defs
import Submission.Work.Transform.bluestein
import Submission.Work.Transform.eps_mul
import Submission.Work.Transform.phiArrL_norm
import Submission.Work.Transform.psiFlatL_norm
import Submission.Work.Transform.psiFlatL_phiArrL
import Submission.Work.Transform.chirp_norm
import Submission.Work.Transform.convR_norm
import Submission.Work.Transform.convR_sub
import Submission.Work.Transform.final_arith
import Submission.Work.ConvR.basic

set_option autoImplicit false
set_option maxHeartbeats 1000000

namespace Work.Transform

open HvdH

/-! ## Small numerical helpers for the error bookkeeping of Theorem 3.1 -/

/-- Pointwise product error with explicit sup-norm factors: if `‖g i‖ ≤ Cg` and `‖h i‖ ≤ Ch`
then the scaled error of `f g` against `h k` is at most `Cg` times the scaled error of `f`
against `h` plus `Ch` times the scaled error of `g` against `k`. -/
theorem scaled_mul_le {ι : Type*} (p : ℕ) (f g h k : ι → ℂ) (Cg Ch : ℝ)
    (hg : ∀ i, ‖g i‖ ≤ Cg) (hh : ∀ i, ‖h i‖ ≤ Ch) (i : ι) :
    (2 : ℝ) ^ p * ‖f i * g i - h i * k i‖ ≤
      Cg * ((2 : ℝ) ^ p * ‖f i - h i‖) + Ch * ((2 : ℝ) ^ p * ‖g i - k i‖) := by
  have hp0 : (0 : ℝ) ≤ (2 : ℝ) ^ p := by positivity
  have hdec : f i * g i - h i * k i = (f i - h i) * g i + h i * (g i - k i) := by ring
  have h1 : ‖f i * g i - h i * k i‖ ≤ ‖f i - h i‖ * Cg + Ch * ‖g i - k i‖ := by
    rw [hdec]
    calc ‖(f i - h i) * g i + h i * (g i - k i)‖
        ≤ ‖(f i - h i) * g i‖ + ‖h i * (g i - k i)‖ := norm_add_le _ _
      _ = ‖f i - h i‖ * ‖g i‖ + ‖h i‖ * ‖g i - k i‖ := by rw [norm_mul, norm_mul]
      _ ≤ ‖f i - h i‖ * Cg + Ch * ‖g i - k i‖ :=
          add_le_add (mul_le_mul_of_nonneg_left (hg i) (norm_nonneg _))
                     (mul_le_mul_of_nonneg_right (hh i) (norm_nonneg _))
  calc (2 : ℝ) ^ p * ‖f i * g i - h i * k i‖
      ≤ (2 : ℝ) ^ p * (‖f i - h i‖ * Cg + Ch * ‖g i - k i‖) :=
        mul_le_mul_of_nonneg_left h1 hp0
    _ = Cg * ((2 : ℝ) ^ p * ‖f i - h i‖) + Ch * ((2 : ℝ) ^ p * ‖g i - k i‖) := by ring

/-- Scaled triangle inequality. -/
theorem scaled_triangle {ι : Type*} (p : ℕ) (f g h : ι → ℂ) (b c : ℝ) (i : ι)
    (h1 : (2 : ℝ) ^ p * ‖f i - g i‖ < b) (h2 : (2 : ℝ) ^ p * ‖g i - h i‖ < c) :
    (2 : ℝ) ^ p * ‖f i - h i‖ < b + c := by
  have hp0 : (0 : ℝ) ≤ (2 : ℝ) ^ p := by positivity
  have hdec : f i - h i = (f i - g i) + (g i - h i) := by ring
  calc (2 : ℝ) ^ p * ‖f i - h i‖
      = (2 : ℝ) ^ p * ‖(f i - g i) + (g i - h i)‖ := by rw [hdec]
    _ ≤ (2 : ℝ) ^ p * (‖f i - g i‖ + ‖g i - h i‖) :=
        mul_le_mul_of_nonneg_left (norm_add_le _ _) hp0
    _ = (2 : ℝ) ^ p * ‖f i - g i‖ + (2 : ℝ) ^ p * ‖g i - h i‖ := by ring
    _ < b + c := by linarith

/-- A pointwise scaled error bound gives the same bound for the sup norm. -/
theorem scaled_sup_le {ι : Type*} [Fintype ι] (p : ℕ) (f g : ι → ℂ) (b : ℝ) (hb : 0 ≤ b)
    (h : ∀ i, (2 : ℝ) ^ p * ‖f i - g i‖ ≤ b) :
    (2 : ℝ) ^ p * ‖f - g‖ ≤ b := by
  have hp : (0 : ℝ) < (2 : ℝ) ^ p := by positivity
  have h1 : ‖f - g‖ ≤ ((2 : ℝ) ^ p)⁻¹ * b := by
    refine (pi_norm_le_iff_of_nonneg (by positivity)).2 (fun i => ?_)
    rw [Pi.sub_apply]
    have h2 := mul_le_mul_of_nonneg_left (h i) (le_of_lt (inv_pos.mpr hp))
    rwa [← mul_assoc, inv_mul_cancel₀ (ne_of_gt hp), one_mul] at h2
  calc (2 : ℝ) ^ p * ‖f - g‖ ≤ (2 : ℝ) ^ p * (((2 : ℝ) ^ p)⁻¹ * b) :=
        mul_le_mul_of_nonneg_left h1 (le_of_lt hp)
    _ = b := by rw [← mul_assoc, mul_inv_cancel₀ (ne_of_gt hp), one_mul]

/-- `convR` is bilinear hence Lipschitz: the scaled error of `convR u v` against
`convR u' v'` is at most `‖v‖` times the scaled error of `u` against `u'` plus `‖u'‖` times
the scaled error of `v` against `v'`. -/
theorem convRScaledErr (p r : ℕ) (ts' : List ℕ) (hpos : ∀ t ∈ ts', 0 < t)
    (u u' v v' : Fin ts'.prod → Fin r → ℂ) :
    (2 : ℝ) ^ p * ‖HvdH.convR r ts' u v - HvdH.convR r ts' u' v'‖ ≤
      ‖v‖ * ((2 : ℝ) ^ p * ‖u - u'‖) + ‖u'‖ * ((2 : ℝ) ^ p * ‖v - v'‖) := by
  have hp0 : (0 : ℝ) ≤ (2 : ℝ) ^ p := by positivity
  have hsub := convR_sub r ts' u u' v v'
  calc (2 : ℝ) ^ p * ‖HvdH.convR r ts' u v - HvdH.convR r ts' u' v'‖
      = (2 : ℝ) ^ p * ‖HvdH.convR r ts' (u - u') v + HvdH.convR r ts' u' (v - v')‖ := by
        rw [hsub]
    _ ≤ (2 : ℝ) ^ p * (‖HvdH.convR r ts' (u - u') v‖
          + ‖HvdH.convR r ts' u' (v - v')‖) :=
        mul_le_mul_of_nonneg_left (norm_add_le _ _) hp0
    _ ≤ (2 : ℝ) ^ p * (‖u - u'‖ * ‖v‖ + ‖u'‖ * ‖v - v'‖) := by
        refine mul_le_mul_of_nonneg_left ?_ hp0
        exact add_le_add (convR_norm r ts' hpos (u - u') v) (convR_norm r ts' hpos u' (v - v'))
    _ = ‖v‖ * ((2 : ℝ) ^ p * ‖u - u'‖) + ‖u'‖ * ((2 : ℝ) ^ p * ‖v - v'‖) := by ring

/-- `ζ^{a r + c} = ζ^{c}` for `c < r`. -/
theorem zeta_mod_eq (r a c : ℕ) (hc : c < r) : zeta r ((a * r + c) % r) = zeta r c := by
  rw [Nat.add_comm (a * r) c, Nat.add_mul_mod_self_right, Nat.mod_eq_of_lt hc]

/-- The numerical bound used at the very end of the error bookkeeping
(`3 T log₂T + 2T + 40D + 40 < 8 T log₂T`), with room to spare. -/
theorem finalArith (T : ℕ) (hlog : HvdH.D ≤ Nat.log 2 T) (hT : 3 ≤ T) :
    (3 * (T : ℝ) * Nat.log 2 T + 2 * (T : ℝ) + (40 * (HvdH.D : ℝ) + 40))
      < 8 * (T : ℝ) * Nat.log 2 T := by
  have hD : (HvdH.D : ℝ) = 1729 := by norm_num [HvdH.D]
  have hlogr : (HvdH.D : ℝ) ≤ (Nat.log 2 T : ℝ) := by exact_mod_cast hlog
  have hTr : (3 : ℝ) ≤ T := by exact_mod_cast hT
  have hLe : (Nat.log 2 T : ℝ) ≤ T := by exact_mod_cast (Nat.log_le_self 2 T)
  have hpow : (2 : ℕ) ^ HvdH.D ≤ T :=
    (Nat.le_log_iff_pow_le (by norm_num) (by omega)).mp hlog
  have hT21 : (21 : ℝ) ≤ T := by
    have h21 : (21:ℕ) ≤ 2 ^ HvdH.D :=
      le_trans (by norm_num : (21:ℕ) ≤ 2^5)
        (Nat.pow_le_pow_right (n := 2) (by norm_num) (by norm_num [HvdH.D]))
    have h3 : (21:ℕ) ≤ T := le_trans h21 hpow
    exact_mod_cast h3
  have hTnn : (0:ℝ) ≤ T := Nat.cast_nonneg T
  nlinarith [hD, hlogr, hTr, hLe, hT21, hTnn]

/-- The zeta-table/chirp hypotheses force the input vector `zs` to be bounded by `3`: this is
not among the hypotheses of `finalApprox`, but follows from the pointwise product relation
for `b`. -/
theorem zsNormLeThree (p T : ℕ) (ts : List ℕ) (hp : 100 ≤ p) (zs ab b : List (ℤ × ℤ))
    (hbD : HvdH.InDiscVec p T b)
    (habE : ∀ i < T, (2 : ℝ) ^ p * ‖HvdH.fxC p (ab.getD i (0,0))
      - star (Work.Transform.chirp ts i)‖ < 4 * HvdH.D)
    (hbE : ∀ i < T, (2 : ℝ) ^ p * ‖HvdH.fxC p (b.getD i (0,0))
        - HvdH.fxC p (ab.getD i (0,0)) * HvdH.fxC p (zs.getD i (0,0))‖ < 2) :
    ∀ i < T, ‖HvdH.fxC p (zs.getD i (0,0))‖ ≤ 3 := by
  intro i hi
  have hp0 : (0 : ℝ) < (2 : ℝ) ^ p := by positivity
  have hDval : (HvdH.D : ℝ) = 1729 := by norm_num [HvdH.D]
  have h8D : 8 * (HvdH.D : ℝ) ≤ (2 : ℝ) ^ p := by
    have h100 : 8 * (HvdH.D : ℝ) ≤ (2 : ℝ) ^ 100 := by rw [hDval]; norm_num
    have hle : (2 : ℝ) ^ 100 ≤ (2 : ℝ) ^ p := pow_le_pow_right₀ (by norm_num) (by omega)
    linarith
  have hp4 : (4 : ℝ) ≤ (2 : ℝ) ^ p := by
    have h : (2 : ℝ) ^ 2 ≤ (2 : ℝ) ^ p := pow_le_pow_right₀ (by norm_num) (by omega)
    linarith [show (2:ℝ)^2 = 4 by norm_num]
  have hA : (1 / 2 : ℝ) ≤ ‖HvdH.fxC p (ab.getD i (0,0))‖ := by
    have hC : ‖star (Work.Transform.chirp ts i)‖ = 1 := by
      rw [norm_star, Work.Transform.chirp_norm]
    have h1 : (2 : ℝ) ^ p * ‖HvdH.fxC p (ab.getD i (0,0)) - star (Work.Transform.chirp ts i)‖
        < (1 / 2) * (2 : ℝ) ^ p := by
      have : (4 : ℝ) * (HvdH.D : ℝ) ≤ (1 / 2) * (2 : ℝ) ^ p := by linarith
      linarith [habE i hi]
    have h2 : ‖HvdH.fxC p (ab.getD i (0,0)) - star (Work.Transform.chirp ts i)‖ < 1 / 2 := by
      nlinarith [h1, hp0]
    have h3 : (1 : ℝ) ≤ ‖HvdH.fxC p (ab.getD i (0,0))‖
        + ‖HvdH.fxC p (ab.getD i (0,0)) - star (Work.Transform.chirp ts i)‖ := by
      calc (1 : ℝ) = ‖star (Work.Transform.chirp ts i)‖ := hC.symm
        _ = ‖HvdH.fxC p (ab.getD i (0,0)) - (HvdH.fxC p (ab.getD i (0,0))
              - star (Work.Transform.chirp ts i))‖ := by congr 1; ring
        _ ≤ ‖HvdH.fxC p (ab.getD i (0,0))‖
              + ‖HvdH.fxC p (ab.getD i (0,0)) - star (Work.Transform.chirp ts i)‖ := norm_sub_le _ _
    linarith
  have hb1 : ‖HvdH.fxC p (b.getD i (0,0))‖ ≤ 1 :=
    Work.ConvR.norm_fxC_le_one (Work.ConvR.InDiscVec.getD hbD ⟨i, hi⟩)
  have hAU : ‖HvdH.fxC p (ab.getD i (0,0)) * HvdH.fxC p (zs.getD i (0,0))‖ ≤ 3 / 2 := by
    have h1 : (2 : ℝ) ^ p * ‖HvdH.fxC p (b.getD i (0,0))
        - HvdH.fxC p (ab.getD i (0,0)) * HvdH.fxC p (zs.getD i (0,0))‖
        < (1 / 2) * (2 : ℝ) ^ p := by
      have : (2 : ℝ) ≤ (1 / 2) * (2 : ℝ) ^ p := by linarith
      linarith [hbE i hi]
    have h2 : ‖HvdH.fxC p (b.getD i (0,0))
        - HvdH.fxC p (ab.getD i (0,0)) * HvdH.fxC p (zs.getD i (0,0))‖ < 1 / 2 := by
      nlinarith [h1, hp0]
    have h3 : ‖HvdH.fxC p (ab.getD i (0,0)) * HvdH.fxC p (zs.getD i (0,0))‖
        ≤ ‖HvdH.fxC p (b.getD i (0,0))‖
          + ‖HvdH.fxC p (b.getD i (0,0))
            - HvdH.fxC p (ab.getD i (0,0)) * HvdH.fxC p (zs.getD i (0,0))‖ := by
      calc ‖HvdH.fxC p (ab.getD i (0,0)) * HvdH.fxC p (zs.getD i (0,0))‖
          = ‖HvdH.fxC p (b.getD i (0,0)) - (HvdH.fxC p (b.getD i (0,0))
              - HvdH.fxC p (ab.getD i (0,0)) * HvdH.fxC p (zs.getD i (0,0)))‖ := by congr 1; ring
        _ ≤ _ := norm_sub_le _ _
    linarith
  rw [norm_mul] at hAU
  have h1 : ‖HvdH.fxC p (zs.getD i (0,0))‖ * (1 / 2) ≤ ‖HvdH.fxC p (zs.getD i (0,0))‖
      * ‖HvdH.fxC p (ab.getD i (0,0))‖ :=
    mul_le_mul_of_nonneg_left hA (norm_nonneg _)
  have h2 : ‖HvdH.fxC p (zs.getD i (0,0))‖ * ‖HvdH.fxC p (ab.getD i (0,0))‖ ≤ 3 / 2 := by
    rw [mul_comm]; exact hAU
  linarith

end Work.Transform
