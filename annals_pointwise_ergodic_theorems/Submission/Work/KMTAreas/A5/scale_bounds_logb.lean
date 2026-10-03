import Mathlib
import Submission.Work.Analysis.EndVar.Defs

namespace Work.KMTAreas.A5

/-- The elementary scale inequalities of §5 of Krause--Mirek--Tao, for `N ≥ 1`:
the two logarithmic scales are at least `1`, the integer scale `Log N` is dominated by the
real scale `max 1 (logb 2 N)`, which in turn lies strictly below `2 ^ (LogLog N + 1)`
(note `Log N < 2 ^ (LogLog N + 1)` is the `2 ^ (LogLog N) ≥ Log N` type bound that keeps the
height `l_{(N)} = C₀ LogLog N` in place), and `2 ^ (LogLog N - 1) ≤ Log N`. -/
theorem scale_bounds_logb {N : ℕ} (hN : 1 ≤ N) :
    (1 ≤ Work.Analysis.EndVar.logN N) ∧ (1 ≤ Work.Analysis.EndVar.logLogN N) ∧
    ((Work.Analysis.EndVar.logN N : ℤ) : ℝ) ≤ max 1 (Real.logb 2 (N : ℝ)) ∧
    max 1 (Real.logb 2 (N : ℝ)) < (2 : ℝ) ^ (((Work.Analysis.EndVar.logLogN N : ℕ) : ℝ) + 1) ∧
    (2 : ℝ) ^ (((Work.Analysis.EndVar.logLogN N : ℕ) : ℝ) - 1) ≤ ((Work.Analysis.EndVar.logN N : ℤ) : ℝ) := by
  simp only [Work.Analysis.EndVar.logN, Work.Analysis.EndVar.logLogN]
  set L : ℕ := Nat.log 2 (max N 2) with hL
  set M : ℕ := Nat.log 2 (L + 2) with hM
  have h2 : (1 : ℝ) < 2 := by norm_num
  have h2n : (1 : ℕ) < 2 := by norm_num
  have hNpos : (0 : ℝ) < (N : ℝ) := by exact_mod_cast hN
  have hL1 : 1 ≤ L := by
    rw [hL]
    have h : 0 < Nat.log 2 (max N 2) := by
      rw [Nat.log_pos_iff]
      exact ⟨le_max_right _ _, by norm_num⟩
    omega
  have hM1 : 1 ≤ M := by
    rw [hM]
    have h : 0 < Nat.log 2 (L + 2) := by
      rw [Nat.log_pos_iff]
      exact ⟨by omega, by norm_num⟩
    omega
  have hLpow : 2 ^ L ≤ max N 2 := by
    rw [hL]
    exact Nat.pow_log_le_self 2 (by omega)
  have hLlt : max N 2 < 2 ^ (L + 1) := by
    rw [hL]
    simpa [Nat.succ_eq_add_one] using Nat.lt_pow_succ_log_self h2n (max N 2)
  have hMpow : 2 ^ M ≤ L + 2 := by
    rw [hM]
    exact Nat.pow_log_le_self 2 (by omega)
  have hMlt : L + 2 < 2 ^ (M + 1) := by
    rw [hM]
    simpa [Nat.succ_eq_add_one] using Nat.lt_pow_succ_log_self h2n (L + 2)
  have hcast : ((L : ℤ) : ℝ) = (L : ℝ) := by simp
  refine ⟨by exact_mod_cast hL1, hM1, ?_, ?_, ?_⟩
  · rw [hcast]
    rcases lt_or_ge 2 N with hN2 | hN2
    · have hN2' : 2 ≤ N := by omega
      have hmax : max N 2 = N := max_eq_left hN2'
      have hLval : L = Nat.log 2 N := by rw [hL, hmax]
      rw [hLval]
      have hpow : 2 ^ Nat.log 2 N ≤ N := Nat.pow_log_le_self 2 (by omega)
      have hpowR : ((2 : ℕ) ^ Nat.log 2 N : ℝ) ≤ (N : ℝ) := by exact_mod_cast hpow
      have hlogb : Real.logb 2 ((2 : ℝ) ^ Nat.log 2 N) ≤ Real.logb 2 (N : ℝ) :=
        Real.logb_le_logb_of_le h2 (by positivity) (by simpa using hpowR)
      rw [Real.logb_pow, Real.logb_self_eq_one h2, mul_one] at hlogb
      exact hlogb.trans (le_max_right (1:ℝ) (Real.logb 2 (N:ℝ)))
    · have hmax : max N 2 = 2 := max_eq_right hN2
      have hLval : L = 1 := by rw [hL, hmax]; norm_num
      rw [hLval, Nat.cast_one]
      exact le_max_left (1:ℝ) (Real.logb 2 (N:ℝ))
  · have hlogb_le : Real.logb 2 (N : ℝ) ≤ Real.logb 2 ((max N 2 : ℕ) : ℝ) :=
      Real.logb_le_logb_of_le h2 hNpos (by exact_mod_cast le_max_left N 2)
    have hlogb_lt : Real.logb 2 ((max N 2 : ℕ) : ℝ) < (L : ℝ) + 1 := by
      have hmaxpos : (0 : ℝ) < ((max N 2 : ℕ) : ℝ) := by positivity
      have hp : (0 : ℝ) < (2 : ℝ) ^ (L + 1) := by positivity
      have hltR : ((max N 2 : ℕ) : ℝ) < (2 : ℝ) ^ (L + 1) := by
        have := hLlt
        exact_mod_cast this
      have := (Real.logb_lt_logb_iff h2 hmaxpos hp).mpr hltR
      rw [Real.logb_pow, Real.logb_self_eq_one h2, mul_one] at this
      simpa using this
    have hMltR : (L : ℝ) + 1 < (2 : ℝ) ^ ((M : ℝ) + 1) := by
      have h : ((L + 2 : ℕ) : ℝ) < ((2 : ℕ) ^ (M + 1) : ℝ) := by exact_mod_cast hMlt
      rw [Nat.cast_add, Nat.cast_ofNat] at h
      have he : (2 : ℝ) ^ ((M : ℝ) + 1) = (2 : ℝ) ^ (M + 1) := by
        have h1 : ((M + 1 : ℕ) : ℝ) = (M : ℝ) + 1 := by push_cast; ring
        rw [← h1, Real.rpow_natCast]
      rw [← he] at h
      linarith
    have hone : (1 : ℝ) < (2 : ℝ) ^ ((M : ℝ) + 1) := Real.one_lt_rpow h2 (by positivity)
    have hA : Real.logb 2 (N : ℝ) < (2 : ℝ) ^ ((M : ℝ) + 1) :=
      lt_of_lt_of_le (hlogb_le.trans_lt hlogb_lt) hMltR.le
    exact max_lt hone hA
  · rw [hcast]
    rcases lt_or_ge 1 L with hLgt | hLle
    · have hL2 : 2 ≤ L := by omega
      have hM2 : 2 ≤ M := by
        rw [hM]
        calc (2 : ℕ) = Nat.log 2 4 := by norm_num
          _ ≤ Nat.log 2 (L + 2) := Nat.log_mono_right (by omega)
      have hsub : ((M - 1 : ℕ) : ℝ) = (M : ℝ) - 1 := Nat.cast_pred (by omega : 0 < M)
      have hMpowR : (2 : ℝ) ^ M ≤ (L : ℝ) + 2 := by
        have := hMpow
        exact_mod_cast this
      have hsplit : (2 : ℝ) ^ M = (2 : ℝ) ^ (M - 1) * 2 := by
        conv_lhs => rw [← Nat.sub_add_cancel hM1]
        rw [pow_succ]
      have hstep : (2 : ℝ) ^ (M - 1) * 2 ≤ (L : ℝ) + 2 := by rw [← hsplit]; exact hMpowR
      have hL2R : (2 : ℝ) ≤ (L : ℝ) := by exact_mod_cast hL2
      have key : (2 : ℝ) ^ (M - 1) ≤ (L : ℝ) := by linarith
      rw [← hsub, Real.rpow_natCast]
      exact key
    · have hLval : L = 1 := by omega
      have hMval : M = 1 := by rw [hM, hLval]; norm_num
      rw [hLval, hMval]
      norm_num

end Work.KMTAreas.A5
