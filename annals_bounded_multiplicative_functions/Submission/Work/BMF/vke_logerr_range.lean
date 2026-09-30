import Mathlib
import Submission.Work.BMF.vke_defs
import Submission.Work.BMF.vke_range_aux
import Submission.Work.BMF.vke_delta

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false

namespace Work.BMF

open scoped BigOperators

set_option maxHeartbeats 4000000

noncomputable section

/-- `(L^{1/6})^2 = L^{1/3}`. -/
lemma vke_sixth_sq {L : ℝ} (hL : 0 < L) : (L ^ (1/6:ℝ))^2 = L ^ (1/3:ℝ) := by
  rw [sq, ← Real.rpow_add hL]; norm_num

/-- `(L^{1/6})^3 = L^{1/2}`. -/
lemma vke_sixth_cube {L : ℝ} (hL : 0 < L) : (L ^ (1/6:ℝ))^3 = L ^ (1/2:ℝ) := by
  rw [show (L^(1/6:ℝ))^3 = (L^(1/6:ℝ) * L^(1/6:ℝ)) * L^(1/6:ℝ) by ring,
      ← Real.rpow_add hL, ← Real.rpow_add hL]
  norm_num

/-- `(c L^{1/6})^2 = c^2 L^{1/3}`. -/
lemma vke_mul_sixth_sq {c L : ℝ} (hL : 0 < L) : (c * L ^ (1/6:ℝ))^2 = c^2 * L ^ (1/3:ℝ) := by
  rw [mul_pow, vke_sixth_sq hL]

/-- `1 ≤ vkS N t` when `2 ≤ N ≤ t`. -/
lemma vke_one_le_vkS {N t : ℝ} (hN : 2 ≤ N) (hNt : N ≤ t) : 1 ≤ vkS N t := by
  have h1 : 1 ≤ vkK N t - 1 := by have := vkK_ge_six hN hNt; omega
  have h2 : 1 ≤ vkR N t := by rw [vkR]; omega
  rw [vkS]
  have := Nat.mul_le_mul h1 h2
  simpa using this

/-- Pure real-analysis input: for positive constants `A₀,…,A₃` and `D`, the expression
`A₀ L^{1/2} log L + A₁ L^{1/3} (log L)^3 + A₂ (log L)^2 + A₃ log L` is eventually dominated by
`D L^{2/3}`.  Each summand is handled by `Work.BMF.vke_log_pow_le`. -/
theorem vke_real_eventual (A0 A1 A2 A3 D : ℝ) (hA0 : 0 < A0) (hA1 : 0 < A1)
    (hA2 : 0 < A2) (hA3 : 0 < A3) (hD : 0 < D) :
    ∃ U : ℝ, 1 ≤ U ∧ ∀ L : ℝ, U ≤ L →
      A0 * L ^ (1 / 2 : ℝ) * Real.log L + A1 * L ^ (1 / 3 : ℝ) * (Real.log L) ^ 3
        + A2 * (Real.log L) ^ 2 + A3 * Real.log L ≤ D * L ^ (2 / 3 : ℝ) := by
  obtain ⟨U1, hU11, h1⟩ := vke_log_pow_le (4 * A0 / D) ((1:ℕ):ℝ) (1 / 6) (by positivity) (by norm_num)
  obtain ⟨U2, hU21, h2⟩ := vke_log_pow_le (4 * A1 / D) ((3:ℕ):ℝ) (1 / 3) (by positivity) (by norm_num)
  obtain ⟨U3, hU31, h3⟩ := vke_log_pow_le (4 * A2 / D) ((2:ℕ):ℝ) (2 / 3) (by positivity) (by norm_num)
  obtain ⟨U4, hU41, h4⟩ := vke_log_pow_le (4 * A3 / D) ((1:ℕ):ℝ) (2 / 3) (by positivity) (by norm_num)
  refine ⟨max (max U1 U2) (max U3 U4), ?_, ?_⟩
  · exact le_trans hU11 (le_trans (le_max_left U1 U2) (le_max_left _ _))
  · intro L hL
    have hLU1 : U1 ≤ L := le_trans (le_trans (le_max_left U1 U2) (le_max_left _ _)) hL
    have hLU2 : U2 ≤ L := le_trans (le_trans (le_max_right U1 U2) (le_max_left _ _)) hL
    have hLU3 : U3 ≤ L := le_trans (le_trans (le_max_left U3 U4) (le_max_right _ _)) hL
    have hLU4 : U4 ≤ L := le_trans (le_trans (le_max_right U3 U4) (le_max_right _ _)) hL
    have hL1 : (1:ℝ) ≤ L := le_trans (le_trans hU11 (le_trans (le_max_left U1 U2) (le_max_left _ _))) hL
    have hLpos : (0:ℝ) < L := lt_of_lt_of_le one_pos hL1
    have h1L := h1 L hLU1
    rw [Real.rpow_natCast, pow_one] at h1L
    have e1 : L ^ (1/6:ℝ) * L ^ (1/2:ℝ) = L ^ (2/3:ℝ) := by
      rw [← Real.rpow_add hLpos]; norm_num
    have ht1 : A0 * L ^ (1/2:ℝ) * Real.log L ≤ (D/4) * L ^ (2/3:ℝ) := by
      have hstep : (4/D) * (A0 * L^(1/2:ℝ) * Real.log L) ≤ L^(2/3:ℝ) := by
        rw [← e1]
        calc (4/D) * (A0 * L^(1/2:ℝ) * Real.log L)
            = ((4*A0/D) * Real.log L) * L^(1/2:ℝ) := by ring
          _ ≤ L^(1/6:ℝ) * L^(1/2:ℝ) := mul_le_mul_of_nonneg_right h1L (Real.rpow_nonneg hLpos.le _)
      have hc : (D/4) * (4/D) = 1 := by field_simp
      have := mul_le_mul_of_nonneg_left hstep (by positivity : (0:ℝ) ≤ D/4)
      rw [← mul_assoc, hc, one_mul] at this
      exact this
    have h2L := h2 L hLU2
    rw [Real.rpow_natCast] at h2L
    have e2 : L ^ (1/3:ℝ) * L ^ (1/3:ℝ) = L ^ (2/3:ℝ) := by
      rw [← Real.rpow_add hLpos]; norm_num
    have ht2 : A1 * L^(1/3:ℝ) * (Real.log L)^3 ≤ (D/4) * L^(2/3:ℝ) := by
      have hstep : (4/D) * (A1 * L^(1/3:ℝ) * (Real.log L)^3) ≤ L^(2/3:ℝ) := by
        rw [← e2]
        calc (4/D) * (A1 * L^(1/3:ℝ) * (Real.log L)^3)
            = ((4*A1/D) * (Real.log L)^3) * L^(1/3:ℝ) := by ring
          _ ≤ L^(1/3:ℝ) * L^(1/3:ℝ) := mul_le_mul_of_nonneg_right h2L (Real.rpow_nonneg hLpos.le _)
      have hc : (D/4) * (4/D) = 1 := by field_simp
      have := mul_le_mul_of_nonneg_left hstep (by positivity : (0:ℝ) ≤ D/4)
      rw [← mul_assoc, hc, one_mul] at this
      exact this
    have h3L := h3 L hLU3
    rw [Real.rpow_natCast] at h3L
    have ht3 : A2 * (Real.log L)^2 ≤ (D/4) * L^(2/3:ℝ) := by
      have hle := mul_le_mul_of_nonneg_left h3L (by positivity : (0:ℝ) ≤ D/4)
      have heq : (D/4) * ((4*A2/D) * (Real.log L)^2) = A2 * (Real.log L)^2 := by
        field_simp
      rw [heq] at hle
      exact hle
    have h4L := h4 L hLU4
    rw [Real.rpow_natCast, pow_one] at h4L
    have ht4 : A3 * Real.log L ≤ (D/4) * L^(2/3:ℝ) := by
      have hle := mul_le_mul_of_nonneg_left h4L (by positivity : (0:ℝ) ≤ D/4)
      have heq : (D/4) * ((4*A3/D) * Real.log L) = A3 * Real.log L := by
        field_simp
      rw [heq] at hle
      exact hle
    linarith [ht1, ht2, ht3, ht4]

/-- Lower bound for the required saving: with `c ≤ 1/100000`, `vkDelta c N t · log N ≥
(1/c) (log N)^{2/3}/log log N`. -/
lemma vke_delta_lb_aux (c : ℝ) (hc : 0 < c) (hc1 : c ≤ 1 / 100000) :
    ∃ U : ℝ, 1 ≤ U ∧ ∀ N t : ℝ, 2 ≤ N → N ≤ t →
      Real.log t ≤ c * (Real.log N) ^ (7 / 6 : ℝ) → U ≤ Real.log N →
      (1 / c) * (Real.log N) ^ (2 / 3 : ℝ) / Real.log (Real.log N)
        ≤ vkDelta c N t * Real.log N := by
  obtain ⟨Ub, hUb, hbasic⟩ := vke_basic c hc hc1
  refine ⟨max Ub 64, le_trans hUb (le_max_left _ _), ?_⟩
  intro N t hN hNt hlt hL
  have hLb : Ub ≤ Real.log N := le_trans (le_max_left _ _) hL
  have hL64 : (64:ℝ) ≤ Real.log N := le_trans (le_max_right _ _) hL
  obtain ⟨hb1, hb2, hb3, hb4, hb5, hb6, hb7, hb8, hb9, hb10⟩ := hbasic N t hN hNt hlt hLb
  set L : ℝ := Real.log N with hLdef
  set M : ℝ := Real.log L with hMdef
  have hLpos : 0 < L := by rw [hLdef]; linarith
  have hMpos : 0 < M := by
    rw [hMdef]
    exact Real.log_pos (by rw [hLdef]; linarith)
  have hlampos : 0 < vkLam N t := vkLam_pos hN hNt
  have hlogpos : 0 < Real.log (vkLam N t + 2) := Real.log_pos (by linarith)
  have hratio : Real.log N / Real.log t = 1 / vkLam N t := by rw [vkLam, one_div, inv_div]
  have hEQ : vkDelta c N t * L = c * L / ((vkLam N t)^2 * Real.log (vkLam N t + 2)) := by
    rw [vkDelta, hratio, div_pow, one_pow]
    have h1 : (vkLam N t)^2 ≠ 0 := pow_ne_zero 2 (ne_of_gt hlampos)
    have h2 : Real.log (vkLam N t + 2) ≠ 0 := ne_of_gt hlogpos
    field_simp
  have hlam2 : (vkLam N t)^2 ≤ c^2 * L^(1/3:ℝ) := by
    have h1 : (vkLam N t)^2 ≤ (c * L^(1/6:ℝ))^2 :=
      pow_le_pow_left₀ (le_of_lt hlampos) hb2 2
    rw [vke_mul_sixth_sq hLpos] at h1
    exact h1
  have hloglamM : Real.log (vkLam N t + 2) ≤ M := by
    rw [hMdef]
    exact Real.log_le_log (by linarith) hb9
  have hden_le : (vkLam N t)^2 * Real.log (vkLam N t + 2) ≤ c^2 * L^(1/3:ℝ) * M :=
    mul_le_mul hlam2 hloglamM hlogpos.le (by positivity)
  have hdenpos : 0 < (vkLam N t)^2 * Real.log (vkLam N t + 2) := by positivity
  have hM2 : (1/c) * L^(2/3:ℝ) / M = L^(2/3:ℝ) / (c * M) := by
    rw [one_div, inv_mul_eq_div, div_div]
  rw [hM2, hEQ]
  refine div_le_div_of_mul_le (mul_pos hc hMpos) hdenpos ?_
  have hLp : L^(2/3:ℝ) * L^(1/3:ℝ) = L := by
    rw [← Real.rpow_add hLpos, show (2/3:ℝ) + 1/3 = 1 by norm_num, Real.rpow_one]
  have hstep : L^(2/3:ℝ) * ((vkLam N t)^2 * Real.log (vkLam N t + 2))
      ≤ L^(2/3:ℝ) * (c^2 * L^(1/3:ℝ) * M) :=
    mul_le_mul_of_nonneg_left hden_le (Real.rpow_nonneg hLpos.le _)
  have hval : L^(2/3:ℝ) * (c^2 * L^(1/3:ℝ) * M) = (c*L) * (c*M) := by
    rw [show L^(2/3:ℝ) * (c^2 * L^(1/3:ℝ) * M) = (L^(2/3:ℝ) * L^(1/3:ℝ)) * c^2 * M by ring,
        hLp]
    ring
  linarith [hstep, hval]

/-- The `s·(1 + log s)` term of `vkLogErr` with `s = (k-1)r`. -/
lemma vke_term_s_aux (c : ℝ) (hc : 0 < c) (hc1 : c ≤ 1 / 100000) :
    ∃ U : ℝ, 1 ≤ U ∧ ∀ N t : ℝ, 2 ≤ N → N ≤ t →
      Real.log t ≤ c * (Real.log N) ^ (7 / 6 : ℝ) → U ≤ Real.log N →
      (((vkK N t - 1 : ℕ) : ℝ) * ((vkR N t : ℕ) : ℝ))
          * (1 + Real.log (((vkK N t - 1 : ℕ) : ℝ) * ((vkR N t : ℕ) : ℝ)))
        ≤ 816 * (1 + Real.log 816 + 4 / 3) * (Real.log N) ^ (1 / 3 : ℝ)
            * (Real.log (Real.log N)) ^ 2 := by
  obtain ⟨Ub, hUb, hbasic⟩ := vke_basic c hc hc1
  refine ⟨max Ub 64, le_trans hUb (le_max_left _ _), ?_⟩
  intro N t hN hNt hlt hL
  have hLb : Ub ≤ Real.log N := le_trans (le_max_left _ _) hL
  have hL64 : (64:ℝ) ≤ Real.log N := le_trans (le_max_right _ _) hL
  obtain ⟨hb1, hb2, hb3, hb4, hb5, hb6, hb7, hb8, hb9, hb10⟩ := hbasic N t hN hNt hlt hLb
  set sR : ℝ := (((vkK N t - 1 : ℕ) : ℝ)) * (((vkR N t : ℕ) : ℝ)) with hsdef
  set L : ℝ := Real.log N with hLdef
  set M : ℝ := Real.log L with hMdef
  have hLpos : 0 < L := by rw [hLdef]; linarith
  have hM1 : 1 ≤ M := by
    rw [hMdef]
    have h3L : (3:ℝ) ≤ L := by rw [hLdef]; linarith
    have := Real.log_le_log (by norm_num : (0:ℝ) < 3) h3L
    linarith [Real.log_three_gt_d9]
  have hMpos : 0 < M := by linarith
  have hlampos : 0 < vkLam N t := vkLam_pos hN hNt
  have hs1 : 1 ≤ sR := by
    rw [hsdef]
    have hk1 : (1:ℝ) ≤ (((vkK N t - 1 : ℕ)) : ℝ) := by
      have : 1 ≤ vkK N t - 1 := by omega
      exact_mod_cast this
    have hr1 : (1:ℝ) ≤ (((vkR N t : ℕ)) : ℝ) := by
      have : 1 ≤ vkR N t := by rw [vkR]; omega
      exact_mod_cast this
    have := mul_le_mul hk1 hr1 (by norm_num : (0:ℝ) ≤ 1) (by linarith : (0:ℝ) ≤ (((vkK N t - 1 : ℕ)) : ℝ))
    simpa using this
  have hlam2 : (vkLam N t)^2 ≤ c^2 * L^(1/3:ℝ) := by
    have h1 : (vkLam N t)^2 ≤ (c * L^(1/6:ℝ))^2 :=
      pow_le_pow_left₀ (le_of_lt hlampos) hb2 2
    rw [vke_mul_sixth_sq hLpos] at h1
    exact h1
  have hlog4 : Real.log 4 ≤ 2 := by rw [Real.log_four_eq]; linarith [Real.log_two_lt_d9]
  have hloglamM : Real.log (vkLam N t + 2) ≤ M := by
    rw [hMdef]
    exact Real.log_le_log (by linarith) hb9
  have hlogsum : Real.log 4 + Real.log (vkLam N t + 2) ≤ 3 * M := by
    linarith [hlog4, hloglamM, hM1]
  have hS : sR ≤ 816 * L^(1/3:ℝ) * M := by
    rw [hsdef]
    have hds := vke_deltaS_bound hN hNt
    have hsEq : ((vkS N t : ℕ):ℝ) = (((vkK N t - 1 : ℕ):ℝ)) * (((vkR N t:ℕ):ℝ)) := by
      rw [vkS]; push_cast; ring
    rw [hsEq] at hds
    have hstep : 272 * (vkLam N t)^2 * (Real.log 4 + Real.log (vkLam N t + 2))
        ≤ 272 * (c^2 * L^(1/3:ℝ)) * (3 * M) := by
      refine mul_le_mul (mul_le_mul_of_nonneg_left hlam2 (by norm_num)) hlogsum ?_ ?_
      · have h1 : (0:ℝ) < Real.log 4 := Real.log_pos (by norm_num)
        have h2 : (0:ℝ) < Real.log (vkLam N t + 2) := Real.log_pos (by linarith)
        linarith
      · positivity
    have hstep2 : 272 * (c^2 * L^(1/3:ℝ)) * (3 * M) ≤ 816 * L^(1/3:ℝ) * M := by
      have hc2 : c^2 ≤ 1 := by nlinarith [hc1, le_of_lt hc]
      have hXnn : (0:ℝ) ≤ L^(1/3:ℝ) * M :=
        mul_nonneg (Real.rpow_nonneg hLpos.le _) hMpos.le
      have e : 272 * (c^2 * L^(1/3:ℝ)) * (3 * M) = 816 * (c^2 * (L^(1/3:ℝ) * M)) := by ring
      rw [e]
      calc 816 * (c^2 * (L^(1/3:ℝ) * M)) ≤ 816 * (1 * (L^(1/3:ℝ) * M)) :=
            mul_le_mul_of_nonneg_left (mul_le_mul_of_nonneg_right hc2 hXnn) (by norm_num)
        _ = 816 * L^(1/3:ℝ) * M := by ring
    linarith [hds, hstep, hstep2]
  have hlogs : Real.log sR ≤ Real.log 816 + (1/3) * M + Real.log M := by
    have h1 : Real.log sR ≤ Real.log (816 * L^(1/3:ℝ) * M) :=
      Real.log_le_log (by linarith) hS
    have h2 : Real.log (816 * L^(1/3:ℝ) * M) = Real.log 816 + (1/3) * M + Real.log M := by
      have hL13 : (0:ℝ) < L^(1/3:ℝ) := Real.rpow_pos_of_pos hLpos _
      have h816L : (0:ℝ) < 816 * L^(1/3:ℝ) := by positivity
      rw [Real.log_mul (ne_of_gt h816L) (ne_of_gt hMpos)]
      have h2a : Real.log (816 * L^(1/3:ℝ)) = Real.log 816 + Real.log (L^(1/3:ℝ)) :=
        Real.log_mul (by norm_num) (ne_of_gt hL13)
      rw [h2a, Real.log_rpow hLpos, ← hMdef]
    linarith [h1, h2.le, h2.ge]
  have h1logs : 1 + Real.log sR ≤ (1 + Real.log 816 + 4/3) * M := by
    have hlogM : Real.log M ≤ M := by
      have := Real.log_le_sub_one_of_pos hMpos; linarith
    have h816 : (0:ℝ) ≤ Real.log 816 := Real.log_nonneg (by norm_num)
    have hkey : 1 + Real.log 816 ≤ (1 + Real.log 816) * M := by nlinarith [hM1, h816]
    linarith [hlogs, hlogM, hkey]
  have hlog_sR_nn : 0 ≤ 1 + Real.log sR := by
    have := Real.log_nonneg hs1; linarith
  have hTs : sR * (1 + Real.log sR)
      ≤ 816 * (1 + Real.log 816 + 4/3) * L^(1/3:ℝ) * M^2 := by
    have hnn2 : (0:ℝ) ≤ 816 * L^(1/3:ℝ) * M := by positivity
    calc sR * (1 + Real.log sR)
        ≤ (816 * L^(1/3:ℝ) * M) * ((1 + Real.log 816 + 4/3) * M) :=
          mul_le_mul hS h1logs hlog_sR_nn hnn2
      _ = 816 * (1 + Real.log 816 + 4/3) * L^(1/3:ℝ) * M^2 := by ring
  exact hTs

/-- The factorial term of `vkLogErr` is bounded by an absolute constant. -/
lemma vke_term_fact_aux (c K : ℝ) (hc : 0 < c) (hc1 : c ≤ 1 / 100000) (hK : 0 < K) :
    ∃ U : ℝ, 1 ≤ U ∧ ∀ N t : ℝ, 2 ≤ N → N ≤ t →
      Real.log t ≤ c * (Real.log N) ^ (7 / 6 : ℝ) → U ≤ Real.log N →
      Real.log (56 * K * (4 : ℝ) ^ (vkK N t) * ((Nat.factorial (vkK N t - 1) : ℕ) : ℝ))
          / (2 * ((vkS N t : ℕ) : ℝ))
        ≤ (Real.log 56 + |Real.log K|) / (240 * Real.log 6)
            + Real.log 4 / (40 * Real.log 6) + 1 / 48 := by
  obtain ⟨Ub, hUb, hbasic⟩ := vke_basic c hc hc1
  refine ⟨max Ub 64, le_trans hUb (le_max_left _ _), ?_⟩
  intro N t hN hNt hlt hL
  have hLb : Ub ≤ Real.log N := le_trans (le_max_left _ _) hL
  set k : ℝ := ((vkK N t : ℕ) : ℝ) with hkdef
  set F : ℝ := ((Nat.factorial (vkK N t - 1) : ℕ) : ℝ) with hFdef
  set D : ℝ := 2 * ((vkS N t : ℕ) : ℝ) with hDdef
  have hk6 : (6:ℝ) ≤ k := by rw [hkdef]; exact_mod_cast vkK_ge_six hN hNt
  have hkpos : 0 < k := by linarith
  have hlogkpos : 0 < Real.log k := Real.log_pos (by linarith)
  have hFpos : 0 < F := by rw [hFdef]; exact_mod_cast Nat.factorial_pos _
  have hkm1pos : 0 < k - 1 := by linarith
  have hlog6pos : (0:ℝ) < Real.log 6 := Real.log_pos (by norm_num)
  have hseq : ((vkS N t : ℕ) : ℝ) = (k - 1) * (((vkR N t : ℕ)) : ℝ) := by
    have h1 : ((vkS N t : ℕ):ℝ) = (((vkK N t - 1 : ℕ)):ℝ) * (((vkR N t : ℕ)):ℝ) := by
      rw [vkS]; push_cast; ring
    have h2 : (((vkK N t - 1 : ℕ)):ℝ) = k - 1 := by
      rw [hkdef, Nat.cast_sub (by have := vkK_ge_six hN hNt; omega : 1 ≤ vkK N t)]; push_cast; ring
    rw [h1, h2]
  have hDpos : 0 < D := by
    rw [hDdef]
    have hs1 : (1:ℝ) ≤ ((vkS N t : ℕ) : ℝ) := by exact_mod_cast vke_one_le_vkS hN hNt
    linarith
  have hrR : 4 * k * Real.log k ≤ (((vkR N t : ℕ)):ℝ) := by
    rw [hkdef]; exact vkR_ge
  have hD_lb : 8 * (k - 1) * k * Real.log k ≤ D := by
    rw [hDdef, hseq]
    have h := mul_le_mul_of_nonneg_left hrR (by linarith : (0:ℝ) ≤ 2 * (k - 1))
    nlinarith [h]
  have hDg240 : 240 * Real.log 6 ≤ D := by
    have h6 : Real.log 6 ≤ Real.log k := Real.log_le_log (by norm_num) hk6
    nlinarith [hD_lb, h6, hk6, hlogkpos]
  have hDg40k : 40 * k * Real.log 6 ≤ D := by
    have h6 : Real.log 6 ≤ Real.log k := Real.log_le_log (by norm_num) hk6
    nlinarith [hD_lb, h6, hk6, hkpos, hlogkpos]
  have hDg48 : 48 * (k - 1) * Real.log k ≤ D := by
    nlinarith [hD_lb, hk6, hkm1pos, hlogkpos]
  have hnum : Real.log (56 * K * (4:ℝ)^(vkK N t) * F)
      ≤ Real.log 56 + |Real.log K| + k * Real.log 4 + (k - 1) * Real.log k := by
    have h1 : Real.log (56 * K * (4:ℝ)^(vkK N t) * F)
        = Real.log 56 + Real.log K + Real.log ((4:ℝ)^(vkK N t)) + Real.log F := by
      have hA : (0:ℝ) < (4:ℝ)^(vkK N t) := by positivity
      rw [show 56 * K * (4:ℝ)^(vkK N t) * F = (56*K) * ((4:ℝ)^(vkK N t) * F) by ring,
          Real.log_mul (by positivity) (by positivity),
          Real.log_mul (by norm_num) (ne_of_gt hK),
          Real.log_mul (ne_of_gt hA) (ne_of_gt hFpos)]
      ring
    have h2 : Real.log ((4:ℝ)^(vkK N t)) = k * Real.log 4 := by
      rw [Real.log_pow, hkdef]
    have h3 : Real.log F ≤ (k - 1) * Real.log k := by
      have hf : F ≤ k ^ (vkK N t - 1) := by
        rw [hFdef, hkdef]
        have h1 : Nat.factorial (vkK N t - 1) ≤ (vkK N t)^(vkK N t - 1) :=
          le_trans (Nat.factorial_le_pow _) (Nat.pow_le_pow_left (Nat.sub_le _ _) _)
        exact_mod_cast h1
      have hflog := Real.log_le_log (by rw [hFdef]; exact_mod_cast Nat.factorial_pos _) hf
      have hkey : Real.log (k ^ (vkK N t - 1)) = (k - 1) * Real.log k := by
        rw [Real.log_pow]
        have : (((vkK N t - 1 : ℕ)):ℝ) = k - 1 := by
          rw [hkdef, Nat.cast_sub (by have := vkK_ge_six hN hNt; omega : 1 ≤ vkK N t)]; push_cast; ring
        rw [this]
      linarith [hflog, hkey.le, hkey.ge]
    have h4 : Real.log K ≤ |Real.log K| := le_abs_self _
    linarith [h1.le, h1.ge, h2.le, h2.ge, h3, h4]
  have hterm1 : (Real.log 56 + |Real.log K|) / D
      ≤ (Real.log 56 + |Real.log K|) / (240 * Real.log 6) := by
    refine div_le_div_of_mul_le hDpos (mul_pos (by norm_num) hlog6pos) ?_
    have hN1 : (0:ℝ) ≤ Real.log 56 + |Real.log K| := by
      have := Real.log_pos (by norm_num : (1:ℝ) < 56); positivity
    exact mul_le_mul_of_nonneg_left hDg240 hN1
  have hterm2 : k * Real.log 4 / D ≤ Real.log 4 / (40 * Real.log 6) := by
    refine div_le_div_of_mul_le hDpos (mul_pos (by norm_num) hlog6pos) ?_
    have hlog4nn : (0:ℝ) ≤ Real.log 4 := le_of_lt (Real.log_pos (by norm_num))
    have h := mul_le_mul_of_nonneg_left hDg40k hlog4nn
    nlinarith [h]
  have hterm3 : (k - 1) * Real.log k / D ≤ 1 / 48 := by
    refine div_le_div_of_mul_le hDpos (by norm_num) ?_
    nlinarith [hDg48]
  have hnumD : Real.log (56 * K * (4:ℝ)^(vkK N t) * F) / D
      ≤ (Real.log 56 + |Real.log K| + k * Real.log 4 + (k - 1) * Real.log k) / D :=
    div_le_div_of_nonneg_right hnum hDpos.le
  have hsplit : (Real.log 56 + |Real.log K| + k * Real.log 4 + (k - 1) * Real.log k) / D
      ≤ (Real.log 56 + |Real.log K|) / (240 * Real.log 6)
          + Real.log 4 / (40 * Real.log 6) + 1 / 48 := by
    have e : (Real.log 56 + |Real.log K| + k * Real.log 4 + (k - 1) * Real.log k) / D
        = (Real.log 56 + |Real.log K|)/D + k * Real.log 4/D + (k-1)*Real.log k/D := by
      rw [add_div, add_div, add_div]
    rw [e]
    linarith [hterm1, hterm2, hterm3]
  linarith [hnumD, hsplit]

/-- **The logarithmic-error budget.**  For `log N` large (depending on `C0, C1, K`),
`vkLogErr C0 C1 K N t ≤ vkDelta (1/100000) N t · log N`.  Route: with
`c = 1/100000` and `λ = vkLam N t`, `log t ≤ c (log N)^{7/6}` gives
`δ_req log N = c (log N)³ /(log t)² / log(λ+2) ≥ (log N)^{2/3} / (c² log(λ+2))`, growing faster than
each of the four summands of `vkLogErr`: `C0 k³ ≲ (log N)^{1/2}`,
`C1 (k−1)r(1+log((k−1)r))/2 ≲ (log N)^{1/3}(log log N)²`,
`log(14k²) ≲ log log N`, and `log(56K4^k (k−1)!)/(2s) = O(1)`.  Use `Work.BMF.vke_basic`
(`k ≤ (log N)^{1/6}`, `log k ≤ (1/6) log log N`, `λ ≥ 1`) together with the definition
`vkR N t = ⌈4k log k⌉₊ + 1` to bound `r`. -/
theorem vke_logerr_range (C0 C1 K : ℝ) (hC0 : 0 < C0) (hC1 : 0 < C1) (hK : 0 < K) :
    ∃ U : ℝ, 0 < U ∧ ∀ (N t : ℝ), 2 ≤ N → N ≤ t →
      Real.log t ≤ (1 / 100000) * Real.log N ^ (7 / 6 : ℝ) → U ≤ Real.log N →
      vkLogErr C0 C1 K N t ≤ vkDelta (1 / 100000) N t * Real.log N := by
  set A1v : ℝ := 408 * C1 * (1 + Real.log 816 + 4/3) with hA1v
  set Bvalv : ℝ := (Real.log 56 + |Real.log K|) / (240 * Real.log 6)
      + Real.log 4 / (40 * Real.log 6) + 1/48 with hBvalv
  set Dv : ℝ := 1 / (4 * (1/100000)) with hDv
  have hA1vpos : 0 < A1v := by
    rw [hA1v]
    have h1 : (0:ℝ) < 1 + Real.log 816 + 4/3 := by
      have := Real.log_pos (by norm_num : (1:ℝ) < 816); linarith
    positivity
  have hBvalvpos : 0 < Bvalv := by
    rw [hBvalv]
    have h1 : (0:ℝ) < Real.log 56 := Real.log_pos (by norm_num)
    have h2 : (0:ℝ) < Real.log 4 := Real.log_pos (by norm_num)
    have h3 : (0:ℝ) < Real.log 6 := Real.log_pos (by norm_num)
    have h4 : (0:ℝ) < 240 * Real.log 6 := by linarith
    have h5 : (0:ℝ) < 40 * Real.log 6 := by linarith
    have h6 : (0:ℝ) < (Real.log 56 + |Real.log K|) / (240 * Real.log 6) :=
      div_pos (by linarith [h1, abs_nonneg (Real.log K)]) h4
    have h7 : (0:ℝ) < Real.log 4 / (40 * Real.log 6) := div_pos h2 h5
    linarith
  have hDvpos : 0 < Dv := by rw [hDv]; norm_num
  obtain ⟨U1, hU11, h1⟩ := vke_real_eventual C0 A1v 1 Bvalv Dv
      hC0 hA1vpos (by norm_num) hBvalvpos hDvpos
  obtain ⟨U2, hU21, h2⟩ := vke_term_s_aux (1/100000) (by norm_num) le_rfl
  obtain ⟨U3, hU31, h3⟩ := vke_term_fact_aux (1/100000) K (by norm_num) le_rfl hK
  obtain ⟨U4, hU41, h4⟩ := vke_delta_lb_aux (1/100000) (by norm_num) le_rfl
  obtain ⟨U5, hU51, h5⟩ := vke_basic (1/100000) (by norm_num) le_rfl
  refine ⟨max (max (max U1 U2) (max U3 U4)) (max U5 64) + 1, ?_, ?_⟩
  · have hlt1 : U1 ≤ max (max (max U1 U2) (max U3 U4)) (max U5 64) :=
      le_trans (le_trans (le_max_left U1 U2) (le_max_left _ _)) (le_max_left _ _)
    linarith [hU11, hlt1]
  · intro N t hN hNt hlt hL
    have hMain_le : max (max (max U1 U2) (max U3 U4)) (max U5 64) ≤ Real.log N := by linarith
    have hLU1 : U1 ≤ Real.log N :=
      le_trans (le_trans (le_trans (le_max_left U1 U2) (le_max_left _ _)) (le_max_left _ _)) hMain_le
    have hLU2 : U2 ≤ Real.log N :=
      le_trans (le_trans (le_trans (le_max_right U1 U2) (le_max_left _ _)) (le_max_left _ _)) hMain_le
    have hLU3 : U3 ≤ Real.log N :=
      le_trans (le_trans (le_trans (le_max_left U3 U4) (le_max_right _ _)) (le_max_left _ _)) hMain_le
    have hLU4 : U4 ≤ Real.log N :=
      le_trans (le_trans (le_trans (le_max_right U3 U4) (le_max_right _ _)) (le_max_left _ _)) hMain_le
    have hLU5 : U5 ≤ Real.log N :=
      le_trans (le_trans (le_max_left U5 64) (le_max_right _ _)) hMain_le
    have hLU6 : (64:ℝ) ≤ Real.log N :=
      le_trans (le_trans (le_max_right U5 64) (le_max_right _ _)) hMain_le
    have hA := h1 (Real.log N) hLU1
    have hB := h2 N t hN hNt hlt hLU2
    have hC := h3 N t hN hNt hlt hLU3
    have hDb := h4 N t hN hNt hlt hLU4
    obtain ⟨hb1, hb2, hb3, hb4, hb5, hb6, hb7, hb8, hb9, hb10⟩ := h5 N t hN hNt hlt hLU5
    set L : ℝ := Real.log N with hLdef
    set M : ℝ := Real.log L with hMdef
    have hLpos : 0 < L := by rw [hLdef]; linarith
    have hMpos : 0 < M := by
      rw [hMdef]; exact Real.log_pos (by rw [hLdef]; linarith)
    have hMnn : 0 ≤ M := le_of_lt hMpos
    have hT1 : C0 * ((vkK N t:ℕ):ℝ)^3 ≤ C0 * L^(1/2:ℝ) := by
      have hknn : (0:ℝ) ≤ ((vkK N t:ℕ):ℝ) := by positivity
      have hle : ((vkK N t:ℕ):ℝ)^3 ≤ (L^(1/6:ℝ))^3 := pow_le_pow_left₀ hknn hb4 3
      rw [vke_sixth_cube hLpos] at hle
      exact mul_le_mul_of_nonneg_left hle hC0.le
    have hT3 : Real.log (14 * ((vkK N t:ℕ):ℝ)^2) ≤ M := by
      have hkpos : (0:ℝ) < ((vkK N t:ℕ):ℝ) := by
        have : (0:ℕ) < vkK N t := by omega
        exact_mod_cast this
      have hk4 : (4:ℝ) ≤ ((vkK N t:ℕ):ℝ) := by exact_mod_cast (by omega : 4 ≤ vkK N t)
      have hk2 : (14:ℝ) ≤ ((vkK N t:ℕ):ℝ)^2 := by nlinarith [hk4]
      have hle14 : 14 * ((vkK N t:ℕ):ℝ)^2 ≤ ((vkK N t:ℕ):ℝ)^4 := by
        have h := mul_le_mul_of_nonneg_right hk2 (by positivity : (0:ℝ) ≤ ((vkK N t:ℕ):ℝ)^2)
        have h4 : ((vkK N t:ℕ):ℝ)^2 * ((vkK N t:ℕ):ℝ)^2 = ((vkK N t:ℕ):ℝ)^4 := by ring
        linarith [h, h4.le, h4.ge]
      have h1 : Real.log (14 * ((vkK N t:ℕ):ℝ)^2) ≤ Real.log (((vkK N t:ℕ):ℝ)^4) :=
        Real.log_le_log (by positivity) hle14
      have h2 : Real.log (((vkK N t:ℕ):ℝ)^4) = 4 * Real.log ((vkK N t:ℕ):ℝ) := by
        rw [Real.log_pow]; norm_num
      rw [h2] at h1
      have h3 : 4 * Real.log ((vkK N t:ℕ):ℝ) ≤ 4 * ((1/6) * M) := by linarith [hb10]
      have h4 : 4 * ((1/6) * M) ≤ M := by linarith [hMnn]
      linarith [h1, h3, h4]
    have hVLE : vkLogErr C0 C1 K N t
        ≤ C0 * L^(1/2:ℝ) + A1v * L^(1/3:ℝ) * M^2 + M + Bvalv := by
      have hT2 : C1 * ((((vkK N t - 1 : ℕ) : ℝ) * ((vkR N t : ℕ) : ℝ))
            * (1 + Real.log (((vkK N t - 1 : ℕ) : ℝ) * ((vkR N t : ℕ) : ℝ)))) / 2
          ≤ A1v * L^(1/3:ℝ) * M^2 := by
        have h := mul_le_mul_of_nonneg_left hB (by linarith : (0:ℝ) ≤ C1 / 2)
        have hA1 : A1v = (C1 / 2) * (816 * (1 + Real.log 816 + 4/3)) := by rw [hA1v]; ring
        rw [hA1]
        calc C1 * ((((vkK N t - 1 : ℕ) : ℝ) * ((vkR N t : ℕ) : ℝ))
              * (1 + Real.log (((vkK N t - 1 : ℕ) : ℝ) * ((vkR N t : ℕ) : ℝ)))) / 2
            = (C1 / 2) * ((((vkK N t - 1 : ℕ) : ℝ) * ((vkR N t : ℕ) : ℝ))
              * (1 + Real.log (((vkK N t - 1 : ℕ) : ℝ) * ((vkR N t : ℕ) : ℝ)))) := by ring
          _ ≤ (C1 / 2) * (816 * (1 + Real.log 816 + 4/3) * L^(1/3:ℝ) * M^2) := h
          _ = (C1 / 2) * (816 * (1 + Real.log 816 + 4/3)) * L^(1/3:ℝ) * M^2 := by ring
      rw [vkLogErr]
      exact add_le_add (add_le_add (add_le_add hT1 hT2) hT3) hC
    have hmm : vkLogErr C0 C1 K N t * M
        ≤ (C0 * L^(1/2:ℝ) + A1v * L^(1/3:ℝ) * M^2 + M + Bvalv) * M :=
      mul_le_mul_of_nonneg_right hVLE hMnn
    have hexp : (C0 * L^(1/2:ℝ) + A1v * L^(1/3:ℝ) * M^2 + M + Bvalv) * M
        = C0 * L^(1/2:ℝ) * M + A1v * L^(1/3:ℝ) * M^3 + 1 * M^2 + Bvalv * M := by ring
    have hA' : C0 * L^(1/2:ℝ) * M + A1v * L^(1/3:ℝ) * M^3 + 1 * M^2 + Bvalv * M
        ≤ Dv * L^(2/3:ℝ) := hA
    have hprod : vkLogErr C0 C1 K N t * M ≤ Dv * L^(2/3:ℝ) := by
      rw [hexp] at hmm
      exact le_trans hmm hA'
    have hDle : Dv * L^(2/3:ℝ) / M ≤ (1 / (1/100000)) * L^(2/3:ℝ) / M := by
      have hD : Dv ≤ 1 / (1/100000) := by rw [hDv]; norm_num
      have hnn : (0:ℝ) ≤ L^(2/3:ℝ) / M := div_nonneg (Real.rpow_nonneg hLpos.le _) hMnn
      calc Dv * L^(2/3:ℝ) / M = Dv * (L^(2/3:ℝ) / M) := by ring
        _ ≤ (1 / (1/100000)) * (L^(2/3:ℝ) / M) := mul_le_mul_of_nonneg_right hD hnn
        _ = (1 / (1/100000)) * L^(2/3:ℝ) / M := by ring
    have hfin : vkLogErr C0 C1 K N t ≤ Dv * L^(2/3:ℝ) / M :=
      (le_div_iff₀ hMpos).mpr hprod
    exact le_trans hfin (le_trans hDle hDb)

end

end Work.BMF
