import Mathlib
import Submission.Work.BMF.vkford51_defs
import Submission.Work.BMF.vkford_defs
import Submission.Work.BMF.liouville.vk_bounded_lambda

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false

/-!
# The bounded-`λ` Vinogradov–Korobov exponential sum bound

This file proves `Work.BMF.VKExpSum.weyl_small_lambda`: in the range
`1 ≤ λ ≤ 13/5` (`λ = log t / log N`) the block sum `Ssum N u t R` satisfies
`‖Ssum N u t R‖ ≤ C N^{1 - 1/(D λ²)}` for absolute constants `C, D > 0`.

The mathematical content is the bounded-`λ` Weyl-method bound of Ford, *Vinogradov's integral
and bounds for the Riemann zeta function*, Proc. LMS **85** (2002), Lemma 6.2 / Lemma 6.3.
That bound is available in the workspace as `Work.BMF.liouville.vk_bounded_lambda`, which
states it (for an *integer* scale) in the range `log t ≤ 88 log N` — a range that contains
`log t ≤ (13/5) log N`.  The work carried out here is the conversion to the stated real-scale
form:

* `Work.BMF.Ssum N u t R` is definitionally `Work.BMF.zpt.ESb N R u t`;
* the block sum only depends on `⌊N⌋₊`, so it is evaluated at the integer `⌊N⌋₊ ≤ N`, whose
  `λ` is at most twice the stated `λ` (because `⌊N⌋₊ ≥ N/2`); the sum is capped at `2⌊N⌋₊`
  and the at most one leftover term is bounded trivially;
* the base change `⌊N⌋₊ → N` is handled by `floor_rpow_le`, which uses `log N ≤ 2 log ⌊N⌋₊`.
-/

namespace Work.BMF.VKExpSum

open Finset

noncomputable section

/-- `log N ≤ 2 log ⌊N⌋₊` for `N ≥ 2` (since `⌊N⌋₊ ≥ N/2 ≥ 1`). -/
lemma log_le_two_log_floor (N : ℝ) (hN : 2 ≤ N) :
    Real.log N ≤ 2 * Real.log ((⌊N⌋₊ : ℕ) : ℝ) := by
  have hN0 : (2 : ℝ) ≤ ((⌊N⌋₊ : ℕ) : ℝ) := by
    have : (2 : ℕ) ≤ ⌊N⌋₊ := Nat.le_floor (by exact_mod_cast hN)
    exact_mod_cast this
  have hlt : N / 2 < ((⌊N⌋₊ : ℕ) : ℝ) := by
    have h1 : N - 1 < ((⌊N⌋₊ : ℕ) : ℝ) := by
      have := Nat.lt_floor_add_one N; linarith
    linarith
  have hpos : 0 < N / 2 := by linarith
  have hlog : Real.log (N / 2) ≤ Real.log ((⌊N⌋₊ : ℕ) : ℝ) := Real.log_le_log hpos hlt.le
  rw [Real.log_div (by linarith) (by norm_num)] at hlog
  have h2 : Real.log 2 ≤ Real.log ((⌊N⌋₊ : ℕ) : ℝ) := Real.log_le_log (by norm_num) hN0
  linarith

/-- **Base change for the bounded-`λ` bound.**  If the integer-scale bound with saving `1/D` is
known and `Dt ≥ 4D`, then the same bound at the real scale `N` holds with saving `1/Dt`
(only the constant changes, which is absorbed at the call site).  The hypothesis
`Real.log N ≤ 2 log ⌊N⌋₊` is supplied by `log_le_two_log_floor` in the application. -/
lemma floor_rpow_le (N t D Dt : ℝ) (hN : 2 ≤ N) (hNt : N ≤ t)
    (hD : 0 < D) (hDt1 : 1 ≤ Dt) (hDt4 : 4 * D ≤ Dt) :
    ((⌊N⌋₊ : ℕ) : ℝ) ^ (1 - (1 / D) * (Real.log ((⌊N⌋₊ : ℕ) : ℝ) / Real.log t) ^ 2)
      ≤ N ^ (1 - 1 / (Dt * (Real.log t / Real.log N) ^ 2)) := by
  have hN1 : 1 ≤ N := by linarith
  have hNpos : 0 < N := by linarith
  have hNlt1 : 1 < N := by linarith
  have ht1 : 1 < t := by linarith
  have hlogtpos : 0 < Real.log t := Real.log_pos ht1
  have hlogNpos : 0 < Real.log N := Real.log_pos hNlt1
  have hDtpos : 0 < Dt := lt_of_lt_of_le zero_lt_one hDt1
  have hN0ge1 : (1 : ℝ) ≤ ((⌊N⌋₊ : ℕ) : ℝ) := by
    have h1 : ((1 : ℕ) : ℝ) ≤ N := by exact_mod_cast hN1
    exact_mod_cast (Nat.le_floor h1 : (1:ℕ) ≤ ⌊N⌋₊)
  have hN0le : ((⌊N⌋₊ : ℕ) : ℝ) ≤ N := Nat.floor_le (by linarith)
  have hN0pos : 0 < ((⌊N⌋₊ : ℕ) : ℝ) := by linarith
  have hN0lt1 : (1 : ℝ) < ((⌊N⌋₊ : ℕ) : ℝ) := by
    have h1 : ((2 : ℕ) : ℝ) ≤ N := by exact_mod_cast hN
    exact_mod_cast (Nat.le_floor h1 : (2:ℕ) ≤ ⌊N⌋₊)
  have hlogN0pos : 0 < Real.log ((⌊N⌋₊ : ℕ) : ℝ) := Real.log_pos hN0lt1
  have hAB : Real.log N ≤ 2 * Real.log ((⌊N⌋₊ : ℕ) : ℝ) := log_le_two_log_floor N hN
  have hs : 1 / (Dt * (Real.log t / Real.log N) ^ 2)
      ≤ (1 / D) * (Real.log ((⌊N⌋₊ : ℕ) : ℝ) / Real.log t) ^ 2 := by
    have heq : 1 / (Dt * (Real.log t / Real.log N) ^ 2)
        = (1 / Dt) * (Real.log N / Real.log t) ^ 2 := by
      field_simp
    rw [heq]
    have hL : (1 / Dt) * (Real.log N / Real.log t) ^ 2
        = ((Real.log N) ^ 2 / Dt) / (Real.log t) ^ 2 := by ring_nf
    have hR : (1 / D) * (Real.log ((⌊N⌋₊ : ℕ) : ℝ) / Real.log t) ^ 2
        = ((Real.log ((⌊N⌋₊ : ℕ) : ℝ)) ^ 2 / D) / (Real.log t) ^ 2 := by ring_nf
    rw [hL, hR, div_le_div_iff_of_pos_right (pow_pos hlogtpos 2)]
    rw [div_le_div_iff₀ (by positivity) (by positivity)]
    have h1 : (Real.log N) ^ 2 ≤ 4 * (Real.log ((⌊N⌋₊ : ℕ) : ℝ)) ^ 2 := by
      have h0 : (0 : ℝ) ≤ Real.log N := le_of_lt hlogNpos
      have h2 : (Real.log N) ^ 2 ≤ (2 * Real.log ((⌊N⌋₊ : ℕ) : ℝ)) ^ 2 :=
        pow_le_pow_left₀ h0 hAB 2
      nlinarith [h2]
    have hsq0 : (0:ℝ) ≤ (Real.log ((⌊N⌋₊ : ℕ) : ℝ)) ^ 2 := sq_nonneg _
    have step1 : (Real.log N) ^ 2 * D ≤ 4 * (Real.log ((⌊N⌋₊ : ℕ) : ℝ)) ^ 2 * D :=
      mul_le_mul_of_nonneg_right h1 hD.le
    have step3 : (Real.log ((⌊N⌋₊ : ℕ) : ℝ)) ^ 2 * (4 * D)
        ≤ (Real.log ((⌊N⌋₊ : ℕ) : ℝ)) ^ 2 * Dt := mul_le_mul_of_nonneg_left hDt4 hsq0
    linarith [step1, step3]
  have hEt0 : 0 ≤ 1 - 1 / (Dt * (Real.log t / Real.log N) ^ 2) := by
    have hlam1 : 1 ≤ Real.log t / Real.log N := by
      rw [le_div_iff₀ hlogNpos]
      simpa using Real.log_le_log hNpos hNt
    have h2 : 1 ≤ (Real.log t / Real.log N) ^ 2 := by nlinarith [hlam1]
    have hpos : 0 < Dt * (Real.log t / Real.log N) ^ 2 :=
      mul_pos hDtpos (pow_pos (by linarith : (0:ℝ) < Real.log t / Real.log N) 2)
    rw [sub_nonneg, div_le_one hpos]
    nlinarith [hDt1, h2]
  rcases le_or_gt 0 (1 - (1 / D) * (Real.log ((⌊N⌋₊ : ℕ) : ℝ) / Real.log t) ^ 2) with he | he
  · exact le_trans (Real.rpow_le_rpow (le_of_lt hN0pos) hN0le he)
      (Real.rpow_le_rpow_of_exponent_le hN1 (by linarith))
  · exact le_trans (Real.rpow_le_one_of_one_le_of_nonpos hN0ge1 (le_of_lt he))
      (Real.one_le_rpow hN1 hEt0)

/-- Each summand of the block sum has modulus one. -/
lemma norm_summand_le_one (n : ℕ) (u t : ℝ) (hu : 0 < u) (hn : 1 ≤ n) :
    ‖((((n : ℝ) + u : ℝ)) : ℂ) ^ (-(Complex.I * (t : ℂ)))‖ = 1 := by
  have hpos : (0 : ℝ) < (n : ℝ) + u := by
    have : (0 : ℝ) < (n : ℝ) := by exact_mod_cast hn
    linarith
  rw [Complex.norm_cpow_eq_rpow_re_of_pos hpos]
  simp

/-- The block sum splits at an intermediate index, the lower block being an `ESb` at the
integer scale `⌊N⌋₊`. -/
lemma ESb_split_nat (N R u t : ℝ) (m : ℕ)
    (h1 : ⌊N⌋₊ ≤ m) (h2 : m ≤ ⌊R⌋₊) :
    Work.BMF.zpt.ESb N R u t
      = Work.BMF.zpt.ESb (((⌊N⌋₊ : ℕ) : ℝ)) (m : ℝ) u t
        + ∑ n ∈ Finset.Ioc m ⌊R⌋₊, ((((n : ℝ) + u : ℝ)) : ℂ) ^ (-(Complex.I * (t : ℂ))) := by
  have e : Work.BMF.zpt.ESb N R u t
      = Work.BMF.zpt.ESb N (m : ℝ) u t
        + ∑ n ∈ Finset.Ioc m ⌊R⌋₊, ((((n : ℝ) + u : ℝ)) : ℂ) ^ (-(Complex.I * (t : ℂ))) := by
    unfold Work.BMF.zpt.ESb
    rw [Nat.floor_natCast, ← Finset.Ioc_union_Ioc_eq_Ioc h1 h2,
      Finset.sum_union (by
        rw [Finset.disjoint_left]
        intro x hx hx'
        simp only [Finset.mem_Ioc] at hx hx'
        omega)]
  have e2 : Work.BMF.zpt.ESb N (m : ℝ) u t
      = Work.BMF.zpt.ESb (((⌊N⌋₊ : ℕ) : ℝ)) (m : ℝ) u t := by
    unfold Work.BMF.zpt.ESb
    simp only [Nat.floor_natCast]
  rw [e, e2]

/-- The leftover after capping at `2⌊N⌋₊` has at most one term, hence modulus `≤ 1`. -/
lemma tail_le_one (N R u t : ℝ) (_hN : 2 ≤ N) (hR0 : 0 ≤ R) (hu : 0 < u)
    (hR : R ≤ 2 * N) :
    ‖∑ n ∈ Finset.Ioc (min ⌊R⌋₊ (2 * ⌊N⌋₊)) ⌊R⌋₊,
        ((((n : ℝ) + u : ℝ)) : ℂ) ^ (-(Complex.I * (t : ℂ)))‖ ≤ 1 := by
  have hRfloor : ⌊R⌋₊ ≤ 2 * ⌊N⌋₊ + 1 := by
    have h5 : (⌊R⌋₊ : ℝ) < ((2 * ⌊N⌋₊ + 2 : ℕ) : ℝ) := by
      have h6 : (⌊R⌋₊ : ℝ) ≤ R := Nat.floor_le hR0
      have h7 : N < ((⌊N⌋₊ : ℕ) : ℝ) + 1 := Nat.lt_floor_add_one N
      push_cast
      linarith
    have h8 : ⌊R⌋₊ < 2 * ⌊N⌋₊ + 2 := by exact_mod_cast h5
    omega
  refine le_trans (norm_sum_le _ _) ?_
  have h1 : ∀ n ∈ Finset.Ioc (min ⌊R⌋₊ (2 * ⌊N⌋₊)) ⌊R⌋₊,
      ‖((((n : ℝ) + u : ℝ)) : ℂ) ^ (-(Complex.I * (t : ℂ)))‖ ≤ (1 : ℝ) := by
    intro n hn
    have hn1 : 1 ≤ n := by have := (Finset.mem_Ioc.mp hn).1; omega
    exact le_of_eq (norm_summand_le_one n u t hu hn1)
  calc ∑ n ∈ Finset.Ioc (min ⌊R⌋₊ (2 * ⌊N⌋₊)) ⌊R⌋₊,
        ‖((((n : ℝ) + u : ℝ)) : ℂ) ^ (-(Complex.I * (t : ℂ)))‖
      ≤ ∑ _n ∈ Finset.Ioc (min ⌊R⌋₊ (2 * ⌊N⌋₊)) ⌊R⌋₊, (1 : ℝ) := Finset.sum_le_sum h1
    _ = ((Finset.Ioc (min ⌊R⌋₊ (2 * ⌊N⌋₊)) ⌊R⌋₊).card : ℝ) := by simp
    _ ≤ 1 := by
      rw [Nat.card_Ioc]
      have : ⌊R⌋₊ - min ⌊R⌋₊ (2 * ⌊N⌋₊) ≤ 1 := by omega
      exact_mod_cast this

/-- Vinogradov–Korobov exponential sum bound in the bounded-`λ` range `1 ≤ λ ≤ 13/5`
(Ford, Proc. LMS 85 (2002), §6, Lemma 6.2, Weyl's method): there are absolute `C, D > 0` with
`‖Σ_{N<n≤R}(n+u)^{-it}‖ ≤ C N^{1-1/(D λ²)}`, `λ = log t/log N`, for `2 ≤ N ≤ t`,
`log t ≤ (13/5) log N`, `0 < u ≤ 1`, `N < R ≤ 2N`. Only existence of `C, D` matters, so the
numerical constants may be loose. Route: the Weyl shift (6.1), Taylor expansion of
`log(1+m/(n+u))` to degree `2` or `3`, Weyl's differencing (6.3), the `min`-count Lemma 6.1, and
the numeric bounds `S ≤ 5N^{1-1/20}` (`λ ≤ 1.9`), `S ≤ 30N^{1-1/83}` (`1.9 ≤ λ ≤ 2.6`). -/
theorem weyl_small_lambda :
    ∃ C D : ℝ, 0 < C ∧ 0 < D ∧
      ∀ N t u R : ℝ, 2 ≤ N → N ≤ t →
        Real.log t ≤ (13 / 5 : ℝ) * Real.log N → 0 < u → u ≤ 1 → N < R → R ≤ 2 * N →
        ‖Work.BMF.Ssum N u t R‖ ≤
          C * N ^ (1 - 1 / (D * (Real.log t / Real.log N) ^ 2)) := by
  obtain ⟨C, D, hC, hD, hW⟩ := Work.BMF.liouville.vk_bounded_lambda
  refine ⟨C + 1, max (4 * D) 1, by linarith, lt_max_of_lt_left (by linarith), ?_⟩
  intro N t u R hN hNt hlogt hu0 hu1 hR hR2
  have hNpos : 0 < N := by linarith
  have hN1 : 1 ≤ N := by linarith
  have hNlt1 : 1 < N := by linarith
  have hlogNpos : 0 < Real.log N := Real.log_pos hNlt1
  have hDtpos : 0 < max (4 * D) 1 := lt_max_of_lt_left (by linarith)
  have hDt1 : 1 ≤ max (4 * D) 1 := le_max_right _ _
  have hDt4 : 4 * D ≤ max (4 * D) 1 := le_max_left _ _
  have hN02 : (2 : ℕ) ≤ ⌊N⌋₊ := Nat.le_floor (by exact_mod_cast hN)
  have hN0le : ((⌊N⌋₊ : ℕ) : ℝ) ≤ N := Nat.floor_le (by linarith)
  have hN0ge1 : (1 : ℝ) ≤ ((⌊N⌋₊ : ℕ) : ℝ) := by
    have : (1 : ℕ) ≤ ⌊N⌋₊ := Nat.le_floor (by exact_mod_cast hN1)
    exact_mod_cast this
  have hN0t : ((⌊N⌋₊ : ℕ) : ℝ) ≤ t := le_trans hN0le hNt
  have hlog88 : Real.log t ≤ 88 * Real.log ((⌊N⌋₊ : ℕ) : ℝ) := by
    have h1 : Real.log N ≤ 2 * Real.log ((⌊N⌋₊ : ℕ) : ℝ) := log_le_two_log_floor N hN
    have h3 : 0 ≤ Real.log ((⌊N⌋₊ : ℕ) : ℝ) := Real.log_nonneg hN0ge1
    nlinarith [h1, hlogt, h3]
  have hpow : ((⌊N⌋₊ : ℕ) : ℝ) ^ (1 - (1 / D) * (Real.log ((⌊N⌋₊ : ℕ) : ℝ) / Real.log t) ^ 2)
      ≤ N ^ (1 - 1 / (max (4 * D) 1 * (Real.log t / Real.log N) ^ 2)) :=
    floor_rpow_le N t D (max (4 * D) 1) hN hNt hD hDt1 hDt4
  have hE0 : 0 ≤ 1 - 1 / (max (4 * D) 1 * (Real.log t / Real.log N) ^ 2) := by
    have hlam1 : 1 ≤ Real.log t / Real.log N := by
      rw [le_div_iff₀ hlogNpos]
      simpa using Real.log_le_log hNpos hNt
    have h2 : 1 ≤ (Real.log t / Real.log N) ^ 2 := by nlinarith [hlam1]
    have hpos : 0 < max (4 * D) 1 * (Real.log t / Real.log N) ^ 2 :=
      mul_pos hDtpos (pow_pos (by linarith : (0:ℝ) < Real.log t / Real.log N) 2)
    rw [sub_nonneg, div_le_one hpos]
    nlinarith [hDt1, h2]
  have hone : (1 : ℝ) ≤ N ^ (1 - 1 / (max (4 * D) 1 * (Real.log t / Real.log N) ^ 2)) :=
    Real.one_le_rpow hN1 hE0
  rw [show Work.BMF.Ssum N u t R = Work.BMF.zpt.ESb N R u t from rfl]
  rcases le_or_gt ⌊R⌋₊ ⌊N⌋₊ with hcase | hcase
  · have hempty : Finset.Ioc ⌊N⌋₊ ⌊R⌋₊ = ∅ :=
      Finset.Ioc_eq_empty_iff.mpr (not_lt.mpr hcase)
    rw [Work.BMF.zpt.ESb, hempty, Finset.sum_empty, norm_zero]
    positivity
  · set m : ℕ := min ⌊R⌋₊ (2 * ⌊N⌋₊) with hm
    have hm_gt : ⌊N⌋₊ < m := by rw [hm]; exact lt_min hcase (by omega)
    have hm_le : m ≤ 2 * ⌊N⌋₊ := by rw [hm]; exact min_le_right _ _
    have hm_leR : m ≤ ⌊R⌋₊ := by rw [hm]; exact min_le_left _ _
    have hsplit := ESb_split_nat N R u t m (le_of_lt hm_gt) hm_leR
    have hbd := hW ⌊N⌋₊ t u (m : ℝ) hN02 hN0t hlog88 hu0 hu1
      (by exact_mod_cast hm_gt) (by exact_mod_cast hm_le)
    have htail0 := tail_le_one N R u t hN (by linarith) hu0 hR2
    have htail : ‖∑ n ∈ Finset.Ioc m ⌊R⌋₊,
        ((((n : ℝ) + u : ℝ)) : ℂ) ^ (-(Complex.I * (t : ℂ)))‖ ≤ 1 := by
      rw [hm]; exact htail0
    calc ‖Work.BMF.zpt.ESb N R u t‖
        = ‖Work.BMF.zpt.ESb (((⌊N⌋₊ : ℕ) : ℝ)) (m : ℝ) u t
            + ∑ n ∈ Finset.Ioc m ⌊R⌋₊, ((((n : ℝ) + u : ℝ)) : ℂ) ^ (-(Complex.I * (t : ℂ)))‖ := by
          rw [hsplit]
      _ ≤ ‖Work.BMF.zpt.ESb (((⌊N⌋₊ : ℕ) : ℝ)) (m : ℝ) u t‖
            + ‖∑ n ∈ Finset.Ioc m ⌊R⌋₊, ((((n : ℝ) + u : ℝ)) : ℂ) ^ (-(Complex.I * (t : ℂ)))‖ :=
          norm_add_le _ _
      _ ≤ C * N ^ (1 - 1 / (max (4 * D) 1 * (Real.log t / Real.log N) ^ 2)) + 1 :=
          add_le_add (le_trans hbd (mul_le_mul_of_nonneg_left hpow hC.le)) htail
      _ ≤ C * N ^ (1 - 1 / (max (4 * D) 1 * (Real.log t / Real.log N) ^ 2))
            + N ^ (1 - 1 / (max (4 * D) 1 * (Real.log t / Real.log N) ^ 2)) := by linarith
      _ = (C + 1) * N ^ (1 - 1 / (max (4 * D) 1 * (Real.log t / Real.log N) ^ 2)) := by ring

end

end Work.BMF.VKExpSum
