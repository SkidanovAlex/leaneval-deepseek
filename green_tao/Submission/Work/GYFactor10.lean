import Submission.Work.GYFactor9
import Submission.Commons.Analysis.Asymptotics.log_poly_le_rpow_log
import Submission.Commons.Analysis.Asymptotics.eventually_const_mul_log_pow_le_rpow
import Submission.Commons.Analysis.Order.exists_threshold_finset

/-!
# Green–Tao §10: the existence of the box-average scale `R`

This file discharges the last explicit hypothesis of `boxAvgGood_of_consts`: for every `ε > 0`
and every `W` containing all the primes up to `w` (with `w` large enough for the `E^{(1)}` tail),
there is a scale `R` with `BoxAvgGood k R W ε`.

The two ingredients are the explicit error decay
`C^m B (1+(log R)^{m-1}) + C^m B e^{-δ√(log R)} ≤ (ε/4)(q log R)^m` for `R` large
(`Commons.Analysis.Asymptotics.log_poly_le_rpow_log`, applied for each `m ≤ k·2^{k-1}` and
combined with `Commons.Analysis.Order.exists_threshold_finset`) and the elementary
`log`-versus-polynomial estimate `6·3k·(log R)^{k2^{k-1}} ≤ ε R^6` for `R` large
(`Commons.Analysis.Asymptotics.eventually_const_mul_log_pow_le_rpow`).
-/

open Finset
open scoped BigOperators

set_option maxHeartbeats 1000000
set_option linter.style.haveILetI false
set_option linter.unusedSimpArgs false

namespace GYMaj
namespace BoxAvg

variable {k : ℕ} {W : ℕ} {ε : ℝ}

/-- The error term of Green–Tao (ddr), with the uniform constants `zbC`, `zbD`. -/
noncomputable def errBound (W m : ℕ) (R : ℝ) : ℝ :=
  (zbC m) ^ m * stripBound W m * (1 + (Real.log R) ^ (m - 1))
    + (zbC m) ^ m * stripBound W m * Real.exp (-(zbD m * Real.sqrt (Real.log R)))

lemma one_le_totient_div (hW : 0 < W) : 1 ≤ (W : ℝ) / (Nat.totient W : ℝ) := by
  have hφpos : (0 : ℝ) < (Nat.totient W : ℝ) :=
    Nat.cast_pos.mpr (Nat.totient_pos.mpr hW)
  rw [le_div_iff₀ hφpos, one_mul]
  exact_mod_cast Nat.totient_le W

/-- **Existence of the box-average scale.** -/
theorem exists_R_boxAvgGood (k : ℕ) (ε : ℝ) (hε : 0 < ε) (hk : 1 ≤ k)
    {W w : ℕ} (hW : 0 < W) (hw2 : 2 ≤ w) (hw : ∀ q : ℕ, q.Prime → q ≤ w → q ∣ W)
    (hwbig : 2 * (k.factorial * k) ^ 2 ≤ w)
    (htail : ∀ m : ℕ, 1 ≤ m → m ≤ k * 2 ^ (k - 1) → Real.exp (tailMajor m w) - 1 ≤ ε / 4) :
    ∃ Rc : ℝ, 3 ≤ Rc ∧ ∀ R : ℕ, Rc ≤ (R : ℝ) → BoxAvgGood k R W ε := by
  classical
  have hK1 : 1 ≤ k * 2 ^ (k - 1) := by
    have h2 : 1 ≤ 2 ^ (k - 1) := one_le_pow₀ (by norm_num : (1:ℕ) ≤ 2)
    calc 1 = 1 * 1 := by ring
      _ ≤ k * 2 ^ (k - 1) := Nat.mul_le_mul hk h2
  have hφpos : (0 : ℝ) < (Nat.totient W : ℝ) :=
    Nat.cast_pos.mpr (Nat.totient_pos.mpr hW)
  have hq1 : 1 ≤ (W : ℝ) / (Nat.totient W : ℝ) := one_le_totient_div hW
  -- the per-`m` thresholds of the contour error
  have hfun : ∀ m ∈ Finset.Icc 1 (k * 2 ^ (k - 1)), ∃ R₀ : ℝ, 3 ≤ R₀ ∧ ∀ R : ℝ, R₀ ≤ R →
      errBound W m R ≤ (ε / 4) * ((W : ℝ) * Real.log R / (Nat.totient W : ℝ)) ^ m := by
    intro m hm
    obtain ⟨hm1, hmK⟩ := Finset.mem_Icc.mp hm
    obtain ⟨R₀, hR₀, hspec⟩ := Commons.Analysis.Asymptotics.log_poly_le_rpow_log
      (m := m) (C := zbC m) (B := stripBound W m) (δ := zbD m)
      (q := (W : ℝ) / (Nat.totient W : ℝ)) (ε := ε)
      (zbC_pos hm1) (stripBound_pos W m) (zbD_pos hm1) hq1 hε hm1
    refine ⟨R₀, hR₀, fun R hR => ?_⟩
    refine le_trans (hspec R hR) ?_
    rw [show (W : ℝ) / (Nat.totient W : ℝ) * Real.log R
        = (W : ℝ) * Real.log R / (Nat.totient W : ℝ) by ring]
  obtain ⟨R₁, hR₁3, hR₁spec⟩ :=
    Commons.Analysis.Order.exists_threshold_finset (Finset.Icc 1 (k * 2 ^ (k - 1)))
      (fun m R => errBound W m R ≤ (ε / 4) * ((W : ℝ) * Real.log R / (Nat.totient W : ℝ)) ^ m)
      hfun
  -- the threshold for the elementary box error
  have hEv := Commons.Analysis.Asymptotics.eventually_const_mul_log_pow_le_rpow
    (c := 6 * (3 * (k : ℝ))) (ε := ε) (r := 6) (K := k * 2 ^ (k - 1))
    (by positivity) hε (by norm_num)
  rw [Filter.eventually_atTop] at hEv
  obtain ⟨R₂, hR₂⟩ := hEv
  -- combine the thresholds
  set Rc : ℝ := max (max 3 R₁) (max (3 * (k : ℝ)) R₂) with hRc
  have hR₁le : R₁ ≤ Rc := le_trans (le_max_right _ _) (le_max_left _ _)
  have h3le : (3 : ℝ) ≤ Rc := le_trans (le_max_left _ _) (le_max_left _ _)
  have h3kle : 3 * (k : ℝ) ≤ Rc := le_trans (le_max_left _ _) (le_max_right _ _)
  have hR₂le : R₂ ≤ Rc := le_trans (le_max_right _ _) (le_max_right _ _)
  refine ⟨Rc, h3le, fun R hRge => ?_⟩
  have hRr3 : (3 : ℝ) ≤ (R : ℝ) := le_trans h3le hRge
  have hR3 : 3 ≤ R := by exact_mod_cast hRr3
  have hRk : 3 * k ≤ R := by
    have h1 : (3 * (k : ℝ)) ≤ (R : ℝ) := le_trans h3kle hRge
    have h2 : ((3 * k : ℕ) : ℝ) ≤ (R : ℝ) := by push_cast; linarith
    exact_mod_cast h2
  refine boxAvgGood_of_consts k R W ε hR3 hRk (by omega) hε ?_ hw2 hw hwbig htail ?_
  · -- the elementary box error
    have h := hR₂ (R : ℝ) (le_trans hR₂le hRge)
    have habs : ε * (R : ℝ) ^ (6 : ℝ) = ε * (R : ℝ) ^ 6 := by
      congr 1
      rw [show (6 : ℝ) = ((6 : ℕ) : ℝ) by norm_num, ← Real.rpow_natCast]
    rw [habs] at h
    exact h
  · -- the contour error
    intro m hm1 hmK
    exact hR₁spec m (Finset.mem_Icc.mpr ⟨hm1, hmK⟩) (R : ℝ) (le_trans hR₁le hRge)


/-! ## 2. The `E^{(1)}` tail: choosing `w` -/

/-- The uniform constant of the `-4/3` majorant. -/
noncomputable def majorC (K : ℕ) : ℝ := 200000 * ((K : ℝ) ^ 3 + 1) * (4 : ℝ) ^ K

/-- The model tail `∑_{k} (k+w+1)^{-4/3}`. -/
noncomputable def tailModel (w : ℕ) : ℝ :=
  ∑' k : ℕ, (((k + (w + 1) : ℕ) : ℝ) ^ (-(4 / 3 : ℝ)))

lemma summable_tailModel (w : ℕ) :
    Summable (fun k : ℕ => (((k + (w + 1) : ℕ) : ℝ) ^ (-(4 / 3 : ℝ)))) :=
  (summable_nat_add_iff (w + 1)).mpr
    (summable_nat_rpow_neg (c := (4 / 3 : ℝ)) (by norm_num))

/-- `1/(6m)`-exponent bookkeeping: the two exponents in `cpowMajor m n` are at most `-4/3`. -/
lemma cpow_exponent_le {m : ℕ} (hm1 : 1 ≤ m) :
    -2 + 2 * (1 / (6 * (m : ℝ))) * (m : ℝ) ≤ -(4 / 3 : ℝ) ∧
      -2 + 4 * (1 / (6 * (m : ℝ))) ≤ -(4 / 3 : ℝ) := by
  have hm0 : (0 : ℝ) < (m : ℝ) := by exact_mod_cast (by omega : 0 < m)
  constructor
  · have h : 2 * (1 / (6 * (m : ℝ))) * (m : ℝ) = 1 / 3 := by
      field_simp
      norm_num
    rw [h]
    norm_num
  · rw [show 4 * (1 / (6 * (m : ℝ))) = 2 / (3 * (m : ℝ)) by ring]
    have h1 : (1 : ℝ) ≤ (m : ℝ) := by exact_mod_cast hm1
    have h2 : 2 / (3 * (m : ℝ)) ≤ 2 / 3 := by
      apply div_le_div_of_nonneg_left (by norm_num) (by norm_num)
      linarith
    linarith

/-- The majorant is dominated by the `-4/3` model, uniformly for `m ≤ K`. -/
lemma e1pMajor_le_model {m K : ℕ} (hm1 : 1 ≤ m) (hmK : m ≤ K) {n : ℕ}
    (hn : (6 * K) ^ 2 + 2 < n) :
    e1pMajor m n ≤ majorC K * ((n : ℝ) ^ (-(4 / 3 : ℝ))) := by
  have hn1 : (1 : ℝ) ≤ (n : ℝ) := by exact_mod_cast (by omega : 1 ≤ n)
  have hn0 : (0 : ℝ) < (n : ℝ) := by linarith
  have hmK' : (m : ℝ) ≤ (K : ℝ) := by exact_mod_cast hmK
  have hK0 : (0 : ℝ) ≤ (K : ℝ) := Nat.cast_nonneg K
  have hsmall : ¬ n ≤ (6 * m) ^ 2 + 2 := by
    have h : (6 * m) ^ 2 + 2 ≤ (6 * K) ^ 2 + 2 := by
      have h6 : 6 * m ≤ 6 * K := Nat.mul_le_mul_left 6 hmK
      have := Nat.pow_le_pow_left h6 2
      omega
    omega
  rw [e1pMajor, if_neg hsmall, add_zero]
  have hexp := cpow_exponent_le hm1
  have hbracket : (n : ℝ) ^ (-2 + 2 * (1 / (6 * (m : ℝ))) * (m : ℝ))
      + (n : ℝ) ^ (-2 + 4 * (1 / (6 * (m : ℝ))))
      ≤ 2 * ((n : ℝ) ^ (-(4 / 3 : ℝ))) := by
    have h1 := Real.rpow_le_rpow_of_exponent_le hn1 hexp.1
    have h2 := Real.rpow_le_rpow_of_exponent_le hn1 hexp.2
    linarith
  have hcoef : 100000 * ((m : ℝ) ^ 3 + 1) * (4 : ℝ) ^ m
      ≤ 100000 * ((K : ℝ) ^ 3 + 1) * (4 : ℝ) ^ K := by
    have hm3 : (m : ℝ) ^ 3 ≤ (K : ℝ) ^ 3 := by
      exact pow_le_pow_left₀ (Nat.cast_nonneg m) hmK' 3
    have h4 : (4 : ℝ) ^ m ≤ (4 : ℝ) ^ K := pow_le_pow_right₀ (by norm_num) hmK
    have hpos : (0 : ℝ) ≤ 100000 := by norm_num
    have ha : (0 : ℝ) ≤ (m : ℝ) ^ 3 + 1 := by positivity
    have hb : (0 : ℝ) ≤ (4 : ℝ) ^ m := by positivity
    have hc : (0 : ℝ) ≤ (K : ℝ) ^ 3 + 1 := by positivity
    have hstep1 : 100000 * ((m : ℝ) ^ 3 + 1) * (4 : ℝ) ^ m
        ≤ 100000 * ((K : ℝ) ^ 3 + 1) * (4 : ℝ) ^ m := by
      apply mul_le_mul_of_nonneg_right _ hb
      apply mul_le_mul_of_nonneg_left _ hpos
      linarith
    have hstep2 : 100000 * ((K : ℝ) ^ 3 + 1) * (4 : ℝ) ^ m
        ≤ 100000 * ((K : ℝ) ^ 3 + 1) * (4 : ℝ) ^ K :=
      mul_le_mul_of_nonneg_left h4 (by positivity)
    linarith
  have hb0 : (0 : ℝ) ≤ (n : ℝ) ^ (-(4 / 3 : ℝ)) := Real.rpow_nonneg (le_of_lt hn0) _
  calc 100000 * ((m : ℝ) ^ 3 + 1) * (4 : ℝ) ^ m
        * ((n : ℝ) ^ (-2 + 2 * (1 / (6 * (m : ℝ))) * (m : ℝ))
          + (n : ℝ) ^ (-2 + 4 * (1 / (6 * (m : ℝ)))))
      ≤ 100000 * ((K : ℝ) ^ 3 + 1) * (4 : ℝ) ^ K
          * (2 * ((n : ℝ) ^ (-(4 / 3 : ℝ)))) := by
        refine mul_le_mul hcoef hbracket ?_ (by positivity)
        positivity
    _ = majorC K * ((n : ℝ) ^ (-(4 / 3 : ℝ))) := by
        rw [majorC]; ring

/-- The `E^{(1)}` tail, dominated by the model tail. -/
lemma tailMajor_le_model {m K w : ℕ} (hm1 : 1 ≤ m) (hmK : m ≤ K)
    (hw : (6 * K) ^ 2 + 2 ≤ w) :
    tailMajor m w ≤ majorC K * tailModel w := by
  have hsum1 : Summable (fun i : ℕ => e1pMajor m (i + (w + 1))) :=
    (summable_nat_add_iff (w + 1)).mpr (summable_e1pMajor hm1)
  have hsum2 : Summable (fun i : ℕ =>
      majorC K * ((((i + (w + 1) : ℕ) : ℝ) ^ (-(4 / 3 : ℝ))))) :=
    (summable_tailModel w).mul_left _
  have hb : ∀ i : ℕ, e1pMajor m (i + (w + 1))
      ≤ majorC K * ((((i + (w + 1) : ℕ) : ℝ) ^ (-(4 / 3 : ℝ)))) := by
    intro i
    refine e1pMajor_le_model hm1 hmK ?_
    omega
  calc tailMajor m w = ∑' i : ℕ, e1pMajor m (i + (w + 1)) := rfl
    _ ≤ ∑' i : ℕ, majorC K * ((((i + (w + 1) : ℕ) : ℝ) ^ (-(4 / 3 : ℝ)))) :=
        Summable.tsum_le_tsum hb hsum1 hsum2
    _ = majorC K * tailModel w := by rw [tsum_mul_left]; rfl

lemma majorC_pos (K : ℕ) : 0 < majorC K := by
  unfold majorC; positivity

/-- The model tail tends to `0`. -/
lemma tailModel_eventually_small {η : ℝ} (hη : 0 < η) :
    ∃ W₀ : ℕ, ∀ w : ℕ, W₀ ≤ w → tailModel w < η := by
  have htend := tendsto_sum_nat_add (fun n : ℕ => ((n : ℝ) ^ (-(4 / 3 : ℝ))))
  rw [Metric.tendsto_atTop] at htend
  obtain ⟨N, hN⟩ := htend η hη
  refine ⟨N, fun w hw => ?_⟩
  have h := hN (w + 1) (by omega)
  rw [Real.dist_eq, sub_zero] at h
  rw [abs_lt] at h
  exact h.2


/-! ## 3. The full existence statement: `w`, `W = ∏_{p ≤ w} p` and `R` -/

/-- **`BoxAvgGood` is satisfiable.**  For every `k ≥ 1` and `ε > 0` there are `w`, `W` (the product
of the primes `≤ w`) and `R` with `BoxAvgGood k R W ε`. -/
theorem exists_W_R_boxAvgGood (k : ℕ) (ε : ℝ) (hε : 0 < ε) (hk : 1 ≤ k) :
    ∃ (w W : ℕ) (Rc : ℝ), 0 < W ∧ 3 ≤ Rc ∧ 2 * (k.factorial * k) ^ 2 ≤ w ∧
      (∀ q : ℕ, q.Prime → q ≤ w → q ∣ W) ∧ ∀ R : ℕ, Rc ≤ (R : ℝ) → BoxAvgGood k R W ε := by
  classical
  set K : ℕ := k * 2 ^ (k - 1) with hK
  have hK1 : 1 ≤ K := by
    rw [hK]
    have h2 : 1 ≤ 2 ^ (k - 1) := one_le_pow₀ (by norm_num : (1 : ℕ) ≤ 2)
    calc 1 = 1 * 1 := by ring
      _ ≤ k * 2 ^ (k - 1) := Nat.mul_le_mul hk h2
  have hlogpos : 0 < Real.log (1 + ε / 4) := Real.log_pos (by linarith)
  have hdenpos : 0 < majorC K + 1 := by linarith [majorC_pos K]
  obtain ⟨W₀, hW₀⟩ := tailModel_eventually_small (div_pos hlogpos hdenpos)
  set w : ℕ := max W₀ (max ((6 * K) ^ 2 + 2) (2 * (k.factorial * k) ^ 2)) with hwdef
  have hw1 : (6 * K) ^ 2 + 2 ≤ w := le_trans (le_max_left _ _) (le_max_right _ _)
  have hw2 : 2 ≤ w := le_trans (by omega : 2 ≤ (6 * K) ^ 2 + 2) hw1
  have hwbig : 2 * (k.factorial * k) ^ 2 ≤ w := le_trans (le_max_right _ _) (le_max_right _ _)
  have hW₀le : W₀ ≤ w := le_max_left W₀ (max ((6 * K) ^ 2 + 2) (2 * (k.factorial * k) ^ 2))
  -- the `E^{(1)}` tail
  have htail : ∀ m : ℕ, 1 ≤ m → m ≤ K → Real.exp (tailMajor m w) - 1 ≤ ε / 4 := by
    intro m hm1 hmK
    have hmodel := tailMajor_le_model hm1 hmK hw1
    have hsmall : tailModel w < Real.log (1 + ε / 4) / (majorC K + 1) := hW₀ w hW₀le
    have hlt : majorC K * tailModel w < Real.log (1 + ε / 4) := by
      have h1 : majorC K * tailModel w
          < majorC K * (Real.log (1 + ε / 4) / (majorC K + 1)) :=
        mul_lt_mul_of_pos_left hsmall (majorC_pos K)
      have h2 : majorC K * (Real.log (1 + ε / 4) / (majorC K + 1))
          < Real.log (1 + ε / 4) := by
        rw [← mul_div_assoc, div_lt_iff₀ hdenpos]
        nlinarith
      linarith
    have hle : tailMajor m w ≤ Real.log (1 + ε / 4) := le_trans hmodel (le_of_lt hlt)
    have hexp := Real.exp_le_exp_of_le hle
    rw [Real.exp_log (by linarith)] at hexp
    linarith
  have htail' : ∀ m : ℕ, 1 ≤ m → m ≤ k * 2 ^ (k - 1) →
      Real.exp (tailMajor m w) - 1 ≤ ε / 4 := by
    intro m hm1 hmK
    exact htail m hm1 (by rw [hK]; exact hmK)
  -- `W`
  set W : ℕ := ∏ p ∈ Nat.primesBelow (w + 1), p with hWdef
  have hWpos : 0 < W := by
    rw [hWdef]
    exact Finset.prod_pos (fun p hp => (Nat.mem_primesBelow.mp hp).2.pos)
  have hwdiv : ∀ q : ℕ, q.Prime → q ≤ w → q ∣ W := by
    intro q hq hqw
    rw [hWdef]
    exact Finset.dvd_prod_of_mem (fun p => p)
      (Nat.mem_primesBelow.mpr ⟨by omega, hq⟩)
  obtain ⟨Rc, hRc3, hbox⟩ :=
    exists_R_boxAvgGood k ε hε hk hWpos hw2 hwdiv hwbig htail'
  exact ⟨w, W, Rc, hWpos, hRc3, hwbig, hwdiv, hbox⟩

end BoxAvg
end GYMaj
