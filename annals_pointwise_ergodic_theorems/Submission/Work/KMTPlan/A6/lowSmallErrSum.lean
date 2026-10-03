import Mathlib
import Submission.Work.KMTPlan.A6.scale_ge_of_heightScale
import Submission.Work.KMTPlan.A6.lacunarySumInv
import Submission.Work.KMTAreas.A7.ModelApproxHelpers

namespace Work.KMTPlan.A6

open scoped ENNReal NNReal BigOperators

/-- A `Λ`-lacunary sequence with `Λ > 1` and `a n ≥ 1` is strictly increasing, hence monotone. -/
lemma lacunary_mono (Λ : ℝ≥0) (hΛ : 1 < Λ) (a : ℕ → ℝ≥0)
    (ha : PointwiseErgodicTheorems.Lacunary Λ a) (ha1 : ∀ n, 1 ≤ a n) : Monotone a := by
  have hstep : ∀ n, Λ * a n ≤ a (n + 1) := fun n =>
    le_of_lt ((lt_div_iff₀ (lt_of_lt_of_le zero_lt_one (ha1 n))).mp (ha n))
  have hstrict : ∀ n, a n < a (n + 1) := fun n => by
    have hpos : (0 : ℝ≥0) < a n := lt_of_lt_of_le zero_lt_one (ha1 n)
    calc a n = 1 * a n := (one_mul _).symm
      _ < Λ * a n := mul_lt_mul_of_pos_right hΛ hpos
      _ ≤ a (n + 1) := hstep n
  exact (strictMono_nat_of_lt_succ hstrict).monotone

/-- **The lacunary reciprocal-floors over a height-scale-index set are summable with the
exponential gain.**

If `P` selects only indices `n` whose height scale `heightScale C₀ ⌊a n⌋` is at least `L`, then
the sum of the reciprocal floors `⌊a n⌋⁻¹` over `P` is bounded by
`2 Λ/(Λ-1) · 2^{-2^{L/C₀-2}}`.

The hypothesis `L ≤ heightScale C₀ ⌊a n⌋ = C₀ LogLog ⌊a n⌋` forces `⌊a n⌋ ≥ 2^{2^{L/C₀-2}}`
(`scale_ge_of_heightScale`), so each *individual* term is already exponentially small; the sum
over the lacunary indices only contributes the factor `Λ/(Λ-1)` because, `a` being `Λ`-lacunary,
the reciprocal terms decrease geometrically — this is `lacunarySumInv`, applied at the least
index `m` of `P` (for which `⌊a m⌋ ≥ 2^{2^{L/C₀-2}}` by the same height-scale bound). The factor
`2` comes from the passage from `⌊a n⌋` to `a n` (`⌊x⌋ ≥ x/2` for `x ≥ 1`, valid here since the
height-scale condition gives `a n ≥ 2`). -/
theorem lowSmallErrSum (C₀ : ℕ) (hC₀ : 1 ≤ C₀) (Λ : NNReal) (hΛ : 1 < Λ)
    (a : ℕ → NNReal) (ha : PointwiseErgodicTheorems.Lacunary Λ a) (ha1 : ∀ n, 1 ≤ a n)
    (P : ℕ → Prop) [DecidablePred P] (L : ℕ) (hL : 2 * C₀ ≤ L)
    (hcond : ∀ n, P n → Work.Analysis.EndVar.heightScale C₀ (Nat.floor (a n)) ≥ L) :
    (∑' n : ℕ, if P n then ENNReal.ofReal ((((Nat.floor (a n) : ℕ) : ℝ))⁻¹) else 0)
      ≤ ENNReal.ofReal (2 * ((Λ : ℝ) / ((Λ : ℝ) - 1)))
          * ENNReal.ofReal ((2 : ℝ) ^ (-(2 : ℝ) ^ ((L : ℝ) / (C₀ : ℝ) - 2))) := by
  classical
  have hΛR : (1 : ℝ) < (Λ : ℝ) := by exact_mod_cast hΛ
  have hΛpos : (0 : ℝ) < (Λ : ℝ) := by linarith
  have hC0pos : (0 : ℝ) < (C₀ : ℝ) := by exact_mod_cast (show 0 < C₀ by omega)
  set T : ℝ := (2 : ℝ) ^ ((2 : ℝ) ^ ((L : ℝ) / (C₀ : ℝ) - 2)) with hTdef
  have hLC : (2 : ℝ) ≤ (L : ℝ) / (C₀ : ℝ) := by
    rw [le_div_iff₀ hC0pos]
    have h : ((2 * C₀ : ℕ) : ℝ) ≤ (L : ℝ) := by exact_mod_cast hL
    push_cast at h
    linarith
  have hexp0 : (0 : ℝ) ≤ (L : ℝ) / (C₀ : ℝ) - 2 := by linarith
  have hT2 : (2 : ℝ) ≤ T := by
    rw [hTdef]
    have h1 : (1 : ℝ) ≤ (2 : ℝ) ^ ((L : ℝ) / (C₀ : ℝ) - 2) :=
      Real.one_le_rpow (by norm_num) hexp0
    calc (2 : ℝ) = (2 : ℝ) ^ (1 : ℝ) := (Real.rpow_one 2).symm
      _ ≤ (2 : ℝ) ^ ((2 : ℝ) ^ ((L : ℝ) / (C₀ : ℝ) - 2)) :=
          Real.rpow_le_rpow_of_exponent_le (by norm_num) h1
  have hTpos : (0 : ℝ) < T := lt_of_lt_of_le (by norm_num) hT2
  have hratio : (0 : ℝ) ≤ (Λ : ℝ) / ((Λ : ℝ) - 1) := div_nonneg hΛpos.le (by linarith)
  have hgeomnorm : ‖((Λ : ℝ)⁻¹)‖ < 1 := by
    rw [Real.norm_eq_abs, abs_of_pos (by positivity : (0 : ℝ) < (Λ : ℝ)⁻¹)]
    rw [inv_lt_one₀ (by positivity : (0 : ℝ) < (Λ : ℝ))]
    linarith
  have hgeom : Summable (fun n : ℕ => ((Λ : ℝ)⁻¹) ^ n) :=
    summable_geometric_of_norm_lt_one hgeomnorm
  have hfloor1 : ∀ n, 1 ≤ Nat.floor (a n) := by
    intro n
    have h : (1 : ℝ) ≤ (a n : ℝ) := by exact_mod_cast ha1 n
    exact (Nat.floor_pos (R := ℝ)).mpr h
  -- the height-scale condition pins `⌊a n⌋` above `T = 2^{2^{L/C₀-2}}`
  have hcondT : ∀ n, P n → T ≤ ((Nat.floor (a n) : ℕ) : ℝ) := fun n hn =>
    scale_ge_of_heightScale C₀ hC₀ (N := Nat.floor (a n)) (L := L) (hfloor1 n) (hcond n hn) hL
  -- `⌊x⌋ ≥ x/2` for `x ≥ 1`, so `⌊a n⌋⁻¹ ≤ 2 (a n)⁻¹`
  have hterm : ∀ n, P n → (((Nat.floor (a n) : ℕ) : ℝ))⁻¹ ≤ 2 * ((a n : ℝ))⁻¹ := by
    intro n hn
    have hhalf : (a n : ℝ) / 2 ≤ ((Nat.floor (a n) : ℕ) : ℝ) :=
      Work.KMTAreas.A7.floor_ge_half (ha1 n)
    have hpos : (0 : ℝ) < (a n : ℝ) / 2 := by
      have h1 : (1 : ℝ) ≤ (a n : ℝ) := by exact_mod_cast ha1 n
      linarith
    calc (((Nat.floor (a n) : ℕ) : ℝ))⁻¹ = 1 / ((Nat.floor (a n) : ℕ) : ℝ) := (one_div _).symm
      _ ≤ 1 / ((a n : ℝ) / 2) := one_div_le_one_div_of_le hpos hhalf
      _ = 2 * ((a n : ℝ))⁻¹ := by rw [one_div_div, div_eq_mul_inv]
  -- summability of the reciprocal scales, against the geometric series `Λ^{-n}`
  have hbound_a : ∀ n, (if P n then ((a n : ℝ))⁻¹ else 0) ≤ ((Λ : ℝ)⁻¹) ^ n := by
    intro n
    by_cases hn : P n
    · rw [if_pos hn]
      have hpow : (Λ : ℝ) ^ n ≤ (a n : ℝ) := by
        exact_mod_cast Work.Analysis.EndVar.pow_le_of_lacunary hΛ ha ha1 n
      have hpos : (0 : ℝ) < (Λ : ℝ) ^ n := by positivity
      have h := one_div_le_one_div_of_le hpos hpow
      rwa [one_div, one_div, ← inv_pow] at h
    · rw [if_neg hn]; positivity
  have hsumm_a : Summable (fun n : ℕ => (if P n then ((a n : ℝ))⁻¹ else 0)) :=
    Summable.of_nonneg_of_le (fun n => by split_ifs <;> positivity) hbound_a hgeom
  have hsumm_2a : Summable (fun n : ℕ => 2 * (if P n then ((a n : ℝ))⁻¹ else 0)) :=
    hsumm_a.mul_left 2
  have hsumm_f : Summable (fun n : ℕ => (if P n then (((Nat.floor (a n) : ℕ) : ℝ))⁻¹ else 0)) := by
    refine Summable.of_nonneg_of_le (fun n => ?_) (fun n => ?_) hsumm_2a
    · split_ifs <;> positivity
    · by_cases hn : P n
      · rw [if_pos hn, if_pos hn]; exact hterm n hn
      · rw [if_neg hn, if_neg hn]; norm_num
  have hfg : ∀ n, (if P n then (((Nat.floor (a n) : ℕ) : ℝ))⁻¹ else 0)
      ≤ 2 * (if P n then ((a n : ℝ))⁻¹ else 0) := by
    intro n
    by_cases hn : P n
    · rw [if_pos hn, if_pos hn]; exact hterm n hn
    · rw [if_neg hn, if_neg hn]; norm_num
  have hmain1 := hsumm_f.tsum_le_tsum hfg hsumm_2a
  by_cases hP : ∃ n, P n
  · -- the least index of `P` is where the reciprocal is already small, and `lacunarySumInv`
    -- converts the lacunary decay into the factor `Λ/(Λ-1)`
    have hm : ∀ n, P n → a (Nat.find hP) ≤ a n := fun n hn =>
      (lacunary_mono Λ hΛ a ha ha1) (Nat.find_min' hP hn)
    have hlas := lacunarySumInv Λ hΛ a ha ha1 P hm
    have hspec : P (Nat.find hP) := Nat.find_spec hP
    have hTle : T ≤ (a (Nat.find hP) : ℝ) :=
      le_trans (hcondT _ hspec) (Nat.floor_le (by positivity : (0 : ℝ) ≤ (a (Nat.find hP) : ℝ)))
    have hinvle : (a (Nat.find hP) : ℝ)⁻¹ ≤ T⁻¹ := by
      have h := one_div_le_one_div_of_le hTpos hTle
      rwa [one_div, one_div] at h
    have h2 : (∑' n : ℕ, (if P n then (((Nat.floor (a n) : ℕ) : ℝ))⁻¹ else 0))
        ≤ 2 * ((Λ : ℝ) / ((Λ : ℝ) - 1)) * T⁻¹ := by
      calc (∑' n, (if P n then (((Nat.floor (a n) : ℕ) : ℝ))⁻¹ else 0))
          ≤ ∑' n, 2 * (if P n then ((a n : ℝ))⁻¹ else 0) := hmain1
        _ = 2 * ∑' n, (if P n then ((a n : ℝ))⁻¹ else 0) := tsum_mul_left
        _ ≤ 2 * (((Λ : ℝ) / ((Λ : ℝ) - 1)) * (a (Nat.find hP) : ℝ)⁻¹) :=
            mul_le_mul_of_nonneg_left hlas (by norm_num)
        _ ≤ 2 * (((Λ : ℝ) / ((Λ : ℝ) - 1)) * T⁻¹) :=
            mul_le_mul_of_nonneg_left (mul_le_mul_of_nonneg_left hinvle hratio) (by norm_num)
        _ = 2 * ((Λ : ℝ) / ((Λ : ℝ) - 1)) * T⁻¹ := by ring
    have hofReal : (∑' n : ℕ, (if P n then ENNReal.ofReal ((((Nat.floor (a n) : ℕ) : ℝ))⁻¹) else 0))
        = ENNReal.ofReal (∑' n : ℕ, (if P n then (((Nat.floor (a n) : ℕ) : ℝ))⁻¹ else 0)) := by
      rw [tsum_congr (fun n => (Work.KMTAreas.A7.ofReal_ite (P n) _).symm),
          ← ENNReal.ofReal_tsum_of_nonneg (fun n => by split_ifs <;> positivity) hsumm_f]
    rw [hofReal]
    calc ENNReal.ofReal (∑' n : ℕ, (if P n then (((Nat.floor (a n) : ℕ) : ℝ))⁻¹ else 0))
        ≤ ENNReal.ofReal (2 * ((Λ : ℝ) / ((Λ : ℝ) - 1)) * T⁻¹) := ENNReal.ofReal_le_ofReal h2
      _ = ENNReal.ofReal (2 * ((Λ : ℝ) / ((Λ : ℝ) - 1))) * ENNReal.ofReal T⁻¹ :=
          ENNReal.ofReal_mul (mul_nonneg (by norm_num) hratio)
      _ = ENNReal.ofReal (2 * ((Λ : ℝ) / ((Λ : ℝ) - 1)))
            * ENNReal.ofReal ((2 : ℝ) ^ (-(2 : ℝ) ^ ((L : ℝ) / (C₀ : ℝ) - 2))) := by
          rw [hTdef, Real.rpow_neg (by norm_num : (0 : ℝ) ≤ 2)]
  · -- no admissible index: the sum vanishes
    have hzero : (fun n : ℕ => (if P n then ENNReal.ofReal ((((Nat.floor (a n) : ℕ) : ℝ))⁻¹) else 0))
        = fun _ => 0 := by
      funext n
      rw [if_neg (fun hn => hP ⟨n, hn⟩)]
    rw [hzero]
    simp

end Work.KMTPlan.A6
