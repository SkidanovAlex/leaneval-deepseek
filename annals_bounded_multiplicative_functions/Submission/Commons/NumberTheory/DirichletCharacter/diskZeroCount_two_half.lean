import Mathlib
import Submission.Commons.NumberTheory.DirichletCharacter.completedL_circleExcess_le
import Submission.Commons.Analysis.Complex.sum_divisor_le_circleAvg
import Submission.Commons.NumberTheory.DirichletCharacter.zerosInStrip
import Submission.Commons.NumberTheory.DirichletCharacter.L_lower_re_two_explicit

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false

open Complex DirichletCharacter Metric
open scoped Real Topology BigOperators

set_option maxHeartbeats 1600000

namespace Commons.NumberTheory.DirichletCharacter

/-!
## Elementary bounds for `L(χ,·)` on `Re s ≥ 2`
-/

private lemma partial_sum_inv_sq_le (K : ℕ) :
    (∑ n ∈ Finset.range K, (if 2 ≤ n then ((n : ℝ) ^ 2)⁻¹ else 0)) ≤ 13 / 20 := by
  rw [← Finset.sum_filter]
  have h2 : (Finset.range K).filter (fun n => 2 ≤ n) = Finset.Icc (2:ℕ) (K - 1) := by
    ext n
    simp only [Finset.mem_filter, Finset.mem_range, Finset.mem_Icc]
    omega
  rw [h2]
  rcases lt_or_ge K 11 with hK | hK
  · refine (Finset.sum_le_sum_of_subset_of_nonneg
      (s := Finset.Icc (2:ℕ) (K-1)) (t := Finset.Icc (2:ℕ) 10) ?_ ?_).trans ?_
    · intro x hx
      simp only [Finset.mem_Icc] at hx ⊢
      omega
    · intro x _ _
      positivity
    · norm_num [Finset.sum_Icc_succ_top]
  · have h3 : Finset.Icc (2:ℕ) (K - 1) = Finset.Icc (2:ℕ) 10 ∪ Finset.Ioc (10:ℕ) (K - 1) := by
      ext n
      simp only [Finset.mem_Icc, Finset.mem_union, Finset.mem_Ioc]
      omega
    rw [h3, Finset.sum_union]
    · have h4 := sum_Ioc_inv_sq_le_sub (α := ℝ) (k := 10) (n := K - 1) (by norm_num)
        (by omega : 10 ≤ K - 1)
      have h5 : (∑ n ∈ Finset.Icc (2:ℕ) 10, ((n : ℝ) ^ 2)⁻¹) ≤ 11 / 20 := by
        norm_num [Finset.sum_Icc_succ_top]
      have h6 : (∑ n ∈ Finset.Ioc (10:ℕ) (K - 1), ((n : ℝ) ^ 2)⁻¹) ≤ (10 : ℝ)⁻¹ := by
        refine h4.trans ?_
        exact sub_le_self _ (by positivity)
      linarith
    · exact Finset.disjoint_left.mpr (fun x hx hx' => by
        simp only [Finset.mem_Icc] at hx
        simp only [Finset.mem_Ioc] at hx'
        omega)

/-- On `Re s ≥ 2` the Dirichlet series of `L(χ,·)` is within `13/20` of its constant term `1`. -/
lemma norm_LFunction_sub_one_le {N : ℕ} [NeZero N] (χ : DirichletCharacter ℂ N) {s : ℂ}
    (hs : 2 ≤ s.re) : ‖LFunction χ s - 1‖ ≤ 13 / 20 := by
  have h1 : 1 < s.re := by linarith
  let f : ℕ → ℂ := fun n => (χ (n : ZMod N) : ℂ)
  let a : ℕ → ℂ := LSeries.term f s
  let c : ℕ → ℂ := fun n => if n = 1 then 0 else a n
  have hf1 : f 1 = 1 := by simp [f]
  have hsum : Summable a := by
    have := DirichletCharacter.LSeriesSummable_of_one_lt_re χ h1
    simpa only [LSeriesSummable, a, f] using this
  have ha1 : a 1 = 1 := by
    simp only [a, LSeries.term_of_ne_zero (by norm_num : (1:ℕ) ≠ 0), hf1]
    simp
  have htail : (∑' n, c n) = (∑' n, a n) - 1 := by
    have hsplit := Summable.tsum_eq_add_tsum_ite (f := a) hsum (b := 1)
    calc (∑' n, c n) = (a 1 + ∑' n, c n) - a 1 := by ring
      _ = (∑' n, a n) - 1 := by rw [← hsplit, ha1]
  have hle : ∀ n : ℕ, ‖c n‖ ≤ (if 2 ≤ n then ((n : ℝ) ^ 2)⁻¹ else 0) := by
    intro n
    by_cases hn1 : n = 1
    · subst hn1; simp [c]
    · by_cases hn0 : n = 0
      · subst hn0
        have : a 0 = 0 := by simp [a]
        simp [c, this]
      · have h2n : 2 ≤ n := by omega
        have hc : c n = a n := by simp [c, hn1]
        rw [hc]
        rw [show ‖a n‖ = ‖f n‖ / (n : ℝ) ^ s.re by
          rw [LSeries.norm_term_eq, if_neg hn0]]
        simp only [h2n, ↓reduceIte]
        have hfn : ‖f n‖ ≤ 1 := by simpa [f] using norm_le_one χ (n : ZMod N)
        have hpos : 0 < (n : ℝ) ^ s.re := Real.rpow_pos_of_pos (by positivity) _
        have hpos2 : 0 < (n : ℝ) ^ (2 : ℝ) := Real.rpow_pos_of_pos (by positivity) _
        have hpow : (n : ℝ) ^ (2 : ℝ) ≤ (n : ℝ) ^ s.re :=
          Real.rpow_le_rpow_of_exponent_le
            (by exact_mod_cast Nat.one_le_iff_ne_zero.mpr hn0) hs
        have hrw : ((n : ℝ) ^ 2)⁻¹ = (((n : ℝ) ^ (2:ℝ)))⁻¹ := by rw [Real.rpow_two]
        rw [hrw]
        calc ‖f n‖ / (n : ℝ) ^ s.re ≤ 1 / (n : ℝ) ^ s.re :=
              div_le_div_of_nonneg_right hfn hpos.le
          _ ≤ 1 / (n : ℝ) ^ (2:ℝ) :=
              div_le_div_of_nonneg_left (by norm_num) hpos2 hpow
          _ = (((n : ℝ) ^ (2:ℝ)))⁻¹ := by rw [one_div]
  have hnorm : ‖LFunction χ s - 1‖ = ‖∑' n, c n‖ := by
    have hLF : LFunction χ s = LSeries f s := by
      simpa [f] using DirichletCharacter.LFunction_eq_LSeries χ h1
    have : LSeries f s = ∑' n, a n := rfl
    rw [hLF, this, ← htail]
  rw [hnorm]
  have hsumm_c : Summable (fun n => ‖c n‖) := by
    refine Summable.of_nonneg_of_le (fun n => norm_nonneg _) hle ?_
    exact summable_of_sum_range_le (fun n => by positivity) partial_sum_inv_sq_le
  refine (norm_tsum_le_tsum_norm hsumm_c).trans ?_
  exact Real.tsum_le_of_sum_range_le (fun n => norm_nonneg _)
    (fun K => (Finset.sum_le_sum (fun n _ => hle n)).trans (partial_sum_inv_sq_le K))


/-- On `Re s ≥ 2`, `log ‖L(χ,s)‖ ≤ log 2`. -/
lemma log_norm_LFunction_le_log_two {N : ℕ} [NeZero N] (χ : DirichletCharacter ℂ N) {s : ℂ}
    (hs : 2 ≤ s.re) : Real.log ‖LFunction χ s‖ ≤ Real.log 2 := by
  have hb := norm_LFunction_sub_one_le χ hs
  have h3 : ‖LFunction χ s‖ ≤ 33 / 20 := by
    calc ‖LFunction χ s‖ = ‖(LFunction χ s - 1) + 1‖ := by ring_nf
      _ ≤ ‖LFunction χ s - 1‖ + ‖(1 : ℂ)‖ := norm_add_le _ _
      _ ≤ 13 / 20 + 1 := by rw [norm_one]; linarith
      _ = 33 / 20 := by norm_num
  rcases eq_or_lt_of_le (norm_nonneg (LFunction χ s)) with h0 | h0
  · rw [← h0, Real.log_zero]
    exact Real.log_nonneg (by norm_num)
  · calc Real.log ‖LFunction χ s‖ ≤ Real.log (33 / 20) := Real.log_le_log h0 h3
      _ ≤ Real.log 2 := Real.log_le_log (by norm_num) (by norm_num)

/-- Functional-equation bound for `log ‖L(χ,z)‖` when `Re z < -1` (so that the reflected
point `1 - z` has real part `> 2`, where `|L| ≤ 33/20`). -/
theorem LFunction_log_le_of_re_lt_neg_one {N : ℕ} [NeZero N] (χ : DirichletCharacter ℂ N)
    (hχ : χ ≠ 1) (hχprim : χ.IsPrimitive) {z : ℂ}
    (hσ : z.re < -1) (hσ2 : -(3:ℝ) ≤ z.re) (hγ : gammaFactor χ z ≠ 0) :
    Real.log ‖LFunction χ z‖ ≤ (1/2 - z.re)*Real.log (N:ℝ) + Real.log 2
      + ((1/2 - z.re)*(Real.log (2 + |z.im/2|) + 2) + (z.re - 3/2)*Real.log Real.pi
          + Real.log (2*Real.pi)) := by
  have hN : N ≠ 1 := ne_one_of_char_ne_one hχ
  have hlt1 : z.re < 1 := by linarith
  have hFE := LFunction_norm_FE χ hχ hχprim hlt1 hγ
  have hNpos : 0 < (N:ℝ) := by exact_mod_cast Nat.pos_of_ne_zero (NeZero.ne N)
  have hN1 : (1:ℝ) ≤ N := by exact_mod_cast Nat.succ_le_of_lt (Nat.pos_of_ne_zero (NeZero.ne N))
  have hγpos : 0 < ‖gammaFactor χ z‖ := norm_pos_iff.mpr hγ
  have hre1z : (1-z).re > 0 := by simp only [Complex.sub_re, Complex.one_re]; linarith
  have hγ1ne : gammaFactor χ (1-z) ≠ 0 := by
    rcases χ.even_or_odd with hE | hO
    · rw [Even.gammaFactor_def hE]; exact Complex.Gammaℝ_ne_zero_of_re_pos hre1z
    · rw [Odd.gammaFactor_def hO]
      exact Complex.Gammaℝ_ne_zero_of_re_pos (by simp only [Complex.add_re, Complex.one_re]; linarith)
  have hγ1pos : 0 < ‖gammaFactor χ (1-z)‖ := norm_pos_iff.mpr hγ1ne
  have h1 : (0:ℝ) < (N:ℝ)^(1/2-z.re) := Real.rpow_pos_of_pos hNpos _
  have hlogFE : Real.log ‖LFunction χ z‖
      = (1/2 - z.re)*Real.log (N:ℝ) + Real.log ‖LFunction χ⁻¹ (1-z)‖
        + (Real.log ‖gammaFactor χ (1-z)‖ - Real.log ‖gammaFactor χ z‖) := by
    rw [hFE]
    rw [Real.log_mul (mul_ne_zero h1.ne' (norm_pos_iff.mpr (by
          have : (1-z).re > 2 := by simp only [Complex.sub_re, Complex.one_re]; linarith
          exact DirichletCharacter.LFunction_ne_zero_of_one_le_re (χ⁻¹)
            (Or.inl (inv_ne_one_of_one χ hχ)) (by linarith))).ne')
        ((div_pos hγ1pos hγpos).ne'),
      Real.log_mul h1.ne' (norm_pos_iff.mpr (by
          have : (1-z).re > 2 := by simp only [Complex.sub_re, Complex.one_re]; linarith
          exact DirichletCharacter.LFunction_ne_zero_of_one_le_re (χ⁻¹)
            (Or.inl (inv_ne_one_of_one χ hχ)) (by linarith))).ne',
      Real.log_div hγ1pos.ne' hγpos.ne',
      Real.log_rpow hNpos]
  have hnorm1z : Real.log ‖LFunction χ⁻¹ (1-z)‖ ≤ Real.log 2 := by
    refine log_norm_LFunction_le_log_two χ⁻¹ ?_
    simp only [Complex.sub_re, Complex.one_re]
    linarith
  have hratio := gammaFactor_ratio_le_of_re_nonpos χ (by linarith : z.re ≤ 0) hσ2 hγ
  rw [hlogFE]
  linarith

/-- `|L(χ,2+iT)| ≥ 7/20` for every non-trivial `χ`. -/
lemma L_lower_re_two_explicit' {N : ℕ} [NeZero N] (χ : DirichletCharacter ℂ N) (hχ : χ ≠ 1)
    (T : ℝ) : (7 : ℝ) / 20 ≤ ‖LFunction χ ((2 : ℂ) + Complex.I * (T : ℂ))‖ := by
  have hs : (2 : ℝ) ≤ (((2 : ℂ) + Complex.I * (T : ℂ))).re := by simp
  have h := norm_LFunction_sub_one_le χ hs
  have htri : ‖(1 : ℂ)‖ - ‖LFunction χ ((2 : ℂ) + Complex.I * (T : ℂ))‖
      ≤ ‖LFunction χ ((2 : ℂ) + Complex.I * (T : ℂ)) - 1‖ := by
    simpa [norm_sub_rev] using
      norm_sub_norm_le (a := (1 : ℂ)) (b := LFunction χ ((2:ℂ) + Complex.I * (T:ℂ)))
  have : (1 : ℝ) - ‖LFunction χ ((2 : ℂ) + Complex.I * (T : ℂ))‖ ≤ 13/20 := by
    simpa using htri.trans h
  linarith


/-! ## A piecewise upper bound for `log ‖L(χ,·)‖` on the circle `|z - (2+iT₀)| = 5` -/

/-- Absorption of the `Γ`-ratio term of the functional equation into `circleP`. -/
private lemma absorb_ratio {N : ℕ} [NeZero N] {T₀ σ im Lv B : ℝ} (hσ : σ ≤ 0)
    (him : 2 + |im/2| ≤ (|T₀| + 9)/2) (hLv : Lv ≤ B) :
    (1/2 - σ)*Real.log (N:ℝ) + Lv
      + ((1/2 - σ)*(Real.log (2 + |im/2|) + 2) + (σ - 3/2)*Real.log Real.pi
          + Real.log (2*Real.pi))
      ≤ (1/2 - σ)*circleP N T₀ + (Real.log 2 + B) := by
  have hlogsub : Real.log (2 + |im/2|) ≤ Real.log ((|T₀| + 9)/2) :=
    Real.log_le_log (by positivity) him
  have hcoef : 0 ≤ 1/2 - σ := by linarith
  have hkey : (1/2 - σ) * Real.log (2 + |im/2|) ≤ (1/2 - σ) * Real.log ((|T₀| + 9)/2) :=
    mul_le_mul_of_nonneg_left hlogsub hcoef
  have h2pi : Real.log (2*Real.pi) = Real.log 2 + Real.log Real.pi :=
    Real.log_mul (by norm_num) Real.pi_ne_zero
  have hP : circleP N T₀ = Real.log (N:ℝ) + Real.log ((|T₀|+9)/2) + 2 - Real.log Real.pi := rfl
  rw [hP, h2pi]
  nlinarith [hkey, hLv]

/-- A piecewise explicit upper bound for `log ‖L(χ,·)‖` on the disk `|z - (2+iT₀)| ≤ 5`,
depending only on `Re z`. -/
noncomputable def circUB (N : ℕ) (T₀ : ℝ) (σ : ℝ) : ℝ :=
  if 2 ≤ σ then Real.log 2
  else if 1 ≤ σ then circleA N T₀
  else if 1/2 ≤ σ then circleB N T₀
  else if 0 ≤ σ then circleC N T₀
  else if -1 ≤ σ then (1/2 - σ) * circleP N T₀ + (Real.log 2 + circleA N T₀)
  else (1/2 - σ) * circleP N T₀ + (Real.log 2 + Real.log 2)

lemma circUB_nonneg {N : ℕ} [NeZero N] (T₀ σ : ℝ) : 0 ≤ circUB N T₀ σ := by
  unfold circUB
  split_ifs with h1 h2 h3 h4 h5
  · exact Real.log_nonneg (by norm_num)
  · exact circleA_nonneg N T₀
  · exact circleB_nonneg N T₀
  · exact circleC_nonneg N T₀
  · have hp := circleP_nonneg N T₀
    have hcoef : 0 ≤ 1/2 - σ := by linarith
    have := mul_nonneg hcoef hp
    linarith [log_two_nonneg, circleA_nonneg (N := N) T₀]
  · have hp := circleP_nonneg N T₀
    have hcoef : 0 ≤ 1/2 - σ := by linarith
    have := mul_nonneg hcoef hp
    linarith [log_two_nonneg]

/-- Pointwise bound: on the sphere `|z - (2 + i T₀)| = 5` the logarithm of `‖L(χ,z)‖` is
bounded by `circUB`. -/
theorem LFunction_log_le_circUB {N : ℕ} [NeZero N] (χ : DirichletCharacter ℂ N)
    (hχ : χ ≠ 1) (hχprim : χ.IsPrimitive) (T₀ : ℝ) {z : ℂ}
    (hre1 : -(3:ℝ) ≤ z.re) (him : |z.im| ≤ |T₀| + 5) :
    Real.log ‖LFunction χ z‖ ≤ circUB N T₀ z.re := by
  have hN1 : (1:ℝ) ≤ N := by exact_mod_cast Nat.one_le_iff_ne_zero.mpr (NeZero.ne N)
  have hlog7 : Real.log (2 + |z.im|) ≤ Real.log (|T₀| + 7) :=
    Real.log_le_log (by linarith [abs_nonneg z.im]) (by linarith)
  have hlog17 : Real.log (1 + |z.im|) ≤ Real.log (|T₀| + 7) :=
    Real.log_le_log (by linarith [abs_nonneg z.im]) (by linarith)
  have hboundh : 2 + |z.im/2| ≤ (|T₀| + 9)/2 := by
    rw [abs_div]
    have : |z.im|/2 ≤ (|T₀|+5)/2 := by linarith
    linarith
  have hA : Real.log (Real.log (N:ℝ) + Real.log (2 + |z.im|) + 6) ≤ circleA N T₀ := by
    unfold circleA
    apply Real.log_le_log
    · have h1' : 0 ≤ Real.log (N:ℝ) := Real.log_nonneg hN1
      have h2' : 0 ≤ Real.log (2 + |z.im|) := Real.log_nonneg (by linarith [abs_nonneg z.im])
      linarith
    · linarith
  unfold circUB
  by_cases h1 : 2 ≤ z.re
  · rw [if_pos h1]
    exact log_norm_LFunction_le_log_two χ h1
  · rw [if_neg h1]
    by_cases h2 : 1 ≤ z.re
    · rw [if_pos h2]
      exact (LFunction_log_le_right χ hχ h2).trans hA
    · rw [if_neg h2]
      by_cases h3 : 1/2 ≤ z.re
      · rw [if_pos h3]
        have h := LFunction_log_le_strip χ hχ (by linarith : 0 < z.re) (by linarith : z.re ≤ 1)
        have h4 : -Real.log z.re ≤ Real.log 2 := by
          have := Real.log_le_log (by norm_num : (0:ℝ) < 1/2) h3
          rw [Real.log_div (by norm_num) (by norm_num), Real.log_one, zero_sub] at this
          linarith
        unfold circleB
        linarith
      · rw [if_neg h3]
        by_cases h4 : 0 ≤ z.re
        · rw [if_pos h4]
          have h := LFunction_log_le_of_re_le_half χ hχ hχprim h4 (le_of_lt (not_le.mp h3))
          unfold circleC
          linarith
        · rw [if_neg h4]
          by_cases h5 : -1 ≤ z.re
          · rw [if_pos h5]
            rcases eq_or_ne (gammaFactor χ z) 0 with hγ | hγ
            · rw [LFunction_eq_completed_div_gammaFactor χ z
                (Or.inr (ne_one_of_char_ne_one hχ)), hγ, div_zero, norm_zero, Real.log_zero]
              have hp := circleP_nonneg N T₀
              have hca := circleA_nonneg N T₀
              have hcoef : 0 ≤ 1/2 - z.re := by linarith
              have := mul_nonneg hcoef hp
              linarith [log_two_nonneg]
            · refine (LFunction_log_le_of_re_nonpos χ hχ hχprim (by linarith : z.re ≤ 0) hre1 hγ).trans ?_
              exact absorb_ratio (N := N) (T₀ := T₀) (σ := z.re) (im := z.im)
                (Lv := Real.log (Real.log (N:ℝ) + Real.log (2 + |z.im|) + 6))
                (B := circleA N T₀) (by linarith) hboundh hA
          · rw [if_neg h5]
            rcases eq_or_ne (gammaFactor χ z) 0 with hγ | hγ
            · rw [LFunction_eq_completed_div_gammaFactor χ z
                (Or.inr (ne_one_of_char_ne_one hχ)), hγ, div_zero, norm_zero, Real.log_zero]
              have hp := circleP_nonneg N T₀
              have hcoef : 0 ≤ 1/2 - z.re := by linarith
              have := mul_nonneg hcoef hp
              linarith [log_two_nonneg]
            · refine (LFunction_log_le_of_re_lt_neg_one χ hχ hχprim
                (by linarith : z.re < -1) hre1 hγ).trans ?_
              exact absorb_ratio (N := N) (T₀ := T₀) (σ := z.re) (im := z.im)
                (Lv := Real.log 2) (B := Real.log 2) (by linarith) hboundh le_rfl


/-! ## Measurability, integrability and the arc decomposition -/

lemma measurable_circUB (N : ℕ) (T₀ : ℝ) : Measurable (fun σ : ℝ => circUB N T₀ σ) := by
  unfold circUB
  refine Measurable.ite measurableSet_Ici measurable_const ?_
  refine Measurable.ite measurableSet_Ici measurable_const ?_
  refine Measurable.ite measurableSet_Ici measurable_const ?_
  refine Measurable.ite measurableSet_Ici measurable_const ?_
  refine Measurable.ite measurableSet_Ici ?_ ?_
  · exact ((measurable_const.sub measurable_id).mul measurable_const).add measurable_const
  · exact ((measurable_const.sub measurable_id).mul measurable_const).add measurable_const

lemma intervalIntegrable_circUB_cos (N : ℕ) [NeZero N] (T₀ a b : ℝ) :
    IntervalIntegrable (fun θ : ℝ => circUB N T₀ (2 + 5 * Real.cos θ)) MeasureTheory.volume a b := by
  apply MeasureTheory.IntegrableOn.intervalIntegrable
  refine MeasureTheory.IntegrableOn.of_bound isCompact_uIcc.measure_lt_top ?_
    (Real.log 2 + circleA N T₀ + circleB N T₀ + circleC N T₀ + (7/2) * circleP N T₀
      + (Real.log 2 + circleA N T₀) + (Real.log 2 + Real.log 2)) ?_
  · exact ((measurable_circUB N T₀).comp
      (by fun_prop : Measurable fun θ : ℝ => 2 + 5 * Real.cos θ)).aestronglyMeasurable
  · filter_upwards [MeasureTheory.ae_restrict_mem measurableSet_uIcc] with θ _
    have hc : Real.cos θ ≤ 1 := Real.cos_le_one θ
    have hc' : -1 ≤ Real.cos θ := Real.neg_one_le_cos θ
    rw [Real.norm_of_nonneg (circUB_nonneg (N := N) T₀ _)]
    unfold circUB
    split_ifs with h1 h2 h3 h4 h5
    · have a1 := circleA_nonneg N T₀; have a2 := circleB_nonneg N T₀
      have a3 := circleC_nonneg N T₀
      have a4 := mul_nonneg (by norm_num : (0:ℝ) ≤ 7/2) (circleP_nonneg N T₀)
      have a5 := circleA_nonneg N T₀
      linarith [log_two_nonneg]
    · have a1 := log_two_nonneg
      have a2 := circleB_nonneg N T₀
      have a3 := circleC_nonneg N T₀
      have a4 := mul_nonneg (by norm_num : (0:ℝ) ≤ 7/2) (circleP_nonneg N T₀)
      have a5 := circleA_nonneg N T₀
      linarith
    · have a1 := log_two_nonneg
      have a2 := circleA_nonneg N T₀
      have a3 := circleC_nonneg N T₀
      have a4 := mul_nonneg (by norm_num : (0:ℝ) ≤ 7/2) (circleP_nonneg N T₀)
      have a5 := circleA_nonneg N T₀
      linarith
    · have a1 := log_two_nonneg
      have a2 := circleA_nonneg N T₀
      have a3 := circleB_nonneg N T₀
      have a4 := mul_nonneg (by norm_num : (0:ℝ) ≤ 7/2) (circleP_nonneg N T₀)
      have a5 := circleA_nonneg N T₀
      linarith
    · have hcoef : 1/2 - (2 + 5 * Real.cos θ) ≤ 7/2 := by linarith
      have hP := circleP_nonneg N T₀
      have a1 := log_two_nonneg
      have a2 := circleA_nonneg N T₀
      have a3 := circleB_nonneg N T₀
      have a4 := circleC_nonneg N T₀
      have a5 := mul_le_mul_of_nonneg_right hcoef hP
      linarith
    · have hcoef : 1/2 - (2 + 5 * Real.cos θ) ≤ 7/2 := by linarith
      have hP := circleP_nonneg N T₀
      have a1 := log_two_nonneg
      have a2 := circleA_nonneg N T₀
      have a3 := circleB_nonneg N T₀
      have a4 := circleC_nonneg N T₀
      have a5 := mul_le_mul_of_nonneg_right hcoef hP
      linarith

lemma circUB_eq_log_two {N : ℕ} (T₀ σ : ℝ) (h : 2 ≤ σ) : circUB N T₀ σ = Real.log 2 := by
  unfold circUB; rw [if_pos h]

lemma circUB_eq_A {N : ℕ} (T₀ σ : ℝ) (h1 : ¬ 2 ≤ σ) (h2 : 1 ≤ σ) :
    circUB N T₀ σ = circleA N T₀ := by
  unfold circUB; rw [if_neg h1, if_pos h2]

lemma circUB_eq_B {N : ℕ} (T₀ σ : ℝ) (h1 : ¬ 2 ≤ σ) (h2 : ¬ 1 ≤ σ) (h3 : 1/2 ≤ σ) :
    circUB N T₀ σ = circleB N T₀ := by
  unfold circUB; rw [if_neg h1, if_neg h2, if_pos h3]

lemma circUB_eq_C {N : ℕ} (T₀ σ : ℝ) (h1 : ¬ 2 ≤ σ) (h2 : ¬ 1 ≤ σ) (h3 : ¬ 1/2 ≤ σ)
    (h4 : 0 ≤ σ) : circUB N T₀ σ = circleC N T₀ := by
  unfold circUB; rw [if_neg h1, if_neg h2, if_neg h3, if_pos h4]

lemma circUB_eq_D1 {N : ℕ} (T₀ σ : ℝ) (h1 : ¬ 2 ≤ σ) (h2 : ¬ 1 ≤ σ) (h3 : ¬ 1/2 ≤ σ)
    (h4 : ¬ 0 ≤ σ) (h5 : -1 ≤ σ) :
    circUB N T₀ σ = (1/2 - σ) * circleP N T₀ + (Real.log 2 + circleA N T₀) := by
  unfold circUB; rw [if_neg h1, if_neg h2, if_neg h3, if_neg h4, if_pos h5]

lemma circUB_eq_D2 {N : ℕ} (T₀ σ : ℝ) (h1 : ¬ 2 ≤ σ) (h2 : ¬ 1 ≤ σ) (h3 : ¬ 1/2 ≤ σ)
    (h4 : ¬ 0 ≤ σ) (h5 : ¬ -1 ≤ σ) :
    circUB N T₀ σ = (1/2 - σ) * circleP N T₀ + (Real.log 2 + Real.log 2) := by
  unfold circUB; rw [if_neg h1, if_neg h2, if_neg h3, if_neg h4, if_neg h5]


/-! ## Numerical bounds for the arc decomposition -/

private lemma cos_eight_sevenths_ge : (2:ℝ)/5 ≤ Real.cos (8/7) := by
  have h1 : 0 ≤ Real.pi/2 - 8/7 := by linarith [Real.pi_gt_d4]
  have h2 : Real.pi/2 - 8/7 ≤ 0.428 := by linarith [Real.pi_lt_d4]
  have h3 : (0.4278:ℝ) ≤ Real.pi/2 - 8/7 := by linarith [Real.pi_gt_d4]
  have hcos : Real.cos (8/7) = Real.sin (Real.pi/2 - 8/7) := by
    have h : Real.cos (8/7) = Real.cos (Real.pi/2 - (Real.pi/2 - 8/7)) := by
      congr 1; ring
    rw [h, Real.cos_pi_div_two_sub]
  rw [hcos]
  have hsin := Real.sin_ge_sub_cube h1
  have hx3 : (Real.pi/2 - 8/7)^3 ≤ (0.428:ℝ)^3 := pow_le_pow_left₀ h1 h2 3
  have h4a : Real.pi/2 - 8/7 - (Real.pi/2 - 8/7)^3/6 ≥ (0.4278:ℝ) - (0.428:ℝ)^3/6 := by
    linarith [h3, hx3]
  have hnum : (2:ℝ)/5 ≤ (0.4278:ℝ) - (0.428:ℝ)^3/6 := by norm_num
  linarith [hsin, h4a, hnum]

private lemma arccos_two_fifths_ge : (8:ℝ)/7 ≤ Real.arccos ((2:ℝ)/5) := by
  have h := Real.arccos_le_arccos cos_eight_sevenths_ge
  rwa [Real.arccos_cos (x := 8/7) (by norm_num) (by linarith [Real.pi_gt_three])] at h

private lemma sqrt21_le : Real.sqrt 21 ≤ 4.5826 := by
  have h : Real.sqrt 21 < 4.5826 :=
    (Real.sqrt_lt' (x := 21) (y := 4.5826) (by norm_num)).mpr (by norm_num)
  linarith

private lemma inv_sqrt24_le : (1:ℝ) / Real.sqrt 24 ≤ 21/100 := by
  rw [div_le_iff₀ (Real.sqrt_pos_of_pos (by norm_num : (0:ℝ) < 24))]
  have h : (100:ℝ)/21 ≤ Real.sqrt 24 :=
    (Real.le_sqrt (by norm_num) (by norm_num)).mpr (by norm_num)
  nlinarith [h]

private lemma arccos_three_fifths_le_one : Real.arccos ((3:ℝ)/5) ≤ 1 := by
  have hcos1 : Real.cos 1 ≤ (3:ℝ)/5 := by
    have h : Real.cos 1 = Real.sin (Real.pi/2 - 1) := by
      have h' : Real.cos 1 = Real.cos (Real.pi/2 - (Real.pi/2 - 1)) := by congr 1; ring
      rw [h', Real.cos_pi_div_two_sub]
    rw [h]
    calc Real.sin (Real.pi/2 - 1) ≤ Real.pi/2 - 1 := Real.sin_le (by linarith [Real.pi_gt_d4])
      _ ≤ 3/5 := by linarith [Real.pi_lt_d4]
  have h1 : Real.arccos ((3:ℝ)/5) ≤ Real.arccos (Real.cos 1) := Real.arccos_le_arccos hcos1
  rwa [Real.arccos_cos (x := 1) (by norm_num) (by linarith [Real.pi_gt_three])] at h1

/-! ## The integral bound -/

lemma integral_circUB_le {N : ℕ} [NeZero N] (T₀ : ℝ) :
    (∫ θ in (0:ℝ)..π, circUB N T₀ (2 + 5*Real.cos θ)) ≤
      (15708/10000) * Real.log 2 + (21/100) * circleA N T₀ + (21/200) * circleB N T₀
        + (11/100) * circleC N T₀ + (287/100) * circleP N T₀
        + (1/4) * (Real.log 2 + circleA N T₀) + (Real.log 2 + Real.log 2) := by
  set θA := Real.arccos (-(1:ℝ)/5) with hθA
  set θB := Real.arccos (-(3:ℝ)/10) with hθB
  set θC := Real.arccos (-(2:ℝ)/5) with hθC
  set θE := Real.arccos (-(3:ℝ)/5) with hθE
  have hcA : Real.cos θA = -(1:ℝ)/5 := by
    rw [hθA]; exact Real.cos_arccos (by norm_num) (by norm_num)
  have hcB : Real.cos θB = -(3:ℝ)/10 := by
    rw [hθB]; exact Real.cos_arccos (by norm_num) (by norm_num)
  have hcC : Real.cos θC = -(2:ℝ)/5 := by
    rw [hθC]; exact Real.cos_arccos (by norm_num) (by norm_num)
  have hcE : Real.cos θE = -(3:ℝ)/5 := by
    rw [hθE]; exact Real.cos_arccos (by norm_num) (by norm_num)
  have hnA : 0 ≤ θA := by rw [hθA]; exact Real.arccos_nonneg _
  have hnB : 0 ≤ θB := by rw [hθB]; exact Real.arccos_nonneg _
  have hnC : 0 ≤ θC := by rw [hθC]; exact Real.arccos_nonneg _
  have hnE : 0 ≤ θE := by rw [hθE]; exact Real.arccos_nonneg _
  have hpA : θA ≤ Real.pi := by rw [hθA]; exact Real.arccos_le_pi _
  have hpB : θB ≤ Real.pi := by rw [hθB]; exact Real.arccos_le_pi _
  have hpC : θC ≤ Real.pi := by rw [hθC]; exact Real.arccos_le_pi _
  have hpE : θE ≤ Real.pi := by rw [hθE]; exact Real.arccos_le_pi _
  have hpi2nn : 0 ≤ Real.pi/2 := by positivity
  have hpi2A : Real.pi/2 ≤ θA := by
    rw [hθA, ← Real.arccos_zero]
    exact Real.arccos_le_arccos (by norm_num)
  have hAB : θA ≤ θB := by
    rw [hθA, hθB]; exact Real.arccos_le_arccos (by norm_num : -(3:ℝ)/10 ≤ -(1:ℝ)/5)
  have hBC : θB ≤ θC := by
    rw [hθB, hθC]; exact Real.arccos_le_arccos (by norm_num : -(2:ℝ)/5 ≤ -(3:ℝ)/10)
  have hCE : θC ≤ θE := by
    rw [hθC, hθE]; exact Real.arccos_le_arccos (by norm_num : -(3:ℝ)/5 ≤ -(2:ℝ)/5)
  have hf : ∀ a b : ℝ,
      IntervalIntegrable (fun θ : ℝ => circUB N T₀ (2 + 5*Real.cos θ)) MeasureTheory.volume a b :=
    fun a b => intervalIntegrable_circUB_cos N T₀ a b
  have hg : ∀ a b : ℝ,
      IntervalIntegrable (fun θ : ℝ => (1/2 - (2 + 5*Real.cos θ))) MeasureTheory.volume a b :=
    fun a b => (by fun_prop : Continuous fun θ : ℝ => (1/2 - (2 + 5*Real.cos θ))).intervalIntegrable a b
  -- arc 1
  have e1 : (∫ θ in (0:ℝ)..(Real.pi/2), circUB N T₀ (2 + 5*Real.cos θ))
      = (Real.pi/2) * Real.log 2 := by
    trans (∫ θ in (0:ℝ)..(Real.pi/2), Real.log 2)
    · apply intervalIntegral.integral_congr_ae
      filter_upwards with θ hθ
      rw [Set.uIoc_of_le hpi2nn, Set.mem_Ioc] at hθ
      have hcos : 0 ≤ Real.cos θ :=
        Real.cos_nonneg_of_mem_Icc ⟨by linarith [hθ.1], by linarith [hθ.2, Real.pi_pos]⟩
      exact circUB_eq_log_two T₀ _ (by linarith)
    · rw [intervalIntegral.integral_const, smul_eq_mul]
      ring
  -- arc 2
  have e2 : (∫ θ in (Real.pi/2)..θA, circUB N T₀ (2 + 5*Real.cos θ))
      = (θA - Real.pi/2) * circleA N T₀ := by
    trans (∫ θ in (Real.pi/2)..θA, circleA N T₀)
    · apply intervalIntegral.integral_congr_ae
      filter_upwards with θ hθ
      rw [Set.uIoc_of_le hpi2A, Set.mem_Ioc] at hθ
      have hθ0 : 0 ≤ θ := le_of_lt (lt_trans (by linarith [Real.pi_pos] : (0:ℝ) < Real.pi/2) hθ.1)
      have hθπ : θ ≤ Real.pi := le_trans hθ.2 hpA
      have hlt : Real.cos θ < 0 := by
        have hc := Real.cos_lt_cos_of_nonneg_of_le_pi hpi2nn hθπ hθ.1
        rwa [Real.cos_pi_div_two] at hc
      have hge : -(1:ℝ)/5 ≤ Real.cos θ := by
        have hc := Real.antitoneOn_cos ⟨hθ0, hθπ⟩ ⟨hnA, hpA⟩ hθ.2
        rwa [hcA] at hc
      exact circUB_eq_A T₀ _ (by linarith) (by linarith)
    · rw [intervalIntegral.integral_const, smul_eq_mul]
  -- arc 3
  have e3 : (∫ θ in θA..θB, circUB N T₀ (2 + 5*Real.cos θ))
      = (θB - θA) * circleB N T₀ := by
    trans (∫ θ in θA..θB, circleB N T₀)
    · apply intervalIntegral.integral_congr_ae
      filter_upwards with θ hθ
      rw [Set.uIoc_of_le hAB, Set.mem_Ioc] at hθ
      have hθ0 : 0 ≤ θ := le_trans hnA hθ.1.le
      have hθπ : θ ≤ Real.pi := le_trans hθ.2 hpB
      have hlt : Real.cos θ < -(1:ℝ)/5 := by
        have hc := Real.cos_lt_cos_of_nonneg_of_le_pi hnA hθπ hθ.1
        rwa [hcA] at hc
      have hge : -(3:ℝ)/10 ≤ Real.cos θ := by
        have hc := Real.antitoneOn_cos ⟨hθ0, hθπ⟩ ⟨hnB, hpB⟩ hθ.2
        rwa [hcB] at hc
      exact circUB_eq_B T₀ _ (by linarith) (by linarith) (by linarith)
    · rw [intervalIntegral.integral_const, smul_eq_mul]
  -- arc 4
  have e4 : (∫ θ in θB..θC, circUB N T₀ (2 + 5*Real.cos θ))
      = (θC - θB) * circleC N T₀ := by
    trans (∫ θ in θB..θC, circleC N T₀)
    · apply intervalIntegral.integral_congr_ae
      filter_upwards with θ hθ
      rw [Set.uIoc_of_le hBC, Set.mem_Ioc] at hθ
      have hθ0 : 0 ≤ θ := le_trans hnB hθ.1.le
      have hθπ : θ ≤ Real.pi := le_trans hθ.2 hpC
      have hlt : Real.cos θ < -(3:ℝ)/10 := by
        have hc := Real.cos_lt_cos_of_nonneg_of_le_pi hnB hθπ hθ.1
        rwa [hcB] at hc
      have hge : -(2:ℝ)/5 ≤ Real.cos θ := by
        have hc := Real.antitoneOn_cos ⟨hθ0, hθπ⟩ ⟨hnC, hpC⟩ hθ.2
        rwa [hcC] at hc
      exact circUB_eq_C T₀ _ (by linarith) (by linarith) (by linarith) (by linarith)
    · rw [intervalIntegral.integral_const, smul_eq_mul]
  -- arcs 5 and 6
  have e5 : (∫ θ in θC..θE, circUB N T₀ (2 + 5*Real.cos θ))
      = circleP N T₀ * (∫ θ in θC..θE, (1/2 - (2 + 5*Real.cos θ)))
        + (θE - θC) * (Real.log 2 + circleA N T₀) := by
    trans (∫ θ in θC..θE,
        ((1/2 - (2 + 5*Real.cos θ)) * circleP N T₀ + (Real.log 2 + circleA N T₀)))
    · apply intervalIntegral.integral_congr_ae
      filter_upwards with θ hθ
      rw [Set.uIoc_of_le hCE, Set.mem_Ioc] at hθ
      have hθ0 : 0 ≤ θ := le_trans hnC hθ.1.le
      have hθπ : θ ≤ Real.pi := le_trans hθ.2 hpE
      have hlt : Real.cos θ < -(2:ℝ)/5 := by
        have hc := Real.cos_lt_cos_of_nonneg_of_le_pi hnC hθπ hθ.1
        rwa [hcC] at hc
      have hge : -(3:ℝ)/5 ≤ Real.cos θ := by
        have hc := Real.antitoneOn_cos ⟨hθ0, hθπ⟩ ⟨hnE, hpE⟩ hθ.2
        rwa [hcE] at hc
      exact circUB_eq_D1 T₀ _ (by linarith) (by linarith) (by linarith) (by linarith) (by linarith)
    · rw [intervalIntegral.integral_add ((hg θC θE).mul_const (circleP N T₀))
        intervalIntegrable_const, intervalIntegral.integral_mul_const,
        intervalIntegral.integral_const, smul_eq_mul]
      ring
  have e6 : (∫ θ in θE..Real.pi, circUB N T₀ (2 + 5*Real.cos θ))
      = circleP N T₀ * (∫ θ in θE..Real.pi, (1/2 - (2 + 5*Real.cos θ)))
        + (Real.pi - θE) * (Real.log 2 + Real.log 2) := by
    trans (∫ θ in θE..Real.pi,
        ((1/2 - (2 + 5*Real.cos θ)) * circleP N T₀ + (Real.log 2 + Real.log 2)))
    · apply intervalIntegral.integral_congr_ae
      filter_upwards with θ hθ
      rw [Set.uIoc_of_le hpE, Set.mem_Ioc] at hθ
      have hθ0 : 0 ≤ θ := le_trans hnE hθ.1.le
      have hlt : Real.cos θ < -(3:ℝ)/5 := by
        have hc := Real.cos_lt_cos_of_nonneg_of_le_pi hnE hθ.2 hθ.1
        rwa [hcE] at hc
      exact circUB_eq_D2 T₀ _ (by linarith) (by linarith) (by linarith) (by linarith) (by linarith)
    · rw [intervalIntegral.integral_add ((hg θE Real.pi).mul_const (circleP N T₀))
        intervalIntegrable_const, intervalIntegral.integral_mul_const,
        intervalIntegral.integral_const, smul_eq_mul]
      ring
  -- bound on the P-integral
  have hX : (∫ θ in θC..Real.pi, (1/2 - (2 + 5*Real.cos θ))) ≤ 287/100 := by
    rw [hθC, integral_leftHalf]
    have h1 := sqrt21_le
    have h2 := arccos_two_fifths_ge
    linarith
  have hδ1 : θE - θC ≤ 1/4 := by
    rw [hθE, hθC]
    have h := arccos_sub_arccos_le (a := -(3:ℝ)/5) (b := -(2:ℝ)/5)
      (by norm_num) (by norm_num) (by norm_num)
    have h2 : Real.sqrt (1 - (-(3:ℝ)/5)^2) = 4/5 := by
      rw [show (1:ℝ) - (-(3:ℝ)/5)^2 = (4/5)^2 by norm_num, Real.sqrt_sq (by norm_num)]
    rw [h2] at h
    have h3 : ((-(2:ℝ)/5) - (-(3:ℝ)/5)) / (4/5) = 1/4 := by norm_num
    rw [h3] at h
    exact h
  have hδ2 : Real.pi - θE ≤ 1 := by
    rw [hθE, show Real.arccos ((-3:ℝ)/5) = Real.pi - Real.arccos ((3:ℝ)/5) by
      rw [show ((-3:ℝ)/5) = -(3/5) by ring]; exact Real.arccos_neg (3/5)]
    linarith [arccos_three_fifths_le_one]
  have hpi2le : Real.pi/2 ≤ 15708/10000 := by
    have := Real.pi_lt_d4
    linarith
  have hsub : θA - Real.pi/2 ≤ 21/100 := by
    rw [hθA, ← Real.arccos_zero]
    have h := arccos_sub_arccos_le (a := -(1:ℝ)/5) (b := 0) (by norm_num) (by norm_num) (by norm_num)
    have h2 : Real.sqrt (1 - (-(1:ℝ)/5)^2) = Real.sqrt 24 / 5 := by
      rw [show (1:ℝ) - (-(1:ℝ)/5)^2 = 24/25 by norm_num, Real.sqrt_div (by norm_num),
        show (25:ℝ) = 5^2 by norm_num, Real.sqrt_sq (by norm_num)]
    rw [h2] at h
    have h3 : ((0:ℝ) - (-(1:ℝ)/5)) / (Real.sqrt 24 / 5) = 1 / Real.sqrt 24 := by
      have h24 : Real.sqrt 24 ≠ 0 := (Real.sqrt_pos_of_pos (by norm_num)).ne'
      field_simp
      ring
    rw [h3] at h
    exact h.trans inv_sqrt24_le
  -- assemble
  have hsplit1 : (∫ θ in (0:ℝ)..Real.pi, circUB N T₀ (2 + 5*Real.cos θ))
      = (∫ θ in (0:ℝ)..(Real.pi/2), circUB N T₀ (2 + 5*Real.cos θ))
        + (∫ θ in (Real.pi/2)..θA, circUB N T₀ (2 + 5*Real.cos θ))
        + (∫ θ in θA..θB, circUB N T₀ (2 + 5*Real.cos θ))
        + (∫ θ in θB..θC, circUB N T₀ (2 + 5*Real.cos θ))
        + (∫ θ in θC..Real.pi, circUB N T₀ (2 + 5*Real.cos θ)) := by
    have a0 := intervalIntegral.integral_add_adjacent_intervals (hf 0 (Real.pi/2)) (hf (Real.pi/2) Real.pi)
    have a1 := intervalIntegral.integral_add_adjacent_intervals (hf (Real.pi/2) θA) (hf θA Real.pi)
    have a2 := intervalIntegral.integral_add_adjacent_intervals (hf θA θB) (hf θB Real.pi)
    have a3 := intervalIntegral.integral_add_adjacent_intervals (hf θB θC) (hf θC Real.pi)
    linarith
  have h56 : (∫ θ in θC..Real.pi, circUB N T₀ (2 + 5*Real.cos θ))
      ≤ (287/100) * circleP N T₀ + (1/4) * (Real.log 2 + circleA N T₀)
        + 1 * (Real.log 2 + Real.log 2) := by
    rw [← intervalIntegral.integral_add_adjacent_intervals (hf θC θE) (hf θE Real.pi), e5, e6]
    have hP := circleP_nonneg N T₀
    have hA := circleA_nonneg N T₀
    have hlog := log_two_nonneg
    have hX' : (∫ θ in θC..θE, (1/2 - (2 + 5*Real.cos θ)))
        + (∫ θ in θE..Real.pi, (1/2 - (2 + 5*Real.cos θ))) ≤ 287/100 := by
      rw [intervalIntegral.integral_add_adjacent_intervals (hg θC θE) (hg θE Real.pi)]
      exact hX
    nlinarith [hX', hδ1, hδ2, hP, hlog, hA,
      mul_le_mul_of_nonneg_left hδ1 (by linarith : (0:ℝ) ≤ Real.log 2 + circleA N T₀),
      mul_le_mul_of_nonneg_left hδ2 (by linarith : (0:ℝ) ≤ Real.log 2 + Real.log 2)]
  have hrest : (∫ θ in (0:ℝ)..(Real.pi/2), circUB N T₀ (2 + 5*Real.cos θ))
        + (∫ θ in (Real.pi/2)..θA, circUB N T₀ (2 + 5*Real.cos θ))
        + (∫ θ in θA..θB, circUB N T₀ (2 + 5*Real.cos θ))
        + (∫ θ in θB..θC, circUB N T₀ (2 + 5*Real.cos θ))
      ≤ (15708/10000) * Real.log 2 + (21/100) * circleA N T₀ + (21/200) * circleB N T₀
        + (11/100) * circleC N T₀ := by
    rw [e1, e2, e3, e4]
    have hlog := log_two_nonneg
    have hA := circleA_nonneg N T₀
    have hB := circleB_nonneg N T₀
    have hC := circleC_nonneg N T₀
    have h1 := mul_le_mul_of_nonneg_right hpi2le hlog
    have h2 := mul_le_mul_of_nonneg_right hsub hA
    have h3 : θB - θA ≤ 21/200 := by rw [hθB, hθA]; exact arccos_neg_three_tenths_sub_arccos_neg_one_fifth_le
    have h4 : θC - θB ≤ 11/100 := by rw [hθC, hθB]; exact arccos_neg_two_fifths_sub_arccos_neg_three_tenths_le
    have h5 := mul_le_mul_of_nonneg_right h3 hB
    have h6 := mul_le_mul_of_nonneg_right h4 hC
    linarith
  linarith [hsplit1, hrest, h56]

/-! ## The circle average of `circUB` -/

lemma circleIntegrable_circUB {N : ℕ} [NeZero N] (T₀ : ℝ) (c : ℂ) (hc : c.re = 2) :
    CircleIntegrable (fun z : ℂ => circUB N T₀ z.re) c 5 := by
  rw [CircleIntegrable]
  have heq : (fun θ : ℝ => (fun z : ℂ => circUB N T₀ z.re) (circleMap c (5:ℝ) θ))
      = (fun θ : ℝ => circUB N T₀ (2 + 5 * Real.cos θ)) := by
    funext θ
    show circUB N T₀ (circleMap c (5:ℝ) θ).re = circUB N T₀ (2 + 5 * Real.cos θ)
    rw [circleMap_re, hc]
  rw [heq]
  exact intervalIntegrable_circUB_cos N T₀ 0 (2 * Real.pi)

lemma circleAverage_circUB {N : ℕ} [NeZero N] (T₀ : ℝ) (c : ℂ) (hc : c.re = 2) :
    Real.circleAverage (fun z : ℂ => circUB N T₀ z.re) c 5
      = (1/Real.pi) * ∫ θ in (0:ℝ)..Real.pi, circUB N T₀ (2 + 5 * Real.cos θ) := by
  rw [Real.circleAverage_def]
  have heq : (fun θ : ℝ => (fun z : ℂ => circUB N T₀ z.re) (circleMap c (5:ℝ) θ))
      = (fun θ : ℝ => circUB N T₀ (2 + 5 * Real.cos θ)) := by
    funext θ
    show circUB N T₀ (circleMap c (5:ℝ) θ).re = circUB N T₀ (2 + 5 * Real.cos θ)
    rw [circleMap_re, hc]
  rw [heq, integral_cos_symm (fun x : ℝ => circUB N T₀ (2 + 5 * x))
    (intervalIntegrable_circUB_cos N T₀ 0 (2*Real.pi)), smul_eq_mul]
  have hpi : Real.pi ≠ 0 := Real.pi_ne_zero
  field_simp

/-! ## The numerical bookkeeping -/

private lemma log_twenty_sevenths_le : Real.log (20/7) ≤ 1.06 := by
  rw [Real.log_le_iff_le_exp (by norm_num)]
  calc (20:ℝ)/7 ≤ 2.7182818283 * 1.06 := by norm_num
    _ ≤ Real.exp 1 * Real.exp (0.06) := by
        have h := Real.add_one_le_exp 0.06
        have h2 : (1.06:ℝ) ≤ Real.exp 0.06 := by linarith
        exact mul_le_mul (le_of_lt Real.exp_one_gt_d9) h2 (by norm_num) (Real.exp_pos 1).le
    _ = Real.exp 1.06 := by rw [← Real.exp_add]; norm_num

private lemma one_div_pi_le : 1/Real.pi ≤ 31833/100000 := by
  rw [div_le_iff₀ Real.pi_pos]
  nlinarith [Real.pi_gt_d4]

private lemma final_arith {X Y A B C P : ℝ} (hX0 : 0 ≤ X) (hY0 : 0 ≤ Y)
    (hA0 : 0 ≤ A) (hB0 : 0 ≤ B) (hC0 : 0 ≤ C)
    (hP0 : 0 ≤ P) (hA : A ≤ (X + Y)/20 + 2.4) (hB : B ≤ X + Y + 12/5)
    (hC : C ≤ 3*X/2 + 2*Y + 67/5) (hP : P ≤ X + Y + 9/8) :
    (1/Real.pi) * ((15708/10000)*Real.log 2 + (21/100)*A + (21/200)*B + (11/100)*C
        + (287/100)*P + (1/4)*(Real.log 2 + A) + (Real.log 2 + Real.log 2)) + 1.06
      ≤ Real.log 2 * (3/2*(X+Y) + 6) := by
  have hpi := one_div_pi_le
  have hlog1 : (0.6931 : ℝ) ≤ Real.log 2 :=
    le_of_lt (lt_trans (by norm_num : (0.6931:ℝ) < 0.6931471803) Real.log_two_gt_d9)
  have hlog2 : Real.log 2 ≤ 0.6932 :=
    le_of_lt (lt_trans Real.log_two_lt_d9 (by norm_num : (0.6931471808:ℝ) < 0.6932))
  have hlog0 : (0:ℝ) ≤ Real.log 2 := by linarith
  have hS0 : 0 ≤ (15708/10000)*Real.log 2 + (21/100)*A + (21/200)*B + (11/100)*C
        + (287/100)*P + (1/4)*(Real.log 2 + A) + (Real.log 2 + Real.log 2) := by
    linarith
  have hS : (15708/10000)*Real.log 2 + (21/100)*A + (21/200)*B + (11/100)*C
        + (287/100)*P + (1/4)*(Real.log 2 + A) + (Real.log 2 + Real.log 2) ≤
      15708/10000*0.6932 + (21/100)*((X+Y)/20+2.4) + (21/200)*(X+Y+12/5)
        + (11/100)*(3*X/2+2*Y+67/5) + (287/100)*(X+Y+9/8)
        + (1/4)*(0.6932 + ((X+Y)/20+2.4)) + (0.6932+0.6932) := by
    nlinarith [hA, hB, hC, hP, hlog2, hlog0, hA0, hB0, hC0, hP0]
  have hkey : (31833/100000) * (15708/10000*0.6932 + (21/100)*((X+Y)/20+2.4)
      + (21/200)*(X+Y+12/5) + (11/100)*(3*X/2+2*Y+67/5) + (287/100)*(X+Y+9/8)
      + (1/4)*(0.6932+((X+Y)/20+2.4)) + (0.6932+0.6932)) + 1.06
      ≤ 0.6931*(3/2*(X+Y)+6) := by
    nlinarith [hX0, hY0]
  have hstep : (1/Real.pi) * ((15708/10000)*Real.log 2 + (21/100)*A + (21/200)*B
        + (11/100)*C + (287/100)*P + (1/4)*(Real.log 2 + A) + (Real.log 2 + Real.log 2))
      ≤ (31833/100000) * (15708/10000*0.6932 + (21/100)*((X+Y)/20+2.4)
        + (21/200)*(X+Y+12/5) + (11/100)*(3*X/2+2*Y+67/5) + (287/100)*(X+Y+9/8)
        + (1/4)*(0.6932+((X+Y)/20+2.4)) + (0.6932+0.6932)) :=
    mul_le_mul hpi hS hS0 (by norm_num)
  have htarget : 0.6931*(3/2*(X+Y)+6) ≤ Real.log 2 * (3/2*(X+Y)+6) :=
    mul_le_mul_of_nonneg_right hlog1 (by nlinarith [hX0, hY0])
  linarith [hstep, hkey, htarget]

private lemma log_twenty_le_three : Real.log 20 ≤ 3 := by
  rw [Real.log_le_iff_le_exp (by norm_num)]
  have h := Real.sum_le_exp_of_nonneg (by norm_num : (0:ℝ) ≤ 3) 10
  have h2 : (20:ℝ) ≤ ∑ i ∈ Finset.range 10, (3:ℝ)^i / (i.factorial : ℝ) := by
    norm_num [Finset.sum_range_succ]
  linarith

/-- **The zero count of the completed Dirichlet L-function in a disk of radius `5/2`.** -/
theorem diskZeroCount_two_half {N : ℕ} [NeZero N] (χ : DirichletCharacter ℂ N)
    (hχ : χ ≠ 1) (hχprim : χ.IsPrimitive) (T₀ : ℝ) :
    (∑ᶠ u : ℂ, (((MeromorphicOn.divisor (DirichletCharacter.completedLFunction χ)
        (Metric.closedBall ((2 : ℂ) + Complex.I * (T₀ : ℂ)) (5 / 2))) u : ℤ) : ℝ))
      ≤ (3 / 2) * (Real.log (N : ℝ) + Real.log (2 + |T₀| + 2)) + 6 := by
  set c : ℂ := (2 : ℂ) + Complex.I * (T₀ : ℂ) with hc
  have hcre : c.re = 2 := by rw [hc]; simp
  have hcim : c.im = T₀ := by rw [hc]; simp
  set X := Real.log (N:ℝ) with hXdef
  set Y := Real.log (|T₀| + 4) with hYdef
  have hX0 : 0 ≤ X := by
    rw [hXdef]; exact Real.log_nonneg (by exact_mod_cast Nat.one_le_iff_ne_zero.mpr (NeZero.ne N))
  have hY0 : 0 ≤ Y := by rw [hYdef]; exact Real.log_nonneg (by linarith [abs_nonneg T₀])
  -- bounds on the constants
  have hBbound : circleB N T₀ ≤ X + Y + 12/5 := by
    have h := circleB_le N T₀
    rw [← hXdef, ← hYdef] at h; linarith
  have hCbound : circleC N T₀ ≤ 3*X/2 + 2*Y + 67/5 := by
    have h := circleC_le N T₀
    rw [← hXdef, ← hYdef] at h; linarith
  have hPbound : circleP N T₀ ≤ X + Y + 9/8 := by
    have h := circleP_le N T₀
    rw [← hXdef, ← hYdef] at h; linarith
  have hAbound : circleA N T₀ ≤ (X + Y)/20 + 2.4 := by
    have hlog7 := log_abs_add_seven_le T₀
    have h1 : circleA N T₀ ≤ Real.log (X + Y + 7) := by
      unfold circleA
      apply Real.log_le_log
      · have h1' : 0 ≤ Real.log (N:ℝ) := hX0
        have h2' : 0 ≤ Real.log (|T₀| + 7) := Real.log_nonneg (by linarith [abs_nonneg T₀])
        linarith
      · rw [hXdef, hYdef]
        linarith
    have hpos : 0 < (X + Y + 7)/20 := by linarith [hX0, hY0]
    have hsplit : Real.log (X + Y + 7) = Real.log ((X + Y + 7)/20) + Real.log 20 := by
      rw [← Real.log_mul (by positivity) (by norm_num : (20:ℝ) ≠ 0)]
      congr 1; ring
    have h2 : Real.log ((X + Y + 7)/20) ≤ (X + Y + 7)/20 - 1 :=
      Real.log_le_sub_one_of_pos hpos
    have h3 := log_twenty_le_three
    have h4 : Real.log (X + Y + 7) ≤ (X + Y + 7)/20 + 2 := by linarith
    linarith
  -- the circle average of `log ‖L‖` is bounded by the integral of `circUB`
  set Is := (1/Real.pi) * ∫ θ in (0:ℝ)..Real.pi, circUB N T₀ (2 + 5 * Real.cos θ) with hIs
  have hLavg : Real.circleAverage (fun z : ℂ => Real.log ‖LFunction χ z‖) c 5 ≤ Is := by
    by_cases hInt : CircleIntegrable (fun z : ℂ => Real.log ‖LFunction χ z‖) c 5
    · have hpoint : ∀ z ∈ Metric.sphere c |(5:ℝ)|,
          Real.log ‖LFunction χ z‖ ≤ circUB N T₀ z.re := by
        intro z hz
        have hdist : dist z c = 5 := by rw [Metric.mem_sphere] at hz; rw [hz]; norm_num
        have hnorm5 : ‖z - c‖ = 5 := by rw [dist_eq_norm] at hdist; exact hdist
        refine LFunction_log_le_circUB χ hχ hχprim T₀ ?_ ?_
        · have h1 : |(z - c).re| ≤ ‖z - c‖ := Complex.abs_re_le_norm _
          rw [Complex.sub_re, hnorm5] at h1
          have h2 := (abs_le.mp h1).1
          rw [hcre] at h2
          linarith
        · have h1 : |(z - c).im| ≤ ‖z - c‖ := Complex.abs_im_le_norm _
          rw [Complex.sub_im, hnorm5] at h1
          have h2 := abs_le.mp h1
          rw [hcim] at h2
          rw [abs_le]
          constructor
          · linarith [neg_le_abs T₀]
          · linarith [le_abs_self T₀]
      have hmono := Real.circleAverage_mono hInt (circleIntegrable_circUB (N := N) T₀ c hcre) hpoint
      rw [circleAverage_circUB (N := N) T₀ c hcre] at hmono
      rw [hIs]
      exact hmono
    · have hzero : Real.circleAverage (fun z : ℂ => Real.log ‖LFunction χ z‖) c 5 = 0 := by
        rw [Real.circleAverage_def, intervalIntegral.integral_undef hInt, smul_zero]
      rw [hzero, hIs]
      exact mul_nonneg (one_div_nonneg.mpr Real.pi_pos.le)
        (intervalIntegral.integral_nonneg_of_forall Real.pi_pos.le
          (fun θ => circUB_nonneg (N := N) T₀ _))
  -- the excess of `Λ` is bounded by that of `L`
  have hexcess : Real.circleAverage (fun z : ℂ => Real.log ‖completedLFunction χ z‖) c 5
      - Real.log ‖completedLFunction χ c‖
      ≤ Real.circleAverage (fun z : ℂ => Real.log ‖LFunction χ z‖) c 5
        - Real.log ‖LFunction χ c‖ := by
    rw [hc]
    exact circleExcess_le_L_excess χ hχ hχprim T₀
  have hΛc : completedLFunction χ c ≠ 0 := by
    intro h0
    have hz := zerosInStrip χ hχ hχprim c h0
    rw [hcre] at hz
    linarith [hz.2]
  -- Jensen
  have hjen := Commons.Analysis.Complex.sum_divisor_le_circleAvg (c := c) (r := (5:ℝ)/2) (R := (5:ℝ))
      (A := Real.circleAverage (fun z : ℂ => Real.log ‖LFunction χ z‖) c 5
        - Real.log ‖LFunction χ c‖ + Real.log ‖completedLFunction χ c‖)
      (f := DirichletCharacter.completedLFunction χ) (by norm_num) (by norm_num)
      (fun z _ => (differentiable_completedLFunction hχ).analyticAt z) hΛc
      (by linarith [hexcess])
  have hjen' : (((∑ᶠ u : ℂ, MeromorphicOn.divisor (DirichletCharacter.completedLFunction χ)
        (Metric.closedBall c (5/2)) u : ℤ)) : ℝ)
      ≤ (Real.circleAverage (fun z : ℂ => Real.log ‖LFunction χ z‖) c 5
          - Real.log ‖LFunction χ c‖) / Real.log 2 := by
    rw [abs_of_nonneg (show (0:ℝ) ≤ 5/2 by norm_num)] at hjen
    have h2 : (5:ℝ)/(5/2) = 2 := by norm_num
    rw [h2] at hjen
    have heq : (Real.circleAverage (fun z : ℂ => Real.log ‖LFunction χ z‖) c 5
          - Real.log ‖LFunction χ c‖ + Real.log ‖completedLFunction χ c‖
          - Real.log ‖completedLFunction χ c‖)
        = (Real.circleAverage (fun z : ℂ => Real.log ‖LFunction χ z‖) c 5
          - Real.log ‖LFunction χ c‖) := by ring
    rw [heq] at hjen
    exact hjen
  -- value of `L` at `c`
  have hcost : -Real.log ‖LFunction χ c‖ ≤ 1.06 := by
    have h := L_lower_re_two_explicit' χ hχ T₀
    have hlog : Real.log (7/20) ≤ Real.log ‖LFunction χ c‖ := by
      rw [hc]
      exact Real.log_le_log (by norm_num) h
    have h1 : Real.log ((7:ℝ)/20) = -Real.log (20/7) := by
      rw [show (7:ℝ)/20 = ((20:ℝ)/7)⁻¹ by norm_num, Real.log_inv]
    linarith [hlog, log_twenty_sevenths_le, h1]
  -- final numerical bound
  have hfinal : (Real.circleAverage (fun z : ℂ => Real.log ‖LFunction χ z‖) c 5
        - Real.log ‖LFunction χ c‖) / Real.log 2 ≤ (3/2)*(X+Y) + 6 := by
    have hlog2pos : 0 < Real.log 2 := Real.log_pos (by norm_num)
    rw [div_le_iff₀ hlog2pos]
    have hIle : Is ≤ (1/Real.pi) * ((15708/10000)*Real.log 2 + (21/100)*circleA N T₀
        + (21/200)*circleB N T₀ + (11/100)*circleC N T₀ + (287/100)*circleP N T₀
        + (1/4)*(Real.log 2 + circleA N T₀) + (Real.log 2 + Real.log 2)) := by
      rw [hIs]
      exact mul_le_mul_of_nonneg_left (integral_circUB_le (N := N) T₀) (by positivity)
    have harith := final_arith (X := X) (Y := Y) (A := circleA N T₀) (B := circleB N T₀)
      (C := circleC N T₀) (P := circleP N T₀) hX0 hY0 (circleA_nonneg N T₀)
      (circleB_nonneg N T₀) (circleC_nonneg N T₀) (circleP_nonneg N T₀)
      hAbound hBbound hCbound hPbound
    linarith [hLavg, hcost, hIle, harith]
  -- assemble
  have hconv : (∑ᶠ u : ℂ, (((MeromorphicOn.divisor (DirichletCharacter.completedLFunction χ)
        (Metric.closedBall c (5/2))) u : ℤ) : ℝ))
      = (((∑ᶠ u : ℂ, MeromorphicOn.divisor (DirichletCharacter.completedLFunction χ)
        (Metric.closedBall c (5/2)) u : ℤ)) : ℝ) := by
    have hfin : Function.HasFiniteSupport
        (fun u : ℂ => MeromorphicOn.divisor (DirichletCharacter.completedLFunction χ)
          (Metric.closedBall c (5/2)) u) :=
      (MeromorphicOn.divisor (DirichletCharacter.completedLFunction χ)
        (Metric.closedBall c (5/2))).finiteSupport (isCompact_closedBall c (5/2))
    exact (map_finsum (Int.castRingHom ℝ) hfin).symm
  rw [hconv]
  have hYeq : Real.log (2 + |T₀| + 2) = Y := by
    rw [hYdef]; congr 1; ring
  rw [hXdef, hYeq]
  exact hjen'.trans hfinal

end Commons.NumberTheory.DirichletCharacter
