import Mathlib
import Submission.Work.BMF.halasz_defs
import Submission.Work.BMF.halasz_basic
import Submission.Work.BMF.halasz_abel
import Submission.Work.BMF.halasz_Kbound
import Submission.Work.BMF.halasz_mertens_aux
import Submission.Work.BMF.halasz_plancherel_defs
import Submission.Work.BMF.integral_dirSum_sq
import Submission.Work.BMF.tendsto_integral_KfN
import Submission.Work.BMF.tendsto_integral_dirSum
import Submission.Work.BMF.HL.sum_log_div_prime_le
import Submission.Work.BMF.casdiv.wdb_support
import Submission.Work.BMF.casdiv.a_bound
import Submission.Work.BMF.halasz_intM
import Submission.Commons.NumberTheory.Mertens.primeRecips_sub_loglog_bound

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false

namespace Work.BMF

open scoped BigOperators MeasureTheory
open MeasureTheory intervalIntegral Finset

/-! ## Step 1: `‖Mf f x‖` against the logarithmic average of `‖Mf‖` -/

/-- `∫_1^x ‖Mf f t‖/t dt ≤ x ∫_1^x ‖Mf f t‖/t² dt` for `1 ≤ x`. -/
lemma integral_Mf_div_le (f : ℕ → ℂ) (hb : ∀ n, ‖f n‖ ≤ 1) {x : ℝ} (hx : 1 ≤ x) :
    (∫ t in (1 : ℝ)..x, ‖Mf f t‖ / t) ≤ x * ∫ t in (1 : ℝ)..x, ‖Mf f t‖ / t ^ 2 := by
  have hnorm : ∀ t : ℝ, 0 ≤ t → ‖Mf f t‖ ≤ t := fun t ht =>
    le_trans (Mf_norm_le f hb t) (Nat.floor_le ht)
  have hI1 : IntervalIntegrable (fun t : ℝ => ‖Mf f t‖ / t) volume 1 x := by
    refine IntervalIntegrable.mono_fun' (g := fun _ : ℝ => (1 : ℝ)) intervalIntegrable_const ?_ ?_
    · exact ((measurable_Mf f).norm.div measurable_id).aestronglyMeasurable
    · filter_upwards [MeasureTheory.self_mem_ae_restrict measurableSet_uIoc] with t ht
      have ht' : t ∈ Set.Ioc (1 : ℝ) x := by rwa [Set.uIoc_of_le hx] at ht
      have ht0 : (0 : ℝ) < t := lt_trans zero_lt_one ht'.1
      simp only [Real.norm_eq_abs, abs_of_nonneg (div_nonneg (norm_nonneg _) ht0.le)]
      rw [div_le_one ht0]
      exact hnorm t ht0.le
  have hinv : IntervalIntegrable (fun t : ℝ => t⁻¹) volume 1 x :=
    intervalIntegrable_inv (f := fun t : ℝ => t) (μ := volume) (a := 1) (b := x)
      (by intro t ht; rw [Set.uIcc_of_le hx] at ht
          exact ne_of_gt (lt_of_lt_of_le zero_lt_one ht.1)) continuousOn_id
  have hI2 : IntervalIntegrable (fun t : ℝ => ‖Mf f t‖ / t ^ 2) volume 1 x := by
    refine IntervalIntegrable.mono_fun' (g := fun t : ℝ => t⁻¹) hinv ?_ ?_
    · exact ((measurable_Mf f).norm.div (measurable_id.pow_const 2)).aestronglyMeasurable
    · filter_upwards [MeasureTheory.self_mem_ae_restrict measurableSet_uIoc] with t ht
      have ht' : t ∈ Set.Ioc (1 : ℝ) x := by rwa [Set.uIoc_of_le hx] at ht
      have ht0 : (0 : ℝ) < t := lt_trans zero_lt_one ht'.1
      have hle : ‖Mf f t‖ ≤ t := hnorm t ht0.le
      have h2 : 0 < t ^ 2 := by positivity
      rw [Real.norm_eq_abs, abs_of_nonneg (div_nonneg (norm_nonneg _) h2.le)]
      rw [div_le_iff₀ h2, inv_mul_eq_div, show t ^ 2 / t = t by field_simp]
      exact hle
  have hI3 : IntervalIntegrable (fun t : ℝ => x * (‖Mf f t‖ / t ^ 2)) volume 1 x := hI2.const_mul x
  have hmono : (∫ t in (1 : ℝ)..x, ‖Mf f t‖ / t) ≤ ∫ t in (1 : ℝ)..x, x * (‖Mf f t‖ / t ^ 2) := by
    refine intervalIntegral.integral_mono_on hx hI1 hI3 ?_
    intro t ht
    have ht0 : (0 : ℝ) < t := lt_of_lt_of_le zero_lt_one ht.1
    have hxx : t ≤ x := ht.2
    have hkey : (1:ℝ)/t ≤ x / t ^ 2 := by
      rw [div_le_div_iff₀ ht0 (by positivity)]; nlinarith
    calc ‖Mf f t‖ / t = ‖Mf f t‖ * (1 / t) := by ring
      _ ≤ ‖Mf f t‖ * (x / t ^ 2) := mul_le_mul_of_nonneg_left hkey (norm_nonneg _)
      _ = x * (‖Mf f t‖ / t ^ 2) := by ring
  rw [intervalIntegral.integral_const_mul] at hmono
  exact hmono

/-- **Abel + Halász `K`-bound.** -/
theorem Mf_bound_aux : ∃ C : ℝ, 0 < C ∧ ∀ (f : ℕ → ℂ), f 1 = 1 →
      (∀ m n : ℕ, m.Coprime n → f (m * n) = f m * f n) → (∀ n, ‖f n‖ ≤ 1) →
      ∀ x : ℝ, 3 ≤ x →
        ‖Mf f x‖ ≤ (2 * x / Real.log x) * (∫ t in (1 : ℝ)..x, ‖Mf f t‖ / t ^ 2)
          + C * x / Real.log x := by
  obtain ⟨C₁, hC₁, hK⟩ := halasz_Kbound
  refine ⟨C₁ + 1, by linarith, ?_⟩
  intro f hf1 hmul hb x hx
  have hx1 : (1:ℝ) ≤ x := by linarith
  have hx2 : (2:ℝ) ≤ x := by linarith
  have hlog : 0 < Real.log x := Real.log_pos (by linarith)
  have hKb := hK f hf1 hmul hb x hx2
  have habel := halasz_abel f x hx1
  have hint : ‖∫ t in (1:ℝ)..x, Mf f t / (t : ℂ)‖ ≤ ∫ t in (1:ℝ)..x, ‖Mf f t‖ / t := by
    refine le_trans (intervalIntegral.norm_integral_le_integral_norm hx1) ?_
    refine le_of_eq ?_
    apply intervalIntegral.integral_congr
    intro t ht
    change ‖Mf f t / (t:ℂ)‖ = ‖Mf f t‖ / t
    rw [Set.uIcc_of_le hx1] at ht
    have ht0 : (0:ℝ) < t := lt_of_lt_of_le zero_lt_one ht.1
    rw [norm_div, Complex.norm_real, Real.norm_eq_abs, abs_of_nonneg ht0.le]
  have hid : Mf f x * (Real.log x : ℂ) = Kf f x + ∫ t in (1:ℝ)..x, Mf f t / (t : ℂ) := by
    rw [← habel]; ring
  have hnorm : ‖Mf f x * (Real.log x : ℂ)‖ = ‖Mf f x‖ * Real.log x := by
    rw [norm_mul, Complex.norm_real, Real.norm_eq_abs, abs_of_nonneg hlog.le]
  have hkey : ‖Mf f x‖ * Real.log x ≤ 2 * (x * (∫ t in (1:ℝ)..x, ‖Mf f t‖ / t ^ 2)) + C₁ * x := by
    rw [← hnorm, hid]
    refine le_trans (norm_add_le _ _) ?_
    refine le_trans (add_le_add hKb hint) ?_
    have := integral_Mf_div_le f hb hx1
    linarith
  rw [show (2 * x / Real.log x) * (∫ t in (1:ℝ)..x, ‖Mf f t‖ / t ^ 2) + (C₁+1) * x / Real.log x
      = ((2 * (x * (∫ t in (1:ℝ)..x, ‖Mf f t‖ / t ^ 2)) + C₁ * x) + x) / Real.log x by
        field_simp; ring]
  rw [le_div_iff₀ hlog]
  linarith [hkey]




/-- `∫_1^x ‖Mf f t‖/t² dt ≥ 1/5` for `2 ≤ x`, `f 1 = 1` and `‖f n‖ ≤ 1`. -/
lemma A_ge (f : ℕ → ℂ) (hf1 : f 1 = 1) (hb : ∀ n, ‖f n‖ ≤ 1) {x : ℝ} (hx : 2 ≤ x) :
    (1:ℝ)/5 ≤ ∫ t in (1:ℝ)..x, ‖Mf f t‖ / t ^ 2 := by
  have h32 : (1:ℝ) ≤ 3/2 := by norm_num
  have hx' : (3/2:ℝ) ≤ x := by linarith
  have hI2 : IntervalIntegrable (fun t : ℝ => ‖Mf f t‖ / t ^ 2) volume 1 (3/2) :=
    intervalIntegrable_norm_Mf_div_sq f le_rfl h32
  have hI3 : IntervalIntegrable (fun t : ℝ => ‖Mf f t‖ / t ^ 2) volume (3/2) x :=
    intervalIntegrable_norm_Mf_div_sq f (by norm_num) hx'
  have hpt : ∀ t ∈ Set.Icc (1:ℝ) (3/2), (2:ℝ)/5 ≤ ‖Mf f t‖ / t ^ 2 := by
    intro t ht
    have hfloor : ⌊t⌋₊ = 1 := by
      rw [Nat.floor_eq_iff (by linarith [ht.1] : (0:ℝ) ≤ t)]
      exact ⟨by simpa using ht.1, by push_cast; linarith [ht.2]⟩
    have hMf : ‖Mf f t‖ = 1 := by
      unfold Mf; rw [hfloor]; simp [hf1]
    rw [hMf, le_div_iff₀ (by nlinarith [ht.1] : (0:ℝ) < t ^ 2)]
    nlinarith [ht.1, ht.2]
  have h1 : (∫ t in (1:ℝ)..(3/2), (2:ℝ)/5) ≤ ∫ t in (1:ℝ)..(3/2), ‖Mf f t‖ / t ^ 2 :=
    intervalIntegral.integral_mono_on h32 intervalIntegrable_const hI2 hpt
  have h2 : (∫ t in (1:ℝ)..(3/2), (2:ℝ)/5) = 1/5 := by
    rw [intervalIntegral.integral_const]; norm_num
  have hsplit : (∫ t in (1:ℝ)..x, ‖Mf f t‖ / t ^ 2)
      = (∫ t in (1:ℝ)..(3/2), ‖Mf f t‖ / t ^ 2)
        + ∫ t in (3/2:ℝ)..x, ‖Mf f t‖ / t ^ 2 :=
    (intervalIntegral.integral_add_adjacent_intervals hI2 hI3).symm
  have hnn : 0 ≤ ∫ t in (3/2:ℝ)..x, ‖Mf f t‖ / t ^ 2 :=
    intervalIntegral.integral_nonneg hx'
      (fun t ht => div_nonneg (norm_nonneg _) (by positivity))
  linarith [h1, h2, hsplit, hnn]

/-- **The "casdiv" bound of Ramaré's proof of Halász's theorem** (specialised to `r ≡ 1`). -/
theorem halasz_casdiv :
    ∃ C : ℝ, 0 < C ∧ ∀ (f : ℕ → ℂ), f 1 = 1 →
      (∀ m n : ℕ, m.Coprime n → f (m * n) = f m * f n) → (∀ n, ‖f n‖ ≤ 1) →
      ∀ x T : ℝ, 3 ≤ x → 2 ≤ T →
        ‖Work.BMF.Mf f x‖ ≤ C * (x / Real.log x) *
          ((∫ α in (1 / Real.log x)..1, Real.exp (Work.BMF.Wsup f x α (T + 1)) / α) +
           Real.exp (Work.BMF.Zrcp x) / Real.sqrt T +
           Real.exp (Work.BMF.Zrcp x) / Real.log x) := by
  obtain ⟨C_K, hC_K, hK⟩ := Mf_bound_aux
  obtain ⟨C_a, hC_a, ha⟩ := Work.BMF.casdiv.a_bound
  have hlog11 : 0 < Real.log 11 := Real.log_pos (by norm_num)
  refine ⟨max (11 * (Real.log 11)^2 / 3) ((2 + 5*C_K) * C_a) + 1, ?_, ?_⟩
  · have h1 : 0 < (11:ℝ) * (Real.log 11)^2 / 3 := by positivity
    have h2 : 0 < (2 + 5*C_K) * C_a := by nlinarith [hC_K, hC_a]
    have h3 := le_max_left (11 * (Real.log 11)^2 / 3) ((2 + 5*C_K) * C_a)
    have h4 := le_max_right (11 * (Real.log 11)^2 / 3) ((2 + 5*C_K) * C_a)
    linarith
  intro f hf1 hmul hb x T hx hT
  have hx3 : (3:ℝ) ≤ x := hx
  have hlogx : 0 < Real.log x := Real.log_pos (by linarith)
  have hlogx1 : 1 ≤ Real.log x := by
    rw [← Real.log_exp 1]
    exact Real.log_le_log (Real.exp_pos 1) (by linarith [Real.exp_one_lt_d9])
  have hlogxnn : 0 ≤ x / Real.log x := by positivity
  set I : ℝ := ∫ α in (1 / Real.log x)..1, Real.exp (Wsup f x α (T + 1)) / α with hIdef
  set E1 : ℝ := Real.exp (Zrcp x) / Real.sqrt T with hE1def
  set E2 : ℝ := Real.exp (Zrcp x) / Real.log x with hE2def
  have hI0 : 0 ≤ I := by
    rw [hIdef]
    refine intervalIntegral.integral_nonneg ?_ (fun α hα => ?_)
    · rw [div_le_iff₀ hlogx, one_mul]; exact hlogx1
    · have hα0 : 0 < α := lt_of_lt_of_le (by positivity : 0 < 1 / Real.log x) hα.1
      exact div_nonneg (Real.exp_pos _).le hα0.le
  have hE1nn : 0 ≤ E1 := by rw [hE1def]; positivity
  have hE2nn : 0 ≤ E2 := by rw [hE2def]; positivity
  by_cases hx11 : x < 11
  · -- small range
    have hlogxle : Real.log x ≤ Real.log 11 := Real.log_le_log (by linarith) hx11.le
    have hZ : (1:ℝ) ≤ Real.exp (Zrcp x) := by
      rw [← Real.exp_zero]; exact Real.exp_le_exp.mpr (Zrcp_nonneg x)
    have hkey : (3/Real.log 11) * (1/Real.log 11)
        ≤ (x/Real.log x) * (I + E1 + E2) := by
      have h1 : 3/Real.log 11 ≤ x / Real.log x :=
        div_le_div₀ (by linarith) hx3 hlogx hlogxle
      have h2 : 1/Real.log 11 ≤ Real.exp (Zrcp x)/Real.log x :=
        div_le_div₀ (by positivity) hZ hlogx hlogxle
      have h3 : (3/Real.log 11) * (1/Real.log 11)
          ≤ (x/Real.log x) * (Real.exp (Zrcp x)/Real.log x) :=
        mul_le_mul h1 h2 (by positivity) (by positivity)
      have h4 : (x/Real.log x) * (Real.exp (Zrcp x)/Real.log x)
          ≤ (x/Real.log x) * (I + E1 + E2) :=
        mul_le_mul_of_nonneg_left (by linarith [hI0, hE1nn, hE2def]) hlogxnn
      linarith [h3, h4]
    have hprod : (11:ℝ) * (Real.log 11)^2 / 3 * ((3/Real.log 11) * (1/Real.log 11)) = 11 := by
      field_simp
    have hpos : 0 < (3/Real.log 11) * (1/Real.log 11) := by positivity
    have hCbig : (11:ℝ) ≤ (max (11 * (Real.log 11)^2 / 3) ((2 + 5*C_K) * C_a) + 1)
        * ((3/Real.log 11) * (1/Real.log 11)) := by
      have hmax : (11:ℝ) * (Real.log 11)^2 / 3
          ≤ max (11 * (Real.log 11)^2 / 3) ((2 + 5*C_K) * C_a) := le_max_left _ _
      nlinarith [hmax, hprod, hpos]
    have hMf : ‖Mf f x‖ ≤ 11 := le_trans (Mf_norm_le_x f hb x (by linarith)) (le_of_lt hx11)
    have hCnn : 0 ≤ max (11 * (Real.log 11)^2 / 3) ((2 + 5*C_K) * C_a) + 1 := by positivity
    calc ‖Mf f x‖ ≤ 11 := hMf
      _ ≤ (max (11 * (Real.log 11)^2 / 3) ((2 + 5*C_K) * C_a) + 1)
            * ((3/Real.log 11) * (1/Real.log 11)) := hCbig
      _ ≤ (max (11 * (Real.log 11)^2 / 3) ((2 + 5*C_K) * C_a) + 1)
            * ((x/Real.log x) * (I + E1 + E2)) := mul_le_mul_of_nonneg_left hkey hCnn
      _ = (max (11 * (Real.log 11)^2 / 3) ((2 + 5*C_K) * C_a) + 1) * (x / Real.log x)
            * (I + E1 + E2) := by ring
      _ = (max (11 * (Real.log 11)^2 / 3) ((2 + 5*C_K) * C_a) + 1) * (x / Real.log x) *
            ((∫ α in (1 / Real.log x)..1, Real.exp (Wsup f x α (T + 1)) / α) +
             Real.exp (Zrcp x) / Real.sqrt T + Real.exp (Zrcp x) / Real.log x) := by
          rw [hIdef, hE1def, hE2def]
  · -- main range
    push_neg at hx11
    have hA := ha f hf1 hmul hb x T hx11 (by linarith)
    have hAhalf := A_ge f hf1 hb (by linarith : (2:ℝ) ≤ x)
    have hKb := hK f hf1 hmul hb x hx3
    have hA'' : (∫ t in (1 : ℝ)..x, ‖Mf f t‖ / t ^ 2) ≤ C_a * (I + E1) := by
      rw [hIdef, hE1def]; exact hA
    have hfin : ‖Mf f x‖ ≤ (2 + 5*C_K) * (x/Real.log x)
        * (∫ t in (1 : ℝ)..x, ‖Mf f t‖ / t ^ 2) := by
      have h1 : C_K * x / Real.log x ≤ 5 * C_K * ((x/Real.log x)
          * (∫ t in (1 : ℝ)..x, ‖Mf f t‖ / t ^ 2)) := by
        have hcl : C_K ≤ 5 * C_K * (∫ t in (1 : ℝ)..x, ‖Mf f t‖ / t ^ 2) := by
          nlinarith [hAhalf, hC_K]
        calc C_K * x / Real.log x = (x/Real.log x) * C_K := by ring
          _ ≤ (x/Real.log x) * (5 * C_K * (∫ t in (1 : ℝ)..x, ‖Mf f t‖ / t ^ 2)) :=
              mul_le_mul_of_nonneg_left hcl hlogxnn
          _ = 5 * C_K * ((x/Real.log x) * (∫ t in (1 : ℝ)..x, ‖Mf f t‖ / t ^ 2)) := by ring
      rw [show (2 + 5*C_K) * (x/Real.log x) * (∫ t in (1 : ℝ)..x, ‖Mf f t‖ / t ^ 2)
          = (2 * x / Real.log x) * (∫ t in (1 : ℝ)..x, ‖Mf f t‖ / t ^ 2)
            + 5 * C_K * ((x/Real.log x) * (∫ t in (1 : ℝ)..x, ‖Mf f t‖ / t ^ 2)) by ring]
      linarith [hKb, h1]
    have hfin2 : (2 + 5*C_K) * (x/Real.log x) * (∫ t in (1 : ℝ)..x, ‖Mf f t‖ / t ^ 2)
        ≤ ((2 + 5*C_K) * C_a) * (x/Real.log x) * (I + E1) := by
      have hnn2 : 0 ≤ (2 + 5*C_K) * (x/Real.log x) := by positivity
      calc (2 + 5*C_K) * (x/Real.log x) * (∫ t in (1 : ℝ)..x, ‖Mf f t‖ / t ^ 2)
          ≤ (2 + 5*C_K) * (x/Real.log x) * (C_a * (I + E1)) :=
            mul_le_mul_of_nonneg_left hA'' hnn2
        _ = ((2 + 5*C_K) * C_a) * (x/Real.log x) * (I + E1) := by ring
    have hCnn : 0 ≤ max (11 * (Real.log 11)^2 / 3) ((2 + 5*C_K) * C_a) + 1 := by positivity
    have hleC : ((2 + 5*C_K) * C_a)
        ≤ max (11 * (Real.log 11)^2 / 3) ((2 + 5*C_K) * C_a) + 1 := by
      linarith [le_max_right (11 * (Real.log 11)^2 / 3) ((2 + 5*C_K) * C_a)]
    have hIEnn : 0 ≤ I + E1 + E2 := by linarith [hI0, hE1nn, hE2nn]
    calc ‖Mf f x‖ ≤ ((2 + 5*C_K) * C_a) * (x/Real.log x) * (I + E1) := le_trans hfin hfin2
      _ ≤ ((2 + 5*C_K) * C_a) * (x/Real.log x) * (I + E1 + E2) := by
          rw [show ((2 + 5*C_K) * C_a) * (x/Real.log x) * (I + E1)
              = ((2 + 5*C_K) * C_a) * ((x/Real.log x) * (I + E1)) by ring,
            show ((2 + 5*C_K) * C_a) * (x/Real.log x) * (I + E1 + E2)
              = ((2 + 5*C_K) * C_a) * ((x/Real.log x) * (I + E1 + E2)) by ring]
          exact mul_le_mul_of_nonneg_left
            (mul_le_mul_of_nonneg_left (by linarith [hE2nn]) hlogxnn) (by positivity)
      _ ≤ (max (11 * (Real.log 11)^2 / 3) ((2 + 5*C_K) * C_a) + 1) * (x/Real.log x)
            * (I + E1 + E2) := by
          rw [show ((2 + 5*C_K) * C_a) * (x/Real.log x) * (I + E1 + E2)
              = ((2 + 5*C_K) * C_a) * ((x/Real.log x) * (I + E1 + E2)) by ring,
            show (max (11 * (Real.log 11)^2 / 3) ((2 + 5*C_K) * C_a) + 1) * (x/Real.log x)
                * (I + E1 + E2)
              = (max (11 * (Real.log 11)^2 / 3) ((2 + 5*C_K) * C_a) + 1)
                * ((x/Real.log x) * (I + E1 + E2)) by ring]
          exact mul_le_mul_of_nonneg_right hleC (mul_nonneg hlogxnn hIEnn)
      _ = (max (11 * (Real.log 11)^2 / 3) ((2 + 5*C_K) * C_a) + 1) * (x / Real.log x) *
            ((∫ α in (1 / Real.log x)..1, Real.exp (Wsup f x α (T + 1)) / α) +
             Real.exp (Zrcp x) / Real.sqrt T + Real.exp (Zrcp x) / Real.log x) := by
          rw [hIdef, hE1def, hE2def]

end Work.BMF
