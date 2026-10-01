import Mathlib
import Submission.Work.ZeroFreeTables.HB63_TestFn
import Submission.Work.ZeroFreeTables.testFn7_2
import Submission.Work.ZeroFreeTables.TestFn_F_eq_integral
import Submission.Work.ZeroFreeTables.TestFn_F_antitone
import Submission.Work.ZeroFreeTables.Table4.HB82
import Submission.Work.LinnikAreas.exists_minLam_zero
import Submission.Work.LinnikContract.API.isZ_lambda_nonneg
import Submission.Work.ZeroFreeTables.lam0_rows_fmethod_wide83
import Submission.Work.ZeroFreeTables.lam0w.table7_p3_certs
import Submission.Work.ZeroFreeTables.lam0w.table7_rows_facts
import Submission.Work.ZeroFreeTables.HBRepZero84_proof
import Submission.Work.ZeroFreeTables.Table4Cert
import Submission.Work.LinnikAreas.boxMaxZeroH
import Submission.Work.ZeroFreeTables.API
import Submission.Work.ZeroFreeTables.tf72G
import Submission.Work.ZeroFreeTables.lam0_row01
import Submission.Work.ZeroFreeTables.lam0_rows_a
import Submission.Work.ZeroFreeTables.lam0_rows_b
import Submission.Work.ZeroFreeTables.lam0_rows_c

namespace Work.ZeroFreeTables

open Work.LinnikContract
open scoped Classical BigOperators

noncomputable section

/-! ## The rows of the request -/

/-- The `λ₀`-rows of the request. -/
def fmRows : List (ℝ × ℝ) :=
  [((1/10 : ℝ), (276/100 : ℝ)), ((12/100 : ℝ), (256/100 : ℝ)), ((14/100 : ℝ), (239/100 : ℝ)),
   ((16/100 : ℝ), (225/100 : ℝ)), ((18/100 : ℝ), (212/100 : ℝ)), ((20/100 : ℝ), (201/100 : ℝ)),
   ((25/100 : ℝ), (177/100 : ℝ)), ((30/100 : ℝ), (158/100 : ℝ)), ((35/100 : ℝ), (142/100 : ℝ)),
   ((2/5 : ℝ), (129/100 : ℝ))]

theorem fmRows_mem_hbTable7 : ∀ p ∈ fmRows, p ∈ tableR hbTable7 := by
  intro p hp
  fin_cases hp <;> norm_num [tableR, hbTable7]

theorem fmRows_le_two_fifths : ∀ p ∈ fmRows, p.1 ≤ 2/5 := by
  intro p hp
  fin_cases hp <;> norm_num

theorem fmRows_le_276 : ∀ p ∈ fmRows, p.2 ≤ 276/100 :=
  fun p hp => (lam0w.table7_rows_facts.1 p (fmRows_mem_hbTable7 p hp)).2.2.2.1

theorem fmRows_small : ∀ p ∈ fmRows, (1:ℝ)/5 < p.1 → p.2 ≤ 2293/1000 := by
  intro p hp h
  by_contra hcon
  push Not at hcon
  have h14 := lam0w.table7_rows_facts.2 p (fmRows_mem_hbTable7 p hp) hcon
  linarith

/-! ## The `F`-monotonicity of §6 -/

/-- `T.F (-a) - T.F (b - a) = ∫₀^{x₀} e^{at}(1 - e^{-bt}) f t dt`. -/
theorem TestFn_F_sub (T : TestFn) (a b : ℝ) :
    T.F (-a) - T.F (b - a)
      = ∫ t in (0:ℝ)..T.x₀, Real.exp (a * t) * (1 - Real.exp (-(b * t))) * T.f t := by
  have h1 : T.F (-a) = ∫ t in (0:ℝ)..T.x₀, Real.exp (a * t) * T.f t := by
    rw [TestFn_F_eq_integral]
    exact intervalIntegral.integral_congr (fun t _ => by simp only [neg_mul, neg_neg])
  have h2 : T.F (b - a) = ∫ t in (0:ℝ)..T.x₀, Real.exp ((a - b) * t) * T.f t := by
    rw [TestFn_F_eq_integral]
    exact intervalIntegral.integral_congr (fun t _ => by
      rw [show -((b - a) * t) = (a - b) * t by ring])
  rw [h1, h2]
  have hcont : ∀ y : ℝ, ContinuousOn (fun t : ℝ => Real.exp (y * t) * T.f t) (Set.Icc 0 T.x₀) :=
    fun y => ((Real.continuous_exp.comp (continuous_const.mul continuous_id)).continuousOn).mul
      (T.f_cont.mono (fun t ht => ht.1))
  have hint : ∀ y : ℝ, IntervalIntegrable (fun t : ℝ => Real.exp (y * t) * T.f t)
      MeasureTheory.volume (0 : ℝ) T.x₀ := fun y =>
    ContinuousOn.intervalIntegrable_of_Icc (le_of_lt T.x₀_pos) (hcont y)
  rw [← intervalIntegral.integral_sub (hint a) (hint (a - b))]
  refine intervalIntegral.integral_congr (fun t _ => ?_)
  rw [show (a - b) * t = a * t + -(b * t) by ring, Real.exp_add]
  ring

/-- `T.F (-a) - T.F (b - a)` is increasing in `a` and in `b` (for `a, b ≥ 0`). -/
theorem TestFn_E_mono (T : TestFn) {a a' b b' : ℝ} (hb : 0 ≤ b) (haa : a ≤ a') (hbb : b ≤ b') :
    T.F (-a) - T.F (b - a) ≤ T.F (-a') - T.F (b' - a') := by
  rw [TestFn_F_sub T a b, TestFn_F_sub T a' b']
  have hx : (0:ℝ) ≤ T.x₀ := le_of_lt T.x₀_pos
  have hcont : ∀ y y' : ℝ, ContinuousOn
      (fun t : ℝ => Real.exp (y * t) * (1 - Real.exp (-(y' * t))) * T.f t) (Set.Icc 0 T.x₀) := by
    intro y y'
    refine ((((Real.continuous_exp.comp (continuous_const.mul continuous_id)).continuousOn).mul
      ((continuous_const.sub ((Real.continuous_exp.comp
        ((continuous_const.mul continuous_id).neg)))).continuousOn)).mul
      (T.f_cont.mono (fun t ht => ht.1)))
  have hint : ∀ y y' : ℝ, IntervalIntegrable
      (fun t : ℝ => Real.exp (y * t) * (1 - Real.exp (-(y' * t))) * T.f t)
      MeasureTheory.volume (0 : ℝ) T.x₀ := fun y y' =>
    ContinuousOn.intervalIntegrable_of_Icc hx (hcont y y')
  refine intervalIntegral.integral_mono_on hx (hint a b) (hint a' b') (fun t ht => ?_)
  have ht0 : 0 ≤ t := ht.1
  have hf : 0 ≤ T.f t := T.f_nonneg t
  have e1 : Real.exp (a * t) ≤ Real.exp (a' * t) := Real.exp_le_exp.mpr (by nlinarith)
  have e2 : Real.exp (-(b' * t)) ≤ Real.exp (-(b * t)) := Real.exp_le_exp.mpr (by nlinarith)
  have e3 : 1 - Real.exp (-(b * t)) ≤ 1 - Real.exp (-(b' * t)) := by linarith
  have e0 : 0 ≤ 1 - Real.exp (-(b * t)) := by
    have h : Real.exp (-(b * t)) ≤ 1 := by
      have := Real.exp_le_exp.mpr (show -(b * t) ≤ 0 by nlinarith)
      simpa using this
    linarith
  have h1 : Real.exp (a * t) * (1 - Real.exp (-(b * t)))
      ≤ Real.exp (a' * t) * (1 - Real.exp (-(b' * t))) := by
    have hb1 : Real.exp (a * t) * (1 - Real.exp (-(b * t)))
        ≤ Real.exp (a' * t) * (1 - Real.exp (-(b * t))) :=
      mul_le_mul_of_nonneg_right e1 e0
    have hb2 : Real.exp (a' * t) * (1 - Real.exp (-(b * t)))
        ≤ Real.exp (a' * t) * (1 - Real.exp (-(b' * t))) :=
      mul_le_mul_of_nonneg_left e3 (Real.exp_pos _).le
    linarith
  exact mul_le_mul_of_nonneg_right h1 hf

/-! ## The certificate rows of HB Table 7 = the rows of `lam0_cert_rows` -/

theorem cert_real : ∀ p ∈ fmRows,
    2 * ((tf72T (37/20) (by norm_num)).F (-(p.2))
          - (tf72T (37/20) (by norm_num)).F (p.1 - p.2))
      < (tf72T (37/20) (by norm_num)).F 0
        - (tf72T (37/20) (by norm_num)).f 0 * ((1/4 : ℝ) + 4 * (1/4000)) := by
  intro p hp
  fin_cases hp
  · exact lam0_row01
  · exact lam0_rows_a.1
  · exact lam0_rows_a.2.1
  · exact lam0_rows_a.2.2.1
  · exact lam0_rows_a.2.2.2
  · exact lam0_rows_b.1
  · exact lam0_rows_b.2.1
  · exact lam0_rows_b.2.2.1
  · exact lam0_rows_b.2.2.2
  · simpa only [show (2/5 : ℝ) = 40/100 from by norm_num] using lam0_rows_c.1

/-! ## `zeroMult`-zeros lie in the critical strip -/

theorem zeroMult_strip {q : ℕ} [NeZero q] {χ : DirichletCharacter ℂ q} (hχ : χ ≠ 1)
    {ρ : ℂ} (hzm : Work.LinnikContract.zeroMult χ ρ ≠ 0) : 0 < ρ.re ∧ ρ.re < 1 := by
  have hprim : χ.primitiveCharacter.IsPrimitive :=
    DirichletCharacter.primitiveCharacter_isPrimitive χ
  have hne1 : χ.primitiveCharacter ≠ 1 := by
    intro h1
    refine hχ ?_
    rw [← DirichletCharacter.changeLevel_primitiveCharacter χ, h1]
    exact DirichletCharacter.changeLevel_one χ.conductor_dvd_level
  have hz : @DirichletCharacter.completedLFunction χ.conductor ⟨χ.conductor_ne_zero⟩
      χ.primitiveCharacter ρ = 0 := by
    apply apply_eq_zero_of_analyticOrderNatAt_ne_zero
    exact hzm
  exact @Commons.NumberTheory.Linnik.completedL_zero_strip χ.conductor ⟨χ.conductor_ne_zero⟩
    χ.primitiveCharacter hne1 hprim ρ hz

/-! ## The `P₃` certificate at a non-real second zero -/

/-- A `P₃` certificate row of HB Table 7 forces `λ(ρ₀) ≥ v` for a *non-real* second zero `ρ₀`,
whenever `λ(ρ₁) ≤ p.1`. -/
theorem cert_nonreal (p : ℝ × ℝ) (a K v : ℝ) (ha : 0 < a) (hK4 : 1/4 ≤ K)
    (hp1nn : 0 ≤ p.1) (hp1v : p.1 ≤ v) (h88 : cond88 0 a K) (h86 : cond86 p.1 v a)
    (h83 : p83 p.1 v a K < 0) :
    ∃ q₀ : ℕ, ∀ q : ℕ, q₀ ≤ q → ∀ [NeZero q] (χ₁ : DirichletCharacter ℂ q) (ρ₁ ρ₀ : ℂ),
      IsMin1WideAt 10 χ₁ ρ₁ → χ₁ ^ 2 = 1 → χ₁ ≠ 1 → ρ₁.im = 0 → IsZ χ₁ ρ₁ → IsZ χ₁ ρ₀ →
      ρ₀ ≠ ρ₁ → ρ₀.im ≠ 0 → lamOf q ρ₁ ≤ p.1 → v ≤ lamOf q ρ₀ := by
  have hK0 : 0 < K := lt_of_lt_of_le (by norm_num : (0:ℝ) < 1/4) hK4
  set e : ℝ := -(p83 p.1 v a K) / (2 * (K + 1) ^ 2 * (a + p.1)) with he
  have hden : 0 < 2 * (K + 1) ^ 2 * (a + p.1) := by
    have h1 : 0 < a + p.1 := by linarith
    positivity
  have hepos : 0 < e := by rw [he]; exact div_pos (by linarith) hden
  obtain ⟨q₀, hq₀⟩ := lam0w.HBLemma8_3_wide_fm a K e ha hK4 hepos
  refine ⟨max q₀ 3, fun q hq _ χ₁ ρ₁ ρ₀ hw hsq hχ1 him1 hZ₁ hZ₀ hne hρ₀im hlo => ?_⟩
  have hq₀' : q₀ ≤ q := le_trans (le_max_left _ _) hq
  have hq2 : 2 ≤ q := by omega
  by_contra hcon
  push Not at hcon
  have hlam1nn : 0 ≤ lamOf q ρ₁ := Work.LinnikContract.API.isZ_lambda_nonneg hq2 hZ₁
  have hlamle : lamOf q ρ₁ ≤ lamOf q ρ₀ :=
    hw.2 χ₁ ρ₀ hχ1 hZ₀.2.1 (by linarith [hZ₀.2.2])
  have hcond : cond86 (lamOf q ρ₁) (lamOf q ρ₀) a :=
    cond86_mono h86 hlo hcon.le (by linarith) (by linarith)
  have hineq := hq₀ q hq₀' χ₁ ρ₁ ρ₀ hw hsq hχ1 him1 hZ₁ hZ₀.2.1
    (by linarith [hZ₀.2.2] : |ρ₀.im| ≤ 2) hne hρ₀im hlamle hcond
  have hmono0 : p83 (lamOf q ρ₁) (lamOf q ρ₀) a K ≤ p83 (lamOf q ρ₁) v a K :=
    p83_mono_lam₀ ha hK0.le (by linarith) (by linarith) (by linarith) hcon.le
  have hc88' : cond88 (lamOf q ρ₁) a K := cond88_mono_lam₁ h88 hlam1nn ha (by linarith) hK0
  have hmono1 : p83 (lamOf q ρ₁) v a K ≤ p83 p.1 v a K :=
    p83_mono_lam₁ hlam1nn hlo hp1v ha hK0 hc88'
  have heval : (K + 1) ^ 2 * (a + p.1) * e = -(p83 p.1 v a K) / 2 := by
    rw [he]
    have h1 : (0:ℝ) < K + 1 := by linarith
    have h2 : (0:ℝ) < a + p.1 := by linarith
    field_simp
  have hterm : (K + 1) ^ 2 * (a + lamOf q ρ₁) * e ≤ (K + 1) ^ 2 * (a + p.1) * e := by
    have h1 : (0:ℝ) < (K + 1) ^ 2 := by positivity
    have h2 : a + lamOf q ρ₁ ≤ a + p.1 := by linarith
    exact mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_left h2 h1.le) hepos.le
  linarith [hineq, hmono0, hmono1, heval, hterm, h83]


/-! ## The Archimedean thresholds -/

theorem guards (δ : ℝ) (hδ : 0 < δ) :
    ∃ q₀ : ℕ, ∀ q : ℕ, q₀ ≤ q →
      3 ≤ q ∧ (1/5) / δ ≤ Real.log (q : ℝ) ∧ 12 / δ ≤ Real.log (q : ℝ) ∧
      (1/5) ≤ Real.sqrt (Real.log (Real.log (q : ℝ))) ∧
      12 ≤ Real.sqrt (Real.log (Real.log (q : ℝ))) ∧
      (1:ℝ)/5 ≤ Real.log (Real.log (Real.log (q : ℝ))) / 3 ∧
      12 ≤ Real.log (Real.log (Real.log (q : ℝ))) / 3 := by
  set N : ℝ := max (max ((1/5) / δ) (12 / δ)) 144 with hN
  have hAN : (1/5) / δ ≤ N := le_trans (le_max_left _ _) (le_max_left _ _)
  have hBN : 12 / δ ≤ N := le_trans (le_max_right _ _) (le_max_left _ _)
  have hN144 : (144:ℝ) ≤ N := le_max_right _ _
  refine ⟨⌈Real.exp (Real.exp (Real.exp N))⌉₊ + 3, ?_⟩
  intro q hq
  have hq3 : 3 ≤ q := by omega
  have hExp : Real.exp (Real.exp (Real.exp N)) ≤ (q : ℝ) := by
    have h1 : Real.exp (Real.exp (Real.exp N))
        ≤ (⌈Real.exp (Real.exp (Real.exp N))⌉₊ : ℝ) := Nat.le_ceil _
    have h2 : ((⌈Real.exp (Real.exp (Real.exp N))⌉₊ : ℕ) : ℝ) ≤ (q : ℝ) := by
      exact_mod_cast (by omega : ⌈Real.exp (Real.exp (Real.exp N))⌉₊ ≤ q)
    linarith
  have hNN : N ≤ Real.exp N := by have := Real.add_one_le_exp N; linarith
  have hNN2 : N ≤ Real.exp (Real.exp N) := le_trans hNN (Real.exp_le_exp.mpr hNN)
  have hlogq : Real.exp (Real.exp N) ≤ Real.log (q : ℝ) := by
    have h := Real.log_le_log (Real.exp_pos (Real.exp (Real.exp N))) hExp
    rwa [Real.log_exp] at h
  have hloglogq : Real.exp N ≤ Real.log (Real.log (q : ℝ)) := by
    have h := Real.log_le_log (Real.exp_pos (Real.exp N)) hlogq
    rwa [Real.log_exp] at h
  have hlogloglogq : N ≤ Real.log (Real.log (Real.log (q : ℝ))) := by
    have h := Real.log_le_log (Real.exp_pos N) hloglogq
    rwa [Real.log_exp] at h
  have hsq : (12:ℝ) ≤ Real.sqrt (Real.log (Real.log (q : ℝ))) := by
    have h144 : (144:ℝ) ≤ Real.log (Real.log (q : ℝ)) :=
      le_trans (le_trans hN144 hNN) hloglogq
    have h := Real.sqrt_le_sqrt h144
    rwa [show Real.sqrt (144:ℝ) = 12 by norm_num] at h
  have hthird : (12:ℝ) ≤ Real.log (Real.log (Real.log (q : ℝ))) / 3 := by linarith
  exact ⟨hq3, le_trans hAN (le_trans hNN2 hlogq), le_trans hBN (le_trans hNN2 hlogq),
    by linarith, hsq, by linarith, hthird⟩

/-! ## Heath-Brown's Lemma 6.3 at scale `37/20` for a real second zero -/

theorem s6_real_37 (c δ : ℝ) (hc : c ≤ 1/8 + 1/1000000) (hδ0 : 0 < δ) (hδ1 : δ < 1)
    (Qδ : ℕ)
    (hprov : ∀ (q : ℕ), Qδ ≤ q → ∀ [NeZero q] (χ : DirichletCharacter ℂ q)
      [NeZero χ.conductor], χ ≠ 1 → χ ^ 2 = 1 →
      Commons.NumberTheory.Linnik.L52Hyp χ c (1/5000) δ) :
    ∃ q₀ : ℕ, ∀ q : ℕ, q₀ ≤ q → ∀ [NeZero q] (χ₁ : DirichletCharacter ℂ q) (ρ₁ u : ℂ),
      IsMin1WideAt 10 χ₁ ρ₁ → χ₁ ^ 2 = 1 → ρ₁.im = 0 → zeroMult χ₁ ρ₁ = 1 →
      IsZ χ₁ u → u ≠ ρ₁ → u.im = 0 →
      (∀ z : ℂ, zeroMult χ₁ z ≠ 0 → |z.im| ≤ 1 → z ≠ ρ₁ → lamOf q u ≤ lamOf q z) →
      lamOf q ρ₁ ≤ 1/5 → lamOf q u ≤ 12 →
      lamOf q u ≤ Real.log (Real.log (Real.log (q : ℝ))) / 3 →
      (1/5) / δ ≤ Real.log (q : ℝ) → 12 / δ ≤ Real.log (q : ℝ) →
      (1/5) ≤ Real.sqrt (Real.log (Real.log (q : ℝ))) →
      12 ≤ Real.sqrt (Real.log (Real.log (q : ℝ))) →
      (1:ℝ)/5 ≤ Real.log (Real.log (Real.log (q : ℝ))) / 3 →
      0 ≤ 2 * (tf72T (37/20) (by norm_num)).F (-(lamOf q u))
        - 2 * (tf72T (37/20) (by norm_num)).F (lamOf q ρ₁ - lamOf q u)
        - (tf72T (37/20) (by norm_num)).F 0
        + (tf72T (37/20) (by norm_num)).f 0 * (2*c + 4*(1/5000)) := by
  obtain ⟨qT, hT⟩ := HB63_TestFn (tf72T (37/20) (by norm_num)) (1/5000) (by norm_num)
    δ hδ0 hδ1 c
  refine ⟨max (max qT 3) Qδ, ?_⟩
  intro q hq _inst χ₁ ρ₁ u hwide hsq him0 hmult1 hZu hune hu0 hMin hlam1 hu12 hcap
    hthr1 hthr2 hpt1 hpt2 hcap1
  have hqT : qT ≤ q := le_trans (le_trans (le_max_left _ _) (le_max_left _ _)) hq
  have hq3 : 3 ≤ q := le_trans (le_trans (le_max_right _ _) (le_max_left _ _)) hq
  have hqδ : Qδ ≤ q := le_trans (le_max_right _ _) hq
  letI : NeZero χ₁.conductor := ⟨χ₁.conductor_ne_zero⟩
  have hχ1 : χ₁ ≠ 1 := isZ_ne_one (isMin1_isZ hwide.1)
  have hq2 : 2 ≤ q := by omega
  have hlogq : 0 < Real.log (q : ℝ) := Real.log_pos (by exact_mod_cast (by omega : 1 < q))
  have hzm1 : zeroMult χ₁ ρ₁ ≠ 0 := by rw [hmult1]; norm_num
  have hstrip₁ : 0 < ρ₁.re ∧ ρ₁.re < 1 := zeroMult_strip hχ1 hzm1
  have hstripu : 0 < u.re ∧ u.re < 1 := zeroMult_strip hχ1 hZu.2.1
  have hconj₁ : ρ₁ = ((ρ₁.re : ℝ) : ℂ) := by apply Complex.ext <;> simp [him0]
  -- the two `δ`-window conditions
  have hβ₁ : |1 - ρ₁.re| ≤ δ := by
    have h1 : 1 - ρ₁.re = lamOf q ρ₁ / Real.log (q : ℝ) := by rw [lamOf]; field_simp
    have h2 : lamOf q ρ₁ / Real.log (q : ℝ) ≤ δ := by
      calc lamOf q ρ₁ / Real.log (q : ℝ) ≤ (1 / 5) / Real.log (q : ℝ) :=
            div_le_div_of_nonneg_right hlam1 hlogq.le
        _ ≤ δ := by
            rw [div_le_iff₀ hlogq]
            linarith [(div_le_iff₀ hδ0).mp hthr1]
    rw [abs_le, h1]
    exact ⟨by linarith [hstrip₁.1], h2⟩
  have hβu : |1 - u.re| ≤ δ := by
    have h1 : 1 - u.re = lamOf q u / Real.log (q : ℝ) := by rw [lamOf]; field_simp
    have h2 : lamOf q u / Real.log (q : ℝ) ≤ δ := by
      calc lamOf q u / Real.log (q : ℝ) ≤ 12 / Real.log (q : ℝ) :=
            div_le_div_of_nonneg_right hu12 hlogq.le
        _ ≤ δ := by
            rw [div_le_iff₀ hlogq]
            linarith [(div_le_iff₀ hδ0).mp hthr2]
    rw [abs_le, h1]
    exact ⟨by linarith [hstripu.1], h2⟩
  have hβ₁pt : |1 - ρ₁.re| ≤ Real.sqrt (Real.log (Real.log (q : ℝ))) / Real.log (q : ℝ) := by
    have h1 : 1 - ρ₁.re = lamOf q ρ₁ / Real.log (q : ℝ) := by rw [lamOf]; field_simp
    have h2 : lamOf q ρ₁ / Real.log (q : ℝ)
        ≤ Real.sqrt (Real.log (Real.log (q : ℝ))) / Real.log (q : ℝ) :=
      div_le_div_of_nonneg_right (by linarith) hlogq.le
    rw [abs_le, h1]
    exact ⟨by linarith [hstrip₁.1], h2⟩
  have hupt : |1 - u.re| ≤ Real.sqrt (Real.log (Real.log (q : ℝ))) / Real.log (q : ℝ) := by
    have h1 : 1 - u.re = lamOf q u / Real.log (q : ℝ) := by rw [lamOf]; field_simp
    have h2 : lamOf q u / Real.log (q : ℝ)
        ≤ Real.sqrt (Real.log (Real.log (q : ℝ))) / Real.log (q : ℝ) :=
      div_le_div_of_nonneg_right (by linarith) hlogq.le
    rw [abs_le, h1]
    exact ⟨by linarith [hstripu.1], h2⟩
  have hcap₁ : lamOf q ((ρ₁.re : ℝ) : ℂ) ≤ Real.log (Real.log (Real.log (q : ℝ))) / 3 := by
    rw [← hconj₁]; linarith
  -- divisor facts
  have hdiff : Differentiable ℂ (DirichletCharacter.completedLFunction χ₁.primitiveCharacter) :=
    DirichletCharacter.differentiable_completedLFunction
      (Work.LinnikAreas.OtherCharRepel.primitiveCharacter_ne_one χ₁ hχ1)
  have hmem1 : ρ₁ ∈ Metric.closedBall (0:ℂ) (|u.im| + 2) := by
    rw [Metric.mem_closedBall, dist_zero_right]
    have h1 : |ρ₁.re| ≤ 1 := by
      rw [abs_le]; exact ⟨by linarith [hstrip₁.1], by linarith [hstrip₁.2]⟩
    calc ‖ρ₁‖ = |ρ₁.re| := by rw [hconj₁, Complex.norm_real]; simp
      _ ≤ |u.im| + 2 := by linarith [abs_nonneg u.im]
  have hmemu : u ∈ Metric.closedBall (0:ℂ) (|u.im| + 2) := by
    rw [Metric.mem_closedBall, dist_zero_right]
    refine le_trans (Complex.norm_le_abs_re_add_abs_im u) ?_
    have h2 : |u.re| ≤ 2 := by
      rw [abs_le]; exact ⟨by linarith [hstripu.1], by linarith [hstripu.2]⟩
    linarith [abs_nonneg u.im]
  have han : AnalyticOnNhd ℂ (DirichletCharacter.completedLFunction χ₁.primitiveCharacter)
      (Metric.closedBall (0:ℂ) (|u.im| + 2)) := fun z _ => hdiff.analyticAt z
  have hdiv₁ := (Work.LinnikAreas.OtherCharRepel.zeroMultTransfer χ₁ hχ1).2.1 ρ₁ (|u.im| + 2)
    hzm1 hmem1
  have hdivu := (Work.LinnikAreas.OtherCharRepel.zeroMultTransfer χ₁ hχ1).2.1 u (|u.im| + 2)
    hZu.2.1 hmemu
  have hdiv₁' : (MeromorphicOn.divisor (DirichletCharacter.completedLFunction χ₁.primitiveCharacter)
      (Metric.closedBall 0 (|u.im| + 2))) ((ρ₁.re : ℝ) : ℂ) ≠ 0 := by rwa [← hconj₁]
  have hmult₁' : (MeromorphicOn.divisor (DirichletCharacter.completedLFunction χ₁.primitiveCharacter)
      (Metric.closedBall 0 (|u.im| + 2))) ((ρ₁.re : ℝ) : ℂ) = 1 := by
    rw [← hconj₁, Commons.Analysis.Complex.divisor_eq_analyticOrderNatAt_cast han hmem1]
    have h1 : analyticOrderNatAt (DirichletCharacter.completedLFunction χ₁.primitiveCharacter) ρ₁
        = 1 := by
      have h := hmult1
      rw [zeroMult] at h
      exact h
    rw [h1]; norm_num
  have hne' : u ≠ ((ρ₁.re : ℝ) : ℂ) := by
    intro h
    exact hune (by rw [h, ← hconj₁])
  have hmax : ∀ w : ℂ, DirichletCharacter.LFunction χ₁.primitiveCharacter w = 0 →
      |w.im| ≤ 1 → w = ((ρ₁.re : ℝ) : ℂ) ∨ w.re ≤ u.re := by
    have h0 := Table4.maxOfMinOr χ₁ hχ1 ρ₁ u
      (fun z hZ hne => hMin z (isZ_mult_ne_zero hZ) hZ.2.2 hne) hZu
    intro w hw him
    rcases h0 w hw him with h | h
    · exact Or.inl (h.trans hconj₁)
    · exact Or.inr h
  have hmain := hT q hqT χ₁ hχ1 hsq (β₁ := ρ₁.re) (ρ' := u) hβ₁ hβu
    (Hb := 1) (by rw [hu0]; simp only [abs_zero, zero_add]; linarith [hδ1])
    (by rw [hu0]; simp only [abs_zero]; linarith [hlogq])
    hβ₁pt hupt hdiv₁' hdivu hne' hmult₁' hmax hcap₁ hcap (hprov q hqδ χ₁ hχ1 hsq)
  have hF1 : (tf72T (37/20) (by norm_num)).F (-(lamOf q u)) =
      ∫ t in (0:ℝ)..(tf72T (37/20) (by norm_num)).x₀,
        Real.exp ((lamOf q u) * t) * (tf72T (37/20) (by norm_num)).f t := by
    rw [TestFn_F_eq_integral]
    exact intervalIntegral.integral_congr (fun t _ => by
      rw [show -((-(lamOf q u)) * t) = (lamOf q u) * t by ring])
  have hF2 : (tf72T (37/20) (by norm_num)).F (lamOf q ρ₁ - lamOf q u) =
      ∫ t in (0:ℝ)..(tf72T (37/20) (by norm_num)).x₀,
        Real.exp ((lamOf q u - lamOf q ρ₁) * t) * (tf72T (37/20) (by norm_num)).f t := by
    rw [TestFn_F_eq_integral]
    exact intervalIntegral.integral_congr (fun t _ => by
      rw [show -(((lamOf q ρ₁ - lamOf q u)) * t)
        = (lamOf q u - lamOf q ρ₁) * t by ring])
  have hF0 : (tf72T (37/20) (by norm_num)).F 0 =
      ∫ t in (0:ℝ)..(tf72T (37/20) (by norm_num)).x₀, (tf72T (37/20) (by norm_num)).f t := by
    rw [TestFn_F_eq_integral]
    exact intervalIntegral.integral_congr (fun t _ => by
      rw [zero_mul, neg_zero, Real.exp_zero, one_mul])
  rw [show lamOf q ((ρ₁.re : ℝ) : ℂ) = lamOf q ρ₁ from by
    simp [lamOf, Complex.ofReal_re]] at hmain
  have hmain' : 0 ≤ 2 * (tf72T (37/20) (by norm_num)).F (-(lamOf q u))
      - 2 * (tf72T (37/20) (by norm_num)).F (lamOf q ρ₁ - lamOf q u)
      - (tf72T (37/20) (by norm_num)).F 0
      + (tf72T (37/20) (by norm_num)).f 0 * (2*c + 4*(1/5000)) := by
    rw [hF1, hF2, hF0]
    simpa only [mul_comm ((tf72T (37/20) (by norm_num)).f 0) (2 * c + 4 * (1 / 5000))] using hmain
  exact hmain'

/-! ## The certificate rows (non-real second zero) -/

theorem row_thr (p : ℝ × ℝ) (hp : p ∈ fmRows) :
    ∃ q₀ : ℕ, ∀ q : ℕ, q₀ ≤ q → ∀ [NeZero q] (χ₁ : DirichletCharacter ℂ q) (ρ₁ ρ₀ : ℂ),
      IsMin1WideAt 10 χ₁ ρ₁ → χ₁ ^ 2 = 1 → χ₁ ≠ 1 → ρ₁.im = 0 → IsZ χ₁ ρ₁ → IsZ χ₁ ρ₀ →
      ρ₀ ≠ ρ₁ → ρ₀.im ≠ 0 → lamOf q ρ₁ ≤ p.1 → p.2 ≤ lamOf q ρ₀ := by
  obtain ⟨a, K, v, ha, hK, hp2v, h88, h86, h83⟩ :=
    lam0w.table7_p3_certs p (fmRows_mem_hbTable7 p hp)
  have hp1v : p.1 ≤ v :=
    le_trans (lam0w.table7_rows_facts.1 p (fmRows_mem_hbTable7 p hp)).2.2.2.2 hp2v
  have hp1nn : 0 ≤ p.1 := (lam0w.table7_rows_facts.1 p (fmRows_mem_hbTable7 p hp)).1
  obtain ⟨q₀, hq₀⟩ := cert_nonreal p a K v ha hK hp1nn hp1v h88 h86 h83
  exact ⟨q₀, fun q hq _ χ₁ ρ₁ ρ₀ hw hsq hχ1 him1 hZ1 hZ0 hne hρ0im hlo =>
    le_trans hp2v (hq₀ q hq χ₁ ρ₁ ρ₀ hw hsq hχ1 him1 hZ1 hZ0 hne hρ0im hlo)⟩

theorem cert_rows : ∃ q₀ : ℕ, ∀ p ∈ fmRows, ∀ q : ℕ, q₀ ≤ q →
    ∀ [NeZero q] (χ₁ : DirichletCharacter ℂ q) (ρ₁ ρ₀ : ℂ),
      IsMin1WideAt 10 χ₁ ρ₁ → χ₁ ^ 2 = 1 → χ₁ ≠ 1 → ρ₁.im = 0 → IsZ χ₁ ρ₁ → IsZ χ₁ ρ₀ →
      ρ₀ ≠ ρ₁ → ρ₀.im ≠ 0 → lamOf q ρ₁ ≤ p.1 → p.2 ≤ lamOf q ρ₀ := by
  obtain ⟨q1, h1⟩ := row_thr ((1/10 : ℝ), (276/100 : ℝ)) (by simp [fmRows])
  obtain ⟨q2, h2⟩ := row_thr ((12/100 : ℝ), (256/100 : ℝ)) (by simp [fmRows])
  obtain ⟨q3, h3⟩ := row_thr ((14/100 : ℝ), (239/100 : ℝ)) (by simp [fmRows])
  obtain ⟨q4, h4⟩ := row_thr ((16/100 : ℝ), (225/100 : ℝ)) (by simp [fmRows])
  obtain ⟨q5, h5⟩ := row_thr ((18/100 : ℝ), (212/100 : ℝ)) (by simp [fmRows])
  obtain ⟨q6, h6⟩ := row_thr ((20/100 : ℝ), (201/100 : ℝ)) (by simp [fmRows])
  obtain ⟨q7, h7⟩ := row_thr ((25/100 : ℝ), (177/100 : ℝ)) (by simp [fmRows])
  obtain ⟨q8, h8⟩ := row_thr ((30/100 : ℝ), (158/100 : ℝ)) (by simp [fmRows])
  obtain ⟨q9, h9⟩ := row_thr ((35/100 : ℝ), (142/100 : ℝ)) (by simp [fmRows])
  obtain ⟨q10, h10⟩ := row_thr ((2/5 : ℝ), (129/100 : ℝ)) (by simp [fmRows])
  refine ⟨max (max (max (max (max (max (max (max (max q1 q2) q3) q4) q5) q6) q7) q8) q9) q10, ?_⟩
  intro p hp q hq
  fin_cases hp <;>
    (first
      | exact h1 q (by omega)
      | exact h2 q (by omega)
      | exact h3 q (by omega)
      | exact h4 q (by omega)
      | exact h5 q (by omega)
      | exact h6 q (by omega)
      | exact h7 q (by omega)
      | exact h8 q (by omega)
      | exact h9 q (by omega)
      | exact h10 q (by omega))

/-! ## The theorem -/

theorem lam0_rows_fmethod : ∃ q₀ : ℕ, ∀ q : ℕ, q₀ ≤ q → ∀ [NeZero q]
    (χ₁ : DirichletCharacter ℂ q) (ρ₁ : ℂ),
    Work.ZeroFreeTables.IsMin1WideAt 10 χ₁ ρ₁ → χ₁ ^ 2 = 1 → ρ₁.im = 0 →
    ∀ p ∈ ([((1/10 : ℝ), (276/100 : ℝ)), ((12/100 : ℝ), (256/100 : ℝ)), ((14/100 : ℝ), (239/100 : ℝ)), ((16/100 : ℝ), (225/100 : ℝ)), ((18/100 : ℝ), (212/100 : ℝ)), ((20/100 : ℝ), (201/100 : ℝ)), ((25/100 : ℝ), (177/100 : ℝ)), ((30/100 : ℝ), (158/100 : ℝ)), ((35/100 : ℝ), (142/100 : ℝ)), ((2/5 : ℝ), (129/100 : ℝ))] : List (ℝ × ℝ)),
      Work.LinnikContract.lamOf q ρ₁ ≤ p.1 → Work.LinnikContract.Lam0Bound χ₁ ρ₁ p.2 := by
  obtain ⟨c, hc0, hcle, δ, hδ0, hδ1, q52, h52⟩ := Table4.l52HypRealQuarter
  have hprov : ∀ (q : ℕ), q52 ≤ q → ∀ [NeZero q] (χ : DirichletCharacter ℂ q) [NeZero χ.conductor],
      χ ≠ 1 → χ ^ 2 = 1 → Commons.NumberTheory.Linnik.L52Hyp χ c (1/5000) δ :=
    fun q hq _ χ _ hχ hsq => h52 q hq χ hχ hsq (1/5000) (by norm_num) (by norm_num)
  obtain ⟨qS6, hS6⟩ := s6_real_37 c δ hcle hδ0 hδ1 q52 hprov
  obtain ⟨qG, hG⟩ := guards δ hδ0
  obtain ⟨q82, hq82⟩ := Table4.HB82
  obtain ⟨qrz, hqrz⟩ := HBRepZero84_proof
  obtain ⟨qC, hqC⟩ := cert_rows
  refine ⟨max (max (max (max (max qS6 qG) q82) qrz) qC) 2, ?_⟩
  intro q hq _inst χ₁ ρ₁ hwide hsq him0 p hp hlam1
  have hq2 : 2 ≤ q := by omega
  have hpF : p ∈ fmRows := hp
  have hqS6le : qS6 ≤ q := by omega
  have hqGle : qG ≤ q := by omega
  have hq82le : q82 ≤ q := by omega
  have hqrzle : qrz ≤ q := by omega
  have hqCle : qC ≤ q := by omega
  have hZ1 : IsZ χ₁ ρ₁ := isMin1_isZ hwide.1
  have hχ1 : χ₁ ≠ 1 := isZ_ne_one hZ1
  have hzm1 : zeroMult χ₁ ρ₁ ≠ 0 := isZ_mult_ne_zero hZ1
  have hlam1pos : 0 < lamOf q ρ₁ := by
    have hstrip := zeroMult_strip hχ1 hzm1
    have hlogq : 0 < Real.log (q : ℝ) := Real.log_pos (by exact_mod_cast (by omega : 1 < q))
    rw [lamOf]
    exact mul_pos (by linarith [hstrip.2]) hlogq
  refine lam0Bound_of_parts ?_ ?_
  · intro hm
    have h1294 : 1294/1000 ≤ lamOf q ρ₁ := hqrz q hqrzle χ₁ ρ₁ hwide hsq him0 hm
    have hp1le : p.1 ≤ 2/5 := fmRows_le_two_fifths p hpF
    linarith
  · intro ρ hZρ hneρ _hconj
    have hzρ : zeroMult χ₁ ρ ≠ 0 := isZ_mult_ne_zero hZρ
    have himρ : |ρ.im| ≤ 1 := hZρ.2.2
    obtain ⟨u, hzu, huim, hune, hule, hminu⟩ :=
      Work.LinnikAreas.boxMaxZeroH hq2 χ₁ ρ₁ ρ (H := 1) le_rfl hzρ himρ hneρ
    have hZu : IsZ χ₁ u := ⟨hχ1, hzu, huim⟩
    suffices p.2 ≤ lamOf q u by linarith
    by_contra hμ
    by_cases hu0 : u.im = 0
    · by_cases h15 : lamOf q ρ₁ ≤ 1/5
      · have hmult1 : zeroMult χ₁ ρ₁ = 1 := by
          have h1 : 1 ≤ zeroMult χ₁ ρ₁ := Nat.one_le_iff_ne_zero.mpr hzm1
          by_contra hne
          have h2 : 2 ≤ zeroMult χ₁ ρ₁ := by omega
          have h3 : 1294/1000 ≤ lamOf q ρ₁ := hqrz q hqrzle χ₁ ρ₁ hwide hsq him0 h2
          linarith
        obtain ⟨hg3, hg1, hg2, hgp1, hgp2, hgc1, hgc2⟩ := hG q hqGle
        have hcon : lamOf q u < p.2 := not_le.mp hμ
        have hu12 : lamOf q u ≤ 12 := by
          have h276 : p.2 ≤ 276/100 := fmRows_le_276 p hpF
          linarith
        have hcapp : lamOf q u ≤ Real.log (Real.log (Real.log (q : ℝ))) / 3 := by linarith
        have hs6 := hS6 q hqS6le χ₁ ρ₁ u hwide hsq him0 hmult1 hZu hune hu0 hminu h15 hu12
          hcapp hg1 hg2 hgp1 hgp2 hgc1
        have hcert := cert_real p hpF
        have hmono : 2 * (tf72T (37/20) (by norm_num)).F (-(lamOf q u))
            - 2 * (tf72T (37/20) (by norm_num)).F (lamOf q ρ₁ - lamOf q u)
            ≤ 2 * (tf72T (37/20) (by norm_num)).F (-(p.2))
              - 2 * (tf72T (37/20) (by norm_num)).F (p.1 - p.2) := by
          have h1 := TestFn_E_mono (tf72T (37/20) (by norm_num)) (le_of_lt hlam1pos)
            (le_of_lt hcon) hlam1
          linarith
        have hconst : 2*c + 4*(1/5000) ≤ 1/4 + 4 * (1/4000) := by linarith
        have hf0 : 0 < (tf72T (37/20) (by norm_num)).f 0 :=
          (tf72T (37/20) (by norm_num)).f0_pos
        have hmul : (tf72T (37/20) (by norm_num)).f 0 * (2*c + 4*(1/5000))
            ≤ (tf72T (37/20) (by norm_num)).f 0 * (1/4 + 4 * (1/4000)) :=
          mul_le_mul_of_nonneg_left hconst hf0.le
        linarith [hs6, hcert, hmono, hmul]
      · have hlt : (1:ℝ)/5 < lamOf q ρ₁ := not_le.mp h15
        have h82 := (hq82 q hq82le χ₁ ρ₁ hwide hsq hχ1 him0 hZ1).2 u hZu hune hu0
          (fun z hZz hnez => hminu z (isZ_mult_ne_zero hZz) hZz.2.2 hnez)
        have hp2 : p.2 ≤ 2293/1000 := fmRows_small p hpF (by linarith)
        linarith
    · exact hμ (hqC p hpF q hqCle χ₁ ρ₁ u hwide hsq hχ1 him0 hZ1 hZu hune hu0 hlam1)

end

end Work.ZeroFreeTables
