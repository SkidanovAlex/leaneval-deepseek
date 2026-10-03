import Mathlib
import Submission.Commons.NumberTheory.DirichletCharacter.exists_odd_character_mod_four
import Submission.Commons.NumberTheory.DirichletCharacter.chebyshevPsiChi_explicit_formula_mult
import Submission.Commons.NumberTheory.LSeries.exists_zero_free_region_LFunction_chi4_all_t
import Submission.Commons.NumberTheory.DirichletCharacter.completedL_zeroSum_inv_abs_le
import Submission.Commons.NumberTheory.DirichletCharacter.lFunction_zeroSet_box_finite
import Submission.Commons.NumberTheory.DirichletCharacter.logDeriv_completedLFunction_conj
import Submission.Commons.NumberTheory.DirichletCharacter.completedLFunction_zeroNearHeight
import Submission.Commons.Analysis.Asymptotics.poly_mul_exp_neg_sqrtLog_le
import Mathlib.Algebra.Order.Star.Real
import Mathlib.Analysis.SpecialFunctions.Log.Basic
import Submission.Commons.NumberTheory.AbelSummation.sum_div_abel_identity
import Submission.Commons.NumberTheory.FriedlanderIwaniec.sum_div_log_abel_identity
import Submission.Commons.NumberTheory.Zeta.summable_vonMangoldt_div_rpow
import Submission.Commons.NumberTheory.Zeta.summable_vonMangoldt_mul_rpow
import Mathlib.NumberTheory.LSeries.DirichletContinuation
import Submission.Commons.NumberTheory.Chebyshev.cumulativePrimePowerLeSqrt
import Submission.Commons.Analysis.InfiniteSum.partialDivSumLeOfCumulativeSqrt

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false

set_option autoImplicit false
set_option maxHeartbeats 4000000

attribute [local instance] Classical.propDecidable

open Complex Finset Filter MeasureTheory
open scoped BigOperators Topology

namespace Commons.NumberTheory.DirichletCharacter

lemma chi4Fun_eq_zmod (a : ZMod 4) : chi4Fun a = ((ZMod.χ₄ a : ℤ) : ℂ) := by
  rcases zmod_four_eq a with rfl | rfl | rfl | rfl
  · simp [chi4Fun_zero, show ZMod.χ₄ (0:ZMod 4) = 0 from by decide]
  · simp [chi4Fun_one]
  · simp [chi4Fun_two, show ZMod.χ₄ (2:ZMod 4) = 0 from by decide]
  · simp [chi4Fun_three, show ZMod.χ₄ (3:ZMod 4) = -1 from by decide]

lemma isUnit_three_four : IsUnit (3 : ZMod 4) := by
  rw [isUnit_iff_exists_inv]; exact ⟨3, by decide⟩

lemma chi4_apply_three : chi4 (3 : ZMod 4) = -1 := by
  rw [chi4_apply, chi4Fun_three]

lemma chi4_ne_one' : chi4 ≠ (1 : DirichletCharacter ℂ 4) := by
  intro h
  have h1 : chi4 (3 : ZMod 4) = (1 : DirichletCharacter ℂ 4) (3 : ZMod 4) := by rw [h]
  rw [chi4_apply_three, MulChar.one_apply isUnit_three_four] at h1
  norm_num at h1

theorem chi4_isPrimitive : chi4.IsPrimitive := by
  rw [DirichletCharacter.isPrimitive_def]
  have hdvd : chi4.conductor ∣ 4 := DirichletCharacter.conductor_dvd_level chi4
  have hne1 : chi4.conductor ≠ 1 := by
    intro h
    have : chi4 = (1 : DirichletCharacter ℂ 4) :=
      (DirichletCharacter.eq_one_iff_conductor_eq_one).mpr h
    exact chi4_ne_one' this
  have hne2 : chi4.conductor ≠ 2 := by
    intro h
    have hfac : DirichletCharacter.FactorsThrough chi4 2 := by
      rw [← h]; exact DirichletCharacter.conductor_mem_conductorSet chi4
    obtain ⟨hd, χ₀, hχ⟩ := hfac
    have h1 : (DirichletCharacter.changeLevel hd χ₀) ((3:ℤ) : ZMod 4)
        = χ₀ ((3:ℤ) : ZMod 2) :=
      DirichletCharacter.changeLevel_eq_cast_of_dvd' (χ := χ₀) hd (by norm_num)
    have h2 : χ₀ (((3:ℤ)) : ZMod 2) = (1:ℂ) := by
      have : (((3:ℤ)) : ZMod 2) = 1 := by decide
      rw [this, MulChar.map_one]
    have h3 : chi4 (3 : ZMod 4) = 1 := by
      rw [hχ]
      exact h1.trans h2
    rw [chi4_apply_three] at h3
    norm_num at h3
  obtain ⟨n, hn, hc⟩ : ∃ n ≤ 2, chi4.conductor = 2 ^ n :=
    (Nat.dvd_prime_pow (p := 2) (by norm_num)).mp (by simpa using hdvd)
  interval_cases n
  · exact absurd hc hne1
  · exact absurd hc hne2
  · rw [hc]; norm_num


private lemma norm_finsum_le' {α : Type*} {f : α → ℂ} (hf : Function.HasFiniteSupport f) :
    ‖∑ᶠ a, f a‖ ≤ ∑ᶠ a, ‖f a‖ := by
  classical
  have hfin : (Function.support f).Finite := hf
  have hsub : Function.support (fun a => ‖f a‖) ⊆ ↑hfin.toFinset := by
    rw [show Function.support (fun a => ‖f a‖) = Function.support f by
      ext a; simp [Function.mem_support]]
    exact le_of_eq hfin.coe_toFinset.symm
  rw [finsum_eq_sum_of_support_subset f (s := hfin.toFinset) (le_of_eq hfin.coe_toFinset.symm),
      finsum_eq_sum_of_support_subset (fun a => ‖f a‖) (s := hfin.toFinset) hsub]
  exact norm_sum_le _ _

private noncomputable def PsiC (x : ℝ) : ℂ :=
  ∑ n ∈ Finset.Icc 1 ⌊x⌋₊, chi4 ((n : ℕ) : ZMod 4) * ((ArithmeticFunction.vonMangoldt n : ℝ) : ℂ)

private noncomputable def ZSc (x T : ℝ) : ℂ :=
  ∑ᶠ ρ : ℂ, ((analyticOrderNatAt (DirichletCharacter.completedLFunction chi4) ρ : ℕ) : ℂ) *
    (if 0 < ρ.re ∧ ρ.re < 1 ∧ |ρ.im| ≤ T then (x : ℂ) ^ ρ / ρ else 0)

private noncomputable def Wc (T : ℝ) (ρ : ℂ) : ℝ :=
  ((analyticOrderNatAt (DirichletCharacter.completedLFunction chi4) ρ : ℕ) : ℝ) *
    (if 0 < ρ.re ∧ ρ.re < 1 ∧ |ρ.im| ≤ T then (‖ρ‖)⁻¹ else 0)

private lemma chi4_zerosum_le {c C₂ x T : ℝ} (hc : 0 < c)
    (hZFR : ∀ σ t : ℝ, 1 - c / (Real.log (|t| + 2)) ^ 9 ≤ σ →
      DirichletCharacter.LFunction chi4 ((σ : ℂ) + (t : ℂ) * Complex.I) ≠ 0)
    (hZS : ∀ T : ℝ, 2 ≤ T → (∑ᶠ ρ : ℂ, Wc T ρ) ≤ C₂ * (Real.log (4 * (T + 3)) + 2) ^ 2)
    (hx : 1 ≤ x) (hT : 2 ≤ T) :
    ‖ZSc x T‖ ≤ x ^ (1 - c / (Real.log (T + 2)) ^ 9) * (∑ᶠ ρ : ℂ, Wc T ρ) := by
  have hxpos : 0 < x := by linarith
  have hT2pos : 0 < T + 2 := by linarith
  have hlogT2pos : 0 < Real.log (T + 2) := Real.log_pos (by linarith)
  set δ : ℝ := c / (Real.log (T + 2)) ^ 9 with hδdef
  have hδpos : 0 < δ := by rw [hδdef]; positivity
  have hfin : ({ρ : ℂ | DirichletCharacter.LFunction chi4 ρ = 0 ∧ 0 < ρ.re ∧ ρ.re < 1 ∧ |ρ.im| ≤ T}).Finite :=
    lFunction_zeroSet_box_finite chi4 chi4_ne_one' chi4_isPrimitive T
  have hLzero : ∀ ρ : ℂ, 0 < ρ.re →
      analyticOrderNatAt (DirichletCharacter.completedLFunction chi4) ρ ≠ 0 → DirichletCharacter.LFunction chi4 ρ = 0 := by
    intro ρ hre hm
    have h1 : DirichletCharacter.completedLFunction chi4 ρ = 0 := apply_eq_zero_of_analyticOrderNatAt_ne_zero hm
    have hγ : DirichletCharacter.gammaFactor chi4 ρ ≠ 0 := gammaFactor_ne_zero_of_pos_re chi4 hre
    have h2 : DirichletCharacter.completedLFunction chi4 ρ = DirichletCharacter.LFunction chi4 ρ * DirichletCharacter.gammaFactor chi4 ρ :=
      completedLFunction_eq_gammaFactor_mul chi4 (by norm_num) hγ
    rw [h2] at h1
    exact (mul_eq_zero.mp h1).resolve_right hγ
  have hsupp1 : Function.support (fun ρ : ℂ => ((analyticOrderNatAt (DirichletCharacter.completedLFunction chi4) ρ : ℕ) : ℂ) *
      (if 0 < ρ.re ∧ ρ.re < 1 ∧ |ρ.im| ≤ T then (x : ℂ) ^ ρ / ρ else 0)) ⊆
      {ρ : ℂ | DirichletCharacter.LFunction chi4 ρ = 0 ∧ 0 < ρ.re ∧ ρ.re < 1 ∧ |ρ.im| ≤ T} := by
    intro ρ hρ
    rw [Function.mem_support] at hρ
    by_cases hind : 0 < ρ.re ∧ ρ.re < 1 ∧ |ρ.im| ≤ T
    · refine ⟨hLzero ρ hind.1 ?_, hind.1, hind.2.1, hind.2.2⟩
      intro hm
      exact hρ (by simp [hind, hm])
    · exact absurd (by simpa [hind] using hρ) hind
  have hfs1 : Function.HasFiniteSupport (fun ρ : ℂ => ((analyticOrderNatAt (DirichletCharacter.completedLFunction chi4) ρ : ℕ) : ℂ) *
      (if 0 < ρ.re ∧ ρ.re < 1 ∧ |ρ.im| ≤ T then (x : ℂ) ^ ρ / ρ else 0)) :=
    hfin.subset hsupp1
  have hsupp2 : Function.support (Wc T) ⊆
      {ρ : ℂ | DirichletCharacter.LFunction chi4 ρ = 0 ∧ 0 < ρ.re ∧ ρ.re < 1 ∧ |ρ.im| ≤ T} := by
    intro ρ hρ
    rw [Function.mem_support] at hρ
    by_cases hind : 0 < ρ.re ∧ ρ.re < 1 ∧ |ρ.im| ≤ T
    · refine ⟨hLzero ρ hind.1 ?_, hind.1, hind.2.1, hind.2.2⟩
      intro hm
      exact hρ (by simp [Wc, hind, hm])
    · exact absurd (by simpa [Wc, hind] using hρ) hind
  have hfs2 : Function.HasFiniteSupport (Wc T) := hfin.subset hsupp2
  have hfs2' : Function.HasFiniteSupport (fun ρ : ℂ => x ^ (1 - δ) * Wc T ρ) := by
    refine hfs2.subset ?_
    intro ρ hρ
    rw [Function.mem_support] at hρ ⊢
    intro h0
    exact hρ (by rw [h0, mul_zero])
  have hfs1' : Function.HasFiniteSupport
      (fun ρ : ℂ => ‖((analyticOrderNatAt (DirichletCharacter.completedLFunction chi4) ρ : ℕ) : ℂ) *
        (if 0 < ρ.re ∧ ρ.re < 1 ∧ |ρ.im| ≤ T then (x : ℂ) ^ ρ / ρ else 0)‖) := by
    show (Function.support (fun ρ : ℂ => ‖((analyticOrderNatAt (DirichletCharacter.completedLFunction chi4) ρ : ℕ) : ℂ) *
        (if 0 < ρ.re ∧ ρ.re < 1 ∧ |ρ.im| ≤ T then (x : ℂ) ^ ρ / ρ else 0)‖)).Finite
    rw [show Function.support (fun ρ : ℂ => ‖((analyticOrderNatAt (DirichletCharacter.completedLFunction chi4) ρ : ℕ) : ℂ) *
        (if 0 < ρ.re ∧ ρ.re < 1 ∧ |ρ.im| ≤ T then (x : ℂ) ^ ρ / ρ else 0)‖)
        = Function.support (fun ρ : ℂ => ((analyticOrderNatAt (DirichletCharacter.completedLFunction chi4) ρ : ℕ) : ℂ) *
        (if 0 < ρ.re ∧ ρ.re < 1 ∧ |ρ.im| ≤ T then (x : ℂ) ^ ρ / ρ else 0)) by
      ext ρ; simp [Function.mem_support]]
    exact hfs1
  have hpoint : ∀ ρ : ℂ, ‖((analyticOrderNatAt (DirichletCharacter.completedLFunction chi4) ρ : ℕ) : ℂ) *
      (if 0 < ρ.re ∧ ρ.re < 1 ∧ |ρ.im| ≤ T then (x : ℂ) ^ ρ / ρ else 0)‖
      ≤ x ^ (1 - δ) * Wc T ρ := by
    intro ρ
    by_cases hind : 0 < ρ.re ∧ ρ.re < 1 ∧ |ρ.im| ≤ T
    · by_cases hm : analyticOrderNatAt (DirichletCharacter.completedLFunction chi4) ρ = 0
      · rw [if_pos hind, show Wc T ρ = 0 by simp [Wc, hind, hm]]
        simp [hm]
      · have hL := hLzero ρ hind.1 hm
        have hlt : ρ.re < 1 - c / (Real.log (|ρ.im| + 2)) ^ 9 := by
          by_contra hcon
          have hcon' : 1 - c / (Real.log (|ρ.im| + 2)) ^ 9 ≤ ρ.re := le_of_not_gt hcon
          have hz := hZFR ρ.re ρ.im hcon'
          exact hz (by
            rw [show ((ρ.re : ℂ) + (ρ.im : ℂ) * Complex.I) = ρ from by
              apply Complex.ext <;> simp]
            exact hL)
        have hlogmono : (Real.log (|ρ.im| + 2)) ^ 9 ≤ (Real.log (T + 2)) ^ 9 := by
          have h1 : |ρ.im| + 2 ≤ T + 2 := by linarith [hind.2.2]
          have h2 : (0:ℝ) ≤ Real.log (|ρ.im| + 2) :=
            Real.log_nonneg (by linarith [abs_nonneg ρ.im])
          have h3 : Real.log (|ρ.im| + 2) ≤ Real.log (T + 2) :=
            Real.log_le_log (by linarith [abs_nonneg ρ.im]) h1
          exact pow_le_pow_left₀ h2 h3 9
        have hdenpos : 0 < (Real.log (|ρ.im| + 2)) ^ 9 :=
          pow_pos (Real.log_pos (by linarith [abs_nonneg ρ.im])) 9
        have hδle : δ ≤ c / (Real.log (|ρ.im| + 2)) ^ 9 := by
          rw [hδdef]
          exact div_le_div_of_nonneg_left (le_of_lt hc) hdenpos hlogmono
        have hbound : ρ.re ≤ 1 - δ := by linarith
        have hval : ‖((analyticOrderNatAt (DirichletCharacter.completedLFunction chi4) ρ : ℕ) : ℂ) *
            ((x : ℂ) ^ ρ / ρ)‖
            = ((analyticOrderNatAt (DirichletCharacter.completedLFunction chi4) ρ : ℕ) : ℝ) * (x ^ ρ.re / ‖ρ‖) := by
          rw [norm_mul, Complex.norm_natCast, norm_div,
            Complex.norm_cpow_eq_rpow_re_of_pos hxpos]
        have hxle : x ^ ρ.re ≤ x ^ (1 - δ) := Real.rpow_le_rpow_of_exponent_le hx hbound
        have hmnn : (0:ℝ) ≤ ((analyticOrderNatAt (DirichletCharacter.completedLFunction chi4) ρ : ℕ) : ℝ) :=
          Nat.cast_nonneg _
        rw [if_pos hind, hval, show Wc T ρ = ((analyticOrderNatAt (DirichletCharacter.completedLFunction chi4) ρ : ℕ) : ℝ) * (‖ρ‖)⁻¹ by
          simp [Wc, hind]]
        calc ((analyticOrderNatAt (DirichletCharacter.completedLFunction chi4) ρ : ℕ) : ℝ) * (x ^ ρ.re / ‖ρ‖)
            ≤ ((analyticOrderNatAt (DirichletCharacter.completedLFunction chi4) ρ : ℕ) : ℝ) * (x ^ (1 - δ) / ‖ρ‖) :=
              mul_le_mul_of_nonneg_left (div_le_div_of_nonneg_right hxle (norm_nonneg ρ)) hmnn
          _ = x ^ (1 - δ) * (((analyticOrderNatAt (DirichletCharacter.completedLFunction chi4) ρ : ℕ) : ℝ) * (‖ρ‖)⁻¹) := by
              ring
    · rw [if_neg hind, show Wc T ρ = 0 by simp [Wc, hind]]
      simp
  calc ‖ZSc x T‖
      = ‖∑ᶠ ρ : ℂ, ((analyticOrderNatAt (DirichletCharacter.completedLFunction chi4) ρ : ℕ) : ℂ) *
          (if 0 < ρ.re ∧ ρ.re < 1 ∧ |ρ.im| ≤ T then (x : ℂ) ^ ρ / ρ else 0)‖ := rfl
    _ ≤ ∑ᶠ ρ : ℂ, ‖((analyticOrderNatAt (DirichletCharacter.completedLFunction chi4) ρ : ℕ) : ℂ) *
          (if 0 < ρ.re ∧ ρ.re < 1 ∧ |ρ.im| ≤ T then (x : ℂ) ^ ρ / ρ else 0)‖ :=
        norm_finsum_le' hfs1
    _ ≤ ∑ᶠ ρ : ℂ, x ^ (1 - δ) * Wc T ρ := finsum_le_finsum' hfs1' hfs2' hpoint
    _ = x ^ (1 - δ) * ∑ᶠ ρ : ℂ, Wc T ρ := by rw [mul_finsum' (Wc T) (x ^ (1 - δ)) hfs2]

private lemma chi4_psi_le {c C₁ C₂ : ℝ} (hc : 0 < c)
    (hZFR : ∀ σ t : ℝ, 1 - c / (Real.log (|t| + 2)) ^ 9 ≤ σ →
      DirichletCharacter.LFunction chi4 ((σ : ℂ) + (t : ℂ) * Complex.I) ≠ 0)
    (hZS : ∀ T : ℝ, 2 ≤ T → (∑ᶠ ρ : ℂ, Wc T ρ) ≤ C₂ * (Real.log (4 * (T + 3)) + 2) ^ 2)
    (hEF : ∀ x : ℝ, 2 ≤ x → ∀ T : ℝ, 2 ≤ T → T ≤ x →
      ‖PsiC x + ZSc x T‖ ≤ C₁ * (x * (Real.log x) ^ 2 / T + Real.log x))
    {x T : ℝ} (hx : 2 ≤ x) (hT2 : 2 ≤ T) (hTx : T ≤ x) :
    ‖PsiC x‖ ≤ C₁ * (x * (Real.log x) ^ 2 / T + Real.log x)
      + x ^ (1 - c / (Real.log (T + 2)) ^ 9) * (C₂ * (Real.log (4 * (T + 3)) + 2) ^ 2) := by
  have h1 : ‖PsiC x + ZSc x T‖ ≤ C₁ * (x * (Real.log x) ^ 2 / T + Real.log x) :=
    hEF x hx T hT2 hTx
  have h2 : ‖ZSc x T‖ ≤ x ^ (1 - c / (Real.log (T + 2)) ^ 9) * (∑ᶠ ρ : ℂ, Wc T ρ) :=
    chi4_zerosum_le hc hZFR hZS (by linarith) hT2
  have h3 : x ^ (1 - c / (Real.log (T + 2)) ^ 9) * (∑ᶠ ρ : ℂ, Wc T ρ)
      ≤ x ^ (1 - c / (Real.log (T + 2)) ^ 9) * (C₂ * (Real.log (4 * (T + 3)) + 2) ^ 2) :=
    mul_le_mul_of_nonneg_left (hZS T hT2) (Real.rpow_nonneg (by linarith) _)
  calc ‖PsiC x‖ = ‖(PsiC x + ZSc x T) - ZSc x T‖ := by rw [add_sub_cancel_right]
    _ ≤ ‖PsiC x + ZSc x T‖ + ‖ZSc x T‖ := norm_sub_le _ _
    _ ≤ C₁ * (x * (Real.log x) ^ 2 / T + Real.log x)
        + x ^ (1 - c / (Real.log (T + 2)) ^ 9) * (C₂ * (Real.log (4 * (T + 3)) + 2) ^ 2) :=
        add_le_add h1 (le_trans h2 h3)

private noncomputable def Tf (x : ℝ) : ℝ := Real.exp ((Real.log x) ^ (1/18 : ℝ))

private lemma pow2_mul_rpow {L : ℝ} (hL : 0 < L) (A : ℝ) : L ^ 2 * L ^ A = L ^ (A + 2) := by
  rw [← Real.rpow_natCast L 2, ← Real.rpow_add hL ((2:ℕ):ℝ) A]
  congr 1; push_cast; ring


private lemma mul_rpow {L : ℝ} (hL : 0 < L) (A : ℝ) : L * L ^ A = L ^ (A + 1) := by
  nth_rewrite 1 [← Real.rpow_one L]
  rw [← Real.rpow_add hL 1 A]
  congr 1; ring


private lemma budget_trunc {A C₁ : ℝ} (hC₁ : 0 < C₁) :
    ∀ᶠ x : ℝ in atTop, C₁ * (x * (Real.log x) ^ 2 / Tf x) ≤ (1/4) * (x / (Real.log x) ^ A) := by
  have h1 : Tendsto (fun v : ℝ => v ^ (18 * (A + 2)) * Real.exp (-1 * v)) atTop (nhds 0) :=
    tendsto_rpow_mul_exp_neg_mul_atTop_nhds_zero (18 * (A + 2)) 1 one_pos
  have hu : Tendsto (fun x : ℝ => (Real.log x) ^ (1/18 : ℝ)) atTop atTop :=
    (tendsto_rpow_atTop (by norm_num : (0:ℝ) < 1/18)).comp Real.tendsto_log_atTop
  have h2 : ∀ᶠ x : ℝ in atTop, ((Real.log x) ^ (1/18 : ℝ)) ^ (18 * (A + 2)) *
      Real.exp (-1 * ((Real.log x) ^ (1/18 : ℝ))) ≤ 1 / (4 * C₁) :=
    (h1.comp hu).eventually_le_const (by positivity)
  filter_upwards [h2, Real.tendsto_log_atTop.eventually_ge_atTop 1, Filter.eventually_ge_atTop 2]
    with x h2x hlog1x hx2x
  have hxpos : 0 < x := by linarith
  have hlogpos : 0 < Real.log x := by linarith
  have hTpos : 0 < Tf x := Real.exp_pos _
  have hLpow : ((Real.log x) ^ (1/18 : ℝ)) ^ (18 * (A + 2)) = (Real.log x) ^ (A + 2) := by
    rw [← Real.rpow_mul (le_of_lt hlogpos) (1/18) (18 * (A + 2))]
    congr 1; ring
  have hkey : 4 * C₁ * (Real.log x) ^ (A + 2) ≤ Tf x := by
    have h3 : (Real.log x) ^ (A + 2) / Real.exp ((Real.log x) ^ (1/18 : ℝ)) ≤ 1 / (4 * C₁) := by
      have h2x' := h2x
      rw [show -1 * ((Real.log x) ^ (1/18 : ℝ)) = -((Real.log x) ^ (1/18 : ℝ)) by ring,
        Real.exp_neg, hLpow] at h2x'
      exact h2x'
    have h4 : (Real.log x) ^ (A + 2) ≤ (1 / (4 * C₁)) * Real.exp ((Real.log x) ^ (1/18 : ℝ)) := by
      have h5 := mul_le_mul_of_nonneg_right h3 (le_of_lt (Real.exp_pos ((Real.log x) ^ (1/18 : ℝ))))
      rwa [div_mul_cancel₀ _ (Real.exp_ne_zero _)] at h5
    have h6 := mul_le_mul_of_nonneg_left h4 (le_of_lt (by positivity : (0:ℝ) < 4 * C₁))
    rw [show 4 * C₁ * ((1 / (4 * C₁)) * Real.exp ((Real.log x) ^ (1/18 : ℝ)))
        = Real.exp ((Real.log x) ^ (1/18 : ℝ)) by
      field_simp] at h6
    rwa [Tf]
  rw [show C₁ * (x * (Real.log x) ^ 2 / Tf x) = C₁ * x * (Real.log x) ^ 2 / Tf x by ring,
      show (1/4 : ℝ) * (x / (Real.log x) ^ A) = x / (4 * (Real.log x) ^ A) by ring]
  rw [div_le_iff₀ hTpos, div_mul_eq_mul_div,
      le_div_iff₀ (by have h := Real.rpow_pos_of_pos hlogpos A; positivity)]
  rw [show C₁ * x * (Real.log x) ^ 2 * (4 * (Real.log x) ^ A)
      = x * (4 * C₁ * ((Real.log x) ^ 2 * (Real.log x) ^ A)) by ring]
  rw [pow2_mul_rpow hlogpos A]
  exact mul_le_mul_of_nonneg_left hkey (le_of_lt hxpos)


private lemma budget_log {A C₁ : ℝ} (hC₁ : 0 < C₁) :
    ∀ᶠ x : ℝ in atTop, C₁ * Real.log x ≤ (1/4) * (x / (Real.log x) ^ A) := by
  have h1 : Tendsto (fun x : ℝ => (Real.log x) ^ (A + 1) / x) atTop (nhds 0) := by
    have h := (isLittleO_log_rpow_rpow_atTop (s := 1) (A + 1) one_pos).tendsto_div_nhds_zero
    simpa using h
  have h2 : ∀ᶠ x : ℝ in atTop, (Real.log x) ^ (A + 1) / x ≤ 1 / (4 * C₁) :=
    h1.eventually_le_const (by positivity)
  filter_upwards [h2, Real.tendsto_log_atTop.eventually_ge_atTop 1, Filter.eventually_ge_atTop 2]
    with x h2x hlog1x hx2x
  have hxpos : 0 < x := by linarith
  have hlogpos : 0 < Real.log x := by linarith
  have hLpos : 0 < (Real.log x) ^ A := Real.rpow_pos_of_pos hlogpos A
  have hkey : 4 * C₁ * (Real.log x) ^ (A + 1) ≤ x := by
    have h' := (div_le_iff₀ hxpos).mp h2x
    have h4 : (1 / (4 * C₁)) * x = x / (4 * C₁) := by rw [one_div, inv_mul_eq_div]
    rw [h4] at h'
    have h5 := (le_div_iff₀ (by positivity : (0:ℝ) < 4 * C₁)).mp h'
    nlinarith [h5]
  rw [show (1/4 : ℝ) * (x / (Real.log x) ^ A) = x / (4 * (Real.log x) ^ A) by ring,
      le_div_iff₀ (by positivity)]
  rw [show C₁ * Real.log x * (4 * (Real.log x) ^ A)
      = 4 * C₁ * (Real.log x * (Real.log x) ^ A) by ring,
      mul_rpow hlogpos A]
  exact hkey


private lemma budget_zer {A c C₂ : ℝ} (hA : 0 < A) (hc : 0 < c) (hC₂ : 0 < C₂) :
    ∀ᶠ x : ℝ in atTop, 4 * C₂ * (Real.log x) ^ (1/9 : ℝ) * Real.exp (-(c/512) * Real.sqrt (Real.log x))
        ≤ (1/2) * ((Real.log x) ^ A)⁻¹ := by
  have hc' : 0 < c / 512 := by positivity
  set kA : ℕ := ⌈A⌉₊ with hkA
  have hAkle : A ≤ (kA : ℝ) := Nat.le_ceil A
  have hpoly := Commons.Analysis.Asymptotics.poly_mul_exp_neg_sqrtLog_le (c/512) hc' (kA + 1) (4 * C₂) (by positivity)
  have hexp0 : Tendsto (fun x : ℝ => Real.exp (-(c/1024) * Real.sqrt (Real.log x))) atTop (nhds 0) := by
    have h1 : Tendsto (fun u : ℝ => Real.exp (-(c/1024) * u)) atTop (nhds 0) := by
      have h0 : Tendsto (fun u : ℝ => (c/1024) * u) atTop atTop :=
        Tendsto.const_mul_atTop (by positivity : (0:ℝ) < c/1024) tendsto_id
      have h2 := Real.tendsto_exp_neg_atTop_nhds_zero.comp h0
      rw [show ((fun x : ℝ => Real.exp (-x)) ∘ fun u : ℝ => (c/1024) * u)
            = (fun u : ℝ => Real.exp (-(c/1024) * u)) from by
          funext u; simp [Function.comp, neg_mul]] at h2
      exact h2
    exact h1.comp (Real.tendsto_sqrt_atTop.comp Real.tendsto_log_atTop)
  have hexp1 : ∀ᶠ x : ℝ in atTop,
      Real.exp (-(c/1024) * Real.sqrt (Real.log x)) ≤ 1/2 :=
    hexp0.eventually_le_const (by norm_num)
  filter_upwards [hpoly, hexp1, Real.tendsto_log_atTop.eventually_ge_atTop 1,
    Filter.eventually_ge_atTop 2] with x hpolyx hexp1x hlog1x hx2x
  have hlogpos : 0 < Real.log x := by linarith
  have hexp_le : (Real.log x) ^ (A + 1/9 : ℝ) ≤ (Real.log x) ^ (kA + 1 : ℕ) := by
    rw [show (Real.log x) ^ (kA + 1 : ℕ) = (Real.log x) ^ ((kA + 1 : ℕ) : ℝ) by
      rw [Real.rpow_natCast]]
    apply Real.rpow_le_rpow_of_exponent_le hlog1x
    push_cast
    linarith
  have hgoal : 4 * C₂ * (Real.log x) ^ (A + 1/9 : ℝ)
      * Real.exp (-(c/512) * Real.sqrt (Real.log x)) ≤ 1/2 := by
    have hstep : 4 * C₂ * (Real.log x) ^ (A + 1/9 : ℝ) * Real.exp (-(c/512) * Real.sqrt (Real.log x))
        ≤ 4 * C₂ * (Real.log x) ^ (kA + 1 : ℕ) * Real.exp (-(c/512) * Real.sqrt (Real.log x)) := by
      have hnn : (0:ℝ) ≤ 4 * C₂ * Real.exp (-(c/512) * Real.sqrt (Real.log x)) := by positivity
      calc 4 * C₂ * (Real.log x) ^ (A + 1/9 : ℝ) * Real.exp (-(c/512) * Real.sqrt (Real.log x))
          = (4 * C₂ * Real.exp (-(c/512) * Real.sqrt (Real.log x))) * (Real.log x) ^ (A + 1/9 : ℝ) := by ring
        _ ≤ (4 * C₂ * Real.exp (-(c/512) * Real.sqrt (Real.log x))) * (Real.log x) ^ (kA + 1 : ℕ) :=
            mul_le_mul_of_nonneg_left hexp_le hnn
        _ = 4 * C₂ * (Real.log x) ^ (kA + 1 : ℕ) * Real.exp (-(c/512) * Real.sqrt (Real.log x)) := by ring
    refine le_trans hstep (le_trans hpolyx ?_)
    have heq : -(c / 512 / 2) * Real.sqrt (Real.log x) = -(c / 1024) * Real.sqrt (Real.log x) := by ring
    rw [heq]
    exact hexp1x
  rw [show (1/2 : ℝ) * ((Real.log x) ^ A)⁻¹ = 1 / (2 * (Real.log x) ^ A) by
        field_simp,
      le_div_iff₀ (by positivity : (0:ℝ) < 2 * (Real.log x) ^ A)]
  rw [show 4 * C₂ * (Real.log x) ^ (1/9 : ℝ) * Real.exp (-(c/512) * Real.sqrt (Real.log x))
        * (2 * (Real.log x) ^ A)
      = 2 * (4 * C₂ * ((Real.log x) ^ (1/9 : ℝ) * (Real.log x) ^ A)
        * Real.exp (-(c/512) * Real.sqrt (Real.log x))) by ring,
      show (Real.log x) ^ (1/9 : ℝ) * (Real.log x) ^ A = (Real.log x) ^ (A + 1/9 : ℝ) by
        rw [← Real.rpow_add hlogpos (1/9) A]; congr 1; ring]
  linarith [hgoal]

private lemma geom_facts :
    ∀ᶠ x : ℝ in atTop, 2 ≤ x ∧ (2:ℝ) ≤ Tf x ∧ Tf x ≤ x ∧ 1 ≤ Real.log x
      ∧ 5 ≤ (Real.log x) ^ (1/18 : ℝ) := by
  have hu_tend : Tendsto (fun x : ℝ => (Real.log x) ^ (1/18 : ℝ)) atTop atTop :=
    (tendsto_rpow_atTop (by norm_num : (0:ℝ) < 1/18)).comp Real.tendsto_log_atTop
  filter_upwards [hu_tend.eventually_ge_atTop 5, Real.tendsto_log_atTop.eventually_ge_atTop 1,
    Filter.eventually_ge_atTop 2] with x hu5x hlog1x hx2x
  have hxpos : 0 < x := by linarith
  have hlogpos : 0 < Real.log x := by linarith
  refine ⟨hx2x, ?_, ?_, hlog1x, hu5x⟩
  · rw [show Tf x = Real.exp ((Real.log x) ^ (1/18 : ℝ)) from rfl,
        ← Real.log_le_iff_le_exp (by norm_num : (0:ℝ) < 2)]
    have hlog2 : Real.log 2 ≤ 5 := by nlinarith [Real.log_two_lt_d9]
    linarith
  · rw [show Tf x = Real.exp ((Real.log x) ^ (1/18 : ℝ)) from rfl,
        ← Real.log_le_log_iff (Real.exp_pos ((Real.log x) ^ (1/18 : ℝ))) hxpos, Real.log_exp]
    calc (Real.log x) ^ (1/18 : ℝ) ≤ (Real.log x) ^ (1 : ℝ) :=
          Real.rpow_le_rpow_of_exponent_le hlog1x (by norm_num)
      _ = Real.log x := Real.rpow_one _

private lemma chi4_psi_eventually {A c C₁ C₂ : ℝ} (hA : 0 < A) (hc : 0 < c)
    (hC₁ : 0 < C₁) (hC₂ : 0 < C₂)
    (hZFR : ∀ σ t : ℝ, 1 - c / (Real.log (|t| + 2)) ^ 9 ≤ σ →
      DirichletCharacter.LFunction chi4 ((σ : ℂ) + (t : ℂ) * Complex.I) ≠ 0)
    (hZS : ∀ T : ℝ, 2 ≤ T → (∑ᶠ ρ : ℂ, Wc T ρ) ≤ C₂ * (Real.log (4 * (T + 3)) + 2) ^ 2)
    (hEF : ∀ x : ℝ, 2 ≤ x → ∀ T : ℝ, 2 ≤ T → T ≤ x →
      ‖PsiC x + ZSc x T‖ ≤ C₁ * (x * (Real.log x) ^ 2 / T + Real.log x)) :
    ∀ᶠ x : ℝ in atTop, ‖PsiC x‖ ≤ x / (Real.log x) ^ A := by
  filter_upwards [budget_trunc (A := A) hC₁, budget_log (A := A) hC₁,
    budget_zer (A := A) hA hc hC₂, geom_facts] with x hB1 hB2 hB3 ⟨hx2x, hTge2, hTlex, hlog1x, hu5x⟩
  have hxpos : 0 < x := by linarith
  have hlogpos : 0 < Real.log x := by linarith
  have hlogT : Real.log (Tf x) = (Real.log x) ^ (1/18 : ℝ) := by rw [Tf, Real.log_exp]
  -- the ZFR saving
  have hδsave : (c / 512) * Real.sqrt (Real.log x) ≤ (c / (Real.log (Tf x + 2)) ^ 9) * Real.log x := by
    have hlogTpos : 0 < Real.log (Tf x) := by rw [hlogT]; linarith
    have hlog2le : Real.log 2 ≤ Real.log (Tf x) := Real.log_le_log (by norm_num) hTge2
    have h1 : Real.log (Tf x + 2) ≤ 2 * Real.log (Tf x) := by
      have hle : Tf x + 2 ≤ 2 * Tf x := by linarith
      have h2 : Real.log (Tf x + 2) ≤ Real.log (2 * Tf x) := Real.log_le_log (by linarith) hle
      rw [Real.log_mul (by norm_num)
        (ne_of_gt (show (0:ℝ) < Tf x from Real.exp_pos _))] at h2
      linarith
    have hpos : 0 < Real.log (Tf x + 2) := Real.log_pos (by linarith)
    have h2 : (Real.log (Tf x + 2)) ^ 9 ≤ 512 * Real.sqrt (Real.log x) := by
      have h3 : (Real.log (Tf x + 2)) ^ 9 ≤ (2 * Real.log (Tf x)) ^ 9 :=
        pow_le_pow_left₀ (le_of_lt hpos) h1 9
      have h4 : (2 * Real.log (Tf x)) ^ 9 = 512 * ((Real.log x) ^ (1/18 : ℝ)) ^ 9 := by
        rw [mul_pow, hlogT]; norm_num
      have h5 : ((Real.log x) ^ (1/18 : ℝ)) ^ 9 = Real.sqrt (Real.log x) := by
        rw [← Real.rpow_natCast ((Real.log x) ^ (1/18 : ℝ)) 9,
            ← Real.rpow_mul (le_of_lt hlogpos) (1/18) ((9:ℕ):ℝ)]
        rw [show (1/18:ℝ) * ((9:ℕ):ℝ) = 1/2 by norm_num, Real.sqrt_eq_rpow]
      rw [h4, h5] at h3
      exact h3
    have h6 : c / (512 * Real.sqrt (Real.log x)) ≤ c / (Real.log (Tf x + 2)) ^ 9 := by
      apply div_le_div_of_nonneg_left (le_of_lt hc)
      · positivity
      · exact h2
    have hs2 : Real.sqrt (Real.log x) * Real.sqrt (Real.log x) = Real.log x :=
      Real.mul_self_sqrt (le_of_lt hlogpos)
    have e1 : c / (512 * Real.sqrt (Real.log x)) * Real.log x
        = c * Real.log x / (512 * Real.sqrt (Real.log x)) := by ring
    have e2 : c / (Real.log (Tf x + 2)) ^ 9 * Real.log x
        = c * Real.log x / (Real.log (Tf x + 2)) ^ 9 := by ring
    have h7 : (c / 512) * Real.sqrt (Real.log x)
        = c * Real.log x / (512 * Real.sqrt (Real.log x)) := by
      rw [div_mul_eq_mul_div, div_eq_div_iff (by positivity) (by positivity)]
      nlinarith [hs2]
    rw [h7, e2]
    have hmm := mul_le_mul_of_nonneg_right h6 (le_of_lt hlogpos)
    rw [e1, e2] at hmm
    exact hmm
  have hmain := chi4_psi_le hc hZFR hZS hEF hx2x hTge2 hTlex
  have hzpart : x ^ (1 - c / (Real.log (Tf x + 2)) ^ 9) * (C₂ * (Real.log (4 * (Tf x + 3)) + 2) ^ 2)
      ≤ 4 * C₂ * (Real.log x) ^ (1/9 : ℝ) * x * Real.exp (-(c/512) * Real.sqrt (Real.log x)) := by
    have hxpow : x ^ (1 - c / (Real.log (Tf x + 2)) ^ 9)
        = x * Real.exp (-(c / (Real.log (Tf x + 2)) ^ 9) * Real.log x) := by
      rw [Real.rpow_def_of_pos hxpos,
        show Real.log x * (1 - c / (Real.log (Tf x + 2)) ^ 9)
          = Real.log x + -(c / (Real.log (Tf x + 2)) ^ 9) * Real.log x by ring,
        Real.exp_add, Real.exp_log hxpos]
    rw [hxpow]
    have hexple : Real.exp (-(c / (Real.log (Tf x + 2)) ^ 9) * Real.log x)
        ≤ Real.exp (-(c/512) * Real.sqrt (Real.log x)) := by
      apply Real.exp_le_exp.mpr
      linarith [hδsave]
    have hlog16 : Real.log 16 + 2 ≤ 5 := by
      rw [show (16:ℝ) = 2^4 by norm_num, Real.log_pow]
      push_cast
      nlinarith [Real.log_two_lt_d9]
    have hlog4T : Real.log (4 * (Tf x + 3)) + 2 ≤ 2 * Real.log (Tf x) := by
      have h1 : Real.log (4 * (Tf x + 3)) ≤ Real.log (Tf x) + Real.log 16 := by
        have hle : 4 * (Tf x + 3) ≤ 16 * Tf x := by linarith
        have h2 := Real.log_le_log (by positivity) hle
        rw [Real.log_mul (by norm_num)
          (ne_of_gt (show (0:ℝ) < Tf x from Real.exp_pos _))] at h2
        nlinarith [h2]
      have h3 : Real.log 16 + 2 ≤ Real.log (Tf x) := by
        rw [hlogT]; linarith
      linarith
    have hlog4Tpos : 0 < Real.log (4 * (Tf x + 3)) + 2 := by
      have h1 : 0 ≤ Real.log (4 * (Tf x + 3)) :=
        Real.log_nonneg (by have h := Real.exp_pos ((Real.log x) ^ (1/18 : ℝ)); rw [Tf]; nlinarith)
      linarith
    have hsq : (Real.log (4 * (Tf x + 3)) + 2) ^ 2 ≤ 4 * (Real.log x) ^ (1/9 : ℝ) := by
      have h2 : (Real.log (4 * (Tf x + 3)) + 2) ^ 2 ≤ (2 * Real.log (Tf x)) ^ 2 :=
        pow_le_pow_left₀ (le_of_lt hlog4Tpos) hlog4T 2
      have h3 : (2 * Real.log (Tf x)) ^ 2 = 4 * ((Real.log x) ^ (1/18 : ℝ)) ^ 2 := by
        rw [mul_pow, hlogT]; norm_num
      have h4 : ((Real.log x) ^ (1/18 : ℝ)) ^ 2 = (Real.log x) ^ (1/9 : ℝ) := by
        rw [← Real.rpow_natCast ((Real.log x) ^ (1/18 : ℝ)) 2,
            ← Real.rpow_mul (le_of_lt hlogpos) (1/18) ((2:ℕ):ℝ)]
        rw [show (1/18:ℝ) * ((2:ℕ):ℝ) = 1/9 by norm_num]
      rw [h3, h4] at h2
      exact h2
    have hC₂nn : 0 ≤ C₂ := le_of_lt hC₂
    calc x * Real.exp (-(c / (Real.log (Tf x + 2)) ^ 9) * Real.log x)
          * (C₂ * (Real.log (4 * (Tf x + 3)) + 2) ^ 2)
        ≤ x * Real.exp (-(c/512) * Real.sqrt (Real.log x))
          * (C₂ * (4 * (Real.log x) ^ (1/9 : ℝ))) := by
          apply mul_le_mul
          · exact mul_le_mul_of_nonneg_left hexple (le_of_lt hxpos)
          · exact mul_le_mul_of_nonneg_left hsq hC₂nn
          · positivity
          · positivity
      _ = 4 * C₂ * (Real.log x) ^ (1/9 : ℝ) * x * Real.exp (-(c/512) * Real.sqrt (Real.log x)) := by ring
  have hT12 : C₁ * (x * (Real.log x) ^ 2 / Tf x + Real.log x) ≤ (1/2) * (x / (Real.log x) ^ A) := by
    have heq : C₁ * (x * (Real.log x) ^ 2 / Tf x + Real.log x)
        = C₁ * (x * (Real.log x) ^ 2 / Tf x) + C₁ * Real.log x := by ring
    rw [heq]
    linarith [hB1, hB2]
  have hZ : 4 * C₂ * (Real.log x) ^ (1/9 : ℝ) * x * Real.exp (-(c/512) * Real.sqrt (Real.log x))
      ≤ (1/2) * (x / (Real.log x) ^ A) := by
    have h := mul_le_mul_of_nonneg_right hB3 (le_of_lt hxpos)
    calc 4 * C₂ * (Real.log x) ^ (1/9 : ℝ) * x * Real.exp (-(c/512) * Real.sqrt (Real.log x))
        = (4 * C₂ * (Real.log x) ^ (1/9 : ℝ) * Real.exp (-(c/512) * Real.sqrt (Real.log x))) * x := by ring
      _ ≤ (1/2) * ((Real.log x) ^ A)⁻¹ * x := h
      _ = (1/2) * (x / (Real.log x) ^ A) := by rw [div_eq_mul_inv]; ring
  calc ‖PsiC x‖ ≤ C₁ * (x * (Real.log x) ^ 2 / Tf x + Real.log x)
        + x ^ (1 - c / (Real.log (Tf x + 2)) ^ 9) * (C₂ * (Real.log (4 * (Tf x + 3)) + 2) ^ 2) := hmain
    _ ≤ (1/2) * (x / (Real.log x) ^ A)
          + 4 * C₂ * (Real.log x) ^ (1/9 : ℝ) * x * Real.exp (-(c/512) * Real.sqrt (Real.log x)) := by
        linarith [hT12, hzpart]
    _ ≤ (1/2) * (x / (Real.log x) ^ A) + (1/2) * (x / (Real.log x) ^ A) := by
        linarith [hZ]
    _ = x / (Real.log x) ^ A := by ring

theorem chi4_psi_le_powLog :
    ∀ A : ℝ, 0 < A → ∃ C : ℝ, 0 < C ∧ ∀ x : ℝ, 2 ≤ x →
      ‖PsiC x‖ ≤ C * x / (Real.log x) ^ A := by
  intro A hA
  obtain ⟨C₁, hC₁pos, hEF⟩ :=
    chebyshevPsiChi_explicit_formula_mult (N := 4) chi4 chi4_ne_one' chi4_isPrimitive
  obtain ⟨c, hcpos, hZFR⟩ :=
    Commons.NumberTheory.LSeries.exists_zero_free_region_LFunction_chi4_all_t
  obtain ⟨C₂, hC₂pos, hZS⟩ :=
    completedL_zeroSum_inv_abs_le (N := 4) chi4 chi4_ne_one' chi4_isPrimitive
  obtain ⟨x₀, hx₀⟩ := Filter.eventually_atTop.mp
    (chi4_psi_eventually (A := A) hA hcpos hC₁pos hC₂pos hZFR hZS hEF)
  set M : ℝ := ∑ n ∈ Finset.Icc 1 ⌊x₀⌋₊, (ArithmeticFunction.vonMangoldt n : ℝ) with hM
  have hMnn : 0 ≤ M := Finset.sum_nonneg (fun n _ => ArithmeticFunction.vonMangoldt_nonneg)
  have hsmall : ∀ x : ℝ, 2 ≤ x → x < x₀ → ‖PsiC x‖ ≤ M := by
    intro x hx2 hxx₀
    have hfl : ⌊x⌋₊ ≤ ⌊x₀⌋₊ := Nat.floor_mono (le_of_lt hxx₀)
    have h1 : ‖PsiC x‖ ≤ ∑ n ∈ Finset.Icc 1 ⌊x⌋₊, (ArithmeticFunction.vonMangoldt n : ℝ) := by
      refine le_trans (norm_sum_le _ _) (Finset.sum_le_sum (fun n _ => ?_))
      calc ‖chi4 ((n : ℕ) : ZMod 4) * ((ArithmeticFunction.vonMangoldt n : ℝ) : ℂ)‖
          = ‖chi4 ((n : ℕ) : ZMod 4)‖ * (ArithmeticFunction.vonMangoldt n : ℝ) := by
            rw [norm_mul, Complex.norm_real,
              Real.norm_of_nonneg ArithmeticFunction.vonMangoldt_nonneg]
        _ ≤ 1 * (ArithmeticFunction.vonMangoldt n : ℝ) :=
            mul_le_mul_of_nonneg_right (DirichletCharacter.norm_le_one _ _)
              ArithmeticFunction.vonMangoldt_nonneg
        _ = (ArithmeticFunction.vonMangoldt n : ℝ) := one_mul _
    have hsub : Finset.Icc 1 ⌊x⌋₊ ⊆ Finset.Icc 1 ⌊x₀⌋₊ := by
      intro i hi; simp only [Finset.mem_Icc] at hi ⊢; exact ⟨hi.1, le_trans hi.2 hfl⟩
    refine le_trans h1 ?_
    rw [hM]
    exact Finset.sum_le_sum_of_subset_of_nonneg hsub
      (fun i _ _ => ArithmeticFunction.vonMangoldt_nonneg)
  set C : ℝ := max 1 (M * (Real.log x₀) ^ A / 2 + 1) with hC
  refine ⟨C, ?_, fun x hx2 => ?_⟩
  · have : 0 < max 1 (M * (Real.log x₀) ^ A / 2 + 1) := lt_max_of_lt_left one_pos
    rwa [hC]
  · rcases le_or_gt x₀ x with hx | hx
    · have h1 := hx₀ x hx
      have hx1 : (1:ℝ) < x := by linarith
      have hlogx : 0 < Real.log x := Real.log_pos hx1
      have hLpos : 0 < (Real.log x) ^ A := Real.rpow_pos_of_pos hlogx A
      have h2 : x / (Real.log x) ^ A ≤ C * x / (Real.log x) ^ A := by
        rw [hC, show max 1 (M * (Real.log x₀) ^ A / 2 + 1) * x / (Real.log x) ^ A
            = max 1 (M * (Real.log x₀) ^ A / 2 + 1) * (x / (Real.log x) ^ A) by ring]
        calc x / (Real.log x) ^ A = 1 * (x / (Real.log x) ^ A) := (one_mul _).symm
          _ ≤ max 1 (M * (Real.log x₀) ^ A / 2 + 1) * (x / (Real.log x) ^ A) :=
              mul_le_mul_of_nonneg_right (le_max_left _ _)
                (le_of_lt (div_pos (by linarith : (0:ℝ) < x) hLpos))
      linarith [h1, h2]
    · have h1 := hsmall x hx2 hx
      have hx1 : (1:ℝ) < x := by linarith
      have hlogx : 0 < Real.log x := Real.log_pos hx1
      have hLpos : 0 < (Real.log x) ^ A := Real.rpow_pos_of_pos hlogx A
      have hx0pos : 0 < x₀ := by linarith
      have hlogx0 : 0 < Real.log x₀ := Real.log_pos (by linarith)
      have hlogx0A : 0 < (Real.log x₀) ^ A := Real.rpow_pos_of_pos hlogx0 A
      have hle : (Real.log x) ^ A ≤ (Real.log x₀) ^ A :=
        Real.rpow_le_rpow (le_of_lt hlogx) (Real.log_le_log (by linarith) (le_of_lt hx))
          (le_of_lt hA)
      have hxC : M ≤ C * x / (Real.log x) ^ A := by
        rw [hC, le_div_iff₀ hLpos]
        have h2 : M * (Real.log x) ^ A ≤ (M * (Real.log x₀) ^ A / 2 + 1) * x := by
          have h2a : M * (Real.log x) ^ A ≤ M * (Real.log x₀) ^ A :=
            mul_le_mul_of_nonneg_left hle hMnn
          have h2b : M * (Real.log x₀) ^ A ≤ (M * (Real.log x₀) ^ A / 2 + 1) * x := by
            have hpos : 0 ≤ M * (Real.log x₀) ^ A / 2 + 1 := by positivity
            have h1 : M * (Real.log x₀) ^ A ≤ (M * (Real.log x₀) ^ A / 2 + 1) * 2 := by linarith
            calc M * (Real.log x₀) ^ A ≤ (M * (Real.log x₀) ^ A / 2 + 1) * 2 := h1
              _ ≤ (M * (Real.log x₀) ^ A / 2 + 1) * x := mul_le_mul_of_nonneg_left hx2 hpos
          linarith [h2a, h2b]
        have h3 : (M * (Real.log x₀) ^ A / 2 + 1) * x
            ≤ max 1 (M * (Real.log x₀) ^ A / 2 + 1) * x :=
          mul_le_mul_of_nonneg_right (le_max_right (1:ℝ) _) (by linarith : (0:ℝ) ≤ x)
        linarith [h2, h3]
      linarith [h1, hxC]

/-! ## The elementary chain: from `ψ(x,χ₄)` to the prime reciprocal sum -/

/-- `χ₄` evaluated at a natural number, as a real number. -/
noncomputable def c4 (n : ℕ) : ℝ := (chi4Fun ((n : ℕ) : ZMod 4)).re

private lemma chi4_eq_ofReal (n : ℕ) : chi4 ((n : ℕ) : ZMod 4) = ((c4 n : ℝ) : ℂ) := by
  rw [chi4_apply, c4, chi4Fun_eq_zmod]
  simp

private lemma abs_c4_le_one (n : ℕ) : |c4 n| ≤ 1 := by
  rw [c4]
  rcases zmod_four_eq ((n : ℕ) : ZMod 4) with h | h | h | h
  · rw [h]; simp [chi4Fun_zero]
  · rw [h]; simp [chi4Fun_one]
  · rw [h]; simp [chi4Fun_two]
  · rw [h]; simp [chi4Fun_three]

/-- The (real) twisted Chebyshev function `ψ(x, χ₄)`. -/
private noncomputable def PsiR (N : ℕ) : ℝ :=
  ∑ n ∈ Finset.Icc 1 N, c4 n * (ArithmeticFunction.vonMangoldt n : ℝ)

private lemma psiC_eq (x : ℝ) : PsiC x = ((PsiR ⌊x⌋₊ : ℝ) : ℂ) := by
  rw [PsiC, PsiR, Complex.ofReal_sum]
  refine Finset.sum_congr rfl (fun n _ => ?_)
  rw [chi4_eq_ofReal, Complex.ofReal_mul]

private lemma psiR_abs_le (N : ℕ) :
    |PsiR N| ≤ ∑ n ∈ Finset.Icc 1 N, (ArithmeticFunction.vonMangoldt n : ℝ) := by
  rw [PsiR]
  refine le_trans (Finset.abs_sum_le_sum_abs _ _) (Finset.sum_le_sum (fun n _ => ?_))
  rw [abs_mul]
  calc |c4 n| * |(ArithmeticFunction.vonMangoldt n : ℝ)|
      ≤ 1 * |(ArithmeticFunction.vonMangoldt n : ℝ)| :=
        mul_le_mul_of_nonneg_right (abs_c4_le_one n) (abs_nonneg _)
    _ = (ArithmeticFunction.vonMangoldt n : ℝ) := by
        rw [one_mul, abs_of_nonneg ArithmeticFunction.vonMangoldt_nonneg]

private lemma psiR_bound : ∀ A : ℝ, 0 < A → ∃ C : ℝ, 0 < C ∧ ∀ N : ℕ, 2 ≤ N →
    |PsiR N| ≤ C * N / (Real.log N) ^ A := by
  intro A hA
  obtain ⟨C, hCpos, hC⟩ := chi4_psi_le_powLog A hA
  refine ⟨C, hCpos, fun N hN => ?_⟩
  have hN2 : (2:ℝ) ≤ (N:ℝ) := by exact_mod_cast hN
  have h := hC (N:ℝ) hN2
  rw [psiC_eq, Nat.floor_natCast, Complex.norm_real, Real.norm_eq_abs] at h
  exact h

private lemma intervalIntegrable_psiR_div_sq {a b : ℝ} (ha : 2 ≤ a) (hab : a ≤ b) :
    IntervalIntegrable (fun t : ℝ => (PsiR ⌊t⌋₊ : ℝ) / t ^ 2) MeasureTheory.volume a b := by
  rw [intervalIntegrable_iff_integrableOn_Ioc_of_le hab]
  refine MeasureTheory.IntegrableOn.of_bound (s := Set.Ioc a b) ?_ ?_
    (∑ n ∈ Finset.Icc 1 ⌊b⌋₊, (ArithmeticFunction.vonMangoldt n : ℝ)) ?_
  · rw [Real.volume_Ioc]; exact ENNReal.ofReal_lt_top
  · exact Measurable.aestronglyMeasurable
      (((measurable_of_countable (fun n : ℕ => (PsiR n : ℝ))).comp Nat.measurable_floor).div
        (measurable_id.pow_const 2))
  · rw [MeasureTheory.ae_restrict_iff' measurableSet_Ioc]
    refine Filter.Eventually.of_forall (fun t ht => ?_)
    have ht2 : 2 ≤ t := le_trans ha (le_of_lt ht.1)
    have htM : ⌊t⌋₊ ≤ ⌊b⌋₊ := Nat.floor_mono ht.2
    have h1 : |PsiR ⌊t⌋₊| ≤ ∑ n ∈ Finset.Icc 1 ⌊t⌋₊, (ArithmeticFunction.vonMangoldt n : ℝ) :=
      psiR_abs_le _
    have h2 : (∑ n ∈ Finset.Icc 1 ⌊t⌋₊, (ArithmeticFunction.vonMangoldt n : ℝ))
        ≤ ∑ n ∈ Finset.Icc 1 ⌊b⌋₊, (ArithmeticFunction.vonMangoldt n : ℝ) :=
      Finset.sum_le_sum_of_subset_of_nonneg
        (by intro i hi; simp only [Finset.mem_Icc] at hi ⊢; exact ⟨hi.1, le_trans hi.2 htM⟩)
        (fun i _ _ => ArithmeticFunction.vonMangoldt_nonneg)
    rw [Real.norm_eq_abs, abs_div, abs_of_nonneg (by positivity : (0:ℝ) ≤ t ^ 2)]
    have ht2sq : 1 ≤ t ^ 2 := by nlinarith
    calc |PsiR ⌊t⌋₊| / t ^ 2 ≤ |PsiR ⌊t⌋₊| / 1 :=
          div_le_div_of_nonneg_left (abs_nonneg _) (by norm_num) ht2sq
      _ = |PsiR ⌊t⌋₊| := div_one _
      _ ≤ ∑ n ∈ Finset.Icc 1 ⌊t⌋₊, (ArithmeticFunction.vonMangoldt n : ℝ) := h1
      _ ≤ ∑ n ∈ Finset.Icc 1 ⌊b⌋₊, (ArithmeticFunction.vonMangoldt n : ℝ) := h2

/-! ### The non-prime (exponent `≥ 2`) part -/

private lemma nonprime_indic_eq (n : ℕ) :
    (if ∃ p e : ℕ, p.Prime ∧ 2 ≤ e ∧ n = p ^ e then (ArithmeticFunction.vonMangoldt n : ℝ) else 0)
      = (if n.Prime then (0:ℝ) else (ArithmeticFunction.vonMangoldt n : ℝ)) := by
  classical
  by_cases hn : n.Prime
  · have hcond : ¬∃ p e : ℕ, p.Prime ∧ 2 ≤ e ∧ n = p ^ e := by
      rintro ⟨p, e, _hp, he, hpe⟩
      exact (Nat.Prime.not_prime_pow he) (hpe ▸ hn)
    rw [if_neg hcond, if_pos hn]
  · by_cases hcond : ∃ p e : ℕ, p.Prime ∧ 2 ≤ e ∧ n = p ^ e
    · rw [if_pos hcond, if_neg hn]
    · have hni : ¬IsPrimePow n := by
        intro hi
        rcases (isPrimePow_nat_iff n).1 hi with ⟨p, k, hp, hk0, hpk⟩
        have hk1 : k ≠ 1 := by
          intro hk1
          apply hn
          simpa [← hpk, hk1] using hp
        have hk2 : 2 ≤ k := by omega
        exact hcond ⟨p, k, hp, hk2, hpk.symm⟩
      have hzero : ArithmeticFunction.vonMangoldt n = 0 :=
        (ArithmeticFunction.vonMangoldt_eq_zero_iff).2 hni
      rw [if_neg hcond, if_neg hn, hzero]

private noncomputable def ppB : ℝ :=
  Classical.choose Commons.NumberTheory.Chebyshev.cumulativePrimePowerLeSqrt

private lemma ppB_pos : 0 < ppB :=
  (Classical.choose_spec Commons.NumberTheory.Chebyshev.cumulativePrimePowerLeSqrt).1

private lemma ppB_cum (m : ℕ) :
    (∑ n ∈ Finset.Icc 0 m, (if n.Prime then (0:ℝ) else (ArithmeticFunction.vonMangoldt n : ℝ)))
      ≤ ppB * Real.sqrt m := by
  have h := (Classical.choose_spec Commons.NumberTheory.Chebyshev.cumulativePrimePowerLeSqrt).2
    (m : ℝ) (Nat.cast_nonneg m)
  rw [Nat.floor_natCast] at h
  have h2 : (∑ n ∈ Finset.Icc 0 m,
        (if ∃ p e : ℕ, p.Prime ∧ 2 ≤ e ∧ n = p ^ e then (ArithmeticFunction.vonMangoldt n : ℝ) else 0))
      = ∑ n ∈ Finset.Icc 0 m, (if n.Prime then (0:ℝ) else (ArithmeticFunction.vonMangoldt n : ℝ)) :=
    Finset.sum_congr rfl (fun n _ => nonprime_indic_eq n)
  rw [h2] at h
  exact h

/-- Tail bound for the exponent-`≥ 2` part of the `Λ`-sum, weighted by `1/n`. -/
private lemma nonprime_tail_le {N M : ℕ} (hN : 2 ≤ N) :
    (∑ k ∈ Finset.Icc (N+1) M,
        (if k.Prime then (0:ℝ) else (ArithmeticFunction.vonMangoldt k : ℝ) / (k:ℝ)))
      ≤ 3 * ppB / Real.sqrt ((N+1 : ℕ) : ℝ) := by
  have hsum : (∑ k ∈ Finset.Icc (N+1) M,
        (if k.Prime then (0:ℝ) else (ArithmeticFunction.vonMangoldt k : ℝ) / (k:ℝ)))
      = ∑ k ∈ Finset.Icc (N+1) M,
          (if k.Prime then (0:ℝ) else (ArithmeticFunction.vonMangoldt k : ℝ)) / (k:ℝ) := by
    refine Finset.sum_congr rfl (fun k _ => ?_)
    by_cases hk : k.Prime <;> simp [hk]
  rw [hsum]
  by_cases hNM : N + 1 ≤ M
  · exact Commons.Analysis.InfiniteSum.partialDivSumLeOfCumulativeSqrt
      (a := fun k => if k.Prime then (0:ℝ) else (ArithmeticFunction.vonMangoldt k : ℝ))
      (fun k => by split_ifs with h; exact le_refl 0; exact ArithmeticFunction.vonMangoldt_nonneg)
      (le_of_lt ppB_pos) ppB_cum (by omega) hNM
  · have hemp : Finset.Icc (N+1) M = ∅ := by
      apply Finset.eq_empty_iff_forall_notMem.mpr
      intro k hk
      simp only [Finset.mem_Icc] at hk
      omega
    rw [hemp, Finset.sum_empty]
    have h1 : 0 < ppB := ppB_pos
    have h2 : (0:ℝ) < Real.sqrt (((N+1 : ℕ)) : ℝ) := Real.sqrt_pos.mpr (by positivity)
    positivity

/-! ### Abel summation for the `Λ`-harmonic sum -/

private noncomputable def bLam (n : ℕ) : ℝ := c4 n * (ArithmeticFunction.vonMangoldt n : ℝ)

private lemma bLam_zero : bLam 0 = 0 := by
  simp only [bLam, mul_eq_zero]
  right
  rw [ArithmeticFunction.vonMangoldt_apply]
  simp [not_isPrimePow_zero]

private lemma bLam_one : bLam 1 = 0 := by
  rw [bLam, ArithmeticFunction.vonMangoldt_apply_one, mul_zero]

private noncomputable def Sred (N : ℕ) : ℝ := ∑ n ∈ Finset.Icc 1 N, bLam n / (n : ℝ)

private lemma Icc_zero_eq_insert (N : ℕ) : Finset.Icc 0 N = insert 0 (Finset.Icc 1 N) := by
  ext n; simp only [Finset.mem_Icc, Finset.mem_insert]; omega

private lemma PsiR_eq_sum_Icc_zero (N : ℕ) : PsiR N = ∑ n ∈ Finset.Icc 0 N, bLam n := by
  rw [PsiR, show (∑ n ∈ Finset.Icc 0 N, bLam n) = ∑ n ∈ insert 0 (Finset.Icc 1 N), bLam n from by
    rw [Icc_zero_eq_insert]]
  rw [Finset.sum_insert (by simp), bLam_zero, zero_add]
  rfl

private lemma Sred_eq_sum_Icc_zero (N : ℕ) : Sred N = ∑ n ∈ Finset.Icc 0 N, bLam n / (n : ℝ) := by
  rw [Sred, show (∑ n ∈ Finset.Icc 0 N, bLam n / (n:ℝ))
      = ∑ n ∈ insert 0 (Finset.Icc 1 N), bLam n / (n:ℝ) from by rw [Icc_zero_eq_insert]]
  rw [Finset.sum_insert (by simp), bLam_zero, zero_div, zero_add]

private lemma Sred_eq (N : ℕ) (hN : 2 ≤ N) :
    Sred N = PsiR N / (N:ℝ) + ∫ t in (2:ℝ)..(N:ℝ), (PsiR ⌊t⌋₊ : ℝ) / t ^ 2 := by
  have h := Commons.NumberTheory.AbelSummation.sum_div_abel_identity bLam bLam_zero bLam_one
    (x := (N:ℝ)) (by exact_mod_cast hN)
  rw [Nat.floor_natCast] at h
  rw [Sred_eq_sum_Icc_zero, h, PsiR_eq_sum_Icc_zero]
  congr 1
  apply intervalIntegral.integral_congr
  intro t _
  simp only [PsiR_eq_sum_Icc_zero]

private lemma Sred_diff (N M : ℕ) (hN : 2 ≤ N) (hNM : N ≤ M) :
    Sred M - Sred N = PsiR M / (M:ℝ) - PsiR N / (N:ℝ)
      + ∫ t in (N:ℝ)..(M:ℝ), (PsiR ⌊t⌋₊ : ℝ) / t ^ 2 := by
  have hM : 2 ≤ M := le_trans hN hNM
  rw [Sred_eq M hM, Sred_eq N hN]
  have hi1 : IntervalIntegrable (fun t : ℝ => (PsiR ⌊t⌋₊ : ℝ) / t ^ 2)
      MeasureTheory.volume (2:ℝ) (N:ℝ) :=
    intervalIntegrable_psiR_div_sq (by norm_num) (by exact_mod_cast hN)
  have hi2 : IntervalIntegrable (fun t : ℝ => (PsiR ⌊t⌋₊ : ℝ) / t ^ 2)
      MeasureTheory.volume (N:ℝ) (M:ℝ) :=
    intervalIntegrable_psiR_div_sq (by exact_mod_cast hN) (by exact_mod_cast hNM)
  have hsplit := intervalIntegral.integral_add_adjacent_intervals hi1 hi2
  rw [← hsplit]
  ring

private lemma integral_inv_mul_log_rpow {s : ℝ} (hs : 1 < s) {a b : ℝ} (ha : 2 ≤ a) (hab : a ≤ b) :
    ∫ t in a..b, (t * (Real.log t) ^ s)⁻¹
      = (s - 1)⁻¹ * ((Real.log a) ^ (1 - s) - (Real.log b) ^ (1 - s)) := by
  have hsm1 : (1:ℝ) - s ≠ 0 := by linarith
  have hderiv : ∀ x ∈ Set.uIcc a b,
      HasDerivAt (fun t : ℝ => (Real.log t) ^ (1 - s) / (1 - s)) ((x * (Real.log x) ^ s)⁻¹) x := by
    intro x hx
    rw [Set.uIcc_of_le hab] at hx
    have hx2 : (2:ℝ) ≤ x := le_trans ha hx.1
    have hx0 : x ≠ 0 := by linarith
    have hlogpos : 0 < Real.log x := Real.log_pos (by linarith)
    have h1 : HasDerivAt (fun t : ℝ => (Real.log t) ^ (1 - s))
        ((1 - s) * (Real.log x) ^ (1 - s - 1) * x⁻¹) x := by
      have hlog : HasDerivAt Real.log x⁻¹ x := Real.hasDerivAt_log hx0
      have hrpow : HasDerivAt (fun u : ℝ => u ^ (1 - s))
          ((1 - s) * (Real.log x) ^ (1 - s - 1)) (Real.log x) :=
        Real.hasDerivAt_rpow_const (Or.inl (ne_of_gt hlogpos))
      exact hrpow.comp x hlog
    have h2 : HasDerivAt (fun t : ℝ => (Real.log t) ^ (1 - s) / (1 - s))
        ((1 - s) * (Real.log x) ^ (1 - s - 1) * x⁻¹ / (1 - s)) x := h1.div_const (1 - s)
    convert h2 using 1
    rw [show (1 - s) - 1 = -s by ring, Real.rpow_neg (le_of_lt hlogpos)]
    field_simp
  have hcont : ContinuousOn (fun t : ℝ => (t * (Real.log t) ^ s)⁻¹) (Set.Icc a b) := by
    apply ContinuousOn.inv₀
    · apply ContinuousOn.mul continuousOn_id
      apply ContinuousOn.rpow_const
      · exact Real.continuousOn_log.mono (fun t ht => by
          simp only [Set.mem_compl_iff, Set.mem_singleton_iff]
          have : (2:ℝ) ≤ t := le_trans ha ht.1
          linarith)
      · intro t ht
        exact Or.inl (ne_of_gt (Real.log_pos (by linarith [le_trans ha ht.1])))
    · intro t ht
      have ht2 : (2:ℝ) ≤ t := le_trans ha ht.1
      have hlog : Real.log t ≠ 0 := ne_of_gt (Real.log_pos (by linarith))
      exact mul_ne_zero (by linarith) (ne_of_gt (Real.rpow_pos_of_pos (Real.log_pos (by linarith)) s))
  have hint : IntervalIntegrable (fun t : ℝ => (t * (Real.log t) ^ s)⁻¹) MeasureTheory.volume a b :=
    hcont.intervalIntegrable_of_Icc hab
  have h := intervalIntegral.integral_eq_sub_of_hasDerivAt
    (f := fun t : ℝ => (Real.log t) ^ (1 - s) / (1 - s))
    (f' := fun t : ℝ => (t * (Real.log t) ^ s)⁻¹) hderiv hint
  rw [h, show (1:ℝ) - s = -(s - 1) by ring]
  field_simp
  ring

/-! ### The Cauchy estimate for the `Λ`-harmonic sum -/

private lemma log_floor_ge_half (t : ℝ) (ht : 4 ≤ t) :
    Real.log t / 2 ≤ Real.log (⌊t⌋₊ : ℝ) := by
  have ht0 : 0 < t := by linarith
  have h2 : t / 2 ≤ (⌊t⌋₊ : ℝ) := by
    have h3 : t - 1 ≤ (⌊t⌋₊ : ℝ) := by
      have := Nat.lt_floor_add_one t
      linarith
    linarith
  have h5 : Real.log (t/2) ≤ Real.log (⌊t⌋₊ : ℝ) := Real.log_le_log (by linarith) h2
  have h6 : Real.log t / 2 ≤ Real.log (t/2) := by
    rw [Real.log_div (ne_of_gt ht0) (by norm_num : (2:ℝ) ≠ 0)]
    have h7 : 2 * Real.log 2 ≤ Real.log t := by
      have h8 := Real.log_le_log (by norm_num : (0:ℝ) < 4) ht
      rw [show (4:ℝ) = 2^2 by norm_num, Real.log_pow] at h8
      push_cast at h8
      linarith
    linarith
  linarith

private lemma integrand_bound {A C₀ t : ℝ} (hA : 0 < A) (hC₀ : 0 < C₀)
    (hpsi : ∀ K : ℕ, 2 ≤ K → |PsiR K| ≤ C₀ * K / (Real.log K) ^ (A+1))
    (ht : 4 ≤ t) :
    |(PsiR ⌊t⌋₊ : ℝ) / t ^ 2| ≤ C₀ * (2:ℝ) ^ (A+1) / (t * (Real.log t) ^ (A+1)) := by
  have ht0 : 0 < t := by linarith
  have hfl2 : 2 ≤ ⌊t⌋₊ := Nat.le_floor (show (2:ℝ) ≤ t by linarith)
  have hflpos : (0:ℝ) < (⌊t⌋₊ : ℝ) := by
    exact_mod_cast (by omega : 0 < ⌊t⌋₊)
  have hflle : ((⌊t⌋₊ : ℕ) : ℝ) ≤ t := Nat.floor_le (by linarith)
  have hlogfl_pos : 0 < Real.log (⌊t⌋₊ : ℝ) := by
    apply Real.log_pos
    have : (2:ℝ) ≤ (⌊t⌋₊ : ℝ) := by exact_mod_cast hfl2
    linarith
  have h1 : |PsiR ⌊t⌋₊| ≤ C₀ * (⌊t⌋₊ : ℝ) / (Real.log (⌊t⌋₊ : ℝ)) ^ (A+1) := hpsi ⌊t⌋₊ hfl2
  have hlogt_pos : 0 < Real.log t := Real.log_pos (by linarith)
  have h2 : Real.log t / 2 ≤ Real.log (⌊t⌋₊ : ℝ) := log_floor_ge_half t ht
  have h3 : (Real.log t / 2) ^ (A+1) ≤ (Real.log (⌊t⌋₊:ℝ)) ^ (A+1) :=
    Real.rpow_le_rpow (by positivity) h2 (by linarith)
  rw [abs_div, abs_of_nonneg (by positivity : (0:ℝ) ≤ t ^ 2)]
  have hstep1 : |PsiR ⌊t⌋₊| / t ^ 2 ≤ C₀ / (t * (Real.log t / 2) ^ (A+1)) := by
    have hden : 0 < (Real.log (⌊t⌋₊:ℝ)) ^ (A+1) := Real.rpow_pos_of_pos hlogfl_pos _
    calc |PsiR ⌊t⌋₊| / t ^ 2
        ≤ (C₀ * (⌊t⌋₊:ℝ) / (Real.log (⌊t⌋₊:ℝ))^(A+1)) / t^2 :=
          div_le_div_of_nonneg_right h1 (by positivity)
      _ ≤ (C₀ * t / (Real.log (⌊t⌋₊:ℝ))^(A+1)) / t^2 := by
          apply div_le_div_of_nonneg_right _ (by positivity)
          exact div_le_div_of_nonneg_right (mul_le_mul_of_nonneg_left hflle (le_of_lt hC₀)) (le_of_lt hden)
      _ = C₀ / ((Real.log (⌊t⌋₊:ℝ))^(A+1) * t) := by
          field_simp
      _ ≤ C₀ / ((Real.log t / 2)^(A+1) * t) := by
          apply div_le_div_of_nonneg_left (le_of_lt hC₀)
          · positivity
          · exact mul_le_mul_of_nonneg_right h3 (le_of_lt ht0)
      _ = C₀ / (t * (Real.log t / 2) ^ (A+1)) := by ring
  calc |PsiR ⌊t⌋₊| / t ^ 2 ≤ C₀ / (t * (Real.log t / 2) ^ (A+1)) := hstep1
    _ = C₀ * (2:ℝ) ^ (A+1) / (t * (Real.log t) ^ (A+1)) := by
        rw [Real.div_rpow (le_of_lt hlogt_pos) (by norm_num : (0:ℝ) ≤ 2)]
        field_simp

private lemma Sred_cauchy {A : ℝ} (hA : 0 < A) :
    ∃ C : ℝ, 0 < C ∧ ∀ N M : ℕ, 4 ≤ N → N ≤ M →
      |Sred M - Sred N| ≤ C / (Real.log N) ^ A := by
  obtain ⟨C₀, hC₀pos, hC₀⟩ := psiR_bound (A + 1) (by linarith)
  refine ⟨2 * C₀ + C₀ * (2:ℝ) ^ (A+1) / A, by positivity, fun N M hN hNM => ?_⟩
  have hN2 : 2 ≤ N := by omega
  have hM2 : 2 ≤ M := by omega
  have hNpos : (0:ℝ) < (N:ℝ) := by exact_mod_cast (by omega : 0 < N)
  have hMpos : (0:ℝ) < (M:ℝ) := by exact_mod_cast (by omega : 0 < M)
  have h4N : (4:ℝ) ≤ (N:ℝ) := by exact_mod_cast hN
  have hlogN : 0 < Real.log N := Real.log_pos (by linarith)
  have hlogN1 : 1 ≤ Real.log N := by
    have h := Real.log_le_log (by norm_num : (0:ℝ) < 4) h4N
    rw [show (4:ℝ) = 2^2 by norm_num, Real.log_pow] at h
    push_cast at h
    nlinarith [Real.log_two_gt_d9]
  have hlogM : Real.log N ≤ Real.log M := Real.log_le_log hNpos (by exact_mod_cast hNM)
  have hA1 : (0:ℝ) < A + 1 := by linarith
  rw [Sred_diff N M hN2 hNM]
  have hb1 : |PsiR M / (M:ℝ)| ≤ C₀ / (Real.log N) ^ (A+1) := by
    rw [abs_div, abs_of_nonneg (le_of_lt hMpos)]
    have h := hC₀ M hM2
    calc |PsiR M| / (M:ℝ) ≤ (C₀ * M / (Real.log M)^(A+1)) / M :=
          div_le_div_of_nonneg_right h (le_of_lt hMpos)
      _ = C₀ / (Real.log M)^(A+1) := by field_simp
      _ ≤ C₀ / (Real.log N)^(A+1) := by
          apply div_le_div_of_nonneg_left (le_of_lt hC₀pos)
          · exact Real.rpow_pos_of_pos hlogN _
          · exact Real.rpow_le_rpow (le_of_lt hlogN) hlogM (le_of_lt hA1)
  have hb2 : |PsiR N / (N:ℝ)| ≤ C₀ / (Real.log N) ^ (A+1) := by
    rw [abs_div, abs_of_nonneg (le_of_lt hNpos)]
    have h := hC₀ N hN2
    calc |PsiR N| / (N:ℝ) ≤ (C₀ * N / (Real.log N)^(A+1)) / N :=
          div_le_div_of_nonneg_right h (le_of_lt hNpos)
      _ = C₀ / (Real.log N)^(A+1) := by field_simp
  have hb3 : |∫ t in (N:ℝ)..(M:ℝ), (PsiR ⌊t⌋₊ : ℝ) / t ^ 2|
      ≤ C₀ * (2:ℝ) ^ (A+1) / A / (Real.log N) ^ A := by
    have hNM' : (N:ℝ) ≤ (M:ℝ) := by exact_mod_cast hNM
    have h4N : (4:ℝ) ≤ (N:ℝ) := by exact_mod_cast hN
    have hMlogpos : 0 < Real.log M := Real.log_pos (by linarith)
    have hintf : IntervalIntegrable (fun t : ℝ => (PsiR ⌊t⌋₊ : ℝ) / t ^ 2)
        MeasureTheory.volume (N:ℝ) (M:ℝ) :=
      intervalIntegrable_psiR_div_sq (by linarith) hNM'
    have hintg : IntervalIntegrable (fun t : ℝ => C₀ * (2:ℝ)^(A+1) / (t * (Real.log t)^(A+1)))
        MeasureTheory.volume (N:ℝ) (M:ℝ) := by
      apply ContinuousOn.intervalIntegrable
      rw [Set.uIcc_of_le hNM']
      apply ContinuousOn.div
      · exact continuousOn_const
      · apply ContinuousOn.mul continuousOn_id
        apply ContinuousOn.rpow_const
        · exact Real.continuousOn_log.mono (fun t ht => by
            simp only [Set.mem_compl_iff, Set.mem_singleton_iff]
            have : (4:ℝ) ≤ t := le_trans h4N ht.1
            linarith)
        · intro t ht
          exact Or.inl (ne_of_gt (Real.log_pos (by linarith [ht.1, h4N])))
      · intro t ht
        have ht4 : (4:ℝ) ≤ t := le_trans h4N ht.1
        have : (0:ℝ) < Real.log t := Real.log_pos (by linarith)
        positivity
    have hmono : ∫ t in (N:ℝ)..(M:ℝ), |(PsiR ⌊t⌋₊ : ℝ) / t ^ 2|
        ≤ ∫ t in (N:ℝ)..(M:ℝ), C₀ * (2:ℝ)^(A+1) / (t * (Real.log t)^(A+1)) := by
      apply intervalIntegral.integral_mono_on hNM' hintf.abs hintg
      intro t ht
      exact integrand_bound hA hC₀pos hC₀ (le_trans h4N ht.1)
    have hconst : ∫ t in (N:ℝ)..(M:ℝ), C₀ * (2:ℝ)^(A+1) / (t * (Real.log t)^(A+1))
        = C₀ * (2:ℝ)^(A+1) * ∫ t in (N:ℝ)..(M:ℝ), (t * (Real.log t)^(A+1))⁻¹ := by
      rw [← intervalIntegral.integral_const_mul]
      apply intervalIntegral.integral_congr
      intro t _
      simp only [Pi.mul_apply]
      rw [div_eq_mul_inv, mul_inv]
    have heval : ∫ t in (N:ℝ)..(M:ℝ), (t * (Real.log t)^(A+1))⁻¹
        = (A+1-1)⁻¹ * ((Real.log N)^(1-(A+1)) - (Real.log M)^(1-(A+1))) :=
      integral_inv_mul_log_rpow (s := A+1) (by linarith) (by linarith) hNM'
    have hpowM : 0 ≤ (Real.log M) ^ (1 - (A+1)) := Real.rpow_nonneg (le_of_lt hMlogpos) _
    have hexp : 1 - (A+1) = -A := by ring
    calc |∫ t in (N:ℝ)..(M:ℝ), (PsiR ⌊t⌋₊ : ℝ) / t ^ 2|
        ≤ ∫ t in (N:ℝ)..(M:ℝ), |(PsiR ⌊t⌋₊ : ℝ) / t ^ 2| :=
          intervalIntegral.abs_integral_le_integral_abs hNM'
      _ ≤ ∫ t in (N:ℝ)..(M:ℝ), C₀ * (2:ℝ)^(A+1) / (t * (Real.log t)^(A+1)) := hmono
      _ = C₀ * (2:ℝ)^(A+1) * ((A+1-1)⁻¹ * ((Real.log N)^(1-(A+1)) - (Real.log M)^(1-(A+1)))) := by
          rw [hconst, heval]
      _ ≤ C₀ * (2:ℝ)^(A+1) * (A⁻¹ * (Real.log N)^(-A)) := by
          have hsub : (Real.log N)^(1-(A+1)) - (Real.log M)^(1-(A+1)) ≤ (Real.log N)^(-A) := by
            rw [hexp] at hpowM ⊢
            linarith
          have hcoef : (A+1-1)⁻¹ = A⁻¹ := by ring_nf
          rw [hcoef]
          exact mul_le_mul_of_nonneg_left (mul_le_mul_of_nonneg_left hsub (inv_nonneg.mpr (le_of_lt hA)))
            (by positivity)
      _ = C₀ * (2:ℝ)^(A+1) / A / (Real.log N) ^ A := by
          rw [Real.rpow_neg (le_of_lt hlogN)]
          field_simp
  have hcomb : |PsiR M / (M:ℝ) - PsiR N / (N:ℝ)
      + ∫ t in (N:ℝ)..(M:ℝ), (PsiR ⌊t⌋₊ : ℝ) / t ^ 2|
      ≤ (2 * C₀ + C₀ * (2:ℝ)^(A+1) / A) / (Real.log N) ^ A := by
    have h1 : |PsiR M / (M:ℝ) - PsiR N / (N:ℝ)
        + ∫ t in (N:ℝ)..(M:ℝ), (PsiR ⌊t⌋₊ : ℝ) / t ^ 2|
        ≤ |PsiR M / (M:ℝ)| + |PsiR N / (N:ℝ)|
          + |∫ t in (N:ℝ)..(M:ℝ), (PsiR ⌊t⌋₊ : ℝ) / t ^ 2| := by
      refine le_trans (abs_add_le _ _) ?_
      have h3 : |PsiR M / (M:ℝ) - PsiR N / (N:ℝ)| ≤ |PsiR M / (M:ℝ)| + |PsiR N / (N:ℝ)| := by
        refine abs_sub_le_iff.mpr ⟨?_, ?_⟩ <;>
          linarith [le_abs_self (PsiR M / (M:ℝ)), neg_abs_le (PsiR M / (M:ℝ)),
            le_abs_self (PsiR N / (N:ℝ)), neg_abs_le (PsiR N / (N:ℝ))]
      linarith
    have h4 : C₀ / (Real.log N) ^ (A+1) ≤ C₀ / (Real.log N) ^ A := by
      apply div_le_div_of_nonneg_left (le_of_lt hC₀pos)
      · exact Real.rpow_pos_of_pos hlogN A
      · exact Real.rpow_le_rpow_of_exponent_le hlogN1 (by linarith)
    have h5 : C₀ * (2:ℝ)^(A+1) / A / (Real.log N) ^ A
        = C₀ * (2:ℝ)^(A+1) / A * ((Real.log N) ^ A)⁻¹ := by rw [div_eq_mul_inv]
    have h6 : (2 * C₀ + C₀ * (2:ℝ)^(A+1) / A) / (Real.log N) ^ A
        = 2 * (C₀ / (Real.log N) ^ A) + C₀ * (2:ℝ)^(A+1) / A * ((Real.log N) ^ A)⁻¹ := by
      rw [add_div, div_eq_mul_inv]
      ring
    have hb3' := hb3
    rw [h5] at hb3'
    rw [h6]
    linarith [h1, hb1, hb2, hb3', h4]
  exact hcomb

/-! ### The `χ₄`-twisted prime log-sum -/

private noncomputable def chilog (N : ℕ) : ℝ :=
  ∑ n ∈ Finset.Icc 1 N, (if n.Prime then c4 n * Real.log (n:ℝ) / (n:ℝ) else 0)

private lemma chilog_abs_le (N : ℕ) :
    |chilog N| ≤ ∑ n ∈ Finset.Icc 1 N, (if n.Prime then Real.log (n:ℝ) / (n:ℝ) else 0) := by
  rw [chilog]
  refine le_trans (Finset.abs_sum_le_sum_abs _ _) (Finset.sum_le_sum (fun n _ => ?_))
  by_cases hp : n.Prime
  · rw [if_pos hp, if_pos hp, abs_div, abs_of_nonneg (by positivity : (0:ℝ) ≤ (n:ℝ)), abs_mul,
      abs_of_nonneg (Real.log_nonneg (by exact_mod_cast hp.one_lt.le))]
    exact div_le_div_of_nonneg_right
      (mul_le_of_le_one_left (Real.log_nonneg (by exact_mod_cast hp.one_lt.le)) (abs_c4_le_one n))
      (by positivity)
  · rw [if_neg hp, if_neg hp, abs_zero]

private lemma Sred_sub_chilog (N : ℕ) :
    Sred N - chilog N = ∑ n ∈ Finset.Icc 1 N, (if n.Prime then (0:ℝ) else bLam n / (n:ℝ)) := by
  rw [Sred, chilog, ← Finset.sum_sub_distrib]
  refine Finset.sum_congr rfl (fun n _ => ?_)
  by_cases hp : n.Prime
  · rw [if_pos hp, if_pos hp, bLam, ArithmeticFunction.vonMangoldt_apply_prime hp, sub_self]
  · rw [if_neg hp, if_neg hp, sub_zero]

private lemma sum_diff_Icc {f : ℕ → ℝ} {N M : ℕ} (hN : 1 ≤ N) (hNM : N ≤ M) :
    (∑ n ∈ Finset.Icc 1 M, f n) - (∑ n ∈ Finset.Icc 1 N, f n)
      = ∑ n ∈ Finset.Icc (N+1) M, f n := by
  have hsub : Finset.Icc 1 N ⊆ Finset.Icc 1 M := by
    intro n hn; simp only [Finset.mem_Icc] at hn ⊢; exact ⟨hn.1, le_trans hn.2 hNM⟩
  have hsd := Finset.sum_sdiff (s₁ := Finset.Icc 1 N) (s₂ := Finset.Icc 1 M) (f := f) hsub
  have hset : Finset.Icc 1 M \ Finset.Icc 1 N = Finset.Icc (N+1) M := by
    ext n; simp only [Finset.mem_sdiff, Finset.mem_Icc]; omega
  rw [hset] at hsd
  linarith

private lemma chilog_diff_le {N M : ℕ} (hN : 2 ≤ N) (hNM : N ≤ M) :
    |chilog M - chilog N| ≤ |Sred M - Sred N| + 3 * ppB / Real.sqrt ((N+1 : ℕ) : ℝ) := by
  have h1 : chilog M - chilog N
      = (Sred M - Sred N)
        - ∑ n ∈ Finset.Icc (N+1) M, (if n.Prime then (0:ℝ) else bLam n / (n:ℝ)) := by
    have hM' := Sred_sub_chilog M
    have hN' := Sred_sub_chilog N
    have h2 := sum_diff_Icc (N := N) (M := M)
      (f := fun n => if n.Prime then (0:ℝ) else bLam n / (n:ℝ)) (by omega) hNM
    linarith
  have h2 : |∑ n ∈ Finset.Icc (N+1) M, (if n.Prime then (0:ℝ) else bLam n / (n:ℝ))|
      ≤ 3 * ppB / Real.sqrt ((N+1 : ℕ) : ℝ) := by
    refine le_trans (Finset.abs_sum_le_sum_abs _ _) (le_trans (Finset.sum_le_sum (fun n _ => ?_))
      (nonprime_tail_le (N := N) (M := M) hN))
    by_cases hp : n.Prime
    · rw [if_pos hp, if_pos hp, abs_zero]
    · rw [if_neg hp, if_neg hp, show bLam n = c4 n * (ArithmeticFunction.vonMangoldt n : ℝ) from rfl,
        abs_div, abs_of_nonneg (by positivity : (0:ℝ) ≤ (n:ℝ)), abs_mul,
        abs_of_nonneg ArithmeticFunction.vonMangoldt_nonneg]
      exact div_le_div_of_nonneg_right
        (mul_le_of_le_one_left ArithmeticFunction.vonMangoldt_nonneg (abs_c4_le_one n))
        (by positivity)
  calc |chilog M - chilog N|
      = |(Sred M - Sred N)
        - ∑ n ∈ Finset.Icc (N+1) M, (if n.Prime then (0:ℝ) else bLam n / (n:ℝ))| := by rw [h1]
    _ ≤ |Sred M - Sred N|
        + |∑ n ∈ Finset.Icc (N+1) M, (if n.Prime then (0:ℝ) else bLam n / (n:ℝ))| := by
        refine abs_sub_le_iff.mpr ⟨?_, ?_⟩ <;>
          linarith [le_abs_self (Sred M - Sred N), neg_abs_le (Sred M - Sred N),
            le_abs_self (∑ n ∈ Finset.Icc (N+1) M, (if n.Prime then (0:ℝ) else bLam n / (n:ℝ))),
            neg_abs_le (∑ n ∈ Finset.Icc (N+1) M, (if n.Prime then (0:ℝ) else bLam n / (n:ℝ)))]
    _ ≤ |Sred M - Sred N| + 3 * ppB / Real.sqrt ((N+1 : ℕ) : ℝ) := by linarith [h2]

private lemma sqrt_le_rpow_quarter {N : ℕ} (hN : 1 ≤ N) :
    (N:ℝ) ^ (1/4:ℝ) ≤ Real.sqrt ((N+1:ℕ) : ℝ) := by
  have h1 : (1:ℝ) ≤ (N:ℝ) := by exact_mod_cast hN
  have h2 : (N:ℝ) ^ (1/4:ℝ) ≤ (N:ℝ) ^ (1/2:ℝ) :=
    Real.rpow_le_rpow_of_exponent_le h1 (by norm_num)
  have h3 : (N:ℝ) ^ (1/2:ℝ) ≤ ((N+1:ℕ):ℝ) ^ (1/2:ℝ) := by
    apply Real.rpow_le_rpow (by positivity)
    · push_cast; linarith
    · norm_num
  have h4 : ((N+1:ℕ):ℝ) ^ (1/2:ℝ) = Real.sqrt ((N+1:ℕ) : ℝ) := (Real.sqrt_eq_rpow _).symm
  linarith [h2, h3, h4.symm.le, h4.le]

private lemma chilog_cauchy {A : ℝ} (hA : 0 < A) :
    ∃ C : ℝ, 0 < C ∧ ∀ N M : ℕ, 4 ≤ N → N ≤ M →
      |chilog M - chilog N| ≤ C * (1 / (Real.log N) ^ A + 1 / (N:ℝ) ^ (1/4:ℝ)) := by
  obtain ⟨C₁, hC₁pos, hC₁⟩ := Sred_cauchy hA
  have hppB : 0 < ppB := ppB_pos
  refine ⟨C₁ + 3 * ppB, by positivity, fun N M hN hNM => ?_⟩
  have hlogN : 0 < Real.log N := Real.log_pos (by exact_mod_cast (by omega : 1 < N))
  have hNpos : (0:ℝ) < (N:ℝ) := by exact_mod_cast (by omega : 0 < N)
  have h7 : |Sred M - Sred N| ≤ C₁ * (1 / (Real.log N) ^ A + 1 / (N:ℝ) ^ (1/4:ℝ)) := by
    refine le_trans (hC₁ N M hN hNM) ?_
    have h8 : (0:ℝ) ≤ 1 / (Real.log N) ^ A + 1 / (N:ℝ) ^ (1/4:ℝ) := by
      have := Real.rpow_pos_of_pos hlogN A
      have := Real.rpow_pos_of_pos hNpos (1/4:ℝ)
      positivity
    calc C₁ / (Real.log N) ^ A = C₁ * (1 / (Real.log N) ^ A) := by rw [mul_one_div]
      _ ≤ C₁ * (1 / (Real.log N) ^ A + 1 / (N:ℝ) ^ (1/4:ℝ)) := by
          apply mul_le_mul_of_nonneg_left _ (le_of_lt hC₁pos)
          have : (0:ℝ) ≤ 1 / (N:ℝ) ^ (1/4:ℝ) := by positivity
          linarith
  have hsq2 : 3 * ppB / Real.sqrt ((N+1 : ℕ) : ℝ)
      ≤ (3 * ppB) * (1 / (Real.log N) ^ A + 1 / (N:ℝ) ^ (1/4:ℝ)) := by
    have hsq : 3 * ppB / Real.sqrt ((N+1 : ℕ) : ℝ) ≤ 3 * ppB / (N:ℝ) ^ (1/4:ℝ) := by
      apply div_le_div_of_nonneg_left (by positivity)
      · exact Real.rpow_pos_of_pos hNpos _
      · exact sqrt_le_rpow_quarter (by omega)
    calc 3 * ppB / Real.sqrt ((N+1 : ℕ) : ℝ) ≤ 3 * ppB / (N:ℝ) ^ (1/4:ℝ) := hsq
      _ = (3 * ppB) * (1 / (N:ℝ) ^ (1/4:ℝ)) := by rw [mul_one_div]
      _ ≤ (3 * ppB) * (1 / (Real.log N) ^ A + 1 / (N:ℝ) ^ (1/4:ℝ)) := by
          apply mul_le_mul_of_nonneg_left _ (by positivity)
          have : (0:ℝ) ≤ 1 / (Real.log N) ^ A := by positivity
          exact le_add_of_nonneg_left this
  calc |chilog M - chilog N| ≤ |Sred M - Sred N| + 3 * ppB / Real.sqrt ((N+1 : ℕ) : ℝ) :=
        chilog_diff_le (by omega) hNM
    _ ≤ C₁ * (1 / (Real.log N) ^ A + 1 / (N:ℝ) ^ (1/4:ℝ))
          + (3 * ppB) * (1 / (Real.log N) ^ A + 1 / (N:ℝ) ^ (1/4:ℝ)) := by linarith [h7, hsq2]
    _ = (C₁ + 3 * ppB) * (1 / (Real.log N) ^ A + 1 / (N:ℝ) ^ (1/4:ℝ)) := by ring

private lemma inv_rpow_quarter_tendsto_zero :
    Tendsto (fun N : ℕ => 1 / (N:ℝ) ^ (1/4:ℝ)) atTop (nhds 0) := by
  have h2 : Tendsto (fun x : ℝ => x ^ (-(1/4) : ℝ)) atTop (nhds 0) :=
    tendsto_rpow_neg_atTop (by norm_num)
  have h3 : (fun x : ℝ => 1 / x ^ (1/4:ℝ)) =ᶠ[atTop] (fun x : ℝ => x ^ (-(1/4) : ℝ)) := by
    filter_upwards [eventually_ge_atTop (1:ℝ)] with x hx
    rw [one_div, ← Real.rpow_neg (by linarith : (0:ℝ) ≤ x)]
  have h4 : Tendsto (fun x : ℝ => 1 / x ^ (1/4:ℝ)) atTop (nhds 0) := h2.congr' h3.symm
  exact (h4.comp tendsto_natCast_atTop_atTop).congr (fun N => by simp)

private lemma inv_log_tendsto_zero :
    Tendsto (fun N : ℕ => 1 / (Real.log N) ^ (1:ℝ)) atTop (nhds 0) := by
  have h2 : Tendsto (fun x : ℝ => (Real.log x) ^ (-(1:ℝ))) atTop (nhds 0) :=
    (tendsto_rpow_neg_atTop (by norm_num : (0:ℝ) < 1)).comp Real.tendsto_log_atTop
  have h3 : (fun x : ℝ => 1 / (Real.log x) ^ (1:ℝ))
      =ᶠ[atTop] (fun x : ℝ => (Real.log x) ^ (-(1:ℝ))) := by
    filter_upwards [Real.tendsto_log_atTop.eventually_ge_atTop 1] with x hx
    rw [one_div, ← Real.rpow_neg (by linarith : (0:ℝ) ≤ Real.log x)]
  have h4 : Tendsto (fun x : ℝ => 1 / (Real.log x) ^ (1:ℝ)) atTop (nhds 0) := h2.congr' h3.symm
  exact (h4.comp tendsto_natCast_atTop_atTop).congr (fun N => by simp)

private lemma limit_of_cauchy_rate {u : ℕ → ℝ} {K : ℕ} (hK : 2 ≤ K)
    (h : ∀ A : ℝ, 0 < A → ∃ C : ℝ, 0 < C ∧ ∀ N M : ℕ, K ≤ N → N ≤ M →
      |u M - u N| ≤ C * (1 / (Real.log N) ^ A + 1 / (N:ℝ) ^ (1/4:ℝ))) :
    ∃ L : ℝ, ∀ A : ℝ, 0 < A → ∃ C : ℝ, 0 < C ∧ ∀ N : ℕ, K ≤ N →
      |u N - L| ≤ C * (1 / (Real.log N) ^ A + 1 / (N:ℝ) ^ (1/4:ℝ)) := by
  obtain ⟨C₁, hC₁pos, hC₁⟩ := h 1 one_pos
  have hb0 : Tendsto (fun K' : ℕ => C₁ * (1 / (Real.log K') ^ (1:ℝ) + 1 / (K':ℝ) ^ (1/4:ℝ)))
      atTop (nhds 0) := by
    have h1 : Tendsto (fun K' : ℕ => 1 / (Real.log K') ^ (1:ℝ) + 1 / (K':ℝ) ^ (1/4:ℝ))
        atTop (nhds (0+0)) := inv_log_tendsto_zero.add inv_rpow_quarter_tendsto_zero
    have h2 : Tendsto (fun K' : ℕ => C₁ * (1 / (Real.log K') ^ (1:ℝ) + 1 / (K':ℝ) ^ (1/4:ℝ)))
        atTop (nhds (C₁ * (0+0))) := h1.const_mul C₁
    simpa using h2
  have hb : Tendsto (fun N : ℕ => C₁ * (1 / (Real.log ((N:ℝ) + (K:ℝ))) ^ (1:ℝ)
      + 1 / ((N:ℝ) + (K:ℝ)) ^ (1/4:ℝ))) atTop (nhds 0) := by
    have h' := hb0.comp (Filter.tendsto_add_atTop_nat K)
    rw [show (fun N : ℕ => C₁ * (1 / (Real.log ((N:ℝ) + (K:ℝ))) ^ (1:ℝ)
        + 1 / ((N:ℝ) + (K:ℝ)) ^ (1/4:ℝ)))
        = (fun K' : ℕ => C₁ * (1 / (Real.log K') ^ (1:ℝ) + 1 / (K':ℝ) ^ (1/4:ℝ)))
          ∘ (fun N : ℕ => N + K) from by
      funext N; simp only [Function.comp_apply, Nat.cast_add]]
    exact h'
  have hcauchy : CauchySeq (fun N : ℕ => u (N + K)) := by
    refine cauchySeq_of_le_tendsto_0 (b := fun N : ℕ => C₁ * (1 / (Real.log ((N:ℝ) + (K:ℝ))) ^ (1:ℝ)
        + 1 / ((N:ℝ) + (K:ℝ)) ^ (1/4:ℝ))) (fun n m N hn hm => ?_) hb
    have hKbn : K ≤ n + K := by omega
    have hKbm : K ≤ m + K := by omega
    have hNK2 : (2:ℕ) ≤ N + K := by omega
    rcases le_total n m with h' | h'
    · have hbnd := hC₁ (n+K) (m+K) hKbn (by omega)
      have hNK : ((N+K:ℕ)) ≤ (n+K:ℕ) := by omega
      have hP' : (0:ℝ) < ((N+K:ℕ):ℝ) := by exact_mod_cast (by omega : 0 < N + K)
      have hP'' : (0:ℝ) < ((n+K:ℕ):ℝ) := by exact_mod_cast (by omega : 0 < n + K)
      have hlogNn : Real.log (((N+K:ℕ)):ℝ) ≤ Real.log (((n+K:ℕ)):ℝ) :=
        Real.log_le_log hP' (by exact_mod_cast hNK)
      have h1 : 1 / (Real.log (((n+K:ℕ)):ℝ)) ^ (1:ℝ)
          ≤ 1 / (Real.log (((N+K:ℕ)):ℝ)) ^ (1:ℝ) := by
        apply div_le_div_of_nonneg_left (by norm_num)
          (Real.rpow_pos_of_pos (Real.log_pos (by exact_mod_cast (by omega : 1 < N + K))) _)
        exact Real.rpow_le_rpow (le_of_lt (Real.log_pos (by exact_mod_cast (by omega : 1 < N + K))))
          hlogNn (by norm_num)
      have h2 : 1 / (((n+K:ℕ)):ℝ) ^ (1/4:ℝ) ≤ 1 / (((N+K:ℕ)):ℝ) ^ (1/4:ℝ) := by
        apply div_le_div_of_nonneg_left (by norm_num) (Real.rpow_pos_of_pos hP' _)
        exact Real.rpow_le_rpow (le_of_lt hP') (by exact_mod_cast hNK) (by norm_num)
      rw [Real.dist_eq, abs_sub_comm, ← Nat.cast_add]
      refine le_trans hbnd (mul_le_mul_of_nonneg_left ?_ (le_of_lt hC₁pos))
      linarith
    · have hbnd := hC₁ (m+K) (n+K) hKbm (by omega)
      have hNK : ((N+K:ℕ)) ≤ (m+K:ℕ) := by omega
      have hP' : (0:ℝ) < ((N+K:ℕ):ℝ) := by exact_mod_cast (by omega : 0 < N + K)
      have hP'' : (0:ℝ) < ((m+K:ℕ):ℝ) := by exact_mod_cast (by omega : 0 < m + K)
      have hlogNm : Real.log (((N+K:ℕ)):ℝ) ≤ Real.log (((m+K:ℕ)):ℝ) :=
        Real.log_le_log hP' (by exact_mod_cast hNK)
      have h1 : 1 / (Real.log (((m+K:ℕ)):ℝ)) ^ (1:ℝ)
          ≤ 1 / (Real.log (((N+K:ℕ)):ℝ)) ^ (1:ℝ) := by
        apply div_le_div_of_nonneg_left (by norm_num)
          (Real.rpow_pos_of_pos (Real.log_pos (by exact_mod_cast (by omega : 1 < N + K))) _)
        exact Real.rpow_le_rpow (le_of_lt (Real.log_pos (by exact_mod_cast (by omega : 1 < N + K))))
          hlogNm (by norm_num)
      have h2 : 1 / (((m+K:ℕ)):ℝ) ^ (1/4:ℝ) ≤ 1 / (((N+K:ℕ)):ℝ) ^ (1/4:ℝ) := by
        apply div_le_div_of_nonneg_left (by norm_num) (Real.rpow_pos_of_pos hP' _)
        exact Real.rpow_le_rpow (le_of_lt hP') (by exact_mod_cast hNK) (by norm_num)
      rw [Real.dist_eq, ← Nat.cast_add]
      refine le_trans hbnd (mul_le_mul_of_nonneg_left ?_ (le_of_lt hC₁pos))
      linarith
  obtain ⟨L, hL⟩ := cauchySeq_tendsto_of_complete hcauchy
  refine ⟨L, fun A hA => ?_⟩
  obtain ⟨C, hCpos, hC⟩ := h A hA
  refine ⟨C, hCpos, fun N hN => ?_⟩
  have hev : ∀ᶠ j : ℕ in atTop,
      |u (j + K) - u N| ≤ C * (1 / (Real.log N) ^ A + 1 / (N:ℝ) ^ (1/4:ℝ)) := by
    filter_upwards [Filter.eventually_ge_atTop N] with j hj
    exact hC N (j+K) hN (by omega)
  have htend : Tendsto (fun j : ℕ => |u (j+K) - u N|) atTop (nhds |L - u N|) :=
    (hL.sub_const (u N)).abs
  have := le_of_tendsto htend hev
  rwa [abs_sub_comm] at this

private lemma chilog_limit : ∃ L : ℝ, ∀ A : ℝ, 0 < A → ∃ C : ℝ, 0 < C ∧ ∀ N : ℕ, 4 ≤ N →
    |chilog N - L| ≤ C * (1 / (Real.log N) ^ A + 1 / (N:ℝ) ^ (1/4:ℝ)) :=
  limit_of_cauchy_rate (u := chilog) (K := 4) (by norm_num) (fun A hA => chilog_cauchy (A := A) hA)

/-! ### The prime reciprocal sum -/

private noncomputable def bLog (n : ℕ) : ℝ :=
  if n.Prime then c4 n * Real.log (n:ℝ) / (n:ℝ) else 0

private lemma bLog_zero : bLog 0 = 0 := by simp [bLog]

private lemma bLog_one : bLog 1 = 0 := by simp [bLog]

private lemma sum_bLog_eq_chilog (K : ℕ) : (∑ n ∈ Finset.Icc 0 K, bLog n) = chilog K := by
  rw [chilog, Icc_zero_eq_insert K, Finset.sum_insert (by simp), bLog_zero, zero_add]
  rfl

private noncomputable def Rsum (N : ℕ) : ℝ :=
  ∑ n ∈ Finset.Icc 0 N, (if n.Prime then c4 n / (n:ℝ) else 0)

private lemma Rsum_eq_primesLE (N : ℕ) : Rsum N = ∑ p ∈ N.primesLE, c4 p / (p:ℝ) := by
  rw [Rsum, ← Finset.sum_filter]
  congr 1
  ext p
  simp only [Finset.mem_filter, Finset.mem_Icc, Nat.mem_primesLE]
  constructor
  · rintro ⟨⟨-, h2⟩, h3⟩; exact ⟨h2, h3⟩
  · rintro ⟨h1, h2⟩; exact ⟨⟨Nat.zero_le _, h1⟩, h2⟩

private lemma Rsum_eq (N : ℕ) (hN : 2 ≤ N) :
    Rsum N = chilog N / Real.log N
      + ∫ t in (2:ℝ)..(N:ℝ), chilog ⌊t⌋₊ / (t * (Real.log t) ^ 2) := by
  have h := Commons.NumberTheory.FriedlanderIwaniec.sum_div_log_abel_identity bLog bLog_zero bLog_one
    (x := (N:ℝ)) (by exact_mod_cast hN)
  rw [Nat.floor_natCast] at h
  have h2 : (∑ n ∈ Finset.Icc 0 N, bLog n / Real.log (n:ℝ)) = Rsum N := by
    rw [Rsum]
    refine Finset.sum_congr rfl (fun n _ => ?_)
    by_cases hp : n.Prime
    · rw [bLog, if_pos hp, if_pos hp]
      have hlog : Real.log (n:ℝ) ≠ 0 := ne_of_gt (Real.log_pos (by exact_mod_cast hp.one_lt))
      field_simp
    · rw [bLog, if_neg hp, if_neg hp, zero_div]
  rw [h2] at h
  rw [sum_bLog_eq_chilog N] at h
  simp only [sum_bLog_eq_chilog] at h
  exact h


/-! ### The Abel identity for the prime reciprocal sum -/

private noncomputable def clip (K : ℕ) : ℝ :=
  ∑ n ∈ Finset.Icc 1 K, (if n.Prime then Real.log (n:ℝ) / (n:ℝ) else 0)

private lemma chilog_clip_le (K : ℕ) : |chilog K| ≤ clip K := chilog_abs_le K

private lemma clip_mono {K K' : ℕ} (h : K ≤ K') : clip K ≤ clip K' := by
  refine Finset.sum_le_sum_of_subset_of_nonneg ?_ (fun i _ _ => ?_)
  · intro i hi; simp only [Finset.mem_Icc] at hi ⊢; exact ⟨hi.1, le_trans hi.2 h⟩
  · split_ifs with hp
    · positivity
    · exact le_refl 0

private lemma intervalIntegrable_chilog_div {a b : ℝ} (ha : 2 ≤ a) (hab : a ≤ b) :
    IntervalIntegrable (fun t : ℝ => chilog ⌊t⌋₊ / (t * (Real.log t) ^ 2))
      MeasureTheory.volume a b := by
  rw [intervalIntegrable_iff_integrableOn_Ioc_of_le hab]
  refine MeasureTheory.IntegrableOn.of_bound (s := Set.Ioc a b) ?_ ?_
    (clip ⌊b⌋₊ / (a * (Real.log a) ^ 2)) ?_
  · rw [Real.volume_Ioc]; exact ENNReal.ofReal_lt_top
  · exact Measurable.aestronglyMeasurable
      (((measurable_of_countable (fun n : ℕ => chilog n)).comp Nat.measurable_floor).div
        (measurable_id.mul (Real.measurable_log.pow_const 2)))
  · rw [MeasureTheory.ae_restrict_iff' measurableSet_Ioc]
    refine Filter.Eventually.of_forall (fun t ht => ?_)
    have ht2 : 2 ≤ t := le_trans ha (le_of_lt ht.1)
    have htlog : 0 < Real.log t := Real.log_pos (by linarith)
    have halog : 0 < Real.log a := Real.log_pos (by linarith)
    have hfl : ⌊t⌋₊ ≤ ⌊b⌋₊ := Nat.floor_mono ht.2
    have h1 : |chilog ⌊t⌋₊| ≤ clip ⌊b⌋₊ := le_trans (chilog_clip_le _) (clip_mono hfl)
    have h2 : a * (Real.log a) ^ 2 ≤ t * (Real.log t) ^ 2 := by
      apply mul_le_mul
      · exact ht.1.le
      · exact pow_le_pow_left₀ (le_of_lt halog) (Real.log_le_log (by linarith) ht.1.le) 2
      · positivity
      · positivity
    rw [Real.norm_eq_abs, abs_div, abs_of_nonneg (by positivity : (0:ℝ) ≤ t * (Real.log t) ^ 2)]
    calc |chilog ⌊t⌋₊| / (t * (Real.log t) ^ 2) ≤ clip ⌊b⌋₊ / (t * (Real.log t) ^ 2) :=
          div_le_div_of_nonneg_right h1 (by positivity)
      _ ≤ clip ⌊b⌋₊ / (a * (Real.log a) ^ 2) := by
          have hclip : 0 ≤ clip ⌊b⌋₊ := by
            rw [clip]; refine Finset.sum_nonneg (fun i _ => ?_); split_ifs <;> positivity
          have hden : 0 < a * (Real.log a) ^ 2 := by positivity
          exact div_le_div_of_nonneg_left hclip hden h2

private lemma Rsum_diff {N M : ℕ} (hN : 2 ≤ N) (hNM : N ≤ M) :
    Rsum M - Rsum N = (chilog M / Real.log M - chilog N / Real.log N)
      + ∫ t in (N:ℝ)..(M:ℝ), chilog ⌊t⌋₊ / (t * (Real.log t) ^ 2) := by
  have hM : 2 ≤ M := le_trans hN hNM
  have hNM' : (N:ℝ) ≤ (M:ℝ) := by exact_mod_cast hNM
  rw [Rsum_eq M hM, Rsum_eq N hN]
  have hi1 : IntervalIntegrable (fun t : ℝ => chilog ⌊t⌋₊ / (t * (Real.log t)^2))
      MeasureTheory.volume (2:ℝ) (N:ℝ) :=
    intervalIntegrable_chilog_div (by norm_num) (by exact_mod_cast hN)
  have hi2 : IntervalIntegrable (fun t : ℝ => chilog ⌊t⌋₊ / (t * (Real.log t)^2))
      MeasureTheory.volume (N:ℝ) (M:ℝ) :=
    intervalIntegrable_chilog_div (by exact_mod_cast hN) hNM'
  have hsplit := intervalIntegral.integral_add_adjacent_intervals hi1 hi2
  rw [← hsplit]
  ring


private lemma log_floor_ge_one {t : ℝ} (ht : 4 ≤ t) : 1 ≤ Real.log (⌊t⌋₊ : ℝ) := by
  have h1 : (4:ℝ) ≤ (⌊t⌋₊ : ℝ) := by
    have h4 : (4:ℕ) ≤ ⌊t⌋₊ := Nat.le_floor (show (4:ℝ) ≤ t from ht)
    exact_mod_cast h4
  have h2 : Real.log 4 ≤ Real.log (⌊t⌋₊ : ℝ) := Real.log_le_log (by norm_num) h1
  have h3 : (1:ℝ) < Real.log 4 := by
    rw [show (4:ℝ) = 2^2 by norm_num, Real.log_pow]
    push_cast
    nlinarith [Real.log_two_gt_d9]
  linarith

private lemma chilog_sub_L_integrand_bound {B C_s L : ℝ} {N : ℕ} {t : ℝ} (hB : 0 < B)
    (hCs : 0 ≤ C_s)
    (hL : ∀ K : ℕ, 4 ≤ K →
      |chilog K - L| ≤ C_s * (1 / (Real.log K) ^ B + 1 / (K:ℝ) ^ (1/4:ℝ)))
    (hN : 4 ≤ N) (ht : 4 ≤ t) (hNt : (N:ℝ) ≤ t) :
    |(chilog ⌊t⌋₊ - L) / (t * (Real.log t) ^ 2)|
      ≤ C_s * (2 ^ B / (t * (Real.log t) ^ (B+1)) + 1 / ((N:ℝ) ^ (1/4:ℝ) * (t * (Real.log t) ^ 2))) := by
  have hfl : N ≤ ⌊t⌋₊ := Nat.le_floor (by exact_mod_cast hNt)
  have hfl4 : 4 ≤ ⌊t⌋₊ := le_trans hN hfl
  have hlogfl : 1 ≤ Real.log (⌊t⌋₊ : ℝ) := log_floor_ge_one ht
  have hlogflpos : 0 < Real.log (⌊t⌋₊ : ℝ) := lt_of_lt_of_le one_pos hlogfl
  have hlogt : 0 < Real.log t := Real.log_pos (by linarith)
  have hlogt1 : 1 ≤ Real.log t := le_trans (log_floor_ge_one ht) (by
    apply Real.log_le_log (by exact_mod_cast (by omega : 0 < ⌊t⌋₊))
    exact Nat.floor_le (by linarith))
  have hfloor : Real.log t / 2 ≤ Real.log (⌊t⌋₊ : ℝ) := log_floor_ge_half t ht
  have hNpos : (0:ℝ) < (N:ℝ) := by exact_mod_cast (by omega : 0 < N)
  -- `1 / (log ⌊t⌋)^B ≤ 2^B / (log t)^B`
  have hBpos : 0 < (2:ℝ) ^ B := Real.rpow_pos_of_pos (by norm_num) B
  have hlogBpos : 0 < (Real.log t) ^ B := Real.rpow_pos_of_pos hlogt B
  have h1 : 1 / (Real.log (⌊t⌋₊ : ℝ)) ^ B ≤ 2 ^ B / (Real.log t) ^ B := by
    have h3 : (Real.log t / 2) ^ B ≤ (Real.log (⌊t⌋₊ : ℝ)) ^ B :=
      Real.rpow_le_rpow (by positivity) hfloor (le_of_lt hB)
    have h4 : (Real.log t / 2) ^ B = (Real.log t) ^ B / 2 ^ B :=
      Real.div_rpow (le_of_lt hlogt) (by norm_num : (0:ℝ) ≤ 2) B
    have h5 : (Real.log t) ^ B / 2 ^ B ≤ (Real.log (⌊t⌋₊ : ℝ)) ^ B := h4 ▸ h3
    have h6 : (Real.log t) ^ B ≤ 2 ^ B * (Real.log (⌊t⌋₊ : ℝ)) ^ B := by
      have h7 := (div_le_iff₀ hBpos).mp h5
      rwa [mul_comm] at h7
    rw [div_le_div_iff₀ (Real.rpow_pos_of_pos hlogflpos B) hlogBpos, one_mul]
    exact h6
  have h2 : 1 / ((⌊t⌋₊ : ℝ)) ^ (1/4:ℝ) ≤ 1 / ((N:ℝ)) ^ (1/4:ℝ) := by
    apply div_le_div_of_nonneg_left (by norm_num)
    · exact Real.rpow_pos_of_pos hNpos _
    · exact Real.rpow_le_rpow (le_of_lt hNpos) (by exact_mod_cast hfl) (by norm_num)
  have h3 : |chilog ⌊t⌋₊ - L| ≤ C_s * (2 ^ B / (Real.log t) ^ B + 1 / ((N:ℝ) ^ (1/4:ℝ))) := by
    refine le_trans (hL ⌊t⌋₊ hfl4) (mul_le_mul_of_nonneg_left ?_ hCs)
    linarith
  have hden : 0 < t * (Real.log t) ^ 2 := by positivity
  rw [abs_div, abs_of_nonneg (le_of_lt hden)]
  have step1 : |chilog ⌊t⌋₊ - L| / (t * (Real.log t) ^ 2)
      ≤ C_s * (2 ^ B / (Real.log t) ^ B + 1 / ((N:ℝ) ^ (1/4:ℝ))) / (t * (Real.log t) ^ 2) :=
    div_le_div_of_nonneg_right h3 (le_of_lt hden)
  have hsq : Real.log t ≤ (Real.log t) ^ 2 := by nlinarith [hlogt1]
  have hpow : (Real.log t) ^ (B+1) = (Real.log t) ^ B * Real.log t := by
    rw [show B + 1 = B + (1:ℝ) by ring, Real.rpow_add hlogt B 1, Real.rpow_one]
  have hpowle : (Real.log t) ^ (B+1) ≤ (Real.log t) ^ B * (Real.log t) ^ 2 := by
    rw [hpow]; nlinarith [hsq, hlogBpos]
  have hx : 2 ^ B / (Real.log t) ^ B / (t * (Real.log t)^2)
      ≤ 2 ^ B / (t * (Real.log t)^(B+1)) := by
    rw [div_div, div_le_div_iff₀ (by positivity) (by positivity)]
    have htpos : (0:ℝ) < t := by linarith
    have hstep : t * (Real.log t) ^ (B+1) ≤ (Real.log t) ^ B * (t * (Real.log t) ^ 2) := by
      nlinarith [hpowle, htpos]
    nlinarith [hstep, hBpos]
  have hy : 1 / ((N:ℝ) ^ (1/4:ℝ)) / (t * (Real.log t)^2)
      = 1 / ((N:ℝ) ^ (1/4:ℝ) * (t * (Real.log t)^2)) := div_div _ _ _
  calc |chilog ⌊t⌋₊ - L| / (t * (Real.log t) ^ 2)
      ≤ C_s * (2 ^ B / (Real.log t) ^ B + 1 / ((N:ℝ) ^ (1/4:ℝ))) / (t * (Real.log t) ^ 2) := step1
    _ = C_s * (2 ^ B / (Real.log t) ^ B / (t * (Real.log t)^2)
          + 1 / ((N:ℝ) ^ (1/4:ℝ)) / (t * (Real.log t)^2)) := by
        rw [mul_div_assoc, add_div]
    _ ≤ C_s * (2 ^ B / (t * (Real.log t)^(B+1))
          + 1 / ((N:ℝ) ^ (1/4:ℝ) * (t * (Real.log t)^2))) := by
        apply mul_le_mul_of_nonneg_left _ hCs
        rw [hy]
        exact add_le_add hx (le_refl _)

private lemma one_le_log_of_four_le {x : ℝ} (hx : 4 ≤ x) : 1 ≤ Real.log x := by
  have h2 : Real.log 4 ≤ Real.log x := Real.log_le_log (by norm_num) hx
  have h3 : (1:ℝ) < Real.log 4 := by
    rw [show (4:ℝ) = 2^2 by norm_num, Real.log_pow]
    push_cast
    nlinarith [Real.log_two_gt_d9]
  linarith

private lemma intervalIntegrable_inv_mul_log_rpow {s : ℝ} {a b : ℝ} (ha : 2 ≤ a) (hab : a ≤ b) :
    IntervalIntegrable (fun t : ℝ => (t * (Real.log t) ^ s)⁻¹) MeasureTheory.volume a b := by
  apply ContinuousOn.intervalIntegrable_of_Icc hab
  apply ContinuousOn.inv₀
  · apply ContinuousOn.mul continuousOn_id
    apply ContinuousOn.rpow_const
    · exact Real.continuousOn_log.mono (fun t ht => by
        simp only [Set.mem_compl_iff, Set.mem_singleton_iff]
        have : (2:ℝ) ≤ t := le_trans ha ht.1
        linarith)
    · intro t ht
      exact Or.inl (ne_of_gt (Real.log_pos (by linarith [le_trans ha ht.1])))
  · intro t ht
    have ht2 : (2:ℝ) ≤ t := le_trans ha ht.1
    have hlog : Real.log t ≠ 0 := ne_of_gt (Real.log_pos (by linarith))
    exact mul_ne_zero (by linarith) (ne_of_gt (Real.rpow_pos_of_pos (Real.log_pos (by linarith)) s))

private lemma intervalIntegrable_inv_mul_log_sq {a b : ℝ} (ha : 2 ≤ a) (hab : a ≤ b) :
    IntervalIntegrable (fun t : ℝ => (t * (Real.log t) ^ 2)⁻¹) MeasureTheory.volume a b := by
  apply ContinuousOn.intervalIntegrable_of_Icc hab
  apply ContinuousOn.inv₀
  · apply ContinuousOn.mul continuousOn_id
    exact (Real.continuousOn_log.mono (fun t ht => by
        simp only [Set.mem_compl_iff, Set.mem_singleton_iff]
        have : (2:ℝ) ≤ t := le_trans ha ht.1
        linarith)).pow 2
  · intro t ht
    have ht2 : (2:ℝ) ≤ t := le_trans ha ht.1
    have hlog : Real.log t ≠ 0 := ne_of_gt (Real.log_pos (by linarith))
    exact mul_ne_zero (by linarith) (pow_ne_zero 2 hlog)

private lemma Rsum_cauchy {A : ℝ} (hA : 0 < A) (L : ℝ)
    (hL : ∀ B : ℝ, 0 < B → ∃ C : ℝ, 0 < C ∧ ∀ N : ℕ, 4 ≤ N →
      |chilog N - L| ≤ C * (1 / (Real.log N) ^ B + 1 / (N:ℝ) ^ (1/4:ℝ))) :
    ∃ C : ℝ, 0 < C ∧ ∀ N M : ℕ, 4 ≤ N → N ≤ M →
      |Rsum M - Rsum N| ≤ C * (1 / (Real.log N) ^ A + 1 / (N:ℝ) ^ (1/4:ℝ)) := by
  obtain ⟨Cs, hCspos, hCs⟩ := hL (A + 2) (by linarith)
  have hA2pos : 0 < A + 2 := by linarith
  have hCsnn : 0 ≤ Cs := le_of_lt hCspos
  refine ⟨Cs * (2 ^ (A + 2) / (A + 2) + 4), by positivity, fun N M hN hNM => ?_⟩
  have hNn : (4:ℝ) ≤ (N:ℝ) := by exact_mod_cast hN
  have hMn : (4:ℝ) ≤ (M:ℝ) := by exact_mod_cast (le_trans hN hNM)
  have hNpos : (0:ℝ) < (N:ℝ) := by linarith
  have hNM' : (N:ℝ) ≤ (M:ℝ) := by exact_mod_cast hNM
  have hlogN : 0 < Real.log (N:ℝ) := Real.log_pos (by linarith)
  have hlogM : 0 < Real.log (M:ℝ) := Real.log_pos (by linarith)
  have hlogNM : Real.log (N:ℝ) ≤ Real.log (M:ℝ) := Real.log_le_log hNpos hNM'
  have hlogN1 : 1 ≤ Real.log (N:ℝ) := one_le_log_of_four_le hNn
  have hlogM1 : 1 ≤ Real.log (M:ℝ) := one_le_log_of_four_le hMn
  have hXnn : 0 ≤ 1 / (Real.log (N:ℝ)) ^ A + 1 / (N:ℝ) ^ (1/4:ℝ) := by
    have h1 : 0 < (Real.log (N:ℝ)) ^ A := Real.rpow_pos_of_pos hlogN A
    have h2 : 0 < (N:ℝ) ^ (1/4:ℝ) := Real.rpow_pos_of_pos hNpos _
    positivity
  -- ### boundary terms
  have hXle : 1 / (Real.log (M:ℝ)) ^ A ≤ 1 / (Real.log (N:ℝ)) ^ A := by
    refine one_div_le_one_div_of_le (Real.rpow_pos_of_pos hlogN A) ?_
    exact Real.rpow_le_rpow (le_of_lt hlogN) hlogNM (le_of_lt hA)
  have hMleq : 1 / ((M:ℝ)) ^ (1/4:ℝ) ≤ 1 / ((N:ℝ)) ^ (1/4:ℝ) := by
    refine one_div_le_one_div_of_le (Real.rpow_pos_of_pos hNpos _) ?_
    exact Real.rpow_le_rpow (le_of_lt hNpos) hNM' (by norm_num)
  have hX' : 1 / (Real.log (M:ℝ)) ^ (A+2) ≤ 1 / (Real.log (N:ℝ)) ^ A := by
    have h1 : (Real.log (M:ℝ)) ^ A ≤ (Real.log (M:ℝ)) ^ (A+2) :=
      Real.rpow_le_rpow_of_exponent_le hlogM1 (by linarith)
    have h2 : 1 / (Real.log (M:ℝ)) ^ (A+2) ≤ 1 / (Real.log (M:ℝ)) ^ A :=
      one_div_le_one_div_of_le (Real.rpow_pos_of_pos hlogM A) h1
    exact le_trans h2 hXle
  have hT1 : |(chilog M - L) / Real.log (M:ℝ)|
      ≤ Cs * (1 / (Real.log (N:ℝ)) ^ A + 1 / (N:ℝ) ^ (1/4:ℝ)) := by
    rw [abs_div, abs_of_pos hlogM]
    have h1 := hCs M (le_trans hN hNM)
    have step : |chilog M - L| / Real.log (M:ℝ)
        ≤ Cs * (1 / (Real.log (M:ℝ)) ^ (A+2) + 1 / (M:ℝ) ^ (1/4:ℝ)) / Real.log (M:ℝ) :=
      div_le_div_of_nonneg_right h1 (le_of_lt hlogM)
    refine le_trans step ?_
    have hu : (1 / (Real.log (M:ℝ)) ^ (A+2) + 1 / (M:ℝ) ^ (1/4:ℝ)) / Real.log (M:ℝ)
        ≤ 1 / (Real.log (N:ℝ)) ^ A + 1 / (N:ℝ) ^ (1/4:ℝ) := by
      have ha : 0 ≤ 1 / (Real.log (M:ℝ)) ^ (A+2) := by positivity
      have hb : 0 ≤ 1 / (M:ℝ) ^ (1/4:ℝ) := by positivity
      have hdiv : (1 / (Real.log (M:ℝ)) ^ (A+2) + 1 / (M:ℝ) ^ (1/4:ℝ)) / Real.log (M:ℝ)
          ≤ 1 / (Real.log (M:ℝ)) ^ (A+2) + 1 / (M:ℝ) ^ (1/4:ℝ) := by
        rw [div_le_iff₀ hlogM]
        nlinarith [hlogM1, ha, hb]
      linarith [hdiv, hX', hMleq]
    calc Cs * (1 / (Real.log (M:ℝ)) ^ (A+2) + 1 / (M:ℝ) ^ (1/4:ℝ)) / Real.log (M:ℝ)
        = Cs * ((1 / (Real.log (M:ℝ)) ^ (A+2) + 1 / (M:ℝ) ^ (1/4:ℝ)) / Real.log (M:ℝ)) := by
          rw [mul_div_assoc]
      _ ≤ Cs * (1 / (Real.log (N:ℝ)) ^ A + 1 / (N:ℝ) ^ (1/4:ℝ)) :=
          mul_le_mul_of_nonneg_left hu hCsnn
  have hT2 : |(chilog N - L) / Real.log (N:ℝ)|
      ≤ Cs * (1 / (Real.log (N:ℝ)) ^ A + 1 / (N:ℝ) ^ (1/4:ℝ)) := by
    rw [abs_div, abs_of_pos hlogN]
    have h1 := hCs N hN
    have step : |chilog N - L| / Real.log (N:ℝ)
        ≤ Cs * (1 / (Real.log (N:ℝ)) ^ (A+2) + 1 / (N:ℝ) ^ (1/4:ℝ)) / Real.log (N:ℝ) :=
      div_le_div_of_nonneg_right h1 (le_of_lt hlogN)
    refine le_trans step ?_
    have hu : (1 / (Real.log (N:ℝ)) ^ (A+2) + 1 / (N:ℝ) ^ (1/4:ℝ)) / Real.log (N:ℝ)
        ≤ 1 / (Real.log (N:ℝ)) ^ A + 1 / (N:ℝ) ^ (1/4:ℝ) := by
      have ha : 0 ≤ 1 / (Real.log (N:ℝ)) ^ (A+2) := by positivity
      have hb : 0 ≤ 1 / (N:ℝ) ^ (1/4:ℝ) := by positivity
      have hdiv : (1 / (Real.log (N:ℝ)) ^ (A+2) + 1 / (N:ℝ) ^ (1/4:ℝ)) / Real.log (N:ℝ)
          ≤ 1 / (Real.log (N:ℝ)) ^ (A+2) + 1 / (N:ℝ) ^ (1/4:ℝ) := by
        rw [div_le_iff₀ hlogN]
        nlinarith [hlogN1, ha, hb]
      have hAA : 1 / (Real.log (N:ℝ)) ^ (A+2) ≤ 1 / (Real.log (N:ℝ)) ^ A := by
        have h1 : (Real.log (N:ℝ)) ^ A ≤ (Real.log (N:ℝ)) ^ (A+2) :=
          Real.rpow_le_rpow_of_exponent_le hlogN1 (by linarith)
        exact one_div_le_one_div_of_le (Real.rpow_pos_of_pos hlogN A) h1
      linarith [hdiv, hAA]
    calc Cs * (1 / (Real.log (N:ℝ)) ^ (A+2) + 1 / (N:ℝ) ^ (1/4:ℝ)) / Real.log (N:ℝ)
        = Cs * ((1 / (Real.log (N:ℝ)) ^ (A+2) + 1 / (N:ℝ) ^ (1/4:ℝ)) / Real.log (N:ℝ)) := by
          rw [mul_div_assoc]
      _ ≤ Cs * (1 / (Real.log (N:ℝ)) ^ A + 1 / (N:ℝ) ^ (1/4:ℝ)) :=
          mul_le_mul_of_nonneg_left hu hCsnn
  -- ### the integral term
  set I1 : ℝ := ∫ t in (N:ℝ)..(M:ℝ), chilog ⌊t⌋₊ / (t * (Real.log t) ^ 2) with hI1def
  set I3 : ℝ := ∫ t in (N:ℝ)..(M:ℝ), (t * (Real.log t) ^ 2)⁻¹ with hI3def
  set I4 : ℝ := ∫ t in (N:ℝ)..(M:ℝ), (t * (Real.log t) ^ (A+3))⁻¹ with hI4def
  have hi1 : IntervalIntegrable (fun t : ℝ => chilog ⌊t⌋₊ / (t * (Real.log t) ^ 2))
      MeasureTheory.volume (N:ℝ) (M:ℝ) := intervalIntegrable_chilog_div (by linarith) hNM'
  have hi3 : IntervalIntegrable (fun t : ℝ => (t * (Real.log t) ^ 2)⁻¹)
      MeasureTheory.volume (N:ℝ) (M:ℝ) := intervalIntegrable_inv_mul_log_sq (by linarith) hNM'
  have hi4 : IntervalIntegrable (fun t : ℝ => (t * (Real.log t) ^ (A+3))⁻¹)
      MeasureTheory.volume (N:ℝ) (M:ℝ) :=
    intervalIntegrable_inv_mul_log_rpow (s := A+3) (by linarith) hNM'
  have hI3 : I3 = (Real.log (N:ℝ))⁻¹ - (Real.log (M:ℝ))⁻¹ :=
    hI3def.trans (Commons.NumberTheory.FriedlanderIwaniec.integral_inv_log_sq (by linarith) hNM')
  have hI4' := hI4def.trans (integral_inv_mul_log_rpow (s := A+3) (by linarith) (by linarith) hNM')
  have hI4 : I4 = (A+2)⁻¹ * ((Real.log (N:ℝ)) ^ (1-(A+3)) - (Real.log (M:ℝ)) ^ (1-(A+3))) := by
    rw [hI4', show A + 3 - 1 = A + 2 by ring]
  have hintF : IntervalIntegrable (fun t : ℝ => (chilog ⌊t⌋₊ - L) / (t * (Real.log t) ^ 2))
      MeasureTheory.volume (N:ℝ) (M:ℝ) := by
    refine (hi1.sub (hi3.const_mul L)).congr (fun t ht => ?_)
    rw [Set.uIoc_of_le hNM'] at ht
    have hDt : (0:ℝ) < t := by linarith [ht.1]
    have hlogt : Real.log t ≠ 0 := ne_of_gt (Real.log_pos (by linarith [ht.1]))
    have hD : t * (Real.log t) ^ 2 ≠ 0 := mul_ne_zero (ne_of_gt hDt) (pow_ne_zero 2 hlogt)
    rw [show L * (t * (Real.log t) ^ 2)⁻¹ = L / (t * (Real.log t) ^ 2) from by rw [div_eq_mul_inv],
      ← sub_div]
  have hpt_id : ∀ t : ℝ,
      Cs * (2 ^ (A+2) / (t * (Real.log t) ^ (A+3)) + 1 / ((N:ℝ) ^ (1/4:ℝ) * (t * (Real.log t) ^ 2)))
        = Cs * (2 ^ (A+2) * (t * (Real.log t) ^ (A+3))⁻¹
          + ((N:ℝ) ^ (1/4:ℝ))⁻¹ * (t * (Real.log t) ^ 2)⁻¹) := by
    intro t
    rw [div_eq_mul_inv, div_eq_mul_inv, one_mul, mul_inv_rev]
    ring
  have hMajInt : IntervalIntegrable
      (fun t : ℝ => Cs * (2 ^ (A+2) / (t * (Real.log t) ^ (A+3))
        + 1 / ((N:ℝ) ^ (1/4:ℝ) * (t * (Real.log t) ^ 2)))) MeasureTheory.volume (N:ℝ) (M:ℝ) := by
    rw [show (fun t : ℝ => Cs * (2 ^ (A+2) / (t * (Real.log t) ^ (A+3))
          + 1 / ((N:ℝ) ^ (1/4:ℝ) * (t * (Real.log t) ^ 2))))
        = (fun t : ℝ => Cs * (2 ^ (A+2) * (t * (Real.log t) ^ (A+3))⁻¹
          + ((N:ℝ) ^ (1/4:ℝ))⁻¹ * (t * (Real.log t) ^ 2)⁻¹)) from funext hpt_id]
    exact ((hi4.const_mul (2 ^ (A+2))).add (hi3.const_mul ((N:ℝ) ^ (1/4:ℝ))⁻¹)).const_mul Cs
  have hpt : ∀ t ∈ Set.Icc (N:ℝ) (M:ℝ),
      |(chilog ⌊t⌋₊ - L) / (t * (Real.log t) ^ 2)|
        ≤ Cs * (2 ^ (A+2) / (t * (Real.log t) ^ (A+3))
          + 1 / ((N:ℝ) ^ (1/4:ℝ) * (t * (Real.log t) ^ 2))) := by
    intro t ht
    have ht4 : 4 ≤ t := le_trans hNn ht.1
    have hb := chilog_sub_L_integrand_bound (B := A+2) hA2pos hCsnn hCs hN ht4 ht.1
    rw [show A + 2 + 1 = A + 3 by ring] at hb
    exact hb
  have hmono : ∫ t in (N:ℝ)..(M:ℝ), |(chilog ⌊t⌋₊ - L) / (t * (Real.log t) ^ 2)|
      ≤ ∫ t in (N:ℝ)..(M:ℝ), Cs * (2 ^ (A+2) / (t * (Real.log t) ^ (A+3))
          + 1 / ((N:ℝ) ^ (1/4:ℝ) * (t * (Real.log t) ^ 2))) :=
    intervalIntegral.integral_mono_on hNM' (hintF.abs) hMajInt (fun t ht => hpt t ht)
  have hInt_g : ∫ t in (N:ℝ)..(M:ℝ), Cs * (2 ^ (A+2) / (t * (Real.log t) ^ (A+3))
        + 1 / ((N:ℝ) ^ (1/4:ℝ) * (t * (Real.log t) ^ 2)))
      = Cs * (2 ^ (A+2) * I4 + ((N:ℝ) ^ (1/4:ℝ))⁻¹ * I3) := by
    rw [show (fun t : ℝ => Cs * (2 ^ (A+2) / (t * (Real.log t) ^ (A+3))
          + 1 / ((N:ℝ) ^ (1/4:ℝ) * (t * (Real.log t) ^ 2))))
        = (fun t : ℝ => Cs * (2 ^ (A+2) * (t * (Real.log t) ^ (A+3))⁻¹
          + ((N:ℝ) ^ (1/4:ℝ))⁻¹ * (t * (Real.log t) ^ 2)⁻¹)) from funext hpt_id]
    rw [intervalIntegral.integral_const_mul]
    congr 1
    rw [intervalIntegral.integral_add (hi4.const_mul (2 ^ (A+2))) (hi3.const_mul ((N:ℝ) ^ (1/4:ℝ))⁻¹)]
    rw [intervalIntegral.integral_const_mul, intervalIntegral.integral_const_mul]
  have hIeq_exp : ∫ t in (N:ℝ)..(M:ℝ), (chilog ⌊t⌋₊ - L) / (t * (Real.log t) ^ 2)
      = (∫ t in (N:ℝ)..(M:ℝ), chilog ⌊t⌋₊ / (t * (Real.log t) ^ 2))
        - L * (∫ t in (N:ℝ)..(M:ℝ), (t * (Real.log t) ^ 2)⁻¹) := by
    rw [← intervalIntegral.integral_const_mul L (fun t : ℝ => (t * (Real.log t) ^ 2)⁻¹)]
    rw [← intervalIntegral.integral_sub hi1 (hi3.const_mul L)]
    apply intervalIntegral.integral_congr
    intro t ht
    rw [Set.uIcc_of_le hNM'] at ht
    have hDt : (0:ℝ) < t := by linarith [ht.1]
    have hlogt : Real.log t ≠ 0 := ne_of_gt (Real.log_pos (by linarith [ht.1]))
    have hD : t * (Real.log t) ^ 2 ≠ 0 := mul_ne_zero (ne_of_gt hDt) (pow_ne_zero 2 hlogt)
    simp only
    rw [show L * (t * (Real.log t) ^ 2)⁻¹ = L / (t * (Real.log t) ^ 2) from by rw [div_eq_mul_inv],
      ← sub_div]
  have hIeq : ∫ t in (N:ℝ)..(M:ℝ), (chilog ⌊t⌋₊ - L) / (t * (Real.log t) ^ 2) = I1 - L * I3 := hIeq_exp
  have hIbound : |I1 - L * I3| ≤ Cs * (2 ^ (A+2) * ((A+2)⁻¹ * (1 / (Real.log (N:ℝ)) ^ (A+2)))
      + ((N:ℝ) ^ (1/4:ℝ))⁻¹ * (1 / Real.log (N:ℝ))) := by
    rw [show |I1 - L * I3| = |∫ t in (N:ℝ)..(M:ℝ), (chilog ⌊t⌋₊ - L) / (t * (Real.log t) ^ 2)| from by
      rw [hIeq]]
    refine le_trans (intervalIntegral.abs_integral_le_integral_abs hNM') ?_
    refine le_trans hmono ?_
    rw [hInt_g]
    apply mul_le_mul_of_nonneg_left _ hCsnn
    apply add_le_add
    · apply mul_le_mul_of_nonneg_left _ (by positivity)
      rw [hI4]
      have h1 : 0 ≤ (Real.log (M:ℝ)) ^ (-(A+2)) := Real.rpow_nonneg (le_of_lt hlogM) _
      have hNp : (Real.log (N:ℝ)) ^ (-(A+2)) = 1 / (Real.log (N:ℝ)) ^ (A+2) := by
        rw [one_div, Real.rpow_neg (le_of_lt hlogN)]
      rw [show 1 - (A+3) = -(A+2) by ring, hNp]
      have h2 : 0 < (A+2)⁻¹ := by positivity
      nlinarith [h1, h2]
    · apply mul_le_mul_of_nonneg_left _ (by positivity)
      rw [hI3, one_div]
      exact sub_le_self _ (le_of_lt (inv_pos.mpr hlogM))
  have hIbound2 : |I1 - L * I3|
      ≤ Cs * (2 ^ (A+2) / (A + 2) + 1) * (1 / (Real.log (N:ℝ)) ^ A + 1 / (N:ℝ) ^ (1/4:ℝ)) := by
    refine le_trans hIbound ?_
    have hbase : 0 ≤ 2 ^ (A+2) / (A + 2) := by positivity
    have hX1 : 1 / (Real.log (N:ℝ)) ^ (A+2) ≤ 1 / (Real.log (N:ℝ)) ^ A + 1 / (N:ℝ) ^ (1/4:ℝ) := by
      have h1 : (Real.log (N:ℝ)) ^ A ≤ (Real.log (N:ℝ)) ^ (A+2) :=
        Real.rpow_le_rpow_of_exponent_le hlogN1 (by linarith)
      have h2 : 1 / (Real.log (N:ℝ)) ^ (A+2) ≤ 1 / (Real.log (N:ℝ)) ^ A :=
        one_div_le_one_div_of_le (Real.rpow_pos_of_pos hlogN A) h1
      have h3 : (0:ℝ) ≤ 1 / (N:ℝ) ^ (1/4:ℝ) := by positivity
      linarith
    have hX2 : ((N:ℝ) ^ (1/4:ℝ))⁻¹ * (1 / Real.log (N:ℝ))
        ≤ 1 / (Real.log (N:ℝ)) ^ A + 1 / (N:ℝ) ^ (1/4:ℝ) := by
      have h3 : (0:ℝ) ≤ 1 / (Real.log (N:ℝ)) ^ A := by positivity
      have h4 : ((N:ℝ) ^ (1/4:ℝ))⁻¹ * (1 / Real.log (N:ℝ)) ≤ ((N:ℝ) ^ (1/4:ℝ))⁻¹ * 1 := by
        apply mul_le_mul_of_nonneg_left _ (by positivity)
        rw [one_div]
        exact inv_le_one_of_one_le₀ hlogN1
      have h5 : ((N:ℝ) ^ (1/4:ℝ))⁻¹ * 1 = 1 / (N:ℝ) ^ (1/4:ℝ) := by
        rw [mul_one, inv_eq_one_div]
      rw [h5] at h4
      linarith
    calc Cs * (2 ^ (A+2) * ((A+2)⁻¹ * (1 / (Real.log (N:ℝ)) ^ (A+2)))
            + ((N:ℝ) ^ (1/4:ℝ))⁻¹ * (1 / Real.log (N:ℝ)))
        = Cs * (2 ^ (A+2) / (A + 2) * (1 / (Real.log (N:ℝ)) ^ (A+2))
            + ((N:ℝ) ^ (1/4:ℝ))⁻¹ * (1 / Real.log (N:ℝ))) := by
          congr 1
          rw [div_eq_mul_inv]
          ring
      _ ≤ Cs * ((2 ^ (A+2) / (A + 2) + 1)
            * (1 / (Real.log (N:ℝ)) ^ A + 1 / (N:ℝ) ^ (1/4:ℝ))) := by
          apply mul_le_mul_of_nonneg_left _ hCsnn
          have hsum := add_le_add (mul_le_mul_of_nonneg_left hX1 hbase) hX2
          nlinarith [hsum]
      _ = Cs * (2 ^ (A+2) / (A + 2) + 1) * (1 / (Real.log (N:ℝ)) ^ A + 1 / (N:ℝ) ^ (1/4:ℝ)) := by
          ring
  -- ### assembling
  have hbdry : (chilog M - L) / Real.log (M:ℝ) - (chilog N - L) / Real.log (N:ℝ)
      = (chilog M / Real.log (M:ℝ) - chilog N / Real.log (N:ℝ))
        - L * ((Real.log (M:ℝ))⁻¹ - (Real.log (N:ℝ))⁻¹) := by
    rw [div_eq_mul_inv (chilog M - L), div_eq_mul_inv (chilog N - L),
      div_eq_mul_inv (chilog M), div_eq_mul_inv (chilog N)]
    ring
  have hmain : Rsum M - Rsum N
      = ((chilog M - L) / Real.log (M:ℝ) - (chilog N - L) / Real.log (N:ℝ)) + (I1 - L * I3) := by
    have h1 : (chilog M - L) / Real.log (M:ℝ) - (chilog N - L) / Real.log (N:ℝ) + (I1 - L * I3)
        = (chilog M / Real.log (M:ℝ) - chilog N / Real.log (N:ℝ)) + I1 := by
      rw [hbdry, hI3]
      ring
    rw [h1]
    exact Rsum_diff (by omega : 2 ≤ N) hNM
  have htri : |Rsum M - Rsum N|
      ≤ |(chilog M - L) / Real.log (M:ℝ)| + |(chilog N - L) / Real.log (N:ℝ)|
        + |I1 - L * I3| := by
    rw [hmain]
    have h2 : |(chilog M - L) / Real.log (M:ℝ) - (chilog N - L) / Real.log (N:ℝ)|
        ≤ |(chilog M - L) / Real.log (M:ℝ)| + |(chilog N - L) / Real.log (N:ℝ)| := by
      have := abs_sub_le ((chilog M - L) / Real.log (M:ℝ)) 0 ((chilog N - L) / Real.log (N:ℝ))
      simpa only [sub_zero, zero_sub, abs_neg] using this
    have h3 := abs_add_le ((chilog M - L) / Real.log (M:ℝ) - (chilog N - L) / Real.log (N:ℝ))
      (I1 - L * I3)
    linarith [h2, h3]
  calc |Rsum M - Rsum N|
      ≤ Cs * (1 / (Real.log (N:ℝ)) ^ A + 1 / (N:ℝ) ^ (1/4:ℝ))
        + Cs * (2 ^ (A+2) / (A + 2) + 1) * (1 / (Real.log (N:ℝ)) ^ A + 1 / (N:ℝ) ^ (1/4:ℝ))
        + Cs * (1 / (Real.log (N:ℝ)) ^ A + 1 / (N:ℝ) ^ (1/4:ℝ)) := by
        linarith [htri, hT1, hT2, hIbound2]
    _ = Cs * (2 ^ (A+2) / (A + 2) + 3) * (1 / (Real.log (N:ℝ)) ^ A + 1 / (N:ℝ) ^ (1/4:ℝ)) := by
        ring
    _ ≤ Cs * (2 ^ (A+2) / (A + 2) + 4) * (1 / (Real.log (N:ℝ)) ^ A + 1 / (N:ℝ) ^ (1/4:ℝ)) := by
        apply mul_le_mul_of_nonneg_right _ hXnn
        apply mul_le_mul_of_nonneg_left _ hCsnn
        linarith

private lemma Rsum_limit (L : ℝ)
    (hL : ∀ B : ℝ, 0 < B → ∃ C : ℝ, 0 < C ∧ ∀ N : ℕ, 4 ≤ N →
      |chilog N - L| ≤ C * (1 / (Real.log N) ^ B + 1 / (N:ℝ) ^ (1/4:ℝ))) :
    ∃ L₀ : ℝ, ∀ A : ℝ, 0 < A → ∃ C : ℝ, 0 < C ∧ ∀ N : ℕ, 4 ≤ N →
      |Rsum N - L₀| ≤ C * (1 / (Real.log N) ^ A + 1 / (N:ℝ) ^ (1/4:ℝ)) :=
  limit_of_cauchy_rate (u := Rsum) (K := 4) (by norm_num) (fun A hA => Rsum_cauchy hA L hL)

private lemma primesLE_mono' {K L : ℕ} (h : K ≤ L) : K.primesLE ⊆ L.primesLE := by
  intro p hp
  simp only [Nat.primesLE_eq_filter_range, Finset.mem_filter, Finset.mem_range] at hp ⊢
  exact ⟨by omega, hp.2⟩

theorem chi4_primeRecips_sub_const_powLog :
    ∀ A : ℝ, 0 < A → ∃ C₀ C : ℝ, 0 < C ∧ ∀ x : ℝ, 2 ≤ x →
      |(∑ p ∈ (⌊x⌋₊).primesLE,
          (Commons.NumberTheory.DirichletCharacter.chi4Fun ((p : ℕ) : ZMod 4)).re / (p : ℝ)) - C₀|
        ≤ C / (Real.log x) ^ A := by
  intro A hA
  obtain ⟨L, hL⟩ := chilog_limit
  obtain ⟨L₀, hL₀⟩ := Rsum_limit L hL
  obtain ⟨C₁, hC₁pos, hC₁⟩ := hL₀ (A + 1) (by linarith)
  have hC₁nn : 0 ≤ C₁ := le_of_lt hC₁pos
  have hA1 : 0 < A + 1 := by linarith
  have hlogA_o : (fun x : ℝ => (Real.log x) ^ A) =o[Filter.atTop] (fun x : ℝ => x ^ (1/4:ℝ)) :=
    isLittleO_log_rpow_rpow_atTop A (by norm_num)
  have hb2 : ∀ᶠ x : ℝ in Filter.atTop,
      (Real.log x) ^ A ≤ 2 ^ (-(1/4):ℝ) * x ^ (1/4:ℝ) := by
    have hb0 : Asymptotics.IsBigOWith (2 ^ (-(1/4):ℝ)) Filter.atTop
        (fun x : ℝ => (Real.log x) ^ A) (fun x : ℝ => x ^ (1/4:ℝ)) :=
      (Asymptotics.isLittleO_iff_forall_isBigOWith.mp hlogA_o)
        (Real.rpow_pos_of_pos (by norm_num : (0:ℝ) < 2) _)
    have hb := Asymptotics.IsBigOWith.bound hb0
    filter_upwards [hb, Filter.eventually_ge_atTop (1:ℝ)] with x hx hx1
    rw [Real.norm_of_nonneg (Real.rpow_nonneg (Real.log_nonneg hx1) A),
        Real.norm_of_nonneg (Real.rpow_nonneg (by linarith) (1/4:ℝ))] at hx
    exact hx
  have hev : ∀ᶠ x : ℝ in Filter.atTop,
      |Rsum ⌊x⌋₊ - L₀| ≤ C₁ * (2 ^ (A+1) + 1) / (Real.log x) ^ A := by
    filter_upwards [hb2, Filter.eventually_ge_atTop (4:ℝ)] with x hxb hx4
    have hxpos : (0:ℝ) < x := by linarith
    have hlogx : 0 < Real.log x := Real.log_pos (by linarith)
    have hlogx1 : 1 ≤ Real.log x := one_le_log_of_four_le hx4
    have hfl4 : 4 ≤ ⌊x⌋₊ := Nat.le_floor hx4
    have hfl4R : (4:ℝ) ≤ (⌊x⌋₊ : ℝ) := by exact_mod_cast hfl4
    have hflpos : (0:ℝ) < (⌊x⌋₊ : ℝ) := by linarith
    have hlogfl : 0 < Real.log (⌊x⌋₊ : ℝ) := Real.log_pos (by linarith)
    have hR := hC₁ ⌊x⌋₊ hfl4
    -- term 1 with the exponent `A+1`
    have hhalf : Real.log x / 2 ≤ Real.log (⌊x⌋₊ : ℝ) := log_floor_ge_half x hx4
    have h1 : (Real.log x / 2) ^ (A+1) ≤ (Real.log (⌊x⌋₊ : ℝ)) ^ (A+1) :=
      Real.rpow_le_rpow (by positivity) hhalf (by linarith)
    have h2 : (Real.log x / 2) ^ (A+1) = (Real.log x) ^ (A+1) / 2 ^ (A+1) :=
      Real.div_rpow (le_of_lt hlogx) (by norm_num) (A+1)
    have h3 : 1 / (Real.log (⌊x⌋₊ : ℝ)) ^ (A+1) ≤ 2 ^ (A+1) / (Real.log x) ^ A := by
      have h4 : (Real.log x) ^ (A+1) ≤ 2 ^ (A+1) * (Real.log (⌊x⌋₊ : ℝ)) ^ (A+1) := by
        have h5 : (Real.log x) ^ (A+1) / 2 ^ (A+1) ≤ (Real.log (⌊x⌋₊ : ℝ)) ^ (A+1) := h2 ▸ h1
        have h6 : (0:ℝ) < 2 ^ (A+1) := Real.rpow_pos_of_pos (by norm_num) _
        rw [div_le_iff₀ h6] at h5
        rwa [mul_comm] at h5
      have hA_le : (Real.log x) ^ A ≤ (Real.log x) ^ (A+1) :=
        Real.rpow_le_rpow_of_exponent_le hlogx1 (by linarith : A ≤ A + 1)
      calc 1 / (Real.log (⌊x⌋₊ : ℝ)) ^ (A+1)
          ≤ 2 ^ (A+1) / (Real.log x) ^ (A+1) := by
            rw [div_le_div_iff₀ (Real.rpow_pos_of_pos hlogfl _) (Real.rpow_pos_of_pos hlogx _), one_mul]
            exact h4
        _ ≤ 2 ^ (A+1) / (Real.log x) ^ A :=
            div_le_div_of_nonneg_left (by positivity) (Real.rpow_pos_of_pos hlogx A) hA_le
    -- term 2 with `1/4`
    have hfloor_half : x / 2 ≤ (⌊x⌋₊ : ℝ) := by
      have h := Nat.lt_floor_add_one x
      linarith
    have h7 : (x / 2) ^ (1/4:ℝ) ≤ (⌊x⌋₊ : ℝ) ^ (1/4:ℝ) :=
      Real.rpow_le_rpow (by linarith) hfloor_half (by norm_num)
    have h8 : (x / 2) ^ (1/4:ℝ) = x ^ (1/4:ℝ) * (2 ^ (1/4:ℝ))⁻¹ :=
      Real.div_rpow (le_of_lt hxpos) (by norm_num : (0:ℝ) ≤ 2) (1/4:ℝ)
    have hb' : (Real.log x) ^ A ≤ x ^ (1/4:ℝ) * (2 ^ (1/4:ℝ))⁻¹ := by
      have hdiv : 2 ^ (-(1/4):ℝ) * x ^ (1/4:ℝ) = x ^ (1/4:ℝ) * (2 ^ (1/4:ℝ))⁻¹ := by
        rw [Real.rpow_neg (by norm_num : (0:ℝ) ≤ 2), mul_comm]
      rwa [hdiv] at hxb
    have h9 : (Real.log x) ^ A ≤ (⌊x⌋₊ : ℝ) ^ (1/4:ℝ) := by
      have h10 : x ^ (1/4:ℝ) * (2 ^ (1/4:ℝ))⁻¹ ≤ (⌊x⌋₊ : ℝ) ^ (1/4:ℝ) := by
        rw [← h8]; exact h7
      linarith [hb', h10]
    have h13 : 1 / (⌊x⌋₊ : ℝ) ^ (1/4:ℝ) ≤ 1 / (Real.log x) ^ A := by
      rw [div_le_div_iff₀ (Real.rpow_pos_of_pos hflpos (1/4:ℝ)) (Real.rpow_pos_of_pos hlogx A),
        one_mul, one_mul]
      exact h9
    have hR' : |Rsum ⌊x⌋₊ - L₀| ≤ C₁ * (2 ^ (A+1) / (Real.log x) ^ A + 1 / (Real.log x) ^ A) := by
      refine le_trans hR ?_
      apply mul_le_mul_of_nonneg_left _ hC₁nn
      linarith [h3, h13]
    calc |Rsum ⌊x⌋₊ - L₀|
        ≤ C₁ * (2 ^ (A+1) / (Real.log x) ^ A + 1 / (Real.log x) ^ A) := hR'
      _ = C₁ * (2 ^ (A+1) + 1) / (Real.log x) ^ A := by
          rw [← add_div, mul_div_assoc]
  obtain ⟨Y, hY⟩ := Filter.eventually_atTop.mp hev
  set S : ℝ := ∑ p ∈ (⌊max Y 4⌋₊).primesLE, 1 / (p : ℝ) with hSdef
  have hSnn : 0 ≤ S := by
    rw [hSdef]
    exact Finset.sum_nonneg (fun p _ => by positivity)
  have hK : ∀ K : ℕ, K ≤ ⌊max Y 4⌋₊ → |Rsum K| ≤ S := by
    intro K hK
    rw [Rsum_eq_primesLE K, hSdef]
    calc |∑ p ∈ K.primesLE, c4 p / (p:ℝ)|
        ≤ ∑ p ∈ K.primesLE, |c4 p / (p:ℝ)| := Finset.abs_sum_le_sum_abs _ _
      _ ≤ ∑ p ∈ K.primesLE, 1 / (p:ℝ) := by
          refine Finset.sum_le_sum (fun p hp => ?_)
          have hp2 : (0:ℝ) < (p:ℝ) := by exact_mod_cast (Nat.prime_of_mem_primesLE hp).pos
          rw [abs_div, abs_of_pos hp2]
          exact div_le_div_of_nonneg_right (abs_c4_le_one p) (le_of_lt hp2)
      _ ≤ ∑ p ∈ (⌊max Y 4⌋₊).primesLE, 1 / (p:ℝ) := by
          refine Finset.sum_le_sum_of_subset_of_nonneg (fun p hp => ?_) (fun p _ _ => by positivity)
          simp only [Nat.mem_primesLE] at hp ⊢
          exact ⟨le_trans hp.1 hK, hp.2⟩
  have hY0ge : (4:ℝ) ≤ max Y 4 := le_max_right _ _
  refine ⟨L₀, max (C₁ * (2 ^ (A+1) + 1)) ((S + |L₀|) * (Real.log (max Y 4)) ^ A) + 1, ?_,
    fun x hx2 => ?_⟩
  · have h1 : 0 < Real.log (max Y 4) := Real.log_pos (by linarith)
    have h2 : 0 < (Real.log (max Y 4)) ^ A := Real.rpow_pos_of_pos h1 A
    have h3 : 0 ≤ (S + |L₀|) * (Real.log (max Y 4)) ^ A := by positivity
    have h4 : 0 ≤ C₁ * (2 ^ (A+1) + 1) := by positivity
    have h5 : C₁ * (2 ^ (A+1) + 1) ≤ max (C₁ * (2 ^ (A+1) + 1)) ((S + |L₀|) * (Real.log (max Y 4)) ^ A) :=
      le_max_left _ _
    linarith
  · have hsum : (∑ p ∈ (⌊x⌋₊).primesLE,
        (Commons.NumberTheory.DirichletCharacter.chi4Fun ((p : ℕ) : ZMod 4)).re / (p : ℝ))
        = Rsum ⌊x⌋₊ := by
      rw [Rsum_eq_primesLE]
      rfl
    rw [hsum]
    rcases le_total (max Y 4) x with hx | hx
    · have h1 : |Rsum ⌊x⌋₊ - L₀| ≤ C₁ * (2 ^ (A+1) + 1) / (Real.log x) ^ A :=
        hY x (le_trans (le_max_left _ _) hx)
      have hlogx : 0 < Real.log x := Real.log_pos (by linarith)
      have h2 : C₁ * (2 ^ (A+1) + 1) / (Real.log x) ^ A
          ≤ (max (C₁ * (2 ^ (A+1) + 1)) ((S + |L₀|) * (Real.log (max Y 4)) ^ A) + 1)
            / (Real.log x) ^ A := by
        apply div_le_div_of_nonneg_right _ (le_of_lt (Real.rpow_pos_of_pos hlogx A))
        linarith [le_max_left (C₁ * (2 ^ (A+1) + 1)) ((S + |L₀|) * (Real.log (max Y 4)) ^ A)]
      linarith
    · have hlogx : 0 < Real.log x := Real.log_pos (by linarith)
      have hlogY : 0 < Real.log (max Y 4) := Real.log_pos (by linarith)
      have hlogle : Real.log x ≤ Real.log (max Y 4) := Real.log_le_log (by linarith) hx
      have hpowle : (Real.log x) ^ A ≤ (Real.log (max Y 4)) ^ A :=
        Real.rpow_le_rpow (le_of_lt hlogx) hlogle (le_of_lt hA)
      have hKle : ⌊x⌋₊ ≤ ⌊max Y 4⌋₊ := Nat.floor_mono hx
      have hR := hK ⌊x⌋₊ hKle
      have hsub : |Rsum ⌊x⌋₊ - L₀| ≤ S + |L₀| := by
        have h := abs_sub_le (Rsum ⌊x⌋₊) 0 L₀
        simp only [sub_zero, zero_sub, abs_neg] at h
        linarith
      have hSnL : 0 ≤ S + |L₀| := add_nonneg hSnn (abs_nonneg L₀)
      have h4 : (S + |L₀|) * (Real.log x) ^ A ≤ (S + |L₀|) * (Real.log (max Y 4)) ^ A :=
        mul_le_mul_of_nonneg_left hpowle hSnL
      have h5 : (S + |L₀|) * (Real.log (max Y 4)) ^ A
          ≤ max (C₁ * (2 ^ (A+1) + 1)) ((S + |L₀|) * (Real.log (max Y 4)) ^ A) + 1 := by
        have h := le_max_right (C₁ * (2 ^ (A+1) + 1)) ((S + |L₀|) * (Real.log (max Y 4)) ^ A)
        linarith
      have h6 : S + |L₀| ≤ (max (C₁ * (2 ^ (A+1) + 1)) ((S + |L₀|) * (Real.log (max Y 4)) ^ A) + 1)
          / (Real.log x) ^ A := by
        rw [le_div_iff₀ (Real.rpow_pos_of_pos hlogx A)]
        linarith [h4, h5]
      linarith [hsub, h6]


end Commons.NumberTheory.DirichletCharacter
