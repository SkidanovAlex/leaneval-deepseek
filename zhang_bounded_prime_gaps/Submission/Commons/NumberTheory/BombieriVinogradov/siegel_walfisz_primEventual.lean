import Mathlib
import Submission.Commons.NumberTheory.BombieriVinogradov.siegel_walfisz_chi_range
import Submission.Commons.NumberTheory.Zeta.psi_sub_id_powLog_real

namespace Commons.NumberTheory.BombieriVinogradov

open scoped BigOperators
open Finset Filter
open Classical

set_option linter.unusedVariables false
set_option linter.style.haveILetI false

private noncomputable def chiS (q : ℕ) (χ : DirichletCharacter ℂ q) (y : ℕ) : ℂ :=
  ∑ n ∈ Finset.range (y + 1), ((ArithmeticFunction.vonMangoldt n : ℝ) : ℂ) * χ ((n : ℕ) : ZMod q)

private noncomputable def chiSupT (q : ℕ) (χ : DirichletCharacter ℂ q) (X : ℕ) : ℝ :=
  sSup ((fun y : ℕ => ‖chiS q χ y - (if χ = 1 then (y : ℂ) else 0)‖) '' Set.Icc 1 X)

private noncomputable def psiSum (y : ℕ) : ℝ :=
  ∑ n ∈ Finset.range (y + 1), ArithmeticFunction.vonMangoldt n

private lemma psiSum_eq_psi (y : ℕ) : psiSum y = Chebyshev.psi (y : ℝ) := by
  rw [psiSum, Chebyshev.psi_eq_sum_Icc]
  simp only [Nat.floor_natCast]
  congr 1
  ext n
  simp only [Finset.mem_range, Finset.mem_Icc]
  omega

private lemma psiSum_le (y : ℕ) : psiSum y ≤ (Real.log 4 + 4) * (y : ℝ) := by
  rw [psiSum_eq_psi]
  exact Chebyshev.psi_le_const_mul_self (Nat.cast_nonneg y)

private lemma psiSum_nonneg (y : ℕ) : 0 ≤ psiSum y :=
  Finset.sum_nonneg (fun n _ => ArithmeticFunction.vonMangoldt_nonneg)

private lemma chiS_norm_le (q y : ℕ) (χ : DirichletCharacter ℂ q) :
    ‖chiS q χ y‖ ≤ (Real.log 4 + 4) * (y : ℝ) := by
  rw [chiS]
  refine le_trans (norm_sum_le _ _) ?_
  have hterm : ∀ n ∈ Finset.range (y+1),
      ‖((ArithmeticFunction.vonMangoldt n : ℝ) : ℂ) * χ ((n : ℕ) : ZMod q)‖
        ≤ ArithmeticFunction.vonMangoldt n := by
    intro n _
    rw [norm_mul, Complex.norm_real, Real.norm_eq_abs,
      abs_of_nonneg ArithmeticFunction.vonMangoldt_nonneg]
    exact mul_le_of_le_one_right ArithmeticFunction.vonMangoldt_nonneg
      (DirichletCharacter.norm_le_one χ _)
  refine le_trans (Finset.sum_le_sum hterm) ?_
  exact psiSum_le y

private lemma one_apply_one (a : ZMod 1) : (1 : DirichletCharacter ℂ 1) a = 1 :=
  MulChar.one_apply (by
    rw [Subsingleton.elim a 0]
    exact isUnit_zero_iff.mpr (Subsingleton.elim (1 : ZMod 1) 0))

private lemma chiS_one (y : ℕ) : chiS 1 (1 : DirichletCharacter ℂ 1) y = (psiSum y : ℂ) := by
  rw [chiS, psiSum, Complex.ofReal_sum]
  apply Finset.sum_congr rfl
  intro n _
  rw [one_apply_one]
  ring

private lemma chiS_one_sub (y : ℕ) :
    chiS 1 (1 : DirichletCharacter ℂ 1) y - (y : ℂ) = ((psiSum y - (y : ℝ) : ℝ) : ℂ) := by
  rw [chiS_one]; push_cast; ring

/-- Eventually `(log X)^r ≤ c · X^s` for natural `X`, real `r`, `0 < s`, `0 < c`. -/
private lemma eventually_log_rpow_le_mul_rpow (r s : ℝ) (hs : 0 < s) (c : ℝ) (hc : 0 < c) :
    ∀ᶠ X : ℕ in atTop, (Real.log (X : ℝ)) ^ r ≤ c * (X : ℝ) ^ s := by
  have h := (Asymptotics.isLittleO_iff.mp
    ((isLittleO_log_rpow_rpow_atTop r hs).comp_tendsto tendsto_natCast_atTop_atTop)) hc
  filter_upwards [h, eventually_ge_atTop 3] with X hX hX3
  simp only [Function.comp_apply] at hX
  have hX3' : (1 : ℝ) ≤ (X : ℝ) := by exact_mod_cast (by omega : 1 ≤ X)
  have h1 : |(Real.log (X : ℝ)) ^ r| = (Real.log (X : ℝ)) ^ r :=
    abs_of_nonneg (Real.rpow_nonneg (Real.log_nonneg hX3') r)
  have h2 : |(X : ℝ) ^ s| = (X : ℝ) ^ s :=
    abs_of_nonneg (Real.rpow_nonneg (Nat.cast_nonneg X) s)
  rw [Real.norm_eq_abs, Real.norm_eq_abs, h1, h2] at hX
  exact hX

/-- Eventually `c ≤ (log X)^p` for natural `X`, real `0 < p`. -/
private lemma eventually_log_rpow_ge (p c : ℝ) (hp : 0 < p) :
    ∀ᶠ X : ℕ in atTop, c ≤ (Real.log (X : ℝ)) ^ p := by
  have ht : Tendsto (fun X : ℕ => (Real.log (X:ℝ)) ^ p) atTop atTop :=
    (tendsto_rpow_atTop hp).comp (Real.tendsto_log_atTop.comp tendsto_natCast_atTop_atTop)
  exact ht.eventually_ge_atTop c

/-- Eventually `c ≤ √X` for natural `X`. -/
private lemma eventually_sqrt_ge (c : ℝ) :
    ∀ᶠ X : ℕ in atTop, c ≤ Real.sqrt (X : ℝ) := by
  have ht : Tendsto (fun X : ℕ => ((X:ℝ)) ^ ((1:ℝ)/2)) atTop atTop :=
    (tendsto_rpow_atTop (by norm_num : (0:ℝ) < 1/2)).comp tendsto_natCast_atTop_atTop
  have ht2 : Tendsto (fun X : ℕ => Real.sqrt (X:ℝ)) atTop atTop := by
    apply ht.congr'
    filter_upwards with X
    rw [Real.sqrt_eq_rpow]
  exact ht2.eventually_ge_atTop c


private lemma nonprincipal_sup_le
    (A1 C B : ℝ) (hA1 : 0 < A1) (hC : 0 < C) (hB : 0 < B) (hBC : B ≤ C)
    (N R q X : ℕ) (χ : DirichletCharacter ℂ q) [NeZero q]
    (hχprim : χ.IsPrimitive) (hχ1 : χ ≠ 1)
    (hSWapp : ∀ y : ℕ, N ≤ y → ∀ {q' : ℕ} [NeZero q'], q' ≤ ⌊(Real.log (y:ℝ))^C⌋₊ →
      ∀ χ' : DirichletCharacter ℂ q', χ'.IsPrimitive → χ' ≠ 1 →
        ‖chiS q' χ' y‖ ≤ (y:ℝ)/(Real.log (y:ℝ))^A1)
    (hX3 : 3 ≤ X)
    (hNle : (N:ℝ) ≤ Real.sqrt (X:ℝ))
    (hRq : q ≤ R) (hRB : (R:ℝ) ≤ (Real.log (X:ℝ))^B)
    (hlogbig : (2:ℝ)^C ≤ (Real.log (X:ℝ))^(C - B))
    (htriv : (Real.log 4 + 4) * (Real.log (X:ℝ))^A1 ≤ (2:ℝ)^A1 * Real.sqrt (X:ℝ))
    : chiSupT q χ X ≤ (2:ℝ)^A1 * (X:ℝ) * (Real.log (X:ℝ))^(-A1) := by
  have hX0 : 0 < (X:ℝ) := by exact_mod_cast (by omega : 0 < X)
  have hLpos : 0 < Real.log (X:ℝ) := by
    apply Real.log_pos; exact_mod_cast (by omega : 1 < X)
  have hsqrtpos : 0 < Real.sqrt (X:ℝ) := Real.sqrt_pos.mpr hX0
  have hsqrt2 : Real.sqrt (X:ℝ) * Real.sqrt (X:ℝ) = (X:ℝ) := Real.mul_self_sqrt hX0.le
  have hBnd_nonneg : 0 ≤ (2:ℝ)^A1 * (X:ℝ) * (Real.log (X:ℝ))^(-A1) :=
    mul_nonneg (mul_nonneg (Real.rpow_nonneg (by norm_num) _) hX0.le)
      (Real.rpow_nonneg hLpos.le _)
  refine Real.sSup_le (fun b hb => ?_) hBnd_nonneg
  rw [Set.mem_image] at hb
  obtain ⟨y, hy, rfl⟩ := hb
  rw [Set.mem_Icc] at hy
  simp only [if_neg hχ1, sub_zero]
  by_cases hyy : (y:ℝ) ≤ Real.sqrt (X:ℝ)
  · -- trivial range
    have hstep : (Real.log 4 + 4) * Real.sqrt (X:ℝ)
        ≤ (2:ℝ)^A1 * (X:ℝ) * (Real.log (X:ℝ))^(-A1) := by
      have h2 : (Real.log 4 + 4) ≤ (2:ℝ)^A1 * Real.sqrt (X:ℝ) * (Real.log (X:ℝ))^(-A1) := by
        have hm := mul_le_mul_of_nonneg_right htriv (Real.rpow_nonneg hLpos.le (-A1))
        rw [mul_assoc, ← Real.rpow_add hLpos A1 (-A1), add_neg_cancel, Real.rpow_zero, mul_one] at hm
        exact hm
      calc (Real.log 4 + 4) * Real.sqrt (X:ℝ)
          ≤ ((2:ℝ)^A1 * Real.sqrt (X:ℝ) * (Real.log (X:ℝ))^(-A1)) * Real.sqrt (X:ℝ) :=
            mul_le_mul_of_nonneg_right h2 hsqrtpos.le
        _ = (2:ℝ)^A1 * (X:ℝ) * (Real.log (X:ℝ))^(-A1) := by
            rw [show (2:ℝ)^A1 * Real.sqrt (X:ℝ) * (Real.log (X:ℝ))^(-A1) * Real.sqrt (X:ℝ)
                = (2:ℝ)^A1 * (Real.sqrt (X:ℝ) * Real.sqrt (X:ℝ)) * (Real.log (X:ℝ))^(-A1) by ring,
              hsqrt2]
    calc ‖chiS q χ y‖ ≤ (Real.log 4 + 4) * (y:ℝ) := chiS_norm_le q y χ
      _ ≤ (Real.log 4 + 4) * Real.sqrt (X:ℝ) :=
          mul_le_mul_of_nonneg_left hyy (by positivity)
      _ ≤ _ := hstep
  · rw [not_le] at hyy
    have hyx : (y:ℝ) ≤ (X:ℝ) := by exact_mod_cast hy.2
    have hyN : N ≤ y := by
      have : (N:ℝ) < (y:ℝ) := lt_of_le_of_lt hNle hyy
      exact le_of_lt (by exact_mod_cast this)
    have hlogsqrt : Real.log (Real.sqrt (X:ℝ)) = Real.log (X:ℝ)/2 := Real.log_sqrt hX0.le
    have hlogy : Real.log (Real.sqrt (X:ℝ)) ≤ Real.log (y:ℝ) :=
      Real.log_le_log hsqrtpos hyy.le
    have hlogypos : 0 < Real.log (y:ℝ) := by
      rw [hlogsqrt] at hlogy; linarith
    have hq_floor : q ≤ ⌊(Real.log (y:ℝ))^C⌋₊ := by
      apply Nat.le_floor
      have h2Cpos : 0 < (2:ℝ)^C := Real.rpow_pos_of_pos (by norm_num) C
      have hLBpos : 0 < (Real.log (X:ℝ))^B := Real.rpow_pos_of_pos hLpos B
      have hchain : (Real.log (X:ℝ))^B ≤ (Real.log (y:ℝ))^C := by
        calc (Real.log (X:ℝ))^B
            = (Real.log (X:ℝ))^B * (2:ℝ)^C / (2:ℝ)^C := by
              rw [mul_div_cancel_right₀ _ (ne_of_gt h2Cpos)]
          _ ≤ (Real.log (X:ℝ))^B * (Real.log (X:ℝ))^(C - B) / (2:ℝ)^C := by
              apply div_le_div_of_nonneg_right _ h2Cpos.le
              exact mul_le_mul_of_nonneg_left hlogbig hLBpos.le
          _ = (Real.log (X:ℝ))^C / (2:ℝ)^C := by
              rw [← Real.rpow_add hLpos B (C-B)]; ring_nf
          _ = ((Real.log (X:ℝ))/2)^C := by rw [Real.div_rpow hLpos.le (by norm_num)]
          _ ≤ (Real.log (y:ℝ))^C := by
              apply Real.rpow_le_rpow (by positivity)
              · rw [← hlogsqrt]; exact hlogy
              · exact hC.le
      exact le_trans (le_trans (Nat.cast_le.mpr hRq) hRB) hchain
    have hsw := hSWapp y hyN hq_floor χ hχprim hχ1
    have hpow : (Real.log (y:ℝ))^(-A1) ≤ ((Real.log (X:ℝ))/2)^(-A1) := by
      have h1 : 0 < Real.log (X:ℝ) / 2 := by positivity
      have h2 : Real.log (X:ℝ) / 2 ≤ Real.log (y:ℝ) := by rw [← hlogsqrt]; exact hlogy
      exact Real.rpow_le_rpow_of_nonpos (x := Real.log (X:ℝ) / 2) h1 h2 (by linarith : -A1 ≤ 0)
    calc ‖chiS q χ y‖ ≤ (y:ℝ)/(Real.log (y:ℝ))^A1 := hsw
      _ = (y:ℝ) * (Real.log (y:ℝ))^(-A1) := by
            rw [div_eq_mul_inv, ← Real.rpow_neg hlogypos.le A1]
      _ ≤ (X:ℝ) * ((Real.log (X:ℝ))/2)^(-A1) :=
            mul_le_mul hyx hpow (Real.rpow_nonneg hlogypos.le _) hX0.le
      _ = (2:ℝ)^A1 * (X:ℝ) * (Real.log (X:ℝ))^(-A1) := by
            rw [Real.div_rpow hLpos.le (by norm_num : (0:ℝ) ≤ 2)]
            rw [Real.rpow_neg hLpos.le A1, Real.rpow_neg (by norm_num : (0:ℝ) ≤ 2) A1, div_inv_eq_mul]
            ring


private lemma principal_sup_le
    (A1 : ℝ) (hA1 : 0 < A1)
    (Np X : ℕ) (hNp2 : (2:ℝ) ≤ (Np:ℝ))
    (hNp_bound : ∀ y : ℕ, Np ≤ y → |psiSum y - (y:ℝ)| ≤ (y:ℝ)/(Real.log (y:ℝ))^A1)
    (hX3 : 3 ≤ X)
    (hconstp : (Real.log 4 + 5) * (Np:ℝ) * (Real.log (X:ℝ))^A1 ≤ (2:ℝ)^A1 * (X:ℝ))
    (hmedp : Real.sqrt (X:ℝ) * (Real.log (Np:ℝ))^(-A1)
        ≤ (2:ℝ)^A1 * (X:ℝ) * (Real.log (X:ℝ))^(-A1))
    : chiSupT 1 (1 : DirichletCharacter ℂ 1) X ≤ (2:ℝ)^A1 * (X:ℝ) * (Real.log (X:ℝ))^(-A1) := by
  have hX0 : 0 < (X:ℝ) := by exact_mod_cast (by omega : 0 < X)
  have hLpos : 0 < Real.log (X:ℝ) := by
    apply Real.log_pos; exact_mod_cast (by omega : 1 < X)
  have hsqrtpos : 0 < Real.sqrt (X:ℝ) := Real.sqrt_pos.mpr hX0
  have hlogNppos : 0 < Real.log (Np:ℝ) := Real.log_pos (by linarith)
  have hBnd_nonneg : 0 ≤ (2:ℝ)^A1 * (X:ℝ) * (Real.log (X:ℝ))^(-A1) :=
    mul_nonneg (mul_nonneg (Real.rpow_nonneg (by norm_num) _) hX0.le) (Real.rpow_nonneg hLpos.le _)
  have hlogsqrt : Real.log (Real.sqrt (X:ℝ)) = Real.log (X:ℝ)/2 := Real.log_sqrt hX0.le
  refine Real.sSup_le (fun b hb => ?_) hBnd_nonneg
  rw [Set.mem_image] at hb
  obtain ⟨y, hy, rfl⟩ := hb
  rw [Set.mem_Icc] at hy
  have hrew : ‖chiS 1 (1 : DirichletCharacter ℂ 1) y - (y:ℂ)‖ = |psiSum y - (y:ℝ)| := by
    rw [chiS_one_sub, Complex.norm_real, Real.norm_eq_abs]
  rw [if_pos rfl, hrew]
  by_cases hyN : Np ≤ y
  · have hb1 := hNp_bound y hyN
    have hlogyle : Real.log (Np:ℝ) ≤ Real.log (y:ℝ) :=
      Real.log_le_log (by positivity) (by exact_mod_cast hyN)
    by_cases hy2 : (y:ℝ) ≤ Real.sqrt (X:ℝ)
    · have hy1 : (1:ℝ) ≤ (y:ℝ) := by exact_mod_cast hy.1
      have hlogypos : 0 ≤ Real.log (y:ℝ) := Real.log_nonneg hy1
      have hpowy : (Real.log (y:ℝ))^(-A1) ≤ (Real.log (Np:ℝ))^(-A1) :=
        Real.rpow_le_rpow_of_nonpos (x := Real.log (Np:ℝ)) hlogNppos hlogyle (by linarith)
      calc |psiSum y - (y:ℝ)| ≤ (y:ℝ)/(Real.log (y:ℝ))^A1 := hb1
        _ = (y:ℝ) * (Real.log (y:ℝ))^(-A1) := by
              rw [div_eq_mul_inv, ← Real.rpow_neg hlogypos A1]
        _ ≤ Real.sqrt (X:ℝ) * (Real.log (Np:ℝ))^(-A1) :=
              mul_le_mul hy2 hpowy (Real.rpow_nonneg hlogypos _) hsqrtpos.le
        _ ≤ _ := hmedp
    · rw [not_le] at hy2
      have hyx : (y:ℝ) ≤ (X:ℝ) := by exact_mod_cast hy.2
      have hy1 : (1:ℝ) ≤ (y:ℝ) := by exact_mod_cast hy.1
      have hlogypos : 0 ≤ Real.log (y:ℝ) := Real.log_nonneg hy1
      have hlogy : Real.log (X:ℝ)/2 ≤ Real.log (y:ℝ) := by
        rw [← hlogsqrt]; exact Real.log_le_log hsqrtpos hy2.le
      have hpowy : (Real.log (y:ℝ))^(-A1) ≤ ((Real.log (X:ℝ))/2)^(-A1) :=
        Real.rpow_le_rpow_of_nonpos (x := Real.log (X:ℝ)/2) (by positivity) hlogy (by linarith)
      calc |psiSum y - (y:ℝ)| ≤ (y:ℝ)/(Real.log (y:ℝ))^A1 := hb1
        _ = (y:ℝ) * (Real.log (y:ℝ))^(-A1) := by
              rw [div_eq_mul_inv, ← Real.rpow_neg hlogypos A1]
        _ ≤ (X:ℝ) * ((Real.log (X:ℝ))/2)^(-A1) :=
              mul_le_mul hyx hpowy (Real.rpow_nonneg hlogypos _) hX0.le
        _ = (2:ℝ)^A1 * (X:ℝ) * (Real.log (X:ℝ))^(-A1) := by
              rw [Real.div_rpow hLpos.le (by norm_num : (0:ℝ) ≤ 2)]
              rw [Real.rpow_neg hLpos.le A1, Real.rpow_neg (by norm_num : (0:ℝ) ≤ 2) A1, div_inv_eq_mul]
              ring
  · rw [not_le] at hyN
    have hyNle : (y:ℝ) ≤ (Np:ℝ) := by exact_mod_cast (le_of_lt hyN)
    have h1 : |psiSum y - (y:ℝ)| ≤ (Real.log 4 + 5) * (y:ℝ) := by
      have h2 : |psiSum y - (y:ℝ)| ≤ psiSum y + (y:ℝ) := by
        apply abs_le.mpr
        constructor <;> linarith [psiSum_nonneg y, (Nat.cast_nonneg y : (0:ℝ) ≤ (y:ℝ))]
      have h3 := psiSum_le y
      nlinarith [h2, h3, (Nat.cast_nonneg y : (0:ℝ) ≤ (y:ℝ))]
    have hc : (Real.log 4 + 5) * (Np:ℝ) ≤ (2:ℝ)^A1 * (X:ℝ) * (Real.log (X:ℝ))^(-A1) := by
      have hLpow : 0 < (Real.log (X:ℝ))^A1 := Real.rpow_pos_of_pos hLpos A1
      have hLneg : (Real.log (X:ℝ))^(-A1) = ((Real.log (X:ℝ))^A1)⁻¹ := Real.rpow_neg hLpos.le A1
      rw [hLneg, inv_eq_one_div, mul_one_div, le_div_iff₀ hLpow]
      exact hconstp
    calc |psiSum y - (y:ℝ)| ≤ (Real.log 4 + 5) * (y:ℝ) := h1
      _ ≤ (Real.log 4 + 5) * (Np:ℝ) := by
            apply mul_le_mul_of_nonneg_left hyNle
            have : (0:ℝ) ≤ Real.log 4 := Real.log_nonneg (by norm_num)
            linarith
      _ ≤ _ := hc



private lemma final_step_bound (X R : ℕ) (A B : ℝ)
    (hX3 : 3 ≤ X)
    (hRB : (R:ℝ) ≤ (Real.log (X:ℝ)) ^ B)
    (hfin : (2:ℝ)^(A+1) ≤ (Real.log (X:ℝ))^(1 - B))
    : (R:ℝ) * ((2:ℝ)^(A+1) * (X:ℝ) * (Real.log (X:ℝ))^(-(A+1)))
        ≤ (X:ℝ) * (Real.log (X:ℝ))^(-A) := by
  have hX0 : 0 < (X:ℝ) := by exact_mod_cast (by omega : 0 < X)
  have hLpos : 0 < Real.log (X:ℝ) := by
    apply Real.log_pos; exact_mod_cast (by omega : 1 < X)
  have hBnd_nonneg : 0 ≤ (2:ℝ)^(A+1) * (X:ℝ) * (Real.log (X:ℝ))^(-(A+1)) :=
    mul_nonneg (mul_nonneg (Real.rpow_nonneg (by norm_num) _) hX0.le) (Real.rpow_nonneg hLpos.le _)
  have key : (2:ℝ)^(A+1) * (Real.log (X:ℝ))^(B - (A+1)) ≤ (Real.log (X:ℝ))^(-A) := by
    have hm := mul_le_mul_of_nonneg_right hfin (Real.rpow_nonneg hLpos.le (B - (A+1)))
    rw [← Real.rpow_add hLpos] at hm
    have he : 1 - B + (B - (A+1)) = -A := by ring
    rw [he] at hm
    exact hm
  calc (R:ℝ) * ((2:ℝ)^(A+1) * (X:ℝ) * (Real.log (X:ℝ))^(-(A+1)))
      ≤ (Real.log (X:ℝ))^B * ((2:ℝ)^(A+1) * (X:ℝ) * (Real.log (X:ℝ))^(-(A+1))) :=
        mul_le_mul_of_nonneg_right hRB hBnd_nonneg
    _ = (2:ℝ)^(A+1) * (X:ℝ) * ((Real.log (X:ℝ))^B * (Real.log (X:ℝ))^(-(A+1))) := by ring
    _ = (2:ℝ)^(A+1) * (X:ℝ) * (Real.log (X:ℝ))^(B - (A+1)) := by
        rw [← Real.rpow_add hLpos B (-(A+1)), sub_eq_add_neg]
    _ = (X:ℝ) * ((2:ℝ)^(A+1) * (Real.log (X:ℝ))^(B - (A+1))) := by ring
    _ ≤ (X:ℝ) * (Real.log (X:ℝ))^(-A) := mul_le_mul_of_nonneg_left key hX0.le


private lemma final_step_bound_param (X R : ℕ) (A1 B E : ℝ)
    (hX3 : 3 ≤ X)
    (hRB : (R:ℝ) ≤ (Real.log (X:ℝ)) ^ B)
    (hfin : (2:ℝ)^A1 ≤ (Real.log (X:ℝ))^(A1 - B - E))
    : (R:ℝ) * ((2:ℝ)^A1 * (X:ℝ) * (Real.log (X:ℝ))^(-A1))
        ≤ (X:ℝ) * (Real.log (X:ℝ))^(-E) := by
  have hX0 : 0 < (X:ℝ) := by exact_mod_cast (by omega : 0 < X)
  have hLpos : 0 < Real.log (X:ℝ) := by
    apply Real.log_pos; exact_mod_cast (by omega : 1 < X)
  have hBnd_nonneg : 0 ≤ (2:ℝ)^A1 * (X:ℝ) * (Real.log (X:ℝ))^(-A1) :=
    mul_nonneg (mul_nonneg (Real.rpow_nonneg (by norm_num) _) hX0.le) (Real.rpow_nonneg hLpos.le _)
  have key : (2:ℝ)^A1 * (Real.log (X:ℝ))^(B - A1) ≤ (Real.log (X:ℝ))^(-E) := by
    have hm := mul_le_mul_of_nonneg_right hfin (Real.rpow_nonneg hLpos.le (B - A1))
    rw [← Real.rpow_add hLpos] at hm
    have he : A1 - B - E + (B - A1) = -E := by ring
    rw [he] at hm
    exact hm
  calc (R:ℝ) * ((2:ℝ)^A1 * (X:ℝ) * (Real.log (X:ℝ))^(-A1))
      ≤ (Real.log (X:ℝ))^B * ((2:ℝ)^A1 * (X:ℝ) * (Real.log (X:ℝ))^(-A1)) :=
        mul_le_mul_of_nonneg_right hRB hBnd_nonneg
    _ = (2:ℝ)^A1 * (X:ℝ) * ((Real.log (X:ℝ))^B * (Real.log (X:ℝ))^(-A1)) := by ring
    _ = (2:ℝ)^A1 * (X:ℝ) * (Real.log (X:ℝ))^(B - A1) := by
        rw [← Real.rpow_add hLpos B (-A1), sub_eq_add_neg]
    _ = (X:ℝ) * ((2:ℝ)^A1 * (Real.log (X:ℝ))^(B - A1)) := by ring
    _ ≤ (X:ℝ) * (Real.log (X:ℝ))^(-E) := mul_le_mul_of_nonneg_left key hX0.le


theorem charSup_sum_param_le
    (hSW : ∀ A C : ℝ, 0 < A → 0 < C → ∀ᶠ x : ℕ in atTop,
      ∀ {q : ℕ} [NeZero q], q ≤ ⌊(Real.log (x : ℝ)) ^ C⌋₊ →
      ∀ χ : DirichletCharacter ℂ q, χ.IsPrimitive → χ ≠ 1 →
        ‖∑ n ∈ Finset.range (x + 1),
            ((ArithmeticFunction.vonMangoldt n : ℝ) : ℂ) * χ ((n : ℕ) : ZMod q)‖ ≤
          (x : ℝ) / (Real.log (x : ℝ)) ^ A)
    (hPNT : ∀ A : ℝ, 0 < A → ∃ x₀ : ℝ, ∀ x : ℝ, x₀ ≤ x →
      |Chebyshev.psi x - x| ≤ x / (Real.log x) ^ A) :
    ∀ A B : ℝ, 0 < A → 0 < B →
      ∀ᶠ X : ℕ in atTop, ∀ R : ℕ, (R : ℝ) ≤ (Real.log (X : ℝ)) ^ B →
        (∑ q ∈ Finset.Icc 1 R, ((q.totient : ℕ) : ℝ)⁻¹ *
          ∑ χ ∈ Finset.univ.filter (fun χ : DirichletCharacter ℂ q => χ.IsPrimitive),
            sSup ((fun y : ℕ => ‖∑ n ∈ Finset.range (y + 1),
                ((ArithmeticFunction.vonMangoldt n : ℝ) : ℂ) * χ ((n : ℕ) : ZMod q)
                  - (if χ = 1 then (y : ℂ) else 0)‖) '' Set.Icc 1 X))
        ≤ (X : ℝ) * (Real.log (X : ℝ)) ^ (-(A + B + 2)) := by
  intro A B hA hB
  set A1 : ℝ := A + 2 * B + 3 with hA1def
  set C : ℝ := B + 1 with hCdef
  have hA1pos : (0:ℝ) < A1 := by rw [hA1def]; linarith
  have hCpos : (0:ℝ) < C := by rw [hCdef]; linarith
  have hBC : B ≤ C := by rw [hCdef]; linarith
  obtain ⟨N, hN⟩ := Filter.eventually_atTop.mp (hSW A1 C hA1pos hCpos)
  obtain ⟨x₀, hx₀⟩ := hPNT A1 hA1pos
  obtain ⟨Np, hNp_ge⟩ := exists_nat_ge (max (max x₀ (Real.exp A1)) (2:ℝ))
  have hNp_x₀ : x₀ ≤ (Np:ℝ) := le_trans (le_trans (le_max_left _ _) (le_max_left _ _)) hNp_ge
  have hNp_exp : Real.exp A1 ≤ (Np:ℝ) := le_trans (le_trans (le_max_right _ _) (le_max_left _ _)) hNp_ge
  have hNp_2 : (2:ℝ) ≤ (Np:ℝ) := le_trans (le_max_right _ _) hNp_ge
  have hNp_pos : 0 < Np := by
    have : (0:ℝ) < (Np:ℝ) := lt_of_lt_of_le (by norm_num) hNp_2
    exact_mod_cast this
  have hlogNppos : 0 < Real.log (Np:ℝ) := Real.log_pos (by linarith)
  have hNp_bound : ∀ y : ℕ, Np ≤ y → |psiSum y - (y:ℝ)| ≤ (y:ℝ)/(Real.log (y:ℝ))^A1 := by
    intro y hy
    have h1 : psiSum y = Chebyshev.psi (y:ℝ) := psiSum_eq_psi y
    have hy' : x₀ ≤ (y:ℝ) := le_trans hNp_x₀ (by exact_mod_cast hy)
    have hb := hx₀ (y:ℝ) hy'
    rw [h1]; exact hb
  have hSWapp : ∀ y : ℕ, N ≤ y → ∀ {q' : ℕ} [NeZero q'], q' ≤ ⌊(Real.log (y:ℝ))^C⌋₊ →
      ∀ χ' : DirichletCharacter ℂ q', χ'.IsPrimitive → χ' ≠ 1 →
        ‖chiS q' χ' y‖ ≤ (y:ℝ)/(Real.log (y:ℝ))^A1 := by
    intro y hy q' _ hq' χ' hp h1
    have h := hN y hy hq' χ' hp h1
    simpa only [chiS] using h
  have hcond : ∀ᶠ X : ℕ in atTop,
      (3 ≤ X) ∧ ((N:ℝ) ≤ Real.sqrt (X:ℝ))
      ∧ ((Real.log 4 + 4) * (Real.log (X:ℝ))^A1 ≤ (2:ℝ)^A1 * Real.sqrt (X:ℝ))
      ∧ ((Real.log 4 + 5) * (Np:ℝ) * (Real.log (X:ℝ))^A1 ≤ (2:ℝ)^A1 * (X:ℝ))
      ∧ (Real.sqrt (X:ℝ) * (Real.log (Np:ℝ))^(-A1)
            ≤ (2:ℝ)^A1 * (X:ℝ) * (Real.log (X:ℝ))^(-A1))
      ∧ ((2:ℝ)^C ≤ (Real.log (X:ℝ))^(C - B))
      ∧ ((2:ℝ)^A1 ≤ (Real.log (X:ℝ))^(A1 - B - (A + B + 2))) := by
    have h1 : ∀ᶠ X : ℕ in atTop, 3 ≤ X := eventually_ge_atTop 3
    have h2 : ∀ᶠ X : ℕ in atTop, (N:ℝ) ≤ Real.sqrt (X:ℝ) := eventually_sqrt_ge _
    have h3 : ∀ᶠ X : ℕ in atTop,
        (Real.log (X:ℝ))^A1 ≤ ((2:ℝ)^A1/(Real.log 4 + 4)) * (X:ℝ)^((1:ℝ)/2) :=
      eventually_log_rpow_le_mul_rpow A1 (1/2) (by norm_num) ((2:ℝ)^A1/(Real.log 4 + 4)) (by positivity)
    have h4 : ∀ᶠ X : ℕ in atTop,
        (Real.log (X:ℝ))^A1 ≤ ((2:ℝ)^A1/((Real.log 4 + 5) * (Np:ℝ))) * (X:ℝ)^(1:ℝ) :=
      eventually_log_rpow_le_mul_rpow A1 1 (by norm_num) ((2:ℝ)^A1/((Real.log 4 + 5) * (Np:ℝ))) (by positivity)
    have h5 : ∀ᶠ X : ℕ in atTop,
        (Real.log (X:ℝ))^A1 ≤ ((2:ℝ)^A1 * (Real.log (Np:ℝ))^A1) * (X:ℝ)^((1:ℝ)/2) :=
      eventually_log_rpow_le_mul_rpow A1 (1/2) (by norm_num) ((2:ℝ)^A1 * (Real.log (Np:ℝ))^A1) (by positivity)
    have h6 : ∀ᶠ X : ℕ in atTop, (2:ℝ)^C ≤ (Real.log (X:ℝ))^(C - B) :=
      eventually_log_rpow_ge (C - B) ((2:ℝ)^C) (by rw [hCdef]; linarith)
    have h7 : ∀ᶠ X : ℕ in atTop, (2:ℝ)^A1 ≤ (Real.log (X:ℝ))^(A1 - B - (A + B + 2)) :=
      eventually_log_rpow_ge (A1 - B - (A + B + 2)) ((2:ℝ)^A1) (by rw [hA1def]; linarith)
    filter_upwards [h1, h2, h3, h4, h5, h6, h7] with X hX3 hXN hX3' hX4 hX5 hX6 hX7
    refine ⟨hX3, hXN, ?_, ?_, ?_, hX6, hX7⟩
    · have hstep : (Real.log 4 + 4) * (Real.log (X:ℝ))^A1 ≤ (2:ℝ)^A1 * (X:ℝ)^((1:ℝ)/2) := by
        calc (Real.log 4 + 4) * (Real.log (X:ℝ))^A1
            ≤ (Real.log 4 + 4) * (((2:ℝ)^A1/(Real.log 4 + 4)) * (X:ℝ)^((1:ℝ)/2)) :=
              mul_le_mul_of_nonneg_left hX3' (by positivity)
          _ = (2:ℝ)^A1 * (X:ℝ)^((1:ℝ)/2) := by field_simp
      rwa [← Real.sqrt_eq_rpow] at hstep
    · have hpos : (0:ℝ) ≤ (Real.log 4 + 5) * (Np:ℝ) := by positivity
      have hstep : (Real.log 4 + 5) * (Np:ℝ) * (Real.log (X:ℝ))^A1 ≤ (2:ℝ)^A1 * (X:ℝ) := by
        calc (Real.log 4 + 5) * (Np:ℝ) * (Real.log (X:ℝ))^A1
            ≤ (Real.log 4 + 5) * (Np:ℝ) *
                (((2:ℝ)^A1/((Real.log 4 + 5) * (Np:ℝ))) * (X:ℝ)^(1:ℝ)) :=
              mul_le_mul_of_nonneg_left hX4 hpos
          _ = (2:ℝ)^A1 * (X:ℝ) := by
              rw [Real.rpow_one]
              have hne : ((Real.log 4 + 5) * (Np:ℝ)) ≠ 0 := ne_of_gt (by positivity)
              field_simp
      exact hstep
    · have hX5' : (Real.log (X:ℝ))^A1
          ≤ (2:ℝ)^A1 * (Real.log (Np:ℝ))^A1 * Real.sqrt (X:ℝ) := by
        rw [Real.sqrt_eq_rpow]; linarith [hX5]
      have h1 : 0 < (Real.log (Np:ℝ))^A1 := Real.rpow_pos_of_pos hlogNppos _
      have h2 : 0 < (Real.log (X:ℝ))^A1 :=
        Real.rpow_pos_of_pos (Real.log_pos (by exact_mod_cast (by omega : 1 < X))) _
      rw [Real.rpow_neg hlogNppos.le A1, Real.rpow_neg (Real.log_pos (by exact_mod_cast (by omega : 1 < X))).le A1,
          ← div_eq_mul_inv, ← div_eq_mul_inv]
      rw [div_le_div_iff₀ h1 h2]
      calc Real.sqrt (X:ℝ) * (Real.log (X:ℝ))^A1
          ≤ Real.sqrt (X:ℝ) * ((2:ℝ)^A1 * (Real.log (Np:ℝ))^A1 * Real.sqrt (X:ℝ)) :=
            mul_le_mul_of_nonneg_left hX5' (Real.sqrt_nonneg X)
        _ = (2:ℝ)^A1 * (X:ℝ) * (Real.log (Np:ℝ))^A1 := by
            have hs : Real.sqrt (X:ℝ) * Real.sqrt (X:ℝ) = (X:ℝ) := Real.mul_self_sqrt (Nat.cast_nonneg X)
            calc Real.sqrt (X:ℝ) * ((2:ℝ)^A1 * (Real.log (Np:ℝ))^A1 * Real.sqrt (X:ℝ))
                = (2:ℝ)^A1 * (Real.log (Np:ℝ))^A1 * (Real.sqrt (X:ℝ) * Real.sqrt (X:ℝ)) := by ring
              _ = (2:ℝ)^A1 * (X:ℝ) * (Real.log (Np:ℝ))^A1 := by rw [hs]; ring
  obtain ⟨Xa, hXa⟩ := Filter.eventually_atTop.mp hcond
  refine Filter.eventually_atTop.2 ⟨max Xa 3, fun X hX => ?_⟩
  intro R hR
  have hXa' : Xa ≤ X := le_trans (le_max_left _ _) hX
  obtain ⟨hX3, hXN, hc3, hc4, hc5, hc6, hc7⟩ := hXa X hXa'
  have hX0 : 0 < (X:ℝ) := by exact_mod_cast (by omega : 0 < X)
  have hLpos : 0 < Real.log (X:ℝ) := by apply Real.log_pos; exact_mod_cast (by omega : 1 < X)
  change (∑ q ∈ Finset.Icc 1 R, ((q.totient : ℕ) : ℝ)⁻¹ *
      ∑ χ ∈ Finset.univ.filter (fun χ : DirichletCharacter ℂ q => χ.IsPrimitive),
        chiSupT q χ X)
    ≤ (X : ℝ) * (Real.log (X : ℝ)) ^ (-(A + B + 2))
  have hBnd_nonneg : 0 ≤ (2:ℝ)^A1 * (X:ℝ) * (Real.log (X:ℝ))^(-A1) :=
    mul_nonneg (mul_nonneg (Real.rpow_nonneg (by norm_num) _) hX0.le) (Real.rpow_nonneg hLpos.le _)
  have hterm : ∀ q ∈ Finset.Icc 1 R,
      ((q.totient : ℕ) : ℝ)⁻¹ *
        ∑ χ ∈ Finset.univ.filter (fun χ : DirichletCharacter ℂ q => χ.IsPrimitive),
          chiSupT q χ X
        ≤ (2:ℝ)^A1 * (X:ℝ) * (Real.log (X:ℝ))^(-A1) := by
    intro q hq
    rw [Finset.mem_Icc] at hq
    haveI : NeZero q := ⟨by omega⟩
    have hφpos : (0:ℝ) < (q.totient:ℝ) := by
      have : 0 < q.totient := Nat.totient_pos.mpr (by omega)
      exact_mod_cast this
    have hinner : (∑ χ ∈ Finset.univ.filter (fun χ : DirichletCharacter ℂ q => χ.IsPrimitive),
          chiSupT q χ X)
        ≤ (q.totient:ℝ) * ((2:ℝ)^A1 * (X:ℝ) * (Real.log (X:ℝ))^(-A1)) := by
      have hpt : ∀ χ ∈ Finset.univ.filter (fun χ : DirichletCharacter ℂ q => χ.IsPrimitive),
          chiSupT q χ X
            ≤ (2:ℝ)^A1 * (X:ℝ) * (Real.log (X:ℝ))^(-A1) := by
        intro χ hχmem
        rw [Finset.mem_filter] at hχmem
        obtain ⟨_, hχprim⟩ := hχmem
        by_cases hχ1 : χ = 1
        · subst hχ1
          have hq1 : q = 1 := by
            have h1 : (1 : DirichletCharacter ℂ q).conductor = q :=
              (DirichletCharacter.isPrimitive_def _).mp hχprim
            have h2 : (1 : DirichletCharacter ℂ q).conductor = 1 := DirichletCharacter.conductor_one
            rw [← h1, h2]
          subst hq1
          exact principal_sup_le A1 hA1pos Np X hNp_2 hNp_bound hX3 hc4 hc5
        · exact nonprincipal_sup_le A1 C B hA1pos hCpos hB hBC N R q X χ hχprim hχ1 hSWapp
            hX3 hXN hq.2 hR hc6 hc3
      calc (∑ χ ∈ Finset.univ.filter (fun χ : DirichletCharacter ℂ q => χ.IsPrimitive),
            chiSupT q χ X)
          ≤ ∑ _χ ∈ Finset.univ.filter (fun χ : DirichletCharacter ℂ q => χ.IsPrimitive),
              ((2:ℝ)^A1 * (X:ℝ) * (Real.log (X:ℝ))^(-A1)) := Finset.sum_le_sum hpt
        _ = (↑(Finset.univ.filter (fun χ : DirichletCharacter ℂ q => χ.IsPrimitive)).card : ℝ)
              * ((2:ℝ)^A1 * (X:ℝ) * (Real.log (X:ℝ))^(-A1)) := by
            rw [Finset.sum_const, nsmul_eq_mul]
        _ ≤ (q.totient:ℝ) * ((2:ℝ)^A1 * (X:ℝ) * (Real.log (X:ℝ))^(-A1)) := by
            apply mul_le_mul_of_nonneg_right _ hBnd_nonneg
            have hle := Finset.card_filter_le (Finset.univ : Finset (DirichletCharacter ℂ q))
              (fun χ : DirichletCharacter ℂ q => χ.IsPrimitive)
            have hc : (Finset.univ : Finset (DirichletCharacter ℂ q)).card = q.totient := by
              rw [Finset.card_univ, ← Nat.card_eq_fintype_card]
              exact DirichletCharacter.card_eq_totient_of_hasEnoughRootsOfUnity ℂ q
            exact_mod_cast (le_trans hle (le_of_eq hc))
    calc ((q.totient : ℕ) : ℝ)⁻¹ *
          (∑ χ ∈ Finset.univ.filter (fun χ : DirichletCharacter ℂ q => χ.IsPrimitive),
            chiSupT q χ X)
        ≤ ((q.totient : ℕ) : ℝ)⁻¹ *
            ((q.totient:ℝ) * ((2:ℝ)^A1 * (X:ℝ) * (Real.log (X:ℝ))^(-A1))) :=
          mul_le_mul_of_nonneg_left hinner (by positivity)
      _ = (2:ℝ)^A1 * (X:ℝ) * (Real.log (X:ℝ))^(-A1) := by
          rw [← mul_assoc, inv_mul_cancel₀ (ne_of_gt hφpos), one_mul]
  calc (∑ q ∈ Finset.Icc 1 R, ((q.totient : ℕ) : ℝ)⁻¹ *
        ∑ χ ∈ Finset.univ.filter (fun χ : DirichletCharacter ℂ q => χ.IsPrimitive),
          chiSupT q χ X)
      ≤ ∑ _q ∈ Finset.Icc 1 R, ((2:ℝ)^A1 * (X:ℝ) * (Real.log (X:ℝ))^(-A1)) :=
        Finset.sum_le_sum hterm
    _ = (R:ℝ) * ((2:ℝ)^A1 * (X:ℝ) * (Real.log (X:ℝ))^(-A1)) := by
        rw [Finset.sum_const, nsmul_eq_mul, Nat.card_Icc]
        simp
    _ ≤ (X:ℝ) * (Real.log (X:ℝ))^(-(A + B + 2)) :=
        final_step_bound_param X R A1 B (A + B + 2) hX3 hR hc7


/-- Siegel--Walfisz in the modular range `q ≤ (log x)^B` with *independent* error
exponent: for every `A > 0` and `B > 0`, eventually for every `R` with
`R ≤ (log x)^B`, the totient-weighted primitive-character sup sum is at most
`x * (log x)^{-(A+B+2)}`.

This is the form of the Siegel--Walfisz range that the Bombieri--Vinogradov
assembly needs (Vaughan §1: the small-moduli contribution).  It differs from
`siegel_walfisz_charSup_sum_le` only in that the modulus exponent `B` is a
parameter rather than `min C 1 / 2`; the proof follows the same route, applying
`siegel_walfisz_chi_range` with error exponent `A + 2B + 2` and modulus exponent
`max B 1`, together with the prime number theorem
`Commons.NumberTheory.Zeta.psi_sub_id_powLog_real` for the principal character
modulo `1`. -/
theorem siegel_walfisz_primEventual :
    ∀ A B : ℝ, 0 < A → 0 < B →
      ∀ᶠ X : ℕ in Filter.atTop, ∀ R : ℕ, (R : ℝ) ≤ (Real.log (X : ℝ)) ^ B →
        (∑ q ∈ Finset.Icc 1 R, ((q.totient : ℕ) : ℝ)⁻¹ *
          ∑ χ ∈ (Finset.univ.filter (fun χ : DirichletCharacter ℂ q => χ.IsPrimitive)),
            sSup ((fun y : ℕ => ‖∑ n ∈ Finset.range (y + 1),
                ((ArithmeticFunction.vonMangoldt n : ℝ) : ℂ) * χ ((n : ℕ) : ZMod q)
                  - (if χ = 1 then (y : ℂ) else 0)‖) '' Set.Icc 1 X))
        ≤ (X : ℝ) * (Real.log (X : ℝ)) ^ (-(A + B + 2)) := by
  intro A B hA hB
  exact charSup_sum_param_le
    (fun A C hA hC => siegel_walfisz_chi_range A C hA hC)
    (fun A hA => Commons.NumberTheory.Zeta.psi_sub_id_powLog_real A hA) A B hA hB

end Commons.NumberTheory.BombieriVinogradov
