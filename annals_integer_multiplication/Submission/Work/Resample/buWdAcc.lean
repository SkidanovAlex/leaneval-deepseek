import Mathlib
import Submission.Work.Resample.buDefs
import Submission.Work.Resample.auPiBound
import Submission.Work.Resample.buZbClose
import Submission.Work.Resample.auHExpClosePos
import Submission.Work.Resample.tdivScalePow
import Submission.Work.Resample.expMulSuccLeFourPow
import Submission.Work.Resample.absExpSubLeExpMax

namespace Work.Resample

open HvdH

set_option autoImplicit false
set_option maxRecDepth 4000

/-- The tabulated diagonal weight `buWd p α s t ℓ` approximates `2^p · (D'_{ℓℓ})` to within `2`
(an ulp in `2^p` units); the true error is far smaller, since the working precision
`auPrec p = 3p + 100` is much larger than `p`. -/
theorem buWdAcc (p α s t : ℕ) (hs : 0 < s) (hα : 2 ≤ α) (hp : 100 ≤ p) (hαp : α ^ 2 < p)
    (ℓ : Fin s) :
    |(Work.Resample.buWd p α s t (ℓ : ℤ) : ℝ) / (2 : ℝ) ^ p
        - (HvdH.diagD' s t α ℓ ℓ).re| ≤ 2 / (2 : ℝ) ^ p := by
  have h2p : (0:ℝ) < (2:ℝ)^p := by positivity
  have hP : (0:ℝ) < (2:ℝ)^(auPrec p) := by positivity
  have h2p100 : (0:ℝ) < (2:ℝ)^(p+100) := by positivity
  have hpi0 : (0:ℤ) ≤ auPi p := by
    rw [auPi, Work.Fx.uval]
    apply Int.fdiv_nonneg
    · rw [Work.Fx.Nval]
      exact add_nonneg (mul_nonneg (Int.natCast_nonneg _) (by positivity)) (by positivity)
    · positivity
  have hpi1 : |(auPi p : ℝ) - (2:ℝ)^(auPrec p) * Real.pi| ≤ 1 := auPiBound p hp
  have hp1 : (p:ℝ) + 1 ≤ (2:ℝ)^(auPrec p) := by
    have hnat : p + 1 ≤ 2 ^ p := by
      have := Nat.lt_two_pow_self (n := p); omega
    have hcast : ((p+1 : ℕ) : ℝ) ≤ ((2^p : ℕ) : ℝ) := by exact_mod_cast hnat
    push_cast at hcast
    have h2 : ((2:ℝ)^p) ≤ (2:ℝ)^(auPrec p) :=
      pow_le_pow_right₀ (by norm_num) (by simp only [auPrec]; omega)
    linarith
  obtain ⟨hZ0raw, hZbraw⟩ := buZbClose p α s t hp hs (ℓ:ℤ) hpi0 hpi1
  obtain ⟨c, hcdef⟩ : ∃ c : ℕ, c = 2 * α ^ 2 - 2 := ⟨_, rfl⟩
  obtain ⟨β, hβdef⟩ : ∃ β : ℝ, β = HvdH.betaR s t (ℓ:ℕ) := ⟨_, rfl⟩
  obtain ⟨U, hUdef⟩ : ∃ U : ℝ, U = Real.pi * (α:ℝ)^2 * β^2 := ⟨_, rfl⟩
  obtain ⟨W, hWdef⟩ : ∃ W : ℝ, W = 1 + (α:ℝ)^2 * β^2 := ⟨_, rfl⟩
  obtain ⟨Z, hZdef⟩ : ∃ Z : ℤ, Z = buZb p α s t (ℓ:ℤ) := ⟨_, rfl⟩
  obtain ⟨E, hEdef⟩ : ∃ E : ℤ, E = auH p Z (auNstep p) := ⟨_, rfl⟩
  obtain ⟨y, hydef⟩ : ∃ y : ℝ, y = (Z:ℝ)/(2:ℝ)^(auPrec p) := ⟨_, rfl⟩
  have hβle : |β| ≤ 1/2 := by
    rw [hβdef, ← Work.ResMath.betaI_eq_betaR]
    exact Work.ResMath.betaI_abs_le s t (ℓ:ℤ)
  have hβsq : β^2 ≤ 1/4 := by
    have h1 : |β|^2 ≤ ((1:ℝ)/2)^2 := pow_le_pow_left₀ (abs_nonneg β) hβle 2
    rw [sq_abs] at h1
    norm_num at h1
    exact h1
  have hU0 : 0 ≤ U := by rw [hUdef]; positivity
  have hα2p : (α:ℝ)^2 ≤ (p:ℝ) := by exact_mod_cast le_of_lt hαp
  have hUp : U ≤ (p:ℝ) := by
    rw [hUdef]
    have h4 : Real.pi * β^2 ≤ 1 := by
      have h1 : Real.pi * β^2 ≤ 4 * β^2 :=
        mul_le_mul_of_nonneg_right (le_of_lt Real.pi_lt_four) (sq_nonneg β)
      linarith [h1, hβsq]
    have h5 : Real.pi * (α:ℝ)^2 * β^2 = (α:ℝ)^2 * (Real.pi * β^2) := by ring
    rw [h5]
    have h6 : (α:ℝ)^2 * (Real.pi * β^2) ≤ (α:ℝ)^2 * 1 :=
      mul_le_mul_of_nonneg_left h4 (sq_nonneg (α:ℝ))
    linarith [h6, hα2p]
  have hW0 : 0 ≤ W := by rw [hWdef]; positivity
  have hWle : W ≤ (p:ℝ) + 1 := by
    rw [hWdef]
    have h1 : (α:ℝ)^2 * β^2 ≤ (p:ℝ) * (1/4) := mul_le_mul hα2p hβsq (by positivity) (by positivity)
    have hp0 : (0:ℝ) ≤ (p:ℝ) := by positivity
    linarith
  have hβb : ((buBeta s t (ℓ:ℤ) : ℤ) : ℝ) = (s:ℝ) * β := by
    rw [hβdef, ← Work.ResMath.betaI_eq_betaR]
    simp only [buBeta, Work.ResMath.betaI, HvdH.rnd]
    push_cast
    field_simp
  have hsqb : ((buBeta s t (ℓ:ℤ) : ℤ) : ℝ)^2 / (s:ℝ)^2 = β^2 := by
    have hs' : (s:ℝ) ≠ 0 := by positivity
    rw [hβb]; field_simp
  have hcb : Real.pi * ((α:ℝ)^2 * ((buBeta s t (ℓ:ℤ) : ℤ) : ℝ)^2 / (s:ℝ)^2) = U := by
    rw [mul_div_assoc, hsqb, hUdef]; ring
  have hcw : (1:ℝ) + (α:ℝ)^2 * ((buBeta s t (ℓ:ℤ):ℤ):ℝ)^2 / (s:ℝ)^2 = W := by
    rw [mul_div_assoc, hsqb, hWdef]
  have hZclose : |(Z:ℝ) - (2:ℝ)^(auPrec p) * U| ≤ W := by
    rw [hcb, hcw] at hZbraw
    rwa [← hZdef] at hZbraw
  have hZ0 : 0 ≤ Z := by rw [hZdef]; exact hZ0raw
  have hZle : (Z:ℝ) ≤ ((p:ℝ)+10) * (2:ℝ)^(auPrec p) := by
    have h7 : (2:ℝ)^(auPrec p) * ((p:ℝ)+1) = (2:ℝ)^(auPrec p) * (p:ℝ) + (2:ℝ)^(auPrec p) := by ring
    have h1 : (Z:ℝ) ≤ (2:ℝ)^(auPrec p) * U + W := by
      have := (abs_le.mp hZclose).2; linarith
    have h2 : (2:ℝ)^(auPrec p) * U ≤ (2:ℝ)^(auPrec p) * (p:ℝ) :=
      mul_le_mul_of_nonneg_left hUp (le_of_lt hP)
    have h3 : W ≤ (2:ℝ)^(auPrec p) := by linarith [hWle, hp1]
    have h4 : (Z:ℝ) ≤ (2:ℝ)^(auPrec p) * ((p:ℝ) + 1) := by linarith [h1, h2, h3, h7]
    have h5 : (2:ℝ)^(auPrec p) * ((p:ℝ) + 1) ≤ (2:ℝ)^(auPrec p) * ((p:ℝ) + 10) :=
      mul_le_mul_of_nonneg_left (by linarith) (le_of_lt hP)
    have h6 : (2:ℝ)^(auPrec p) * ((p:ℝ) + 10) = ((p:ℝ)+10) * (2:ℝ)^(auPrec p) := by ring
    linarith [h4, h5, h6]
  have hy0 : 0 ≤ y := by rw [hydef]; exact div_nonneg (by exact_mod_cast hZ0) (le_of_lt hP)
  have hE : |(E:ℝ)/(2:ℝ)^(auPrec p) - Real.exp y| ≤ 2/(2:ℝ)^p := by
    rw [hEdef, hydef]
    exact auHExpClosePos p hp Z hZ0 hZle
  have hT : |((Int.tdiv E ((2:ℤ)^(auPrec p - p + c)) : ℤ) : ℝ)/(2:ℝ)^p
      - (E:ℝ)/(2:ℝ)^(auPrec p + c)| ≤ 1/(2:ℝ)^p := tdivScalePow p c E
  have hbuWd : buWd p α s t (ℓ:ℤ) = Int.tdiv E ((2:ℤ)^(auPrec p - p + c)) := by
    unfold buWd
    rw [← hZdef, ← hcdef, ← hEdef]
  have htdiv1 : |(buWd p α s t (ℓ:ℤ) : ℝ)/(2:ℝ)^p - (E:ℝ)/(2:ℝ)^(auPrec p + c)| ≤ 1/(2:ℝ)^p := by
    rw [hbuWd]; exact hT
  have hV : (HvdH.diagD' s t α ℓ ℓ).re = Real.exp U / (2:ℝ)^c := by
    have hval : HvdH.diagD' s t α ℓ ℓ
        = ((((1:ℝ)/(2:ℝ)^(2*α^2-2) * Real.exp (Real.pi * (α:ℝ)^2 * (HvdH.betaR s t (ℓ:ℕ))^2)) : ℝ) : ℂ) := by
      simp [HvdH.diagD', HvdH.diagD, Matrix.diagonal_apply_eq]
    rw [hval, Complex.ofReal_re, hUdef, hβdef, hcdef]
    ring
  have h23 : |(E:ℝ)/(2:ℝ)^(auPrec p + c) - Real.exp y/(2:ℝ)^c| ≤ (2/(2:ℝ)^p)/(2:ℝ)^c := by
    have hdiff : (E:ℝ)/(2:ℝ)^(auPrec p + c) - Real.exp y/(2:ℝ)^c
        = ((E:ℝ)/(2:ℝ)^(auPrec p) - Real.exp y)/(2:ℝ)^c := by
      rw [pow_add]; field_simp
    rw [hdiff, abs_div, abs_of_pos (by positivity : (0:ℝ) < (2:ℝ)^c)]
    exact div_le_div_of_nonneg_right hE (by positivity)
  have hyUabs : |y - U| ≤ W/(2:ℝ)^(auPrec p) := by
    have h : y - U = ((Z:ℝ) - (2:ℝ)^(auPrec p) * U)/(2:ℝ)^(auPrec p) := by
      rw [hydef]; field_simp
    rw [h, abs_div, abs_of_pos hP]
    exact div_le_div_of_nonneg_right hZclose (le_of_lt hP)
  have hWdiv : W/(2:ℝ)^(auPrec p) ≤ 1 := by
    rw [div_le_one hP]; linarith [hWle, hp1]
  have hmax : max y U ≤ U + 1 := by
    have h1 : y - U ≤ 1 := by linarith [(abs_le.mp hyUabs).2, hWdiv]
    exact max_le (by linarith) (by linarith)
  have h2c1 : (1:ℝ) ≤ (2:ℝ)^c := by
    calc (1:ℝ) = (2:ℝ)^0 := by norm_num
      _ ≤ (2:ℝ)^c := pow_le_pow_right₀ (by norm_num) (Nat.zero_le c)
  have h34 : |Real.exp y/(2:ℝ)^c - Real.exp U/(2:ℝ)^c| ≤ Real.exp 1/(2:ℝ)^(p+100) := by
    have h1 : |Real.exp y/(2:ℝ)^c - Real.exp U/(2:ℝ)^c|
        ≤ Real.exp (max y U) * |y - U| / (2:ℝ)^c := by
      have heq : Real.exp y/(2:ℝ)^c - Real.exp U/(2:ℝ)^c
          = (Real.exp y - Real.exp U)/(2:ℝ)^c := by ring
      rw [heq, abs_div, abs_of_pos (by positivity : (0:ℝ) < (2:ℝ)^c)]
      exact div_le_div_of_nonneg_right (absExpSubLeExpMax y U) (by positivity)
    have h2 : Real.exp (max y U) * |y - U| ≤ Real.exp (U+1) * (W/(2:ℝ)^(auPrec p)) :=
      mul_le_mul (Real.exp_le_exp.mpr hmax) hyUabs (abs_nonneg _) (Real.exp_pos (U+1)).le
    have h3 : Real.exp (U+1) * W ≤ Real.exp 1 * (2:ℝ)^(2*p) := by
      have hEW : Real.exp U * W ≤ (2:ℝ)^(2*p) := by
        have hb1 : Real.exp U ≤ Real.exp (p:ℝ) := Real.exp_le_exp.mpr hUp
        have hhm := mul_le_mul hb1 hWle hW0 (Real.exp_pos (p:ℝ)).le
        exact le_trans hhm (expMulSuccLeFourPow p hp)
      have he : Real.exp (U+1) = Real.exp 1 * Real.exp U := by rw [Real.exp_add]; ring
      rw [he, mul_assoc]
      exact mul_le_mul_of_nonneg_left hEW (Real.exp_pos 1).le
    have h4 : Real.exp (U+1) * (W/(2:ℝ)^(auPrec p))
        ≤ (Real.exp 1 * (2:ℝ)^(2*p))/(2:ℝ)^(auPrec p) := by
      have hEq : Real.exp (U+1) * (W/(2:ℝ)^(auPrec p)) = Real.exp (U+1) * W / (2:ℝ)^(auPrec p) :=
        (mul_div_assoc _ _ _).symm
      rw [hEq]
      exact div_le_div_of_nonneg_right h3 (le_of_lt hP)
    have h5 : (Real.exp 1 * (2:ℝ)^(2*p))/(2:ℝ)^(auPrec p) = Real.exp 1/(2:ℝ)^(p+100) := by
      have hP2 : (2:ℝ)^(auPrec p) = (2:ℝ)^(2*p) * (2:ℝ)^(p+100) := by
        rw [show auPrec p = 2 * p + (p + 100) by simp only [auPrec]; omega, pow_add]
      rw [hP2]
      field_simp
    calc |Real.exp y/(2:ℝ)^c - Real.exp U/(2:ℝ)^c|
        ≤ Real.exp (max y U) * |y - U| / (2:ℝ)^c := h1
      _ ≤ (Real.exp (U+1) * (W/(2:ℝ)^(auPrec p)))/(2:ℝ)^c :=
          div_le_div_of_nonneg_right h2 (by positivity)
      _ ≤ ((Real.exp 1 * (2:ℝ)^(2*p))/(2:ℝ)^(auPrec p))/(2:ℝ)^c :=
          div_le_div_of_nonneg_right h4 (by positivity)
      _ ≤ Real.exp 1/(2:ℝ)^(p+100) := by
          rw [h5, div_div]
          refine div_le_div_of_nonneg_left (Real.exp_pos 1).le h2p100 ?_
          simpa using mul_le_mul_of_nonneg_left h2c1 (le_of_lt h2p100)
  have h23b : (2/(2:ℝ)^p)/(2:ℝ)^c ≤ 1/(32*(2:ℝ)^p) := by
    have h2c64 : (64:ℝ) ≤ (2:ℝ)^c := by
      have hc6 : 6 ≤ c := by
        simp only [hcdef]
        have h4 : 4 ≤ α^2 := by simpa using Nat.pow_le_pow_left hα 2
        omega
      calc (64:ℝ) = (2:ℝ)^6 := by norm_num
        _ ≤ (2:ℝ)^c := pow_le_pow_right₀ (by norm_num) hc6
    calc (2/(2:ℝ)^p)/(2:ℝ)^c = 2/((2:ℝ)^p * (2:ℝ)^c) := by rw [div_div]
      _ ≤ 2/((2:ℝ)^p * 64) := by
          refine div_le_div_of_nonneg_left (by norm_num) (by positivity) ?_
          exact mul_le_mul_of_nonneg_left h2c64 (le_of_lt h2p)
      _ = 1/(32*(2:ℝ)^p) := by ring
  have hfinal : (1:ℝ)/(2:ℝ)^p + 1/(32*(2:ℝ)^p) + Real.exp 1/(2:ℝ)^(p+100) ≤ 2/(2:ℝ)^p := by
    have key : (1:ℝ)/(2:ℝ)^p + 1/(32*(2:ℝ)^p) + Real.exp 1/(2:ℝ)^(p+100)
        = (1 + 1/32 + Real.exp 1/(2:ℝ)^100)/(2:ℝ)^p := by
      rw [show (2:ℝ)^(p+100) = (2:ℝ)^p * (2:ℝ)^100 by rw [← pow_add]]
      field_simp
    rw [key]
    apply div_le_div_of_nonneg_right _ (le_of_lt h2p)
    have hb : Real.exp 1/(2:ℝ)^100 ≤ 1/32 := by
      rw [div_le_iff₀ (by positivity : (0:ℝ) < (2:ℝ)^100)]
      have he1 : Real.exp 1 ≤ 4 := by linarith [Real.exp_one_lt_d9]
      have h4 : (4:ℝ) ≤ (1/32) * (2:ℝ)^100 := by norm_num
      linarith
    linarith
  have hmain : |(buWd p α s t (ℓ:ℤ) : ℝ)/(2:ℝ)^p - Real.exp U/(2:ℝ)^c| ≤ 2/(2:ℝ)^p := by
    have hsum : |(buWd p α s t (ℓ:ℤ) : ℝ)/(2:ℝ)^p - (E:ℝ)/(2:ℝ)^(auPrec p + c)|
        + |(E:ℝ)/(2:ℝ)^(auPrec p + c) - Real.exp y/(2:ℝ)^c|
        + |Real.exp y/(2:ℝ)^c - Real.exp U/(2:ℝ)^c| ≤ 2/(2:ℝ)^p := by
      linarith [htdiv1, h23, h34, h23b, hfinal]
    calc |(buWd p α s t (ℓ:ℤ) : ℝ)/(2:ℝ)^p - Real.exp U/(2:ℝ)^c|
        ≤ |(buWd p α s t (ℓ:ℤ) : ℝ)/(2:ℝ)^p - (E:ℝ)/(2:ℝ)^(auPrec p + c)|
          + |(E:ℝ)/(2:ℝ)^(auPrec p + c) - Real.exp y/(2:ℝ)^c|
          + |Real.exp y/(2:ℝ)^c - Real.exp U/(2:ℝ)^c| := by
          have hA := abs_sub_le ((buWd p α s t (ℓ:ℤ) : ℝ)/(2:ℝ)^p) ((E:ℝ)/(2:ℝ)^(auPrec p+c)) (Real.exp U/(2:ℝ)^c)
          have hB := abs_sub_le ((E:ℝ)/(2:ℝ)^(auPrec p+c)) (Real.exp y/(2:ℝ)^c) (Real.exp U/(2:ℝ)^c)
          linarith
      _ ≤ 2/(2:ℝ)^p := hsum
  rw [hV]
  exact hmain


end Work.Resample
