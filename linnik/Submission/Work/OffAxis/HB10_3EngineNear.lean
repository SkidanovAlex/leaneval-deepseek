import Mathlib
import Submission.Work.ZeroFreeTables.OffAxis.Defs
import Submission.Work.ZeroFreeTables.OffAxis.WideDefs
import Submission.Work.ZeroFreeTables.OffAxis.L52SupplyGen
import Submission.Work.ZeroFreeTables.OffAxis.HB10_3EngineHelpers
import Submission.Work.ZeroFreeTables.Ksum_positivity_three
import Submission.Work.NumberTheory.Linnik.scratch_l62app_phi
import Submission.Commons.NumberTheory.Linnik.Ksum_principal_le
import Submission.Work.ZeroFreeTables.OffAxis.RectC.Facts
import Submission.Work.ZeroFreeTables.hbLemma6_2_engine_v2
import Submission.Work.LinnikAreas.boxMaxZero
import Submission.Work.ZeroFreeTables.TestFn_F_eq_integral
import Submission.Work.ZeroFreeTables.OffAxis.offAxis_identify
import Submission.Work.LinnikAreas.principalKsumWide
import Submission.Work.A7.zeroMult_conj_inv
import Submission.Work.OffAxis.KsumLeTwoMain6

open DirichletCharacter Complex
open scoped Classical BigOperators ComplexConjugate
open scoped Interval
open MeasureTheory

set_option maxHeartbeats 1000000

noncomputable section

namespace Work.OffAxis

open Work.LinnikContract


/-! ## Elementary facts about `λ` at a zero -/

/-- `λ(ρ) ≥ 0` for a zero of a non-principal character. -/
theorem lamOf_nonneg_of_zeroMult {q : ℕ} [NeZero q] {χ : DirichletCharacter ℂ q} {ρ : ℂ}
    (hzm : Work.LinnikContract.zeroMult χ ρ ≠ 0) : 0 ≤ Work.LinnikContract.lamOf q ρ := by
  have hlog : 0 ≤ Real.log (q : ℝ) := Real.log_nonneg (by exact_mod_cast NeZero.one_le)
  rw [Work.LinnikContract.lamOf]
  refine mul_nonneg ?_ hlog
  have := Work.LinnikAreas.boxMaxZeroAux.zeroMult_re_lt_one χ hzm
  linarith

/-- A zero of a non-principal character of the completed `L`-function has `|Re ρ| ≤ 1`. -/
theorem abs_re_le_one_of_zeroMult {q : ℕ} [NeZero q] {χ : DirichletCharacter ℂ q}
    (hχ : χ ≠ 1) {ρ : ℂ} (hzm : Work.LinnikContract.zeroMult χ ρ ≠ 0) : |ρ.re| ≤ 1 := by
  haveI : NeZero χ.conductor := ⟨χ.conductor_ne_zero⟩
  have hψne : χ.primitiveCharacter ≠ 1 := by
    intro h
    apply hχ
    rw [← DirichletCharacter.changeLevel_primitiveCharacter χ, h]
    exact DirichletCharacter.changeLevel_one χ.conductor_dvd_level
  have hzero : DirichletCharacter.completedLFunction χ.primitiveCharacter ρ = 0 :=
    apply_eq_zero_of_analyticOrderNatAt_ne_zero (by simpa [Work.LinnikContract.zeroMult] using hzm)
  obtain ⟨h1, h2⟩ :=
    Commons.NumberTheory.DirichletCharacter.zerosInStrip χ.primitiveCharacter hψne
      (DirichletCharacter.primitiveCharacter_isPrimitive χ) ρ hzero
  rw [abs_le]
  exact ⟨by linarith, by linarith⟩

/-- The threshold `⌈exp M⌉ + 1 ≤ q` makes `M ≤ log q`. -/
theorem le_log_of_ceil_exp_le {M : ℝ} {q : ℕ} (hq : Nat.ceil (Real.exp M) + 1 ≤ q) :
    M ≤ Real.log (q : ℝ) := by
  have h1 : Real.exp M ≤ (Nat.ceil (Real.exp M) : ℝ) := Nat.le_ceil _
  have h2 : ((Nat.ceil (Real.exp M) : ℕ) : ℝ) + 1 ≤ (q : ℝ) := by exact_mod_cast hq
  have h3 : Real.exp M ≤ (q : ℝ) := by linarith
  calc M = Real.log (Real.exp M) := (Real.log_exp M).symm
    _ ≤ Real.log (q : ℝ) := Real.log_le_log (Real.exp_pos M) h3

/-- The argument of the extracted zero term: `(s - ρ)·log q = λ(ρ) - λ`. -/
theorem sub_mul_log_eq {q : ℕ} {β γ lam lam₁ : ℝ} {ρ : ℂ}
    (hlog : Real.log (q : ℝ) ≠ 0)
    (hβ : β = 1 - lam₁ / Real.log (q : ℝ)) (hρre : ρ.re = 1 - lam / Real.log (q : ℝ))
    (hργ : ρ.im = γ) :
    ((β : ℂ) + (γ : ℂ) * Complex.I - ρ) * (Real.log (q : ℝ) : ℂ) = ((lam - lam₁ : ℝ) : ℂ) := by
  have h1 : ((β : ℂ) + (γ : ℂ) * Complex.I - ρ) = ((((lam - lam₁) / Real.log (q : ℝ)) : ℝ) : ℂ) := by
    apply Complex.ext
    · have hre : (((β : ℂ) + (γ : ℂ) * Complex.I - ρ).re) = β - ρ.re := by simp
      rw [Complex.ofReal_re, hre, hβ, hρre]
      field_simp
      ring
    · have him : (((β : ℂ) + (γ : ℂ) * Complex.I - ρ).im) = γ - ρ.im := by simp
      rw [Complex.ofReal_im, him, hργ]
      ring
  rw [h1, ← Complex.ofReal_mul]
  congr 1
  rw [div_mul_cancel₀ _ hlog]

/-! ## The `F`-method case-1 engine: HB (10.6) -/
/-- **HB (10.6) in the case of Lemma 10.1.**  For any test function `T` of HB's class, and any
three conjugate pairs of non-principal characters at rectangle height `L` with no principal
signed triple product, `lam₂ ≤ lam₃ ≤ 6/7`, and `ρ₁` the rectangle minimiser, the `F`-method
combination is non-negative:
`F(-lam₁) - F(0) - F(lam₂-lam₁) - F(lam₃-lam₁) + f(0)(7/6 + 8ε') ≥ 0`. -/
theorem hb106NearF1 (T : Work.ZeroFreeTables.TestFn) (ε' : ℝ) (hε' : 0 < ε') :
    ∀ L : ℝ, 1 ≤ L → ∃ q₀ : ℕ, ∀ q : ℕ, q₀ ≤ q → ∀ [NeZero q]
      (χ₁ χ₂ χ₃ : DirichletCharacter ℂ q) (ρ₁ ρ₂ ρ₃ : ℂ),
      Work.ZeroFreeTables.IsRectMin L χ₁ ρ₁ →
      Work.ZeroFreeTables.IsZAt L χ₂ ρ₂ → Work.ZeroFreeTables.IsZAt L χ₃ ρ₃ →
      χ₂ ≠ χ₁ → χ₂ ≠ χ₁⁻¹ → χ₃ ≠ χ₁ → χ₃ ≠ χ₁⁻¹ → χ₃ ≠ χ₂ → χ₃ ≠ χ₂⁻¹ →
      Work.LinnikContract.lamOf q ρ₂ ≤ Work.LinnikContract.lamOf q ρ₃ →
      Work.LinnikContract.lamOf q ρ₃ ≤ 6/7 →
      χ₁ * χ₂ * χ₃ ≠ 1 → χ₁ * χ₂ ≠ χ₃ → χ₁ * χ₃ ≠ χ₂ → χ₂ * χ₃ ≠ χ₁ →
      0 ≤ T.F (-(Work.LinnikContract.lamOf q ρ₁)) - T.F 0
        - T.F (Work.LinnikContract.lamOf q ρ₂ - Work.LinnikContract.lamOf q ρ₁)
        - T.F (Work.LinnikContract.lamOf q ρ₃ - Work.LinnikContract.lamOf q ρ₁)
        + T.f 0 * (7/6 + 8 * ε') := by
  obtain ⟨δ, hδ0, hδ1, qL52, hL52⟩ := Work.ZeroFreeTables.OffAxis.L52SupplyGen ε' hε'
  obtain ⟨B, hB0, hBnd⟩ := T.f_bound
  have hF : ∀ z : ℂ, 0 ≤ z.re →
      0 ≤ (∫ t in (0:ℝ)..T.x₀, Complex.exp (-(z * (t : ℂ))) * ((T.f t : ℝ) : ℂ)).re := by
    intro z hz
    rw [← T.Fc_spec]
    exact T.Fc_re_nonneg z hz
  obtain ⟨qA, hA⟩ := Commons.NumberTheory.Linnik.Ksum_le_self_of_L52_phi T.x₀ B (1/6)
    T.x₀_pos hB0 (f := T.f) T.f_cont T.f_supp T.f_diff hBnd T.f0_pos hF hε' hδ0 hδ1
  obtain ⟨qS, hS⟩ := Commons.NumberTheory.Linnik.Ksum_le_single_of_L52_phi T.x₀ B (1/6)
    T.x₀_pos hB0 (f := T.f) T.f_cont T.f_supp T.f_diff hBnd T.f0_pos hF hε' hδ0 hδ1
  obtain ⟨qP, hP⟩ := Commons.NumberTheory.Linnik.Ksum_principal_le T.x₀ B T.x₀_pos hB0
    (f := T.f) T.f_cont T.f_supp T.f_diff hBnd hε' T.f0_pos
  intro L hL1
  refine ⟨max (max (max qL52 qA) (max qS qP))
      (Nat.ceil (Real.exp (max (max L ((6:ℝ)/7/δ)) (Real.exp (((6:ℝ)/7)^2)))) + 1), ?_⟩
  intro q hq _inst χ₁ χ₂ χ₃ ρ₁ ρ₂ ρ₃ hR hZ2 hZ3
    hne21 hne2i hne31 hne3i hne32 hne3ii hlam23 hlam3 hprod1 hprod2 hprod3 hprod4
  have hqA : qA ≤ q := by omega
  have hqS : qS ≤ q := by omega
  have hqP : qP ≤ q := by omega
  have hqL52 : qL52 ≤ q := by omega
  have hexpq : Nat.ceil (Real.exp (max (max L ((6:ℝ)/7/δ)) (Real.exp (((6:ℝ)/7)^2)))) + 1 ≤ q := by
    omega
  have hMle : max (max L ((6:ℝ)/7/δ)) (Real.exp (((6:ℝ)/7)^2)) ≤ Real.log (q : ℝ) :=
    le_log_of_ceil_exp_le hexpq
  have hLle : L ≤ Real.log (q : ℝ) :=
    le_trans (le_trans (le_max_left _ _) (le_max_left _ _)) hMle
  have hδle : (6:ℝ)/7/δ ≤ Real.log (q : ℝ) :=
    le_trans (le_trans (le_max_right _ _) (le_max_left _ _)) hMle
  have hexple : Real.exp (((6:ℝ)/7)^2) ≤ Real.log (q : ℝ) :=
    le_trans (le_max_right _ _) hMle
  have hloglog : ((6:ℝ)/7)^2 ≤ Real.log (Real.log (q : ℝ)) := by
    calc ((6:ℝ)/7)^2 = Real.log (Real.exp (((6:ℝ)/7)^2)) := (Real.log_exp _).symm
      _ ≤ Real.log (Real.log (q : ℝ)) := Real.log_le_log (Real.exp_pos _) hexple
  have hloglog0 : 0 ≤ Real.log (Real.log (q : ℝ)) := le_trans (by norm_num) hloglog
  have hsqrt : (6:ℝ)/7 ≤ Real.sqrt (Real.log (Real.log (q : ℝ))) := by
    rw [Real.le_sqrt (by norm_num) hloglog0]
    exact hloglog
  have hlogq : 0 < Real.log (q : ℝ) := by
    have h1 : (1:ℝ) < Real.exp (((6:ℝ)/7)^2) := Real.one_lt_exp_iff.mpr (by norm_num)
    linarith [hexple]
  have hδinv : (6:ℝ)/7/Real.log (q : ℝ) ≤ δ := by
    rw [div_le_iff₀ hlogq]
    rw [mul_comm]
    rw [div_le_iff₀ hδ0] at hδle
    linarith
  set lam₁ : ℝ := Work.LinnikContract.lamOf q ρ₁ with hlam₁
  set lam₂ : ℝ := Work.LinnikContract.lamOf q ρ₂ with hlam₂
  set lam₃ : ℝ := Work.LinnikContract.lamOf q ρ₃ with hlam₃
  set γ₁ : ℝ := ρ₁.im with hγ₁
  set γ₂ : ℝ := ρ₂.im with hγ₂
  set γ₃ : ℝ := ρ₃.im with hγ₃
  set β : ℝ := 1 - lam₁ / Real.log (q : ℝ) with hβ
  have hl1nn : 0 ≤ lam₁ := by rw [hlam₁]; exact lamOf_nonneg_of_zeroMult hR.1.2.1
  have hl2nn : 0 ≤ lam₂ := by rw [hlam₂]; exact lamOf_nonneg_of_zeroMult hZ2.2.1
  have hl3nn : 0 ≤ lam₃ := by rw [hlam₃]; exact lamOf_nonneg_of_zeroMult hZ3.2.1
  have hl12 : lam₁ ≤ lam₂ := by
    rw [hlam₁, hlam₂]
    exact hR.2 χ₂ ρ₂ ⟨hZ2.1, hZ2.2.1, le_trans hZ2.2.2 (by linarith)⟩
  have hl13 : lam₁ ≤ lam₃ := le_trans hl12 hlam23
  have hl16 : lam₁ ≤ 6/7 := le_trans hl13 hlam3
  have hl26 : lam₂ ≤ 6/7 := le_trans hlam23 hlam3
  have hγ1L : |γ₁| ≤ L := by rw [hγ₁]; exact hR.1.2.2
  have hγ2L : |γ₂| ≤ L := by rw [hγ₂]; exact hZ2.2.2
  have hγ3L : |γ₃| ≤ L := by rw [hγ₃]; exact hZ3.2.2
  have hβ1 : |β - 1| = lam₁ / Real.log (q : ℝ) := by
    rw [hβ, show 1 - lam₁ / Real.log (q : ℝ) - 1 = -(lam₁ / Real.log (q : ℝ)) by ring, abs_neg,
      abs_of_nonneg (div_nonneg hl1nn hlogq.le)]
  have hdivle : lam₁ / Real.log (q : ℝ)
      ≤ Real.sqrt (Real.log (Real.log (q : ℝ))) / Real.log (q : ℝ) :=
    div_le_div_of_nonneg_right (le_trans hl16 hsqrt) hlogq.le
  -- the range conditions at a point `(β) + iγ`
  have hrange : ∀ (γ : ℝ), |γ| ≤ 3 * L →
      |(((β : ℂ) + (γ : ℂ) * Complex.I).re - 1)| ≤
          Real.sqrt (Real.log (Real.log (q : ℝ))) / Real.log (q : ℝ) ∧
      |(((β : ℂ) + (γ : ℂ) * Complex.I).im)| ≤ 10 * Real.log (q : ℝ) ∧
      1 - Real.sqrt (Real.log (Real.log (q : ℝ))) / Real.log (q : ℝ)
        ≤ ((β : ℂ) + (γ : ℂ) * Complex.I).re := by
    intro γ hγ
    have hre : (((β : ℂ) + (γ : ℂ) * Complex.I).re) = β := by simp
    have him : (((β : ℂ) + (γ : ℂ) * Complex.I).im) = γ := by simp
    refine ⟨?_, ?_, ?_⟩
    · rw [hre, hβ1]; exact hdivle
    · rw [him]; linarith
    · rw [hre, hβ]; linarith
  -- (6.5)/(6.6): the window condition, from the rectangle minimality of `ρ₁`
  have hwin : ∀ (χ : DirichletCharacter ℂ q) [NeZero χ.conductor], χ ≠ 1 → ∀ s : ℂ,
      s.re = β → |s.im| ≤ 3 * L →
      ∀ u : ℂ, (MeromorphicOn.divisor (DirichletCharacter.completedLFunction χ.primitiveCharacter)
          (Metric.closedBall 0 (|s.im| + 2))) u ≠ 0 →
        ‖(1:ℂ) + (s.im : ℂ) * Complex.I - u‖ ≤ δ → u.re ≤ s.re := by
    intro χ _instc hχ s hs hsim u hdiv hwu
    have hzm : Work.LinnikContract.zeroMult χ u ≠ 0 := Work.ZeroFreeTables.OffAxis.zeroMult_ne_zero_of_divisor χ hχ hdiv
    have him1 : |s.im - u.im| ≤ δ := by
      have h := Complex.abs_im_le_norm ((1:ℂ) + (s.im : ℂ) * Complex.I - u)
      have h' : (((1:ℂ) + (s.im : ℂ) * Complex.I - u).im) = s.im - u.im := by simp
      rw [h'] at h
      exact le_trans h hwu
    have him2 : |u.im| ≤ |s.im| + δ := by
      calc |u.im| = |s.im - (s.im - u.im)| := by ring_nf
        _ ≤ |s.im| + |s.im - u.im| := abs_sub _ _
        _ ≤ |s.im| + δ := by linarith
    have him3 : |u.im| ≤ 10 * L := by linarith [hsim, him2, hδ1, hL1]
    have hZ : Work.ZeroFreeTables.IsZAt (10 * L) χ u := ⟨hχ, hzm, him3⟩
    have hle : Work.LinnikContract.lamOf q ρ₁ ≤ Work.LinnikContract.lamOf q u := hR.2 χ u hZ
    rw [← hlam₁, Work.LinnikContract.lamOf] at hle
    rw [hs, hβ]
    have h2 : lam₁ / Real.log (q : ℝ) ≤ 1 - u.re := by
      rw [div_le_iff₀ hlogq]
      linarith
    linarith
  -- conductor instances
  haveI hc1 : NeZero χ₁.conductor := ⟨χ₁.conductor_ne_zero⟩
  haveI hc2 : NeZero χ₂.conductor := ⟨χ₂.conductor_ne_zero⟩
  haveI hc3 : NeZero χ₃.conductor := ⟨χ₃.conductor_ne_zero⟩
  haveI hc12 : NeZero (χ₁ * χ₂).conductor := ⟨(χ₁ * χ₂).conductor_ne_zero⟩
  haveI hc1i2 : NeZero (χ₁ * χ₂⁻¹).conductor := ⟨(χ₁ * χ₂⁻¹).conductor_ne_zero⟩
  haveI hc13 : NeZero (χ₁ * χ₃).conductor := ⟨(χ₁ * χ₃).conductor_ne_zero⟩
  haveI hc1i3 : NeZero (χ₁ * χ₃⁻¹).conductor := ⟨(χ₁ * χ₃⁻¹).conductor_ne_zero⟩
  haveI hc23 : NeZero (χ₂ * χ₃).conductor := ⟨(χ₂ * χ₃).conductor_ne_zero⟩
  haveI hc2i3 : NeZero (χ₂ * χ₃⁻¹).conductor := ⟨(χ₂ * χ₃⁻¹).conductor_ne_zero⟩
  haveI hc123 : NeZero (χ₁ * χ₂ * χ₃).conductor := ⟨(χ₁ * χ₂ * χ₃).conductor_ne_zero⟩
  haveI hc12i3 : NeZero (χ₁ * χ₂ * χ₃⁻¹).conductor := ⟨(χ₁ * χ₂ * χ₃⁻¹).conductor_ne_zero⟩
  haveI hc1i23 : NeZero (χ₁ * χ₂⁻¹ * χ₃).conductor := ⟨(χ₁ * χ₂⁻¹ * χ₃).conductor_ne_zero⟩
  haveI hc123i : NeZero (χ₁⁻¹ * χ₂ * χ₃).conductor := ⟨(χ₁⁻¹ * χ₂ * χ₃).conductor_ne_zero⟩
  -- non-principality of the auxiliary characters
  have hp12 : χ₁ * χ₂ ≠ 1 := fun h => hne2i (eq_inv_of_mul_eq_one_right h)
  have hp1i2 : χ₁ * χ₂⁻¹ ≠ 1 := fun h => hne21 ((mul_inv_eq_one.mp h).symm)
  have hp13 : χ₁ * χ₃ ≠ 1 := fun h => hne3i (eq_inv_of_mul_eq_one_right h)
  have hp1i3 : χ₁ * χ₃⁻¹ ≠ 1 := fun h => hne31 ((mul_inv_eq_one.mp h).symm)
  have hp23 : χ₂ * χ₃ ≠ 1 := fun h => hne3ii (eq_inv_of_mul_eq_one_right h)
  have hp2i3 : χ₂ * χ₃⁻¹ ≠ 1 := fun h => hne32 ((mul_inv_eq_one.mp h).symm)
  have ht12i3 : χ₁ * χ₂ * χ₃⁻¹ ≠ 1 := fun h => hprod2 (mul_inv_eq_one.mp h)
  have ht1i23 : χ₁ * χ₂⁻¹ * χ₃ ≠ 1 := by
    intro h
    have h' : (χ₁ * χ₃) * χ₂⁻¹ = χ₁ * χ₂⁻¹ * χ₃ := by
      rw [mul_assoc, mul_comm χ₃ χ₂⁻¹, ← mul_assoc]
    rw [← h'] at h
    exact hprod3 (mul_inv_eq_one.mp h)
  have ht123i : χ₁⁻¹ * χ₂ * χ₃ ≠ 1 := by
    intro h
    have h' : (χ₂ * χ₃) * χ₁⁻¹ = χ₁⁻¹ * χ₂ * χ₃ := by
      rw [mul_assoc, mul_comm χ₃ χ₁⁻¹, ← mul_assoc, mul_comm χ₂ χ₁⁻¹]
    rw [← h'] at h
    exact hprod4 (mul_inv_eq_one.mp h)
  -- the 14 point bounds

  have hbP : Work.ZeroFreeTables.Ksum q T.f (Real.log (q : ℝ)) (β : ℂ) 1
      ≤ Real.log (q : ℝ) * T.F (-lam₁) + T.f 0 * ε' * Real.log (q : ℝ) := by
    have h := hP hqP (β := β) (lam := lam₁) ?_ ?_
    · have hFint : T.F (-lam₁) = ∫ t in (0:ℝ)..T.x₀, Real.exp (lam₁ * t) * T.f t := by
        rw [Work.ZeroFreeTables.TestFn_F_eq_integral]
        apply intervalIntegral.integral_congr
        intro t _
        simp only [neg_mul, neg_neg]
      rw [hFint]
      exact h
    · rw [hlam₁, hβ]
      field_simp
      ring
    · rw [hβ1]; exact hdivle
  have hsingle : ∀ (χ : DirichletCharacter ℂ q) [NeZero χ.conductor], χ ≠ 1 →
      ∀ (γ : ℝ), |γ| ≤ 3 * L → ∀ (ρ : ℂ) (lam : ℝ),
      ρ.im = γ → lam = Work.LinnikContract.lamOf q ρ → lam ≤ 6/7 →
      Work.LinnikContract.zeroMult χ ρ ≠ 0 →
      Work.ZeroFreeTables.Ksum q T.f (Real.log (q : ℝ)) ((β : ℂ) + (γ : ℂ) * Complex.I) χ
        ≤ -Real.log (q : ℝ) * T.F (lam - lam₁) + T.f 0 * (1/6 + ε') * Real.log (q : ℝ) := by
    intro χ _instc hχ γ hγ ρ lam hργ hlam hlam67 hzm
    obtain ⟨hr1, hr2, hr3⟩ := hrange γ hγ
    have hmem : ρ ∈ Metric.closedBall (0:ℂ) (|γ| + 2) := by
      have h := Work.ZeroFreeTables.mem_closedBall_of_absre_le_one_v2 (abs_re_le_one_of_zeroMult hχ hzm)
      rwa [hργ] at h
    have hdiv : (MeromorphicOn.divisor (DirichletCharacter.completedLFunction χ.primitiveCharacter)
        (Metric.closedBall 0 (|((β : ℂ) + (γ : ℂ) * Complex.I).im| + 2))) ρ ≠ 0 := by
      have him : (((β : ℂ) + (γ : ℂ) * Complex.I).im) = γ := by simp
      rw [him]
      exact Work.ZeroFreeTables.OffAxis.divisor_ne_zero_of_zeroMult χ hχ hmem hzm
    have hwinρ : ‖(1:ℂ) + ((((β : ℂ) + (γ : ℂ) * Complex.I)).im : ℂ) * Complex.I - ρ‖ ≤ δ := by
      have him : (((β : ℂ) + (γ : ℂ) * Complex.I).im) = γ := by simp
      rw [him, ← hργ]
      have h1 : (1:ℂ) + (ρ.im : ℂ) * Complex.I - ρ = ((1 - ρ.re : ℝ) : ℂ) := by
        apply Complex.ext <;> simp
      rw [h1, Complex.norm_real, Real.norm_eq_abs]
      have hre : ρ.re = 1 - lam / Real.log (q : ℝ) := by
        rw [hlam, Work.LinnikContract.lamOf]; field_simp; ring
      have hval : 1 - ρ.re = lam / Real.log (q : ℝ) := by rw [hre]; ring
      have hlamnn : 0 ≤ lam := by rw [hlam]; exact lamOf_nonneg_of_zeroMult hzm
      rw [abs_of_nonneg (by rw [hval]; exact div_nonneg hlamnn hlogq.le), hval]
      exact le_trans (div_le_div_of_nonneg_right hlam67 hlogq.le) hδinv
    have hsre : (((β : ℂ) + (γ : ℂ) * Complex.I).re) = β := by simp
    have h := hS (q := q) hqS χ hχ hr1 hr2 hr3 (hL52 q hqL52 χ hχ) hdiv hwinρ
      (hwin χ hχ ((β : ℂ) + (γ : ℂ) * Complex.I) hsre
        (by rw [show (((β : ℂ) + (γ : ℂ) * Complex.I).im) = γ from by simp]; exact hγ))
    have hint : (∫ t in (0:ℝ)..T.x₀,
          Complex.exp (-(((((β : ℂ) + (γ : ℂ) * Complex.I)) - ρ) * (Real.log (q : ℝ) : ℂ) * (t:ℂ))) *
            ((T.f t : ℝ) : ℂ)).re = T.F (lam - lam₁) := by
      rw [← T.Fc_spec]
      rw [sub_mul_log_eq (q := q) (β := β) (γ := γ) (lam := lam) (lam₁ := lam₁) (ρ := ρ)
        hlogq.ne' hβ ?_ hργ]
      · rfl
      · rw [hlam, Work.LinnikContract.lamOf]; field_simp; ring
    rw [hint] at h
    exact h
  have hbS1 : Work.ZeroFreeTables.Ksum q T.f (Real.log (q : ℝ))
        ((β : ℂ) + (γ₁ : ℂ) * Complex.I) χ₁
      ≤ -Real.log (q : ℝ) * T.F 0 + T.f 0 * (1/6 + ε') * Real.log (q : ℝ) := by
    have h := hsingle χ₁ hR.1.1 γ₁ (by rw [hγ₁]; linarith [hL1]) ρ₁ lam₁ (by rw [hγ₁]) hlam₁ hl16 hR.1.2.1
    simpa only [sub_self] using h
  have hbS2 : Work.ZeroFreeTables.Ksum q T.f (Real.log (q : ℝ))
        ((β : ℂ) + (γ₂ : ℂ) * Complex.I) χ₂
      ≤ -Real.log (q : ℝ) * T.F (lam₂ - lam₁) + T.f 0 * (1/6 + ε') * Real.log (q : ℝ) :=
    hsingle χ₂ hZ2.1 γ₂ (by rw [hγ₂]; linarith [hL1]) ρ₂ lam₂ (by rw [hγ₂]) hlam₂ hl26 hZ2.2.1
  have hbS3 : Work.ZeroFreeTables.Ksum q T.f (Real.log (q : ℝ))
        ((β : ℂ) + (γ₃ : ℂ) * Complex.I) χ₃
      ≤ -Real.log (q : ℝ) * T.F (lam₃ - lam₁) + T.f 0 * (1/6 + ε') * Real.log (q : ℝ) :=
    hsingle χ₃ hZ3.1 γ₃ (by rw [hγ₃]; linarith [hL1]) ρ₃ lam₃ (by rw [hγ₃]) hlam₃ hlam3 hZ3.2.1
  have hself : ∀ (χ : DirichletCharacter ℂ q) [NeZero χ.conductor], χ ≠ 1 →
      ∀ (γ : ℝ), |γ| ≤ 3 * L →
      Work.ZeroFreeTables.Ksum q T.f (Real.log (q : ℝ)) ((β : ℂ) + (γ : ℂ) * Complex.I) χ
        ≤ T.f 0 * (1/6 + ε') * Real.log (q : ℝ) := by
    intro χ _instc hχ γ hγ
    obtain ⟨hr1, hr2, hr3⟩ := hrange γ hγ
    have hsre : (((β : ℂ) + (γ : ℂ) * Complex.I).re) = β := by simp
    exact hA (q := q) hqA χ hχ hr1 hr2 hr3 (hL52 q hqL52 χ hχ)
      (hwin χ hχ ((β : ℂ) + (γ : ℂ) * Complex.I) hsre
        (by rw [show (((β : ℂ) + (γ : ℂ) * Complex.I).im) = γ from by simp]; exact hγ))
  have hbP12 : Work.ZeroFreeTables.Ksum q T.f (Real.log (q : ℝ))
        ((β : ℂ) + ((γ₁ : ℂ) + (γ₂ : ℂ)) * Complex.I) (χ₁ * χ₂)
      ≤ T.f 0 * (1/6 + ε') * Real.log (q : ℝ) := by
    have h := hself (χ₁ * χ₂) hp12 (γ₁ + γ₂) (by
      calc |γ₁ + γ₂| ≤ |γ₁| + |γ₂| := abs_add_le _ _
        _ ≤ 3 * L := by linarith [hL1])
    simpa only [ofReal_add] using h
  have hbPi12 : Work.ZeroFreeTables.Ksum q T.f (Real.log (q : ℝ))
        ((β : ℂ) + ((γ₁ : ℂ) - (γ₂ : ℂ)) * Complex.I) (χ₁ * χ₂⁻¹)
      ≤ T.f 0 * (1/6 + ε') * Real.log (q : ℝ) := by
    have h := hself (χ₁ * χ₂⁻¹) hp1i2 (γ₁ - γ₂) (by
      calc |γ₁ - γ₂| ≤ |γ₁| + |γ₂| := by
            simpa [sub_eq_add_neg] using abs_add_le γ₁ (-γ₂)
        _ ≤ 3 * L := by linarith [hL1])
    simpa only [ofReal_sub] using h
  have hbP13 : Work.ZeroFreeTables.Ksum q T.f (Real.log (q : ℝ))
        ((β : ℂ) + ((γ₁ : ℂ) + (γ₃ : ℂ)) * Complex.I) (χ₁ * χ₃)
      ≤ T.f 0 * (1/6 + ε') * Real.log (q : ℝ) := by
    have h := hself (χ₁ * χ₃) hp13 (γ₁ + γ₃) (by
      calc |γ₁ + γ₃| ≤ |γ₁| + |γ₃| := abs_add_le _ _
        _ ≤ 3 * L := by linarith [hL1])
    simpa only [ofReal_add] using h
  have hbPi13 : Work.ZeroFreeTables.Ksum q T.f (Real.log (q : ℝ))
        ((β : ℂ) + ((γ₁ : ℂ) - (γ₃ : ℂ)) * Complex.I) (χ₁ * χ₃⁻¹)
      ≤ T.f 0 * (1/6 + ε') * Real.log (q : ℝ) := by
    have h := hself (χ₁ * χ₃⁻¹) hp1i3 (γ₁ - γ₃) (by
      calc |γ₁ - γ₃| ≤ |γ₁| + |γ₃| := by
            simpa [sub_eq_add_neg] using abs_add_le γ₁ (-γ₃)
        _ ≤ 3 * L := by linarith [hL1])
    simpa only [ofReal_sub] using h
  have hbP23 : Work.ZeroFreeTables.Ksum q T.f (Real.log (q : ℝ))
        ((β : ℂ) + ((γ₂ : ℂ) + (γ₃ : ℂ)) * Complex.I) (χ₂ * χ₃)
      ≤ T.f 0 * (1/6 + ε') * Real.log (q : ℝ) := by
    have h := hself (χ₂ * χ₃) hp23 (γ₂ + γ₃) (by
      calc |γ₂ + γ₃| ≤ |γ₂| + |γ₃| := abs_add_le _ _
        _ ≤ 3 * L := by linarith [hL1])
    simpa only [ofReal_add] using h
  have hbPi23 : Work.ZeroFreeTables.Ksum q T.f (Real.log (q : ℝ))
        ((β : ℂ) + ((γ₂ : ℂ) - (γ₃ : ℂ)) * Complex.I) (χ₂ * χ₃⁻¹)
      ≤ T.f 0 * (1/6 + ε') * Real.log (q : ℝ) := by
    have h := hself (χ₂ * χ₃⁻¹) hp2i3 (γ₂ - γ₃) (by
      calc |γ₂ - γ₃| ≤ |γ₂| + |γ₃| := by
            simpa [sub_eq_add_neg] using abs_add_le γ₂ (-γ₃)
        _ ≤ 3 * L := by linarith [hL1])
    simpa only [ofReal_sub] using h
  have hbT123 : Work.ZeroFreeTables.Ksum q T.f (Real.log (q : ℝ))
        ((β : ℂ) + ((γ₁ : ℂ) + (γ₂ : ℂ) + (γ₃ : ℂ)) * Complex.I) (χ₁ * χ₂ * χ₃)
      ≤ T.f 0 * (1/6 + ε') * Real.log (q : ℝ) := by
    have h := hself (χ₁ * χ₂ * χ₃) hprod1 (γ₁ + γ₂ + γ₃) (by
      have h12 : |γ₁ + γ₂| ≤ 2 * L := by
        calc |γ₁ + γ₂| ≤ |γ₁| + |γ₂| := abs_add_le _ _
          _ ≤ 2 * L := by linarith
      calc |γ₁ + γ₂ + γ₃| ≤ |γ₁ + γ₂| + |γ₃| := abs_add_le _ _
        _ ≤ 3 * L := by linarith)
    simpa only [ofReal_add] using h
  have hbT12i3 : Work.ZeroFreeTables.Ksum q T.f (Real.log (q : ℝ))
        ((β : ℂ) + ((γ₁ : ℂ) + (γ₂ : ℂ) - (γ₃ : ℂ)) * Complex.I) (χ₁ * χ₂ * χ₃⁻¹)
      ≤ T.f 0 * (1/6 + ε') * Real.log (q : ℝ) := by
    have h := hself (χ₁ * χ₂ * χ₃⁻¹) ht12i3 (γ₁ + γ₂ - γ₃) (by
      have h12 : |γ₁ + γ₂| ≤ 2 * L := by
        calc |γ₁ + γ₂| ≤ |γ₁| + |γ₂| := abs_add_le _ _
          _ ≤ 2 * L := by linarith
      calc |γ₁ + γ₂ - γ₃| ≤ |γ₁ + γ₂| + |γ₃| := by
            simpa [sub_eq_add_neg] using abs_add_le (γ₁ + γ₂) (-γ₃)
        _ ≤ 3 * L := by linarith)
    simpa only [ofReal_sub, ofReal_add] using h
  have hbT1i23 : Work.ZeroFreeTables.Ksum q T.f (Real.log (q : ℝ))
        ((β : ℂ) + ((γ₁ : ℂ) - (γ₂ : ℂ) + (γ₃ : ℂ)) * Complex.I) (χ₁ * χ₂⁻¹ * χ₃)
      ≤ T.f 0 * (1/6 + ε') * Real.log (q : ℝ) := by
    have h := hself (χ₁ * χ₂⁻¹ * χ₃) ht1i23 (γ₁ - γ₂ + γ₃) (by
      have h12 : |γ₁ - γ₂| ≤ 2 * L := by
        calc |γ₁ - γ₂| ≤ |γ₁| + |γ₂| := by
              simpa [sub_eq_add_neg] using abs_add_le γ₁ (-γ₂)
          _ ≤ 2 * L := by linarith
      calc |γ₁ - γ₂ + γ₃| ≤ |γ₁ - γ₂| + |γ₃| := abs_add_le _ _
        _ ≤ 3 * L := by linarith)
    simpa only [ofReal_sub, ofReal_add] using h
  have hbTi123 : Work.ZeroFreeTables.Ksum q T.f (Real.log (q : ℝ))
        ((β : ℂ) + (-(γ₁ : ℂ) + (γ₂ : ℂ) + (γ₃ : ℂ)) * Complex.I) (χ₁⁻¹ * χ₂ * χ₃)
      ≤ T.f 0 * (1/6 + ε') * Real.log (q : ℝ) := by
    have h := hself (χ₁⁻¹ * χ₂ * χ₃) ht123i (-γ₁ + γ₂ + γ₃) (by
      have h23 : |γ₂ + γ₃| ≤ 2 * L := by
        calc |γ₂ + γ₃| ≤ |γ₂| + |γ₃| := abs_add_le _ _
          _ ≤ 2 * L := by linarith
      have h1 : |-γ₁| = |γ₁| := abs_neg γ₁
      calc |-γ₁ + γ₂ + γ₃| = |(-γ₁) + (γ₂ + γ₃)| := by ring_nf
        _ ≤ |(-γ₁)| + |γ₂ + γ₃| := abs_add_le _ _
        _ ≤ 3 * L := by linarith)
    simpa only [ofReal_neg, ofReal_add] using h
  have hpos := Work.ZeroFreeTables.Ksum_positivity_three (f := T.f) (fun t => T.f_nonneg t)
    (x₀ := T.x₀) (L := Real.log (q : ℝ)) (β := β) (γ₁ := γ₁) (γ₂ := γ₂) (γ₃ := γ₃)
    T.x₀_pos hlogq T.f_supp χ₁ χ₂ χ₃
  simp only [Work.ZeroFreeTables.Ksum] at hbP hbS1 hbS2 hbS3
  simp only [Work.ZeroFreeTables.Ksum] at hbP12 hbPi12 hbP13 hbPi13
  simp only [Work.ZeroFreeTables.Ksum] at hbP23 hbPi23
  simp only [Work.ZeroFreeTables.Ksum] at hbT123 hbT12i3 hbT1i23 hbTi123
  have hkey : 0 ≤ Real.log (q : ℝ) * (T.F (-lam₁) - T.F 0 - T.F (lam₂ - lam₁) - T.F (lam₃ - lam₁))
      + T.f 0 * (7/6 + 8 * ε') * Real.log (q : ℝ) := by
    linarith [hpos, hbP, hbS1, hbS2, hbS3, hbP12, hbPi12, hbP13, hbPi13, hbP23, hbPi23,
      hbT123, hbT12i3, hbT1i23, hbTi123]
  have hX : 0 ≤ T.F (-lam₁) - T.F 0 - T.F (lam₂ - lam₁) - T.F (lam₃ - lam₁) + T.f 0 * (7/6 + 8 * ε') := by
    by_contra hneg
    push_neg at hneg
    have h2 : Real.log (q : ℝ) * (T.F (-lam₁) - T.F 0 - T.F (lam₂ - lam₁) - T.F (lam₃ - lam₁)
        + T.f 0 * (7/6 + 8 * ε')) < 0 := mul_neg_of_pos_of_neg hlogq hneg
    have h3 : Real.log (q : ℝ) * (T.F (-lam₁) - T.F 0 - T.F (lam₂ - lam₁) - T.F (lam₃ - lam₁)
        + T.f 0 * (7/6 + 8 * ε')) = Real.log (q : ℝ) * (T.F (-lam₁) - T.F 0 - T.F (lam₂ - lam₁)
          - T.F (lam₃ - lam₁)) + T.f 0 * (7/6 + 8 * ε') * Real.log (q : ℝ) := by ring
    linarith [hkey, h2, h3]
  rw [hlam₁, hlam₂, hlam₃] at hX
  exact hX

/-! ## Conjugation of a zero pair -/

/-- Conjugating a zero pair `(χ,ρ) ↦ (χ⁻¹, conj ρ)` preserves `IsZAt`. -/
theorem IsZAt_inv_conj {q : ℕ} [NeZero q] {H : ℝ} {χ : DirichletCharacter ℂ q} {ρ : ℂ}
    (h : Work.ZeroFreeTables.IsZAt H χ ρ) :
    Work.ZeroFreeTables.IsZAt H χ⁻¹ (starRingEnd ℂ ρ) := by
  refine ⟨?_, ?_, ?_⟩
  · intro h1
    exact h.1 (inv_eq_one.mp h1)
  · rw [Work.A7.zeroMult_conj_inv χ ρ]
    exact h.2.1
  · simpa [Complex.conj_im, abs_neg] using h.2.2

/-- Conjugating a zero pair `(χ,ρ) ↦ (χ⁻¹, conj ρ)` preserves `IsRectMin`. -/
theorem IsRectMin_inv_conj {q : ℕ} [NeZero q] {L : ℝ} {χ : DirichletCharacter ℂ q} {ρ : ℂ}
    (h : Work.ZeroFreeTables.IsRectMin L χ ρ) :
    Work.ZeroFreeTables.IsRectMin L χ⁻¹ (starRingEnd ℂ ρ) := by
  refine ⟨IsZAt_inv_conj h.1, ?_⟩
  intro χ' u hu
  rw [Work.ZeroFreeTables.OffAxis.lamOf_conj q ρ]
  exact h.2 χ' u hu


/-! ## The canonical second-level engine (HB Lemma 10.2, `χ₁χ₂χ₃ = χ₀`) -/

/-- **HB (10.6) in the case `χ₁χ₂χ₃ = χ₀` of Lemma 10.2**, at rectangle height `L`. -/
theorem hb106Canon (T : Work.ZeroFreeTables.TestFn) (ε' : ℝ) (hε' : 0 < ε') :
    ∀ L : ℝ, 1 ≤ L → ∃ q₀ : ℕ, ∀ q : ℕ, q₀ ≤ q → ∀ [NeZero q]
      (χ₁ χ₂ χ₃ : DirichletCharacter ℂ q) (ρ₁ ρ₂ ρ₃ : ℂ),
      Work.ZeroFreeTables.IsRectMin L χ₁ ρ₁ → ρ₁.im ≠ 0 →
      Work.ZeroFreeTables.IsZAt L χ₂ ρ₂ → Work.ZeroFreeTables.IsZAt L χ₃ ρ₃ →
      χ₂ ≠ χ₁ → χ₂ ≠ χ₁⁻¹ → χ₃ ≠ χ₁ → χ₃ ≠ χ₁⁻¹ → χ₃ ≠ χ₂ → χ₃ ≠ χ₂⁻¹ →
      Work.LinnikContract.lamOf q ρ₂ ≤ Work.LinnikContract.lamOf q ρ₃ →
      Work.LinnikContract.lamOf q ρ₃ ≤ 6/7 →
      χ₁ * χ₂ * χ₃ = 1 →
      (∀ a μ : ℝ, 0 ≤ a → a ≤ 6/7 → |μ| ≤ 4 →
        (T.Fc (((-a : ℝ) : ℂ) + (μ : ℂ) * Complex.I)).re
          - 2 * (T.Fc ((μ : ℂ) * Complex.I)).re ≤ T.f 0 / 6) →
      (∀ a μ : ℝ, 0 ≤ a → a ≤ 6/7 → 4 ≤ |μ| →
        (T.Fc (((-a : ℝ) : ℂ) + (μ : ℂ) * Complex.I)).re ≤ T.f 0 / 6) →
      0 ≤ T.F (-(Work.LinnikContract.lamOf q ρ₁)) - T.F 0
        - T.F (Work.LinnikContract.lamOf q ρ₂ - Work.LinnikContract.lamOf q ρ₁)
        - T.F (Work.LinnikContract.lamOf q ρ₃ - Work.LinnikContract.lamOf q ρ₁)
        + T.f 0 * (7/6 + 8 * ε') := by
  classical
  obtain ⟨δ, hδ0, hδ1, qL52, hL52⟩ := Work.ZeroFreeTables.OffAxis.L52SupplyGen ε' hε'
  obtain ⟨B, hB0, hBnd⟩ := T.f_bound
  have hFnn : ∀ z : ℂ, 0 ≤ z.re →
      0 ≤ (∫ t in (0:ℝ)..T.x₀, Complex.exp (-(z * (t : ℂ))) * ((T.f t : ℝ) : ℂ)).re := by
    intro z hz; rw [← T.Fc_spec z]; exact T.Fc_re_nonneg z hz
  obtain ⟨qA, hA⟩ := Commons.NumberTheory.Linnik.Ksum_le_self_of_L52_phi T.x₀ B (1/6)
    T.x₀_pos hB0 (f := T.f) T.f_cont T.f_supp T.f_diff hBnd T.f0_pos hFnn hε' hδ0 hδ1
  obtain ⟨qS, hS⟩ := Commons.NumberTheory.Linnik.Ksum_le_single_of_L52_phi T.x₀ B (1/6)
    T.x₀_pos hB0 (f := T.f) T.f_cont T.f_supp T.f_diff hBnd T.f0_pos hFnn hε' hδ0 hδ1
  obtain ⟨qP, hP⟩ := Work.LinnikAreas.principalKsumWide T.x₀ B T.x₀_pos hB0
    (f := T.f) T.f_cont T.f_supp T.f_diff hBnd hε' T.f0_pos
  obtain ⟨qT6, hT6⟩ := KsumLeTwoMain6 T.x₀ B T.x₀_pos hB0
    (f := T.f) T.f_cont T.f_supp T.f_diff hBnd T.f0_pos hFnn hε' hδ0 hδ1
  intro L hL1
  refine ⟨max (max (max (max qL52 qA) (max qS qP)) qT6)
      (Nat.ceil (Real.exp (max (max L ((5:ℝ)/δ)) (Real.exp (((6:ℝ)/7)^2)))) + 1), ?_⟩
  intro q hq _inst χ₁ χ₂ χ₃ ρ₁ ρ₂ ρ₃ hR hg1 hZ2 hZ3 h21 h2i h31 h3i h32 h3ii hlam23 hlam3 hprod hnum1 hnum2
  have hqL52 : qL52 ≤ q := by omega
  have hqA : qA ≤ q := by omega
  have hqS : qS ≤ q := by omega
  have hqP : qP ≤ q := by omega
  have hqT6 : qT6 ≤ q := by omega
  have hexpq : Nat.ceil (Real.exp (max (max L ((5:ℝ)/δ)) (Real.exp (((6:ℝ)/7)^2)))) + 1 ≤ q := by omega
  have hMle : max (max L ((5:ℝ)/δ)) (Real.exp (((6:ℝ)/7)^2)) ≤ Real.log (q : ℝ) :=
    le_log_of_ceil_exp_le hexpq
  set Lq : ℝ := Real.log (q : ℝ) with hLqdef
  have hLle : L ≤ Lq := by
    rw [hLqdef]
    exact le_trans (le_trans (le_max_left _ _) (le_max_left _ _)) hMle
  have h5δ : (5:ℝ)/δ ≤ Lq := by
    rw [hLqdef]
    exact le_trans (le_trans (le_max_right _ _) (le_max_left _ _)) hMle
  have hexple : Real.exp (((6:ℝ)/7)^2) ≤ Lq := by
    rw [hLqdef]; exact le_trans (le_max_right _ _) hMle
  have hloglog : ((6:ℝ)/7)^2 ≤ Real.log Lq := by
    calc ((6:ℝ)/7)^2 = Real.log (Real.exp (((6:ℝ)/7)^2)) := (Real.log_exp _).symm
      _ ≤ Real.log Lq := Real.log_le_log (Real.exp_pos _) hexple
  have hloglog0 : 0 ≤ Real.log Lq := le_trans (by norm_num) hloglog
  have hsqrt : (6:ℝ)/7 ≤ Real.sqrt (Real.log Lq) := by
    rw [Real.le_sqrt (by norm_num) hloglog0]; exact hloglog
  have hlogq : 0 < Lq := by
    have h1 : (1:ℝ) < Real.exp (((6:ℝ)/7)^2) := Real.one_lt_exp_iff.mpr (by norm_num)
    rw [hLqdef]; linarith [hexple, h1]
  have hδ5 : (5:ℝ) ≤ δ * Lq := by
    rw [div_le_iff₀ hδ0] at h5δ; linarith [h5δ]
  have hδLq : (12:ℝ)/7 ≤ δ * Lq := by linarith
  have hδinv : (6:ℝ)/7 / Lq ≤ δ := by
    rw [div_le_iff₀ hlogq]; linarith [hδLq]
  set lam₁ : ℝ := Work.LinnikContract.lamOf q ρ₁ with hlam₁
  set lam₂ : ℝ := Work.LinnikContract.lamOf q ρ₂ with hlam₂
  set lam₃ : ℝ := Work.LinnikContract.lamOf q ρ₃ with hlam₃
  set γ₁ : ℝ := ρ₁.im with hγ₁
  set γ₂ : ℝ := ρ₂.im with hγ₂
  set γ₃ : ℝ := ρ₃.im with hγ₃
  set β : ℝ := 1 - lam₁ / Lq with hβ
  set a : ℝ := T.f 0 * (1/6 + ε') * Lq with ha
  have hl1nn : 0 ≤ lam₁ := by rw [hlam₁]; exact lamOf_nonneg_of_zeroMult hR.1.2.1
  have hl2nn : 0 ≤ lam₂ := by rw [hlam₂]; exact lamOf_nonneg_of_zeroMult hZ2.2.1
  have hl3nn : 0 ≤ lam₃ := by rw [hlam₃]; exact lamOf_nonneg_of_zeroMult hZ3.2.1
  have hl12 : lam₁ ≤ lam₂ := by
    rw [hlam₁, hlam₂]
    exact hR.2 χ₂ ρ₂ ⟨hZ2.1, hZ2.2.1, le_trans hZ2.2.2 (by linarith [hL1])⟩
  have hl13 : lam₁ ≤ lam₃ := le_trans hl12 hlam23
  have hl16 : lam₁ ≤ 6/7 := le_trans hl13 hlam3
  have hl26 : lam₂ ≤ 6/7 := le_trans hlam23 hlam3
  have hγ1L : |γ₁| ≤ L := by rw [hγ₁]; exact hR.1.2.2
  have hγ2L : |γ₂| ≤ L := by rw [hγ₂]; exact hZ2.2.2
  have hγ3L : |γ₃| ≤ L := by rw [hγ₃]; exact hZ3.2.2
  have hβ1 : |β - 1| = lam₁ / Lq := by
    rw [hβ, show 1 - lam₁ / Lq - 1 = -(lam₁ / Lq) by ring, abs_neg,
      abs_of_nonneg (div_nonneg hl1nn hlogq.le)]
  have hdivle : lam₁ / Lq ≤ Real.sqrt (Real.log Lq) / Lq :=
    div_le_div_of_nonneg_right (le_trans hl16 hsqrt) hlogq.le
  have hl1' : lam₁ = (1 - ρ₁.re) * Lq := by
    rw [hlam₁, Work.LinnikContract.lamOf, ← hLqdef]
  have hl1'' : lam₁ / Lq = 1 - ρ₁.re := by
    rw [hl1', div_eq_iff hlogq.ne']
  have hcancel1 : (1 - ρ₁.re) * Lq / Lq = 1 - ρ₁.re := by
    rw [div_eq_iff hlogq.ne']
  have hρ1re : ρ₁.re = β := by
    rw [hβ, hl1', hcancel1]; ring
  have hβcast : (β : ℂ) = ((1 - lam₁ / Lq : ℝ) : ℂ) := by rw [hβ]
  have hρ1real : (1 - ρ₁.re) = lam₁ / Lq := hl1''.symm
  have hl2' : lam₂ = (1 - ρ₂.re) * Lq := by
    rw [hlam₂, Work.LinnikContract.lamOf, ← hLqdef]
  have hl2'' : lam₂ / Lq = 1 - ρ₂.re := by
    rw [hl2', div_eq_iff hlogq.ne']
  have hρ2real : (1 - ρ₂.re) = lam₂ / Lq := hl2''.symm
  have hl3' : lam₃ = (1 - ρ₃.re) * Lq := by
    rw [hlam₃, Work.LinnikContract.lamOf, ← hLqdef]
  have hl3'' : lam₃ / Lq = 1 - ρ₃.re := by
    rw [hl3', div_eq_iff hlogq.ne']
  have hρ3real : (1 - ρ₃.re) = lam₃ / Lq := hl3''.symm
  have hconj1real : (1 - (starRingEnd ℂ ρ₁).re) = lam₁ / Lq := by
    rw [Complex.conj_re]; exact hρ1real
  have hconj2real : (1 - (starRingEnd ℂ ρ₂).re) = lam₂ / Lq := by
    rw [Complex.conj_re]; exact hρ2real
  have hconj3real : (1 - (starRingEnd ℂ ρ₃).re) = lam₃ / Lq := by
    rw [Complex.conj_re]; exact hρ3real
  have hFc_conj : ∀ z : ℂ, T.Fc (starRingEnd ℂ z) = starRingEnd ℂ (T.Fc z) := by
    intro z
    rw [T.Fc_spec, T.Fc_spec]
    have hpt : ∀ t : ℝ, Complex.exp (-((starRingEnd ℂ z) * (t : ℂ))) * ((T.f t : ℝ) : ℂ)
        = starRingEnd ℂ (Complex.exp (-(z * (t : ℂ))) * ((T.f t : ℝ) : ℂ)) := by
      intro t
      have h1 : -(z * (t : ℂ)) = starRingEnd ℂ (-((starRingEnd ℂ z) * (t : ℂ))) := by
        rw [map_neg, map_mul]; simp
      rw [h1, map_mul, ← Complex.exp_conj]; simp
    rw [intervalIntegral.integral_of_le (le_of_lt T.x₀_pos),
      intervalIntegral.integral_of_le (le_of_lt T.x₀_pos),
      MeasureTheory.integral_congr_ae (Filter.Eventually.of_forall hpt),
      ← integral_conj]
  have hFc_even : ∀ m : ℝ, (T.Fc ((((-m : ℝ)) : ℂ) * Complex.I)).re
      = (T.Fc ((m : ℂ) * Complex.I)).re := by
    intro m
    have h1 : ((((-m : ℝ)) : ℂ)) * Complex.I = starRingEnd ℂ ((m : ℂ) * Complex.I) := by
      rw [map_mul, Complex.conj_I, Complex.conj_ofReal]; push_cast; ring
    rw [h1, hFc_conj]; simp
  -- ============ range / window / divisor helpers ============
  have hrange : ∀ γ : ℝ, |γ| ≤ 3 * L →
      |(((β : ℂ) + (γ : ℂ) * Complex.I).re - 1)| ≤ Real.sqrt (Real.log Lq) / Lq ∧
      |(((β : ℂ) + (γ : ℂ) * Complex.I).im)| ≤ 10 * Lq ∧
      1 - Real.sqrt (Real.log Lq) / Lq ≤ ((β : ℂ) + (γ : ℂ) * Complex.I).re := by
    intro γ hγ
    have hre : ((β : ℂ) + (γ : ℂ) * Complex.I).re = β := by simp
    have him : ((β : ℂ) + (γ : ℂ) * Complex.I).im = γ := by simp
    refine ⟨?_, ?_, ?_⟩
    · rw [hre, hβ1]; exact hdivle
    · rw [him]; linarith [hγ, hLle]
    · rw [hre, hβ]; linarith [hdivle]
  have hwin_sh : ∀ (ρ : ℂ) (τ lam m : ℝ), 1 - ρ.re = lam / Lq → 0 ≤ lam → lam ≤ 6/7 →
      (τ - ρ.im) * Lq = m → |m| ≤ 4 →
      ‖(1:ℂ) + (τ : ℂ) * Complex.I - ρ‖ ≤ δ := by
    intro ρ τ lam m hre hlam0 hl67 hm hm4
    have h1 : (1:ℂ) + (τ : ℂ) * Complex.I - ρ
        = ((1 - ρ.re : ℝ) : ℂ) + ((τ - ρ.im : ℝ) : ℂ) * Complex.I := by
      apply Complex.ext <;>
        simp only [Complex.add_re, Complex.add_im, Complex.sub_re, Complex.sub_im,
          Complex.mul_re, Complex.mul_im, Complex.ofReal_re, Complex.ofReal_im,
          Complex.I_re, Complex.I_im, Complex.one_re, Complex.one_im, mul_zero, mul_one,
          zero_mul, zero_add, add_zero, sub_zero] <;>
        ring
    rw [h1]
    have hm' : τ - ρ.im = m / Lq := by
      rw [eq_div_iff hlogq.ne']; linarith [hm]
    have hnorm : ‖((1 - ρ.re : ℝ) : ℂ) + ((τ - ρ.im : ℝ) : ℂ) * Complex.I‖ ^ 2
        = (1 - ρ.re) ^ 2 + (τ - ρ.im) ^ 2 := by
      rw [Complex.sq_norm, Complex.normSq_add_mul_I]
    have hsq : (1 - ρ.re) ^ 2 + (τ - ρ.im) ^ 2 ≤ δ ^ 2 := by
      rw [hre, hm', div_pow, div_pow, ← add_div, div_le_iff₀ (by positivity : (0:ℝ) < Lq ^ 2)]
      have hkey : (25:ℝ) ≤ δ ^ 2 * Lq ^ 2 := by
        have h := pow_le_pow_left₀ (by norm_num : (0:ℝ) ≤ 5) hδ5 2
        nlinarith [h]
      have h1 : lam ^ 2 ≤ ((6:ℝ)/7) ^ 2 := pow_le_pow_left₀ hlam0 hl67 2
      have h2 : m ^ 2 ≤ (16:ℝ) := by
        have h := pow_le_pow_left₀ (abs_nonneg m) hm4 2
        rw [sq_abs] at h
        norm_num at h
        exact h
      nlinarith [hkey, h1, h2]
    have hs : ‖((1 - ρ.re : ℝ) : ℂ) + ((τ - ρ.im : ℝ) : ℂ) * Complex.I‖ ^ 2 ≤ δ ^ 2 := by
      rw [hnorm]; exact hsq
    have h3 : |‖((1 - ρ.re : ℝ) : ℂ) + ((τ - ρ.im : ℝ) : ℂ) * Complex.I‖| ≤ |δ| :=
      sq_le_sq.mp hs
    rwa [abs_of_nonneg (norm_nonneg _), abs_of_pos hδ0] at h3
  have hdiv_sh : ∀ (ψ : DirichletCharacter ℂ q) [NeZero ψ.conductor], ψ ≠ 1 → ∀ (ρ : ℂ) (τ : ℝ),
      Work.LinnikContract.zeroMult ψ ρ ≠ 0 → |τ| ≤ 3 * L →
      ‖(1:ℂ) + (τ : ℂ) * Complex.I - ρ‖ ≤ δ →
      (MeromorphicOn.divisor (DirichletCharacter.completedLFunction ψ.primitiveCharacter)
        (Metric.closedBall 0 (|τ| + 2))) ρ ≠ 0 := by
    intro ψ _instc hψ ρ τ hzm hτ hwin
    refine Work.ZeroFreeTables.OffAxis.divisor_ne_zero_of_zeroMult ψ hψ ?_ hzm
    rw [Metric.mem_closedBall, dist_zero_right]
    have him1 : |τ - ρ.im| ≤ δ := by
      have h := Complex.abs_im_le_norm ((1:ℂ) + (τ : ℂ) * Complex.I - ρ)
      have h' : (((1:ℂ) + (τ : ℂ) * Complex.I - ρ).im) = τ - ρ.im := by simp
      rw [h'] at h; exact le_trans h hwin
    have hlim : |ρ.im| ≤ |τ| + δ := by
      calc |ρ.im| = |τ - (τ - ρ.im)| := by ring_nf
        _ ≤ |τ| + |τ - ρ.im| := abs_sub _ _
        _ ≤ |τ| + δ := by linarith
    have hre : |ρ.re| ≤ 1 := abs_re_le_one_of_zeroMult hψ hzm
    have h1 : ‖ρ‖ ≤ |ρ.re| + |ρ.im| := by
      have hρ : ρ = (ρ.re : ℂ) + (ρ.im : ℂ) * Complex.I := by
        apply Complex.ext <;> simp
      calc ‖ρ‖ = ‖(ρ.re : ℂ) + (ρ.im : ℂ) * Complex.I‖ := congrArg Norm.norm hρ
        _ ≤ ‖(ρ.re : ℂ)‖ + ‖(ρ.im : ℂ) * Complex.I‖ := norm_add_le _ _
        _ = |ρ.re| + |ρ.im| := by
            simp only [Complex.norm_real, Real.norm_eq_abs, norm_mul, Complex.norm_I, mul_one]
    have h2 : |ρ.re| + |ρ.im| ≤ 1 + (|τ| + δ) := by linarith
    have h3 : (1:ℝ) + (|τ| + δ) ≤ |τ| + 2 := by linarith [hδ1]
    exact le_trans (le_trans h1 h2) h3
  -- ============ conductor instances and non-principality ============
  haveI hc1 : NeZero χ₁.conductor := ⟨χ₁.conductor_ne_zero⟩
  haveI hc2 : NeZero χ₂.conductor := ⟨χ₂.conductor_ne_zero⟩
  haveI hc3 : NeZero χ₃.conductor := ⟨χ₃.conductor_ne_zero⟩
  haveI hc12 : NeZero (χ₁ * χ₂).conductor := ⟨(χ₁ * χ₂).conductor_ne_zero⟩
  haveI hc1i2 : NeZero (χ₁ * χ₂⁻¹).conductor := ⟨(χ₁ * χ₂⁻¹).conductor_ne_zero⟩
  haveI hc13 : NeZero (χ₁ * χ₃).conductor := ⟨(χ₁ * χ₃).conductor_ne_zero⟩
  haveI hc1i3 : NeZero (χ₁ * χ₃⁻¹).conductor := ⟨(χ₁ * χ₃⁻¹).conductor_ne_zero⟩
  haveI hc23 : NeZero (χ₂ * χ₃).conductor := ⟨(χ₂ * χ₃).conductor_ne_zero⟩
  haveI hc2i3 : NeZero (χ₂ * χ₃⁻¹).conductor := ⟨(χ₂ * χ₃⁻¹).conductor_ne_zero⟩
  haveI hc123 : NeZero (χ₁ * χ₂ * χ₃).conductor := ⟨(χ₁ * χ₂ * χ₃).conductor_ne_zero⟩
  haveI hc12i3 : NeZero (χ₁ * χ₂ * χ₃⁻¹).conductor := ⟨(χ₁ * χ₂ * χ₃⁻¹).conductor_ne_zero⟩
  haveI hc1i23 : NeZero (χ₁ * χ₂⁻¹ * χ₃).conductor := ⟨(χ₁ * χ₂⁻¹ * χ₃).conductor_ne_zero⟩
  haveI hc123i : NeZero (χ₁⁻¹ * χ₂ * χ₃).conductor := ⟨(χ₁⁻¹ * χ₂ * χ₃).conductor_ne_zero⟩
  obtain ⟨hp12, hp1i2, hp13, hp1i3, hp23, hp2i3⟩ :=
    Work.ZeroFreeTables.OffAxis.pairProducts_ne_one h21 h2i h31 h3i h32 h3ii
  have eqinv : ∀ a b : DirichletCharacter ℂ q, a * b = 1 → a = b⁻¹ := by
    intro a b h
    calc a = a * 1 := (mul_one a).symm
      _ = a * (b * b⁻¹) := by rw [mul_inv_cancel]
      _ = (a * b) * b⁻¹ := (mul_assoc a b b⁻¹).symm
      _ = 1 * b⁻¹ := by rw [h]
      _ = b⁻¹ := one_mul b⁻¹
  have hχ23 : χ₂ * χ₃ = χ₁⁻¹ :=
    eqinv (χ₂ * χ₃) χ₁ (by rw [mul_comm (χ₂ * χ₃) χ₁, ← mul_assoc]; exact hprod)
  have hχ13 : χ₁ * χ₃ = χ₂⁻¹ :=
    eqinv (χ₁ * χ₃) χ₂ (by rw [mul_assoc, mul_comm χ₃ χ₂, ← mul_assoc]; exact hprod)
  have hχ12 : χ₁ * χ₂ = χ₃⁻¹ := eqinv (χ₁ * χ₂) χ₃ hprod
  -- ============ generic self bound ============
  have hself : ∀ (ψ : DirichletCharacter ℂ q) [NeZero ψ.conductor], ψ ≠ 1 →
      ∀ (γ : ℝ), |γ| ≤ 3 * L →
      Work.ZeroFreeTables.Ksum q T.f Lq ((β : ℂ) + (γ : ℂ) * Complex.I) ψ ≤ a := by
    intro ψ _instc hψ γ hγ
    obtain ⟨hr1, hr2, hr3⟩ := hrange γ hγ
    have h := hA (q := q) hqA ψ hψ hr1 hr2 hr3 (hL52 q hqL52 ψ hψ)
      (Work.ZeroFreeTables.OffAxis.IsRectMin.window_left (q := q) hR hlogq hψ
        (by rw [show (((β : ℂ) + (γ : ℂ) * Complex.I).im) = γ from by simp]
            linarith [hγ, hδ1, hL1])
        (by rw [show (((β : ℂ) + (γ : ℂ) * Complex.I).re) = β from by simp]; exact hρ1re.symm))
    rw [ha]; exact h
  -- ============ the single-zero bound at the same imaginary part ============
  have hsingle : ∀ (ψ : DirichletCharacter ℂ q) [NeZero ψ.conductor], ψ ≠ 1 →
      ∀ (γ : ℝ), |γ| ≤ 3 * L → ∀ (ρ : ℂ) (lam : ℝ),
      ρ.im = γ → lam = Work.LinnikContract.lamOf q ρ → lam ≤ 6/7 →
      Work.LinnikContract.zeroMult ψ ρ ≠ 0 →
      Work.ZeroFreeTables.Ksum q T.f Lq ((β : ℂ) + (γ : ℂ) * Complex.I) ψ
        ≤ -Lq * T.F (lam - lam₁) + a := by
    intro ψ _instc hψ γ hγ ρ lam hργ hlam hlam67 hzm
    obtain ⟨hr1, hr2, hr3⟩ := hrange γ hγ
    have hmem : ρ ∈ Metric.closedBall (0:ℂ) (|γ| + 2) := by
      have h := Work.ZeroFreeTables.mem_closedBall_of_absre_le_one_v2
        (abs_re_le_one_of_zeroMult hψ hzm)
      rwa [hργ] at h
    have hdiv : (MeromorphicOn.divisor (DirichletCharacter.completedLFunction ψ.primitiveCharacter)
        (Metric.closedBall 0 (|((β : ℂ) + (γ : ℂ) * Complex.I).im| + 2))) ρ ≠ 0 := by
      have him : (((β : ℂ) + (γ : ℂ) * Complex.I).im) = γ := by simp
      rw [him]
      exact Work.ZeroFreeTables.OffAxis.divisor_ne_zero_of_zeroMult ψ hψ hmem hzm
    have hwinρ : ‖(1:ℂ) + ((((β : ℂ) + (γ : ℂ) * Complex.I)).im : ℂ) * Complex.I - ρ‖ ≤ δ := by
      have him : (((β : ℂ) + (γ : ℂ) * Complex.I).im) = γ := by simp
      rw [him, ← hργ]
      have h1 : (1:ℂ) + (ρ.im : ℂ) * Complex.I - ρ = ((1 - ρ.re : ℝ) : ℂ) := by
        apply Complex.ext <;> simp
      rw [h1, Complex.norm_real, Real.norm_eq_abs]
      have hval : 1 - ρ.re = lam / Lq := by
        have hl : lam = (1 - ρ.re) * Lq := by rw [hlam, Work.LinnikContract.lamOf, ← hLqdef]
        rw [eq_div_iff hlogq.ne', hl]
      rw [abs_of_nonneg (by rw [hval]; exact div_nonneg (by rw [hlam]; exact lamOf_nonneg_of_zeroMult hzm) hlogq.le),
        hval]
      exact le_trans (div_le_div_of_nonneg_right hlam67 hlogq.le) hδinv
    have h := hS (q := q) hqS ψ hψ hr1 hr2 hr3 (hL52 q hqL52 ψ hψ) hdiv hwinρ
      (Work.ZeroFreeTables.OffAxis.IsRectMin.window_left (q := q) hR hlogq hψ
        (by rw [show (((β : ℂ) + (γ : ℂ) * Complex.I).im) = γ from by simp]
            linarith [hγ, hδ1, hL1])
        (by rw [show (((β : ℂ) + (γ : ℂ) * Complex.I).re) = β from by simp]; exact hρ1re.symm))
    have hint : (∫ t in (0:ℝ)..T.x₀,
          Complex.exp (-(((((β : ℂ) + (γ : ℂ) * Complex.I)) - ρ) * (Lq : ℂ) * (t:ℂ))) *
            ((T.f t : ℝ) : ℂ)).re = T.F (lam - lam₁) := by
      rw [← T.Fc_spec]
      rw [sub_mul_log_eq (q := q) (β := β) (γ := γ) (lam := lam) (lam₁ := lam₁) (ρ := ρ)
        hlogq.ne' hβ ?_ hργ]
      · rfl
      · rw [hlam, Work.LinnikContract.lamOf, ← hLqdef]; field_simp; ring
    rw [hint] at h
    rw [ha]; exact h
  -- ============ the shifted single-zero (credit) bound ============
  have hcred : ∀ (ψ : DirichletCharacter ℂ q) [NeZero ψ.conductor], ψ ≠ 1 →
      ∀ (ρ : ℂ) (τ m : ℝ), ρ.re = β → |τ| ≤ 3 * L → (τ - ρ.im) * Lq = m →
      (MeromorphicOn.divisor (DirichletCharacter.completedLFunction ψ.primitiveCharacter)
          (Metric.closedBall 0 (|τ| + 2))) ρ ≠ 0 →
      ‖(1:ℂ) + (τ : ℂ) * Complex.I - ρ‖ ≤ δ →
      Work.ZeroFreeTables.Ksum q T.f Lq ((β : ℂ) + (τ : ℂ) * Complex.I) ψ
        ≤ -Lq * (T.Fc (((m : ℝ) : ℂ) * Complex.I)).re + a := by
    intro ψ _instc hψ ρ τ m hρre hτ hm hdiv hwinρ
    obtain ⟨hr1, hr2, hr3⟩ := hrange τ hτ
    have hsub : (β : ℂ) + (τ : ℂ) * Complex.I - ρ = ((τ - ρ.im : ℝ) : ℂ) * Complex.I := by
      have hone : (β : ℂ) + (τ : ℂ) * Complex.I - ρ
          = (((β - ρ.re : ℝ)) : ℂ) + (((τ - ρ.im : ℝ)) : ℂ) * Complex.I := by
        apply Complex.ext <;>
          simp only [Complex.add_re, Complex.add_im, Complex.sub_re, Complex.sub_im,
            Complex.mul_re, Complex.mul_im, Complex.ofReal_re, Complex.ofReal_im,
            Complex.I_re, Complex.I_im, mul_zero, mul_one, zero_mul, zero_add, add_zero,
            sub_zero] <;> ring
      rw [hone, hρre, sub_self, Complex.ofReal_zero, zero_add]
    have hz : (((β : ℂ) + (τ : ℂ) * Complex.I) - ρ) * (Lq : ℂ) = ((m : ℝ) : ℂ) * Complex.I := by
      rw [hsub, mul_assoc, mul_comm Complex.I (Lq : ℂ), ← mul_assoc, ← Complex.ofReal_mul, hm]
    have hdivs : (MeromorphicOn.divisor (DirichletCharacter.completedLFunction ψ.primitiveCharacter)
        (Metric.closedBall 0 (|(((β : ℂ) + (τ : ℂ) * Complex.I)).im| + 2))) ρ ≠ 0 := by
      rwa [show (((β : ℂ) + (τ : ℂ) * Complex.I).im) = τ from by simp]
    have hwins : ‖(1:ℂ) + ((((β : ℂ) + (τ : ℂ) * Complex.I)).im : ℂ) * Complex.I - ρ‖ ≤ δ := by
      rwa [show (((β : ℂ) + (τ : ℂ) * Complex.I).im) = τ from by simp]
    have h := hS (q := q) (s := (β : ℂ) + (τ : ℂ) * Complex.I) hqS ψ hψ hr1 hr2 hr3
      (hL52 q hqL52 ψ hψ) hdivs hwins
      (Work.ZeroFreeTables.OffAxis.IsRectMin.window_left (q := q) hR hlogq hψ
        (by rw [show (((β : ℂ) + (τ : ℂ) * Complex.I).im) = τ from by simp]
            linarith [hτ, hδ1, hL1])
        (by rw [show (((β : ℂ) + (τ : ℂ) * Complex.I).re) = β from by simp]; exact hρ1re.symm))
    rw [hz] at h
    have hconv : (∫ t in (0:ℝ)..T.x₀, Complex.exp (-((((m : ℝ) : ℂ) * Complex.I) * (t : ℂ)))
        * ((T.f t : ℝ) : ℂ)).re = (T.Fc (((m : ℝ) : ℂ) * Complex.I)).re := by
      rw [T.Fc_spec]
    rw [hconv] at h
    rw [ha]; exact h
  -- ============ the shifted two-zero (double credit) bound ============
  have hcred2 : ∀ (ψ : DirichletCharacter ℂ q) [NeZero ψ.conductor], ψ ≠ 1 →
      ∀ (ρ ρ' : ℂ) (τ m m' : ℝ), ρ.re = β → ρ'.re = β → ρ ≠ ρ' → |τ| ≤ 3 * L →
      (τ - ρ.im) * Lq = m → (τ - ρ'.im) * Lq = m' →
      (MeromorphicOn.divisor (DirichletCharacter.completedLFunction ψ.primitiveCharacter)
          (Metric.closedBall 0 (|τ| + 2))) ρ ≠ 0 →
      (MeromorphicOn.divisor (DirichletCharacter.completedLFunction ψ.primitiveCharacter)
          (Metric.closedBall 0 (|τ| + 2))) ρ' ≠ 0 →
      ‖(1:ℂ) + (τ : ℂ) * Complex.I - ρ‖ ≤ δ →
      ‖(1:ℂ) + (τ : ℂ) * Complex.I - ρ'‖ ≤ δ →
      Work.ZeroFreeTables.Ksum q T.f Lq ((β : ℂ) + (τ : ℂ) * Complex.I) ψ
        ≤ -Lq * (T.Fc (((m : ℝ) : ℂ) * Complex.I)).re
          - Lq * (T.Fc (((m' : ℝ) : ℂ) * Complex.I)).re + a := by
    intro ψ _instc hψ ρ ρ' τ m m' hρre hρ're hne hτ hm hm' hdiv hdiv' hwin hwin'
    obtain ⟨hr1, hr2, hr3⟩ := hrange τ hτ
    have hsre1 : ρ.re ≤ ((β : ℂ) + (τ : ℂ) * Complex.I).re := by
      rw [show (((β : ℂ) + (τ : ℂ) * Complex.I).re) = β from by simp]
      exact le_of_eq hρre
    have hsre2 : ρ'.re ≤ ((β : ℂ) + (τ : ℂ) * Complex.I).re := by
      rw [show (((β : ℂ) + (τ : ℂ) * Complex.I).re) = β from by simp]
      exact le_of_eq hρ're
    have hdivs : (MeromorphicOn.divisor (DirichletCharacter.completedLFunction ψ.primitiveCharacter)
        (Metric.closedBall 0 (|(((β : ℂ) + (τ : ℂ) * Complex.I)).im| + 2))) ρ ≠ 0 := by
      rwa [show (((β : ℂ) + (τ : ℂ) * Complex.I).im) = τ from by simp]
    have hdivs' : (MeromorphicOn.divisor (DirichletCharacter.completedLFunction ψ.primitiveCharacter)
        (Metric.closedBall 0 (|(((β : ℂ) + (τ : ℂ) * Complex.I)).im| + 2))) ρ' ≠ 0 := by
      rwa [show (((β : ℂ) + (τ : ℂ) * Complex.I).im) = τ from by simp]
    have hwins : ‖(1:ℂ) + ((((β : ℂ) + (τ : ℂ) * Complex.I)).im : ℂ) * Complex.I - ρ‖ ≤ δ := by
      rwa [show (((β : ℂ) + (τ : ℂ) * Complex.I).im) = τ from by simp]
    have hwins' : ‖(1:ℂ) + ((((β : ℂ) + (τ : ℂ) * Complex.I)).im : ℂ) * Complex.I - ρ'‖ ≤ δ := by
      rwa [show (((β : ℂ) + (τ : ℂ) * Complex.I).im) = τ from by simp]
    have h := hT6 (q := q) hqT6 ψ hψ hr1 hr2 hr3 (hL52 q hqL52 ψ hψ)
      hdivs hdivs' hne hwins hwins' hsre1 hsre2
      (Work.ZeroFreeTables.OffAxis.IsRectMin.window_left (q := q) hR hlogq hψ
        (by rw [show (((β : ℂ) + (τ : ℂ) * Complex.I).im) = τ from by simp]
            linarith [hτ, hδ1, hL1])
        (by rw [show (((β : ℂ) + (τ : ℂ) * Complex.I).re) = β from by simp]; exact hρ1re.symm))
    have hz : (((β : ℂ) + (τ : ℂ) * Complex.I) - ρ) * (Lq : ℂ) = ((m : ℝ) : ℂ) * Complex.I := by
      have hsub : (β : ℂ) + (τ : ℂ) * Complex.I - ρ = ((τ - ρ.im : ℝ) : ℂ) * Complex.I := by
        have hone : (β : ℂ) + (τ : ℂ) * Complex.I - ρ
            = (((β - ρ.re : ℝ)) : ℂ) + (((τ - ρ.im : ℝ)) : ℂ) * Complex.I := by
          apply Complex.ext <;>
            simp only [Complex.add_re, Complex.add_im, Complex.sub_re, Complex.sub_im,
              Complex.mul_re, Complex.mul_im, Complex.ofReal_re, Complex.ofReal_im,
              Complex.I_re, Complex.I_im, mul_zero, mul_one, zero_mul, zero_add, add_zero,
              sub_zero] <;> ring
        rw [hone, hρre, sub_self, Complex.ofReal_zero, zero_add]
      rw [hsub, mul_assoc, mul_comm Complex.I (Lq : ℂ), ← mul_assoc, ← Complex.ofReal_mul, hm]
    have hz' : (((β : ℂ) + (τ : ℂ) * Complex.I) - ρ') * (Lq : ℂ) = ((m' : ℝ) : ℂ) * Complex.I := by
      have hsub : (β : ℂ) + (τ : ℂ) * Complex.I - ρ' = ((τ - ρ'.im : ℝ) : ℂ) * Complex.I := by
        have hone : (β : ℂ) + (τ : ℂ) * Complex.I - ρ'
            = (((β - ρ'.re : ℝ)) : ℂ) + (((τ - ρ'.im : ℝ)) : ℂ) * Complex.I := by
          apply Complex.ext <;>
            simp only [Complex.add_re, Complex.add_im, Complex.sub_re, Complex.sub_im,
              Complex.mul_re, Complex.mul_im, Complex.ofReal_re, Complex.ofReal_im,
              Complex.I_re, Complex.I_im, mul_zero, mul_one, zero_mul, zero_add, add_zero,
              sub_zero] <;> ring
        rw [hone, hρ're, sub_self, Complex.ofReal_zero, zero_add]
      rw [hsub, mul_assoc, mul_comm Complex.I (Lq : ℂ), ← mul_assoc, ← Complex.ofReal_mul, hm']
    rw [hz, hz'] at h
    have hconv : (∫ t in (0:ℝ)..T.x₀, Complex.exp (-((((m : ℝ) : ℂ) * Complex.I) * (t : ℂ)))
        * ((T.f t : ℝ) : ℂ)).re = (T.Fc (((m : ℝ) : ℂ) * Complex.I)).re := by
      rw [T.Fc_spec]
    have hconv' : (∫ t in (0:ℝ)..T.x₀, Complex.exp (-((((m' : ℝ) : ℂ) * Complex.I) * (t : ℂ)))
        * ((T.f t : ℝ) : ℂ)).re = (T.Fc (((m' : ℝ) : ℂ) * Complex.I)).re := by
      rw [T.Fc_spec]
    rw [hconv, hconv'] at h
    rw [ha]; exact h
  set μ₀ : ℝ := (γ₁ + γ₂ + γ₃) * Lq with hμ₀
  set μ₁ : ℝ := (-γ₁ + γ₂ + γ₃) * Lq with hμ₁
  set μ₂ : ℝ := (γ₁ - γ₂ + γ₃) * Lq with hμ₂
  set μ₃ : ℝ := (γ₁ + γ₂ - γ₃) * Lq with hμ₃
  set crd₀ : ℝ := (if |μ₀| ≤ 4 then Lq * (T.Fc ((μ₀ : ℂ) * Complex.I)).re else 0) with hcrd₀
  set crd₁ : ℝ := (if χ₂ * χ₃ = χ₁ ∧ |μ₁| ≤ 4 then Lq * (T.Fc ((μ₁ : ℂ) * Complex.I)).re else 0) with hcrd₁
  set crd₂ : ℝ := (if χ₂ * χ₃⁻¹ = χ₁ ∧ |μ₂| ≤ 4 then Lq * (T.Fc ((μ₂ : ℂ) * Complex.I)).re else 0) with hcrd₂
  set crd₃ : ℝ := (if χ₂ * χ₃⁻¹ = χ₁⁻¹ ∧ |μ₃| ≤ 4 then Lq * (T.Fc ((μ₃ : ℂ) * Complex.I)).re else 0) with hcrd₃
  -- ============ the principal-character bound at a shifted point ============
  have htriple : ∀ (τ : ℝ), |τ| ≤ 3 * L →
      Work.ZeroFreeTables.Ksum q T.f Lq ((β : ℂ) + (τ : ℂ) * Complex.I) 1
        ≤ Lq * (T.Fc (((-lam₁ : ℝ) : ℂ) + ((τ * Lq : ℝ) : ℂ) * Complex.I)).re
          + T.f 0 * ε' * Lq := by
    intro τ hτ
    have hb := hP (q := q) hqP (β := β) (γ := τ) (by rw [hβ1]; exact hdivle)
      (by linarith [hτ, hLle])
    have harg : (((β : ℂ) + (τ : ℂ) * Complex.I) - 1) * (Lq : ℂ)
        = ((-lam₁ : ℝ) : ℂ) + ((τ * Lq : ℝ) : ℂ) * Complex.I := by
      have h1 : (β : ℂ) + (τ : ℂ) * Complex.I - 1
          = ((β - 1 : ℝ) : ℂ) + (τ : ℂ) * Complex.I := by push_cast; ring
      rw [h1]
      have h2 : ((((β - 1 : ℝ) : ℂ) + (τ : ℂ) * Complex.I) * (Lq : ℂ))
          = (((β - 1) * Lq : ℝ) : ℂ) + ((τ * Lq : ℝ) : ℂ) * Complex.I := by
        apply Complex.ext <;>
          simp only [Complex.add_re, Complex.add_im, Complex.mul_re, Complex.mul_im,
            Complex.ofReal_re, Complex.ofReal_im, Complex.I_re, Complex.I_im, mul_zero,
            mul_one, zero_mul, zero_add, add_zero, sub_zero] <;> ring
      rw [h2]
      have h3 : (β - 1) * Lq = -lam₁ := by
        rw [hβ, show (1:ℝ) - lam₁ / Lq - 1 = -(lam₁ / Lq) by ring, neg_mul, neg_inj]
        exact div_mul_cancel₀ lam₁ hlogq.ne'
      rw [h3]
    rw [harg] at hb
    have hconv : (∫ t in (0:ℝ)..T.x₀,
        Complex.exp (-((((-lam₁ : ℝ) : ℂ) + ((τ * Lq : ℝ) : ℂ) * Complex.I) * (t : ℂ)))
        * ((T.f t : ℝ) : ℂ)).re
        = (T.Fc (((-lam₁ : ℝ) : ℂ) + ((τ * Lq : ℝ) : ℂ) * Complex.I)).re := by
      rw [T.Fc_spec]
    rw [hconv] at hb
    simpa only [Work.ZeroFreeTables.Ksum] using hb
  -- ============ the leading principal term at `β` ============
  have hbP0 : Work.ZeroFreeTables.Ksum q T.f Lq (β : ℂ) 1
      ≤ Lq * T.F (-lam₁) + T.f 0 * ε' * Lq := by
    have hb := hP (q := q) hqP (β := β) (γ := 0) (by rw [hβ1]; exact hdivle)
      (by rw [abs_zero]; linarith [hlogq])
    rw [show ((β : ℂ) + ((0:ℝ) : ℂ) * Complex.I) = (β : ℂ) from by simp] at hb
    have harg : ((β : ℂ) - 1) * (Lq : ℂ) = ((-lam₁ : ℝ) : ℂ) := by
      have h1 : (β : ℂ) - 1 = ((-(lam₁ / Lq) : ℝ) : ℂ) := by
        rw [hβcast]
        rw [show (((1 - lam₁ / Lq : ℝ)) : ℂ) - 1 = (((1 - lam₁ / Lq - 1 : ℝ)) : ℂ) by
          push_cast; ring]
        congr 1
        ring
      rw [h1, ← Complex.ofReal_mul]
      congr 1
      rw [neg_mul, neg_inj]
      exact div_mul_cancel₀ lam₁ hlogq.ne'
    rw [harg] at hb
    have hconv : (∫ t in (0:ℝ)..T.x₀,
        Complex.exp (-((((-lam₁ : ℝ) : ℂ)) * (t : ℂ))) * ((T.f t : ℝ) : ℂ)).re
        = T.F (-lam₁) := by
      rw [show T.F (-lam₁) = (T.Fc (((-lam₁ : ℝ) : ℂ))).re from rfl, T.Fc_spec]
    rw [hconv] at hb
    simpa only [Work.ZeroFreeTables.Ksum] using hb
  -- ============ the three single terms ============
  have hbS1 : Work.ZeroFreeTables.Ksum q T.f Lq ((β : ℂ) + (γ₁ : ℂ) * Complex.I) χ₁
      ≤ -Lq * T.F 0 + a := by
    have h := hsingle χ₁ hR.1.1 γ₁ (by linarith [hγ1L, hL1]) ρ₁ lam₁ hγ₁.symm hlam₁ hl16
      hR.1.2.1
    simpa using h
  have hbS2 : Work.ZeroFreeTables.Ksum q T.f Lq ((β : ℂ) + (γ₂ : ℂ) * Complex.I) χ₂
      ≤ -Lq * T.F (lam₂ - lam₁) + a :=
    hsingle χ₂ hZ2.1 γ₂ (by linarith [hγ2L, hL1]) ρ₂ lam₂ hγ₂.symm hlam₂ hl26 hZ2.2.1
  have hbS3 : Work.ZeroFreeTables.Ksum q T.f Lq ((β : ℂ) + (γ₃ : ℂ) * Complex.I) χ₃
      ≤ -Lq * T.F (lam₃ - lam₁) + a :=
    hsingle χ₃ hZ3.1 γ₃ (by linarith [hγ3L, hL1]) ρ₃ lam₃ hγ₃.symm hlam₃ hlam3 hZ3.2.1
  -- ============ the four generic pairs ============
  have hbP12 : Work.ZeroFreeTables.Ksum q T.f Lq
        ((β : ℂ) + ((γ₁ : ℂ) + (γ₂ : ℂ)) * Complex.I) (χ₁ * χ₂) ≤ a := by
    have hb := hself (χ₁ * χ₂) hp12 (γ₁ + γ₂) (by linarith [abs_add_le γ₁ γ₂, hγ1L, hγ2L])
    simpa only [Complex.ofReal_add] using hb
  have hbP1i2 : Work.ZeroFreeTables.Ksum q T.f Lq
        ((β : ℂ) + ((γ₁ : ℂ) - (γ₂ : ℂ)) * Complex.I) (χ₁ * χ₂⁻¹) ≤ a := by
    have hb := hself (χ₁ * χ₂⁻¹) hp1i2 (γ₁ - γ₂) (by
      have h := abs_add_le γ₁ (-γ₂)
      rw [abs_neg] at h
      rw [sub_eq_add_neg]
      linarith [h, hγ1L, hγ2L])
    simpa only [Complex.ofReal_sub] using hb
  have hbP13 : Work.ZeroFreeTables.Ksum q T.f Lq
        ((β : ℂ) + ((γ₁ : ℂ) + (γ₃ : ℂ)) * Complex.I) (χ₁ * χ₃) ≤ a := by
    have hb := hself (χ₁ * χ₃) hp13 (γ₁ + γ₃) (by linarith [abs_add_le γ₁ γ₃, hγ1L, hγ3L])
    simpa only [Complex.ofReal_add] using hb
  have hbP1i3 : Work.ZeroFreeTables.Ksum q T.f Lq
        ((β : ℂ) + ((γ₁ : ℂ) - (γ₃ : ℂ)) * Complex.I) (χ₁ * χ₃⁻¹) ≤ a := by
    have hb := hself (χ₁ * χ₃⁻¹) hp1i3 (γ₁ - γ₃) (by
      have h := abs_add_le γ₁ (-γ₃)
      rw [abs_neg] at h
      rw [sub_eq_add_neg]
      linarith [h, hγ1L, hγ3L])
    simpa only [Complex.ofReal_sub] using hb
  -- ============ the pair `χ₂χ₃` (credits `crd₀`,`crd₁`) ============
  have hbP23 : Work.ZeroFreeTables.Ksum q T.f Lq
        ((β : ℂ) + ((γ₂ : ℂ) + (γ₃ : ℂ)) * Complex.I) (χ₂ * χ₃)
      ≤ a - crd₀ - crd₁ := by
    have hτ : |γ₂ + γ₃| ≤ 3 * L := by linarith [abs_add_le γ₂ γ₃, hγ2L, hγ3L]
    have hm0 : (γ₂ + γ₃ - (starRingEnd ℂ ρ₁).im) * Lq = μ₀ := by
      have hc : (starRingEnd ℂ ρ₁).im = -γ₁ := by rw [Complex.conj_im, ← hγ₁]
      rw [hc, show (γ₂ + γ₃ - -γ₁) * Lq = (γ₁ + γ₂ + γ₃) * Lq by ring, ← hμ₀]
    have hm1 : (γ₂ + γ₃ - ρ₁.im) * Lq = μ₁ := by
      have hc : ρ₁.im = γ₁ := by rw [← hγ₁]
      rw [hc, show (γ₂ + γ₃ - γ₁) * Lq = (-γ₁ + γ₂ + γ₃) * Lq by ring, ← hμ₁]
    have hzm0 : Work.LinnikContract.zeroMult (χ₂ * χ₃) (starRingEnd ℂ ρ₁) ≠ 0 := by
      rw [hχ23, Work.A7.zeroMult_conj_inv]; exact hR.1.2.1
    have hne : (starRingEnd ℂ ρ₁) ≠ ρ₁ := by
      intro hh
      apply hg1
      have h2 : (starRingEnd ℂ ρ₁).im = ρ₁.im := congrArg Complex.im hh
      rw [Complex.conj_im] at h2
      linarith
    by_cases h40 : |μ₀| ≤ 4
    · have hwin0 : ‖(1:ℂ) + ((γ₂ + γ₃ : ℝ) : ℂ) * Complex.I - (starRingEnd ℂ ρ₁)‖ ≤ δ :=
        hwin_sh (starRingEnd ℂ ρ₁) (γ₂ + γ₃) lam₁ μ₀ hconj1real hl1nn hl16 hm0 h40
      by_cases h41 : χ₂ * χ₃ = χ₁ ∧ |μ₁| ≤ 4
      · have hwin1 : ‖(1:ℂ) + ((γ₂ + γ₃ : ℝ) : ℂ) * Complex.I - ρ₁‖ ≤ δ :=
          hwin_sh ρ₁ (γ₂ + γ₃) lam₁ μ₁ hρ1real hl1nn hl16 hm1 h41.2
        have hzm1 : Work.LinnikContract.zeroMult (χ₂ * χ₃) ρ₁ ≠ 0 := by
          rw [h41.1]; exact hR.1.2.1
        have hb := hcred2 (χ₂ * χ₃) hp23 (starRingEnd ℂ ρ₁) ρ₁ (γ₂ + γ₃) μ₀ μ₁
          (by rw [Complex.conj_re]; exact hρ1re) hρ1re hne hτ hm0 hm1
          (hdiv_sh (χ₂ * χ₃) hp23 (starRingEnd ℂ ρ₁) (γ₂ + γ₃) hzm0 hτ hwin0)
          (hdiv_sh (χ₂ * χ₃) hp23 ρ₁ (γ₂ + γ₃) hzm1 hτ hwin1) hwin0 hwin1
        have hc0 : crd₀ = Lq * (T.Fc ((μ₀ : ℂ) * Complex.I)).re := by rw [hcrd₀, if_pos h40]
        have hc1 : crd₁ = Lq * (T.Fc ((μ₁ : ℂ) * Complex.I)).re := by rw [hcrd₁, if_pos h41]
        rw [hc0, hc1]
        simp only [Complex.ofReal_add] at hb
        linarith only [hb]
      · have hb := hcred (χ₂ * χ₃) hp23 (starRingEnd ℂ ρ₁) (γ₂ + γ₃) μ₀
          (by rw [Complex.conj_re]; exact hρ1re) hτ hm0
          (hdiv_sh (χ₂ * χ₃) hp23 (starRingEnd ℂ ρ₁) (γ₂ + γ₃) hzm0 hτ hwin0) hwin0
        have hc0 : crd₀ = Lq * (T.Fc ((μ₀ : ℂ) * Complex.I)).re := by rw [hcrd₀, if_pos h40]
        have hc1 : crd₁ = 0 := by rw [hcrd₁, if_neg h41]
        rw [hc0, hc1]
        simp only [Complex.ofReal_add] at hb
        linarith only [hb]
    · by_cases h41 : χ₂ * χ₃ = χ₁ ∧ |μ₁| ≤ 4
      · have hwin1 : ‖(1:ℂ) + ((γ₂ + γ₃ : ℝ) : ℂ) * Complex.I - ρ₁‖ ≤ δ :=
          hwin_sh ρ₁ (γ₂ + γ₃) lam₁ μ₁ hρ1real hl1nn hl16 hm1 h41.2
        have hzm1 : Work.LinnikContract.zeroMult (χ₂ * χ₃) ρ₁ ≠ 0 := by
          rw [h41.1]; exact hR.1.2.1
        have hb := hcred (χ₂ * χ₃) hp23 ρ₁ (γ₂ + γ₃) μ₁ hρ1re hτ hm1
          (hdiv_sh (χ₂ * χ₃) hp23 ρ₁ (γ₂ + γ₃) hzm1 hτ hwin1) hwin1
        have hc0 : crd₀ = 0 := by rw [hcrd₀, if_neg h40]
        have hc1 : crd₁ = Lq * (T.Fc ((μ₁ : ℂ) * Complex.I)).re := by rw [hcrd₁, if_pos h41]
        rw [hc0, hc1]
        simp only [Complex.ofReal_add] at hb
        linarith only [hb]
      · have hb := hself (χ₂ * χ₃) hp23 (γ₂ + γ₃) hτ
        have hc0 : crd₀ = 0 := by rw [hcrd₀, if_neg h40]
        have hc1 : crd₁ = 0 := by rw [hcrd₁, if_neg h41]
        rw [hc0, hc1]
        simp only [Complex.ofReal_add] at hb
        linarith only [hb]
  -- ============ the pair `χ₂χ₃⁻¹` (credits `crd₂`,`crd₃`) ============
  have hbP2i3 : Work.ZeroFreeTables.Ksum q T.f Lq
        ((β : ℂ) + ((γ₂ : ℂ) - (γ₃ : ℂ)) * Complex.I) (χ₂ * χ₃⁻¹)
      ≤ a - crd₂ - crd₃ := by
    have hτ : |γ₂ - γ₃| ≤ 3 * L := by
      have h := abs_add_le γ₂ (-γ₃)
      rw [abs_neg] at h
      rw [sub_eq_add_neg]
      linarith [h, hγ2L, hγ3L]
    have hm2 : (γ₂ - γ₃ - ρ₁.im) * Lq = -μ₂ := by
      have hc : ρ₁.im = γ₁ := by rw [← hγ₁]
      rw [hc, show (γ₂ - γ₃ - γ₁) * Lq = -((γ₁ - γ₂ + γ₃) * Lq) by ring, ← hμ₂]
    have hm3 : (γ₂ - γ₃ - (starRingEnd ℂ ρ₁).im) * Lq = μ₃ := by
      have hc : (starRingEnd ℂ ρ₁).im = -γ₁ := by rw [Complex.conj_im, ← hγ₁]
      rw [hc, show (γ₂ - γ₃ - -γ₁) * Lq = (γ₁ + γ₂ - γ₃) * Lq by ring, ← hμ₃]
    have hne : (starRingEnd ℂ ρ₁) ≠ ρ₁ := by
      intro hh
      apply hg1
      have h2 : (starRingEnd ℂ ρ₁).im = ρ₁.im := congrArg Complex.im hh
      rw [Complex.conj_im] at h2
      linarith
    by_cases h42 : χ₂ * χ₃⁻¹ = χ₁ ∧ |μ₂| ≤ 4
    · have hwin2 : ‖(1:ℂ) + ((γ₂ - γ₃ : ℝ) : ℂ) * Complex.I - ρ₁‖ ≤ δ :=
        hwin_sh ρ₁ (γ₂ - γ₃) lam₁ (-μ₂) hρ1real hl1nn hl16 hm2 (by rw [abs_neg]; exact h42.2)
      have hzm2 : Work.LinnikContract.zeroMult (χ₂ * χ₃⁻¹) ρ₁ ≠ 0 := by
        rw [h42.1]; exact hR.1.2.1
      by_cases h43 : χ₂ * χ₃⁻¹ = χ₁⁻¹ ∧ |μ₃| ≤ 4
      · have hwin3 : ‖(1:ℂ) + ((γ₂ - γ₃ : ℝ) : ℂ) * Complex.I - (starRingEnd ℂ ρ₁)‖ ≤ δ :=
          hwin_sh (starRingEnd ℂ ρ₁) (γ₂ - γ₃) lam₁ μ₃ hconj1real hl1nn hl16 hm3 h43.2
        have hzm3 : Work.LinnikContract.zeroMult (χ₂ * χ₃⁻¹) (starRingEnd ℂ ρ₁) ≠ 0 := by
          rw [h43.1, Work.A7.zeroMult_conj_inv]; exact hR.1.2.1
        have hb := hcred2 (χ₂ * χ₃⁻¹) hp2i3 ρ₁ (starRingEnd ℂ ρ₁) (γ₂ - γ₃) (-μ₂) μ₃
          hρ1re (by rw [Complex.conj_re]; exact hρ1re) (Ne.symm hne) hτ hm2 hm3
          (hdiv_sh (χ₂ * χ₃⁻¹) hp2i3 ρ₁ (γ₂ - γ₃) hzm2 hτ hwin2)
          (hdiv_sh (χ₂ * χ₃⁻¹) hp2i3 (starRingEnd ℂ ρ₁) (γ₂ - γ₃) hzm3 hτ hwin3) hwin2 hwin3
        have hc2 : crd₂ = Lq * (T.Fc ((μ₂ : ℂ) * Complex.I)).re := by rw [hcrd₂, if_pos h42]
        have hc3 : crd₃ = Lq * (T.Fc ((μ₃ : ℂ) * Complex.I)).re := by rw [hcrd₃, if_pos h43]
        rw [hFc_even μ₂] at hb
        rw [hc2, hc3]
        simp only [Complex.ofReal_add, Complex.ofReal_sub] at hb
        linarith only [hb]
      · have hb := hcred (χ₂ * χ₃⁻¹) hp2i3 ρ₁ (γ₂ - γ₃) (-μ₂) hρ1re hτ hm2
          (hdiv_sh (χ₂ * χ₃⁻¹) hp2i3 ρ₁ (γ₂ - γ₃) hzm2 hτ hwin2) hwin2
        have hc2 : crd₂ = Lq * (T.Fc ((μ₂ : ℂ) * Complex.I)).re := by rw [hcrd₂, if_pos h42]
        have hc3 : crd₃ = 0 := by rw [hcrd₃, if_neg h43]
        rw [hFc_even μ₂] at hb
        rw [hc2, hc3]
        simp only [Complex.ofReal_add, Complex.ofReal_sub] at hb
        linarith only [hb]
    · by_cases h43 : χ₂ * χ₃⁻¹ = χ₁⁻¹ ∧ |μ₃| ≤ 4
      · have hwin3 : ‖(1:ℂ) + ((γ₂ - γ₃ : ℝ) : ℂ) * Complex.I - (starRingEnd ℂ ρ₁)‖ ≤ δ :=
          hwin_sh (starRingEnd ℂ ρ₁) (γ₂ - γ₃) lam₁ μ₃ hconj1real hl1nn hl16 hm3 h43.2
        have hzm3 : Work.LinnikContract.zeroMult (χ₂ * χ₃⁻¹) (starRingEnd ℂ ρ₁) ≠ 0 := by
          rw [h43.1, Work.A7.zeroMult_conj_inv]; exact hR.1.2.1
        have hb := hcred (χ₂ * χ₃⁻¹) hp2i3 (starRingEnd ℂ ρ₁) (γ₂ - γ₃) μ₃
          (by rw [Complex.conj_re]; exact hρ1re) hτ hm3
          (hdiv_sh (χ₂ * χ₃⁻¹) hp2i3 (starRingEnd ℂ ρ₁) (γ₂ - γ₃) hzm3 hτ hwin3) hwin3
        have hc2 : crd₂ = 0 := by rw [hcrd₂, if_neg h42]
        have hc3 : crd₃ = Lq * (T.Fc ((μ₃ : ℂ) * Complex.I)).re := by rw [hcrd₃, if_pos h43]
        rw [hc2, hc3]
        simp only [Complex.ofReal_add, Complex.ofReal_sub] at hb
        linarith only [hb]
      · have hb := hself (χ₂ * χ₃⁻¹) hp2i3 (γ₂ - γ₃) hτ
        have hc2 : crd₂ = 0 := by rw [hcrd₂, if_neg h42]
        have hc3 : crd₃ = 0 := by rw [hcrd₃, if_neg h43]
        rw [hc2, hc3]
        simp only [Complex.ofReal_add, Complex.ofReal_sub] at hb
        linarith only [hb]
  -- ============ the four triple terms ============
  have hbT123 : Work.ZeroFreeTables.Ksum q T.f Lq
        ((β : ℂ) + ((γ₁ : ℂ) + (γ₂ : ℂ) + (γ₃ : ℂ)) * Complex.I) (χ₁ * χ₂ * χ₃)
      ≤ a + 2 * crd₀ := by
    rw [hprod]
    rw [show ((β : ℂ) + ((γ₁ : ℂ) + (γ₂ : ℂ) + (γ₃ : ℂ)) * Complex.I)
        = (β : ℂ) + (((γ₁ + γ₂ + γ₃ : ℝ)) : ℂ) * Complex.I by push_cast; ring]
    have hτ : |γ₁ + γ₂ + γ₃| ≤ 3 * L := by
      have h := abs_add_le (γ₁ + γ₂) γ₃
      have h' := abs_add_le γ₁ γ₂
      linarith [h, h', hγ1L, hγ2L, hγ3L]
    have hb := htriple (γ₁ + γ₂ + γ₃) hτ
    rw [← hμ₀] at hb
    by_cases h4 : |μ₀| ≤ 4
    · have hcr : crd₀ = Lq * (T.Fc ((μ₀ : ℂ) * Complex.I)).re := by rw [hcrd₀, if_pos h4]
      rw [hcr]
      have hnum := hnum1 lam₁ μ₀ hl1nn hl16 h4
      have hmul := mul_le_mul_of_nonneg_left hnum hlogq.le
      have hgoal : Lq * (T.Fc (((-lam₁ : ℝ) : ℂ) + (μ₀ : ℂ) * Complex.I)).re + T.f 0 * ε' * Lq
          ≤ a + 2 * (Lq * (T.Fc ((μ₀ : ℂ) * Complex.I)).re) := by
        rw [ha]; linarith only [hmul, hlogq, hε']
      exact le_trans hb hgoal
    · have hcr : crd₀ = 0 := by rw [hcrd₀, if_neg h4]
      rw [hcr]
      have hnum := hnum2 lam₁ μ₀ hl1nn hl16 (le_of_lt (not_le.mp h4))
      have hmul := mul_le_mul_of_nonneg_left hnum hlogq.le
      have hgoal : Lq * (T.Fc (((-lam₁ : ℝ) : ℂ) + (μ₀ : ℂ) * Complex.I)).re + T.f 0 * ε' * Lq
          ≤ a + 2 * 0 := by
        rw [ha]; linarith only [hmul, hlogq, hε']
      exact le_trans hb hgoal
  have hbTi123 : Work.ZeroFreeTables.Ksum q T.f Lq
        ((β : ℂ) + (-(γ₁ : ℂ) + (γ₂ : ℂ) + (γ₃ : ℂ)) * Complex.I) (χ₁⁻¹ * χ₂ * χ₃)
      ≤ a + 2 * crd₁ := by
    rw [show ((β : ℂ) + (-(γ₁ : ℂ) + (γ₂ : ℂ) + (γ₃ : ℂ)) * Complex.I)
        = (β : ℂ) + (((-γ₁ + γ₂ + γ₃ : ℝ)) : ℂ) * Complex.I by push_cast; ring]
    have hτ : |-γ₁ + γ₂ + γ₃| ≤ 3 * L := by
      have h := abs_add_le (-γ₁ + γ₂) γ₃
      have h' := abs_add_le (-γ₁) γ₂
      rw [abs_neg] at h'
      linarith [h, h', hγ1L, hγ2L, hγ3L]
    by_cases h1c : χ₂ * χ₃ = χ₁
    · have hchar : χ₁⁻¹ * χ₂ * χ₃ = 1 := by rw [mul_assoc, h1c, inv_mul_cancel]
      rw [hchar]
      have hb := htriple (-γ₁ + γ₂ + γ₃) hτ
      rw [← hμ₁] at hb
      by_cases h4 : |μ₁| ≤ 4
      · have hcr : crd₁ = Lq * (T.Fc ((μ₁ : ℂ) * Complex.I)).re := by
          rw [hcrd₁, if_pos ⟨h1c, h4⟩]
        rw [hcr]
        have hnum := hnum1 lam₁ μ₁ hl1nn hl16 h4
        have hmul := mul_le_mul_of_nonneg_left hnum hlogq.le
        have hgoal : Lq * (T.Fc (((-lam₁ : ℝ) : ℂ) + (μ₁ : ℂ) * Complex.I)).re + T.f 0 * ε' * Lq
            ≤ a + 2 * (Lq * (T.Fc ((μ₁ : ℂ) * Complex.I)).re) := by
          rw [ha]; linarith only [hmul, hlogq, hε']
        exact le_trans hb hgoal
      · have hcr : crd₁ = 0 := by rw [hcrd₁, if_neg (fun hh => h4 hh.2)]
        rw [hcr]
        have hnum := hnum2 lam₁ μ₁ hl1nn hl16 (le_of_lt (not_le.mp h4))
        have hmul := mul_le_mul_of_nonneg_left hnum hlogq.le
        have hgoal : Lq * (T.Fc (((-lam₁ : ℝ) : ℂ) + (μ₁ : ℂ) * Complex.I)).re + T.f 0 * ε' * Lq
            ≤ a + 2 * 0 := by
          rw [ha]; linarith only [hmul, hlogq, hε']
        exact le_trans hb hgoal
    · have hne : χ₁⁻¹ * χ₂ * χ₃ ≠ 1 := by
        have h23 : χ₂ * χ₃ = χ₁⁻¹ := hχ23
        intro hh
        apply h1c
        have hh' : χ₁⁻¹ * (χ₂ * χ₃) = 1 := by rw [mul_assoc] at hh; exact hh
        rw [h23] at hh'
        have h4 : χ₁⁻¹ = χ₁ := by
          have h5 : χ₁ * (χ₁⁻¹ * χ₁⁻¹) = χ₁ * 1 := by rw [hh']
          rwa [← mul_assoc, mul_inv_cancel, one_mul, mul_one] at h5
        rw [← h4, ← h23]
      have hb := hself (χ₁⁻¹ * χ₂ * χ₃) hne (-γ₁ + γ₂ + γ₃) hτ
      have hcr : crd₁ = 0 := by rw [hcrd₁, if_neg (fun hh => h1c hh.1)]
      rw [hcr]
      linarith only [hb]
  have hbT1i23 : Work.ZeroFreeTables.Ksum q T.f Lq
        ((β : ℂ) + ((γ₁ : ℂ) - (γ₂ : ℂ) + (γ₃ : ℂ)) * Complex.I) (χ₁ * χ₂⁻¹ * χ₃)
      ≤ a + 2 * crd₂ := by
    rw [show ((β : ℂ) + ((γ₁ : ℂ) - (γ₂ : ℂ) + (γ₃ : ℂ)) * Complex.I)
        = (β : ℂ) + (((γ₁ - γ₂ + γ₃ : ℝ)) : ℂ) * Complex.I by push_cast; ring]
    have hτ : |γ₁ - γ₂ + γ₃| ≤ 3 * L := by
      have h := abs_add_le (γ₁ - γ₂) γ₃
      have h' := abs_add_le γ₁ (-γ₂)
      rw [abs_neg] at h'
      simp only [sub_eq_add_neg] at h ⊢
      linarith [h, h', hγ1L, hγ2L, hγ3L]
    by_cases h2c : χ₂ * χ₃⁻¹ = χ₁
    · have hchar : χ₁ * χ₂⁻¹ * χ₃ = 1 := by
        rw [← h2c]
        calc ((χ₂ * χ₃⁻¹) * χ₂⁻¹) * χ₃ = (χ₂ * χ₂⁻¹) * (χ₃⁻¹ * χ₃) := by
              rw [mul_assoc (χ₂ * χ₃⁻¹) χ₂⁻¹ χ₃, mul_assoc χ₂ χ₃⁻¹ (χ₂⁻¹ * χ₃),
                mul_left_comm χ₃⁻¹ χ₂⁻¹ χ₃, ← mul_assoc χ₂ χ₂⁻¹ (χ₃⁻¹ * χ₃)]
          _ = 1 := by rw [mul_inv_cancel, inv_mul_cancel, mul_one]
      rw [hchar]
      have hb := htriple (γ₁ - γ₂ + γ₃) hτ
      rw [← hμ₂] at hb
      by_cases h4 : |μ₂| ≤ 4
      · have hcr : crd₂ = Lq * (T.Fc ((μ₂ : ℂ) * Complex.I)).re := by
          rw [hcrd₂, if_pos ⟨h2c, h4⟩]
        rw [hcr]
        have hnum := hnum1 lam₁ μ₂ hl1nn hl16 h4
        have hmul := mul_le_mul_of_nonneg_left hnum hlogq.le
        have hgoal : Lq * (T.Fc (((-lam₁ : ℝ) : ℂ) + (μ₂ : ℂ) * Complex.I)).re + T.f 0 * ε' * Lq
            ≤ a + 2 * (Lq * (T.Fc ((μ₂ : ℂ) * Complex.I)).re) := by
          rw [ha]; linarith only [hmul, hlogq, hε']
        exact le_trans hb hgoal
      · have hcr : crd₂ = 0 := by rw [hcrd₂, if_neg (fun hh => h4 hh.2)]
        rw [hcr]
        have hnum := hnum2 lam₁ μ₂ hl1nn hl16 (le_of_lt (not_le.mp h4))
        have hmul := mul_le_mul_of_nonneg_left hnum hlogq.le
        have hgoal : Lq * (T.Fc (((-lam₁ : ℝ) : ℂ) + (μ₂ : ℂ) * Complex.I)).re + T.f 0 * ε' * Lq
            ≤ a + 2 * 0 := by
          rw [ha]; linarith only [hmul, hlogq, hε']
        exact le_trans hb hgoal
    · have hne : χ₁ * χ₂⁻¹ * χ₃ ≠ 1 := by
        intro hh
        apply h2c
        have h1 : χ₁ * χ₂⁻¹ = χ₃⁻¹ := eqinv (χ₁ * χ₂⁻¹) χ₃ hh
        calc χ₂ * χ₃⁻¹ = χ₃⁻¹ * χ₂ := mul_comm _ _
          _ = (χ₁ * χ₂⁻¹) * χ₂ := by rw [h1]
          _ = χ₁ * (χ₂⁻¹ * χ₂) := mul_assoc _ _ _
          _ = χ₁ * 1 := by rw [inv_mul_cancel]
          _ = χ₁ := mul_one χ₁
      have hb := hself (χ₁ * χ₂⁻¹ * χ₃) hne (γ₁ - γ₂ + γ₃) hτ
      have hcr : crd₂ = 0 := by rw [hcrd₂, if_neg (fun hh => h2c hh.1)]
      rw [hcr]
      linarith only [hb]
  have hbT12i3 : Work.ZeroFreeTables.Ksum q T.f Lq
        ((β : ℂ) + ((γ₁ : ℂ) + (γ₂ : ℂ) - (γ₃ : ℂ)) * Complex.I) (χ₁ * χ₂ * χ₃⁻¹)
      ≤ a + 2 * crd₃ := by
    rw [show ((β : ℂ) + ((γ₁ : ℂ) + (γ₂ : ℂ) - (γ₃ : ℂ)) * Complex.I)
        = (β : ℂ) + (((γ₁ + γ₂ - γ₃ : ℝ)) : ℂ) * Complex.I by push_cast; ring]
    have hτ : |γ₁ + γ₂ - γ₃| ≤ 3 * L := by
      have h := abs_add_le (γ₁ + γ₂) (-γ₃)
      have h' := abs_add_le γ₁ γ₂
      rw [abs_neg] at h
      simp only [sub_eq_add_neg] at h ⊢
      linarith [h, h', hγ1L, hγ2L, hγ3L]
    by_cases h3c : χ₂ * χ₃⁻¹ = χ₁⁻¹
    · have hχ1 : χ₁ = (χ₂ * χ₃⁻¹)⁻¹ := by rw [h3c, inv_inv]
      have hchar : χ₁ * χ₂ * χ₃⁻¹ = 1 := by
        rw [hχ1, mul_inv_rev, inv_inv]
        calc ((χ₃ * χ₂⁻¹) * χ₂) * χ₃⁻¹ = χ₃ * ((χ₂⁻¹ * χ₂) * χ₃⁻¹) := by
              rw [mul_assoc χ₃ χ₂⁻¹ χ₂, mul_assoc χ₃ (χ₂⁻¹ * χ₂) χ₃⁻¹]
          _ = χ₃ * (1 * χ₃⁻¹) := by rw [inv_mul_cancel]
          _ = χ₃ * χ₃⁻¹ := by rw [one_mul]
          _ = 1 := mul_inv_cancel χ₃
      rw [hchar]
      have hb := htriple (γ₁ + γ₂ - γ₃) hτ
      rw [← hμ₃] at hb
      by_cases h4 : |μ₃| ≤ 4
      · have hcr : crd₃ = Lq * (T.Fc ((μ₃ : ℂ) * Complex.I)).re := by
          rw [hcrd₃, if_pos ⟨h3c, h4⟩]
        rw [hcr]
        have hnum := hnum1 lam₁ μ₃ hl1nn hl16 h4
        have hmul := mul_le_mul_of_nonneg_left hnum hlogq.le
        have hgoal : Lq * (T.Fc (((-lam₁ : ℝ) : ℂ) + (μ₃ : ℂ) * Complex.I)).re + T.f 0 * ε' * Lq
            ≤ a + 2 * (Lq * (T.Fc ((μ₃ : ℂ) * Complex.I)).re) := by
          rw [ha]; linarith only [hmul, hlogq, hε']
        exact le_trans hb hgoal
      · have hcr : crd₃ = 0 := by rw [hcrd₃, if_neg (fun hh => h4 hh.2)]
        rw [hcr]
        have hnum := hnum2 lam₁ μ₃ hl1nn hl16 (le_of_lt (not_le.mp h4))
        have hmul := mul_le_mul_of_nonneg_left hnum hlogq.le
        have hgoal : Lq * (T.Fc (((-lam₁ : ℝ) : ℂ) + (μ₃ : ℂ) * Complex.I)).re + T.f 0 * ε' * Lq
            ≤ a + 2 * 0 := by
          rw [ha]; linarith only [hmul, hlogq, hε']
        exact le_trans hb hgoal
    · have hne : χ₁ * χ₂ * χ₃⁻¹ ≠ 1 := by
        intro hh
        apply h3c
        have h1 : χ₁ * χ₂ = (χ₃⁻¹)⁻¹ := eqinv (χ₁ * χ₂) χ₃⁻¹ hh
        rw [inv_inv] at h1
        calc χ₂ * χ₃⁻¹ = χ₂ * (χ₁ * χ₂)⁻¹ := by rw [← h1]
          _ = χ₂ * (χ₂⁻¹ * χ₁⁻¹) := by rw [mul_inv_rev]
          _ = (χ₂ * χ₂⁻¹) * χ₁⁻¹ := by rw [mul_assoc]
          _ = 1 * χ₁⁻¹ := by rw [mul_inv_cancel]
          _ = χ₁⁻¹ := one_mul _
      have hb := hself (χ₁ * χ₂ * χ₃⁻¹) hne (γ₁ + γ₂ - γ₃) hτ
      have hcr : crd₃ = 0 := by rw [hcrd₃, if_neg (fun hh => h3c hh.1)]
      rw [hcr]
      linarith only [hb]
  -- ============ the assembly ============
  have hpos := Work.ZeroFreeTables.Ksum_positivity_three (q := q) (f := T.f) T.f_nonneg
    (x₀ := T.x₀) (L := Lq) (β := β) (γ₁ := γ₁) (γ₂ := γ₂) (γ₃ := γ₃)
    T.x₀_pos hlogq T.f_supp χ₁ χ₂ χ₃
  have hbPsum :
      (Work.ZeroFreeTables.Ksum q T.f Lq ((β : ℂ) + ((γ₁ : ℂ) + (γ₂ : ℂ)) * Complex.I) (χ₁ * χ₂))
      + (Work.ZeroFreeTables.Ksum q T.f Lq ((β : ℂ) + ((γ₁ : ℂ) - (γ₂ : ℂ)) * Complex.I) (χ₁ * χ₂⁻¹))
      + (Work.ZeroFreeTables.Ksum q T.f Lq ((β : ℂ) + ((γ₁ : ℂ) + (γ₃ : ℂ)) * Complex.I) (χ₁ * χ₃))
      + (Work.ZeroFreeTables.Ksum q T.f Lq ((β : ℂ) + ((γ₁ : ℂ) - (γ₃ : ℂ)) * Complex.I) (χ₁ * χ₃⁻¹))
      + (Work.ZeroFreeTables.Ksum q T.f Lq ((β : ℂ) + ((γ₂ : ℂ) + (γ₃ : ℂ)) * Complex.I) (χ₂ * χ₃))
      + (Work.ZeroFreeTables.Ksum q T.f Lq ((β : ℂ) + ((γ₂ : ℂ) - (γ₃ : ℂ)) * Complex.I) (χ₂ * χ₃⁻¹))
      ≤ 6 * a - (crd₀ + crd₁ + crd₂ + crd₃) := by
    linarith only [hbP12, hbP1i2, hbP13, hbP1i3, hbP23, hbP2i3]
  have hbTsum :
      (Work.ZeroFreeTables.Ksum q T.f Lq
          ((β : ℂ) + ((γ₁ : ℂ) + (γ₂ : ℂ) + (γ₃ : ℂ)) * Complex.I) (χ₁ * χ₂ * χ₃))
      + (Work.ZeroFreeTables.Ksum q T.f Lq
          ((β : ℂ) + ((γ₁ : ℂ) + (γ₂ : ℂ) - (γ₃ : ℂ)) * Complex.I) (χ₁ * χ₂ * χ₃⁻¹))
      + (Work.ZeroFreeTables.Ksum q T.f Lq
          ((β : ℂ) + ((γ₁ : ℂ) - (γ₂ : ℂ) + (γ₃ : ℂ)) * Complex.I) (χ₁ * χ₂⁻¹ * χ₃))
      + (Work.ZeroFreeTables.Ksum q T.f Lq
          ((β : ℂ) + (-(γ₁ : ℂ) + (γ₂ : ℂ) + (γ₃ : ℂ)) * Complex.I) (χ₁⁻¹ * χ₂ * χ₃))
      ≤ 4 * a + 2 * (crd₀ + crd₁ + crd₂ + crd₃) := by
    linarith only [hbT123, hbT12i3, hbT1i23, hbTi123]
  simp only [Work.ZeroFreeTables.Ksum] at hbP0 hbS1 hbS2 hbS3 hbPsum hbTsum
  have h7a : 7 * a = T.f 0 * (7/6 + 7 * ε') * Lq := by rw [ha]; ring
  have key : 0 ≤ Lq * (T.F (-lam₁) - T.F 0 - T.F (lam₂ - lam₁) - T.F (lam₃ - lam₁)
      + T.f 0 * (7/6 + 8 * ε')) := by
    have hrw : Lq * (T.F (-lam₁) - T.F 0 - T.F (lam₂ - lam₁) - T.F (lam₃ - lam₁)
        + T.f 0 * (7/6 + 8 * ε'))
        = Lq * T.F (-lam₁) - Lq * T.F 0 - Lq * T.F (lam₂ - lam₁) - Lq * T.F (lam₃ - lam₁)
          + (T.f 0 * (7/6 + 8 * ε')) * Lq := by ring
    rw [hrw]
    nlinarith only [hpos, hbP0, hbS1, hbS2, hbS3, hbPsum, hbTsum, ha, h7a]
  exact (mul_nonneg_iff_of_pos_left hlogq).mp key
/-- HB (1992) §10 (10.1)–(10.6) at rectangle height `L`, in the "near" configuration: `ρ₁` complex (`Im ρ₁ ≠ 0`) but with no lower bound on `|Im ρ₁|`; this is HB Lemma 10.1 (no signed triple product principal) together with HB Lemma 10.2 (`χ₁` complex or `ρ₁` complex, i.e. exactly our `Im ρ₁ ≠ 0`), so the hypothesis list carries no product condition: every configuration of the three conjugate pairs must satisfy (10.6). For every test function `T` of HB's class and every `ε' > 0` there is `q₀` such that for `q ≥ q₀` and pairs at height `L` with `λ₁ ≤ λ₂ ≤ λ₃ ≤ 6/7`, the two numeric conditions (10.8)/(10.9) (`hnum₁`, the `|μ| ≤ 4` case, and `hnum₂`, the `|μ| ≥ 4` case) imply `F(-λ₁) - F(0) - F(λ₂-λ₁) - F(λ₃-λ₁) + f(0)(7/6+8ε') ≥ 0`. This is the height-`L`/`IsZAt`/free-slack analogue of the on-axis engines `ZeroFreeTables/OffAxis/HB10_3Engine.lean` and `OffAxis/Rect10_3EngineH.lean`, and its consumer is `OffAxis/Rect10_3NearF2.lean` (via `tf72T (6/7)` and `OffAxis/tf72FcOneNum`). Decomposition, following the existing work: (i) the companion first-level case (`hb106Near` in the requester's `_wStage1.lean`, where none of the four signed triple characters is principal) is already proved and is the template for all the boilerplate (δ from `OffAxis/L52SupplyGen`, the point conditions, the window/minimality argument, the conductor instances, the final `linarith`); (ii) the second-level case (some signed triple product trivial) is HB's Lemma 10.2 and is worked out in `MyScratchHB103/full.lean` (kernel `hb103_kernel`, credits `crd j = log q · Re F(i μ_j)`, triple bounds `bt j ≤ f 0 (1/6+ε)log q + 2 crd j`, pair aggregate `bPsum ≤ 6 f 0 (1/6+ε) log q - Σ crd j`), which handles the general configuration at height `1 < |Im ρ₁|` and uses that hypothesis only once (to get `Im ρ₁ ≠ 0`), so it can be weakened to the present statement; the changes are `IsZAt L` in place of `IsZ`, and the case-split absorbed into the hypothesis list. The principal sums at shifted points come from the *proved* `Work.LinnikAreas.principalKsumWide` (main term kept, `|γ| ≤ 10 log q`; the deposit `Submission/Work/ZeroFreeTables/OffAxis/KsumPrincipalShiftF.lean` states the same for `|s.im| ≤ log q` and may be used instead); the kept-zero pair sums from the proved `Ksum_le_single_of_L52_phi`, or — when a single pair sum must keep two zeros (the all-real-character case with `μ₁ ≠ 0`) — from `OffAxis/KsumLeTwoMain6` (`Submission/Work/OffAxis/KsumLeTwoMain6.lean`, requested in parallel; the identical statement with general `c` is the in-flight `Work.ZeroFreeTables.OffAxis.KsumLeTwoOfL52`). -/
theorem HB10_3EngineNear (T : Work.ZeroFreeTables.TestFn) (ε' : ℝ) (hε' : 0 < ε') :
    ∀ L : ℝ, 1 ≤ L → ∃ q₀ : ℕ, ∀ q : ℕ, q₀ ≤ q → ∀ [NeZero q]
      (χ₁ χ₂ χ₃ : DirichletCharacter ℂ q) (ρ₁ ρ₂ ρ₃ : ℂ),
      Work.ZeroFreeTables.IsRectMin L χ₁ ρ₁ →
      ρ₁.im ≠ 0 →
      Work.ZeroFreeTables.IsZAt L χ₂ ρ₂ → Work.ZeroFreeTables.IsZAt L χ₃ ρ₃ →
      χ₂ ≠ χ₁ → χ₂ ≠ χ₁⁻¹ → χ₃ ≠ χ₁ → χ₃ ≠ χ₁⁻¹ → χ₃ ≠ χ₂ → χ₃ ≠ χ₂⁻¹ →
      Work.LinnikContract.lamOf q ρ₂ ≤ Work.LinnikContract.lamOf q ρ₃ →
      Work.LinnikContract.lamOf q ρ₃ ≤ 6/7 →
      (∀ a μ : ℝ, 0 ≤ a → a ≤ 6/7 → |μ| ≤ 4 →
        (T.Fc (((-a : ℝ) : ℂ) + (μ : ℂ) * Complex.I)).re
          - 2 * (T.Fc ((μ : ℂ) * Complex.I)).re ≤ T.f 0 / 6) →
      (∀ a μ : ℝ, 0 ≤ a → a ≤ 6/7 → 4 ≤ |μ| →
        (T.Fc (((-a : ℝ) : ℂ) + (μ : ℂ) * Complex.I)).re ≤ T.f 0 / 6) →
      0 ≤ T.F (-(Work.LinnikContract.lamOf q ρ₁)) - T.F 0
        - T.F (Work.LinnikContract.lamOf q ρ₂ - Work.LinnikContract.lamOf q ρ₁)
        - T.F (Work.LinnikContract.lamOf q ρ₃ - Work.LinnikContract.lamOf q ρ₁)
        + T.f 0 * (7/6 + 8 * ε')
 := by
  intro L hL1
  obtain ⟨qF1, hF1⟩ := hb106NearF1 T ε' hε' L hL1
  obtain ⟨qC, hC⟩ := hb106Canon T ε' hε' L hL1
  refine ⟨max qF1 qC, ?_⟩
  intro q hq _inst χ₁ χ₂ χ₃ ρ₁ ρ₂ ρ₃ hR hg hZ2 hZ3 h21 h2i h31 h3i h32 h3ii hlam23 hlam3 hnum1 hnum2
  have hqF1 : qF1 ≤ q := le_trans (le_max_left _ _) hq
  have hqC : qC ≤ q := le_trans (le_max_right _ _) hq
  by_cases hdisj : χ₁ * χ₂ * χ₃ = 1 ∨ χ₁ * χ₂ = χ₃ ∨ χ₁ * χ₃ = χ₂ ∨ χ₂ * χ₃ = χ₁
  · rcases hdisj with h0 | h3 | h2 | h1
    · exact hC q hqC χ₁ χ₂ χ₃ ρ₁ ρ₂ ρ₃ hR hg hZ2 hZ3 h21 h2i h31 h3i h32 h3ii hlam23 hlam3 h0 hnum1 hnum2
    · have hZ3' : Work.ZeroFreeTables.IsZAt L χ₃⁻¹ (starRingEnd ℂ ρ₃) := IsZAt_inv_conj hZ3
      have hc := hC q hqC χ₁ χ₂ χ₃⁻¹ ρ₁ ρ₂ (starRingEnd ℂ ρ₃) hR hg hZ2 hZ3'
        h21 h2i
        (fun hh => h3i (by rw [← hh]; simp))
        (fun hh => h31 (inv_injective hh))
        (fun hh => h3ii (by rw [← hh]; simp))
        (fun hh => h32 (inv_injective hh))
        (by rw [Work.ZeroFreeTables.OffAxis.lamOf_conj]; exact hlam23)
        (by rw [Work.ZeroFreeTables.OffAxis.lamOf_conj]; exact hlam3)
        (by rw [h3, mul_inv_cancel]) hnum1 hnum2
      rw [Work.ZeroFreeTables.OffAxis.lamOf_conj] at hc
      exact hc
    · have hZ2' : Work.ZeroFreeTables.IsZAt L χ₂⁻¹ (starRingEnd ℂ ρ₂) := IsZAt_inv_conj hZ2
      have hc := hC q hqC χ₁ χ₂⁻¹ χ₃ ρ₁ (starRingEnd ℂ ρ₂) ρ₃ hR hg hZ2' hZ3
        (fun hh => h2i (by rw [← hh]; simp))
        (fun hh => h21 (inv_injective hh))
        h31 h3i h3ii (by simpa using h32)
        (by rw [Work.ZeroFreeTables.OffAxis.lamOf_conj]; exact hlam23)
        hlam3
        (by rw [mul_assoc, mul_comm χ₂⁻¹ χ₃, ← mul_assoc, h2, mul_inv_cancel]) hnum1 hnum2
      rw [Work.ZeroFreeTables.OffAxis.lamOf_conj] at hc
      exact hc
    · have hR' : Work.ZeroFreeTables.IsRectMin L χ₁⁻¹ (starRingEnd ℂ ρ₁) := IsRectMin_inv_conj hR
      have hg' : (starRingEnd ℂ ρ₁).im ≠ 0 := by
        rw [Complex.conj_im]; exact neg_ne_zero.mpr hg
      have hc := hC q hqC χ₁⁻¹ χ₂ χ₃ (starRingEnd ℂ ρ₁) ρ₂ ρ₃ hR' hg' hZ2 hZ3
        h2i (by simpa using h21) h3i (by simpa using h31) h32 h3ii hlam23 hlam3
        (by rw [mul_assoc, h1, inv_mul_cancel]) hnum1 hnum2
      rw [Work.ZeroFreeTables.OffAxis.lamOf_conj] at hc
      exact hc
  · simp only [not_or] at hdisj
    exact hF1 q hqF1 χ₁ χ₂ χ₃ ρ₁ ρ₂ ρ₃ hR hZ2 hZ3 h21 h2i h31 h3i h32 h3ii hlam23 hlam3
      hdisj.1 hdisj.2.1 hdisj.2.2.1 hdisj.2.2.2

end Work.OffAxis
