/-
# OffAxis/Rect10_3RealF1Clean

`Rect10_3RealF1Clean` (Heath-Brown 1992, §10, the "real-"`ρ₁` case of Lemma 10.1: none of the four
signed triple products of the three characters is principal) at rectangle height `L`.

The analytic input is the `F`-method engine HB (10.6), proved here for an **arbitrary** rectangle
minimiser `IsRectMin L χ₁ ρ₁` (`hb106RealC`): the case-1 engine of `Rect10_3H_F1` (`hb106`) never
uses its hypothesis `1 < |ρ₁.im|`, so dropping it disposes of the real-zero case `ρ₁.im = 0` as
well.  The numerical endgame is the (§10 endgame, `rect10_3_endgame`) applied to the test
function `tf72T (6/7)`; the moment step `Tf72MomentStep` is delegated (see
`Submission/Work/OffAxis/Tf72MomentStep.lean`).
-/
import Mathlib
import Submission.Work.ZeroFreeTables.OffAxis.Defs
import Submission.Work.ZeroFreeTables.OffAxis.WideDefs
import Submission.Work.ZeroFreeTables.OffAxis.L52SupplyGen
import Submission.Work.ZeroFreeTables.Ksum_positivity_three
import Submission.Work.NumberTheory.Linnik.scratch_l62app_phi
import Submission.Work.ZeroFreeTables.Engine
import Submission.Commons.NumberTheory.Linnik.Ksum_principal_le
import Submission.Work.ZeroFreeTables.OffAxis.RectC.Facts
import Submission.Work.ZeroFreeTables.hbLemma6_2_engine_v2
import Submission.Work.LinnikAreas.boxMaxZero
import Submission.Work.ZeroFreeTables.CertData
import Submission.Work.ZeroFreeTables.testFn7_2
import Submission.Work.ZeroFreeTables.TestFn_F_eq_integral
import Submission.Work.OffAxis.Rect10_3EndgameClean
import Submission.Work.ZeroFreeTables.tf72f_gap_mono
import Submission.Work.ZeroFreeTables.TestFn_F_antitone
import Submission.Work.ZeroFreeTables.tf72f_laplace_counterexample_bounds
import Submission.Work.OffAxis.Tf72MomentStep

open DirichletCharacter Complex
open scoped Classical BigOperators
open scoped Interval
open MeasureTheory

noncomputable section

namespace Work.ZeroFreeTables.OffAxis

open Work.LinnikContract

/-! ## Elementary facts about `λ` at a zero (copies of `Rect10_3H_F1`'s helpers, so that
this module does not import the `tf72G` chain and stays compatible with the complex-`G72`
numerics of the §10 `F`-method) -/

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

/-! ## The `F`-method case-1 engine: HB (10.6) -/
/-- **HB (10.6) in the case of Lemma 10.1.**  For any test function `T` of HB's class, and any
three conjugate pairs of non-principal characters at rectangle height `L` with no principal
signed triple product, `lam₂ ≤ lam₃ ≤ 6/7`, and `ρ₁` the rectangle minimiser, the `F`-method
combination is non-negative:
`F(-lam₁) - F(0) - F(lam₂-lam₁) - F(lam₃-lam₁) + f(0)(7/6 + 8ε') ≥ 0`. -/
theorem hb106RealC (T : Work.ZeroFreeTables.TestFn) (ε' : ℝ) (hε' : 0 < ε') :
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
  obtain ⟨δ, hδ0, hδ1, qL52, hL52⟩ := L52SupplyGen ε' hε'
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
    have hzm : Work.LinnikContract.zeroMult χ u ≠ 0 := zeroMult_ne_zero_of_divisor χ hχ hdiv
    have him1 : |s.im - u.im| ≤ δ := by
      have h := Complex.abs_im_le_norm ((1:ℂ) + (s.im : ℂ) * Complex.I - u)
      have h' : (((1:ℂ) + (s.im : ℂ) * Complex.I - u).im) = s.im - u.im := by simp
      rw [h'] at h
      exact le_trans h hwu
    have him2 : |u.im| ≤ |s.im| + δ := by
      calc |u.im| = |s.im - (s.im - u.im)| := by ring_nf
        _ ≤ |s.im| + |s.im - u.im| := abs_sub _ _
        _ ≤ |s.im| + δ := by linarith
    have him3 : |u.im| ≤ 10 * L := by linarith only [hsim, him2, hδ1, hL1]
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
        rw [TestFn_F_eq_integral]
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
      have h := mem_closedBall_of_absre_le_one_v2 (abs_re_le_one_of_zeroMult hχ hzm)
      rwa [hργ] at h
    have hdiv : (MeromorphicOn.divisor (DirichletCharacter.completedLFunction χ.primitiveCharacter)
        (Metric.closedBall 0 (|((β : ℂ) + (γ : ℂ) * Complex.I).im| + 2))) ρ ≠ 0 := by
      have him : (((β : ℂ) + (γ : ℂ) * Complex.I).im) = γ := by simp
      rw [him]
      exact divisor_ne_zero_of_zeroMult χ hχ hmem hzm
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
    linarith only [hpos, hbP, hbS1, hbS2, hbS3, hbP12, hbPi12, hbP13, hbPi13, hbP23, hbPi23,
      hbT123, hbT12i3, hbT1i23, hbTi123]
  have hX : 0 ≤ T.F (-lam₁) - T.F 0 - T.F (lam₂ - lam₁) - T.F (lam₃ - lam₁) + T.f 0 * (7/6 + 8 * ε') := by
    by_contra hneg
    push_neg at hneg
    have h2 : Real.log (q : ℝ) * (T.F (-lam₁) - T.F 0 - T.F (lam₂ - lam₁) - T.F (lam₃ - lam₁)
        + T.f 0 * (7/6 + 8 * ε')) < 0 := mul_neg_of_pos_of_neg hlogq hneg
    have h3 : Real.log (q : ℝ) * (T.F (-lam₁) - T.F 0 - T.F (lam₂ - lam₁) - T.F (lam₃ - lam₁)
        + T.f 0 * (7/6 + 8 * ε')) = Real.log (q : ℝ) * (T.F (-lam₁) - T.F 0 - T.F (lam₂ - lam₁)
          - T.F (lam₃ - lam₁)) + T.f 0 * (7/6 + 8 * ε') * Real.log (q : ℝ) := by ring
    linarith only [hkey, h2, h3]
  rw [hlam₁, hlam₂, hlam₃] at hX
  exact hX

/-- **The `F`-method combination (10.7) fails with an explicit margin.**
For any `TestFn T` with `x₀ = 7/3`, `f = tf72f (6/7)`, `F 0 = 8/9` and `F(-6/7) = 8/5`, and
every `0 ≤ λ₁ ≤ 792/1000`,

`T.F(-6/7) - T.F(-λ₁) ≥ 2 (T.F 0 - T.F(6/7 - λ₁)) + 83/9000`.

The proof is the endpoint computation of `tf72f_laplace_counterexample_bounds`
(`F(-792/1000) ≤ 761/500`, `F(57/875) ≥ 1709/2000`) together with the maximality of the
`F`-method gap `λ ↦ F(-λ) - 2F(6/7-λ)` at `λ = 792/1000` (`tf72f_gap_mono`): the gap is at most
`761/500 - 2·(1709/2000) = -187/1000`, while `8/5 + 187/1000 = 16/9 + 83/9000`. -/
theorem tf72f_refute_quant_realC (T : Work.ZeroFreeTables.TestFn) (hT : T.x₀ = 7/3)
    (hf : T.f = Work.ZeroFreeTables.tf72f (6/7)) (hF0 : T.F 0 = 8/9)
    (hF6 : T.F (-(6/7)) = 8/5) :
    ∀ l₁ : ℝ, 0 ≤ l₁ → l₁ ≤ 792/1000 →
      T.F (-(6/7)) - T.F (-l₁) ≥ 2 * (T.F 0 - T.F (6/7 - l₁)) + 83/9000 := by
  intro l₁ h0 h1
  obtain ⟨hb1, hb2⟩ := Work.ZeroFreeTables.tf72f_laplace_counterexample_bounds
  have hb1' : (∫ t in (0:ℝ)..(7/3),
      Real.exp ((792/1000:ℝ) * t) * Work.ZeroFreeTables.tf72f (6/7) t) ≤ 761/500 := by
    have h := hb1; rwa [show (2:ℝ)/(6/7) = 7/3 by norm_num] at h
  have hb2' : (1709/2000 : ℝ) ≤ ∫ t in (0:ℝ)..(7/3),
      Real.exp (-(57/875:ℝ) * t) * Work.ZeroFreeTables.tf72f (6/7) t := by
    have h := hb2; rwa [show (2:ℝ)/(6/7) = 7/3 by norm_num] at h
  have eB : T.F (-l₁) = ∫ t in (0:ℝ)..(7/3),
      Real.exp (l₁ * t) * Work.ZeroFreeTables.tf72f (6/7) t := by
    rw [Work.ZeroFreeTables.F_eq_tf72f_int T hT hf]
    exact intervalIntegral.integral_congr (fun t _ => by
      rw [show -((-l₁) * t) = l₁ * t from by ring])
  have eC : T.F (6/7 - l₁) = ∫ t in (0:ℝ)..(7/3),
      Real.exp (-((6/7 - l₁) * t)) * Work.ZeroFreeTables.tf72f (6/7) t :=
    Work.ZeroFreeTables.F_eq_tf72f_int T hT hf (6/7 - l₁)
  have hgap := Work.ZeroFreeTables.tf72f_gap_mono l₁ h0 h1
  have hker : T.F (-l₁) - 2 * T.F (6/7 - l₁) ≤ (761/500 : ℝ) - 2 * (1709/2000 : ℝ) := by
    rw [eB, eC]
    linarith
  have hsub : (761/500 : ℝ) - 2 * (1709/2000 : ℝ) = -(187/1000) := by norm_num
  rw [hsub] at hker
  rw [hF6, hF0]
  linarith

/-- **HB §10 endgame.**  From Heath-Brown's (10.6) for the test function of Lemma 7.2 at
`λ = 6/7`, the ordering `0 ≤ λ₁ ≤ λ₃ ≤ 6/7` and the identity `f(0)(7/6) = 3F(0) - F(-6/7)`
(Lemma 7.5), one gets (10.7) with the `ε'`-slack `s = 8ε'f(0)`.  The moment step `hmom` then
splits: either `λ₁ ≤ 792/1000` (and the refutation `href` — `tf72f_refute_quant` — contradicts
(10.7)), or `λ₁ ≥ 6/7 - ε/2`, which already gives `λ₃ ≥ λ₁ ≥ 6/7 - ε/2 > 6/7 - ε`.  The
hypothesis `s ≤ ε/10000` is what makes the moment step sharp enough; `s < 83/9000` is the
margin of `href`. -/
theorem rect10_3_endgame_realC (T : Work.ZeroFreeTables.TestFn) (ε' ε s l₁ l₂ l₃ : ℝ)
    (hε : 0 < ε) (hT : T.x₀ = 7/3) (hf : T.f = Work.ZeroFreeTables.tf72f (6/7))
    (hF0 : T.F 0 = 8/9) (hF6 : T.F (-(6/7)) = 8/5)
    (hL75 : T.f 0 * (7/6) = 3 * T.F 0 - T.F (-(6/7)))
    (hs0 : 0 ≤ s) (hse : s ≤ ε/10000) (hs8 : 8 * ε' * T.f 0 ≤ s) (hs83 : s < 83/9000)
    (hmom : ∀ l : ℝ, 0 ≤ l → l < 6/7 →
      T.F (-(6/7)) - T.F (-l) ≤ 2 * (T.F 0 - T.F (6/7 - l)) + s →
        l ≤ 792/1000 ∨ 6/7 - ε/2 ≤ l)
    (href : ∀ l : ℝ, 0 ≤ l → l ≤ 792/1000 →
      T.F (-(6/7)) - T.F (-l) ≥ 2 * (T.F 0 - T.F (6/7 - l)) + 83/9000)
    (h106 : T.F (-l₁) - T.F 0 - T.F (l₂ - l₁) - T.F (l₃ - l₁) + T.f 0 * (7/6 + 8 * ε') ≥ 0)
    (h01 : 0 ≤ l₁) (h13 : l₁ ≤ l₃) (h23 : l₂ ≤ l₃) (h36 : l₃ ≤ 6/7) :
    6/7 - ε ≤ l₃ := by
  by_contra hcon
  rw [not_le] at hcon
  have hanti := Work.ZeroFreeTables.TestFn_F_antitone T
  have h2 : T.F (6/7 - l₁) ≤ T.F (l₂ - l₁) := hanti (by linarith [h23])
  have h3 : T.F (6/7 - l₁) ≤ T.F (l₃ - l₁) := hanti (by linarith)
  -- (10.7) with the slack
  have h107 : T.F (-(6/7)) - T.F (-l₁) ≤ 2 * (T.F 0 - T.F (6/7 - l₁)) + s := by
    have hk : T.f 0 * (7/6 + 8 * ε') = (3 * T.F 0 - T.F (-(6/7))) + 8 * ε' * T.f 0 := by
      rw [← hL75]; ring
    rw [hk] at h106
    linarith only [h2, h3, h106, hs8]
  by_cases hcase : l₁ < 6/7
  · rcases hmom l₁ h01 hcase h107 with hle | hbig
    · have hh := href l₁ h01 hle
      linarith only [hh, h107, hs83]
    · linarith
  · push Not at hcase
    linarith

end Work.ZeroFreeTables.OffAxis

namespace Work.OffAxis

open DirichletCharacter Complex
open Work.LinnikContract

theorem Rect10_3RealF1Clean : ∀ ε : ℝ, 0 < ε → ∀ L : ℝ, 1 ≤ L → ∃ q₀ : ℕ, ∀ q : ℕ, q₀ ≤ q → ∀ [NeZero q]
    (χ₁ χ₂ χ₃ : DirichletCharacter ℂ q) (ρ₁ ρ₂ ρ₃ : ℂ),
    Work.ZeroFreeTables.IsRectMin L χ₁ ρ₁ → ρ₁.im = 0 →
    Work.ZeroFreeTables.IsZAt L χ₂ ρ₂ → Work.ZeroFreeTables.IsZAt L χ₃ ρ₃ →
    χ₂ ≠ χ₁ → χ₂ ≠ χ₁⁻¹ → χ₃ ≠ χ₁ → χ₃ ≠ χ₁⁻¹ → χ₃ ≠ χ₂ → χ₃ ≠ χ₂⁻¹ →
    (∀ (χ : DirichletCharacter ℂ q) (u : ℂ), Work.ZeroFreeTables.IsZAt L χ u → χ ≠ χ₁ → χ ≠ χ₁⁻¹ → Work.LinnikContract.lamOf q ρ₂ ≤ Work.LinnikContract.lamOf q u) →
    (∀ (χ : DirichletCharacter ℂ q) (u : ℂ), Work.ZeroFreeTables.IsZAt L χ u → χ ≠ χ₁ → χ ≠ χ₁⁻¹ → χ ≠ χ₂ → χ ≠ χ₂⁻¹ → Work.LinnikContract.lamOf q ρ₃ ≤ Work.LinnikContract.lamOf q u) →
    Work.LinnikContract.lamOf q ρ₂ ≤ Work.LinnikContract.lamOf q ρ₃ →
    Work.LinnikContract.lamOf q ρ₃ ≤ 6/7 - ε →
    χ₁ * χ₂ * χ₃ ≠ 1 → χ₁ * χ₂ ≠ χ₃ → χ₁ * χ₃ ≠ χ₂ → χ₂ * χ₃ ≠ χ₁ →
    6/7 - ε ≤ Work.LinnikContract.lamOf q ρ₃ := by
  intro ε hε L hL1
  set s : ℝ := min (ε / 10000) (83 / 18000) with hsdef
  have hs_pos : 0 < s := by
    rw [hsdef]
    exact lt_min (by positivity) (by norm_num)
  have hs0 : 0 ≤ s := hs_pos.le
  have hse : s ≤ ε / 10000 := by rw [hsdef]; exact min_le_left _ _
  have hs83 : s < 83 / 9000 := by
    have h := min_le_right (ε / 10000) (83 / 18000)
    rw [hsdef]
    linarith
  set ε' : ℝ := s * (35 / 512) with hepsdef
  have hε' : 0 < ε' := by
    rw [hepsdef]
    exact mul_pos hs_pos (by norm_num)
  set T : Work.ZeroFreeTables.TestFn := Work.ZeroFreeTables.tf72T ((6 : ℝ) / 7) (by norm_num)
    with hTdef
  obtain ⟨q₀, hq₀⟩ := Work.ZeroFreeTables.OffAxis.hb106RealC T ε' hε' L hL1
  refine ⟨q₀, ?_⟩
  intro q hq _inst χ₁ χ₂ χ₃ ρ₁ ρ₂ ρ₃ hR him1 hZ2 hZ3 hne21 hne2i hne31 hne3i hne32 hne3ii
    hmin2 hmin3 h23 h3le hp1 hp2 hp3 hp4
  have h36 : Work.LinnikContract.lamOf q ρ₃ ≤ 6/7 := by linarith
  have h106 := hq₀ q hq χ₁ χ₂ χ₃ ρ₁ ρ₂ ρ₃ hR hZ2 hZ3 hne21 hne2i hne31 hne3i hne32 hne3ii
    h23 h36 hp1 hp2 hp3 hp4
  have hT : T.x₀ = 7/3 := by
    rw [hTdef]
    show (2 : ℝ) / ((6 : ℝ) / 7) = 7/3
    norm_num
  have hf : T.f = Work.ZeroFreeTables.tf72f (6/7) := by rw [hTdef]; rfl
  have hF0 : T.F 0 = 8/9 := by
    rw [hTdef]
    show (Work.ZeroFreeTables.tf72Fc ((6 : ℝ) / 7) ((0 : ℝ) : ℂ)).re = 8/9
    rw [show ((0 : ℝ) : ℂ) = 0 from by norm_num]
    exact Work.ZeroFreeTables.tf72Fc_zero_re _ (by norm_num)
  have hF6 : T.F (-(6/7)) = 8/5 := by
    rw [hTdef]
    show (Work.ZeroFreeTables.tf72Fc ((6 : ℝ) / 7) (((-((6 : ℝ) / 7)) : ℝ) : ℂ)).re = 8/5
    exact Work.ZeroFreeTables.tf72Fc_neglam_re _ (by norm_num)
  have hf0 : T.f 0 = 32/35 := by
    rw [hTdef]
    show Work.ZeroFreeTables.tf72f (6/7) 0 = 32/35
    rw [Work.ZeroFreeTables.tf72f_at_zero (6/7) (by norm_num)]
    norm_num
  have hL75 : T.f 0 * (7/6) = 3 * T.F 0 - T.F (-(6/7)) := by
    rw [hf0, hF0, hF6]; norm_num
  have hs8 : 8 * ε' * T.f 0 ≤ s := by
    rw [hepsdef, hf0]; linarith only [hs0]
  have href := Work.ZeroFreeTables.OffAxis.tf72f_refute_quant_realC T hT hf hF0 hF6
  have hmom : ∀ l : ℝ, 0 ≤ l → l < 6/7 →
      T.F (-(6/7)) - T.F (-l) ≤ 2 * (T.F 0 - T.F (6/7 - l)) + s →
      l ≤ 792/1000 ∨ 6/7 - ε/2 ≤ l := by
    intro l hl0 hl67 hineq
    have h1 := Work.ZeroFreeTables.F_eq_tf72f_int T hT hf (-(6/7))
    have h2 := Work.ZeroFreeTables.F_eq_tf72f_int T hT hf (-l)
    have h3 := Work.ZeroFreeTables.F_eq_tf72f_int T hT hf 0
    have h4 := Work.ZeroFreeTables.F_eq_tf72f_int T hT hf (6/7 - l)
    rw [h1, h2, h3, h4] at hineq
    refine Work.OffAxis.Tf72MomentStep ε s hε hs0 hse l hl0 hl67 ?_
    simpa only [neg_mul, neg_neg, neg_zero, zero_mul, Real.exp_zero, one_mul] using hineq
  have hl1nn : 0 ≤ Work.LinnikContract.lamOf q ρ₁ :=
    Work.ZeroFreeTables.OffAxis.lamOf_nonneg_of_zeroMult hR.1.2.1
  have hl13 : Work.LinnikContract.lamOf q ρ₁ ≤ Work.LinnikContract.lamOf q ρ₃ :=
    hR.2 χ₃ ρ₃ ⟨hZ3.1, hZ3.2.1, le_trans hZ3.2.2 (by linarith)⟩
  exact Work.ZeroFreeTables.OffAxis.rect10_3_endgame_realC T ε' ε s
    (Work.LinnikContract.lamOf q ρ₁) (Work.LinnikContract.lamOf q ρ₂)
    (Work.LinnikContract.lamOf q ρ₃)
    hε hT hf hF0 hF6 hL75 hs0 hse hs8 hs83 hmom href h106 hl1nn hl13 h23 h36

end Work.OffAxis


