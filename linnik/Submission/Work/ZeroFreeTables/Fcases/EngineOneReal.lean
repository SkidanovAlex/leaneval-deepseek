/-
# The (10.6)-ledger of HB §10 case 3, (10.12): exactly one real character

Copy of `Work.OffAxis.rect103OneRealH` (`OffAxis/Rect10_3OneReal.lean`) with the two
minimality hypotheses on `ρ₂`, `ρ₃` deleted (they occur only in the statement, never in the
proof); the branch `ρ₁ ∈ ℝ`, `χ₁` real, `χ₂, χ₃` complex of `HB10_3_Fcases` cannot supply them.
-/
import Submission.Work.OffAxis.Rect10_3OneReal

open DirichletCharacter Complex
open scoped Classical BigOperators
open MeasureTheory
noncomputable section

namespace Work.OffAxis

set_option maxHeartbeats 4000000 in
theorem rect103OneRealNoMin (T : Work.ZeroFreeTables.TestFn) (ε' : ℝ) (hε' : 0 < ε')
    (hP : ∃ qP : ℕ, ∀ q : ℕ, qP ≤ q → ∀ [NeZero q] (s : ℂ),
        |s.re - 1| ≤ Real.sqrt (Real.log (Real.log (q : ℝ))) / Real.log (q : ℝ) →
        |s.im| ≤ Real.log (q : ℝ) →
        Work.ZeroFreeTables.Ksum q T.f (Real.log (q : ℝ)) s (1 : DirichletCharacter ℂ q)
          ≤ Real.log (q : ℝ) *
              (∫ t in (0:ℝ)..T.x₀,
                Complex.exp (-(((s - 1) * ((Real.log (q : ℝ) : ℂ)) * (t : ℂ))))
                  * ((T.f t : ℝ) : ℂ)).re
            + T.f 0 * ε' * Real.log (q : ℝ))
    (hsub : ∀ a m : ℝ, 0 ≤ a → a ≤ 6/7 → 9/7 ≤ |m| →
        (T.Fc (((-a : ℝ) : ℂ) + (m : ℂ) * Complex.I)).re - (T.Fc ((m : ℂ) * Complex.I)).re
          ≤ 7 * T.f 0 / 24)
    (hlow : ∀ t m : ℝ, 0 ≤ t → t ≤ 6/7 → |m| ≤ 9/7 →
        3 * T.f 0 / 8 ≤ (T.Fc ((t : ℂ) + (m : ℂ) * Complex.I)).re)
    (hB : ∀ a m : ℝ, 0 ≤ a → a ≤ 6/7 → 200 ≤ |m| →
        (T.Fc (((-a : ℝ) : ℂ) + (m : ℂ) * Complex.I)).re ≤ T.f 0 / 6)
    (hF20 : ∀ a m : ℝ, 0 ≤ a → a ≤ 6/7 → |m| ≤ 9/7 →
        (T.Fc (((-a : ℝ) : ℂ) + (m : ℂ) * Complex.I)).re ≤ T.f 0 * (7/4)) :
    ∀ H : ℝ, 1 ≤ H → ∃ q₀ : ℕ, ∀ q : ℕ, q₀ ≤ q → ∀ [NeZero q]
      (χ₁ χ₂ χ₃ : DirichletCharacter ℂ q) (ρ₁ ρ₂ ρ₃ : ℂ),
      Work.ZeroFreeTables.IsRectMin H χ₁ ρ₁ → ρ₁.im = 0 →
      χ₁ ^ 2 = 1 → χ₂ ^ 2 ≠ 1 → χ₃ ^ 2 ≠ 1 → χ₁ * χ₂ * χ₃ = 1 →
      Work.ZeroFreeTables.IsZAt H χ₂ ρ₂ → Work.ZeroFreeTables.IsZAt H χ₃ ρ₃ →
      χ₂ ≠ χ₁ → χ₂ ≠ χ₁⁻¹ → χ₃ ≠ χ₁ → χ₃ ≠ χ₁⁻¹ → χ₃ ≠ χ₂ → χ₃ ≠ χ₂⁻¹ →
      Work.LinnikContract.lamOf q ρ₂ ≤ Work.LinnikContract.lamOf q ρ₃ →
      Work.LinnikContract.lamOf q ρ₃ ≤ 6/7 →
      T.F (-(Work.LinnikContract.lamOf q ρ₁)) - T.F 0
          - T.F (Work.LinnikContract.lamOf q ρ₂ - Work.LinnikContract.lamOf q ρ₁)
          - T.F (Work.LinnikContract.lamOf q ρ₃ - Work.LinnikContract.lamOf q ρ₁)
          + T.f 0 * (7/6 + 8 * ε') ≥ 0 := by
  intro H hH1
  -- the two `L52Hyp` supplies: `c = 1/6` for arbitrary non-principal characters, `c = 1/8` for
  -- real ones (HB Lemma 3.1 with `φ = 1/4`), and the principal bound `hP`
  obtain ⟨δ, hδ0, hδ1, qL52, hL52⟩ := Work.ZeroFreeTables.OffAxis.L52SupplyGen ε' hε'
  obtain ⟨δR, hδR0, hδR1, qL52R, hL52R⟩ := Work.ZeroFreeTables.XY.L52HypEighth_delta (ε := ε') hε'
  obtain ⟨B, hB0, hBnd⟩ := T.f_bound
  have hF : ∀ z : ℂ, 0 ≤ z.re →
      0 ≤ (∫ t in (0:ℝ)..T.x₀, Complex.exp (-(z * (t : ℂ))) * ((T.f t : ℝ) : ℂ)).re := by
    intro z hz; rw [← T.Fc_spec z]; exact T.Fc_re_nonneg z hz
  obtain ⟨qAs, hAs⟩ := Commons.NumberTheory.Linnik.Ksum_le_self_of_L52_phi T.x₀ B (1/6)
    T.x₀_pos hB0 (f := T.f) T.f_cont T.f_supp T.f_diff hBnd T.f0_pos hF hε' hδ0 hδ1
  obtain ⟨qSs, hSs⟩ := Commons.NumberTheory.Linnik.Ksum_le_single_of_L52_phi T.x₀ B (1/6)
    T.x₀_pos hB0 (f := T.f) T.f_cont T.f_supp T.f_diff hBnd T.f0_pos hF hε' hδ0 hδ1
  obtain ⟨qAsR, hAsR⟩ := Commons.NumberTheory.Linnik.Ksum_le_self_of_L52_phi T.x₀ B (1/8)
    T.x₀_pos hB0 (f := T.f) T.f_cont T.f_supp T.f_diff hBnd T.f0_pos hF hε' hδR0 hδR1
  obtain ⟨qSsR, hSsR⟩ := Commons.NumberTheory.Linnik.Ksum_le_single_of_L52_phi T.x₀ B (1/8)
    T.x₀_pos hB0 (f := T.f) T.f_cont T.f_supp T.f_diff hBnd T.f0_pos hF hε' hδR0 hδR1
  obtain ⟨qPs, hPs⟩ := Commons.NumberTheory.Linnik.Ksum_principal_le T.x₀ B T.x₀_pos hB0
    (f := T.f) T.f_cont T.f_supp T.f_diff hBnd hε' T.f0_pos
  obtain ⟨qPsh, hPsh⟩ := hP
  refine ⟨max (max (max (max qL52 qL52R) (max qAs (max qSs (max qAsR qSsR)))) (max qPs qPsh))
      (Nat.ceil (Real.exp (max (max (3 * H) (18 / (7 * min δ δR)))
        (max (400 / min δ δR) (Real.exp (((6 : ℝ) / 7) ^ 2))))) + 1), ?_⟩
  intro q hq _inst χ₁ χ₂ χ₃ ρ₁ ρ₂ ρ₃ hR him0 hsq1 hsq2 hsq3 hprod hZ2 hZ3
    hne21 hne2i hne31 hne3i hne32 hne3ii hlam23 hlam3
  have hqL52 : qL52 ≤ q := by omega
  have hqL52R : qL52R ≤ q := by omega
  have hqAs : qAs ≤ q := by omega
  have hqSs : qSs ≤ q := by omega
  have hqAsR : qAsR ≤ q := by omega
  have hqSsR : qSsR ≤ q := by omega
  have hqPs : qPs ≤ q := by omega
  have hqPsh : qPsh ≤ q := by omega
  have hexpq : Nat.ceil (Real.exp (max (max (3 * H) (18 / (7 * min δ δR)))
      (max (400 / min δ δR) (Real.exp (((6 : ℝ) / 7) ^ 2))))) + 1 ≤ q := by omega
  have hMle : max (max (3 * H) (18 / (7 * min δ δR)))
      (max (400 / min δ δR) (Real.exp (((6 : ℝ) / 7) ^ 2))) ≤ Real.log (q : ℝ) :=
    ceil_exp_le_log_rect hexpq
  set L : ℝ := Real.log (q : ℝ) with hLdef
  have h3H : 3 * H ≤ L :=
    le_trans (le_trans (le_max_left _ _) (le_max_left _ _)) hMle
  have h18δ : 18 / (7 * min δ δR) ≤ L :=
    le_trans (le_trans (le_max_right _ _) (le_max_left _ _)) hMle
  have h400δ : 400 / min δ δR ≤ L :=
    le_trans (le_trans (le_max_left _ _) (le_max_right _ _)) hMle
  have hexp2 : Real.exp (((6 : ℝ) / 7) ^ 2) ≤ L :=
    le_trans (le_trans (le_max_right _ _) (le_max_right _ _)) hMle
  have hL1 : 1 ≤ L := by
    have h0 : (1:ℝ) ≤ Real.exp (((6 : ℝ) / 7) ^ 2) := Real.one_le_exp (by norm_num)
    linarith
  have hloglog : ((6 : ℝ) / 7) ^ 2 ≤ Real.log (Real.log (q : ℝ)) := by
    calc ((6 : ℝ) / 7) ^ 2 = Real.log (Real.exp (((6 : ℝ) / 7) ^ 2)) := (Real.log_exp _).symm
      _ ≤ Real.log (Real.log (q : ℝ)) :=
          Real.log_le_log (Real.exp_pos _) (by rw [← hLdef]; exact hexp2)
  have hloglog0 : 0 ≤ Real.log (Real.log (q : ℝ)) := le_trans (by norm_num) hloglog
  have hsqrt : (6 : ℝ) / 7 ≤ Real.sqrt (Real.log (Real.log (q : ℝ))) := by
    rw [Real.le_sqrt (by norm_num) hloglog0]
    exact hloglog
  have hlogq : 0 < Real.log (q : ℝ) := by
    have h1 : (1:ℝ) < Real.exp (((6 : ℝ) / 7) ^ 2) := Real.one_lt_exp_iff.mpr (by norm_num)
    linarith [hexp2, h1]
  have hδm0 : 0 < min δ δR := lt_min hδ0 hδR0
  have hδm1 : min δ δR < 1 := lt_of_le_of_lt (min_le_left _ _) hδ1
  set δm : ℝ := min δ δR with hδmdef
  have hδm_le_δ : δm ≤ δ := min_le_left _ _
  have hδm_le_δR : δm ≤ δR := min_le_right _ _
  have hδmhalf : (6 : ℝ) / 7 / L ≤ δm / 2 := by
    rw [div_le_iff₀ hlogq]
    have h := (div_le_iff₀ (by positivity : (0:ℝ) < 7 * δm)).mp h18δ
    nlinarith [h]
  set lam₁ : ℝ := Work.LinnikContract.lamOf q ρ₁ with hlam₁
  set lam₂ : ℝ := Work.LinnikContract.lamOf q ρ₂ with hlam₂
  set lam₃ : ℝ := Work.LinnikContract.lamOf q ρ₃ with hlam₃
  set γ₁ : ℝ := ρ₁.im with hγ₁
  set γ₂ : ℝ := ρ₂.im with hγ₂
  set γ₃ : ℝ := ρ₃.im with hγ₃
  set β : ℝ := 1 - lam₁ / L with hβ
  have hl1nn : 0 ≤ lam₁ := by
    rw [hlam₁]; exact lamOf_nonneg_of_zeroMult hR.1.2.1
  have hl2nn : 0 ≤ lam₂ := by
    rw [hlam₂]; exact lamOf_nonneg_of_zeroMult hZ2.2.1
  have hl3nn : 0 ≤ lam₃ := by
    rw [hlam₃]; exact lamOf_nonneg_of_zeroMult hZ3.2.1
  have hl12 : lam₁ ≤ lam₂ := by
    rw [hlam₁, hlam₂]
    exact hR.2 χ₂ ρ₂ ⟨hZ2.1, hZ2.2.1, le_trans hZ2.2.2 (by linarith [hH1])⟩
  have hl13 : lam₁ ≤ lam₃ := le_trans hl12 hlam23
  have hl16 : lam₁ ≤ 6 / 7 := le_trans hl13 hlam3
  have hγ1z : γ₁ = 0 := by rw [hγ₁]; exact him0
  have him0' : ρ₁.im = 0 := by rw [← hγ₁]; exact him0
  have hγ2L : |γ₂| ≤ H := by rw [hγ₂]; exact hZ2.2.2
  have hγ3L : |γ₃| ≤ H := by rw [hγ₃]; exact hZ3.2.2
  have hβ1 : |β - 1| = lam₁ / L := by
    rw [hβ, show 1 - lam₁ / L - 1 = -(lam₁ / L) by ring, abs_neg,
      abs_of_nonneg (div_nonneg hl1nn hlogq.le)]
  have hdivle : lam₁ / L ≤ Real.sqrt (Real.log (Real.log (q : ℝ))) / L :=
    div_le_div_of_nonneg_right (le_trans hl16 hsqrt) hlogq.le
  have hρ1re : ρ₁.re = β := by
    rw [hβ, hlam₁, Work.LinnikContract.lamOf]
    field_simp
    ring
  have hρ2re : ρ₂.re = 1 - lam₂ / L := by
    rw [hlam₂, Work.LinnikContract.lamOf]; field_simp; ring
  have hρ3re : ρ₃.re = 1 - lam₃ / L := by
    rw [hlam₃, Work.LinnikContract.lamOf]; field_simp; ring
  -- the range conditions at a point `β + iγ`
  have hrange : ∀ (γ : ℝ), |γ| ≤ 3 * H →
      |(((β : ℂ) + (γ : ℂ) * Complex.I).re - 1)| ≤
          Real.sqrt (Real.log (Real.log (q : ℝ))) / L ∧
      |(((β : ℂ) + (γ : ℂ) * Complex.I).im)| ≤ 10 * L ∧
      1 - Real.sqrt (Real.log (Real.log (q : ℝ))) / L ≤
        ((β : ℂ) + (γ : ℂ) * Complex.I).re := by
    intro γ hγ
    have hre : ((β : ℂ) + (γ : ℂ) * Complex.I).re = β := by simp
    have him : ((β : ℂ) + (γ : ℂ) * Complex.I).im = γ := by simp
    refine ⟨?_, ?_, ?_⟩
    · rw [hre, hβ1]; exact hdivle
    · rw [him]; linarith [hγ, h3H, hL1]
    · rw [hre, hβ]; linarith [hdivle, hsqrt, hlogq]
  -- the window condition, from the rectangle minimality of `ρ₁` (radius-parametric)
  have hwin : ∀ (χ : DirichletCharacter ℂ q) [NeZero χ.conductor], χ ≠ 1 → ∀ s : ℂ,
      s.re = β → |s.im| ≤ 3 * H → ∀ r : ℝ, r ≤ 1 →
      ∀ u : ℂ, (MeromorphicOn.divisor (DirichletCharacter.completedLFunction χ.primitiveCharacter)
          (Metric.closedBall 0 (|s.im| + 2))) u ≠ 0 →
        ‖(1:ℂ) + (s.im : ℂ) * Complex.I - u‖ ≤ r → u.re ≤ s.re := by
    intro χ _instc hχ s hs hsim r hr1 u hdiv hwu
    have hzm : Work.LinnikContract.zeroMult χ u ≠ 0 :=
      Work.ZeroFreeTables.OffAxis.zeroMult_ne_zero_of_divisor χ hχ hdiv
    have him1 : |s.im - u.im| ≤ r := by
      have h := Complex.abs_im_le_norm ((1:ℂ) + (s.im : ℂ) * Complex.I - u)
      have h' : (((1:ℂ) + (s.im : ℂ) * Complex.I - u).im) = s.im - u.im := by simp
      rw [h'] at h
      exact le_trans h hwu
    have him2 : |u.im| ≤ |s.im| + r := by
      calc |u.im| = |s.im - (s.im - u.im)| := by congr 1; ring
        _ ≤ |s.im| + |s.im - u.im| := abs_sub _ _
        _ ≤ |s.im| + r := by linarith
    have him3 : |u.im| ≤ 10 * H := by linarith [hsim, him2, hr1, hH1]
    have hZ : Work.ZeroFreeTables.IsZAt (10 * H) χ u := ⟨hχ, hzm, him3⟩
    have hle : Work.LinnikContract.lamOf q ρ₁ ≤ Work.LinnikContract.lamOf q u := hR.2 χ u hZ
    rw [← hlam₁, Work.LinnikContract.lamOf] at hle
    rw [hs, hβ]
    have h2 : lam₁ / L ≤ 1 - u.re := by
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
  haveI hci1 : NeZero (χ₁⁻¹).conductor := ⟨(χ₁⁻¹).conductor_ne_zero⟩
  haveI hci2 : NeZero (χ₂⁻¹).conductor := ⟨(χ₂⁻¹).conductor_ne_zero⟩
  haveI hci3 : NeZero (χ₃⁻¹).conductor := ⟨(χ₃⁻¹).conductor_ne_zero⟩
  -- non-principality of the auxiliary characters
  have hχ₁ne : χ₁ ≠ 1 := hR.1.1
  have hχ₂ne : χ₂ ≠ 1 := ne_one_of_sq_ne_one hsq2
  have hχ₃ne : χ₃ ≠ 1 := ne_one_of_sq_ne_one hsq3
  have h23 : χ₂ * χ₃ = χ₁ := by
    have h' : χ₁ * (χ₂ * χ₃) = 1 := by rwa [← mul_assoc]
    rw [eq_inv_of_mul_eq_one_right h', inv_eq_self_of_sq_eq_one hsq1]
  have hp12 : χ₁ * χ₂ ≠ 1 := by
    intro hh
    exact hχ₃ne (inv_eq_one.mp (by rw [← mul_eq_inv_of_mul_mul_eq_one hprod]; exact hh))
  have hp1i2 : χ₁ * χ₂⁻¹ ≠ 1 := by
    intro hh
    exact hχ₃ne (by rw [← mul_inv_eq_of_mul_mul_eq_one hprod hsq1]; exact hh)
  have hp13 : χ₁ * χ₃ ≠ 1 := by
    intro hh
    exact hχ₂ne (inv_eq_one.mp (by rw [← mul_eq_inv_of_mul_mul_eq_one' hprod hsq1]; exact hh))
  have hp1i3 : χ₁ * χ₃⁻¹ ≠ 1 := by
    intro hh
    exact hχ₂ne (by rw [← mul_inv_eq_of_mul_mul_eq_one' hprod hsq1]; exact hh)
  have hp23 : χ₂ * χ₃ ≠ 1 := by
    intro hh; exact hχ₁ne (by rw [← h23]; exact hh)
  have hp2i3 : χ₂ * χ₃⁻¹ ≠ 1 := (mul_mul_ne_one hprod hsq1 hχ₁ne hne32).2
  have ht12i3 : χ₁ * χ₂ * χ₃⁻¹ ≠ 1 := by
    intro hh
    apply hsq3
    have h1 : χ₃⁻¹ = χ₃ := by
      rw [eq_inv_of_mul_eq_one_right hh, mul_eq_inv_of_mul_mul_eq_one hprod, inv_inv]
    calc χ₃ ^ 2 = χ₃ * χ₃ := pow_two χ₃
      _ = χ₃ * χ₃⁻¹ := by rw [h1]
      _ = 1 := mul_inv_cancel χ₃
  have ht1i23 : χ₁ * χ₂⁻¹ * χ₃ ≠ 1 := by
    intro hh
    rw [mul_inv_eq_of_mul_mul_eq_one hprod hsq1, ← pow_two] at hh
    exact hsq3 hh
  have ht123i : χ₁⁻¹ * χ₂ * χ₃ = 1 := by
    rw [inv_eq_self_of_sq_eq_one hsq1]; exact hprod
  have hzm_c2inv : Work.LinnikContract.zeroMult χ₂⁻¹ ((starRingEnd ℂ) ρ₂) ≠ 0 := by
    rw [Work.A7.zeroMult_conj_inv]; exact hZ2.2.1
  have hzm_c3inv : Work.LinnikContract.zeroMult χ₃⁻¹ ((starRingEnd ℂ) ρ₃) ≠ 0 := by
    rw [Work.A7.zeroMult_conj_inv]; exact hZ3.2.1
  have hzm1 : Work.LinnikContract.zeroMult χ₁ ρ₁ ≠ 0 := hR.1.2.1
  have hconjρ2_re : ((starRingEnd ℂ) ρ₂).re = 1 - lam₂ / L := by
    rw [Complex.conj_re]; exact hρ2re
  have hconjρ2_im : ((starRingEnd ℂ) ρ₂).im = -γ₂ := by
    rw [Complex.conj_im, hγ₂]
    -- ===================== point bounds =====================
  -- the generic (no window zero) bound; needs only the range conditions and the window
  -- hypothesis `hwin`, which at the base `β` follows from the rectangle minimality of `ρ₁`
  have hself6 : ∀ (χ : DirichletCharacter ℂ q) [NeZero χ.conductor], χ ≠ 1 →
      ∀ (γ : ℝ), |γ| ≤ 3 * H →
      Work.ZeroFreeTables.Ksum q T.f L ((β : ℂ) + (γ : ℂ) * Complex.I) χ
        ≤ T.f 0 * (1/6 + ε') * L := by
    intro χ _instc hχ γ hγ
    obtain ⟨hr1, hr2, hr3⟩ := hrange γ hγ
    have hsre : (((β : ℂ) + (γ : ℂ) * Complex.I)).re = β := by simp
    have hsim : (((β : ℂ) + (γ : ℂ) * Complex.I)).im = γ := by simp
    exact hAs (q := q) hqAs χ hχ hr1 hr2 hr3 (hL52 q hqL52 χ hχ)
      (hwin χ hχ ((β : ℂ) + (γ : ℂ) * Complex.I) hsre (by rw [hsim]; exact hγ) δ (le_of_lt hδ1))
  have hself8 : ∀ (χ : DirichletCharacter ℂ q) [NeZero χ.conductor], χ ≠ 1 → χ * χ = 1 →
      ∀ (γ : ℝ), |γ| ≤ 3 * H →
      Work.ZeroFreeTables.Ksum q T.f L ((β : ℂ) + (γ : ℂ) * Complex.I) χ
        ≤ T.f 0 * (1/8 + ε') * L := by
    intro χ _instc hχ hreal γ hγ
    obtain ⟨hr1, hr2, hr3⟩ := hrange γ hγ
    have hsre : (((β : ℂ) + (γ : ℂ) * Complex.I)).re = β := by simp
    have hsim : (((β : ℂ) + (γ : ℂ) * Complex.I)).im = γ := by simp
    exact hAsR (q := q) hqAsR χ hχ hr1 hr2 hr3 (hL52R q hqL52R χ hχ hreal)
      (hwin χ hχ ((β : ℂ) + (γ : ℂ) * Complex.I) hsre (by rw [hsim]; exact hγ) δR (le_of_lt hδR1))
  -- the extraction bound at `c = 1/6`
  have hextract6 : ∀ (χ : DirichletCharacter ℂ q) [NeZero χ.conductor], χ ≠ 1 →
      ∀ (γ : ℝ), |γ| ≤ 3 * H → ∀ (ρ : ℂ) (lam t m : ℝ), lam = Work.LinnikContract.lamOf q ρ → t = lam - lam₁ →
      m = (γ - ρ.im) * L →
      Work.LinnikContract.zeroMult χ ρ ≠ 0 →
      ‖(1:ℂ) + (γ : ℂ) * Complex.I - ρ‖ ≤ δ →
      Work.ZeroFreeTables.Ksum q T.f L ((β : ℂ) + (γ : ℂ) * Complex.I) χ
        ≤ -(L) * (T.Fc ((t : ℝ) + (m : ℝ) * Complex.I)).re
          + T.f 0 * (1/6 + ε') * L := by
    intro χ _instc hχ γ hγ ρ lam t m hlam ht hm hzm hwinρ
    obtain ⟨hr1, hr2, hr3⟩ := hrange γ hγ
    have him : |γ - ρ.im| ≤ δ := by
      have h := Complex.abs_im_le_norm ((1:ℂ) + (γ : ℂ) * Complex.I - ρ)
      have h' : (((1:ℂ) + (γ : ℂ) * Complex.I - ρ).im) = γ - ρ.im := by simp
      rw [h'] at h
      exact le_trans h hwinρ
    have him2 : |ρ.im| ≤ |γ| + δ := by
      calc |ρ.im| = |γ - (γ - ρ.im)| := by congr 1; ring
        _ ≤ |γ| + |γ - ρ.im| := abs_sub _ _
        _ ≤ |γ| + δ := by linarith
    have hmem : ρ ∈ Metric.closedBall (0:ℂ) (|γ| + 2) := by
      rw [Metric.mem_closedBall, dist_zero_right]
      have h1 : |ρ.re| ≤ 1 := zeroMult_abs_re_le_one hχ hzm
      calc ‖ρ‖ ≤ |ρ.re| + |ρ.im| := Complex.norm_le_abs_re_add_abs_im ρ
        _ ≤ |γ| + 2 := by linarith [h1, him2, hδ1, abs_nonneg γ]
    have hdiv : (MeromorphicOn.divisor (DirichletCharacter.completedLFunction χ.primitiveCharacter)
        (Metric.closedBall 0 (|((β : ℂ) + (γ : ℂ) * Complex.I).im| + 2))) ρ ≠ 0 := by
      have hsim : (((β : ℂ) + (γ : ℂ) * Complex.I).im) = γ := by simp
      rw [hsim]
      exact Work.ZeroFreeTables.OffAxis.divisor_ne_zero_of_zeroMult χ hχ hmem hzm
    have hsre : (((β : ℂ) + (γ : ℂ) * Complex.I)).re = β := by simp
    have hsim : (((β : ℂ) + (γ : ℂ) * Complex.I)).im = γ := by simp
    have hwinρ' : ‖(1:ℂ) + ((((β : ℂ) + (γ : ℂ) * Complex.I).im : ℂ)) * Complex.I - ρ‖ ≤ δ := by
      rw [hsim]; exact hwinρ
    have h := hSs (q := q) hqSs χ hχ hr1 hr2 hr3 (hL52 q hqL52 χ hχ) hdiv hwinρ'
      (hwin χ hχ ((β : ℂ) + (γ : ℂ) * Complex.I) hsre (by rw [hsim]; exact hγ) δ (le_of_lt hδ1))
    have hz : (((β : ℂ) + (γ : ℂ) * Complex.I) - ρ) * ((L : ℝ) : ℂ)
        = ((t : ℝ) : ℂ) + ((m : ℝ) : ℂ) * Complex.I := by
      have hρre : ρ.re = 1 - lam / L := by
        rw [hlam, Work.LinnikContract.lamOf]; field_simp; ring
      have h1 : (((β:ℂ) + (γ:ℂ)*Complex.I) - ρ).re = β - ρ.re := by simp
      have h2 : (((β:ℂ) + (γ:ℂ)*Complex.I) - ρ).im = γ - ρ.im := by simp
      apply Complex.ext
      · rw [Complex.mul_re, h1]
        simp only [Complex.add_re, Complex.ofReal_re, Complex.ofReal_im, Complex.mul_re,
          Complex.mul_im, Complex.I_re, Complex.I_im, mul_zero, mul_one, sub_zero, add_zero, sub_self]
        rw [hβ, hρre, ht]
        field_simp
        ring
      · rw [Complex.mul_im, h2]
        simp only [Complex.add_im, Complex.ofReal_re, Complex.ofReal_im, Complex.mul_re,
          Complex.mul_im, Complex.I_re, Complex.I_im, mul_zero, mul_one, sub_zero, zero_mul,
          add_zero, zero_add]
        rw [hm]
    rw [← T.Fc_spec] at h
    rw [hz] at h
    exact h
  -- the extraction bound at `c = 1/8` (real characters)
  have hextract8 : ∀ (χ : DirichletCharacter ℂ q) [NeZero χ.conductor], χ ≠ 1 → χ * χ = 1 →
      ∀ (γ : ℝ), |γ| ≤ 3 * H → ∀ (ρ : ℂ) (lam t m : ℝ), lam = Work.LinnikContract.lamOf q ρ → t = lam - lam₁ →
      m = (γ - ρ.im) * L →
      Work.LinnikContract.zeroMult χ ρ ≠ 0 →
      ‖(1:ℂ) + (γ : ℂ) * Complex.I - ρ‖ ≤ δR →
      Work.ZeroFreeTables.Ksum q T.f L ((β : ℂ) + (γ : ℂ) * Complex.I) χ
        ≤ -(L) * (T.Fc ((t : ℝ) + (m : ℝ) * Complex.I)).re
          + T.f 0 * (1/8 + ε') * L := by
    intro χ _instc hχ hreal γ hγ ρ lam t m hlam ht hm hzm hwinρ
    obtain ⟨hr1, hr2, hr3⟩ := hrange γ hγ
    have him : |γ - ρ.im| ≤ δR := by
      have h := Complex.abs_im_le_norm ((1:ℂ) + (γ : ℂ) * Complex.I - ρ)
      have h' : (((1:ℂ) + (γ : ℂ) * Complex.I - ρ).im) = γ - ρ.im := by simp
      rw [h'] at h
      exact le_trans h hwinρ
    have him2 : |ρ.im| ≤ |γ| + δR := by
      calc |ρ.im| = |γ - (γ - ρ.im)| := by congr 1; ring
        _ ≤ |γ| + |γ - ρ.im| := abs_sub _ _
        _ ≤ |γ| + δR := by linarith
    have hmem : ρ ∈ Metric.closedBall (0:ℂ) (|γ| + 2) := by
      rw [Metric.mem_closedBall, dist_zero_right]
      have h1 : |ρ.re| ≤ 1 := zeroMult_abs_re_le_one hχ hzm
      calc ‖ρ‖ ≤ |ρ.re| + |ρ.im| := Complex.norm_le_abs_re_add_abs_im ρ
        _ ≤ |γ| + 2 := by linarith [h1, him2, hδR1, abs_nonneg γ]
    have hdiv : (MeromorphicOn.divisor (DirichletCharacter.completedLFunction χ.primitiveCharacter)
        (Metric.closedBall 0 (|((β : ℂ) + (γ : ℂ) * Complex.I).im| + 2))) ρ ≠ 0 := by
      have hsim : (((β : ℂ) + (γ : ℂ) * Complex.I).im) = γ := by simp
      rw [hsim]
      exact Work.ZeroFreeTables.OffAxis.divisor_ne_zero_of_zeroMult χ hχ hmem hzm
    have hsre : (((β : ℂ) + (γ : ℂ) * Complex.I)).re = β := by simp
    have hsim : (((β : ℂ) + (γ : ℂ) * Complex.I)).im = γ := by simp
    have hwinρ' : ‖(1:ℂ) + ((((β : ℂ) + (γ : ℂ) * Complex.I).im : ℂ)) * Complex.I - ρ‖ ≤ δR := by
      rw [hsim]; exact hwinρ
    have h := hSsR (q := q) hqSsR χ hχ hr1 hr2 hr3 (hL52R q hqL52R χ hχ hreal) hdiv hwinρ'
      (hwin χ hχ ((β : ℂ) + (γ : ℂ) * Complex.I) hsre (by rw [hsim]; exact hγ) δR (le_of_lt hδR1))
    have hz : (((β : ℂ) + (γ : ℂ) * Complex.I) - ρ) * ((L : ℝ) : ℂ)
        = ((t : ℝ) : ℂ) + ((m : ℝ) : ℂ) * Complex.I := by
      have hρre : ρ.re = 1 - lam / L := by
        rw [hlam, Work.LinnikContract.lamOf]; field_simp; ring
      have h1 : (((β:ℂ) + (γ:ℂ)*Complex.I) - ρ).re = β - ρ.re := by simp
      have h2 : (((β:ℂ) + (γ:ℂ)*Complex.I) - ρ).im = γ - ρ.im := by simp
      apply Complex.ext
      · rw [Complex.mul_re, h1]
        simp only [Complex.add_re, Complex.ofReal_re, Complex.ofReal_im, Complex.mul_re,
          Complex.mul_im, Complex.I_re, Complex.I_im, mul_zero, mul_one, sub_zero, add_zero, sub_self]
        rw [hβ, hρre, ht]
        field_simp
        ring
      · rw [Complex.mul_im, h2]
        simp only [Complex.add_im, Complex.ofReal_re, Complex.ofReal_im, Complex.mul_re,
          Complex.mul_im, Complex.I_re, Complex.I_im, mul_zero, mul_one, sub_zero, zero_mul,
          add_zero, zero_add]
        rw [hm]
    rw [← T.Fc_spec] at h
    rw [hz] at h
    exact h
  -- the norm bound `a² + b² ≤ c² ⟹ ‖a + bi‖ ≤ c`
  have hnorm_le : ∀ (a b c : ℝ), a^2 + b^2 ≤ c^2 → 0 < c →
      ‖((a : ℝ) : ℂ) + ((b : ℝ) : ℂ) * Complex.I‖ ≤ c := by
    intro a b c h hc
    have hz2 : ‖((a : ℝ) : ℂ) + ((b : ℝ) : ℂ) * Complex.I‖^2 ≤ c^2 := by
      rw [Complex.sq_norm, Complex.normSq_apply]
      simp only [Complex.add_re, Complex.add_im, Complex.ofReal_re, Complex.ofReal_im,
        Complex.mul_re, Complex.mul_im, Complex.I_re, Complex.I_im, mul_zero, mul_one,
        sub_zero, add_zero]
      nlinarith [h]
    nlinarith [norm_nonneg (((a : ℝ) : ℂ) + ((b : ℝ) : ℂ) * Complex.I), hz2, hc]
  have hwinb : ∀ (l b : ℝ), 0 ≤ l → l ≤ 6/7 → |b| ≤ δm / 2 →
      ‖((l / L : ℝ) : ℂ) + ((b : ℝ) : ℂ) * Complex.I‖ ≤ δm := by
    intro l b hl0 hl67 hb
    have hlL : l / L ≤ δm / 2 := le_trans (div_le_div_of_nonneg_right hl67 hlogq.le) hδmhalf
    have h1 : (l / L)^2 ≤ (δm / 2)^2 := by
      nlinarith [hlL, div_nonneg hl0 hlogq.le, hδm0]
    have h2 : b^2 ≤ (δm / 2)^2 := by nlinarith [abs_le.mp hb, hδm0]
    refine hnorm_le _ _ _ ?_ (by linarith [hδm0])
    nlinarith [h1, h2, hδm0]
  have h9L : (9/7 : ℝ) / L ≤ δm / 2 := by
    rw [div_le_iff₀ hlogq]
    have h := (div_le_iff₀ (by positivity : (0:ℝ) < 7 * δm)).mp h18δ
    nlinarith [h]
  have h200L : (200:ℝ) / L ≤ δm / 2 := by
    rw [div_le_iff₀ hlogq]
    have h := (div_le_iff₀ (by positivity : (0:ℝ) < δm)).mp h400δ
    nlinarith [h]
  -- the vector identity `1 + gi - ρ = (l/L) + (g - ρ.im)i`
  have hvecid : ∀ (g l : ℝ) (ρ : ℂ), ρ.re = 1 - l / L →
      (1:ℂ) + (g : ℂ) * Complex.I - ρ
        = ((l / L : ℝ) : ℂ) + (((g - ρ.im) : ℝ) : ℂ) * Complex.I := by
    intro g l ρ hρre
    apply Complex.ext
    · simp only [Complex.sub_re, Complex.add_re, Complex.one_re, Complex.ofReal_re,
        Complex.mul_re, Complex.mul_im, Complex.ofReal_im, Complex.I_re, Complex.I_im,
        mul_one, mul_zero, sub_zero, zero_mul, add_zero]
      rw [hρre]
      field_simp
      ring
    · simp only [Complex.sub_im, Complex.add_im, Complex.one_im, Complex.ofReal_im,
        Complex.mul_re, Complex.mul_im, Complex.ofReal_re, Complex.I_re, Complex.I_im,
        mul_one, mul_zero, sub_zero, zero_mul, add_zero]
      ring
  have hbμ : ∀ (m₀ : ℝ), |(γ₂ + γ₃) * L| ≤ m₀ → m₀ / L ≤ δm / 2 → |γ₂ + γ₃| ≤ δm / 2 := by
    intro m₀ hμ hm
    have h1 : γ₂ + γ₃ = ((γ₂ + γ₃) * L) / L := by field_simp
    rw [h1, abs_div, abs_of_pos hlogq]
    exact le_trans (div_le_div_of_nonneg_right hμ hlogq.le) hm
  -- ===================== the slots of the ledger =====================
  -- the pole term (the principal character at `β`)
  have hbP : Work.ZeroFreeTables.Ksum q T.f L (β : ℂ) 1 ≤ L * T.F (-lam₁) + T.f 0 * ε' * L := by
    have hcond : lam₁ = Real.log (q : ℝ) * (1 - β) := by
      rw [hβ, ← hLdef]
      field_simp
      ring
    have h := hPs (q := q) hqPs (β := β) (lam := lam₁) hcond (by rw [hβ1]; exact hdivle)
    have hFint : T.F (-lam₁) = ∫ t in (0:ℝ)..T.x₀, Real.exp (lam₁ * t) * T.f t := by
      rw [Work.ZeroFreeTables.TestFn_F_eq_integral]
      apply intervalIntegral.integral_congr
      intro t _
      simp only [neg_mul, neg_neg]
    rw [hFint]
    exact h
  -- the principal triple (the character `1` at height `γ₂ + γ₃`)
  have hbTrip : Work.ZeroFreeTables.Ksum q T.f L
        ((β : ℂ) + (((γ₂ + γ₃) : ℝ) : ℂ) * Complex.I) 1
      ≤ L * (T.Fc (((-lam₁ : ℝ) : ℂ) + (((γ₂ + γ₃) * L : ℝ) : ℂ) * Complex.I)).re
        + T.f 0 * ε' * L := by
    have h23 : |γ₂ + γ₃| ≤ 2 * H := by linarith [abs_add_le γ₂ γ₃, hγ2L, hγ3L]
    have hm1 : ((β : ℂ) + (((γ₂ + γ₃) : ℝ) : ℂ) * Complex.I).re = β := by simp
    have hm2 : ((β : ℂ) + (((γ₂ + γ₃) : ℝ) : ℂ) * Complex.I).im = γ₂ + γ₃ := by simp
    have hs := hPsh (q := q) hqPsh ((β : ℂ) + (((γ₂ + γ₃) : ℝ) : ℂ) * Complex.I)
      (by rw [hm1, hβ1]; exact hdivle)
      (by rw [hm2]; linarith [h23, h3H, hH1])
    rw [show (((β : ℂ) + (((γ₂ + γ₃) : ℝ) : ℂ) * Complex.I) - 1) * ((L : ℝ) : ℂ)
        = (((-lam₁ : ℝ) : ℂ) + (((γ₂ + γ₃) * L : ℝ) : ℂ) * Complex.I) from
        sub_one_mul_log hlogq.ne' hβ] at hs
    rw [← T.Fc_spec] at hs
    exact hs
  -- the three single extractions
  have hbS1 : Work.ZeroFreeTables.Ksum q T.f L (β : ℂ) χ₁
      ≤ -(L) * T.F 0 + T.f 0 * (1/8 + ε') * L := by
    have hγ10 : |γ₁| ≤ 3 * H := by rw [hγ1z, abs_zero]; linarith [hH1]
    have hw : ‖(1:ℂ) + (γ₁ : ℂ) * Complex.I - ρ₁‖ ≤ δR := by
      have h1 := hvecid γ₁ lam₁ ρ₁ hρ1re
      rw [show γ₁ - ρ₁.im = 0 by rw [hγ1z, him0']; ring] at h1
      rw [h1]
      exact le_trans (hwinb lam₁ 0 hl1nn hl16 (by rw [abs_zero]; linarith [hδm0])) hδm_le_δR
    have hchi : χ₁ * χ₁ = 1 := by simpa [pow_two] using hsq1
    have h := hextract8 χ₁ hχ₁ne hchi γ₁ hγ10 ρ₁ lam₁ (lam₁ - lam₁) (0:ℝ) hlam₁ rfl
      (by rw [hγ1z, him0']; ring) hzm1 hw
    rw [show (β : ℂ) + (γ₁ : ℂ) * Complex.I = (β : ℂ) by rw [hγ1z]; simp] at h
    simpa [Work.ZeroFreeTables.TestFn.F] using h
  have hbS2 : Work.ZeroFreeTables.Ksum q T.f L ((β : ℂ) + (γ₂ : ℂ) * Complex.I) χ₂
      ≤ -(L) * T.F (lam₂ - lam₁) + T.f 0 * (1/6 + ε') * L := by
    have hγ2c : |γ₂| ≤ 3 * H := by linarith [hγ2L, hH1]
    have hw : ‖(1:ℂ) + (γ₂ : ℂ) * Complex.I - ρ₂‖ ≤ δ := by
      have h1 := hvecid γ₂ lam₂ ρ₂ hρ2re
      rw [show γ₂ - ρ₂.im = 0 by rw [← hγ₂]; ring] at h1
      rw [h1]
      exact le_trans (hwinb lam₂ 0 hl2nn (by linarith [hlam23, hlam3]) (by rw [abs_zero]; linarith [hδm0])) hδm_le_δ
    have h := hextract6 χ₂ hχ₂ne γ₂ hγ2c ρ₂ lam₂ (lam₂ - lam₁) (0:ℝ) hlam₂ rfl
      (by rw [← hγ₂]; ring) hZ2.2.1 hw
    simpa [Work.ZeroFreeTables.TestFn.F] using h
  have hbS3 : Work.ZeroFreeTables.Ksum q T.f L ((β : ℂ) + (γ₃ : ℂ) * Complex.I) χ₃
      ≤ -(L) * T.F (lam₃ - lam₁) + T.f 0 * (1/6 + ε') * L := by
    have hγ3c : |γ₃| ≤ 3 * H := by linarith [hγ3L, hH1]
    have hw : ‖(1:ℂ) + (γ₃ : ℂ) * Complex.I - ρ₃‖ ≤ δ := by
      have h1 := hvecid γ₃ lam₃ ρ₃ hρ3re
      rw [show γ₃ - ρ₃.im = 0 by rw [← hγ₃]; ring] at h1
      rw [h1]
      exact le_trans (hwinb lam₃ 0 hl3nn hlam3 (by rw [abs_zero]; linarith [hδm0])) hδm_le_δ
    have h := hextract6 χ₃ hχ₃ne γ₃ hγ3c ρ₃ lam₃ (lam₃ - lam₁) (0:ℝ) hlam₃ rfl
      (by rw [← hγ₃]; ring) hZ3.2.1 hw
    simpa [Work.ZeroFreeTables.TestFn.F] using h
  -- the generic pair `χ₂χ₃⁻¹` at height `γ₂ - γ₃` and the generic triples
  have hbP9 : Work.ZeroFreeTables.Ksum q T.f L
        ((β : ℂ) + (((γ₂ - γ₃) : ℝ) : ℂ) * Complex.I) (χ₂ * χ₃⁻¹)
      ≤ T.f 0 * (1/6 + ε') * L := by
    have h := hself6 (χ₂ * χ₃⁻¹) hp2i3 (γ₂ - γ₃) (by
      calc |γ₂ - γ₃| ≤ |γ₂| + |γ₃| := by simpa [sub_eq_add_neg] using abs_add_le γ₂ (-γ₃)
        _ ≤ 3 * H := by linarith [hγ2L, hγ3L, hH1])
    simpa only [Complex.ofReal_sub, Complex.ofReal_add, Complex.ofReal_neg] using h
  have hbT11 : Work.ZeroFreeTables.Ksum q T.f L
        ((β : ℂ) + (((γ₂ - γ₃) : ℝ) : ℂ) * Complex.I) (χ₁ * χ₂ * χ₃⁻¹)
      ≤ T.f 0 * (1/6 + ε') * L := by
    have h := hself6 (χ₁ * χ₂ * χ₃⁻¹) ht12i3 (γ₂ - γ₃) (by
      calc |γ₂ - γ₃| ≤ |γ₂| + |γ₃| := by simpa [sub_eq_add_neg] using abs_add_le γ₂ (-γ₃)
        _ ≤ 3 * H := by linarith [hγ2L, hγ3L, hH1])
    simpa only [Complex.ofReal_sub, Complex.ofReal_add, Complex.ofReal_neg] using h
  have hbT12 : Work.ZeroFreeTables.Ksum q T.f L
        ((β : ℂ) + (((-γ₂ + γ₃) : ℝ) : ℂ) * Complex.I) (χ₁ * χ₂⁻¹ * χ₃)
      ≤ T.f 0 * (1/6 + ε') * L := by
    have h := hself6 (χ₁ * χ₂⁻¹ * χ₃) ht1i23 (-γ₂ + γ₃) (by
      calc |-γ₂ + γ₃| ≤ |γ₂| + |γ₃| := by
            simpa [neg_add_eq_sub, sub_eq_add_neg, add_comm] using abs_add_le (-γ₂) γ₃
        _ ≤ 3 * H := by linarith [hγ2L, hγ3L, hH1])
    simpa only [Complex.ofReal_sub, Complex.ofReal_add, Complex.ofReal_neg] using h
  -- ===================== the ledger =====================
  have hpos := Work.ZeroFreeTables.Ksum_positivity_three (f := T.f) (fun t => T.f_nonneg t)
    (x₀ := T.x₀) (L := L) (β := β) (γ₁ := 0) (γ₂ := γ₂) (γ₃ := γ₃)
    T.x₀_pos hlogq T.f_supp χ₁ χ₂ χ₃
  -- the vector identities relating the window points to the canonical form
  have hv4 : (1:ℂ) + (((γ₂ : ℝ)) : ℂ) * Complex.I - (starRingEnd ℂ) ρ₃
      = (((lam₃ / L : ℝ)) : ℂ) + (((γ₂ + γ₃ : ℝ)) : ℂ) * Complex.I := by
    apply Complex.ext
    · simp only [Complex.add_re, Complex.sub_re, Complex.one_re, Complex.ofReal_re,
        Complex.ofReal_im, Complex.mul_re, Complex.mul_im, Complex.I_re, Complex.I_im,
        Complex.conj_re, Complex.conj_im, mul_zero, mul_one, sub_zero, add_zero, sub_self]
      rw [hρ3re]
      field_simp
      ring
    · simp only [Complex.add_im, Complex.sub_im, Complex.one_im, Complex.ofReal_re,
        Complex.ofReal_im, Complex.mul_re, Complex.mul_im, Complex.I_re, Complex.I_im,
        Complex.conj_re, Complex.conj_im, mul_zero, mul_one, sub_zero, add_zero, zero_add,
        zero_mul, neg_zero, sub_self]
      rw [hγ₃]
      ring

  have hv5 : (1:ℂ) + (((-γ₂ : ℝ)) : ℂ) * Complex.I - ρ₃
      = (((lam₃ / L : ℝ)) : ℂ) + (((-(γ₂ + γ₃) : ℝ)) : ℂ) * Complex.I := by
    apply Complex.ext
    · simp only [Complex.add_re, Complex.sub_re, Complex.one_re, Complex.ofReal_re,
        Complex.ofReal_im, Complex.mul_re, Complex.mul_im, Complex.I_re, Complex.I_im,
        Complex.conj_re, Complex.conj_im, mul_zero, mul_one, sub_zero, add_zero, sub_self]
      rw [hρ3re]
      field_simp
      ring
    · simp only [Complex.add_im, Complex.sub_im, Complex.one_im, Complex.ofReal_re,
        Complex.ofReal_im, Complex.mul_re, Complex.mul_im, Complex.I_re, Complex.I_im,
        Complex.conj_re, Complex.conj_im, mul_zero, mul_one, sub_zero, add_zero, zero_add,
        zero_mul, neg_zero, sub_self]
      rw [hγ₃]
      ring

  have hv6 : (1:ℂ) + (((γ₃ : ℝ)) : ℂ) * Complex.I - (starRingEnd ℂ) ρ₂
      = (((lam₂ / L : ℝ)) : ℂ) + (((γ₂ + γ₃ : ℝ)) : ℂ) * Complex.I := by
    apply Complex.ext
    · simp only [Complex.add_re, Complex.sub_re, Complex.one_re, Complex.ofReal_re,
        Complex.ofReal_im, Complex.mul_re, Complex.mul_im, Complex.I_re, Complex.I_im,
        Complex.conj_re, Complex.conj_im, mul_zero, mul_one, sub_zero, add_zero, sub_self]
      rw [hρ2re]
      field_simp
      ring
    · simp only [Complex.add_im, Complex.sub_im, Complex.one_im, Complex.ofReal_re,
        Complex.ofReal_im, Complex.mul_re, Complex.mul_im, Complex.I_re, Complex.I_im,
        Complex.conj_re, Complex.conj_im, mul_zero, mul_one, sub_zero, add_zero, zero_add,
        zero_mul, neg_zero, sub_self]
      rw [hγ₂]
      ring

  have hv7 : (1:ℂ) + (((-γ₃ : ℝ)) : ℂ) * Complex.I - ρ₂
      = (((lam₂ / L : ℝ)) : ℂ) + (((-(γ₂ + γ₃) : ℝ)) : ℂ) * Complex.I := by
    apply Complex.ext
    · simp only [Complex.add_re, Complex.sub_re, Complex.one_re, Complex.ofReal_re,
        Complex.ofReal_im, Complex.mul_re, Complex.mul_im, Complex.I_re, Complex.I_im,
        Complex.conj_re, Complex.conj_im, mul_zero, mul_one, sub_zero, add_zero, sub_self]
      rw [hρ2re]
      field_simp
      ring
    · simp only [Complex.add_im, Complex.sub_im, Complex.one_im, Complex.ofReal_re,
        Complex.ofReal_im, Complex.mul_re, Complex.mul_im, Complex.I_re, Complex.I_im,
        Complex.conj_re, Complex.conj_im, mul_zero, mul_one, sub_zero, add_zero, zero_add,
        zero_mul, neg_zero, sub_self]
      rw [hγ₂]
      ring

  have hv8 : (1:ℂ) + (((γ₂ + γ₃ : ℝ)) : ℂ) * Complex.I - ρ₁
      = (((lam₁ / L : ℝ)) : ℂ) + (((γ₂ + γ₃ : ℝ)) : ℂ) * Complex.I := by
    apply Complex.ext
    · simp only [Complex.add_re, Complex.sub_re, Complex.one_re, Complex.ofReal_re,
        Complex.ofReal_im, Complex.mul_re, Complex.mul_im, Complex.I_re, Complex.I_im,
        Complex.conj_re, Complex.conj_im, mul_zero, mul_one, sub_zero, add_zero, sub_self]
      rw [hρ1re, hβ]
      field_simp
      ring
    · simp only [Complex.add_im, Complex.sub_im, Complex.one_im, Complex.ofReal_re,
        Complex.ofReal_im, Complex.mul_re, Complex.mul_im, Complex.I_re, Complex.I_im,
        Complex.conj_re, Complex.conj_im, mul_zero, mul_one, sub_zero, add_zero, zero_add,
        zero_mul, neg_zero, sub_self]
      rw [him0']
      ring

  have hdiv67 : ∀ (l : ℝ), l ≤ 6/7 → l / L ≤ 6/7 := by
    intro l hl
    rw [div_le_iff₀ hlogq]
    nlinarith [hl, hL1]
  have hw4 : |(γ₂ + γ₃) * L| ≤ 9/7 →
      ‖(1:ℂ) + (((γ₂ : ℝ)) : ℂ) * Complex.I - (starRingEnd ℂ) ρ₃‖ ≤ δ := by
    intro hμ
    rw [hv4]
    refine le_trans (hwinb lam₃ (γ₂ + γ₃) hl3nn (le_trans hlam3 (by norm_num)) (hbμ (9/7) hμ h9L)) hδm_le_δ
  have hw5 : |(γ₂ + γ₃) * L| ≤ 9/7 →
      ‖(1:ℂ) + (((-γ₂ : ℝ)) : ℂ) * Complex.I - ρ₃‖ ≤ δ := by
    intro hμ
    rw [hv5]
    refine le_trans (hwinb lam₃ (-(γ₂ + γ₃)) hl3nn (le_trans hlam3 (by norm_num)) (by rw [abs_neg]; exact hbμ (9/7) hμ h9L))
      hδm_le_δ
  have hw6 : |(γ₂ + γ₃) * L| ≤ 9/7 →
      ‖(1:ℂ) + (((γ₃ : ℝ)) : ℂ) * Complex.I - (starRingEnd ℂ) ρ₂‖ ≤ δ := by
    intro hμ
    rw [hv6]
    refine le_trans (hwinb lam₂ (γ₂ + γ₃) hl2nn (by linarith [hlam23, hlam3]) (hbμ (9/7) hμ h9L)) hδm_le_δ
  have hw7 : |(γ₂ + γ₃) * L| ≤ 9/7 →
      ‖(1:ℂ) + (((-γ₃ : ℝ)) : ℂ) * Complex.I - ρ₂‖ ≤ δ := by
    intro hμ
    rw [hv7]
    refine le_trans (hwinb lam₂ (-(γ₂ + γ₃)) hl2nn (by linarith [hlam23, hlam3]) (by rw [abs_neg]; exact hbμ (9/7) hμ h9L))
      hδm_le_δ
  have hw8 : |(γ₂ + γ₃) * L| ≤ 9/7 →
      ‖(1:ℂ) + (((γ₂ + γ₃ : ℝ)) : ℂ) * Complex.I - ρ₁‖ ≤ δR := by
    intro hμ
    rw [hv8]
    refine le_trans (hwinb lam₁ (γ₂ + γ₃) hl1nn hl16 (hbμ (9/7) hμ h9L)) hδm_le_δR
  have hw8b : |(γ₂ + γ₃) * L| ≤ 200 →
      ‖(1:ℂ) + (((γ₂ + γ₃ : ℝ)) : ℂ) * Complex.I - ρ₁‖ ≤ δR := by
    intro hμ
    rw [hv8]
    refine le_trans (hwinb lam₁ (γ₂ + γ₃) hl1nn hl16 (hbμ 200 hμ h200L)) hδm_le_δR
  -- ===================== the five pair bounds =====================
  have hpair4' : ‖(1:ℂ) + (γ₂ : ℂ) * Complex.I - (starRingEnd ℂ) ρ₃‖ ≤ δ →
      Work.ZeroFreeTables.Ksum q T.f L ((β : ℂ) + (γ₂ : ℂ) * Complex.I) (χ₁ * χ₂)
        ≤ -(L) * (T.Fc ((lam₃ - lam₁ : ℝ) + (((γ₂ + γ₃) * L : ℝ) : ℂ) * Complex.I)).re
          + T.f 0 * (1/6 + ε') * L := by
    intro hw
    have hz : Work.LinnikContract.zeroMult (χ₁ * χ₂) ((starRingEnd ℂ) ρ₃) ≠ 0 := by
      rw [show χ₁ * χ₂ = χ₃⁻¹ by rw [mul_eq_inv_of_mul_mul_eq_one hprod]]
      exact hzm_c3inv
    have h := hextract6 (χ₁ * χ₂) hp12 γ₂ (by linarith [hγ2L, hH1])
      ((starRingEnd ℂ) ρ₃) lam₃ (lam₃ - lam₁) ((γ₂ + γ₃) * L)
      (by simpa [Work.OffAxis.lamOf_star] using hlam₃)
      rfl (by rw [Complex.conj_im, hγ₃]; ring) hz hw
    exact h
  have hpair5' : ‖(1:ℂ) + (((-γ₂ : ℝ)) : ℂ) * Complex.I - ρ₃‖ ≤ δ →
      Work.ZeroFreeTables.Ksum q T.f L ((β : ℂ) + (((-γ₂ : ℝ)) : ℂ) * Complex.I) (χ₁ * χ₂⁻¹)
        ≤ -(L) * (T.Fc ((lam₃ - lam₁ : ℝ) + (((γ₂ + γ₃) * L : ℝ) : ℂ) * Complex.I)).re
          + T.f 0 * (1/6 + ε') * L := by
    intro hw
    have hz : Work.LinnikContract.zeroMult (χ₁ * χ₂⁻¹) ρ₃ ≠ 0 := by
      rw [show χ₁ * χ₂⁻¹ = χ₃ by rw [mul_inv_eq_of_mul_mul_eq_one hprod hsq1]]
      exact hZ3.2.1
    have h := hextract6 (χ₁ * χ₂⁻¹) hp1i2 (-γ₂) (by rw [abs_neg]; linarith [hγ2L, hH1])
      ρ₃ lam₃ (lam₃ - lam₁) (((-γ₂) - ρ₃.im) * L) hlam₃ rfl rfl hz hw
    rw [show ((-γ₂) - ρ₃.im) * L = -((γ₂ + γ₃) * L) by rw [hγ₃]; ring] at h
    rw [show ((lam₃ - lam₁ : ℝ) : ℂ) + ((-((γ₂ + γ₃) * L) : ℝ) : ℂ) * Complex.I
        = starRingEnd ℂ (((lam₃ - lam₁ : ℝ) : ℂ) + (((γ₂ + γ₃) * L : ℝ) : ℂ) * Complex.I) by
      apply Complex.ext <;> simp] at h
    rw [TestFn_Fc_conj, Complex.conj_re] at h
    exact h
  have hpair6' : ‖(1:ℂ) + (γ₃ : ℂ) * Complex.I - (starRingEnd ℂ) ρ₂‖ ≤ δ →
      Work.ZeroFreeTables.Ksum q T.f L ((β : ℂ) + (γ₃ : ℂ) * Complex.I) (χ₁ * χ₃)
        ≤ -(L) * (T.Fc ((lam₂ - lam₁ : ℝ) + (((γ₂ + γ₃) * L : ℝ) : ℂ) * Complex.I)).re
          + T.f 0 * (1/6 + ε') * L := by
    intro hw
    have hz : Work.LinnikContract.zeroMult (χ₁ * χ₃) ((starRingEnd ℂ) ρ₂) ≠ 0 := by
      rw [show χ₁ * χ₃ = χ₂⁻¹ by rw [mul_eq_inv_of_mul_mul_eq_one' hprod hsq1]]
      exact hzm_c2inv
    have h := hextract6 (χ₁ * χ₃) hp13 γ₃ (by linarith [hγ3L, hH1])
      ((starRingEnd ℂ) ρ₂) lam₂ (lam₂ - lam₁) ((γ₂ + γ₃) * L)
      (by simpa [Work.OffAxis.lamOf_star] using hlam₂)
      rfl (by rw [Complex.conj_im, hγ₂]; ring) hz hw
    exact h
  have hpair7' : ‖(1:ℂ) + (((-γ₃ : ℝ)) : ℂ) * Complex.I - ρ₂‖ ≤ δ →
      Work.ZeroFreeTables.Ksum q T.f L ((β : ℂ) + (((-γ₃ : ℝ)) : ℂ) * Complex.I) (χ₁ * χ₃⁻¹)
        ≤ -(L) * (T.Fc ((lam₂ - lam₁ : ℝ) + (((γ₂ + γ₃) * L : ℝ) : ℂ) * Complex.I)).re
          + T.f 0 * (1/6 + ε') * L := by
    intro hw
    have hz : Work.LinnikContract.zeroMult (χ₁ * χ₃⁻¹) ρ₂ ≠ 0 := by
      rw [show χ₁ * χ₃⁻¹ = χ₂ by rw [mul_inv_eq_of_mul_mul_eq_one' hprod hsq1]]
      exact hZ2.2.1
    have h := hextract6 (χ₁ * χ₃⁻¹) hp1i3 (-γ₃) (by rw [abs_neg]; linarith [hγ3L, hH1])
      ρ₂ lam₂ (lam₂ - lam₁) (((-γ₃) - ρ₂.im) * L) hlam₂ rfl rfl hz hw
    rw [show ((-γ₃) - ρ₂.im) * L = -((γ₂ + γ₃) * L) by rw [hγ₂]; ring] at h
    rw [show ((lam₂ - lam₁ : ℝ) : ℂ) + ((-((γ₂ + γ₃) * L) : ℝ) : ℂ) * Complex.I
        = starRingEnd ℂ (((lam₂ - lam₁ : ℝ) : ℂ) + (((γ₂ + γ₃) * L : ℝ) : ℂ) * Complex.I) by
      apply Complex.ext <;> simp] at h
    rw [TestFn_Fc_conj, Complex.conj_re] at h
    exact h
  have hpair8' : ‖(1:ℂ) + (((γ₂ + γ₃ : ℝ)) : ℂ) * Complex.I - ρ₁‖ ≤ δR →
      Work.ZeroFreeTables.Ksum q T.f L ((β : ℂ) + (((γ₂ + γ₃ : ℝ)) : ℂ) * Complex.I) (χ₂ * χ₃)
        ≤ -(L) * (T.Fc ((0:ℝ) + (((γ₂ + γ₃) * L : ℝ) : ℂ) * Complex.I)).re
          + T.f 0 * (1/8 + ε') * L := by
    intro hw
    have hz : Work.LinnikContract.zeroMult (χ₂ * χ₃) ρ₁ ≠ 0 := by
      rw [h23]; exact hzm1
    have h := hextract8 (χ₂ * χ₃) hp23 (by rw [h23, ← pow_two]; exact hsq1)
      (γ₂ + γ₃) (by linarith [abs_add_le γ₂ γ₃, hγ2L, hγ3L, hH1]) ρ₁ lam₁ (0:ℝ) ((γ₂ + γ₃) * L)
      hlam₁ (by ring) (by rw [him0']; ring) hz hw
    exact h

  -- ===================== the case analysis =====================
  simp only [Complex.ofReal_zero, zero_add, add_zero, zero_sub, sub_zero, zero_mul, mul_zero,
    neg_zero, ← Complex.ofReal_neg, ← Complex.ofReal_add, ← Complex.ofReal_sub, hprod, ht123i] at hpos
  have hring : 7/48 * (T.f 0 * L) + (3/2) * (T.f 0 * (1/8 + ε') * L)
      + 5 * (T.f 0 * (1/6 + ε') * L) + (3/2) * (T.f 0 * ε' * L)
      = T.f 0 * (7/6 + 8 * ε') * L := by ring
  have hBnn : 0 ≤ (T.Fc (((0:ℝ) : ℂ) + (((γ₂ + γ₃) * L : ℝ) : ℂ) * Complex.I)).re :=
    T.Fc_re_nonneg _ (by simp)
  have hmain : 0 ≤ L * (T.F (-lam₁) - T.F 0 - T.F (lam₂ - lam₁) - T.F (lam₃ - lam₁))
      + T.f 0 * (7/6 + 8 * ε') * L := by
    by_cases hcase1 : |(γ₂ + γ₃) * L| ≤ 9/7
    · -- ============ case 1: |μ| ≤ 9/7 (hlow) ============
      have hA : (T.Fc (((-lam₁ : ℝ) : ℂ) + (((γ₂ + γ₃) * L : ℝ) : ℂ) * Complex.I)).re
          ≤ T.f 0 * (7/4) := hF20 lam₁ ((γ₂ + γ₃) * L) hl1nn hl16 hcase1
      have hC2 : 3 * T.f 0 / 8 ≤
          (T.Fc (((lam₂ - lam₁ : ℝ) : ℂ) + (((γ₂ + γ₃) * L : ℝ) : ℂ) * Complex.I)).re :=
        hlow (lam₂ - lam₁) ((γ₂ + γ₃) * L) (by linarith) (by linarith [hlam23, hlam3]) hcase1
      have hC3 : 3 * T.f 0 / 8 ≤
          (T.Fc (((lam₃ - lam₁ : ℝ) : ℂ) + (((γ₂ + γ₃) * L : ℝ) : ℂ) * Complex.I)).re :=
        hlow (lam₃ - lam₁) ((γ₂ + γ₃) * L) (by linarith) (by linarith [hlam3]) hcase1
      have hp4 := hpair4' (hw4 hcase1)
      have hp5 := hpair5' (hw5 hcase1)
      have hp6 := hpair6' (hw6 hcase1)
      have hp7 := hpair7' (hw7 hcase1)
      have hp8 := hpair8' (hw8 hcase1)
      set A1 : ℝ := (T.Fc (((-lam₁ : ℝ) : ℂ) + (((γ₂ + γ₃) * L : ℝ) : ℂ) * Complex.I)).re with hA1
      set A2 : ℝ := (T.Fc (((lam₂ - lam₁ : ℝ) : ℂ) + (((γ₂ + γ₃) * L : ℝ) : ℂ) * Complex.I)).re with hA2
      set A3 : ℝ := (T.Fc (((lam₃ - lam₁ : ℝ) : ℂ) + (((γ₂ + γ₃) * L : ℝ) : ℂ) * Complex.I)).re with hA3
      set B1 : ℝ := (T.Fc (((0:ℝ) : ℂ) + (((γ₂ + γ₃) * L : ℝ) : ℂ) * Complex.I)).re with hB1
      have hLt : (L/2) * A1 - L * A3 - L * A2 - (L/2) * B1 ≤ (7/48) * (T.f 0 * L) := by
        have e0 : (L/2) * (T.f 0 * (7/4)) - L * (3 * T.f 0 / 8) - L * (3 * T.f 0 / 8) - (L/2) * 0
            ≤ (7/48) * (T.f 0 * L) := by nlinarith [T.f0_pos, hlogq]
        have eA : (L/2) * A1 ≤ (L/2) * (T.f 0 * (7/4)) := mul_le_mul_of_nonneg_left hA (by linarith)
        have e2 : L * (3 * T.f 0 / 8) ≤ L * A2 := mul_le_mul_of_nonneg_left hC2 (by linarith)
        have e3 : L * (3 * T.f 0 / 8) ≤ L * A3 := mul_le_mul_of_nonneg_left hC3 (by linarith)
        have eB : 0 ≤ (L/2) * B1 := mul_nonneg (by linarith) hBnn
        linarith [e0, eA, e2, e3, eB]
      simp only [Work.ZeroFreeTables.Ksum] at hbP hbS1 hbS2 hbS3 hbTrip hp4 hp5 hp6 hp7 hp8 hbP9 hbT11 hbT12
      linarith [hpos, hbP, hbS1, hbS2, hbS3, hbTrip, hp4, hp5, hp6, hp7, hp8, hbP9, hbT11, hbT12, hLt, hring]
    · by_cases hcase2 : |(γ₂ + γ₃) * L| ≤ 200
      · -- ============ case 2: 9/7 ≤ |μ| ≤ 200 (hsub) ============
        have hsl : 9/7 ≤ |(γ₂ + γ₃) * L| := (le_of_lt (not_le.mp hcase1))
        have hsub' : (T.Fc (((-lam₁ : ℝ) : ℂ) + (((γ₂ + γ₃) * L : ℝ) : ℂ) * Complex.I)).re
            - (T.Fc (((0:ℝ) : ℂ) + (((γ₂ + γ₃) * L : ℝ) : ℂ) * Complex.I)).re
            ≤ 7 * T.f 0 / 24 := by
          have h := hsub lam₁ ((γ₂ + γ₃) * L) hl1nn hl16 hsl
          simpa only [Complex.ofReal_zero, zero_add] using h
        set A1 : ℝ := (T.Fc (((-lam₁ : ℝ) : ℂ) + (((γ₂ + γ₃) * L : ℝ) : ℂ) * Complex.I)).re with hA1
        set B1 : ℝ := (T.Fc (((0:ℝ) : ℂ) + (((γ₂ + γ₃) * L : ℝ) : ℂ) * Complex.I)).re with hB1
        have hsub'' : A1 - B1 ≤ 7 * T.f 0 / 24 := by simpa [hA1, hB1] using hsub'
        have hLt : (L/2) * A1 - (L/2) * B1 ≤ (7/48) * (T.f 0 * L) := by
          have e : (L/2) * (A1 - B1) ≤ (L/2) * (7 * T.f 0 / 24) :=
            mul_le_mul_of_nonneg_left hsub'' (by linarith)
          have e0 : (L/2) * (7 * T.f 0 / 24) ≤ (7/48) * (T.f 0 * L) := by
            nlinarith [T.f0_pos, hlogq]
          linarith [e, e0]
        have hg4 : Work.ZeroFreeTables.Ksum q T.f L ((β : ℂ) + ((γ₂ : ℝ) : ℂ) * Complex.I) (χ₁ * χ₂)
            ≤ T.f 0 * (1/6 + ε') * L := hself6 (χ₁ * χ₂) hp12 γ₂ (by linarith [hγ2L, hH1])
        have hg5 : Work.ZeroFreeTables.Ksum q T.f L ((β : ℂ) + (((-γ₂) : ℝ) : ℂ) * Complex.I)
            (χ₁ * χ₂⁻¹) ≤ T.f 0 * (1/6 + ε') * L := by
          have h := hself6 (χ₁ * χ₂⁻¹) hp1i2 (-γ₂) (by rw [abs_neg]; linarith [hγ2L, hH1])
          simpa only [Complex.ofReal_neg] using h
        have hg6 : Work.ZeroFreeTables.Ksum q T.f L ((β : ℂ) + ((γ₃ : ℝ) : ℂ) * Complex.I) (χ₁ * χ₃)
            ≤ T.f 0 * (1/6 + ε') * L := hself6 (χ₁ * χ₃) hp13 γ₃ (by linarith [hγ3L, hH1])
        have hg7 : Work.ZeroFreeTables.Ksum q T.f L ((β : ℂ) + (((-γ₃) : ℝ) : ℂ) * Complex.I)
            (χ₁ * χ₃⁻¹) ≤ T.f 0 * (1/6 + ε') * L := by
          have h := hself6 (χ₁ * χ₃⁻¹) hp1i3 (-γ₃) (by rw [abs_neg]; linarith [hγ3L, hH1])
          simpa only [Complex.ofReal_neg] using h
        have hp8 := hpair8' (hw8b hcase2)
        simp only [Work.ZeroFreeTables.Ksum] at hbP hbS1 hbS2 hbS3 hbTrip hg4 hg5 hg6 hg7 hp8 hbP9 hbT11 hbT12
        linarith [hpos, hbP, hbS1, hbS2, hbS3, hbTrip, hg4, hg5, hg6, hg7, hp8, hbP9, hbT11, hbT12, hLt, hring]
      · -- ============ case 3: |μ| ≥ 200 (hB) ============
        have hfar : 200 ≤ |(γ₂ + γ₃) * L| := (le_of_lt (not_le.mp hcase2))
        have hA : (T.Fc (((-lam₁ : ℝ) : ℂ) + (((γ₂ + γ₃) * L : ℝ) : ℂ) * Complex.I)).re
            ≤ T.f 0 / 6 := hB lam₁ ((γ₂ + γ₃) * L) hl1nn hl16 hfar
        set A1 : ℝ := (T.Fc (((-lam₁ : ℝ) : ℂ) + (((γ₂ + γ₃) * L : ℝ) : ℂ) * Complex.I)).re with hA1
        have hA' : A1 ≤ T.f 0 / 6 := by simpa [hA1] using hA
        have hLt : (L/2) * A1 ≤ (7/48) * (T.f 0 * L) := by
          have e : (L/2) * A1 ≤ (L/2) * (T.f 0 / 6) := mul_le_mul_of_nonneg_left hA' (by linarith)
          have e0 : (L/2) * (T.f 0 / 6) ≤ (7/48) * (T.f 0 * L) := by nlinarith [T.f0_pos, hlogq]
          linarith [e, e0]
        have hg4 : Work.ZeroFreeTables.Ksum q T.f L ((β : ℂ) + ((γ₂ : ℝ) : ℂ) * Complex.I) (χ₁ * χ₂)
            ≤ T.f 0 * (1/6 + ε') * L := hself6 (χ₁ * χ₂) hp12 γ₂ (by linarith [hγ2L, hH1])
        have hg5 : Work.ZeroFreeTables.Ksum q T.f L ((β : ℂ) + (((-γ₂) : ℝ) : ℂ) * Complex.I)
            (χ₁ * χ₂⁻¹) ≤ T.f 0 * (1/6 + ε') * L := by
          have h := hself6 (χ₁ * χ₂⁻¹) hp1i2 (-γ₂) (by rw [abs_neg]; linarith [hγ2L, hH1])
          simpa only [Complex.ofReal_neg] using h
        have hg6 : Work.ZeroFreeTables.Ksum q T.f L ((β : ℂ) + ((γ₃ : ℝ) : ℂ) * Complex.I) (χ₁ * χ₃)
            ≤ T.f 0 * (1/6 + ε') * L := hself6 (χ₁ * χ₃) hp13 γ₃ (by linarith [hγ3L, hH1])
        have hg7 : Work.ZeroFreeTables.Ksum q T.f L ((β : ℂ) + (((-γ₃) : ℝ) : ℂ) * Complex.I)
            (χ₁ * χ₃⁻¹) ≤ T.f 0 * (1/6 + ε') * L := by
          have h := hself6 (χ₁ * χ₃⁻¹) hp1i3 (-γ₃) (by rw [abs_neg]; linarith [hγ3L, hH1])
          simpa only [Complex.ofReal_neg] using h
        have hg8 : Work.ZeroFreeTables.Ksum q T.f L
            ((β : ℂ) + (((γ₂ + γ₃) : ℝ) : ℂ) * Complex.I) (χ₂ * χ₃)
            ≤ T.f 0 * (1/8 + ε') * L := by
          have h := hself8 χ₁ hχ₁ne (by simpa [pow_two] using hsq1) (γ₂ + γ₃)
            (by linarith [abs_add_le γ₂ γ₃, hγ2L, hγ3L, hH1])
          simpa only [h23] using h
        simp only [Work.ZeroFreeTables.Ksum] at hbP hbS1 hbS2 hbS3 hbTrip hg4 hg5 hg6 hg7 hg8 hbP9 hbT11 hbT12
        linarith [hpos, hbP, hbS1, hbS2, hbS3, hbTrip, hg4, hg5, hg6, hg7, hg8, hbP9, hbT11, hbT12, hLt, hring]
  have hfinal : 0 ≤ L * (T.F (-lam₁) - T.F 0 - T.F (lam₂ - lam₁) - T.F (lam₃ - lam₁)
      + T.f 0 * (7/6 + 8 * ε')) := by linarith [hmain]
  exact (mul_nonneg_iff_of_pos_left hlogq).mp hfinal

/-! ## The numerical input `hlow` for the test function of HB Lemma 7.2 at `λ = 6/7`

`hlow` is the extraction lower bound `Re F_{6/7}(t + im) ≥ (3/8)·(32/35)` for `0 ≤ t ≤ 6/7`,
`|m| ≤ 9/7`.  Rescaling by `λ = 6/7` (`tf72Fc_scale`) and using `Re (tf72Fc 1 w) = Re (G72 w)`,
this is the scale-free statement `12/35 ≤ Re G72(s + iσ)` for `s = 7t/6 ∈ [0,1]` and
`|σ| ≤ 3/2`: the `G72RePosBox` bound `2/5 ≤ Re G72(s + iσ)` on `σ ∈ [0,3/2]` together with the
evenness of `σ ↦ Re G72(s + iσ)` (`G72_re_eq_integral` and `Real.cos_abs`).  Since `12/35 < 2/5`
we are done. -/

end Work.OffAxis
