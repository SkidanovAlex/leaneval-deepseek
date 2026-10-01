/-
# The (10.6)-ledger of HB §10 in the `χ₁χ₂χ₃ = χ₀`, `ρ₁` real, `χ₁` complex case

Copy of `Work.OffAxis.rect103Engine` (`OffAxis/Rect10_3RealF2Complex.lean`) with the two
minimality hypotheses on `ρ₂`, `ρ₃` deleted: they occur only in the statement, never in the
proof, and the branch `ρ₁ ∈ ℝ`, `χ₁` complex of `HB10_3_Fcases` cannot supply them.
-/
import Submission.Work.OffAxis.Rect10_3RealF2Complex

open DirichletCharacter Complex
open Work.ZeroFreeTables
open scoped Classical BigOperators
open scoped Interval
open MeasureTheory
noncomputable section

namespace Work.OffAxis

open Work.LinnikContract

set_option maxHeartbeats 4000000 in
theorem rect103EngineNoMin (T : Work.ZeroFreeTables.TestFn) (ε' : ℝ) (hε' : 0 < ε')
    (hP : ∃ qP : ℕ, ∀ q : ℕ, qP ≤ q → ∀ [NeZero q] (s : ℂ),
        |s.re - 1| ≤ Real.sqrt (Real.log (Real.log (q : ℝ))) / Real.log (q : ℝ) →
        |s.im| ≤ Real.log (q : ℝ) →
        Work.ZeroFreeTables.Ksum q T.f (Real.log (q : ℝ)) s (1 : DirichletCharacter ℂ q)
          ≤ Real.log (q : ℝ) *
              (∫ t in (0:ℝ)..T.x₀,
                Complex.exp (-(((s - 1) * ((Real.log (q : ℝ) : ℂ)) * (t : ℂ))))
                  * ((T.f t : ℝ) : ℂ)).re
            + T.f 0 * ε' * Real.log (q : ℝ))
    (hA : ∀ a m : ℝ, 0 ≤ a → a ≤ 6/7 →
        (T.Fc (((-a : ℝ) : ℂ) + (m : ℂ) * Complex.I)).re
          - 2 * (T.Fc ((m : ℂ) * Complex.I)).re ≤ T.f 0 / 6)
    (hB : ∀ a m : ℝ, 0 ≤ a → a ≤ 6/7 → 200 ≤ |m| →
        (T.Fc (((-a : ℝ) : ℂ) + (m : ℂ) * Complex.I)).re ≤ T.f 0 / 6) :
    ∀ H : ℝ, 1 ≤ H → ∃ q₀ : ℕ, ∀ q : ℕ, q₀ ≤ q → ∀ [NeZero q]
      (χ₁ χ₂ χ₃ : DirichletCharacter ℂ q) (ρ₁ ρ₂ ρ₃ : ℂ),
      Work.ZeroFreeTables.IsRectMin H χ₁ ρ₁ → ρ₁.im = 0 → χ₁ ^ 2 ≠ 1 →
      Work.ZeroFreeTables.IsZAt H χ₂ ρ₂ → Work.ZeroFreeTables.IsZAt H χ₃ ρ₃ →
      χ₂ ≠ χ₁ → χ₂ ≠ χ₁⁻¹ → χ₃ ≠ χ₁ → χ₃ ≠ χ₁⁻¹ → χ₃ ≠ χ₂ → χ₃ ≠ χ₂⁻¹ →
      lamOf q ρ₂ ≤ lamOf q ρ₃ →
      lamOf q ρ₃ ≤ 6/7 →
      χ₁ * χ₂ * χ₃ = 1 →
      T.F (-(lamOf q ρ₁)) - T.F 0 - T.F (lamOf q ρ₂ - lamOf q ρ₁)
        - T.F (lamOf q ρ₃ - lamOf q ρ₁) + T.f 0 * (7/6 + 8 * ε') ≥ 0 := by
  intro H hH1
  obtain ⟨δ, hδ0, hδ1, qL52, hL52⟩ :=
    Work.ZeroFreeTables.OffAxis.L52SupplyGen ε' hε'
  obtain ⟨B, hB0, hBnd⟩ := T.f_bound
  have hF : ∀ z : ℂ, 0 ≤ z.re →
      0 ≤ (∫ t in (0:ℝ)..T.x₀, Complex.exp (-(z * (t : ℂ))) * ((T.f t : ℝ) : ℂ)).re := by
    intro z hz
    rw [← T.Fc_spec]
    exact T.Fc_re_nonneg z hz
  obtain ⟨qAs, hAs⟩ := Commons.NumberTheory.Linnik.Ksum_le_self_of_L52_phi T.x₀ B (1/6)
    T.x₀_pos hB0 (f := T.f) T.f_cont T.f_supp T.f_diff hBnd T.f0_pos hF hε' hδ0 hδ1
  obtain ⟨qSs, hSs⟩ := Commons.NumberTheory.Linnik.Ksum_le_single_of_L52_phi T.x₀ B (1/6)
    T.x₀_pos hB0 (f := T.f) T.f_cont T.f_supp T.f_diff hBnd T.f0_pos hF hε' hδ0 hδ1
  obtain ⟨qPs, hPs⟩ := Commons.NumberTheory.Linnik.Ksum_principal_le T.x₀ B T.x₀_pos hB0
    (f := T.f) T.f_cont T.f_supp T.f_diff hBnd hε' T.f0_pos
  obtain ⟨qPsh, hPsh⟩ := hP
  refine ⟨max (max (max (max qL52 qAs) (max qSs qPs)) qPsh)
      (Nat.ceil (Real.exp (max (max (3 * H) (12 / (7 * δ)))
        (max (Real.exp (((6 : ℝ) / 7) ^ 2)) (400 / δ)))) + 1), ?_⟩
  intro q hq _inst χ₁ χ₂ χ₃ ρ₁ ρ₂ ρ₃ hR him0 hsq1 hZ2 hZ3
    hne21 hne2i hne31 hne3i hne32 hne3ii hlam23 hlam3 hprod
  have hqL52 : qL52 ≤ q := by omega
  have hqAs : qAs ≤ q := by omega
  have hqSs : qSs ≤ q := by omega
  have hqPs : qPs ≤ q := by omega
  have hqPsh : qPsh ≤ q := by omega
  have hexpq : Nat.ceil (Real.exp (max (max (3 * H) (12 / (7 * δ)))
      (max (Real.exp (((6 : ℝ) / 7) ^ 2)) (400 / δ)))) + 1 ≤ q := by omega
  have hMle : max (max (3 * H) (12 / (7 * δ)))
      (max (Real.exp (((6 : ℝ) / 7) ^ 2)) (400 / δ)) ≤ Real.log (q : ℝ) :=
    ceil_exp_le_log hexpq
  set L : ℝ := Real.log (q : ℝ) with hLdef
  have h3H : 3 * H ≤ L :=
    le_trans (le_trans (le_max_left _ _) (le_max_left _ _)) hMle
  have h12δ : 12 / (7 * δ) ≤ L :=
    le_trans (le_trans (le_max_right _ _) (le_max_left _ _)) hMle
  have hexp2 : Real.exp (((6 : ℝ) / 7) ^ 2) ≤ L :=
    le_trans (le_trans (le_max_left _ _) (le_max_right _ _)) hMle
  have h400δ : 400 / δ ≤ L :=
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
  have hδhalf : (6 : ℝ) / 7 / L ≤ δ / 2 := by
    rw [div_le_iff₀ hlogq]
    have h := (div_le_iff₀ (by positivity : (0:ℝ) < 7 * δ)).mp h12δ
    nlinarith [h]
  set lam₁ : ℝ := lamOf q ρ₁ with hlam₁
  set lam₂ : ℝ := lamOf q ρ₂ with hlam₂
  set lam₃ : ℝ := lamOf q ρ₃ with hlam₃
  set γ₁ : ℝ := ρ₁.im with hγ₁
  set γ₂ : ℝ := ρ₂.im with hγ₂
  set γ₃ : ℝ := ρ₃.im with hγ₃
  set β : ℝ := 1 - lam₁ / L with hβ
  have hl1nn : 0 ≤ lam₁ := by
    rw [hlam₁]; exact lamOf_nonneg_of_zeroMult_aux hR.1.2.1
  have hl2nn : 0 ≤ lam₂ := by
    rw [hlam₂]; exact lamOf_nonneg_of_zeroMult_aux hZ2.2.1
  have hl3nn : 0 ≤ lam₃ := by
    rw [hlam₃]; exact lamOf_nonneg_of_zeroMult_aux hZ3.2.1
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
    rw [hβ, hlam₁, lamOf]
    field_simp
    ring
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
    · rw [him]; linarith [hγ, h3H]
    · rw [hre, hβ]; linarith [hdivle]
  -- the window condition, from the rectangle minimality of `ρ₁`
  have hwin : ∀ (χ : DirichletCharacter ℂ q) [NeZero χ.conductor], χ ≠ 1 → ∀ s : ℂ,
      s.re = β → |s.im| ≤ 3 * H →
      ∀ u : ℂ, (MeromorphicOn.divisor (DirichletCharacter.completedLFunction χ.primitiveCharacter)
          (Metric.closedBall 0 (|s.im| + 2))) u ≠ 0 →
        ‖(1:ℂ) + (s.im : ℂ) * Complex.I - u‖ ≤ δ → u.re ≤ s.re := by
    intro χ _instc hχ s hs hsim u hdiv hwu
    have hzm : Work.LinnikContract.zeroMult χ u ≠ 0 :=
      Work.ZeroFreeTables.OffAxis.zeroMult_ne_zero_of_divisor χ hχ hdiv
    have him1 : |s.im - u.im| ≤ δ := by
      have h := Complex.abs_im_le_norm ((1:ℂ) + (s.im : ℂ) * Complex.I - u)
      have h' : (((1:ℂ) + (s.im : ℂ) * Complex.I - u).im) = s.im - u.im := by simp
      rw [h'] at h
      exact le_trans h hwu
    have him2 : |u.im| ≤ |s.im| + δ := by
      calc |u.im| = |s.im - (s.im - u.im)| := by congr 1; ring
        _ ≤ |s.im| + |s.im - u.im| := abs_sub _ _
        _ ≤ |s.im| + δ := by linarith
    have him3 : |u.im| ≤ 10 * H := by linarith [hsim, him2, hδ1, hH1]
    have hZ : Work.ZeroFreeTables.IsZAt (10 * H) χ u := ⟨hχ, hzm, him3⟩
    have hle : lamOf q ρ₁ ≤ lamOf q u := hR.2 χ u hZ
    rw [← hlam₁, lamOf] at hle
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
  -- non-principality of the auxiliary characters
  have hp12 : χ₁ * χ₂ ≠ 1 := by
    intro h
    apply hne2i
    calc χ₂ = χ₁⁻¹ * (χ₁ * χ₂) := by rw [← mul_assoc, inv_mul_cancel, one_mul]
      _ = χ₁⁻¹ * 1 := by rw [h]
      _ = χ₁⁻¹ := mul_one _
  have hp1i2 : χ₁ * χ₂⁻¹ ≠ 1 := by
    intro h
    apply hne21
    have h2 : χ₂⁻¹ = χ₁⁻¹ := by
      calc χ₂⁻¹ = χ₁⁻¹ * (χ₁ * χ₂⁻¹) := by rw [← mul_assoc, inv_mul_cancel, one_mul]
        _ = χ₁⁻¹ * 1 := by rw [h]
        _ = χ₁⁻¹ := mul_one _
    calc χ₂ = (χ₂⁻¹)⁻¹ := (inv_inv χ₂).symm
      _ = (χ₁⁻¹)⁻¹ := by rw [h2]
      _ = χ₁ := inv_inv χ₁
  have hp13 : χ₁ * χ₃ ≠ 1 := by
    intro h
    apply hne3i
    calc χ₃ = χ₁⁻¹ * (χ₁ * χ₃) := by rw [← mul_assoc, inv_mul_cancel, one_mul]
      _ = χ₁⁻¹ * 1 := by rw [h]
      _ = χ₁⁻¹ := mul_one _
  have hp1i3 : χ₁ * χ₃⁻¹ ≠ 1 := by
    intro h
    apply hne31
    have h2 : χ₃⁻¹ = χ₁⁻¹ := by
      calc χ₃⁻¹ = χ₁⁻¹ * (χ₁ * χ₃⁻¹) := by rw [← mul_assoc, inv_mul_cancel, one_mul]
        _ = χ₁⁻¹ * 1 := by rw [h]
        _ = χ₁⁻¹ := mul_one _
    calc χ₃ = (χ₃⁻¹)⁻¹ := (inv_inv χ₃).symm
      _ = (χ₁⁻¹)⁻¹ := by rw [h2]
      _ = χ₁ := inv_inv χ₁
  have hp23 : χ₂ * χ₃ ≠ 1 := by
    intro h
    apply hne3ii
    calc χ₃ = χ₂⁻¹ * (χ₂ * χ₃) := by rw [← mul_assoc, inv_mul_cancel, one_mul]
      _ = χ₂⁻¹ * 1 := by rw [h]
      _ = χ₂⁻¹ := mul_one _
  have hp2i3 : χ₂ * χ₃⁻¹ ≠ 1 := by
    intro h
    apply hne32
    have h2 : χ₃⁻¹ = χ₂⁻¹ := by
      calc χ₃⁻¹ = χ₂⁻¹ * (χ₂ * χ₃⁻¹) := by rw [← mul_assoc, inv_mul_cancel, one_mul]
        _ = χ₂⁻¹ * 1 := by rw [h]
        _ = χ₂⁻¹ := mul_one _
    calc χ₃ = (χ₃⁻¹)⁻¹ := (inv_inv χ₃).symm
      _ = (χ₂⁻¹)⁻¹ := by rw [h2]
      _ = χ₂ := inv_inv χ₂
  have hχ12 : χ₁ * χ₂ = χ₃⁻¹ := by
    have h2 : (χ₁ * χ₂) * χ₃ = 1 := hprod
    calc χ₁ * χ₂ = (χ₁ * χ₂) * χ₃ * χ₃⁻¹ := by rw [mul_assoc, mul_inv_cancel, mul_one]
      _ = 1 * χ₃⁻¹ := by rw [h2]
      _ = χ₃⁻¹ := one_mul _
  have hχ23 : χ₂ * χ₃ = χ₁⁻¹ := by
    have h2 : χ₁ * (χ₂ * χ₃) = 1 := by rw [← mul_assoc]; exact hprod
    calc χ₂ * χ₃ = χ₁⁻¹ * (χ₁ * (χ₂ * χ₃)) := by rw [← mul_assoc, inv_mul_cancel, one_mul]
      _ = χ₁⁻¹ * 1 := by rw [h2]
      _ = χ₁⁻¹ := mul_one _
  have hχ13 : χ₁ * χ₃ = χ₂⁻¹ := by
    have h2 : χ₂ * (χ₁ * χ₃) = 1 := by
      calc χ₂ * (χ₁ * χ₃) = χ₁ * χ₂ * χ₃ := by ac_rfl
        _ = 1 := hprod
    calc χ₁ * χ₃ = χ₂⁻¹ * (χ₂ * (χ₁ * χ₃)) := by rw [← mul_assoc, inv_mul_cancel, one_mul]
      _ = χ₂⁻¹ * 1 := by rw [h2]
      _ = χ₂⁻¹ := mul_one _
  have ht12i3 : χ₃ ^ 2 ≠ 1 → χ₁ * χ₂ * χ₃⁻¹ ≠ 1 := by
    intro h3 h
    apply h3
    have h4 : χ₃⁻¹ * χ₃⁻¹ = 1 := by rw [hχ12] at h; exact h
    have h5 : χ₃⁻¹ = χ₃ := by
      have h6 : χ₃ * (χ₃⁻¹ * χ₃⁻¹) = χ₃ := by rw [h4, mul_one]
      rwa [← mul_assoc, mul_inv_cancel, one_mul] at h6
    calc χ₃ ^ 2 = χ₃ * χ₃ := pow_two χ₃
      _ = χ₃ * χ₃⁻¹ := by rw [h5]
      _ = 1 := mul_inv_cancel χ₃
  have ht1i23 : χ₂ ^ 2 ≠ 1 → χ₁ * χ₂⁻¹ * χ₃ ≠ 1 := by
    intro h2 h
    apply h2
    have h4 : χ₂⁻¹ * χ₂⁻¹ = 1 := by
      have h8 : χ₁ * χ₂⁻¹ * χ₃ = (χ₁ * χ₃) * χ₂⁻¹ := by ac_rfl
      rw [h8, hχ13] at h
      exact h
    have h5' : χ₂⁻¹ = χ₂ := by
      have h6 : χ₂ * (χ₂⁻¹ * χ₂⁻¹) = χ₂ := by rw [h4, mul_one]
      rwa [← mul_assoc, mul_inv_cancel, one_mul] at h6
    calc χ₂ ^ 2 = χ₂ * χ₂ := pow_two χ₂
      _ = χ₂ * χ₂⁻¹ := by rw [h5']
      _ = 1 := mul_inv_cancel χ₂
  have ht123i : χ₁⁻¹ * χ₂ * χ₃ ≠ 1 := by
    intro h
    apply hsq1
    have h1 : χ₁⁻¹ * χ₁⁻¹ = 1 := by
      have h2 : χ₁⁻¹ * (χ₂ * χ₃) = 1 := by rw [← mul_assoc]; exact h
      rwa [hχ23] at h2
    have h4 : χ₁⁻¹ = χ₁ := by
      have h6 : χ₁ * (χ₁⁻¹ * χ₁⁻¹) = χ₁ := by rw [h1, mul_one]
      rwa [← mul_assoc, mul_inv_cancel, one_mul] at h6
    calc χ₁ ^ 2 = χ₁ * χ₁ := pow_two χ₁
      _ = χ₁ * χ₁⁻¹ := by rw [h4]
      _ = 1 := mul_inv_cancel χ₁
  -- `ρ₁` is a zero of `χ₁⁻¹` (it is real)
  have hρ1inv : Work.LinnikContract.zeroMult χ₁⁻¹ ρ₁ ≠ 0 := by
    have h2 := Work.A7.zeroMult_conj_inv χ₁ ρ₁
    have hconj : starRingEnd ℂ ρ₁ = ρ₁ := by
      rw [starRingEnd_apply, Complex.star_def, Complex.conj_eq_iff_im]
      exact him0'
    rw [hconj] at h2
    rw [h2]
    exact hR.1.2.1
  -- ==================== the point bounds ====================
  have hbP : Work.ZeroFreeTables.Ksum q T.f L (β : ℂ) 1
      ≤ L * T.F (-lam₁) + T.f 0 * ε' * L := by
    have h := hPs (q := q) hqPs (β := β) (lam := lam₁) ?_ ?_
    · have hFint : T.F (-lam₁) = ∫ t in (0:ℝ)..T.x₀, Real.exp (lam₁ * t) * T.f t := by
        rw [TestFn_F_eq_integral]
        apply intervalIntegral.integral_congr
        intro t _
        simp only [neg_mul, neg_neg]
      rw [hFint]
      exact h
    · rw [hβ, hlam₁]; field_simp; ring
    · rw [hβ1]; exact hdivle
  have hsingle : ∀ (χ : DirichletCharacter ℂ q) [NeZero χ.conductor], χ ≠ 1 →
      ∀ (γ : ℝ), |γ| ≤ 3 * H → ∀ (ρ : ℂ) (lam : ℝ),
      ρ.im = γ → lam = lamOf q ρ → lam ≤ 6 / 7 →
      Work.LinnikContract.zeroMult χ ρ ≠ 0 →
      Work.ZeroFreeTables.Ksum q T.f L ((β : ℂ) + (γ : ℂ) * Complex.I) χ
        ≤ -L * T.F (lam - lam₁) + T.f 0 * (1/6 + ε') * L := by
    intro χ _instc hχ γ hγ ρ lam hργ hlam hlam67 hzm
    obtain ⟨hr1, hr2, hr3⟩ := hrange γ hγ
    have hmem : ρ ∈ Metric.closedBall (0:ℂ) (|γ| + 2) := by
      have h := Work.ZeroFreeTables.mem_closedBall_of_absre_le_one_v2
        (zeroMult_abs_re_le_one hχ hzm)
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
      have hre : ρ.re = 1 - lam / L := by
        rw [hlam, lamOf]; field_simp; ring
      have hval : 1 - ρ.re = lam / L := by rw [hre]; ring
      have hlamnn : 0 ≤ lam := by
        rw [hlam]; exact lamOf_nonneg_of_zeroMult_aux hzm
      rw [abs_of_nonneg (by rw [hval]; exact div_nonneg hlamnn hlogq.le), hval]
      exact le_trans (le_trans (div_le_div_of_nonneg_right hlam67 hlogq.le) hδhalf)
        (by linarith [hδ0])
    have hsre : (((β : ℂ) + (γ : ℂ) * Complex.I).re) = β := by simp
    have h := hSs (q := q) hqSs χ hχ hr1 hr2 hr3 (hL52 q hqL52 χ hχ) hdiv hwinρ
      (hwin χ hχ ((β : ℂ) + (γ : ℂ) * Complex.I) hsre
        (by rw [show (((β : ℂ) + (γ : ℂ) * Complex.I).im) = γ from by simp]; exact hγ))
    have hint : (∫ t in (0:ℝ)..T.x₀,
          Complex.exp (-(((((β : ℂ) + (γ : ℂ) * Complex.I)) - ρ) * (L : ℂ) * (t:ℂ))) *
            ((T.f t : ℝ) : ℂ)).re = T.F (lam - lam₁) := by
      rw [← T.Fc_spec]
      rw [sub_mul_log_eq_aux (q := q) (β := β) (γ := γ) (lam := lam)
        (lam₁ := lam₁) (ρ := ρ) hlogq.ne' hβ ?_ hργ]
      · rfl
      · rw [hlam, lamOf]; field_simp; ring
    rw [hint] at h
    exact h
  have hbS1 : Work.ZeroFreeTables.Ksum q T.f L ((β : ℂ) + (γ₁ : ℂ) * Complex.I) χ₁
      ≤ -L * T.F 0 + T.f 0 * (1/6 + ε') * L := by
    have h := hsingle χ₁ hR.1.1 γ₁ (by rw [hγ1z, abs_zero]; linarith [hH1])
      ρ₁ lam₁ (by rw [hγ₁])
      hlam₁ hl16 hR.1.2.1
    simpa only [sub_self] using h
  have hbS2 : Work.ZeroFreeTables.Ksum q T.f L ((β : ℂ) + (γ₂ : ℂ) * Complex.I) χ₂
      ≤ -L * T.F (lam₂ - lam₁) + T.f 0 * (1/6 + ε') * L :=
    hsingle χ₂ hZ2.1 γ₂ (by rw [hγ₂]; linarith [hγ2L, hH1]) ρ₂ lam₂ (by rw [hγ₂]) hlam₂
      (le_trans hlam23 hlam3) hZ2.2.1
  have hbS3 : Work.ZeroFreeTables.Ksum q T.f L ((β : ℂ) + (γ₃ : ℂ) * Complex.I) χ₃
      ≤ -L * T.F (lam₃ - lam₁) + T.f 0 * (1/6 + ε') * L :=
    hsingle χ₃ hZ3.1 γ₃ (by rw [hγ₃]; linarith [hγ3L, hH1]) ρ₃ lam₃ (by rw [hγ₃]) hlam₃
      hlam3 hZ3.2.1
  have hself : ∀ (χ : DirichletCharacter ℂ q) [NeZero χ.conductor], χ ≠ 1 →
      ∀ (γ : ℝ), |γ| ≤ 3 * H →
      Work.ZeroFreeTables.Ksum q T.f L ((β : ℂ) + (γ : ℂ) * Complex.I) χ
        ≤ T.f 0 * (1/6 + ε') * L := by
    intro χ _instc hχ γ hγ
    obtain ⟨hr1, hr2, hr3⟩ := hrange γ hγ
    have hsre : (((β : ℂ) + (γ : ℂ) * Complex.I).re) = β := by simp
    exact hAs (q := q) hqAs χ hχ hr1 hr2 hr3 (hL52 q hqL52 χ hχ)
      (hwin χ hχ ((β : ℂ) + (γ : ℂ) * Complex.I) hsre
        (by rw [show (((β : ℂ) + (γ : ℂ) * Complex.I).im) = γ from by simp]; exact hγ))
  -- the generic pair bounds
  have hbP12 : Work.ZeroFreeTables.Ksum q T.f L
        ((β : ℂ) + ((γ₁ : ℂ) + (γ₂ : ℂ)) * Complex.I) (χ₁ * χ₂)
      ≤ T.f 0 * (1/6 + ε') * L := by
    have h := hself (χ₁ * χ₂) hp12 (γ₁ + γ₂) (by
      calc |γ₁ + γ₂| ≤ |γ₁| + |γ₂| := abs_add_le _ _
        _ = |γ₂| := by rw [hγ1z, abs_zero, zero_add]
        _ ≤ 3 * H := by linarith [hγ2L, hH1])
    simpa only [ofReal_add] using h
  have hbPi12 : Work.ZeroFreeTables.Ksum q T.f L
        ((β : ℂ) + ((γ₁ : ℂ) - (γ₂ : ℂ)) * Complex.I) (χ₁ * χ₂⁻¹)
      ≤ T.f 0 * (1/6 + ε') * L := by
    have h := hself (χ₁ * χ₂⁻¹) hp1i2 (γ₁ - γ₂) (by
      calc |γ₁ - γ₂| ≤ |γ₁| + |γ₂| := by
            simpa [sub_eq_add_neg] using abs_add_le γ₁ (-γ₂)
        _ = |γ₂| := by rw [hγ1z, abs_zero, zero_add]
        _ ≤ 3 * H := by linarith [hγ2L, hH1])
    simpa only [ofReal_sub] using h
  have hbP13 : Work.ZeroFreeTables.Ksum q T.f L
        ((β : ℂ) + ((γ₁ : ℂ) + (γ₃ : ℂ)) * Complex.I) (χ₁ * χ₃)
      ≤ T.f 0 * (1/6 + ε') * L := by
    have h := hself (χ₁ * χ₃) hp13 (γ₁ + γ₃) (by
      calc |γ₁ + γ₃| ≤ |γ₁| + |γ₃| := abs_add_le _ _
        _ = |γ₃| := by rw [hγ1z, abs_zero, zero_add]
        _ ≤ 3 * H := by linarith [hγ3L, hH1])
    simpa only [ofReal_add] using h
  have hbPi13 : Work.ZeroFreeTables.Ksum q T.f L
        ((β : ℂ) + ((γ₁ : ℂ) - (γ₃ : ℂ)) * Complex.I) (χ₁ * χ₃⁻¹)
      ≤ T.f 0 * (1/6 + ε') * L := by
    have h := hself (χ₁ * χ₃⁻¹) hp1i3 (γ₁ - γ₃) (by
      calc |γ₁ - γ₃| ≤ |γ₁| + |γ₃| := by
            simpa [sub_eq_add_neg] using abs_add_le γ₁ (-γ₃)
        _ = |γ₃| := by rw [hγ1z, abs_zero, zero_add]
        _ ≤ 3 * H := by linarith [hγ3L, hH1])
    simpa only [ofReal_sub] using h
  have hbP23g : Work.ZeroFreeTables.Ksum q T.f L
        ((β : ℂ) + ((γ₂ : ℂ) + (γ₃ : ℂ)) * Complex.I) (χ₂ * χ₃)
      ≤ T.f 0 * (1/6 + ε') * L := by
    have h := hself (χ₂ * χ₃) hp23 (γ₂ + γ₃) (by
      calc |γ₂ + γ₃| ≤ |γ₂| + |γ₃| := abs_add_le _ _
        _ ≤ 3 * H := by linarith [hγ2L, hγ3L, hH1])
    simpa only [ofReal_add] using h
  have hbPi23g : Work.ZeroFreeTables.Ksum q T.f L
        ((β : ℂ) + ((γ₂ : ℂ) - (γ₃ : ℂ)) * Complex.I) (χ₂ * χ₃⁻¹)
      ≤ T.f 0 * (1/6 + ε') * L := by
    have h := hself (χ₂ * χ₃⁻¹) hp2i3 (γ₂ - γ₃) (by
      calc |γ₂ - γ₃| ≤ |γ₂| + |γ₃| := by
            simpa [sub_eq_add_neg] using abs_add_le γ₂ (-γ₃)
        _ ≤ 3 * H := by linarith [hγ2L, hγ3L, hH1])
    simpa only [ofReal_sub] using h
  -- a single-point bound with the zero `ρ₁` (a zero of `χ₁⁻¹`, since it is real), at the point
  -- `β + iτ`: this is the window extraction that pays for a principal triple.
  have hsingleρ₁ : ∀ (ψ : DirichletCharacter ℂ q) [NeZero ψ.conductor], ψ ≠ 1 →
      Work.LinnikContract.zeroMult ψ ρ₁ ≠ 0 → ∀ (τ : ℝ), |τ| ≤ δ / 2 →
      Work.ZeroFreeTables.Ksum q T.f L ((β : ℂ) + (τ : ℂ) * Complex.I) ψ
        ≤ -L * (T.Fc (((τ * L : ℝ)) * Complex.I)).re + T.f 0 * (1/6 + ε') * L := by
    intro ψ _instc hψ hzm τ hτ
    have hτ3 : |τ| ≤ 3 * H := by linarith [hτ, hδ1, hH1]
    obtain ⟨hr1, hr2, hr3⟩ := hrange τ hτ3
    have hmem : ρ₁ ∈ Metric.closedBall (0:ℂ) (|τ| + 2) := by
      rw [Metric.mem_closedBall, dist_zero_right]
      have h1 : |ρ₁.re| ≤ 1 :=
        zeroMult_abs_re_le_one hψ hzm
      have h2 : ‖ρ₁‖ = |ρ₁.re| := by
        have h3 : Complex.normSq ρ₁ = ρ₁.re ^ 2 := by
          rw [Complex.normSq_apply, him0']
          ring
        have h4 : ‖ρ₁‖ ^ 2 = ρ₁.re ^ 2 := by rw [← Complex.normSq_eq_norm_sq, h3]
        calc ‖ρ₁‖ = Real.sqrt (‖ρ₁‖ ^ 2) := (Real.sqrt_sq (norm_nonneg ρ₁)).symm
          _ = Real.sqrt (ρ₁.re ^ 2) := by rw [h4]
          _ = |ρ₁.re| := Real.sqrt_sq_eq_abs _
      rw [h2]
      linarith [h1, abs_nonneg τ]
    have hdiv : (MeromorphicOn.divisor (DirichletCharacter.completedLFunction ψ.primitiveCharacter)
        (Metric.closedBall 0 (|((β : ℂ) + (τ : ℂ) * Complex.I).im| + 2))) ρ₁ ≠ 0 := by
      have him : (((β : ℂ) + (τ : ℂ) * Complex.I).im) = τ := by simp
      rw [him]
      exact Work.ZeroFreeTables.OffAxis.divisor_ne_zero_of_zeroMult ψ hψ hmem hzm
    have hwinρ : ‖(1:ℂ) + ((((β : ℂ) + (τ : ℂ) * Complex.I)).im : ℂ) * Complex.I - ρ₁‖ ≤ δ := by
      have him : (((β : ℂ) + (τ : ℂ) * Complex.I).im) = τ := by simp
      have h1 : (1:ℂ) + (τ : ℂ) * Complex.I - ρ₁
          = ((lam₁ / L : ℝ) : ℂ) + (τ : ℂ) * Complex.I := by
        have h2 : (1:ℂ) - ρ₁ = ((lam₁ / L : ℝ) : ℂ) := by
          apply Complex.ext
          · simp only [Complex.sub_re, Complex.one_re, Complex.ofReal_re]
            rw [hρ1re, hβ]; ring
          · simp only [Complex.sub_im, Complex.one_im, Complex.ofReal_im, Complex.zero_im]
            rw [him0']
            ring
        calc (1:ℂ) + (τ : ℂ) * Complex.I - ρ₁ = ((1:ℂ) - ρ₁) + (τ : ℂ) * Complex.I := by ring
          _ = ((lam₁ / L : ℝ) : ℂ) + (τ : ℂ) * Complex.I := by rw [h2]
      rw [him, h1]
      have h6 : lam₁ / L ≤ δ / 2 :=
        le_trans (div_le_div_of_nonneg_right hl16 hlogq.le) hδhalf
      have h4 : Complex.normSq (((lam₁ / L : ℝ) : ℂ) + (τ : ℂ) * Complex.I)
          = (lam₁ / L) ^ 2 + τ ^ 2 := by
        rw [Complex.normSq_apply]
        simp only [Complex.add_re, Complex.add_im, Complex.ofReal_re, Complex.ofReal_im,
          Complex.mul_re, Complex.mul_im, Complex.I_re, Complex.I_im, mul_zero, mul_one,
          sub_zero, add_zero]
        ring
      have h6b : (lam₁ / L) ^ 2 ≤ (δ / 2) ^ 2 := by
        have h6c : 0 ≤ lam₁ / L := div_nonneg hl1nn hlogq.le
        nlinarith [h6c, h6]
      have hτ2 : τ ^ 2 ≤ (δ / 2) ^ 2 := by nlinarith [abs_le.mp hτ]
      have h5 : ((lam₁ / L) ^ 2 + τ ^ 2) ≤ δ ^ 2 := by nlinarith [h6b, hτ2, hδ0]
      have h7 : ‖((lam₁ / L : ℝ) : ℂ) + (τ : ℂ) * Complex.I‖ ^ 2 ≤ δ ^ 2 := by
        rw [Complex.sq_norm, h4]
        exact h5
      nlinarith [norm_nonneg (((lam₁ / L : ℝ) : ℂ) + (τ : ℂ) * Complex.I), hδ0]
    have hsre : (((β : ℂ) + (τ : ℂ) * Complex.I).re) = β := by simp
    have h := hSs (q := q) hqSs ψ hψ hr1 hr2 hr3 (hL52 q hqL52 ψ hψ) hdiv hwinρ
      (hwin ψ hψ ((β : ℂ) + (τ : ℂ) * Complex.I) hsre
        (by rw [show (((β : ℂ) + (τ : ℂ) * Complex.I).im) = τ from by simp]; exact hτ3))
    have hz : (((β : ℂ) + (τ : ℂ) * Complex.I) - ρ₁) * (L : ℂ)
        = (((τ * L : ℝ)) : ℂ) * Complex.I := by
      have hβL : ((β : ℂ) - ρ₁) * (L : ℂ) = 0 := by
        have hb2 : (β : ℂ) - ρ₁ = 0 := by
          apply Complex.ext
          · simp only [Complex.sub_re, Complex.ofReal_re]
            exact sub_eq_zero.mpr hρ1re.symm
          · simp only [Complex.sub_im, Complex.ofReal_im, Complex.zero_im]
            rw [him0']
            ring
        rw [hb2, zero_mul]
      rw [show ((β : ℂ) + (τ : ℂ) * Complex.I) - ρ₁ = ((β : ℂ) - ρ₁) + (τ : ℂ) * Complex.I
        from by ring, add_mul, hβL, zero_add]
      push_cast
      ring
    rw [hz] at h
    rw [← T.Fc_spec] at h
    exact h
  -- the companion pair `(2,3)+`
  have hbP23s : |γ₂ + γ₃| ≤ δ / 2 →
      Work.ZeroFreeTables.Ksum q T.f L
        ((β : ℂ) + ((γ₂ : ℂ) + (γ₃ : ℂ)) * Complex.I) (χ₂ * χ₃)
      ≤ -L * (T.Fc ((((γ₂ + γ₃) * L : ℝ)) * Complex.I)).re + T.f 0 * (1/6 + ε') * L := by
    intro hsh
    have h := hsingleρ₁ (χ₂ * χ₃) hp23 (by rw [hχ23]; exact hρ1inv) (γ₂ + γ₃) hsh
    simpa only [ofReal_add] using h
  -- the companion pair `(2,3)-` (available when its character is `χ₁⁻¹`)
  have hbPi23s : Work.LinnikContract.zeroMult (χ₂ * χ₃⁻¹) ρ₁ ≠ 0 → |γ₂ - γ₃| ≤ δ / 2 →
      Work.ZeroFreeTables.Ksum q T.f L
        ((β : ℂ) + ((γ₂ : ℂ) - (γ₃ : ℂ)) * Complex.I) (χ₂ * χ₃⁻¹)
      ≤ -L * (T.Fc ((((γ₂ - γ₃) * L : ℝ)) * Complex.I)).re + T.f 0 * (1/6 + ε') * L := by
    intro hz hsh
    have h := hsingleρ₁ (χ₂ * χ₃⁻¹) hp2i3 hz (γ₂ - γ₃) hsh
    simpa only [ofReal_sub] using h
  -- the principal triple `(1)`: character `χ₁χ₂χ₃ = 1`, from the shifted principal bound
  have hbT123 : Work.ZeroFreeTables.Ksum q T.f L
        ((β : ℂ) + ((γ₁ : ℂ) + (γ₂ : ℂ) + (γ₃ : ℂ)) * Complex.I) (χ₁ * χ₂ * χ₃)
      ≤ L * (T.Fc (((-lam₁ : ℝ) : ℂ) + (((γ₂ + γ₃) * L : ℝ) : ℂ) * Complex.I)).re
        + T.f 0 * ε' * L := by
    have hm1 : ((β : ℂ) + ((γ₂ + γ₃ : ℝ) : ℂ) * Complex.I).re = β := by simp
    have hm2 : ((β : ℂ) + ((γ₂ + γ₃ : ℝ) : ℂ) * Complex.I).im = γ₂ + γ₃ := by simp
    have hs := hPsh (q := q) hqPsh ((β : ℂ) + ((γ₂ + γ₃ : ℝ) : ℂ) * Complex.I)
      (by rw [hm1, hβ1]; exact hdivle)
      (by rw [hm2]
          have h23 : |γ₂ + γ₃| ≤ 2 * H := by linarith [abs_add_le γ₂ γ₃, hγ2L, hγ3L]
          linarith [h23, h3H])
    rw [show ((β : ℂ) + ((γ₂ + γ₃ : ℝ) : ℂ) * Complex.I - 1) * ((L : ℂ))
        = (((-lam₁ : ℝ) : ℂ) + (((γ₂ + γ₃) * L : ℝ) : ℂ) * Complex.I) from
        sub_one_mul_log hlogq.ne' hβ] at hs
    rw [← T.Fc_spec] at hs
    have hpt : ((β : ℂ) + ((γ₁ : ℂ) + (γ₂ : ℂ) + (γ₃ : ℂ)) * Complex.I)
        = (β : ℂ) + ((γ₂ + γ₃ : ℝ) : ℂ) * Complex.I := by
      rw [hγ1z]; push_cast; ring
    rw [hprod, hpt]
    exact hs
  -- the principal triple `(2)`: character `χ₁χ₂χ₃⁻¹ = 1` when `χ₃² = 1`
  have hbT12i3 : χ₃ ^ 2 = 1 →
      Work.ZeroFreeTables.Ksum q T.f L
        ((β : ℂ) + ((γ₁ : ℂ) + (γ₂ : ℂ) - (γ₃ : ℂ)) * Complex.I) (χ₁ * χ₂ * χ₃⁻¹)
      ≤ L * (T.Fc (((-lam₁ : ℝ) : ℂ) + (((γ₂ - γ₃) * L : ℝ) : ℂ) * Complex.I)).re
        + T.f 0 * ε' * L := by
    intro h3
    have hchar : χ₁ * χ₂ * χ₃⁻¹ = 1 := by
      have h4 : χ₃⁻¹ * χ₃⁻¹ = (χ₃ ^ 2)⁻¹ := by rw [pow_two, mul_inv_rev]
      rw [hχ12, h4, h3, inv_one]
    have hm1 : ((β : ℂ) + ((γ₂ - γ₃ : ℝ) : ℂ) * Complex.I).re = β := by simp
    have hm2 : ((β : ℂ) + ((γ₂ - γ₃ : ℝ) : ℂ) * Complex.I).im = γ₂ - γ₃ := by simp
    have hs := hPsh (q := q) hqPsh ((β : ℂ) + ((γ₂ - γ₃ : ℝ) : ℂ) * Complex.I)
      (by rw [hm1, hβ1]; exact hdivle)
      (by rw [hm2]
          have h23 : |γ₂ - γ₃| ≤ 2 * H := by
            have h2' : |γ₂ - γ₃| ≤ |γ₂| + |γ₃| := by
              simpa [sub_eq_add_neg] using abs_add_le γ₂ (-γ₃)
            linarith [h2', hγ2L, hγ3L]
          have h23' : |γ₃ - γ₂| ≤ 2 * H := by
            rw [show γ₃ - γ₂ = -(γ₂ - γ₃) by ring, abs_neg]
            exact h23
          linarith [h23', h3H, hH1])
    rw [show ((β : ℂ) + ((γ₂ - γ₃ : ℝ) : ℂ) * Complex.I - 1) * ((L : ℂ))
        = (((-lam₁ : ℝ) : ℂ) + (((γ₂ - γ₃) * L : ℝ) : ℂ) * Complex.I) from
        sub_one_mul_log hlogq.ne' hβ] at hs
    rw [← T.Fc_spec] at hs
    have hpt : ((β : ℂ) + ((γ₁ : ℂ) + (γ₂ : ℂ) - (γ₃ : ℂ)) * Complex.I)
        = (β : ℂ) + ((γ₂ - γ₃ : ℝ) : ℂ) * Complex.I := by
      rw [hγ1z]; push_cast; ring
    rw [hchar, hpt]
    exact hs
  -- the principal triple `(3)`: character `χ₁χ₂⁻¹χ₃ = 1` when `χ₂² = 1`
  have hbT1i23 : χ₂ ^ 2 = 1 →
      Work.ZeroFreeTables.Ksum q T.f L
        ((β : ℂ) + ((γ₁ : ℂ) - (γ₂ : ℂ) + (γ₃ : ℂ)) * Complex.I) (χ₁ * χ₂⁻¹ * χ₃)
      ≤ L * (T.Fc (((-lam₁ : ℝ) : ℂ) + (((γ₃ - γ₂) * L : ℝ) : ℂ) * Complex.I)).re
        + T.f 0 * ε' * L := by
    intro h2
    have hchar : χ₁ * χ₂⁻¹ * χ₃ = 1 := by
      have hχ₁₃ : χ₁ * χ₃ = χ₂⁻¹ := by
        have h6 : χ₂ * (χ₁ * χ₃) = 1 := by
          rw [← mul_assoc, mul_comm χ₂ χ₁]; exact hprod
        exact eq_inv_of_mul_eq_one_right h6
      have h7 : χ₁ * χ₂⁻¹ * χ₃ = χ₂⁻¹ * χ₂⁻¹ := by rw [← hχ₁₃]; ac_rfl
      have h4 : χ₂⁻¹ * χ₂⁻¹ = (χ₂ ^ 2)⁻¹ := by rw [pow_two, mul_inv_rev]
      rw [h7, h4, h2, inv_one]
    have hm1 : ((β : ℂ) + ((γ₃ - γ₂ : ℝ) : ℂ) * Complex.I).re = β := by simp
    have hm2 : ((β : ℂ) + ((γ₃ - γ₂ : ℝ) : ℂ) * Complex.I).im = γ₃ - γ₂ := by simp
    have hs := hPsh (q := q) hqPsh ((β : ℂ) + ((γ₃ - γ₂ : ℝ) : ℂ) * Complex.I)
      (by rw [hm1, hβ1]; exact hdivle)
      (by rw [hm2]
          have h23 : |γ₂ - γ₃| ≤ 2 * H := by
            have h2' : |γ₂ - γ₃| ≤ |γ₂| + |γ₃| := by
              simpa [sub_eq_add_neg] using abs_add_le γ₂ (-γ₃)
            linarith [h2', hγ2L, hγ3L]
          have h23' : |γ₃ - γ₂| ≤ 2 * H := by
            rw [show γ₃ - γ₂ = -(γ₂ - γ₃) by ring, abs_neg]
            exact h23
          linarith [h23', h3H, hH1])
    rw [show ((β : ℂ) + ((γ₃ - γ₂ : ℝ) : ℂ) * Complex.I - 1) * ((L : ℂ))
        = (((-lam₁ : ℝ) : ℂ) + (((γ₃ - γ₂) * L : ℝ) : ℂ) * Complex.I) from
        sub_one_mul_log hlogq.ne' hβ] at hs
    rw [← T.Fc_spec] at hs
    have hpt : ((β : ℂ) + ((γ₁ : ℂ) - (γ₂ : ℂ) + (γ₃ : ℂ)) * Complex.I)
        = (β : ℂ) + ((γ₃ - γ₂ : ℝ) : ℂ) * Complex.I := by
      rw [hγ1z]; push_cast; ring
    rw [hchar, hpt]
    exact hs
  -- the generic triple bounds
  have hbT12i3g : χ₃ ^ 2 ≠ 1 →
      Work.ZeroFreeTables.Ksum q T.f L
        ((β : ℂ) + ((γ₁ : ℂ) + (γ₂ : ℂ) - (γ₃ : ℂ)) * Complex.I) (χ₁ * χ₂ * χ₃⁻¹)
      ≤ T.f 0 * (1/6 + ε') * L := by
    intro h3
    have h := hself (χ₁ * χ₂ * χ₃⁻¹) (ht12i3 h3) (γ₁ + γ₂ - γ₃) (by
      calc |γ₁ + γ₂ - γ₃| ≤ |γ₁ + γ₂| + |γ₃| := by
            simpa [sub_eq_add_neg] using abs_add_le (γ₁ + γ₂) (-γ₃)
        _ ≤ 3 * H := by
            have h12 : |γ₂| ≤ H := hγ2L
            rw [hγ1z] at *
            simp only [abs_zero, zero_add] at *
            linarith [h12, hH1])
    simpa only [ofReal_sub, ofReal_add] using h
  have hbT1i23g : χ₂ ^ 2 ≠ 1 →
      Work.ZeroFreeTables.Ksum q T.f L
        ((β : ℂ) + ((γ₁ : ℂ) - (γ₂ : ℂ) + (γ₃ : ℂ)) * Complex.I) (χ₁ * χ₂⁻¹ * χ₃)
      ≤ T.f 0 * (1/6 + ε') * L := by
    intro h2
    have h := hself (χ₁ * χ₂⁻¹ * χ₃) (ht1i23 h2) (γ₁ - γ₂ + γ₃) (by
      calc |γ₁ - γ₂ + γ₃| ≤ |γ₁ - γ₂| + |γ₃| := abs_add_le _ _
        _ ≤ 3 * H := by
            have h12 : |γ₂| ≤ H := hγ2L
            rw [hγ1z] at *
            simp only [abs_zero, zero_sub, abs_neg] at *
            linarith [h12, hH1])
    simpa only [ofReal_sub, ofReal_add] using h
  have hbTi123 : Work.ZeroFreeTables.Ksum q T.f L
        ((β : ℂ) + (-(γ₁ : ℂ) + (γ₂ : ℂ) + (γ₃ : ℂ)) * Complex.I) (χ₁⁻¹ * χ₂ * χ₃)
      ≤ T.f 0 * (1/6 + ε') * L := by
    have h := hself (χ₁⁻¹ * χ₂ * χ₃) ht123i (-γ₁ + γ₂ + γ₃) (by
      have h23 : |γ₂ + γ₃| ≤ 2 * H := by linarith [abs_add_le γ₂ γ₃, hγ2L, hγ3L]
      have h1 : |-γ₁| = |γ₁| := abs_neg γ₁
      calc |-γ₁ + γ₂ + γ₃| = |(-γ₁) + (γ₂ + γ₃)| := by ring
        _ ≤ |(-γ₁)| + |γ₂ + γ₃| := abs_add_le _ _
        _ ≤ 3 * H := by rw [h1, hγ1z, abs_zero, zero_add]; linarith [h23, hH1])
    simpa only [ofReal_neg, ofReal_add] using h
  -- ==================== the case analysis ====================
  have hpos := Work.ZeroFreeTables.Ksum_positivity_three (f := T.f) (fun t => T.f_nonneg t)
    (x₀ := T.x₀) (L := L) (β := β) (γ₁ := γ₁) (γ₂ := γ₂) (γ₃ := γ₃)
    T.x₀_pos hlogq T.f_supp χ₁ χ₂ χ₃
  have hbigOf : ∀ τ : ℝ, δ / 2 < |τ| → 200 ≤ |τ * L| := by
    intro τ hτ
    rw [abs_mul, abs_of_pos hlogq]
    have h1 : δ / 2 * L ≤ |τ| * L := mul_le_mul_of_nonneg_right hτ.le hlogq.le
    have h2 : 200 ≤ δ / 2 * L := by
      have h3 := (div_le_iff₀ hδ0).mp h400δ
      linarith
    linarith
  have h2not : χ₃ ^ 2 = 1 → χ₂ ^ 2 ≠ 1 := by
    intro h3r h2r
    apply hsq1
    have h6 : χ₁ = χ₂ * χ₃ := by
      calc χ₁ = (χ₁⁻¹)⁻¹ := (inv_inv χ₁).symm
        _ = (χ₂ * χ₃)⁻¹ := by rw [← hχ23]
        _ = χ₂ * χ₃ := by
              rw [mul_inv_rev, inv_eq_self_of_sq_eq_one' h2r,
                inv_eq_self_of_sq_eq_one' h3r, mul_comm χ₃ χ₂]
    calc χ₁ ^ 2 = (χ₂ * χ₃) ^ 2 := by rw [h6]
      _ = χ₂ ^ 2 * χ₃ ^ 2 := by rw [mul_pow]
      _ = 1 := by rw [h2r, h3r, one_mul]
  have h3not : χ₂ ^ 2 = 1 → χ₃ ^ 2 ≠ 1 := by
    intro h2r h3r
    exact (h2not h3r) h2r
  -- group bounds: principal triple + its companion pair
  have hgroupRing : (1/4) * (L * (T.f 0 / 6)) + (1/4) * (T.f 0 * ε' * L)
      + (1/2) * (T.f 0 * (1/6 + ε') * L) = (3/4) * (T.f 0 * (1/6 + ε') * L) := by ring
  have hg1 : (1/4) * Work.ZeroFreeTables.Ksum q T.f L
        ((β : ℂ) + ((γ₁ : ℂ) + (γ₂ : ℂ) + (γ₃ : ℂ)) * Complex.I) (χ₁ * χ₂ * χ₃)
      + (1/2) * Work.ZeroFreeTables.Ksum q T.f L
        ((β : ℂ) + ((γ₂ : ℂ) + (γ₃ : ℂ)) * Complex.I) (χ₂ * χ₃)
      ≤ (3/4) * (T.f 0 * (1/6 + ε') * L) := by
    by_cases hs1 : |γ₂ + γ₃| ≤ δ / 2
    · have hA1 := hA lam₁ ((γ₂ + γ₃) * L) hl1nn hl16
      have hmul : L * (T.Fc (((-lam₁ : ℝ) : ℂ) + (((γ₂ + γ₃) * L : ℝ) : ℂ) * Complex.I)).re
          - 2 * (L * (T.Fc ((((γ₂ + γ₃) * L : ℝ) : ℂ) * Complex.I)).re)
          ≤ L * (T.f 0 / 6) := by
        have h := mul_le_mul_of_nonneg_left hA1 hlogq.le
        nlinarith [h]
      linarith [hbT123, hbP23s hs1, hmul, hgroupRing]
    · have hbig := hbigOf (γ₂ + γ₃) (lt_of_not_ge hs1)
      have hB1 := hB lam₁ ((γ₂ + γ₃) * L) hl1nn hl16 hbig
      have hB1L : L * (T.Fc (((-lam₁ : ℝ) : ℂ) + (((γ₂ + γ₃) * L : ℝ) : ℂ) * Complex.I)).re
          ≤ L * (T.f 0 / 6) := mul_le_mul_of_nonneg_left hB1 hlogq.le
      linarith [hbT123, hB1L, hbP23g, hgroupRing]
  simp only [Work.ZeroFreeTables.Ksum] at hbP hbS1 hbS2 hbS3 hbP12 hbPi12 hbP13 hbPi13 hbP23g hbPi23g hbT123 hbT12i3 hbT1i23 hbT12i3g hbT1i23g hbTi123 hbP23s hg1
  have hmainRing : 7 * (T.f 0 * (1/6 + ε') * L) + T.f 0 * ε' * L
      = T.f 0 * (7/6 + 8 * ε') * L := by ring
  have hmain : 0 ≤ L * (T.F (-lam₁) - T.F 0 - T.F (lam₂ - lam₁) - T.F (lam₃ - lam₁))
      + T.f 0 * (7/6 + 8 * ε') * L := by
    by_cases h3r : χ₃ ^ 2 = 1
    · have h2c : χ₂ ^ 2 ≠ 1 := h2not h3r
      have hcharPi : χ₂ * χ₃⁻¹ = χ₁⁻¹ := by
        rw [inv_eq_self_of_sq_eq_one' h3r]
        exact hχ23
      have hzPi : Work.LinnikContract.zeroMult (χ₂ * χ₃⁻¹) ρ₁ ≠ 0 := by
        rw [hcharPi]; exact hρ1inv
      have hg2 : (1/4) * Work.ZeroFreeTables.Ksum q T.f L
            ((β : ℂ) + ((γ₁ : ℂ) + (γ₂ : ℂ) - (γ₃ : ℂ)) * Complex.I) (χ₁ * χ₂ * χ₃⁻¹)
          + (1/2) * Work.ZeroFreeTables.Ksum q T.f L
            ((β : ℂ) + ((γ₂ : ℂ) - (γ₃ : ℂ)) * Complex.I) (χ₂ * χ₃⁻¹)
          ≤ (3/4) * (T.f 0 * (1/6 + ε') * L) := by
        simp only [Work.ZeroFreeTables.Ksum]
        by_cases hs2 : |γ₂ - γ₃| ≤ δ / 2
        · have hA1 := hA lam₁ ((γ₂ - γ₃) * L) hl1nn hl16
          have hmul : L * (T.Fc (((-lam₁ : ℝ) : ℂ) + (((γ₂ - γ₃) * L : ℝ) : ℂ) * Complex.I)).re
              - 2 * (L * (T.Fc ((((γ₂ - γ₃) * L : ℝ) : ℂ) * Complex.I)).re)
              ≤ L * (T.f 0 / 6) := by
            have h := mul_le_mul_of_nonneg_left hA1 hlogq.le
            nlinarith [h]
          have hb2 := hbPi23s hzPi hs2
          simp only [Work.ZeroFreeTables.Ksum] at hb2
          nlinarith [hbT12i3 h3r, hb2, hmul, hgroupRing]
        · have hbig := hbigOf (γ₂ - γ₃) (lt_of_not_ge hs2)
          have hB1 := hB lam₁ ((γ₂ - γ₃) * L) hl1nn hl16 hbig
          have hB1L : L * (T.Fc (((-lam₁ : ℝ) : ℂ) + (((γ₂ - γ₃) * L : ℝ) : ℂ) * Complex.I)).re
              ≤ L * (T.f 0 / 6) := mul_le_mul_of_nonneg_left hB1 hlogq.le
          linarith [hbT12i3 h3r, hbPi23g, hB1L, hgroupRing]
      simp only [Work.ZeroFreeTables.Ksum] at hg2
      linarith [hpos, hbP, hbS1, hbS2, hbS3, hbP12, hbPi12, hbP13, hbPi13, hg1, hg2,
        hbT1i23g h2c, hbTi123, hmainRing]
    · by_cases h2r : χ₂ ^ 2 = 1
      · have hcharPi : χ₂ * χ₃⁻¹ = χ₁ := by
          have hχ₃inv : χ₃⁻¹ = χ₁ * χ₂ := by
            have h : χ₃ = χ₂⁻¹ * χ₁⁻¹ := by
              calc χ₃ = χ₂⁻¹ * (χ₂ * χ₃) := by rw [← mul_assoc, inv_mul_cancel, one_mul]
                _ = χ₂⁻¹ * χ₁⁻¹ := by rw [hχ23]
            calc χ₃⁻¹ = (χ₂⁻¹ * χ₁⁻¹)⁻¹ := by rw [h]
              _ = χ₁ * χ₂ := by rw [mul_inv_rev, inv_inv, inv_inv]
          rw [hχ₃inv]
          calc χ₂ * (χ₁ * χ₂) = χ₁ * (χ₂ * χ₂) := by ac_rfl
            _ = χ₁ * χ₂ ^ 2 := by rw [pow_two]
            _ = χ₁ * 1 := by rw [h2r]
            _ = χ₁ := mul_one χ₁
        have hzPi : Work.LinnikContract.zeroMult (χ₂ * χ₃⁻¹) ρ₁ ≠ 0 := by
          rw [hcharPi]; exact hR.1.2.1
        have hg3 : (1/4) * Work.ZeroFreeTables.Ksum q T.f L
              ((β : ℂ) + ((γ₁ : ℂ) - (γ₂ : ℂ) + (γ₃ : ℂ)) * Complex.I) (χ₁ * χ₂⁻¹ * χ₃)
            + (1/2) * Work.ZeroFreeTables.Ksum q T.f L
              ((β : ℂ) + ((γ₂ : ℂ) - (γ₃ : ℂ)) * Complex.I) (χ₂ * χ₃⁻¹)
            ≤ (3/4) * (T.f 0 * (1/6 + ε') * L) := by
          simp only [Work.ZeroFreeTables.Ksum]
          have heven : (T.Fc (((-lam₁ : ℝ) : ℂ)
                + (((γ₃ - γ₂) * L : ℝ) : ℂ) * Complex.I)).re
              = (T.Fc (((-lam₁ : ℝ) : ℂ)
                + (((γ₂ - γ₃) * L : ℝ) : ℂ) * Complex.I)).re := by
            have h := TestFn_Fc_conj T
              (((-lam₁ : ℝ) : ℂ) + (((γ₂ - γ₃) * L : ℝ) : ℂ) * Complex.I)
            have h1 : starRingEnd ℂ (((-lam₁ : ℝ) : ℂ)
                  + (((γ₂ - γ₃) * L : ℝ) : ℂ) * Complex.I)
                = (((-lam₁ : ℝ) : ℂ) + (((γ₃ - γ₂) * L : ℝ) : ℂ) * Complex.I) := by
              rw [map_add, map_mul, starRingEnd_apply, Complex.star_def, Complex.conj_ofReal,
                starRingEnd_apply, Complex.star_def, Complex.conj_I, Complex.conj_ofReal]
              push_cast
              ring
            rw [h1] at h
            rw [h, starRingEnd_apply, Complex.star_def]
            exact Complex.conj_re _
          by_cases hs2 : |γ₂ - γ₃| ≤ δ / 2
          · have hA1 := hA lam₁ ((γ₂ - γ₃) * L) hl1nn hl16
            have hmul : L * (T.Fc (((-lam₁ : ℝ) : ℂ)
                  + (((γ₂ - γ₃) * L : ℝ) : ℂ) * Complex.I)).re
                - 2 * (L * (T.Fc ((((γ₂ - γ₃) * L : ℝ) : ℂ) * Complex.I)).re)
                ≤ L * (T.f 0 / 6) := by
              have h := mul_le_mul_of_nonneg_left hA1 hlogq.le
              nlinarith [h]
            have hb2 := hbPi23s hzPi hs2
            simp only [Work.ZeroFreeTables.Ksum] at hb2
            nlinarith [hbT1i23 h2r, heven, hb2, hmul, hgroupRing]
          · have hbig := hbigOf (γ₂ - γ₃) (lt_of_not_ge hs2)
            have hbig' : 200 ≤ |(γ₃ - γ₂) * L| := by
              rw [show (γ₃ - γ₂) * L = -((γ₂ - γ₃) * L) by ring, abs_neg]
              exact hbig
            have hB1 := hB lam₁ ((γ₃ - γ₂) * L) hl1nn hl16 hbig'
            have hB1L : L * (T.Fc (((-lam₁ : ℝ) : ℂ)
                  + (((γ₃ - γ₂) * L : ℝ) : ℂ) * Complex.I)).re
                ≤ L * (T.f 0 / 6) := mul_le_mul_of_nonneg_left hB1 hlogq.le
            linarith [hbT1i23 h2r, hbPi23g, hB1L, hgroupRing]
        simp only [Work.ZeroFreeTables.Ksum] at hg3
        linarith [hpos, hbP, hbS1, hbS2, hbS3, hbP12, hbPi12, hbP13, hbPi13, hg1, hg3,
          hbT12i3g (h3not h2r), hbTi123, hmainRing]
      · linarith [hpos, hbP, hbS1, hbS2, hbS3, hbP12, hbPi12, hbP13, hbPi13, hg1,
          hbPi23g, hbT12i3g h3r, hbT1i23g h2r, hbTi123, hmainRing]
  have hX : 0 ≤ T.F (-lam₁) - T.F 0 - T.F (lam₂ - lam₁) - T.F (lam₃ - lam₁)
      + T.f 0 * (7/6 + 8 * ε') := by
    by_contra hneg
    push_neg at hneg
    have h2 : L * (T.F (-lam₁) - T.F 0 - T.F (lam₂ - lam₁) - T.F (lam₃ - lam₁)
        + T.f 0 * (7/6 + 8 * ε')) < 0 := mul_neg_of_pos_of_neg hlogq hneg
    have h3 : L * (T.F (-lam₁) - T.F 0 - T.F (lam₂ - lam₁) - T.F (lam₃ - lam₁)
        + T.f 0 * (7/6 + 8 * ε')) = L * (T.F (-lam₁) - T.F 0 - T.F (lam₂ - lam₁)
          - T.F (lam₃ - lam₁)) + T.f 0 * (7/6 + 8 * ε') * L := by ring
    linarith [hmain, h2, h3]
  rw [hlam₁, hlam₂, hlam₃] at hX
  exact hX

end Work.OffAxis
