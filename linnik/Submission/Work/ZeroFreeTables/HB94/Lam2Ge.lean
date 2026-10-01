import Mathlib
import Submission.Work.ZeroFreeTables.HB95plus.Main
import Submission.Work.ZeroFreeTables.HB95plus.tf72_numeric_inputs
import Submission.Work.ZeroFreeTables.HBProps
import Submission.Work.NumberTheory.Linnik.scratch_l62app_phi
import Submission.Work.ZeroFreeTables.HB94.hbLemma6_2_engine_restricted

open DirichletCharacter Complex
open Work.LinnikContract
open scoped Classical BigOperators
open MeasureTheory

noncomputable section

namespace Work.ZeroFreeTables.HB94

open Work.ZeroFreeTables

lemma tf72F17_le_La_aux (hlam : (0:ℝ) < (17:ℝ)/20) (a : ℝ) (ha : a ≤ (348:ℝ)/1000) :
    (tf72T ((17:ℝ)/20) hlam).F (-a) ≤ (11105:ℝ)/10000 := by
  set G : ℝ → ℝ := fun t => Real.exp (a * t) * tf72f ((17:ℝ)/20) t with hG
  have hcont : ContinuousOn G (Set.Icc (0:ℝ) (8/3)) := by
    rw [hG]
    exact ((Real.continuous_exp.comp (continuous_const.mul continuous_id)).continuousOn).mul
      ((tf72f_cont ((17:ℝ)/20) hlam).mono (fun t ht => ht.1))
  have hzero : ∀ t ∈ Set.Icc ((40:ℝ)/17) (8/3), G t = 0 := by
    intro t ht
    have ht2 : (2:ℝ)/((17:ℝ)/20) ≤ t := by
      rw [show (2:ℝ)/((17:ℝ)/20) = (40:ℝ)/17 by norm_num]; exact ht.1
    rw [hG]
    simp only
    rw [tf72f_supp ((17:ℝ)/20) hlam t ht2, mul_zero]
  have htrunc := Work.ZeroFreeTables.HB95plus.intervalIntegral_eq_of_eqOn_zero
      (F := G) (a := (0:ℝ)) (b := (40:ℝ)/17) (c := (8:ℝ)/3)
      (by norm_num) (by norm_num) hcont hzero
  have hL : (tf72T ((17:ℝ)/20) hlam).F (-a)
      = ∫ t in (0:ℝ)..((40:ℝ)/17), G t := by
    rw [TestFn_F_eq_integral]
    show (∫ t in (0:ℝ)..(2/((17:ℝ)/20)),
        Real.exp (-((-a) * t)) * tf72f ((17:ℝ)/20) t) = ∫ t in (0:ℝ)..((40:ℝ)/17), G t
    rw [show (2:ℝ)/((17:ℝ)/20) = (40:ℝ)/17 by norm_num]
    refine intervalIntegral.integral_congr (fun t _ => ?_)
    rw [hG]
    simp only
    rw [show -((-a) * t) = a * t from by ring]
  have hint2 : IntervalIntegrable
      (fun t : ℝ => Real.exp (((348:ℝ)/1000) * t) * tf72f ((17:ℝ)/20) t) MeasureTheory.volume (0:ℝ) (8/3) := by
    refine (((Real.continuous_exp.comp (continuous_const.mul continuous_id)).continuousOn).mul
      ((tf72f_cont ((17:ℝ)/20) hlam).mono (fun t ht => ht.1))).intervalIntegrable_of_Icc ?_
    norm_num
  calc (tf72T ((17:ℝ)/20) hlam).F (-a)
      = ∫ t in (0:ℝ)..((40:ℝ)/17), G t := hL
    _ = ∫ t in (0:ℝ)..(8/3), G t := htrunc.symm
    _ ≤ ∫ t in (0:ℝ)..(8/3),
          Real.exp (((348:ℝ)/1000) * t) * tf72f ((17:ℝ)/20) t := by
        apply intervalIntegral.integral_mono_on (by norm_num : (0:ℝ) ≤ 8/3)
        · exact hcont.intervalIntegrable_of_Icc (by norm_num)
        · exact hint2
        · intro t ht
          rw [hG]
          simp only
          exact mul_le_mul_of_nonneg_right
            (Real.exp_le_exp.mpr (by have h := mul_le_mul_of_nonneg_right ha ht.1; linarith))
            (tf72f_nonneg ((17:ℝ)/20) hlam t)
    _ ≤ (11105:ℝ)/10000 := by
        have hnum : Work.ZeroFreeTables.TfNumericInputs :=
          Work.ZeroFreeTables.HB95plus.tf72_numeric_inputs
        obtain ⟨-, -, -, h4, -⟩ := hnum
        exact h4

lemma tf72F17_ge_F472_aux (hlam : (0:ℝ) < (17:ℝ)/20) :
    (68:ℝ)/100 ≤ (tf72T ((17:ℝ)/20) hlam).F ((472:ℝ)/1000) := by
  set G : ℝ → ℝ := fun t => Real.exp (-(((472:ℝ)/1000) * t)) * tf72f ((17:ℝ)/20) t with hG
  have hcont : ContinuousOn G (Set.Icc (0:ℝ) (8/3)) := by
    rw [hG]
    exact ((Real.continuous_exp.comp ((continuous_const.mul continuous_id).neg)).continuousOn).mul
      ((tf72f_cont ((17:ℝ)/20) hlam).mono (fun t ht => ht.1))
  have hzero : ∀ t ∈ Set.Icc ((40:ℝ)/17) (8/3), G t = 0 := by
    intro t ht
    have ht2 : (2:ℝ)/((17:ℝ)/20) ≤ t := by
      rw [show (2:ℝ)/((17:ℝ)/20) = (40:ℝ)/17 by norm_num]; exact ht.1
    rw [hG]
    simp only
    rw [tf72f_supp ((17:ℝ)/20) hlam t ht2, mul_zero]
  have htrunc := Work.ZeroFreeTables.HB95plus.intervalIntegral_eq_of_eqOn_zero
      (F := G) (a := (0:ℝ)) (b := (40:ℝ)/17) (c := (8:ℝ)/3)
      (by norm_num) (by norm_num) hcont hzero
  have hL : (tf72T ((17:ℝ)/20) hlam).F ((472:ℝ)/1000)
      = ∫ t in (0:ℝ)..((40:ℝ)/17), G t := by
    rw [TestFn_F_eq_integral]
    show (∫ t in (0:ℝ)..(2/((17:ℝ)/20)),
        Real.exp (-(((472:ℝ)/1000) * t)) * tf72f ((17:ℝ)/20) t) = ∫ t in (0:ℝ)..((40:ℝ)/17), G t
    rw [show (2:ℝ)/((17:ℝ)/20) = (40:ℝ)/17 by norm_num]
  have h5 : (68:ℝ)/100 ≤ ∫ t in (0:ℝ)..(8/3), G t := by
    have hnum : Work.ZeroFreeTables.TfNumericInputs :=
      Work.ZeroFreeTables.HB95plus.tf72_numeric_inputs
    obtain ⟨-, -, -, -, h5'⟩ := hnum
    rw [hG]
    exact h5'
  calc (68:ℝ)/100 ≤ ∫ t in (0:ℝ)..(8/3), G t := h5
    _ = ∫ t in (0:ℝ)..((40:ℝ)/17), G t := htrunc
    _ = (tf72T ((17:ℝ)/20) hlam).F ((472:ℝ)/1000) := hL.symm

/-- **The second-minimum bound `λ₂ ≥ λ₁ + 472/1000`** for `λ₁ ≤ 348/1000`.

HB Lemma 6.2 with the test function `tf72T (17/20)` (`F 0 = 8/9`, `f 0 = 68/75`,
`x₀ = 40/17`) and the four characters `χ₁, χ, χ₁χ, χ₁χ⁻¹` all carrying the *unconditional*
constant `1/6` (so `ψ = 1/2`) gives
`0 ≤ F(-λ₁) - F(0) - F(λ(u) - λ₁) + (68/75)(1/2 + 4ε)`; with the engine
`Work.ZeroFreeTables.HB94.hbLemma6_2_engine_restricted` (proved, thresholded) this yields
`F(λ(u) - λ₁) ≤ La(λ₁) - 8/9 + (68/75)(1/2 + 4·(1/1000)) ≤ F(472/1000)` by
`Work.ZeroFreeTables.lam2_arith` and `TfNumericInputs` (both proved: `La(348/1000) ≤ 11105/10000`
and `F(472/1000) ≥ 68/100`), and strict antitonicity of `x ↦ ∫₀^{40/17} e^{-xt} tf72f (17/20) t`
(`Work.ZeroFreeTables.le_of_F_lt_of_le_F`, `HB95plus/Main.lean`) gives `λ(u) - λ₁ ≥ 472/1000`.

Window/maximality data come from `IsMin1WideAt 10 χ₁ ρ₁`; `χ` ranges over the working region with
`χ ∉ {χ₁, χ₁⁻¹}`.  (`ε = 1/1000`, `δ` as given.) -/
theorem Lam2Ge (δ : ℝ) (hδ0 : 0 < δ) (hδ1 : δ < 1) (q₁ : ℕ)
    (hL52 : ∀ q : ℕ, q₁ ≤ q → ∀ [NeZero q] (χ : DirichletCharacter ℂ q) [NeZero χ.conductor],
      χ ≠ 1 → Commons.NumberTheory.Linnik.L52Hyp χ ((1:ℝ)/6) (1/1000) δ) :
    ∃ q₀ : ℕ, ∀ q : ℕ, q₀ ≤ q → ∀ [NeZero q] (χ₁ : DirichletCharacter ℂ q) (ρ₁ : ℂ),
      Work.ZeroFreeTables.IsMin1WideAt 10 χ₁ ρ₁ →
      Work.LinnikContract.lamOf q ρ₁ ≤ 348/1000 →
      ∀ (χ : DirichletCharacter ℂ q) (u : ℂ), Work.LinnikContract.IsZ χ u →
        χ ≠ χ₁ → χ ≠ χ₁⁻¹ →
          Work.LinnikContract.lamOf q ρ₁ + 472/1000 ≤ Work.LinnikContract.lamOf q u := by
  have hl : (0:ℝ) < (17:ℝ)/20 := by norm_num
  let T : TestFn := tf72T ((17:ℝ)/20) hl
  obtain ⟨qE, hqE⟩ := hbLemma6_2_engine_restricted T ((1:ℝ)/6) ((1:ℝ)/1000) δ
    (by norm_num) hδ0 hδ1
  refine ⟨max q₁ qE, ?_⟩
  intro q hq _instq χ₁ ρ₁ hmin hl1 χ u hZ hne1 hne2
  have hq1 : q₁ ≤ q := by omega
  have hqE' : qE ≤ q := by omega
  have hF0 : T.F 0 = 8/9 := by
    show (tf72Fc ((17:ℝ)/20) ((0:ℝ) : ℂ)).re = 8/9
    rw [show ((0:ℝ) : ℂ) = 0 from by norm_num]
    exact tf72Fc_zero_re _ hl
  have hf0 : T.f 0 = 68/75 := by
    show tf72f ((17:ℝ)/20) 0 = 68/75
    rw [tf72f_at_zero _ hl]
    norm_num
  have hLa : T.F (-(lamOf q ρ₁)) ≤ (11105:ℝ)/10000 := tf72F17_le_La_aux hl _ hl1
  have hF472 : (68:ℝ)/100 ≤ T.F ((472:ℝ)/1000) := tf72F17_ge_F472_aux hl
  have hstrict : T.F (-(lamOf q ρ₁)) - 8/9 + (68/75) * (3 * ((1:ℝ)/6 + (1:ℝ)/1000))
      < T.F ((472:ℝ)/1000) := by
    have h12 := Work.ZeroFreeTables.lam2_arith hLa hF472
    have hcoef : (68:ℝ)/75 * (3 * ((1:ℝ)/6 + (1:ℝ)/1000))
        < (68:ℝ)/75 * (1/2 + 4 * ((1:ℝ)/1000)) := by norm_num
    linarith
  by_cases hcase : lamOf q u ≤ 1
  · haveI : NeZero χ₁.conductor := ⟨χ₁.conductor_ne_zero⟩
    haveI : NeZero χ.conductor := ⟨χ.conductor_ne_zero⟩
    haveI : NeZero (χ₁ * χ).conductor := ⟨(χ₁ * χ).conductor_ne_zero⟩
    haveI : NeZero (χ₁ * χ⁻¹).conductor := ⟨(χ₁ * χ⁻¹).conductor_ne_zero⟩
    have hneA : χ₁ * χ ≠ 1 := fun h => hne2 (eq_inv_of_mul_eq_one_right h)
    have hneB : χ₁ * χ⁻¹ ≠ 1 := fun h => hne1 ((mul_inv_eq_one.mp h).symm)
    have hcore := hqE q hqE' χ₁ χ ρ₁ u
      (hL52 q hq1 χ₁ hmin.1.1.1)
      (hL52 q hq1 χ hZ.1)
      (hL52 q hq1 (χ₁ * χ) hneA)
      (hL52 q hq1 (χ₁ * χ⁻¹) hneB)
      hmin hmin.1.1 hZ hmin.1.1.1 hZ.1 hne1 hne2 (by linarith) hcase
    have hmain : T.F (lamOf q u - lamOf q ρ₁)
        ≤ T.F (-(lamOf q ρ₁)) - 8/9 + (68/75) * (3 * ((1:ℝ)/6 + (1:ℝ)/1000)) := by
      rw [hF0, hf0] at hcore
      linarith
    by_contra hcon
    push_neg at hcon
    have hle : T.F ((472:ℝ)/1000) ≤ T.F (lamOf q u - lamOf q ρ₁) := by
      refine (TestFn_F_antitone T) ?_
      linarith
    linarith [hstrict, hmain, hle]
  · push_neg at hcase
    linarith

end Work.ZeroFreeTables.HB94
