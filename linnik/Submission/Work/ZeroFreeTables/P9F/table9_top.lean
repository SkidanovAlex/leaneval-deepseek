
/-
# P9F — the Table 9 assembly (HB Lemma 9.2 for the twenty rows)

For every row `(λ₁, λ_j)` of HB's Table 9 (p. 55) we apply the `F`-method inequality of Lemma 9.2
(`hbLemma9_2_engine`), whose window input `L52Hyp` with the constant `1/6 + 10⁻⁶` is supplied by
the hypothesis `L52Supply`, to a hypothetical bad pair `(χ_j, ρ_j)`; we identify `T.F` with the
real-axis Laplace transform `La` of Lemma 7.1's test function and contradict the numerical
certificate `rowcontra_*` at the tabulated point.  The Heath-Brown numbering argument
(`lam3_of_row`) then gives `Lam3Bound χ₁ λ_j`.

`L52Supply` is the paper's Lemma 3.1 with `φ = 1/3` (the Burgess input): it is
`Work.LinnikAreas.DhCapped.l52HypExplicit`, re-exported through this file's hypothesis so that the
assembly below does not itself depend on the analytic chain.
-/
import Mathlib
import Submission.Work.ZeroFreeTables.HBProps
import Submission.Work.ZeroFreeTables.P9F.assembly
import Submission.Work.ZeroFreeTables.P9F.table9_rows
import Submission.Work.ZeroFreeTables.P9F.table9_certs
import Submission.Work.ZeroFreeTables.P9F.hbLemma9_2_engine
import Submission.Work.ZeroFreeTables.P9F.tf71F_real_eq
import Submission.Work.ZeroFreeTables.P9F.arctan_bounds
import Submission.Work.ZeroFreeTables.testFn7_1

open DirichletCharacter Complex
open scoped Real
noncomputable section

namespace Work.ZeroFreeTables.P9F

open Work.ZeroFreeTables Work.LinnikContract

/-- The analytic input of the Table 9 computation: Heath-Brown's Lemma 3.1 with `φ = 1/3`, i.e.
`Commons.NumberTheory.Linnik.L52Hyp χ (1/6 + 10⁻⁶) ε δ` for every non-principal `χ` and every
`ε > 0`, with window radius `δ` and for all large levels `q`.  (This is
`Work.LinnikAreas.DhCapped.l52HypExplicit`; it is the Burgess input of the paper and is not proved
here.) -/
def L52Supply : Prop :=
  ∃ δ : ℝ, 0 < δ ∧ δ < 1 ∧ ∃ q₀ : ℕ, ∀ q : ℕ, q₀ ≤ q → ∀ [NeZero q]
    (χ : DirichletCharacter ℂ q) [NeZero χ.conductor], χ ≠ 1 → ∀ ε : ℝ, 0 < ε →
      Commons.NumberTheory.Linnik.L52Hyp χ (1/6 + 1/1000000) ε δ

/-- A level so large that `2 ≤ √(log log q)` (needed to run the engine at `λ ≤ 2`). -/
def Qsq : ℕ := Nat.ceil (Real.exp (Real.exp 4)) + 1

theorem sqrt_loglog_ge_two {q : ℕ} (hq : Qsq ≤ q) :
    2 ≤ Real.sqrt (Real.log (Real.log (q : ℝ))) := by
  have h1 : Real.exp (Real.exp 4) ≤ (q : ℝ) := by
    have h2 : Real.exp (Real.exp 4) ≤ ((Nat.ceil (Real.exp (Real.exp 4)) : ℕ) : ℝ) :=
      Nat.le_ceil _
    have h3 : ((Nat.ceil (Real.exp (Real.exp 4)) : ℕ) : ℝ) + 1 ≤ (q : ℝ) := by
      exact_mod_cast hq
    linarith
  have h4 : Real.exp 4 ≤ Real.log (q : ℝ) := by
    have := Real.log_le_log (Real.exp_pos (Real.exp 4)) h1
    rwa [Real.log_exp] at this
  have h5 : (4 : ℝ) ≤ Real.log (Real.log (q : ℝ)) := by
    have := Real.log_le_log (Real.exp_pos 4) h4
    rwa [Real.log_exp] at this
  rw [Real.le_sqrt (by norm_num) (by linarith)]
  linarith

/-- **The bridge between the engine's `T.F` and the real-axis Laplace transform `La`** of
Lemma 7.1's test function: `T.F x = La θ lam (−x)`. -/
theorem tf71T_F_eq_La (θ lam : ℝ) (hθ0 : 0 < θ) (hθ1 : θ < Real.pi / 2) (hlam : 0 < lam)
    (x : ℝ) : (tf71T θ lam hθ0 hθ1 hlam).F x = La θ lam (-x) := by
  rw [TestFn_F_eq_integral]
  unfold La
  simp only [tf71T]
  apply intervalIntegral.integral_congr
  intro t _
  simp only [neg_mul]

theorem arctan25_bounds :
    (3827044099179/2500000000000 : ℝ) ≤ Real.arctan 25 ∧
    Real.arctan 25 ≤ (153081763967161/100000000000000 : ℝ) := by
  obtain ⟨h1, h2⟩ := arctan_of_inv_bounds 25 (by norm_num) 10
    (3827044099179/2500000000000) (153081763967161/100000000000000) (by norm_num) (by norm_num)
  exact ⟨h1, h2⟩

theorem arctan24_bounds :
    (15291537476963/10000000000000 : ℝ) ≤ Real.arctan 24 ∧
    Real.arctan 24 ≤ (152915374769631/100000000000000 : ℝ) := by
  obtain ⟨h1, h2⟩ := arctan_of_inv_bounds 24 (by norm_num) 10
    (15291537476963/10000000000000) (152915374769631/100000000000000) (by norm_num) (by norm_num)
  exact ⟨h1, h2⟩

theorem arctan15_bounds :
    (150422816301907/100000000000000 : ℝ) ≤ Real.arctan 15 ∧
    Real.arctan 15 ≤ (37605704075477/25000000000000 : ℝ) := by
  obtain ⟨h1, h2⟩ := arctan_of_inv_bounds 15 (by norm_num) 10
    (150422816301907/100000000000000) (37605704075477/25000000000000) (by norm_num) (by norm_num)
  exact ⟨h1, h2⟩

/-- **HB Table 9, row `λ₁ ≤ 34/100 ⟹ λ_j ≥ 1283/1000`.** -/
theorem row_034_1283 (Q : ℕ) (hsup : L52Supply) :
    ∃ Q' : ℕ, Q ≤ Q' ∧ ∀ q : ℕ, Q' ≤ q → ∀ [NeZero q] (χ₁ : DirichletCharacter ℂ q) (ρ₁ : ℂ),
      IsMin1WideAt 10 χ₁ ρ₁ → χ₁ ^ 2 ≠ 1 → lamOf q ρ₁ ≤ ((34/100 : ℚ) : ℝ) →
      Lam3Bound χ₁ (((1283/1000 : ℚ) : ℝ)) := by
  obtain ⟨δ, hδ0, hδ1, qA, hA⟩ := hsup
  have hθ0 : 0 < Real.arctan (25:ℝ) := Real.arctan_pos.mpr (by norm_num)
  have hθπ : Real.arctan (25:ℝ) < Real.pi / 2 := Real.arctan_lt_pi_div_two _
  have htanθ : Real.tan (Real.arctan (25:ℝ)) = (25/1 : ℝ) := by
    rw [Real.tan_arctan]; norm_num
  have hlampos : (0:ℝ) < (21/500 : ℝ) := by norm_num
  obtain ⟨qE, hqE⟩ := hbLemma9_2_engine (tf71T (Real.arctan (25:ℝ)) (21/500:ℝ) hθ0 hθπ hlampos)
      (81/100:ℝ) (1/6 + 1/1000000) (1/1000000000000) δ (by norm_num) (by norm_num) hδ0 hδ1
  refine ⟨max (max Q qA) (max qE Qsq), ?_, ?_⟩
  · exact le_trans (le_max_left _ _) (le_max_left _ _)
  intro q hq _inst χ₁ ρ₁ hmin hcplx hlam1
  have hqA' : qA ≤ q := by omega
  have hqE' : qE ≤ q := by omega
  have hsq : 2 ≤ Real.sqrt (Real.log (Real.log (q : ℝ))) := sqrt_loglog_ge_two (by omega)
  obtain ⟨hTlo, hThi⟩ := arctan25_bounds
  have hθlo : (3827044099179/2500000000000 : ℝ) ≤ Real.arctan (25:ℝ) := hTlo
  have hθhi : Real.arctan (25:ℝ) ≤ (153081763967161/100000000000000 : ℝ) := hThi
  refine lam3_of_row (a := ((34/100 : ℚ) : ℝ)) (c := ((1283/1000 : ℚ) : ℝ))
    (θ := Real.arctan (25:ℝ)) (lam := (21/500:ℝ)) (k := (81/100:ℝ))
    (slack := (4496782761/5000000000:ℝ)) hmin hcplx hlam1 ?_ ?_
  · intro χj ρj hZj hne1 hne2 h3 h4 hlaj
    have hE := hqE q hqE' χ₁ χj ρ₁ ρj
      (fun χ _ hχ => hA q hqA' χ hχ (1/1000000000000) (by norm_num))
      hmin hmin.1.1 hZj hmin.1.1.1 hZj.1 hne1 hne2 hcplx h3 h4
      (by linarith [hlam1]) (by linarith [hlaj]) hsq
    rw [tf71T_F_eq_La (Real.arctan (25:ℝ)) (21/500:ℝ) hθ0 hθπ hlampos (-(lamOf q ρ₁)),
        tf71T_F_eq_La (Real.arctan (25:ℝ)) (21/500:ℝ) hθ0 hθπ hlampos (lamOf q ρj - lamOf q ρ₁),
        tf71T_F_eq_La (Real.arctan (25:ℝ)) (21/500:ℝ) hθ0 hθπ hlampos 0] at hE
    simp only [neg_neg, neg_sub, neg_zero, tf71T] at hE
    have hf0 : 0 ≤ tf71f (Real.arctan (25:ℝ)) (21/500:ℝ) 0 := tf71f_nonneg _ _ hθ0 hθπ hlampos 0
    have hsl : ((81/100:ℝ) ^ 2 + 4 * (81/100:ℝ) + 3/2) * (1/6 + 1/1000000 + 1/1000000000000)
        ≤ (4496782761/5000000000:ℝ) := by norm_num
    linarith [hE, mul_nonneg hf0 (sub_nonneg.mpr hsl)]
  · intro la1 laj h0 h1 h2 hineq
    refine rowcontra_034_1283 hθlo hθhi htanθ h0 ?_ ?_ hineq
    · have h' : ((34/100 : ℚ) : ℝ) = (17/50 : ℝ) := by norm_num
      linarith
    · have h' : ((1283/1000 : ℚ) : ℝ) = (1283/1000 : ℝ) := by norm_num
      linarith


/-- **HB Table 9, row `λ₁ ≤ 36/100 ⟹ λ_j ≥ 1230/1000`.** -/
theorem row_036_123 (Q : ℕ) (hsup : L52Supply) :
    ∃ Q' : ℕ, Q ≤ Q' ∧ ∀ q : ℕ, Q' ≤ q → ∀ [NeZero q] (χ₁ : DirichletCharacter ℂ q) (ρ₁ : ℂ),
      IsMin1WideAt 10 χ₁ ρ₁ → χ₁ ^ 2 ≠ 1 → lamOf q ρ₁ ≤ ((36/100 : ℚ) : ℝ) →
      Lam3Bound χ₁ (((1230/1000 : ℚ) : ℝ)) := by
  obtain ⟨δ, hδ0, hδ1, qA, hA⟩ := hsup
  have hθ0 : 0 < Real.arctan (25:ℝ) := Real.arctan_pos.mpr (by norm_num)
  have hθπ : Real.arctan (25:ℝ) < Real.pi / 2 := Real.arctan_lt_pi_div_two _
  have htanθ : Real.tan (Real.arctan (25:ℝ)) = (25/1 : ℝ) := by
    rw [Real.tan_arctan]; norm_num
  have hlampos : (0:ℝ) < (21/500 : ℝ) := by norm_num
  obtain ⟨qE, hqE⟩ := hbLemma9_2_engine (tf71T (Real.arctan (25:ℝ)) (21/500:ℝ) hθ0 hθπ hlampos)
      (407/500:ℝ) (1/6 + 1/1000000) (1/1000000000000) δ (by norm_num) (by norm_num) hδ0 hδ1
  refine ⟨max (max Q qA) (max qE Qsq), ?_, ?_⟩
  · exact le_trans (le_max_left _ _) (le_max_left _ _)
  intro q hq _inst χ₁ ρ₁ hmin hcplx hlam1
  have hqA' : qA ≤ q := by omega
  have hqE' : qE ≤ q := by omega
  have hsq : 2 ≤ Real.sqrt (Real.log (Real.log (q : ℝ))) := sqrt_loglog_ge_two (by omega)
  obtain ⟨hTlo, hThi⟩ := arctan25_bounds
  have hθlo : (3827044099179/2500000000000 : ℝ) ≤ Real.arctan (25:ℝ) := hTlo
  have hθhi : Real.arctan (25:ℝ) ≤ (153081763967161/100000000000000 : ℝ) := hThi
  refine lam3_of_row (a := ((36/100 : ℚ) : ℝ)) (c := ((1230/1000 : ℚ) : ℝ))
    (θ := Real.arctan (25:ℝ)) (lam := (21/500:ℝ)) (k := (407/500:ℝ))
    (slack := (338664717947/375000000000:ℝ)) hmin hcplx hlam1 ?_ ?_
  · intro χj ρj hZj hne1 hne2 h3 h4 hlaj
    have hE := hqE q hqE' χ₁ χj ρ₁ ρj
      (fun χ _ hχ => hA q hqA' χ hχ (1/1000000000000) (by norm_num))
      hmin hmin.1.1 hZj hmin.1.1.1 hZj.1 hne1 hne2 hcplx h3 h4
      (by linarith [hlam1]) (by linarith [hlaj]) hsq
    rw [tf71T_F_eq_La (Real.arctan (25:ℝ)) (21/500:ℝ) hθ0 hθπ hlampos (-(lamOf q ρ₁)),
        tf71T_F_eq_La (Real.arctan (25:ℝ)) (21/500:ℝ) hθ0 hθπ hlampos (lamOf q ρj - lamOf q ρ₁),
        tf71T_F_eq_La (Real.arctan (25:ℝ)) (21/500:ℝ) hθ0 hθπ hlampos 0] at hE
    simp only [neg_neg, neg_sub, neg_zero, tf71T] at hE
    have hf0 : 0 ≤ tf71f (Real.arctan (25:ℝ)) (21/500:ℝ) 0 := tf71f_nonneg _ _ hθ0 hθπ hlampos 0
    have hsl : ((407/500:ℝ) ^ 2 + 4 * (407/500:ℝ) + 3/2) * (1/6 + 1/1000000 + 1/1000000000000)
        ≤ (338664717947/375000000000:ℝ) := by norm_num
    linarith [hE, mul_nonneg hf0 (sub_nonneg.mpr hsl)]
  · intro la1 laj h0 h1 h2 hineq
    refine rowcontra_036_123 hθlo hθhi htanθ h0 ?_ ?_ hineq
    · have h' : ((36/100 : ℚ) : ℝ) = (9/25 : ℝ) := by norm_num
      linarith
    · have h' : ((1230/1000 : ℚ) : ℝ) = (123/100 : ℝ) := by norm_num
      linarith


/-- **HB Table 9, row `λ₁ ≤ 38/100 ⟹ λ_j ≥ 1181/1000`.** -/
theorem row_038_1181 (Q : ℕ) (hsup : L52Supply) :
    ∃ Q' : ℕ, Q ≤ Q' ∧ ∀ q : ℕ, Q' ≤ q → ∀ [NeZero q] (χ₁ : DirichletCharacter ℂ q) (ρ₁ : ℂ),
      IsMin1WideAt 10 χ₁ ρ₁ → χ₁ ^ 2 ≠ 1 → lamOf q ρ₁ ≤ ((38/100 : ℚ) : ℝ) →
      Lam3Bound χ₁ (((1181/1000 : ℚ) : ℝ)) := by
  obtain ⟨δ, hδ0, hδ1, qA, hA⟩ := hsup
  have hθ0 : 0 < Real.arctan (24:ℝ) := Real.arctan_pos.mpr (by norm_num)
  have hθπ : Real.arctan (24:ℝ) < Real.pi / 2 := Real.arctan_lt_pi_div_two _
  have htanθ : Real.tan (Real.arctan (24:ℝ)) = (24/1 : ℝ) := by
    rw [Real.tan_arctan]; norm_num
  have hlampos : (0:ℝ) < (9/200 : ℝ) := by norm_num
  obtain ⟨qE, hqE⟩ := hbLemma9_2_engine (tf71T (Real.arctan (24:ℝ)) (9/200:ℝ) hθ0 hθπ hlampos)
      (817/1000:ℝ) (1/6 + 1/1000000) (1/1000000000000) δ (by norm_num) (by norm_num) hδ0 hδ1
  refine ⟨max (max Q qA) (max qE Qsq), ?_, ?_⟩
  · exact le_trans (le_max_left _ _) (le_max_left _ _)
  intro q hq _inst χ₁ ρ₁ hmin hcplx hlam1
  have hqA' : qA ≤ q := by omega
  have hqE' : qE ≤ q := by omega
  have hsq : 2 ≤ Real.sqrt (Real.log (Real.log (q : ℝ))) := sqrt_loglog_ge_two (by omega)
  obtain ⟨hTlo, hThi⟩ := arctan24_bounds
  have hθlo : (15291537476963/10000000000000 : ℝ) ≤ Real.arctan (24:ℝ) := hTlo
  have hθhi : Real.arctan (24:ℝ) ≤ (152915374769631/100000000000000 : ℝ) := hThi
  refine lam3_of_row (a := ((38/100 : ℚ) : ℝ)) (c := ((1181/1000 : ℚ) : ℝ))
    (θ := Real.arctan (24:ℝ)) (lam := (9/200:ℝ)) (k := (817/1000:ℝ))
    (slack := (1358882154467/1500000000000:ℝ)) hmin hcplx hlam1 ?_ ?_
  · intro χj ρj hZj hne1 hne2 h3 h4 hlaj
    have hE := hqE q hqE' χ₁ χj ρ₁ ρj
      (fun χ _ hχ => hA q hqA' χ hχ (1/1000000000000) (by norm_num))
      hmin hmin.1.1 hZj hmin.1.1.1 hZj.1 hne1 hne2 hcplx h3 h4
      (by linarith [hlam1]) (by linarith [hlaj]) hsq
    rw [tf71T_F_eq_La (Real.arctan (24:ℝ)) (9/200:ℝ) hθ0 hθπ hlampos (-(lamOf q ρ₁)),
        tf71T_F_eq_La (Real.arctan (24:ℝ)) (9/200:ℝ) hθ0 hθπ hlampos (lamOf q ρj - lamOf q ρ₁),
        tf71T_F_eq_La (Real.arctan (24:ℝ)) (9/200:ℝ) hθ0 hθπ hlampos 0] at hE
    simp only [neg_neg, neg_sub, neg_zero, tf71T] at hE
    have hf0 : 0 ≤ tf71f (Real.arctan (24:ℝ)) (9/200:ℝ) 0 := tf71f_nonneg _ _ hθ0 hθπ hlampos 0
    have hsl : ((817/1000:ℝ) ^ 2 + 4 * (817/1000:ℝ) + 3/2) * (1/6 + 1/1000000 + 1/1000000000000)
        ≤ (1358882154467/1500000000000:ℝ) := by norm_num
    linarith [hE, mul_nonneg hf0 (sub_nonneg.mpr hsl)]
  · intro la1 laj h0 h1 h2 hineq
    refine rowcontra_038_1181 hθlo hθhi htanθ h0 ?_ ?_ hineq
    · have h' : ((38/100 : ℚ) : ℝ) = (19/50 : ℝ) := by norm_num
      linarith
    · have h' : ((1181/1000 : ℚ) : ℝ) = (1181/1000 : ℝ) := by norm_num
      linarith


/-- **HB Table 9, row `λ₁ ≤ 40/100 ⟹ λ_j ≥ 1135/1000`.** -/
theorem row_04_1135 (Q : ℕ) (hsup : L52Supply) :
    ∃ Q' : ℕ, Q ≤ Q' ∧ ∀ q : ℕ, Q' ≤ q → ∀ [NeZero q] (χ₁ : DirichletCharacter ℂ q) (ρ₁ : ℂ),
      IsMin1WideAt 10 χ₁ ρ₁ → χ₁ ^ 2 ≠ 1 → lamOf q ρ₁ ≤ ((40/100 : ℚ) : ℝ) →
      Lam3Bound χ₁ (((1135/1000 : ℚ) : ℝ)) := by
  obtain ⟨δ, hδ0, hδ1, qA, hA⟩ := hsup
  have hθ0 : 0 < Real.arctan (25:ℝ) := Real.arctan_pos.mpr (by norm_num)
  have hθπ : Real.arctan (25:ℝ) < Real.pi / 2 := Real.arctan_lt_pi_div_two _
  have htanθ : Real.tan (Real.arctan (25:ℝ)) = (25/1 : ℝ) := by
    rw [Real.tan_arctan]; norm_num
  have hlampos : (0:ℝ) < (11/250 : ℝ) := by norm_num
  obtain ⟨qE, hqE⟩ := hbLemma9_2_engine (tf71T (Real.arctan (25:ℝ)) (11/250:ℝ) hθ0 hθπ hlampos)
      (41/50:ℝ) (1/6 + 1/1000000) (1/1000000000000) δ (by norm_num) (by norm_num) hδ0 hδ1
  refine ⟨max (max Q qA) (max qE Qsq), ?_, ?_⟩
  · exact le_trans (le_max_left _ _) (le_max_left _ _)
  intro q hq _inst χ₁ ρ₁ hmin hcplx hlam1
  have hqA' : qA ≤ q := by omega
  have hqE' : qE ≤ q := by omega
  have hsq : 2 ≤ Real.sqrt (Real.log (Real.log (q : ℝ))) := sqrt_loglog_ge_two (by omega)
  obtain ⟨hTlo, hThi⟩ := arctan25_bounds
  have hθlo : (3827044099179/2500000000000 : ℝ) ≤ Real.arctan (25:ℝ) := hTlo
  have hθhi : Real.arctan (25:ℝ) ≤ (153081763967161/100000000000000 : ℝ) := hThi
  refine lam3_of_row (a := ((40/100 : ℚ) : ℝ)) (c := ((1135/1000 : ℚ) : ℝ))
    (θ := Real.arctan (25:ℝ)) (lam := (11/250:ℝ)) (k := (41/50:ℝ))
    (slack := (3407774843/3750000000:ℝ)) hmin hcplx hlam1 ?_ ?_
  · intro χj ρj hZj hne1 hne2 h3 h4 hlaj
    have hE := hqE q hqE' χ₁ χj ρ₁ ρj
      (fun χ _ hχ => hA q hqA' χ hχ (1/1000000000000) (by norm_num))
      hmin hmin.1.1 hZj hmin.1.1.1 hZj.1 hne1 hne2 hcplx h3 h4
      (by linarith [hlam1]) (by linarith [hlaj]) hsq
    rw [tf71T_F_eq_La (Real.arctan (25:ℝ)) (11/250:ℝ) hθ0 hθπ hlampos (-(lamOf q ρ₁)),
        tf71T_F_eq_La (Real.arctan (25:ℝ)) (11/250:ℝ) hθ0 hθπ hlampos (lamOf q ρj - lamOf q ρ₁),
        tf71T_F_eq_La (Real.arctan (25:ℝ)) (11/250:ℝ) hθ0 hθπ hlampos 0] at hE
    simp only [neg_neg, neg_sub, neg_zero, tf71T] at hE
    have hf0 : 0 ≤ tf71f (Real.arctan (25:ℝ)) (11/250:ℝ) 0 := tf71f_nonneg _ _ hθ0 hθπ hlampos 0
    have hsl : ((41/50:ℝ) ^ 2 + 4 * (41/50:ℝ) + 3/2) * (1/6 + 1/1000000 + 1/1000000000000)
        ≤ (3407774843/3750000000:ℝ) := by norm_num
    linarith [hE, mul_nonneg hf0 (sub_nonneg.mpr hsl)]
  · intro la1 laj h0 h1 h2 hineq
    refine rowcontra_04_1135 hθlo hθhi htanθ h0 ?_ ?_ hineq
    · have h' : ((40/100 : ℚ) : ℝ) = (2/5 : ℝ) := by norm_num
      linarith
    · have h' : ((1135/1000 : ℚ) : ℝ) = (227/200 : ℝ) := by norm_num
      linarith


/-- **HB Table 9, row `λ₁ ≤ 42/100 ⟹ λ_j ≥ 1094/1000`.** -/
theorem row_042_1094 (Q : ℕ) (hsup : L52Supply) :
    ∃ Q' : ℕ, Q ≤ Q' ∧ ∀ q : ℕ, Q' ≤ q → ∀ [NeZero q] (χ₁ : DirichletCharacter ℂ q) (ρ₁ : ℂ),
      IsMin1WideAt 10 χ₁ ρ₁ → χ₁ ^ 2 ≠ 1 → lamOf q ρ₁ ≤ ((42/100 : ℚ) : ℝ) →
      Lam3Bound χ₁ (((1094/1000 : ℚ) : ℝ)) := by
  obtain ⟨δ, hδ0, hδ1, qA, hA⟩ := hsup
  have hθ0 : 0 < Real.arctan (24:ℝ) := Real.arctan_pos.mpr (by norm_num)
  have hθπ : Real.arctan (24:ℝ) < Real.pi / 2 := Real.arctan_lt_pi_div_two _
  have htanθ : Real.tan (Real.arctan (24:ℝ)) = (24/1 : ℝ) := by
    rw [Real.tan_arctan]; norm_num
  have hlampos : (0:ℝ) < (23/500 : ℝ) := by norm_num
  obtain ⟨qE, hqE⟩ := hbLemma9_2_engine (tf71T (Real.arctan (24:ℝ)) (23/500:ℝ) hθ0 hθπ hlampos)
      (411/500:ℝ) (1/6 + 1/1000000) (1/1000000000000) δ (by norm_num) (by norm_num) hδ0 hδ1
  refine ⟨max (max Q qA) (max qE Qsq), ?_, ?_⟩
  · exact le_trans (le_max_left _ _) (le_max_left _ _)
  intro q hq _inst χ₁ ρ₁ hmin hcplx hlam1
  have hqA' : qA ≤ q := by omega
  have hqE' : qE ≤ q := by omega
  have hsq : 2 ≤ Real.sqrt (Real.log (Real.log (q : ℝ))) := sqrt_loglog_ge_two (by omega)
  obtain ⟨hTlo, hThi⟩ := arctan24_bounds
  have hθlo : (15291537476963/10000000000000 : ℝ) ≤ Real.arctan (24:ℝ) := hTlo
  have hθhi : Real.arctan (24:ℝ) ≤ (152915374769631/100000000000000 : ℝ) := hThi
  refine lam3_of_row (a := ((42/100 : ℚ) : ℝ)) (c := ((1094/1000 : ℚ) : ℝ))
    (θ := Real.arctan (24:ℝ)) (lam := (23/500:ℝ)) (k := (411/500:ℝ))
    (slack := (113827579921/125000000000:ℝ)) hmin hcplx hlam1 ?_ ?_
  · intro χj ρj hZj hne1 hne2 h3 h4 hlaj
    have hE := hqE q hqE' χ₁ χj ρ₁ ρj
      (fun χ _ hχ => hA q hqA' χ hχ (1/1000000000000) (by norm_num))
      hmin hmin.1.1 hZj hmin.1.1.1 hZj.1 hne1 hne2 hcplx h3 h4
      (by linarith [hlam1]) (by linarith [hlaj]) hsq
    rw [tf71T_F_eq_La (Real.arctan (24:ℝ)) (23/500:ℝ) hθ0 hθπ hlampos (-(lamOf q ρ₁)),
        tf71T_F_eq_La (Real.arctan (24:ℝ)) (23/500:ℝ) hθ0 hθπ hlampos (lamOf q ρj - lamOf q ρ₁),
        tf71T_F_eq_La (Real.arctan (24:ℝ)) (23/500:ℝ) hθ0 hθπ hlampos 0] at hE
    simp only [neg_neg, neg_sub, neg_zero, tf71T] at hE
    have hf0 : 0 ≤ tf71f (Real.arctan (24:ℝ)) (23/500:ℝ) 0 := tf71f_nonneg _ _ hθ0 hθπ hlampos 0
    have hsl : ((411/500:ℝ) ^ 2 + 4 * (411/500:ℝ) + 3/2) * (1/6 + 1/1000000 + 1/1000000000000)
        ≤ (113827579921/125000000000:ℝ) := by norm_num
    linarith [hE, mul_nonneg hf0 (sub_nonneg.mpr hsl)]
  · intro la1 laj h0 h1 h2 hineq
    refine rowcontra_042_1094 hθlo hθhi htanθ h0 ?_ ?_ hineq
    · have h' : ((42/100 : ℚ) : ℝ) = (21/50 : ℝ) := by norm_num
      linarith
    · have h' : ((1094/1000 : ℚ) : ℝ) = (547/500 : ℝ) := by norm_num
      linarith


/-- **HB Table 9, row `λ₁ ≤ 44/100 ⟹ λ_j ≥ 1055/1000`.** -/
theorem row_044_1055 (Q : ℕ) (hsup : L52Supply) :
    ∃ Q' : ℕ, Q ≤ Q' ∧ ∀ q : ℕ, Q' ≤ q → ∀ [NeZero q] (χ₁ : DirichletCharacter ℂ q) (ρ₁ : ℂ),
      IsMin1WideAt 10 χ₁ ρ₁ → χ₁ ^ 2 ≠ 1 → lamOf q ρ₁ ≤ ((44/100 : ℚ) : ℝ) →
      Lam3Bound χ₁ (((1055/1000 : ℚ) : ℝ)) := by
  obtain ⟨δ, hδ0, hδ1, qA, hA⟩ := hsup
  have hθ0 : 0 < Real.arctan (25:ℝ) := Real.arctan_pos.mpr (by norm_num)
  have hθπ : Real.arctan (25:ℝ) < Real.pi / 2 := Real.arctan_lt_pi_div_two _
  have htanθ : Real.tan (Real.arctan (25:ℝ)) = (25/1 : ℝ) := by
    rw [Real.tan_arctan]; norm_num
  have hlampos : (0:ℝ) < (23/500 : ℝ) := by norm_num
  obtain ⟨qE, hqE⟩ := hbLemma9_2_engine (tf71T (Real.arctan (25:ℝ)) (23/500:ℝ) hθ0 hθπ hlampos)
      (33/40:ℝ) (1/6 + 1/1000000) (1/1000000000000) δ (by norm_num) (by norm_num) hδ0 hδ1
  refine ⟨max (max Q qA) (max qE Qsq), ?_, ?_⟩
  · exact le_trans (le_max_left _ _) (le_max_left _ _)
  intro q hq _inst χ₁ ρ₁ hmin hcplx hlam1
  have hqA' : qA ≤ q := by omega
  have hqE' : qE ≤ q := by omega
  have hsq : 2 ≤ Real.sqrt (Real.log (Real.log (q : ℝ))) := sqrt_loglog_ge_two (by omega)
  obtain ⟨hTlo, hThi⟩ := arctan25_bounds
  have hθlo : (3827044099179/2500000000000 : ℝ) ≤ Real.arctan (25:ℝ) := hTlo
  have hθhi : Real.arctan (25:ℝ) ≤ (153081763967161/100000000000000 : ℝ) := hThi
  refine lam3_of_row (a := ((44/100 : ℚ) : ℝ)) (c := ((1055/1000 : ℚ) : ℝ))
    (θ := Real.arctan (25:ℝ)) (lam := (23/500:ℝ)) (k := (33/40:ℝ))
    (slack := (730755329/800000000:ℝ)) hmin hcplx hlam1 ?_ ?_
  · intro χj ρj hZj hne1 hne2 h3 h4 hlaj
    have hE := hqE q hqE' χ₁ χj ρ₁ ρj
      (fun χ _ hχ => hA q hqA' χ hχ (1/1000000000000) (by norm_num))
      hmin hmin.1.1 hZj hmin.1.1.1 hZj.1 hne1 hne2 hcplx h3 h4
      (by linarith [hlam1]) (by linarith [hlaj]) hsq
    rw [tf71T_F_eq_La (Real.arctan (25:ℝ)) (23/500:ℝ) hθ0 hθπ hlampos (-(lamOf q ρ₁)),
        tf71T_F_eq_La (Real.arctan (25:ℝ)) (23/500:ℝ) hθ0 hθπ hlampos (lamOf q ρj - lamOf q ρ₁),
        tf71T_F_eq_La (Real.arctan (25:ℝ)) (23/500:ℝ) hθ0 hθπ hlampos 0] at hE
    simp only [neg_neg, neg_sub, neg_zero, tf71T] at hE
    have hf0 : 0 ≤ tf71f (Real.arctan (25:ℝ)) (23/500:ℝ) 0 := tf71f_nonneg _ _ hθ0 hθπ hlampos 0
    have hsl : ((33/40:ℝ) ^ 2 + 4 * (33/40:ℝ) + 3/2) * (1/6 + 1/1000000 + 1/1000000000000)
        ≤ (730755329/800000000:ℝ) := by norm_num
    linarith [hE, mul_nonneg hf0 (sub_nonneg.mpr hsl)]
  · intro la1 laj h0 h1 h2 hineq
    refine rowcontra_044_1055 hθlo hθhi htanθ h0 ?_ ?_ hineq
    · have h' : ((44/100 : ℚ) : ℝ) = (11/25 : ℝ) := by norm_num
      linarith
    · have h' : ((1055/1000 : ℚ) : ℝ) = (211/200 : ℝ) := by norm_num
      linarith


/-- **HB Table 9, row `λ₁ ≤ 46/100 ⟹ λ_j ≥ 1018/1000`.** -/
theorem row_046_1018 (Q : ℕ) (hsup : L52Supply) :
    ∃ Q' : ℕ, Q ≤ Q' ∧ ∀ q : ℕ, Q' ≤ q → ∀ [NeZero q] (χ₁ : DirichletCharacter ℂ q) (ρ₁ : ℂ),
      IsMin1WideAt 10 χ₁ ρ₁ → χ₁ ^ 2 ≠ 1 → lamOf q ρ₁ ≤ ((46/100 : ℚ) : ℝ) →
      Lam3Bound χ₁ (((1018/1000 : ℚ) : ℝ)) := by
  obtain ⟨δ, hδ0, hδ1, qA, hA⟩ := hsup
  have hθ0 : 0 < Real.arctan (25:ℝ) := Real.arctan_pos.mpr (by norm_num)
  have hθπ : Real.arctan (25:ℝ) < Real.pi / 2 := Real.arctan_lt_pi_div_two _
  have htanθ : Real.tan (Real.arctan (25:ℝ)) = (25/1 : ℝ) := by
    rw [Real.tan_arctan]; norm_num
  have hlampos : (0:ℝ) < (23/500 : ℝ) := by norm_num
  obtain ⟨qE, hqE⟩ := hbLemma9_2_engine (tf71T (Real.arctan (25:ℝ)) (23/500:ℝ) hθ0 hθπ hlampos)
      (207/250:ℝ) (1/6 + 1/1000000) (1/1000000000000) δ (by norm_num) (by norm_num) hδ0 hδ1
  refine ⟨max (max Q qA) (max qE Qsq), ?_, ?_⟩
  · exact le_trans (le_max_left _ _) (le_max_left _ _)
  intro q hq _inst χ₁ ρ₁ hmin hcplx hlam1
  have hqA' : qA ≤ q := by omega
  have hqE' : qE ≤ q := by omega
  have hsq : 2 ≤ Real.sqrt (Real.log (Real.log (q : ℝ))) := sqrt_loglog_ge_two (by omega)
  obtain ⟨hTlo, hThi⟩ := arctan25_bounds
  have hθlo : (3827044099179/2500000000000 : ℝ) ≤ Real.arctan (25:ℝ) := hTlo
  have hθhi : Real.arctan (25:ℝ) ≤ (153081763967161/100000000000000 : ℝ) := hThi
  refine lam3_of_row (a := ((46/100 : ℚ) : ℝ)) (c := ((1018/1000 : ℚ) : ℝ))
    (θ := Real.arctan (25:ℝ)) (lam := (23/500:ℝ)) (k := (207/250:ℝ))
    (slack := (28633458849/31250000000:ℝ)) hmin hcplx hlam1 ?_ ?_
  · intro χj ρj hZj hne1 hne2 h3 h4 hlaj
    have hE := hqE q hqE' χ₁ χj ρ₁ ρj
      (fun χ _ hχ => hA q hqA' χ hχ (1/1000000000000) (by norm_num))
      hmin hmin.1.1 hZj hmin.1.1.1 hZj.1 hne1 hne2 hcplx h3 h4
      (by linarith [hlam1]) (by linarith [hlaj]) hsq
    rw [tf71T_F_eq_La (Real.arctan (25:ℝ)) (23/500:ℝ) hθ0 hθπ hlampos (-(lamOf q ρ₁)),
        tf71T_F_eq_La (Real.arctan (25:ℝ)) (23/500:ℝ) hθ0 hθπ hlampos (lamOf q ρj - lamOf q ρ₁),
        tf71T_F_eq_La (Real.arctan (25:ℝ)) (23/500:ℝ) hθ0 hθπ hlampos 0] at hE
    simp only [neg_neg, neg_sub, neg_zero, tf71T] at hE
    have hf0 : 0 ≤ tf71f (Real.arctan (25:ℝ)) (23/500:ℝ) 0 := tf71f_nonneg _ _ hθ0 hθπ hlampos 0
    have hsl : ((207/250:ℝ) ^ 2 + 4 * (207/250:ℝ) + 3/2) * (1/6 + 1/1000000 + 1/1000000000000)
        ≤ (28633458849/31250000000:ℝ) := by norm_num
    linarith [hE, mul_nonneg hf0 (sub_nonneg.mpr hsl)]
  · intro la1 laj h0 h1 h2 hineq
    refine rowcontra_046_1018 hθlo hθhi htanθ h0 ?_ ?_ hineq
    · have h' : ((46/100 : ℚ) : ℝ) = (23/50 : ℝ) := by norm_num
      linarith
    · have h' : ((1018/1000 : ℚ) : ℝ) = (509/500 : ℝ) := by norm_num
      linarith


/-- **HB Table 9, row `λ₁ ≤ 48/100 ⟹ λ_j ≥ 984/1000`.** -/
theorem row_048_0984 (Q : ℕ) (hsup : L52Supply) :
    ∃ Q' : ℕ, Q ≤ Q' ∧ ∀ q : ℕ, Q' ≤ q → ∀ [NeZero q] (χ₁ : DirichletCharacter ℂ q) (ρ₁ : ℂ),
      IsMin1WideAt 10 χ₁ ρ₁ → χ₁ ^ 2 ≠ 1 → lamOf q ρ₁ ≤ ((48/100 : ℚ) : ℝ) →
      Lam3Bound χ₁ (((984/1000 : ℚ) : ℝ)) := by
  obtain ⟨δ, hδ0, hδ1, qA, hA⟩ := hsup
  have hθ0 : 0 < Real.arctan (25:ℝ) := Real.arctan_pos.mpr (by norm_num)
  have hθπ : Real.arctan (25:ℝ) < Real.pi / 2 := Real.arctan_lt_pi_div_two _
  have htanθ : Real.tan (Real.arctan (25:ℝ)) = (25/1 : ℝ) := by
    rw [Real.tan_arctan]; norm_num
  have hlampos : (0:ℝ) < (47/1000 : ℝ) := by norm_num
  obtain ⟨qE, hqE⟩ := hbLemma9_2_engine (tf71T (Real.arctan (25:ℝ)) (47/1000:ℝ) hθ0 hθπ hlampos)
      (104/125:ℝ) (1/6 + 1/1000000) (1/1000000000000) δ (by norm_num) (by norm_num) hδ0 hδ1
  refine ⟨max (max Q qA) (max qE Qsq), ?_, ?_⟩
  · exact le_trans (le_max_left _ _) (le_max_left _ _)
  intro q hq _inst χ₁ ρ₁ hmin hcplx hlam1
  have hqA' : qA ≤ q := by omega
  have hqE' : qE ≤ q := by omega
  have hsq : 2 ≤ Real.sqrt (Real.log (Real.log (q : ℝ))) := sqrt_loglog_ge_two (by omega)
  obtain ⟨hTlo, hThi⟩ := arctan25_bounds
  have hθlo : (3827044099179/2500000000000 : ℝ) ≤ Real.arctan (25:ℝ) := hTlo
  have hθhi : Real.arctan (25:ℝ) ≤ (153081763967161/100000000000000 : ℝ) := hThi
  refine lam3_of_row (a := ((48/100 : ℚ) : ℝ)) (c := ((984/1000 : ℚ) : ℝ))
    (θ := Real.arctan (25:ℝ)) (lam := (47/1000:ℝ)) (k := (104/125:ℝ))
    (slack := (21563532323/23437500000:ℝ)) hmin hcplx hlam1 ?_ ?_
  · intro χj ρj hZj hne1 hne2 h3 h4 hlaj
    have hE := hqE q hqE' χ₁ χj ρ₁ ρj
      (fun χ _ hχ => hA q hqA' χ hχ (1/1000000000000) (by norm_num))
      hmin hmin.1.1 hZj hmin.1.1.1 hZj.1 hne1 hne2 hcplx h3 h4
      (by linarith [hlam1]) (by linarith [hlaj]) hsq
    rw [tf71T_F_eq_La (Real.arctan (25:ℝ)) (47/1000:ℝ) hθ0 hθπ hlampos (-(lamOf q ρ₁)),
        tf71T_F_eq_La (Real.arctan (25:ℝ)) (47/1000:ℝ) hθ0 hθπ hlampos (lamOf q ρj - lamOf q ρ₁),
        tf71T_F_eq_La (Real.arctan (25:ℝ)) (47/1000:ℝ) hθ0 hθπ hlampos 0] at hE
    simp only [neg_neg, neg_sub, neg_zero, tf71T] at hE
    have hf0 : 0 ≤ tf71f (Real.arctan (25:ℝ)) (47/1000:ℝ) 0 := tf71f_nonneg _ _ hθ0 hθπ hlampos 0
    have hsl : ((104/125:ℝ) ^ 2 + 4 * (104/125:ℝ) + 3/2) * (1/6 + 1/1000000 + 1/1000000000000)
        ≤ (21563532323/23437500000:ℝ) := by norm_num
    linarith [hE, mul_nonneg hf0 (sub_nonneg.mpr hsl)]
  · intro la1 laj h0 h1 h2 hineq
    refine rowcontra_048_0984 hθlo hθhi htanθ h0 ?_ ?_ hineq
    · have h' : ((48/100 : ℚ) : ℝ) = (12/25 : ℝ) := by norm_num
      linarith
    · have h' : ((984/1000 : ℚ) : ℝ) = (123/125 : ℝ) := by norm_num
      linarith


/-- **HB Table 9, row `λ₁ ≤ 50/100 ⟹ λ_j ≥ 952/1000`.** -/
theorem row_05_0952 (Q : ℕ) (hsup : L52Supply) :
    ∃ Q' : ℕ, Q ≤ Q' ∧ ∀ q : ℕ, Q' ≤ q → ∀ [NeZero q] (χ₁ : DirichletCharacter ℂ q) (ρ₁ : ℂ),
      IsMin1WideAt 10 χ₁ ρ₁ → χ₁ ^ 2 ≠ 1 → lamOf q ρ₁ ≤ ((50/100 : ℚ) : ℝ) →
      Lam3Bound χ₁ (((952/1000 : ℚ) : ℝ)) := by
  obtain ⟨δ, hδ0, hδ1, qA, hA⟩ := hsup
  have hθ0 : 0 < Real.arctan (25:ℝ) := Real.arctan_pos.mpr (by norm_num)
  have hθπ : Real.arctan (25:ℝ) < Real.pi / 2 := Real.arctan_lt_pi_div_two _
  have htanθ : Real.tan (Real.arctan (25:ℝ)) = (25/1 : ℝ) := by
    rw [Real.tan_arctan]; norm_num
  have hlampos : (0:ℝ) < (6/125 : ℝ) := by norm_num
  obtain ⟨qE, hqE⟩ := hbLemma9_2_engine (tf71T (Real.arctan (25:ℝ)) (6/125:ℝ) hθ0 hθπ hlampos)
      (417/500:ℝ) (1/6 + 1/1000000) (1/1000000000000) δ (by norm_num) (by norm_num) hδ0 hδ1
  refine ⟨max (max Q qA) (max qE Qsq), ?_, ?_⟩
  · exact le_trans (le_max_left _ _) (le_max_left _ _)
  intro q hq _inst χ₁ ρ₁ hmin hcplx hlam1
  have hqA' : qA ≤ q := by omega
  have hqE' : qE ≤ q := by omega
  have hsq : 2 ≤ Real.sqrt (Real.log (Real.log (q : ℝ))) := sqrt_loglog_ge_two (by omega)
  obtain ⟨hTlo, hThi⟩ := arctan25_bounds
  have hθlo : (3827044099179/2500000000000 : ℝ) ≤ Real.arctan (25:ℝ) := hTlo
  have hθhi : Real.arctan (25:ℝ) ≤ (153081763967161/100000000000000 : ℝ) := hThi
  refine lam3_of_row (a := ((50/100 : ℚ) : ℝ)) (c := ((952/1000 : ℚ) : ℝ))
    (θ := Real.arctan (25:ℝ)) (lam := (6/125:ℝ)) (k := (417/500:ℝ))
    (slack := (115241590889/125000000000:ℝ)) hmin hcplx hlam1 ?_ ?_
  · intro χj ρj hZj hne1 hne2 h3 h4 hlaj
    have hE := hqE q hqE' χ₁ χj ρ₁ ρj
      (fun χ _ hχ => hA q hqA' χ hχ (1/1000000000000) (by norm_num))
      hmin hmin.1.1 hZj hmin.1.1.1 hZj.1 hne1 hne2 hcplx h3 h4
      (by linarith [hlam1]) (by linarith [hlaj]) hsq
    rw [tf71T_F_eq_La (Real.arctan (25:ℝ)) (6/125:ℝ) hθ0 hθπ hlampos (-(lamOf q ρ₁)),
        tf71T_F_eq_La (Real.arctan (25:ℝ)) (6/125:ℝ) hθ0 hθπ hlampos (lamOf q ρj - lamOf q ρ₁),
        tf71T_F_eq_La (Real.arctan (25:ℝ)) (6/125:ℝ) hθ0 hθπ hlampos 0] at hE
    simp only [neg_neg, neg_sub, neg_zero, tf71T] at hE
    have hf0 : 0 ≤ tf71f (Real.arctan (25:ℝ)) (6/125:ℝ) 0 := tf71f_nonneg _ _ hθ0 hθπ hlampos 0
    have hsl : ((417/500:ℝ) ^ 2 + 4 * (417/500:ℝ) + 3/2) * (1/6 + 1/1000000 + 1/1000000000000)
        ≤ (115241590889/125000000000:ℝ) := by norm_num
    linarith [hE, mul_nonneg hf0 (sub_nonneg.mpr hsl)]
  · intro la1 laj h0 h1 h2 hineq
    refine rowcontra_05_0952 hθlo hθhi htanθ h0 ?_ ?_ hineq
    · have h' : ((50/100 : ℚ) : ℝ) = (1/2 : ℝ) := by norm_num
      linarith
    · have h' : ((952/1000 : ℚ) : ℝ) = (119/125 : ℝ) := by norm_num
      linarith


/-- **HB Table 9, row `λ₁ ≤ 52/100 ⟹ λ_j ≥ 922/1000`.** -/
theorem row_052_0922 (Q : ℕ) (hsup : L52Supply) :
    ∃ Q' : ℕ, Q ≤ Q' ∧ ∀ q : ℕ, Q' ≤ q → ∀ [NeZero q] (χ₁ : DirichletCharacter ℂ q) (ρ₁ : ℂ),
      IsMin1WideAt 10 χ₁ ρ₁ → χ₁ ^ 2 ≠ 1 → lamOf q ρ₁ ≤ ((52/100 : ℚ) : ℝ) →
      Lam3Bound χ₁ (((922/1000 : ℚ) : ℝ)) := by
  obtain ⟨δ, hδ0, hδ1, qA, hA⟩ := hsup
  have hθ0 : 0 < Real.arctan (25:ℝ) := Real.arctan_pos.mpr (by norm_num)
  have hθπ : Real.arctan (25:ℝ) < Real.pi / 2 := Real.arctan_lt_pi_div_two _
  have htanθ : Real.tan (Real.arctan (25:ℝ)) = (25/1 : ℝ) := by
    rw [Real.tan_arctan]; norm_num
  have hlampos : (0:ℝ) < (6/125 : ℝ) := by norm_num
  obtain ⟨qE, hqE⟩ := hbLemma9_2_engine (tf71T (Real.arctan (25:ℝ)) (6/125:ℝ) hθ0 hθπ hlampos)
      (209/250:ℝ) (1/6 + 1/1000000) (1/1000000000000) δ (by norm_num) (by norm_num) hδ0 hδ1
  refine ⟨max (max Q qA) (max qE Qsq), ?_, ?_⟩
  · exact le_trans (le_max_left _ _) (le_max_left _ _)
  intro q hq _inst χ₁ ρ₁ hmin hcplx hlam1
  have hqA' : qA ≤ q := by omega
  have hqE' : qE ≤ q := by omega
  have hsq : 2 ≤ Real.sqrt (Real.log (Real.log (q : ℝ))) := sqrt_loglog_ge_two (by omega)
  obtain ⟨hTlo, hThi⟩ := arctan25_bounds
  have hθlo : (3827044099179/2500000000000 : ℝ) ≤ Real.arctan (25:ℝ) := hTlo
  have hθhi : Real.arctan (25:ℝ) ≤ (153081763967161/100000000000000 : ℝ) := hThi
  refine lam3_of_row (a := ((52/100 : ℚ) : ℝ)) (c := ((922/1000 : ℚ) : ℝ))
    (θ := Real.arctan (25:ℝ)) (lam := (6/125:ℝ)) (k := (209/250:ℝ))
    (slack := (28869460681/31250000000:ℝ)) hmin hcplx hlam1 ?_ ?_
  · intro χj ρj hZj hne1 hne2 h3 h4 hlaj
    have hE := hqE q hqE' χ₁ χj ρ₁ ρj
      (fun χ _ hχ => hA q hqA' χ hχ (1/1000000000000) (by norm_num))
      hmin hmin.1.1 hZj hmin.1.1.1 hZj.1 hne1 hne2 hcplx h3 h4
      (by linarith [hlam1]) (by linarith [hlaj]) hsq
    rw [tf71T_F_eq_La (Real.arctan (25:ℝ)) (6/125:ℝ) hθ0 hθπ hlampos (-(lamOf q ρ₁)),
        tf71T_F_eq_La (Real.arctan (25:ℝ)) (6/125:ℝ) hθ0 hθπ hlampos (lamOf q ρj - lamOf q ρ₁),
        tf71T_F_eq_La (Real.arctan (25:ℝ)) (6/125:ℝ) hθ0 hθπ hlampos 0] at hE
    simp only [neg_neg, neg_sub, neg_zero, tf71T] at hE
    have hf0 : 0 ≤ tf71f (Real.arctan (25:ℝ)) (6/125:ℝ) 0 := tf71f_nonneg _ _ hθ0 hθπ hlampos 0
    have hsl : ((209/250:ℝ) ^ 2 + 4 * (209/250:ℝ) + 3/2) * (1/6 + 1/1000000 + 1/1000000000000)
        ≤ (28869460681/31250000000:ℝ) := by norm_num
    linarith [hE, mul_nonneg hf0 (sub_nonneg.mpr hsl)]
  · intro la1 laj h0 h1 h2 hineq
    refine rowcontra_052_0922 hθlo hθhi htanθ h0 ?_ ?_ hineq
    · have h' : ((52/100 : ℚ) : ℝ) = (13/25 : ℝ) := by norm_num
      linarith
    · have h' : ((922/1000 : ℚ) : ℝ) = (461/500 : ℝ) := by norm_num
      linarith


/-- **HB Table 9, row `λ₁ ≤ 54/100 ⟹ λ_j ≥ 893/1000`.** -/
theorem row_054_0893 (Q : ℕ) (hsup : L52Supply) :
    ∃ Q' : ℕ, Q ≤ Q' ∧ ∀ q : ℕ, Q' ≤ q → ∀ [NeZero q] (χ₁ : DirichletCharacter ℂ q) (ρ₁ : ℂ),
      IsMin1WideAt 10 χ₁ ρ₁ → χ₁ ^ 2 ≠ 1 → lamOf q ρ₁ ≤ ((54/100 : ℚ) : ℝ) →
      Lam3Bound χ₁ (((893/1000 : ℚ) : ℝ)) := by
  obtain ⟨δ, hδ0, hδ1, qA, hA⟩ := hsup
  have hθ0 : 0 < Real.arctan (25:ℝ) := Real.arctan_pos.mpr (by norm_num)
  have hθπ : Real.arctan (25:ℝ) < Real.pi / 2 := Real.arctan_lt_pi_div_two _
  have htanθ : Real.tan (Real.arctan (25:ℝ)) = (25/1 : ℝ) := by
    rw [Real.tan_arctan]; norm_num
  have hlampos : (0:ℝ) < (6/125 : ℝ) := by norm_num
  obtain ⟨qE, hqE⟩ := hbLemma9_2_engine (tf71T (Real.arctan (25:ℝ)) (6/125:ℝ) hθ0 hθπ hlampos)
      (419/500:ℝ) (1/6 + 1/1000000) (1/1000000000000) δ (by norm_num) (by norm_num) hδ0 hδ1
  refine ⟨max (max Q qA) (max qE Qsq), ?_, ?_⟩
  · exact le_trans (le_max_left _ _) (le_max_left _ _)
  intro q hq _inst χ₁ ρ₁ hmin hcplx hlam1
  have hqA' : qA ≤ q := by omega
  have hqE' : qE ≤ q := by omega
  have hsq : 2 ≤ Real.sqrt (Real.log (Real.log (q : ℝ))) := sqrt_loglog_ge_two (by omega)
  obtain ⟨hTlo, hThi⟩ := arctan25_bounds
  have hθlo : (3827044099179/2500000000000 : ℝ) ≤ Real.arctan (25:ℝ) := hTlo
  have hθhi : Real.arctan (25:ℝ) ≤ (153081763967161/100000000000000 : ℝ) := hThi
  refine lam3_of_row (a := ((54/100 : ℚ) : ℝ)) (c := ((893/1000 : ℚ) : ℝ))
    (θ := Real.arctan (25:ℝ)) (lam := (6/125:ℝ)) (k := (419/500:ℝ))
    (slack := (347142783683/375000000000:ℝ)) hmin hcplx hlam1 ?_ ?_
  · intro χj ρj hZj hne1 hne2 h3 h4 hlaj
    have hE := hqE q hqE' χ₁ χj ρ₁ ρj
      (fun χ _ hχ => hA q hqA' χ hχ (1/1000000000000) (by norm_num))
      hmin hmin.1.1 hZj hmin.1.1.1 hZj.1 hne1 hne2 hcplx h3 h4
      (by linarith [hlam1]) (by linarith [hlaj]) hsq
    rw [tf71T_F_eq_La (Real.arctan (25:ℝ)) (6/125:ℝ) hθ0 hθπ hlampos (-(lamOf q ρ₁)),
        tf71T_F_eq_La (Real.arctan (25:ℝ)) (6/125:ℝ) hθ0 hθπ hlampos (lamOf q ρj - lamOf q ρ₁),
        tf71T_F_eq_La (Real.arctan (25:ℝ)) (6/125:ℝ) hθ0 hθπ hlampos 0] at hE
    simp only [neg_neg, neg_sub, neg_zero, tf71T] at hE
    have hf0 : 0 ≤ tf71f (Real.arctan (25:ℝ)) (6/125:ℝ) 0 := tf71f_nonneg _ _ hθ0 hθπ hlampos 0
    have hsl : ((419/500:ℝ) ^ 2 + 4 * (419/500:ℝ) + 3/2) * (1/6 + 1/1000000 + 1/1000000000000)
        ≤ (347142783683/375000000000:ℝ) := by norm_num
    linarith [hE, mul_nonneg hf0 (sub_nonneg.mpr hsl)]
  · intro la1 laj h0 h1 h2 hineq
    refine rowcontra_054_0893 hθlo hθhi htanθ h0 ?_ ?_ hineq
    · have h' : ((54/100 : ℚ) : ℝ) = (27/50 : ℝ) := by norm_num
      linarith
    · have h' : ((893/1000 : ℚ) : ℝ) = (893/1000 : ℝ) := by norm_num
      linarith


/-- **HB Table 9, row `λ₁ ≤ 56/100 ⟹ λ_j ≥ 866/1000`.** -/
theorem row_056_0866 (Q : ℕ) (hsup : L52Supply) :
    ∃ Q' : ℕ, Q ≤ Q' ∧ ∀ q : ℕ, Q' ≤ q → ∀ [NeZero q] (χ₁ : DirichletCharacter ℂ q) (ρ₁ : ℂ),
      IsMin1WideAt 10 χ₁ ρ₁ → χ₁ ^ 2 ≠ 1 → lamOf q ρ₁ ≤ ((56/100 : ℚ) : ℝ) →
      Lam3Bound χ₁ (((866/1000 : ℚ) : ℝ)) := by
  obtain ⟨δ, hδ0, hδ1, qA, hA⟩ := hsup
  have hθ0 : 0 < Real.arctan (25:ℝ) := Real.arctan_pos.mpr (by norm_num)
  have hθπ : Real.arctan (25:ℝ) < Real.pi / 2 := Real.arctan_lt_pi_div_two _
  have htanθ : Real.tan (Real.arctan (25:ℝ)) = (25/1 : ℝ) := by
    rw [Real.tan_arctan]; norm_num
  have hlampos : (0:ℝ) < (49/1000 : ℝ) := by norm_num
  obtain ⟨qE, hqE⟩ := hbLemma9_2_engine (tf71T (Real.arctan (25:ℝ)) (49/1000:ℝ) hθ0 hθπ hlampos)
      (21/25:ℝ) (1/6 + 1/1000000) (1/1000000000000) δ (by norm_num) (by norm_num) hδ0 hδ1
  refine ⟨max (max Q qA) (max qE Qsq), ?_, ?_⟩
  · exact le_trans (le_max_left _ _) (le_max_left _ _)
  intro q hq _inst χ₁ ρ₁ hmin hcplx hlam1
  have hqA' : qA ≤ q := by omega
  have hqE' : qE ≤ q := by omega
  have hsq : 2 ≤ Real.sqrt (Real.log (Real.log (q : ℝ))) := sqrt_loglog_ge_two (by omega)
  obtain ⟨hTlo, hThi⟩ := arctan25_bounds
  have hθlo : (3827044099179/2500000000000 : ℝ) ≤ Real.arctan (25:ℝ) := hTlo
  have hθhi : Real.arctan (25:ℝ) ≤ (153081763967161/100000000000000 : ℝ) := hThi
  refine lam3_of_row (a := ((56/100 : ℚ) : ℝ)) (c := ((866/1000 : ℚ) : ℝ))
    (θ := Real.arctan (25:ℝ)) (lam := (49/1000:ℝ)) (k := (21/25:ℝ))
    (slack := (72469279/78125000:ℝ)) hmin hcplx hlam1 ?_ ?_
  · intro χj ρj hZj hne1 hne2 h3 h4 hlaj
    have hE := hqE q hqE' χ₁ χj ρ₁ ρj
      (fun χ _ hχ => hA q hqA' χ hχ (1/1000000000000) (by norm_num))
      hmin hmin.1.1 hZj hmin.1.1.1 hZj.1 hne1 hne2 hcplx h3 h4
      (by linarith [hlam1]) (by linarith [hlaj]) hsq
    rw [tf71T_F_eq_La (Real.arctan (25:ℝ)) (49/1000:ℝ) hθ0 hθπ hlampos (-(lamOf q ρ₁)),
        tf71T_F_eq_La (Real.arctan (25:ℝ)) (49/1000:ℝ) hθ0 hθπ hlampos (lamOf q ρj - lamOf q ρ₁),
        tf71T_F_eq_La (Real.arctan (25:ℝ)) (49/1000:ℝ) hθ0 hθπ hlampos 0] at hE
    simp only [neg_neg, neg_sub, neg_zero, tf71T] at hE
    have hf0 : 0 ≤ tf71f (Real.arctan (25:ℝ)) (49/1000:ℝ) 0 := tf71f_nonneg _ _ hθ0 hθπ hlampos 0
    have hsl : ((21/25:ℝ) ^ 2 + 4 * (21/25:ℝ) + 3/2) * (1/6 + 1/1000000 + 1/1000000000000)
        ≤ (72469279/78125000:ℝ) := by norm_num
    linarith [hE, mul_nonneg hf0 (sub_nonneg.mpr hsl)]
  · intro la1 laj h0 h1 h2 hineq
    refine rowcontra_056_0866 hθlo hθhi htanθ h0 ?_ ?_ hineq
    · have h' : ((56/100 : ℚ) : ℝ) = (14/25 : ℝ) := by norm_num
      linarith
    · have h' : ((866/1000 : ℚ) : ℝ) = (433/500 : ℝ) := by norm_num
      linarith


/-- **HB Table 9, row `λ₁ ≤ 58/100 ⟹ λ_j ≥ 840/1000`.** -/
theorem row_058_084 (Q : ℕ) (hsup : L52Supply) :
    ∃ Q' : ℕ, Q ≤ Q' ∧ ∀ q : ℕ, Q' ≤ q → ∀ [NeZero q] (χ₁ : DirichletCharacter ℂ q) (ρ₁ : ℂ),
      IsMin1WideAt 10 χ₁ ρ₁ → χ₁ ^ 2 ≠ 1 → lamOf q ρ₁ ≤ ((58/100 : ℚ) : ℝ) →
      Lam3Bound χ₁ (((840/1000 : ℚ) : ℝ)) := by
  obtain ⟨δ, hδ0, hδ1, qA, hA⟩ := hsup
  have hθ0 : 0 < Real.arctan (25:ℝ) := Real.arctan_pos.mpr (by norm_num)
  have hθπ : Real.arctan (25:ℝ) < Real.pi / 2 := Real.arctan_lt_pi_div_two _
  have htanθ : Real.tan (Real.arctan (25:ℝ)) = (25/1 : ℝ) := by
    rw [Real.tan_arctan]; norm_num
  have hlampos : (0:ℝ) < (1/20 : ℝ) := by norm_num
  obtain ⟨qE, hqE⟩ := hbLemma9_2_engine (tf71T (Real.arctan (25:ℝ)) (1/20:ℝ) hθ0 hθπ hlampos)
      (421/500:ℝ) (1/6 + 1/1000000) (1/1000000000000) δ (by norm_num) (by norm_num) hδ0 hδ1
  refine ⟨max (max Q qA) (max qE Qsq), ?_, ?_⟩
  · exact le_trans (le_max_left _ _) (le_max_left _ _)
  intro q hq _inst χ₁ ρ₁ hmin hcplx hlam1
  have hqA' : qA ≤ q := by omega
  have hqE' : qE ≤ q := by omega
  have hsq : 2 ≤ Real.sqrt (Real.log (Real.log (q : ℝ))) := sqrt_loglog_ge_two (by omega)
  obtain ⟨hTlo, hThi⟩ := arctan25_bounds
  have hθlo : (3827044099179/2500000000000 : ℝ) ≤ Real.arctan (25:ℝ) := hTlo
  have hθhi : Real.arctan (25:ℝ) ≤ (153081763967161/100000000000000 : ℝ) := hThi
  refine lam3_of_row (a := ((58/100 : ℚ) : ℝ)) (c := ((840/1000 : ℚ) : ℝ))
    (θ := Real.arctan (25:ℝ)) (lam := (1/20:ℝ)) (k := (421/500:ℝ))
    (slack := (116187598241/125000000000:ℝ)) hmin hcplx hlam1 ?_ ?_
  · intro χj ρj hZj hne1 hne2 h3 h4 hlaj
    have hE := hqE q hqE' χ₁ χj ρ₁ ρj
      (fun χ _ hχ => hA q hqA' χ hχ (1/1000000000000) (by norm_num))
      hmin hmin.1.1 hZj hmin.1.1.1 hZj.1 hne1 hne2 hcplx h3 h4
      (by linarith [hlam1]) (by linarith [hlaj]) hsq
    rw [tf71T_F_eq_La (Real.arctan (25:ℝ)) (1/20:ℝ) hθ0 hθπ hlampos (-(lamOf q ρ₁)),
        tf71T_F_eq_La (Real.arctan (25:ℝ)) (1/20:ℝ) hθ0 hθπ hlampos (lamOf q ρj - lamOf q ρ₁),
        tf71T_F_eq_La (Real.arctan (25:ℝ)) (1/20:ℝ) hθ0 hθπ hlampos 0] at hE
    simp only [neg_neg, neg_sub, neg_zero, tf71T] at hE
    have hf0 : 0 ≤ tf71f (Real.arctan (25:ℝ)) (1/20:ℝ) 0 := tf71f_nonneg _ _ hθ0 hθπ hlampos 0
    have hsl : ((421/500:ℝ) ^ 2 + 4 * (421/500:ℝ) + 3/2) * (1/6 + 1/1000000 + 1/1000000000000)
        ≤ (116187598241/125000000000:ℝ) := by norm_num
    linarith [hE, mul_nonneg hf0 (sub_nonneg.mpr hsl)]
  · intro la1 laj h0 h1 h2 hineq
    refine rowcontra_058_084 hθlo hθhi htanθ h0 ?_ ?_ hineq
    · have h' : ((58/100 : ℚ) : ℝ) = (29/50 : ℝ) := by norm_num
      linarith
    · have h' : ((840/1000 : ℚ) : ℝ) = (21/25 : ℝ) := by norm_num
      linarith


/-- **HB Table 9, row `λ₁ ≤ 60/100 ⟹ λ_j ≥ 816/1000`.** -/
theorem row_06_0816 (Q : ℕ) (hsup : L52Supply) :
    ∃ Q' : ℕ, Q ≤ Q' ∧ ∀ q : ℕ, Q' ≤ q → ∀ [NeZero q] (χ₁ : DirichletCharacter ℂ q) (ρ₁ : ℂ),
      IsMin1WideAt 10 χ₁ ρ₁ → χ₁ ^ 2 ≠ 1 → lamOf q ρ₁ ≤ ((60/100 : ℚ) : ℝ) →
      Lam3Bound χ₁ (((816/1000 : ℚ) : ℝ)) := by
  obtain ⟨δ, hδ0, hδ1, qA, hA⟩ := hsup
  have hθ0 : 0 < Real.arctan (15:ℝ) := Real.arctan_pos.mpr (by norm_num)
  have hθπ : Real.arctan (15:ℝ) < Real.pi / 2 := Real.arctan_lt_pi_div_two _
  have htanθ : Real.tan (Real.arctan (15:ℝ)) = (15/1 : ℝ) := by
    rw [Real.tan_arctan]; norm_num
  have hlampos : (0:ℝ) < (41/500 : ℝ) := by norm_num
  obtain ⟨qE, hqE⟩ := hbLemma9_2_engine (tf71T (Real.arctan (15:ℝ)) (41/500:ℝ) hθ0 hθπ hlampos)
      (211/250:ℝ) (1/6 + 1/1000000) (1/1000000000000) δ (by norm_num) (by norm_num) hδ0 hδ1
  refine ⟨max (max Q qA) (max qE Qsq), ?_, ?_⟩
  · exact le_trans (le_max_left _ _) (le_max_left _ _)
  intro q hq _inst χ₁ ρ₁ hmin hcplx hlam1
  have hqA' : qA ≤ q := by omega
  have hqE' : qE ≤ q := by omega
  have hsq : 2 ≤ Real.sqrt (Real.log (Real.log (q : ℝ))) := sqrt_loglog_ge_two (by omega)
  obtain ⟨hTlo, hThi⟩ := arctan15_bounds
  have hθlo : (150422816301907/100000000000000 : ℝ) ≤ Real.arctan (15:ℝ) := hTlo
  have hθhi : Real.arctan (15:ℝ) ≤ (37605704075477/25000000000000 : ℝ) := hThi
  refine lam3_of_row (a := ((60/100 : ℚ) : ℝ)) (c := ((816/1000 : ℚ) : ℝ))
    (θ := Real.arctan (15:ℝ)) (lam := (41/500:ℝ)) (k := (211/250:ℝ))
    (slack := (87318387563/93750000000:ℝ)) hmin hcplx hlam1 ?_ ?_
  · intro χj ρj hZj hne1 hne2 h3 h4 hlaj
    have hE := hqE q hqE' χ₁ χj ρ₁ ρj
      (fun χ _ hχ => hA q hqA' χ hχ (1/1000000000000) (by norm_num))
      hmin hmin.1.1 hZj hmin.1.1.1 hZj.1 hne1 hne2 hcplx h3 h4
      (by linarith [hlam1]) (by linarith [hlaj]) hsq
    rw [tf71T_F_eq_La (Real.arctan (15:ℝ)) (41/500:ℝ) hθ0 hθπ hlampos (-(lamOf q ρ₁)),
        tf71T_F_eq_La (Real.arctan (15:ℝ)) (41/500:ℝ) hθ0 hθπ hlampos (lamOf q ρj - lamOf q ρ₁),
        tf71T_F_eq_La (Real.arctan (15:ℝ)) (41/500:ℝ) hθ0 hθπ hlampos 0] at hE
    simp only [neg_neg, neg_sub, neg_zero, tf71T] at hE
    have hf0 : 0 ≤ tf71f (Real.arctan (15:ℝ)) (41/500:ℝ) 0 := tf71f_nonneg _ _ hθ0 hθπ hlampos 0
    have hsl : ((211/250:ℝ) ^ 2 + 4 * (211/250:ℝ) + 3/2) * (1/6 + 1/1000000 + 1/1000000000000)
        ≤ (87318387563/93750000000:ℝ) := by norm_num
    linarith [hE, mul_nonneg hf0 (sub_nonneg.mpr hsl)]
  · intro la1 laj h0 h1 h2 hineq
    refine rowcontra_06_0816 hθlo hθhi htanθ h0 ?_ ?_ hineq
    · have h' : ((60/100 : ℚ) : ℝ) = (3/5 : ℝ) := by norm_num
      linarith
    · have h' : ((816/1000 : ℚ) : ℝ) = (102/125 : ℝ) := by norm_num
      linarith


/-- **HB Table 9, row `λ₁ ≤ 62/100 ⟹ λ_j ≥ 792/1000`.** -/
theorem row_062_0792 (Q : ℕ) (hsup : L52Supply) :
    ∃ Q' : ℕ, Q ≤ Q' ∧ ∀ q : ℕ, Q' ≤ q → ∀ [NeZero q] (χ₁ : DirichletCharacter ℂ q) (ρ₁ : ℂ),
      IsMin1WideAt 10 χ₁ ρ₁ → χ₁ ^ 2 ≠ 1 → lamOf q ρ₁ ≤ ((62/100 : ℚ) : ℝ) →
      Lam3Bound χ₁ (((792/1000 : ℚ) : ℝ)) := by
  obtain ⟨δ, hδ0, hδ1, qA, hA⟩ := hsup
  have hθ0 : 0 < Real.arctan (25:ℝ) := Real.arctan_pos.mpr (by norm_num)
  have hθπ : Real.arctan (25:ℝ) < Real.pi / 2 := Real.arctan_lt_pi_div_two _
  have htanθ : Real.tan (Real.arctan (25:ℝ)) = (25/1 : ℝ) := by
    rw [Real.tan_arctan]; norm_num
  have hlampos : (0:ℝ) < (1/20 : ℝ) := by norm_num
  obtain ⟨qE, hqE⟩ := hbLemma9_2_engine (tf71T (Real.arctan (25:ℝ)) (1/20:ℝ) hθ0 hθπ hlampos)
      (847/1000:ℝ) (1/6 + 1/1000000) (1/1000000000000) δ (by norm_num) (by norm_num) hδ0 hδ1
  refine ⟨max (max Q qA) (max qE Qsq), ?_, ?_⟩
  · exact le_trans (le_max_left _ _) (le_max_left _ _)
  intro q hq _inst χ₁ ρ₁ hmin hcplx hlam1
  have hqA' : qA ≤ q := by omega
  have hqE' : qE ≤ q := by omega
  have hsq : 2 ≤ Real.sqrt (Real.log (Real.log (q : ℝ))) := sqrt_loglog_ge_two (by omega)
  obtain ⟨hTlo, hThi⟩ := arctan25_bounds
  have hθlo : (3827044099179/2500000000000 : ℝ) ≤ Real.arctan (25:ℝ) := hTlo
  have hθhi : Real.arctan (25:ℝ) ≤ (153081763967161/100000000000000 : ℝ) := hThi
  refine lam3_of_row (a := ((62/100 : ℚ) : ℝ)) (c := ((792/1000 : ℚ) : ℝ))
    (θ := Real.arctan (25:ℝ)) (lam := (1/20:ℝ)) (k := (847/1000:ℝ))
    (slack := (1401362484227/1500000000000:ℝ)) hmin hcplx hlam1 ?_ ?_
  · intro χj ρj hZj hne1 hne2 h3 h4 hlaj
    have hE := hqE q hqE' χ₁ χj ρ₁ ρj
      (fun χ _ hχ => hA q hqA' χ hχ (1/1000000000000) (by norm_num))
      hmin hmin.1.1 hZj hmin.1.1.1 hZj.1 hne1 hne2 hcplx h3 h4
      (by linarith [hlam1]) (by linarith [hlaj]) hsq
    rw [tf71T_F_eq_La (Real.arctan (25:ℝ)) (1/20:ℝ) hθ0 hθπ hlampos (-(lamOf q ρ₁)),
        tf71T_F_eq_La (Real.arctan (25:ℝ)) (1/20:ℝ) hθ0 hθπ hlampos (lamOf q ρj - lamOf q ρ₁),
        tf71T_F_eq_La (Real.arctan (25:ℝ)) (1/20:ℝ) hθ0 hθπ hlampos 0] at hE
    simp only [neg_neg, neg_sub, neg_zero, tf71T] at hE
    have hf0 : 0 ≤ tf71f (Real.arctan (25:ℝ)) (1/20:ℝ) 0 := tf71f_nonneg _ _ hθ0 hθπ hlampos 0
    have hsl : ((847/1000:ℝ) ^ 2 + 4 * (847/1000:ℝ) + 3/2) * (1/6 + 1/1000000 + 1/1000000000000)
        ≤ (1401362484227/1500000000000:ℝ) := by norm_num
    linarith [hE, mul_nonneg hf0 (sub_nonneg.mpr hsl)]
  · intro la1 laj h0 h1 h2 hineq
    refine rowcontra_062_0792 hθlo hθhi htanθ h0 ?_ ?_ hineq
    · have h' : ((62/100 : ℚ) : ℝ) = (31/50 : ℝ) := by norm_num
      linarith
    · have h' : ((792/1000 : ℚ) : ℝ) = (99/125 : ℝ) := by norm_num
      linarith


/-- **HB Table 9, row `λ₁ ≤ 64/100 ⟹ λ_j ≥ 770/1000`.** -/
theorem row_064_077 (Q : ℕ) (hsup : L52Supply) :
    ∃ Q' : ℕ, Q ≤ Q' ∧ ∀ q : ℕ, Q' ≤ q → ∀ [NeZero q] (χ₁ : DirichletCharacter ℂ q) (ρ₁ : ℂ),
      IsMin1WideAt 10 χ₁ ρ₁ → χ₁ ^ 2 ≠ 1 → lamOf q ρ₁ ≤ ((64/100 : ℚ) : ℝ) →
      Lam3Bound χ₁ (((770/1000 : ℚ) : ℝ)) := by
  obtain ⟨δ, hδ0, hδ1, qA, hA⟩ := hsup
  have hθ0 : 0 < Real.arctan (25:ℝ) := Real.arctan_pos.mpr (by norm_num)
  have hθπ : Real.arctan (25:ℝ) < Real.pi / 2 := Real.arctan_lt_pi_div_two _
  have htanθ : Real.tan (Real.arctan (25:ℝ)) = (25/1 : ℝ) := by
    rw [Real.tan_arctan]; norm_num
  have hlampos : (0:ℝ) < (51/1000 : ℝ) := by norm_num
  obtain ⟨qE, hqE⟩ := hbLemma9_2_engine (tf71T (Real.arctan (25:ℝ)) (51/1000:ℝ) hθ0 hθπ hlampos)
      (849/1000:ℝ) (1/6 + 1/1000000) (1/1000000000000) δ (by norm_num) (by norm_num) hδ0 hδ1
  refine ⟨max (max Q qA) (max qE Qsq), ?_, ?_⟩
  · exact le_trans (le_max_left _ _) (le_max_left _ _)
  intro q hq _inst χ₁ ρ₁ hmin hcplx hlam1
  have hqA' : qA ≤ q := by omega
  have hqE' : qE ≤ q := by omega
  have hsq : 2 ≤ Real.sqrt (Real.log (Real.log (q : ℝ))) := sqrt_loglog_ge_two (by omega)
  obtain ⟨hTlo, hThi⟩ := arctan25_bounds
  have hθlo : (3827044099179/2500000000000 : ℝ) ≤ Real.arctan (25:ℝ) := hTlo
  have hθhi : Real.arctan (25:ℝ) ≤ (153081763967161/100000000000000 : ℝ) := hThi
  refine lam3_of_row (a := ((64/100 : ℚ) : ℝ)) (c := ((770/1000 : ℚ) : ℝ))
    (θ := Real.arctan (25:ℝ)) (lam := (51/1000:ℝ)) (k := (849/1000:ℝ))
    (slack := (468070168801/500000000000:ℝ)) hmin hcplx hlam1 ?_ ?_
  · intro χj ρj hZj hne1 hne2 h3 h4 hlaj
    have hE := hqE q hqE' χ₁ χj ρ₁ ρj
      (fun χ _ hχ => hA q hqA' χ hχ (1/1000000000000) (by norm_num))
      hmin hmin.1.1 hZj hmin.1.1.1 hZj.1 hne1 hne2 hcplx h3 h4
      (by linarith [hlam1]) (by linarith [hlaj]) hsq
    rw [tf71T_F_eq_La (Real.arctan (25:ℝ)) (51/1000:ℝ) hθ0 hθπ hlampos (-(lamOf q ρ₁)),
        tf71T_F_eq_La (Real.arctan (25:ℝ)) (51/1000:ℝ) hθ0 hθπ hlampos (lamOf q ρj - lamOf q ρ₁),
        tf71T_F_eq_La (Real.arctan (25:ℝ)) (51/1000:ℝ) hθ0 hθπ hlampos 0] at hE
    simp only [neg_neg, neg_sub, neg_zero, tf71T] at hE
    have hf0 : 0 ≤ tf71f (Real.arctan (25:ℝ)) (51/1000:ℝ) 0 := tf71f_nonneg _ _ hθ0 hθπ hlampos 0
    have hsl : ((849/1000:ℝ) ^ 2 + 4 * (849/1000:ℝ) + 3/2) * (1/6 + 1/1000000 + 1/1000000000000)
        ≤ (468070168801/500000000000:ℝ) := by norm_num
    linarith [hE, mul_nonneg hf0 (sub_nonneg.mpr hsl)]
  · intro la1 laj h0 h1 h2 hineq
    refine rowcontra_064_077 hθlo hθhi htanθ h0 ?_ ?_ hineq
    · have h' : ((64/100 : ℚ) : ℝ) = (16/25 : ℝ) := by norm_num
      linarith
    · have h' : ((770/1000 : ℚ) : ℝ) = (77/100 : ℝ) := by norm_num
      linarith


/-- **HB Table 9, row `λ₁ ≤ 66/100 ⟹ λ_j ≥ 748/1000`.** -/
theorem row_066_0748 (Q : ℕ) (hsup : L52Supply) :
    ∃ Q' : ℕ, Q ≤ Q' ∧ ∀ q : ℕ, Q' ≤ q → ∀ [NeZero q] (χ₁ : DirichletCharacter ℂ q) (ρ₁ : ℂ),
      IsMin1WideAt 10 χ₁ ρ₁ → χ₁ ^ 2 ≠ 1 → lamOf q ρ₁ ≤ ((66/100 : ℚ) : ℝ) →
      Lam3Bound χ₁ (((748/1000 : ℚ) : ℝ)) := by
  obtain ⟨δ, hδ0, hδ1, qA, hA⟩ := hsup
  have hθ0 : 0 < Real.arctan (25:ℝ) := Real.arctan_pos.mpr (by norm_num)
  have hθπ : Real.arctan (25:ℝ) < Real.pi / 2 := Real.arctan_lt_pi_div_two _
  have htanθ : Real.tan (Real.arctan (25:ℝ)) = (25/1 : ℝ) := by
    rw [Real.tan_arctan]; norm_num
  have hlampos : (0:ℝ) < (13/250 : ℝ) := by norm_num
  obtain ⟨qE, hqE⟩ := hbLemma9_2_engine (tf71T (Real.arctan (25:ℝ)) (13/250:ℝ) hθ0 hθπ hlampos)
      (213/250:ℝ) (1/6 + 1/1000000) (1/1000000000000) δ (by norm_num) (by norm_num) hδ0 hδ1
  refine ⟨max (max Q qA) (max qE Qsq), ?_, ?_⟩
  · exact le_trans (le_max_left _ _) (le_max_left _ _)
  intro q hq _inst χ₁ ρ₁ hmin hcplx hlam1
  have hqA' : qA ≤ q := by omega
  have hqE' : qE ≤ q := by omega
  have hsq : 2 ≤ Real.sqrt (Real.log (Real.log (q : ℝ))) := sqrt_loglog_ge_two (by omega)
  obtain ⟨hTlo, hThi⟩ := arctan25_bounds
  have hθlo : (3827044099179/2500000000000 : ℝ) ≤ Real.arctan (25:ℝ) := hTlo
  have hθhi : Real.arctan (25:ℝ) ≤ (153081763967161/100000000000000 : ℝ) := hThi
  refine lam3_of_row (a := ((66/100 : ℚ) : ℝ)) (c := ((748/1000 : ℚ) : ℝ))
    (θ := Real.arctan (25:ℝ)) (lam := (13/250:ℝ)) (k := (213/250:ℝ))
    (slack := (29343464369/31250000000:ℝ)) hmin hcplx hlam1 ?_ ?_
  · intro χj ρj hZj hne1 hne2 h3 h4 hlaj
    have hE := hqE q hqE' χ₁ χj ρ₁ ρj
      (fun χ _ hχ => hA q hqA' χ hχ (1/1000000000000) (by norm_num))
      hmin hmin.1.1 hZj hmin.1.1.1 hZj.1 hne1 hne2 hcplx h3 h4
      (by linarith [hlam1]) (by linarith [hlaj]) hsq
    rw [tf71T_F_eq_La (Real.arctan (25:ℝ)) (13/250:ℝ) hθ0 hθπ hlampos (-(lamOf q ρ₁)),
        tf71T_F_eq_La (Real.arctan (25:ℝ)) (13/250:ℝ) hθ0 hθπ hlampos (lamOf q ρj - lamOf q ρ₁),
        tf71T_F_eq_La (Real.arctan (25:ℝ)) (13/250:ℝ) hθ0 hθπ hlampos 0] at hE
    simp only [neg_neg, neg_sub, neg_zero, tf71T] at hE
    have hf0 : 0 ≤ tf71f (Real.arctan (25:ℝ)) (13/250:ℝ) 0 := tf71f_nonneg _ _ hθ0 hθπ hlampos 0
    have hsl : ((213/250:ℝ) ^ 2 + 4 * (213/250:ℝ) + 3/2) * (1/6 + 1/1000000 + 1/1000000000000)
        ≤ (29343464369/31250000000:ℝ) := by norm_num
    linarith [hE, mul_nonneg hf0 (sub_nonneg.mpr hsl)]
  · intro la1 laj h0 h1 h2 hineq
    refine rowcontra_066_0748 hθlo hθhi htanθ h0 ?_ ?_ hineq
    · have h' : ((66/100 : ℚ) : ℝ) = (33/50 : ℝ) := by norm_num
      linarith
    · have h' : ((748/1000 : ℚ) : ℝ) = (187/250 : ℝ) := by norm_num
      linarith


/-- **HB Table 9, row `λ₁ ≤ 68/100 ⟹ λ_j ≥ 728/1000`.** -/
theorem row_068_0728 (Q : ℕ) (hsup : L52Supply) :
    ∃ Q' : ℕ, Q ≤ Q' ∧ ∀ q : ℕ, Q' ≤ q → ∀ [NeZero q] (χ₁ : DirichletCharacter ℂ q) (ρ₁ : ℂ),
      IsMin1WideAt 10 χ₁ ρ₁ → χ₁ ^ 2 ≠ 1 → lamOf q ρ₁ ≤ ((68/100 : ℚ) : ℝ) →
      Lam3Bound χ₁ (((728/1000 : ℚ) : ℝ)) := by
  obtain ⟨δ, hδ0, hδ1, qA, hA⟩ := hsup
  have hθ0 : 0 < Real.arctan (25:ℝ) := Real.arctan_pos.mpr (by norm_num)
  have hθπ : Real.arctan (25:ℝ) < Real.pi / 2 := Real.arctan_lt_pi_div_two _
  have htanθ : Real.tan (Real.arctan (25:ℝ)) = (25/1 : ℝ) := by
    rw [Real.tan_arctan]; norm_num
  have hlampos : (0:ℝ) < (13/250 : ℝ) := by norm_num
  obtain ⟨qE, hqE⟩ := hbLemma9_2_engine (tf71T (Real.arctan (25:ℝ)) (13/250:ℝ) hθ0 hθπ hlampos)
      (427/500:ℝ) (1/6 + 1/1000000) (1/1000000000000) δ (by norm_num) (by norm_num) hδ0 hδ1
  refine ⟨max (max Q qA) (max qE Qsq), ?_, ?_⟩
  · exact le_trans (le_max_left _ _) (le_max_left _ _)
  intro q hq _inst χ₁ ρ₁ hmin hcplx hlam1
  have hqA' : qA ≤ q := by omega
  have hqE' : qE ≤ q := by omega
  have hsq : 2 ≤ Real.sqrt (Real.log (Real.log (q : ℝ))) := sqrt_loglog_ge_two (by omega)
  obtain ⟨hTlo, hThi⟩ := arctan25_bounds
  have hθlo : (3827044099179/2500000000000 : ℝ) ≤ Real.arctan (25:ℝ) := hTlo
  have hθhi : Real.arctan (25:ℝ) ≤ (153081763967161/100000000000000 : ℝ) := hThi
  refine lam3_of_row (a := ((68/100 : ℚ) : ℝ)) (c := ((728/1000 : ℚ) : ℝ))
    (θ := Real.arctan (25:ℝ)) (lam := (13/250:ℝ)) (k := (427/500:ℝ))
    (slack := (117611609329/125000000000:ℝ)) hmin hcplx hlam1 ?_ ?_
  · intro χj ρj hZj hne1 hne2 h3 h4 hlaj
    have hE := hqE q hqE' χ₁ χj ρ₁ ρj
      (fun χ _ hχ => hA q hqA' χ hχ (1/1000000000000) (by norm_num))
      hmin hmin.1.1 hZj hmin.1.1.1 hZj.1 hne1 hne2 hcplx h3 h4
      (by linarith [hlam1]) (by linarith [hlaj]) hsq
    rw [tf71T_F_eq_La (Real.arctan (25:ℝ)) (13/250:ℝ) hθ0 hθπ hlampos (-(lamOf q ρ₁)),
        tf71T_F_eq_La (Real.arctan (25:ℝ)) (13/250:ℝ) hθ0 hθπ hlampos (lamOf q ρj - lamOf q ρ₁),
        tf71T_F_eq_La (Real.arctan (25:ℝ)) (13/250:ℝ) hθ0 hθπ hlampos 0] at hE
    simp only [neg_neg, neg_sub, neg_zero, tf71T] at hE
    have hf0 : 0 ≤ tf71f (Real.arctan (25:ℝ)) (13/250:ℝ) 0 := tf71f_nonneg _ _ hθ0 hθπ hlampos 0
    have hsl : ((427/500:ℝ) ^ 2 + 4 * (427/500:ℝ) + 3/2) * (1/6 + 1/1000000 + 1/1000000000000)
        ≤ (117611609329/125000000000:ℝ) := by norm_num
    linarith [hE, mul_nonneg hf0 (sub_nonneg.mpr hsl)]
  · intro la1 laj h0 h1 h2 hineq
    refine rowcontra_068_0728 hθlo hθhi htanθ h0 ?_ ?_ hineq
    · have h' : ((68/100 : ℚ) : ℝ) = (17/25 : ℝ) := by norm_num
      linarith
    · have h' : ((728/1000 : ℚ) : ℝ) = (91/125 : ℝ) := by norm_num
      linarith


/-- **HB Table 9, row `λ₁ ≤ 70/100 ⟹ λ_j ≥ 708/1000`.** -/
theorem row_07_0708 (Q : ℕ) (hsup : L52Supply) :
    ∃ Q' : ℕ, Q ≤ Q' ∧ ∀ q : ℕ, Q' ≤ q → ∀ [NeZero q] (χ₁ : DirichletCharacter ℂ q) (ρ₁ : ℂ),
      IsMin1WideAt 10 χ₁ ρ₁ → χ₁ ^ 2 ≠ 1 → lamOf q ρ₁ ≤ ((70/100 : ℚ) : ℝ) →
      Lam3Bound χ₁ (((708/1000 : ℚ) : ℝ)) := by
  obtain ⟨δ, hδ0, hδ1, qA, hA⟩ := hsup
  have hθ0 : 0 < Real.arctan (25:ℝ) := Real.arctan_pos.mpr (by norm_num)
  have hθπ : Real.arctan (25:ℝ) < Real.pi / 2 := Real.arctan_lt_pi_div_two _
  have htanθ : Real.tan (Real.arctan (25:ℝ)) = (25/1 : ℝ) := by
    rw [Real.tan_arctan]; norm_num
  have hlampos : (0:ℝ) < (13/250 : ℝ) := by norm_num
  obtain ⟨qE, hqE⟩ := hbLemma9_2_engine (tf71T (Real.arctan (25:ℝ)) (13/250:ℝ) hθ0 hθπ hlampos)
      (107/125:ℝ) (1/6 + 1/1000000) (1/1000000000000) δ (by norm_num) (by norm_num) hδ0 hδ1
  refine ⟨max (max Q qA) (max qE Qsq), ?_, ?_⟩
  · exact le_trans (le_max_left _ _) (le_max_left _ _)
  intro q hq _inst χ₁ ρ₁ hmin hcplx hlam1
  have hqA' : qA ≤ q := by omega
  have hqE' : qE ≤ q := by omega
  have hsq : 2 ≤ Real.sqrt (Real.log (Real.log (q : ℝ))) := sqrt_loglog_ge_two (by omega)
  obtain ⟨hTlo, hThi⟩ := arctan25_bounds
  have hθlo : (3827044099179/2500000000000 : ℝ) ≤ Real.arctan (25:ℝ) := hTlo
  have hθhi : Real.arctan (25:ℝ) ≤ (153081763967161/100000000000000 : ℝ) := hThi
  refine lam3_of_row (a := ((70/100 : ℚ) : ℝ)) (c := ((708/1000 : ℚ) : ℝ))
    (θ := Real.arctan (25:ℝ)) (lam := (13/250:ℝ)) (k := (107/125:ℝ))
    (slack := (2762098309/2929687500:ℝ)) hmin hcplx hlam1 ?_ ?_
  · intro χj ρj hZj hne1 hne2 h3 h4 hlaj
    have hE := hqE q hqE' χ₁ χj ρ₁ ρj
      (fun χ _ hχ => hA q hqA' χ hχ (1/1000000000000) (by norm_num))
      hmin hmin.1.1 hZj hmin.1.1.1 hZj.1 hne1 hne2 hcplx h3 h4
      (by linarith [hlam1]) (by linarith [hlaj]) hsq
    rw [tf71T_F_eq_La (Real.arctan (25:ℝ)) (13/250:ℝ) hθ0 hθπ hlampos (-(lamOf q ρ₁)),
        tf71T_F_eq_La (Real.arctan (25:ℝ)) (13/250:ℝ) hθ0 hθπ hlampos (lamOf q ρj - lamOf q ρ₁),
        tf71T_F_eq_La (Real.arctan (25:ℝ)) (13/250:ℝ) hθ0 hθπ hlampos 0] at hE
    simp only [neg_neg, neg_sub, neg_zero, tf71T] at hE
    have hf0 : 0 ≤ tf71f (Real.arctan (25:ℝ)) (13/250:ℝ) 0 := tf71f_nonneg _ _ hθ0 hθπ hlampos 0
    have hsl : ((107/125:ℝ) ^ 2 + 4 * (107/125:ℝ) + 3/2) * (1/6 + 1/1000000 + 1/1000000000000)
        ≤ (2762098309/2929687500:ℝ) := by norm_num
    linarith [hE, mul_nonneg hf0 (sub_nonneg.mpr hsl)]
  · intro la1 laj h0 h1 h2 hineq
    refine rowcontra_07_0708 hθlo hθhi htanθ h0 ?_ ?_ hineq
    · have h' : ((70/100 : ℚ) : ℝ) = (7/10 : ℝ) := by norm_num
      linarith
    · have h' : ((708/1000 : ℚ) : ℝ) = (177/250 : ℝ) := by norm_num
      linarith


/-- **HB Table 9, row `λ₁ ≤ 704/1000 ⟹ λ_j ≥ 704/1000`.** -/
theorem row_0704_0704 (Q : ℕ) (hsup : L52Supply) :
    ∃ Q' : ℕ, Q ≤ Q' ∧ ∀ q : ℕ, Q' ≤ q → ∀ [NeZero q] (χ₁ : DirichletCharacter ℂ q) (ρ₁ : ℂ),
      IsMin1WideAt 10 χ₁ ρ₁ → χ₁ ^ 2 ≠ 1 → lamOf q ρ₁ ≤ ((704/1000 : ℚ) : ℝ) →
      Lam3Bound χ₁ (((704/1000 : ℚ) : ℝ)) := by
  obtain ⟨δ, hδ0, hδ1, qA, hA⟩ := hsup
  have hθ0 : 0 < Real.arctan (25:ℝ) := Real.arctan_pos.mpr (by norm_num)
  have hθπ : Real.arctan (25:ℝ) < Real.pi / 2 := Real.arctan_lt_pi_div_two _
  have htanθ : Real.tan (Real.arctan (25:ℝ)) = (25/1 : ℝ) := by
    rw [Real.tan_arctan]; norm_num
  have hlampos : (0:ℝ) < (13/250 : ℝ) := by norm_num
  obtain ⟨qE, hqE⟩ := hbLemma9_2_engine (tf71T (Real.arctan (25:ℝ)) (13/250:ℝ) hθ0 hθπ hlampos)
      (107/125:ℝ) (1/6 + 1/1000000) (1/1000000000000) δ (by norm_num) (by norm_num) hδ0 hδ1
  refine ⟨max (max Q qA) (max qE Qsq), ?_, ?_⟩
  · exact le_trans (le_max_left _ _) (le_max_left _ _)
  intro q hq _inst χ₁ ρ₁ hmin hcplx hlam1
  have hqA' : qA ≤ q := by omega
  have hqE' : qE ≤ q := by omega
  have hsq : 2 ≤ Real.sqrt (Real.log (Real.log (q : ℝ))) := sqrt_loglog_ge_two (by omega)
  obtain ⟨hTlo, hThi⟩ := arctan25_bounds
  have hθlo : (3827044099179/2500000000000 : ℝ) ≤ Real.arctan (25:ℝ) := hTlo
  have hθhi : Real.arctan (25:ℝ) ≤ (153081763967161/100000000000000 : ℝ) := hThi
  refine lam3_of_row (a := ((704/1000 : ℚ) : ℝ)) (c := ((704/1000 : ℚ) : ℝ))
    (θ := Real.arctan (25:ℝ)) (lam := (13/250:ℝ)) (k := (107/125:ℝ))
    (slack := (2762098309/2929687500:ℝ)) hmin hcplx hlam1 ?_ ?_
  · intro χj ρj hZj hne1 hne2 h3 h4 hlaj
    have hE := hqE q hqE' χ₁ χj ρ₁ ρj
      (fun χ _ hχ => hA q hqA' χ hχ (1/1000000000000) (by norm_num))
      hmin hmin.1.1 hZj hmin.1.1.1 hZj.1 hne1 hne2 hcplx h3 h4
      (by linarith [hlam1]) (by linarith [hlaj]) hsq
    rw [tf71T_F_eq_La (Real.arctan (25:ℝ)) (13/250:ℝ) hθ0 hθπ hlampos (-(lamOf q ρ₁)),
        tf71T_F_eq_La (Real.arctan (25:ℝ)) (13/250:ℝ) hθ0 hθπ hlampos (lamOf q ρj - lamOf q ρ₁),
        tf71T_F_eq_La (Real.arctan (25:ℝ)) (13/250:ℝ) hθ0 hθπ hlampos 0] at hE
    simp only [neg_neg, neg_sub, neg_zero, tf71T] at hE
    have hf0 : 0 ≤ tf71f (Real.arctan (25:ℝ)) (13/250:ℝ) 0 := tf71f_nonneg _ _ hθ0 hθπ hlampos 0
    have hsl : ((107/125:ℝ) ^ 2 + 4 * (107/125:ℝ) + 3/2) * (1/6 + 1/1000000 + 1/1000000000000)
        ≤ (2762098309/2929687500:ℝ) := by norm_num
    linarith [hE, mul_nonneg hf0 (sub_nonneg.mpr hsl)]
  · intro la1 laj h0 h1 h2 hineq
    refine rowcontra_0704_0704 hθlo hθhi htanθ h0 ?_ ?_ hineq
    · have h' : ((704/1000 : ℚ) : ℝ) = (88/125 : ℝ) := by norm_num
      linarith
    · have h' : ((704/1000 : ℚ) : ℝ) = (88/125 : ℝ) := by norm_num
      linarith


/-- **HB Table 9 from the analytic input.**  The full Table 9 statement
`Work.ZeroFreeTables.HBTable9`, conditional on the `L52Hyp` supply with the Burgess constant
`1/6 + 10⁻⁶`. -/
theorem HBTable9_of_supply (hsup : L52Supply) : Work.ZeroFreeTables.HBTable9 := by
  have hs := hsup
  obtain ⟨δ, hδ0, hδ1, qA, hA⟩ := hs
  obtain ⟨Q0, hQ0, hrow0⟩ := row_034_1283 (max qA Qsq) hsup
  obtain ⟨Q1, hQ1, hrow1⟩ := row_036_123 Q0 hsup
  obtain ⟨Q2, hQ2, hrow2⟩ := row_038_1181 Q1 hsup
  obtain ⟨Q3, hQ3, hrow3⟩ := row_04_1135 Q2 hsup
  obtain ⟨Q4, hQ4, hrow4⟩ := row_042_1094 Q3 hsup
  obtain ⟨Q5, hQ5, hrow5⟩ := row_044_1055 Q4 hsup
  obtain ⟨Q6, hQ6, hrow6⟩ := row_046_1018 Q5 hsup
  obtain ⟨Q7, hQ7, hrow7⟩ := row_048_0984 Q6 hsup
  obtain ⟨Q8, hQ8, hrow8⟩ := row_05_0952 Q7 hsup
  obtain ⟨Q9, hQ9, hrow9⟩ := row_052_0922 Q8 hsup
  obtain ⟨Q10, hQ10, hrow10⟩ := row_054_0893 Q9 hsup
  obtain ⟨Q11, hQ11, hrow11⟩ := row_056_0866 Q10 hsup
  obtain ⟨Q12, hQ12, hrow12⟩ := row_058_084 Q11 hsup
  obtain ⟨Q13, hQ13, hrow13⟩ := row_06_0816 Q12 hsup
  obtain ⟨Q14, hQ14, hrow14⟩ := row_062_0792 Q13 hsup
  obtain ⟨Q15, hQ15, hrow15⟩ := row_064_077 Q14 hsup
  obtain ⟨Q16, hQ16, hrow16⟩ := row_066_0748 Q15 hsup
  obtain ⟨Q17, hQ17, hrow17⟩ := row_068_0728 Q16 hsup
  obtain ⟨Q18, hQ18, hrow18⟩ := row_07_0708 Q17 hsup
  obtain ⟨Q19, hQ19, hrow19⟩ := row_0704_0704 Q18 hsup
  refine ⟨Q19, ?_⟩
  intro q hq _inst χ₁ ρ₁ hmin hcplx p hp hlep
  have hQ0s : Q0 ≤ q := by omega
  have hQ1s : Q1 ≤ q := by omega
  have hQ2s : Q2 ≤ q := by omega
  have hQ3s : Q3 ≤ q := by omega
  have hQ4s : Q4 ≤ q := by omega
  have hQ5s : Q5 ≤ q := by omega
  have hQ6s : Q6 ≤ q := by omega
  have hQ7s : Q7 ≤ q := by omega
  have hQ8s : Q8 ≤ q := by omega
  have hQ9s : Q9 ≤ q := by omega
  have hQ10s : Q10 ≤ q := by omega
  have hQ11s : Q11 ≤ q := by omega
  have hQ12s : Q12 ≤ q := by omega
  have hQ13s : Q13 ≤ q := by omega
  have hQ14s : Q14 ≤ q := by omega
  have hQ15s : Q15 ≤ q := by omega
  have hQ16s : Q16 ≤ q := by omega
  have hQ17s : Q17 ≤ q := by omega
  have hQ18s : Q18 ≤ q := by omega
  have hQ19s : Q19 ≤ q := by omega
  simp only [tableR, hbTable9, List.map_cons, List.map_nil, List.mem_cons, List.not_mem_nil,
    or_false] at hp
  rcases hp with hp0 | hp1 | hp2 | hp3 | hp4 | hp5 | hp6 | hp7 | hp8 | hp9 | hp10 | hp11 | hp12 | hp13 | hp14 | hp15 | hp16 | hp17 | hp18 | hp19
  · subst hp0; exact hrow0 q hQ0s χ₁ ρ₁ hmin hcplx hlep
  · subst hp1; exact hrow1 q hQ1s χ₁ ρ₁ hmin hcplx hlep
  · subst hp2; exact hrow2 q hQ2s χ₁ ρ₁ hmin hcplx hlep
  · subst hp3; exact hrow3 q hQ3s χ₁ ρ₁ hmin hcplx hlep
  · subst hp4; exact hrow4 q hQ4s χ₁ ρ₁ hmin hcplx hlep
  · subst hp5; exact hrow5 q hQ5s χ₁ ρ₁ hmin hcplx hlep
  · subst hp6; exact hrow6 q hQ6s χ₁ ρ₁ hmin hcplx hlep
  · subst hp7; exact hrow7 q hQ7s χ₁ ρ₁ hmin hcplx hlep
  · subst hp8; exact hrow8 q hQ8s χ₁ ρ₁ hmin hcplx hlep
  · subst hp9; exact hrow9 q hQ9s χ₁ ρ₁ hmin hcplx hlep
  · subst hp10; exact hrow10 q hQ10s χ₁ ρ₁ hmin hcplx hlep
  · subst hp11; exact hrow11 q hQ11s χ₁ ρ₁ hmin hcplx hlep
  · subst hp12; exact hrow12 q hQ12s χ₁ ρ₁ hmin hcplx hlep
  · subst hp13; exact hrow13 q hQ13s χ₁ ρ₁ hmin hcplx hlep
  · subst hp14; exact hrow14 q hQ14s χ₁ ρ₁ hmin hcplx hlep
  · subst hp15; exact hrow15 q hQ15s χ₁ ρ₁ hmin hcplx hlep
  · subst hp16; exact hrow16 q hQ16s χ₁ ρ₁ hmin hcplx hlep
  · subst hp17; exact hrow17 q hQ17s χ₁ ρ₁ hmin hcplx hlep
  · subst hp18; exact hrow18 q hQ18s χ₁ ρ₁ hmin hcplx hlep
  · subst hp19; exact hrow19 q hQ19s χ₁ ρ₁ hmin hcplx hlep

end Work.ZeroFreeTables.P9F
