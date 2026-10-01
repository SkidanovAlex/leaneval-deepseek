import Mathlib
import Submission.Work.ZeroFreeTables.HBTable7_defs
import Submission.Work.ZeroFreeTables.HBTable7_engine_region
import Submission.Work.ZeroFreeTables.HBTable7_assembly
import Submission.Work.NumberTheory.Linnik.scratch_l62app_phi
import Submission.Work.LinnikAreas.OtherCharRepel.maximalityOfMinimality
import Submission.Work.LinnikAreas.OtherCharRepel.zeroMultStripPos
import Submission.Work.ZeroFreeTables.tf71Pi4Data
import Submission.Work.ZeroFreeTables.chiMulNeFacts

namespace Work.ZeroFreeTables

open DirichletCharacter Complex
open scoped Classical BigOperators

set_option linter.style.haveILetI false

noncomputable section

private theorem maximalityAtAux {q : ℕ} [NeZero q] {χ₀ : DirichletCharacter ℂ q} {ρ₂ : ℂ}
    (hβ₂pos : 0 < ρ₂.re) (hlogq : 0 < Real.log q) {H H' : ℝ} (hHH' : H' ≤ H)
    (hmin : ∀ (ψ : DirichletCharacter ℂ q) (u : ℂ), ψ ≠ 1 → ψ ≠ χ₀ →
      Work.LinnikContract.zeroMult ψ u ≠ 0 → |u.im| ≤ H →
      Work.LinnikContract.lamOf q ρ₂ ≤ Work.LinnikContract.lamOf q u)
    (ψ : DirichletCharacter ℂ q) (hψ : ψ ≠ 1) (hne : ψ ≠ χ₀) [NeZero ψ.conductor] :
    ∀ u : ℂ, DirichletCharacter.LFunction ψ.primitiveCharacter u = 0 →
      |u.im| ≤ H' → u.re ≤ ρ₂.re := by
  intro u hu him
  by_cases h0 : u.re ≤ 0
  · exact le_trans h0 hβ₂pos.le
  · push Not at h0
    have h1 : u.re < 1 := by
      by_contra hc
      push Not at hc
      exact (DirichletCharacter.LFunction_ne_zero_of_one_le_re ψ.primitiveCharacter
        (Or.inl (Work.LinnikAreas.OtherCharRepel.primitiveCharacter_ne_one ψ hψ)) hc) hu
    have hzm : Work.LinnikContract.zeroMult ψ u ≠ 0 :=
      (Work.LinnikAreas.OtherCharRepel.zeroMultTransfer ψ hψ).2.2 u hu h0 h1
    have h := hmin ψ u hψ hne hzm (le_trans him hHH')
    rw [Work.LinnikContract.lamOf, Work.LinnikContract.lamOf] at h
    nlinarith [h, hlogq]

theorem row_contra_general_weak (b c k lam ε δ : ℝ) (hk : 0 ≤ k) (hlam : 0 < lam) (hε : 0 < ε)
    (hδ0 : 0 < δ) (hδ1 : δ < 1) (hcert : Work.ZeroFreeTables.CertRow b c k lam ε)
    (hL8 : ∀ (q : ℕ) [NeZero q] (χ : DirichletCharacter ℂ q) [NeZero χ.conductor],
      χ ≠ 1 → χ * χ = 1 → Commons.NumberTheory.Linnik.L52Hyp χ (1/8) ε δ)
    (hL6 : ∀ (q : ℕ) [NeZero q] (χ : DirichletCharacter ℂ q) [NeZero χ.conductor],
      χ ≠ 1 → Commons.NumberTheory.Linnik.L52Hyp χ (1/6) ε δ)
    (hbridge : ∀ z : ℝ, Work.ZeroFreeTables.tfF lam z =
      ∫ t in (0:ℝ)..(2 * Work.ZeroFreeTables.tf71γ (Real.pi/4) lam),
        Real.exp (-(z * t)) * Work.ZeroFreeTables.tf71f (Real.pi/4) lam t) :
    ∃ q₀ : ℕ, ∀ q : ℕ, q₀ ≤ q → ∀ [NeZero q] (χ₁ : DirichletCharacter ℂ q) (ρ₁ ρ₂ : ℂ)
      (χ₂ : DirichletCharacter ℂ q) [NeZero χ₁.conductor] [NeZero χ₂.conductor],
      Work.ZeroFreeTables.IsMin1WideAt 10 χ₁ ρ₁ → χ₁ * χ₁ = 1 → ρ₁.im = 0 →
      χ₂ ≠ 1 → χ₂ ≠ χ₁ → χ₂ ≠ χ₁⁻¹ → χ₂ * χ₂ ≠ 1 → χ₁ * (χ₂ * χ₂) ≠ 1 →
      Work.LinnikContract.IsZ χ₂ ρ₂ → Work.LinnikContract.lamOf q ρ₁ ≤ b →
      Work.LinnikContract.lamOf q ρ₂ ≤ c → 2 * |ρ₂.im| + 1 ≤ 10 * Real.log (q : ℝ) →
      (∀ (ψ : DirichletCharacter ℂ q) (u : ℂ), ψ ≠ 1 → ψ ≠ χ₁ → ψ ≠ χ₁⁻¹ →
        Work.LinnikContract.zeroMult ψ u ≠ 0 → |u.im| ≤ 2 * |ρ₂.im| + 1 →
        Work.LinnikContract.lamOf q ρ₂ ≤ Work.LinnikContract.lamOf q u) →
      DirichletCharacter.LFunction χ₁ ((ρ₁.re : ℂ)) = 0 →
      DirichletCharacter.LFunction χ₂ (((ρ₂.re : ℂ)) + ((ρ₂.im : ℂ)) * Complex.I) = 0 →
      |1 - ρ₁.re| ≤ δ → |1 - ρ₂.re| ≤ δ →
      |1 - ρ₂.re| ≤ Real.sqrt (Real.log (Real.log (q : ℝ))) / Real.log (q : ℝ) →
      (MeromorphicOn.divisor (DirichletCharacter.completedLFunction χ₂.primitiveCharacter)
          (Metric.closedBall 0 (|ρ₂.im| + 2))) (((ρ₂.re : ℂ)) + ((ρ₂.im : ℂ)) * Complex.I) ≠ 0 →
      (MeromorphicOn.divisor (DirichletCharacter.completedLFunction χ₁.primitiveCharacter)
          (Metric.closedBall 0 (|ρ₂.im| + 2))) ((ρ₁.re : ℂ)) ≠ 0 →
      (∀ u : ℂ, DirichletCharacter.LFunction χ₁.primitiveCharacter u = 0 →
        |u.im| ≤ 1 → u = ((ρ₁.re : ℂ)) ∨ u.re ≤ ρ₂.re) →
      False := by
  obtain ⟨hBnd, hcont, hsupp, hf2, hf0, hfnn, hF⟩ := tf71Pi4Data lam hlam
  obtain ⟨BT, hBT0, hBTbnd⟩ := hBnd
  obtain ⟨qE, hqE⟩ := lemma8_7_region (2 * tf71γ (Real.pi / 4) lam) BT (1/8) (1/6)
    (by have h := tf71γ_pos pi_div_four_mem.1 pi_div_four_mem.2 hlam; linarith) hBT0
    hcont hsupp hf2 hBTbnd hf0 hfnn hF hk hε hδ0 hδ1
  refine ⟨max qE 8, ?_⟩
  intro q hq _inst χ₁ ρ₁ ρ₂ χ₂ hc₁ hc₂ hmin1 hsq₁ him₁ hne₂ hne₂₁ hne₂₁' hsq₂ h₁₂₂
    hZ₂ hle₁ hle₂ hγ₂ hminimal hzero₁ hzero₂ hβ₁ hβ₂ hβ₂reg hdivB hdivE hmaxE
  haveI : NeZero χ₁.conductor := hc₁
  haveI : NeZero χ₂.conductor := hc₂
  haveI : NeZero (χ₁ * χ₂).conductor := ⟨(χ₁ * χ₂).conductor_ne_zero⟩
  haveI : NeZero (χ₂ * χ₂).conductor := ⟨(χ₂ * χ₂).conductor_ne_zero⟩
  haveI : NeZero (χ₁ * (χ₂ * χ₂)).conductor := ⟨(χ₁ * (χ₂ * χ₂)).conductor_ne_zero⟩
  have hqE' : qE ≤ q := le_trans (le_max_left _ _) hq
  have hq8 : 8 ≤ q := le_trans (le_max_right _ _) hq
  have hq2 : 2 ≤ q := by omega
  have hq1 : 1 < q := by omega
  have hlogq : 0 < Real.log (q : ℝ) := Real.log_pos (by exact_mod_cast hq1)
  have hχ₁ne1 : χ₁ ≠ 1 := hmin1.1.1.1
  have hzm₁ : Work.LinnikContract.zeroMult χ₁ ρ₁ ≠ 0 := hmin1.1.1.2.1
  have hχ₂ne1 : χ₂ ≠ 1 := hZ₂.1
  have hzm₂ : Work.LinnikContract.zeroMult χ₂ ρ₂ ≠ 0 := hZ₂.2.1
  obtain ⟨hρ₁re, hρ₁re1, hlam₁pos⟩ :=
    Work.LinnikAreas.OtherCharRepel.zeroMultStripPos hq2 hχ₁ne1 hzm₁
  obtain ⟨hρ₂re, hρ₂re1, hlam₂pos⟩ :=
    Work.LinnikAreas.OtherCharRepel.zeroMultStripPos hq2 hχ₂ne1 hzm₂
  obtain ⟨hA1, hA2, hA3, hB1, hB2, hC1, hC2⟩ :=
    chiMulNeFacts χ₁ χ₂ hsq₁ hne₂ hne₂₁ hsq₂ h₁₂₂
  have hInv : χ₁⁻¹ = χ₁ := inv_eq_of_mul_eq_one_left hsq₁
  have hminT : ∀ (ψ : DirichletCharacter ℂ q) (u : ℂ), ψ ≠ 1 → ψ ≠ χ₁ →
      Work.LinnikContract.zeroMult ψ u ≠ 0 → |u.im| ≤ 2 * |ρ₂.im| + 1 →
      Work.LinnikContract.lamOf q ρ₂ ≤ Work.LinnikContract.lamOf q u := by
    intro ψ u hψ hne hzm him
    exact hminimal ψ u hψ hne (by rw [hInv]; exact hne) hzm him
  have hmaxA : ∀ u : ℂ, DirichletCharacter.LFunction (χ₁ * χ₂).primitiveCharacter u = 0 →
      |u.im| ≤ |ρ₂.im| + 1 → u.re ≤ ρ₂.re :=
    maximalityAtAux (ρ₂ := ρ₂) hρ₂re hlogq (H := 2 * |ρ₂.im| + 1) (H' := |ρ₂.im| + 1)
      (by linarith [abs_nonneg ρ₂.im]) hminT (χ₁ * χ₂) hA1 hA2
  have hmaxB : ∀ u : ℂ, DirichletCharacter.LFunction (χ₂ * χ₂).primitiveCharacter u = 0 →
      |u.im| ≤ 2 * |ρ₂.im| + 1 → u.re ≤ ρ₂.re :=
    maximalityAtAux (ρ₂ := ρ₂) hρ₂re hlogq (H := 2 * |ρ₂.im| + 1) (H' := 2 * |ρ₂.im| + 1)
      le_rfl hminT (χ₂ * χ₂) hsq₂ hB1
  have hmaxC : ∀ u : ℂ,
      DirichletCharacter.LFunction (χ₁ * (χ₂ * χ₂)).primitiveCharacter u = 0 →
      |u.im| ≤ 2 * |ρ₂.im| + 1 → u.re ≤ ρ₂.re :=
    maximalityAtAux (ρ₂ := ρ₂) hρ₂re hlogq (H := 2 * |ρ₂.im| + 1) (H' := 2 * |ρ₂.im| + 1)
      le_rfl hminT (χ₁ * (χ₂ * χ₂)) h₁₂₂ hC1
  have hmaxD : ∀ u : ℂ, DirichletCharacter.LFunction χ₂.primitiveCharacter u = 0 →
      |u.im| ≤ |ρ₂.im| + 1 → u.re ≤ ρ₂.re :=
    maximalityAtAux (ρ₂ := ρ₂) hρ₂re hlogq (H := 2 * |ρ₂.im| + 1) (H' := |ρ₂.im| + 1)
      (by linarith [abs_nonneg ρ₂.im]) hminT χ₂ hne₂ hne₂₁
  have H₁ : Commons.NumberTheory.Linnik.L52Hyp χ₁ (1/8) ε δ := hL8 q χ₁ hχ₁ne1 hsq₁
  have H₂ : Commons.NumberTheory.Linnik.L52Hyp χ₂ (1/6) ε δ := hL6 q χ₂ hχ₂ne1
  have H₃ : Commons.NumberTheory.Linnik.L52Hyp (χ₁ * χ₂) (1/6) ε δ := hL6 q (χ₁ * χ₂) hA1
  have H₄ : Commons.NumberTheory.Linnik.L52Hyp (χ₂ * χ₂) (1/6) ε δ := hL6 q (χ₂ * χ₂) hsq₂
  have H₅ : Commons.NumberTheory.Linnik.L52Hyp (χ₁ * (χ₂ * χ₂)) (1/6) ε δ :=
    hL6 q (χ₁ * (χ₂ * χ₂)) h₁₂₂
  have h5 := hqE (q := q) hqE' χ₁ χ₂ hχ₁ne1 hχ₂ne1 hne₂₁ hA1 hsq₂ h₁₂₂ hsq₁
    (β₁ := ρ₁.re) (β₂ := ρ₂.re) (γ₂ := ρ₂.im)
    hβ₁ hβ₂ hγ₂ hβ₂reg hzero₁ hzero₂ hmaxA hmaxB hmaxC hmaxD hmaxE hdivB hdivE H₁ H₂ H₃ H₄ H₅
  have hl2 : Real.log (q : ℝ) * (1 - ρ₂.re) = Work.LinnikContract.lamOf q ρ₂ := by
    rw [Work.LinnikContract.lamOf]; ring
  have hdiff : -((Real.log (q : ℝ) * (1 - ρ₁.re)) - (Real.log (q : ℝ) * (1 - ρ₂.re)))
      = Work.LinnikContract.lamOf q ρ₂ - Work.LinnikContract.lamOf q ρ₁ := by
    rw [Work.LinnikContract.lamOf, Work.LinnikContract.lamOf]; ring
  rw [hdiff, hl2, engine_coeff_eq] at h5
  have heng : 0 ≤ (k ^ 2 + 1/2) *
        (tfF lam (-(Work.LinnikContract.lamOf q ρ₂))
          - tfF lam (Work.LinnikContract.lamOf q ρ₁ - Work.LinnikContract.lamOf q ρ₂))
      - 2 * k * tfF lam 0
      + (2 * lam * (Real.pi - 3)) * (psi87 k + tfSlack k ε) :=
    heng_of_engine (lam := lam) (k := k) (ε := ε)
      (z₁ := Work.LinnikContract.lamOf q ρ₁) (z₂ := Work.LinnikContract.lamOf q ρ₂)
      hlam hbridge h5
  exact cert_forces lam k ε b c (Work.LinnikContract.lamOf q ρ₁)
    (Work.LinnikContract.lamOf q ρ₂) hlam hk (hcont.mono (fun x hx => hx.1))
    (fun t _ => hfnn t) hbridge heng hcert hlam₁pos.le hle₁ hle₂

end

end Work.ZeroFreeTables
