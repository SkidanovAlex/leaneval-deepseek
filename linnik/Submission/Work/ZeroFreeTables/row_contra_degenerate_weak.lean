import Mathlib
import Submission.Work.ZeroFreeTables.HBTable7_defs85
import Submission.Work.ZeroFreeTables.HBTable7_rowHelpers
import Submission.Work.ZeroFreeTables.HBTable7_engine85
import Submission.Work.NumberTheory.Linnik.scratch_l62app_phi
import Submission.Work.LinnikAreas.OtherCharRepel.zeroMultTransfer
import Submission.Work.LinnikAreas.OtherCharRepel.zeroMultStripPos

namespace Work.ZeroFreeTables

section Helpers

open DirichletCharacter Complex
open scoped Classical BigOperators

/-- Transfer of the "ball maximality" of `ρ₂` (a minimality assumption over all `zeroMult`-zeros
of non-principal characters in the ball `|Im| ≤ 2|ρ₂.im| + 1`, excluding `χ₁` and `χ₁⁻¹`) to the
maximal-real-part statement for zeros of the ordinary `L`-function of a primitive character `ψ`,
in the window `|Im| ≤ |ρ₂.im| + 1`. -/
theorem maxOfBallAux {q : ℕ} [NeZero q] (χ₁ : DirichletCharacter ℂ q) (ρ₂ : ℂ)
    (hlogq : 0 < Real.log q) (hβ₂pos : 0 < ρ₂.re)
    (hball : ∀ (ψ : DirichletCharacter ℂ q) (u : ℂ), ψ ≠ 1 → ψ ≠ χ₁ → ψ ≠ χ₁⁻¹ →
      Work.LinnikContract.zeroMult ψ u ≠ 0 → |u.im| ≤ 2 * |ρ₂.im| + 1 →
        Work.LinnikContract.lamOf q ρ₂ ≤ Work.LinnikContract.lamOf q u)
    (ψ : DirichletCharacter ℂ q) (hψ : ψ ≠ 1) (hψ₁ : ψ ≠ χ₁) (hψ₁' : ψ ≠ χ₁⁻¹)
    [NeZero ψ.conductor] :
    ∀ u : ℂ, DirichletCharacter.LFunction ψ.primitiveCharacter u = 0 →
      |u.im| ≤ |ρ₂.im| + 1 → u.re ≤ ρ₂.re := by
  intro u hu him
  have him' : |u.im| ≤ 2 * |ρ₂.im| + 1 := by linarith [abs_nonneg ρ₂.im]
  by_cases h1 : u.re ≤ 0
  · linarith
  · push_neg at h1
    by_cases h2 : u.re < 1
    · have hzm : Work.LinnikContract.zeroMult ψ u ≠ 0 :=
        (Work.LinnikAreas.OtherCharRepel.zeroMultTransfer ψ hψ).2.2 u hu h1 h2
      have hle := hball ψ u hψ hψ₁ hψ₁' hzm him'
      rw [Work.LinnikContract.lamOf, Work.LinnikContract.lamOf] at hle
      nlinarith [hle, hlogq]
    · push_neg at h2
      exact absurd hu (DirichletCharacter.LFunction_ne_zero_of_one_le_re ψ.primitiveCharacter
        (Or.inl (Work.LinnikAreas.OtherCharRepel.primitiveCharacter_ne_one ψ hψ)) h2)

/-- Conversion of the engine's conclusion (an inequality between integrals of the test function
`tf71f (π/4) lam`) into the `tfF` form consumed by `cert_forces85`, using the bridge and
`f(0) = 2λ(π-3)`. -/
theorem heng85Aux {lam ε z₁ z₂ : ℝ} (hlam : 0 < lam)
    (hbridge : ∀ z : ℝ, tfF lam z =
      ∫ t in (0:ℝ)..(2 * tf71γ (Real.pi/4) lam),
        Real.exp (-(z * t)) * tf71f (Real.pi/4) lam t)
    (h : 0 ≤ (∫ t in (0:ℝ)..(2 * tf71γ (Real.pi/4) lam),
              Real.exp (z₂ * t) * tf71f (Real.pi/4) lam t)
            - (∫ t in (0:ℝ)..(2 * tf71γ (Real.pi/4) lam),
              Real.exp ((z₂ - z₁) * t) * tf71f (Real.pi/4) lam t)
            - (∫ t in (0:ℝ)..(2 * tf71γ (Real.pi/4) lam),
              tf71f (Real.pi/4) lam t)
            + tf71f (Real.pi/4) lam 0 * (3/8 + 4 * ε)) :
    0 ≤ tfF lam (-z₂) - tfF lam (z₁ - z₂) - tfF lam 0
        + (2 * lam * (Real.pi - 3)) * (3/8 + 4 * ε) := by
  have h0 : tfF lam 0 =
      ∫ t in (0:ℝ)..(2 * tf71γ (Real.pi/4) lam), tf71f (Real.pi/4) lam t := by
    rw [hbridge 0]
    exact intervalIntegral.integral_congr
      (fun t _ => by rw [zero_mul, neg_zero, Real.exp_zero, one_mul])
  rw [tf71f_pi_div_four_at_zero lam hlam] at h
  rw [tfF_eq_exp hbridge z₂, tfF_eq_exp_sub hbridge z₁ z₂, h0]
  exact h

end Helpers

theorem row_contra_degenerate_weak (b c lam ε δ : ℝ) (hlam : 0 < lam) (hε : 0 < ε)
    (hδ0 : 0 < δ) (hδ1 : δ < 1) (hcert : Work.ZeroFreeTables.CertRow85 b c lam ε)
    (hL8 : ∀ (q : ℕ) [NeZero q] (χ : DirichletCharacter ℂ q) [NeZero χ.conductor],
      χ ≠ 1 → χ ^ 4 = 1 → Commons.NumberTheory.Linnik.L52Hyp χ (1/8) ε δ)
    (hbridge : ∀ z : ℝ, Work.ZeroFreeTables.tfF lam z =
      ∫ t in (0:ℝ)..(2 * Work.ZeroFreeTables.tf71γ (Real.pi/4) lam),
        Real.exp (-(z * t)) * Work.ZeroFreeTables.tf71f (Real.pi/4) lam t) :
    ∃ q₀ : ℕ, ∀ q : ℕ, q₀ ≤ q → ∀ [NeZero q] (χ₁ : DirichletCharacter ℂ q) (ρ₁ ρ₂ : ℂ)
      (χ₂ : DirichletCharacter ℂ q) [NeZero χ₁.conductor] [NeZero χ₂.conductor],
      Work.ZeroFreeTables.IsMin1WideAt 10 χ₁ ρ₁ → χ₁ * χ₁ = 1 → ρ₁.im = 0 →
      χ₂ ≠ 1 → χ₂ ≠ χ₁ → χ₂ ≠ χ₁⁻¹ → χ₂ ^ 4 = 1 →
      Work.LinnikContract.IsZ χ₂ ρ₂ → Work.LinnikContract.lamOf q ρ₁ ≤ b →
      Work.LinnikContract.lamOf q ρ₂ ≤ c → |ρ₂.im| + 1 ≤ 10 * Real.log (q : ℝ) →
      (∀ (ψ : DirichletCharacter ℂ q) (u : ℂ), ψ ≠ 1 → ψ ≠ χ₁ → ψ ≠ χ₁⁻¹ →
        Work.LinnikContract.zeroMult ψ u ≠ 0 → |u.im| ≤ 2 * |ρ₂.im| + 1 →
        Work.LinnikContract.lamOf q ρ₂ ≤ Work.LinnikContract.lamOf q u) →
      DirichletCharacter.LFunction χ₁ ((ρ₁.re : ℂ)) = 0 →
      DirichletCharacter.LFunction χ₂ (((ρ₂.re : ℂ)) + ((ρ₂.im : ℂ)) * Complex.I) = 0 →
      |1 - ρ₁.re| ≤ δ → |1 - ρ₂.re| ≤ δ →
      |1 - ρ₁.re| ≤ Real.sqrt (Real.log (Real.log (q : ℝ))) / Real.log (q : ℝ) →
      |1 - ρ₂.re| ≤ Real.sqrt (Real.log (Real.log (q : ℝ))) / Real.log (q : ℝ) →
      (MeromorphicOn.divisor (DirichletCharacter.completedLFunction χ₁.primitiveCharacter)
          (Metric.closedBall 0 (|ρ₂.im| + 2))) ((ρ₁.re : ℂ)) ≠ 0 →
      (MeromorphicOn.divisor (DirichletCharacter.completedLFunction χ₂.primitiveCharacter)
          (Metric.closedBall 0 (|ρ₂.im| + 2))) (((ρ₂.re : ℂ)) + ((ρ₂.im : ℂ)) * Complex.I) ≠ 0 →
      (∀ u : ℂ, DirichletCharacter.LFunction χ₁.primitiveCharacter u = 0 →
        |u.im| ≤ 1 → u = ((ρ₁.re : ℂ)) ∨ u.re ≤ ρ₂.re) →
      False := by
  have hθ0 : 0 < Real.pi / 4 := pi_div_four_mem.1
  have hθ1 : Real.pi / 4 < Real.pi / 2 := pi_div_four_mem.2
  have hγpos : 0 < tf71γ (Real.pi/4) lam := tf71γ_pos hθ0 hθ1 hlam
  have hx₀ : 0 < 2 * tf71γ (Real.pi/4) lam := by linarith
  obtain ⟨B, hB0, hBnd⟩ := tf71f_bound (Real.pi/4) lam hγpos
  obtain ⟨qE, hqE⟩ := lemma85pt_region (2 * tf71γ (Real.pi/4) lam) B (1/8) hx₀ hB0
      (f := tf71f (Real.pi/4) lam)
      (tf71f_cont (Real.pi/4) lam)
      (fun t ht => tf71f_supp hθ0 hθ1 hlam t ht)
      (tf71f_diff (Real.pi/4) lam hγpos)
      hBnd
      (tf71f_zero_pos (Real.pi/4) lam hθ0 hθ1 hlam)
      (tf71f_nonneg (Real.pi/4) lam hθ0 hθ1 hlam)
      (fun z hz => by
        simpa only [tf71Fc] using tf71Fc_re_nonneg (Real.pi/4) lam hθ0 hθ1 hlam z hz)
      hε hδ0 hδ1
  refine ⟨max qE 2, ?_⟩
  intro q hq _inst χ₁ ρ₁ ρ₂ χ₂ _ic₁ _ic₂ hmin hχ₁sq hρ₁im hχ₂ne1 hχ₂neχ₁ hχ₂neχ₁inv hχ₂4
    hZ₂ hlamB hlamC hγ hball hL1 hL2 hδa hδb hpta hptb hdivC hdivD hmaxC0
  haveI : NeZero q := _inst
  haveI : NeZero χ₁.conductor := _ic₁
  haveI : NeZero χ₂.conductor := _ic₂
  have hq2 : 2 ≤ q := le_trans (le_max_right qE 2) hq
  have hqE' : qE ≤ q := le_trans (le_max_left qE 2) hq
  have hlogqpos : 0 < Real.log (q : ℝ) := by
    have h1 : (1 : ℝ) < (q : ℝ) := by exact_mod_cast (by omega : 1 < q)
    exact Real.log_pos h1
  have hχ₁ne1 : χ₁ ≠ 1 := hmin.1.1.1
  have hzm₁ : Work.LinnikContract.zeroMult χ₁ ρ₁ ≠ 0 := hmin.1.1.2.1
  obtain ⟨hρ₁re, hρ₁re1, hlam₁pos⟩ :=
    Work.LinnikAreas.OtherCharRepel.zeroMultStripPos hq2 hχ₁ne1 hzm₁
  have hzm₂ : Work.LinnikContract.zeroMult χ₂ ρ₂ ≠ 0 := hZ₂.2.1
  obtain ⟨hρ₂re, hρ₂re1, hlam₂pos⟩ :=
    Work.LinnikAreas.OtherCharRepel.zeroMultStripPos hq2 hχ₂ne1 hzm₂
  -- `χ₁` is an involution
  have hχ₁inv : χ₁⁻¹ = χ₁ := inv_eq_of_mul_eq_one_left hχ₁sq
  -- non-principality of the four characters
  have hprod_ne_χ₁ : χ₁ * χ₂ ≠ χ₁ := by
    intro h
    refine hχ₂ne1 ?_
    calc χ₂ = χ₁⁻¹ * (χ₁ * χ₂) := by rw [← mul_assoc, inv_mul_cancel, one_mul]
      _ = χ₁⁻¹ * χ₁ := by rw [h]
      _ = 1 := inv_mul_cancel χ₁
  have hprod_ne_χ₁inv : χ₁ * χ₂ ≠ χ₁⁻¹ := by
    intro h
    exact hprod_ne_χ₁ (by rw [h, hχ₁inv])
  have hprodinv_ne_χ₁ : χ₁ * χ₂⁻¹ ≠ χ₁ := by
    intro h
    refine hχ₂ne1 ?_
    have h2 : χ₂⁻¹ = 1 := by
      calc χ₂⁻¹ = χ₁⁻¹ * (χ₁ * χ₂⁻¹) := by rw [← mul_assoc, inv_mul_cancel, one_mul]
        _ = χ₁⁻¹ * χ₁ := by rw [h]
        _ = 1 := inv_mul_cancel χ₁
    exact inv_eq_one.mp h2
  have hprodinv_ne_χ₁inv : χ₁ * χ₂⁻¹ ≠ χ₁⁻¹ := by
    intro h
    exact hprodinv_ne_χ₁ (by rw [h, hχ₁inv])
  have hχ₁χ₂_ne_one : χ₁ * χ₂ ≠ 1 := by
    intro h
    refine hχ₂neχ₁ ?_
    calc χ₂ = χ₁⁻¹ * (χ₁ * χ₂) := by rw [← mul_assoc, inv_mul_cancel, one_mul]
      _ = χ₁⁻¹ * 1 := by rw [h]
      _ = χ₁⁻¹ := mul_one _
      _ = χ₁ := hχ₁inv
  have hχ₁χ₂inv_ne_one : χ₁ * χ₂⁻¹ ≠ 1 := by
    intro h
    refine hχ₂neχ₁ ?_
    have h2 : χ₂⁻¹ = χ₁⁻¹ := by
      calc χ₂⁻¹ = χ₁⁻¹ * (χ₁ * χ₂⁻¹) := by rw [← mul_assoc, inv_mul_cancel, one_mul]
        _ = χ₁⁻¹ * 1 := by rw [h]
        _ = χ₁⁻¹ := mul_one _
    have h3 : χ₂ = χ₁ := by
      have := congrArg Inv.inv h2
      simpa using this
    exact h3
  -- the four maximality conditions
  letI : NeZero (χ₁ * χ₂).conductor := ⟨(χ₁ * χ₂).conductor_ne_zero⟩
  letI : NeZero (χ₁ * χ₂⁻¹).conductor := ⟨(χ₁ * χ₂⁻¹).conductor_ne_zero⟩
  have hmaxA : ∀ u : ℂ, DirichletCharacter.LFunction (χ₁ * χ₂).primitiveCharacter u = 0 →
      |u.im| ≤ |ρ₂.im| + 1 → u.re ≤ ρ₂.re :=
    maxOfBallAux χ₁ ρ₂ hlogqpos hρ₂re hball (χ₁ * χ₂) hχ₁χ₂_ne_one hprod_ne_χ₁ hprod_ne_χ₁inv
  have hmaxB : ∀ u : ℂ, DirichletCharacter.LFunction (χ₁ * χ₂⁻¹).primitiveCharacter u = 0 →
      |u.im| ≤ |ρ₂.im| + 1 → u.re ≤ ρ₂.re :=
    maxOfBallAux χ₁ ρ₂ hlogqpos hρ₂re hball (χ₁ * χ₂⁻¹) hχ₁χ₂inv_ne_one hprodinv_ne_χ₁
      hprodinv_ne_χ₁inv
  have hmaxD : ∀ u : ℂ, DirichletCharacter.LFunction χ₂.primitiveCharacter u = 0 →
      |u.im| ≤ |ρ₂.im| + 1 → u.re ≤ ρ₂.re :=
    maxOfBallAux χ₁ ρ₂ hlogqpos hρ₂re hball χ₂ hχ₂ne1 hχ₂neχ₁ hχ₂neχ₁inv
  have hmaxC : ∀ u : ℂ, DirichletCharacter.LFunction χ₁.primitiveCharacter u = 0 →
      |u.im| ≤ 1 → u = (ρ₁.re : ℂ) ∨ u.re ≤ ρ₂.re :=
    fun u hu him => hmaxC0 u hu (by linarith [abs_nonneg ρ₂.im, him])
  -- the four `L52Hyp` inputs (all four characters have order dividing `4`)
  have hχ₁4 : χ₁ ^ 4 = 1 := by
    have h2 : χ₁ ^ 2 = 1 := by rw [pow_two]; exact hχ₁sq
    rw [show (4:ℕ) = 2 * 2 from rfl, pow_mul, h2, one_pow]
  have hprod4 : (χ₁ * χ₂) ^ 4 = 1 := by rw [mul_pow, hχ₁4, hχ₂4, one_mul]
  have hprodinv4 : (χ₁ * χ₂⁻¹) ^ 4 = 1 := by
    rw [mul_pow, hχ₁4, inv_pow, hχ₂4, inv_one, one_mul]
  have H₁ : Commons.NumberTheory.Linnik.L52Hyp χ₁ (1/8) ε δ := hL8 q χ₁ hχ₁ne1 hχ₁4
  have H₂ : Commons.NumberTheory.Linnik.L52Hyp χ₂ (1/8) ε δ := hL8 q χ₂ hχ₂ne1 hχ₂4
  have H₃ : Commons.NumberTheory.Linnik.L52Hyp (χ₁ * χ₂) (1/8) ε δ :=
    hL8 q (χ₁ * χ₂) hχ₁χ₂_ne_one hprod4
  have H₄ : Commons.NumberTheory.Linnik.L52Hyp (χ₁ * χ₂⁻¹) (1/8) ε δ :=
    hL8 q (χ₁ * χ₂⁻¹) hχ₁χ₂inv_ne_one hprodinv4
  -- Heath-Brown's Lemma 8.5 (five-term positivity)
  have hEng := hqE (q := q) hqE' χ₁ χ₂ hχ₁ne1 hχ₂ne1 hχ₂neχ₁ hχ₁χ₂_ne_one hχ₁χ₂inv_ne_one
    (β₁ := ρ₁.re) (β₂ := ρ₂.re) (γ₂ := ρ₂.im)
    hδa hδb hγ hpta hptb hL1 hL2 hmaxA hmaxB hmaxC hmaxD hdivC hdivD H₁ H₂ H₃ H₄
  -- convert the engine's conclusion into the `tfF` form of the certificate extraction
  have hEng' : 0 ≤
      (∫ t in (0:ℝ)..(2 * tf71γ (Real.pi/4) lam),
        Real.exp ((Work.LinnikContract.lamOf q ρ₂) * t) * tf71f (Real.pi/4) lam t)
      - (∫ t in (0:ℝ)..(2 * tf71γ (Real.pi/4) lam),
        Real.exp (((Work.LinnikContract.lamOf q ρ₂) - (Work.LinnikContract.lamOf q ρ₁)) * t)
          * tf71f (Real.pi/4) lam t)
      - (∫ t in (0:ℝ)..(2 * tf71γ (Real.pi/4) lam), tf71f (Real.pi/4) lam t)
      + tf71f (Real.pi/4) lam 0 * (3/8 + 4 * ε) := by
    have hz₂eq : Real.log (q : ℝ) * (1 - ρ₂.re) = Work.LinnikContract.lamOf q ρ₂ := by
      simp only [Work.LinnikContract.lamOf]; ring
    have hsub : -((Real.log (q : ℝ) * (1 - ρ₁.re)) - (Real.log (q : ℝ) * (1 - ρ₂.re)))
        = Work.LinnikContract.lamOf q ρ₂ - Work.LinnikContract.lamOf q ρ₁ := by
      simp only [Work.LinnikContract.lamOf]; ring
    have hcoef : (3 : ℝ) * (1/8) + 4 * ε = 3/8 + 4 * ε := by norm_num
    rw [hsub, hz₂eq, hcoef] at hEng
    exact hEng
  exact cert_forces85 lam ε b c (Work.LinnikContract.lamOf q ρ₁) (Work.LinnikContract.lamOf q ρ₂)
    hlam ((tf71f_cont (Real.pi/4) lam).mono Set.Icc_subset_Ici_self)
    (fun t _ => tf71f_nonneg (Real.pi/4) lam hθ0 hθ1 hlam t)
    hbridge (heng85Aux hlam hbridge hEng')
    hcert hlam₁pos.le hlamB hlamC

end Work.ZeroFreeTables
