import Mathlib
import Submission.Work.LinnikAreas.Setup
import Submission.Work.LinnikAreas.CIDeps
import Submission.Work.LinnikAreas.CIDefs
import Submission.Work.LinnikAreas.UniformPrimePowerTail
import Submission.Work.LinnikAreas.UniformNonCoprimeTail
import Submission.Work.LinnikAreas.ClassLambdaSumDecomp
import Submission.Work.LinnikAreas.ChiSumSubPrimitive
import Submission.Work.LinnikAreas.ClassSumOrthogonality
import Submission.Work.LinnikAreas.ZeroSumBoxComparison

/-!
# `ClassIdentity` — Heath-Brown's Lemma 13.1 (box-restricted, uniform in `q`)

This file proves `Work.LinnikAreas.ClassIdentityHyp`, the box-restricted explicit formula for the
class prime sum used by Area 2 of the Linnik contract.

The class prime sum `PS` is decomposed by the orthogonality relation for Dirichlet characters
(`ArithmeticFunction.vonMangoldt.residueClass_apply`), the per-character von Mangoldt sums are
evaluated by the uniform explicit formula `tentMellin_bridge_scale` (which produces for each
character `χ ≠ 1` a limit `Z_χ` of its zero sum, together with the bound
`‖Z_χ - boxSum χ‖ ≤ farSum χ`), the principal character is evaluated by `tentMellin_principal`,
the prime-power part by `UniformPrimePowerTail`, the `p ∣ q` and imprimitive corrections by
`UniformNonCoprimeTail`, and the elementary identities by `ClassLambdaSumDecomp`,
`ClassSumOrthogonality` and `ChiSumSubPrimitive`.
-/

open DirichletCharacter Complex
open scoped BigOperators Classical
noncomputable section
set_option autoImplicit false
set_option maxHeartbeats 1600000

namespace Work.LinnikAreas
open Work.LinnikContract

/-- Every Dirichlet character over a nonzero level has a nonzero conductor. -/
instance conductorNeZero {R : Type*} [CommMonoidWithZero R] {n : ℕ} [NeZero n]
    (χ : DirichletCharacter R n) : NeZero χ.conductor := ⟨χ.conductor_ne_zero⟩

/-- `Hk`, written in the expanded form in which `tentMellin_bridge_scale` states its hypothesis. -/
lemma Hk_eq_exp_form (u : ℂ) (q : ℕ) :
    Hk (11/2) (3/10) ((1 - u) * ((Real.log (q : ℝ) : ℝ) : ℂ)) =
      Complex.exp (-(((11/2 - 2 * (3/10) : ℝ) : ℂ) * ((1 - u) * ((Real.log (q : ℝ) : ℝ) : ℂ)))) *
        (((1 - Complex.exp (-(((3/10 : ℝ) : ℂ) * ((1 - u) * ((Real.log (q : ℝ) : ℝ) : ℂ))))) /
          ((1 - u) * ((Real.log (q : ℝ) : ℝ) : ℂ))) ^ 2) := by
  simp only [Hk, F2, neg_mul]

/-- The real prime sum of `ClassLambdaSumDecomp`, cast to `ℂ`, is `primePS`. -/
lemma ofReal_primeSum_eq_primePS {q : ℕ} (a X : ℕ) :
    (((∑ p ∈ (Finset.Icc 1 X).filter (fun p : ℕ => p.Prime ∧ p ≡ a [MOD q]),
        Real.log (p : ℝ) / (p : ℝ) *
          Commons.NumberTheory.Linnik.tentWeight (11/2) (3/10)
            (Real.log (p : ℝ) / Real.log (q : ℝ)) : ℝ)) : ℂ)
      = primePS (q := q) a X := by
  rw [primePS, Complex.ofReal_sum]
  refine Finset.sum_congr rfl (fun p hp => ?_)
  push_cast
  ring

/-- The prime-power part of `ClassLambdaSumDecomp`, cast to `ℂ`. -/
lemma ofReal_classPP_eq {q : ℕ} (a X : ℕ) :
    (((∑ n ∈ (Finset.Icc 1 X).filter (fun n : ℕ => ¬ n.Prime ∧ n ≡ a [MOD q]),
        ArithmeticFunction.vonMangoldt n / (n : ℝ) *
          Commons.NumberTheory.Linnik.tentWeight (11/2) (3/10)
            (Real.log (n : ℝ) / Real.log (q : ℝ)) : ℝ)) : ℂ)
      = ((classPP (q := q) a X : ℝ) : ℂ) := by
  rw [classPP, Complex.ofReal_sum]

/-- `chiSum` of the principal character is the difference of the total von Mangoldt sum and the
sum over the non-coprime terms. -/
lemma chiSum_one_eq {q : ℕ} [NeZero q] (X : ℕ) :
    chiSum (1 : DirichletCharacter ℂ q) q X = allSum q X - ncsSumC q X := by
  have h1 : chiSum (1 : DirichletCharacter ℂ q) q X
      = ∑ n ∈ (Finset.Icc 1 X).filter (fun n : ℕ => Nat.Coprime n q),
          (ArithmeticFunction.vonMangoldt n : ℂ) / (n : ℂ) *
            ((tentW (Real.log (n : ℝ) / Real.log (q : ℝ)) : ℝ) : ℂ) := by
    rw [chiSum, Finset.sum_filter]
    refine Finset.sum_congr rfl (fun n hn => ?_)
    rw [one_apply_natCast]
    by_cases h : Nat.Coprime n q
    · rw [if_pos h, if_pos h]; ring
    · rw [if_neg h, if_neg h]; ring
  have h2 : allSum q X - ncsSumC q X
      = ∑ n ∈ (Finset.Icc 1 X).filter (fun n : ℕ => Nat.Coprime n q),
          (ArithmeticFunction.vonMangoldt n : ℂ) / (n : ℂ) *
            ((tentW (Real.log (n : ℝ) / Real.log (q : ℝ)) : ℝ) : ℂ) := by
    rw [allSum, ncsSumC, Finset.sum_filter, Finset.sum_filter, ← Finset.sum_sub_distrib]
    refine Finset.sum_congr rfl (fun n hn => ?_)
    by_cases h : Nat.Coprime n q
    · rw [if_neg (fun hc => hc h), if_pos h]; ring
    · rw [if_pos h, if_neg h]; ring
  rw [h1, h2]

/-- `q ^ (-(49/10)) ≤ 16 * (q ^ (-(49/20))) / log q` for `q ≥ 2`. -/
lemma rpow_neg_le_div_log {q : ℕ} (hq : 2 ≤ q) :
    (q : ℝ) ^ (-((49 : ℝ) / 10)) ≤ 16 * ((q : ℝ) ^ (-((49 : ℝ) / 20)) / Real.log (q : ℝ)) := by
  have hq1 : 1 ≤ q := by omega
  have hqR : (0 : ℝ) < (q : ℝ) := by positivity
  have hlog : 0 < Real.log (q : ℝ) := Real.log_pos (by exact_mod_cast (by omega : 1 < q))
  have hlogle : Real.log (q : ℝ) ≤ 16 * (q : ℝ) ^ ((49 : ℝ) / 20) := log_natCast_le_rpow q hq1
  have hmain : (q : ℝ) ^ (-((49 : ℝ) / 10)) * Real.log (q : ℝ) ≤ 16 * (q : ℝ) ^ (-((49 : ℝ) / 20)) := by
    calc (q : ℝ) ^ (-((49 : ℝ) / 10)) * Real.log (q : ℝ)
        ≤ (q : ℝ) ^ (-((49 : ℝ) / 10)) * (16 * (q : ℝ) ^ ((49 : ℝ) / 20)) :=
          mul_le_mul_of_nonneg_left hlogle (Real.rpow_nonneg hqR.le _)
      _ = 16 * ((q : ℝ) ^ (-((49 : ℝ) / 10)) * (q : ℝ) ^ ((49 : ℝ) / 20)) := by ring
      _ = 16 * ((q : ℝ) ^ (-((49 : ℝ) / 10) + ((49 : ℝ) / 20))) := by
            rw [← Real.rpow_add hqR]
      _ = 16 * (q : ℝ) ^ (-((49 : ℝ) / 20)) := by norm_num
  calc (q : ℝ) ^ (-((49 : ℝ) / 10))
      = ((q : ℝ) ^ (-((49 : ℝ) / 10)) * Real.log (q : ℝ)) / Real.log (q : ℝ) := by
        rw [mul_div_cancel_right₀ _ hlog.ne']
    _ ≤ (16 * (q : ℝ) ^ (-((49 : ℝ) / 20))) / Real.log (q : ℝ) :=
        div_le_div_of_nonneg_right hmain hlog.le
    _ = 16 * ((q : ℝ) ^ (-((49 : ℝ) / 20)) / Real.log (q : ℝ)) := by ring

/-- `(log q)^2 * q ^ (-(49/10)) ≤ 256` for `q ≥ 1`. -/
lemma log_sq_mul_rpow_neg_le' {q : ℕ} (hq : 1 ≤ q) :
    (Real.log (q : ℝ)) ^ 2 * (q : ℝ) ^ (-((49 : ℝ) / 10)) ≤ 256 := by
  have hqR : (0 : ℝ) < (q : ℝ) := by positivity
  have h1 : (Real.log (q : ℝ)) ^ 2 * (q : ℝ) ^ (-((49 : ℝ) / 20)) ≤ 256 :=
    log_sq_mul_rpow_neg_le q hq
  have h2 : (q : ℝ) ^ (-((49 : ℝ) / 10))
      = (q : ℝ) ^ (-((49 : ℝ) / 20)) * (q : ℝ) ^ (-((49 : ℝ) / 20)) := by
    rw [← Real.rpow_add hqR]; norm_num
  have h3 : (q : ℝ) ^ (-((49 : ℝ) / 20)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by exact_mod_cast hq) (by norm_num)
  have h4 : 0 ≤ (Real.log (q : ℝ)) ^ 2 * (q : ℝ) ^ (-((49 : ℝ) / 20)) := by positivity
  rw [h2, ← mul_assoc]
  calc (Real.log (q : ℝ)) ^ 2 * (q : ℝ) ^ (-((49 : ℝ) / 20)) * (q : ℝ) ^ (-((49 : ℝ) / 20))
      ≤ 256 * 1 := mul_le_mul h1 h3 (Real.rpow_nonneg hqR.le _) (by norm_num)
    _ = 256 := by norm_num

/-- `((q.totient : ℂ))⁻¹ * (K² : ℂ) = ((K² / φ(q) : ℝ) : ℂ)`. -/
lemma totient_inv_mul_Ksq {q : ℕ} :
    ((q.totient : ℂ))⁻¹ * ((((3/10 : ℝ) ^ 2 : ℝ)) : ℂ)
      = (((3/10 : ℝ) ^ 2 / (q.totient : ℝ) : ℝ) : ℂ) := by
  rw [← Complex.ofReal_natCast q.totient, ← Complex.ofReal_inv, ← Complex.ofReal_mul]
  congr 1
  ring

/-- `x⁻¹ * (x * y) = y` for `x ≠ 0`. -/
lemma inv_mul_cancel_left' {x : ℂ} (hx : x ≠ 0) (y : ℂ) : x⁻¹ * (x * y) = y := by
  rw [← mul_assoc, inv_mul_cancel₀ hx, one_mul]

/-- `x * (x⁻¹ * y) = y` for `x ≠ 0`. -/
lemma mul_inv_cancel_left' {x : ℂ} (hx : x ≠ 0) (y : ℂ) : x * (x⁻¹ * y) = y := by
  rw [← mul_assoc, mul_inv_cancel₀ hx, one_mul]

/-- `‖(φ(q) : ℂ)⁻¹‖ = (φ(q) : ℝ)⁻¹`. -/
lemma norm_totient_inv {q : ℕ} : ‖((q.totient : ℂ))⁻¹‖ = ((q.totient : ℝ))⁻¹ := by
  rw [norm_inv, Complex.norm_natCast]

/-- `‖(x : ℂ)‖ = x` for `x ≥ 0`. -/
lemma norm_ofReal_of_nonneg {x : ℝ} (hx : 0 ≤ x) : ‖((x : ℂ))‖ = x := by
  have h1 : ‖((x : ℂ))‖ ^ 2 = x ^ 2 := by
    rw [← Complex.normSq_eq_norm_sq, Complex.normSq_ofReal]
    ring
  nlinarith only [h1, norm_nonneg ((x : ℂ) : ℂ), hx]

theorem ClassIdentity : Work.LinnikAreas.ClassIdentityHyp := by
  classical
  obtain ⟨Cbr, hCbrpos, hCbr⟩ :=
    Commons.NumberTheory.Linnik.tentMellin_bridge_scale (L := 11/2) (K := 3/10)
      (by norm_num) (by norm_num)
  obtain ⟨Cpr, hCprpos, hCpr⟩ := Commons.NumberTheory.Linnik.tentMellin_principal
  obtain ⟨Cpp, hCpppos, hCpp⟩ := UniformPrimePowerTail
  obtain ⟨Cnc, hCncpos, hCnc⟩ := UniformNonCoprimeTail
  refine ⟨1024 * (Cpr + Cnc + Cpp + Cbr + 1), by positivity, ?_⟩
  intro q hq hqne R hR a ha X hX
  have hq1 : 1 < q := by omega
  have hqR1 : (1 : ℝ) < (q : ℝ) := by exact_mod_cast hq1
  have hqR0 : (0 : ℝ) < (q : ℝ) := by linarith only [hqR1]
  have hqRle : (1 : ℝ) ≤ (q : ℝ) := le_of_lt hqR1
  have hlogq : 0 < Real.log (q : ℝ) := Real.log_pos hqR1
  have hlogne : (Real.log (q : ℝ)) ≠ 0 := ne_of_gt hlogq
  have hlogqC : ((Real.log (q : ℝ) : ℂ)) ≠ 0 := Complex.ofReal_ne_zero.mpr hlogne
  have hφnat : 0 < q.totient := Nat.totient_pos.mpr (by omega)
  have hφpos : 0 < (q.totient : ℝ) := by exact_mod_cast hφnat
  have hφne : ((q.totient : ℝ)) ≠ 0 := ne_of_gt hφpos
  have hφCne : ((q.totient : ℂ)) ≠ 0 := by
    rw [← Complex.ofReal_natCast q.totient]
    exact Complex.ofReal_ne_zero.mpr hφne
  set farTot : ℝ := ∑ χ ∈ Finset.univ.erase (1 : DirichletCharacter ℂ q),
      farSum q (11/2) (3/10) R χ with hfarTot
  set Eb : ℝ := Cbr * ((q : ℝ) ^ (-((49 : ℝ) / 10))
      + ((Real.log (q : ℝ))⁻¹ * ((q : ℝ) ^ (-((147 : ℝ) / 20))) * (1 + Real.log (q : ℝ)))) with hEb
  set Nb : ℝ := Cnc * (Real.log (q : ℝ)) ^ 2 * (q : ℝ) ^ (-((49 : ℝ) / 10)) with hNb
  set Qv : ℝ := (q : ℝ) ^ (-((49 : ℝ) / 20)) / Real.log (q : ℝ) with hQv
  have hQvnn : 0 ≤ Qv := by rw [hQv]; positivity
  have hprincipal : ‖chiSum (1 : DirichletCharacter ℂ q) q X
      - ((Real.log (q : ℝ) * (3/10 : ℝ) ^ 2 : ℝ) : ℂ)‖ ≤ Cpr + 256 * Cnc := by
    have h1 : ‖allSum q X - ((Real.log (q : ℝ) * (3/10 : ℝ) ^ 2 : ℝ) : ℂ)‖ ≤ Cpr := by
      have h := hCpr hq (by norm_num : (0 : ℝ) < (3/10 : ℝ)) (by norm_num : (3/10 : ℝ) ≤ 1)
        (by norm_num : 2 * (3/10 : ℝ) + 2 ≤ 11/2) X hX
      have h' : ‖((Real.log (q : ℝ) : ℂ))⁻¹ * allSum q X - (((3/10 : ℝ) ^ 2 : ℝ) : ℂ)‖
          ≤ Cpr * ((Real.log (q : ℝ))⁻¹) := by
        rw [show allSum q X = (∑ n ∈ Finset.Icc 1 X,
          (ArithmeticFunction.vonMangoldt n : ℂ) / (n : ℂ) *
            ((tentW (Real.log (n : ℝ) / Real.log (q : ℝ)) : ℝ) : ℂ)) from rfl,
          ← Complex.ofReal_inv]
        exact h
      have h2 : ((Real.log (q : ℝ) : ℂ)) * (((Real.log (q : ℝ) : ℂ))⁻¹ * allSum q X
          - (((3/10 : ℝ) ^ 2 : ℝ) : ℂ))
          = allSum q X - ((Real.log (q : ℝ) * (3/10 : ℝ) ^ 2 : ℝ) : ℂ) := by
        rw [mul_sub, mul_inv_cancel_left' hlogqC]
        push_cast
        ring
      calc ‖allSum q X - ((Real.log (q : ℝ) * (3/10 : ℝ) ^ 2 : ℝ) : ℂ)‖
          = ‖((Real.log (q : ℝ) : ℂ)) * (((Real.log (q : ℝ) : ℂ))⁻¹ * allSum q X
              - (((3/10 : ℝ) ^ 2 : ℝ) : ℂ))‖ := by rw [h2]
        _ = ‖((Real.log (q : ℝ) : ℂ))‖ * ‖((Real.log (q : ℝ) : ℂ))⁻¹ * allSum q X
              - (((3/10 : ℝ) ^ 2 : ℝ) : ℂ)‖ := norm_mul _ _
        _ = (Real.log (q : ℝ)) * ‖((Real.log (q : ℝ) : ℂ))⁻¹ * allSum q X
              - (((3/10 : ℝ) ^ 2 : ℝ) : ℂ)‖ := by rw [norm_ofReal_of_nonneg hlogq.le]
        _ ≤ (Real.log (q : ℝ)) * (Cpr * ((Real.log (q : ℝ))⁻¹)) :=
            mul_le_mul_of_nonneg_left h' hlogq.le
        _ = Cpr := by
            rw [← mul_assoc, mul_comm (Real.log (q : ℝ)) Cpr, mul_assoc,
              mul_inv_cancel₀ hlogne, mul_one]
    have h2 : ‖ncsSumC q X‖ ≤ 256 * Cnc := by
      have hcast : ncsSumC q X = ((ncsSum q X : ℝ) : ℂ) := by
        rw [ncsSumC, ncsSum, Complex.ofReal_sum]
        refine Finset.sum_congr rfl (fun n hn => ?_)
        push_cast
        ring
      have hnn : 0 ≤ ncsSum q X := by
        refine Finset.sum_nonneg (fun n hn => ?_)
        have hn1 : 1 ≤ n := (Finset.mem_Icc.mp (Finset.mem_filter.mp hn).1).1
        have hnR : (0 : ℝ) < (n : ℝ) := by exact_mod_cast hn1
        have hwt : 0 ≤ tentW (Real.log (n : ℝ) / Real.log (q : ℝ)) :=
          (Commons.NumberTheory.Linnik.tentWeight_bounds (L := 11/2) (K := 3/10)
            (by norm_num) (by norm_num)).1 _
        have hΛ : 0 ≤ ArithmeticFunction.vonMangoldt n := ArithmeticFunction.vonMangoldt_nonneg
        positivity
      rw [hcast, Complex.norm_real, Real.norm_eq_abs, abs_of_nonneg hnn]
      have hb := hCnc q hq X
      calc ncsSum q X ≤ Nb := hb
        _ ≤ Cnc * 256 := by
            rw [show Nb = Cnc * ((Real.log (q : ℝ)) ^ 2 * (q : ℝ) ^ (-((49 : ℝ) / 10))) by
              rw [hNb]; ring]
            exact mul_le_mul_of_nonneg_left (log_sq_mul_rpow_neg_le' (by omega))
              (le_of_lt hCncpos)
        _ = 256 * Cnc := by ring
    rw [chiSum_one_eq X]
    have h3 : allSum q X - ncsSumC q X - ((Real.log (q : ℝ) * (3/10 : ℝ) ^ 2 : ℝ) : ℂ)
        = (allSum q X - ((Real.log (q : ℝ) * (3/10 : ℝ) ^ 2 : ℝ) : ℂ)) - ncsSumC q X := by ring
    rw [h3]
    exact le_trans (norm_sub_le _ _) (add_le_add h1 h2)
  have hZex : ∀ (χ : DirichletCharacter ℂ q), χ ≠ 1 → ∃ Z : ℂ,
      (Filter.Tendsto (fun ρ : ℝ => ∑ᶠ u : ℂ,
          ((((MeromorphicOn.divisor (completedLFunction χ.primitiveCharacter)
            (Metric.closedBall 0 ρ)) u : ℤ) : ℂ) *
            Hk (11/2) (3/10) ((1 - u) * ((Real.log (q : ℝ) : ℝ) : ℂ))))
        Filter.atTop (nhds Z))
      ∧ ‖Z - boxSum q (11/2) (3/10) R χ‖ ≤ farSum q (11/2) (3/10) R χ := by
    intro χ hχ
    exact ZeroSumBoxComparison χ hχ hR
  let Z : DirichletCharacter ℂ q → ℂ := fun χ => if h : χ = 1 then 0 else Classical.choose (hZex χ h)
  have hZval : ∀ (χ : DirichletCharacter ℂ q) (hχ : χ ≠ 1), Z χ = Classical.choose (hZex χ hχ) := by
    intro χ hχ
    dsimp only [Z]
    rw [dif_neg hχ]
  have hZtend : ∀ (χ : DirichletCharacter ℂ q) (hχ : χ ≠ 1), Filter.Tendsto (fun ρ : ℝ => ∑ᶠ u : ℂ,
      ((((MeromorphicOn.divisor (completedLFunction χ.primitiveCharacter)
        (Metric.closedBall 0 ρ)) u : ℤ) : ℂ) *
        Hk (11/2) (3/10) ((1 - u) * ((Real.log (q : ℝ) : ℝ) : ℂ))))
      Filter.atTop (nhds (Z χ)) := by
    intro χ hχ
    rw [hZval χ hχ]
    exact (Classical.choose_spec (hZex χ hχ)).1
  have hZbox : ∀ (χ : DirichletCharacter ℂ q) (hχ : χ ≠ 1),
      ‖boxSum q (11/2) (3/10) R χ - Z χ‖ ≤ farSum q (11/2) (3/10) R χ := by
    intro χ hχ
    rw [hZval χ hχ, norm_sub_rev]
    exact (Classical.choose_spec (hZex χ hχ)).2
  have hbridge : ∀ (χ : DirichletCharacter ℂ q) (hχ : χ ≠ 1),
      ‖((Real.log (q : ℝ) : ℂ))⁻¹ * chiSum χ.primitiveCharacter q X + Z χ‖ ≤ Eb := by
    intro χ hχ
    have hχ' : χ.primitiveCharacter ≠ 1 := by
      intro h
      apply hχ
      rw [← DirichletCharacter.changeLevel_primitiveCharacter χ, h, DirichletCharacter.changeLevel_one]
    have hprim : (χ.primitiveCharacter).IsPrimitive := DirichletCharacter.primitiveCharacter_isPrimitive χ
    have hNq : χ.conductor ≤ q := Nat.le_of_dvd (by omega) (DirichletCharacter.conductor_dvd_level χ)
    let Kb : ℂ → ℂ := fun u =>
      Complex.exp (-(((11/2 - 2 * (3/10) : ℝ) : ℂ) * ((1 - u) * ((Real.log (q : ℝ) : ℝ) : ℂ)))) *
        (((1 - Complex.exp (-(((3/10 : ℝ) : ℂ) * ((1 - u) * ((Real.log (q : ℝ) : ℝ) : ℂ))))) /
          ((1 - u) * ((Real.log (q : ℝ) : ℝ) : ℂ))) ^ 2)
    have htend : Filter.Tendsto (fun ρ : ℝ => ∑ᶠ u : ℂ,
        ((((MeromorphicOn.divisor (completedLFunction χ.primitiveCharacter)
          (Metric.closedBall 0 ρ)) u : ℤ) : ℂ) * Kb u)) Filter.atTop (nhds (Z χ)) := by
      refine (hZtend χ hχ).congr' (Filter.Eventually.of_forall (fun ρ => ?_))
      refine finsum_congr (fun u => ?_)
      simp only [Kb]
      rw [Hk_eq_exp_form u q]
    have h := hCbr (N := χ.conductor) (χ := χ.primitiveCharacter) hχ' hprim (Q := q) hNq
      (Z := Z χ) htend (X := X) hX
    have e1 : ((11 : ℝ) / 2 - 2 * ((3 : ℝ) / 10)) = ((49 : ℝ) / 10) := by norm_num
    have e2 : (-(3 / 2 : ℝ)) * ((49 : ℝ) / 10) = -((147 : ℝ) / 20) := by norm_num
    simp only [e1, e2] at h
    rw [hEb]
    exact h
  have hDel : ∀ (χ : DirichletCharacter ℂ q) (hχ : χ ≠ 1),
      ‖chiSum χ q X - chiSum χ.primitiveCharacter q X‖ ≤ ncsSum q X := by
    intro χ hχ
    exact ChiSumSubPrimitive χ hχ X
  have hncsu : ncsSum q X ≤ Nb := hCnc q hq X
  set SumChi : ℂ := ∑ χ ∈ Finset.univ.erase (1 : DirichletCharacter ℂ q),
      starRingEnd ℂ (χ (a : ZMod q)) * chiSum χ q X with hSumChi
  set SumBox : ℂ := ∑ χ ∈ Finset.univ.erase (1 : DirichletCharacter ℂ q),
      starRingEnd ℂ (χ (a : ZMod q)) * boxSum q (11/2) (3/10) R χ with hSumBox
  set SumZ : ℂ := ∑ χ ∈ Finset.univ.erase (1 : DirichletCharacter ℂ q),
      starRingEnd ℂ (χ (a : ZMod q)) * Z χ with hSumZ
  set SumErr : ℂ := ∑ χ ∈ Finset.univ.erase (1 : DirichletCharacter ℂ q),
      starRingEnd ℂ (χ (a : ZMod q)) * ((chiSum χ.primitiveCharacter q X
        + ((Real.log (q : ℝ) : ℂ)) * Z χ)
        + (chiSum χ q X - chiSum χ.primitiveCharacter q X)) with hSumErr
  set Rho1 : ℂ := chiSum (1 : DirichletCharacter ℂ q) q X
      - ((Real.log (q : ℝ)) * (((3/10 : ℝ) ^ 2 : ℝ) : ℂ)) with hRho1
  have hdecomp : classSum (q := q) a X = primePS (q := q) a X + ((classPP (q := q) a X : ℝ) : ℂ) := by
    rw [show classSum (q := q) a X = (∑ n ∈ Finset.Ioc 0 X,
        ((ArithmeticFunction.vonMangoldt.residueClass (a : ZMod q) n : ℝ) : ℂ) *
          (((Commons.NumberTheory.Linnik.tentWeight (11/2) (3/10)
            (Real.log (n : ℝ) / Real.log (q : ℝ)) : ℝ) : ℂ) / (n : ℂ))) from rfl,
      ClassLambdaSumDecomp (q := q) a X, ofReal_primeSum_eq_primePS, ofReal_classPP_eq]
  have horth_all : classSum (q := q) a X = ((q.totient : ℂ))⁻¹ *
      ∑ χ : DirichletCharacter ℂ q, starRingEnd ℂ (χ (a : ZMod q)) * chiSum χ q X :=
    ClassSumOrthogonality a ha X
  have hsum_split : (∑ χ : DirichletCharacter ℂ q,
        starRingEnd ℂ (χ (a : ZMod q)) * chiSum χ q X)
      = SumChi + starRingEnd ℂ ((1 : DirichletCharacter ℂ q) (a : ZMod q))
          * chiSum (1 : DirichletCharacter ℂ q) q X := by
    rw [hSumChi]
    exact (Finset.sum_erase_add (Finset.univ)
      (fun χ : DirichletCharacter ℂ q => starRingEnd ℂ (χ (a : ZMod q)) * chiSum χ q X)
      (Finset.mem_univ 1)).symm
  have hstar1 : starRingEnd ℂ ((1 : DirichletCharacter ℂ q) (a : ZMod q)) = 1 := by
    rw [one_apply_eq_indicator, if_pos (isUnit_of_coprime ha)]
    simp
  have hrel : ((Real.log (q : ℝ) : ℂ))⁻¹ * primePS (q := q) a X
      = ((q.totient : ℂ))⁻¹ * (((Real.log (q : ℝ) : ℂ))⁻¹
          * (chiSum (1 : DirichletCharacter ℂ q) q X + SumChi))
        - ((Real.log (q : ℝ) : ℂ))⁻¹ * ((classPP (q := q) a X : ℝ) : ℂ) := by
    have h1 : primePS (q := q) a X = ((q.totient : ℂ))⁻¹
        * (SumChi + chiSum (1 : DirichletCharacter ℂ q) q X)
        - ((classPP (q := q) a X : ℝ) : ℂ) := by
      have h2 : classSum (q := q) a X = ((q.totient : ℂ))⁻¹
          * (SumChi + chiSum (1 : DirichletCharacter ℂ q) q X) := by
        rw [horth_all, hsum_split, hstar1, one_mul]
      rw [← h2, hdecomp]
      ring
    rw [h1]
    ring
  have hchi1 : ((Real.log (q : ℝ) : ℂ))⁻¹ * chiSum (1 : DirichletCharacter ℂ q) q X
      = (((3/10 : ℝ) ^ 2 : ℝ) : ℂ) + ((Real.log (q : ℝ) : ℂ))⁻¹ * Rho1 := by
    rw [hRho1, mul_sub, ← mul_assoc, inv_mul_cancel₀ hlogqC, one_mul]
    ring
  have hsumchi : ((Real.log (q : ℝ) : ℂ))⁻¹ * SumChi
      = -SumZ + ((Real.log (q : ℝ) : ℂ))⁻¹ * SumErr := by
    have hpoint : ∀ (χ : DirichletCharacter ℂ q),
        chiSum χ q X = -(((Real.log (q : ℝ) : ℂ)) * Z χ)
          + ((chiSum χ.primitiveCharacter q X + ((Real.log (q : ℝ) : ℂ)) * Z χ)
              + (chiSum χ q X - chiSum χ.primitiveCharacter q X)) := fun χ => by ring
    have hA : SumChi = ∑ χ ∈ Finset.univ.erase (1 : DirichletCharacter ℂ q),
        starRingEnd ℂ (χ (a : ZMod q)) * (-(((Real.log (q : ℝ) : ℂ)) * Z χ))
        + ∑ χ ∈ Finset.univ.erase (1 : DirichletCharacter ℂ q),
          starRingEnd ℂ (χ (a : ZMod q))
            * ((chiSum χ.primitiveCharacter q X + ((Real.log (q : ℝ) : ℂ)) * Z χ)
                + (chiSum χ q X - chiSum χ.primitiveCharacter q X)) := by
      rw [hSumChi, ← Finset.sum_add_distrib]
      refine Finset.sum_congr rfl (fun χ hχ => ?_)
      rw [hpoint χ]
      ring
    have hB : ∑ χ ∈ Finset.univ.erase (1 : DirichletCharacter ℂ q),
        starRingEnd ℂ (χ (a : ZMod q)) * (-(((Real.log (q : ℝ) : ℂ)) * Z χ))
        = -(((Real.log (q : ℝ) : ℂ)) * SumZ) := by
      rw [hSumZ, Finset.mul_sum, ← Finset.sum_neg_distrib]
      refine Finset.sum_congr rfl (fun χ hχ => by ring)
    rw [hA, hB, hSumErr, mul_add, mul_neg]
    rw [inv_mul_cancel_left' hlogqC]
  have hkey : ((Real.log (q : ℝ) : ℂ))⁻¹ * primePS (q := q) a X
        - (((3/10 : ℝ) ^ 2 / (q.totient : ℝ) : ℝ) : ℂ) + ((q.totient : ℂ))⁻¹ * SumBox
      = ((q.totient : ℂ))⁻¹ * (SumBox - SumZ)
        + ((q.totient : ℂ))⁻¹ * (((Real.log (q : ℝ) : ℂ))⁻¹ * (Rho1 + SumErr))
        - ((Real.log (q : ℝ) : ℂ))⁻¹ * ((classPP (q := q) a X : ℝ) : ℂ) := by
    rw [← totient_inv_mul_Ksq, hrel, mul_add, hchi1, hsumchi]
    ring
  have hstarnorm : ∀ χ : DirichletCharacter ℂ q, ‖starRingEnd ℂ (χ (a : ZMod q))‖ = 1 := by
    intro χ
    rw [starRingEnd_apply, norm_star]
    have hu : IsUnit (a : ZMod q) := isUnit_of_coprime ha
    have h : χ (a : ZMod q) = χ (hu.unit : ZMod q) := by rw [hu.unit_spec]
    rw [h]
    exact DirichletCharacter.unit_norm_eq_one χ hu.unit
  have hfar : ‖SumBox - SumZ‖ ≤ farTot := by
    have hsum : SumBox - SumZ = ∑ χ ∈ Finset.univ.erase (1 : DirichletCharacter ℂ q),
        starRingEnd ℂ (χ (a : ZMod q)) * (boxSum q (11/2) (3/10) R χ - Z χ) := by
      rw [hSumBox, hSumZ, ← Finset.sum_sub_distrib]
      refine Finset.sum_congr rfl (fun χ hχ => by ring)
    rw [hsum, hfarTot]
    calc ‖∑ χ ∈ Finset.univ.erase (1 : DirichletCharacter ℂ q),
          starRingEnd ℂ (χ (a : ZMod q)) * (boxSum q (11/2) (3/10) R χ - Z χ)‖
        ≤ ∑ χ ∈ Finset.univ.erase (1 : DirichletCharacter ℂ q),
            ‖starRingEnd ℂ (χ (a : ZMod q)) * (boxSum q (11/2) (3/10) R χ - Z χ)‖ :=
          norm_sum_le _ _
      _ = ∑ χ ∈ Finset.univ.erase (1 : DirichletCharacter ℂ q),
            ‖boxSum q (11/2) (3/10) R χ - Z χ‖ := by
          refine Finset.sum_congr rfl (fun χ hχ => ?_)
          rw [norm_mul, hstarnorm χ, one_mul]
      _ ≤ ∑ χ ∈ Finset.univ.erase (1 : DirichletCharacter ℂ q),
            farSum q (11/2) (3/10) R χ :=
          Finset.sum_le_sum (fun χ hχ => hZbox χ (Finset.mem_erase.mp hχ).1)
  have hbridgeErr : ∀ (χ : DirichletCharacter ℂ q) (hχ : χ ≠ 1),
      ‖chiSum χ.primitiveCharacter q X + ((Real.log (q : ℝ) : ℂ)) * Z χ‖
        ≤ (Real.log (q : ℝ)) * Eb := by
    intro χ hχ
    have h := hbridge χ hχ
    have hmul : ((Real.log (q : ℝ) : ℂ))
          * (((Real.log (q : ℝ) : ℂ))⁻¹ * chiSum χ.primitiveCharacter q X + Z χ)
        = chiSum χ.primitiveCharacter q X + ((Real.log (q : ℝ) : ℂ)) * Z χ := by
      rw [mul_add, mul_inv_cancel_left' hlogqC]
    rw [← hmul, norm_mul, norm_ofReal_of_nonneg hlogq.le]
    exact mul_le_mul_of_nonneg_left h hlogq.le
  have hSumErr_bound : ‖SumErr‖ ≤ (q.totient : ℝ) * ((Real.log (q : ℝ)) * Eb + Nb) := by
    rw [hSumErr]
    refine le_trans (norm_sum_le _ _) ?_
    have hterm : ∀ χ ∈ Finset.univ.erase (1 : DirichletCharacter ℂ q),
        ‖starRingEnd ℂ (χ (a : ZMod q)) * ((chiSum χ.primitiveCharacter q X
          + ((Real.log (q : ℝ) : ℂ)) * Z χ) + (chiSum χ q X - chiSum χ.primitiveCharacter q X))‖
        ≤ (Real.log (q : ℝ)) * Eb + Nb := by
      intro χ hχmem
      have hχ : χ ≠ 1 := (Finset.mem_erase.mp hχmem).1
      rw [norm_mul, hstarnorm χ, one_mul]
      refine le_trans (norm_add_le _ _) (add_le_add (hbridgeErr χ hχ) ?_)
      exact le_trans (hDel χ hχ) hncsu
    calc ∑ χ ∈ Finset.univ.erase (1 : DirichletCharacter ℂ q),
          ‖starRingEnd ℂ (χ (a : ZMod q)) * ((chiSum χ.primitiveCharacter q X
            + ((Real.log (q : ℝ) : ℂ)) * Z χ) + (chiSum χ q X - chiSum χ.primitiveCharacter q X))‖
        ≤ ∑ _χ ∈ Finset.univ.erase (1 : DirichletCharacter ℂ q),
            ((Real.log (q : ℝ)) * Eb + Nb) := Finset.sum_le_sum hterm
      _ = (Finset.univ.erase (1 : DirichletCharacter ℂ q)).card
            * ((Real.log (q : ℝ)) * Eb + Nb) := by rw [Finset.sum_const, nsmul_eq_mul]
      _ ≤ (q.totient : ℝ) * ((Real.log (q : ℝ)) * Eb + Nb) := by
          refine mul_le_mul_of_nonneg_right ?_ (by positivity)
          have hcard : (Finset.univ : Finset (DirichletCharacter ℂ q)).card = q.totient := by
            rw [Finset.card_univ, ← Nat.card_eq_fintype_card]
            exact DirichletCharacter.card_eq_totient_of_hasEnoughRootsOfUnity ℂ q
          have hle : (Finset.univ.erase (1 : DirichletCharacter ℂ q)).card ≤ q.totient := by
            rw [← hcard]
            exact Finset.card_le_card (Finset.erase_subset _ _)
          exact_mod_cast hle
  have hEb1 : Eb ≤ 128 * Cbr * Qv := by
    rw [hEb, hQv]
    have h4 : (q : ℝ) ^ (-((49 : ℝ) / 10))
        ≤ 16 * ((q : ℝ) ^ (-((49 : ℝ) / 20)) / Real.log (q : ℝ)) := rpow_neg_le_div_log hq
    have h17 : 1 + Real.log (q : ℝ) ≤ 17 * (q : ℝ) ^ ((49 : ℝ) / 10) := by
      have hl : Real.log (q : ℝ) ≤ 16 * (q : ℝ) ^ ((49 : ℝ) / 20) := log_natCast_le_rpow q (by omega)
      have hq4 : (1 : ℝ) ≤ (q : ℝ) ^ ((49 : ℝ) / 10) := by
        have h := Real.rpow_le_rpow (by norm_num : (0 : ℝ) ≤ 1) hqRle
          (by norm_num : (0 : ℝ) ≤ (49 : ℝ) / 10)
        rwa [Real.one_rpow] at h
      have h20 : (q : ℝ) ^ ((49 : ℝ) / 20) ≤ (q : ℝ) ^ ((49 : ℝ) / 10) :=
        Real.rpow_le_rpow_of_exponent_le hqRle (by norm_num)
      linarith only [hl, hq4, h20]
    have hrpow : (q : ℝ) ^ (-((147 : ℝ) / 20))
        ≤ 16 * ((q : ℝ) ^ (-((49 : ℝ) / 20)) / Real.log (q : ℝ)) := by
      have key : (q : ℝ) ^ (-((147 : ℝ) / 20)) * Real.log (q : ℝ)
          ≤ 16 * (q : ℝ) ^ (-((49 : ℝ) / 20)) := by
        calc (q : ℝ) ^ (-((147 : ℝ) / 20)) * Real.log (q : ℝ)
            ≤ (q : ℝ) ^ (-((147 : ℝ) / 20)) * (16 * (q : ℝ) ^ ((49 : ℝ) / 20)) :=
              mul_le_mul_of_nonneg_left (log_natCast_le_rpow q (by omega)) (by positivity)
          _ = 16 * ((q : ℝ) ^ (-((147 : ℝ) / 20)) * (q : ℝ) ^ ((49 : ℝ) / 20)) := by ring
          _ = 16 * ((q : ℝ) ^ (-((147 : ℝ) / 20) + ((49 : ℝ) / 20))) := by rw [Real.rpow_add hqR0]
          _ = 16 * (q : ℝ) ^ (-((49 : ℝ) / 10)) := by norm_num
          _ ≤ 16 * (q : ℝ) ^ (-((49 : ℝ) / 20)) := by
              have h1 : (q : ℝ) ^ (-((49 : ℝ) / 10)) ≤ (q : ℝ) ^ (-((49 : ℝ) / 20)) :=
                Real.rpow_le_rpow_of_exponent_le hqRle (by norm_num)
              linarith only [h1]
      calc (q : ℝ) ^ (-((147 : ℝ) / 20))
          = ((q : ℝ) ^ (-((147 : ℝ) / 20)) * Real.log (q : ℝ)) / Real.log (q : ℝ) := by
            rw [mul_div_cancel_right₀ _ hlogne]
        _ ≤ (16 * (q : ℝ) ^ (-((49 : ℝ) / 20))) / Real.log (q : ℝ) :=
            div_le_div_of_nonneg_right key hlogq.le
        _ = 16 * ((q : ℝ) ^ (-((49 : ℝ) / 20)) / Real.log (q : ℝ)) := by ring
    have h5 : (Real.log (q : ℝ))⁻¹ * ((q : ℝ) ^ (-((147 : ℝ) / 20))) * (1 + Real.log (q : ℝ))
        ≤ 32 * ((q : ℝ) ^ (-((49 : ℝ) / 20)) / Real.log (q : ℝ)) := by
      have key : (Real.log (q : ℝ))⁻¹ * (q : ℝ) ^ (-((147 : ℝ) / 20)) * (1 + Real.log (q : ℝ))
            * Real.log (q : ℝ) ≤ 32 * (q : ℝ) ^ (-((49 : ℝ) / 20)) := by
        calc (Real.log (q : ℝ))⁻¹ * (q : ℝ) ^ (-((147 : ℝ) / 20)) * (1 + Real.log (q : ℝ))
              * Real.log (q : ℝ)
            = ((Real.log (q : ℝ))⁻¹ * Real.log (q : ℝ))
                * ((q : ℝ) ^ (-((147 : ℝ) / 20)) * (1 + Real.log (q : ℝ))) := by ring
          _ = 1 * ((q : ℝ) ^ (-((147 : ℝ) / 20)) * (1 + Real.log (q : ℝ))) := by
              rw [inv_mul_cancel₀ hlogne]
          _ = (q : ℝ) ^ (-((147 : ℝ) / 20)) * (1 + Real.log (q : ℝ)) := by rw [one_mul]
          _ ≤ (q : ℝ) ^ (-((147 : ℝ) / 20)) * (17 * (q : ℝ) ^ ((49 : ℝ) / 10)) :=
              mul_le_mul_of_nonneg_left h17 (by positivity)
          _ = 17 * ((q : ℝ) ^ (-((147 : ℝ) / 20)) * (q : ℝ) ^ ((49 : ℝ) / 10)) := by ring
          _ = 17 * ((q : ℝ) ^ (-((147 : ℝ) / 20) + ((49 : ℝ) / 10))) := by rw [Real.rpow_add hqR0]
          _ = 17 * (q : ℝ) ^ (-((49 : ℝ) / 20)) := by norm_num
          _ ≤ 32 * (q : ℝ) ^ (-((49 : ℝ) / 20)) := by
              have hpos : 0 < (q : ℝ) ^ (-((49 : ℝ) / 20)) := Real.rpow_pos_of_pos hqR0 _
              linarith only [hpos]
      calc (Real.log (q : ℝ))⁻¹ * (q : ℝ) ^ (-((147 : ℝ) / 20)) * (1 + Real.log (q : ℝ))
          = ((Real.log (q : ℝ))⁻¹ * (q : ℝ) ^ (-((147 : ℝ) / 20)) * (1 + Real.log (q : ℝ))
              * Real.log (q : ℝ)) / Real.log (q : ℝ) := by
            rw [mul_div_cancel_right₀ _ hlogne]
        _ ≤ (32 * (q : ℝ) ^ (-((49 : ℝ) / 20))) / Real.log (q : ℝ) :=
            div_le_div_of_nonneg_right key hlogq.le
        _ = 32 * ((q : ℝ) ^ (-((49 : ℝ) / 20)) / Real.log (q : ℝ)) := by ring
    have hsum : (q : ℝ) ^ (-((49 : ℝ) / 10))
        + (Real.log (q : ℝ))⁻¹ * ((q : ℝ) ^ (-((147 : ℝ) / 20))) * (1 + Real.log (q : ℝ))
        ≤ 64 * ((q : ℝ) ^ (-((49 : ℝ) / 20)) / Real.log (q : ℝ)) := by linarith only [hQvnn, h4, h5]
    calc Cbr * ((q : ℝ) ^ (-((49 : ℝ) / 10))
          + ((Real.log (q : ℝ))⁻¹ * ((q : ℝ) ^ (-((147 : ℝ) / 20))) * (1 + Real.log (q : ℝ))))
        ≤ Cbr * (64 * ((q : ℝ) ^ (-((49 : ℝ) / 20)) / Real.log (q : ℝ))) :=
          mul_le_mul_of_nonneg_left hsum (le_of_lt hCbrpos)
      _ ≤ 128 * Cbr * ((q : ℝ) ^ (-((49 : ℝ) / 20)) / Real.log (q : ℝ)) := by
          have hpos : 0 ≤ ((q : ℝ) ^ (-((49 : ℝ) / 20)) / Real.log (q : ℝ)) := by positivity
          nlinarith only [hCbrpos, hpos, hQvnn]
  have hNb1 : (Real.log (q : ℝ))⁻¹ * Nb ≤ 256 * Cnc * Qv := by
    rw [hNb, hQv]
    have h256 : (Real.log (q : ℝ)) ^ 2 * (q : ℝ) ^ (-((49 : ℝ) / 20)) ≤ 256 :=
      log_sq_mul_rpow_neg_le q (by omega)
    have hswap : (q : ℝ) ^ (-((49 : ℝ) / 10))
        = (q : ℝ) ^ (-((49 : ℝ) / 20)) * (q : ℝ) ^ (-((49 : ℝ) / 20)) := by
      rw [← Real.rpow_add hqR0]; norm_num
    have hpos : 0 ≤ ((q : ℝ) ^ (-((49 : ℝ) / 20)) / Real.log (q : ℝ)) := by positivity
    calc (Real.log (q : ℝ))⁻¹ * (Cnc * (Real.log (q : ℝ)) ^ 2 * (q : ℝ) ^ (-((49 : ℝ) / 10)))
        = Cnc * ((Real.log (q : ℝ)) ^ 2 * (q : ℝ) ^ (-((49 : ℝ) / 20)))
            * ((q : ℝ) ^ (-((49 : ℝ) / 20)) / Real.log (q : ℝ)) := by
          rw [hswap, div_eq_mul_inv]; ring
      _ ≤ Cnc * 256 * ((q : ℝ) ^ (-((49 : ℝ) / 20)) / Real.log (q : ℝ)) :=
          mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_left h256 (le_of_lt hCncpos)) hpos
      _ = 256 * Cnc * ((q : ℝ) ^ (-((49 : ℝ) / 20)) / Real.log (q : ℝ)) := by ring
  have hmain : ‖((Real.log (q : ℝ) : ℂ))⁻¹ * primePS (q := q) a X
        - (((3/10 : ℝ) ^ 2 / (q.totient : ℝ) : ℝ) : ℂ) + ((q.totient : ℂ))⁻¹ * SumBox‖
      ≤ (q.totient : ℝ)⁻¹ * farTot
        + ((q.totient : ℝ))⁻¹ * ((Real.log (q : ℝ))⁻¹
            * ((Cpr + 256 * Cnc) + (q.totient : ℝ) * ((Real.log (q : ℝ)) * Eb + Nb)))
        + (Real.log (q : ℝ))⁻¹ * (Cpp * (q : ℝ) ^ (-((49 : ℝ) / 20))) := by
    rw [hkey]
    refine le_trans (norm_sub_le _ _) (add_le_add ?_ ?_)
    · refine le_trans (norm_add_le _ _) (add_le_add ?_ ?_)
      · rw [norm_mul, norm_totient_inv]
        exact mul_le_mul_of_nonneg_left hfar (by positivity)
      · rw [norm_mul, norm_totient_inv, norm_mul, norm_inv, norm_ofReal_of_nonneg hlogq.le]
        refine mul_le_mul_of_nonneg_left (mul_le_mul_of_nonneg_left ?_ (by positivity)) (by positivity)
        have hRho1bound : ‖Rho1‖ ≤ Cpr + 256 * Cnc := by
          have h : Rho1 = chiSum (1 : DirichletCharacter ℂ q) q X
              - ((Real.log (q : ℝ) * (3/10 : ℝ) ^ 2 : ℝ) : ℂ) := by
            rw [hRho1]
            push_cast
            ring
          rw [h]
          exact hprincipal
        exact le_trans (norm_add_le _ _) (add_le_add hRho1bound hSumErr_bound)
    · rw [norm_mul, norm_inv, norm_ofReal_of_nonneg hlogq.le]
      have hcpp : ‖((classPP (q := q) a X : ℝ) : ℂ)‖ = classPP (q := q) a X := by
        rw [Complex.norm_real, Real.norm_eq_abs, abs_of_nonneg]
        refine Finset.sum_nonneg (fun n hn => ?_)
        have hn1 : 1 ≤ n := (Finset.mem_Icc.mp (Finset.mem_filter.mp hn).1).1
        have hnR : (0 : ℝ) < (n : ℝ) := by exact_mod_cast hn1
        have hwt : 0 ≤ tentW (Real.log (n : ℝ) / Real.log (q : ℝ)) :=
          (Commons.NumberTheory.Linnik.tentWeight_bounds (L := 11/2) (K := 3/10)
            (by norm_num) (by norm_num)).1 _
        have hΛ : 0 ≤ ArithmeticFunction.vonMangoldt n := ArithmeticFunction.vonMangoldt_nonneg
        positivity
      rw [hcpp]
      exact mul_le_mul_of_nonneg_left (hCpp q hq a X) (by positivity)
  have hnum3 : (q.totient : ℝ)⁻¹ * farTot
        + ((q.totient : ℝ))⁻¹ * ((Real.log (q : ℝ))⁻¹
            * ((Cpr + 256 * Cnc) + (q.totient : ℝ) * ((Real.log (q : ℝ)) * Eb + Nb)))
        + (Real.log (q : ℝ))⁻¹ * (Cpp * (q : ℝ) ^ (-((49 : ℝ) / 20)))
      ≤ 1024 * (Cpr + Cnc + Cpp + Cbr + 1) / ((q.totient : ℝ) * Real.log (q : ℝ))
        + (q.totient : ℝ)⁻¹ * farTot
        + 1024 * (Cpr + Cnc + Cpp + Cbr + 1) * (q : ℝ) ^ (-((49 : ℝ) / 20)) / Real.log (q : ℝ) := by
    have hsplit : ((q.totient : ℝ))⁻¹ * ((Real.log (q : ℝ))⁻¹
          * ((Cpr + 256 * Cnc) + (q.totient : ℝ) * ((Real.log (q : ℝ)) * Eb + Nb)))
        = ((q.totient : ℝ) * Real.log (q : ℝ))⁻¹ * (Cpr + 256 * Cnc)
          + ((Real.log (q : ℝ))⁻¹ * ((Real.log (q : ℝ)) * Eb + Nb)) := by
      field_simp
    rw [hsplit]
    have hY : (Real.log (q : ℝ))⁻¹ * ((Real.log (q : ℝ)) * Eb + Nb)
        = Eb + (Real.log (q : ℝ))⁻¹ * Nb := by
      rw [mul_add, ← mul_assoc, inv_mul_cancel₀ hlogne, one_mul]
    rw [hY]
    have hprin : ((q.totient : ℝ) * Real.log (q : ℝ))⁻¹ * (Cpr + 256 * Cnc)
        ≤ 1024 * (Cpr + Cnc + Cpp + Cbr + 1) / ((q.totient : ℝ) * Real.log (q : ℝ)) := by
      rw [div_eq_mul_inv]
      rw [show 1024 * (Cpr + Cnc + Cpp + Cbr + 1) * ((q.totient : ℝ) * Real.log (q : ℝ))⁻¹
          = ((q.totient : ℝ) * Real.log (q : ℝ))⁻¹ * (1024 * (Cpr + Cnc + Cpp + Cbr + 1)) by ring]
      refine mul_le_mul_of_nonneg_left ?_ (by positivity :
        (0 : ℝ) ≤ ((q.totient : ℝ) * Real.log (q : ℝ))⁻¹)
      linarith only [hCprpos, hCncpos, hCpppos, hCbrpos]
    have hEN : Eb + (Real.log (q : ℝ))⁻¹ * Nb ≤ (128 * Cbr + 256 * Cnc) * Qv := by
      have h1 := hEb1
      have h2 := hNb1
      linarith only [h1, h2, hQvnn, hEb1, hNb1]
    have hP : (Real.log (q : ℝ))⁻¹ * (Cpp * (q : ℝ) ^ (-((49 : ℝ) / 20))) ≤ Cpp * Qv := by
      rw [hQv]
      rw [show (Real.log (q : ℝ))⁻¹ * (Cpp * (q : ℝ) ^ (-((49 : ℝ) / 20)))
          = Cpp * ((q : ℝ) ^ (-((49 : ℝ) / 20)) / Real.log (q : ℝ)) by
        rw [div_eq_mul_inv]
        ring]
    have hK : (128 * Cbr + 256 * Cnc + Cpp) ≤ 1024 * (Cpr + Cnc + Cpp + Cbr + 1) := by
      linarith only [hCprpos, hCncpos, hCpppos, hCbrpos]
    have hKQv : (128 * Cbr + 256 * Cnc + Cpp) * Qv
        ≤ 1024 * (Cpr + Cnc + Cpp + Cbr + 1) * Qv := mul_le_mul_of_nonneg_right hK hQvnn
    have hKQv' : 1024 * (Cpr + Cnc + Cpp + Cbr + 1) * Qv
        = 1024 * (Cpr + Cnc + Cpp + Cbr + 1) * (q : ℝ) ^ (-((49 : ℝ) / 20))
            / Real.log (q : ℝ) := by
      rw [hQv, mul_div_assoc]
    have hENP : (128 * Cbr + 256 * Cnc) * Qv + Cpp * Qv
        = (128 * Cbr + 256 * Cnc + Cpp) * Qv := by ring
    rw [hKQv'] at hKQv
    linarith only [hprin, hEN, hP, hKQv, hENP, hEb1, hNb1]
  refine le_trans hmain ?_
  rw [show (-((49 : ℝ) / 10) / 2) = -((49 : ℝ) / 20) by norm_num]
  exact hnum3

end Work.LinnikAreas
