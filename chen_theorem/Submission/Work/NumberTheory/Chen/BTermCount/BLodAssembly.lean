import Mathlib
import Submission.Work.NumberTheory.Chen.BTermCount.BLodCut
import Submission.Work.NumberTheory.Chen.BTermCount.BLodConductorDecomp
import Submission.Work.NumberTheory.Chen.BTermCount.BLodMobiusBound
import Submission.Work.NumberTheory.Chen.BTermCount.BLodCutBilinear
import Submission.Work.NumberTheory.Chen.BTermCount.BLodSmallLargeSplit
import Submission.Work.NumberTheory.Chen.BTermCount.bRemCorrCharSum
import Submission.Work.NumberTheory.Chen.BTermCount.sumThreePowInvTotientBound

open Finset Filter
open scoped BigOperators

namespace Work.NumberTheory.Chen.BTermCount

attribute [local instance] Classical.propDecidable

/-!
# Assembly of the level-of-distribution estimate

`BLodStepChar` is the first step of the reduction: the character identity `abs_bRemCorr_le`
together with the conductor decomposition `BLodConductorDecomp`.
-/

/-- The primitive-character sum at level `r` of the `t`-divisible part of `B̄`. -/
noncomputable def bProdCharSumDivSum (x M Y t r : ℕ) : ℝ :=
  ∑ ψ ∈ (Finset.univ.filter (fun ψ : DirichletCharacter ℂ r => ψ.IsPrimitive)),
    ‖∑ n ∈ (bProdSet x M Y).filter (fun n => t ∣ n), ψ ((n:ℕ) : ZMod r)‖

theorem bProdCharSumDivSum_nonneg (x M Y t r : ℕ) : 0 ≤ bProdCharSumDivSum x M Y t r :=
  Finset.sum_nonneg (fun _ _ => norm_nonneg _)

/-- **Step 1 of the reduction.**  The weighted absolute values of the corrected remainders are
bounded by the totient-weighted sum of the character sums over primitive conductors. -/
theorem BLodStepChar (x M Y D : ℕ) :
    (∑ d ∈ (Finset.Icc 1 D).filter (fun d => d % 2 = 1),
        (3 : ℝ) ^ (d.primeFactors.card) * |bRemCorr x M Y d|)
      ≤ ∑ d ∈ (Finset.Icc 1 D).filter (fun d => d % 2 = 1),
          ((3 : ℝ) ^ (d.primeFactors.card) / (Nat.totient d : ℝ)) *
            (∑ c ∈ (d.divisors.attach.filter (fun c => 2 ≤ c.1)),
              ∑ ψ : {ψ' : DirichletCharacter ℂ c.1 // ψ'.IsPrimitive},
                ‖bProdCharSum x M Y d
                  (DirichletCharacter.changeLevel (Nat.mem_divisors.mp c.2).1 ψ.1)‖) := by
  refine Finset.sum_le_sum (fun d hd => ?_)
  obtain ⟨hdmem, hodd⟩ := Finset.mem_filter.mp hd
  have hd1 : 1 ≤ d := (Finset.mem_Icc.mp hdmem).1
  haveI : NeZero d := ⟨by omega⟩
  have h := abs_bRemCorr_le x M Y d hodd
  have h' : |bRemCorr x M Y d| ≤ (Nat.totient d : ℝ)⁻¹ *
      (∑ c ∈ (d.divisors.attach.filter (fun c => 2 ≤ c.1)),
        ∑ ψ : {ψ' : DirichletCharacter ℂ c.1 // ψ'.IsPrimitive},
          ‖bProdCharSum x M Y d
            (DirichletCharacter.changeLevel (Nat.mem_divisors.mp c.2).1 ψ.1)‖) := by
    rw [← BLodConductorDecomp x M Y d]
    exact h
  calc (3 : ℝ) ^ (d.primeFactors.card) * |bRemCorr x M Y d|
      ≤ (3 : ℝ) ^ (d.primeFactors.card) * ((Nat.totient d : ℝ)⁻¹ *
          (∑ c ∈ (d.divisors.attach.filter (fun c => 2 ≤ c.1)),
            ∑ ψ : {ψ' : DirichletCharacter ℂ c.1 // ψ'.IsPrimitive},
              ‖bProdCharSum x M Y d
                (DirichletCharacter.changeLevel (Nat.mem_divisors.mp c.2).1 ψ.1)‖)) :=
        mul_le_mul_of_nonneg_left h' (by positivity)
    _ = ((3 : ℝ) ^ (d.primeFactors.card) / (Nat.totient d : ℝ)) *
          (∑ c ∈ (d.divisors.attach.filter (fun c => 2 ≤ c.1)),
            ∑ ψ : {ψ' : DirichletCharacter ℂ c.1 // ψ'.IsPrimitive},
              ‖bProdCharSum x M Y d
                (DirichletCharacter.changeLevel (Nat.mem_divisors.mp c.2).1 ψ.1)‖) := by
        rw [div_eq_mul_inv]; ring

/-- **Step 3 of the reduction.**  The `t`-divisible part of the ternary character sum is a sum
of dyadic-block hyperbola bilinear forms with the cut coefficient sequences
`aCut M Y j (tSmall Y t)`, `bCut Y (tLarge Y t)`. -/
theorem BLodXtBlock (x M Y t r : ℕ) (ht : t ≠ 0) (hM : 1 ≤ M)
    (ψ : DirichletCharacter ℂ r) :
    ‖∑ n ∈ (bProdSet x M Y).filter (fun n => t ∣ n), ψ ((n:ℕ) : ZMod r)‖
      ≤ ∑ j ∈ Finset.range (blockCount M Y),
          ‖bilinForm (2 * blockStart M j) ((x + 2) / blockStart M j + 1) (x + 2)
            (aCut M Y j (tSmall Y t)) (bCut Y (tLarge Y t)) r ψ‖ := by
  have h1 : ∀ p : ℕ, p.Prime → p ∣ tSmall Y t → p < Y :=
    fun p hp h => prime_dvd_tSmall_lt hp h
  have h2 : ∀ p : ℕ, p.Prime → p ∣ tLarge Y t → Y ≤ p :=
    fun p hp h => prime_dvd_tLarge_ge hp h
  have hprod := tSmall_mul_tLarge Y t ht
  have hkey := BLodCutBilinear x M Y r (tSmall Y t) (tLarge Y t) hM ψ h1 h2
  rw [hprod] at hkey
  rw [hkey]
  exact norm_sum_le _ _

/-- **Step 3, summed form.**  The primitive-character sum of the `t`-divisible part of `B̄` is
bounded by the sum over dyadic blocks and primitive characters of the cut bilinear forms. -/
theorem bProdCharSumDivSum_le_block (x M Y t r : ℕ) (ht : t ≠ 0) (hM : 1 ≤ M) :
    bProdCharSumDivSum x M Y t r
      ≤ ∑ j ∈ Finset.range (blockCount M Y),
          ∑ ψ ∈ (Finset.univ.filter (fun ψ : DirichletCharacter ℂ r => ψ.IsPrimitive)),
            ‖bilinForm (2 * blockStart M j) ((x + 2) / blockStart M j + 1) (x + 2)
              (aCut M Y j (tSmall Y t)) (bCut Y (tLarge Y t)) r ψ‖ := by
  unfold bProdCharSumDivSum
  rw [Finset.sum_comm]
  exact Finset.sum_le_sum (fun ψ _ => BLodXtBlock x M Y t r ht hM ψ)

end Work.NumberTheory.Chen.BTermCount
