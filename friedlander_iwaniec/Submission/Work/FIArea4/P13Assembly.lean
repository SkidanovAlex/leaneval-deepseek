import Mathlib
import Submission.Work.FIArea4.P13Defs
import Submission.Work.FIArea4.P13basic
import Submission.Work.FIArea4.P13Scale

/-!
# The §13 assembly: Proposition 12.1 (all `ε`) implies Proposition 13.1 (all `ε`)

The file isolates the combinatorial part of the Friedlander–Iwaniec §13 argument from its
analytic/numerical inputs, which appear as explicit hypotheses: Proposition 12.1 at the exponent
`ε/8` (`h121`), the divisor bound (`htau`), the two numerical comparisons of the brackets
`p14T12`/`p14T13` (`hnl`, `hns`), the prime-count and prime-divisor bounds (`hpc`, `hpd`), the
arithmetic facts about `P` (`haf`), the trivial estimate of the `p ∣ r` part (`heb`), the
class-refinement monotonicity (`hea`) and the `1`-to-`1` summation bound for the enlarged moduli
(`hm`).
-/

namespace Work.FIArea4

open Finset
open scoped BigOperators

attribute [local instance] Classical.propDecidable

noncomputable section

/-- **Case A of the §13 assembly** (`P ≤ 1`): Proposition 12.1 applied directly at `D`. -/
theorem p13_caseA (ε : ℝ) (hε : 0 < ε) (C121 : ℝ) (hC121 : 0 < C121)
    (h121 : ∀ (D R S : ℕ) (α : ℕ → ℕ → ℂ), 1 ≤ D → 1 ≤ R → 1 ≤ S →
        (∀ r s, α r s ≠ 0 → Nat.Coprime r (2 * s)) →
        Work.FIPlan.Vvar R S D α ≤ C121 * p14T12 D R S (ε / 8) * p14Ener R S α)
    (KE : ℝ) (hKE : 0 < KE)
    (hEner : ∀ (R S : ℕ) (α : ℕ → ℕ → ℂ), 1 ≤ R → 1 ≤ S →
        p14Ener R S α ≤ KE * (((R:ℝ)*(S:ℝ))^(ε/4)) * p14L2 R S α)
    (Knl : ℝ) (hKnl : 0 < Knl)
    (hnl : ∀ (D R S : ℕ) (P : ℝ), 1 ≤ D → 1 ≤ R → 1 ≤ S → P = p13P D R S → P ≤ 1 →
        p14T12 D R S (ε/8) ≤ Knl * p14T13 D R S ε * (((R:ℝ) * (S:ℝ)) ^ (ε/2)))
    (Kaf : ℝ) (hKaf : 0 < Kaf)
    (haf : ∀ (D R S : ℕ), 1 ≤ D → 1 ≤ R → 1 ≤ S → 1 < p13P D R S →
        Real.log (4 * p13P D R S) ≤ Kaf * (((R:ℝ)*(S:ℝ))^(ε/8)) ∧
        (∀ x : ℝ, 1 ≤ x → x ≤ 32 * (((R:ℝ)*(S:ℝ))^(3/4)) →
            Real.log x ≤ Kaf * (((R:ℝ)*(S:ℝ))^(ε/8))))
    (Kt : ℝ) (hKt : 0 < Kt)
    (htau : ∀ n : ℕ, 1 ≤ n → ((n.divisors.card : ℕ) : ℝ) ≤ Kt * (n : ℝ) ^ (ε / 4))
    (Kns : ℝ) (hKns : 0 < Kns)
    (cp : ℝ) (hcp : 0 < cp)
    (Kpd : ℝ) (hKpd : 0 < Kpd) :
    ∃ C : ℝ, 0 < C ∧ ∀ (D R S : ℕ) (α : ℕ → ℕ → ℂ), 1 ≤ D → 1 ≤ R → 1 ≤ S →
        (∀ r s, α r s ≠ 0 → Nat.Coprime r (2 * s)) → p13P D R S ≤ 1 →
        Work.FIPlan.Vvar R S D α ≤ C * p14T13 D R S ε * (((R:ℝ)*(S:ℝ))^ε) * p14L2 R S α := by
  have h8pow : (0:ℝ) < (8:ℝ)^(ε/4) := Real.rpow_pos_of_pos (by norm_num) _
  have hCpos : 0 < C121*KE*Knl
      + (24*Kns*C121*KE*Kaf/cp + (2*Kaf*Kpd/cp)*(1 + 8*Kt*8^(ε/4))) := by positivity
  refine ⟨C121*KE*Knl
      + (24*Kns*C121*KE*Kaf/cp + (2*Kaf*Kpd/cp)*(1 + 8*Kt*8^(ε/4))), hCpos, ?_⟩
  intro D R S α hD hR hS hsup hcase
  have hX1 : (1:ℝ) ≤ ((R:ℝ)*(S:ℝ)) := by
    have hR1 : (1:ℝ) ≤ (R:ℝ) := by exact_mod_cast hR
    have hS1 : (1:ℝ) ≤ (S:ℝ) := by exact_mod_cast hS
    nlinarith
  have hX0 : (0:ℝ) < ((R:ℝ)*(S:ℝ)) := lt_of_lt_of_le zero_lt_one hX1
  have hL2nn : (0:ℝ) ≤ p14L2 R S α := by
    rw [p14L2]
    exact Finset.sum_nonneg (fun r _ => Finset.sum_nonneg (fun s _ => Complex.normSq_nonneg _))
  have h1 := h121 D R S α hD hR hS hsup
  have h2 := hEner R S α hR hS
  have h3 := hnl D R S (p13P D R S) hD hR hS rfl hcase
  have hT12nn : (0:ℝ) ≤ p14T12 D R S (ε/8) := le_of_lt (p14T12_pos D R S hD hR hS (ε/8))
  have hT13nn : (0:ℝ) ≤ p14T13 D R S ε := le_of_lt (p14T13_pos D R S hD hR hS ε)
  have hXenn : (0:ℝ) ≤ ((R:ℝ)*(S:ℝ))^ε := le_of_lt (Real.rpow_pos_of_pos hX0 ε)
  have h2' : C121 * p14T12 D R S (ε/8) * p14Ener R S α
      ≤ C121 * p14T12 D R S (ε/8) * (KE * ((R:ℝ)*(S:ℝ))^(ε/4) * p14L2 R S α) := by
    apply mul_le_mul_of_nonneg_left h2
    exact mul_nonneg (le_of_lt hC121) hT12nn
  have hKEodd : (0:ℝ) ≤ KE * ((R:ℝ)*(S:ℝ))^(ε/4) * p14L2 R S α := by positivity
  have h3' : C121 * p14T12 D R S (ε/8) * (KE * ((R:ℝ)*(S:ℝ))^(ε/4) * p14L2 R S α)
      ≤ C121 * (Knl * p14T13 D R S ε * ((R:ℝ)*(S:ℝ))^(ε/2))
          * (KE * ((R:ℝ)*(S:ℝ))^(ε/4) * p14L2 R S α) := by
    apply mul_le_mul_of_nonneg_right _ hKEodd
    apply mul_le_mul_of_nonneg_left _ (le_of_lt hC121)
    exact h3
  have h4 : C121 * (Knl * p14T13 D R S ε * ((R:ℝ)*(S:ℝ))^(ε/2))
        * (KE * ((R:ℝ)*(S:ℝ))^(ε/4) * p14L2 R S α)
      = (C121*KE*Knl) * p14T13 D R S ε
          * (((R:ℝ)*(S:ℝ))^(ε/4) * ((R:ℝ)*(S:ℝ))^(ε/2)) * p14L2 R S α := by ring
  have h5 : ((R:ℝ)*(S:ℝ))^(ε/4) * ((R:ℝ)*(S:ℝ))^(ε/2)
      = ((R:ℝ)*(S:ℝ))^(ε/4 + ε/2) := by rw [Real.rpow_add hX0]
  have h6 : ((R:ℝ)*(S:ℝ))^(ε/4 + ε/2) ≤ ((R:ℝ)*(S:ℝ))^ε :=
    Real.rpow_le_rpow_of_exponent_le hX1 (by linarith)
  have hkey : (C121*KE*Knl) * p14T13 D R S ε
        * (((R:ℝ)*(S:ℝ))^(ε/4) * ((R:ℝ)*(S:ℝ))^(ε/2)) * p14L2 R S α
      ≤ (C121*KE*Knl) * p14T13 D R S ε * ((R:ℝ)*(S:ℝ))^ε * p14L2 R S α := by
    rw [h5]
    have hA : (0:ℝ) ≤ (C121*KE*Knl) * p14T13 D R S ε :=
      mul_nonneg (mul_nonneg (mul_nonneg (le_of_lt hC121) (le_of_lt hKE)) (le_of_lt hKnl)) hT13nn
    exact mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_left h6 hA) hL2nn
  have hCmono : (C121*KE*Knl)
      ≤ C121*KE*Knl + (24*Kns*C121*KE*Kaf/cp + (2*Kaf*Kpd/cp)*(1 + 8*Kt*8^(ε/4))) := by
    have h1 : (0:ℝ) ≤ 24*Kns*C121*KE*Kaf/cp := by positivity
    have h2 : (0:ℝ) ≤ (2*Kaf*Kpd/cp)*(1 + 8*Kt*8^(ε/4)) := by positivity
    linarith
  have hrest : (0:ℝ) ≤ p14T13 D R S ε * (((R:ℝ)*(S:ℝ))^ε * p14L2 R S α) :=
    mul_nonneg hT13nn (mul_nonneg hXenn hL2nn)
  have hfin : (C121*KE*Knl) * p14T13 D R S ε * ((R:ℝ)*(S:ℝ))^ε * p14L2 R S α
      ≤ (C121*KE*Knl + (24*Kns*C121*KE*Kaf/cp + (2*Kaf*Kpd/cp)*(1 + 8*Kt*8^(ε/4))))
        * p14T13 D R S ε * ((R:ℝ)*(S:ℝ))^ε * p14L2 R S α := by
    calc (C121*KE*Knl) * p14T13 D R S ε * ((R:ℝ)*(S:ℝ))^ε * p14L2 R S α
        = (C121*KE*Knl) * (p14T13 D R S ε * (((R:ℝ)*(S:ℝ))^ε * p14L2 R S α)) := by ring
      _ ≤ (C121*KE*Knl + (24*Kns*C121*KE*Kaf/cp + (2*Kaf*Kpd/cp)*(1 + 8*Kt*8^(ε/4))))
            * (p14T13 D R S ε * (((R:ℝ)*(S:ℝ))^ε * p14L2 R S α)) :=
          mul_le_mul_of_nonneg_right hCmono hrest
      _ = _ := by ring
  calc Work.FIPlan.Vvar R S D α
      ≤ C121 * p14T12 D R S (ε/8) * p14Ener R S α := h1
    _ ≤ C121 * p14T12 D R S (ε/8) * (KE * ((R:ℝ)*(S:ℝ))^(ε/4) * p14L2 R S α) := h2'
    _ ≤ C121 * (Knl * p14T13 D R S ε * ((R:ℝ)*(S:ℝ))^(ε/2))
          * (KE * ((R:ℝ)*(S:ℝ))^(ε/4) * p14L2 R S α) := h3'
    _ = (C121*KE*Knl) * p14T13 D R S ε
          * (((R:ℝ)*(S:ℝ))^(ε/4) * ((R:ℝ)*(S:ℝ))^(ε/2)) * p14L2 R S α := h4
    _ ≤ (C121*KE*Knl) * p14T13 D R S ε * ((R:ℝ)*(S:ℝ))^ε * p14L2 R S α := hkey
    _ ≤ (C121*KE*Knl + (24*Kns*C121*KE*Kaf/cp + (2*Kaf*Kpd/cp)*(1 + 8*Kt*8^(ε/4))))
        * p14T13 D R S ε * ((R:ℝ)*(S:ℝ))^ε * p14L2 R S α := hfin

/-- **Combination**: the two cases `P ≤ 1` and `1 < P` give the conclusion. -/
theorem p13_combine (ε : ℝ)
    (hA : ∃ C : ℝ, 0 < C ∧ ∀ (D R S : ℕ) (α : ℕ → ℕ → ℂ), 1 ≤ D → 1 ≤ R → 1 ≤ S →
        (∀ r s, α r s ≠ 0 → Nat.Coprime r (2 * s)) → p13P D R S ≤ 1 →
        Work.FIPlan.Vvar R S D α ≤ C * p14T13 D R S ε * (((R:ℝ)*(S:ℝ))^ε) * p14L2 R S α)
    (hB : ∃ C : ℝ, 0 < C ∧ ∀ (D R S : ℕ) (α : ℕ → ℕ → ℂ), 1 ≤ D → 1 ≤ R → 1 ≤ S →
        (∀ r s, α r s ≠ 0 → Nat.Coprime r (2 * s)) → 1 < p13P D R S →
        Work.FIPlan.Vvar R S D α ≤ C * p14T13 D R S ε * (((R:ℝ)*(S:ℝ))^ε) * p14L2 R S α) :
    ∃ C : ℝ, 0 < C ∧ ∀ (D R S : ℕ) (α : ℕ → ℕ → ℂ), 1 ≤ D → 1 ≤ R → 1 ≤ S →
        (∀ r s, α r s ≠ 0 → Nat.Coprime r (2 * s)) →
        Work.FIPlan.Vvar R S D α ≤ C * p14T13 D R S ε * (((R:ℝ)*(S:ℝ))^ε) * p14L2 R S α := by
  obtain ⟨CA, hCA, hA'⟩ := hA
  obtain ⟨CB, hCB, hB'⟩ := hB
  refine ⟨max CA CB, lt_max_of_lt_left hCA, fun D R S α hD hR hS hsup => ?_⟩
  by_cases h : p13P D R S ≤ 1
  · exact le_trans (hA' D R S α hD hR hS hsup h)
      (mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_right
        (mul_le_mul_of_nonneg_right (le_max_left _ _) (le_of_lt (p14T13_pos D R S hD hR hS ε)))
        (le_of_lt (Real.rpow_pos_of_pos (by
          have hR1 : (1:ℝ) ≤ (R:ℝ) := by exact_mod_cast hR
          have hS1 : (1:ℝ) ≤ (S:ℝ) := by exact_mod_cast hS
          nlinarith) ε)))
        (by rw [p14L2]; exact Finset.sum_nonneg (fun r _ => Finset.sum_nonneg (fun s _ => Complex.normSq_nonneg _))))
  · exact le_trans (hB' D R S α hD hR hS hsup (not_le.mp h))
      (mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_right
        (mul_le_mul_of_nonneg_right (le_max_right _ _) (le_of_lt (p14T13_pos D R S hD hR hS ε)))
        (le_of_lt (Real.rpow_pos_of_pos (by
          have hR1 : (1:ℝ) ≤ (R:ℝ) := by exact_mod_cast hR
          have hS1 : (1:ℝ) ≤ (S:ℝ) := by exact_mod_cast hS
          nlinarith) ε)))
        (by rw [p14L2]; exact Finset.sum_nonneg (fun r _ => Finset.sum_nonneg (fun s _ => Complex.normSq_nonneg _))))

end

end Work.FIArea4
