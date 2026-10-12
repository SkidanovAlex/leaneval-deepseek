import Mathlib.Analysis.CStarAlgebra.Classes
import Mathlib.Analysis.Normed.Lp.MeasurableSpace
import Mathlib.MeasureTheory.Integral.Bochner.Basic
import Mathlib.MeasureTheory.Measure.Haar.OfBasis
import Submission.Work.BoseBoxFock.boxSlotSum_comp_pairCoord
import Submission.Work.BoseBoxFock.slotFactsInst
-- PORT435-BEGIN (v4.35 isDefEq respectTransparency compat)
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- PORT435-END

/-!
# `Work.BoseBoxFock.slotFactsComp` — the `SlotFacts` instances of the pair shapes

Besides the one-body slot sum (`SlotFacts.boxSlotSumFacts`) and the identity (`SlotFacts.id`), the
box twin `AVslot` of `H2ndF` is built from **compositions** of two slot sums (the pair rows
`|w₁⟩⟨v₁| ∘ |w₂⟩⟨v₂|`, the `L₀`/`L₁`-linear rows, and the `bW2slot` rows).  This module records

* the closure of `SlotFacts` under subtraction and under transport along an operator equality,
* `SlotFacts.comp_slotSum` — the composition of two one-body slot sums, whose sector splitting is
  `boxSlotSum_comp_sector_split` and whose pointwise decoupling is `boxSlotSum_comp_pairCoord`.

Everything here is `sorry`-free.
-/

noncomputable section

open MeasureTheory

namespace Work.BoseBoxFock

local notation "Ω" => EuclideanSpace ℝ (Fin 3)

open Work.BoseDict

set_option autoImplicit false
set_option linter.unusedVariables false
set_option maxHeartbeats 4000000

variable {m n : ℕ}

/-- Transport of `SlotFacts` along an equality of operators. -/
theorem SlotFacts.congr {e : Fin m → Ω → ℂ} {Φc : Xn n → ℂ}
    {Op Op' : (Xn n → ℂ) → (Xn n → ℂ)}
    {OpS OpS' : (S : Finset (Fin n)) → (({i // i ∈ S} → Ω) → ℂ) → (({i // i ∈ S} → Ω) → ℂ)}
    (hOp : Op = Op') (hS : OpS = OpS') (h : SlotFacts e Φc Op OpS) :
    SlotFacts e Φc Op' OpS' := by
  rw [← hOp, ← hS]
  exact h

/-- **The subtraction closure.** -/
theorem SlotFacts.sub {e : Fin m → Ω → ℂ} {Φc : Xn n → ℂ}
    (he : ∀ l, Continuous (e l)) (hec : ∀ l, HasCompactSupport (e l))
    (hΦcont : Continuous Φc) (hΦc : HasCompactSupport Φc)
    {Op1 Op2 : (Xn n → ℂ) → (Xn n → ℂ)}
    {OpS1 OpS2 : (S : Finset (Fin n)) → (({i // i ∈ S} → Ω) → ℂ)
      → (({i // i ∈ S} → Ω) → ℂ)}
    (h1 : SlotFacts e Φc Op1 OpS1) (h2 : SlotFacts e Φc Op2 OpS2) :
    SlotFacts e Φc (Op1 - Op2) (fun S X => OpS1 S X - OpS2 S X) := by
  have hΦ : SlotGood Φc := ⟨hΦcont.measurable, hΦcont.bounded_above_of_compact_support hΦc⟩
  have hsec := fun S => slotExact_slotGood he hec S Φc hΦcont hΦc
  refine ⟨?_, ?_, ?_⟩
  · intro X hX
    have h : (Op1 - Op2) X = Op1 X - Op2 X := rfl
    rw [h]
    exact (h1.good X hX).sub (h2.good X hX)
  · intro S u y
    show Op1 (slotExact e S Φc) (pairCoord S u y) - Op2 (slotExact e S Φc) (pairCoord S u y)
      = OpS1 S (fun u' => slotExact e S Φc (pairCoord S u' y)) u
        - OpS2 S (fun u' => slotExact e S Φc (pairCoord S u' y)) u
    rw [h1.slice S u y, h2.slice S u y]
  · have hi1 : MeasureTheory.Integrable (fun x : Xn n => star (Φc x) * Op1 Φc x) :=
      integrable_star_mul_of_compact hΦc hΦ (h1.good Φc hΦ)
    have hi2 : MeasureTheory.Integrable (fun x : Xn n => star (Φc x) * Op2 Φc x) :=
      integrable_star_mul_of_compact hΦc hΦ (h2.good Φc hΦ)
    have hj1 : ∀ S : Finset (Fin n), MeasureTheory.Integrable (fun x : Xn n =>
        star (slotExact e S Φc x) * Op1 (slotExact e S Φc) x) := fun S =>
      integrable_star_mul_of_compact (hsec S).2 (hsec S).1 (h1.good _ (hsec S).1)
    have hj2 : ∀ S : Finset (Fin n), MeasureTheory.Integrable (fun x : Xn n =>
        star (slotExact e S Φc x) * Op2 (slotExact e S Φc) x) := fun S =>
      integrable_star_mul_of_compact (hsec S).2 (hsec S).1 (h2.good _ (hsec S).1)
    have hpt1 : (fun x : Xn n => star (Φc x) * (Op1 - Op2) Φc x)
        = fun x : Xn n => star (Φc x) * Op1 Φc x - star (Φc x) * Op2 Φc x := by
      funext x
      simp only [Pi.sub_apply, mul_sub]
    have hpt2 : ∀ S : Finset (Fin n),
        (fun x : Xn n => star (slotExact e S Φc x) * (Op1 - Op2) (slotExact e S Φc) x)
          = fun x : Xn n => star (slotExact e S Φc x) * Op1 (slotExact e S Φc) x
              - star (slotExact e S Φc x) * Op2 (slotExact e S Φc) x := by
      intro S
      funext x
      simp only [Pi.sub_apply, mul_sub]
    calc (∫ x : Xn n, star (Φc x) * (Op1 - Op2) Φc x).re
        = (∫ x : Xn n, (star (Φc x) * Op1 Φc x - star (Φc x) * Op2 Φc x)).re := by
          rw [hpt1]
      _ = ((∫ x : Xn n, star (Φc x) * Op1 Φc x)
            - (∫ x : Xn n, star (Φc x) * Op2 Φc x)).re := by
          rw [MeasureTheory.integral_sub hi1 hi2]
      _ = (∫ x : Xn n, star (Φc x) * Op1 Φc x).re
            - (∫ x : Xn n, star (Φc x) * Op2 Φc x).re := Complex.sub_re _ _
      _ = (∑ S : Finset (Fin n),
              (∫ x : Xn n, star (slotExact e S Φc x) * Op1 (slotExact e S Φc) x).re)
            - ∑ S : Finset (Fin n),
              (∫ x : Xn n, star (slotExact e S Φc x) * Op2 (slotExact e S Φc) x).re := by
          rw [h1.split, h2.split]
      _ = ∑ S : Finset (Fin n),
              ((∫ x : Xn n, star (slotExact e S Φc x) * Op1 (slotExact e S Φc) x).re
                - (∫ x : Xn n, star (slotExact e S Φc x) * Op2 (slotExact e S Φc) x).re) :=
          (Finset.sum_sub_distrib _ _).symm
      _ = ∑ S : Finset (Fin n),
              (∫ x : Xn n, star (slotExact e S Φc x) * (Op1 - Op2) (slotExact e S Φc) x).re := by
          refine Finset.sum_congr rfl (fun S _ => ?_)
          rw [hpt2 S, MeasureTheory.integral_sub (hj1 S) (hj2 S), Complex.sub_re]

/-- **The composition of two one-body slot sums.**  Its sector splitting is
`boxSlotSum_comp_sector_split` and its pointwise decoupling `boxSlotSum_comp_pairCoord`. -/
theorem SlotFacts.comp_slotSum {e : Fin m → Ω → ℂ} (he : ∀ l, Continuous (e l))
    (hec : ∀ l, HasCompactSupport (e l))
    (horth : ∀ l l', (∫ z : Ω, star (e l z) * e l' z) = (if l = l' then (1 : ℂ) else 0))
    (hint : ∀ l l', MeasureTheory.Integrable (fun z : Ω => star (e l z) * e l' z))
    {Φc : Xn n → ℂ} (hΦcont : Continuous Φc) (hΦc : HasCompactSupport Φc)
    (T₁ T₂ : (Fin m → ℝ) →ₗ[ℝ] (Fin m → ℝ)) :
    SlotFacts e Φc
      (fun Θ : Xn n → ℂ => Work.BoseDict.boxSlotSum e T₁ (Work.BoseDict.boxSlotSum e T₂ Θ))
      (fun S X => slotSumSub e T₁ S (slotSumSub e T₂ S X)) :=
  ⟨RowGood.comp ((SlotFacts.boxSlotSumFacts he hec horth hint hΦcont hΦc T₁).good)
      ((SlotFacts.boxSlotSumFacts he hec horth hint hΦcont hΦc T₂).good),
    (fun S u y => boxSlotSum_comp_pairCoord e T₁ T₂ S Φc he hec horth hint hΦcont hΦc u y),
    (by
      have h := congrArg Complex.re
        (boxSlotSum_comp_sector_split e T₁ T₂ he hec horth hint Φc hΦcont hΦc)
      have hsum : (∑ S : Finset (Fin n),
            ∫ x : Xn n, star (slotExact e S Φc x)
              * Work.BoseDict.boxSlotSum e T₁
                  (Work.BoseDict.boxSlotSum e T₂ (slotExact e S Φc)) x).re
          = ∑ S : Finset (Fin n),
            (∫ x : Xn n, star (slotExact e S Φc x)
              * Work.BoseDict.boxSlotSum e T₁
                  (Work.BoseDict.boxSlotSum e T₂ (slotExact e S Φc)) x).re := by
        simp
      exact h.trans hsum)⟩

end Work.BoseBoxFock
