import Mathlib.Analysis.CStarAlgebra.Classes
import Mathlib.Analysis.Normed.Lp.MeasurableSpace
import Mathlib.MeasureTheory.Integral.Bochner.Basic
import Mathlib.MeasureTheory.Measure.Haar.OfBasis
import Submission.Work.BoseBoxFock.slotFactsComp
import Submission.Work.MB.SlotSumSplitAux
-- PORT435-BEGIN (v4.35 isDefEq respectTransparency compat)
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- PORT435-END

/-!
# `Work.MB.boxSlotSum_comp_sector_split_ae` — the sector split for a *composition*

This is the measurable/bounded ("weak") twin of
`Work.BoseBoxFock.boxSlotSum_comp_sector_split`, in the same way that
`Work.MB.slotSum_sector_split_ae` is the weak twin of `Work.BoseBoxFock.slotSum_sector_split`.

The strong version assumes the modes `e l` are `Continuous` with `HasCompactSupport` and the state
`Φ` is continuous with compact support; those hypotheses are unsatisfiable at the honest modes of
the box ↔ model bridge (`FINDING_continuous_hypotheses_UNSATISFIABLE.md`).  Here the modes are
measurable, everywhere bounded and supported in the corpus box `boxL ℓ`, while the state is
measurable, everywhere bounded and supported in `boxPow n ℓ`.

The identity proved is

    ∫ star Φ · boxSlotSum e T₁ (boxSlotSum e T₂ Φ)
      = ∑_S ∫ star (slotExact e S Φ) · boxSlotSum e T₁ (boxSlotSum e T₂ (slotExact e S Φ))

for the **composition** of the two first-quantised slot sums, which is what the box ↔ model bridge
needs when two one-body rows are applied in succession.

The proof is the script of `Work.MB.slotSum_sector_split_ae` with the single slot sum
`B = boxSlotSum e T` replaced by the composite `B = boxSlotSum e T₁ ∘ boxSlotSum e T₂`.  Only three
facts about `B` are used, and each holds for the composite because it holds for each factor:

* `B` is linear on the sector decomposition of `Φ` (linearity of `boxSlotSum` in the state,
  `Work.MB.boxSlotSum_bdd`, applied twice);
* `B` commutes with every one-slot projection `slotProj1 e i`
  (`Work.MB.boxSlotSum_slotProj1_bdd`, applied twice);
* `B` kills the zero state (`Work.MB.boxSlotSum_zero_weak`, applied twice).

The remaining ingredients are the weak sector algebra of `Submission/Work/MB/SlotSumSplitAux.lean`:
`Work.MB.slotExact_mb_weak`, `Work.MB.slotProj1_slotExact_bdd`,
`Work.MB.slotExact_eq_self_of_slotProj1`, `Work.MB.slotExact_adjoint_bdd` and
`Work.MB.integrable_star_mul_of_support_boxPow`.
-/

namespace Work.MB

open MeasureTheory

set_option maxHeartbeats 1600000

theorem boxSlotSum_comp_sector_split_ae {m n : ℕ} {ℓ : ℝ}
    {e : Fin m → EuclideanSpace ℝ (Fin 3) → ℂ}
    (hmeas : ∀ l, Measurable (e l)) (hbdE : ∀ l, ∃ C, ∀ x, ‖e l x‖ ≤ C)
    (hsupp : ∀ l, Function.support (e l) ⊆ Work.BoseK15.corpusBox.boxL ℓ)
    (horth : ∀ l l', (∫ z : EuclideanSpace ℝ (Fin 3), star (e l z) * e l' z)
      = (if l = l' then (1 : ℂ) else 0))
    (hint : ∀ l l', MeasureTheory.Integrable
      (fun z : EuclideanSpace ℝ (Fin 3) => star (e l z) * e l' z))
    (T₁ T₂ : (Fin m → ℝ) →ₗ[ℝ] (Fin m → ℝ))
    (Φ : (Fin n → EuclideanSpace ℝ (Fin 3)) → ℂ)
    (hΦm : Measurable Φ) (hΦb : ∃ C, ∀ x, ‖Φ x‖ ≤ C)
    (hΦsupp : Function.support Φ ⊆ Work.MB.boxPow n ℓ) :
    ∫ x, star (Φ x)
        * Work.BoseDict.boxSlotSum e T₁ (Work.BoseDict.boxSlotSum e T₂ Φ) x
      = ∑ S : Finset (Fin n),
          ∫ x, star (Work.BoseBoxFock.slotExact e S Φ x)
            * Work.BoseDict.boxSlotSum e T₁
                (Work.BoseDict.boxSlotSum e T₂ (Work.BoseBoxFock.slotExact e S Φ)) x := by
  classical
  -- ## 0. Regularity of the sectors
  have hA : ∀ S : Finset (Fin n),
      Measurable (Work.BoseBoxFock.slotExact e S Φ) ∧
      (∃ C : ℝ, 0 ≤ C ∧ ∀ x, ‖Work.BoseBoxFock.slotExact e S Φ x‖ ≤ C) ∧
      (Function.support Φ ⊆ boxPow n ℓ →
        Function.support (Work.BoseBoxFock.slotExact e S Φ) ⊆ boxPow n ℓ) :=
    fun S => Work.MB.slotExact_mb_weak hmeas hbdE hsupp S hΦm hΦb
  have hAmeas : ∀ S : Finset (Fin n), Measurable (Work.BoseBoxFock.slotExact e S Φ) :=
    fun S => (hA S).1
  have hAbdd : ∀ S : Finset (Fin n),
      ∃ C : ℝ, 0 ≤ C ∧ ∀ x, ‖Work.BoseBoxFock.slotExact e S Φ x‖ ≤ C :=
    fun S => (hA S).2.1
  have hAbdd0 : ∀ S : Finset (Fin n), ∃ C, ∀ x, ‖Work.BoseBoxFock.slotExact e S Φ x‖ ≤ C :=
    fun S => (hAbdd S).imp (fun C hC => hC.2)
  have hAsupp : ∀ S : Finset (Fin n),
      Function.support (Work.BoseBoxFock.slotExact e S Φ) ⊆ boxPow n ℓ :=
    fun S => (hA S).2.2 hΦsupp
  -- ## 1. Regularity of the two layers of the composite
  have hB2m : ∀ S : Finset (Fin n),
      Measurable (Work.BoseDict.boxSlotSum e T₂ (Work.BoseBoxFock.slotExact e S Φ)) :=
    fun S => ((Work.MB.boxSlotSum_bdd hmeas hbdE hsupp T₂).2
      (Work.BoseBoxFock.slotExact e S Φ) (hAmeas S) (hAbdd0 S)).1
  have hB2b : ∀ S : Finset (Fin n), ∃ C : ℝ, 0 ≤ C ∧ ∀ x,
      ‖Work.BoseDict.boxSlotSum e T₂ (Work.BoseBoxFock.slotExact e S Φ) x‖ ≤ C :=
    fun S => ((Work.MB.boxSlotSum_bdd hmeas hbdE hsupp T₂).2
      (Work.BoseBoxFock.slotExact e S Φ) (hAmeas S) (hAbdd0 S)).2.1
  have hB2supp : ∀ S : Finset (Fin n),
      Function.support (Work.BoseDict.boxSlotSum e T₂ (Work.BoseBoxFock.slotExact e S Φ))
        ⊆ boxPow n ℓ :=
    fun S => ((Work.MB.boxSlotSum_bdd hmeas hbdE hsupp T₂).2
      (Work.BoseBoxFock.slotExact e S Φ) (hAmeas S) (hAbdd0 S)).2.2 (hAsupp S)
  have hB2d : ∀ S : Finset (Fin n), ∃ C, ∀ x,
      ‖Work.BoseDict.boxSlotSum e T₂ (Work.BoseBoxFock.slotExact e S Φ) x‖ ≤ C :=
    fun S => (hB2b S).imp (fun C hC => hC.2)
  have hC1m : ∀ S : Finset (Fin n), Measurable (Work.BoseDict.boxSlotSum e T₁
      (Work.BoseDict.boxSlotSum e T₂ (Work.BoseBoxFock.slotExact e S Φ))) :=
    fun S => ((Work.MB.boxSlotSum_bdd hmeas hbdE hsupp T₁).2
      (Work.BoseDict.boxSlotSum e T₂ (Work.BoseBoxFock.slotExact e S Φ))
      (hB2m S) (hB2d S)).1
  have hC1b : ∀ S : Finset (Fin n), ∃ C : ℝ, 0 ≤ C ∧ ∀ x,
      ‖Work.BoseDict.boxSlotSum e T₁
        (Work.BoseDict.boxSlotSum e T₂ (Work.BoseBoxFock.slotExact e S Φ)) x‖ ≤ C :=
    fun S => ((Work.MB.boxSlotSum_bdd hmeas hbdE hsupp T₁).2
      (Work.BoseDict.boxSlotSum e T₂ (Work.BoseBoxFock.slotExact e S Φ))
      (hB2m S) (hB2d S)).2.1
  have hC1supp : ∀ S : Finset (Fin n),
      Function.support (Work.BoseDict.boxSlotSum e T₁
        (Work.BoseDict.boxSlotSum e T₂ (Work.BoseBoxFock.slotExact e S Φ))) ⊆ boxPow n ℓ :=
    fun S => ((Work.MB.boxSlotSum_bdd hmeas hbdE hsupp T₁).2
      (Work.BoseDict.boxSlotSum e T₂ (Work.BoseBoxFock.slotExact e S Φ))
      (hB2m S) (hB2d S)).2.2 (hB2supp S)
  have hC1d : ∀ S : Finset (Fin n), ∃ C, ∀ x,
      ‖Work.BoseDict.boxSlotSum e T₁
        (Work.BoseDict.boxSlotSum e T₂ (Work.BoseBoxFock.slotExact e S Φ)) x‖ ≤ C :=
    fun S => (hC1b S).imp (fun C hC => hC.2)
  -- ## 2. The composite splits over the sectors
  have hsplit2 : Work.BoseDict.boxSlotSum e T₂ Φ
      = fun x => ∑ S ∈ Finset.univ,
          (1 : ℂ) • Work.BoseDict.boxSlotSum e T₂ (Work.BoseBoxFock.slotExact e S Φ) x := by
    have hres : Φ = fun x => ∑ S ∈ Finset.univ, (1 : ℂ) •
        Work.BoseBoxFock.slotExact e S Φ x := by
      funext x
      have h := congrFun (Work.BoseBoxFock.slotExact_sum_eq e Φ) x
      simpa using h.symm
    conv_lhs => rw [hres]
    rw [(Work.MB.boxSlotSum_bdd hmeas hbdE hsupp T₂).1 Finset.univ (fun _ => (1 : ℂ))
      (fun S => Work.BoseBoxFock.slotExact e S Φ) (fun S => hAmeas S) (fun S => hAbdd0 S)]
  have hBsplit : Work.BoseDict.boxSlotSum e T₁ (Work.BoseDict.boxSlotSum e T₂ Φ)
      = fun x => ∑ S ∈ Finset.univ,
          (1 : ℂ) • Work.BoseDict.boxSlotSum e T₁
            (Work.BoseDict.boxSlotSum e T₂ (Work.BoseBoxFock.slotExact e S Φ)) x := by
    rw [hsplit2]
    rw [(Work.MB.boxSlotSum_bdd hmeas hbdE hsupp T₁).1 Finset.univ (fun _ => (1 : ℂ))
      (fun S => Work.BoseDict.boxSlotSum e T₂ (Work.BoseBoxFock.slotExact e S Φ))
      (fun S => hB2m S) (fun S => hB2d S)]
  -- ## 3. Expand the left-hand side over the sectors
  have hLHS : (∫ x, star (Φ x)
        * Work.BoseDict.boxSlotSum e T₁ (Work.BoseDict.boxSlotSum e T₂ Φ) x)
      = ∑ S : Finset (Fin n),
          ∫ x, star (Φ x) * Work.BoseDict.boxSlotSum e T₁
            (Work.BoseDict.boxSlotSum e T₂ (Work.BoseBoxFock.slotExact e S Φ)) x := by
    have hpt : ∀ x, star (Φ x)
          * Work.BoseDict.boxSlotSum e T₁ (Work.BoseDict.boxSlotSum e T₂ Φ) x
        = ∑ S ∈ Finset.univ, star (Φ x) * Work.BoseDict.boxSlotSum e T₁
            (Work.BoseDict.boxSlotSum e T₂ (Work.BoseBoxFock.slotExact e S Φ)) x := by
      intro x
      rw [congrFun hBsplit x, Finset.mul_sum]
      exact Finset.sum_congr rfl fun S _ => by simp
    rw [show (∫ x, star (Φ x)
          * Work.BoseDict.boxSlotSum e T₁ (Work.BoseDict.boxSlotSum e T₂ Φ) x)
        = ∫ x, ∑ S ∈ Finset.univ, star (Φ x) * Work.BoseDict.boxSlotSum e T₁
            (Work.BoseDict.boxSlotSum e T₂ (Work.BoseBoxFock.slotExact e S Φ)) x from
      integral_congr_ae (Filter.Eventually.of_forall hpt)]
    rw [MeasureTheory.integral_finsetSum]
    intro S _
    exact Work.MB.integrable_star_mul_of_support_boxPow hΦm hΦb hΦsupp
      (hC1m S) (hC1d S) (hC1supp S)
  -- ## 4. Each sector contributes its own diagonal term
  have hdiag : ∀ S : Finset (Fin n),
      (∫ x, star (Φ x) * Work.BoseDict.boxSlotSum e T₁
          (Work.BoseDict.boxSlotSum e T₂ (Work.BoseBoxFock.slotExact e S Φ)) x)
        = ∫ x, star (Work.BoseBoxFock.slotExact e S Φ x)
            * Work.BoseDict.boxSlotSum e T₁
                (Work.BoseDict.boxSlotSum e T₂ (Work.BoseBoxFock.slotExact e S Φ)) x := by
    intro S
    -- the composite fixes its own sector: it commutes with every `slotProj1` and kills `0`
    have hfix : Work.BoseBoxFock.slotExact e S
        (Work.BoseDict.boxSlotSum e T₁
          (Work.BoseDict.boxSlotSum e T₂ (Work.BoseBoxFock.slotExact e S Φ)))
        = Work.BoseDict.boxSlotSum e T₁
            (Work.BoseDict.boxSlotSum e T₂ (Work.BoseBoxFock.slotExact e S Φ)) := by
      refine Work.MB.slotExact_eq_self_of_slotProj1 hmeas hbdE hsupp S
        (hC1m S) (hC1d S) ?_
      intro i
      rw [Work.MB.boxSlotSum_slotProj1_bdd hmeas hbdE hsupp horth hint T₁
            (hB2m S) (hB2d S) i,
          Work.MB.boxSlotSum_slotProj1_bdd hmeas hbdE hsupp horth hint T₂
            (hAmeas S) (hAbdd0 S) i,
          Work.MB.slotProj1_slotExact_bdd hmeas hbdE hsupp horth hint S i hΦm hΦb]
      by_cases hi : i ∈ S
      · rw [if_pos hi, if_pos hi]
      · rw [if_neg hi, if_neg hi, Work.MB.boxSlotSum_zero_weak, Work.MB.boxSlotSum_zero_weak]
    calc (∫ x, star (Φ x) * Work.BoseDict.boxSlotSum e T₁
            (Work.BoseDict.boxSlotSum e T₂ (Work.BoseBoxFock.slotExact e S Φ)) x)
        = ∫ x, star (Φ x) * Work.BoseBoxFock.slotExact e S
            (Work.BoseDict.boxSlotSum e T₁
              (Work.BoseDict.boxSlotSum e T₂ (Work.BoseBoxFock.slotExact e S Φ))) x := by
          rw [hfix]
      _ = ∫ x, star (Work.BoseBoxFock.slotExact e S Φ x)
            * Work.BoseDict.boxSlotSum e T₁
                (Work.BoseDict.boxSlotSum e T₂ (Work.BoseBoxFock.slotExact e S Φ)) x :=
          (Work.MB.slotExact_adjoint_bdd hmeas hbdE hsupp S hΦm hΦb hΦsupp
            (hC1m S) (hC1d S) (hC1supp S)).symm
  rw [hLHS]
  exact Finset.sum_congr rfl fun S _ => hdiag S

end Work.MB
