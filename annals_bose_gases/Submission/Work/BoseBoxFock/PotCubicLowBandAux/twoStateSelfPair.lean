import Mathlib.Analysis.CStarAlgebra.Classes
import Mathlib.Analysis.Normed.Lp.MeasurableSpace
import Mathlib.MeasureTheory.Function.L1Space.Integrable
import Mathlib.MeasureTheory.Measure.Haar.OfBasis
import Submission.Work.BoseBoxFock.PotCubicLowBandAux.cIPn_boxAnnOf_self_pair
-- PORT435-BEGIN (v4.35 isDefEq respectTransparency compat)
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- PORT435-END

namespace Work.BoseBoxFock.PotCubicLowBandAux

theorem twoStateSelfPair {m d : ℕ} [NeZero m] {ℓ : ℝ} {e : Fin m → EuclideanSpace ℝ (Fin 3) → ℂ} (hmeas : ∀ l, Measurable (e l)) (hbdd : ∀ l, ∃ C : ℝ, ∀ x, ‖e l x‖ ≤ C) (hsupp : ∀ l, Function.support (e l) ⊆ Work.BoseK15.corpusBox.boxL ℓ) (hMemLp : ∀ l, MeasureTheory.MemLp (e l) ⊤) (u v : Fin m → ℝ) {Θ Φ : Work.BoseDict.Xn (d + 1) → ℂ} (hΘm : Measurable Θ) {CΘ : ℝ} (hΘb : ∀ x, ‖Θ x‖ ≤ CΘ) (hΘsupp : Function.support Θ ⊆ Work.MB.boxPow (d + 1) ℓ) (hΘsym : ∀ (σ : Equiv.Perm (Fin (d + 1))) (x : Work.BoseDict.Xn (d + 1)), Θ (x ∘ σ) = Θ x) (hΦm : Measurable Φ) {CΦ : ℝ} (hΦb : ∀ x, ‖Φ x‖ ≤ CΦ) (hΦsupp : Function.support Φ ⊆ Work.MB.boxPow (d + 1) ℓ) (hΦsym : ∀ (σ : Equiv.Perm (Fin (d + 1))) (x : Work.BoseDict.Xn (d + 1)), Φ (x ∘ σ) = Φ x) : Work.BoseDict.cIPn d (Work.BoseDict.boxAnnOf e u d Θ) (Work.BoseDict.boxAnnOf e v d Φ) = Work.BoseDict.cIPn (d + 1) Θ (Work.BoseDict.boxSlotSum e (Work.BoseBoxFock.rankOnePair u v) Φ) := by
  classical
  -- `Θ` and `Φ` (and hence `boxAnnOf e v d Φ`) are weakly regular, hence integrable.
  have hΘW : Work.BoseBoxFock.WRegG ℓ Θ := ⟨hΘm, ⟨CΘ, hΘb⟩, hΘsupp⟩
  have hΦW : Work.BoseBoxFock.WRegG ℓ Φ := ⟨hΦm, ⟨CΦ, hΦb⟩, hΦsupp⟩
  have hY : Work.BoseBoxFock.WRegG ℓ (Work.BoseDict.boxAnnOf e v d Φ) :=
    Work.BoseBoxFock.boxAnnOf_wregG hmeas hbdd hsupp v hΦW
  -- the Fubini integrability input of the adjointness identity, with the state `Θ` on the bra side
  have hInt :=
    Work.BoseBoxFock.integrable_etaOf_conj_cons_mul_wregG hmeas hbdd hsupp u hΘW hY
  -- adjointness (`Θ` symmetric is what the change of variables needs), then the dictionary
  -- `boxCreOf ∘ boxAnnOf = Σ_j boxSlotOf` applied to the symmetric state `Φ`
  rw [Work.BoseDict.cIPn_boxAnnOf_eqInt (d := d) hMemLp hsupp u Θ hΘW.integrable hΘsym
    (Work.BoseDict.boxAnnOf e v d Φ) hY.integrable hInt,
    Work.BoseDict.boxCreOf_boxAnnOf_slot u v Φ hΦsym,
    boxSlotSum_rankOnePairG hmeas hbdd hsupp u v Φ hΦm ⟨CΦ, hΦb⟩]

end Work.BoseBoxFock.PotCubicLowBandAux
