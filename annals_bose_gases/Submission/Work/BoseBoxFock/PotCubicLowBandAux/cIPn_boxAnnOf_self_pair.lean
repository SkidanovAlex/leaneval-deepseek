import Mathlib.Analysis.CStarAlgebra.Classes
import Mathlib.Analysis.Normed.Lp.MeasurableSpace
import Mathlib.MeasureTheory.Function.L1Space.Integrable
import Mathlib.MeasureTheory.Measure.Haar.OfBasis
import Submission.Work.BoseBoxFock.PotCubicLowBandAux.selfPairG
import Submission.Work.BoseBoxFock.PotCubicLowBandAux.slotRankOneG
-- PORT435-BEGIN (v4.35 isDefEq respectTransparency compat)
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- PORT435-END

namespace Work.BoseBoxFock.PotCubicLowBandAux

/-- The strategy of `cIPn_boxAnnOf_self_pair`: `boxCreOf` is the formal adjoint of `boxAnnOf`
(`cIPn_boxAnnOf_eqInt`), and `boxCreOf ∘ boxAnnOf = Σ_j boxSlotOf` on symmetric functions
(`boxCreOf_boxAnnOf_slot`); the rank-one slot sum then unfolds to
`boxSlotSum e (rankOnePair u v)` (`boxSlotSum_rankOnePairG`).

Everything is unconditional once `Θ` and `boxAnnOf e v d Θ` are in the weak bundle `WRegG`
(measurable, everywhere bounded, supported in a box of finite measure). -/
theorem cIPn_boxAnnOf_self_pair {m d : ℕ} [NeZero m] {ℓ : ℝ}
    {e : Fin m → EuclideanSpace ℝ (Fin 3) → ℂ}
    (hmeas : ∀ l, Measurable (e l)) (hbdd : ∀ l, ∃ C : ℝ, ∀ x, ‖e l x‖ ≤ C)
    (hsupp : ∀ l, Function.support (e l) ⊆ Work.BoseK15.corpusBox.boxL ℓ)
    (hMemLp : ∀ l, MeasureTheory.MemLp (e l) ⊤)
    (u v : Fin m → ℝ) {Θ : Work.BoseDict.Xn (d + 1) → ℂ}
    (hΘm : Measurable Θ) {CΘ : ℝ} (hΘb : ∀ x, ‖Θ x‖ ≤ CΘ)
    (hΘsupp : Function.support Θ ⊆ Work.MB.boxPow (d + 1) ℓ)
    (hΘsym : ∀ (σ : Equiv.Perm (Fin (d + 1))) (x : Work.BoseDict.Xn (d + 1)),
      Θ (x ∘ σ) = Θ x) :
    Work.BoseDict.cIPn d (Work.BoseDict.boxAnnOf e u d Θ)
        (Work.BoseDict.boxAnnOf e v d Θ)
      = Work.BoseDict.cIPn (d + 1) Θ
          (Work.BoseDict.boxSlotSum e (Work.BoseBoxFock.rankOnePair u v) Θ) := by
  classical
  -- `Θ` and `boxAnnOf e v d Θ` are weakly regular, hence integrable.
  have hΘW : Work.BoseBoxFock.WRegG ℓ Θ := ⟨hΘm, ⟨CΘ, hΘb⟩, hΘsupp⟩
  have hY : Work.BoseBoxFock.WRegG ℓ (Work.BoseDict.boxAnnOf e v d Θ) :=
    Work.BoseBoxFock.boxAnnOf_wregG hmeas hbdd hsupp v hΘW
  -- the Fubini integrability input of the adjointness identity
  have hInt :=
    Work.BoseBoxFock.integrable_etaOf_conj_cons_mul_wregG hmeas hbdd hsupp u hΘW hY
  -- adjointness, then the dictionary `boxCreOf ∘ boxAnnOf = Σ_j boxSlotOf`
  rw [Work.BoseDict.cIPn_boxAnnOf_eqInt (d := d) hMemLp hsupp u Θ hΘW.integrable hΘsym
    (Work.BoseDict.boxAnnOf e v d Θ) hY.integrable hInt]
  -- the rank-one slot sum is the first-quantised rank-one operator `|η_u⟩⟨η_v|`
  rw [Work.BoseDict.boxCreOf_boxAnnOf_slot u v Θ hΘsym,
    boxSlotSum_rankOnePairG hmeas hbdd hsupp u v Θ hΘm ⟨CΘ, hΘb⟩]

end Work.BoseBoxFock.PotCubicLowBandAux
