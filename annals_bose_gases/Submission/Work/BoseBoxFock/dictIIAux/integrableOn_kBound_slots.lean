import Mathlib.MeasureTheory.Integral.IntegrableOn
import Mathlib.Analysis.Normed.Lp.MeasurableSpace
import Mathlib.MeasureTheory.Measure.Haar.OfBasis
import Submission.Work.BoseBoxFock.dictIIDefs
import Submission.Work.BoseFixB1S.integrableOn_cont_mul_pairComp
-- PORT435-BEGIN (v4.35 isDefEq respectTransparency compat)
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- PORT435-END

/-!
# `Work.BoseBoxFock.dictIIAux.integrableOn_kBound_slots`

`Work.BoseBoxFock.dictII_L1` removes the boundedness hypothesis from `blockII_dict` by clamping
the kernel, and controls the clamped/limit difference through the pointwise dominator
`kBound ℓ b` of the `Q M Q` kernel `qmqKR ℓ b` (`dictIIDefs`).  The passage to the limit on the
**left-hand** side needs the fine-grained integrability

    `x ↦ kBound ℓ b (x p.1, x p.2)`   is integrable on the centred box `abox n ℓ`   (`p.1 ≠ p.2`),

which is what this module supplies.

## Proof

The pair `(p.1, p.2)` of *distinct* slots is an injection of `abox n ℓ` into `Λ × Λ`,
`Λ = acube ℓ`, and the two-particle marginal of the flat measure is the product measure, so the
only input is the integrability of `kBound ℓ b` **on the product** `Λ × Λ`.

* `Work.BoseBoxFock.acubePair ℓ` is by definition `(volume↾Λ).prod (volume↾Λ)`, and by
  `MeasureTheory.Measure.prod_restrict` (with `volume` on `Λ × Λ` definitionally the product
  of the two `volume`s) this is the restriction of the ambient volume to `Λ ×ˢ Λ`; hence the
  hypothesis `hb` *is* `IntegrableOn (kBound ℓ b) (Λ ×ˢ Λ)`.
* `Work.BoseFixB1S.integrableOn_cont_mul_pairComp` with the constant factor `G ≡ 1`
  (via the corpus measure-preserving two-coordinate insertion
  `Submission.BoseGases.integrableOn_pair_comp_ae`, which also disposes of the cases `n ≤ 1`,
  where no distinct slots exist) then gives the claim.

Everything here is `sorry`-free.
-/

noncomputable section

open MeasureTheory

namespace Work.BoseBoxFock.dictIIAux

local notation "E3" => EuclideanSpace ℝ (Fin 3)

theorem integrableOn_kBound_slots {n : ℕ} {ℓ : ℝ} (hℓ : 0 < ℓ) {p : Fin n × Fin n} (hp : p.1 ≠ p.2)
    {b : EuclideanSpace ℝ (Fin 3) → EuclideanSpace ℝ (Fin 3) → ℝ}
    (hb : MeasureTheory.Integrable (Work.BoseBoxFock.kBound ℓ b) (Work.BoseBoxFock.acubePair ℓ)) :
    MeasureTheory.IntegrableOn (fun x : Submission.BoseGases.X n =>
        Work.BoseBoxFock.kBound ℓ b (x p.1, x p.2)) (Submission.BoseGases.abox n ℓ)
      MeasureTheory.volume := by
  -- the hypothesis is integrability *on the cube product* `Λ ×ˢ Λ`
  have hcube : MeasureTheory.IntegrableOn (Work.BoseBoxFock.kBound ℓ b)
      (Submission.BoseGases.acube ℓ ×ˢ Submission.BoseGases.acube ℓ) := by
    rw [MeasureTheory.IntegrableOn,
      show (volume : Measure (E3 × E3))
          = (volume : Measure E3).prod (volume : Measure E3) from rfl,
      ← MeasureTheory.Measure.prod_restrict]
    simpa only [Work.BoseBoxFock.acubePair] using hb
  -- insert the bounded factor `1` and use the measure-preserving two-slot peel
  have h := Work.BoseFixB1S.integrableOn_cont_mul_pairComp (N := n) hℓ hp
    (G := fun _ : Submission.BoseGases.X n => (1 : ℝ)) continuous_const hcube
  simpa using h

end Work.BoseBoxFock.dictIIAux
