import Mathlib.MeasureTheory.Constructions.Pi
import Mathlib.Analysis.Normed.Lp.MeasurableSpace
import Mathlib.MeasureTheory.Measure.Haar.OfBasis
import Submission.Work.BoseFixB1.Cube.Loc.fibreSplitAux
-- PORT435-BEGIN (v4.35 isDefEq respectTransparency compat)
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- PORT435-END

/-!
# `Work.BoseFixB1.Cube.Loc.subsectorSupp_slice_snd`

Mathematical content: the a.e. subsector support of `Φ` (on the `(k+m)`-box), in the block
coordinates supplied by `subsectorSupp_merge`, survives the **exchange** of the two slices.  That
is, the statement `∀ᵐ (y, w), support condition` for the *product* measure
`(volume↾abox k a).prod (volume↾abox m a)` implies the same for the *iterated* a.e. form with the
`m`-slice outermost:

    ∀ᵐ w ∂μm, ∀ᵐ y ∂μk, Φ (mergeBlock k m (y, w)) ≠ 0 → (∀ i, y i ∈ A) ∧ (∀ j, w j ∉ A) .

The only ingredient is that the swap `Prod.swap` is measure preserving from `μm.prod μk` to
`μk.prod μm` (`Measure.measurePreserving_swap`, i.e. `Measure.prod_swap`), together with
`Measure.ae_ae_of_ae_prod`; **no measurability of `Φ` or of `A`** is needed, because the argument
is carried out at the level of a.e. statements (preimages of null sets).
-/

namespace Work.BoseFixB1.Cube.Loc

open MeasureTheory

theorem subsectorSupp_slice_snd {k m : ℕ} {a : ℝ} {A : Set (EuclideanSpace ℝ (Fin 3))}
    {Φ : Submission.BoseGases.X (k + m) → ℝ}
    (hsupp : Work.BoseFixB1.Cube.Loc.SubsectorSupp k m a A Φ) :
    ∀ᵐ w ∂((MeasureTheory.volume : MeasureTheory.Measure (Submission.BoseGases.X m)).restrict
        (Submission.BoseGases.abox m a)),
      ∀ᵐ y ∂((MeasureTheory.volume : MeasureTheory.Measure (Submission.BoseGases.X k)).restrict
        (Submission.BoseGases.abox k a)),
        Φ (Submission.BoseGases.mergeBlock k m (y, w)) ≠ 0 →
          (∀ i : Fin k, y i ∈ A) ∧ (∀ j : Fin m, w j ∉ A) := by
  -- `h0` is the product-measure form of the support hypothesis.
  have h0 := subsectorSupp_merge hsupp
  -- The swap is measure preserving `(μm.prod μk) → (μk.prod μm)`.
  have hswap : MeasureTheory.MeasurePreserving Prod.swap
      (((MeasureTheory.volume : MeasureTheory.Measure (Submission.BoseGases.X m)).restrict
          (Submission.BoseGases.abox m a)).prod
        ((MeasureTheory.volume : MeasureTheory.Measure (Submission.BoseGases.X k)).restrict
          (Submission.BoseGases.abox k a)))
      (((MeasureTheory.volume : MeasureTheory.Measure (Submission.BoseGases.X k)).restrict
          (Submission.BoseGases.abox k a)).prod
        ((MeasureTheory.volume : MeasureTheory.Measure (Submission.BoseGases.X m)).restrict
          (Submission.BoseGases.abox m a))) :=
    MeasureTheory.Measure.measurePreserving_swap
  -- Transport along the swap: a.e. statement for `μm.prod μk`, in the exchanged coordinates.
  have h1 : ∀ᵐ q ∂(((MeasureTheory.volume : MeasureTheory.Measure
          (Submission.BoseGases.X m)).restrict (Submission.BoseGases.abox m a)).prod
        ((MeasureTheory.volume : MeasureTheory.Measure (Submission.BoseGases.X k)).restrict
          (Submission.BoseGases.abox k a))),
      Φ (Submission.BoseGases.mergeBlock k m (q.2, q.1)) ≠ 0 →
        (∀ i : Fin k, q.2 i ∈ A) ∧ (∀ j : Fin m, q.1 j ∉ A) :=
    hswap.quasiMeasurePreserving.ae h0
  exact MeasureTheory.Measure.ae_ae_of_ae_prod h1

end Work.BoseFixB1.Cube.Loc
