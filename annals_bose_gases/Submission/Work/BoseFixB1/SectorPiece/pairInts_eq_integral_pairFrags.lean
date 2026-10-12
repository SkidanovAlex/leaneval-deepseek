import Mathlib.MeasureTheory.Integral.IntegrableOn
import Mathlib.Analysis.Normed.Lp.MeasurableSpace
import Mathlib.MeasureTheory.Integral.Bochner.Basic
import Mathlib.MeasureTheory.Measure.Haar.OfBasis
import Submission.Work.BoseFixB1S.boxPairRaw_eq
-- PORT435-BEGIN (v4.35 isDefEq respectTransparency compat)
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- PORT435-END

namespace Work.BoseFixB1.SectorPiece

theorem pairInts_eq_integral_pairFrags {N : ℕ} {ℓ volA : ℝ}
    {A : Set (EuclideanSpace ℝ (Fin 3))}
    {w w1 w2 om : EuclideanSpace ℝ (Fin 3) → EuclideanSpace ℝ (Fin 3) → ℝ}
    {Φ : Submission.BoseGases.X N → ℝ} {i j : Fin N}
    (I0 : MeasureTheory.IntegrableOn (fun x : Submission.BoseGases.X N =>
      Work.BoseFixB1S.fg0 volA A w2 Φ i j x) (Submission.BoseGases.abox N ℓ) MeasureTheory.volume)
    (I1 : MeasureTheory.IntegrableOn (fun x : Submission.BoseGases.X N =>
      Work.BoseFixB1S.fg1 volA A w2 Φ i j x) (Submission.BoseGases.abox N ℓ) MeasureTheory.volume)
    (I2a : MeasureTheory.IntegrableOn (fun x : Submission.BoseGases.X N =>
      Work.BoseFixB1S.fg2a volA A w2 Φ i j x) (Submission.BoseGases.abox N ℓ) MeasureTheory.volume)
    (I2b : MeasureTheory.IntegrableOn (fun x : Submission.BoseGases.X N =>
      Work.BoseFixB1S.fg2b volA A w2 Φ i j x) (Submission.BoseGases.abox N ℓ) MeasureTheory.volume)
    (I2c : MeasureTheory.IntegrableOn (fun x : Submission.BoseGases.X N =>
      Work.BoseFixB1S.fg2c volA A w1 Φ i j x) (Submission.BoseGases.abox N ℓ) MeasureTheory.volume)
    (I3 : MeasureTheory.IntegrableOn (fun x : Submission.BoseGases.X N =>
      Work.BoseFixB1S.fg3 volA A w1 Φ i j x) (Submission.BoseGases.abox N ℓ) MeasureTheory.volume)
    (I4 : MeasureTheory.IntegrableOn (fun x : Submission.BoseGases.X N =>
      Work.BoseFixB1S.fg4 volA A w om Φ i j x) (Submission.BoseGases.abox N ℓ) MeasureTheory.volume) :
    Work.BoseFixB1S.pairInts volA ℓ A w w1 w2 om Φ i j
      = ∫ x in Submission.BoseGases.abox N ℓ,
          Work.BoseFixB1S.pairFrags volA A w w1 w2 om Φ i j x := by
  -- the running partial sums of the fragment integrands, each integrable by `IntegrableOn.add`
  have P1 : MeasureTheory.IntegrableOn (fun x : Submission.BoseGases.X N =>
      Work.BoseFixB1S.fg0 volA A w2 Φ i j x + Work.BoseFixB1S.fg1 volA A w2 Φ i j x)
      (Submission.BoseGases.abox N ℓ) MeasureTheory.volume := I0.add I1
  have P2 : MeasureTheory.IntegrableOn (fun x : Submission.BoseGases.X N =>
      Work.BoseFixB1S.fg0 volA A w2 Φ i j x + Work.BoseFixB1S.fg1 volA A w2 Φ i j x
        + Work.BoseFixB1S.fg2a volA A w2 Φ i j x)
      (Submission.BoseGases.abox N ℓ) MeasureTheory.volume := P1.add I2a
  have P3 : MeasureTheory.IntegrableOn (fun x : Submission.BoseGases.X N =>
      Work.BoseFixB1S.fg0 volA A w2 Φ i j x + Work.BoseFixB1S.fg1 volA A w2 Φ i j x
        + Work.BoseFixB1S.fg2a volA A w2 Φ i j x + Work.BoseFixB1S.fg2b volA A w2 Φ i j x)
      (Submission.BoseGases.abox N ℓ) MeasureTheory.volume := P2.add I2b
  have P4 : MeasureTheory.IntegrableOn (fun x : Submission.BoseGases.X N =>
      Work.BoseFixB1S.fg0 volA A w2 Φ i j x + Work.BoseFixB1S.fg1 volA A w2 Φ i j x
        + Work.BoseFixB1S.fg2a volA A w2 Φ i j x + Work.BoseFixB1S.fg2b volA A w2 Φ i j x
        + Work.BoseFixB1S.fg2c volA A w1 Φ i j x)
      (Submission.BoseGases.abox N ℓ) MeasureTheory.volume := P3.add I2c
  have P5 : MeasureTheory.IntegrableOn (fun x : Submission.BoseGases.X N =>
      Work.BoseFixB1S.fg0 volA A w2 Φ i j x + Work.BoseFixB1S.fg1 volA A w2 Φ i j x
        + Work.BoseFixB1S.fg2a volA A w2 Φ i j x + Work.BoseFixB1S.fg2b volA A w2 Φ i j x
        + Work.BoseFixB1S.fg2c volA A w1 Φ i j x + Work.BoseFixB1S.fg3 volA A w1 Φ i j x)
      (Submission.BoseGases.abox N ℓ) MeasureTheory.volume := P4.add I3
  unfold Work.BoseFixB1S.pairInts Work.BoseFixB1S.pairFrags
  rw [← MeasureTheory.integral_add I0 I1]
  rw [← MeasureTheory.integral_add P1 I2a]
  rw [← MeasureTheory.integral_add P2 I2b]
  rw [← MeasureTheory.integral_add P3 I2c]
  rw [← MeasureTheory.integral_add P4 I3]
  rw [← MeasureTheory.integral_add P5 I4]

end Work.BoseFixB1.SectorPiece
