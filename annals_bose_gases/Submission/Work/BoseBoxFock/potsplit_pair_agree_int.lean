import Mathlib.MeasureTheory.Integral.IntegrableOn
import Mathlib.Analysis.Normed.Lp.MeasurableSpace
import Mathlib.MeasureTheory.Integral.Bochner.Basic
import Mathlib.MeasureTheory.Measure.Haar.OfBasis
import Submission.PotWords
-- PORT435-BEGIN (v4.35 isDefEq respectTransparency compat)
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- PORT435-END

namespace Work.BoseBoxFock

open MeasureTheory

/-- The per-pair half of FS `lem:potsplit`/`eq:potsplit` with *integrability* hypotheses instead of continuity: the two orientations of the seven word fragments at the ordered pairs `(i,j)` and `(j,i)` combine into the full two-body expectation `∫ Φ²·w(xᵢ,xⱼ)`.  Given the integrability of the fourteen fragment integrands (bundled hypotheses `hI` for `(i,j)`, `hJ` for `(j,i)`), this is the `MeasureTheory.integral_add`/`MeasureTheory.integral_congr_ae` transcription of `Submission.BoseGases.potsplit_pair_agree` (`Submission/PotWords.lean`), whose only use of continuity was to *produce* exactly those fourteen integrabilities; the pointwise input is `Submission.BoseGases.potsplit_pair_pointwise`. -/
theorem potsplit_pair_agree_int {N : ℕ} {ℓ : ℝ} (hℓ : 0 < ℓ) {i j : Fin N} (hij : i ≠ j)
    {w w1 w2 om : EuclideanSpace ℝ (Fin 3) → EuclideanSpace ℝ (Fin 3) → ℝ}
    (hwsym : ∀ x y, w x y = w y x) (homsym : ∀ x y, om x y = om y x)
    (hw1rel : ∀ x y, w1 x y = w x y * (1 - om x y))
    (hw2rel : ∀ x y, w2 x y = w x y * (1 - om x y ^ 2))
    {Φ : Submission.BoseGases.X N → ℝ} (hΦc : Continuous Φ)
    (hI : MeasureTheory.IntegrableOn (fun x : Submission.BoseGases.X N => Submission.BoseGases.fg0 ℓ w2 Φ i j x) (Submission.BoseGases.abox N ℓ) MeasureTheory.volume ∧
      MeasureTheory.IntegrableOn (fun x : Submission.BoseGases.X N => Submission.BoseGases.fg1 ℓ w2 Φ i j x) (Submission.BoseGases.abox N ℓ) MeasureTheory.volume ∧
      MeasureTheory.IntegrableOn (fun x : Submission.BoseGases.X N => Submission.BoseGases.fg2a ℓ w2 Φ i j x) (Submission.BoseGases.abox N ℓ) MeasureTheory.volume ∧
      MeasureTheory.IntegrableOn (fun x : Submission.BoseGases.X N => Submission.BoseGases.fg2b ℓ w2 Φ i j x) (Submission.BoseGases.abox N ℓ) MeasureTheory.volume ∧
      MeasureTheory.IntegrableOn (fun x : Submission.BoseGases.X N => Submission.BoseGases.fg2c ℓ w1 Φ i j x) (Submission.BoseGases.abox N ℓ) MeasureTheory.volume ∧
      MeasureTheory.IntegrableOn (fun x : Submission.BoseGases.X N => Submission.BoseGases.fg3 ℓ w1 Φ i j x) (Submission.BoseGases.abox N ℓ) MeasureTheory.volume ∧
      MeasureTheory.IntegrableOn (fun x : Submission.BoseGases.X N => Submission.BoseGases.fg4 ℓ w om Φ i j x) (Submission.BoseGases.abox N ℓ) MeasureTheory.volume)
    (hJ : MeasureTheory.IntegrableOn (fun x : Submission.BoseGases.X N => Submission.BoseGases.fg0 ℓ w2 Φ j i x) (Submission.BoseGases.abox N ℓ) MeasureTheory.volume ∧
      MeasureTheory.IntegrableOn (fun x : Submission.BoseGases.X N => Submission.BoseGases.fg1 ℓ w2 Φ j i x) (Submission.BoseGases.abox N ℓ) MeasureTheory.volume ∧
      MeasureTheory.IntegrableOn (fun x : Submission.BoseGases.X N => Submission.BoseGases.fg2a ℓ w2 Φ j i x) (Submission.BoseGases.abox N ℓ) MeasureTheory.volume ∧
      MeasureTheory.IntegrableOn (fun x : Submission.BoseGases.X N => Submission.BoseGases.fg2b ℓ w2 Φ j i x) (Submission.BoseGases.abox N ℓ) MeasureTheory.volume ∧
      MeasureTheory.IntegrableOn (fun x : Submission.BoseGases.X N => Submission.BoseGases.fg2c ℓ w1 Φ j i x) (Submission.BoseGases.abox N ℓ) MeasureTheory.volume ∧
      MeasureTheory.IntegrableOn (fun x : Submission.BoseGases.X N => Submission.BoseGases.fg3 ℓ w1 Φ j i x) (Submission.BoseGases.abox N ℓ) MeasureTheory.volume ∧
      MeasureTheory.IntegrableOn (fun x : Submission.BoseGases.X N => Submission.BoseGases.fg4 ℓ w om Φ j i x) (Submission.BoseGases.abox N ℓ) MeasureTheory.volume) :
    Submission.BoseGases.pairInts ℓ w w1 w2 om Φ i j + Submission.BoseGases.pairInts ℓ w w1 w2 om Φ j i =
      ∫ x in Submission.BoseGases.abox N ℓ, (Φ x) ^ 2 * w (x i) (x j) := by
  obtain ⟨hI0, hI1, hI2, hI3, hI4, hI5, hI6⟩ := hI
  obtain ⟨hJ0, hJ1, hJ2, hJ3, hJ4, hJ5, hJ6⟩ := hJ
  have p1 : IntegrableOn (fun x : Submission.BoseGases.X N => Submission.BoseGases.fg0 ℓ w2 Φ i j x + Submission.BoseGases.fg1 ℓ w2 Φ i j x) (Submission.BoseGases.abox N ℓ) volume := hI0.add hI1
  have p2 : IntegrableOn (fun x : Submission.BoseGases.X N => Submission.BoseGases.fg0 ℓ w2 Φ i j x + Submission.BoseGases.fg1 ℓ w2 Φ i j x + Submission.BoseGases.fg2a ℓ w2 Φ i j x) (Submission.BoseGases.abox N ℓ) volume := p1.add hI2
  have p3 : IntegrableOn (fun x : Submission.BoseGases.X N => Submission.BoseGases.fg0 ℓ w2 Φ i j x + Submission.BoseGases.fg1 ℓ w2 Φ i j x + Submission.BoseGases.fg2a ℓ w2 Φ i j x + Submission.BoseGases.fg2b ℓ w2 Φ i j x) (Submission.BoseGases.abox N ℓ) volume := p2.add hI3
  have p4 : IntegrableOn (fun x : Submission.BoseGases.X N => Submission.BoseGases.fg0 ℓ w2 Φ i j x + Submission.BoseGases.fg1 ℓ w2 Φ i j x + Submission.BoseGases.fg2a ℓ w2 Φ i j x + Submission.BoseGases.fg2b ℓ w2 Φ i j x + Submission.BoseGases.fg2c ℓ w1 Φ i j x) (Submission.BoseGases.abox N ℓ) volume := p3.add hI4
  have p5 : IntegrableOn (fun x : Submission.BoseGases.X N => Submission.BoseGases.fg0 ℓ w2 Φ i j x + Submission.BoseGases.fg1 ℓ w2 Φ i j x + Submission.BoseGases.fg2a ℓ w2 Φ i j x + Submission.BoseGases.fg2b ℓ w2 Φ i j x + Submission.BoseGases.fg2c ℓ w1 Φ i j x + Submission.BoseGases.fg3 ℓ w1 Φ i j x) (Submission.BoseGases.abox N ℓ) volume := p4.add hI5
  have p6 : IntegrableOn (fun x : Submission.BoseGases.X N => Submission.BoseGases.fg0 ℓ w2 Φ i j x + Submission.BoseGases.fg1 ℓ w2 Φ i j x + Submission.BoseGases.fg2a ℓ w2 Φ i j x + Submission.BoseGases.fg2b ℓ w2 Φ i j x + Submission.BoseGases.fg2c ℓ w1 Φ i j x + Submission.BoseGases.fg3 ℓ w1 Φ i j x + Submission.BoseGases.fg4 ℓ w om Φ i j x) (Submission.BoseGases.abox N ℓ) volume := p5.add hI6
  have q1 : IntegrableOn (fun x : Submission.BoseGases.X N => Submission.BoseGases.fg0 ℓ w2 Φ j i x + Submission.BoseGases.fg1 ℓ w2 Φ j i x) (Submission.BoseGases.abox N ℓ) volume := hJ0.add hJ1
  have q2 : IntegrableOn (fun x : Submission.BoseGases.X N => Submission.BoseGases.fg0 ℓ w2 Φ j i x + Submission.BoseGases.fg1 ℓ w2 Φ j i x + Submission.BoseGases.fg2a ℓ w2 Φ j i x) (Submission.BoseGases.abox N ℓ) volume := q1.add hJ2
  have q3 : IntegrableOn (fun x : Submission.BoseGases.X N => Submission.BoseGases.fg0 ℓ w2 Φ j i x + Submission.BoseGases.fg1 ℓ w2 Φ j i x + Submission.BoseGases.fg2a ℓ w2 Φ j i x + Submission.BoseGases.fg2b ℓ w2 Φ j i x) (Submission.BoseGases.abox N ℓ) volume := q2.add hJ3
  have q4 : IntegrableOn (fun x : Submission.BoseGases.X N => Submission.BoseGases.fg0 ℓ w2 Φ j i x + Submission.BoseGases.fg1 ℓ w2 Φ j i x + Submission.BoseGases.fg2a ℓ w2 Φ j i x + Submission.BoseGases.fg2b ℓ w2 Φ j i x + Submission.BoseGases.fg2c ℓ w1 Φ j i x) (Submission.BoseGases.abox N ℓ) volume := q3.add hJ4
  have q5 : IntegrableOn (fun x : Submission.BoseGases.X N => Submission.BoseGases.fg0 ℓ w2 Φ j i x + Submission.BoseGases.fg1 ℓ w2 Φ j i x + Submission.BoseGases.fg2a ℓ w2 Φ j i x + Submission.BoseGases.fg2b ℓ w2 Φ j i x + Submission.BoseGases.fg2c ℓ w1 Φ j i x + Submission.BoseGases.fg3 ℓ w1 Φ j i x) (Submission.BoseGases.abox N ℓ) volume := q4.add hJ5
  have q6 : IntegrableOn (fun x : Submission.BoseGases.X N => Submission.BoseGases.fg0 ℓ w2 Φ j i x + Submission.BoseGases.fg1 ℓ w2 Φ j i x + Submission.BoseGases.fg2a ℓ w2 Φ j i x + Submission.BoseGases.fg2b ℓ w2 Φ j i x + Submission.BoseGases.fg2c ℓ w1 Φ j i x + Submission.BoseGases.fg3 ℓ w1 Φ j i x + Submission.BoseGases.fg4 ℓ w om Φ j i x) (Submission.BoseGases.abox N ℓ) volume := q5.add hJ6
  have hA : Submission.BoseGases.pairInts ℓ w w1 w2 om Φ i j = ∫ x in Submission.BoseGases.abox N ℓ, (Submission.BoseGases.fg0 ℓ w2 Φ i j x + Submission.BoseGases.fg1 ℓ w2 Φ i j x + Submission.BoseGases.fg2a ℓ w2 Φ i j x + Submission.BoseGases.fg2b ℓ w2 Φ i j x + Submission.BoseGases.fg2c ℓ w1 Φ i j x + Submission.BoseGases.fg3 ℓ w1 Φ i j x + Submission.BoseGases.fg4 ℓ w om Φ i j x) := by
    unfold Submission.BoseGases.pairInts
    rw [← integral_add hI0 hI1]
    rw [← integral_add p1 hI2]
    rw [← integral_add p2 hI3]
    rw [← integral_add p3 hI4]
    rw [← integral_add p4 hI5]
    rw [← integral_add p5 hI6]
  have hB : Submission.BoseGases.pairInts ℓ w w1 w2 om Φ j i = ∫ x in Submission.BoseGases.abox N ℓ, (Submission.BoseGases.fg0 ℓ w2 Φ j i x + Submission.BoseGases.fg1 ℓ w2 Φ j i x + Submission.BoseGases.fg2a ℓ w2 Φ j i x + Submission.BoseGases.fg2b ℓ w2 Φ j i x + Submission.BoseGases.fg2c ℓ w1 Φ j i x + Submission.BoseGases.fg3 ℓ w1 Φ j i x + Submission.BoseGases.fg4 ℓ w om Φ j i x) := by
    unfold Submission.BoseGases.pairInts
    rw [← integral_add hJ0 hJ1]
    rw [← integral_add q1 hJ2]
    rw [← integral_add q2 hJ3]
    rw [← integral_add q3 hJ4]
    rw [← integral_add q4 hJ5]
    rw [← integral_add q5 hJ6]
  have hpt : ∀ x : Submission.BoseGases.X N,
      (Submission.BoseGases.fg0 ℓ w2 Φ i j x + Submission.BoseGases.fg1 ℓ w2 Φ i j x + Submission.BoseGases.fg2a ℓ w2 Φ i j x + Submission.BoseGases.fg2b ℓ w2 Φ i j x + Submission.BoseGases.fg2c ℓ w1 Φ i j x + Submission.BoseGases.fg3 ℓ w1 Φ i j x + Submission.BoseGases.fg4 ℓ w om Φ i j x)
        + (Submission.BoseGases.fg0 ℓ w2 Φ j i x + Submission.BoseGases.fg1 ℓ w2 Φ j i x + Submission.BoseGases.fg2a ℓ w2 Φ j i x + Submission.BoseGases.fg2b ℓ w2 Φ j i x + Submission.BoseGases.fg2c ℓ w1 Φ j i x + Submission.BoseGases.fg3 ℓ w1 Φ j i x + Submission.BoseGases.fg4 ℓ w om Φ j i x)
      = (Φ x) ^ 2 * w (x i) (x j) := by
    intro x
    have h1 := Submission.BoseGases.potsplit_pair_pointwise hℓ hij hwsym homsym hw1rel hw2rel hΦc x
    unfold Submission.BoseGases.fgsum at h1
    rw [← h1]
    ring
  calc
    Submission.BoseGases.pairInts ℓ w w1 w2 om Φ i j + Submission.BoseGases.pairInts ℓ w w1 w2 om Φ j i
        = (∫ x in Submission.BoseGases.abox N ℓ, (Submission.BoseGases.fg0 ℓ w2 Φ i j x + Submission.BoseGases.fg1 ℓ w2 Φ i j x + Submission.BoseGases.fg2a ℓ w2 Φ i j x + Submission.BoseGases.fg2b ℓ w2 Φ i j x + Submission.BoseGases.fg2c ℓ w1 Φ i j x + Submission.BoseGases.fg3 ℓ w1 Φ i j x + Submission.BoseGases.fg4 ℓ w om Φ i j x)) + (∫ x in Submission.BoseGases.abox N ℓ, (Submission.BoseGases.fg0 ℓ w2 Φ j i x + Submission.BoseGases.fg1 ℓ w2 Φ j i x + Submission.BoseGases.fg2a ℓ w2 Φ j i x + Submission.BoseGases.fg2b ℓ w2 Φ j i x + Submission.BoseGases.fg2c ℓ w1 Φ j i x + Submission.BoseGases.fg3 ℓ w1 Φ j i x + Submission.BoseGases.fg4 ℓ w om Φ j i x)) := by
          rw [hA, hB]
    _ = (∫ x in Submission.BoseGases.abox N ℓ, ((Submission.BoseGases.fg0 ℓ w2 Φ i j x + Submission.BoseGases.fg1 ℓ w2 Φ i j x + Submission.BoseGases.fg2a ℓ w2 Φ i j x + Submission.BoseGases.fg2b ℓ w2 Φ i j x + Submission.BoseGases.fg2c ℓ w1 Φ i j x + Submission.BoseGases.fg3 ℓ w1 Φ i j x + Submission.BoseGases.fg4 ℓ w om Φ i j x) + (Submission.BoseGases.fg0 ℓ w2 Φ j i x + Submission.BoseGases.fg1 ℓ w2 Φ j i x + Submission.BoseGases.fg2a ℓ w2 Φ j i x + Submission.BoseGases.fg2b ℓ w2 Φ j i x + Submission.BoseGases.fg2c ℓ w1 Φ j i x + Submission.BoseGases.fg3 ℓ w1 Φ j i x + Submission.BoseGases.fg4 ℓ w om Φ j i x))) := by
          rw [← integral_add p6 q6]
    _ = (∫ x in Submission.BoseGases.abox N ℓ, (Φ x) ^ 2 * w (x i) (x j)) := by
          apply integral_congr_ae
          filter_upwards with x
          exact hpt x

end Work.BoseBoxFock
