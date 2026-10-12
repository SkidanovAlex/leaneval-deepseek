import Mathlib.Analysis.Normed.Lp.MeasurableSpace
import Mathlib.MeasureTheory.Measure.Haar.OfBasis
import Submission.Work.BoseB1Cube.ConeC.BoseFixB1_sectorPieceProj
-- PORT435-BEGIN (v4.35 isDefEq respectTransparency compat)
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- PORT435-END

namespace Work.BoseFixB1.SectorPiece

theorem pairFrags_sum_eq {N : ℕ} {ℓ volA : ℝ}
    {A : Set (EuclideanSpace ℝ (Fin 3))} (hℓ : 0 < ℓ) (hvol : 0 < volA)
    (hA : MeasurableSet A) (hvolA : volA = (MeasureTheory.volume A).toReal)
    (hAc : A ⊆ Submission.BoseGases.acube ℓ)
    {w w1 w2 om : EuclideanSpace ℝ (Fin 3) → EuclideanSpace ℝ (Fin 3) → ℝ}
    (hwsym : ∀ x y : EuclideanSpace ℝ (Fin 3), w x y = w y x)
    (homsym : ∀ x y : EuclideanSpace ℝ (Fin 3), om x y = om y x)
    (hw1rel : ∀ x y : EuclideanSpace ℝ (Fin 3), w1 x y = w x y * (1 - om x y))
    (hw2rel : ∀ x y : EuclideanSpace ℝ (Fin 3), w2 x y = w x y * (1 - om x y ^ 2))
    (hsuppA : ∀ x y : EuclideanSpace ℝ (Fin 3), w x y ≠ 0 → x ∈ A ∧ y ∈ A)
    {Φ : Submission.BoseGases.X N → ℝ} (hΦc : Continuous Φ)
    {x : Submission.BoseGases.X N} (hx : x ∈ Submission.BoseGases.abox N ℓ) :
    (∑ p ∈ Submission.BoseGases.pairSet N,
        Work.BoseFixB1S.pairFrags volA A w w1 w2 om Φ p.1 p.2 x)
      = (1 / 2) * (Φ x) ^ 2 * (∑ p ∈ Submission.BoseGases.pairSet N, w (x p.1) (x p.2)) := by
  classical
  -- The two-orientation sum is the `fgsum` sum, whose summand is the flat pair integrand.
  have hswap := Submission.BoseGases.pairSet_swap_sum (N := N)
    (fun p : Fin N × Fin N =>
      Work.BoseFixB1S.pairFrags volA A w w1 w2 om Φ p.1 p.2 x)
  have key : (∑ p ∈ Submission.BoseGases.pairSet N,
        Work.BoseFixB1S.pairFrags volA A w w1 w2 om Φ p.1 p.2 x)
      = (1 / 2) * (∑ p ∈ Submission.BoseGases.pairSet N,
          (Work.BoseFixB1S.pairFrags volA A w w1 w2 om Φ p.1 p.2 x
            + Work.BoseFixB1S.pairFrags volA A w w1 w2 om Φ p.2 p.1 x)) := by
    rw [Finset.sum_add_distrib, hswap]
    ring
  have hfg : (∑ p ∈ Submission.BoseGases.pairSet N,
        (Work.BoseFixB1S.pairFrags volA A w w1 w2 om Φ p.1 p.2 x
          + Work.BoseFixB1S.pairFrags volA A w w1 w2 om Φ p.2 p.1 x))
      = ∑ p ∈ Submission.BoseGases.pairSet N,
          Work.BoseFixB1S.fgsum volA A w w1 w2 om Φ p.1 p.2 x := by
    apply Finset.sum_congr rfl
    intro p _
    exact (Work.BoseFixB1S.fgsum_eq_pairFrags volA A w w1 w2 om Φ p.1 p.2 x).symm
  have hpt : (∑ p ∈ Submission.BoseGases.pairSet N,
        Work.BoseFixB1S.fgsum volA A w w1 w2 om Φ p.1 p.2 x)
      = ∑ p ∈ Submission.BoseGases.pairSet N,
          Work.BoseFixB1S.Aind A (x p.1) * Work.BoseFixB1S.Aind A (x p.2)
            * (Φ x) ^ 2 * w (x p.1) (x p.2) := by
    apply Finset.sum_congr rfl
    intro p hp
    have hpne : p.1 ≠ p.2 := by simpa [Submission.BoseGases.pairSet] using hp
    exact Work.BoseFixB1S.boxPairPointwise hℓ hvol hA hvolA hAc hwsym homsym hw1rel hw2rel
      hpne hΦc x hx
  have hdrop : (∑ p ∈ Submission.BoseGases.pairSet N,
        Work.BoseFixB1S.Aind A (x p.1) * Work.BoseFixB1S.Aind A (x p.2)
          * (Φ x) ^ 2 * w (x p.1) (x p.2))
      = ∑ p ∈ Submission.BoseGases.pairSet N, (Φ x) ^ 2 * w (x p.1) (x p.2) := by
    apply Finset.sum_congr rfl
    intro p _
    exact Work.BoseFixB1S.Aind_pair_mul_eq hsuppA ((Φ x) ^ 2) (x p.1) (x p.2)
  have hfac : (∑ p ∈ Submission.BoseGases.pairSet N, (Φ x) ^ 2 * w (x p.1) (x p.2))
      = (Φ x) ^ 2 * (∑ p ∈ Submission.BoseGases.pairSet N, w (x p.1) (x p.2)) :=
    (Finset.mul_sum (Submission.BoseGases.pairSet N)
      (fun p : Fin N × Fin N => w (x p.1) (x p.2)) ((Φ x) ^ 2)).symm
  rw [key, hfg, hpt, hdrop, hfac]
  ring

end Work.BoseFixB1.SectorPiece
