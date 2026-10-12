import Mathlib.Analysis.Normed.Lp.MeasurableSpace
import Mathlib.MeasureTheory.Measure.Haar.OfBasis
import Submission.Work.BoseFixB1S.BoxPotOper
-- PORT435-BEGIN (v4.35 isDefEq respectTransparency compat)
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- PORT435-END

noncomputable section

open MeasureTheory
open scoped Real BigOperators ENNReal

namespace Work.BoseFixB1S

open Submission.BoseGases

set_option autoImplicit false
set_option maxHeartbeats 800000

theorem boxPairPointwise {N : ℕ} {ℓ volA : ℝ} (hℓ : 0 < ℓ) (hvol : 0 < volA)
    {A : Set ℝ³} (hA : MeasurableSet A) (hvolA : volA = (volume A).toReal) (hAc : A ⊆ acube ℓ)
    {w w1 w2 om : ℝ³ → ℝ³ → ℝ}
    (hwsym : ∀ x y : ℝ³, w x y = w y x) (homsym : ∀ x y : ℝ³, om x y = om y x)
    (hw1rel : ∀ x y : ℝ³, w1 x y = w x y * (1 - om x y))
    (hw2rel : ∀ x y : ℝ³, w2 x y = w x y * (1 - om x y ^ 2))
    {i j : Fin N} (hij : i ≠ j) {Φ : Submission.BoseGases.X N → ℝ} (hΦc : Continuous Φ)
    (x : Submission.BoseGases.X N) (hx : x ∈ abox N ℓ) :
    fgsum volA A w w1 w2 om Φ i j x
      = Aind A (x i) * Aind A (x j) * (Φ x) ^ 2 * w (x i) (x j) := by
  unfold fgsum fg0 fg1 fg2a fg2b fg2c fg3 fg4
  let Aa : ℝ := Work.UBBInputs8.boxPInd volA A i (Work.UBBInputs8.boxPInd volA A j Φ) x
  let Bb : ℝ := Work.UBBInputs8.boxPInd volA A i (Work.UBBInputs8.boxQInd volA A j Φ) x
  let Cc : ℝ := Work.UBBInputs8.boxQInd volA A i (Work.UBBInputs8.boxPInd volA A j Φ) x
  let Dd : ℝ := Work.UBBInputs8.boxQInd volA A i (Work.UBBInputs8.boxQInd volA A j Φ) x
  let W : ℝ := w (x i) (x j)
  let O : ℝ := om (x i) (x j)
  let W1 : ℝ := w1 (x i) (x j)
  let W2 : ℝ := w2 (x i) (x j)
  have hW1rel : W1 = W * (1 - O) := by simp only [W1, W, O, hw1rel]
  have hW2rel : W2 = W * (1 - O ^ 2) := by simp only [W2, W, O, hw2rel]
  -- the pattern sum
  have hpat : Aa + Bb + Cc + Dd = Aind A (x i) * Aind A (x j) * Φ x := by
    simp only [Aa, Bb, Cc, Dd]
    exact boxPatternSum hℓ hvol hA hvolA hAc hij hΦc x hx
  -- the orientation swaps
  have hA' : Work.UBBInputs8.boxPInd volA A j (Work.UBBInputs8.boxPInd volA A i Φ) x = Aa := by
    simp only [Aa]
    exact boxPPswap hℓ hvol hA hvolA hAc hij hΦc x
  have hB' : Work.UBBInputs8.boxPInd volA A j (Work.UBBInputs8.boxQInd volA A i Φ) x = Cc := by
    simp only [Cc]
    exact boxPQswap hℓ hvol hA hvolA hAc hij hΦc x hx
  have hC' : Work.UBBInputs8.boxQInd volA A j (Work.UBBInputs8.boxPInd volA A i Φ) x = Bb := by
    simp only [Bb]
    exact boxQPswap hℓ hvol hA hvolA hAc hij hΦc x hx
  have hD' : Work.UBBInputs8.boxQInd volA A j (Work.UBBInputs8.boxQInd volA A i Φ) x = Dd := by
    simp only [Dd]
    exact boxQQswap hℓ hvol hA hvolA hAc hij hΦc x hx
  -- the kernel symmetries at the swapped slots
  have hWsym : w (x j) (x i) = W := by simp only [W]; exact (hwsym (x i) (x j)).symm
  have hOsym : om (x j) (x i) = O := by simp only [O]; exact (homsym (x i) (x j)).symm
  have hW1sym : w1 (x j) (x i) = W1 := by
    simp only [W1]
    rw [hw1rel (x j) (x i), hw1rel (x i) (x j), hwsym (x i) (x j), homsym (x i) (x j)]
  have hW2sym : w2 (x j) (x i) = W2 := by
    simp only [W2]
    rw [hw2rel (x j) (x i), hw2rel (x i) (x j), hwsym (x i) (x j), homsym (x i) (x j)]
  -- the two `Q₄` brackets, in explicit form
  have hB4ij : boxQ4B volA A om Φ (i, j) x
      = Dd + om (x i) (x j) * (Aa + Bb + Cc) := by
    have h1 : boxQ4B volA A om Φ (i, j) x
        = Work.UBBInputs8.boxQInd volA A j (Work.UBBInputs8.boxQInd volA A i Φ) x
          + om (x i) (x j)
            * (Work.UBBInputs8.boxPInd volA A j (Work.UBBInputs8.boxPInd volA A i Φ) x
              + Work.UBBInputs8.boxPInd volA A j (Work.UBBInputs8.boxQInd volA A i Φ) x
              + Work.UBBInputs8.boxQInd volA A j (Work.UBBInputs8.boxPInd volA A i Φ) x) := rfl
    rw [h1, hD', hA', hB', hC']
    try ring
  have hB4ji : boxQ4B volA A om Φ (j, i) x
      = Dd + om (x i) (x j) * (Aa + Bb + Cc) := by
    have h1 : boxQ4B volA A om Φ (j, i) x
        = Work.UBBInputs8.boxQInd volA A i (Work.UBBInputs8.boxQInd volA A j Φ) x
          + om (x j) (x i)
            * (Work.UBBInputs8.boxPInd volA A i (Work.UBBInputs8.boxPInd volA A j Φ) x
              + Work.UBBInputs8.boxPInd volA A i (Work.UBBInputs8.boxQInd volA A j Φ) x
              + Work.UBBInputs8.boxQInd volA A i (Work.UBBInputs8.boxPInd volA A j Φ) x) := rfl
    rw [h1, hOsym]
  -- the fourteen fragment values
  have h0ij : (1 / 2) * (Work.UBBInputs8.boxPInd volA A i
        (Work.UBBInputs8.boxPInd volA A j Φ) x) ^ 2 * w2 (x i) (x j)
      = (1 / 2) * Aa ^ 2 * W2 := by
    simp only [Aa, W2]; try ring
  have h1ij : 2 * (Work.UBBInputs8.boxPInd volA A i (Work.UBBInputs8.boxQInd volA A j Φ) x)
        * (Work.UBBInputs8.boxPInd volA A i (Work.UBBInputs8.boxPInd volA A j Φ) x)
        * w2 (x i) (x j) = 2 * Bb * Aa * W2 := by
    simp only [Aa, Bb, W2]; try ring
  have h2aij : (Work.UBBInputs8.boxPInd volA A i (Work.UBBInputs8.boxQInd volA A j Φ) x)
        * (Work.UBBInputs8.boxPInd volA A j (Work.UBBInputs8.boxQInd volA A i Φ) x)
        * w2 (x i) (x j) = Bb * Cc * W2 := by
    simp only [hB', Bb, Cc, W2]; try ring
  have h2bij : (Work.UBBInputs8.boxPInd volA A i (Work.UBBInputs8.boxQInd volA A j Φ) x)
        * (Work.UBBInputs8.boxQInd volA A j (Work.UBBInputs8.boxPInd volA A i Φ) x)
        * w2 (x i) (x j) = Bb * Bb * W2 := by
    simp only [hC', Bb, W2]; try ring
  have h2cij : (Work.UBBInputs8.boxPInd volA A i (Work.UBBInputs8.boxPInd volA A j Φ) x)
        * (Work.UBBInputs8.boxQInd volA A j (Work.UBBInputs8.boxQInd volA A i Φ) x)
        * w1 (x i) (x j) = Aa * Dd * W1 := by
    simp only [hD', Aa, Dd, W1]; try ring
  have h3ij : 2 * (Work.UBBInputs8.boxPInd volA A i (Work.UBBInputs8.boxQInd volA A j Φ) x)
        * (Work.UBBInputs8.boxQInd volA A j (Work.UBBInputs8.boxQInd volA A i Φ) x)
        * w1 (x i) (x j) = 2 * Bb * Dd * W1 := by
    simp only [hD', Bb, Dd, W1]; try ring
  have h4ij : (1 / 2) * (boxQ4B volA A om Φ (i, j) x) ^ 2 * w (x i) (x j)
      = (1 / 2) * (Dd + om (x i) (x j) * (Aa + Bb + Cc)) ^ 2 * W := by
    simp only [hB4ij, W]; try ring
  have h0ji : (1 / 2) * (Work.UBBInputs8.boxPInd volA A j
        (Work.UBBInputs8.boxPInd volA A i Φ) x) ^ 2 * w2 (x j) (x i)
      = (1 / 2) * Aa ^ 2 * W2 := by
    simp only [hA', hW2sym, Aa, W2]; try ring
  have h1ji : 2 * (Work.UBBInputs8.boxPInd volA A j (Work.UBBInputs8.boxQInd volA A i Φ) x)
        * (Work.UBBInputs8.boxPInd volA A j (Work.UBBInputs8.boxPInd volA A i Φ) x)
        * w2 (x j) (x i) = 2 * Cc * Aa * W2 := by
    simp only [hB', hA', hW2sym, Aa, Cc, W2]; try ring
  have h2aji : (Work.UBBInputs8.boxPInd volA A j (Work.UBBInputs8.boxQInd volA A i Φ) x)
        * (Work.UBBInputs8.boxPInd volA A i (Work.UBBInputs8.boxQInd volA A j Φ) x)
        * w2 (x j) (x i) = Cc * Bb * W2 := by
    simp only [hB', hW2sym, Bb, Cc, W2]; try ring
  have h2bji : (Work.UBBInputs8.boxPInd volA A j (Work.UBBInputs8.boxQInd volA A i Φ) x)
        * (Work.UBBInputs8.boxQInd volA A i (Work.UBBInputs8.boxPInd volA A j Φ) x)
        * w2 (x j) (x i) = Cc * Cc * W2 := by
    simp only [hB', hW2sym, Cc, W2]; try ring
  have h2cji : (Work.UBBInputs8.boxPInd volA A j (Work.UBBInputs8.boxPInd volA A i Φ) x)
        * (Work.UBBInputs8.boxQInd volA A i (Work.UBBInputs8.boxQInd volA A j Φ) x)
        * w1 (x j) (x i) = Aa * Dd * W1 := by
    simp only [hA', hW1sym, Aa, Dd, W1]; try ring
  have h3ji : 2 * (Work.UBBInputs8.boxPInd volA A j (Work.UBBInputs8.boxQInd volA A i Φ) x)
        * (Work.UBBInputs8.boxQInd volA A i (Work.UBBInputs8.boxQInd volA A j Φ) x)
        * w1 (x j) (x i) = 2 * Cc * Dd * W1 := by
    simp only [hB', hW1sym, Cc, Dd, W1]; try ring
  have h4ji : (1 / 2) * (boxQ4B volA A om Φ (j, i) x) ^ 2 * w (x j) (x i)
      = (1 / 2) * (Dd + om (x i) (x j) * (Aa + Bb + Cc)) ^ 2 * W := by
    simp only [hB4ji, hWsym, W]; try ring
  -- the target right-hand side in atom form
  have hRHS : Aind A (x i) * Aind A (x j) * (Φ x) ^ 2 * w (x i) (x j)
      = (Aa + Bb + Cc + Dd) ^ 2 * W := by
    have hσ : Aind A (x i) * Aind A (x j) * (Aind A (x i) * Aind A (x j))
        = Aind A (x i) * Aind A (x j) := by
      rw [show Aind A (x i) * Aind A (x j) * (Aind A (x i) * Aind A (x j))
          = Aind A (x i) * Aind A (x i) * (Aind A (x j) * Aind A (x j)) from by ring,
        Aind_mul_self A (x i), Aind_mul_self A (x j)]
    have hσΦ : (Aind A (x i) * Aind A (x j) * Φ x) ^ 2
        = Aind A (x i) * Aind A (x j) * (Φ x) ^ 2 := by
      calc (Aind A (x i) * Aind A (x j) * Φ x) ^ 2
          = (Aind A (x i) * Aind A (x j) * (Aind A (x i) * Aind A (x j)))
              * ((Φ x) * (Φ x)) := by ring
        _ = (Aind A (x i) * Aind A (x j)) * ((Φ x) * (Φ x)) := by rw [hσ]
        _ = Aind A (x i) * Aind A (x j) * (Φ x) ^ 2 := by ring
    rw [hpat, hσΦ]
  rw [hRHS]
  rw [h0ij, h1ij, h2aij, h2bij, h2cij, h3ij, h4ij,
    h0ji, h1ji, h2aji, h2bji, h2cji, h3ji, h4ji]
  rw [hW1rel, hW2rel]
  ring

end Work.BoseFixB1S
