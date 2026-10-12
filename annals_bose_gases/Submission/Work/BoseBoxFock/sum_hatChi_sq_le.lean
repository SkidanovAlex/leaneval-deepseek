import Mathlib.Data.ZMod.ValMinAbs
import Mathlib.MeasureTheory.Function.LocallyIntegrable
import Mathlib.Algebra.Order.Star.Real
import Mathlib.Analysis.Normed.Lp.MeasurableSpace
import Mathlib.MeasureTheory.Integral.Bochner.Basic
import Mathlib.MeasureTheory.Measure.Haar.OfBasis
import Submission.Work.BoseBoxFock.integral_unitCell_chi_cos
import Submission.Work.BoseBoxFock.integral_unitCell_chi_sq
import Submission.Work.BoseBoxFock.integral_unitCell_cos_cos
import Submission.Work.BoseBoxFock.sum_pair_delta
-- PORT435-BEGIN (v4.35 isDefEq respectTransparency compat)
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- PORT435-END

/-!
# `Work.BoseBoxFock.sum_hatChi_sq_le` — the lattice Bessel bound `∑_k χ̂(2πk)² ≤ 1`

For the corpus localization function `χ = Submission.BoseGases.chi` (the `C^∞` bump on the
unit cell, `∫χ² = 1`) and the cube lattice `Lab N = (ZMod (2N+1))³` of the box `[−1/2,1/2]³`
at side `ℓ = 1` (momenta `2π·(centred label)`), the sum of the squared Fourier coefficients
`χ̂(2πk) = ∫ χ(x)cos⟨2πk,x⟩` over the labels of the cube is at most `1`.

This is the Bessel/Parseval bound for the orthonormal system
`{x ↦ cos⟨2πk,x⟩}_{k ∈ ℤ³} ∪ {x ↦ sin⟨2πk,x⟩}_{k ∈ ℤ³ \ {0}}` of `L²(unitCell)`: the
*cosine* half of it gives `∫_cell χ̂_k cos_k = χ̂_k`, while the *sine* half contributes the
missing `sin⟨2πk,x⟩`-mass, which is what makes the complex-exponential identity
`∑_k χ̂(2πk)² = ∫_cell χ² = 1` (Parseval on the unit torus) valid.  A `cos`-only argument
would give the weaker `∑_{k≠0} χ̂(2πk)² ≤ (1 − χ̂(0)²)/2`, so the sine terms are recorded
here as the pair-sum identity `∫ P² = ∑_k c_k²` of `hPP` below.

## The argument

Write `P(x) = ∑_k c_k cos⟨2πℓ_k,x⟩` with `c_k = χ̂(2πℓ_k)`, the `k`-sum over the labels of
`Lab N` (`ℓ_k = vec (labVec N k)`).  Then

* `∫_cell χ·P = ∑_k c_k²` (`hchiP`, linearity and the pairing `integral_unitCell_chi_cos`);
* `∫_cell P² = ∑_k c_k²` (`hPP`): expanding the square gives the double sum of
  `c_k c_{k'} ∫ cos_k cos_{k'} = c_k c_{k'} (δ_{kk'} + δ_{k,−k'})/2`
  (`integral_unitCell_cos_cos`), and the pairing identity `sum_pair_delta` collapses it;
* `∫_cell χ² = 1` (`integral_unitCell_chi_sq`).

Since `0 ≤ ∫_cell (χ − P)² = 1 − 2∑_k c_k² + ∑_k c_k² = 1 − ∑_k c_k²`, the bound follows.
The hypotheses `hcos`/`hchi`/`hχ2`/`hdelta` of the lemma `sum_sq_le_of_cosData` are exactly
the lattice facts above, so the lemma is pure Hilbert-space algebra over the unit cell.
-/

noncomputable section

open MeasureTheory
open scoped BigOperators

namespace Work.BoseBoxFock

/-- **The Hilbert-space core.**  For coefficients `c : Lab N → ℝ` of the cosine system of the
unit cell — `hcos` (the `cos`-orthogonality `∫ cos_k cos_{k'} = (δ_{kk'} + δ_{k,−k'})/2`),
`hchi` (the pairing `∫ χ cos_k = c_k`), `hχ2` (`∫ χ² = 1`) and the collapsed double sum
`hdelta` — one has `∑_k c_k² ≤ 1`.

The proof is `0 ≤ ∫_cell (χ − P)²` with `P = ∑_k c_k cos_k`: expanding the square with
`∫_cell χ² = 1`, `∫_cell χ·P = ∑_k c_k²` and `∫_cell P² = ∑_k c_k²` gives
`0 ≤ 1 − ∑_k c_k²`. -/
lemma sum_sq_le_of_cosData (N : ℕ) (c : Lab N → ℝ)
    (hcos : ∀ k k' : Lab N,
      ∫ x in Work.BoseB4.unitCell,
          Real.cos (inner ℝ (Work.BoseB4.vec (labVec N k)) x)
            * Real.cos (inner ℝ (Work.BoseB4.vec (labVec N k')) x)
        = ((if labVec N k = labVec N k' then (1 : ℝ) else 0)
            + (if labVec N k = -(labVec N k') then (1 : ℝ) else 0)) / 2)
    (hchi : ∀ k : Lab N,
      ∫ x in Work.BoseB4.unitCell,
          Submission.BoseGases.chi x * Real.cos (inner ℝ (Work.BoseB4.vec (labVec N k)) x) = c k)
    (hχ2 : ∫ x in Work.BoseB4.unitCell, (Submission.BoseGases.chi x) ^ 2 = 1)
    (hdelta : (∑ k : Lab N, ∑ k' : Lab N, c k * c k' *
        (((if labVec N k = labVec N k' then (1 : ℝ) else 0)
          + (if labVec N k = -(labVec N k') then (1 : ℝ) else 0)) / 2))
        = ∑ k : Lab N, (c k) ^ 2) :
    ∑ k : Lab N, (c k) ^ 2 ≤ 1 := by
  classical
  -- the cosine projection of `χ` onto the labels of the cube
  let P : EuclideanSpace ℝ (Fin 3) → ℝ := fun x =>
    ∑ k : Lab N, c k * Real.cos (inner ℝ (Work.BoseB4.vec (labVec N k)) x)
  have hPeval : ∀ x,
      P x = ∑ k : Lab N, c k * Real.cos (inner ℝ (Work.BoseB4.vec (labVec N k)) x) :=
    fun x => rfl
  have hχc : Continuous fun x : EuclideanSpace ℝ (Fin 3) => Submission.BoseGases.chi x :=
    Submission.BoseGases.chi_continuous
  have hInt : ∀ f : EuclideanSpace ℝ (Fin 3) → ℝ, Continuous f →
      Integrable f (volume.restrict Work.BoseB4.unitCell) := fun f hf =>
    ContinuousOn.integrableOn_compact Work.BoseB4.isCompact_unitCell hf.continuousOn
  have hcoscont : ∀ v : EuclideanSpace ℝ (Fin 3),
      Continuous fun x : EuclideanSpace ℝ (Fin 3) => Real.cos (inner ℝ v x) := by
    intro v
    exact Real.continuous_cos.comp (continuous_const.inner continuous_id)
  -- ### (1) the pairing `∫_cell χ · P = ∑_k c_k²`
  have hchiP : ∫ x in Work.BoseB4.unitCell, Submission.BoseGases.chi x * P x
      = ∑ k : Lab N, (c k) ^ 2 := by
    have hfun : (fun x => Submission.BoseGases.chi x * P x)
        = fun x => ∑ k : Lab N, c k *
            (Submission.BoseGases.chi x * Real.cos (inner ℝ (Work.BoseB4.vec (labVec N k)) x)) := by
      funext x
      rw [hPeval x, Finset.mul_sum]
      exact Finset.sum_congr rfl fun k _ => by ring
    rw [hfun]
    rw [integral_finsetSum (Finset.univ)
      (f := fun k x => c k *
        (Submission.BoseGases.chi x * Real.cos (inner ℝ (Work.BoseB4.vec (labVec N k)) x)))
      (fun k _ => hInt _ (continuous_const.mul (hχc.mul (hcoscont _))))]
    apply Finset.sum_congr rfl
    intro k _
    rw [integral_const_mul, hchi k]
    ring
  -- ### (2) the self-pairing `∫_cell P² = ∑_k c_k²`
  have hPP : ∫ x in Work.BoseB4.unitCell, (P x) ^ 2 = ∑ k : Lab N, (c k) ^ 2 := by
    have hfun : (fun x => (P x) ^ 2) = fun x => ∑ k : Lab N, ∑ k' : Lab N,
        c k * c k' * (Real.cos (inner ℝ (Work.BoseB4.vec (labVec N k)) x)
          * Real.cos (inner ℝ (Work.BoseB4.vec (labVec N k')) x)) := by
      funext x
      rw [hPeval x, pow_two, Finset.sum_mul_sum]
      apply Finset.sum_congr rfl; intro k _
      apply Finset.sum_congr rfl; intro k' _
      ring
    rw [hfun]
    rw [integral_finsetSum (Finset.univ)
      (f := fun k x => ∑ k' : Lab N, c k * c k' *
        (Real.cos (inner ℝ (Work.BoseB4.vec (labVec N k)) x)
          * Real.cos (inner ℝ (Work.BoseB4.vec (labVec N k')) x)))
      (fun k _ => hInt _ (continuous_finsetSum _ (fun k' _ =>
        (continuous_const.mul continuous_const).mul ((hcoscont _).mul (hcoscont _)))))]
    rw [show (∑ k : Lab N, ∫ x in Work.BoseB4.unitCell, ∑ k' : Lab N, c k * c k' *
          (Real.cos (inner ℝ (Work.BoseB4.vec (labVec N k)) x)
            * Real.cos (inner ℝ (Work.BoseB4.vec (labVec N k')) x)))
        = ∑ k : Lab N, ∑ k' : Lab N, ∫ x in Work.BoseB4.unitCell, c k * c k' *
          (Real.cos (inner ℝ (Work.BoseB4.vec (labVec N k)) x)
            * Real.cos (inner ℝ (Work.BoseB4.vec (labVec N k')) x)) from by
      apply Finset.sum_congr rfl; intro k _
      exact integral_finsetSum (Finset.univ) (fun k' _ =>
        hInt _ ((continuous_const.mul continuous_const).mul ((hcoscont _).mul (hcoscont _))))]
    rw [show (∑ k : Lab N, ∑ k' : Lab N, ∫ x in Work.BoseB4.unitCell, c k * c k' *
          (Real.cos (inner ℝ (Work.BoseB4.vec (labVec N k)) x)
            * Real.cos (inner ℝ (Work.BoseB4.vec (labVec N k')) x)))
        = ∑ k : Lab N, ∑ k' : Lab N, c k * c k' *
          (((if labVec N k = labVec N k' then (1 : ℝ) else 0)
            + (if labVec N k = -(labVec N k') then (1 : ℝ) else 0)) / 2) from by
      apply Finset.sum_congr rfl; intro k _
      apply Finset.sum_congr rfl; intro k' _
      rw [integral_const_mul, hcos k k']]
    rw [hdelta]
  have hPcont : Continuous P := by
    change Continuous (fun x : EuclideanSpace ℝ (Fin 3) =>
      ∑ k : Lab N, c k * Real.cos (inner ℝ (Work.BoseB4.vec (labVec N k)) x))
    exact continuous_finsetSum _ (fun k _ => continuous_const.mul (hcoscont _))
  -- ### (3) the square expansion of the residual
  have hsq : ∫ x in Work.BoseB4.unitCell, ((Submission.BoseGases.chi x - P x) ^ 2)
      = 1 - 2 * (∑ k : Lab N, (c k) ^ 2) + ∑ k : Lab N, (c k) ^ 2 := by
    have hfun : (fun x => (Submission.BoseGases.chi x - P x) ^ 2)
        = fun x => ((Submission.BoseGases.chi x) ^ 2
            - 2 * (Submission.BoseGases.chi x * P x) + (P x) ^ 2) := by
      funext x; ring
    rw [hfun]
    have h1 : Integrable (fun x => (Submission.BoseGases.chi x) ^ 2
        - 2 * (Submission.BoseGases.chi x * P x)) (volume.restrict Work.BoseB4.unitCell) :=
      hInt _ ((hχc.pow 2).sub (continuous_const.mul (hχc.mul hPcont)))
    have h2 : Integrable (fun x => (P x) ^ 2) (volume.restrict Work.BoseB4.unitCell) :=
      hInt _ (hPcont.pow 2)
    have h3 : Integrable (fun x => (Submission.BoseGases.chi x) ^ 2)
        (volume.restrict Work.BoseB4.unitCell) := hInt _ (hχc.pow 2)
    have h4 : Integrable (fun x => 2 * (Submission.BoseGases.chi x * P x))
        (volume.restrict Work.BoseB4.unitCell) :=
      hInt _ (continuous_const.mul (hχc.mul hPcont))
    rw [integral_add h1 h2, integral_sub h3 h4, integral_const_mul, hχ2, hchiP, hPP]
  -- ### (4) the residual is nonnegative
  have hnn : 0 ≤ ∫ x in Work.BoseB4.unitCell, ((Submission.BoseGases.chi x - P x) ^ 2) :=
    integral_nonneg (fun x => sq_nonneg _)
  linarith

theorem sum_hatChi_sq_le (N : ℕ) :
    ∑ k : Work.BoseBoxFock.Lab N,
        (Work.BoseK15.corpusBox.hatChi (Work.BoseB4.vec (Work.BoseBoxFock.labVec N k))) ^ 2 ≤ 1 := by
  classical
  -- the cube label determines the lattice point
  have hinj : Function.Injective (labVec N) := fun a b h => by
    funext i
    exact ZMod.valMinAbs_inj.mp (congrFun h i)
  -- and the label map is odd, so `χ̂` (even) is invariant under the cube involution
  have heven : ∀ k : Lab N,
      Work.BoseK15.corpusBox.hatChi (Work.BoseB4.vec (labVec N (-k)))
        = Work.BoseK15.corpusBox.hatChi (Work.BoseB4.vec (labVec N k)) := by
    intro k
    rw [labVec_neg, vec_neg, Work.BoseB4.BoxData.hatChi_neg]
  refine sum_sq_le_of_cosData N
    (fun k => Work.BoseK15.corpusBox.hatChi (Work.BoseB4.vec (labVec N k)))
    (fun k k' => integral_unitCell_cos_cos (labVec N k) (labVec N k'))
    (fun k => integral_unitCell_chi_cos (Work.BoseB4.vec (labVec N k)))
    integral_unitCell_chi_sq ?_
  exact sum_pair_delta (labVec N) hinj (fun k => labVec_neg N k)
    (fun k => Work.BoseK15.corpusBox.hatChi (Work.BoseB4.vec (labVec N k))) heven

end Work.BoseBoxFock
