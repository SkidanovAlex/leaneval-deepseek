import Mathlib.Analysis.Normed.Lp.MeasurableSpace
import Mathlib.MeasureTheory.Integral.Bochner.Basic
import Mathlib.MeasureTheory.Measure.Haar.OfBasis
import Submission.Work.BoseBoxFock.Middle_channels
-- PORT435-BEGIN (v4.35 isDefEq respectTransparency compat)
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- PORT435-END

namespace Work.BoseBoxFock

noncomputable section

open scoped BigOperators
open MeasureTheory

/-- Splitting a doubly indexed sum into its four parts (the `A - B - C + D` rearrangement of the
four channels of `summand_four_split`). -/
lemma meorf_sum_four {ι κ : Type*} [DecidableEq ι] [DecidableEq κ] (s : Finset ι)
    (t : Finset κ) (g1 g2 g3 g4 : ι → κ → ℂ) :
    (∑ i ∈ s, ∑ j ∈ t, (g1 i j - g2 i j - g3 i j + g4 i j))
      = (∑ i ∈ s, ∑ j ∈ t, g1 i j) - (∑ i ∈ s, ∑ j ∈ t, g2 i j)
        - (∑ i ∈ s, ∑ j ∈ t, g3 i j) + (∑ i ∈ s, ∑ j ∈ t, g4 i j) := by
  simp only [Finset.sum_sub_distrib, Finset.sum_add_distrib]

/-- Pulling the constant `((√ℓ³)⁻¹)³` out of a doubly indexed sum. -/
lemma meorf_sum_const_mul {ι κ : Type*} [DecidableEq ι] [DecidableEq κ] (s : Finset ι)
    (t : Finset κ) (c : ℂ) (f : ι → κ → ℂ) :
    (∑ i ∈ s, ∑ j ∈ t, c * f i j) = c * (∑ i ∈ s, ∑ j ∈ t, f i j) := by
  rw [Finset.mul_sum]
  refine Finset.sum_congr rfl fun i _ => ?_
  rw [Finset.mul_sum]

theorem Middle_eq_of_rows_fixed (v : EuclideanSpace ℝ (Fin 3) → ℝ) (h : Work.UBB.ScatSol v)
    (fc fu : Work.BoseBoxFix.LowCut) (μ : ℝ) (N : ℕ) (x y u : EuclideanSpace ℝ (Fin 3))
    (hA : Work.BoseBoxFock.ChA v h fc fu μ N y x u
      = Work.BoseBoxFock.Ksfr v fc μ N (x - y)
          * ((Work.BoseK15.corpusBox.chiLam (Work.BoseBoxFock.ellH v μ) y : ℝ) : ℂ)
          * Work.BoseK15.corpusBox.thetaFun (Work.BoseBoxFock.ellH v μ) x
          * ((Work.BoseK15.corpusBox.chiLam (Work.BoseBoxFock.ellH v μ) u : ℝ) : ℂ)
          * Work.BoseBoxFock.Kfr v h μ fu N (y - u))
    (hB : Work.BoseBoxFock.ChB v h fc fu μ N y x u
      = Work.BoseBoxFock.Ksfr v fc μ N (x - y)
          * ((Work.BoseK15.corpusBox.chiLam (Work.BoseBoxFock.ellH v μ) y : ℝ) : ℂ)
          * Work.BoseK15.corpusBox.thetaFun (Work.BoseBoxFock.ellH v μ) x
          * Work.BoseK15.corpusBox.thetaFun (Work.BoseBoxFock.ellH v μ) u
          * Work.BoseBoxFock.Kχfr v h μ fu N y)
    (hC : Work.BoseBoxFock.ChC v h fc fu μ N y x u
      = Work.BoseK15.corpusBox.thetaFun (Work.BoseBoxFock.ellH v μ) y
          * Work.BoseK15.corpusBox.thetaFun (Work.BoseBoxFock.ellH v μ) x
          * ((Work.BoseK15.corpusBox.chiLam (Work.BoseBoxFock.ellH v μ) u : ℝ) : ℂ)
          * (((Work.BoseBoxFock.ellH v μ) ^ (-(3 : ℤ)) : ℝ) : ℂ)
          * (∫ w : EuclideanSpace ℝ (Fin 3),
              ((Work.BoseK15.corpusBox.chiLam (Work.BoseBoxFock.ellH v μ) w : ℝ) : ℂ)
              * Work.BoseBoxFock.Ksfr v fc μ N (x + w)
              * Work.BoseBoxFock.Kfr v h μ fu N (u + w)))
    (hD : Work.BoseBoxFock.ChD v h fc fu μ N y x u
      = Work.BoseK15.corpusBox.thetaFun (Work.BoseBoxFock.ellH v μ) y
          * Work.BoseK15.corpusBox.thetaFun (Work.BoseBoxFock.ellH v μ) x
          * Work.BoseK15.corpusBox.thetaFun (Work.BoseBoxFock.ellH v μ) u
          * (((Work.BoseBoxFock.ellH v μ) ^ (-(3 : ℤ)) : ℝ) : ℂ)
          * (∫ w : EuclideanSpace ℝ (Fin 3),
              ((Work.BoseK15.corpusBox.chiLam (Work.BoseBoxFock.ellH v μ) w : ℝ) : ℂ)
              * Work.BoseBoxFock.Ksfr v fc μ N (x + w)
              * Work.BoseBoxFock.Kχfr v h μ fu N w)) :
    Work.BoseBoxFock.Middle v h fc fu μ N x y u
      = (((Work.BoseBoxFock.ellH v μ) ^ (-(9 / 2 : ℝ)) : ℝ) : ℂ) *
        ( Work.BoseBoxFock.Ksfr v fc μ N (x - y)
            * ((Work.BoseK15.corpusBox.chiLam (Work.BoseBoxFock.ellH v μ) y : ℝ) : ℂ)
            * Work.BoseK15.corpusBox.thetaFun (Work.BoseBoxFock.ellH v μ) x
            * ((Work.BoseK15.corpusBox.chiLam (Work.BoseBoxFock.ellH v μ) u : ℝ) : ℂ)
            * Work.BoseBoxFock.Kfr v h μ fu N (y - u)
        - Work.BoseBoxFock.Ksfr v fc μ N (x - y)
            * ((Work.BoseK15.corpusBox.chiLam (Work.BoseBoxFock.ellH v μ) y : ℝ) : ℂ)
            * Work.BoseK15.corpusBox.thetaFun (Work.BoseBoxFock.ellH v μ) x
            * Work.BoseK15.corpusBox.thetaFun (Work.BoseBoxFock.ellH v μ) u
            * Work.BoseBoxFock.Kχfr v h μ fu N y
        - Work.BoseK15.corpusBox.thetaFun (Work.BoseBoxFock.ellH v μ) y
            * Work.BoseK15.corpusBox.thetaFun (Work.BoseBoxFock.ellH v μ) x
            * ((Work.BoseK15.corpusBox.chiLam (Work.BoseBoxFock.ellH v μ) u : ℝ) : ℂ)
            * (((Work.BoseBoxFock.ellH v μ) ^ (-(3 : ℤ)) : ℝ) : ℂ)
            * (∫ w : EuclideanSpace ℝ (Fin 3),
                ((Work.BoseK15.corpusBox.chiLam (Work.BoseBoxFock.ellH v μ) w : ℝ) : ℂ)
                * Work.BoseBoxFock.Ksfr v fc μ N (x + w)
                * Work.BoseBoxFock.Kfr v h μ fu N (u + w))
        + Work.BoseK15.corpusBox.thetaFun (Work.BoseBoxFock.ellH v μ) y
            * Work.BoseK15.corpusBox.thetaFun (Work.BoseBoxFock.ellH v μ) x
            * Work.BoseK15.corpusBox.thetaFun (Work.BoseBoxFock.ellH v μ) u
            * (((Work.BoseBoxFock.ellH v μ) ^ (-(3 : ℤ)) : ℝ) : ℂ)
            * (∫ w : EuclideanSpace ℝ (Fin 3),
                ((Work.BoseK15.corpusBox.chiLam (Work.BoseBoxFock.ellH v μ) w : ℝ) : ℂ)
                * Work.BoseBoxFock.Ksfr v fc μ N (x + w)
                * Work.BoseBoxFock.Kχfr v h μ fu N w)) := by
  -- `(((√(ℓ³))⁻¹)³) = ↑(ℓ^{-9/2})`
  have hA3 : ((((Real.sqrt ((ellH v μ) ^ 3))⁻¹ : ℝ) : ℂ)) ^ 3
      = (((ellH v μ) ^ (-(9 / 2 : ℝ)) : ℝ) : ℂ) := by
    rw [← Complex.ofReal_pow, inv_sqrt_cube (ellH_pos v μ)]
  -- unfold `Middle` and apply the four-channel algebraic split summand by summand
  have h1 : Middle v h fc fu μ N x y u
      = ∑ s ∈ Work.BoseB7.excited (Lab N), ∑ k ∈ Work.BoseB7.excited (Lab N),
          ((fLh v fc μ N s * W1h v h μ fu N k : ℝ) : ℂ)
            * (((((Real.sqrt ((ellH v μ) ^ 3))⁻¹ : ℝ) : ℂ)) ^ 3
                * (chsA v h fc fu μ N y x u s k - chsB v h fc fu μ N y x u s k
                  - chsC v h fc fu μ N y x u s k + chsD v h fc fu μ N y x u s k)) := by
    rw [Middle]
    refine Finset.sum_congr rfl fun s _ => Finset.sum_congr rfl fun k _ => ?_
    have hre : ((fLh v fc μ N s * W1h v h μ fu N k : ℝ) : ℂ)
          * star (pinQ v μ N (s - k) y) * pinTheta v μ N s x * star (pinQ v μ N k u)
        = ((fLh v fc μ N s * W1h v h μ fu N k : ℝ) : ℂ)
          * (star (pinQ v μ N (s - k) y) * pinTheta v μ N s x * star (pinQ v μ N k u)) := by
      ring
    rw [hre, Complex.star_def, summand_four_split]
    rfl
  -- distribute the doubly indexed sum over the four channels and pull out the constant
  have h2 : (∑ s ∈ Work.BoseB7.excited (Lab N), ∑ k ∈ Work.BoseB7.excited (Lab N),
          ((fLh v fc μ N s * W1h v h μ fu N k : ℝ) : ℂ)
            * (((((Real.sqrt ((ellH v μ) ^ 3))⁻¹ : ℝ) : ℂ)) ^ 3
                * (chsA v h fc fu μ N y x u s k - chsB v h fc fu μ N y x u s k
                  - chsC v h fc fu μ N y x u s k + chsD v h fc fu μ N y x u s k)))
      = ((((Real.sqrt ((ellH v μ) ^ 3))⁻¹ : ℝ) : ℂ)) ^ 3
        * (ChA v h fc fu μ N y x u - ChB v h fc fu μ N y x u
            - ChC v h fc fu μ N y x u + ChD v h fc fu μ N y x u) := by
    have h3 : (∑ s ∈ Work.BoseB7.excited (Lab N), ∑ k ∈ Work.BoseB7.excited (Lab N),
          ((fLh v fc μ N s * W1h v h μ fu N k : ℝ) : ℂ)
            * (((((Real.sqrt ((ellH v μ) ^ 3))⁻¹ : ℝ) : ℂ)) ^ 3
                * (chsA v h fc fu μ N y x u s k - chsB v h fc fu μ N y x u s k
                  - chsC v h fc fu μ N y x u s k + chsD v h fc fu μ N y x u s k)))
        = ∑ s ∈ Work.BoseB7.excited (Lab N), ∑ k ∈ Work.BoseB7.excited (Lab N),
          (((((Real.sqrt ((ellH v μ) ^ 3))⁻¹ : ℝ) : ℂ)) ^ 3
              * (((fLh v fc μ N s * W1h v h μ fu N k : ℝ) : ℂ) * chsA v h fc fu μ N y x u s k)
            - ((((Real.sqrt ((ellH v μ) ^ 3))⁻¹ : ℝ) : ℂ)) ^ 3
              * (((fLh v fc μ N s * W1h v h μ fu N k : ℝ) : ℂ) * chsB v h fc fu μ N y x u s k)
            - ((((Real.sqrt ((ellH v μ) ^ 3))⁻¹ : ℝ) : ℂ)) ^ 3
              * (((fLh v fc μ N s * W1h v h μ fu N k : ℝ) : ℂ) * chsC v h fc fu μ N y x u s k)
            + ((((Real.sqrt ((ellH v μ) ^ 3))⁻¹ : ℝ) : ℂ)) ^ 3
              * (((fLh v fc μ N s * W1h v h μ fu N k : ℝ) : ℂ) * chsD v h fc fu μ N y x u s k)) := by
      refine Finset.sum_congr rfl fun s _ => Finset.sum_congr rfl fun k _ => ?_
      ring
    rw [h3, meorf_sum_four, meorf_sum_const_mul, meorf_sum_const_mul,
      meorf_sum_const_mul, meorf_sum_const_mul]
    simp only [ChA, ChB, ChC, ChD]
    ring
  -- feed in the four channel evaluations and the coefficient identity
  rw [h1, h2, hA, hB, hC, hD, hA3]

end

end Work.BoseBoxFock
