import Mathlib.Algebra.Order.Star.Real
import Mathlib.Analysis.Normed.Lp.MeasurableSpace
import Mathlib.Analysis.Real.Pi.Bounds
import Mathlib.MeasureTheory.Integral.Bochner.Set
import Mathlib.MeasureTheory.Measure.Haar.OfBasis
import Submission.Work.BoseRowsL.LatticeCoulomb.cellSumVsIntegral
import Submission.Work.BoseRowsL.LatticeCoulomb.kernelBoundsCore
import Submission.Work.BoseRowsL.LatticeCoulomb.latToolbox
import Submission.Work.BoseRowsL.LatticeCoulomb.latticeCellExpand
import Submission.Work.BoseRowsL.LatticeCoulomb.telescopeInner
-- PORT435-BEGIN (v4.35 isDefEq respectTransparency compat)
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- PORT435-END

/-!
# `Work.BoseBogFS.ZPKernel.Bound`

The normalised lattice-Coulomb kernel bound

`|Σ_{0<‖n‖≤R} cos(2π⟪n,z⟫)/‖n‖² − ∫_{‖q‖≤R} cos(2π⟪q,z⟫)/‖q‖²dq| ≤ C`, `‖z‖ ≤ 1/2`,

assembled from the corpus's proved cell machinery (`latticeCellExpand`, `cellSumVsIntegral`,
`kernelBoundsCore`, `ballInvSqBound`) and the two *telescoping* inputs `CosBound` (`(1−cos)·|A|`
bounded) and `SinBound` (`|Y + sin·A|` bounded).
-/

noncomputable section
open scoped Real BigOperators Topology
open MeasureTheory Metric

namespace Work.BoseBogFS

set_option autoImplicit false

abbrev E3 := Work.BoseRowsL.LatticeCoulomb.E3


/-- For `q` in the unit cell at the origin, `‖q‖ ≤ 1`. -/
lemma norm_le_one_of_mem_ucell_zero {q : E3}
    (hq : q ∈ Work.BoseRowsL.LatticeCoulomb.ucell (0 : Fin 3 → ℤ)) : ‖q‖ ≤ 1 := by
  have h2 : ‖q‖ ^ 2 ≤ (3 : ℝ) / 4 := by
    rw [EuclideanSpace.norm_sq_eq]
    calc ∑ i : Fin 3, ‖q.ofLp i‖ ^ 2 ≤ ∑ _i : Fin 3, ((1 / 2 : ℝ)) ^ 2 := by
          refine Finset.sum_le_sum (fun i _ => ?_)
          have hi : |q.ofLp i| ≤ 1 / 2 := by
            have h := hq i
            simp only [Work.BoseRowsL.LatticeCoulomb.ucell, Set.mem_setOf_eq] at h
            simpa using h
          rw [Real.norm_eq_abs]
          exact pow_le_pow_left₀ (abs_nonneg _) hi 2
      _ = 3 / 4 := by rw [Fin.sum_univ_three]; norm_num
  nlinarith [norm_nonneg q]

/-- **The first moment of the cell is `O(‖z‖)`**: `‖sigBullet z‖ ≤ 10‖z‖`. -/
lemma sigBullet_le' (z : E3) : ‖Work.BoseRowsL.LatticeCoulomb.sigBullet z‖ ≤ 10 * ‖z‖ := by
  have hvol : volume (Work.BoseRowsL.LatticeCoulomb.ucell (0 : Fin 3 → ℤ)) < ⊤ := by
    rw [Work.BoseRowsL.LatticeCoulomb.volume_ucell]; norm_num
  have h := norm_setIntegral_le_of_norm_le_const (μ := volume)
    (s := Work.BoseRowsL.LatticeCoulomb.ucell (0 : Fin 3 → ℤ))
    (f := fun q : E3 => (Real.sin (2 * Real.pi * inner ℝ q z)) • q) (C := 10 * ‖z‖) hvol ?_
  · rw [Measure.real_def, Work.BoseRowsL.LatticeCoulomb.volume_ucell, ENNReal.toReal_one,
      mul_one] at h
    simpa only [Work.BoseRowsL.LatticeCoulomb.sigBullet] using h
  · intro q hq
    rw [norm_smul, Real.norm_eq_abs]
    have h1 := Real.abs_sin_le_abs (x := 2 * Real.pi * inner ℝ q z)
    have h3 : ‖q‖ ≤ 1 := norm_le_one_of_mem_ucell_zero hq
    have h2 : |2 * Real.pi * inner ℝ q z| ≤ 2 * Real.pi * ‖z‖ := by
      have hi := abs_real_inner_le_norm q z
      have hpi : (0 : ℝ) ≤ 2 * Real.pi := by positivity
      have hmul : (2 * Real.pi) * |inner ℝ q z| ≤ (2 * Real.pi) * (‖q‖ * ‖z‖) :=
        mul_le_mul_of_nonneg_left hi hpi
      have hqz : ‖q‖ * ‖z‖ ≤ ‖z‖ := by
        simpa using mul_le_mul_of_nonneg_right h3 (norm_nonneg z)
      calc |2 * Real.pi * inner ℝ q z| = (2 * Real.pi) * |inner ℝ q z| := by
            rw [abs_mul, abs_of_nonneg hpi]
        _ ≤ (2 * Real.pi) * (‖q‖ * ‖z‖) := hmul
        _ ≤ (2 * Real.pi) * ‖z‖ := mul_le_mul_of_nonneg_left hqz hpi
    have h4 : 2 * Real.pi * ‖z‖ ≤ 10 * ‖z‖ := by nlinarith [Real.pi_lt_four, norm_nonneg z]
    nlinarith [h1, h2, h3, h4, abs_nonneg (2 * Real.pi * inner ℝ q z), norm_nonneg q]

/-- **The cosine telescoping input.**  `(1 − cos(2πz_j))·|Σ cos(2π⟪n,z⟫)/‖n‖²|` is bounded,
uniformly in the lattice ball `T` and in `z` with `‖z‖ ≤ 1/2`. -/
def CosBound : Prop :=
  ∀ (R : ℝ) (T : Finset (Fin 3 → ℤ)) (j : Fin 3) (z : E3),
    (∀ n ∈ T, n ≠ 0) → (∀ n ∈ T, ‖Work.BoseRowsL.LatticeCoulomb.nvec n‖ ≤ R) →
    (∀ n : Fin 3 → ℤ, n ≠ 0 → ‖Work.BoseRowsL.LatticeCoulomb.nvec n‖ ≤ R → n ∈ T) →
    ‖z‖ ≤ 1 / 2 →
      (1 - Real.cos (2 * Real.pi * z.ofLp j))
        * |∑ n ∈ T, Real.cos (2 * Real.pi
              * inner ℝ (Work.BoseRowsL.LatticeCoulomb.nvec n) z)
            / ‖Work.BoseRowsL.LatticeCoulomb.nvec n‖ ^ 2| ≤ 10 ^ 8

/-- **The sine telescoping input.**  `|Σ sin(2π⟪n,z⟫)(−2n_j/‖n‖⁴) + sin(2πz_j)·A|` is bounded,
uniformly in the lattice ball `T`, the direction `j` and `z` with `‖z‖ ≤ 1/2`. -/
def SinBound : Prop :=
  ∀ (R : ℝ) (T : Finset (Fin 3 → ℤ)) (j : Fin 3) (z : E3),
    (∀ n ∈ T, n ≠ 0) → (∀ n ∈ T, ‖Work.BoseRowsL.LatticeCoulomb.nvec n‖ ≤ R) →
    (∀ n : Fin 3 → ℤ, n ≠ 0 → ‖Work.BoseRowsL.LatticeCoulomb.nvec n‖ ≤ R → n ∈ T) →
    ‖z‖ ≤ 1 / 2 →
      |(∑ n ∈ T, Real.sin (2 * Real.pi * inner ℝ (Work.BoseRowsL.LatticeCoulomb.nvec n) z)
          * (-2 * (Work.BoseRowsL.LatticeCoulomb.nvec n).ofLp j
              / ‖Work.BoseRowsL.LatticeCoulomb.nvec n‖ ^ 4))
        + Real.sin (2 * Real.pi * z.ofLp j)
          * (∑ n ∈ T, Real.cos (2 * Real.pi
                * inner ℝ (Work.BoseRowsL.LatticeCoulomb.nvec n) z)
              / ‖Work.BoseRowsL.LatticeCoulomb.nvec n‖ ^ 2)| ≤ 10 ^ 8

/-- **The inner telescoping bound** `|Y + gam·A| ≤ 15·10⁸`, derived from `SinBound` by
decomposing `sigBullet z` and `gam z` in the coordinates of `E3`. -/
theorem innerBound_of (hsin : SinBound) (R : ℝ) (T : Finset (Fin 3 → ℤ))
    (z : E3) (h1 : ∀ n ∈ T, n ≠ 0)
    (h2 : ∀ n ∈ T, ‖Work.BoseRowsL.LatticeCoulomb.nvec n‖ ≤ R)
    (h4 : ∀ n : Fin 3 → ℤ, n ≠ 0 → ‖Work.BoseRowsL.LatticeCoulomb.nvec n‖ ≤ R → n ∈ T)
    (hz : ‖z‖ ≤ 1 / 2) :
    |(∑ n ∈ T, Real.sin (2 * Real.pi * inner ℝ (Work.BoseRowsL.LatticeCoulomb.nvec n) z)
        * (inner ℝ (Work.BoseRowsL.LatticeCoulomb.nvec n)
            (Work.BoseRowsL.LatticeCoulomb.sigBullet z)) * (-2 /
              ‖Work.BoseRowsL.LatticeCoulomb.nvec n‖ ^ 4))
      + Work.BoseRowsL.LatticeCoulomb.gam z
        * (∑ n ∈ T, Real.cos (2 * Real.pi
              * inner ℝ (Work.BoseRowsL.LatticeCoulomb.nvec n) z)
            / ‖Work.BoseRowsL.LatticeCoulomb.nvec n‖ ^ 2)| ≤ 15 * 10 ^ 8 := by
  classical
  set A : ℝ := ∑ n ∈ T, Real.cos (2 * Real.pi
        * inner ℝ (Work.BoseRowsL.LatticeCoulomb.nvec n) z)
      / ‖Work.BoseRowsL.LatticeCoulomb.nvec n‖ ^ 2 with hA
  set B : E3 := Work.BoseRowsL.LatticeCoulomb.sigBullet z with hB
  -- coordinate decompositions
  have hinner : ∀ n : Fin 3 → ℤ,
      inner ℝ (Work.BoseRowsL.LatticeCoulomb.nvec n) B
        = ∑ i : Fin 3, ((n i : ℝ)) * B.ofLp i := by
    intro n
    rw [Work.BoseRowsL.LatticeCoulomb.inner_nvec_eq_sum]
  have hgam : Work.BoseRowsL.LatticeCoulomb.gam z
      = ∑ i : Fin 3, B.ofLp i * Real.sin (2 * Real.pi * z.ofLp i) := by
    rw [Work.BoseRowsL.LatticeCoulomb.gam]
    have : inner ℝ B (Work.BoseRowsL.LatticeCoulomb.sinVec z)
        = ∑ i : Fin 3, B.ofLp i * (Work.BoseRowsL.LatticeCoulomb.sinVec z).ofLp i := by
      rw [PiLp.inner_apply]
      exact Finset.sum_congr rfl (fun i _ => by rw [Real.inner_apply, mul_comm])
    rw [this]
    exact Finset.sum_congr rfl (fun i _ => by rw [Work.BoseRowsL.LatticeCoulomb.sinVec_apply])
  have hsinN : ∀ n ∈ T, Real.sin (2 * Real.pi
        * inner ℝ (Work.BoseRowsL.LatticeCoulomb.nvec n) z)
        * (inner ℝ (Work.BoseRowsL.LatticeCoulomb.nvec n) B)
        * (-2 / ‖Work.BoseRowsL.LatticeCoulomb.nvec n‖ ^ 4)
      = ∑ i : Fin 3, B.ofLp i * (Real.sin (2 * Real.pi
            * inner ℝ (Work.BoseRowsL.LatticeCoulomb.nvec n) z)
          * ((Work.BoseRowsL.LatticeCoulomb.nvec n).ofLp i)
          * (-2 / ‖Work.BoseRowsL.LatticeCoulomb.nvec n‖ ^ 4)) := by
    intro n _
    rw [hinner n, Finset.mul_sum, Finset.sum_mul]
    refine Finset.sum_congr rfl (fun i _ => ?_)
    rw [Work.BoseRowsL.LatticeCoulomb.nvec_apply]
    ring
  have hsplit : (∑ n ∈ T, Real.sin (2 * Real.pi
        * inner ℝ (Work.BoseRowsL.LatticeCoulomb.nvec n) z)
        * (inner ℝ (Work.BoseRowsL.LatticeCoulomb.nvec n) B)
        * (-2 / ‖Work.BoseRowsL.LatticeCoulomb.nvec n‖ ^ 4))
      + Work.BoseRowsL.LatticeCoulomb.gam z * A
      = ∑ i : Fin 3, B.ofLp i *
          ((∑ n ∈ T, Real.sin (2 * Real.pi
                * inner ℝ (Work.BoseRowsL.LatticeCoulomb.nvec n) z)
              * ((Work.BoseRowsL.LatticeCoulomb.nvec n).ofLp i)
              * (-2 / ‖Work.BoseRowsL.LatticeCoulomb.nvec n‖ ^ 4))
            + Real.sin (2 * Real.pi * z.ofLp i) * A) := by
    rw [hgam, Finset.sum_mul]
    have hL : (∑ n ∈ T, Real.sin (2 * Real.pi
          * inner ℝ (Work.BoseRowsL.LatticeCoulomb.nvec n) z)
          * (inner ℝ (Work.BoseRowsL.LatticeCoulomb.nvec n) B)
          * (-2 / ‖Work.BoseRowsL.LatticeCoulomb.nvec n‖ ^ 4))
        = ∑ i : Fin 3, B.ofLp i *
            (∑ n ∈ T, Real.sin (2 * Real.pi
                  * inner ℝ (Work.BoseRowsL.LatticeCoulomb.nvec n) z)
                * ((Work.BoseRowsL.LatticeCoulomb.nvec n).ofLp i)
                * (-2 / ‖Work.BoseRowsL.LatticeCoulomb.nvec n‖ ^ 4)) := by
      rw [Finset.sum_congr rfl hsinN, Finset.sum_comm]
      exact Finset.sum_congr rfl (fun i _ => by rw [Finset.mul_sum])
    rw [hL, ← Finset.sum_add_distrib]
    exact Finset.sum_congr rfl (fun i _ => by ring)
  rw [hsplit]
  have hterm : ∀ i : Fin 3, |B.ofLp i| ≤ 10 * ‖z‖ := by
    intro i
    have h := PiLp.norm_apply_le B i
    rw [Real.norm_eq_abs] at h
    exact le_trans h (sigBullet_le' z)
  have hstep : ∀ i : Fin 3,
      |B.ofLp i *
        ((∑ n ∈ T, Real.sin (2 * Real.pi
              * inner ℝ (Work.BoseRowsL.LatticeCoulomb.nvec n) z)
            * ((Work.BoseRowsL.LatticeCoulomb.nvec n).ofLp i)
            * (-2 / ‖Work.BoseRowsL.LatticeCoulomb.nvec n‖ ^ 4))
          + Real.sin (2 * Real.pi * z.ofLp i) * A)| ≤ (10 * ‖z‖) * 10 ^ 8 := by
    intro i
    rw [abs_mul]
    have hS := hsin R T i z h1 h2 h4 hz
    have hkey : |(∑ n ∈ T, Real.sin (2 * Real.pi
              * inner ℝ (Work.BoseRowsL.LatticeCoulomb.nvec n) z)
              * ((Work.BoseRowsL.LatticeCoulomb.nvec n).ofLp i)
              * (-2 / ‖Work.BoseRowsL.LatticeCoulomb.nvec n‖ ^ 4))
            + Real.sin (2 * Real.pi * z.ofLp i) * A| ≤ 10 ^ 8 := by
      have heq : (∑ n ∈ T, Real.sin (2 * Real.pi
                * inner ℝ (Work.BoseRowsL.LatticeCoulomb.nvec n) z)
                * ((Work.BoseRowsL.LatticeCoulomb.nvec n).ofLp i)
                * (-2 / ‖Work.BoseRowsL.LatticeCoulomb.nvec n‖ ^ 4))
              = ∑ n ∈ T, Real.sin (2 * Real.pi
                * inner ℝ (Work.BoseRowsL.LatticeCoulomb.nvec n) z)
                * (-2 * (Work.BoseRowsL.LatticeCoulomb.nvec n).ofLp i
                    / ‖Work.BoseRowsL.LatticeCoulomb.nvec n‖ ^ 4) :=
            Finset.sum_congr rfl (fun n _ => by ring)
      rw [heq, hA]
      exact hS
    exact mul_le_mul (hterm i) hkey (abs_nonneg _) (by positivity)
  have htri : |∑ i : Fin 3, B.ofLp i *
          ((∑ n ∈ T, Real.sin (2 * Real.pi
                * inner ℝ (Work.BoseRowsL.LatticeCoulomb.nvec n) z)
              * ((Work.BoseRowsL.LatticeCoulomb.nvec n).ofLp i)
              * (-2 / ‖Work.BoseRowsL.LatticeCoulomb.nvec n‖ ^ 4))
            + Real.sin (2 * Real.pi * z.ofLp i) * A)|
      ≤ ∑ i : Fin 3, |B.ofLp i *
          ((∑ n ∈ T, Real.sin (2 * Real.pi
                * inner ℝ (Work.BoseRowsL.LatticeCoulomb.nvec n) z)
              * ((Work.BoseRowsL.LatticeCoulomb.nvec n).ofLp i)
              * (-2 / ‖Work.BoseRowsL.LatticeCoulomb.nvec n‖ ^ 4))
            + Real.sin (2 * Real.pi * z.ofLp i) * A)| :=
        Finset.abs_sum_le_sum_abs _ _
  have hsum : (∑ i : Fin 3, |B.ofLp i *
          ((∑ n ∈ T, Real.sin (2 * Real.pi
                * inner ℝ (Work.BoseRowsL.LatticeCoulomb.nvec n) z)
              * ((Work.BoseRowsL.LatticeCoulomb.nvec n).ofLp i)
              * (-2 / ‖Work.BoseRowsL.LatticeCoulomb.nvec n‖ ^ 4))
            + Real.sin (2 * Real.pi * z.ofLp i) * A)|)
      ≤ ∑ _i : Fin 3, (10 * ‖z‖) * 10 ^ 8 :=
        Finset.sum_le_sum (fun i _ => hstep i)
  have hval : (∑ _i : Fin 3, (10 * ‖z‖) * 10 ^ 8 : ℝ) = 3 * ((10 * ‖z‖) * 10 ^ 8) := by
    rw [Fin.sum_univ_three]
    ring
  have h3 : 3 * ((10 * ‖z‖) * 10 ^ 8) ≤ 15 * 10 ^ 8 := by nlinarith [hz, norm_nonneg z]
  exact le_trans htri (le_trans hsum (le_trans (le_of_eq hval) h3))

/-- **The normalised lattice-Coulomb kernel bound** (with a very generous constant),
from the two telescoping inputs. -/
theorem kernelBound_of (hcos : CosBound) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ (R : ℝ) (T : Finset (Fin 3 → ℤ)) (z : E3),
      1 ≤ R → (∀ n ∈ T, n ≠ 0) → (∀ n ∈ T, ‖Work.BoseRowsL.LatticeCoulomb.nvec n‖ ≤ R) →
      (∀ n : Fin 3 → ℤ, n ≠ 0 → ‖Work.BoseRowsL.LatticeCoulomb.nvec n‖ ≤ R → n ∈ T) →
      ‖z‖ ≤ 1 / 2 →
      |(∑ n ∈ T, Real.cos (2 * Real.pi
            * inner ℝ (Work.BoseRowsL.LatticeCoulomb.nvec n) z)
          / ‖Work.BoseRowsL.LatticeCoulomb.nvec n‖ ^ 2)
        - ∫ q in Metric.closedBall 0 R,
            Real.cos (2 * Real.pi * inner ℝ q z) / ‖q‖ ^ 2| ≤ C := by
  refine ⟨10 ^ 15, by norm_num, ?_⟩
  intro R T z hR h1 h2 h4 hz
  set A : ℝ := ∑ n ∈ T, Real.cos (2 * Real.pi
        * inner ℝ (Work.BoseRowsL.LatticeCoulomb.nvec n) z)
      / ‖Work.BoseRowsL.LatticeCoulomb.nvec n‖ ^ 2 with hA
  set B : ℝ := ∑ n ∈ T, ∫ q in Work.BoseRowsL.LatticeCoulomb.ucell n,
      Real.cos (2 * Real.pi * inner ℝ q z) / ‖q‖ ^ 2 with hB
  set I : ℝ := ∫ q in Metric.closedBall 0 R,
      Real.cos (2 * Real.pi * inner ℝ q z) / ‖q‖ ^ 2 with hI
  set Y : ℝ := ∑ n ∈ T, Real.sin (2 * Real.pi
        * inner ℝ (Work.BoseRowsL.LatticeCoulomb.nvec n) z)
      * (inner ℝ (Work.BoseRowsL.LatticeCoulomb.nvec n)
          (Work.BoseRowsL.LatticeCoulomb.sigBullet z))
      * (-2 / ‖Work.BoseRowsL.LatticeCoulomb.nvec n‖ ^ 4) with hY
  obtain ⟨-, -, hσb, hγb, -, -, j, hj⟩ := Work.BoseRowsL.LatticeCoulomb.kernelBoundsCore z hz
  have hcell := Work.BoseRowsL.LatticeCoulomb.latticeCellExpand T z h1
  have hcell' : |(A - B) - ((1 - Work.BoseRowsL.LatticeCoulomb.sigma z) * A + Y)| ≤ 10000 := by
    rw [hA, hB, hY, ← Finset.sum_sub_distrib]
    exact hcell
  have hcvs := Work.BoseRowsL.LatticeCoulomb.cellSumVsIntegral R T z hR hz h1 h2 h4
  have hcvs' : |B - I| ≤ 100 := by rw [hB, hI]; exact hcvs
  have hin : |Y + Work.BoseRowsL.LatticeCoulomb.gam z * A| ≤ 1000 := by
    rw [hY, hA]
    exact Work.BoseRowsL.LatticeCoulomb.telescopeInner R T z h1 h2 h4
  have hcosj := hcos R T j z h1 h2 h4 hz
  have hzj : ‖z‖ ^ 2 ≤ 6 * (1 - Real.cos (2 * Real.pi * z.ofLp j)) := hj
  have hAabs : ‖z‖ ^ 2 * |A| ≤ 6 * 10 ^ 8 := by
    have hpos : 0 ≤ 1 - Real.cos (2 * Real.pi * z.ofLp j) := by
      linarith [Real.cos_le_one (2 * Real.pi * z.ofLp j)]
    have := mul_le_mul_of_nonneg_right hzj (abs_nonneg A)
    linarith [hcosj]
  have hsigA : |(1 - Work.BoseRowsL.LatticeCoulomb.sigma z
        - Work.BoseRowsL.LatticeCoulomb.gam z) * A| ≤ 150 * (‖z‖ ^ 2 * |A|) := by
    rw [abs_mul]
    have h1' : |1 - Work.BoseRowsL.LatticeCoulomb.sigma z
        - Work.BoseRowsL.LatticeCoulomb.gam z|
        ≤ |1 - Work.BoseRowsL.LatticeCoulomb.sigma z|
          + |Work.BoseRowsL.LatticeCoulomb.gam z| := by
      have := abs_sub_le (1 - Work.BoseRowsL.LatticeCoulomb.sigma z) 0
        (Work.BoseRowsL.LatticeCoulomb.gam z)
      simpa using this
    have h2' : |1 - Work.BoseRowsL.LatticeCoulomb.sigma z|
        + |Work.BoseRowsL.LatticeCoulomb.gam z| ≤ 150 * ‖z‖ ^ 2 := by
      linarith [hσb, hγb]
    have h3' : 0 ≤ |A| := abs_nonneg A
    nlinarith [h1', h2', h3', sq_nonneg ‖z‖]
  have hid : A - I = ((A - B) - ((1 - Work.BoseRowsL.LatticeCoulomb.sigma z) * A + Y))
      + (B - I) + ((1 - Work.BoseRowsL.LatticeCoulomb.sigma z
          - Work.BoseRowsL.LatticeCoulomb.gam z) * A)
      + (Y + Work.BoseRowsL.LatticeCoulomb.gam z * A) := by ring
  rw [hA, hI, hid]
  calc |((A - B) - ((1 - Work.BoseRowsL.LatticeCoulomb.sigma z) * A + Y)) + (B - I)
        + ((1 - Work.BoseRowsL.LatticeCoulomb.sigma z - Work.BoseRowsL.LatticeCoulomb.gam z) * A)
        + (Y + Work.BoseRowsL.LatticeCoulomb.gam z * A)|
      ≤ |(A - B) - ((1 - Work.BoseRowsL.LatticeCoulomb.sigma z) * A + Y)| + |B - I|
        + |(1 - Work.BoseRowsL.LatticeCoulomb.sigma z - Work.BoseRowsL.LatticeCoulomb.gam z) * A|
        + |Y + Work.BoseRowsL.LatticeCoulomb.gam z * A| := by
        have ha := abs_add_le (((A - B) - ((1 - Work.BoseRowsL.LatticeCoulomb.sigma z) * A + Y))
          + (B - I) + ((1 - Work.BoseRowsL.LatticeCoulomb.sigma z
              - Work.BoseRowsL.LatticeCoulomb.gam z) * A))
          (Y + Work.BoseRowsL.LatticeCoulomb.gam z * A)
        have hb := abs_add_le (((A - B) - ((1 - Work.BoseRowsL.LatticeCoulomb.sigma z) * A + Y))
          + (B - I)) ((1 - Work.BoseRowsL.LatticeCoulomb.sigma z
              - Work.BoseRowsL.LatticeCoulomb.gam z) * A)
        have hc := abs_add_le ((A - B) - ((1 - Work.BoseRowsL.LatticeCoulomb.sigma z) * A + Y))
          (B - I)
        linarith [abs_nonneg (Y + Work.BoseRowsL.LatticeCoulomb.gam z * A),
          abs_nonneg ((1 - Work.BoseRowsL.LatticeCoulomb.sigma z
              - Work.BoseRowsL.LatticeCoulomb.gam z) * A),
          abs_nonneg (B - I),
          abs_nonneg ((A - B) - ((1 - Work.BoseRowsL.LatticeCoulomb.sigma z) * A + Y))]
    _ ≤ 10000 + 100 + 150 * (6 * 10 ^ 8) + 1000 := by
        linarith only [hcell', hcvs', hsigA, hAabs, hin]
    _ ≤ 10 ^ 15 := by norm_num

end Work.BoseBogFS
