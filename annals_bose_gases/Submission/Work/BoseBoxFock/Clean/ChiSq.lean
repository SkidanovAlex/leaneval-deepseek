import Mathlib.Data.ZMod.ValMinAbs
import Mathlib.Algebra.Order.Star.Real
import Mathlib.Analysis.Normed.Lp.MeasurableSpace
import Mathlib.MeasureTheory.Integral.Bochner.Set
import Mathlib.MeasureTheory.Measure.Haar.OfBasis
import Submission.Work.BoseBoxFock.chi_sq_bounds
import Submission.Work.BoseBoxFock.sum_hatChi_sq_le
-- PORT435-BEGIN (v4.35 isDefEq respectTransparency compat)
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- PORT435-END

/-!
# `Submission/Work/BoseBoxFock/Clean/ChiSq.lean`

**Why this module exists.**  The honest Bessel bundle (`honestEnvBesselCorrected`) needs the
lattice ℓ²-bound `∑_k χ̂²(p_k)² ≤ 48/π` (`Submission/Work/BoseBoxFock/sum_hatChiSq_sq_le.lean`),
but that module imports `Submission.Work.BoseFixR.FarKernelRowsB` — whose module imports
`Submission.Work.BoseGateFS.GateHonest` and `Submission.Work.BoseFixR.RB5FSFixAux`, two modules
that (after the interface change `F9`, `CloseCond` → `CloseCondFS`) no longer compile, so the
whole cone is unloadable.

This file collects the pieces of that proof that do **not** need the broken cone:

* `unitCell_chiSq_cos`, `BesselUnitCell` — verbatim copies of the two lemmas of
  `FarKernelRowsB` that the ℓ²-row uses (the `Work.BoseFixR` versions; `RB5FSFixAux`/`ChiPin`
  are not used by their proofs);
* `unitCell_chi_pow4_le_48`, `sum_hatChiSq_sq_le` — verbatim copies of
  `Submission/Work/BoseBoxFock/sum_hatChiSq_sq_le.lean` with the `FarKernelRowsB` import
  replaced by the copies above.

Everything is re-scoped to `Work.BoseBoxFock.Clean`.  Nothing new is proved here.
-/

namespace Work.BoseBoxFock.Clean

open MeasureTheory

set_option autoImplicit false

/-- `χ̂²(p) = ∫_{cell} χ² cos⟪p,·⟫`: the corpus `χ` vanishes off the unit cell. -/
theorem unitCell_chiSq_cos (p : EuclideanSpace ℝ (Fin 3)) :
    ∫ x in Work.BoseB4.unitCell, (Submission.BoseGases.chi x) ^ 2 * Real.cos (inner ℝ p x)
      = Work.BoseK15.corpusBox.hatChiSq p := by
  rw [Work.BoseB4.BoxData.hatChiSq]
  rw [MeasureTheory.setIntegral_eq_integral_of_forall_compl_eq_zero]
  · simp
  · intro x hx
    have h0 : Submission.BoseGases.chi x = 0 := by
      by_contra h
      exact hx (Work.BoseK15.chi_support_subset_unitCell (Function.mem_support.mpr h))
    rw [h0]
    simp

/-- **Bessel on the unit cell.**  For a continuous `g` and the label cube `Lab N`,
`∑_k (∫_{cell} g cos⟪p_k,·⟫)² ≤ ∫_{cell} g²`.

Proof: with `c_k = ∫_{cell} g cos_k` and `P = ∑_k c_k cos_k`, one has `∫_{cell} g·P = ∑_k c_k²`
(the pairing identity), `∫_{cell} P² = ∑_k c_k²` (the `cos`-orthogonality `(δ + δ)/2` collapsed
by `sum_pair_delta`, using that `k ↦ c_k` is even under `k ↦ -k`), and `∫_{cell} g² = ∫_{cell} g²`;
hence `0 ≤ ∫_{cell} (g − P)² = ∫_{cell} g² − ∑_k c_k²`. -/
theorem BesselUnitCell (N : ℕ) (g : EuclideanSpace ℝ (Fin 3) → ℝ) (hg : Continuous g) :
    (∑ k : Lab N,
        (∫ x in Work.BoseB4.unitCell,
          g x * Real.cos (inner ℝ (Work.BoseB4.vec (labVec N k)) x)) ^ 2)
      ≤ ∫ x in Work.BoseB4.unitCell, (g x) ^ 2 := by
  classical
  let c : Lab N → ℝ := fun k => ∫ x in Work.BoseB4.unitCell,
    g x * Real.cos (inner ℝ (Work.BoseB4.vec (labVec N k)) x)
  change (∑ k : Lab N, (c k) ^ 2) ≤ ∫ x in Work.BoseB4.unitCell, (g x) ^ 2
  have hc : ∀ k : Lab N, (∫ x in Work.BoseB4.unitCell,
      g x * Real.cos (inner ℝ (Work.BoseB4.vec (labVec N k)) x)) = c k := fun k => rfl
  -- the label map is injective and odd, and `c` is even under the cube involution
  have hinj : Function.Injective (labVec N) := fun a b h => by
    funext i
    exact ZMod.valMinAbs_inj.mp (congrFun h i)
  have heven : ∀ k : Lab N, c (-k) = c k := by
    intro k
    show (∫ x in Work.BoseB4.unitCell,
        g x * Real.cos (inner ℝ (Work.BoseB4.vec (labVec N (-k))) x))
      = ∫ x in Work.BoseB4.unitCell,
        g x * Real.cos (inner ℝ (Work.BoseB4.vec (labVec N k)) x)
    rw [labVec_neg]
    simp only [vec_neg, inner_neg_left, Real.cos_neg]
  have hcos : ∀ k k' : Lab N,
      ∫ x in Work.BoseB4.unitCell,
          Real.cos (inner ℝ (Work.BoseB4.vec (labVec N k)) x)
            * Real.cos (inner ℝ (Work.BoseB4.vec (labVec N k')) x)
        = ((if labVec N k = labVec N k' then (1 : ℝ) else 0)
            + (if labVec N k = -(labVec N k') then (1 : ℝ) else 0)) / 2 :=
    fun k k' => Work.BoseBoxFock.integral_unitCell_cos_cos (labVec N k) (labVec N k')
  have hdelta : (∑ k : Lab N, ∑ k' : Lab N, c k * c k' *
        (((if labVec N k = labVec N k' then (1 : ℝ) else 0)
          + (if labVec N k = -(labVec N k') then (1 : ℝ) else 0)) / 2))
      = ∑ k : Lab N, (c k) ^ 2 :=
    Work.BoseBoxFock.sum_pair_delta (labVec N) hinj (fun k => labVec_neg N k) c heven
  -- the cosine projection of `g` onto the labels of the cube
  let P : EuclideanSpace ℝ (Fin 3) → ℝ := fun x =>
    ∑ k : Lab N, c k * Real.cos (inner ℝ (Work.BoseB4.vec (labVec N k)) x)
  have hPeval : ∀ x,
      P x = ∑ k : Lab N, c k * Real.cos (inner ℝ (Work.BoseB4.vec (labVec N k)) x) :=
    fun x => rfl
  have hgc : Continuous fun x : EuclideanSpace ℝ (Fin 3) => g x := hg
  have hInt : ∀ f : EuclideanSpace ℝ (Fin 3) → ℝ, Continuous f →
      Integrable f (volume.restrict Work.BoseB4.unitCell) := fun f hf =>
    ContinuousOn.integrableOn_compact Work.BoseB4.isCompact_unitCell hf.continuousOn
  have hcoscont : ∀ v : EuclideanSpace ℝ (Fin 3),
      Continuous fun x : EuclideanSpace ℝ (Fin 3) => Real.cos (inner ℝ v x) := by
    intro v
    exact Real.continuous_cos.comp (continuous_const.inner continuous_id)
  -- ### (1) the pairing `∫_cell g · P = ∑_k c_k²`
  have hchiP : ∫ x in Work.BoseB4.unitCell, g x * P x
      = ∑ k : Lab N, (c k) ^ 2 := by
    have hfun : (fun x => g x * P x)
        = fun x => ∑ k : Lab N, c k *
            (g x * Real.cos (inner ℝ (Work.BoseB4.vec (labVec N k)) x)) := by
      funext x
      rw [hPeval x, Finset.mul_sum]
      exact Finset.sum_congr rfl fun k _ => by ring
    rw [hfun]
    rw [integral_finsetSum (Finset.univ)
      (f := fun k x => c k *
        (g x * Real.cos (inner ℝ (Work.BoseB4.vec (labVec N k)) x)))
      (fun k _ => hInt _ (continuous_const.mul (hgc.mul (hcoscont _))))]
    apply Finset.sum_congr rfl
    intro k _
    rw [integral_const_mul, hc k]
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
  have hsq : ∫ x in Work.BoseB4.unitCell, ((g x - P x) ^ 2)
      = (∫ x in Work.BoseB4.unitCell, (g x) ^ 2)
        - 2 * (∑ k : Lab N, (c k) ^ 2) + ∑ k : Lab N, (c k) ^ 2 := by
    have hfun : (fun x => (g x - P x) ^ 2)
        = fun x => ((g x) ^ 2 - 2 * (g x * P x) + (P x) ^ 2) := by
      funext x; ring
    rw [hfun]
    have h1 : Integrable (fun x => (g x) ^ 2 - 2 * (g x * P x))
        (volume.restrict Work.BoseB4.unitCell) :=
      hInt _ ((hgc.pow 2).sub (continuous_const.mul (hgc.mul hPcont)))
    have h2 : Integrable (fun x => (P x) ^ 2) (volume.restrict Work.BoseB4.unitCell) :=
      hInt _ (hPcont.pow 2)
    have h3 : Integrable (fun x => (g x) ^ 2)
        (volume.restrict Work.BoseB4.unitCell) := hInt _ (hgc.pow 2)
    have h4 : Integrable (fun x => 2 * (g x * P x))
        (volume.restrict Work.BoseB4.unitCell) :=
      hInt _ (continuous_const.mul (hgc.mul hPcont))
    rw [integral_add h1 h2, integral_sub h3 h4, integral_const_mul, hchiP, hPP]
  -- ### (4) the residual is nonnegative
  have hnn : 0 ≤ ∫ x in Work.BoseB4.unitCell, ((g x - P x) ^ 2) :=
    integral_nonneg (fun x => sq_nonneg _)
  linarith

/-- **The numeric input.**  `∫_{cell} χ⁴ ≤ 48/π`, from the pointwise bound
`χ(x)² ≤ 48/π` (`chi_sq_bounds`) and the normalisation `∫_{cell} χ² = 1`. -/
theorem unitCell_chi_pow4_le_48 :
    (∫ x in Work.BoseB4.unitCell, (Submission.BoseGases.chi x) ^ 4) ≤ 48 / Real.pi := by
  have hpt : ∀ x : EuclideanSpace ℝ (Fin 3), (Submission.BoseGases.chi x) ^ 4
      ≤ (48 / Real.pi) * (Submission.BoseGases.chi x) ^ 2 := by
    intro x
    have h : (Submission.BoseGases.chi x) ^ 2 ≤ 48 / Real.pi := chi_sq_bounds.2 x
    calc (Submission.BoseGases.chi x) ^ 4
        = (Submission.BoseGases.chi x) ^ 2 * (Submission.BoseGases.chi x) ^ 2 := by ring
      _ ≤ (48 / Real.pi) * (Submission.BoseGases.chi x) ^ 2 :=
          mul_le_mul_of_nonneg_right h (sq_nonneg _)
  have hmono : (∫ x in Work.BoseB4.unitCell, (Submission.BoseGases.chi x) ^ 4)
      ≤ ∫ x in Work.BoseB4.unitCell, (48 / Real.pi) * (Submission.BoseGases.chi x) ^ 2 :=
    MeasureTheory.setIntegral_mono_ae
      ((Submission.BoseGases.chi_continuous.pow 4).continuousOn.integrableOn_compact
        Work.BoseB4.isCompact_unitCell)
      ((continuous_const.mul (Submission.BoseGases.chi_continuous.pow 2)).continuousOn.integrableOn_compact
        Work.BoseB4.isCompact_unitCell)
      (Filter.Eventually.of_forall hpt)
  calc (∫ x in Work.BoseB4.unitCell, (Submission.BoseGases.chi x) ^ 4)
      ≤ ∫ x in Work.BoseB4.unitCell, (48 / Real.pi) * (Submission.BoseGases.chi x) ^ 2 :=
        hmono
    _ = (48 / Real.pi) * ∫ x in Work.BoseB4.unitCell, (Submission.BoseGases.chi x) ^ 2 :=
        MeasureTheory.integral_const_mul _ _
    _ = 48 / Real.pi := by rw [integral_unitCell_chi_sq]; ring

theorem sum_hatChiSq_sq_le (N : ℕ) :
    ∑ k : Work.BoseBoxFock.Lab N,
        (Work.BoseK15.corpusBox.hatChiSq (Work.BoseB4.vec (Work.BoseBoxFock.labVec N k))) ^ 2
      ≤ 48 / Real.pi := by
  -- the defining Fourier integral of `χ̂²` may be taken over the unit cell
  have hconv : (∑ k : Work.BoseBoxFock.Lab N,
        (Work.BoseK15.corpusBox.hatChiSq (Work.BoseB4.vec (labVec N k))) ^ 2)
      = ∑ k : Work.BoseBoxFock.Lab N,
          (∫ x in Work.BoseB4.unitCell, (Submission.BoseGases.chi x) ^ 2
            * Real.cos (inner ℝ (Work.BoseB4.vec (labVec N k)) x)) ^ 2 := by
    refine Finset.sum_congr rfl fun k _ => ?_
    rw [unitCell_chiSq_cos]
  calc (∑ k : Work.BoseBoxFock.Lab N,
        (Work.BoseK15.corpusBox.hatChiSq (Work.BoseB4.vec (labVec N k))) ^ 2)
      = ∑ k : Work.BoseBoxFock.Lab N,
          (∫ x in Work.BoseB4.unitCell, (Submission.BoseGases.chi x) ^ 2
            * Real.cos (inner ℝ (Work.BoseB4.vec (labVec N k)) x)) ^ 2 := hconv
    _ ≤ ∫ x in Work.BoseB4.unitCell, ((Submission.BoseGases.chi x) ^ 2) ^ 2 :=
        BesselUnitCell N (fun x => (Submission.BoseGases.chi x) ^ 2)
          (Submission.BoseGases.chi_continuous.pow 2)
    _ = ∫ x in Work.BoseB4.unitCell, (Submission.BoseGases.chi x) ^ 4 := by
        apply MeasureTheory.setIntegral_congr_fun Work.BoseB4.isClosed_unitCell.measurableSet
        intro x _
        ring
    _ ≤ 48 / Real.pi := unitCell_chi_pow4_le_48


end Work.BoseBoxFock.Clean
