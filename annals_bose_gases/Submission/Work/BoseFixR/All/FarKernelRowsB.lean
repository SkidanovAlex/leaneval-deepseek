import ChallengeDeps
import Mathlib.Data.ZMod.ValMinAbs
import Mathlib.Algebra.Order.Star.Real
import Mathlib.MeasureTheory.Integral.Bochner.Set
import Submission.Work.BoseFixR.All.FarKernelRows
-- PORT435-BEGIN (v4.35 isDefEq respectTransparency compat)
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- PORT435-END

namespace Work.BoseFixR.All

open _root_.BoseGases Submission.BoseGases Work.UBB Work.BoseBox
open Work.BoseBoxFix Work.BoseBoxFock

open scoped Real Topology BigOperators
open MeasureTheory Filter Metric

set_option autoImplicit false
set_option linter.unusedVariables false
set_option maxHeartbeats 1000000

/-! ## 0. The `χ²`-facts on the unit cell

The ℓ² row of the far leg is the Bessel bound for the Fourier coefficients of `χ²`.  The two
ingredients are (i) `χ̂²(p) = ∫_{cell} χ² cos⟪p,·⟫` (`unitCell_chiSq_cos`, the set-integral form of
`BoxData.hatChiSq`) and (ii) the numeric bound `∫_{cell} χ⁴ ≤ 100` for the corpus bump. -/

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

/-- Pointwise: `χ(x)⁴ ≤ chiNormSq⁻¹ · χ(x)²` (`χ = chiBase/√chiNormSq` with `0 ≤ chiBase ≤ 1`). -/
lemma chi_pow4_le_inv_mul_sq (x : EuclideanSpace ℝ (Fin 3)) :
    (Submission.BoseGases.chi x) ^ 4
      ≤ (Submission.BoseGases.chiNormSq)⁻¹ * (Submission.BoseGases.chi x) ^ 2 := by
  have hZ : 0 < Submission.BoseGases.chiNormSq := Submission.BoseGases.chiNormSq_pos
  have hsq : (Submission.BoseGases.chi x) ^ 2 ≤ (Submission.BoseGases.chiNormSq)⁻¹ := by
    rw [Submission.BoseGases.chi, div_pow, Real.sq_sqrt (le_of_lt hZ), ← one_div]
    exact div_le_div_of_nonneg_right
      (pow_le_one₀ (Submission.BoseGases.chiBase_nonneg x)
        (Submission.BoseGases.chiBase_le_one x)) (le_of_lt hZ)
  have h0 : 0 ≤ (Submission.BoseGases.chi x) ^ 2 := sq_nonneg _
  have hinv : 0 ≤ (Submission.BoseGases.chiNormSq)⁻¹ := le_of_lt (inv_pos.mpr hZ)
  nlinarith [hsq, h0, hinv]

/-- `∫ χ⁴ ≤ ∫ χ² / chiNormSq = 1 / chiNormSq ≤ 16`: the numeric input of the ℓ² row of the far
leg.  (`chiNormSq_ge_inv_sixteen`, the sharp form of the corpus normalisation.) -/
theorem integral_chi_pow4_le_sixteen :
    (∫ x : EuclideanSpace ℝ (Fin 3), (Submission.BoseGases.chi x) ^ 4) ≤ 16 := by
  have hZ : 0 < Submission.BoseGases.chiNormSq := Submission.BoseGases.chiNormSq_pos
  have hInt2 : Integrable
      (fun x : EuclideanSpace ℝ (Fin 3) => (Submission.BoseGases.chiNormSq)⁻¹
        * (Submission.BoseGases.chi x) ^ 2) :=
    (Work.BoseK15.corpusBox.chi_sq_integrable).const_mul _
  have hInt4 : Integrable
      (fun x : EuclideanSpace ℝ (Fin 3) => (Submission.BoseGases.chi x) ^ 4) := by
    refine hInt2.mono' (Submission.BoseGases.chi_continuous.pow 4).aestronglyMeasurable ?_
    filter_upwards with x
    rw [Real.norm_eq_abs, abs_of_nonneg (by positivity)]
    exact chi_pow4_le_inv_mul_sq x
  calc (∫ x : EuclideanSpace ℝ (Fin 3), (Submission.BoseGases.chi x) ^ 4)
      ≤ ∫ x : EuclideanSpace ℝ (Fin 3),
          (Submission.BoseGases.chiNormSq)⁻¹ * (Submission.BoseGases.chi x) ^ 2 :=
        integral_mono hInt4 hInt2 (fun x => chi_pow4_le_inv_mul_sq x)
    _ = (Submission.BoseGases.chiNormSq)⁻¹
          * (∫ x : EuclideanSpace ℝ (Fin 3), (Submission.BoseGases.chi x) ^ 2) :=
        integral_const_mul _ _
    _ = (Submission.BoseGases.chiNormSq)⁻¹ := by rw [Submission.BoseGases.chi_L2]; ring
    _ ≤ 16 := by
        rw [inv_le_iff_one_le_mul₀ hZ]
        linarith [Work.SmallBoxOneBody.chiNormSq_ge_inv_sixteen]

/-- `∫_{cell} χ⁴ ≤ 100`: the numeric bound consumed by the ℓ² far row. -/
theorem unitCell_chi_pow4_le :
    (∫ x in Work.BoseB4.unitCell, (Submission.BoseGases.chi x) ^ 4) ≤ 100 := by
  rw [MeasureTheory.setIntegral_eq_integral_of_forall_compl_eq_zero
    (f := fun x : EuclideanSpace ℝ (Fin 3) => (Submission.BoseGases.chi x) ^ 4)]
  · linarith [integral_chi_pow4_le_sixteen]
  · intro x hx
    have h0 : Submission.BoseGases.chi x = 0 := by
      by_contra h
      exact hx (Work.BoseK15.chi_support_subset_unitCell (Function.mem_support.mpr h))
    rw [h0]
    norm_num

/-! ## 1. The Bessel bound for a general continuous `g` on the unit cell

This is the Hilbert-space core of `Work.BoseBoxFock.sum_hatChi_sq_le` with `χ` replaced by an
arbitrary continuous `g` and the normalisation `∫χ² = 1` replaced by `∫g²`; it is the engine of
the ℓ² row of the far leg (`g = χ²`). -/

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

/-! ## 2. The two `χ̂`-rows at the honest family

Row 3 (`∑_{k≠0} χ̂(k)² ≤ 100`) is the Bessel bound `sum_hatChi_sq_le` (`≤ 1`) through the pin
`honest_hatChi_eq`; row 4 is the ℓ² row `∑_{k≠0} χ̂²(k)² ≤ 100`, which is `BesselUnitCell` at
`g = χ²` (the ℓ¹ form `∑|χ̂²| ≤ 10^100` is *not* provable — see the header of
`Submission/Work/BoseFixR/FarKernelRows.lean` — while this ℓ² form is, with the numeric constant
`1/chiNormSq ≤ 16`). -/

/-- **Row 3** (`∑_{k≠0} χ̂(k)² ≤ 100`): the pin `honest_hatChi_eq` turns the sum into the Bessel
sum `∑_k χ̂(k)² ≤ 1`, the excited modes being a sub-finset of the label cube. -/
theorem farRowB_hatChi {v : EuclideanSpace ℝ (Fin 3) → ℝ} (h : Work.UBB.ScatSol v)
    (fc fu : LowCut) (HM : ∀ μ : ℝ, HonestModes v μ) {μ R : ℝ} (hR : 0 < R)
    (hRℓ : R ≤ ell v μ * Submission.BoseGases.chiR0) :
    (∑ k ∈ Work.BoseB7.excited (Lab (HM μ).N),
        ((HonestBoxFam v h fc fu HM μ).E.hatChi k) ^ 2) ≤ 100 := by
  have hℓ : 0 < ell v μ := ell_pos_of_le hR hRℓ
  have hsub : (∑ k ∈ Work.BoseB7.excited (Lab (HM μ).N),
        ((HonestBoxFam v h fc fu HM μ).E.hatChi k) ^ 2)
      ≤ ∑ k : Lab (HM μ).N,
          ((HonestBoxFam v h fc fu HM μ).E.hatChi k) ^ 2 := by
    refine Finset.sum_le_sum_of_subset_of_nonneg
      (Finset.erase_subset (0 : Lab (HM μ).N) Finset.univ) ?_
    intro x _ _
    positivity
  have hpin : (∑ k : Lab (HM μ).N,
        ((HonestBoxFam v h fc fu HM μ).E.hatChi k) ^ 2)
      = ∑ k : Lab (HM μ).N,
          (Work.BoseK15.corpusBox.hatChi (Work.BoseB4.vec (labVec (HM μ).N k))) ^ 2 :=
    Finset.sum_congr rfl (fun k _ => by rw [honest_hatChi_eq h fc fu HM hℓ k])
  calc (∑ k ∈ Work.BoseB7.excited (Lab (HM μ).N),
        ((HonestBoxFam v h fc fu HM μ).E.hatChi k) ^ 2)
      ≤ ∑ k : Lab (HM μ).N,
          ((HonestBoxFam v h fc fu HM μ).E.hatChi k) ^ 2 := hsub
    _ = ∑ k : Lab (HM μ).N,
          (Work.BoseK15.corpusBox.hatChi (Work.BoseB4.vec (labVec (HM μ).N k))) ^ 2 := hpin
    _ ≤ 1 := Work.BoseBoxFock.sum_hatChi_sq_le (HM μ).N
    _ ≤ 100 := by norm_num

/-- **The ℓ² `χ̂²`-sum on the label cube**: `∑_{k≠0} χ̂²(p_k)² ≤ 100`.  `BesselUnitCell` at
`g = χ²` gives `∑_k χ̂²(p_k)² ≤ ∫_{cell} χ⁴ ≤ 100` (`unitCell_chi_pow4_le`), the pin
`unitCell_chiSq_cos` identifying the coefficients. -/
theorem sum_hatChiSq_sq_le (N : ℕ) :
    (∑ k ∈ Work.BoseB7.excited (Lab N),
        (Work.BoseK15.corpusBox.hatChiSq (Work.BoseB4.vec (labVec N k))) ^ 2) ≤ 100 := by
  have hsub : (∑ k ∈ Work.BoseB7.excited (Lab N),
        (Work.BoseK15.corpusBox.hatChiSq (Work.BoseB4.vec (labVec N k))) ^ 2)
      ≤ ∑ k : Lab N,
          (Work.BoseK15.corpusBox.hatChiSq (Work.BoseB4.vec (labVec N k))) ^ 2 := by
    refine Finset.sum_le_sum_of_subset_of_nonneg
      (Finset.erase_subset (0 : Lab N) Finset.univ) ?_
    intro x _ _
    positivity
  have hconv : (∑ k : Lab N,
        (Work.BoseK15.corpusBox.hatChiSq (Work.BoseB4.vec (labVec N k))) ^ 2)
      = ∑ k : Lab N,
          (∫ x in Work.BoseB4.unitCell,
            (Submission.BoseGases.chi x) ^ 2
              * Real.cos (inner ℝ (Work.BoseB4.vec (labVec N k)) x)) ^ 2 :=
    Finset.sum_congr rfl (fun k _ => by rw [unitCell_chiSq_cos])
  calc (∑ k ∈ Work.BoseB7.excited (Lab N),
        (Work.BoseK15.corpusBox.hatChiSq (Work.BoseB4.vec (labVec N k))) ^ 2)
      ≤ ∑ k : Lab N,
          (Work.BoseK15.corpusBox.hatChiSq (Work.BoseB4.vec (labVec N k))) ^ 2 := hsub
    _ = ∑ k : Lab N,
          (∫ x in Work.BoseB4.unitCell,
            (Submission.BoseGases.chi x) ^ 2
              * Real.cos (inner ℝ (Work.BoseB4.vec (labVec N k)) x)) ^ 2 := hconv
    _ ≤ ∫ x in Work.BoseB4.unitCell, ((Submission.BoseGases.chi x) ^ 2) ^ 2 :=
        BesselUnitCell N (fun x => (Submission.BoseGases.chi x) ^ 2)
          (Submission.BoseGases.chi_continuous.pow 2)
    _ = ∫ x in Work.BoseB4.unitCell, (Submission.BoseGases.chi x) ^ 4 := by
        apply MeasureTheory.setIntegral_congr_fun Work.BoseB4.isClosed_unitCell.measurableSet
        intro x _
        ring
    _ ≤ 100 := unitCell_chi_pow4_le

/-- **Row 4** (`∑_{k≠0} χ̂²(k)² ≤ 100`) at the honest family: the pin `honest_hatChiSq_eq` and
the lattice Bessel bound `sum_hatChiSq_sq_le`. -/
theorem farRowB_hatChiSq {v : EuclideanSpace ℝ (Fin 3) → ℝ} (h : Work.UBB.ScatSol v)
    (fc fu : LowCut) (HM : ∀ μ : ℝ, HonestModes v μ) {μ R : ℝ} (hR : 0 < R)
    (hRℓ : R ≤ ell v μ * Submission.BoseGases.chiR0) :
    (∑ k ∈ Work.BoseB7.excited (Lab (HM μ).N),
        ((HonestBoxFam v h fc fu HM μ).E.hatChiSq k) ^ 2) ≤ 100 := by
  have hℓ : 0 < ell v μ := ell_pos_of_le hR hRℓ
  have hEq : (∑ k ∈ Work.BoseB7.excited (Lab (HM μ).N),
        ((HonestBoxFam v h fc fu HM μ).E.hatChiSq k) ^ 2)
      = ∑ k ∈ Work.BoseB7.excited (Lab (HM μ).N),
          (Work.BoseK15.corpusBox.hatChiSq (Work.BoseB4.vec (labVec (HM μ).N k))) ^ 2 :=
    Finset.sum_congr rfl (fun k _ => by rw [honest_hatChiSq_eq h fc fu HM hℓ k])
  rw [hEq]
  exact sum_hatChiSq_sq_le (HM μ).N

theorem FarKernelRowsB {v : EuclideanSpace ℝ (Fin 3) → ℝ} (h : Work.UBB.ScatSol v)
    (hv : 0 ≤ v) (hv1 : MeasureTheory.MemLp v 1) (hvrad : BoseGases.IsRadial v)
    {R : ℝ} (hR : 0 < R)
    (hv_supp : tsupport v ⊆ Metric.ball (0 : EuclideanSpace ℝ (Fin 3)) R)
    (hav : 0 < BoseGases.a v) (fc fu : Work.BoseBoxFix.LowCut)
    (HM : ∀ μ : ℝ, Work.BoseBoxFock.HonestModes v μ) {μ : ℝ} (hμ : 0 < μ)
    (hview : (Work.BoseBoxFock.HonestBoxFam v h fc fu HM μ).viewFSAll v h μ)
    (hRℓ : R ≤ Work.BoseFixR.ell v μ * Submission.BoseGases.chiR0) :
    (∀ k : Work.BoseBoxFock.Lab (HM μ).N,
        |(Work.BoseBoxFock.HonestBoxFam v h fc fu HM μ).E.W1 k| ≤ 16 * Real.pi * BoseGases.a v)
    ∧ (∀ k : Work.BoseBoxFock.Lab (HM μ).N,
        |(Work.BoseBoxFock.HonestBoxFam v h fc fu HM μ).E.W1omega k|
          ≤ 16 * Real.pi * BoseGases.a v)
    ∧ (∑ k ∈ Work.BoseB7.excited (Work.BoseBoxFock.Lab (HM μ).N),
        ((Work.BoseBoxFock.HonestBoxFam v h fc fu HM μ).E.hatChi k) ^ 2 ≤ 100)
    ∧ (∑ k ∈ Work.BoseB7.excited (Work.BoseBoxFock.Lab (HM μ).N),
        ((Work.BoseBoxFock.HonestBoxFam v h fc fu HM μ).E.hatChiSq k) ^ 2 ≤ 100)
    ∧ ((∑ s ∈ (Work.BoseB7.excited (Work.BoseBoxFock.Lab (HM μ).N)).filter
        (fun s => (Work.BoseBoxFock.HonestBoxFam v h fc fu HM μ).E.fL s ≠ 0), (1 : ℝ))
          ≤ 10 ^ 6 * (Work.BoseFixR.ell v μ
              * (Work.BoseBoxFock.HonestBoxFam v h fc fu HM μ).E.KL
              * Real.sqrt (μ * BoseGases.a v) + 1) ^ 3) :=
  ⟨farRow_W1 h hv hvrad hR hv_supp hav fc fu HM hRℓ,
    farRow_W1omega h hv hvrad hR hv_supp hav fc fu HM hRℓ,
    farRowB_hatChi h fc fu HM hR hRℓ,
    farRowB_hatChiSq h fc fu HM hR hRℓ,
    farRow_count h hv hvrad hR hv_supp hav fc fu HM hμ hview hRℓ⟩

end Work.BoseFixR.All
