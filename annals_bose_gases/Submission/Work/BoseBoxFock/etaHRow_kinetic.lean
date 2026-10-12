import Mathlib.Data.ZMod.ValMinAbs
import Mathlib.Algebra.Order.Star.Real
import Mathlib.Analysis.Normed.Lp.MeasurableSpace
import Mathlib.MeasureTheory.Integral.Bochner.Basic
import Mathlib.MeasureTheory.Measure.Haar.OfBasis
import Submission.Work.BoseBoxFock.moment2LatticeC
import Submission.Work.BoseBoxFock.qVec_overlap_eq_cboxQ
-- PORT435-BEGIN (v4.35 isDefEq respectTransparency compat)
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- PORT435-END

/-!
# `Work.BoseBoxFock.etaHRow_kinetic`

The **second-moment (Sobolev) companion of the `qVec` Bessel/Parseval identity**: the `η_H` row of
the kinetic group is bounded by `(2κ)⁻²` times the second lattice moment of the windowed, mean-free
state.

The pointwise input is the elementary bound `η_H(k) ≤ (2κ)⁻²‖k‖²` for **every** `k` (`η_H = 0`
below the onset `2κ`, `η_H ≤ 1` above it, and `1 ≤ (‖k‖/(2κ))²` there).  The lattice bookkeeping is
then:

* `kmomLab ℓ N k = kmomInt ℓ (labVec N k)` (definitional) and `labVec N` is injective
  (`ZMod.injective_valMinAbs`), so the finite `Lab N` sum embeds into the full `ℤ³` `tsum`;
* the `qVec`-coefficient is the transform of the windowed mean-free state:
  `∫ conj(qVec ℓ k)·u = kinFT (χ_Λ·cboxQ ℓ u) k` (`qVec_overlap_eq_cboxQ` followed by the
  `modeVec`/`kinFT` dictionary `star_modeVec_eq`).

The consumer supplies the summability hypothesis `hsum`; without it the `tsum` convention makes the
right-hand side `0` and the inequality fails (see the finding files of this subproject).
-/

namespace Work.BoseBoxFock

noncomputable section

open scoped BigOperators

local notation "E3" => EuclideanSpace ℝ (Fin 3)

/-- `labVec N` (the centred integer representative of a `Lab N` label) is injective, because
`ZMod.valMinAbs` is. -/
theorem etaHKin_labVec_injective (N : ℕ) : Function.Injective (labVec N) := by
  intro a b hab
  funext i
  exact ZMod.injective_valMinAbs (congrFun hab i)

/-- The truncated lattice momentum of a label *is* the full lattice momentum of its integer
representative (definitional). -/
theorem etaHKin_kmomLab_eq_kmomInt (ℓ : ℝ) (N : ℕ) (k : Lab N) :
    kmomLab ℓ N k = kmomInt ℓ (labVec N k) := rfl

/-- The complex `modeVec`/`kinFT` dictionary: `∫ conj(modeVec ℓ k)·w = kinFT (χ_Λ·w) k`. -/
theorem etaHKin_modeVec_overlap_eq_kinFT {ℓ : ℝ} (k : E3) (w : E3 → ℂ) :
    (∫ x : E3, (starRingEnd ℂ) (Work.BoseK15.corpusBox.modeVec ℓ k x) * w x)
      = Submission.BoseGases.kinFT
          (fun z : E3 => ((Work.BoseK15.corpusBox.chiLam ℓ z : ℝ) : ℂ) * w z) k := by
  rw [Submission.BoseGases.kinFT]
  refine MeasureTheory.integral_congr_ae (Filter.Eventually.of_forall fun x => ?_)
  beta_reduce
  rw [star_modeVec_eq, chiLam_eq_chiScale]
  ring

/-- **The `qVec`-coefficient is the transform of the windowed mean-free state** (complex state):
for `u` measurable, bounded and supported in the box, `∫ conj(qVec ℓ k)·u = kinFT (χ_Λ·cboxQ ℓ u) k`
at *every* momentum `k` (not only lattice ones). -/
theorem etaHKin_qVec_overlap_eq_kinFT {ℓ : ℝ} (hℓ : 0 < ℓ) (k : E3) {u : E3 → ℂ}
    (hum : Measurable u) (hub : ∃ C : ℝ, ∀ x, ‖u x‖ ≤ C)
    (hus : Function.support u ⊆ Work.BoseK15.corpusBox.boxL ℓ) :
    (∫ x : E3, (starRingEnd ℂ) (Work.BoseK15.corpusBox.qVec ℓ k x) * u x)
      = Submission.BoseGases.kinFT
          (fun z : E3 => ((Work.BoseK15.corpusBox.chiLam ℓ z : ℝ) : ℂ) * cboxQ ℓ u z) k := by
  rw [qVec_overlap_eq_cboxQ hℓ k hum hub hus]
  exact etaHKin_modeVec_overlap_eq_kinFT k (cboxQ ℓ u)

/-- **The pointwise Sobolev bound of `η_H`**: `η_H(k) ≤ (2κ)⁻²‖k‖²` for every `k` and every
`LowCut` (`η_H = 0` below the onset `2κ`, `η_H ≤ 1 ≤ (‖k‖/(2κ))²` above it). -/
theorem etaHKin_etaH_le_zpow_mul_sq {fu : Work.BoseBoxFix.LowCut} {κ : ℝ} (hκ : 0 < κ)
    (k : E3) : etaH fu κ k ≤ (2 * κ) ^ (-2 : ℤ) * ‖k‖ ^ 2 := by
  have h2κ : (0 : ℝ) < 2 * κ := by linarith
  have hz : (2 * κ) ^ (-2 : ℤ) = ((2 * κ) ^ 2)⁻¹ := by
    simp only [zpow_neg, zpow_ofNat]
  rcases le_or_gt (2 * κ) ‖k‖ with h | h
  · have h1 : etaH fu κ k ≤ 1 := etaH_le_one fu κ k
    have h2 : (1 : ℝ) ≤ (2 * κ) ^ (-2 : ℤ) * ‖k‖ ^ 2 := by
      rw [hz, ← div_eq_inv_mul, one_le_div₀ (by positivity)]
      nlinarith [h, h2κ, norm_nonneg k]
    linarith
  · have hr : ‖k‖ / (2 * κ) < 1 := (div_lt_one h2κ).mpr h
    have hf : fu.f (‖k‖ / (2 * κ)) = 1 := fu.one _ hr.le
    rw [etaH, hf, sub_self]
    exact mul_nonneg (le_of_lt (by positivity : (0 : ℝ) < (2 * κ) ^ (-2 : ℤ))) (sq_nonneg _)

theorem etaHRow_kinetic {ℓ : ℝ} (hℓ : 0 < ℓ) (N : ℕ) {fu : Work.BoseBoxFix.LowCut}
    {κ : ℝ} (hκ : 0 < κ) {u : EuclideanSpace ℝ (Fin 3) → ℂ}
    (hum : Measurable u) (hub : ∃ C : ℝ, ∀ x, ‖u x‖ ≤ C)
    (hus : Function.support u ⊆ Work.BoseK15.corpusBox.boxL ℓ)
    (hsum : Summable (fun n : Fin 3 → ℤ => (ℓ ^ 3)⁻¹ * ‖Work.BoseBoxFock.kmomInt ℓ n‖ ^ 2 *
        ‖Submission.BoseGases.kinFT
          (fun x : EuclideanSpace ℝ (Fin 3) =>
            ((Work.BoseK15.corpusBox.chiLam ℓ x : ℝ) : ℂ) *
              Work.BoseBoxFock.cboxQ ℓ u x)
          (Work.BoseBoxFock.kmomInt ℓ n)‖ ^ 2)) :
    (∑ k : Work.BoseBoxFock.Lab N, Work.BoseBoxFock.etaH fu κ
        (Work.BoseBoxFock.kmomLab ℓ N k) *
        (((ℓ ^ 3)⁻¹) * ‖∫ x : EuclideanSpace ℝ (Fin 3),
          (starRingEnd ℂ) (Work.BoseK15.corpusBox.qVec ℓ
            (Work.BoseBoxFock.kmomLab ℓ N k) x) * u x‖ ^ 2))
      ≤ (2 * κ) ^ (-2 : ℤ) *
          (∑' n : Fin 3 → ℤ, (ℓ ^ 3)⁻¹ * ‖Work.BoseBoxFock.kmomInt ℓ n‖ ^ 2 *
            ‖Submission.BoseGases.kinFT
              (fun x : EuclideanSpace ℝ (Fin 3) =>
                ((Work.BoseK15.corpusBox.chiLam ℓ x : ℝ) : ℂ) *
                  Work.BoseBoxFock.cboxQ ℓ u x)
              (Work.BoseBoxFock.kmomInt ℓ n)‖ ^ 2) := by
  set A : (Fin 3 → ℤ) → ℝ := fun m => (ℓ ^ 3)⁻¹ * ‖kmomInt ℓ m‖ ^ 2 *
      ‖Submission.BoseGases.kinFT
        (fun z : E3 => ((Work.BoseK15.corpusBox.chiLam ℓ z : ℝ) : ℂ) * cboxQ ℓ u z)
        (kmomInt ℓ m)‖ ^ 2 with hA
  have hsumA : Summable A := by simpa only [hA] using hsum
  have hA0 : ∀ m : Fin 3 → ℤ, 0 ≤ A m := by
    intro m
    simp only [hA]
    exact mul_nonneg (mul_nonneg (inv_nonneg.mpr (pow_nonneg hℓ.le 3)) (sq_nonneg _))
      (sq_nonneg _)
  have hApt : ∀ n : Fin 3 → ℤ, A n = (ℓ ^ 3)⁻¹ * ‖kmomInt ℓ n‖ ^ 2 *
      ‖Submission.BoseGases.kinFT
        (fun x : E3 => ((Work.BoseK15.corpusBox.chiLam ℓ x : ℝ) : ℂ) * cboxQ ℓ u x)
        (kmomInt ℓ n)‖ ^ 2 := by
    intro n
    simp only [hA]
  -- the per-label bound
  have hstep : ∀ k : Lab N, etaH fu κ (kmomLab ℓ N k) *
        (((ℓ ^ 3)⁻¹) * ‖∫ x : E3, (starRingEnd ℂ)
          (Work.BoseK15.corpusBox.qVec ℓ (kmomLab ℓ N k) x) * u x‖ ^ 2)
      ≤ (2 * κ) ^ (-2 : ℤ) * A (labVec N k) := by
    intro k
    have hkey : (∫ x : E3, (starRingEnd ℂ)
          (Work.BoseK15.corpusBox.qVec ℓ (kmomLab ℓ N k) x) * u x)
        = Submission.BoseGases.kinFT
            (fun z : E3 => ((Work.BoseK15.corpusBox.chiLam ℓ z : ℝ) : ℂ) * cboxQ ℓ u z)
            (kmomInt ℓ (labVec N k)) := by
      rw [etaHKin_qVec_overlap_eq_kinFT hℓ (kmomLab ℓ N k) hum hub hus,
        etaHKin_kmomLab_eq_kmomInt ℓ N k]
    rw [hkey, hA, etaHKin_kmomLab_eq_kmomInt ℓ N k]
    have hb : 0 ≤ (ℓ ^ 3)⁻¹ * ‖Submission.BoseGases.kinFT
        (fun z : E3 => ((Work.BoseK15.corpusBox.chiLam ℓ z : ℝ) : ℂ) * cboxQ ℓ u z)
        (kmomInt ℓ (labVec N k))‖ ^ 2 :=
      mul_nonneg (inv_nonneg.mpr (pow_nonneg hℓ.le 3)) (sq_nonneg _)
    have hle := mul_le_mul_of_nonneg_right
      (etaHKin_etaH_le_zpow_mul_sq (fu := fu) hκ (kmomInt ℓ (labVec N k))) hb
    refine hle.trans (le_of_eq ?_)
    ring
  -- the finite `Lab N` sum embeds into the full `ℤ³` sum
  have hB : (∑ k : Lab N, A (labVec N k)) ≤ ∑' m : Fin 3 → ℤ, A m := by
    have himg : (∑ m ∈ Finset.univ.image (labVec N), A m) = ∑ k : Lab N, A (labVec N k) :=
      Finset.sum_image (f := A) (s := Finset.univ) (g := labVec N)
        (fun a _ b _ hab => etaHKin_labVec_injective N hab)
    rw [← himg]
    exact Summable.sum_le_tsum (Finset.univ.image (labVec N)) (fun i _ => hA0 i) hsumA
  have hpos : (0 : ℝ) ≤ (2 * κ) ^ (-2 : ℤ) :=
    le_of_lt (by positivity : (0 : ℝ) < (2 * κ) ^ (-2 : ℤ))
  calc (∑ k : Lab N, etaH fu κ (kmomLab ℓ N k) *
        (((ℓ ^ 3)⁻¹) * ‖∫ x : E3, (starRingEnd ℂ)
          (Work.BoseK15.corpusBox.qVec ℓ (kmomLab ℓ N k) x) * u x‖ ^ 2))
      ≤ ∑ k : Lab N, (2 * κ) ^ (-2 : ℤ) * A (labVec N k) :=
        Finset.sum_le_sum (fun k _ => hstep k)
    _ = (2 * κ) ^ (-2 : ℤ) * ∑ k : Lab N, A (labVec N k) := by rw [Finset.mul_sum]
    _ ≤ (2 * κ) ^ (-2 : ℤ) * ∑' m : Fin 3 → ℤ, A m :=
        mul_le_mul_of_nonneg_left hB hpos
    _ = (2 * κ) ^ (-2 : ℤ) *
          (∑' n : Fin 3 → ℤ, (ℓ ^ 3)⁻¹ * ‖kmomInt ℓ n‖ ^ 2 *
            ‖Submission.BoseGases.kinFT
              (fun x : E3 => ((Work.BoseK15.corpusBox.chiLam ℓ x : ℝ) : ℂ) * cboxQ ℓ u x)
              (kmomInt ℓ n)‖ ^ 2) := by
        rw [show (∑' m : Fin 3 → ℤ, A m) = (∑' n : Fin 3 → ℤ,
            (ℓ ^ 3)⁻¹ * ‖kmomInt ℓ n‖ ^ 2 *
              ‖Submission.BoseGases.kinFT
                (fun x : E3 => ((Work.BoseK15.corpusBox.chiLam ℓ x : ℝ) : ℂ) * cboxQ ℓ u x)
                (kmomInt ℓ n)‖ ^ 2) from tsum_congr hApt]

end

end Work.BoseBoxFock
