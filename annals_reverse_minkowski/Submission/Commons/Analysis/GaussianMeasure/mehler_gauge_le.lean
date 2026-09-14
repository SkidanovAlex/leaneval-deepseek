import Mathlib
import Submission.Commons.Analysis.Convex.convexOn_logLaplace

namespace Commons.Analysis.GaussianMeasure

open MeasureTheory

/-! ## A generalised Mehler-type inequality for the gauge of a weighted integral

The core content is that the gauge of a convex balanced absorbent set is a seminorm — hence
sublinear — and therefore the Minkowski functional of the Bochner integral of a vector valued
function is at most the integral of the Minkowski functional.  We prove this for an arbitrary
nonnegative weight written as `Real.exp ∘ g`, which allows the weight to be recognised as a
`Measure.tilted` density (so that the normalised version is a probability measure) and Jensen's
inequality applies. -/

private theorem mehler_gauge_integral_le_exp {n N : ℕ} (K : Set (EuclideanSpace ℝ (Fin n)))
    (hKcvx : Convex ℝ K) (hKabs : Absorbent ℝ K) (hKbal : Balanced ℝ K)
    (g : EuclideanSpace ℝ (Fin N) → ℝ)
    (hg : MeasureTheory.Integrable
      (fun y : EuclideanSpace ℝ (Fin N) => Real.exp (g y)) MeasureTheory.volume)
    (Φ : EuclideanSpace ℝ (Fin N) → EuclideanSpace ℝ (Fin n))
    (hΦ : MeasureTheory.Integrable
      (fun y => Real.exp (g y) • Φ y) MeasureTheory.volume)
    (hΦg : MeasureTheory.Integrable
      (fun y => Real.exp (g y) * gauge K (Φ y)) MeasureTheory.volume) :
    gauge K (∫ y, Real.exp (g y) • Φ y ∂MeasureTheory.volume)
      ≤ ∫ y, Real.exp (g y) * gauge K (Φ y) ∂MeasureTheory.volume := by
  classical
  set Z : ℝ := ∫ y, Real.exp (g y) ∂MeasureTheory.volume with hZ
  have hZpos : 0 < Z := by
    rw [hZ]; exact MeasureTheory.integral_exp_pos hg
  have hZne : Z ≠ 0 := hZpos.ne'
  have hprob : MeasureTheory.IsProbabilityMeasure
      (MeasureTheory.Measure.tilted MeasureTheory.volume g) :=
    MeasureTheory.isProbabilityMeasure_tilted hg
  haveI := hprob
  have hIntΦ : MeasureTheory.Integrable Φ
      (MeasureTheory.Measure.tilted MeasureTheory.volume g) :=
    (MeasureTheory.integrable_tilted_iff hg Φ).2 hΦ
  have hIntg : MeasureTheory.Integrable (fun y => gauge K (Φ y))
      (MeasureTheory.Measure.tilted MeasureTheory.volume g) :=
    (MeasureTheory.integrable_tilted_iff hg (fun y => gauge K (Φ y))).2
      (by simpa only [smul_eq_mul] using hΦg)
  have hconv : ConvexOn ℝ (Set.univ : Set (EuclideanSpace ℝ (Fin n))) (gauge K) := by
    have h := (gaugeSeminorm hKbal hKcvx hKabs).convexOn
    convert h using 1
    ext x; rfl
  have hjensen : gauge K (∫ y, Φ y ∂(MeasureTheory.Measure.tilted MeasureTheory.volume g))
      ≤ ∫ y, gauge K (Φ y) ∂(MeasureTheory.Measure.tilted MeasureTheory.volume g) :=
    hconv.map_integral_le (hconv.continuousOn isOpen_univ) isClosed_univ
      (Filter.Eventually.of_forall (fun y => Set.mem_univ (Φ y))) hIntΦ hIntg
  have key1 : ∫ y, Φ y ∂(MeasureTheory.Measure.tilted MeasureTheory.volume g)
      = Z⁻¹ • ∫ y, Real.exp (g y) • Φ y ∂MeasureTheory.volume := by
    rw [MeasureTheory.integral_tilted, hZ, ← integral_smul]
    congr 1
    ext y
    rw [div_eq_inv_mul, smul_smul, mul_comm]
  have hvec : ∫ y, Real.exp (g y) • Φ y ∂MeasureTheory.volume
      = Z • ∫ y, Φ y ∂(MeasureTheory.Measure.tilted MeasureTheory.volume g) := by
    rw [key1, smul_smul, mul_inv_cancel₀ hZne, one_smul]
  have key2 : ∫ y, gauge K (Φ y) ∂(MeasureTheory.Measure.tilted MeasureTheory.volume g)
      = Z⁻¹ * ∫ y, Real.exp (g y) * gauge K (Φ y) ∂MeasureTheory.volume := by
    rw [MeasureTheory.integral_tilted, hZ, ← integral_const_mul]
    congr 1
    ext y
    simp only [div_eq_inv_mul, smul_eq_mul]
    ring
  have hreal : ∫ y, Real.exp (g y) * gauge K (Φ y) ∂MeasureTheory.volume
      = Z * ∫ y, gauge K (Φ y) ∂(MeasureTheory.Measure.tilted MeasureTheory.volume g) := by
    rw [key2, ← mul_assoc, mul_inv_cancel₀ hZne, one_mul]
  calc gauge K (∫ y, Real.exp (g y) • Φ y ∂MeasureTheory.volume)
      = gauge K (Z • ∫ y, Φ y ∂(MeasureTheory.Measure.tilted MeasureTheory.volume g)) := by
        rw [hvec]
    _ = Z * gauge K (∫ y, Φ y ∂(MeasureTheory.Measure.tilted MeasureTheory.volume g)) := by
        rw [gauge_smul_of_nonneg hZpos.le, smul_eq_mul]
    _ ≤ Z * ∫ y, gauge K (Φ y) ∂(MeasureTheory.Measure.tilted MeasureTheory.volume g) :=
        mul_le_mul_of_nonneg_left hjensen hZpos.le
    _ = ∫ y, Real.exp (g y) * gauge K (Φ y) ∂MeasureTheory.volume := hreal.symm

theorem mehler_gauge_le {n N : ℕ} (K : Set (EuclideanSpace ℝ (Fin n))) (hKcvx : Convex ℝ K)
    (hK0 : (0 : EuclideanSpace ℝ (Fin n)) ∈ K) (hKabs : Absorbent ℝ K)
    (hKbdd : Bornology.IsVonNBounded ℝ K) (hKbal : Balanced ℝ K)
    (ρ : ℝ) (hρ : ρ ^ 2 < 1) (x : EuclideanSpace ℝ (Fin N))
    (Φ : EuclideanSpace ℝ (Fin N) → EuclideanSpace ℝ (Fin n))
    (hΦ : MeasureTheory.Integrable
      (fun y : EuclideanSpace ℝ (Fin N) =>
        (Real.exp (-‖y - ρ • x‖ ^ 2 / (2 * (1 - ρ ^ 2))) : ℝ) • Φ y) MeasureTheory.volume)
    (hΦg : MeasureTheory.Integrable
      (fun y : EuclideanSpace ℝ (Fin N) =>
        Real.exp (-‖y - ρ • x‖ ^ 2 / (2 * (1 - ρ ^ 2))) * gauge K (Φ y)) MeasureTheory.volume) :
    gauge K (∫ y, (Real.exp (-‖y - ρ • x‖ ^ 2 / (2 * (1 - ρ ^ 2))) : ℝ) • Φ y
        ∂MeasureTheory.volume)
      ≤ ∫ y, Real.exp (-‖y - ρ • x‖ ^ 2 / (2 * (1 - ρ ^ 2))) * gauge K (Φ y)
        ∂MeasureTheory.volume := by
  have hden : 0 < 2 * (1 - ρ ^ 2) := by nlinarith [hρ]
  have hg : MeasureTheory.Integrable
      (fun y : EuclideanSpace ℝ (Fin N) => Real.exp (-‖y - ρ • x‖ ^ 2 / (2 * (1 - ρ ^ 2))))
      MeasureTheory.volume := by
    have hε : 0 < Real.sqrt (2 * (1 - ρ ^ 2)) := Real.sqrt_pos.2 hden
    refine (Commons.Analysis.Convex.integrable_gaussian_translate (n := N) hε (ρ • x)).congr
      (Filter.Eventually.of_forall (fun y => ?_))
    dsimp only
    rw [norm_sub_rev, Real.sq_sqrt hden.le]
  exact mehler_gauge_integral_le_exp K hKcvx hKabs hKbal
    (fun y => -‖y - ρ • x‖ ^ 2 / (2 * (1 - ρ ^ 2))) hg Φ hΦ hΦg

end Commons.Analysis.GaussianMeasure
