import Mathlib.Analysis.CStarAlgebra.Classes
import Mathlib.MeasureTheory.Function.LpSeminorm.CompareExp
import Mathlib.MeasureTheory.Measure.Haar.InnerProductSpace

namespace Commons.Analysis.Fourier

open MeasureTheory
open scoped ENNReal

theorem eLpNorm_one_le_of_ae_support_cube (d : ℕ) (r : ℝ) (hr : 0 < r)
    {f : EuclideanSpace ℝ (Fin d) → ℂ}
    (h2 : MeasureTheory.MemLp f 2
      (MeasureTheory.volume : MeasureTheory.Measure (EuclideanSpace ℝ (Fin d))))
    (hsupp : ∀ᵐ x ∂(MeasureTheory.volume : MeasureTheory.Measure (EuclideanSpace ℝ (Fin d))),
      (∃ i : Fin d, r < |x i|) → f x = 0) :
    MeasureTheory.MemLp f 1
        (MeasureTheory.volume : MeasureTheory.Measure (EuclideanSpace ℝ (Fin d))) ∧
      (MeasureTheory.eLpNorm f 1
          (MeasureTheory.volume : MeasureTheory.Measure (EuclideanSpace ℝ (Fin d)))).toReal ≤
        (2 * r) ^ ((d : ℝ) / 2) *
          (MeasureTheory.eLpNorm f 2
            (MeasureTheory.volume : MeasureTheory.Measure (EuclideanSpace ℝ (Fin d)))).toReal := by
  have hr2 : (0:ℝ) ≤ 2 * r := by linarith
  set C : Set (EuclideanSpace ℝ (Fin d)) := {x | ∀ i : Fin d, |x i| ≤ r} with hCdef
  have hCeq : C = WithLp.ofLp ⁻¹' (Set.pi Set.univ (fun _ : Fin d => Set.Icc (-r) r)) := by
    rw [hCdef]
    ext x
    simp only [Set.mem_ofPred_eq, Set.mem_preimage, Set.mem_pi, Set.mem_univ, Set.mem_Icc,
      true_implies]
    exact ⟨fun h i => abs_le.mp (h i), fun h i => abs_le.mpr (h i)⟩
  have hBmeas : MeasurableSet (Set.pi Set.univ (fun _ : Fin d => Set.Icc (-r) r)) :=
    MeasurableSet.pi Set.countable_univ (fun i _ => measurableSet_Icc)
  have hmeasC : MeasurableSet C := by
    rw [hCeq]
    exact hBmeas.preimage (WithLp.measurable_ofLp (2:ℝ≥0∞) (Fin d → ℝ))
  have hvolC : (volume C) = ENNReal.ofReal ((2*r)^d) := by
    rw [hCeq, (PiLp.volume_preserving_ofLp (Fin d)).measure_preimage hBmeas.nullMeasurableSet]
    rw [volume_pi_pi]
    simp only [Real.volume_Icc]
    have hp : (∏ _i : Fin d, ENNReal.ofReal (r - -r)) = ∏ _i : Fin d, ENNReal.ofReal (2*r) := by
      apply Finset.prod_congr rfl
      intro i _
      congr 1
      ring
    rw [hp, Finset.prod_const, Finset.card_univ, Fintype.card_fin]
    exact (ENNReal.ofReal_pow hr2 d).symm
  have hsupp' : f =ᵐ[volume] C.indicator f := by
    filter_upwards [hsupp] with x hx
    by_cases hxC : x ∈ C
    · rw [Set.indicator_of_mem hxC]
    · rw [Set.indicator_of_notMem hxC]
      apply hx
      by_contra hcon
      rw [not_exists] at hcon
      exact hxC (by rw [hCdef]; intro i; exact not_lt.mp (hcon i))
  have hprod : (fun x => (C.indicator (fun _ => (1:ℂ))) x * f x) = C.indicator f := by
    funext x
    by_cases hx : x ∈ C
    · simp [Set.indicator_of_mem hx]
    · simp [Set.indicator_of_notMem hx]
  have hφnorm : eLpNorm (C.indicator (fun _ => (1:ℂ))) (2:ℝ≥0∞) volume
      = (volume C) ^ (1/2:ℝ) := by
    rw [eLpNorm_indicator_const hmeasC (by norm_num) (by norm_num)]
    simp
  have hvolpow : (volume C) ^ (1/2:ℝ) = ENNReal.ofReal ((2*r)^((d:ℝ)/2)) := by
    rw [hvolC, ENNReal.ofReal_rpow_of_nonneg (x := (2*r)^d) (pow_nonneg hr2 d)
      (by norm_num : (0:ℝ) ≤ 1/2)]
    congr 1
    rw [← Real.rpow_natCast (2*r) d, ← Real.rpow_mul hr2 (d:ℝ) (1/2)]
    rw [show (d:ℝ)*(1/2) = (d:ℝ)/2 by ring]
  have hholder : eLpNorm (fun x => (C.indicator (fun _ => (1:ℂ))) x * f x) (1:ℝ≥0∞) volume
      ≤ eLpNorm (C.indicator (fun _ => (1:ℂ))) (2:ℝ≥0∞) volume
        * eLpNorm f (2:ℝ≥0∞) volume := by
    have htriple : ENNReal.HolderTriple (2:ℝ≥0∞) 2 1 := by
      rw [ENNReal.holderTriple_iff]; simpa using ENNReal.inv_two_add_inv_two
    have hφmeas : AEStronglyMeasurable (C.indicator (fun _ => (1:ℂ))) volume :=
      (measurable_const.indicator hmeasC).aestronglyMeasurable
    have := eLpNorm_le_eLpNorm_mul_eLpNorm_of_nnnorm (μ := volume)
      (p := (2:ℝ≥0∞)) (q := (2:ℝ≥0∞)) (r := (1:ℝ≥0∞)) (hpqr := htriple)
      (f := C.indicator (fun _ => (1:ℂ))) (g := f) hφmeas h2.1
      (fun (a b : ℂ) => a * b) 1
      (Filter.Eventually.of_forall (fun x => by simp [nnnorm_mul]))
    simpa using this
  have hmain : eLpNorm f (1:ℝ≥0∞) volume
      ≤ ENNReal.ofReal ((2*r)^((d:ℝ)/2)) * eLpNorm f (2:ℝ≥0∞) volume := by
    calc
      eLpNorm f (1:ℝ≥0∞) volume = eLpNorm (C.indicator f) (1:ℝ≥0∞) volume :=
        eLpNorm_congr_ae hsupp'
      _ = eLpNorm (fun x => (C.indicator (fun _ => (1:ℂ))) x * f x) (1:ℝ≥0∞) volume := by rw [hprod]
      _ ≤ eLpNorm (C.indicator (fun _ => (1:ℂ))) (2:ℝ≥0∞) volume
            * eLpNorm f (2:ℝ≥0∞) volume := hholder
      _ = (volume C) ^ (1/2:ℝ) * eLpNorm f (2:ℝ≥0∞) volume := by rw [hφnorm]
      _ = ENNReal.ofReal ((2*r)^((d:ℝ)/2)) * eLpNorm f (2:ℝ≥0∞) volume := by rw [hvolpow]
  refine ⟨⟨h2.1, ?_⟩, ?_⟩
  · exact lt_of_le_of_lt hmain (ENNReal.mul_lt_top ENNReal.ofReal_lt_top h2.2)
  · have hfin : ENNReal.ofReal ((2*r)^((d:ℝ)/2)) * eLpNorm f (2:ℝ≥0∞) volume ≠ ∞ :=
      ENNReal.mul_ne_top ENNReal.ofReal_ne_top h2.2.ne
    have h1 := ENNReal.toReal_mono hfin hmain
    rwa [ENNReal.toReal_mul, ENNReal.toReal_ofReal (Real.rpow_nonneg hr2 _)] at h1

end Commons.Analysis.Fourier