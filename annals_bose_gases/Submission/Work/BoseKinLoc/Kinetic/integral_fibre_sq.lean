import Mathlib.MeasureTheory.Integral.Prod
import Mathlib.Analysis.Calculus.ContDiff.Defs
import Mathlib.Analysis.Normed.Lp.MeasurableSpace
import Submission.Work.BoseKinLoc.Defs
-- PORT435-BEGIN (v4.35 isDefEq respectTransparency compat)
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- PORT435-END

namespace Work.BoseKinLoc.Kinetic

open MeasureTheory

theorem integral_fibre_sq {n : ℕ} {Φ : Submission.BoseGases.X (n + 1) → ℝ}
    (hΦ : ContDiff ℝ (⊤ : ENat) Φ) (hcs : HasCompactSupport Φ) (i : Fin (n + 1)) :
    MeasureTheory.Integrable
        (fun r : Submission.BoseGases.X n =>
          ∫ z : EuclideanSpace ℝ (Fin 3), (Φ (Submission.BoseGases.kcInsN n i (z, r))) ^ 2)
      ∧ (∫ r : Submission.BoseGases.X n,
            ∫ z : EuclideanSpace ℝ (Fin 3), (Φ (Submission.BoseGases.kcInsN n i (z, r))) ^ 2)
          = ∫ x : Submission.BoseGases.X (n + 1), (Φ x) ^ 2 := by
  have hcont : Continuous (fun x : Submission.BoseGases.X (n + 1) => (Φ x) ^ 2) := by
    fun_prop
  have hcs2 : HasCompactSupport (fun x : Submission.BoseGases.X (n + 1) => (Φ x) ^ 2) :=
    hcs.comp_left (g := fun t : ℝ => t ^ 2) (by norm_num)
  have h2 : Integrable (fun x : Submission.BoseGases.X (n + 1) => (Φ x) ^ 2) :=
    hcont.integrable_of_hasCompactSupport hcs2
  have hmp : MeasurePreserving (⇑(Submission.BoseGases.kcInsN n i)) volume volume :=
    Submission.BoseGases.kc_mp_insN n i
  have hInt : Integrable
      (fun p : EuclideanSpace ℝ (Fin 3) × Submission.BoseGases.X n =>
        (Φ (Submission.BoseGases.kcInsN n i p)) ^ 2) :=
    (hmp.integrable_comp h2.aestronglyMeasurable).mpr h2
  refine ⟨?_, ?_⟩
  · simpa using hInt.integral_prod_right
  · calc
      (∫ r : Submission.BoseGases.X n,
          ∫ z : EuclideanSpace ℝ (Fin 3), (Φ (Submission.BoseGases.kcInsN n i (z, r))) ^ 2)
          = ∫ p : EuclideanSpace ℝ (Fin 3) × Submission.BoseGases.X n,
              (Φ (Submission.BoseGases.kcInsN n i p)) ^ 2 :=
            (integral_prod_symm
              (fun p : EuclideanSpace ℝ (Fin 3) × Submission.BoseGases.X n =>
                (Φ (Submission.BoseGases.kcInsN n i p)) ^ 2) hInt).symm
      _ = ∫ x : Submission.BoseGases.X (n + 1), (Φ x) ^ 2 :=
            hmp.integral_comp' (fun x : Submission.BoseGases.X (n + 1) => (Φ x) ^ 2)

end Work.BoseKinLoc.Kinetic
