import Mathlib
import Submission.Work.A14.defs
import Submission.Work.A14D.LC_setup
import Submission.Work.C17I.pullback_rel_disc

namespace Work.A14D

/-- The pullback relation on the disc `‖z‖ ≤ 34/100`: from a `ℚ`-relation among the fourteen
`y`-series `fourteen a b c` (hypothesis `hrel`) together with the coefficient bounds `hbou`
(rate `R > 1/5`), the relation still holds after evaluating each `y`-series at `y = yC z = z²/(z-1)`.
This is the exact `Fin 14` analogue of the proved `Work.C17I.pullback_rel_disc`
(`Submission/Work/C17I/pullback_rel_disc.lean`); its helpers `Work.C17I.evp_sum`,
`Work.C17I.evp_poly_mul`, `Work.C17I.summable_of_rate_bound` and `Work.C17I.yC_norm_lt_fifth` are
all generic (arbitrary `PowerSeries ℚ` / arbitrary coefficient family), so the proof goes through
verbatim with `Fin 17 → Fin 14` and `seventeen → fourteen`. -/
theorem pullback_rel_disc_A (a b c : ℤ) (h : Submission.CDTPlan.ARel a b c) (P : Fin 14 → Polynomial ℚ)
    (hrel : ∑ i : Fin 14, (P i : PowerSeries ℚ) * Submission.CDTPlan.fourteen a b c i = 0)
    (hbou : ∀ i : Fin 14, ∃ C R : ℝ, 0 < C ∧ 1 / 5 < R ∧ R ≤ 1 ∧ ∀ k : ℕ,
      ‖((PowerSeries.coeff k (Submission.CDTPlan.fourteen a b c i) : ℚ) : ℂ)‖ * R ^ k ≤ C) :
    ∀ z : ℂ, ‖z‖ ≤ (34 : ℝ) / 100 →
      ∑ i : Fin 14, (P i).eval₂ (algebraMap ℚ ℂ) (yC z)
        * (∑' k : ℕ, ((PowerSeries.coeff k (Submission.CDTPlan.fourteen a b c i) : ℚ) : ℂ)
            * (yC z) ^ k) = 0 := by
  intro z hz
  -- `yC` is defined by the same formula as `Work.C17.yC`, so the generic norm estimate applies.
  have hw5 : ‖yC z‖ < 1 / 5 := Work.C17I.yC_norm_lt_fifth z hz
  have hS : ∀ i : Fin 14, Summable (fun k : ℕ =>
      ((PowerSeries.coeff k (Submission.CDTPlan.fourteen a b c i) : ℚ) : ℂ)
        * (yC z) ^ k) := by
    intro i
    obtain ⟨C, R, hC, hR5, _hR1, hb⟩ := hbou i
    exact Work.C17I.summable_of_rate_bound hC (by linarith) hb (lt_trans hw5 hR5)
  have hprod := fun i : Fin 14 => Work.C17I.evp_poly_mul (P i)
    (Submission.CDTPlan.fourteen a b c i) (yC z) (hS i)
  calc ∑ i : Fin 14, (P i).eval₂ (algebraMap ℚ ℂ) (yC z)
        * (∑' k : ℕ, ((PowerSeries.coeff k (Submission.CDTPlan.fourteen a b c i) : ℚ) : ℂ)
            * (yC z) ^ k)
      = ∑ i : Fin 14, Work.CPull.evp ((P i : PowerSeries ℚ)
          * Submission.CDTPlan.fourteen a b c i) (yC z) :=
        Finset.sum_congr rfl (fun i _ => (hprod i).2)
    _ = Work.CPull.evp (∑ i : Fin 14, (P i : PowerSeries ℚ)
          * Submission.CDTPlan.fourteen a b c i) (yC z) :=
        (Work.C17I.evp_sum Finset.univ
          (fun i : Fin 14 => (P i : PowerSeries ℚ)
            * Submission.CDTPlan.fourteen a b c i)
          (yC z) (fun i _ => (hprod i).1)).symm
    _ = Work.CPull.evp 0 (yC z) := by rw [hrel]
    _ = 0 := Work.CPull.evp_zero (yC z)

end Work.A14D
