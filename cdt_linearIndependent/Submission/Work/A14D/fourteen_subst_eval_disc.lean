import Mathlib
import Submission.Work.A14.defs
import Submission.Work.A14D.fourteen_coeff_bounds
import Submission.Work.C17I.seventeen_subst_eval_disc

namespace Work.A14D

/-- The absolute series of `sympY` at radius `ρ = 34/100` sums to `(34/100)²/(1-34/100) < 1/5`. -/
private lemma sympY_abs_lt_fifth :
    (∑' k : ℕ, ‖((PowerSeries.coeff k Submission.CDT.sympY : ℚ) : ℂ)‖ * (34 / 100 : ℝ) ^ k)
      < 1 / 5 := by
  have hsum := Work.C17I.sympY_norm_hasSum (ρ := 34 / 100) (by norm_num) (by norm_num)
  rw [hsum.tsum_eq]
  norm_num

/-- The substitution/evaluation identity on the disc `‖z‖ ≤ 34/100` for the fourteen functions of
Theorem A: for each slot `i`, the substituted series `(fourteen a b c i).subst sympY` converges at
`z` to the value of the `y`-series at `y = yC z = z²/(z−1)`.

This is the `Fin 14` analogue of the proved `Work.C17I.seventeen_subst_eval_disc`
(`Submission/Work/C17I/seventeen_subst_eval_disc.lean`), whose engine
`Work.C17I.subst_eval_abs` is generic in the series: it needs (i) a coefficient bound
`‖[yᵏ]fᵢ‖ · Rᵏ ≤ C` with `R > 1/5` (`hbou`, supplied by `Work.A14D.fourteen_coeff_bounds`),
(ii) `constantCoeff sympY = 0` (`Submission.CDT.coeff_sympY_zero`), (iii) the absolute convergence
of `sympY` at `ρ = 34/100` with `Σ ‖coeff sympY‖ ρᵏ < R` (`Work.C17I.sympY_norm_hasSum`), and
finally `Σ k [xᵏ]sympY · zᵏ = yC z` (`Work.C17I.sympY_hasSum`; `Work.A14D.yC` is definitionally
`Work.C17.yC`).  It identifies each pullback function with the corresponding `y`-series evaluation,
which is what turns `Work.A14D.pullback_rel_disc_A` into a relation among the analytic functions
`Hfun z + Hfun (wC z)`, etc. -/
theorem fourteen_subst_eval_disc (a b c : ℤ) (h : Submission.CDTPlan.ARel a b c)
    (hbou : ∀ i : Fin 14, ∃ C R : ℝ, 0 < C ∧ 1 / 5 < R ∧ R ≤ 1 ∧ ∀ k : ℕ,
      ‖((PowerSeries.coeff k (Submission.CDTPlan.fourteen a b c i) : ℚ) : ℂ)‖ * R ^ k ≤ C) :
    ∀ i : Fin 14, ∀ z : ℂ, ‖z‖ ≤ (34 : ℝ) / 100 →
      HasSum (fun k : ℕ =>
          ((PowerSeries.coeff k
            ((Submission.CDTPlan.fourteen a b c i).subst Submission.CDT.sympY) : ℚ) : ℂ) * z ^ k)
        (∑' k : ℕ, ((PowerSeries.coeff k (Submission.CDTPlan.fourteen a b c i) : ℚ) : ℂ)
          * (yC z) ^ k) := by
  intro i z hz
  obtain ⟨C, R, hC, hR5, _hR1, hb⟩ := hbou i
  have hRpos : (0 : ℝ) < R := by linarith
  have hzlt : ‖z‖ < 1 := lt_of_le_of_lt hz (by norm_num)
  have hsum : HasSum
      (fun k : ℕ => ‖((PowerSeries.coeff k Submission.CDT.sympY : ℚ) : ℂ)‖ * (34 / 100 : ℝ) ^ k)
      (((34 : ℝ) / 100) ^ 2 / (1 - 34 / 100)) :=
    Work.C17I.sympY_norm_hasSum (by norm_num) (by norm_num)
  have hgS : Summable
      (fun k : ℕ => ‖((PowerSeries.coeff k Submission.CDT.sympY : ℚ) : ℂ)‖ * (34 / 100 : ℝ) ^ k) :=
    hsum.summable
  have hgR : (∑' k : ℕ,
      ‖((PowerSeries.coeff k Submission.CDT.sympY : ℚ) : ℂ)‖ * (34 / 100 : ℝ) ^ k) < R :=
    lt_trans sympY_abs_lt_fifth hR5
  have hg0 : PowerSeries.constantCoeff Submission.CDT.sympY = 0 := by
    rw [← PowerSeries.coeff_zero_eq_constantCoeff_apply]
    exact Submission.CDT.coeff_sympY_zero
  have hkey := Work.C17I.subst_eval_abs
    (f := Submission.CDTPlan.fourteen a b c i) (g := Submission.CDT.sympY)
    (C := C) (R := R) (ρ := 34 / 100) (z := z)
    hC.le (by norm_num) hRpos hg0 hb hgS hgR hz
  have hsymp : (∑' m : ℕ, ((PowerSeries.coeff m Submission.CDT.sympY : ℚ) : ℂ) * z ^ m)
      = yC z := by
    rw [(Work.C17I.sympY_hasSum z hzlt).tsum_eq]
    rfl
  rw [hsymp] at hkey
  exact hkey

end Work.A14D
