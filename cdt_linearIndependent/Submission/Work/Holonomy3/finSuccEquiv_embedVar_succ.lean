import Mathlib
import Submission.Work.Holonomy3.aux_defs

namespace Work.Holonomy3

/-- The image under `MvPowerSeries.finSuccEquiv` (`X 0 ↦ X`, `X (j+1) ↦ C (X j)`) of the series
`embedVar j.succ g` (a series in the single variable `X (j+1)`) is the *constant* series
`PowerSeries.C (embedVar j g)`, i.e. the same series viewed as a series in `X_1..X_n` placed in the
coefficient ring.  Proof: `PowerSeries.ext` in `k`, `MvPowerSeries.ext` in `x`, then
`MvPowerSeries.coeff_coeff_finSuccEquiv` and `Finsupp.cons_eq_single_succ_iff`. -/
lemma finSuccEquiv_embedVar_succ {n : ℕ} (j : Fin n) (g : PowerSeries ℚ) :
    MvPowerSeries.finSuccEquiv ℚ n (Submission.CDTPlan.embedVar j.succ g)
      = PowerSeries.C (Submission.CDTPlan.embedVar j g) := by
  ext k x
  rw [MvPowerSeries.coeff_coeff_finSuccEquiv, PowerSeries.coeff_C]
  have hR : MvPowerSeries.coeff x (Submission.CDTPlan.embedVar j g)
      = (if x = Finsupp.single j (x j) then PowerSeries.coeff (x j) g else 0) := rfl
  have hcond : (Finsupp.cons k x = Finsupp.single j.succ (x j)) ↔
      (x = Finsupp.single j (x j) ∧ k = 0) := Finsupp.cons_eq_single_succ_iff j
  by_cases hk : k = 0
  · rw [if_pos hk]
    show (if Finsupp.cons k x = Finsupp.single j.succ ((Finsupp.cons k x) j.succ) then
        PowerSeries.coeff ((Finsupp.cons k x) j.succ) g else 0)
      = MvPowerSeries.coeff x (Submission.CDTPlan.embedVar j g)
    rw [Finsupp.cons_succ]
    rw [hR]
    by_cases hx : x = Finsupp.single j (x j)
    · rw [if_pos (hcond.mpr ⟨hx, hk⟩), if_pos hx]
    · rw [if_neg (fun h => hx (hcond.mp h).1), if_neg hx]
  · rw [if_neg hk]
    show (if Finsupp.cons k x = Finsupp.single j.succ ((Finsupp.cons k x) j.succ) then
        PowerSeries.coeff ((Finsupp.cons k x) j.succ) g else 0)
      = (0 : ℚ)
    rw [Finsupp.cons_succ]
    rw [if_neg (fun h => hk (hcond.mp h).2)]

end Work.Holonomy3
