import Mathlib
import Submission.Work.KMTAreas.A4.symbolRatioDefs

namespace Work.KMTAreas.A4

/-- **The complex IW symbol is the complexification of the real one.**

`Work.Analysis.IonescuWainger.etaCut kmtEta k` is the complexification of
`Work.KMTAreas.A4.bumpRescaled k` (definitionally, `etaCut kmtEta k θ = ((bumpRescaled k θ : ℝ) : ℂ)`),
and `bumpRescaled k` vanishes off `[-2^k, 2^k]`, so for any `R ≥ 2^k` its periodisation at a point
`ξ : ℝ/ℤ` is the finite sum over `Work.KMTAreas.A4.suppIdx R` of its translates, and the whole
symbol is the complexification of the real sum.

Route: `Work.KMTAreas.A4.periodize_eq_sum_of_support` (`Submission/Work/KMTAreas/A4/symbolRatioDefs.lean`)
gives `periodize φ ξ = ∑ j ∈ suppIdx R, φ (x + j)` for `φ` supported in `[-R,R]`, `R ≥ 0`;
apply it with `φ = etaCut kmtEta k`, `R` (using `Work.KMTAreas.A4.etaCut_eq_zero` for the
support condition, which needs `2^k < |x|` from `R < |x|` and `2^k ≤ R`), then `etaCut_eq_ofReal`
termwise and `Complex.ofReal_sum` for the outer `Finset.sum`. -/
theorem symbolOfReal (ρ : ℝ) (l : ℕ) (k : ℤ) {R : ℝ} (hR : (2 : ℝ) ^ k ≤ R)
    (ξ : Work.Analysis.IonescuWainger.Circle) :
    Work.Analysis.IonescuWainger.iwSymbolSet (Work.Analysis.IonescuWainger.iwArithFreqs ρ l)
        (Work.Analysis.IonescuWainger.periodize
          (Work.Analysis.IonescuWainger.etaCut Work.KMTContract.kmtEta k)) ξ
      = ((Work.KMTAreas.A4.symReal ρ l k R ξ : ℝ) : ℂ) := by
  have h2k : (0 : ℝ) < (2 : ℝ) ^ k := zpow_pos (by norm_num) k
  have hR0 : 0 ≤ R := le_trans h2k.le hR
  rw [Work.Analysis.IonescuWainger.iwSymbolSet_apply, symReal, Complex.ofReal_sum]
  refine Finset.sum_congr rfl fun α _ => ?_
  rw [periodize_eq_sum_of_support hR0
    (fun x hx => etaCut_eq_zero (lt_of_le_of_lt hR hx)) (ξ - α)]
  rw [Complex.ofReal_sum]
  exact Finset.sum_congr rfl fun j _ => etaCut_eq_ofReal k _

end Work.KMTAreas.A4
