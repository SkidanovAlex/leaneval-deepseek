/-
# `Submission.Work.FIArea6Hecke.R.heckeStripWBoundDefs`

The Phragmén–Lindelöf weight used for the strip bound `1/2 ≤ re s ≤ 1` of the Hecke `L`-function.

    `heckeStripW d z = ((4d)^20)^(1 - z) · (Γ(2 - z/2)/Γ(1 + z/2))^20 · (log (4d·(z+2)))^8`

On the strip `1/2 ≤ re z ≤ 1` its modulus is comparable to
`(4d(2+|im z|))^(20(1-re z))·log^8(4d(2+|im z|))`: the two factors `(4d)^{20(1-z)}` and the
`20`-th power of the Γ-ratio produce the `d`- and `|im|`-powers, and the logarithmic factor
supplies the `log`-powers which are needed because the boundary bound at `re z = 1` is only a
power of `log(4d(2+|im z|))`.
-/
import Mathlib
import Submission.Work.FIArea5.S16Hecke.ThetaDefs
import Submission.Work.FIArea6Hecke.StripCoreDefs
import Submission.Work.FIPlan.Interface

namespace Work.FIArea6Hecke.R

open scoped BigOperators

noncomputable section

attribute [local instance] Classical.propDecidable

/-- The Phragmén–Lindelöf weight of the strip `1/2 ≤ re s ≤ 1`. -/
def heckeStripW (d : ℕ) (z : ℂ) : ℂ :=
  ((((4 * (d : ℝ)) ^ (20 : ℕ) : ℝ)) : ℂ) ^ (1 - z) *
    (Complex.Gamma (2 - z / 2) / Complex.Gamma (1 + z / 2)) ^ (20 : ℕ) *
    (Complex.log (((4 * (d : ℝ)) : ℂ) * (z + 2))) ^ (8 : ℕ)

/-- The primary fundamental domain of `ℤ[i]/(4d)`: the primary elements of the box
`gBox (4d - 1)` in the first quadrant. -/
def primaryFund (d : ℕ) : Finset GaussianInt :=
  (Work.FIPlan.gBox (((4 * d : ℕ) : ℤ) - 1)).filter
    (fun z => Work.FIPlan.IsPrimary z ∧ 0 ≤ z.re ∧ 0 ≤ z.im)

/-- The primary elements of modulus `≤ X`: the disc sum of a strict character over this set is the
summatory function whose cancellation drives the bound at `re s = 1`. -/
def primaryBox (d : ℕ) (X : ℝ) : Finset GaussianInt :=
  (Work.FIPlan.gBox ⌈X⌉₊).filter
    (fun z => Work.FIPlan.IsPrimary z ∧ (Work.FIPlan.gnorm z : ℝ) ≤ X)

/-- The `if`-form of the disc sum, matching the shape used by the Abel-summation bound. -/
lemma primaryBox_sum_eq (d : ℕ) (X : ℝ) (chi : GaussianInt → ℂ) :
    (∑ z ∈ primaryBox d X, chi z) =
      ∑ z ∈ Work.FIPlan.gBox ⌈X⌉₊,
        (if Work.FIPlan.IsPrimary z ∧ (Work.FIPlan.gnorm z : ℝ) ≤ X then chi z else 0) := by
  rw [primaryBox, Finset.sum_filter]

/-- The `if`-form of the mean over the primary fundamental domain. -/
lemma primaryFund_sum_eq (d : ℕ) (chi : GaussianInt → ℂ) :
    (∑ z ∈ primaryFund d, chi z) =
      ∑ z ∈ Work.FIPlan.gBox (((4 * d : ℕ) : ℤ) - 1),
        (if Work.FIPlan.IsPrimary z ∧ 0 ≤ z.re ∧ 0 ≤ z.im then chi z else 0) := by
  rw [primaryFund, Finset.sum_filter]

end

end Work.FIArea6Hecke.R
