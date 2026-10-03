/-
# The weight functions of the variational bound `Work.KMTPlan.A6.weightVarBound`

This module contains the *definitions* used by `weightVarBound.lean`: the polynomials (in the
reciprocal variable `u = 1/y`) that the three weights of `weightVarBound` become, together with
their coefficient-sum constants.

For `P ∈ ℤ[X]` with `d = P.natDegree ≥ 1` and `y > 0`, with `u = 1/y`,

* `PderivR P y / y^{d-1} = Phi1u P u`,
* `PderivR P y = y^{d-1} * Phi1u P u`,
* `Pderiv2R P y = y^{d-2} * Phi2u P u`.

So all three sequences of `weightVarBound` are of the form `u ↦ φ(u_n)` with `u_n ↦ 0` antitone,
which is what makes their `r`-variation uniformly bounded.  The constants below are the obvious
coefficient sums: `Phi1uConst`/`Phi2uConst` bound the functions on `[0,1]` and
`Phi1uLip`/`Phi2uLip` are their Lipschitz constants there.
-/
import Mathlib

namespace Work.KMTPlan.A6

open Polynomial Finset

noncomputable section

/-- The `j`-th coefficient of `P'` in the monomial form `P'(y) = ∑_j der1Coeff P j * y^j`. -/
def der1Coeff (P : Polynomial ℤ) (j : ℕ) : ℝ := ((P.coeff (j + 1) * ((j + 1 : ℕ) : ℤ) : ℤ) : ℝ)

/-- The `j`-th coefficient of `P''` in the monomial form `P''(y) = ∑_j der2Coeff P j * y^j`. -/
def der2Coeff (P : Polynomial ℤ) (j : ℕ) : ℝ :=
  ((P.coeff (j + 2) * (((j + 2 : ℕ) * (j + 1 : ℕ) : ℕ) : ℤ) : ℤ) : ℝ)

/-- `Phi1u P u = ∑_j der1Coeff P j * u^(d-1-j)`, the weight `P'(y)/y^(d-1)` in `u = 1/y`. -/
def Phi1u (P : Polynomial ℤ) (u : ℝ) : ℝ :=
  ∑ j ∈ Finset.range P.natDegree, der1Coeff P j * u ^ (P.natDegree - 1 - j)

/-- `Phi2u P u = ∑_j der2Coeff P j * u^(d-2-j)`, the weight `P''(y)/y^(d-2)` in `u = 1/y`. -/
def Phi2u (P : Polynomial ℤ) (u : ℝ) : ℝ :=
  ∑ j ∈ Finset.range (P.natDegree - 1), der2Coeff P j * u ^ (P.natDegree - 2 - j)

/-- `∑_j |der1Coeff P j|`, a bound for `|Phi1u P u|` on `[0,1]`. -/
def Phi1uConst (P : Polynomial ℤ) : ℝ := ∑ j ∈ Finset.range P.natDegree, |der1Coeff P j|

/-- `∑_j |der1Coeff P j| * (d-1-j)`, a Lipschitz constant for `Phi1u P` on `[0,1]`. -/
def Phi1uLip (P : Polynomial ℤ) : ℝ :=
  ∑ j ∈ Finset.range P.natDegree, |der1Coeff P j| * ((P.natDegree - 1 - j : ℕ) : ℝ)

/-- `∑_j |der2Coeff P j|`, a bound for `|Phi2u P u|` on `[0,1]`. -/
def Phi2uConst (P : Polynomial ℤ) : ℝ := ∑ j ∈ Finset.range (P.natDegree - 1), |der2Coeff P j|

/-- `∑_j |der2Coeff P j| * (d-2-j)`, a Lipschitz constant for `Phi2u P` on `[0,1]`. -/
def Phi2uLip (P : Polynomial ℤ) : ℝ :=
  ∑ j ∈ Finset.range (P.natDegree - 1), |der2Coeff P j| * ((P.natDegree - 2 - j : ℕ) : ℝ)

/-- `|u ^ n - v ^ n| ≤ n * |u - v|` for `u, v ∈ [0,1]`: the elementary Lipschitz bound on powers. -/
theorem abs_pow_sub_pow_le_one (n : ℕ) {u v : ℝ} (hu : 0 ≤ u) (hu1 : u ≤ 1) (hv : 0 ≤ v)
    (hv1 : v ≤ 1) : |u ^ n - v ^ n| ≤ (n : ℝ) * |u - v| := by
  have h := abs_pow_sub_pow_le u v n
  have hu' : |u| ≤ 1 := abs_le.mpr ⟨by linarith, hu1⟩
  have hv' : |v| ≤ 1 := abs_le.mpr ⟨by linarith, hv1⟩
  have hmax : max |u| |v| ^ (n - 1) ≤ 1 := by
    rcases Nat.eq_zero_or_pos n with h0 | hpos
    · subst h0; simp
    · exact pow_le_one₀ (le_trans (abs_nonneg u) (le_max_left _ _)) (max_le hu' hv')
  calc |u ^ n - v ^ n| ≤ |u - v| * (n : ℝ) * max |u| |v| ^ (n - 1) := h
    _ ≤ |u - v| * (n : ℝ) * 1 := by gcongr
    _ = (n : ℝ) * |u - v| := by ring

end

end Work.KMTPlan.A6
