import Mathlib
import Submission.Commons.NumberTheory.Zeta.eulerProduct_zeta_nat

namespace Commons.NumberTheory.Zeta

open Complex

/-- Green–Tao (10.9) in `HasProd` form: the Euler product of the third local factors converges to the ratio of zeta values.  This is exactly the intermediate `hprod`/`hmain` computation inside the proof of `Commons.NumberTheory.Zeta.tprod_E3_eq_zeta_ratio` (same file), exposed as a standalone `HasProd` statement so that it can be combined with `HasProd.mul`.  NOTE the index set is `ℕ` and the composite indices contribute the neutral factor `1`. -/
theorem hasProd_E3_eq_zeta_ratio (m : ℕ) (z z' : Fin m → ℂ)
    (hz : ∀ j, 0 < (z j).re) (hz' : ∀ j, 0 < (z' j).re) :
    HasProd (fun p : ℕ => if p.Prime then ∏ j : Fin m,
        (1 - (p : ℂ) ^ (-(1 + z j))) * (1 - (p : ℂ) ^ (-(1 + z' j)))
          * (1 - (p : ℂ) ^ (-(1 + z j + z' j)))⁻¹ else 1)
      (∏ j : Fin m,
        riemannZeta (1 + z j + z' j) / (riemannZeta (1 + z j) * riemannZeta (1 + z' j))) := by
  classical
  -- The local factor at a prime `p`, as a function of `p`, has product the `j`-th zeta ratio.
  have key : ∀ j : Fin m,
      HasProd (fun p : ℕ => if p.Prime then
        (1 - (p : ℂ) ^ (-(1 + z j))) * (1 - (p : ℂ) ^ (-(1 + z' j)))
          * (1 - (p : ℂ) ^ (-(1 + z j + z' j)))⁻¹ else 1)
      (riemannZeta (1 + z j + z' j) / (riemannZeta (1 + z j) * riemannZeta (1 + z' j))) := by
    intro j
    have hsj : (1 : ℝ) < (1 + z j).re := by
      simp only [Complex.add_re, Complex.one_re]; linarith [hz j]
    have hsj' : (1 : ℝ) < (1 + z' j).re := by
      simp only [Complex.add_re, Complex.one_re]; linarith [hz' j]
    have hsjj : (1 : ℝ) < (1 + z j + z' j).re := by
      simp only [Complex.add_re, Complex.one_re]; linarith [hz j, hz' j]
    have hA := eulerProduct_zeta_nat (s := 1 + z j) hsj
    have hA' := eulerProduct_zeta_nat (s := 1 + z' j) hsj'
    have hB := eulerProduct_zeta_nat (s := 1 + z j + z' j) hsjj
    -- invert the first two Euler products (all values are nonzero for `Re > 1`)
    have hAi := hA.inv₀ (riemannZeta_ne_zero_of_one_lt_re hsj)
    have hA'i := hA'.inv₀ (riemannZeta_ne_zero_of_one_lt_re hsj')
    have hP := (hAi.mul hA'i).mul hB
    have hv : (riemannZeta (1 + z j))⁻¹ * (riemannZeta (1 + z' j))⁻¹
          * riemannZeta (1 + z j + z' j)
        = riemannZeta (1 + z j + z' j) / (riemannZeta (1 + z j) * riemannZeta (1 + z' j)) := by
      rw [div_eq_mul_inv, mul_inv_rev]; ring
    rw [hv] at hP
    exact hP.congr_fun (fun p => by by_cases hp : p.Prime <;> simp [hp])
  -- Take the finite product over `j` inside the `HasProd`.
  have hprod := hasProd_prod (s := Finset.univ)
      (f := fun j : Fin m => fun p : ℕ => if p.Prime then
        (1 - (p : ℂ) ^ (-(1 + z j))) * (1 - (p : ℂ) ^ (-(1 + z' j)))
          * (1 - (p : ℂ) ^ (-(1 + z j + z' j)))⁻¹ else 1)
      (a := fun j : Fin m =>
        riemannZeta (1 + z j + z' j) / (riemannZeta (1 + z j) * riemannZeta (1 + z' j)))
      (fun j _ => key j)
  refine hprod.congr_fun (fun p => ?_)
  by_cases hp : p.Prime <;> simp [hp]

end Commons.NumberTheory.Zeta
