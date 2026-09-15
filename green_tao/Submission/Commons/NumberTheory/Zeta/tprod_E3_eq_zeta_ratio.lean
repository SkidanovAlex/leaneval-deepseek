import Mathlib
import Submission.Commons.NumberTheory.Zeta.eulerProduct_zeta_nat

namespace Commons.NumberTheory.Zeta

open Complex

/-- Green–Tao (10.9): the Euler product `G₃ = ∏_p E_p^{(3)}` of the third local factor equals the
ratio of zeta values.  Concretely, for `Re z_j > 0`, `Re z'_j > 0`,

`∏'_p (∏_j (1 - p^{-1-z_j})(1 - p^{-1-z'_j})(1 - p^{-1-z_j-z'_j})⁻¹)`
`   = ∏_j ζ(1 + z_j + z'_j) / (ζ(1 + z_j) · ζ(1 + z'_j))`,

where the `∏'_p` is over `ℕ` (the composite indices contribute the neutral factor `1`; write the
summand as `if p.Prime then … else 1`). -/
theorem tprod_E3_eq_zeta_ratio (m : ℕ) (z z' : Fin m → ℂ)
    (hz : ∀ j, 0 < (z j).re) (hz' : ∀ j, 0 < (z' j).re) :
    (∏' p : ℕ, if p.Prime then ∏ j : Fin m,
        (1 - (p : ℂ) ^ (-(1 + z j))) * (1 - (p : ℂ) ^ (-(1 + z' j)))
          * (1 - (p : ℂ) ^ (-(1 + z j + z' j)))⁻¹ else 1)
      = ∏ j : Fin m,
          riemannZeta (1 + z j + z' j) / (riemannZeta (1 + z j) * riemannZeta (1 + z' j)) := by
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
    refine hP.congr_fun (fun p => ?_)
    by_cases hp : p.Prime <;> simp [hp]
  -- Take the finite product over `j` inside the `HasProd`.
  have hprod := hasProd_prod (s := Finset.univ)
      (f := fun j : Fin m => fun p : ℕ => if p.Prime then
        (1 - (p : ℂ) ^ (-(1 + z j))) * (1 - (p : ℂ) ^ (-(1 + z' j)))
          * (1 - (p : ℂ) ^ (-(1 + z j + z' j)))⁻¹ else 1)
      (a := fun j : Fin m =>
        riemannZeta (1 + z j + z' j) / (riemannZeta (1 + z j) * riemannZeta (1 + z' j)))
      (fun j _ => key j)
  have hmain : ∏' p : ℕ, ∏ j : Fin m, (if p.Prime then
        (1 - (p : ℂ) ^ (-(1 + z j))) * (1 - (p : ℂ) ^ (-(1 + z' j)))
          * (1 - (p : ℂ) ^ (-(1 + z j + z' j)))⁻¹ else 1)
      = ∏ j : Fin m,
          riemannZeta (1 + z j + z' j) / (riemannZeta (1 + z j) * riemannZeta (1 + z' j)) := by
    have := hprod.tprod_eq
    simpa using this
  rw [← hmain]
  refine tprod_congr (fun p => ?_)
  by_cases hp : p.Prime <;> simp [hp]

end Commons.NumberTheory.Zeta
