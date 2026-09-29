import Mathlib

namespace Work.Holonomy3

/-- Compatibility of `MvPowerSeries.finSuccEquiv` with the coercion of multivariable
*polynomials*: the image of a polynomial `p ∈ R[X_0,..,X_n]` (embedded in the power series ring) is
the image of `MvPolynomial.finSuccEquiv R n p ∈ R[X_1,..,X_n][X_0]` under `Polynomial.map` along the
coercion `R[X_1,..,X_n] → R⟦X_1,..,X_n⟧`.  (In particular the image is again a *polynomial* in the
outer variable `X`.)  Proof: `PowerSeries.ext` in `k`, `MvPowerSeries.ext` in `x`, then
`MvPowerSeries.coeff_coeff_finSuccEquiv`, `Polynomial.coeff_map`, `MvPolynomial.coeff_coe` and
`MvPolynomial.finSuccEquiv_coeff_coeff`. -/
lemma finSuccEquiv_coe_mvPolynomial {n : ℕ} {R : Type*} [CommSemiring R]
    (p : MvPolynomial (Fin (n + 1)) R) :
    MvPowerSeries.finSuccEquiv R n (p : MvPowerSeries (Fin (n + 1)) R)
      = ((Polynomial.map MvPolynomial.coeToMvPowerSeries.ringHom
            (MvPolynomial.finSuccEquiv R n p) : Polynomial (MvPowerSeries (Fin n) R)) :
          PowerSeries (MvPowerSeries (Fin n) R)) := by
  ext k x
  simp only [MvPowerSeries.coeff_coeff_finSuccEquiv, Polynomial.coeff_coe, Polynomial.coeff_map,
      MvPolynomial.coeToMvPowerSeries.ringHom_apply, MvPolynomial.coeff_coe,
      MvPolynomial.finSuccEquiv_coeff_coeff]

end Work.Holonomy3
