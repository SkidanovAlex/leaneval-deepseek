import Mathlib
import Submission.Work.FatouDeg.Petal.DefsAux

-- Lean v4.35.0-rc3 / Mathlib 5e0c4e5 made `isDefEq` respect transparency when unifying instances; with it,
-- `ZMod.instField` and `ZMod.commRing` (and `Neg (ZMod p)` via `SubtractionMonoid`) no longer unify, which
-- breaks `ring`/`rw`/module-instance search on `ZMod p`. Restore the v4.34 behaviour for this file.
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false


namespace Work.FatouDeg.Petal

/-- `PowerSeries.trunc n f` written as a sum of monomials with the power-series coefficients. -/
lemma trunc_eq_sum_monomial (n : ℕ) (f : PowerSeries ℂ) :
    PowerSeries.trunc n f
      = ∑ j ∈ Finset.range n, Polynomial.monomial j (PowerSeries.coeff j f) := by
  rw [PowerSeries.trunc_apply, Nat.Ico_zero_eq_range]

/-- `PowerSeries.trunc n f` written as a sum of monomials with the *polynomial* coefficients
of the truncation itself. -/
lemma trunc_eq_sum_monomial_coeff (n : ℕ) (f : PowerSeries ℂ) :
    PowerSeries.trunc n f
      = ∑ j ∈ Finset.range n, Polynomial.monomial j ((PowerSeries.trunc n f).coeff j) := by
  conv_lhs => rw [trunc_eq_sum_monomial]
  apply Finset.sum_congr rfl
  intro j hj
  rw [Finset.mem_range] at hj
  congr 1
  exact ((PowerSeries.coeff_trunc j n f).trans (ite_eq_left hj)).symm

/-- The action of `X * d/dX` on a monomial. -/
lemma X_mul_derivative_monomial (j : ℕ) (c : ℂ) :
    Polynomial.X * Polynomial.derivative (Polynomial.monomial j c)
      = Polynomial.monomial j (c * (j : ℂ)) := by
  rw [Polynomial.derivative_monomial]
  cases j with
  | zero => simp
  | succ k =>
      rw [Nat.succ_sub_one, Polynomial.X_mul_monomial]

/-- The Euler-type operator `p ↦ C n * p - X * p'` applied to a polynomial written as a sum
of monomials of degree `< n`. -/
lemma op_sum (n : ℕ) (c : ℕ → ℂ) :
    Polynomial.C ((n : ℂ)) * (∑ j ∈ Finset.range n, Polynomial.monomial j (c j))
      - Polynomial.X * Polynomial.derivative (∑ j ∈ Finset.range n, Polynomial.monomial j (c j))
    = ∑ j ∈ Finset.range n, Polynomial.monomial j (c j * ((n : ℂ) - (j : ℂ))) := by
  rw [Finset.mul_sum, Polynomial.derivative_sum, Finset.mul_sum, ← Finset.sum_sub_distrib]
  apply Finset.sum_congr rfl
  intro j hj
  rw [Polynomial.C_mul_monomial, X_mul_derivative_monomial, ← Polynomial.monomial_sub]
  congr 1
  ring

/-- **The polynomial algebra behind the corrected chart.**

With `upoly G = 1 - X*G`, `Qpoly m G = trunc (m-1) (upoly G)⁻¹` (the degree `< m-1` truncation of
the formal inverse) and `Ppoly m G = ∑_{j<m-1} monomial j (q_j / (m-1-j))` where `q_j` is the
`j`-th coefficient of `Qpoly m G`, we have

* `(upoly G * Qpoly m G).coeff j = 0` for `0 < j < m-1` and `= 1` for `j = 0`;
* `(m-1) * Ppoly m G - X * (Ppoly m G)' = Qpoly m G`.

Both are coefficient identities; useful Mathlib lemmas are `PowerSeries.coeff_trunc`,
`PowerSeries.coeff_mul_eq_coeff_trunc_mul_trunc₂`, `PowerSeries.mul_inv_cancel`,
`Polynomial.coeff_coe`, `Polynomial.coeff_mul`, `PowerSeries.coeff_coe`. -/
theorem polyAlgebraAux (m : ℕ) (hm : 2 ≤ m) (G : Polynomial ℂ) :
    (∀ j : ℕ, j < m - 1 → ((upoly G) * (Qpoly m G)).coeff j = if j = 0 then 1 else 0) ∧
    Polynomial.C (((m - 1 : ℕ) : ℂ)) * (Ppoly m G)
      - Polynomial.X * (Polynomial.derivative (Ppoly m G)) = Qpoly m G := by
  refine ⟨?_, ?_⟩
  · intro j hj
    set u : PowerSeries ℂ := (upoly G : PowerSeries ℂ) with hu
    have hcc : PowerSeries.constantCoeff u ≠ 0 := by
      rw [hu, ← PowerSeries.coeff_zero_eq_constantCoeff_apply, Polynomial.coeff_coe, upoly]
      simp
    have hinv : u * u⁻¹ = 1 := PowerSeries.mul_inv_cancel _ hcc
    have hQ : ((Qpoly m G : Polynomial ℂ) : PowerSeries ℂ)
        = PowerSeries.trunc (m - 1) u⁻¹ := rfl
    rw [← Polynomial.coeff_coe]
    rw [Polynomial.coe_mul, hQ]
    have hinv' : u * u⁻¹ = (1 : PowerSeries ℂ) := hinv
    calc PowerSeries.coeff j (u * ↑(PowerSeries.trunc (m - 1) u⁻¹))
        = PowerSeries.coeff j
            (PowerSeries.trunc (m - 1) (u * ↑(PowerSeries.trunc (m - 1) u⁻¹))) :=
            (PowerSeries.coeff_coe_trunc_of_lt hj).symm
      _ = PowerSeries.coeff j (PowerSeries.trunc (m - 1) (u * u⁻¹)) := by
            rw [PowerSeries.trunc_mul_trunc]
      _ = PowerSeries.coeff j (u * u⁻¹) := PowerSeries.coeff_coe_trunc_of_lt hj
      _ = if j = 0 then 1 else 0 := by rw [hinv', PowerSeries.coeff_one]
  · have hP : Ppoly m G = ∑ j ∈ Finset.range (m - 1), Polynomial.monomial j
        ((Qpoly m G).coeff j / (((m - 1 : ℕ) : ℂ) - (j : ℂ))) := rfl
    have hQrep : Qpoly m G
        = ∑ j ∈ Finset.range (m - 1), Polynomial.monomial j ((Qpoly m G).coeff j) :=
      trunc_eq_sum_monomial_coeff (m - 1) ((upoly G : PowerSeries ℂ)⁻¹)
    calc Polynomial.C (((m - 1 : ℕ) : ℂ)) * (Ppoly m G)
          - Polynomial.X * (Polynomial.derivative (Ppoly m G))
        = Polynomial.C (((m - 1 : ℕ) : ℂ))
            * (∑ j ∈ Finset.range (m - 1), Polynomial.monomial j
                ((Qpoly m G).coeff j / (((m - 1 : ℕ) : ℂ) - (j : ℂ))))
          - Polynomial.X * Polynomial.derivative (∑ j ∈ Finset.range (m - 1), Polynomial.monomial j
                ((Qpoly m G).coeff j / (((m - 1 : ℕ) : ℂ) - (j : ℂ)))) := by rw [hP]
      _ = ∑ j ∈ Finset.range (m - 1), Polynomial.monomial j
              (((Qpoly m G).coeff j / (((m - 1 : ℕ) : ℂ) - (j : ℂ)))
                * (((m - 1 : ℕ) : ℂ) - (j : ℂ))) :=
            op_sum (m - 1) (fun j => (Qpoly m G).coeff j / (((m - 1 : ℕ) : ℂ) - (j : ℂ)))
      _ = ∑ j ∈ Finset.range (m - 1), Polynomial.monomial j ((Qpoly m G).coeff j) := by
            apply Finset.sum_congr rfl
            intro j hj
            rw [Finset.mem_range] at hj
            congr 1
            have hne : (((m - 1 : ℕ) : ℂ) - (j : ℂ)) ≠ 0 := by
              rw [sub_ne_zero]
              exact fun h => (ne_of_lt hj) (Nat.cast_injective h).symm
            exact div_mul_cancel₀ _ hne
      _ = Qpoly m G := hQrep.symm

end Work.FatouDeg.Petal
