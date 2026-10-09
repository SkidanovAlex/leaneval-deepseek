/-
# The factorisation of a formal group law by its second variable

Every formal group law satisfies `F(X,0) = X` (Mathlib's `FormalGroup.Xzero_eq_X`), hence
`F(X,Y) - X` is divisible by `Y`; by the definitional normalisation of a formal group law the
quotient `Θ` has constant coefficient `1`, i.e. it is a **unit** of the power series ring.

This unit is what makes the Lubin–Tate addition computationally accessible: for the
`𝒪[F]`-action on the torsion points `Λ_n` it produces the "sum formula"

  `(b + d) · x = b · x + (d · x) · H`,   `H ≠ 0`,

of `Eval/smulDiv_add.lean`, which is the substitute for the missing `𝒪[F]`-module structure on
`Λ_n` (see `README.md`).

## Main result

* `NK.LocalReciprocityLubinTate.Eval.FormalGroup.exists_unit_factorization`.
-/
import Mathlib
-- PORT435-BEGIN (v4.35 isDefEq respectTransparency compat)
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- PORT435-END

open MvPowerSeries

namespace NK.LocalReciprocityLubinTate.Eval

/-- **The second-variable factorisation of a formal group law**, with a *unit* factor:
for every formal group law `F` over a commutative ring whose `F(X,Y) - X` is divisible by `Y`,
there is a unit `Θ` of the two-variable power series ring with

  `F(X,Y) = X + Y * Θ`.

The unit is the culprit of the classical identity `F(X,0) = X`: it has constant coefficient `1`
because the coefficient of `Y` in `F` is `1` (`FormalGroup.lin_coeff_Y`). -/
theorem FormalGroup.exists_unit_factorization {R : Type*} [CommRing R] (G : FormalGroup R)
    (hdiv : (MvPowerSeries.X (1 : Fin 2) : MvPowerSeries (Fin 2) R) ∣
      ((G : MvPowerSeries (Fin 2) R) - MvPowerSeries.X 0)) :
    ∃ Θ : MvPowerSeries (Fin 2) R, IsUnit Θ ∧
      (G : MvPowerSeries (Fin 2) R) = MvPowerSeries.X 0 + MvPowerSeries.X 1 * Θ := by
  obtain ⟨Θ, hΘ⟩ := hdiv
  refine ⟨Θ, ?_, ?_⟩
  · -- the constant coefficient of `Θ` is the coefficient of `Y` in `F(X,Y) - X`, i.e. `1`
    rw [isUnit_iff_constantCoeff, ← MvPowerSeries.coeff_zero_eq_constantCoeff_apply]
    have h := congrArg (fun φ : MvPowerSeries (Fin 2) R =>
      MvPowerSeries.coeff (Finsupp.single (1 : Fin 2) 1) φ) hΘ
    have hz : MvPowerSeries.coeff (Finsupp.single (1 : Fin 2) 1)
        (MvPowerSeries.X (0 : Fin 2) : MvPowerSeries (Fin 2) R) = 0 := by
      rw [MvPowerSeries.coeff_X]
      split_ifs with hh
      · exact absurd (congrArg (fun f : Fin 2 →₀ ℕ => f 0) hh) (by simp)
      · rfl
    have hmul : MvPowerSeries.coeff (Finsupp.single (1 : Fin 2) 1)
        ((MvPowerSeries.X (1 : Fin 2) : MvPowerSeries (Fin 2) R) * Θ)
        = MvPowerSeries.coeff 0 Θ := by
      rw [show (MvPowerSeries.X (1 : Fin 2) : MvPowerSeries (Fin 2) R)
          = monomial (Finsupp.single (1 : Fin 2) 1) 1 from rfl]
      rw [MvPowerSeries.coeff_monomial_mul]
      simp
    rw [map_sub, hz, sub_zero, G.lin_coeff_Y, hmul] at h
    rw [h.symm]
    exact isUnit_one
  · rw [← sub_eq_iff_eq_add, ← hΘ]
    ring

end NK.LocalReciprocityLubinTate.Eval
