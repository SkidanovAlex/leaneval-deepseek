import Mathlib

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false

/-!
# The arithmetic rearrangement behind the sharp Siegel step

Pure bookkeeping identity: the factor `(N : ℝ) ^ (M * [F : ℚ] / 2)` on the left is the
product over `i : Fin M` of the constant `(N : ℝ) ^ ([F : ℚ] / 2)`, and the two products
over `i` distribute against it.  The only mathematical input is the real power law
`x ^ (y * n) = (x ^ y) ^ n` for `0 ≤ x` (`Real.rpow_mul_natCast`), applied to `x = N ≥ 0`.
-/

namespace Work.BW

theorem sieg2_arith {F : Type*} [Field F] [NumberField F] {M N : ℕ}
    (a : Fin M → Fin N → F) :
    (N : ℝ) ^ ((M : ℝ) * (Module.finrank ℚ F : ℝ) / 2) *
        (∏ i : Fin M, ∏ w : NumberField.InfinitePlace F, (⨆ j : Fin N, w (a i j)) ^ w.mult) *
        (∏ i : Fin M, ∏ᶠ v : NumberField.FinitePlace F, (⨆ j : Fin N, v (a i j)))
      = (∏ i : Fin M, (N : ℝ) ^ ((Module.finrank ℚ F : ℝ) / 2) *
            ∏ w : NumberField.InfinitePlace F, (⨆ j : Fin N, w (a i j)) ^ w.mult) *
          (∏ i : Fin M, ∏ᶠ w : NumberField.FinitePlace F, (⨆ j : Fin N, w (a i j))) := by
  -- `N ^ (M * r / 2) = (N ^ (r / 2)) ^ M` for the nonnegative base `N`
  have hrpow : (N : ℝ) ^ ((M : ℝ) * (Module.finrank ℚ F : ℝ) / 2)
      = ((N : ℝ) ^ ((Module.finrank ℚ F : ℝ) / 2)) ^ M := by
    rw [show (M : ℝ) * (Module.finrank ℚ F : ℝ) / 2
        = ((Module.finrank ℚ F : ℝ) / 2) * (M : ℝ) by ring]
    exact Real.rpow_mul_natCast (Nat.cast_nonneg N) _ _
  rw [hrpow, Finset.prod_mul_distrib, Finset.prod_const, Finset.card_univ, Fintype.card_fin]

end Work.BW
