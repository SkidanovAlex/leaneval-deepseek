import Mathlib
import Submission.Work.BW.mixedCoordAux

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false

/-!
# The product of the per-place bounds, raised to the place multiplicities

At a real infinite place `v` the bound `placeBound ρ v` equals `ρ` and the multiplicity `v.mult`
is `1`; at a complex place it equals `√2 · ρ` and the multiplicity is `2`. Hence

`∏ v, placeBound ρ v ^ v.mult = ρ ^ nrRealPlaces F * (2 * ρ ^ 2) ^ nrComplexPlaces F
  = ρ ^ (finrank ℚ F) * 2 ^ nrComplexPlaces F`,

using `nrRealPlaces F + 2 * nrComplexPlaces F = finrank ℚ F`. In particular the product is bounded
by `ρ ^ (finrank ℚ F) * 2 ^ nrComplexPlaces F`.
-/

namespace Work.BW

open NumberField NumberField.InfinitePlace

lemma prod_place_pow_le {F : Type*} [Field F] [NumberField F] (ρ : ℝ) :
    (∏ v : NumberField.InfinitePlace F, (Work.BW.placeBound (F := F) ρ v) ^ v.mult)
      ≤ ρ ^ (Module.finrank ℚ F) * 2 ^ (NumberField.InfinitePlace.nrComplexPlaces F) := by
  classical
  have h1 : (∏ w : {w : InfinitePlace F // IsReal w}, placeBound ρ w.1 ^ w.1.mult)
      = ρ ^ nrRealPlaces F := by
    rw [show (∏ w : {w : InfinitePlace F // IsReal w}, placeBound ρ w.1 ^ w.1.mult)
          = ∏ _w : {w : InfinitePlace F // IsReal w}, ρ from by
        apply Finset.prod_congr rfl
        intro w _
        rw [placeBound_of_isReal w.2, w.2.mult_eq_one, pow_one]]
    rw [Finset.prod_const, Finset.card_univ]
  have h2 : (∏ w : {w : InfinitePlace F // IsComplex w}, placeBound ρ w.1 ^ w.1.mult)
      = (2 * ρ^2) ^ nrComplexPlaces F := by
    rw [show (∏ w : {w : InfinitePlace F // IsComplex w}, placeBound ρ w.1 ^ w.1.mult)
          = ∏ _w : {w : InfinitePlace F // IsComplex w}, (2 * ρ^2) from by
        apply Finset.prod_congr rfl
        intro w _
        rw [placeBound_of_isComplex w.2, w.2.mult_eq_two, mul_pow,
          Real.sq_sqrt (by norm_num : (0 : ℝ) ≤ 2)]]
    rw [Finset.prod_const, Finset.card_univ]
  rw [prod_eq_prod_mul_prod, h1, h2, mul_pow, ← pow_mul, ← card_add_two_mul_card_eq_rank,
    pow_add]
  exact le_of_eq (by ring)

end Work.BW
