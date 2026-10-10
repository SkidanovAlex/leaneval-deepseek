import Mathlib
import Submission.Work.MotC5N3.Defs
import Submission.Work.MotV5.Defs
import Submission.Work.MotV.Defs
import Submission.Work.MotC5N3.GenAux_relfinrank_bot_adjoin_genX

set_option linter.unusedVariables false -- v435-speed

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

namespace Work.MotC5N3
open Work.MotV5
/-- **Nontriviality of the projective fifth-torsion shift on the Klein field.**

For good Klein data `D` over a field `𝕜` of characteristic `5` and a projective fifth-torsion
shift `σS` (`σS κ_i = λ κ_{i+1}`, `λ ≠ 0`; this is `Work.MotC5N3.KleinData.ShiftOf D σS`), the
`Work.MotC5N3.KbA K`-automorphism `σS` does not fix `Work.MotC5N3.kleinField K D` pointwise.

Proof route.  Write `κ i := Work.MotV.kleinCoord D (Work.MotC5N3.KbA K) i` and `r i := κ i / κ 0`, so
that `Work.MotC5N3.kleinField K D = IntermediateField.adjoin (K) (Set.range r)` (definitional; use
`IntermediateField.subset_adjoin`, `Set.mem_range_self` for membership of the `r i`) and
`κ 0 ≠ 0` (`D.Good.coord0_ne`).

* From `hσS` obtain `lam ≠ 0` with `σS (κ i) = lam * κ (i+1)` (indices cyclic in `Fin 5`: the
  addition is `Fin`-addition, so `(4 : Fin 5) + 1 = 0`).  Since `lam` cancels in ratios,
  `σS (r i) = r (i+1) / r 1` for all `i` (use `map_div₀`, `mul_div_mul_left _ _ hlam`,
  `div_div_div_cancel_right₀ _ hκ0`).
* Assume for contradiction `∀ z ∈ Work.MotC5N3.kleinField K D, σS z = z`.  Then `r (i+1) = r i * r 1` for all `i`
  (`div_eq_iff` with `r 1 ≠ 0`; `r 1 ≠ 0` itself follows from the `i = 0` case: it gives
  `r 1 / r 1 = r 0 = 1`, so `r 1 = 0` would give `0 = 1`).  Hence `r 2 = r 1^2`, `r 3 = r 1^3`,
  `r 4 = r 1^4`, and `r 0 = r 4 * r 1 = r 1^5`; as `r 0 = 1`, this gives `r 1^5 = 1`.
* In characteristic `5`, `r 1 ^ 5 = 1` forces `r 1 = 1` (e.g. `sub_pow_char` gives
  `(r1 - 1)^5 = r1^5 - 1^5 = 0`), whence `r i = 1` and `κ i = κ 0` for all `i`
  (`div_eq_one_iff_eq hκ0`).
* Contradicts `D.Good.spans`: put `c m i := algebraMap (Work.MotC5N3.KbA K) (Work.MotC5N3.OmA K D) (algebraMap 𝕜 (Work.MotC5N3.KbA K) (e m i))`
  and `S m := ∑ i, c m i = algebraMap (Work.MotC5N3.KbA K) (Work.MotC5N3.OmA K D) (s m)`, `s m := ∑ i, algebraMap 𝕜 (Work.MotC5N3.KbA K) (e m i)`
  (`map_sum`), so that `kleinBas D (Work.MotC5N3.KbA K) m = S m * κ 0` for every `m` (rewrite `κ i = κ 0` and
  `Finset.sum_mul`).  For `m = 0` this is `1 = S 0 * κ 0` (`kleinBas D (Work.MotC5N3.KbA K) 0 = 1`), so `S 0 ≠ 0`
  and `κ 0 = S 0⁻¹`; for `m = 1` it is
  `genX (D.E.baseChange (Work.MotC5N3.KbA K)) = S 1 * κ 0 = algebraMap (Work.MotC5N3.KbA K) (Work.MotC5N3.OmA K D) (s 1 * s 0⁻¹)`: the generic
  point lies in the image of the constants, contradicting
  `Work.MotV5.transcendental_genX_ratFunc` (file
  `Submission.Work.MotC5N3.GenAux_relfinrank_bot_adjoin_genX`) combined with
  `IsAlgebraic.algebraMap` and `Algebra.IsAlgebraic.isAlgebraic` for `Work.MotC5N3.KbA K / K`.
  (Equivalently `Work.MotC2.genX_ne_algebraMap` after the bridge `Work.MotC2.coordX_eq_mk`.)

Relevant existing statements: `Work.MotV5.kleinCoord_not_all_one` (same shape of conclusion but
with the extra hypothesis `D.a^2 - D.a*D.b - D.b^2 ≠ 0` — do not use it, it is weaker),
`Work.MotV5.sigmaS_mem_kleinField` (the shift preserves `Work.MotC5N3.kleinField K D`, sorry-free),
`Work.MotV.kleinCoord_eq_sum`, `Work.MotV.kleinBas`, `Work.MotV5.kleinField_eq_adjoin_range`. -/
theorem GenAux_sigmaS_ne_one_on_kleinField (𝕜 : Type) [Field 𝕜] [CharP 𝕜 5] {K : Type} [Field K] [Algebra 𝕜 K] [CharP K 5]
    (D : Work.MotV.KleinData 𝕜) (hD : D.Good)
    (σS : Work.MotC5N3.OmA K D ≃ₐ[Work.MotC5N3.KbA K] Work.MotC5N3.OmA K D)
    (hσS : Work.MotC5N3.KleinData.ShiftOf D σS) :
    ∃ z ∈ Work.MotC5N3.kleinField K D, σS z ≠ z := by
  by_contra hcon
  simp only [not_exists, not_and, not_not] at hcon
  have hκ0 : Work.MotV.kleinCoord D (Work.MotC5N3.KbA K) 0 ≠ 0 := hD.coord0_ne (Work.MotC5N3.KbA K)
  obtain ⟨lam, hlam, hσ⟩ := hσS
  -- The Klein ratios are fixed by the shift (by `hcon`) and acted on by the projective shift.
  have hfix : ∀ i : Fin 5, σS (Work.MotV.kleinCoord D (Work.MotC5N3.KbA K) i
      / Work.MotV.kleinCoord D (Work.MotC5N3.KbA K) 0)
        = Work.MotV.kleinCoord D (Work.MotC5N3.KbA K) i
          / Work.MotV.kleinCoord D (Work.MotC5N3.KbA K) 0 := by
    intro i
    exact hcon _ (IntermediateField.subset_adjoin _ _ (Set.mem_range_self i))
  have hratio : ∀ i : Fin 5,
      σS (Work.MotV.kleinCoord D (Work.MotC5N3.KbA K) i / Work.MotV.kleinCoord D (Work.MotC5N3.KbA K) 0)
      = (Work.MotV.kleinCoord D (Work.MotC5N3.KbA K) (i + 1) / Work.MotV.kleinCoord D (Work.MotC5N3.KbA K) 0)
        / (Work.MotV.kleinCoord D (Work.MotC5N3.KbA K) 1 / Work.MotV.kleinCoord D (Work.MotC5N3.KbA K) 0) := by
    intro i
    rw [map_div₀, hσ i, hσ 0, mul_div_mul_left _ _ hlam]
    exact (div_div_div_cancel_right₀ hκ0 _ _).symm
  -- `r 1 = κ 1 / κ 0` is non-zero: the `i = 0` case gives `r 1 / r 1 = r 0 = 1`.
  have hr1 : Work.MotV.kleinCoord D (Work.MotC5N3.KbA K) 1 / Work.MotV.kleinCoord D (Work.MotC5N3.KbA K) 0
      ≠ 0 := by
    have hone : (Work.MotV.kleinCoord D (Work.MotC5N3.KbA K) 1 / Work.MotV.kleinCoord D (Work.MotC5N3.KbA K) 0)
        / (Work.MotV.kleinCoord D (Work.MotC5N3.KbA K) 1 / Work.MotV.kleinCoord D (Work.MotC5N3.KbA K) 0) = 1 := by
      have h0 := hratio 0
      rw [hfix 0, div_self hκ0] at h0
      exact h0.symm
    intro hz
    rw [hz, div_zero] at hone
    exact one_ne_zero hone.symm
  -- Multiplicativity of the ratios around the cycle.
  have hrel : ∀ i : Fin 5,
      Work.MotV.kleinCoord D (Work.MotC5N3.KbA K) (i+1) / Work.MotV.kleinCoord D (Work.MotC5N3.KbA K) 0
      = (Work.MotV.kleinCoord D (Work.MotC5N3.KbA K) i / Work.MotV.kleinCoord D (Work.MotC5N3.KbA K) 0)
        * (Work.MotV.kleinCoord D (Work.MotC5N3.KbA K) 1 / Work.MotV.kleinCoord D (Work.MotC5N3.KbA K) 0) := by
    intro i
    have h : (Work.MotV.kleinCoord D (Work.MotC5N3.KbA K) (i+1) / Work.MotV.kleinCoord D (Work.MotC5N3.KbA K) 0)
        / (Work.MotV.kleinCoord D (Work.MotC5N3.KbA K) 1 / Work.MotV.kleinCoord D (Work.MotC5N3.KbA K) 0)
        = Work.MotV.kleinCoord D (Work.MotC5N3.KbA K) i / Work.MotV.kleinCoord D (Work.MotC5N3.KbA K) 0 := by
      rw [← hratio i, hfix i]
    exact (div_eq_iff hr1).mp h
  set R : Work.MotC5N3.OmA K D := Work.MotV.kleinCoord D (Work.MotC5N3.KbA K) 1
    / Work.MotV.kleinCoord D (Work.MotC5N3.KbA K) 0 with hRdef
  have hR2 : Work.MotV.kleinCoord D (Work.MotC5N3.KbA K) 2 / Work.MotV.kleinCoord D (Work.MotC5N3.KbA K) 0
      = R * R := hrel 1
  have hR3 : Work.MotV.kleinCoord D (Work.MotC5N3.KbA K) 3 / Work.MotV.kleinCoord D (Work.MotC5N3.KbA K) 0
      = (Work.MotV.kleinCoord D (Work.MotC5N3.KbA K) 2 / Work.MotV.kleinCoord D (Work.MotC5N3.KbA K) 0) * R :=
    hrel 2
  have hR4 : Work.MotV.kleinCoord D (Work.MotC5N3.KbA K) 4 / Work.MotV.kleinCoord D (Work.MotC5N3.KbA K) 0
      = (Work.MotV.kleinCoord D (Work.MotC5N3.KbA K) 3 / Work.MotV.kleinCoord D (Work.MotC5N3.KbA K) 0) * R :=
    hrel 3
  have hR0 : Work.MotV.kleinCoord D (Work.MotC5N3.KbA K) 0 / Work.MotV.kleinCoord D (Work.MotC5N3.KbA K) 0
      = (Work.MotV.kleinCoord D (Work.MotC5N3.KbA K) 4 / Work.MotV.kleinCoord D (Work.MotC5N3.KbA K) 0) * R :=
    hrel 4
  -- `Work.MotC5N3.OmA K D` has characteristic `5`.
  haveI : CharP (Work.MotC5N3.OmA K D) 5 :=
    charP_of_injective_algebraMap (FaithfulSMul.algebraMap_injective (Work.MotC5N3.KbA K) (Work.MotC5N3.OmA K D)) 5
  haveI : Fact (Nat.Prime 5) := ⟨by norm_num⟩
  -- `R ^ 5 = 1`, since `R ^ 5 = r 0 = 1`.
  have hp5 : R ^ 5 = 1 := by
    have hp2 : R ^ 2 = Work.MotV.kleinCoord D (Work.MotC5N3.KbA K) 2
        / Work.MotV.kleinCoord D (Work.MotC5N3.KbA K) 0 := by
      rw [pow_two]; exact hR2.symm
    have hp3 : R ^ 3 = Work.MotV.kleinCoord D (Work.MotC5N3.KbA K) 3
        / Work.MotV.kleinCoord D (Work.MotC5N3.KbA K) 0 := by
      rw [show R ^ 3 = R ^ 2 * R from pow_succ R 2, hp2]; exact hR3.symm
    have hp4 : R ^ 4 = Work.MotV.kleinCoord D (Work.MotC5N3.KbA K) 4
        / Work.MotV.kleinCoord D (Work.MotC5N3.KbA K) 0 := by
      rw [show R ^ 4 = R ^ 3 * R from pow_succ R 3, hp3]; exact hR4.symm
    have hp0 : R ^ 5 = Work.MotV.kleinCoord D (Work.MotC5N3.KbA K) 0
        / Work.MotV.kleinCoord D (Work.MotC5N3.KbA K) 0 := by
      rw [show R ^ 5 = R ^ 4 * R from pow_succ R 4, hp4]; exact hR0.symm
    rw [hp0]; exact div_self hκ0
  -- In characteristic `5`, `R ^ 5 = 1` forces `R = 1`.
  have hR1 : R = 1 := by
    have h5 : (R - 1) ^ 5 = 0 := by
      rw [sub_pow_char, hp5]; simp
    have hz := (pow_eq_zero_iff (n := 5) (by norm_num)).mp h5
    exact sub_eq_zero.mp hz
  have h01 : Work.MotV.kleinCoord D (Work.MotC5N3.KbA K) 0
      / Work.MotV.kleinCoord D (Work.MotC5N3.KbA K) 0 = 1 := div_self hκ0
  have h21 : Work.MotV.kleinCoord D (Work.MotC5N3.KbA K) 2
      / Work.MotV.kleinCoord D (Work.MotC5N3.KbA K) 0 = 1 := by
    rw [hR2, hR1]; ring
  have h31 : Work.MotV.kleinCoord D (Work.MotC5N3.KbA K) 3
      / Work.MotV.kleinCoord D (Work.MotC5N3.KbA K) 0 = 1 := by
    rw [hR3, h21, hR1]; ring
  have h41 : Work.MotV.kleinCoord D (Work.MotC5N3.KbA K) 4
      / Work.MotV.kleinCoord D (Work.MotC5N3.KbA K) 0 = 1 := by
    rw [hR4, h31, hR1]; ring
  have hratios : ∀ i : Fin 5, Work.MotV.kleinCoord D (Work.MotC5N3.KbA K) i
      / Work.MotV.kleinCoord D (Work.MotC5N3.KbA K) 0 = 1 := by
    intro i
    fin_cases i
    · exact h01
    · exact hR1
    · exact h21
    · exact h31
    · exact h41
  -- All Klein coordinates coincide with `κ 0`, contradicting `spans` and transcendence of `genX`.
  have hall : ∀ i : Fin 5, Work.MotV.kleinCoord D (Work.MotC5N3.KbA K) i
      = Work.MotV.kleinCoord D (Work.MotC5N3.KbA K) 0 := by
    intro i
    exact (div_eq_one_iff_eq hκ0).mp (hratios i)
  obtain ⟨e, he⟩ := hD.spans
  have key : ∀ m : Fin 5, Work.MotV.kleinBas D (Work.MotC5N3.KbA K) m
      = (∑ i, algebraMap (Work.MotC5N3.KbA K) (Work.MotC5N3.OmA K D)
          (algebraMap 𝕜 (Work.MotC5N3.KbA K) (e m i))) * Work.MotV.kleinCoord D (Work.MotC5N3.KbA K) 0 := by
    intro m
    rw [he (Work.MotC5N3.KbA K) m, Finset.sum_mul]
    refine Finset.sum_congr rfl (fun i _ => ?_)
    rw [hall i]
  have h0 := key 0
  rw [show Work.MotV.kleinBas D (Work.MotC5N3.KbA K) 0 = 1 from rfl] at h0
  have h1 := key 1
  rw [show Work.MotV.kleinBas D (Work.MotC5N3.KbA K) 1
      = Work.MotV.genX (D.E.baseChange (Work.MotC5N3.KbA K)) from rfl] at h1
  have hκ0inv : Work.MotV.kleinCoord D (Work.MotC5N3.KbA K) 0
      = (∑ i, algebraMap (Work.MotC5N3.KbA K) (Work.MotC5N3.OmA K D)
          (algebraMap 𝕜 (Work.MotC5N3.KbA K) (e 0 i)))⁻¹ :=
    eq_inv_of_mul_eq_one_right h0.symm
  have hX : Work.MotV.genX (D.E.baseChange (Work.MotC5N3.KbA K))
      = algebraMap (Work.MotC5N3.KbA K) (Work.MotC5N3.OmA K D)
          ((∑ i, algebraMap 𝕜 (Work.MotC5N3.KbA K) (e 1 i))
            * (∑ i, algebraMap 𝕜 (Work.MotC5N3.KbA K) (e 0 i))⁻¹) := by
    rw [h1, hκ0inv, ← map_sum (algebraMap (Work.MotC5N3.KbA K) (Work.MotC5N3.OmA K D)),
      ← map_sum (algebraMap (Work.MotC5N3.KbA K) (Work.MotC5N3.OmA K D)), ← map_inv₀, ← map_mul]
  have hbridge : Work.MotV.genX (D.E.baseChange (Work.MotC5N3.KbA K))
      = Work.MotC2.genX (D.E.baseChange (Work.MotC5N3.KbA K)) := by
    rw [Work.MotV.genX, Work.MotC2.genX, Work.MotC2.coordX_eq_mk]
  exact Work.MotC2.genX_ne_algebraMap (D.E.baseChange (Work.MotC5N3.KbA K)) _
    (by rw [← hbridge]; exact hX)

end Work.MotC5N3