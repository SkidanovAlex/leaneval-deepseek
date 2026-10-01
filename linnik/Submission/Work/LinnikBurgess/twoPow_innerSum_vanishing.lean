import Mathlib
import Submission.Work.LinnikBurgess.burgess_lead_defs

/-! # 2-adic vanishing of the cubic correlation summand off the unit locus

At `x = y + 2^m w` (`m ≥ 1`) the factor `x + c` of the cubic correlation is congruent to
`y + c` modulo `2`, so if some `y + a_l` or `y + b_l` is even then one factor of the product
`∏_l (x + a_l)` (or `∏_l (x + b_l)`) is a multiple of `2` in `ZMod (2^e)`, hence a non-unit,
hence has Dirichlet character value `0`. -/

namespace Work.LinnikBurgess

/-- `2` is not a unit of `ZMod (2^e)` as soon as `e ≥ 1`. -/
lemma not_isUnit_two_zmod (e : ℕ) (he : 1 ≤ e) : ¬ IsUnit ((2 : ℕ) : ZMod (2 ^ e)) := by
  rw [ZMod.isUnit_iff_coprime]
  exact Nat.not_coprime_of_dvd_of_dvd (by norm_num) (by omega) (dvd_pow_self 2 (by omega))

/-- A product over `Fin 3` one of whose factors equals `2 * t` is a non-unit of `ZMod (2^e)`. -/
lemma not_isUnit_prod_fin3_of_factor_two {e : ℕ} (he : 1 ≤ e) (f : Fin 3 → ZMod (2 ^ e))
    (l : Fin 3) (t : ZMod (2 ^ e)) (h : f l = ((2 : ℕ) : ZMod (2 ^ e)) * t) :
    ¬ IsUnit (∏ i : Fin 3, f i) := by
  intro hu
  rw [Finset.prod_eq_prod_sdiff_singleton_mul (Finset.mem_univ l), h] at hu
  exact not_isUnit_two_zmod e he (IsUnit.mul_iff.mp (IsUnit.mul_iff.mp hu).2).1

/-- If `2 ∣ y + c` then the factor `x + c` of the cubic correlation at `x = y + 2^m w`
(`m ≥ 1`) is `2` times an explicit element of `ZMod (2^e)`. -/
lemma twoPow_factor_eq_two_mul {e m : ℕ} (hm : 1 ≤ m) (y c wv : ℕ) (hc : 2 ∣ y + c) :
    ∃ t : ℕ, ((y : ℕ) : ZMod (2 ^ e)) + ((2 ^ m : ℕ) : ZMod (2 ^ e)) * ((wv : ℕ) : ZMod (2 ^ e))
        + ((c : ℕ) : ZMod (2 ^ e))
      = ((2 : ℕ) : ZMod (2 ^ e)) * ((t : ℕ) : ZMod (2 ^ e)) := by
  obtain ⟨z, hz⟩ := hc
  refine ⟨z + 2 ^ (m - 1) * wv, ?_⟩
  have hnat : y + 2 ^ m * wv + c = 2 * (z + 2 ^ (m - 1) * wv) := by
    have h2m : 2 ^ m = 2 * 2 ^ (m - 1) := by
      conv_lhs => rw [show m = (m - 1) + 1 by omega]
      rw [pow_succ]; ring
    have key : y + (2 * 2 ^ (m - 1)) * wv + c = (y + c) + 2 * (2 ^ (m - 1) * wv) := by ring
    rw [h2m, key, hz]; ring
  have hcast : ((y + 2 ^ m * wv + c : ℕ) : ZMod (2 ^ e))
      = ((2 : ℕ) : ZMod (2 ^ e)) * ((z + 2 ^ (m - 1) * wv : ℕ) : ZMod (2 ^ e)) := by
    rw [hnat, Nat.cast_mul]
  rw [← hcast]; push_cast; ring

/-- **Vanishing off the unit locus.**  If some `y + a_l` or `y + b_l` is even (`¬ UnitAt 2 y a b`)
then the summand of the cubic correlation at `x = y + 2^m w` vanishes, because the corresponding
product `∏_l (x + a_l)` is even, hence a non-unit of `ZMod (2^e)`, hence `χ` of it is `0`. -/
theorem twoPow_innerSum_vanishing {e m : ℕ} (hm : 1 ≤ m) (h2 : 2 * m ≤ e)
    (χ : DirichletCharacter ℂ (2 ^ e)) (a b : Fin 3 → ℕ) (y : ℕ) (hy : ¬ UnitAt 2 y a b)
    (w : ZMod (2 ^ (e - m))) :
    χ (∏ l : Fin 3, (((y : ℕ) : ZMod (2 ^ e)) + ((2 ^ m : ℕ) : ZMod (2 ^ e)) * ((w.val : ℕ) : ZMod (2 ^ e)) + (a l : ℕ)))
      * (starRingEnd ℂ) (χ (∏ l : Fin 3, (((y : ℕ) : ZMod (2 ^ e)) + ((2 ^ m : ℕ) : ZMod (2 ^ e)) * ((w.val : ℕ) : ZMod (2 ^ e)) + (b l : ℕ)))) = 0 := by
  have he : 1 ≤ e := by omega
  simp only [UnitAt, not_forall, not_and_or, not_not] at hy
  obtain ⟨l, hl⟩ := hy
  rcases hl with hl | hl
  · obtain ⟨t, ht⟩ := twoPow_factor_eq_two_mul hm y (a l) w.val hl
    have hnu : ¬ IsUnit (∏ i : Fin 3, (((y : ℕ) : ZMod (2 ^ e))
        + ((2 ^ m : ℕ) : ZMod (2 ^ e)) * ((w.val : ℕ) : ZMod (2 ^ e)) + ((a i : ℕ) : ZMod (2 ^ e)))) :=
      not_isUnit_prod_fin3_of_factor_two he _ l t ht
    have hchi := MulChar.map_nonunit χ hnu
    rw [hchi, zero_mul]
  · obtain ⟨t, ht⟩ := twoPow_factor_eq_two_mul hm y (b l) w.val hl
    have hnu : ¬ IsUnit (∏ i : Fin 3, (((y : ℕ) : ZMod (2 ^ e))
        + ((2 ^ m : ℕ) : ZMod (2 ^ e)) * ((w.val : ℕ) : ZMod (2 ^ e)) + ((b i : ℕ) : ZMod (2 ^ e)))) :=
      not_isUnit_prod_fin3_of_factor_two he _ l t ht
    have hchi := MulChar.map_nonunit χ hnu
    rw [hchi, map_zero, mul_zero]

end Work.LinnikBurgess
