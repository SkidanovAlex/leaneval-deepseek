import Mathlib.NumberTheory.Padics.Hensel
import Mathlib.NumberTheory.Padics.RingHoms
import Submission.Work.QuadraticLocalGlobal.Defs
-- PORT435-BEGIN (v4.35 isDefEq respectTransparency compat)
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- PORT435-END

/-!
# Squares in `ℚ_[2]`

Over `ℚ_[2]` the square classes are described as follows: `x ≠ 0` is a square if and only if
its valuation is even and its unit part `padicUnitOf 2 x hx : ℤ_[2]ˣ` is congruent to `1`
modulo `8`, i.e. its image under `PadicInt.toZModPow 3 : ℤ_[2] →+* ZMod 8` is `1`.

The proof splits into two statements:

* `isSquare_padic_two_iff_even_and_unit`: `x` is a square iff `v_2(x)` is even and the unit part
  of `x` is a square in `ℤ_[2]`.  Writing `x = 2 ^ v * u`, this is the usual decomposition of the
  square class of `x` into the square class of `2 ^ v` (a square iff `v` is even) and the square
  class of the unit `u`;
* `isSquare_padicInt_two_unit_iff`: a unit `v` of `ℤ_[2]` is a square iff `v ≡ 1 (mod 8)`.
  The forward implication only uses that the square of a unit of `ZMod 8` is `1`; the converse is
  Hensel's lemma applied to `X ^ 2 - v` at `X = 1`, the hypothesis `‖1 - v‖ < ‖2‖ ^ 2` being
  exactly the congruence `v ≡ 1 (mod 8)`.
-/

namespace Work.QuadraticLocalGlobal

/-- In `ZMod 8`, the image of any unit has square `1`. -/
theorem zmod_eight_sq_of_mul_eq_one {a b : ZMod 8} (h : a * b = 1) : a ^ 2 = 1 := by
  have key : ∀ a b : ZMod 8, a * b = 1 → a ^ 2 = 1 := by decide
  exact key a b h

/-- A unit `v` of `ℤ_[2]` is a square if and only if `v ≡ 1 (mod 8)`. -/
theorem isSquare_padicInt_two_unit_iff (v : ℤ_[2]ˣ) :
    IsSquare (v : ℤ_[2]) ↔ PadicInt.toZModPow 3 (v : ℤ_[2]) = 1 := by
  constructor
  · -- If `v = w ^ 2` then `w` is a unit modulo `8`, whence `w ^ 2 = 1`.
    intro h
    obtain ⟨w, hw⟩ := h
    have hu : (v : ℤ_[2]) * (↑(v⁻¹) : ℤ_[2]) = 1 := by simp
    have hwv : w * (w * (↑(v⁻¹) : ℤ_[2])) = 1 := by rw [← mul_assoc, ← hw, hu]
    have hkey : (PadicInt.toZModPow 3) w * (PadicInt.toZModPow 3) (w * (↑(v⁻¹) : ℤ_[2])) = 1 := by
      rw [← map_mul, hwv, map_one]
    have hsq : ((PadicInt.toZModPow 3) w) ^ 2 = 1 := zmod_eight_sq_of_mul_eq_one hkey
    rw [hw, map_mul, ← sq]
    exact hsq
  · -- Conversely `toZModPow 3 v = 1` says `8 ∣ v - 1`, so `‖1 - v‖ ≤ 1 / 8 < ‖2‖ ^ 2` and
    -- Hensel's lemma on `X ^ 2 - v` produces a square root of `v`.
    intro h
    have h2 : (2 : ℤ_[2]) = 1 + 1 := by norm_num
    have hle : ‖(1 : ℤ_[2]) - (v : ℤ_[2])‖ ≤ 1 / 8 := by
      have hmem : (v : ℤ_[2]) - 1 ∈
          RingHom.ker (PadicInt.toZModPow (p := 2) 3 : ℤ_[2] →+* ZMod (2 ^ 3)) := by
        rw [RingHom.mem_ker, map_sub, h, map_one, sub_self]
      rw [PadicInt.ker_toZModPow] at hmem
      rw [Ideal.mem_span_singleton] at hmem
      obtain ⟨c, hc⟩ := hmem
      have h1 : ‖(1 : ℤ_[2]) - (v : ℤ_[2])‖ = ‖(v : ℤ_[2]) - 1‖ := by
        rw [← norm_neg]; ring_nf
      rw [h1, hc, norm_mul, PadicInt.norm_p_pow]
      have hp : (0 : ℝ) < (2 : ℝ) ^ (-3 : ℤ) := by positivity
      nlinarith [norm_nonneg c, PadicInt.norm_le_one c]
    have hlt : ‖(1 : ℤ_[2]) - (v : ℤ_[2])‖ < ‖((2 : ℤ_[2]))‖ ^ 2 := by
      have hsq : ‖((2 : ℤ_[2]))‖ ^ 2 = (1 / 4 : ℝ) := by
        rw [show (2 : ℤ_[2]) = ((2 : ℕ) : ℤ_[2]) by norm_num, PadicInt.norm_p]
        norm_num
      linarith
    have h' : ‖(1 : ℤ_[2]) - (v : ℤ_[2])‖ < ‖(1 : ℤ_[2]) + 1‖ ^ 2 := by rw [← h2]; exact hlt
    have key := hensels_lemma (p := 2) (R := ℤ_[2])
      (F := Polynomial.X ^ 2 - Polynomial.C (v : ℤ_[2])) (a := 1) (by simpa using h')
    obtain ⟨z, hz, _⟩ := key
    have hz0 : z ^ 2 - (v : ℤ_[2]) = 0 := by simpa using hz
    have hz' : z ^ 2 = (v : ℤ_[2]) := sub_eq_zero.mp hz0
    exact ⟨z, by rw [← hz', sq]⟩

/-- `x ≠ 0` in `ℚ_[2]` is a square if and only if its valuation is even and its unit part is a
square in `ℤ_[2]`. -/
theorem isSquare_padic_two_iff_even_and_unit {x : ℚ_[2]} (hx : x ≠ 0) :
    IsSquare x ↔ Even (x.valuation) ∧ IsSquare (padicUnitOf 2 x hx : ℤ_[2]) := by
  constructor
  · intro h
    obtain ⟨y, hy⟩ := h
    have hy0 : y ≠ 0 := by
      rintro rfl
      exact hx (by rw [hy]; ring)
    have hvy : x.valuation = 2 * y.valuation := by
      rw [hy, ← sq, Padic.valuation_pow]
      norm_num
    refine ⟨?_, ?_⟩
    · rw [hvy]; exact ⟨y.valuation, by ring⟩
    · refine ⟨(padicUnitOf 2 y hy0 : ℤ_[2]), ?_⟩
      apply Subtype.ext
      push_cast
      rw [padicUnitOf_coe, padicUnitOf_coe, hvy, hy]
      simp only [Nat.cast_ofNat]
      rw [show -(2 * y.valuation) = -y.valuation + -y.valuation by ring]
      rw [zpow_add₀ (show (2 : ℚ_[2]) ≠ 0 by norm_num)]
      ring
  · rintro ⟨hv, w, hw⟩
    obtain ⟨m, hm⟩ := hv
    refine ⟨(2 : ℚ_[2]) ^ m * (w : ℚ_[2]), ?_⟩
    have hwu : ((padicUnitOf 2 x hx : ℤ_[2]) : ℚ_[2]) = (w : ℚ_[2]) * (w : ℚ_[2]) := by
      rw [hw]; push_cast; ring
    have hxu : x = (2 : ℚ_[2]) ^ (x.valuation) * ((padicUnitOf 2 x hx : ℤ_[2]) : ℚ_[2]) := by
      rw [padicUnitOf_coe]
      simp only [Nat.cast_ofNat]
      rw [← mul_assoc, ← zpow_add₀ (show (2 : ℚ_[2]) ≠ 0 by norm_num), add_neg_cancel,
        zpow_zero, one_mul]
    rw [hxu, hwu, hm]
    rw [zpow_add₀ (show (2 : ℚ_[2]) ≠ 0 by norm_num)]
    ring

theorem isSquare_padic_two_iff {x : ℚ_[2]} (hx : x ≠ 0) : IsSquare x ↔ Even (x.valuation) ∧ PadicInt.toZModPow 3 (Work.QuadraticLocalGlobal.padicUnitOf 2 x hx : ℤ_[2]) = 1 := by
  exact (isSquare_padic_two_iff_even_and_unit hx).trans
    (and_congr_right fun _ => isSquare_padicInt_two_unit_iff _)

end Work.QuadraticLocalGlobal
