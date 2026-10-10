import Mathlib.NumberTheory.Padics.RingHoms
import Submission.Work.HilbertSymbol.Basic
-- PORT435-BEGIN (v4.35 isDefEq respectTransparency compat)
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- PORT435-END

namespace Work.HilbertSymbol

/-!
# Multiplicativity of the `2`-adic Hilbert symbol in the first argument

We prove `(a₁ a₂, b)_2 = (a₁, b)_2 * (a₂, b)_2` for `a₁ a₂ b : ℚˣ`, where `(·,·)_2` is the
explicit `2`-adic Hilbert symbol of `Submission.Work.HilbertSymbol.Basic`.

The symbol is defined through the two `ZMod 2`-valued functions

* `epsZ u = (u - 1)/2 mod 2`, obtained from the residue class of the unit `u` of `ℤ_[2]`
  in `ZMod 4`, and
* `omegaZ u = (u² - 1)/8 mod 2`, obtained from the residue class of `u` in `ZMod 8`,

together with the valuation parities.  The mathematical content of the multiplication formula
is that both `epsZ` and `omegaZ` are group homomorphisms `ℤ_[2]ˣ → ZMod 2`.  Since the residue
rings `ZMod 4` and `ZMod 8` are finite, these multiplicativity statements reduce to a finite
computation on the unit groups `(ZMod 4)ˣ = {1,3}` and `(ZMod 8)ˣ = {1,3,5,7}`.

Everything below is `private`: the corresponding statements about `epsZ`/`omegaZ` are in
the process of being established elsewhere in the repository, and we must not shadow them.
-/

/-! ## The character `epsZ` on units of `ZMod 4` -/

private lemma zmod4_unit_eq : ∀ t : (ZMod 4)ˣ, (t : ZMod 4) = 1 ∨ (t : ZMod 4) = 3 := by
  decide

private lemma zmod4_isUnit_eq (x : ZMod 4) (hx : IsUnit x) : x = 1 ∨ x = 3 := by
  rw [← hx.unit_spec]
  exact zmod4_unit_eq hx.unit

private lemma zmod4_eps_mul (x y : ZMod 4) (hx : IsUnit x) (hy : IsUnit y) :
    (((x * y).val / 2 : ℕ) : ZMod 2) = ((x.val / 2 : ℕ) : ZMod 2) + ((y.val / 2 : ℕ) : ZMod 2) := by
  rcases zmod4_isUnit_eq x hx with h | h <;> rcases zmod4_isUnit_eq y hy with k | k <;>
    rw [h, k] <;> decide

private lemma epsZ_mul_left (u v : ℤ_[2]ˣ) : epsZ (u * v) = epsZ u + epsZ v := by
  simp only [epsZ, Units.val_mul, map_mul]
  exact zmod4_eps_mul _ _ (IsUnit.map _ (Units.isUnit u)) (IsUnit.map _ (Units.isUnit v))

/-! ## The character `omegaZ` on units of `ZMod 8` -/

/-- `ω` read off from the residue class in `ZMod 8`: `0` for `1, 7` and `1` for `3, 5`. -/
private def zmod8_omega (x : ZMod 8) : ZMod 2 := if x.val = 1 ∨ x.val = 7 then 0 else 1

private lemma zmod8_unit_eq :
    ∀ t : (ZMod 8)ˣ,
      (t : ZMod 8) = 1 ∨ (t : ZMod 8) = 3 ∨ (t : ZMod 8) = 5 ∨ (t : ZMod 8) = 7 := by
  decide

private lemma zmod8_isUnit_eq (x : ZMod 8) (hx : IsUnit x) :
    x = 1 ∨ x = 3 ∨ x = 5 ∨ x = 7 := by
  rw [← hx.unit_spec]
  exact zmod8_unit_eq hx.unit

private lemma zmod8_omega_mul (x y : ZMod 8) (hx : IsUnit x) (hy : IsUnit y) :
    zmod8_omega (x * y) = zmod8_omega x + zmod8_omega y := by
  rcases zmod8_isUnit_eq x hx with h | h | h | h <;>
    rcases zmod8_isUnit_eq y hy with k | k | k | k <;>
    rw [h, k] <;> decide

private lemma omegaZ_mul_left (u v : ℤ_[2]ˣ) : omegaZ (u * v) = omegaZ u + omegaZ v := by
  simp only [omegaZ, Units.val_mul, map_mul]
  exact zmod8_omega_mul _ _ (IsUnit.map _ (Units.isUnit u)) (IsUnit.map _ (Units.isUnit v))

/-! ## The multiplication formula -/

theorem hilbertSymbolTwo_mul_left (a₁ a₂ b : ℚˣ) :
    hilbertSymbolTwo (a₁ * a₂) b = hilbertSymbolTwo a₁ b * hilbertSymbolTwo a₂ b := by
  simp only [hilbertSymbolTwo]
  rw [unitPart_mul, padicVal_mul, epsZ_mul_left, omegaZ_mul_left, ← signOf_add]
  congr 1
  push_cast
  ring

end Work.HilbertSymbol
