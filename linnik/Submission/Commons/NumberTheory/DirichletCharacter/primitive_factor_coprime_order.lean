import Mathlib
import Submission.Commons.NumberTheory.DirichletCharacter.primitive_factor_coprime

namespace Commons.NumberTheory.DirichletCharacter

/-- The order of the `u`-component of a character of modulus `u * v` divides the order of
the character.  Indeed, the `u`-component is the restriction of `χ` to the image of the
CRT section `crtSu`, on which the `v`-component is trivial. -/
theorem orderOf_factorLeft_dvd {u v : ℕ} [NeZero u] [NeZero v] (huv : u.Coprime v)
    (χ : DirichletCharacter ℂ (u * v)) :
    orderOf (factorLeft huv χ) ∣ orderOf χ := by
  rw [orderOf_dvd_iff_pow_eq_one]
  ext g
  rw [MulChar.pow_apply_coe, MulChar.one_apply_coe]
  have hval : (factorLeft huv χ) (g : ZMod u) =
      χ ((crtSu huv g : (ZMod (u * v))ˣ) : ZMod (u * v)) := by
    rw [factorLeft, MulChar.ofUnitHom_coe, MonoidHom.comp_apply, MulChar.coe_toUnitHom]
  rw [hval, ← MulChar.pow_apply_coe χ (orderOf χ) (crtSu huv g), pow_orderOf_eq_one,
    MulChar.one_apply_coe]

/-- The order of the `v`-component of a character of modulus `u * v` divides the order of
the character. -/
theorem orderOf_factorRight_dvd {u v : ℕ} [NeZero u] [NeZero v] (huv : u.Coprime v)
    (χ : DirichletCharacter ℂ (u * v)) :
    orderOf (factorRight huv χ) ∣ orderOf χ := by
  rw [orderOf_dvd_iff_pow_eq_one]
  ext g
  rw [MulChar.pow_apply_coe, MulChar.one_apply_coe]
  have hval : (factorRight huv χ) (g : ZMod v) =
      χ ((crtSv huv g : (ZMod (u * v))ˣ) : ZMod (u * v)) := by
    rw [factorRight, MulChar.ofUnitHom_coe, MonoidHom.comp_apply, MulChar.coe_toUnitHom]
  rw [hval, ← MulChar.pow_apply_coe χ (orderOf χ) (crtSv huv g), pow_orderOf_eq_one,
    MulChar.one_apply_coe]

theorem primitive_factor_coprime_order {u v : ℕ} [NeZero u] [NeZero v] (huv : u.Coprime v)
    (χ : DirichletCharacter ℂ (u * v)) (hχ : χ.IsPrimitive) :
    ∃ (χu : DirichletCharacter ℂ u) (χv : DirichletCharacter ℂ v),
      χu.IsPrimitive ∧ χv.IsPrimitive ∧
      χ = (χu.changeLevel (Nat.dvd_mul_right u v)) * (χv.changeLevel (Nat.dvd_mul_left v u)) ∧
      orderOf χu ∣ orderOf χ ∧ orderOf χv ∣ orderOf χ := by
  refine ⟨factorLeft huv χ, factorRight huv χ, factorLeft_isPrimitive huv χ hχ,
    factorRight_isPrimitive huv χ hχ, (factor_eq huv χ).symm, ?_, ?_⟩
  · exact orderOf_factorLeft_dvd huv χ
  · exact orderOf_factorRight_dvd huv χ

end Commons.NumberTheory.DirichletCharacter
