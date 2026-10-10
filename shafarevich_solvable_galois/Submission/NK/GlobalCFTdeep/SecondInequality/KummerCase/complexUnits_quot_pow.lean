import Mathlib.Analysis.Complex.Polynomial.Basic
-- PORT435-BEGIN (v4.35 isDefEq respectTransparency compat)
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- PORT435-END

namespace NK.GlobalCFTdeep.SecondInequality.KummerCase

/-- Over an algebraically closed field every element is an `n`-th power; consequently every
unit of `ℂ` is an `n`-th power of a unit, so the quotient of `ℂˣ` by the `n`-th powers is
trivial. -/
theorem complexUnits_quot_pow (n : ℕ) (hn : 0 < n) :
    Nat.card (ℂˣ ⧸ (powMonoidHom n : ℂˣ →* ℂˣ).range) = 1 := by
  -- The `n`-th power map on `ℂˣ` is surjective.
  have hsurj : Function.Surjective (powMonoidHom n : ℂˣ →* ℂˣ) := by
    intro u
    -- `ℂ` is algebraically closed, so `(u : ℂ)` has an `n`-th root `z`.
    obtain ⟨z, hz⟩ := IsAlgClosed.exists_pow_nat_eq (k := ℂ) (u : ℂ) hn
    -- `u ≠ 0` forces `z ≠ 0`.
    have hz0 : z ≠ 0 := by
      rintro rfl
      have : (u : ℂ) = 0 := by rw [← hz]; exact zero_pow hn.ne'
      exact Units.ne_zero u this
    refine ⟨Units.mk0 z hz0, ?_⟩
    rw [powMonoidHom_apply]
    ext
    rw [Units.val_pow_eq_pow_val, Units.val_mk0, hz]
  -- Hence the range is everything and the quotient is `ℂˣ ⧸ ⊤`.
  have hrange : (powMonoidHom n : ℂˣ →* ℂˣ).range = ⊤ := MonoidHom.range_eq_top.mpr hsurj
  rw [hrange, Nat.card_eq_one_iff_unique]
  exact ⟨QuotientGroup.subsingleton_quotient_top, ⟨1⟩⟩

end NK.GlobalCFTdeep.SecondInequality.KummerCase
