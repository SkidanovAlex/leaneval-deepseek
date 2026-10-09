import Mathlib
-- PORT435-BEGIN (v4.35 isDefEq respectTransparency compat)
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- PORT435-END

namespace NK.CFTLib.ARL

theorem autToPow_eq_of_pow_eq {K L : Type*} [Field K] [Field L] [Algebra K L]
    {n : ℕ} [NeZero n] {ζ : L} (hζ : IsPrimitiveRoot ζ n)
    (σ : Gal(L/K)) (k : ℕ) (h : σ ζ = ζ ^ k) :
    ((hζ.autToPow K σ : (ZMod n)ˣ) : ZMod n) = (k : ZMod n) := by
  set u : (ZMod n)ˣ := hζ.autToPow K σ with hu
  have hspec : ζ ^ (((u : (ZMod n)ˣ) : ZMod n)).val = σ ζ :=
    IsPrimitiveRoot.autToPow_spec K hζ σ
  have hnk : ζ ^ k = ζ ^ (k % n) := by
    conv_lhs => rw [← Nat.mod_add_div k n]
    rw [pow_add, pow_mul, hζ.pow_eq_one, one_pow, mul_one]
  have hmod : (((u : (ZMod n)ˣ) : ZMod n)).val = k % n :=
    hζ.pow_inj (ZMod.val_lt _) (Nat.mod_lt _ (NeZero.pos n)) (by rw [hspec, h, hnk])
  rw [← ZMod.natCast_zmod_val ((u : (ZMod n)ˣ) : ZMod n), hmod,
      ← ZMod.natCast_zmod_val (k : ZMod n), ZMod.val_natCast]

end NK.CFTLib.ARL
