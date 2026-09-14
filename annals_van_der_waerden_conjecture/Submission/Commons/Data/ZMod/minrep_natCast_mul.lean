import Mathlib.Data.ZMod.Basic

namespace Commons.Data.ZMod

theorem minrep_natCast_mul (M q y : ℕ) (hM : 0 < M) (hq : 0 < q) :
    min (ZMod.val (((q * y : ℕ)) : ZMod (q * M)))
        (q * M - ZMod.val (((q * y : ℕ)) : ZMod (q * M)))
      = q * min (ZMod.val ((y : ℕ) : ZMod M)) (M - ZMod.val ((y : ℕ) : ZMod M)) := by
  rw [ZMod.val_natCast (q * M) (q * y), ZMod.val_natCast M y]
  rw [Nat.mul_mod_mul_left q y M]
  rw [← Nat.mul_sub_left_distrib q M (y % M)]
  rw [Nat.mul_min_mul_left]

end Commons.Data.ZMod