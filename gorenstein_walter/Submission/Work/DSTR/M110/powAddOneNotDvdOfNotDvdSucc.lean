import Mathlib

namespace Work.DSTR.M110

theorem powAddOneNotDvdOfNotDvdSucc (A q : ℕ) (hq : q.Prime) (h : ¬ q ∣ A + 1) : ¬ q ∣ A ^ q + 1 := by
  -- Fermat's little theorem: `A ^ q ≡ A [MOD q]`, via `ZMod.pow_card`.
  have hfermat : A ^ q ≡ A [MOD q] := by
    rw [← ZMod.natCast_eq_natCast_iff]
    rw [Nat.cast_pow]
    exact @ZMod.pow_card q ⟨hq⟩ (A : ZMod q)
  intro hdiv
  have hzero : A ^ q + 1 ≡ 0 [MOD q] := (Nat.modEq_zero_iff_dvd).2 hdiv
  have hadd : A ^ q + 1 ≡ A + 1 [MOD q] := hfermat.add (Nat.ModEq.refl 1)
  exact h ((Nat.modEq_zero_iff_dvd).1 (hadd.symm.trans hzero))

end Work.DSTR.M110
