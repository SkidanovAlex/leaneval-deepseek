import Mathlib

namespace Work.Tower.CyclotomicBase

/-- Given coprime `A B` and a unit `v` of `ZMod B`, there is a unit `u` of `ZMod (A * B)`
whose image in `ZMod A` is `1` and whose image in `ZMod B` is `v`. This is one half of the
Chinese remainder theorem for the unit groups of `ZMod` (the two projections being jointly
surjective / the natural map being an isomorphism). -/
theorem exists_unitsMap_eq_one_and {A B : ℕ} (h : A.Coprime B) (v : (ZMod B)ˣ) :
    ∃ u : (ZMod (A * B))ˣ, ZMod.unitsMap (Nat.dvd_mul_right A B) u = 1 ∧
      ZMod.unitsMap (Nat.dvd_mul_left B A) u = v := by
  rcases eq_or_ne B 0 with rfl | hB
  · -- Degenerate case `B = 0`: coprimality forces `A = 1`, so both targets are trivial.
    have hA : A = 1 := (Nat.coprime_zero_right A).mp h
    subst hA
    refine ⟨v, ?_, ?_⟩
    · apply Units.ext
      exact @Subsingleton.elim (ZMod 1) (ZMod.subsingleton_iff.mpr rfl) _ _
    · apply Units.ext
      rw [ZMod.unitsMap_val]
      exact Int.cast_id
  · have hBz : NeZero B := ⟨hB⟩
    -- a natural representative of `v` and the Chinese-remainder element `x`
    have hbv : (((v : ZMod B).val : ℕ) : ZMod B) = (v : ZMod B) := ZMod.natCast_zmod_val _
    have hbcop : ((v : ZMod B).val).Coprime B := ZMod.val_coe_unit_coprime v
    obtain ⟨x, hxA, hxB⟩ := Nat.chineseRemainder h 1 (v : ZMod B).val
    have hcopA : x.Coprime A := by
      rw [Nat.coprime_iff_gcd_eq_one, Nat.ModEq.gcd_eq hxA, Nat.gcd_one_left]
    have hcopB : x.Coprime B := by
      rw [Nat.coprime_iff_gcd_eq_one, Nat.ModEq.gcd_eq hxB]
      exact Nat.coprime_iff_gcd_eq_one.mp hbcop
    have hcopAB : x.Coprime (A * B) := hcopA.mul_right hcopB
    refine ⟨ZMod.unitOfCoprime x hcopAB, ?_, ?_⟩
    · apply Units.ext
      rw [ZMod.unitsMap_val, ZMod.coe_unitOfCoprime, Units.val_one,
        ZMod.cast_natCast (Nat.dvd_mul_right A B) x, ← Nat.cast_one, ZMod.natCast_eq_natCast_iff]
      exact hxA
    · apply Units.ext
      rw [ZMod.unitsMap_val, ZMod.coe_unitOfCoprime,
        ZMod.cast_natCast (Nat.dvd_mul_left B A) x, ← hbv, ZMod.natCast_eq_natCast_iff]
      exact hxB

end Work.Tower.CyclotomicBase
