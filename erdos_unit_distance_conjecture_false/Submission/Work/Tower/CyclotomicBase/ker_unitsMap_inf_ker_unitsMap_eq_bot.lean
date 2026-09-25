import Mathlib

namespace Work.Tower.CyclotomicBase

/-- If `A` and `B` are coprime, a unit of `ZMod (A * B)` reducing to `1` both modulo `A`
and modulo `B` is `1`: the two reduction kernels intersect trivially.  This is the kernel
form of the Chinese remainder theorem `ZMod.chineseRemainder`. -/
theorem ker_unitsMap_inf_ker_unitsMap_eq_bot {A B : ℕ} (h : A.Coprime B) :
    (ZMod.unitsMap (Nat.dvd_mul_right A B)).ker ⊓ (ZMod.unitsMap (Nat.dvd_mul_left B A)).ker = ⊥ := by
  rw [Subgroup.eq_bot_iff_forall]
  intro u hu
  rw [Subgroup.mem_inf, MonoidHom.mem_ker, MonoidHom.mem_ker] at hu
  obtain ⟨huA, huB⟩ := hu
  -- The value of `u` casts to `1` both in `ZMod A` and in `ZMod B`.
  have hA1 : (ZMod.castHom (Nat.dvd_mul_right A B) (ZMod A)) (u : ZMod (A * B)) = 1 := by
    have h2 := congrArg Units.val huA
    rwa [ZMod.unitsMap_val, ← ZMod.castHom_apply] at h2
  have hB1 : (ZMod.castHom (Nat.dvd_mul_left B A) (ZMod B)) (u : ZMod (A * B)) = 1 := by
    have h2 := congrArg Units.val huB
    rwa [ZMod.unitsMap_val, ← ZMod.castHom_apply] at h2
  -- The Chinese remainder map is componentwise `castHom`, so it sends `u` to `(1, 1)`.
  have hCR : (ZMod.chineseRemainder h).toRingHom =
      RingHom.prod (ZMod.castHom (Nat.dvd_mul_right A B) (ZMod A))
        (ZMod.castHom (Nat.dvd_mul_left B A) (ZMod B)) := RingHom.ext_zmod _ _
  have hval : (ZMod.chineseRemainder h) (u : ZMod (A * B)) = 1 := by
    show (ZMod.chineseRemainder h).toRingHom (u : ZMod (A * B)) = 1
    rw [hCR, RingHom.prod_apply, hA1, hB1]
    rfl
  have huval : (u : ZMod (A * B)) = 1 :=
    (ZMod.chineseRemainder h).injective (hval.trans (map_one _).symm)
  exact Units.ext huval

end Work.Tower.CyclotomicBase
