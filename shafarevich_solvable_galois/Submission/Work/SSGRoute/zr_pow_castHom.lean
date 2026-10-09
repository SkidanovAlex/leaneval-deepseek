import Mathlib
import Submission.Work.SSGRoute.zmod_roots_of_unity
-- PORT435-BEGIN (v4.35 isDefEq respectTransparency compat)
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- PORT435-END

/-!
# Compatibility of `zr` with the reduction `ZMod (p^(a+1)) → ZMod (p^a)`

Given a primitive `p^(a+1)`-st root of unity `ζ'` and a primitive `p^a`-th root `ζ` with
`ζ'^p = ζ`, raising `zr hζ' k` (a `p^(a+1)`-st root of unity) to the `p`-th power produces
`zr hζ` applied to the image of `k` under the reduction map
`ZMod (p^(a+1)) → ZMod (p^a)`.
-/

open scoped Classical

namespace Work.SSGRoute

/-- Two integer powers of a primitive `n`-th root of unity agree as soon as the exponents
agree modulo `n`. -/
lemma zpow_eq_of_intCast_eq {G : Type*} [CommGroup G] {n : ℕ} {ζ : G}
    (hζ : IsPrimitiveRoot ζ n) {i j : ℤ} (h : (i : ZMod n) = (j : ZMod n)) :
    ζ ^ i = ζ ^ j := by
  have hdvd : (n : ℤ) ∣ j - i := (Int.modEq_iff_dvd.mp ((ZMod.intCast_eq_intCast_iff i j n).mp h))
  have hone : ζ ^ (j - i) = 1 := (hζ.zpow_eq_one_iff_dvd (j - i)).mpr hdvd
  calc ζ ^ i = ζ ^ i * 1 := (mul_one _).symm
    _ = ζ ^ i * ζ ^ (j - i) := by rw [hone]
    _ = ζ ^ (i + (j - i)) := (zpow_add _ _ _).symm
    _ = ζ ^ j := by ring_nf

/-- Evaluation of `zr` at an arbitrary class, via its canonical representative `x.val`. -/
lemma zr_apply_val {R : Type*} [CommRing R] [IsDomain R] {n : ℕ} [NeZero n] {ζ : Rˣ}
    (hζ : IsPrimitiveRoot ζ n) (x : ZMod n) :
    ((zr hζ (Multiplicative.ofAdd x) : ↥(rootsOfUnity n R)) : Rˣ) = ζ ^ ((x.val : ℤ)) := by
  have hx : x = ((x.val : ℤ) : ZMod n) := by
    rw [Int.cast_natCast]
    exact (ZMod.natCast_zmod_val x).symm
  rw [congrArg Multiplicative.ofAdd hx]
  exact zr_apply_int hζ (x.val : ℤ)

theorem zr_pow_castHom {R : Type*} [CommRing R] [IsDomain R] {p a : ℕ} [NeZero (p ^ (a+1))] [NeZero (p ^ a)]
    {ζ' ζ : Rˣ} (hζ' : IsPrimitiveRoot ζ' (p ^ (a+1))) (hζ : IsPrimitiveRoot ζ (p ^ a))
    (h : ζ' ^ p = ζ) (k : Multiplicative (ZMod (p ^ (a+1)))) :
    (((zr hζ' k : ↥(rootsOfUnity (p ^ (a+1)) R)) : Rˣ) ^ p)
      = ((zr hζ (Multiplicative.ofAdd (ZMod.castHom (pow_dvd_pow p (Nat.le_succ a)) (ZMod (p ^ a)) k.toAdd))
          : ↥(rootsOfUnity (p ^ a) R)) : Rˣ) := by
  have hL : ((zr hζ' k : ↥(rootsOfUnity (p ^ (a+1)) R)) : Rˣ) = ζ' ^ (k.toAdd.val : ℤ) :=
    zr_apply_val hζ' k.toAdd
  have hR : ((zr hζ (Multiplicative.ofAdd (ZMod.castHom (pow_dvd_pow p (Nat.le_succ a)) (ZMod (p ^ a)) k.toAdd))
        : ↥(rootsOfUnity (p ^ a) R)) : Rˣ)
      = ζ ^ ((ZMod.castHom (pow_dvd_pow p (Nat.le_succ a)) (ZMod (p ^ a)) k.toAdd).val : ℤ) :=
    zr_apply_val hζ _
  have hcast : ZMod.castHom (pow_dvd_pow p (Nat.le_succ a)) (ZMod (p ^ a)) k.toAdd
      = ((k.toAdd.val : ℕ) : ZMod (p ^ a)) := by
    conv_lhs => rw [← ZMod.natCast_zmod_val k.toAdd]
    rw [map_natCast]
  have hexp : ((k.toAdd.val : ℤ) : ZMod (p ^ a))
      = (((ZMod.castHom (pow_dvd_pow p (Nat.le_succ a)) (ZMod (p ^ a)) k.toAdd).val : ℤ) : ZMod (p ^ a)) := by
    rw [Int.cast_natCast, Int.cast_natCast, ZMod.natCast_zmod_val, hcast]
  rw [hL, hR]
  have hpow : (ζ' ^ (k.toAdd.val : ℤ)) ^ p = ζ ^ (k.toAdd.val : ℤ) := by
    calc (ζ' ^ (k.toAdd.val : ℤ)) ^ p = ζ' ^ ((k.toAdd.val : ℤ) * p) := (zpow_mul ζ' (k.toAdd.val : ℤ) p).symm
      _ = ζ' ^ (p * (k.toAdd.val : ℤ)) := by rw [mul_comm]
      _ = (ζ' ^ p) ^ (k.toAdd.val : ℤ) := zpow_mul ζ' p (k.toAdd.val : ℤ)
      _ = ζ ^ (k.toAdd.val : ℤ) := by rw [h]
  have h2 : ζ ^ (k.toAdd.val : ℤ)
      = ζ ^ ((ZMod.castHom (pow_dvd_pow p (Nat.le_succ a)) (ZMod (p ^ a)) k.toAdd).val : ℤ) :=
    zpow_eq_of_intCast_eq hζ hexp
  rw [hpow, h2]

end Work.SSGRoute
