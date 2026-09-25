import Mathlib
import Submission.NK.RankTheoryDeep.ProductRank
import Submission.NK.Reconstruct.GammaModule

namespace NK.RankTheoryDeep

/-!
# `ℤ_2`-linearity of a homomorphism of finite `2`-groups into `ℤ/2^n`

Let `A` be a finite commutative group and `H = ellPart A 2` its `2`-primary part.  The latter is a
finite `2`-group killed by `2 ^ ellExp A 2`, hence canonically a `ℤ_2`-module
(`NK.Reconstruct.instModuleAdditiveEllPart`), and `ZMod (2 ^ n)` carries the `ℤ_2`-module
structure induced by the reduction `PadicInt.toZModPow n`.

The point of this file is that **every** group homomorphism

  `φ : H →* Multiplicative (ZMod (2 ^ n))`

is automatically `ℤ_2`-linear for these two canonical structures.  Indeed `φ` is `ℤ`-linear for
trivial reasons, and the two `ℤ_2`-structures only involve the reductions of the scalar modulo
`2 ^ ellExp A 2` resp. `2 ^ n`; the two representatives differ by a multiple of
`2 ^ min (ellExp A 2) n`, which annihilates the image of `φ` because that image is killed both by
`2 ^ n` (it lies in `ZMod (2 ^ n)`) and by `2 ^ ellExp A 2` (it is the image of a group of exponent
`2 ^ ellExp A 2`).

This is the algebraic heart of the reconstruction: it says that the `ℤ_2`-module structure on the
`2`-part of an abelianisation is *definitional*, not extra structure, so that group-theoretic
constructions on the `2`-parts are automatically `ℤ_2`-linear.
-/

/-- For `m ≤ n` the reduction of `x : ZMod (2 ^ n)` is the class of `x.val` modulo `2 ^ m`. -/
private lemma natCast_val_eq_cast {m n : ℕ} (h : m ≤ n) (x : ZMod (2 ^ n)) :
    ((x.val : ℕ) : ZMod (2 ^ m)) = ZMod.cast x := by
  rw [← ZMod.cast_natCast (R := ZMod (2 ^ m)) (pow_dvd_pow 2 h) x.val, ZMod.natCast_zmod_val]

/-- The two representatives `(toZModPow N a).val` and `(toZModPow n a).val` of one `2`-adic scalar
agree modulo `2 ^ min N n`: they are the integers of the reductions of `a` modulo `2 ^ N` and
`2 ^ n`, and those two reductions are compatible. -/
private lemma val_toZModPow_modEq (a : PadicInt 2) (N n : ℕ) :
    (PadicInt.toZModPow (p := 2) N a).val ≡ (PadicInt.toZModPow (p := 2) n a).val
      [MOD 2 ^ min N n] := by
  refine (ZMod.natCast_eq_natCast_iff _ _ (2 ^ min N n)).mp ?_
  rcases le_total N n with h | h
  · rw [min_eq_left h, ZMod.natCast_zmod_val, natCast_val_eq_cast h,
      PadicInt.cast_toZModPow N n h]
  · rw [min_eq_right h, natCast_val_eq_cast h, PadicInt.cast_toZModPow n N h,
      ZMod.natCast_zmod_val]

theorem exists_linearMap_of_groupHom {A : Type*} [CommGroup A] [Finite A] {n : ℕ}
    (φ : ↥(NK.Reconstruct.ellPart A 2) →* Multiplicative (ZMod (2 ^ n))) :
    ∃ Φ : Additive ↥(NK.Reconstruct.ellPart A 2) →ₗ[PadicInt 2] ZMod (2 ^ n),
      ∀ x, Φ (Additive.ofMul x) = (φ x : ZMod (2 ^ n)) := by
  classical
  -- the underlying additive map: `x ↦ φ x`
  let Φ₀ : Additive ↥(NK.Reconstruct.ellPart A 2) →+ ZMod (2 ^ n) :=
    { toFun := fun x => Multiplicative.toAdd (φ (Additive.toMul x))
      map_zero' := by
        show Multiplicative.toAdd (φ (Additive.toMul (0 : Additive ↥(NK.Reconstruct.ellPart A 2)))) = 0
        rw [show Additive.toMul (0 : Additive ↥(NK.Reconstruct.ellPart A 2)) = 1 from rfl, map_one]
        rfl
      map_add' := by
        intro x y
        show Multiplicative.toAdd (φ (Additive.toMul (x + y)))
          = Multiplicative.toAdd (φ (Additive.toMul x))
            + Multiplicative.toAdd (φ (Additive.toMul y))
        rw [show Additive.toMul (x + y) = Additive.toMul x * Additive.toMul y from rfl, map_mul]
        rfl }
  -- `Φ₀` is `ℤ_2`-linear: the scalar actions are the power maps, and the exponents agree
  -- modulo the exponent of the (image of the) group
  have hlin : ∀ (m : PadicInt 2) (x : Additive ↥(NK.Reconstruct.ellPart A 2)),
      Φ₀ (m • x) = m • Φ₀ x := by
    intro m x
    obtain ⟨y, rfl⟩ : ∃ y, Additive.ofMul y = x := ⟨Additive.toMul x, ofMul_toMul x⟩
    -- the source scalar action is the power map with exponent `(toZModPow _ a).val`
    have hsm : m • Additive.ofMul y
        = (PadicInt.toZModPow (p := 2) (NK.Reconstruct.ellExp A 2) m).val
            • Additive.ofMul y := by
      rw [NK.Reconstruct.smul_ellPart_eq_pow, ofMul_pow]
    rw [hsm, map_nsmul]
    have hz : Φ₀ (Additive.ofMul y) = Multiplicative.toAdd (φ y) := rfl
    rw [hz]
    -- the target scalar action is multiplication by the reduction of the scalar
    have hR : m • Multiplicative.toAdd (φ y : Multiplicative (ZMod (2 ^ n)))
        = (PadicInt.toZModPow (p := 2) n m).val
            • Multiplicative.toAdd (φ y : Multiplicative (ZMod (2 ^ n))) := by
      rw [NK.RankTheoryDeep.smul_zmodPow_eq_mul, nsmul_eq_mul, ZMod.natCast_zmod_val]
    rw [hR]
    -- the smallest of the two moduli annihilates the image
    have hkill : 2 ^ min (NK.Reconstruct.ellExp A 2) n
        • Multiplicative.toAdd (φ y : Multiplicative (ZMod (2 ^ n))) = 0 := by
      rcases le_total (NK.Reconstruct.ellExp A 2) n with h | h
      · rw [min_eq_left h]
        have hp : (φ y) ^ (2 ^ NK.Reconstruct.ellExp A 2) = 1 := by
          rw [← map_pow, NK.Reconstruct.pow_ellExp_eq_one (A := A) 2 y, map_one]
        show 2 ^ NK.Reconstruct.ellExp A 2
          • Multiplicative.toAdd (φ y : Multiplicative (ZMod (2 ^ n))) = 0
        rw [← toAdd_pow (φ y) (2 ^ NK.Reconstruct.ellExp A 2), hp]
        rfl
      · rw [min_eq_right h, nsmul_eq_mul, ZMod.natCast_self, zero_mul]
    exact nsmul_eq_nsmul_of_modEq (val_toZModPow_modEq m (NK.Reconstruct.ellExp A 2) n) hkill
  refine ⟨{ toFun := ⇑Φ₀, map_add' := Φ₀.map_add', map_smul' := hlin }, ?_⟩
  intro x
  rfl

end NK.RankTheoryDeep
