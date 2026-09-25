import Mathlib
import Submission.NK.RankTheoryDeep.ProductRank
import Submission.NK.Reconstruct.GammaModule

namespace NK.RankTheoryDeep.PrimeTower

/-!
# `ℤ_ℓ`-linearity of a homomorphism of finite `ℓ`-groups into `ℤ/ℓ^n`

Let `A` be a finite commutative group and `H = ellPart A ℓ` its `ℓ`-primary part.  The latter is a
finite `ℓ`-group killed by `ℓ ^ ellExp A ℓ`, hence canonically a `ℤ_ℓ`-module
(`NK.Reconstruct.instModuleAdditiveEllPart`), and `ZMod (ℓ ^ n)` carries the `ℤ_ℓ`-module
structure induced by the reduction `PadicInt.toZModPow n`.

Every group homomorphism `φ : H →* Multiplicative (ZMod (ℓ ^ n))` is automatically `ℤ_ℓ`-linear for
these two canonical structures: `φ` is `ℤ`-linear for trivial reasons, and the two `ℤ_ℓ`-structures
only involve the reductions of the scalar modulo `ℓ ^ ellExp A ℓ` resp. `ℓ ^ n`; the two
representatives differ by a multiple of `ℓ ^ min (ellExp A ℓ) n`, which annihilates the image of
`φ` because that image is killed both by `ℓ ^ n` (it lies in `ZMod (ℓ ^ n)`) and by
`ℓ ^ ellExp A ℓ` (it is the image of a group of exponent `ℓ ^ ellExp A ℓ`).

This is the `ℓ`-generalisation of `Submission/Work/RankTheoryDeep/exists_linearMap_of_groupHom.lean`.
-/

/-- For `m ≤ n` the reduction of `x : ZMod (ℓ ^ n)` is the class of `x.val` modulo `ℓ ^ m`. -/
private lemma natCast_val_eq_cast {ℓ m n : ℕ} [NeZero ℓ] (h : m ≤ n) (x : ZMod (ℓ ^ n)) :
    ((x.val : ℕ) : ZMod (ℓ ^ m)) = ZMod.cast x := by
  rw [← ZMod.cast_natCast (R := ZMod (ℓ ^ m)) (pow_dvd_pow ℓ h) x.val, ZMod.natCast_zmod_val]

/-- The two representatives `(toZModPow N a).val` and `(toZModPow n a).val` of one `ℓ`-adic scalar
agree modulo `ℓ ^ min N n`. -/
private lemma val_toZModPow_modEq (ℓ : ℕ) [Fact ℓ.Prime] (a : PadicInt ℓ) (N n : ℕ) :
    (PadicInt.toZModPow (p := ℓ) N a).val ≡ (PadicInt.toZModPow (p := ℓ) n a).val
      [MOD ℓ ^ min N n] := by
  haveI : NeZero ℓ := ⟨(Fact.out : ℓ.Prime).ne_zero⟩
  refine (ZMod.natCast_eq_natCast_iff _ _ (ℓ ^ min N n)).mp ?_
  rcases le_total N n with h | h
  · rw [min_eq_left h, ZMod.natCast_zmod_val, natCast_val_eq_cast (ℓ := ℓ) h,
      PadicInt.cast_toZModPow N n h]
  · rw [min_eq_right h, natCast_val_eq_cast (ℓ := ℓ) h, PadicInt.cast_toZModPow n N h,
      ZMod.natCast_zmod_val]

theorem exists_linearMap_of_groupHom {A : Type*} [CommGroup A] [Finite A] (ℓ : ℕ) [Fact ℓ.Prime]
    {n : ℕ} (φ : ↥(NK.Reconstruct.ellPart A ℓ) →* Multiplicative (ZMod (ℓ ^ n))) :
    ∃ Φ : Additive ↥(NK.Reconstruct.ellPart A ℓ) →ₗ[PadicInt ℓ] ZMod (ℓ ^ n),
      ∀ x, Φ (Additive.ofMul x) = (φ x : ZMod (ℓ ^ n)) := by
  classical
  -- the underlying additive map: `x ↦ φ x`
  let Φ₀ : Additive ↥(NK.Reconstruct.ellPart A ℓ) →+ ZMod (ℓ ^ n) :=
    { toFun := fun x => Multiplicative.toAdd (φ (Additive.toMul x))
      map_zero' := by
        show Multiplicative.toAdd (φ (Additive.toMul (0 : Additive ↥(NK.Reconstruct.ellPart A ℓ)))) = 0
        rw [show Additive.toMul (0 : Additive ↥(NK.Reconstruct.ellPart A ℓ)) = 1 from rfl, map_one]
        rfl
      map_add' := by
        intro x y
        show Multiplicative.toAdd (φ (Additive.toMul (x + y)))
          = Multiplicative.toAdd (φ (Additive.toMul x))
            + Multiplicative.toAdd (φ (Additive.toMul y))
        rw [show Additive.toMul (x + y) = Additive.toMul x * Additive.toMul y from rfl, map_mul]
        rfl }
  -- `Φ₀` is `ℤ_ℓ`-linear: the scalar actions are the power maps, and the exponents agree
  -- modulo the exponent of the (image of the) group
  have hlin : ∀ (m : PadicInt ℓ) (x : Additive ↥(NK.Reconstruct.ellPart A ℓ)),
      Φ₀ (m • x) = m • Φ₀ x := by
    intro m x
    obtain ⟨y, rfl⟩ : ∃ y, Additive.ofMul y = x := ⟨Additive.toMul x, ofMul_toMul x⟩
    -- the source scalar action is the power map with exponent `(toZModPow _ a).val`
    have hsm : m • Additive.ofMul y
        = (PadicInt.toZModPow (p := ℓ) (NK.Reconstruct.ellExp A ℓ) m).val
            • Additive.ofMul y := by
      rw [NK.Reconstruct.smul_ellPart_eq_pow, ofMul_pow]
    rw [hsm, map_nsmul]
    have hz : Φ₀ (Additive.ofMul y) = Multiplicative.toAdd (φ y) := rfl
    rw [hz]
    -- the target scalar action is multiplication by the reduction of the scalar
    have hR : m • Multiplicative.toAdd (φ y : Multiplicative (ZMod (ℓ ^ n)))
        = (PadicInt.toZModPow (p := ℓ) n m).val
            • Multiplicative.toAdd (φ y : Multiplicative (ZMod (ℓ ^ n))) := by
      rw [NK.RankTheoryDeep.smul_zmodPow_eq_mul, nsmul_eq_mul, ZMod.natCast_zmod_val]
    rw [hR]
    -- the smallest of the two moduli annihilates the image
    have hkill : ℓ ^ min (NK.Reconstruct.ellExp A ℓ) n
        • Multiplicative.toAdd (φ y : Multiplicative (ZMod (ℓ ^ n))) = 0 := by
      rcases le_total (NK.Reconstruct.ellExp A ℓ) n with h | h
      · rw [min_eq_left h]
        have hp : (φ y) ^ (ℓ ^ NK.Reconstruct.ellExp A ℓ) = 1 := by
          rw [← map_pow, NK.Reconstruct.pow_ellExp_eq_one (A := A) ℓ y, map_one]
        show ℓ ^ NK.Reconstruct.ellExp A ℓ
          • Multiplicative.toAdd (φ y : Multiplicative (ZMod (ℓ ^ n))) = 0
        rw [← toAdd_pow (φ y) (ℓ ^ NK.Reconstruct.ellExp A ℓ), hp]
        rfl
      · rw [min_eq_right h, nsmul_eq_mul, ZMod.natCast_self, zero_mul]
    exact nsmul_eq_nsmul_of_modEq (val_toZModPow_modEq ℓ m (NK.Reconstruct.ellExp A ℓ) n) hkill
  refine ⟨{ toFun := ⇑Φ₀, map_add' := Φ₀.map_add', map_smul' := hlin }, ?_⟩
  intro x
  rfl

end NK.RankTheoryDeep.PrimeTower
