import Mathlib

-- Lean v4.35.0-rc3: restore v4.34 instance-unification transparency (port).
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false

/-!
# The character `ZMod n →* ℂˣ` given by `k ↦ exp(2πi k/n)`

The free action of `ZMod n` on `ℂ^K` (hence on the unit sphere) that produces the lens space is by
scalar multiplication with the `n`-th roots of unity; this file provides the group homomorphism
`φ : Multiplicative (ZMod n) →* ℂˣ` realising it, together with the two properties used later:
`φ` is injective (so the action is free off the origin) and `‖φ g‖ = 1` (so the action preserves
the sphere).
-/

namespace Work.RatHurewicz

noncomputable section

/-- `ζ = exp(2πi/n)`, a primitive `n`-th root of unity, viewed as a unit of `ℂ`. -/
def zeta (n : ℕ) : ℂˣ :=
  Units.mk0 (Complex.exp (2 * (Real.pi : ℂ) * Complex.I / (n : ℂ))) (Complex.exp_ne_zero _)

@[simp] theorem zeta_coe (n : ℕ) :
    (zeta n : ℂ) = Complex.exp (2 * (Real.pi : ℂ) * Complex.I / (n : ℂ)) := rfl

/-- `ζ` is a primitive `n`-th root of unity. -/
theorem zeta_isPrimitiveRoot {n : ℕ} (hn : n ≠ 0) : IsPrimitiveRoot (zeta n : ℂ) n :=
  Complex.isPrimitiveRoot_exp n hn

/-- `ζⁿ = 1`. -/
theorem zeta_pow_eq_one {n : ℕ} (hn : n ≠ 0) : (zeta n) ^ n = 1 :=
  Units.ext (by simpa using (zeta_isPrimitiveRoot hn).pow_eq_one)

/-- `ζ` has norm one. -/
theorem zeta_norm (n : ℕ) : ‖(zeta n : ℂ)‖ = 1 := by
  rw [zeta_coe, Complex.norm_exp]
  have hre : (2 * (Real.pi : ℂ) * Complex.I / (n : ℂ)).re = 0 := by
    simp [Complex.div_re, Complex.mul_re]
  rw [hre, Real.exp_zero]

/-- The additive homomorphism `ℤ → Additive ℂˣ`, `k ↦ ζᵏ`. -/
def zetaPowAdd (n : ℕ) : ℤ →+ Additive ℂˣ where
  toFun k := Additive.ofMul (zeta n ^ k)
  map_zero' := by simp
  map_add' k l := by
    show Additive.ofMul (zeta n ^ (k + l))
      = Additive.ofMul (zeta n ^ k) + Additive.ofMul (zeta n ^ l)
    rw [zpow_add]
    rfl

/-- **The character `ZMod n →+ Additive ℂˣ`.**  Every element of `ZMod n` is the class of an
integer, and the class of `n` is zero, so `k ↦ ζᵏ` descends. -/
def phiAdd (n : ℕ) (hn : n ≠ 0) : ZMod n →+ Additive ℂˣ :=
  ZMod.lift n ⟨zetaPowAdd n, by
    show Additive.ofMul (zeta n ^ ((n : ℤ))) = 0
    rw [zpow_natCast, zeta_pow_eq_one hn]
    rfl⟩

theorem phiAdd_apply_val (n : ℕ) (hn : n ≠ 0) (a : ZMod n) :
    phiAdd n hn a = Additive.ofMul (zeta n ^ ((a.val : ℤ))) := by
  have : NeZero n := ⟨hn⟩
  conv_lhs =>
    rw [← ZMod.natCast_zmod_val a]
    rw [← Int.cast_natCast]
  rw [phiAdd, ZMod.lift_coe]
  rfl

/-- **The character `Multiplicative (ZMod n) →* ℂˣ`**, the multiplicative form of `phiAdd`. -/
def phi (n : ℕ) (hn : n ≠ 0) : Multiplicative (ZMod n) →* ℂˣ where
  toFun g := Additive.toMul (phiAdd n hn (Multiplicative.toAdd g))
  map_one' := by
    have h : Multiplicative.toAdd (1 : Multiplicative (ZMod n)) = 0 := rfl
    rw [h, map_zero]
    rfl
  map_mul' g h := by
    have h1 : Multiplicative.toAdd (g * h)
        = Multiplicative.toAdd g + Multiplicative.toAdd h := rfl
    rw [h1, map_add]
    rfl

theorem phi_apply_units (n : ℕ) (hn : n ≠ 0) (g : Multiplicative (ZMod n)) :
    phi n hn g = zeta n ^ (Multiplicative.toAdd g).val := by
  show Additive.toMul (phiAdd n hn (Multiplicative.toAdd g)) = zeta n ^ (Multiplicative.toAdd g).val
  rw [phiAdd_apply_val, zpow_natCast]
  rfl

theorem phi_apply (n : ℕ) (hn : n ≠ 0) (g : Multiplicative (ZMod n)) :
    (phi n hn g : ℂ) = (zeta n : ℂ) ^ (Multiplicative.toAdd g).val := by
  rw [phi_apply_units, Units.val_pow_eq_pow_val]

/-- **`φ a = 1` forces `a = 0`**: `ζ` is a primitive `n`-th root of unity and `a.val < n`. -/
theorem phiAdd_eq_zero_iff {n : ℕ} (hn : n ≠ 0) (a : ZMod n) :
    phiAdd n hn a = 0 ↔ a = 0 := by
  have : NeZero n := ⟨hn⟩
  constructor
  · intro h
    have h1 : (zeta n : ℂ) ^ (a.val : ℤ) = 1 := by
      have h2 : Additive.toMul (phiAdd n hn a) = 1 := congrArg Additive.toMul h
      rw [phiAdd_apply_val] at h2
      simpa using congrArg (fun u : ℂˣ => (u : ℂ)) h2
    rw [zpow_natCast] at h1
    have hdvd : n ∣ a.val := (zeta_isPrimitiveRoot hn).pow_eq_one_iff_dvd a.val |>.mp h1
    have hlt : a.val < n := ZMod.val_lt a
    have h0 : a.val = 0 := Nat.eq_zero_of_dvd_of_lt hdvd hlt
    rw [← ZMod.natCast_zmod_val a, h0]
    simp
  · intro h
    subst h
    rw [phiAdd_apply_val]
    simp

/-- **`φ` is injective.** -/
theorem phi_injective (n : ℕ) (hn : n ≠ 0) : Function.Injective (phi n hn) := by
  intro g h hgh
  have h2 : phiAdd n hn (Multiplicative.toAdd g) = phiAdd n hn (Multiplicative.toAdd h) := by
    have := congrArg (fun u : ℂˣ => Additive.ofMul u) hgh
    simpa [phi] using this
  have h3 : phiAdd n hn (Multiplicative.toAdd g - Multiplicative.toAdd h) = 0 := by
    rw [map_sub, h2, sub_self]
  have h4 := (phiAdd_eq_zero_iff hn _).mp h3
  exact Multiplicative.toAdd.injective (sub_eq_zero.mp h4)

/-- Every value of `φ` has norm one: the action preserves the unit sphere. -/
theorem phi_norm (n : ℕ) (hn : n ≠ 0) (g : Multiplicative (ZMod n)) :
    ‖(phi n hn g : ℂ)‖ = 1 := by
  rw [phi_apply, norm_pow, zeta_norm, one_pow]

end

end Work.RatHurewicz
