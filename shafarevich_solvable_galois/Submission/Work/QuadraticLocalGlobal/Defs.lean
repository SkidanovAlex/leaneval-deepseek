/-
Copyright (c) 2025. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.

# The quadratic local–global principles over `ℚ`

This file sets up the vocabulary of the area `Submission/Work/QuadraticLocalGlobal/`:

* the *norm form* condition `IsNorm d x` — "`x` is a norm from `ℚ(√d)`", i.e. `x = p² - d q²`;
* the *isotropy* of the ternary form `x² - a y² - b z²` over `ℚ` (the library's `Isotropic ℚ`);
* the measure `meas a b` used for the descent proof of the Hasse norm theorem;
* the local square-class relations used for Grünwald's theorem in degree `2`;
* the squarefree-part machinery (`sqfreePart`), and the "uniqueness of the local square class"
  interface.

Everything lives in the namespace `Work.QuadraticLocalGlobal` and reuses the conventions of
`Work.HilbertSymbol` (`Place := Option ℕ`, `ℚ_[p] = Padic p`).
-/
import Submission.Work.HilbertSymbol.All
-- PORT435-BEGIN (v4.35 isDefEq respectTransparency compat)
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- PORT435-END

noncomputable section

open scoped Classical

namespace Work.QuadraticLocalGlobal

open Work.HilbertSymbol

/-! ## The norm-form and isotropy predicates -/

/-- `IsNorm d x` means that `x` is a norm from `ℚ(√d)`: there are `p q : ℚ` with
`x = p² - d q²`. -/
def IsNorm (d x : ℚˣ) : Prop := ∃ p q : ℚ, p ^ 2 - (d : ℚ) * q ^ 2 = (x : ℚ)

/-- The ternary form `x² - a y² - b z²` is isotropic over `ℚ`.  This is the library's
`Work.HilbertSymbol.Isotropic` at `K = ℚ`, recorded here for convenience. -/
def IsotropicRat (a b : ℚˣ) : Prop :=
  ∃ x y z : ℚ, (x ≠ 0 ∨ y ≠ 0 ∨ z ≠ 0) ∧ x ^ 2 - (a : ℚ) * y ^ 2 - (b : ℚ) * z ^ 2 = 0

theorem isotropicRat_iff (a b : ℚˣ) :
    IsotropicRat a b ↔ Isotropic ℚ (a : ℚ) (b : ℚ) := Iff.rfl

theorem isotropicRat_comm (a b : ℚˣ) : IsotropicRat a b ↔ IsotropicRat b a := by
  constructor
  · rintro ⟨x, y, z, hne, h⟩
    refine ⟨x, z, y, ?_, ?_⟩
    · rcases hne with h | h | h
      · exact Or.inl h
      · exact Or.inr (Or.inr h)
      · exact Or.inr (Or.inl h)
    · rw [← h]; ring
  · rintro ⟨x, y, z, hne, h⟩
    refine ⟨x, z, y, ?_, ?_⟩
    · rcases hne with h | h | h
      · exact Or.inl h
      · exact Or.inr (Or.inr h)
      · exact Or.inr (Or.inl h)
    · rw [← h]; ring

/-! ## The descent measure -/

/-- The measure used for the induction in the proof of the Hasse norm theorem: the sum of the
`numDenNat`s (the product of numerator and denominator, in lowest terms) of the two arguments. -/
def meas (a b : ℚˣ) : ℕ := numDenNat a + numDenNat b

theorem meas_comm (a b : ℚˣ) : meas a b = meas b a := by
  simp [meas, Nat.add_comm]

theorem meas_pos (a b : ℚˣ) : 0 < meas a b := by
  have h1 : 0 < numDenNat a := by
    rw [numDenNat]
    exact Nat.mul_pos (Int.natAbs_pos.mpr (Rat.num_ne_zero.mpr a.ne_zero)) (Rat.den_pos _)
  have h2 : 0 < numDenNat b := by
    rw [numDenNat]
    exact Nat.mul_pos (Int.natAbs_pos.mpr (Rat.num_ne_zero.mpr b.ne_zero)) (Rat.den_pos _)
  simp [meas, Nat.add_pos_left h1]

/-- The integer `num * den` attached to a rational unit; multiplying it by `(den)²` gives back
the original element (`intUnit_num_den_mul_sq`). -/
def intRep (a : ℚˣ) : ℤ := (a : ℚ).num * ((a : ℚ).den : ℤ)

theorem intRep_ne_zero (a : ℚˣ) : intRep a ≠ 0 :=
  mul_ne_zero (Rat.num_ne_zero.mpr a.ne_zero) (by exact_mod_cast (a : ℚ).den_ne_zero)

theorem natAbs_intRep (a : ℚˣ) : (intRep a).natAbs = numDenNat a := by
  rw [intRep, numDenNat, Int.natAbs_mul]
  norm_num [Int.natAbs_natCast]

/-- The integral representative of the square class of `a`: `intRep a = num a * den a`, and
`a / intRep a` is a square in `ℚˣ`. -/
theorem exists_intRep_mul_sq (a : ℚˣ) :
    ∃ s : ℚˣ, intUnit (intRep a) (intRep_ne_zero a) * s ^ 2 = a := by
  obtain ⟨s, hs⟩ : ∃ s : ℚˣ,
      intUnit ((a : ℚ).num * ((a : ℚ).den : ℤ))
        (mul_ne_zero (Rat.num_ne_zero.mpr a.ne_zero)
          (by exact_mod_cast (a : ℚ).den_ne_zero)) * s ^ 2 = a := by
    refine ⟨(intUnit ((a : ℚ).den : ℤ) (by exact_mod_cast (a : ℚ).den_ne_zero))⁻¹, ?_⟩
    rw [← intUnit_num_den_mul_sq a]
    group
  exact ⟨s, by simpa [intRep] using hs⟩

/-! ## Local square classes -/

/-- `SameSquare d c` means that `d` and `c` have the same class modulo squares in `ℚ_[p]`:
there is `z` with `z ^ 2 * d = c`. -/
def SameSquare {p : ℕ} [Fact p.Prime] (d c : ℚ_[p]) : Prop := ∃ z : ℚ_[p], z ^ 2 * d = c

theorem sameSquare_refl {p : ℕ} [Fact p.Prime] (d : ℚ_[p]) : SameSquare d d :=
  ⟨1, by ring⟩

theorem sameSquare_iff_isSquare_div {p : ℕ} [Fact p.Prime] {d c : ℚ_[p]} (hd : d ≠ 0) :
    SameSquare d c ↔ IsSquare (c / d) := by
  constructor
  · rintro ⟨z, hz⟩
    refine ⟨z, ?_⟩
    have h : c / d = z * z := by rw [← hz]; field_simp
    rw [h]
  · rintro ⟨y, hy⟩
    refine ⟨y, ?_⟩
    have h : y ^ 2 = c / d := by rw [sq]; exact hy.symm
    rw [h]
    field_simp

/-! ## The `p`-adic unit part of an element of `ℚ_[p]` -/

/-- The unit part of a nonzero `p`-adic number: `p ^ (-v_p x) * x`, as a unit of `ℤ_[p]`. -/
def padicUnitOf (p : ℕ) [Fact p.Prime] (x : ℚ_[p]) (hx : x ≠ 0) : ℤ_[p]ˣ :=
  PadicInt.mkUnits (u := (p : ℚ_[p]) ^ (-(x.valuation)) * x) (by
    have hprod : (p : ℚ_[p]) ^ (-(x.valuation)) * x ≠ 0 :=
      mul_ne_zero (zpow_ne_zero _ (p_cast_ne_zero p)) hx
    rw [Padic.norm_eq_zpow_neg_valuation hprod]
    have hv : ((p : ℚ_[p]) ^ (-(x.valuation)) * x).valuation = 0 := by
      rw [Padic.valuation_mul (zpow_ne_zero _ (p_cast_ne_zero p)) hx, Padic.valuation_zpow,
        Padic.valuation_p]
      ring
    rw [hv, neg_zero, zpow_zero])

theorem padicUnitOf_coe (p : ℕ) [Fact p.Prime] (x : ℚ_[p]) (hx : x ≠ 0) :
    ((padicUnitOf p x hx : ℤ_[p]) : ℚ_[p]) =
      (p : ℚ_[p]) ^ (-(x.valuation)) * x :=
  PadicInt.mkUnits_eq _

theorem padicUnitOf_norm (p : ℕ) [Fact p.Prime] (x : ℚ_[p]) (hx : x ≠ 0) :
    ‖((padicUnitOf p x hx : ℤ_[p]) : ℚ_[p])‖ = 1 := by
  rw [padicUnitOf_coe]
  have hprod : (p : ℚ_[p]) ^ (-(x.valuation)) * x ≠ 0 :=
    mul_ne_zero (zpow_ne_zero _ (p_cast_ne_zero p)) hx
  rw [Padic.norm_eq_zpow_neg_valuation hprod]
  have hv : ((p : ℚ_[p]) ^ (-(x.valuation)) * x).valuation = 0 := by
    rw [Padic.valuation_mul (zpow_ne_zero _ (p_cast_ne_zero p)) hx, Padic.valuation_zpow,
      Padic.valuation_p]
    ring
  rw [hv, neg_zero, zpow_zero]

end Work.QuadraticLocalGlobal
