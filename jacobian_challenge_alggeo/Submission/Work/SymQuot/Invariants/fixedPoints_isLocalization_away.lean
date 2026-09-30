/-
Copyright (c) 2026. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.

# Localization away from a `G`-invariant element commutes with invariants

Let a finite group `G` act on commutative rings `A` and `B`, with `B` an `A`-algebra such that the
structure map `A → B` is `G`-equivariant (`hcompat`).  If `B` is the localization of `A` away from an
element `s : A` which is fixed by `G`, then the fixed subring `B^G` is the localization of `A^G`
away from `s`.

This is the ring-theoretic shadow of the fact that localizing a `G`-scheme at an invariant open
subset commutes with the quotient by `G`.
-/
import Mathlib
import Submission.Work.SymQuot.Invariants

-- Lean v4.35.0-rc3 / Mathlib 5e0c4e5 made `isDefEq` respect transparency when unifying instances; with it,
-- `ZMod.instField` and `ZMod.commRing` (and `Neg (ZMod p)` via `SubtractionMonoid`) no longer unify, which
-- breaks `ring`/`rw`/module-instance search on `ZMod p`. Restore the v4.34 behaviour for this file.
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false


set_option linter.style.haveILetI false
set_option linter.unusedSectionVars false

namespace Work.SymQuot.Invariants

open Work.SymQuot

section

variable {G : Type*} [Group G] [Finite G] {A : Type*} [CommRing A]
  {B : Type*} [CommRing B] [Algebra A B] [MulSemiringAction G A] [MulSemiringAction G B]

/-- If `s : A` is fixed by `G`, then so is its image `algebraMap A B s` in any `G`-equivariant
`A`-algebra `B`. -/
lemma smul_algebraMap_of_fixed
    (hcompat : ∀ (g : G) (a : A), algebraMap A B (g • a) = g • algebraMap A B a)
    (s : A) (hs : ∀ g : G, g • s = s) (g : G) :
    g • algebraMap A B s = algebraMap A B s := by
  rw [← hcompat g s, hs g]

/-- For `B` the localization of `A` away from a `G`-fixed element `s`, the image of `s` under the
induced map `A^G →+* B^G` is a unit of `B^G` (its inverse in `B` is also `G`-fixed). -/
lemma isUnit_fixedPointsMap_away
    (hcompat : ∀ (g : G) (a : A), algebraMap A B (g • a) = g • algebraMap A B a)
    (s : A) (hs : ∀ g : G, g • s = s) [IsLocalization.Away s B] :
    IsUnit (fixedPointsMap hcompat (⟨s, hs⟩ : FixedPoints.subring A G)) := by
  have hfix : ∀ g : G, g • algebraMap A B s = algebraMap A B s :=
    fun g => smul_algebraMap_of_fixed hcompat s hs g
  obtain ⟨u, hu⟩ : IsUnit (algebraMap A B s) := IsLocalization.Away.algebraMap_isUnit s
  have hv_fix : ∀ g : G, g • (↑(u⁻¹) : B) = ↑(u⁻¹) := by
    intro g
    have hv : (↑(u⁻¹) : B) * algebraMap A B s = 1 := by rw [← hu]; exact Units.inv_mul u
    have h2 : algebraMap A B s * (g • (↑(u⁻¹) : B)) = 1 := by
      have h1 : algebraMap A B s * (↑(u⁻¹) : B) = 1 := by rw [← hu]; exact Units.mul_inv u
      have := congrArg (fun x : B => g • x) h1
      rw [MulSemiringAction.smul_mul, hfix g, MulDistribMulAction.smul_one] at this
      exact this
    have : (↑(u⁻¹) : B) = g • (↑(u⁻¹) : B) := by
      calc (↑(u⁻¹) : B) = (↑(u⁻¹) : B) * 1 := (mul_one _).symm
        _ = (↑(u⁻¹) : B) * (algebraMap A B s * (g • (↑(u⁻¹) : B))) := by rw [h2]
        _ = ((↑(u⁻¹) : B) * algebraMap A B s) * (g • (↑(u⁻¹) : B)) := by rw [mul_assoc]
        _ = 1 * (g • (↑(u⁻¹) : B)) := by rw [hv]
        _ = g • (↑(u⁻¹) : B) := by rw [one_mul]
    exact this.symm
  show IsUnit (⟨algebraMap A B s, hfix⟩ : FixedPoints.subring B G)
  rw [isUnit_iff_exists]
  refine ⟨⟨↑(u⁻¹), hv_fix⟩, ?_, ?_⟩
  · apply Subtype.ext
    show algebraMap A B s * (↑(u⁻¹) : B) = 1
    rw [← hu]; exact Units.mul_inv u
  · apply Subtype.ext
    show (↑(u⁻¹) : B) * algebraMap A B s = 1
    rw [← hu]; exact Units.inv_mul u

/-- Every element `z` of `B^G` can be written as `z * s^n = a` with `a ∈ A^G`, i.e. the image of
`A^G` in `B^G` generates `B^G` as a localization away from `s`.  The proof picks, for each `g`, an
exponent killing `g • a - a`, and takes the maximum over the finite group. -/
lemma exists_fixed_mul_fixedPointsMap_away
    (hcompat : ∀ (g : G) (a : A), algebraMap A B (g • a) = g • algebraMap A B a)
    (s : A) (hs : ∀ g : G, g • s = s) [IsLocalization.Away s B]
    (z : FixedPoints.subring B G) :
    ∃ (n : ℕ) (a : FixedPoints.subring A G),
      z * (fixedPointsMap hcompat (⟨s, hs⟩ : FixedPoints.subring A G)) ^ n
        = fixedPointsMap hcompat a := by
  haveI : Fintype G := Fintype.ofFinite G
  have hz : ∀ g : G, g • (z : B) = (z : B) := z.2
  have hfix : ∀ g : G, g • algebraMap A B s = algebraMap A B s :=
    fun g => smul_algebraMap_of_fixed hcompat s hs g
  obtain ⟨n₀, a₀, ha₀⟩ := IsLocalization.Away.surj s (z : B)
  have hfixed_z : ∀ g : G, g • ((z : B) * (algebraMap A B s) ^ n₀)
      = (z : B) * (algebraMap A B s) ^ n₀ := by
    intro g
    rw [MulSemiringAction.smul_mul, hz g, smul_pow', hfix g]
  have hex : ∀ g : G, ∃ k : ℕ, s ^ k * (g • a₀) = s ^ k * a₀ := by
    intro g
    have h : algebraMap A B (g • a₀) = algebraMap A B a₀ := by
      rw [hcompat g a₀, ← ha₀]
      exact hfixed_z g
    exact IsLocalization.Away.exists_of_eq s h
  let k : G → ℕ := fun g => Classical.choose (hex g)
  have hk : ∀ g, s ^ (k g) * (g • a₀) = s ^ (k g) * a₀ := fun g => Classical.choose_spec (hex g)
  let N : ℕ := Finset.univ.sup k
  have hkN : ∀ g, k g ≤ N := fun g => Finset.le_sup (Finset.mem_univ g)
  have hpow : ∀ g : G, s ^ N * (g • a₀) = s ^ N * a₀ := by
    intro g
    have hle := hkN g
    rw [← Nat.sub_add_cancel hle, pow_add]
    rw [mul_assoc, hk g, ← mul_assoc, ← pow_add, Nat.sub_add_cancel hle]
  have hafix : ∀ g : G, g • (s ^ N * a₀) = s ^ N * a₀ := by
    intro g
    rw [MulSemiringAction.smul_mul, smul_pow', hs g, hpow g]
  refine ⟨n₀ + N, ⟨s ^ N * a₀, hafix⟩, ?_⟩
  apply Subtype.ext
  have hB : (z : B) * (algebraMap A B s) ^ (n₀ + N) = algebraMap A B (s ^ N * a₀) := by
    rw [pow_add, ← mul_assoc, ha₀, map_mul, map_pow, mul_comm]
  simpa using hB

/-- If `a b ∈ A^G` have the same image in `B` (a localization of `A` away from `s`), then some
power of `s` already kills their difference in `A`. -/
lemma exists_pow_mul_eq_of_fixedPointsMap_eq
    (hcompat : ∀ (g : G) (a : A), algebraMap A B (g • a) = g • algebraMap A B a)
    (s : A) (hs : ∀ g : G, g • s = s) [IsLocalization.Away s B]
    {a b : FixedPoints.subring A G}
    (h : fixedPointsMap hcompat a = fixedPointsMap hcompat b) :
    ∃ n : ℕ, (⟨s, hs⟩ : FixedPoints.subring A G) ^ n * a
      = (⟨s, hs⟩ : FixedPoints.subring A G) ^ n * b := by
  have h' : algebraMap A B (a : A) = algebraMap A B (b : A) := by
    have := congrArg Subtype.val h
    simpa using this
  obtain ⟨n, hn⟩ := IsLocalization.Away.exists_of_eq s h'
  refine ⟨n, ?_⟩
  apply Subtype.ext
  simpa using hn

end

theorem fixedPoints_isLocalization_away {G : Type*} [Group G] [Finite G] {A : Type*} [CommRing A]
    {B : Type*} [CommRing B] [Algebra A B] [MulSemiringAction G A] [MulSemiringAction G B]
    (hcompat : ∀ (g : G) (a : A), algebraMap A B (g • a) = g • algebraMap A B a)
    (s : A) (hs : ∀ g : G, g • s = s) [IsLocalization.Away s B] :
    letI : Algebra (FixedPoints.subring A G) (FixedPoints.subring B G) :=
      RingHom.toAlgebra (Work.SymQuot.fixedPointsMap hcompat)
    IsLocalization.Away (⟨s, hs⟩ : FixedPoints.subring A G) (FixedPoints.subring B G) := by
  letI : Algebra (FixedPoints.subring A G) (FixedPoints.subring B G) :=
    RingHom.toAlgebra (Work.SymQuot.fixedPointsMap hcompat)
  have key : (algebraMap (FixedPoints.subring A G) (FixedPoints.subring B G))
      = Work.SymQuot.fixedPointsMap hcompat := RingHom.algebraMap_toAlgebra _
  refine IsLocalization.Away.mk (⟨s, hs⟩ : FixedPoints.subring A G) ?_ ?_ ?_
  · rw [key]
    exact isUnit_fixedPointsMap_away hcompat s hs
  · intro z
    rw [key]
    exact exists_fixed_mul_fixedPointsMap_away hcompat s hs z
  · intro a b h
    rw [key] at h
    exact exists_pow_mul_eq_of_fixedPointsMap_eq hcompat s hs h

end Work.SymQuot.Invariants
