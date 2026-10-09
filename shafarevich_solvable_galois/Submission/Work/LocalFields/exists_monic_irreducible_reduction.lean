/-
Copyright (c) 2025. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.

# Monic polynomials with irreducible reduction

This file proves that the ring of integers of a non-archimedean local field `k` has, for
every positive degree `n`, a monic polynomial `f` of degree `n` whose reduction to the (finite)
residue field `𝓀[k]` is irreducible.

The mathematics is in two independent steps:

* `exists_monic_irreducible_of_finite_field`: over a *finite* field there is a monic
  irreducible polynomial of every positive degree.  We realize a finite field `F` of
  characteristic `p` as a subfield of the Galois field with `|F| ^ n` elements, take a primitive
  element of that extension and its minimal polynomial.
* `exists_monic_map_eq_of_surjective`: a monic polynomial over a ring `B` lifts, along a
  surjective ring homomorphism `A →+* B`, to a monic polynomial over `A` with the same image.

Combining the two along the residue map of the (finite) residue field gives the result.
-/
import Mathlib
import Submission.Work.LocalFields.Basic
import Submission.Work.LocalFields.LocalFieldAPI
-- PORT435-BEGIN (v4.35 isDefEq respectTransparency compat)
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- PORT435-END

namespace Work.LocalFields

open Polynomial

set_option linter.style.haveILetI false

/-- Over a finite field there is a monic irreducible polynomial of every positive degree.

We embed `F` into the Galois field with `Nat.card F ^ n` elements, use the primitive element
theorem to write that field extension as `F⟮α⟯` and take `minpoly F α`. -/
theorem exists_monic_irreducible_of_finite_field (F : Type*) [Field F] [Finite F]
    (n : ℕ) (hn : n ≠ 0) :
    ∃ f : F[X], f.Monic ∧ f.natDegree = n ∧ Irreducible f := by
  obtain ⟨p, hp⟩ := CharP.exists F
  haveI : CharP F p := hp
  have hp_prime : p.Prime := CharP.char_is_prime F p
  haveI : Fact p.Prime := ⟨hp_prime⟩
  letI : Algebra (ZMod p) F := ZMod.algebra F p
  set k := Module.finrank (ZMod p) F with hk
  have hFcard : Nat.card F = p ^ k := by
    rw [hk]; exact (FiniteField.pow_finrank_eq_natCard p F).symm
  have hk_ne : k ≠ 0 := by
    intro h0
    rw [h0, pow_zero] at hFcard
    have := Finite.one_lt_card (α := F)
    omega
  -- An extension `E` of `F` of degree `n`, namely the Galois field with `p ^ (k * n)` elements.
  let E := GaloisField p (k * n)
  haveI : Finite E := inferInstance
  have hE : Module.finrank (ZMod p) E = k * n :=
    GaloisField.finrank p (n := k * n) (Nat.mul_ne_zero hk_ne hn)
  have hdvd : Module.finrank (ZMod p) F ∣ Module.finrank (ZMod p) E := by
    rw [hE, ← hk]
    exact dvd_mul_right k n
  obtain ⟨φ⟩ :=
    FiniteField.nonempty_algHom_of_finrank_dvd (F := ZMod p) (K := F) (L := E) hdvd
  letI : Algebra F E := φ.toRingHom.toAlgebra
  have hcardE : Nat.card E = p ^ (k * n) := GaloisField.card p (k * n) (Nat.mul_ne_zero hk_ne hn)
  -- Comparison of cardinalities gives `[E : F] = n`.
  have hfin : Module.finrank F E = n := by
    haveI : Module.Finite F E := Module.Finite.of_finite
    have h1 : Nat.card E = Nat.card F ^ Module.finrank F E := Module.natCard_eq_pow_finrank
    rw [hcardE, hFcard, ← pow_mul] at h1
    have h2 : k * n = k * Module.finrank F E := Nat.pow_right_injective hp_prime.one_lt h1
    exact (Nat.mul_left_cancel (Nat.pos_of_ne_zero hk_ne) h2).symm
  haveI : FiniteDimensional F E := Module.Finite.of_finite
  haveI : Algebra.IsSeparable F E := inferInstance
  obtain ⟨α, hα⟩ := Field.exists_primitive_element F E
  refine ⟨minpoly F α, ?_, ?_, ?_⟩
  · exact minpoly.monic (IsIntegral.of_finite F α)
  · exact ((Field.primitive_element_iff_minpoly_natDegree_eq F α).mp hα).trans hfin
  · exact minpoly.irreducible (IsIntegral.of_finite F α)

/-- A monic polynomial over `B` lifts to a monic polynomial over `A` with the same image, along
a surjective ring homomorphism `A →+* B`.

The lift is built coefficientwise: fix any section of `φ` normalized so that it sends `0` to `0`
and `1` to `1`, lift the coefficients of `g` by it and use that `g` is monic. -/
theorem exists_monic_map_eq_of_surjective {A B : Type*} [CommSemiring A] [Nontrivial A]
    [CommSemiring B] [Nontrivial B] (φ : A →+* B) (hφ : Function.Surjective φ)
    {g : B[X]} (hg : g.Monic) :
    ∃ f : A[X], f.Monic ∧ f.map φ = g := by
  classical
  let s : B → A := fun b =>
    if h0 : b = 0 then 0 else if h1 : b = 1 then 1 else Classical.choose (hφ b)
  have hs : ∀ b, φ (s b) = b := by
    intro b
    by_cases h0 : b = 0
    · subst h0; simp [s]
    · by_cases h1 : b = 1
      · subst h1; simp [s]
      · simp only [s, dif_neg h0, dif_neg h1]
        exact Classical.choose_spec (hφ b)
  have hs0 : s 0 = 0 := by simp [s]
  have hs1 : s 1 = 1 := by simp [s]
  have hcoeff : ∀ j, (g.sum fun i a => C (s a) * X ^ i).coeff j
      = if j ∈ g.support then s (g.coeff j) else 0 := by
    intro j
    rw [Polynomial.coeff_sum]
    simp only [Polynomial.coeff_C_mul_X_pow]
    rw [Polynomial.sum_def]
    rw [Finset.sum_ite_eq]
  have hmap : (g.sum fun i a => C (s a) * X ^ i).map φ = g := by
    rw [Polynomial.sum_def, Polynomial.map_sum]
    simp only [Polynomial.map_mul, Polynomial.map_pow, Polynomial.map_C, Polynomial.map_X, hs]
    exact Polynomial.sum_C_mul_X_pow_eq g
  refine ⟨g.sum fun i a => C (s a) * X ^ i, ?_, hmap⟩
  have hmem : g.natDegree ∈ g.support :=
    Polynomial.mem_support_iff.mpr (by rw [Polynomial.Monic.coeff_natDegree hg]; exact one_ne_zero)
  have hgoal : (g.sum fun i a => C (s a) * X ^ i).coeff g.natDegree = 1 := by
    rw [hcoeff g.natDegree, if_pos hmem, Polynomial.Monic.coeff_natDegree hg, hs1]
  have hnd : (g.sum fun i a => C (s a) * X ^ i).natDegree = g.natDegree := by
    refine Polynomial.natDegree_eq_of_le_of_coeff_ne_zero ?_ ?_
    · rw [Polynomial.natDegree_le_iff_coeff_eq_zero]
      intro N hN
      rw [hcoeff N]
      simp [Polynomial.mem_support_iff, Polynomial.coeff_eq_zero_of_natDegree_lt hN]
    · rw [hgoal]
      exact one_ne_zero
  rw [Polynomial.Monic, Polynomial.leadingCoeff, hnd, hgoal]

theorem exists_monic_irreducible_reduction {k : Type*} [Field k]
    [Valued k (WithZero (Multiplicative ℤ))] [Work.LocalFields.IsLocalField k]
    (n : ℕ) (hn : n ≠ 0) :
    ∃ f : Polynomial (Valued.integer k), f.Monic ∧ f.natDegree = n ∧
      Irreducible (f.map (IsLocalRing.residue (Valued.integer k))) := by
  obtain ⟨g, hgmon, hgdeg, hgirr⟩ :=
    exists_monic_irreducible_of_finite_field (IsLocalRing.ResidueField (Valued.integer k)) n hn
  obtain ⟨f, hfmon, hfmap⟩ := exists_monic_map_eq_of_surjective
    (IsLocalRing.residue (Valued.integer k)) IsLocalRing.residue_surjective hgmon
  refine ⟨f, hfmon, ?_, ?_⟩
  · rw [← hfmon.natDegree_map (IsLocalRing.residue (Valued.integer k)), hfmap]
    exact hgdeg
  · rw [hfmap]
    exact hgirr

end Work.LocalFields
