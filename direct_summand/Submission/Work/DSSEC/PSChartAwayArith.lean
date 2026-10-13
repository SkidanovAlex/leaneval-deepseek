import Mathlib
import Submission.Work.DSSEC.PSChart

namespace Work.DSSEC
namespace PSGen

attribute [local instance] MvPolynomial.gradedAlgebra
open CategoryTheory AlgebraicGeometry
universe u

section Gen

variable {A : Type u} [CommRing A] {N : ℕ}

/-- `n • d = n * d` in `ℕ`. -/
lemma nsmul_nat_eq_mul (n d : ℕ) : n • d = n * d := by
  induction n with
  | zero => simp
  | succ k ih => rw [succ_nsmul, ih, Nat.succ_mul]

/-! ### Arithmetic of `Away.mk` -/

/-- `Away.mk` is additive in the numerator, for a fixed degree. -/
theorem Away_mk_add {f : MvPolynomial (Fin (N + 1)) A} {d : ℕ} (hf : f ∈ DSMap.PGr A N d)
    (n : ℕ) (x y : MvPolynomial (Fin (N + 1)) A)
    (hx : x ∈ DSMap.PGr A N (n • d)) (hy : y ∈ DSMap.PGr A N (n • d))
    (hxy : x + y ∈ DSMap.PGr A N (n • d)) :
    HomogeneousLocalization.Away.mk (DSMap.PGr A N) hf n x hx
      + HomogeneousLocalization.Away.mk (DSMap.PGr A N) hf n y hy
      = HomogeneousLocalization.Away.mk (DSMap.PGr A N) hf n (x + y) hxy := by
  apply HomogeneousLocalization.val_injective (Submonoid.powers f)
  rw [HomogeneousLocalization.val_add, HomogeneousLocalization.Away.val_mk,
    HomogeneousLocalization.Away.val_mk, HomogeneousLocalization.Away.val_mk]
  exact Localization.add_mk_self x ⟨f ^ n, by use n⟩ y

/-- `Away.mk` depends on the numerator only. -/
theorem Away_mk_congr {f : MvPolynomial (Fin (N + 1)) A} {d : ℕ} (hf : f ∈ DSMap.PGr A N d)
    (n : ℕ) {x y : MvPolynomial (Fin (N + 1)) A} (hxy : x = y)
    (hx : x ∈ DSMap.PGr A N (n • d)) (hy : y ∈ DSMap.PGr A N (n • d)) :
    HomogeneousLocalization.Away.mk (DSMap.PGr A N) hf n x hx
      = HomogeneousLocalization.Away.mk (DSMap.PGr A N) hf n y hy := by
  subst hxy
  exact congrArg (fun h => HomogeneousLocalization.Away.mk (DSMap.PGr A N) hf n x h)
    (Subsingleton.elim _ _)

/-- `IsLocalization.mk'` is additive in the numerator, for a fixed denominator. -/
theorem mk'_add_same (f : MvPolynomial (Fin (N + 1)) A) (n : ℕ)
    (x y : MvPolynomial (Fin (N + 1)) A) :
    IsLocalization.mk' (M := Submonoid.powers f) (Localization.Away f) (x + y)
        ⟨f ^ n, by use n⟩
      = IsLocalization.mk' (M := Submonoid.powers f) (Localization.Away f) x ⟨f ^ n, by use n⟩
      + IsLocalization.mk' (M := Submonoid.powers f) (Localization.Away f) y
          ⟨f ^ n, by use n⟩ := by
  rw [← Localization.mk_eq_mk']
  exact (Localization.add_mk_self x ⟨f ^ n, by use n⟩ y).symm

/-- The `Finset` form of `mk'_add_same`. -/
theorem mk'_sum_same (f : MvPolynomial (Fin (N + 1)) A) (n : ℕ)
    (s : Finset (Fin (N + 1) →₀ ℕ)) (g : (Fin (N + 1) →₀ ℕ) → MvPolynomial (Fin (N + 1)) A) :
    IsLocalization.mk' (M := Submonoid.powers f) (Localization.Away f) (∑ i ∈ s, g i)
        ⟨f ^ n, by use n⟩
      = ∑ i ∈ s, IsLocalization.mk' (M := Submonoid.powers f) (Localization.Away f) (g i)
          ⟨f ^ n, by use n⟩ := by
  induction s using Finset.induction_on with
  | empty => simp [Finset.sum_empty]
  | insert a t ha ih => rw [Finset.sum_insert ha, Finset.sum_insert ha, mk'_add_same, ih]

/-- `Away.mk` is additive over a finite sum of numerators of a fixed degree. -/
theorem Away_mk_sum {f : MvPolynomial (Fin (N + 1)) A} {d : ℕ} (hf : f ∈ DSMap.PGr A N d)
    (n : ℕ) (s : Finset (Fin (N + 1) →₀ ℕ))
    (g : (Fin (N + 1) →₀ ℕ) → MvPolynomial (Fin (N + 1)) A)
    (hg : ∀ i, g i ∈ DSMap.PGr A N (n • d))
    (hsum : (∑ i ∈ s, g i) ∈ DSMap.PGr A N (n • d)) :
    HomogeneousLocalization.Away.mk (DSMap.PGr A N) hf n (∑ i ∈ s, g i) hsum
      = ∑ i ∈ s, HomogeneousLocalization.Away.mk (DSMap.PGr A N) hf n (g i) (hg i) := by
  have h1 : (∑ i ∈ s, HomogeneousLocalization.Away.mk (DSMap.PGr A N) hf n (g i) (hg i)).val
      = ∑ i ∈ s, Localization.mk (g i) ⟨f ^ n, by use n⟩ := by
    rw [← HomogeneousLocalization.algebraMap_apply (𝒜 := DSMap.PGr A N)
      (x := Submonoid.powers f), map_sum]
    simp only [HomogeneousLocalization.algebraMap_apply, HomogeneousLocalization.Away.val_mk]
  apply HomogeneousLocalization.val_injective (Submonoid.powers f)
  rw [HomogeneousLocalization.Away.val_mk, h1]
  rw [Localization.mk_eq_mk']
  exact mk'_sum_same f n s g

/-! ### The structure map -/

/-- The value of `AtoAwayS S a` in the localisation is the constant polynomial `a`. -/
theorem val_AtoAwayS (S : Finset (Idx N)) (a : A) :
    (AtoAwayS (A := A) (N := N) S a).val =
      algebraMap (MvPolynomial (Fin (N + 1)) A)
        (Localization.Away (tPS (A := A) (N := N) S)) (MvPolynomial.C a) := by
  rw [AtoAwayS, RingHom.comp_apply, ← HomogeneousLocalization.algebraMap_eq]
  rw [← HomogeneousLocalization.algebraMap_apply (𝒜 := DSMap.PGr A N)
    (x := Submonoid.powers (tPS (A := A) (N := N) S))]
  rw [← IsScalarTower.algebraMap_apply (↥(DSMap.PGr A N 0))
    (HomogeneousLocalization.Away (DSMap.PGr A N) (tPS (A := A) (N := N) S))
    (Localization.Away (tPS (A := A) (N := N) S)) (AtoA0 (A := A) (N := N) a)]
  rw [IsScalarTower.algebraMap_apply (↥(DSMap.PGr A N 0)) (MvPolynomial (Fin (N + 1)) A)
    (Localization.Away (tPS (A := A) (N := N) S)) (AtoA0 (A := A) (N := N) a)]
  congr 1

/-- The polynomial `C c` is homogeneous of degree `0`. -/
theorem mem_PGr_C (S : Finset (Idx N)) (c : A) :
    (MvPolynomial.C c : MvPolynomial (Fin (N + 1)) A) ∈ DSMap.PGr A N (0 • S.card) := by
  rw [MvPolynomial.mem_homogeneousSubmodule]
  simpa using MvPolynomial.isHomogeneous_C (Fin (N + 1)) c

/-- `Away.mk` at degree `0` of a constant polynomial is `AtoAwayS S c`. -/
theorem Away_mk_C (S : Finset (Idx N)) (c : A)
    (h : (MvPolynomial.C c) ∈ DSMap.PGr A N (0 • S.card)) :
    HomogeneousLocalization.Away.mk (DSMap.PGr A N) (tPS_mem S) 0 (MvPolynomial.C c) h
      = AtoAwayS (A := A) (N := N) S c := by
  apply HomogeneousLocalization.val_injective (Submonoid.powers (tPS (A := A) (N := N) S))
  rw [HomogeneousLocalization.Away.val_mk, val_AtoAwayS]
  rw [Localization.mk_eq_mk']
  rw [show (⟨(tPS (A := A) (N := N) S) ^ 0, by use 0⟩ :
      Submonoid.powers (tPS (A := A) (N := N) S)) = 1 from Subtype.ext (pow_zero _)]
  rw [IsLocalization.mk'_one]

/-- `Away.mk` of the zero numerator is zero. -/
theorem Away_mk_zero (S : Finset (Idx N)) (n : ℕ)
    (h : (0 : MvPolynomial (Fin (N + 1)) A) ∈ DSMap.PGr A N (n • S.card)) :
    HomogeneousLocalization.Away.mk (DSMap.PGr A N) (tPS_mem S) n
      (0 : MvPolynomial (Fin (N + 1)) A) h = 0 :=
  HomogeneousLocalization.mk_eq_zero_of_num _ (Subtype.ext rfl)

/-- A constant multiple of a numerator: `Away.mk` interacts with `C c *` as `AtoAwayS c *`. -/
theorem Away_mk_C_mul (S : Finset (Idx N)) (n : ℕ) (c : A) (p : MvPolynomial (Fin (N + 1)) A)
    (hp : p ∈ DSMap.PGr A N (n • S.card))
    (hx : (MvPolynomial.C c) ∈ DSMap.PGr A N (0 • S.card))
    (h : MvPolynomial.C c * p ∈ DSMap.PGr A N (n • S.card)) :
    HomogeneousLocalization.Away.mk (DSMap.PGr A N) (tPS_mem S) n (MvPolynomial.C c * p) h
      = HomogeneousLocalization.Away.mk (DSMap.PGr A N) (tPS_mem S) 0 (MvPolynomial.C c) hx
        * HomogeneousLocalization.Away.mk (DSMap.PGr A N) (tPS_mem S) n p hp := by
  apply HomogeneousLocalization.val_injective (Submonoid.powers (tPS (A := A) (N := N) S))
  rw [HomogeneousLocalization.val_mul, HomogeneousLocalization.Away.val_mk,
    HomogeneousLocalization.Away.val_mk, HomogeneousLocalization.Away.val_mk]
  rw [Localization.mk_mul]
  congr 1
  exact Subtype.ext (by simp)

/-! ### The chart coordinates -/

/-- In the localisation, `x_k/x_l` multiplied by `x_l` is `x_k`. -/
theorem val_chartFracPS_mul (S : Finset (Idx N)) (l : Idx N) (hl : l ∈ S) (k : Idx N) :
    (chartFracPS (A := A) (N := N) S l hl k).val *
      algebraMap (MvPolynomial (Fin (N + 1)) A)
        (Localization.Away (tPS (A := A) (N := N) S)) (MvPolynomial.X l.down)
      = algebraMap (MvPolynomial (Fin (N + 1)) A)
        (Localization.Away (tPS (A := A) (N := N) S)) (MvPolynomial.X k.down) := by
  have h1 : (chartFracPS (A := A) (N := N) S l hl k).val *
      algebraMap (MvPolynomial (Fin (N + 1)) A)
        (Localization.Away (tPS (A := A) (N := N) S)) (tPS (A := A) (N := N) S)
      = algebraMap (MvPolynomial (Fin (N + 1)) A)
        (Localization.Away (tPS (A := A) (N := N) S))
        (MvPolynomial.X k.down * ∏ m ∈ S.erase l, MvPolynomial.X m.down) := by
    rw [chartFracPS, HomogeneousLocalization.Away.val_mk]
    rw [show algebraMap (MvPolynomial (Fin (N + 1)) A)
          (Localization.Away (tPS (A := A) (N := N) S)) (tPS (A := A) (N := N) S)
        = algebraMap (MvPolynomial (Fin (N + 1)) A)
          (Localization.Away (tPS (A := A) (N := N) S)) ((tPS (A := A) (N := N) S) ^ 1)
        from by rw [map_pow, pow_one]]
    rw [Localization.mk_eq_mk'_apply, IsLocalization.mk'_spec]
  refine IsUnit.mul_right_cancel
    (IsLocalization.Away.algebraMap_isUnit (tPS (A := A) (N := N) S)) ?_
  rw [mul_assoc,
    mul_comm (algebraMap (MvPolynomial (Fin (N + 1)) A)
      (Localization.Away (tPS (A := A) (N := N) S)) (MvPolynomial.X l.down))
      (algebraMap (MvPolynomial (Fin (N + 1)) A)
        (Localization.Away (tPS (A := A) (N := N) S)) (tPS (A := A) (N := N) S)),
    ← mul_assoc, h1]
  rw [← map_mul, ← map_mul]
  congr 1
  rw [tPS_eq_mul (A := A) (N := N) S l hl]
  ring

/-! ### Monomials -/


end Gen

end PSGen

end Work.DSSEC
