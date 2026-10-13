import Mathlib
import Submission.Work.DSSEC.Basic
import Submission.Work.DSSEC.adjoin_xiSecS_eq_top
import Submission.Work.DSG2.ChartRingMain

namespace Work.DSSEC

attribute [local instance] MvPolynomial.gradedAlgebra
open CategoryTheory AlgebraicGeometry
universe u

/-! ## Generation of `Away (PGr A N) (tPS S)` by the chart coordinates `x_k/x_l`

This file proves the single missing link of `adjoin_xiSecS_eq_top` directly (rather than through
`awayGenPS_aux`): for `S` nonempty, `Away (PGr A N) (tPS S)` is generated over `A` by the elements
`chartFracPS S l hl k = x_k/x_l`, `l ∈ S`.

The proof follows the pattern of `Work.DSG2.Phi_surjective`: write a general element as
`Away.mk (tPS_mem S) n p hp` with `p` homogeneous of degree `n * |S|`
(`HomogeneousLocalization.Away.mk_surjective`), expand `p` into monomials, and show that each
monomial `∏_j x_j^{w j}` (with `w.degree = n * |S|`) satisfies

  `mk n (∏_j x_j^{w j}) = (∏_j (x_j/x_{l₀})^{w j}) · (∏_{m∈S} x_{l₀}/x_m)^n`.

The arithmetic of `Away.mk` (`Away_mk_add`, `Away_mk_congr`, `Away_mk_sum`, `Away_mk_C`,
`Away_mk_C_mul`) is the same as in `Submission/Work/DSG2/ChartRingBasic.lean`, transported to the
localisation at `tPS S`; every identity is proved by passing to the underlying localisation
`Localization.Away (tPS S)` along the injective `HomogeneousLocalization.val` and clearing
denominators. -/

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

/-- The product of the variables over `S` equals the product over the subtype. -/
theorem tPS_eq_prod_attach (S : Finset (Idx N)) :
    tPS (A := A) (N := N) S =
      ∏ m : {m // m ∈ S}, (MvPolynomial.X m.1.down : MvPolynomial (Fin (N + 1)) A) := by
  rw [tPS, ← Finset.prod_attach S
    (fun m => (MvPolynomial.X m.down : MvPolynomial (Fin (N + 1)) A))]
  rw [Finset.attach_eq_univ]

/-- The monomial `∏ j, X_j ^ (w j)` is homogeneous of degree `w.degree`. -/
theorem isHomogeneous_prod_X (w : Fin (N + 1) →₀ ℕ) :
    (∏ j, (MvPolynomial.X j : MvPolynomial (Fin (N + 1)) A) ^ (w j)).IsHomogeneous w.degree := by
  rw [Finsupp.degree_eq_sum]
  exact MvPolynomial.IsHomogeneous.prod Finset.univ
    (fun j => (MvPolynomial.X j : MvPolynomial (Fin (N + 1)) A) ^ (w j)) w
    (fun j _ => by simpa using (MvPolynomial.isHomogeneous_X A j).pow (w j))

/-- The monomial `∏ j, X_j ^ (w j)` lies in the graded piece of degree `n * |S|`. -/
theorem mem_PGr_prod_X (S : Finset (Idx N)) (n : ℕ) (w : Fin (N + 1) →₀ ℕ)
    (hw : w.degree = n * S.card) :
    (∏ j, (MvPolynomial.X j : MvPolynomial (Fin (N + 1)) A) ^ (w j))
      ∈ DSMap.PGr A N (n • S.card) := by
  rw [MvPolynomial.mem_homogeneousSubmodule, nsmul_nat_eq_mul, ← hw]
  exact isHomogeneous_prod_X (A := A) (N := N) w

/-- `(∏_{m∈S} x_{l₀}/x_m) · ∏_{m∈S} x_m = x_{l₀}^{|S|}` in the localisation. -/
theorem prod_val_mul_tPS (S : Finset (Idx N)) (l₀ : Idx N) (_hl₀ : l₀ ∈ S) :
    (∏ m : {m // m ∈ S}, (chartFracPS (A := A) (N := N) S m.1 m.2 l₀).val) *
      algebraMap (MvPolynomial (Fin (N + 1)) A)
        (Localization.Away (tPS (A := A) (N := N) S)) (tPS (A := A) (N := N) S)
      = (algebraMap (MvPolynomial (Fin (N + 1)) A)
          (Localization.Away (tPS (A := A) (N := N) S))
          (MvPolynomial.X l₀.down)) ^ S.card := by
  have hmap : algebraMap (MvPolynomial (Fin (N + 1)) A)
        (Localization.Away (tPS (A := A) (N := N) S)) (tPS (A := A) (N := N) S)
      = ∏ m : {m // m ∈ S}, algebraMap (MvPolynomial (Fin (N + 1)) A)
          (Localization.Away (tPS (A := A) (N := N) S)) (MvPolynomial.X m.1.down) := by
    rw [← map_prod]
    exact congrArg _ (tPS_eq_prod_attach (A := A) (N := N) S)
  rw [hmap, ← Finset.prod_mul_distrib]
  rw [show (∏ m : {m // m ∈ S}, (chartFracPS (A := A) (N := N) S m.1 m.2 l₀).val *
        algebraMap (MvPolynomial (Fin (N + 1)) A)
          (Localization.Away (tPS (A := A) (N := N) S)) (MvPolynomial.X m.1.down))
      = ∏ _m : {m // m ∈ S}, algebraMap (MvPolynomial (Fin (N + 1)) A)
          (Localization.Away (tPS (A := A) (N := N) S)) (MvPolynomial.X l₀.down) from
    Finset.prod_congr rfl (fun m _ => val_chartFracPS_mul (A := A) (N := N) S m.1 m.2 l₀)]
  rw [Finset.prod_const, Finset.card_univ, Fintype.card_coe]

/-- `(∏_j (x_j/x_{l₀})^{w j}) · x_{l₀}^{w.degree} = ∏_j x_j^{w j}` in the localisation. -/
theorem prod_pow_val_chartFracPS (S : Finset (Idx N)) (l₀ : Idx N) (hl₀ : l₀ ∈ S)
    (w : Fin (N + 1) →₀ ℕ) :
    (∏ j : Fin (N + 1), (chartFracPS (A := A) (N := N) S l₀ hl₀ (ULift.up j)).val ^ (w j)) *
      (algebraMap (MvPolynomial (Fin (N + 1)) A)
        (Localization.Away (tPS (A := A) (N := N) S)) (MvPolynomial.X l₀.down)) ^ (w.degree)
      = algebraMap (MvPolynomial (Fin (N + 1)) A)
        (Localization.Away (tPS (A := A) (N := N) S))
        (∏ j, (MvPolynomial.X j : MvPolynomial (Fin (N + 1)) A) ^ (w j)) := by
  rw [Finsupp.degree_eq_sum, ← Finset.prod_pow_eq_pow_sum]
  rw [← Finset.prod_mul_distrib]
  rw [show (∏ j : Fin (N + 1),
        (chartFracPS (A := A) (N := N) S l₀ hl₀ (ULift.up j)).val ^ (w j) *
        (algebraMap (MvPolynomial (Fin (N + 1)) A)
          (Localization.Away (tPS (A := A) (N := N) S)) (MvPolynomial.X l₀.down)) ^ (w j))
      = ∏ j : Fin (N + 1), ((chartFracPS (A := A) (N := N) S l₀ hl₀ (ULift.up j)).val *
        algebraMap (MvPolynomial (Fin (N + 1)) A)
          (Localization.Away (tPS (A := A) (N := N) S)) (MvPolynomial.X l₀.down)) ^ (w j) from
    Finset.prod_congr rfl (fun j _ => (mul_pow _ _ _).symm)]
  rw [show (∏ j : Fin (N + 1), ((chartFracPS (A := A) (N := N) S l₀ hl₀ (ULift.up j)).val *
        algebraMap (MvPolynomial (Fin (N + 1)) A)
          (Localization.Away (tPS (A := A) (N := N) S)) (MvPolynomial.X l₀.down)) ^ (w j))
      = ∏ j : Fin (N + 1), (algebraMap (MvPolynomial (Fin (N + 1)) A)
          (Localization.Away (tPS (A := A) (N := N) S)) (MvPolynomial.X j)) ^ (w j) from
    Finset.prod_congr rfl
      (fun j _ => by rw [val_chartFracPS_mul (A := A) (N := N) S l₀ hl₀ (ULift.up j)])]
  rw [show (∏ j : Fin (N + 1), (algebraMap (MvPolynomial (Fin (N + 1)) A)
          (Localization.Away (tPS (A := A) (N := N) S)) (MvPolynomial.X j)) ^ (w j))
      = ∏ j : Fin (N + 1), algebraMap (MvPolynomial (Fin (N + 1)) A)
          (Localization.Away (tPS (A := A) (N := N) S))
          ((MvPolynomial.X j : MvPolynomial (Fin (N + 1)) A) ^ (w j)) from
    Finset.prod_congr rfl (fun j _ => (map_pow _ _ _).symm)]
  rw [← map_prod]

/-- The value of `Away.mk` on a monomial: for `w.degree = n * |S|`,
`(∏_j x_j^{w j}) / f^n = (∏_j (x_j/x_{l₀})^{w j}) · (∏_{m∈S} x_{l₀}/x_m)^n`. -/
theorem Away_mk_prod_X (S : Finset (Idx N)) (l₀ : Idx N) (hl₀ : l₀ ∈ S)
    (n : ℕ) (w : Fin (N + 1) →₀ ℕ) (hw : w.degree = n * S.card)
    (h : (∏ j, (MvPolynomial.X j : MvPolynomial (Fin (N + 1)) A) ^ (w j))
        ∈ DSMap.PGr A N (n • S.card)) :
    HomogeneousLocalization.Away.mk (DSMap.PGr A N) (tPS_mem S) n
        (∏ j, (MvPolynomial.X j : MvPolynomial (Fin (N + 1)) A) ^ (w j)) h
      = (∏ j : Fin (N + 1), chartFracPS (A := A) (N := N) S l₀ hl₀ (ULift.up j) ^ (w j)) *
        (∏ m : {m // m ∈ S}, chartFracPS (A := A) (N := N) S m.1 m.2 l₀) ^ n := by
  have hvalRHS : ((∏ j : Fin (N + 1),
          chartFracPS (A := A) (N := N) S l₀ hl₀ (ULift.up j) ^ (w j)) *
        (∏ m : {m // m ∈ S}, chartFracPS (A := A) (N := N) S m.1 m.2 l₀) ^ n).val
      = (∏ j : Fin (N + 1),
          ((chartFracPS (A := A) (N := N) S l₀ hl₀ (ULift.up j)).val) ^ (w j)) *
        (∏ m : {m // m ∈ S}, (chartFracPS (A := A) (N := N) S m.1 m.2 l₀).val) ^ n := by
    rw [← HomogeneousLocalization.algebraMap_apply (𝒜 := DSMap.PGr A N)
      (x := Submonoid.powers (tPS (A := A) (N := N) S))]
    simp only [map_mul, map_pow, map_prod, HomogeneousLocalization.algebraMap_apply]
    rfl
  have hunit : IsUnit (algebraMap (MvPolynomial (Fin (N + 1)) A)
      (Localization.Away (tPS (A := A) (N := N) S)) ((tPS (A := A) (N := N) S) ^ n)) := by
    rw [map_pow]
    exact (IsLocalization.Away.algebraMap_isUnit (tPS (A := A) (N := N) S)).pow n
  apply HomogeneousLocalization.val_injective (Submonoid.powers (tPS (A := A) (N := N) S))
  rw [HomogeneousLocalization.Away.val_mk, hvalRHS, Localization.mk_eq_mk']
  refine IsUnit.mul_right_cancel hunit ?_
  rw [IsLocalization.mk'_spec, map_pow, mul_assoc, ← mul_pow,
    prod_val_mul_tPS (A := A) (N := N) S l₀ hl₀, ← pow_mul, Nat.mul_comm S.card n, ← hw]
  exact (prod_pow_val_chartFracPS (A := A) (N := N) S l₀ hl₀ w).symm

/-- The value of `Away.mk` on a monomial times a constant. -/
theorem Away_mk_mon (S : Finset (Idx N)) (l₀ : Idx N) (hl₀ : l₀ ∈ S)
    (n : ℕ) (w : Fin (N + 1) →₀ ℕ) (c : A) (hw : w.degree = n * S.card)
    (h : (MvPolynomial.C c * ∏ j, (MvPolynomial.X j : MvPolynomial (Fin (N + 1)) A) ^ (w j))
        ∈ DSMap.PGr A N (n • S.card)) :
    HomogeneousLocalization.Away.mk (DSMap.PGr A N) (tPS_mem S) n
        (MvPolynomial.C c * ∏ j, (MvPolynomial.X j : MvPolynomial (Fin (N + 1)) A) ^ (w j)) h
      = AtoAwayS (A := A) (N := N) S c *
        (∏ j : Fin (N + 1), chartFracPS (A := A) (N := N) S l₀ hl₀ (ULift.up j) ^ (w j)) *
        (∏ m : {m // m ∈ S}, chartFracPS (A := A) (N := N) S m.1 m.2 l₀) ^ n := by
  rw [Away_mk_C_mul (S := S) (n := n) (c := c)
      (p := ∏ j, (MvPolynomial.X j : MvPolynomial (Fin (N + 1)) A) ^ (w j))
      (mem_PGr_prod_X (A := A) (N := N) S n w hw) (mem_PGr_C (A := A) (N := N) S c) h]
  rw [Away_mk_C (S := S) c (mem_PGr_C (A := A) (N := N) S c)]
  rw [Away_mk_prod_X (S := S) (l₀ := l₀) (hl₀ := hl₀) (n := n) (w := w) hw
      (mem_PGr_prod_X (A := A) (N := N) S n w hw)]
  ring

end Gen

/-- **Generation of the chart ring, graded level (insurance copy).** `Away (PGr A N) (tPS S)` is
generated over `A` (via `Work.DSSEC.AtoAwayS S`) by the chart coordinates
`chartFracPS S l hl k = x_k/x_l` for `l` in `S`.

Same statement as `Work.DSSEC.awayGenPS` in `Submission/Work/DSSEC/awayGenPS.lean`, in turn the
content of `awayGenPS_aux` inside `Submission/Work/DSSEC/adjoin_xiSecS_eq_top.lean`, requested at
a second path as insurance since it is the single missing link of `adjoin_xiSecS_eq_top` (all its
other ingredients are proved in that file: `preimage_DPS`, `DPS_affine`, `appLE_surjective`,
`awayToSection_surjective`, `eval₂_xiSecS_eq`, `eval₂_pspace_eq`, `chartFracPS_eq`,
`tPS_eq_mul`).

Proof route.  Put `f = tPS S` and pick `l₀ ∈ S`, `g = ∏ m ∈ S.erase l₀, x m`, so that
`f = x l₀ * g`.  Every element of `Away 𝒜 f` is `p / f^n` with `p` homogeneous of degree `n|S|`
(`HomogeneousLocalization.Away.mk_surjective`); expand `p` into monomials `monomial d c`, and for
`d.degree = n|S|` one has
`(∏ j, x_j ^ (d j)) / f ^ n = c * ∏ j, (x_j / x l₀) ^ (d j) * ∏ m ∈ S, (x l₀ / x m) ^ n`
because `∏ m ∈ S, (x l₀ / x m) ^ n = (x l₀) ^ (n|S|) / f ^ n` and
`∏ j, (x_j / x l₀) ^ (d j) = (∏ j, x_j ^ (d j)) / (x l₀) ^ (n|S|)`.  Each factor is one of the
generators `chartFracPS S l hl k = x_k/x_l` (`Work.DSSEC.chartFracPS_eq`).  Formally this is an
identity in `Localization.Away f` (`Localization.mk_mul`, `Localization.mk_eq_mk_iff`) with the
cofactor `1`, transported along the injective `HomogeneousLocalization.val`.

Alternative route: `Away 𝒜 f` is the localization of `Away 𝒜 (x l₀)` at
`t = g / (x l₀) ^ (|S| - 1)` (`HomogeneousLocalization.Away.isLocalization_mul`), the chart ring
`Away 𝒜 (x l₀)` is generated by the `x_j / x l₀` (`Work.DSG2.Phi_surjective`), and the inverse of
`t` is the product of the `x l₀ / x m` for `m` in `S`, again a `chartFracPS`. -/
theorem awayGenPSAlt {A : Type u} [CommRing A] {N : ℕ} (S : Finset (Work.DSSEC.Idx N))
    (hS : S.Nonempty) :
    Function.Surjective fun p : MvPolynomial ({l // l ∈ S} × Work.DSSEC.Idx N) A =>
      MvPolynomial.eval₂ (Work.DSSEC.AtoAwayS (A := A) (N := N) S)
        (fun q : {l // l ∈ S} × Work.DSSEC.Idx N =>
          Work.DSSEC.chartFracPS (A := A) S q.1.1 q.1.2 q.2) p := by
  obtain ⟨l₀, hl₀⟩ := hS
  let C : Subring (HomogeneousLocalization.Away (DSMap.PGr A N) (tPS (A := A) (N := N) S)) :=
    Subring.closure (Set.range (fun q : {l // l ∈ S} × Idx N =>
        chartFracPS (A := A) S q.1.1 q.1.2 q.2) ∪
      Set.range (AtoAwayS (A := A) (N := N) S))
  have hmem_gen : ∀ q : {l // l ∈ S} × Idx N,
      chartFracPS (A := A) S q.1.1 q.1.2 q.2 ∈ C :=
    fun q => Subring.subset_closure (Or.inl ⟨q, rfl⟩)
  have hmem_A : ∀ a : A, AtoAwayS (A := A) (N := N) S a ∈ C :=
    fun a => Subring.subset_closure (Or.inr ⟨a, rfl⟩)
  have hgen : ∀ y : HomogeneousLocalization.Away (DSMap.PGr A N) (tPS (A := A) (N := N) S),
      y ∈ C := by
    intro y
    obtain ⟨n, p, hp, hz⟩ :=
      HomogeneousLocalization.Away.mk_surjective (𝒜 := DSMap.PGr A N) (tPS_mem S) y
    rw [← hz]
    have hp' : p.IsHomogeneous (n • S.card) := by
      rw [MvPolynomial.mem_homogeneousSubmodule] at hp; exact hp
    have hdeg : ∀ w ∈ p.support, w.degree = n * S.card := fun w hw => by
      by_contra h
      refine (MvPolynomial.mem_support_iff.mp hw) (MvPolynomial.IsHomogeneous.coeff_eq_zero hp' ?_)
      rw [nsmul_nat_eq_mul]
      exact h
    have hG : ∀ w : Fin (N + 1) →₀ ℕ, MvPolynomial.C (p.coeff w) *
        ∏ j, (MvPolynomial.X j : MvPolynomial (Fin (N + 1)) A) ^ (w j)
          ∈ DSMap.PGr A N (n • S.card) := fun w => by
      by_cases hw : w ∈ p.support
      · have hmon : (MvPolynomial.C (p.coeff w) *
            ∏ j, (MvPolynomial.X j : MvPolynomial (Fin (N + 1)) A) ^ (w j))
            = MvPolynomial.monomial w (p.coeff w) := by
          rw [MvPolynomial.monomial_eq, ← Work.DSG2.prod_eq_finsupp_prod A N w]
        rw [hmon, MvPolynomial.mem_homogeneousSubmodule, nsmul_nat_eq_mul, ← hdeg w hw]
        exact MvPolynomial.isHomogeneous_monomial (p.coeff w) rfl
      · rw [show p.coeff w = 0 from by
          by_contra h
          exact hw (MvPolynomial.mem_support_iff.mpr h)]
        simp
    have hdecomp : p = ∑ w ∈ p.support, MvPolynomial.C (p.coeff w) *
        ∏ j, (MvPolynomial.X j : MvPolynomial (Fin (N + 1)) A) ^ (w j) := by
      conv_lhs => rw [MvPolynomial.as_sum p]
      apply Finset.sum_congr rfl
      intro w _
      rw [MvPolynomial.monomial_eq, ← Work.DSG2.prod_eq_finsupp_prod A N w]
    have hsummem : (∑ w ∈ p.support, MvPolynomial.C (p.coeff w) *
        ∏ j, (MvPolynomial.X j : MvPolynomial (Fin (N + 1)) A) ^ (w j))
        ∈ DSMap.PGr A N (n • S.card) := by
      rw [← hdecomp]; exact hp
    have hmem : ∀ w : Fin (N + 1) →₀ ℕ,
        HomogeneousLocalization.Away.mk (DSMap.PGr A N) (tPS_mem S) n
          (MvPolynomial.C (p.coeff w) *
            ∏ j, (MvPolynomial.X j : MvPolynomial (Fin (N + 1)) A) ^ (w j)) (hG w) ∈ C := by
      intro w
      by_cases hw : w ∈ p.support
      · rw [Away_mk_mon (A := A) (N := N) S l₀ hl₀ n w (p.coeff w) (hdeg w hw) (hG w)]
        refine Subring.mul_mem C (Subring.mul_mem C ?_ ?_) ?_
        · exact hmem_A (p.coeff w)
        · exact Subring.prod_mem C
            (fun j _ => Subring.pow_mem C (hmem_gen (⟨l₀, hl₀⟩, ULift.up j)) (w j))
        · exact Subring.pow_mem C
            (Subring.prod_mem C (fun m _ => hmem_gen (m, l₀))) n
      · have hc : p.coeff w = 0 := by
          by_contra h; exact hw (MvPolynomial.mem_support_iff.mpr h)
        have hnum : MvPolynomial.C (p.coeff w) *
            ∏ j, (MvPolynomial.X j : MvPolynomial (Fin (N + 1)) A) ^ (w j) = 0 := by
          rw [hc]; simp
        rw [Away_mk_congr (tPS_mem S) n hnum (hG w) (zero_mem _)]
        rw [Away_mk_zero (A := A) (N := N) S n (zero_mem _)]
        exact Subring.zero_mem C
    rw [Away_mk_congr (tPS_mem S) n hdecomp hp hsummem]
    rw [Away_mk_sum (tPS_mem S) n p.support
      (fun w => MvPolynomial.C (p.coeff w) *
        ∏ j, (MvPolynomial.X j : MvPolynomial (Fin (N + 1)) A) ^ (w j)) hG hsummem]
    exact Subring.sum_mem C (fun w _ => hmem w)
  intro y
  change ∃ r, MvPolynomial.eval₂Hom (AtoAwayS (A := A) (N := N) S)
      (fun q : {l // l ∈ S} × Idx N => chartFracPS (A := A) S q.1.1 q.1.2 q.2) r = y
  refine Subring.closure_induction (p := fun y _ => ∃ r, MvPolynomial.eval₂Hom
      (AtoAwayS (A := A) (N := N) S)
      (fun q : {l // l ∈ S} × Idx N => chartFracPS (A := A) S q.1.1 q.1.2 q.2) r = y)
    ?_ ?_ ?_ ?_ ?_ ?_ (hgen y)
  · rintro x (hx | hx)
    · obtain ⟨q, rfl⟩ := hx
      exact ⟨MvPolynomial.X (⟨q.1, ULift.up q.2.down⟩ : {l // l ∈ S} × Idx N),
        MvPolynomial.eval₂Hom_X' _ _ _⟩
    · obtain ⟨a, rfl⟩ := hx
      exact ⟨MvPolynomial.C a, MvPolynomial.eval₂Hom_C _ _ a⟩
  · exact ⟨0, map_zero _⟩
  · exact ⟨1, map_one _⟩
  · rintro x y _ _ ⟨q1, h1⟩ ⟨q2, h2⟩
    exact ⟨q1 + q2, by rw [map_add, h1, h2]⟩
  · rintro x _ ⟨q, h⟩
    exact ⟨-q, by rw [map_neg, h]⟩
  · rintro x y _ _ ⟨q1, h1⟩ ⟨q2, h2⟩
    exact ⟨q1 * q2, by rw [map_mul, h1, h2]⟩

end Work.DSSEC
