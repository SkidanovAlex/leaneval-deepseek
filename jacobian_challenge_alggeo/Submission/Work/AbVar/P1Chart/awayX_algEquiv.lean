import Mathlib
import Submission.Work.AbVar.P1Chart.Basic

-- Lean v4.35.0-rc3 / Mathlib 5e0c4e5 made `isDefEq` respect transparency when unifying instances; with it,
-- `ZMod.instField` and `ZMod.commRing` (and `Neg (ZMod p)` via `SubtractionMonoid`) no longer unify, which
-- breaks `ring`/`rw`/module-instance search on `ZMod p`. Restore the v4.34 behaviour for this file.
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false


/-!
# The chart ring of `P¹` at a standard affine chart is a polynomial ring

For the standard grading of `k[X₀,X₁]` by total degree, the degree-zero part
`AX k i = Away (gr k) (X i)` of the localisation at the powers of `Xᵢ` is a polynomial ring
in one variable over the degree-zero part `gr k 0` (the constants).  The generator is
`X_j/X_i` for `j ≠ i`.

We prove this by exhibiting the `gr k 0`-algebra map
`polyToAway i : (↥(gr k 0))[T] →ₐ[↥(gr k 0)] AX k i` sending `T` to `X_j/X_i` (`j = other i`).

* It is injective because it is a section of the dehomogenisation
  `awayToPoly i : AX k i →+* (↥(gr k 0))[T]` (`X_j/X_i ↦ T`), see
  `awayToPoly_polyToAway`.
* It is surjective because the generators of `AX k i` over `↥(gr k 0)` produced by
  `HomogeneousLocalization.Away.adjoin_mk_prod_pow_eq_top` are all powers of `X_j/X_i`.
-/

set_option autoImplicit false

noncomputable section

open HomogeneousLocalization MvPolynomial

namespace Work.AbVar.P1Chart

variable {k : Type*} [Field k]

/-! ### Basic computations in `Away (gr k) (X i)` -/

/-- The element `x / Xᵢⁿ` of `Away (gr k) (X i)` for `x : A` homogeneous of degree `n`. -/
abbrev awmk (i : Fin 2) (n : ℕ) (x : MvPolynomial (Fin 2) k) (hx : x ∈ gr k n) :
    Away (gr k) (MvPolynomial.X i) :=
  Away.mk (gr k) (X_mem k i) n x (by simpa using hx)

/-- Graded membership of a power. -/
lemma mem_gr_pow {x : MvPolynomial (Fin 2) k} (hx : x ∈ gr k 1) (n : ℕ) :
    x^n ∈ gr k n := by
  simpa using SetLike.pow_mem_graded n hx

lemma away_mk_add (i : Fin 2) (n : ℕ) (x y : MvPolynomial (Fin 2) k)
    (hx : x ∈ gr k n) (hy : y ∈ gr k n) :
    awmk i n x hx + awmk i n y hy = awmk i n (x + y) (add_mem hx hy) := by
  apply HomogeneousLocalization.val_injective
    (Submonoid.powers (MvPolynomial.X i : MvPolynomial (Fin 2) k))
  rw [val_add, Away.val_mk, Away.val_mk, Away.val_mk]
  exact Localization.add_mk_self _ _ _

lemma away_mk_mul (i : Fin 2) (n m : ℕ) (x y : MvPolynomial (Fin 2) k)
    (hx : x ∈ gr k n) (hy : y ∈ gr k m) :
    awmk i n x hx * awmk i m y hy = awmk i (n + m) (x * y) (SetLike.mul_mem_graded hx hy) := by
  apply HomogeneousLocalization.val_injective
    (Submonoid.powers (MvPolynomial.X i : MvPolynomial (Fin 2) k))
  rw [HomogeneousLocalization.val_mul, Away.val_mk, Away.val_mk, Away.val_mk]
  rw [Localization.mk_mul, Localization.mk_eq_mk']
  apply IsLocalization.mk'_eq_of_eq
  rw [Submonoid.coe_mul, ← pow_add]

lemma away_mk_zero (i : Fin 2) (a : MvPolynomial (Fin 2) k) (ha : a ∈ gr k 0) :
    awmk i 0 a ha = algebraMap ↥(gr k 0) (Away (gr k) (MvPolynomial.X i)) ⟨a, ha⟩ := by
  apply HomogeneousLocalization.val_injective
    (Submonoid.powers (MvPolynomial.X i : MvPolynomial (Fin 2) k))
  rw [Away.val_mk]
  change Localization.mk a ⟨(MvPolynomial.X i)^0, _⟩ =
    Localization.mk a (1 : Submonoid.powers (MvPolynomial.X i : MvPolynomial (Fin 2) k))
  exact congrArg (Localization.mk a) (Subtype.ext (pow_zero _))

lemma away_mk_pow (i : Fin 2) (n : ℕ) (x : MvPolynomial (Fin 2) k) (hx : x ∈ gr k 1) :
    (awmk i 1 x hx)^n = awmk i n (x^n) (mem_gr_pow hx n) := by
  induction n with
  | zero =>
      rw [pow_zero]
      symm
      apply HomogeneousLocalization.val_injective
        (Submonoid.powers (MvPolynomial.X i : MvPolynomial (Fin 2) k))
      rw [Away.val_mk, HomogeneousLocalization.val_one, pow_zero]
      exact (congrArg (Localization.mk (1 : MvPolynomial (Fin 2) k)) (Subtype.ext (pow_zero _))).trans
        ((Localization.mk_one_eq_algebraMap (M := Submonoid.powers (MvPolynomial.X i)) 1).trans (map_one _))
  | succ n ih =>
      rw [pow_succ, ih, away_mk_mul i n 1 (x^n) x (mem_gr_pow hx n) hx]
      apply HomogeneousLocalization.val_injective
        (Submonoid.powers (MvPolynomial.X i : MvPolynomial (Fin 2) k))
      rw [Away.val_mk, Away.val_mk, show x^n * x = x^(n+1) from (pow_succ x n).symm]

/-- Multiplying numerator and denominator of `x / Xᵢⁿ` by `Xᵢᵐ` does not change the element. -/
lemma away_mk_frac (i : Fin 2) (n m : ℕ) (a : MvPolynomial (Fin 2) k) (ha : a ∈ gr k n) :
    awmk i (m + n) ((MvPolynomial.X i)^m * a)
        (SetLike.mul_mem_graded (mem_gr_pow (X_mem k i) m) ha) = awmk i n a ha := by
  apply HomogeneousLocalization.val_injective
    (Submonoid.powers (MvPolynomial.X i : MvPolynomial (Fin 2) k))
  rw [Away.val_mk, Away.val_mk, Localization.mk_eq_mk']
  apply IsLocalization.mk'_eq_of_eq
  change (MvPolynomial.X i)^(m + n) * a = (MvPolynomial.X i)^n * ((MvPolynomial.X i)^m * a)
  rw [← mul_assoc, ← pow_add, Nat.add_comm]

/-! ### The degree-zero part of `gr k` as constants -/

lemma gr_zero_eq_C {p : MvPolynomial (Fin 2) k} (hp : p ∈ gr k 0) :
    p = MvPolynomial.C (p.coeff 0) := by
  rw [← MvPolynomial.totalDegree_eq_zero_iff_eq_C]
  exact (MvPolynomial.totalDegree_zero_iff_isHomogeneous (Fin 2)).mpr hp

lemma C_mem_gr_zero (r : k) : (MvPolynomial.C r : MvPolynomial (Fin 2) k) ∈ gr k 0 :=
  (MvPolynomial.mem_homogeneousSubmodule 0 _).mpr (MvPolynomial.isHomogeneous_C (Fin 2) r)

/-- The identification of `k` with the degree zero part of the standard grading. -/
noncomputable def constToZero : k →+* ↥(gr k 0) where
  toFun r := ⟨MvPolynomial.C r, C_mem_gr_zero r⟩
  map_one' := Subtype.ext (by simp)
  map_mul' a b := Subtype.ext (by simp)
  map_zero' := Subtype.ext (by simp)
  map_add' a b := Subtype.ext (by simp)

@[simp]
lemma constToZero_apply (r : k) : (constToZero r : MvPolynomial (Fin 2) k) = MvPolynomial.C r :=
  rfl

lemma constToZero_surj (a : ↥(gr k 0)) : constToZero (a.1.coeff 0) = a := by
  refine Subtype.ext ?_
  rw [constToZero_apply]
  exact (gr_zero_eq_C a.2).symm

/-! ### The dehomogenisation `Away (gr k) (X i) → (↥(gr k 0))[T]` -/

/-- The coefficients `k → (↥(gr k 0))[T]` of the chart coordinates. -/
noncomputable def constToPoly : k →+* Polynomial ↥(gr k 0) :=
  (Polynomial.C : ↥(gr k 0) →+* Polynomial ↥(gr k 0)).comp (constToZero (k := k))

lemma constToPoly_apply (r : k) : constToPoly (k := k) r = Polynomial.C (constToZero r) := rfl

/-- The substitution `k[X₀,X₁] → (↥(gr k 0))[T]` sending `X_i ↦ 1` and `X_l ↦ T` for `l ≠ i`. -/
noncomputable def subst (i : Fin 2) :
    MvPolynomial (Fin 2) k →+* Polynomial ↥(gr k 0) :=
  MvPolynomial.eval₂Hom (S₁ := Polynomial ↥(gr k 0)) (constToPoly (k := k))
    (fun l : Fin 2 => if l = i then (1 : Polynomial ↥(gr k 0)) else Polynomial.X)

lemma subst_self (i : Fin 2) : subst i (MvPolynomial.X i : MvPolynomial (Fin 2) k) = 1 := by
  rw [subst, MvPolynomial.eval₂Hom_X']; simp

lemma subst_other {i l : Fin 2} (hil : l ≠ i) :
    subst i (MvPolynomial.X l : MvPolynomial (Fin 2) k) = Polynomial.X := by
  rw [subst, MvPolynomial.eval₂Hom_X']; simp [hil]

lemma subst_C (i : Fin 2) (r : k) :
    subst i (MvPolynomial.C r) = Polynomial.C (constToZero r) := by
  rw [subst, MvPolynomial.eval₂Hom_C, constToPoly_apply]

lemma subst_eq_C (i : Fin 2) (a : ↥(gr k 0)) :
    subst i (a : MvPolynomial (Fin 2) k) = Polynomial.C a := by
  rw [show (a : MvPolynomial (Fin 2) k) = MvPolynomial.C (a.1.coeff 0) from gr_zero_eq_C a.2]
  rw [subst_C, constToZero_surj a]

/-- `X_i ^ 1` as an element of `Submonoid.powers (X_i)`. -/
noncomputable def powOne (i : Fin 2) :
    Submonoid.powers (MvPolynomial.X i : MvPolynomial (Fin 2) k) :=
  ⟨(MvPolynomial.X i : MvPolynomial (Fin 2) k) ^ 1, ⟨1, rfl⟩⟩

@[simp]
lemma powOne_val (i : Fin 2) :
    (powOne (k := k) i : MvPolynomial (Fin 2) k) = (MvPolynomial.X i)^1 := rfl

/-- `X_i ∈ Submonoid.powers (X_i)` is a unit for the substitution map. -/
theorem substUnitProof (i : Fin 2) :
    ∀ y : Submonoid.powers (MvPolynomial.X i : MvPolynomial (Fin 2) k),
      IsUnit (subst i (y : MvPolynomial (Fin 2) k)) := by
  rintro ⟨y, n, rfl⟩
  rw [show subst i ((MvPolynomial.X i : MvPolynomial (Fin 2) k)^n) = 1 by
    rw [map_pow, subst_self, one_pow]]
  exact isUnit_one

/-- The localisation of the substitution map at `X_i`. -/
noncomputable def awayToPolyAux (i : Fin 2) :
    Localization (Submonoid.powers (MvPolynomial.X i : MvPolynomial (Fin 2) k)) →+*
      Polynomial ↥(gr k 0) :=
  IsLocalization.lift (M := Submonoid.powers (MvPolynomial.X i : MvPolynomial (Fin 2) k))
    (substUnitProof i)

lemma awayToPolyAux_apply_lift (i : Fin 2) (a : MvPolynomial (Fin 2) k) :
    awayToPolyAux i (algebraMap (MvPolynomial (Fin 2) k)
      (Localization (Submonoid.powers (MvPolynomial.X i : MvPolynomial (Fin 2) k))) a)
      = subst i a := by
  rw [awayToPolyAux]
  exact IsLocalization.lift_eq _ a

lemma awayToPolyAux_mk_mul (i : Fin 2) (x : MvPolynomial (Fin 2) k)
    (y : Submonoid.powers (MvPolynomial.X i : MvPolynomial (Fin 2) k)) :
    awayToPolyAux i (Localization.mk x y) * subst i (y : MvPolynomial (Fin 2) k) = subst i x := by
  rw [Localization.mk_eq_mk']
  have hspec := IsLocalization.mk'_spec
    (S := Localization (Submonoid.powers (MvPolynomial.X i : MvPolynomial (Fin 2) k))) x y
  have h2 := congrArg (awayToPolyAux i) hspec
  rwa [map_mul, awayToPolyAux_apply_lift, awayToPolyAux_apply_lift] at h2

/-- The dehomogenisation `Away (gr k) (X i) →+* (↥(gr k 0))[T]`, `X_j/X_i ↦ T`. -/
noncomputable def awayToPoly (i : Fin 2) :
    Away (gr k) (MvPolynomial.X i) →+* Polynomial ↥(gr k 0) :=
  (awayToPolyAux i).comp
    (algebraMap (Away (gr k) (MvPolynomial.X i))
      (Localization (Submonoid.powers (MvPolynomial.X i : MvPolynomial (Fin 2) k))))

/-- The `↥(gr k 0)`-algebra map `(↥(gr k 0))[T] → AX k i` sending `T` to `X_j/X_i`. -/
noncomputable def polyToAway (i : Fin 2) :
    Polynomial ↥(gr k 0) →ₐ[↥(gr k 0)] Away (gr k) (MvPolynomial.X i) :=
  Polynomial.aeval (awmk i 1 (MvPolynomial.X (other i)) (X_mem k (other i)))

lemma polyToAway_X (i : Fin 2) :
    polyToAway (k := k) i Polynomial.X =
      awmk i 1 (MvPolynomial.X (other i)) (X_mem k (other i)) :=
  Polynomial.aeval_X _

lemma polyToAway_C (i : Fin 2) (r : ↥(gr k 0)) :
    polyToAway (k := k) i (Polynomial.C r) =
      algebraMap ↥(gr k 0) (Away (gr k) (MvPolynomial.X i)) r :=
  Polynomial.aeval_C _ _

lemma awayU_val (i : Fin 2) :
    (awmk i 1 (MvPolynomial.X (other i)) (X_mem k (other i))).val
      = Localization.mk (MvPolynomial.X (other i) : MvPolynomial (Fin 2) k) (powOne (k := k) i) :=
  Away.val_mk _ _ _ _ _

lemma awayToPoly_awayU (i : Fin 2) :
    awayToPoly i (polyToAway (k := k) i Polynomial.X) = Polynomial.X := by
  rw [polyToAway_X]
  show awayToPolyAux i (algebraMap (Away (gr k) (MvPolynomial.X i))
    (Localization (Submonoid.powers (MvPolynomial.X i : MvPolynomial (Fin 2) k)))
    (awmk i 1 (MvPolynomial.X (other i)) (X_mem k (other i)))) = Polynomial.X
  rw [HomogeneousLocalization.algebraMap_apply, awayU_val]
  have h := awayToPolyAux_mk_mul i (MvPolynomial.X (other i) : MvPolynomial (Fin 2) k)
    (powOne (k := k) i)
  rw [powOne_val, map_pow, subst_self, one_pow, subst_other (other_ne i), mul_one] at h
  exact h

lemma awayToPoly_algMap (i : Fin 2) (a : ↥(gr k 0)) :
    awayToPoly i (algebraMap ↥(gr k 0) (Away (gr k) (MvPolynomial.X i)) a) = Polynomial.C a := by
  show awayToPolyAux i (algebraMap (Away (gr k) (MvPolynomial.X i))
    (Localization (Submonoid.powers (MvPolynomial.X i : MvPolynomial (Fin 2) k)))
    (algebraMap ↥(gr k 0) (Away (gr k) (MvPolynomial.X i)) a)) = _
  rw [HomogeneousLocalization.algebraMap_apply, HomogeneousLocalization.algebraMap_eq,
    show (HomogeneousLocalization.fromZeroRingHom (gr k)
      (Submonoid.powers (MvPolynomial.X i : MvPolynomial (Fin 2) k)) a).val
      = Localization.mk (a : MvPolynomial (Fin 2) k)
        (1 : Submonoid.powers (MvPolynomial.X i : MvPolynomial (Fin 2) k)) from rfl,
    Localization.mk_eq_mk']
  rw [IsLocalization.mk'_one, awayToPolyAux_apply_lift, subst_eq_C]

/-- The key computation: `polyToAway` followed by `awayToPoly` is the identity. -/
lemma awayToPoly_polyToAway (i : Fin 2) (p : Polynomial ↥(gr k 0)) :
    awayToPoly i (polyToAway i p) = p := by
  induction p using Polynomial.induction_on' with
  | monomial n r =>
    rw [← Polynomial.C_mul_X_pow_eq_monomial, map_mul, map_pow, map_mul, map_pow, polyToAway_C,
      awayToPoly_algMap, awayToPoly_awayU, Polynomial.C_mul_X_pow_eq_monomial]
  | add p q hp hq => rw [map_add, map_add, hp, hq]

lemma polyToAway_injective (i : Fin 2) : Function.Injective (polyToAway (k := k) i) := by
  intro p q h
  rw [← awayToPoly_polyToAway i p, ← awayToPoly_polyToAway i q, h]

/-! ### The `↥(gr k 0)`-algebra `gr k 0[X₀,X₁]` is generated by `X₀, X₁` -/

lemma adjoin_range_X_eq_top :
    Algebra.adjoin ↥(gr k 0)
      (Set.range (fun i : Fin 2 => (MvPolynomial.X i : MvPolynomial (Fin 2) k))) = ⊤ := by
  rw [eq_top_iff]
  have aux : ∀ p : MvPolynomial (Fin 2) k,
      p ∈ Algebra.adjoin ↥(gr k 0)
        (Set.range (fun i : Fin 2 => (MvPolynomial.X i : MvPolynomial (Fin 2) k))) := by
    intro p
    induction p using MvPolynomial.induction_on with
    | C r =>
        exact Subalgebra.algebraMap_mem
          (Algebra.adjoin ↥(gr k 0)
            (Set.range (fun i : Fin 2 => (MvPolynomial.X i : MvPolynomial (Fin 2) k))))
          ⟨MvPolynomial.C r, C_mem_gr_zero r⟩
    | add p q hp hq => exact add_mem hp hq
    | mul_X p n hp => exact mul_mem hp (Algebra.subset_adjoin (Set.mem_range_self n))
  exact fun p _ => aux p

/-! ### Index manipulations in `Fin 2` -/

lemma fin2_sum_eq (i : Fin 2) (d : Fin 2 → ℕ) :
    (∑ t : Fin 2, d t) = d i + d (other i) := by
  rw [Fin.sum_univ_two]
  fin_cases i <;> simp [other, Nat.add_comm]

lemma fin2_prod_eq (i : Fin 2) (d : Fin 2 → ℕ) :
    (∏ t : Fin 2, (MvPolynomial.X t : MvPolynomial (Fin 2) k) ^ d t) =
      (MvPolynomial.X i)^(d i) * (MvPolynomial.X (other i))^(d (other i)) := by
  rw [Fin.prod_univ_two]
  fin_cases i <;> simp [other, mul_comm]

/-! ### Surjectivity of `polyToAway` -/

lemma polyToAway_surjective (i : Fin 2) :
    Function.Surjective (polyToAway (k := k) i) := by
  rw [← AlgHom.range_eq_top]
  have hgen := Away.adjoin_mk_prod_pow_eq_top (𝒜 := gr k)
    (f := (MvPolynomial.X i : MvPolynomial (Fin 2) k)) (d := 1) (X_mem k i)
    (Fin 2) (fun t => MvPolynomial.X t) adjoin_range_X_eq_top (fun _ => 1) (fun t => X_mem k t)
  rw [eq_top_iff, ← hgen]
  apply Algebra.adjoin_le_iff.mpr
  rintro x ⟨a, d, hai, _hle, rfl⟩
  have hsum : a = d i + d (other i) := by
    have h1 : (∑ t : Fin 2, d t) = a := by simpa [Nat.mul_one] using hai
    rw [← h1, fin2_sum_eq]
  have hprod := fin2_prod_eq (k := k) i d
  refine ⟨Polynomial.X ^ (d (other i)), ?_⟩
  change polyToAway i (Polynomial.X ^ (d (other i))) = _
  rw [map_pow, polyToAway_X, away_mk_pow]
  apply HomogeneousLocalization.val_injective
    (Submonoid.powers (MvPolynomial.X i : MvPolynomial (Fin 2) k))
  rw [Away.val_mk, Away.val_mk]
  subst hsum
  rw [hprod, Localization.mk_eq_mk']
  apply IsLocalization.mk'_eq_of_eq
  rw [← mul_assoc, ← pow_add, Nat.add_comm]

theorem awayX_algEquiv (k : Type*) [Field k] (i : Fin 2) :
    Nonempty (Work.AbVar.P1Chart.AX k i ≃ₐ[↥(Work.AbVar.P1Chart.gr k 0)]
      Polynomial ↥(Work.AbVar.P1Chart.gr k 0)) :=
  ⟨(AlgEquiv.ofBijective (polyToAway (k := k) i)
    ⟨polyToAway_injective i, polyToAway_surjective i⟩).symm⟩

end Work.AbVar.P1Chart
