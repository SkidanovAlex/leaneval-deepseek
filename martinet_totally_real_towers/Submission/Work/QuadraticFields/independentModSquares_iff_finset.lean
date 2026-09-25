import Mathlib
import Submission.Work.QuadraticFields.RankTwo

/-!
# Independence modulo squares, tested on finite subsets

Let `A` be a commutative group and `a : ι → A` a finite family.  The family is
*independent modulo squares* (`IndependentModSquares a`) if the classes
`sqClass (a i)` of the `a i` in `A ⧸ A²` are linearly independent over `𝔽₂`.
The point of this file is the elementary reformulation

  `a` is independent modulo squares
    ↔ no nonempty finite sub-product `∏ i ∈ T, a i` is a square.

Because the only scalars are `0` and `1`, a linear relation over `𝔽₂` between
the classes is precisely a sub-product that is a square; this is the criterion
used in the quadratic-field chapter to turn a square-class computation into a
counting statement about independent quadratic extensions.

## Main results

* `Work.QuadraticFields.sqClass_eq_zero_iff`: the class of `a` vanishes in
  `A ⧸ A²` exactly when `a` lies in `squareSubgroup A`, i.e. is a product of
  squares (`A` commutative, so the squares already form a subgroup).
* `Work.QuadraticFields.independentModSquares_iff_finset`: the criterion above.
-/

namespace Work.QuadraticFields

set_option autoImplicit false

universe u w

section Basic

variable {A : Type u} [CommGroup A]

/-- The class map to `A ⧸ A²` is additive on products. -/
private lemma sqClass_mul (a b : A) : sqClass (a * b) = sqClass a + sqClass b := by
  simp only [sqClass, ModN.mkQ]
  rw [show Additive.ofMul (a * b) = Additive.ofMul a + Additive.ofMul b from by simp, map_add]

private lemma sqClass_one : sqClass (1 : A) = 0 := by
  simp only [sqClass, ModN.mkQ]
  rw [show Additive.ofMul (1 : A) = 0 from by simp, map_zero]

private lemma sqClass_inv (a : A) : sqClass a⁻¹ = -sqClass a := by
  simp only [sqClass, ModN.mkQ]
  rw [show Additive.ofMul a⁻¹ = -Additive.ofMul a from by simp, map_neg]

/-- A square has trivial class modulo squares. -/
private lemma sqClass_sq (a : A) : sqClass (a ^ 2) = 0 := by
  change (Submodule.Quotient.mk (Additive.ofMul (a ^ 2)) : ModN (Additive A) 2) = 0
  rw [Submodule.Quotient.mk_eq_zero, LinearMap.mem_range]
  refine ⟨Additive.ofMul a, ?_⟩
  rw [LinearMap.lsmul_apply, Nat.cast_smul_eq_nsmul ℤ 2 (Additive.ofMul a), two_nsmul, sq]
  rfl

/-- An element of a commutative group has trivial class in `A ⧸ A²` if and only if it is a
product of squares.  (Since `A` is commutative the squares already form a subgroup, so this is
the same as being a square.) -/
private lemma sqClass_eq_zero_iff (a : A) : sqClass a = 0 ↔ a ∈ squareSubgroup A := by
  refine ⟨fun h => ?_, fun ha => ?_⟩
  · -- `sqClass a = 0` means `a ∈ range (fun y => 2 • y)`, so `a` is a square.
    change (Submodule.Quotient.mk (Additive.ofMul a) : ModN (Additive A) 2) = 0 at h
    rw [Submodule.Quotient.mk_eq_zero, LinearMap.mem_range] at h
    obtain ⟨y, hy⟩ := h
    obtain ⟨b, rfl⟩ := Additive.ofMul.surjective y
    rw [LinearMap.lsmul_apply, Nat.cast_smul_eq_nsmul ℤ 2 (Additive.ofMul b), two_nsmul] at hy
    have hb : b * b = a := Additive.ofMul.injective hy
    rw [← hb]
    exact Subgroup.subset_closure ⟨b, by simp [pow_two]⟩
  · -- a product of squares has trivial class, by induction over the closure
    refine Subgroup.closure_induction (k := Set.range fun x : A => x ^ 2)
      (p := fun x _ => sqClass x = 0) ?_ ?_ ?_ ?_ ha
    · rintro x ⟨y, rfl⟩
      exact sqClass_sq y
    · exact sqClass_one
    · intro x y _ _ hx hy
      rw [sqClass_mul, hx, hy, add_zero]
    · intro x _ hx
      rw [sqClass_inv, hx, neg_zero]

private lemma zmod_two_eq_zero_or_one (x : ZMod 2) : x = 0 ∨ x = 1 := by
  have h : x.val = 0 ∨ x.val = 1 := by have := ZMod.val_lt x; omega
  rcases h with h | h
  · left; rw [← ZMod.natCast_zmod_val x, h]; norm_num
  · right; rw [← ZMod.natCast_zmod_val x, h]; norm_num

/-- The class of a finite product is the sum of the classes. -/
private lemma sqClass_prod {ι : Type w} [DecidableEq ι] (a : ι → A) (T : Finset ι) :
    sqClass (∏ i ∈ T, a i) = ∑ i ∈ T, sqClass (a i) := by
  classical
  induction T using Finset.induction_on with
  | empty => simp [sqClass_one]
  | insert i T hi ih => rw [Finset.prod_insert hi, Finset.sum_insert hi, sqClass_mul, ih]

/-- In an `𝔽₂`-module the only scalars are `0` and `1`, so a sum with `{0,1}`-coefficients
indexed by `T` is the plain sum over `T`. -/
private lemma sum_indicator_smul_eq {ι : Type w} [Fintype ι] [DecidableEq ι] {M : Type*}
    [AddCommMonoid M] [Module (ZMod 2) M] (v : ι → M) (T : Finset ι) :
    (∑ i, (if i ∈ T then (1 : ZMod 2) else 0) • v i) = ∑ i ∈ T, v i := by
  classical
  have h : (∑ i ∈ T, (if i ∈ T then (1 : ZMod 2) else 0) • v i)
      = ∑ i, (if i ∈ T then (1 : ZMod 2) else 0) • v i :=
    Finset.sum_subset (Finset.subset_univ T) (fun x _ hx => by simp [hx])
  rw [← h]
  exact Finset.sum_congr rfl fun i hi => by simp [hi]

end Basic

/-- **Independence modulo squares, detected on finite subsets.**  A finite family `a` of elements
of a commutative group is independent modulo squares (its classes in `A ⧸ A²` are linearly
independent over `𝔽₂`) if and only if no nonempty finite sub-product of the family is a product
of squares. -/
theorem independentModSquares_iff_finset {A : Type*} [CommGroup A] {ι : Type*} [Fintype ι]
    [DecidableEq ι] (a : ι → A) :
    IndependentModSquares a ↔
      ∀ T : Finset ι, T.Nonempty → (∏ i ∈ T, a i) ∉ squareSubgroup A := by
  classical
  constructor
  · intro hlin T hT hmem
    -- the sub-product over `T` is a square, so it gives a nontrivial `𝔽₂`-relation
    rw [IndependentModSquares] at hlin
    have hzero : (∑ i, (if i ∈ T then (1 : ZMod 2) else 0) • sqClass (a i)) = 0 := by
      rw [sum_indicator_smul_eq (fun i => sqClass (a i)) T, ← sqClass_prod a T]
      exact (sqClass_eq_zero_iff _).mpr hmem
    have hcoeff := (Fintype.linearIndependent_iff.mp hlin)
      (fun i => if i ∈ T then (1 : ZMod 2) else 0) hzero
    obtain ⟨i, hi⟩ := hT
    exact one_ne_zero (show (1 : ZMod 2) = 0 by simpa [hi] using hcoeff i)
  · intro hT
    -- a relation over `𝔽₂` is a sub-product over the support which is a square
    rw [IndependentModSquares, Fintype.linearIndependent_iff]
    intro g hg i
    by_contra hgi
    set T : Finset ι := Finset.univ.filter (fun j => g j ≠ 0) with hTdef
    have hiT : i ∈ T := by simp [hTdef, hgi]
    have hpoint : ∀ j, g j • sqClass (a j)
        = (if j ∈ T then (1 : ZMod 2) else 0) • sqClass (a j) := by
      intro j
      by_cases hj : j ∈ T
      · have hgne : g j ≠ 0 := by simpa [hTdef] using hj
        have hg1 : g j = 1 := (zmod_two_eq_zero_or_one (g j)).resolve_left hgne
        simp [hj, hg1]
      · have hg0 : g j = 0 := by
          by_contra h
          exact hj (by simpa [hTdef] using h)
        simp [hj, hg0]
    have hzero : (∑ j ∈ T, sqClass (a j)) = 0 := by
      have h1 : (∑ j ∈ T, sqClass (a j))
          = ∑ j, (if j ∈ T then (1 : ZMod 2) else 0) • sqClass (a j) :=
        (sum_indicator_smul_eq (fun j => sqClass (a j)) T).symm
      have h2 : (∑ j, (if j ∈ T then (1 : ZMod 2) else 0) • sqClass (a j))
          = ∑ j, g j • sqClass (a j) :=
        Finset.sum_congr rfl (fun j _ => (hpoint j).symm)
      rw [h1, h2, hg]
    rw [← sqClass_prod a T] at hzero
    exact hT T ⟨i, hiT⟩ ((sqClass_eq_zero_iff _).mp hzero)

end Work.QuadraticFields
