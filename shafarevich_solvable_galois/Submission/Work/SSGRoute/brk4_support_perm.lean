import Mathlib
import Submission.Work.SSGRoute.free_lie_four_defs
-- PORT435-BEGIN (v4.35 isDefEq respectTransparency compat)
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- PORT435-END

namespace Work.SSGRoute

/-! ## Support of the degree-`4` left-nested commutator: the permutation form

We expand `brk4 X t` (`= ⁅⁅⁅t₁,t₂⁆,t₃⁆,t₄⁆`, with `⁅a,b⁆ = a*b + b*a` over `𝔽₂`) into the eight
monomials

`t₁t₂t₃t₄, t₂t₁t₃t₄, t₃t₁t₂t₄, t₃t₂t₁t₄, t₄t₁t₂t₃, t₄t₂t₁t₃, t₄t₃t₁t₂, t₄t₃t₂t₁`,

and observe that each of these monomial words is a *permutation* of the four letters of `t`.  Since
the coefficient of `w` in a single monomial vanishes unless the index word *is* `w`, the coefficient
of `w` can only be nonzero when `w.toList` is such a permutation. -/

/-- Expansion of the degree-`4` left-nested commutator `⁅⁅⁅t₁,t₂⁆,t₃⁆,t₄⁆` (`brk4`) into the
eight monomials obtained by distributing the products. -/
private lemma brk4_expand_perm {X : Type} (t : X × X × X × X) :
    brk4 X t =
      MonoidAlgebra.single (FreeMonoid.of t.1 * FreeMonoid.of t.2.1 * FreeMonoid.of t.2.2.1 * FreeMonoid.of t.2.2.2) (1 : ZMod 2)
    + MonoidAlgebra.single (FreeMonoid.of t.2.1 * FreeMonoid.of t.1 * FreeMonoid.of t.2.2.1 * FreeMonoid.of t.2.2.2) 1
    + MonoidAlgebra.single (FreeMonoid.of t.2.2.1 * FreeMonoid.of t.1 * FreeMonoid.of t.2.1 * FreeMonoid.of t.2.2.2) 1
    + MonoidAlgebra.single (FreeMonoid.of t.2.2.1 * FreeMonoid.of t.2.1 * FreeMonoid.of t.1 * FreeMonoid.of t.2.2.2) 1
    + MonoidAlgebra.single (FreeMonoid.of t.2.2.2 * FreeMonoid.of t.1 * FreeMonoid.of t.2.1 * FreeMonoid.of t.2.2.1) 1
    + MonoidAlgebra.single (FreeMonoid.of t.2.2.2 * FreeMonoid.of t.2.1 * FreeMonoid.of t.1 * FreeMonoid.of t.2.2.1) 1
    + MonoidAlgebra.single (FreeMonoid.of t.2.2.2 * FreeMonoid.of t.2.2.1 * FreeMonoid.of t.1 * FreeMonoid.of t.2.1) 1
    + MonoidAlgebra.single (FreeMonoid.of t.2.2.2 * FreeMonoid.of t.2.2.1 * FreeMonoid.of t.2.1 * FreeMonoid.of t.1) 1 := by
  simp only [brk4, brk, MonoidAlgebra.single_mul_single, mul_one, add_mul, mul_add]
  noncomm_ring

/-- The letter list of a product of four one-letter words. -/
private lemma toList_of4 {X : Type} (a b c d : X) :
    (FreeMonoid.of a * FreeMonoid.of b * FreeMonoid.of c * FreeMonoid.of d).toList
      = [a, b, c, d] := by
  simp [FreeMonoid.toList_mul]

/-- The coefficient of a word `w` in a single monomial `single u r` vanishes as soon as `u.toList`
is a permutation of a list `L` and `w.toList` is not. -/
private lemma coeff_single_eq_zero_of_not_perm {X : Type} {L : List X} (u : FreeMonoid X)
    {w : FreeMonoid X} (hu : u.toList.Perm L) (h : ¬ w.toList.Perm L) (r : ZMod 2) :
    (MonoidAlgebra.single u r).coeff w = 0 := by
  rw [MonoidAlgebra.coeff_single]
  exact Finsupp.single_eq_of_ne (fun hwu => h (by rw [hwu]; exact hu))

/-- **The support of `brk4 t` consists of permutations of `t`'s letters.**

If the list of letters of a word `w` is not a permutation of the list `[t.1, t.2.1, t.2.2.1,
t.2.2.2]`, then the coefficient of `w` in the degree-`4` left-nested commutator `brk4 X t` is zero.

This is the sharp form of `brk4_support`: `brk4_expand` (present in
`Submission/Work/SSGRoute/coeffW_selfWord_eq_zero.lean`, but that file imports the target, so it
should be re-derived here or from `free_lie_four_defs`) exhibits `brk4 X t` as the sum of the eight
monomials `t₁t₂t₃t₄, t₂t₁t₃t₄, t₃t₁t₂t₄, t₃t₂t₁t₄, t₄t₁t₂t₃, t₄t₂t₁t₃, t₄t₃t₁t₂, t₄t₃t₂t₁`,
each of which is a permutation of the four letters. -/
theorem brk4_support_perm {X : Type} (t : X × X × X × X) (w : FreeMonoid X)
    (h : ¬ w.toList.Perm [t.1, t.2.1, t.2.2.1, t.2.2.2]) :
    (brk4 X t).coeff w = 0 := by
  -- the eight arrangements of the four letters are permutations of `[t.1, t.2.1, t.2.2.1, t.2.2.2]`
  have p2 : ([t.2.1, t.1, t.2.2.1, t.2.2.2] : List X).Perm [t.1, t.2.1, t.2.2.1, t.2.2.2] :=
    List.Perm.swap t.1 t.2.1 [t.2.2.1, t.2.2.2]
  have p3 : ([t.2.2.1, t.1, t.2.1, t.2.2.2] : List X).Perm [t.1, t.2.1, t.2.2.1, t.2.2.2] :=
    (List.Perm.swap t.1 t.2.2.1 [t.2.1, t.2.2.2]).trans
      (List.Perm.cons t.1 (List.Perm.swap t.2.1 t.2.2.1 [t.2.2.2]))
  have p4 : ([t.2.2.1, t.2.1, t.1, t.2.2.2] : List X).Perm [t.1, t.2.1, t.2.2.1, t.2.2.2] :=
    ((List.Perm.cons t.2.2.1 (List.Perm.swap t.1 t.2.1 [t.2.2.2])).trans
      (List.Perm.swap t.1 t.2.2.1 [t.2.1, t.2.2.2])).trans
      (List.Perm.cons t.1 (List.Perm.swap t.2.1 t.2.2.1 [t.2.2.2]))
  have e1 : (FreeMonoid.of t.1 * FreeMonoid.of t.2.1 * FreeMonoid.of t.2.2.1 * FreeMonoid.of t.2.2.2).toList.Perm
      [t.1, t.2.1, t.2.2.1, t.2.2.2] := by
    simpa only [toList_of4] using (List.Perm.refl ([t.1, t.2.1, t.2.2.1, t.2.2.2] : List X))
  have e2 : (FreeMonoid.of t.2.1 * FreeMonoid.of t.1 * FreeMonoid.of t.2.2.1 * FreeMonoid.of t.2.2.2).toList.Perm
      [t.1, t.2.1, t.2.2.1, t.2.2.2] := by
    simpa only [toList_of4] using p2
  have e3 : (FreeMonoid.of t.2.2.1 * FreeMonoid.of t.1 * FreeMonoid.of t.2.1 * FreeMonoid.of t.2.2.2).toList.Perm
      [t.1, t.2.1, t.2.2.1, t.2.2.2] := by
    simpa only [toList_of4] using p3
  have e4 : (FreeMonoid.of t.2.2.1 * FreeMonoid.of t.2.1 * FreeMonoid.of t.1 * FreeMonoid.of t.2.2.2).toList.Perm
      [t.1, t.2.1, t.2.2.1, t.2.2.2] := by
    simpa only [toList_of4] using p4
  have e5 : (FreeMonoid.of t.2.2.2 * FreeMonoid.of t.1 * FreeMonoid.of t.2.1 * FreeMonoid.of t.2.2.1).toList.Perm
      [t.1, t.2.1, t.2.2.1, t.2.2.2] := by
    simpa only [toList_of4] using
      ((List.Perm.swap t.1 t.2.2.2 [t.2.1, t.2.2.1]).trans
        (List.Perm.cons t.1 (List.Perm.swap t.2.1 t.2.2.2 [t.2.2.1]))).trans
        (List.Perm.cons t.1 (List.Perm.cons t.2.1 (List.Perm.swap t.2.2.1 t.2.2.2 [])))
  have e6 : (FreeMonoid.of t.2.2.2 * FreeMonoid.of t.2.1 * FreeMonoid.of t.1 * FreeMonoid.of t.2.2.1).toList.Perm
      [t.1, t.2.1, t.2.2.1, t.2.2.2] := by
    simpa only [toList_of4] using
      (((List.Perm.swap t.2.1 t.2.2.2 [t.1, t.2.2.1]).trans
        (List.Perm.cons t.2.1 (List.Perm.swap t.1 t.2.2.2 [t.2.2.1]))).trans
        (List.Perm.cons t.2.1 (List.Perm.cons t.1 (List.Perm.swap t.2.2.1 t.2.2.2 [])))).trans p2
  have e7 : (FreeMonoid.of t.2.2.2 * FreeMonoid.of t.2.2.1 * FreeMonoid.of t.1 * FreeMonoid.of t.2.1).toList.Perm
      [t.1, t.2.1, t.2.2.1, t.2.2.2] := by
    simpa only [toList_of4] using
      ((List.Perm.swap t.2.2.1 t.2.2.2 [t.1, t.2.1]).trans
        (List.Perm.cons t.2.2.1 (List.Perm.swap t.1 t.2.2.2 [t.2.1]))).trans
        ((List.Perm.cons t.2.2.1 (List.Perm.cons t.1 (List.Perm.swap t.2.1 t.2.2.2 []))).trans p3)
  have e8 : (FreeMonoid.of t.2.2.2 * FreeMonoid.of t.2.2.1 * FreeMonoid.of t.2.1 * FreeMonoid.of t.1).toList.Perm
      [t.1, t.2.1, t.2.2.1, t.2.2.2] := by
    simpa only [toList_of4] using
      ((List.Perm.swap t.2.2.1 t.2.2.2 [t.2.1, t.1]).trans
        (List.Perm.cons t.2.2.1 (List.Perm.swap t.2.1 t.2.2.2 [t.1]))).trans
        ((List.Perm.cons t.2.2.1 (List.Perm.cons t.2.1 (List.Perm.swap t.1 t.2.2.2 []))).trans p4)
  rw [brk4_expand_perm t]
  simp only [MonoidAlgebra.coeff_add, Finsupp.add_apply]
  rw [coeff_single_eq_zero_of_not_perm _ e1 h 1, coeff_single_eq_zero_of_not_perm _ e2 h 1,
      coeff_single_eq_zero_of_not_perm _ e3 h 1, coeff_single_eq_zero_of_not_perm _ e4 h 1,
      coeff_single_eq_zero_of_not_perm _ e5 h 1, coeff_single_eq_zero_of_not_perm _ e6 h 1,
      coeff_single_eq_zero_of_not_perm _ e7 h 1, coeff_single_eq_zero_of_not_perm _ e8 h 1]
  simp

end Work.SSGRoute
