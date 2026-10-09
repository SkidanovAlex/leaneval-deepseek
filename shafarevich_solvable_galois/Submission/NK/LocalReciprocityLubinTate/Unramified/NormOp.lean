import Mathlib
-- PORT435-BEGIN (v4.35 isDefEq respectTransparency compat)
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- PORT435-END

/-!
# The norm operator `R_f(h)(Y) = Res_X(f(X) - Y, h(X))`

For a commutative ring `A` and polynomials `f, h ∈ A[X]`, this file introduces the *norm operator*

`normOp f h := Res_X(f(X) - Y, h(X)) ∈ A[Y]`,

the `X`-resultant of `f(X) - Y` and `h(X)`, computed in the polynomial ring `(A[Y])[X]`.

In the application `f = πX + X^q` is the standard Lubin–Tate series and `h` a polynomial: the
roots `α` of `f(X) - Y` satisfy `(normOp f h)(Y) = ∏_{f(α)=Y} h(α)`, so that `normOp f` is the
norm operator of the level-one Lubin–Tate extension, transported to a polynomial identity over the
coefficient ring.  This is the operator `R` of the elementary proof of Honda's norm computation
(see `Submission/Work/LocalReciprocityLubinTate/Unramified/`).

## Main definitions and results

* `NK.LocalReciprocityLubinTate.Unramified.normOp`;
* `normOp_eval` — `(normOp f h).eval c = Res(f - C c, h)`;
* `normOp_eval_zero` — `(normOp f h).eval 0 = Res(f, h)`.
-/

namespace NK.LocalReciprocityLubinTate.Unramified

open Polynomial

universe u

variable {A : Type u} [CommRing A]

/-- The **norm operator** associated with `f ∈ A[X]`:

`normOp f h = Res_X(f(X) - Y, h(X)) ∈ A[Y]`,

where the resultant is taken in the polynomial ring `(A[Y])[X]` whose variable is `X` and whose
coefficient variable is `Y`. -/
noncomputable def normOp (f h : Polynomial A) : Polynomial A :=
  Polynomial.resultant (f.map Polynomial.C - Polynomial.C (Polynomial.X : Polynomial A))
    (Polynomial.map Polynomial.C h)

theorem normOp_def (f h : Polynomial A) :
    normOp f h = Polynomial.resultant
      (f.map Polynomial.C - Polynomial.C (Polynomial.X : Polynomial A))
      (Polynomial.map Polynomial.C h) := rfl

/-- The degree of `f(X) - Y` in `(A[Y])[X]`, for `f` monic of positive degree and `A` nontrivial. -/
theorem natDegree_map_C_sub_C_X {A : Type u} [CommRing A] [IsDomain A]
    (f : Polynomial A) (hf : f.Monic) (hd : 0 < f.natDegree) :
    (f.map Polynomial.C - Polynomial.C (Polynomial.X : Polynomial A)).natDegree = f.natDegree := by
  have h1 : (Polynomial.map Polynomial.C f).natDegree = f.natDegree := by
    rw [Polynomial.natDegree_map_eq_of_injective]
    exact Polynomial.C_injective
  have hlt : (Polynomial.C (Polynomial.X : Polynomial A) :
      Polynomial (Polynomial A)).natDegree < (Polynomial.map Polynomial.C f).natDegree := by
    rw [Polynomial.natDegree_C, h1]
    exact_mod_cast hd
  rw [Polynomial.natDegree_sub_eq_left_of_natDegree_lt hlt, h1]

theorem natDegree_map_C {A : Type u} [CommRing A] [IsDomain A]
    (h : Polynomial A) :
    (Polynomial.map Polynomial.C h : Polynomial (Polynomial A)).natDegree = h.natDegree := by
  rw [Polynomial.natDegree_map_eq_of_injective]
  exact Polynomial.C_injective

/-- **The norm operator evaluated at a point** is a resultant: for `f` monic of positive degree,
`(normOp f h)(c) = Res(f(X) - c, h(X))`. -/
theorem normOp_eval {A : Type u} [CommRing A] [IsDomain A]
    (f h : Polynomial A) (hf : f.Monic) (hd : 0 < f.natDegree) (c : A) :
    (normOp f h).eval c = (f - Polynomial.C c).resultant h := by
  have h1 := natDegree_map_C_sub_C_X f hf hd
  have h2 := natDegree_map_C (A := A) h
  have hkey : (normOp f h).eval c
      = (Polynomial.map (Polynomial.evalRingHom c)
            (f.map Polynomial.C - Polynomial.C (Polynomial.X : Polynomial A))).resultant
          (Polynomial.map (Polynomial.evalRingHom c) (Polynomial.map Polynomial.C h))
          (f.map Polynomial.C - Polynomial.C (Polynomial.X : Polynomial A)).natDegree
          (Polynomial.map Polynomial.C h).natDegree := by
    rw [normOp]
    exact (Polynomial.resultant_map_map
      (f.map Polynomial.C - Polynomial.C (Polynomial.X : Polynomial A))
      (Polynomial.map Polynomial.C h) _ _ (Polynomial.evalRingHom c)).symm
  have hcomp : (Polynomial.evalRingHom c).comp (Polynomial.C : A →+* Polynomial A)
      = RingHom.id A := by
    ext a; simp
  have hcX : Polynomial.map (Polynomial.evalRingHom c)
      (Polynomial.C (Polynomial.X : Polynomial A)) = Polynomial.C c := by
    rw [Polynomial.map_C]
    congr 1
    simp
  have hmap1 : Polynomial.map (Polynomial.evalRingHom c)
      (f.map Polynomial.C) = f := by
    rw [Polynomial.map_map, hcomp, Polynomial.map_id]
  have hmap2 : Polynomial.map (Polynomial.evalRingHom c)
      (Polynomial.map Polynomial.C h) = h := by
    rw [Polynomial.map_map, hcomp, Polynomial.map_id]
  have hm1 : Polynomial.map (Polynomial.evalRingHom c)
      (f.map Polynomial.C - Polynomial.C (Polynomial.X : Polynomial A)) = f - Polynomial.C c := by
    rw [Polynomial.map_sub, hmap1, hcX]
  have hd' : (f - Polynomial.C c).natDegree = f.natDegree := Polynomial.natDegree_sub_C
  rw [hkey, h1, h2, hm1, hmap2, hd']

/-- **The norm operator evaluated at `0`** is the resultant: `(normOp f h)(0) = Res(f,h)` for `f`
monic of positive degree. -/
theorem normOp_eval_zero {A : Type u} [CommRing A] [IsDomain A]
    (f h : Polynomial A) (hf : f.Monic) (hd : 0 < f.natDegree) :
    (normOp f h).eval 0 = f.resultant h := by
  have := normOp_eval f h hf hd 0
  rwa [Polynomial.C_0, sub_zero] at this

end NK.LocalReciprocityLubinTate.Unramified
