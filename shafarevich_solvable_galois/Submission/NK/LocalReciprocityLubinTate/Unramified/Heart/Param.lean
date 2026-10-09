import Mathlib
import Submission.NK.LocalReciprocityLubinTate.Basic
import Submission.NK.LocalReciprocityLubinTate.LubinTate.Integers
import Submission.NK.LocalReciprocityLubinTate.LubinTate.isFrobeniusPower_integers
import Submission.NK.LocalReciprocityLubinTate.Unramified.NormOp
import Submission.NK.LocalReciprocityLubinTate.Unramified.LTGain
import Submission.NK.LocalReciprocityLubinTate.Unramified.GainAux
import Submission.NK.LocalReciprocityLubinTate.Unramified.gainPoly_sCoeff
-- PORT435-BEGIN (v4.35 isDefEq respectTransparency compat)
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- PORT435-END

/-!
# The two-parameter norm operator `Res_X(f(X) - Y, v(X) + s·t(X))`

This file sets up the *`s`-parametrised* norm operator of the Lubin–Tate gain lemma, but for an
arbitrary second argument `v + s·t` instead of `1 + s·t`:

`paramNormOp P q v t = Res_X(f(X) - Y, v(X) + s·t(X)) ∈ (A[s])[Y]`,  `f = LTpoly P q`.

The `s`-variable is `Polynomial.X : Polynomial A` and the resultant is computed in
`(A[s][Y])[X]`; the output is a polynomial in `Y` whose coefficients are polynomials in `s`.

## Main definitions and results

* `paramPoly` — `v + s·t ∈ (A[s])[X]`;
* `paramF`, `paramH` — the two arguments of the resultant in `(A[s][Y])[X]`;
* `paramNormOp` — the resultant `Res_X(f(X) - Y, v(X) + s·t(X)) ∈ (A[s])[Y]`;
* `map_paramNormOp` — base change along a ring hom `A[s] →+* R`;
* `paramPoly_map_map_evalRingHom` — substituting `s = x` in `v + s·t`;
* `map_paramNormOp_evalRingHom` — substituting `s = x` in `paramNormOp` gives
  `normOp f (v + C x · t)`;
* `map_paramNormOp_evalRingHom_zero` — `paramNormOp` at `s = 0` is `normOp f v`.
-/

open Polynomial

namespace NK.LocalReciprocityLubinTate.Unramified.Heart

universe u v

noncomputable section

variable {A : Type u} [CommRing A]

/-- `v + s·t ∈ (A[s])[X]`, the second argument of the `s`-parametrised norm operator. -/
noncomputable def paramPoly (v t : Polynomial A) : Polynomial (Polynomial A) :=
  v.map Polynomial.C + Polynomial.C (Polynomial.X : Polynomial A) * t.map Polynomial.C

/-- `v + s·t` viewed in `(A[s][Y])[X]` (all coefficients constants). -/
noncomputable def paramH (v t : Polynomial A) : Polynomial (Polynomial (Polynomial A)) :=
  (paramPoly v t).map Polynomial.C

/-- `f(X) - Y ∈ (A[s][Y])[X]`, where `f = LTpoly P q`: the first argument of the resultant
defining `paramNormOp`. -/
noncomputable def paramF (P : A) (q : ℕ) : Polynomial (Polynomial (Polynomial A)) :=
  (((NK.LocalReciprocityLubinTate.LTpoly P q).map Polynomial.C).map Polynomial.C)
    - Polynomial.C (Polynomial.X : Polynomial (Polynomial A))

/-- **The `s`-parametrised norm operator**

`paramNormOp P q v t = Res_X(f(X) - Y, v(X) + s·t(X)) ∈ (A[s])[Y]`, where `f = LTpoly P q`. -/
noncomputable def paramNormOp (P : A) (q : ℕ) (v t : Polynomial A) : Polynomial (Polynomial A) :=
  Polynomial.resultant (paramF P q) (paramH v t) q (paramPoly v t).natDegree

/-- **Base change of the `s`-parametrised norm operator.**  For a ring hom `ψ : A[s] →+* R`, the
image of `paramNormOp P q v t` is the resultant of the base-changed factors. -/
theorem map_paramNormOp {R : Type v} [CommRing R] (P : A) (q : ℕ) (v t : Polynomial A)
    (ψ : Polynomial A →+* R) :
    Polynomial.map ψ (paramNormOp P q v t)
      = Polynomial.resultant
          ((((NK.LocalReciprocityLubinTate.LTpoly P q).map Polynomial.C).map ψ).map Polynomial.C
            - Polynomial.C (Polynomial.X : Polynomial R))
          (((paramPoly v t).map ψ).map Polynomial.C)
          q (paramPoly v t).natDegree := by
  have hX : (Polynomial.mapRingHom ψ) (Polynomial.X : Polynomial (Polynomial A)) = Polynomial.X :=
    Polynomial.map_X ψ
  have h1 : Polynomial.map ψ (paramNormOp P q v t)
      = Polynomial.resultant (Polynomial.map (Polynomial.mapRingHom ψ) (paramF P q))
          (Polynomial.map (Polynomial.mapRingHom ψ) (paramH v t)) q (paramPoly v t).natDegree := by
    rw [show Polynomial.map ψ (paramNormOp P q v t)
        = (Polynomial.mapRingHom ψ) (paramNormOp P q v t) from rfl]
    rw [paramNormOp]
    exact (Polynomial.resultant_map_map (paramF P q) (paramH v t) q (paramPoly v t).natDegree
      (Polynomial.mapRingHom ψ)).symm
  rw [h1]
  have hF : Polynomial.map (Polynomial.mapRingHom ψ) (paramF P q)
      = (((NK.LocalReciprocityLubinTate.LTpoly P q).map Polynomial.C).map ψ).map Polynomial.C
        - Polynomial.C (Polynomial.X : Polynomial R) := by
    rw [paramF, Polynomial.map_sub, Polynomial.map_C, hX]
    congr 1
    rw [Polynomial.map_map, Polynomial.map_map, Polynomial.map_map, Polynomial.map_map,
      Polynomial.mapRingHom_comp_C]
  have hH : Polynomial.map (Polynomial.mapRingHom ψ) (paramH v t)
      = ((paramPoly v t).map ψ).map Polynomial.C := by
    rw [paramH, Polynomial.map_map, Polynomial.map_map, Polynomial.mapRingHom_comp_C]
  rw [hF, hH]

/-- Substituting `s = x` in `v + s·t` gives `v + C x · t`. -/
theorem paramPoly_map_map_evalRingHom (v t : Polynomial A) (x : A) :
    (paramPoly v t).map (Polynomial.evalRingHom x) = v + Polynomial.C x * t := by
  have hX : (Polynomial.evalRingHom x) (Polynomial.X : Polynomial A) = x := by
    rw [Polynomial.coe_evalRingHom, Polynomial.eval_X]
  have hcomp : (Polynomial.evalRingHom x).comp (Polynomial.C : A →+* Polynomial A)
      = RingHom.id A := by
    ext a
    rw [RingHom.comp_apply, Polynomial.coe_evalRingHom, Polynomial.eval_C]
    rfl
  rw [paramPoly, Polynomial.map_add, Polynomial.map_mul, Polynomial.map_C, hX,
    Polynomial.map_map, hcomp, Polynomial.map_id,
    Polynomial.map_map, hcomp, Polynomial.map_id]

/-- Substituting `s = x` in `f = LTpoly P q` changes nothing (all coefficients are constants). -/
theorem LTpoly_map_map_evalRingHom' (P : A) (q : ℕ) (x : A) :
    ((NK.LocalReciprocityLubinTate.LTpoly P q).map Polynomial.C).map
        (Polynomial.evalRingHom x) = NK.LocalReciprocityLubinTate.LTpoly P q := by
  have hcomp : (Polynomial.evalRingHom x).comp (Polynomial.C : A →+* Polynomial A) = RingHom.id A := by
    ext a
    rw [RingHom.comp_apply, Polynomial.coe_evalRingHom, Polynomial.eval_C]
    rfl
  rw [Polynomial.map_map, hcomp, Polynomial.map_id]

/-- **Substituting `s = x` in the `s`-parametrised norm operator.**  For `f = LTpoly P q` monic of
degree `q`, the value of `paramNormOp P q v t` at `s = x` is the norm operator of `v + C x · t`:
`Res_X(f(X) - Y, v(X) + x·t(X)) = 𝒩(v + C x · t)`. -/
theorem map_paramNormOp_evalRingHom [IsDomain A] (P : A) (q : ℕ) (x : A) (v t : Polynomial A)
    (hq0 : 0 < q) (hf : (NK.LocalReciprocityLubinTate.LTpoly P q).Monic)
    (hdeg : (NK.LocalReciprocityLubinTate.LTpoly P q).natDegree = q) :
    Polynomial.map (Polynomial.evalRingHom x) (paramNormOp P q v t)
      = NK.LocalReciprocityLubinTate.Unramified.normOp
          (NK.LocalReciprocityLubinTate.LTpoly P q) (v + Polynomial.C x * t) := by
  rw [map_paramNormOp, LTpoly_map_map_evalRingHom', paramPoly_map_map_evalRingHom]
  rw [NK.LocalReciprocityLubinTate.Unramified.normOp_def]
  have hfa : ((NK.LocalReciprocityLubinTate.LTpoly P q).map Polynomial.C
      - Polynomial.C (Polynomial.X : Polynomial A) : Polynomial (Polynomial A)).natDegree = q := by
    rw [NK.LocalReciprocityLubinTate.Unramified.natDegree_map_C_sub_C_X _
      hf (by rw [hdeg]; exact hq0)]
    exact hdeg
  rw [hfa]
  have hle : ((v + Polynomial.C x * t).map Polynomial.C :
      Polynomial (Polynomial A)).natDegree ≤ (paramPoly v t).natDegree := by
    rw [NK.LocalReciprocityLubinTate.Unramified.natDegree_map_C]
    rw [← paramPoly_map_map_evalRingHom v t x]
    exact Polynomial.natDegree_map_le
  rw [show (paramPoly v t).natDegree
      = ((v + Polynomial.C x * t).map Polynomial.C : Polynomial (Polynomial A)).natDegree
        + ((paramPoly v t).natDegree
          - ((v + Polynomial.C x * t).map Polynomial.C : Polynomial (Polynomial A)).natDegree)
      from (Nat.add_sub_cancel' hle).symm]
  rw [Polynomial.resultant_add_right_deg _ _ _ _ _ (le_refl _)]
  have hcoeffLT : (NK.LocalReciprocityLubinTate.LTpoly P q).coeff q = 1 := by
    have := hf.coeff_natDegree
    rwa [hdeg] at this
  have hcq : ((NK.LocalReciprocityLubinTate.LTpoly P q).map Polynomial.C
      - Polynomial.C (Polynomial.X : Polynomial A) :
        Polynomial (Polynomial A)).coeff q = 1 := by
    rw [Polynomial.coeff_sub, Polynomial.coeff_map, Polynomial.coeff_C, hcoeffLT, map_one]
    rw [if_neg (by omega : q ≠ 0), sub_zero]
  rw [hcq, one_pow, one_mul]

/-- **The constant term of the `s`-parametrised norm operator.**  Substituting `s = 0` gives the
norm operator of `v`: `paramNormOp P q v t` at `s = 0` is `𝒩 v`. -/
theorem map_paramNormOp_evalRingHom_zero [IsDomain A] (P : A) (q : ℕ) (v t : Polynomial A)
    (hq0 : 0 < q) (hf : (NK.LocalReciprocityLubinTate.LTpoly P q).Monic)
    (hdeg : (NK.LocalReciprocityLubinTate.LTpoly P q).natDegree = q) :
    Polynomial.map (Polynomial.evalRingHom 0) (paramNormOp P q v t)
      = NK.LocalReciprocityLubinTate.Unramified.normOp
          (NK.LocalReciprocityLubinTate.LTpoly P q) v := by
  rw [map_paramNormOp_evalRingHom P q 0 v t hq0 hf hdeg, Polynomial.C_0, zero_mul, add_zero]

end

end NK.LocalReciprocityLubinTate.Unramified.Heart
