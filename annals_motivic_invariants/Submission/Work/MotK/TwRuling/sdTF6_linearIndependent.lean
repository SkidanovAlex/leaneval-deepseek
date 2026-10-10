import Mathlib
import Submission.Work.MotK.TwRuling.TwFivetenDefs
import Submission.Work.MotK.TwRuling.sdTF5_linearIndependent

set_option linter.unusedVariables false -- v435-speed

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

open WeierstrassCurve WeierstrassCurve.Affine

namespace Work.MotK.TwRuling

/-!
# Independence of the 30 monomials `1, x, …, x¹⁵, y, xy, …, x¹³y`

For any Weierstrass curve `E` over a field `R`, the `(Fin 16 ⊕ Fin 14)`-indexed family

`sdTF6 E : i ↦ x^i` (`i : Fin 16`), `j ↦ x^j * y` (`j : Fin 14`)

in `R(E) = FunctionField E` is `R`-linearly independent.  These are precisely the monomials
`x^i y^j` with `j ≤ 1` and `2i + 3j ≤ 30`, i.e. the 30 monomials of the Riemann–Roch space
`L(30·O)` when `E` is smooth; the argument below, however, needs no smoothness.

The argument is the degree-30 case of the one used in `sdTF5_linearIndependent` (and in
`TwRuling/MonomialIndep.lean`).  Work in the affine coordinate ring
`A = CoordinateRing E = R[X,Y]/(W_E)`, which is a domain for every Weierstrass curve over a field,
and which is *free over `R[X]` with basis `{1, Y}`* (`CoordinateRing.basis`).  Writing
`xA := mk (C X)`, `yA := mk X`, the key rewriting facts are

* `(X^m) • (1 : A) = xA^m`            (`A`-action of `R[X]`, `CoordinateRing.smul`),
* `(X^m) • yA = yA * xA^m`,

and `CoordinateRing.smul_basis_eq_zero` (linear independence of `1, yA` over `R[X]`).

The 30 monomials split into the two families `u k = xA^k` (`k < 16`) and `v j = yA * xA^j`
(`j < 14`), whose `R`-independence over `Fin 16 ⊕ Fin 14` follows from `smul_basis_eq_zero` and the
independence of the monomials `X^n` in `R[X]` (`Polynomial.basisMonomials`).  The injective
`R`-algebra map `A → R(E)` (a fraction ring) carries it to the function field.
-/

theorem sdTF6_linearIndependent (R : Type) [Field R] (E : WeierstrassCurve R) :
    LinearIndependent R (Work.MotK.TwRuling.sdTF6 E) := by
  -- Rewriting facts for the `R[X]`-action on the coordinate ring.
  have hxA : ∀ m : ℕ, ((Polynomial.X : Polynomial R) ^ m) • (1 : CoordinateRing E)
      = (CoordinateRing.mk E (Polynomial.C Polynomial.X)) ^ m := by
    intro m
    rw [CoordinateRing.smul, mul_one, Polynomial.C_pow, map_pow]
  have hyA : ∀ m : ℕ, ((Polynomial.X : Polynomial R) ^ m) • (CoordinateRing.mk E Polynomial.X)
      = (CoordinateRing.mk E Polynomial.X) * (CoordinateRing.mk E (Polynomial.C Polynomial.X)) ^ m := by
    intro m
    rw [CoordinateRing.smul, Polynomial.C_pow, map_pow, mul_comm]
  -- Independence of the monomials `X^n` in `R[X]`.
  have hXall : LinearIndependent R (fun n : ℕ => (Polynomial.X : Polynomial R) ^ n) := by
    have h := (Polynomial.basisMonomials R).linearIndependent
    rw [Polynomial.coe_basisMonomials] at h
    simpa only [Polynomial.monomial_one_right_eq_X_pow] using h
  have hX16 : LinearIndependent R (fun k : Fin 16 => (Polynomial.X : Polynomial R) ^ (k : ℕ)) :=
    hXall.comp _ (fun a b h => Fin.ext h)
  have hX14 : LinearIndependent R (fun j : Fin 14 => (Polynomial.X : Polynomial R) ^ (j : ℕ)) :=
    hXall.comp _ (fun a b h => Fin.ext h)
  -- Independence of the two families `u k = xA^k`, `v j = yA * xA^j` in the coordinate ring.
  have hLI : LinearIndependent R (Sum.elim
      (fun k : Fin 16 => (CoordinateRing.mk E (Polynomial.C Polynomial.X)) ^ (k : ℕ))
      (fun j : Fin 14 => (CoordinateRing.mk E Polynomial.X) *
        (CoordinateRing.mk E (Polynomial.C Polynomial.X)) ^ (j : ℕ))) := by
    rw [Fintype.linearIndependent_iff]
    intro c hc
    have hP : (∑ k : Fin 16, c (Sum.inl k) • ((Polynomial.X : Polynomial R) ^ (k:ℕ))) • (1 : CoordinateRing E)
        = ∑ k : Fin 16, c (Sum.inl k) • (CoordinateRing.mk E (Polynomial.C Polynomial.X) ^ (k:ℕ)) := by
      rw [Finset.sum_smul]
      refine Finset.sum_congr rfl ?_
      intro k _
      rw [smul_assoc, hxA k]
    have hQ : (∑ j : Fin 14, c (Sum.inr j) • ((Polynomial.X : Polynomial R) ^ (j:ℕ))) • (CoordinateRing.mk E Polynomial.X)
        = ∑ j : Fin 14, c (Sum.inr j) • ((CoordinateRing.mk E Polynomial.X) * (CoordinateRing.mk E (Polynomial.C Polynomial.X) ^ (j:ℕ))) := by
      rw [Finset.sum_smul]
      refine Finset.sum_congr rfl ?_
      intro j _
      rw [smul_assoc, hyA j]
    have h1 : (∑ k : Fin 16, c (Sum.inl k) • ((Polynomial.X : Polynomial R) ^ (k:ℕ))) • (1 : CoordinateRing E)
        + (∑ j : Fin 14, c (Sum.inr j) • ((Polynomial.X : Polynomial R) ^ (j:ℕ))) • (CoordinateRing.mk E Polynomial.X) = 0 := by
      rw [hP, hQ, ← hc, Fintype.sum_sum_type]
      simp only [Sum.elim_inl, Sum.elim_inr]
    obtain ⟨hP0, hQ0⟩ := CoordinateRing.smul_basis_eq_zero h1
    intro i
    cases i with
    | inl k => exact (Fintype.linearIndependent_iff.mp hX16) (fun k => c (Sum.inl k)) hP0 k
    | inr j => exact (Fintype.linearIndependent_iff.mp hX14) (fun j => c (Sum.inr j)) hQ0 j
  -- Transport along the injective `R`-algebra map `A → R(E)`; `A` is a domain and `R(E)` its
  -- fraction field.
  have hker : (IsScalarTower.toAlgHom R (CoordinateRing E) (FunctionField E)).toLinearMap.ker = ⊥ := by
    rw [LinearMap.ker_eq_bot]
    intro a b hab
    exact IsFractionRing.injective (CoordinateRing E) (FunctionField E) (by simpa using hab)
  have hF : LinearIndependent R ((IsScalarTower.toAlgHom R (CoordinateRing E) (FunctionField E)).toLinearMap ∘
      (Sum.elim
      (fun k : Fin 16 => (CoordinateRing.mk E (Polynomial.C Polynomial.X)) ^ (k : ℕ))
      (fun j : Fin 14 => (CoordinateRing.mk E Polynomial.X) *
        (CoordinateRing.mk E (Polynomial.C Polynomial.X)) ^ (j : ℕ)))) := hLI.map' _ hker
  have hlast : ((IsScalarTower.toAlgHom R (CoordinateRing E) (FunctionField E)).toLinearMap ∘
      (Sum.elim
      (fun k : Fin 16 => (CoordinateRing.mk E (Polynomial.C Polynomial.X)) ^ (k : ℕ))
      (fun j : Fin 14 => (CoordinateRing.mk E Polynomial.X) *
        (CoordinateRing.mk E (Polynomial.C Polynomial.X)) ^ (j : ℕ))))
      = Work.MotK.TwRuling.sdTF6 E := by
    funext i
    cases i with
    | inl k => simp [Work.MotV.genX]
    | inr j =>
      rw [Function.comp_apply, Sum.elim_inr, Work.MotK.TwRuling.sdTF6_inr]
      show (algebraMap (CoordinateRing E) (Affine.FunctionField E))
          ((CoordinateRing.mk E) Polynomial.X *
            (CoordinateRing.mk E) (Polynomial.C Polynomial.X) ^ (j : ℕ))
        = (algebraMap (CoordinateRing E) (Affine.FunctionField E))
              ((CoordinateRing.mk E) (Polynomial.C Polynomial.X)) ^ (j : ℕ)
          * (algebraMap (CoordinateRing E) (Affine.FunctionField E))
              ((CoordinateRing.mk E) Polynomial.X)
      rw [map_mul, map_pow, mul_comm]
  rw [hlast] at hF
  exact hF

end Work.MotK.TwRuling
