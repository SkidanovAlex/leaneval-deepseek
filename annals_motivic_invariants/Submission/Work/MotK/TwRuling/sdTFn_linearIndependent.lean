import Mathlib
import Submission.Work.MotK.TwRuling.KleinKerDefs
import Submission.Work.MotK.TwRuling.SdWNdeg
import Submission.Work.MotK.TwRuling.sdTF5_linearIndependent

set_option linter.unusedVariables false -- v435-speed

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

set_option maxHeartbeats 800000

open WeierstrassCurve WeierstrassCurve.Affine
open Polynomial

namespace Work.MotK.TwRuling

noncomputable section

/-!
# Independence of the `5n` monomials `x^i` (`i < 5n/2 + 1`) and `x^j y` (`j < (5n+1)/2 - 1`)

This generalises `sdTF5_linearIndependent` (`n = 5`, 25 monomials) and `linearIndependent_sdTen`
(`n = 2`, 10 monomials) to every `n`.

The argument is identical in shape.  Work in the affine coordinate ring
`A = CoordinateRing E = R[X,Y]/(W_E)`, which is a domain for every Weierstrass curve over a field,
and which is *free over `R[X]` with basis `{1, Y}`* (`CoordinateRing.basis`).  Writing
`xA := crX E`, `yA := crY E`, the key rewriting facts are

* `(X^m) • (1 : A) = xA^m`            (`CoordinateRing.smul`),
* `(X^m) • yA = yA * xA^m`,

and `CoordinateRing.smul_basis_eq_zero` (linear independence of `1, yA` over `R[X]`).

The `5n` monomials split into the two families `u i = xA^i` (`i < 5n/2 + 1`) and
`v j = yA * xA^j` (`j < (5n+1)/2 - 1`), whose `R`-independence follows from `smul_basis_eq_zero`
and the independence of the monomials `X^n` in `R[X]` (`Polynomial.basisMonomials`).  The injective
`R`-algebra map `A → R(E)` (a fraction ring) carries it to the function field.
-/

/-! ## §1 The general linear-independence lemmas in the coordinate ring

These are the `n`-independent versions of the lemmas proved for `Fin 6 ⊕ Fin 4` in
`SdWNdeg.lean`; the proofs are verbatim copies with `Fin 6 ↦ Fin a`, `Fin 4 ↦ Fin b`. -/

/-- The monomial classes `crX E ^ i` (`i < a`) are `R`-linearly independent in the coordinate
ring. -/
theorem li_crX_gen (R : Type) [Field R] (E : WeierstrassCurve R) (a : ℕ) :
    LinearIndependent R (fun i : Fin a => crX E ^ (i : ℕ)) := by
  have h := (li_X_pow (R := R) a).map' (smulOne E) (ker_smulOne E)
  convert h using 1
  · funext i
    exact crX_pow_eq E i

/-- The monomial classes `crX E ^ j * crY E` (`j < b`) are `R`-linearly independent in the
coordinate ring. -/
theorem li_crXY_gen (R : Type) [Field R] (E : WeierstrassCurve R) (b : ℕ) :
    LinearIndependent R (fun j : Fin b => crX E ^ (j : ℕ) * crY E) := by
  have h := (li_X_pow (R := R) b).map' (smulY E) (ker_smulY E)
  convert h using 1
  · funext j
    exact crX_pow_mul_crY_eq E j

/-- The two spans in the coordinate ring intersect trivially (from the freeness of
`CoordinateRing E` over `R[X]` with basis `{1, crY E}`). -/
theorem disjoint_cr_gen (R : Type) [Field R] (E : WeierstrassCurve R) (a b : ℕ) : Disjoint
    (Submodule.span R (Set.range (fun i : Fin a => crX E ^ (i : ℕ))))
    (Submodule.span R (Set.range (fun j : Fin b => crX E ^ (j : ℕ) * crY E))) := by
  rw [Submodule.disjoint_def]
  intro z hz1 hz2
  have e1 : Set.range (fun i : Fin a => crX E ^ (i : ℕ))
      = (smulOne E) '' (Set.range (fun i : Fin a => (Polynomial.X : R[X]) ^ (i : ℕ))) := by
    rw [← Set.range_comp]
    congr 1
    funext i
    exact crX_pow_eq E i
  have e2 : Set.range (fun j : Fin b => crX E ^ (j : ℕ) * crY E)
      = (smulY E) '' (Set.range (fun j : Fin b => (Polynomial.X : R[X]) ^ (j : ℕ))) := by
    rw [← Set.range_comp]
    congr 1
    funext j
    exact crX_pow_mul_crY_eq E j
  rw [e1, ← Submodule.map_span] at hz1
  rw [e2, ← Submodule.map_span] at hz2
  obtain ⟨P, hP, hPz⟩ := hz1
  obtain ⟨Q, hQ, hQz⟩ := hz2
  have hp : P • (1 : CoordinateRing E) = z := hPz
  have hq : (-Q) • crY E = -z := by
    rw [neg_smul]
    exact congrArg Neg.neg hQz
  have h : P • (1 : CoordinateRing E) + (-Q) • crY E = 0 := by rw [hp, hq, add_neg_cancel]
  obtain ⟨hP0, _⟩ := CoordinateRing.smul_basis_eq_zero h
  rw [← hp, hP0, zero_smul]

/-! ## §2 Transport to the function field -/

/-- The monomials `x ^ i` (`i < a`) are `R`-linearly independent in the function field. -/
theorem li_genX_gen (R : Type) [Field R] (E : WeierstrassCurve R) (a : ℕ) :
    LinearIndependent R (fun i : Fin a => (Work.MotV.genX E) ^ (i : ℕ)) := by
  have h := (li_crX_gen R E a).map' (algMapLin E) (ker_algMapLin E)
  convert h using 1
  · funext i
    exact (algMapLin_crX_pow E i).symm

/-- The monomials `x ^ j * y` (`j < b`) are `R`-linearly independent in the function field. -/
theorem li_genXY_gen (R : Type) [Field R] (E : WeierstrassCurve R) (b : ℕ) :
    LinearIndependent R (fun j : Fin b => (Work.MotV.genX E) ^ (j : ℕ) * Work.MotV.genY E) := by
  have h := (li_crXY_gen R E b).map' (algMapLin E) (ker_algMapLin E)
  convert h using 1
  · funext j
    exact (algMapLin_crX_pow_mul_crY E j).symm

/-- The two spans in the function field intersect trivially. -/
theorem disjoint_gen_gen (R : Type) [Field R] (E : WeierstrassCurve R) (a b : ℕ) : Disjoint
    (Submodule.span R (Set.range (fun i : Fin a => (Work.MotV.genX E) ^ (i : ℕ))))
    (Submodule.span R (Set.range (fun j : Fin b =>
      (Work.MotV.genX E) ^ (j : ℕ) * Work.MotV.genY E))) := by
  have hcr : ∀ x ∈ Submodule.span R (Set.range (fun i : Fin a => crX E ^ (i : ℕ))),
      x ∈ Submodule.span R (Set.range (fun j : Fin b => crX E ^ (j : ℕ) * crY E)) → x = 0 :=
    Submodule.disjoint_def.mp (disjoint_cr_gen R E a b)
  rw [Submodule.disjoint_def]
  intro z hz1 hz2
  have e1 : Set.range (fun i : Fin a => (Work.MotV.genX E) ^ (i : ℕ))
      = (algMapLin E) '' (Set.range (fun i : Fin a => crX E ^ (i : ℕ))) := by
    rw [← Set.range_comp]
    congr 1
    funext i
    exact (algMapLin_crX_pow E i).symm
  have e2 : Set.range (fun j : Fin b => (Work.MotV.genX E) ^ (j : ℕ) * Work.MotV.genY E)
      = (algMapLin E) '' (Set.range (fun j : Fin b => crX E ^ (j : ℕ) * crY E)) := by
    rw [← Set.range_comp]
    congr 1
    funext j
    exact (algMapLin_crX_pow_mul_crY E j).symm
  rw [e1, ← Submodule.map_span] at hz1
  rw [e2, ← Submodule.map_span] at hz2
  obtain ⟨P, hP, hPz⟩ := hz1
  obtain ⟨Q, hQ, hQz⟩ := hz2
  have hPQ : P = Q := by
    have hker : P - Q ∈ (algMapLin E).ker := by
      rw [LinearMap.mem_ker, map_sub, hPz, hQz, sub_self]
    rw [ker_algMapLin, Submodule.mem_bot] at hker
    exact sub_eq_zero.mp hker
  rw [← hPz, hPQ, hcr Q (by rw [← hPQ]; exact hP) hQ, map_zero]

/-! ## §3 The main statement -/

/-- The `5n` monomials `x^i` (`i < 5n/2 + 1`) and `x^j * y` (`j < (5n+1)/2 - 1`) of the
Weierstrass function field (the family `sdTFn R E n`) are `R`-linearly independent.  ROUTE: mimic
`sdTF5_linearIndependent` (case `n = 5`) and `linearIndependent_sdTen` (case `n = 2`,
`Submission.Work.MotK.TwRuling.SdWNdeg`): in the coordinate ring (free over `R[X]` with basis
`{1, Y}`) use `CoordinateRing.smul_basis_eq_zero` and `Polynomial.basisMonomials`, then transport
along the injective algebra map to the function field. -/
theorem sdTFn_linearIndependent (R : Type) [Field R] (E : WeierstrassCurve R) (n : ℕ) :
    LinearIndependent R (sdTFn R E n) := by
  have h := LinearIndependent.sum_type
    (li_genX_gen R E (5 * n / 2 + 1))
    (li_genXY_gen R E ((5 * n + 1) / 2 - 1))
    (disjoint_gen_gen R E (5 * n / 2 + 1) ((5 * n + 1) / 2 - 1))
  exact h

end

end Work.MotK.TwRuling
