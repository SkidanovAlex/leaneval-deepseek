/-
Copyright (c) 2026 The annals_motivic_invariants team. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Work.MotK
-/
import Mathlib
import Submission.Work.MotV.Defs
import Submission.Work.MotC2.Relations

set_option linter.unusedVariables false -- v435-speed

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

/-!
# Vocabulary for the non-degeneracy of the ruling chart

This file holds the pieces shared by the proof of `Work.MotK.TwRuling.sdW_four_ne_zero`
(the non-degeneracy `sdW K D h 4 ≠ 0`) and by the "kernel of the multiplication map"
argument that underlies it (`Work.MotK.TwRuling.KleinNondeg`).

Let `R` be a field, `E` a Weierstrass curve over `R`, and `Om := E.FunctionField`.

* `crX E`, `crY E` are the classes of `X`, `Y` in the *coordinate ring* `E.CoordinateRing`;
* `sdBas E = ![1, x, y, x², xy]` is the basis of `L(5·O)` (in `Om`);
* `sdTen E`, indexed by `Fin 6 ⊕ Fin 4`, is the family `(1, x, …, x⁵; y, xy, x²y, x³y)` of
  monomials spanning `L(10·O)` (in `Om`).

Main results proved here (all sorry-free, no hypotheses beyond `R` a field):

* `li_X_pow` : the monomials `X^i` are `R`-linearly independent in `R[X]`;
* `linearIndependent_sdTen` : the ten monomials are `R`-linearly independent in `Om`;
* `sdWeierstrass` : the Weierstrass relation in `Om`;
* `ker_smulOne`, `ker_smulY` : `P ↦ P·1` and `P ↦ P·y` are injective on `R[X]`.

The companion statement `productSpan_eq` (the span of the products `b_i b_j` of two elements of
the basis equals the span of the ten monomials) is proved in the sibling module
`Submission.Work.MotK.TwRuling.productSpan_eq`.
-/

set_option autoImplicit false
set_option linter.unusedSectionVars false
set_option maxHeartbeats 400000

open WeierstrassCurve WeierstrassCurve.Affine
open Polynomial

namespace Work.MotK.TwRuling

noncomputable section

variable {R : Type} [Field R]

/-! ## §1 The monomials `X^i` are linearly independent in `R[X]` -/

/-- The monomials `X ^ i`, `i < n`, are `R`-linearly independent in `R[X]`. -/
theorem li_X_pow (n : ℕ) :
    LinearIndependent R (fun i : Fin n => (Polynomial.X : R[X]) ^ (i : ℕ)) := by
  rw [Fintype.linearIndependent_iff]
  intro c hc j
  have h := congrArg (Polynomial.lcoeff R (j : ℕ)) hc
  simp only [map_sum, map_smul, Polynomial.lcoeff_apply, map_zero] at h
  rw [Finset.sum_eq_single j] at h
  · simpa using h
  · intro b _ hb
    rw [Polynomial.coeff_X_pow, ite_eq_right (fun hjb => hb (Fin.ext hjb).symm), smul_zero]
  · intro h; exact absurd (Finset.mem_univ j) h

/-! ## §2 The classes of `X` and `Y` in the coordinate ring -/

/-- The class of `X` in `E.CoordinateRing`. -/
noncomputable def crX (E : WeierstrassCurve R) : CoordinateRing E :=
  CoordinateRing.mk E (Polynomial.C (Polynomial.X : R[X]))

/-- The class of `Y` in `E.CoordinateRing`. -/
noncomputable def crY (E : WeierstrassCurve R) : CoordinateRing E :=
  CoordinateRing.mk E (Polynomial.X : (R[X])[X])

theorem algebraMap_X_eq_crX (E : WeierstrassCurve R) :
    algebraMap R[X] (CoordinateRing E) Polynomial.X = crX E := by
  rw [AdjoinRoot.algebraMap_eq, crX]
  exact (AdjoinRoot.mk_C (f := polynomial E) Polynomial.X).symm

section

variable (E : WeierstrassCurve R)

theorem crX_pow_eq (i : ℕ) : crX E ^ i = (Polynomial.X : R[X]) ^ i • (1 : CoordinateRing E) := by
  rw [Algebra.smul_def, mul_one, map_pow, algebraMap_X_eq_crX]

theorem crX_pow_mul_crY_eq (j : ℕ) :
    crX E ^ j * crY E = (Polynomial.X : R[X]) ^ j • crY E := by
  rw [Algebra.smul_def, map_pow, algebraMap_X_eq_crX]

/-- The linear map `P ↦ P • 1` on `R[X]`. -/
noncomputable def smulOne : R[X] →ₗ[R] CoordinateRing E where
  toFun P := P • (1 : CoordinateRing E)
  map_add' a b := by rw [add_smul]
  map_smul' r a := by rw [smul_assoc]; rfl

/-- The linear map `P ↦ P • Y` on `R[X]`. -/
noncomputable def smulY : R[X] →ₗ[R] CoordinateRing E where
  toFun P := P • crY E
  map_add' a b := by rw [add_smul]
  map_smul' r a := by rw [smul_assoc]; rfl

theorem smulOne_apply (P : R[X]) : smulOne E P = algebraMap R[X] (CoordinateRing E) P := by
  show P • (1 : CoordinateRing E) = algebraMap R[X] (CoordinateRing E) P
  rw [Algebra.smul_def, mul_one]

theorem smulY_apply (P : R[X]) : smulY E P = algebraMap R[X] (CoordinateRing E) P * crY E := by
  show P • crY E = algebraMap R[X] (CoordinateRing E) P * crY E
  rw [Algebra.smul_def]

theorem ker_smulOne : (smulOne E).ker = ⊥ := by
  rw [LinearMap.ker_eq_bot']
  intro P hP
  have h : P • (1 : CoordinateRing E) + (0 : R[X]) • crY E = 0 := by
    simp only [zero_smul, add_zero]
    exact hP
  exact (CoordinateRing.smul_basis_eq_zero h).1

theorem ker_smulY : (smulY E).ker = ⊥ := by
  rw [LinearMap.ker_eq_bot']
  intro P hP
  have h : (0 : R[X]) • (1 : CoordinateRing E) + P • crY E = 0 := by
    simp only [zero_smul, zero_add]
    exact hP
  exact (CoordinateRing.smul_basis_eq_zero h).2

theorem li_crX : LinearIndependent R (fun i : Fin 6 => crX E ^ (i : ℕ)) := by
  have h := (li_X_pow (R := R) 6).map' (smulOne E) (ker_smulOne E)
  convert h using 1
  · funext i
    exact crX_pow_eq E i

theorem li_crXY : LinearIndependent R (fun j : Fin 4 => crX E ^ (j : ℕ) * crY E) := by
  have h := (li_X_pow (R := R) 4).map' (smulY E) (ker_smulY E)
  convert h using 1
  · funext j
    exact crX_pow_mul_crY_eq E j

/-- The two families `1, x, …, x⁵` and `y, xy, x²y, x³y` have independent spans in the
coordinate ring. -/
theorem disjoint_cr : Disjoint
    (Submodule.span R (Set.range (fun i : Fin 6 => crX E ^ (i : ℕ))))
    (Submodule.span R (Set.range (fun j : Fin 4 => crX E ^ (j : ℕ) * crY E))) := by
  rw [Submodule.disjoint_def]
  intro z hz1 hz2
  have e1 : Set.range (fun i : Fin 6 => crX E ^ (i : ℕ))
      = (smulOne E) '' (Set.range (fun i : Fin 6 => (Polynomial.X : R[X]) ^ (i : ℕ))) := by
    rw [← Set.range_comp]
    congr 1
    funext i
    exact crX_pow_eq E i
  have e2 : Set.range (fun j : Fin 4 => crX E ^ (j : ℕ) * crY E)
      = (smulY E) '' (Set.range (fun j : Fin 4 => (Polynomial.X : R[X]) ^ (j : ℕ))) := by
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

end

/-! ## §3 Transport to the function field -/

section

variable (E : WeierstrassCurve R)

/-- The `R`-linear map `E.CoordinateRing → E.FunctionField` (injective). -/
noncomputable def algMapLin : CoordinateRing E →ₗ[R] Affine.FunctionField E where
  toFun := algebraMap (CoordinateRing E) (Affine.FunctionField E)
  map_add' a b := map_add _ a b
  map_smul' r a := by
    simp only [Algebra.smul_def, map_mul, RingHom.id_apply]
    rw [IsScalarTower.algebraMap_apply R (CoordinateRing E) (Affine.FunctionField E) r]

theorem ker_algMapLin : (algMapLin E).ker = ⊥ := by
  rw [LinearMap.ker_eq_bot']
  intro z hz
  refine IsFractionRing.injective (CoordinateRing E) (Affine.FunctionField E) ?_
  show algebraMap (CoordinateRing E) (Affine.FunctionField E) z
    = algebraMap (CoordinateRing E) (Affine.FunctionField E) 0
  rw [map_zero]
  exact hz

theorem algMap_crX : algebraMap (CoordinateRing E) (Affine.FunctionField E) (crX E)
    = Work.MotV.genX E := rfl

theorem algMap_crY : algebraMap (CoordinateRing E) (Affine.FunctionField E) (crY E)
    = Work.MotV.genY E := rfl

theorem algMap_crX_pow (i : ℕ) :
    algebraMap (CoordinateRing E) (Affine.FunctionField E) (crX E ^ i)
      = (Work.MotV.genX E) ^ i := by
  rw [map_pow, algMap_crX]

theorem algMap_crX_pow_mul_crY (j : ℕ) :
    algebraMap (CoordinateRing E) (Affine.FunctionField E) (crX E ^ j * crY E)
      = (Work.MotV.genX E) ^ j * Work.MotV.genY E := by
  rw [map_mul, map_pow, algMap_crX, algMap_crY]

theorem algMapLin_crX_pow (i : ℕ) : algMapLin E (crX E ^ i) = (Work.MotV.genX E) ^ i :=
  algMap_crX_pow E i

theorem algMapLin_crX_pow_mul_crY (j : ℕ) :
    algMapLin E (crX E ^ j * crY E) = (Work.MotV.genX E) ^ j * Work.MotV.genY E :=
  algMap_crX_pow_mul_crY E j

theorem li_genX : LinearIndependent R (fun i : Fin 6 => (Work.MotV.genX E) ^ (i : ℕ)) := by
  have h := (li_crX E).map' (algMapLin E) (ker_algMapLin E)
  convert h using 1
  · funext i
    exact (algMapLin_crX_pow E i).symm

theorem li_genXY : LinearIndependent R
    (fun j : Fin 4 => (Work.MotV.genX E) ^ (j : ℕ) * Work.MotV.genY E) := by
  have h := (li_crXY E).map' (algMapLin E) (ker_algMapLin E)
  convert h using 1
  · funext j
    exact (algMapLin_crX_pow_mul_crY E j).symm

theorem disjoint_gen : Disjoint
    (Submodule.span R (Set.range (fun i : Fin 6 => (Work.MotV.genX E) ^ (i : ℕ))))
    (Submodule.span R (Set.range (fun j : Fin 4 =>
      (Work.MotV.genX E) ^ (j : ℕ) * Work.MotV.genY E))) := by
  have hcr : ∀ x ∈ Submodule.span R (Set.range (fun i : Fin 6 => crX E ^ (i : ℕ))),
      x ∈ Submodule.span R (Set.range (fun j : Fin 4 => crX E ^ (j : ℕ) * crY E)) → x = 0 :=
    Submodule.disjoint_def.mp (disjoint_cr E)
  rw [Submodule.disjoint_def]
  intro z hz1 hz2
  have e1 : Set.range (fun i : Fin 6 => (Work.MotV.genX E) ^ (i : ℕ))
      = (algMapLin E) '' (Set.range (fun i : Fin 6 => crX E ^ (i : ℕ))) := by
    rw [← Set.range_comp]
    congr 1
    funext i
    exact (algMapLin_crX_pow E i).symm
  have e2 : Set.range (fun j : Fin 4 => (Work.MotV.genX E) ^ (j : ℕ) * Work.MotV.genY E)
      = (algMapLin E) '' (Set.range (fun j : Fin 4 => crX E ^ (j : ℕ) * crY E)) := by
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

end

/-! ## §4 The basis of `L(5·O)` and the ten monomials of `L(10·O)` -/

/-- The basis `1, x, y, x², xy` of `L(5·O)`, as elements of the function field of `E`. -/
noncomputable def sdBas (E : WeierstrassCurve R) : Fin 5 → Affine.FunctionField E :=
  ![1, Work.MotV.genX E, Work.MotV.genY E, (Work.MotV.genX E) ^ 2,
    Work.MotV.genX E * Work.MotV.genY E]

/-- The ten monomials of `L(10·O)`: the six functions `1, x, …, x⁵` followed by the four functions
`y, xy, x²y, x³y`.  (Indexed by `Fin 6 ⊕ Fin 4` so that the two blocks are separate.) -/
noncomputable def sdTen (E : WeierstrassCurve R) : Fin 6 ⊕ Fin 4 → Affine.FunctionField E :=
  Sum.elim (fun i : Fin 6 => (Work.MotV.genX E) ^ (i : ℕ))
    (fun j : Fin 4 => (Work.MotV.genX E) ^ (j : ℕ) * Work.MotV.genY E)

@[simp]
theorem sdTen_inl (E : WeierstrassCurve R) (i : Fin 6) :
    sdTen E (Sum.inl i) = (Work.MotV.genX E) ^ (i : ℕ) := rfl

@[simp]
theorem sdTen_inr (E : WeierstrassCurve R) (j : Fin 4) :
    sdTen E (Sum.inr j) = (Work.MotV.genX E) ^ (j : ℕ) * Work.MotV.genY E := rfl

@[simp]
theorem sdBas_apply_zero (E : WeierstrassCurve R) : sdBas E 0 = 1 := rfl
@[simp]
theorem sdBas_apply_one (E : WeierstrassCurve R) : sdBas E 1 = Work.MotV.genX E := rfl
@[simp]
theorem sdBas_apply_two (E : WeierstrassCurve R) : sdBas E 2 = Work.MotV.genY E := rfl
@[simp]
theorem sdBas_apply_three (E : WeierstrassCurve R) : sdBas E 3 = (Work.MotV.genX E) ^ 2 := rfl
@[simp]
theorem sdBas_apply_four (E : WeierstrassCurve R) :
    sdBas E 4 = Work.MotV.genX E * Work.MotV.genY E := rfl

/-- **The ten monomials of `L(10·O)` are linearly independent** over the base field. -/
theorem linearIndependent_sdTen (E : WeierstrassCurve R) : LinearIndependent R (sdTen E) := by
  have h : LinearIndependent R (Sum.elim (fun i : Fin 6 => (Work.MotV.genX E) ^ (i : ℕ))
      (fun j : Fin 4 => (Work.MotV.genX E) ^ (j : ℕ) * Work.MotV.genY E)) :=
    LinearIndependent.sum_type (li_genX E) (li_genXY E) (disjoint_gen E)
  exact h

/-- The span of the ten monomials has dimension ten. -/
theorem finrank_span_sdTen (E : WeierstrassCurve R) :
    Module.finrank R (Submodule.span R (Set.range (sdTen E))) = 10 := by
  rw [finrank_span_eq_card (linearIndependent_sdTen E)]
  simp [Fintype.card_sum]

/-! ## §5 The Weierstrass relation in the function field -/

/-- The affine Weierstrass relation for the generic point of `E`. -/
theorem sdWeierstrass (E : WeierstrassCurve R) :
    (Work.MotV.genY E) ^ 2 + algebraMap R (Affine.FunctionField E) E.a₁ * Work.MotV.genX E
        * Work.MotV.genY E
      + algebraMap R (Affine.FunctionField E) E.a₃ * Work.MotV.genY E
      = (Work.MotV.genX E) ^ 3 + algebraMap R (Affine.FunctionField E) E.a₂
          * (Work.MotV.genX E) ^ 2
        + algebraMap R (Affine.FunctionField E) E.a₄ * Work.MotV.genX E
        + algebraMap R (Affine.FunctionField E) E.a₆ := by
  have h := Work.MotC2.genY_sq_relation E
  rw [Work.MotC2.genX, Work.MotC2.genY, Work.MotC2.coordX_eq_mk, Work.MotC2.coordY_eq_mk] at h
  exact h

end

end Work.MotK.TwRuling
