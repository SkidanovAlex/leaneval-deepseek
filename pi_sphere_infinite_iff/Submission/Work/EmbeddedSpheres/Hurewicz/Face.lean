import Submission.Work.Cohomology.SingBridge
import Submission.Work.EmbeddedSpheres.Hurewicz.Simplex

/-!
# The faces of the composition and reversal 2-simplices, and the chain identities

This file contains the pointwise face computations for `compSimplex` and `revSimplex`, and the two
chain-level consequences: `chainOf (concat p q h) - chainOf p - chainOf q` is a boundary, and
`chainOf (rev p) + chainOf p` is a boundary.
-/

set_option maxHeartbeats 800000
set_option linter.unusedVariables false
set_option backward.isDefEq.respectTransparency false

attribute [local implicit_reducible] AlgebraicTopology.singularChainComplexFunctor

open CategoryTheory CategoryTheory.Limits
open scoped Topology

namespace Work.EmbeddedSpheres.Hurewicz

open Classical

noncomputable section

/-! ## 1. Coordinate computations -/

@[simp] theorem coord0_0 (y : stdSimplex ℝ (Fin 2)) :
    (stdSimplex.map (Fin.succAbove (0 : Fin 3)) y : Fin 3 → ℝ) 0 = 0 := by
  rw [stdSimplex.map_coe, FunOnFinite.linearMap_apply_apply]
  rw [show Finset.filter (fun x : Fin 2 => Fin.succAbove (0:Fin 3) x = (0:Fin 3)) Finset.univ = ∅ from by decide]
  simp

@[simp] theorem coord0_1 (y : stdSimplex ℝ (Fin 2)) :
    (stdSimplex.map (Fin.succAbove (0 : Fin 3)) y : Fin 3 → ℝ) 1 = (y : Fin 2 → ℝ) 0 := by
  rw [stdSimplex.map_coe, FunOnFinite.linearMap_apply_apply]
  rw [show Finset.filter (fun x : Fin 2 => Fin.succAbove (0:Fin 3) x = (1:Fin 3)) Finset.univ = {0} from by decide]
  simp

@[simp] theorem coord0_2 (y : stdSimplex ℝ (Fin 2)) :
    (stdSimplex.map (Fin.succAbove (0 : Fin 3)) y : Fin 3 → ℝ) 2 = (y : Fin 2 → ℝ) 1 := by
  rw [stdSimplex.map_coe, FunOnFinite.linearMap_apply_apply]
  rw [show Finset.filter (fun x : Fin 2 => Fin.succAbove (0:Fin 3) x = (2:Fin 3)) Finset.univ = {1} from by decide]
  simp

@[simp] theorem coord1_0 (y : stdSimplex ℝ (Fin 2)) :
    (stdSimplex.map (Fin.succAbove (1 : Fin 3)) y : Fin 3 → ℝ) 0 = (y : Fin 2 → ℝ) 0 := by
  rw [stdSimplex.map_coe, FunOnFinite.linearMap_apply_apply]
  rw [show Finset.filter (fun x : Fin 2 => Fin.succAbove (1:Fin 3) x = (0:Fin 3)) Finset.univ = {0} from by decide]
  simp

@[simp] theorem coord1_1 (y : stdSimplex ℝ (Fin 2)) :
    (stdSimplex.map (Fin.succAbove (1 : Fin 3)) y : Fin 3 → ℝ) 1 = 0 := by
  rw [stdSimplex.map_coe, FunOnFinite.linearMap_apply_apply]
  rw [show Finset.filter (fun x : Fin 2 => Fin.succAbove (1:Fin 3) x = (1:Fin 3)) Finset.univ = ∅ from by decide]
  simp

@[simp] theorem coord1_2 (y : stdSimplex ℝ (Fin 2)) :
    (stdSimplex.map (Fin.succAbove (1 : Fin 3)) y : Fin 3 → ℝ) 2 = (y : Fin 2 → ℝ) 1 := by
  rw [stdSimplex.map_coe, FunOnFinite.linearMap_apply_apply]
  rw [show Finset.filter (fun x : Fin 2 => Fin.succAbove (1:Fin 3) x = (2:Fin 3)) Finset.univ = {1} from by decide]
  simp

@[simp] theorem coord2_0 (y : stdSimplex ℝ (Fin 2)) :
    (stdSimplex.map (Fin.succAbove (2 : Fin 3)) y : Fin 3 → ℝ) 0 = (y : Fin 2 → ℝ) 0 := by
  rw [stdSimplex.map_coe, FunOnFinite.linearMap_apply_apply]
  rw [show Finset.filter (fun x : Fin 2 => Fin.succAbove (2:Fin 3) x = (0:Fin 3)) Finset.univ = {0} from by decide]
  simp

@[simp] theorem coord2_1 (y : stdSimplex ℝ (Fin 2)) :
    (stdSimplex.map (Fin.succAbove (2 : Fin 3)) y : Fin 3 → ℝ) 1 = (y : Fin 2 → ℝ) 1 := by
  rw [stdSimplex.map_coe, FunOnFinite.linearMap_apply_apply]
  rw [show Finset.filter (fun x : Fin 2 => Fin.succAbove (2:Fin 3) x = (1:Fin 3)) Finset.univ = {1} from by decide]
  simp

@[simp] theorem coord2_2 (y : stdSimplex ℝ (Fin 2)) :
    (stdSimplex.map (Fin.succAbove (2 : Fin 3)) y : Fin 3 → ℝ) 2 = 0 := by
  rw [stdSimplex.map_coe, FunOnFinite.linearMap_apply_apply]
  rw [show Finset.filter (fun x : Fin 2 => Fin.succAbove (2:Fin 3) x = (2:Fin 3)) Finset.univ = ∅ from by decide]
  simp

/-! ## 2. The branches of the composition 2-simplex in coordinates -/

theorem sum_three (x : stdSimplex ℝ (Fin 3)) :
    (x : Fin 3 → ℝ) 0 + (x : Fin 3 → ℝ) 1 + (x : Fin 3 → ℝ) 2 = 1 := by
  simpa only [Fin.sum_univ_three] using stdSimplex.sum_eq_one x

theorem rhoA_eq_of (x : stdSimplex ℝ (Fin 3))
    (h : (x : Fin 3 → ℝ) 2 ≤ (x : Fin 3 → ℝ) 0) :
    rhoA x = ss2 ((x : Fin 3 → ℝ) 0 - (x : Fin 3 → ℝ) 2)
      ((x : Fin 3 → ℝ) 1 + 2 * (x : Fin 3 → ℝ) 2)
      (by have := stdSimplex.zero_le x 0; have' := stdSimplex.zero_le x 2; linarith)
      (by have := stdSimplex.zero_le x 1; have' := stdSimplex.zero_le x 2; linarith)
      (by have := sum_three x; linarith) := by
  dsimp only [rhoA]
  refine ss2_congr ?_ ?_
  · rw [max_eq_right (sub_nonneg.mpr h)]
  · rw [max_eq_right (sub_nonneg.mpr h)]
    have := sum_three x; linarith

theorem rhoB_eq_of (x : stdSimplex ℝ (Fin 3))
    (h : (x : Fin 3 → ℝ) 0 ≤ (x : Fin 3 → ℝ) 2) :
    rhoB x = ss2 (2 * (x : Fin 3 → ℝ) 0 + (x : Fin 3 → ℝ) 1)
      ((x : Fin 3 → ℝ) 2 - (x : Fin 3 → ℝ) 0)
      (by have := stdSimplex.zero_le x 0; have' := stdSimplex.zero_le x 1; linarith)
      (by have := stdSimplex.zero_le x 0; have' := stdSimplex.zero_le x 2; linarith)
      (by have := sum_three x; linarith) := by
  dsimp only [rhoB]
  refine ss2_congr ?_ ?_
  · rw [max_eq_right (sub_nonneg.mpr h)]
    have := sum_three x; linarith
  · rw [max_eq_right (sub_nonneg.mpr h)]

/-! ## 3. The faces of the composition 2-simplex -/

theorem face_compSimplex_two {X : TopCat.{0}} (p q : Simp X 1)
    (h : p (stdSimplex.vertex (1 : Fin 2)) = q (stdSimplex.vertex (0 : Fin 2))) :
    face 2 (compSimplex p q h) = p := by
  ext y
  rw [face_apply, compSimplex_apply]
  have hc : (stdSimplex.map (Fin.succAbove (2 : Fin 3)) y : Fin 3 → ℝ) 2 ≤
      (stdSimplex.map (Fin.succAbove (2 : Fin 3)) y : Fin 3 → ℝ) 0 := by
    rw [coord2_2, coord2_0]; exact stdSimplex.zero_le y 0
  rw [if_pos hc]
  congr 1
  rw [rhoA_eq_of _ hc]
  refine (ss2_congr ?_ ?_).trans (ss2_self y)
  · rw [coord2_0, coord2_2, sub_zero]
  · rw [coord2_1, coord2_2, mul_zero, add_zero]

theorem face_compSimplex_zero {X : TopCat.{0}} (p q : Simp X 1)
    (h : p (stdSimplex.vertex (1 : Fin 2)) = q (stdSimplex.vertex (0 : Fin 2))) :
    face 0 (compSimplex p q h) = q := by
  ext y
  rw [face_apply, compSimplex_apply]
  by_cases hy : (y : Fin 2 → ℝ) 1 ≤ 0
  · have hy0 : (y : Fin 2 → ℝ) 1 = 0 := le_antisymm hy (stdSimplex.zero_le y 1)
    have hy1v : (y : Fin 2 → ℝ) 0 = 1 := by have := ss2_sum y; linarith
    have hyv : y = stdSimplex.vertex (0 : Fin 2) := by
      refine Subtype.ext ?_
      funext i
      fin_cases i
      · simp [stdSimplex.vertex]
        exact hy1v
      · simp [stdSimplex.vertex]
        exact hy0
    have hc : (stdSimplex.map (Fin.succAbove (0 : Fin 3)) y : Fin 3 → ℝ) 2 ≤
        (stdSimplex.map (Fin.succAbove (0 : Fin 3)) y : Fin 3 → ℝ) 0 := by
      rw [coord0_2, coord0_0]; exact hy
    have hr : rhoA (stdSimplex.map (Fin.succAbove (0 : Fin 3)) y) = stdSimplex.vertex (1 : Fin 2) := by
      apply rhoA_eq_vertex_one
      rw [coord0_2, coord0_0, hy0]
    rw [if_pos hc, hr, hyv]
    exact h
  · push_neg at hy
    have hc : ¬ ((stdSimplex.map (Fin.succAbove (0 : Fin 3)) y : Fin 3 → ℝ) 2 ≤
        (stdSimplex.map (Fin.succAbove (0 : Fin 3)) y : Fin 3 → ℝ) 0) := by
      rw [coord0_2, coord0_0]; exact not_le.mpr hy
    rw [if_neg hc]
    congr 1
    rw [rhoB_eq_of _ (by rw [coord0_2, coord0_0]; exact le_of_lt hy)]
    refine (ss2_congr ?_ ?_).trans (ss2_self y)
    · rw [coord0_0, coord0_1, mul_zero, zero_add]
    · rw [coord0_2, coord0_0, sub_zero]

theorem face_compSimplex_one {X : TopCat.{0}} (p q : Simp X 1)
    (h : p (stdSimplex.vertex (1 : Fin 2)) = q (stdSimplex.vertex (0 : Fin 2))) :
    face 1 (compSimplex p q h) = concat p q h := by
  ext y
  rw [face_apply, compSimplex_apply, concat_apply]
  by_cases hy : (y : Fin 2 → ℝ) 1 ≤ (y : Fin 2 → ℝ) 0
  · have hc : (stdSimplex.map (Fin.succAbove (1 : Fin 3)) y : Fin 3 → ℝ) 2 ≤
        (stdSimplex.map (Fin.succAbove (1 : Fin 3)) y : Fin 3 → ℝ) 0 := by
      rw [coord1_2, coord1_0]; exact hy
    rw [if_pos hc, if_pos hy]
    congr 1
    rw [rhoA_eq_of _ hc, rho1_eq hy]
    refine ss2_congr ?_ ?_
    · rw [coord1_0, coord1_2]
    · rw [coord1_1, coord1_2, zero_add]
  · push_neg at hy
    have hc : ¬ ((stdSimplex.map (Fin.succAbove (1 : Fin 3)) y : Fin 3 → ℝ) 2 ≤
        (stdSimplex.map (Fin.succAbove (1 : Fin 3)) y : Fin 3 → ℝ) 0) := by
      rw [coord1_2, coord1_0]; exact not_le.mpr hy
    rw [if_neg hc, if_neg (not_le.mpr hy)]
    congr 1
    rw [rhoB_eq_of _ (by rw [coord1_2, coord1_0]; exact le_of_lt hy), rho2_eq (le_of_lt hy)]
    refine ss2_congr ?_ ?_
    · rw [coord1_0, coord1_1, add_zero]
    · rw [coord1_2, coord1_0]

/-! ## 4. The faces of the reversal 2-simplex -/

theorem face_revSimplex_zero {X : TopCat.{0}} (p : Simp X 1) :
    face 0 (revSimplex p) = rev p := by
  ext y
  rw [face_apply, revSimplex_apply, rev_apply]
  congr 1
  refine ss2_congr ?_ ?_
  · rw [coord0_1]; have := ss2_sum y; linarith
  · rw [coord0_1]

theorem face_revSimplex_two {X : TopCat.{0}} (p : Simp X 1) :
    face 2 (revSimplex p) = p := by
  ext y
  rw [face_apply, revSimplex_apply]
  rw [show p y = p (ss2 ((y : Fin 2 → ℝ) 0) ((y : Fin 2 → ℝ) 1)
    (stdSimplex.zero_le y 0) (stdSimplex.zero_le y 1)
    (by have := ss2_sum y; linarith)) from by rw [ss2_self]]
  congr 1
  refine ss2_congr ?_ ?_
  · rw [coord2_1]; have := ss2_sum y; linarith
  · rw [coord2_1]

theorem face_revSimplex_one {X : TopCat.{0}} (p : Simp X 1) :
    face 1 (revSimplex p) = const1 (p (stdSimplex.vertex (0 : Fin 2))) := by
  ext y
  rw [face_apply, revSimplex_apply, const1_apply]
  rw [show (stdSimplex.vertex (0 : Fin 2)) = ss2 1 0 (by norm_num) (by norm_num) (by norm_num)
    from ss2_vertex_zero.symm]
  congr 1
  refine ss2_congr ?_ ?_
  · rw [coord1_1]; norm_num
  · rw [coord1_1]

/-! ## 5. Chain-level API -/

/-- The singular chain complex of `X` (with `ℤ` coefficients). -/
abbrev CX (X : TopCat.{0}) : ChainComplex (ModuleCat ℤ) ℕ :=
  (TopCat.toSSet.obj X).chainComplex (ModuleCat.of ℤ ℤ)

/-- The face of a simplex through the canonical equivalence. -/
theorem toSSetObjEquiv_delta {X : TopCat.{0}} {n : ℕ} (i : Fin (n+2))
    (x : (TopCat.toSSet.obj X).obj (Opposite.op (SimplexCategory.mk (n+1)))) :
    (TopCat.toSSetObjEquivT X (Opposite.op (SimplexCategory.mk n)))
        ((SimplicialObject.δ (TopCat.toSSet.obj X) i) x)
      = face i ((TopCat.toSSetObjEquivT X (Opposite.op (SimplexCategory.mk (n+1)))) x) := by
  ext y
  simp [face, TopCat.toSSetObjEquivT_δ_apply]

/-- The generator of the chain complex of the `i`-th face of a simplex. -/
theorem genElt_delta {X : TopCat.{0}} {n : ℕ} (i : Fin (n+2)) (σ : Simp X (n+1)) :
    Work.Cohomology.genElt ℤ (TopCat.toSSet.obj X)
        ((SimplicialObject.δ (TopCat.toSSet.obj X) i)
          ((TopCat.toSSetObjEquivT X (Opposite.op (SimplexCategory.mk (n+1)))).symm σ))
      = chainOf (face i σ) := by
  have h := toSSetObjEquiv_delta i
    ((TopCat.toSSetObjEquivT X (Opposite.op (SimplexCategory.mk (n+1)))).symm σ)
  rw [Equiv.apply_symm_apply] at h
  have h2 : (TopCat.toSSetObjEquivT X (Opposite.op (SimplexCategory.mk n))).symm (face i σ)
      = (SimplicialObject.δ (TopCat.toSSet.obj X) i)
          ((TopCat.toSSetObjEquivT X (Opposite.op (SimplexCategory.mk (n+1)))).symm σ) :=
    (Equiv.symm_apply_eq _).mpr h.symm
  rw [← h2]
  rfl

/-- `(c • f) 1 = c • (f 1)` for linear maps out of `ℤ`. -/
theorem zsmul_apply_int {N : Type*} [AddCommGroup N] [Module ℤ N]
    (f : ℤ →ₗ[ℤ] N) (c : ℤ) : ((c • f : ℤ →ₗ[ℤ] N)) 1 = c • f 1 := rfl

/-- The boundary of a generator, in terms of the faces. -/
theorem d_genElt {X : TopCat.{0}} {n : ℕ}
    (x : (TopCat.toSSet.obj X).obj (Opposite.op (SimplexCategory.mk (n+1)))) :
    (ModuleCat.Hom.hom ((CX X).d (n+1) n))
        (Work.Cohomology.genElt ℤ (TopCat.toSSet.obj X) x)
      = ∑ i : Fin (n+2), ((-1 : ℤ) ^ (i : ℕ)) •
          Work.Cohomology.genElt ℤ (TopCat.toSSet.obj X)
            ((SimplicialObject.δ (TopCat.toSSet.obj X) i) x) := by
  have h := congrArg
    (fun (g : ModuleCat.of ℤ ℤ ⟶ (CX X).X n) => ModuleCat.Hom.hom g (1 : ℤ))
    (SSet.ιChainComplex_d (X := TopCat.toSSet.obj X) (R := ModuleCat.of ℤ ℤ) x)
  simp only [ModuleCat.hom_comp, LinearMap.comp_apply, ModuleCat.hom_sum,
    ModuleCat.hom_zsmul, LinearMap.sum_apply, zsmul_apply_int] at h
  have key : (ModuleCat.Hom.hom
        (((TopCat.toSSet.obj X).chainComplex (ModuleCat.of ℤ ℤ)).d (n+1) n))
        (Work.Cohomology.genElt ℤ (TopCat.toSSet.obj X) x)
      = ∑ i : Fin (n+2), ((-1 : ℤ) ^ (i : ℕ)) •
          Work.Cohomology.genElt ℤ (TopCat.toSSet.obj X)
            ((SimplicialObject.δ (TopCat.toSSet.obj X) i) x) := by
    simpa only [Work.Cohomology.genElt] using h
  exact key

/-- The boundary of the chain of a simplex, in terms of the faces. -/
theorem d_chainOf {X : TopCat.{0}} {n : ℕ} (σ : Simp X (n+1)) :
    (ModuleCat.Hom.hom ((CX X).d (n+1) n)) (chainOf σ)
      = ∑ i : Fin (n+2), ((-1 : ℤ) ^ (i : ℕ)) • chainOf (face i σ) := by
  rw [show chainOf σ = Work.Cohomology.genElt ℤ (TopCat.toSSet.obj X)
      ((TopCat.toSSetObjEquivT X (Opposite.op (SimplexCategory.mk (n+1)))).symm σ) from rfl]
  rw [d_genElt]
  exact Finset.sum_congr rfl (fun i _ => by rw [genElt_delta])

/-! ## 6. The chain identities -/

theorem chainOf_concat_sub {X : TopCat.{0}} (p q : Simp X 1)
    (h : p (stdSimplex.vertex (1 : Fin 2)) = q (stdSimplex.vertex (0 : Fin 2))) :
    ∃ c : (CX X).X 2,
      (ModuleCat.Hom.hom ((CX X).d 2 1)) c
        = chainOf (concat p q h) - chainOf p - chainOf q := by
  refine ⟨- chainOf (compSimplex p q h), ?_⟩
  rw [map_neg, d_chainOf (compSimplex p q h), Fin.sum_univ_three,
    face_compSimplex_zero, face_compSimplex_one, face_compSimplex_two]
  simp
  abel

theorem face_const2 {X : TopCat.{0}} (x : X) (i : Fin 3) :
    face i (const2 x) = const1 x := rfl

theorem chainOf_rev_add {X : TopCat.{0}} (p : Simp X 1) :
    ∃ c : (CX X).X 2,
      (ModuleCat.Hom.hom ((CX X).d 2 1)) c = chainOf (rev p) + chainOf p := by
  refine ⟨chainOf (revSimplex p) + chainOf (const2 (p (stdSimplex.vertex (0 : Fin 2)))), ?_⟩
  rw [map_add, d_chainOf (revSimplex p), d_chainOf (const2 (p (stdSimplex.vertex (0 : Fin 2)))),
    Fin.sum_univ_three, Fin.sum_univ_three,
    face_revSimplex_zero, face_revSimplex_one, face_revSimplex_two,
    face_const2, face_const2, face_const2]
  simp
  abel

end

end Work.EmbeddedSpheres.Hurewicz
