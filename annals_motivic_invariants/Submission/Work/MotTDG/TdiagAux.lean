import Mathlib
import Submission.Work.MotTDG.Defs
import Submission.Work.MotTDG.Setup
import Submission.Work.MotTDG.rhoVW_eq_zero
import Submission.Work.MotTDG.muMat_det_ne_zero
import Submission.Work.MotTDG.exists_algHom_of_point
import Submission.Work.MotK.KleinPScale
import Submission.Work.MotTDG.reduce_alg
import Submission.Work.MotTDG.pfaffStable_unlift
import Submission.Work.Reflect.PolyId
set_option maxRecDepth 100000

set_option linter.unusedVariables false -- v435-speed

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

/-!
# TDG-T, the auxiliary machinery (node TDG-M, done directly)

Everything that node TDG-T needs on top of the dispatched leaves: the homogeneity of the
Pfaffians, the "algebraicity is transitive along the Weierstrass equation" brick, the
non-vanishing of the normalising scalar `ell (kvec M)`, the reduction of a net-preserving
projectivity to a point of the curve, the transcendence of the first coordinate, the
resulting endomorphism, and finally the `AlgEquiv` for an invertible net-preserving pair
`M`, `M'`.
-/

set_option maxHeartbeats 3200000
set_option linter.unusedSectionVars false

namespace Work.MotTDG
noncomputable section

open Polynomial WeierstrassCurve WeierstrassCurve.Affine
open scoped IntermediateField

/-! ## §1 Homogeneity of the Pfaffians -/

/-- The Pfaffians are homogeneous of degree `2`. -/
theorem kleinP_smul {R : Type*} [CommRing R] (a b c : R) (z : Fin 5 → R) (k : Fin 5) :
    Work.MotK.kleinP a b (fun i => c * z i) k = c ^ 2 * Work.MotK.kleinP a b z k := by
  fin_cases k <;>
    simp only [Work.MotK.kleinP_zero', Work.MotK.kleinP_one', Work.MotK.kleinP_two',
      Work.MotK.kleinP_three', Work.MotK.kleinP_four', Work.MotK.kleinP0, Work.MotK.kleinP1,
      Work.MotK.kleinP2, Work.MotK.kleinP3, Work.MotK.kleinP4] <;> ring

/-! ## §2 Finite sums of algebraic elements -/

/-- A finite sum of algebraic elements is algebraic. -/
theorem Tdiag_isAlgebraic_finset_sum {R : Type*} [CommRing R] {S : Type*} [CommRing S] [Algebra R S]
    [NoZeroDivisors R] [Nontrivial R] {ι : Type*} (f : ι → S) :
    ∀ (s : Finset ι), (∀ i ∈ s, IsAlgebraic R (f i)) → IsAlgebraic R (∑ i ∈ s, f i) := by
  classical
  intro s
  induction s using Finset.induction with
  | empty => intro _; simpa using isAlgebraic_zero
  | insert a s ha ih =>
      intro hf
      rw [Finset.sum_insert ha]
      exact (hf a (Finset.mem_insert_self a s)).add
        (ih fun i hi => hf i (Finset.mem_insert_of_mem hi))

/-! ## §3 Algebraicity along the Weierstrass equation -/

/-- The Weierstrass equation, rearranged as a quadratic form identity. -/
theorem quad_eq_of_equation {L : Type*} [Field L] (E : WeierstrassCurve L)
    {U V : FunctionField E} (h : Equation (E.map (algebraMap L (FunctionField E))) U V) :
    V ^ 2 + (algebraMap L (FunctionField E) E.a₁ * U + algebraMap L (FunctionField E) E.a₃) * V
      + -(U ^ 3 + algebraMap L (FunctionField E) E.a₂ * U ^ 2
        + algebraMap L (FunctionField E) E.a₄ * U + algebraMap L (FunctionField E) E.a₆) = 0 := by
  have h' := h
  rw [equation_iff, WeierstrassCurve.map_a₁, WeierstrassCurve.map_a₂, WeierstrassCurve.map_a₃,
    WeierstrassCurve.map_a₄, WeierstrassCurve.map_a₆] at h'
  linear_combination (norm := first | refl_ring1 | ring1) h'

/-- **Algebraicity is transitive along the Weierstrass equation**: if `(U, V)` lies on `E` over
the function field of `E` and `U` is algebraic over `L`, then so is `V`.  (The relative algebraic
closure of `L` in `L(E)` is a field, and `V` is integral over it.) -/
theorem isAlgebraic_of_equation {L : Type*} [Field L] (E : WeierstrassCurve L)
    {U V : FunctionField E}
    (h : Equation (E.map (algebraMap L (FunctionField E))) U V) (hU : IsAlgebraic L U) :
    IsAlgebraic L V := by
  have hUint : IsIntegral L U := isAlgebraic_iff_isIntegral.mp hU
  let K : IntermediateField L (FunctionField E) := L⟮U⟯
  have hUmem : U ∈ K := IntermediateField.mem_adjoin_simple_self L U
  let b : K := ⟨algebraMap L _ E.a₁ * U + algebraMap L _ E.a₃,
      K.add_mem (K.mul_mem (IntermediateField.algebraMap_mem K E.a₁) hUmem)
        (IntermediateField.algebraMap_mem K E.a₃)⟩
  let c : K := ⟨-(U ^ 3 + algebraMap L _ E.a₂ * U ^ 2 + algebraMap L _ E.a₄ * U
        + algebraMap L _ E.a₆),
      K.neg_mem (K.add_mem (K.add_mem (K.add_mem (K.pow_mem hUmem 3)
        (K.mul_mem (IntermediateField.algebraMap_mem K E.a₂) (K.pow_mem hUmem 2)))
        (K.mul_mem (IntermediateField.algebraMap_mem K E.a₄) hUmem))
        (IntermediateField.algebraMap_mem K E.a₆))⟩
  have hmonic : (X ^ 2 + C b * X + C c : Polynomial K).Monic := by
    rw [show (X ^ 2 + C b * X + C c : Polynomial K) = X ^ 2 + (C b * X + C c) from by ring]
    refine Polynomial.monic_X_pow_add ?_
    calc (C b * X + C c : Polynomial K).degree ≤ max (C b * X).degree (C c).degree :=
          Polynomial.degree_add_le _ _
      _ ≤ max 1 0 := by
          refine max_le_max ?_ ?_
          · exact Polynomial.degree_C_mul_X_le b
          · exact Polynomial.degree_C_le
      _ < (2 : WithBot ℕ) := by norm_num
  have heval : Polynomial.eval₂ (algebraMap K (FunctionField E)) V
      (X ^ 2 + C b * X + C c) = 0 := by
    have key : Polynomial.eval₂ (algebraMap K (FunctionField E)) V (X ^ 2 + C b * X + C c)
        = V ^ 2 + (algebraMap L (FunctionField E) E.a₁ * U
            + algebraMap L (FunctionField E) E.a₃) * V
          + -(U ^ 3 + algebraMap L (FunctionField E) E.a₂ * U ^ 2
            + algebraMap L (FunctionField E) E.a₄ * U + algebraMap L (FunctionField E) E.a₆) := by
      simp only [eval₂_add, eval₂_mul, eval₂_pow, eval₂_X, eval₂_C,
        IntermediateField.algebraMap_apply]
      simp only [b, c]
      rfl
    rw [key, quad_eq_of_equation E h]
  haveI : Module.Finite L K := IntermediateField.adjoin.finiteDimensional hUint
  haveI : Algebra.IsAlgebraic L K := Algebra.IsAlgebraic.of_finite L K
  exact IsIntegral.trans_isAlgebraic L ⟨_, hmonic, heval⟩

section Main

variable {𝕜 : Type} [Field 𝕜] (D : Work.MotV.KleinData 𝕜)

/-- `ell` of the `M`-image of the Klein coordinates does not vanish. -/
theorem Tdiag_ell_kvec_ne_zero (L : Type) [Field L] [Algebra 𝕜 L] (e : Fin 5 → Fin 5 → 𝕜)
    (he : ∀ m, Work.MotV.kleinBas D L m =
      ∑ i, algebraMap L (FunctionField (D.E.baseChange L)) (algebraMap 𝕜 L (e m i))
        * Work.MotV.kleinCoord D L i)
    (M M' : Matrix (Fin 5) (Fin 5) L) (hMM' : M * M' = 1) :
    ell D L e (kvec D L M) ≠ 0 := by
  intro h0
  have hlm : ∀ (A : Matrix (Fin 5) (Fin 5) L)
      (v : Fin 5 → FunctionField (D.E.baseChange L)) (i : Fin 5),
      lmulVec (D.E.baseChange L) A v i = ∑ j, algebraMap L _ (A i j) * v j := by
    intro A v i
    rw [lmulVec_apply]
    exact Finset.sum_congr rfl fun j _ => Algebra.smul_def _ _
  have hkvec : kvec D L M = lmulVec (D.E.baseChange L) M (Work.MotV.kleinCoord D L) := by
    funext i
    rw [kvec, hlm]
  have hmat : matMul (eL D L e) M = (eL D L e) * M := by
    funext a b
    rw [matMul_apply, Matrix.mul_apply]
  have hell : ell D L e (kvec D L M)
      = ∑ j, (∑ i, eL D L e 0 i * M i j) • Work.MotV.kleinCoord D L j := by
    calc ell D L e (kvec D L M)
        = lmulVec (D.E.baseChange L) (eL D L e) (kvec D L M) 0 := (hlm (eL D L e) _ 0).symm
      _ = lmulVec (D.E.baseChange L) (eL D L e)
            (lmulVec (D.E.baseChange L) M (Work.MotV.kleinCoord D L)) 0 := by rw [hkvec]
      _ = lmulVec (D.E.baseChange L) (matMul (eL D L e) M) (Work.MotV.kleinCoord D L) 0 := by
            rw [lmulVec_matMul]
      _ = lmulVec (D.E.baseChange L) ((eL D L e) * M) (Work.MotV.kleinCoord D L) 0 := by
            rw [hmat]
      _ = ∑ j, (∑ i, eL D L e 0 i * M i j) • Work.MotV.kleinCoord D L j := by
            rw [lmulVec_apply]
            exact Finset.sum_congr rfl fun j _ => by rw [Matrix.mul_apply]
  have hsum : (∑ j, (∑ i, eL D L e 0 i * M i j) • Work.MotV.kleinCoord D L j) = 0 := by
    rw [← hell]; exact h0
  have hg : ∀ j : Fin 5, (∑ i, eL D L e 0 i * M i j) = 0 := fun j =>
    (Fintype.linearIndependent_iff.mp (kleinCoord_linearIndependent D L e he)
      (fun j => ∑ i, eL D L e 0 i * M i j)) hsum j
  have hNM : ∀ a b : Fin 5, (∑ j, M a j * M' j b) = if a = b then (1 : L) else 0 := by
    intro a b
    have h := congrFun (congrFun hMM' a) b
    rwa [Matrix.mul_apply, Matrix.one_apply] at h
  have hrow : ∀ l : Fin 5, eL D L e 0 l = 0 := by
    intro l
    calc eL D L e 0 l
        = ∑ j, (∑ i, eL D L e 0 i * M i j) * M' j l := by
          symm
          calc ∑ j, (∑ i, eL D L e 0 i * M i j) * M' j l
              = ∑ j, ∑ i, eL D L e 0 i * (M i j * M' j l) := by
                  refine Finset.sum_congr rfl fun j _ => ?_
                  rw [Finset.sum_mul]
                  exact Finset.sum_congr rfl fun i _ => by ring
            _ = ∑ i, ∑ j, eL D L e 0 i * (M i j * M' j l) := Finset.sum_comm
            _ = ∑ i, eL D L e 0 i * (∑ j, M i j * M' j l) := by
                  refine Finset.sum_congr rfl fun i _ => ?_
                  rw [Finset.mul_sum]
            _ = ∑ i, eL D L e 0 i * (if i = l then (1 : L) else 0) := by
                  refine Finset.sum_congr rfl fun i _ => ?_
                  rw [hNM i l]
            _ = eL D L e 0 l := by
                  rw [Finset.sum_eq_single l]
                  · rw [if_pos rfl, mul_one]
                  · intro b _ hb; rw [if_neg hb, mul_zero]
                  · intro hl; exact absurd (Finset.mem_univ l) hl
      _ = 0 := by rw [Finset.sum_eq_zero (fun j _ => by rw [hg j, zero_mul])]
  have hone : (1 : FunctionField (D.E.baseChange L))
      = ∑ i, algebraMap L _ (eL D L e 0 i) * Work.MotV.kleinCoord D L i := by
    have h := basE_eq_eL_kleinCoord D L e he 0
    rw [basE_zero] at h
    exact h
  have hzero : (1 : FunctionField (D.E.baseChange L)) = 0 := by
    rw [hone]
    exact Finset.sum_eq_zero fun i _ => by rw [hrow i, map_zero, zero_mul]
  exact one_ne_zero hzero

/-- `cL` applied to `wvec` is the shifted vector itself. -/
theorem Tdiag_sum_cL_wvec (L : Type) [Field L] [Algebra 𝕜 L] (e : Fin 5 → Fin 5 → 𝕜)
    (he : ∀ m, Work.MotV.kleinBas D L m =
      ∑ i, algebraMap L (FunctionField (D.E.baseChange L)) (algebraMap 𝕜 L (e m i))
        * Work.MotV.kleinCoord D L i)
    (M : Matrix (Fin 5) (Fin 5) L) :
    (fun i => ∑ m, algebraMap L (FunctionField (D.E.baseChange L)) (cL D L i m)
      * wvec D L e M m) = kappaShift D L e M := by
  have hlm : ∀ (A : Matrix (Fin 5) (Fin 5) L)
      (v : Fin 5 → FunctionField (D.E.baseChange L)) (i : Fin 5),
      lmulVec (D.E.baseChange L) A v i = ∑ j, algebraMap L _ (A i j) * v j := by
    intro A v i
    rw [lmulVec_apply]
    exact Finset.sum_congr rfl fun j _ => Algebra.smul_def _ _
  have hwvec : wvec D L e M = lmulVec (D.E.baseChange L) (eL D L e) (kappaShift D L e M) := by
    funext m
    rw [wvec, hlm]
  funext i
  calc ∑ m, algebraMap L _ (cL D L i m) * wvec D L e M m
      = lmulVec (D.E.baseChange L) (cL D L) (wvec D L e M) i := (hlm (cL D L) _ i).symm
    _ = lmulVec (D.E.baseChange L) (cL D L)
          (lmulVec (D.E.baseChange L) (eL D L e) (kappaShift D L e M)) i := by rw [hwvec]
    _ = lmulVec (D.E.baseChange L) (matMul (cL D L) (eL D L e)) (kappaShift D L e M) i := by
          rw [lmulVec_matMul]
    _ = lmulVec (D.E.baseChange L) matOne (kappaShift D L e M) i := by
          rw [cL_matMul_eL D L e he]
    _ = kappaShift D L e M i := by rw [lmulVec_matOne]

/-- `wvec D L e M 0 = 1`. -/
theorem Tdiag_wvec_zero (L : Type) [Field L] [Algebra 𝕜 L] (e : Fin 5 → Fin 5 → 𝕜)
    (M : Matrix (Fin 5) (Fin 5) L) (hne : ell D L e (kvec D L M) ≠ 0) :
    wvec D L e M 0 = 1 := by
  have h1 : wvec D L e M 0
      = (∑ i, algebraMap L (FunctionField (D.E.baseChange L)) (eL D L e 0 i) * kvec D L M i)
        / ell D L e (kvec D L M) := by
    rw [wvec]
    simp only [kappaShift]
    rw [Finset.sum_div]
    exact Finset.sum_congr rfl fun i _ => by rw [mul_div_assoc]
  rw [h1]
  rw [show ell D L e (kvec D L M)
      = ∑ i, algebraMap L (FunctionField (D.E.baseChange L)) (eL D L e 0 i) * kvec D L M i
      from rfl]
  exact div_self hne

/-- The shifted vector is the `M`-image divided by `ell (kvec M)`. -/
theorem Tdiag_kvec_eq_ell_mul_kappaShift (L : Type) [Field L] [Algebra 𝕜 L]
    (e : Fin 5 → Fin 5 → 𝕜) (M : Matrix (Fin 5) (Fin 5) L)
    (hne : ell D L e (kvec D L M) ≠ 0) (i : Fin 5) :
    kvec D L M i = ell D L e (kvec D L M) * kappaShift D L e M i := by
  rw [kappaShift, ← mul_div_assoc, mul_div_cancel_left₀ _ hne]

/-- **Inverting the matrix.**  If `N * M = 1` then `∑ j, N l j * kvec M j = κ l`. -/
theorem Tdiag_sum_mat_mulVec (L : Type) [Field L] [Algebra 𝕜 L]
    (N M : Matrix (Fin 5) (Fin 5) L) (h : N * M = 1) (l : Fin 5) :
    ∑ j, algebraMap L (FunctionField (D.E.baseChange L)) (N l j) * kvec D L M j =
      Work.MotV.kleinCoord D L l := by
  have hlm : ∀ (A : Matrix (Fin 5) (Fin 5) L)
      (v : Fin 5 → FunctionField (D.E.baseChange L)) (i : Fin 5),
      lmulVec (D.E.baseChange L) A v i = ∑ j, algebraMap L _ (A i j) * v j := by
    intro A v i
    rw [lmulVec_apply]
    exact Finset.sum_congr rfl fun j _ => Algebra.smul_def _ _
  have hkvec : kvec D L M = lmulVec (D.E.baseChange L) M (Work.MotV.kleinCoord D L) := by
    funext i
    rw [kvec, hlm]
  have hmat : matMul N M = matOne := by
    funext a b
    rw [matMul_apply, matOne_apply]
    have h' := congrFun (congrFun h a) b
    rwa [Matrix.mul_apply, Matrix.one_apply] at h'
  calc ∑ j, algebraMap L _ (N l j) * kvec D L M j
      = lmulVec (D.E.baseChange L) N (kvec D L M) l := (hlm N (kvec D L M) l).symm
    _ = lmulVec (D.E.baseChange L) N
          (lmulVec (D.E.baseChange L) M (Work.MotV.kleinCoord D L)) l := by rw [hkvec]
    _ = lmulVec (D.E.baseChange L) (matMul N M) (Work.MotV.kleinCoord D L) l := by
          rw [lmulVec_matMul]
    _ = lmulVec (D.E.baseChange L) matOne (Work.MotV.kleinCoord D L) l := by rw [hmat]
    _ = Work.MotV.kleinCoord D L l := by rw [lmulVec_matOne]

/-! ## §6 The Pfaffian equations for the shifted coordinates -/

/-- The shifted coordinates satisfy the Pfaffian equations. -/
theorem Tdiag_kleinP_kappaShift_eq_zero (hkl : ∀ (L : Type) [Field L] [Algebra 𝕜 L] (k : Fin 5),
      Work.MotK.kleinP (algebraMap 𝕜 _ D.a) (algebraMap 𝕜 _ D.b)
        (Work.MotV.kleinCoord D L) k = 0) (L : Type) [Field L] [Algebra 𝕜 L]
    (e : Fin 5 → Fin 5 → 𝕜) (M : Matrix (Fin 5) (Fin 5) L) (hM : PfaffStable D L M)
    (k : Fin 5) :
    Work.MotK.kleinP (algebraMap L (FunctionField (D.E.baseChange L)) (algebraMap 𝕜 L D.a))
      (algebraMap L _ (algebraMap 𝕜 L D.b)) (kappaShift D L e M) k = 0 := by
  obtain ⟨N, hN⟩ := pfaffStable_unlift D L M hM
  have hkvec : kvec D L M = fun i => ∑ j,
      algebraMap L (FunctionField (D.E.baseChange L)) (M i j) * Work.MotV.kleinCoord D L j := rfl
  have hk : Work.MotK.kleinP (algebraMap L _ (algebraMap 𝕜 L D.a))
      (algebraMap L _ (algebraMap 𝕜 L D.b)) (kvec D L M) k = 0 := by
    have h := hN (FunctionField (D.E.baseChange L)) (Work.MotV.kleinCoord D L) k
    rw [hkvec, h]
    refine Finset.sum_eq_zero fun j _ => ?_
    rw [← IsScalarTower.algebraMap_apply 𝕜 L (FunctionField (D.E.baseChange L)) D.a,
      ← IsScalarTower.algebraMap_apply 𝕜 L (FunctionField (D.E.baseChange L)) D.b, hkl L j,
      mul_zero]
  have h2 : kappaShift D L e M
      = fun i => (ell D L e (kvec D L M))⁻¹ * kvec D L M i := by
    funext i
    rw [kappaShift, div_eq_mul_inv, mul_comm]
  rw [h2, kleinP_smul, hk, mul_zero]

/-- The `wvec` of an invertible net-preserving matrix is a point of `E`. -/
theorem Tdiag_vwQuad_wvec_eq_zero (hab : D.a * D.b ≠ 0) (hkl : ∀ (L : Type) [Field L] [Algebra 𝕜 L] (k : Fin 5),
      Work.MotK.kleinP (algebraMap 𝕜 _ D.a) (algebraMap 𝕜 _ D.b)
        (Work.MotV.kleinCoord D L) k = 0) (hsp : ∃ e : Fin 5 → Fin 5 → 𝕜, ∀ (L : Type) [Field L] [Algebra 𝕜 L] (m : Fin 5),
      Work.MotV.kleinBas D L m =
        ∑ i, algebraMap L _ (algebraMap 𝕜 L (e m i)) * Work.MotV.kleinCoord D L i)
    (L : Type) [Field L] [Algebra 𝕜 L] (e : Fin 5 → Fin 5 → 𝕜)
    (he : ∀ m, Work.MotV.kleinBas D L m =
      ∑ i, algebraMap L (FunctionField (D.E.baseChange L)) (algebraMap 𝕜 L (e m i))
        * Work.MotV.kleinCoord D L i)
    (M : Matrix (Fin 5) (Fin 5) L) (hM : PfaffStable D L M)
    (hne : ell D L e (kvec D L M) ≠ 0) :
    vwQuad (algebraMap L (FunctionField (D.E.baseChange L)) (D.E.baseChange L).a₁)
      (algebraMap L _ (D.E.baseChange L).a₂) (algebraMap L _ (D.E.baseChange L).a₃)
      (algebraMap L _ (D.E.baseChange L).a₄) (algebraMap L _ (D.E.baseChange L).a₆)
      (wvec D L e M) = 0 := by
  have hdet := muMat_det_ne_zero D hab hkl hsp L
  have hdetF : ((muMat D L).map (algebraMap L (FunctionField (D.E.baseChange L)))).det ≠ 0 := by
    have h1 : ((muMat D L).map (algebraMap L (FunctionField (D.E.baseChange L)))).det
        = algebraMap L (FunctionField (D.E.baseChange L)) ((muMat D L).det) := by
      rw [← RingHom.mapMatrix_apply]
      exact (RingHom.map_det _ _).symm
    rw [h1]
    exact fun h => hdet ((algebraMap L (FunctionField (D.E.baseChange L))).injective
      (by simpa using h))
  refine Matrix.eq_zero_of_mulVec_eq_zero hdetF ?_
  have key : ∀ k, ∑ j, algebraMap L _ (muMat D L k j) *
      vwQuad (algebraMap L _ (D.E.baseChange L).a₁) (algebraMap L _ (D.E.baseChange L).a₂)
        (algebraMap L _ (D.E.baseChange L).a₃) (algebraMap L _ (D.E.baseChange L).a₄)
        (algebraMap L _ (D.E.baseChange L).a₆) (wvec D L e M) j = 0 := by
    intro k
    have h := reduce_alg D hkl L (FunctionField (D.E.baseChange L)) (wvec D L e M) k
    rw [Tdiag_sum_cL_wvec D L e he M, Tdiag_kleinP_kappaShift_eq_zero D hkl L e M hM k] at h
    simpa using h.symm
  funext k
  rw [Matrix.mulVec_apply, dotProduct]
  exact key k

/-- The first `wvec`-quadric: `wvec 3 = (wvec 1) ^ 2`. -/
theorem Tdiag_wvec_three (L : Type) [Field L] [Algebra 𝕜 L] (e : Fin 5 → Fin 5 → 𝕜)
    (M : Matrix (Fin 5) (Fin 5) L)
    (hvw : vwQuad (algebraMap L (FunctionField (D.E.baseChange L)) (D.E.baseChange L).a₁)
      (algebraMap L _ (D.E.baseChange L).a₂) (algebraMap L _ (D.E.baseChange L).a₃)
      (algebraMap L _ (D.E.baseChange L).a₄) (algebraMap L _ (D.E.baseChange L).a₆)
      (wvec D L e M) = 0)
    (hw0 : wvec D L e M 0 = 1) :
    wvec D L e M 3 = (wvec D L e M 1) ^ 2 := by
  have hv0 : wvec D L e M 0 * wvec D L e M 3 - (wvec D L e M 1) ^ 2 = 0 := by
    have h := congrFun hvw 0
    simpa only [vwQuad, Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.cons_val_succ,
      Matrix.cons_val, Pi.zero_apply] using h
  rw [hw0, one_mul] at hv0
  linear_combination (norm := ring_nf) hv0

/-- The second `wvec`-quadric: `wvec 4 = wvec 1 * wvec 2`. -/
theorem Tdiag_wvec_four (L : Type) [Field L] [Algebra 𝕜 L] (e : Fin 5 → Fin 5 → 𝕜)
    (M : Matrix (Fin 5) (Fin 5) L)
    (hvw : vwQuad (algebraMap L (FunctionField (D.E.baseChange L)) (D.E.baseChange L).a₁)
      (algebraMap L _ (D.E.baseChange L).a₂) (algebraMap L _ (D.E.baseChange L).a₃)
      (algebraMap L _ (D.E.baseChange L).a₄) (algebraMap L _ (D.E.baseChange L).a₆)
      (wvec D L e M) = 0)
    (hw0 : wvec D L e M 0 = 1) :
    wvec D L e M 4 = wvec D L e M 1 * wvec D L e M 2 := by
  have hv1 : wvec D L e M 0 * wvec D L e M 4 - wvec D L e M 1 * wvec D L e M 2 = 0 := by
    have h := congrFun hvw 1
    simpa only [vwQuad, Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.cons_val_succ,
      Matrix.cons_val, Pi.zero_apply] using h
  rw [hw0, one_mul] at hv1
  linear_combination (norm := ring_nf) hv1

/-- The Weierstrass equation for `(wvec 1, wvec 2)`. -/
theorem Tdiag_equation_wvec (L : Type) [Field L] [Algebra 𝕜 L] (e : Fin 5 → Fin 5 → 𝕜)
    (M : Matrix (Fin 5) (Fin 5) L)
    (hvw : vwQuad (algebraMap L (FunctionField (D.E.baseChange L)) (D.E.baseChange L).a₁)
      (algebraMap L _ (D.E.baseChange L).a₂) (algebraMap L _ (D.E.baseChange L).a₃)
      (algebraMap L _ (D.E.baseChange L).a₄) (algebraMap L _ (D.E.baseChange L).a₆)
      (wvec D L e M) = 0)
    (hw0 : wvec D L e M 0 = 1) :
    Equation (((D.E.baseChange L)).map (algebraMap L (FunctionField (D.E.baseChange L))))
      (wvec D L e M 1) (wvec D L e M 2) := by
  rw [equation_iff, WeierstrassCurve.map_a₁, WeierstrassCurve.map_a₂, WeierstrassCurve.map_a₃,
    WeierstrassCurve.map_a₄, WeierstrassCurve.map_a₆]
  exact relation_of_vwQuad_eq_zero hw0 hvw

/-! ## §7 Transcendence of the first `wvec`-coordinate -/

/-- **The first coordinate of `wvec` is transcendental over `L`.** -/
theorem Tdiag_transcendental_wvec (L : Type) [Field L] [Algebra 𝕜 L] (e : Fin 5 → Fin 5 → 𝕜)
    (he : ∀ m, Work.MotV.kleinBas D L m =
      ∑ i, algebraMap L (FunctionField (D.E.baseChange L)) (algebraMap 𝕜 L (e m i))
        * Work.MotV.kleinCoord D L i)
    (M M' : Matrix (Fin 5) (Fin 5) L) (hMM' : M * M' = 1)
    (hne : ell D L e (kvec D L M) ≠ 0)
    (hvw : vwQuad (algebraMap L (FunctionField (D.E.baseChange L)) (D.E.baseChange L).a₁)
      (algebraMap L _ (D.E.baseChange L).a₂) (algebraMap L _ (D.E.baseChange L).a₃)
      (algebraMap L _ (D.E.baseChange L).a₄) (algebraMap L _ (D.E.baseChange L).a₆)
      (wvec D L e M) = 0) :
    Transcendental L (wvec D L e M 1) := by
  show ¬ IsAlgebraic L (wvec D L e M 1)
  intro hU
  have hw0 : wvec D L e M 0 = 1 := Tdiag_wvec_zero D L e M hne
  have hw3 : wvec D L e M 3 = (wvec D L e M 1) ^ 2 := Tdiag_wvec_three D L e M hvw hw0
  have hw4 : wvec D L e M 4 = wvec D L e M 1 * wvec D L e M 2 := Tdiag_wvec_four D L e M hvw hw0
  have hEq := Tdiag_equation_wvec D L e M hvw hw0
  have hV : IsAlgebraic L (wvec D L e M 2) := isAlgebraic_of_equation _ hEq hU
  have hw_alg : ∀ m : Fin 5, IsAlgebraic L (wvec D L e M m) := by
    intro m
    fin_cases m
    · show IsAlgebraic L (wvec D L e M (0 : Fin 5)); rw [hw0]; exact isAlgebraic_one
    · show IsAlgebraic L (wvec D L e M (1 : Fin 5)); exact hU
    · show IsAlgebraic L (wvec D L e M (2 : Fin 5)); exact hV
    · show IsAlgebraic L (wvec D L e M (3 : Fin 5)); rw [hw3]; exact hU.pow 2
    · show IsAlgebraic L (wvec D L e M (4 : Fin 5)); rw [hw4]; exact hU.mul hV
  have hκ' : ∀ i, IsAlgebraic L (kappaShift D L e M i) := by
    intro i
    have h1 : kappaShift D L e M i
        = ∑ m, algebraMap L (FunctionField (D.E.baseChange L)) (cL D L i m)
            * wvec D L e M m := (congrFun (Tdiag_sum_cL_wvec D L e he M) i).symm
    rw [h1]
    exact Tdiag_isAlgebraic_finset_sum _ Finset.univ
      (fun m _ => (isAlgebraic_algebraMap _).mul (hw_alg m))
  have hB_alg : IsAlgebraic L (∑ i, algebraMap L _ (eL D L e 0 i)
      * (∑ p, algebraMap L _ (M' i p) * kappaShift D L e M p)) :=
    Tdiag_isAlgebraic_finset_sum _ Finset.univ (fun i _ =>
      (isAlgebraic_algebraMap _).mul (Tdiag_isAlgebraic_finset_sum _ Finset.univ
        (fun p _ => (isAlgebraic_algebraMap _).mul (hκ' p))))
  have hMM : M' * M = 1 := mul_eq_one_comm.mp hMM'
  have hsumM' : ∀ i, (∑ j, algebraMap L _ (M' i j) * kvec D L M j)
      = Work.MotV.kleinCoord D L i := fun i => Tdiag_sum_mat_mulVec D L M' M hMM i
  have hkvec : ∀ i, kvec D L M i = ell D L e (kvec D L M) * kappaShift D L e M i :=
    fun i => Tdiag_kvec_eq_ell_mul_kappaShift D L e M hne i
  have hell_mul : ell D L e (kvec D L M) * (∑ i, algebraMap L _ (eL D L e 0 i)
      * (∑ p, algebraMap L _ (M' i p) * kappaShift D L e M p)) = 1 := by
    have hb : (1 : FunctionField (D.E.baseChange L))
        = ∑ i, algebraMap L _ (eL D L e 0 i) * Work.MotV.kleinCoord D L i := by
      have h := basE_eq_eL_kleinCoord D L e he 0
      rw [basE_zero] at h
      exact h
    have hmain : ∑ i, algebraMap L _ (eL D L e 0 i) * Work.MotV.kleinCoord D L i
        = ell D L e (kvec D L M) * (∑ i, algebraMap L _ (eL D L e 0 i)
            * (∑ p, algebraMap L _ (M' i p) * kappaShift D L e M p)) := by
      calc ∑ i, algebraMap L _ (eL D L e 0 i) * Work.MotV.kleinCoord D L i
          = ∑ i, algebraMap L _ (eL D L e 0 i)
              * (∑ p, algebraMap L _ (M' i p) * kvec D L M p) := by
              refine Finset.sum_congr rfl fun i _ => ?_
              rw [← hsumM' i]
        _ = ∑ i, ∑ p, algebraMap L _ (eL D L e 0 i)
              * (algebraMap L _ (M' i p) * kvec D L M p) := by
              refine Finset.sum_congr rfl fun i _ => by rw [Finset.mul_sum]
        _ = ∑ i, ∑ p, algebraMap L _ (eL D L e 0 i)
              * (algebraMap L _ (M' i p)
                * (ell D L e (kvec D L M) * kappaShift D L e M p)) := by
              refine Finset.sum_congr rfl fun i _ => Finset.sum_congr rfl fun p _ => ?_
              rw [hkvec p]
        _ = ell D L e (kvec D L M) * ∑ i, ∑ p, algebraMap L _ (eL D L e 0 i)
              * (algebraMap L _ (M' i p) * kappaShift D L e M p) := by
              rw [Finset.mul_sum]
              refine Finset.sum_congr rfl fun i _ => ?_
              rw [Finset.mul_sum]
              refine Finset.sum_congr rfl fun p _ => ?_
              first | refl_ring1 | ring
        _ = ell D L e (kvec D L M) * (∑ i, algebraMap L _ (eL D L e 0 i)
              * (∑ p, algebraMap L _ (M' i p) * kappaShift D L e M p)) := by
              congr 1
              refine Finset.sum_congr rfl fun i _ => ?_
              rw [Finset.mul_sum]
    rw [hb]
    exact hmain.symm
  have hB_ne : (∑ i, algebraMap L _ (eL D L e 0 i)
      * (∑ p, algebraMap L _ (M' i p) * kappaShift D L e M p)) ≠ 0 := by
    intro h0
    rw [h0, mul_zero] at hell_mul
    exact one_ne_zero hell_mul.symm
  have hell_alg : IsAlgebraic L (ell D L e (kvec D L M)) := by
    have h := hell_mul
    rw [mul_comm] at h
    rw [eq_inv_of_mul_eq_one_right h]
    exact hB_alg.inv
  have hκ_alg : ∀ i, IsAlgebraic L (Work.MotV.kleinCoord D L i) := by
    intro i
    have hsplit : Work.MotV.kleinCoord D L i = ell D L e (kvec D L M)
        * (∑ p, algebraMap L _ (M' i p) * kappaShift D L e M p) := by
      calc Work.MotV.kleinCoord D L i
          = ∑ p, algebraMap L _ (M' i p) * kvec D L M p := (hsumM' i).symm
        _ = ∑ p, algebraMap L _ (M' i p)
              * (ell D L e (kvec D L M) * kappaShift D L e M p) := by
              refine Finset.sum_congr rfl fun p _ => ?_
              rw [hkvec p]
        _ = ell D L e (kvec D L M)
              * (∑ p, algebraMap L _ (M' i p) * kappaShift D L e M p) := by
              rw [Finset.mul_sum]
              refine Finset.sum_congr rfl fun p _ => by ring
    rw [hsplit]
    exact hell_alg.mul (Tdiag_isAlgebraic_finset_sum _ Finset.univ
      (fun p _ => (isAlgebraic_algebraMap _).mul (hκ' p)))
  have hx_alg : IsAlgebraic L (Work.MotC2.genX (D.E.baseChange L)) := by
    have hb := basE_eq_eL_kleinCoord D L e he 1
    rw [basE_one] at hb
    rw [← genX_eq (D.E.baseChange L), hb]
    exact Tdiag_isAlgebraic_finset_sum _ Finset.univ
      (fun i _ => (isAlgebraic_algebraMap _).mul (hκ_alg i))
  exact Work.MotC2.transcendental_genX (D.E.baseChange L) hx_alg

/-! ## §8 The algebra endomorphism attached to a net-preserving matrix -/

/-- A net-preserving matrix with an inverse produces an `L`-algebra endomorphism of `L(E)`
sending the Klein coordinates to the shifted ones. -/
theorem exists_algHom_shift (hab : D.a * D.b ≠ 0) (hkl : ∀ (L : Type) [Field L] [Algebra 𝕜 L] (k : Fin 5),
      Work.MotK.kleinP (algebraMap 𝕜 _ D.a) (algebraMap 𝕜 _ D.b)
        (Work.MotV.kleinCoord D L) k = 0) (hsp : ∃ e : Fin 5 → Fin 5 → 𝕜, ∀ (L : Type) [Field L] [Algebra 𝕜 L] (m : Fin 5),
      Work.MotV.kleinBas D L m =
        ∑ i, algebraMap L _ (algebraMap 𝕜 L (e m i)) * Work.MotV.kleinCoord D L i)
    (L : Type) [Field L] [Algebra 𝕜 L] (e : Fin 5 → Fin 5 → 𝕜)
    (he : ∀ m, Work.MotV.kleinBas D L m =
      ∑ i, algebraMap L (FunctionField (D.E.baseChange L)) (algebraMap 𝕜 L (e m i))
        * Work.MotV.kleinCoord D L i)
    (M M' : Matrix (Fin 5) (Fin 5) L) (hMM' : M * M' = 1) (hM : PfaffStable D L M) :
    ∃ σ : FunctionField (D.E.baseChange L) →ₐ[L] FunctionField (D.E.baseChange L),
      ∀ i, σ (Work.MotV.kleinCoord D L i) = kappaShift D L e M i := by
  have hne : ell D L e (kvec D L M) ≠ 0 := Tdiag_ell_kvec_ne_zero D L e he M M' hMM'
  have hvw : vwQuad (algebraMap L _ (D.E.baseChange L).a₁)
      (algebraMap L _ (D.E.baseChange L).a₂) (algebraMap L _ (D.E.baseChange L).a₃)
      (algebraMap L _ (D.E.baseChange L).a₄) (algebraMap L _ (D.E.baseChange L).a₆)
      (wvec D L e M) = 0 := Tdiag_vwQuad_wvec_eq_zero D hab hkl hsp L e he M hM hne
  have hw0 : wvec D L e M 0 = 1 := Tdiag_wvec_zero D L e M hne
  have hw3 : wvec D L e M 3 = (wvec D L e M 1) ^ 2 := Tdiag_wvec_three D L e M hvw hw0
  have hw4 : wvec D L e M 4 = wvec D L e M 1 * wvec D L e M 2 := Tdiag_wvec_four D L e M hvw hw0
  have hEq := Tdiag_equation_wvec D L e M hvw hw0
  have htr : Transcendental L (wvec D L e M 1) :=
    Tdiag_transcendental_wvec D L e he M M' hMM' hne hvw
  obtain ⟨σ, hσx, hσy⟩ :=
    exists_algHom_of_point (D.E.baseChange L) (wvec D L e M 1) (wvec D L e M 2) hEq htr
  refine ⟨σ, ?_⟩
  have hbas : ∀ m, σ (basE (D.E.baseChange L) m) = wvec D L e M m := by
    intro m
    fin_cases m
    · show σ (basE (D.E.baseChange L) (0 : Fin 5)) = wvec D L e M (0 : Fin 5)
      rw [basE_zero, map_one, hw0]
    · show σ (basE (D.E.baseChange L) (1 : Fin 5)) = wvec D L e M (1 : Fin 5)
      rw [basE_one, hσx]
    · show σ (basE (D.E.baseChange L) (2 : Fin 5)) = wvec D L e M (2 : Fin 5)
      rw [basE_two, hσy]
    · show σ (basE (D.E.baseChange L) (3 : Fin 5)) = wvec D L e M (3 : Fin 5)
      rw [basE_three, map_pow, hσx]
      exact hw3.symm
    · show σ (basE (D.E.baseChange L) (4 : Fin 5)) = wvec D L e M (4 : Fin 5)
      rw [basE_four, map_mul, hσx, hσy]
      exact hw4.symm
  intro i
  calc σ (Work.MotV.kleinCoord D L i)
      = σ (∑ m, algebraMap L _ (cL D L i m) * basE (D.E.baseChange L) m) := by
          rw [kleinCoord_eq_cL]
    _ = ∑ m, algebraMap L _ (cL D L i m) * σ (basE (D.E.baseChange L) m) := by
          rw [map_sum]
          exact Finset.sum_congr rfl fun m _ => by rw [map_mul, AlgHom.commutes]
    _ = ∑ m, algebraMap L _ (cL D L i m) * wvec D L e M m := by
          exact Finset.sum_congr rfl fun m _ => by rw [hbas m]
    _ = kappaShift D L e M i := by rw [← congrFun (Tdiag_sum_cL_wvec D L e he M) i]

/-! ## §9 The automorphism attached to an invertible net-preserving pair -/

/-- **Node TDG-M.**  An invertible projectivity `M` of `ℙ⁴` preserving the Pfaffian net (with
inverse `M'`) induces an `L`-algebra automorphism of `L(E)` acting on the Klein ratios as `M`
does. -/
theorem projAut_general (hab : D.a * D.b ≠ 0) (hkl : ∀ (L : Type) [Field L] [Algebra 𝕜 L] (k : Fin 5),
      Work.MotK.kleinP (algebraMap 𝕜 _ D.a) (algebraMap 𝕜 _ D.b)
        (Work.MotV.kleinCoord D L) k = 0) (hsp : ∃ e : Fin 5 → Fin 5 → 𝕜, ∀ (L : Type) [Field L] [Algebra 𝕜 L] (m : Fin 5),
      Work.MotV.kleinBas D L m =
        ∑ i, algebraMap L _ (algebraMap 𝕜 L (e m i)) * Work.MotV.kleinCoord D L i)
    (L : Type) [Field L] [Algebra 𝕜 L] (M M' : Matrix (Fin 5) (Fin 5) L) (hMM' : M * M' = 1)
    (hM : PfaffStable D L M) (hM' : PfaffStable D L M') :
    ∃ σ : FunctionField (D.E.baseChange L) ≃ₐ[L] FunctionField (D.E.baseChange L),
      ∀ i, σ (Work.MotV.kleinCoord D L i / Work.MotV.kleinCoord D L 0) =
        (∑ j, algebraMap L (FunctionField (D.E.baseChange L)) (M i j)
            * Work.MotV.kleinCoord D L j) /
          (∑ j, algebraMap L _ (M 0 j) * Work.MotV.kleinCoord D L j) := by
  obtain ⟨e, he⟩ := hsp
  have hMM : M' * M = 1 := mul_eq_one_comm.mp hMM'
  have heL : ∀ m, Work.MotV.kleinBas D L m =
      ∑ i, algebraMap L _ (algebraMap 𝕜 L (e m i)) * Work.MotV.kleinCoord D L i :=
    fun m => he L m
  have hsp' : ∃ e : Fin 5 → Fin 5 → 𝕜, ∀ (L : Type) [Field L] [Algebra 𝕜 L] (m : Fin 5),
      Work.MotV.kleinBas D L m =
        ∑ i, algebraMap L _ (algebraMap 𝕜 L (e m i)) * Work.MotV.kleinCoord D L i := ⟨e, he⟩
  obtain ⟨σM, hσM⟩ := exists_algHom_shift D hab hkl hsp' L e heL M M' hMM' hM
  obtain ⟨σM', hσM'⟩ := exists_algHom_shift D hab hkl hsp' L e heL M' M hMM hM'
  have hne : ell D L e (kvec D L M) ≠ 0 := Tdiag_ell_kvec_ne_zero D L e heL M M' hMM'
  have hne' : ell D L e (kvec D L M') ≠ 0 := Tdiag_ell_kvec_ne_zero D L e heL M' M hMM
  have h1gen : ∀ j : Fin 5, σM' (kvec D L M j)
      = (ell D L e (kvec D L M'))⁻¹ * Work.MotV.kleinCoord D L j := by
    intro j
    calc σM' (kvec D L M j)
        = ∑ p, algebraMap L _ (M j p) * kappaShift D L e M' p := by
            rw [kvec, map_sum]
            exact Finset.sum_congr rfl fun p _ => by
              rw [map_mul, AlgHom.commutes, hσM' p]
      _ = ∑ p, algebraMap L _ (M j p) * kvec D L M' p / ell D L e (kvec D L M') := by
            refine Finset.sum_congr rfl fun p _ => ?_
            rw [kappaShift, ← mul_div_assoc]
      _ = (∑ p, algebraMap L _ (M j p) * kvec D L M' p) / ell D L e (kvec D L M') := by
            rw [Finset.sum_div]
      _ = Work.MotV.kleinCoord D L j / ell D L e (kvec D L M') := by
            rw [Tdiag_sum_mat_mulVec D L M M' hMM' j]
      _ = (ell D L e (kvec D L M'))⁻¹ * Work.MotV.kleinCoord D L j := by
            rw [div_eq_inv_mul]
  have h2 : σM' (ell D L e (kvec D L M)) = (ell D L e (kvec D L M'))⁻¹ := by
    have hterm : ∀ i, σM' (algebraMap L _ (eL D L e 0 i) * kvec D L M i)
        = algebraMap L _ (eL D L e 0 i)
          * ((ell D L e (kvec D L M'))⁻¹ * Work.MotV.kleinCoord D L i) := by
      intro i
      rw [map_mul, AlgHom.commutes, h1gen i]
    have hterm2 : ∀ i, algebraMap L _ (eL D L e 0 i)
          * ((ell D L e (kvec D L M'))⁻¹ * Work.MotV.kleinCoord D L i)
        = (ell D L e (kvec D L M'))⁻¹
          * (algebraMap L _ (eL D L e 0 i) * Work.MotV.kleinCoord D L i) :=
      fun i => by ring
    rw [ell, map_sum, Finset.sum_congr rfl (fun i _ => hterm i),
      Finset.sum_congr rfl (fun i _ => hterm2 i), ← Finset.mul_sum]
    have hb : (∑ i, algebraMap L _ (eL D L e 0 i) * Work.MotV.kleinCoord D L i) = 1 := by
      have h := basE_eq_eL_kleinCoord D L e heL 0
      rw [basE_zero] at h
      exact h.symm
    rw [hb, mul_one]
  have hfixM : ∀ i, (σM'.comp σM) (Work.MotV.kleinCoord D L i)
      = Work.MotV.kleinCoord D L i := by
    intro i
    rw [AlgHom.comp_apply, hσM i, kappaShift, map_div₀, h1gen i, h2]
    have hx : (ell D L e (kvec D L M'))⁻¹ ≠ 0 := inv_ne_zero hne'
    rw [div_eq_iff hx, mul_comm]
  have h1gen' : ∀ j : Fin 5, σM (kvec D L M' j)
      = (ell D L e (kvec D L M))⁻¹ * Work.MotV.kleinCoord D L j := by
    intro j
    calc σM (kvec D L M' j)
        = ∑ p, algebraMap L _ (M' j p) * kappaShift D L e M p := by
            rw [kvec, map_sum]
            exact Finset.sum_congr rfl fun p _ => by
              rw [map_mul, AlgHom.commutes, hσM p]
      _ = ∑ p, algebraMap L _ (M' j p) * kvec D L M p / ell D L e (kvec D L M) := by
            refine Finset.sum_congr rfl fun p _ => ?_
            rw [kappaShift, ← mul_div_assoc]
      _ = (∑ p, algebraMap L _ (M' j p) * kvec D L M p) / ell D L e (kvec D L M) := by
            rw [Finset.sum_div]
      _ = Work.MotV.kleinCoord D L j / ell D L e (kvec D L M) := by
            rw [Tdiag_sum_mat_mulVec D L M' M hMM j]
      _ = (ell D L e (kvec D L M))⁻¹ * Work.MotV.kleinCoord D L j := by
            rw [div_eq_inv_mul]
  have h2' : σM (ell D L e (kvec D L M')) = (ell D L e (kvec D L M))⁻¹ := by
    have hterm : ∀ i, σM (algebraMap L _ (eL D L e 0 i) * kvec D L M' i)
        = algebraMap L _ (eL D L e 0 i)
          * ((ell D L e (kvec D L M))⁻¹ * Work.MotV.kleinCoord D L i) := by
      intro i
      rw [map_mul, AlgHom.commutes, h1gen' i]
    have hterm2 : ∀ i, algebraMap L _ (eL D L e 0 i)
          * ((ell D L e (kvec D L M))⁻¹ * Work.MotV.kleinCoord D L i)
        = (ell D L e (kvec D L M))⁻¹
          * (algebraMap L _ (eL D L e 0 i) * Work.MotV.kleinCoord D L i) :=
      fun i => by ring
    rw [ell, map_sum, Finset.sum_congr rfl (fun i _ => hterm i),
      Finset.sum_congr rfl (fun i _ => hterm2 i), ← Finset.mul_sum]
    have hb : (∑ i, algebraMap L _ (eL D L e 0 i) * Work.MotV.kleinCoord D L i) = 1 := by
      have h := basE_eq_eL_kleinCoord D L e heL 0
      rw [basE_zero] at h
      exact h.symm
    rw [hb, mul_one]
  have hfixM' : ∀ i, (σM.comp σM') (Work.MotV.kleinCoord D L i)
      = Work.MotV.kleinCoord D L i := by
    intro i
    rw [AlgHom.comp_apply, hσM' i, kappaShift, map_div₀, h1gen' i, h2']
    have hx : (ell D L e (kvec D L M))⁻¹ ≠ 0 := inv_ne_zero hne
    rw [div_eq_iff hx, mul_comm]
  have hcomp1 : σM'.comp σM = AlgHom.id L (FunctionField (D.E.baseChange L)) := by
    refine algHom_eq_id_of_kleinCoord_ratio D L e heL _ fun i => ?_
    rw [map_div₀, hfixM i, hfixM 0]
  have hcomp2 : σM.comp σM' = AlgHom.id L (FunctionField (D.E.baseChange L)) := by
    refine algHom_eq_id_of_kleinCoord_ratio D L e heL _ fun i => ?_
    rw [map_div₀, hfixM' i, hfixM' 0]
  refine ⟨AlgEquiv.ofAlgHom σM σM' hcomp2 hcomp1, ?_⟩
  intro i
  show σM (Work.MotV.kleinCoord D L i / Work.MotV.kleinCoord D L 0) = _
  rw [map_div₀, hσM i, hσM 0]
  show (kvec D L M i / ell D L e (kvec D L M))
      / (kvec D L M 0 / ell D L e (kvec D L M)) = kvec D L M i / kvec D L M 0
  exact div_div_div_cancel_right₀ hne _ _

end Main

end

end Work.MotTDG
