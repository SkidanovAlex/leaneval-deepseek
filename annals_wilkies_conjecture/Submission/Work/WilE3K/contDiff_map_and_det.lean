/-
  annals_wilkies_conjecture, AREA E3K.

  `Work.WilE3K.contDiff_map_and_det`: the system map `E.map` of a lifted exp/`arctan` system
  (`Submission.Work.WilE3K.ET`) is `C²` on `ℝ^{N+1}`, and the determinant of its Fréchet
  derivative at `z` is the determinant of the symbolic Jacobian `E.jac z` (the matrix whose
  `tan` rows are the gradients of the `arctan` equations and whose other rows are the evaluated
  symbolic derivatives `E.dPoly c (E.G i)` of the exp-affine equations).

  The content is the two derivative computations:

  * `ETData.tanFun_hasFDerivAt` — `∂(arctan (z (tanCoord j)) - lin j z) = ∑ c, dTanFun j z c • proj c`,
    which is `Real.hasDerivAt_arctan` composed with the projection plus the linearity of `lin j`
    (the coefficient bookkeeping is `ETData.sum_dTanFun`);
  * `ETData.evP_hasFDerivAt` — the EA-chain derivative theorem `Work.WilE9.EaD.eaD_hasFDerivAt`
    transported along the vocabulary bridge `E.evalPoly = eaEval E.toChain`,
    `E.dPoly = eaD E.toChain` of `Submission.Work.WilE3K.ContAux`.

  Smoothness (`ETData.contDiff_map`) is the coordinatewise statement `contDiff_pi` together with
  `contDiff_arctan`, `ContDiff.sum` (for `lin`) and `eaEval_contDiff`.

  The determinant is `det_fderiv_eq`: the determinant of the Fréchet derivative of a map
  `ℝ^m → ℝ^m` is the determinant of the matrix of its directional derivatives in the standard
  basis, which is exactly `E.jac z` (`ETData.map_hasFDerivAt`).
-/
import Mathlib
import Submission.Work.WilE3K.ET
import Submission.Work.WilE3K.ContAux
import Submission.Work.WilE9.EaD.eaD_hasFDerivAt
import Submission.Work.WilE9.EaD.eaEval_contDiff

set_option autoImplicit false
set_option maxHeartbeats 1000000
noncomputable section
open Classical Topology Filter
namespace Work.WilE3K
open WilkiesConjecture WilkiesDesign WilkiesDesign.E

variable {N rt n re : ℕ}

/-! ## §0. Two general calculus helpers -/

/-- Evaluating the continuous linear map `∑ i, f i • proj i` on a vector is the sum
`∑ i, f i * v i`. -/
private lemma sum_smul_proj_apply {σ : Type*} [Fintype σ] (f v : σ → ℝ) :
    (∑ i, f i • (ContinuousLinearMap.proj i : (σ → ℝ) →L[ℝ] ℝ)) v = ∑ i, f i * v i := by
  simp only [ContinuousLinearMap.sum_apply, ContinuousLinearMap.smul_apply,
    ContinuousLinearMap.proj_apply, smul_eq_mul]

/-- The matrix of a continuous linear endomorphism of `ℝ^m` in the standard basis is the matrix
of its values on the vectors `Pi.single j 1`. -/
private theorem toMatrix_fderiv_eq {m : ℕ} (Φ : (Fin m → ℝ) → (Fin m → ℝ)) (z : Fin m → ℝ) :
    (LinearMap.toMatrix (Pi.basisFun ℝ (Fin m)) (Pi.basisFun ℝ (Fin m))) (fderiv ℝ Φ z).toLinearMap
      = Matrix.of fun i j => fderiv ℝ Φ z (Pi.single j 1) i := by
  ext i j
  rw [LinearMap.toMatrix_apply, Pi.basisFun_repr, Pi.basisFun_apply]
  rfl

/-- The determinant of the Fréchet derivative of a map `ℝ^m → ℝ^m` is the determinant of the
matrix of its directional derivatives in the standard basis. -/
private theorem det_fderiv_eq {m : ℕ} (Φ : (Fin m → ℝ) → (Fin m → ℝ)) (z : Fin m → ℝ) :
    (fderiv ℝ Φ z).det = (Matrix.of fun i j => fderiv ℝ Φ z (Pi.single j 1) i).det := by
  rw [show (fderiv ℝ Φ z).det = LinearMap.det (fderiv ℝ Φ z).toLinearMap from rfl,
    ← LinearMap.det_toMatrix (Pi.basisFun ℝ (Fin m)) (fderiv ℝ Φ z).toLinearMap,
    toMatrix_fderiv_eq]

namespace ETData

variable (E : ETData N rt n re)

/-! ## §1. The derivative of the exp-affine equations -/

/-- Each exp-affine equation `E.evP i` has derivative `∑ c, E.evalPoly (E.dPoly c (E.G i)) z • proj c`:
the EA-chain derivative theorem `eaD_hasFDerivAt`, along the vocabulary bridge of `ContAux`. -/
theorem evP_hasFDerivAt (i : Fin n) (z : Fin (N + 1) → ℝ) :
    HasFDerivAt (E.evP i)
      (∑ c, E.evalPoly (E.dPoly c (E.G i)) z •
        (ContinuousLinearMap.proj c : (Fin (N + 1) → ℝ) →L[ℝ] ℝ)) z := by
  have h := Work.WilE9.EaD.eaD_hasFDerivAt E.toChain (E.G i) z
  have hfun : (fun w : Fin (N + 1) → ℝ => eaEval E.toChain (E.G i) w) = E.evP i := by
    funext w; exact (E.evalPoly_eq_eaEval (E.G i) w).symm
  rw [hfun] at h
  refine h.congr_fderiv ?_
  apply Finset.sum_congr rfl
  intro c _
  rw [← ETData.evalPoly_eq_eaEval, ← ETData.dPoly_eq_eaD]

/-! ## §2. The derivative of the `arctan` equations -/

/-- The coefficients of the derivative of `E.tanFun j`, read off coordinatewise. -/
theorem sum_dTanFun (j : Fin rt) (z : Fin (N + 1) → ℝ) (v : Fin (N + 1) → ℝ) :
    (∑ c, E.dTanFun j z c * v c)
      = (1 / (1 + z (E.tanCoord j) ^ 2)) * v (E.tanCoord j)
        - ∑ i : Fin n, E.lam j i * v (E.freeCoord i) := by
  rw [← Finset.sum_filter_add_sum_filter_not (s := Finset.univ)
      (p := fun c : Fin (N + 1) => (c : ℕ) < rt) (f := fun c => E.dTanFun j z c * v c)]
  have h1 : ∑ c ∈ Finset.univ.filter (fun c : Fin (N + 1) => (c : ℕ) < rt),
      E.dTanFun j z c * v c = (1 / (1 + z (E.tanCoord j) ^ 2)) * v (E.tanCoord j) := by
    have hzero : ∀ b ∈ Finset.univ.filter (fun c : Fin (N + 1) => (c : ℕ) < rt),
        b ≠ E.tanCoord j → E.dTanFun j z b * v b = 0 := by
      intro b hb hne
      simp only [Finset.mem_filter, Finset.mem_univ, true_and] at hb
      rw [ETData.dTanFun, dif_pos hb, if_neg hne, zero_mul]
    have hmem : E.tanCoord j ∈ Finset.univ.filter (fun c : Fin (N + 1) => (c : ℕ) < rt) := by
      simp only [Finset.mem_filter, Finset.mem_univ, true_and, ETData.tanCoord_val]
      exact j.isLt
    rw [Finset.sum_eq_single (E.tanCoord j) hzero (fun h => absurd hmem h)]
    simp
  have h2 : ∑ c ∈ Finset.univ.filter (fun c : Fin (N + 1) => ¬ (c : ℕ) < rt),
      E.dTanFun j z c * v c = - ∑ i : Fin n, E.lam j i * v (E.freeCoord i) := by
    rw [E.filter_not_lt_eq_image_freeCoord]
    rw [Finset.sum_image (E.freeCoord_injective.injOn)]
    rw [Finset.sum_congr rfl (fun i _ => by rw [E.dTanFun_free, neg_mul]),
      Finset.sum_neg_distrib]
  rw [h1, h2]
  ring

/-- The `j`-th `arctan` equation has derivative `∑ c, E.dTanFun j z c • proj c`. -/
theorem tanFun_hasFDerivAt (j : Fin rt) (z : Fin (N + 1) → ℝ) :
    HasFDerivAt (E.tanFun j)
      (∑ c, E.dTanFun j z c •
        (ContinuousLinearMap.proj c : (Fin (N + 1) → ℝ) →L[ℝ] ℝ)) z := by
  have hArctan : HasFDerivAt (fun w : Fin (N + 1) → ℝ => Real.arctan (w (E.tanCoord j)))
      ((1 / (1 + z (E.tanCoord j) ^ 2)) •
        (ContinuousLinearMap.proj (E.tanCoord j) : (Fin (N + 1) → ℝ) →L[ℝ] ℝ)) z := by
    have h1 : HasFDerivAt (fun w : Fin (N + 1) → ℝ => w (E.tanCoord j))
        (ContinuousLinearMap.proj (E.tanCoord j) : (Fin (N + 1) → ℝ) →L[ℝ] ℝ) z :=
      hasFDerivAt_apply (E.tanCoord j) z
    exact (Real.hasDerivAt_arctan (z (E.tanCoord j))).comp_hasFDerivAt z h1
  have hLin : HasFDerivAt (E.lin j)
      (∑ i : Fin n, E.lam j i •
        (ContinuousLinearMap.proj (E.freeCoord i) : (Fin (N + 1) → ℝ) →L[ℝ] ℝ)) z := by
    have h' : HasFDerivAt (fun w : Fin (N + 1) → ℝ =>
        (∑ i : Fin n, E.lam j i •
          (ContinuousLinearMap.proj (E.freeCoord i) : (Fin (N + 1) → ℝ) →L[ℝ] ℝ)) w + E.mu j)
        (∑ i : Fin n, E.lam j i •
          (ContinuousLinearMap.proj (E.freeCoord i) : (Fin (N + 1) → ℝ) →L[ℝ] ℝ)) z :=
      (ContinuousLinearMap.hasFDerivAt (∑ i : Fin n, E.lam j i •
        (ContinuousLinearMap.proj (E.freeCoord i) : (Fin (N + 1) → ℝ) →L[ℝ] ℝ))).add_const (E.mu j)
    have hfun : (fun w : Fin (N + 1) → ℝ =>
        (∑ i : Fin n, E.lam j i •
          (ContinuousLinearMap.proj (E.freeCoord i) : (Fin (N + 1) → ℝ) →L[ℝ] ℝ)) w + E.mu j)
        = E.lin j := by
      funext w
      simp only [ETData.lin, ContinuousLinearMap.sum_apply, ContinuousLinearMap.smul_apply,
        ContinuousLinearMap.proj_apply, smul_eq_mul]
    rw [hfun] at h'
    exact h'
  refine (hArctan.sub hLin).congr_fderiv ?_
  ext v
  rw [sum_smul_proj_apply, E.sum_dTanFun j z v]
  simp only [ContinuousLinearMap.sub_apply, ContinuousLinearMap.smul_apply,
    ContinuousLinearMap.proj_apply, ContinuousLinearMap.sum_apply, smul_eq_mul]

/-! ## §3. Smoothness of the system map -/

theorem contDiff_lin (j : Fin rt) : ContDiff ℝ ⊤ (E.lin j) := by
  rw [show E.lin j = fun z : Fin (N + 1) → ℝ =>
      (∑ i : Fin n, E.lam j i * z (E.freeCoord i)) + E.mu j from by
    funext z; rw [ETData.lin]]
  exact (ContDiff.sum (fun i _ => contDiff_const.mul (contDiff_apply ℝ ℝ (E.freeCoord i)))).add
    contDiff_const

theorem contDiff_tanFun (j : Fin rt) : ContDiff ℝ ⊤ (E.tanFun j) := by
  exact (Real.contDiff_arctan.comp (contDiff_apply ℝ ℝ (E.tanCoord j))).sub (E.contDiff_lin j)

theorem contDiff_evP (i : Fin n) : ContDiff ℝ ⊤ (E.evP i) := by
  rw [show E.evP i = fun z : Fin (N + 1) → ℝ => eaEval E.toChain (E.G i) z from by
    funext z; exact E.evalPoly_eq_eaEval (E.G i) z]
  exact Work.WilE9.EaD.eaEval_contDiff E.toChain (E.G i)

/-- The system map of the lifted system is `C²`. -/
theorem contDiff_map : ContDiff ℝ 2 E.map := by
  rw [contDiff_pi]
  intro i
  by_cases hi : (i : ℕ) < rt
  · have hfun : (fun z => E.map z i) = E.tanFun (E.tanIndex i hi) := by
      funext z; simp only [ETData.map, dif_pos hi]
    rw [hfun]
    exact (E.contDiff_tanFun (E.tanIndex i hi)).of_le le_top
  · have hfun : (fun z => E.map z i) = E.evP (E.freeIndex i (not_lt.mp hi)) := by
      funext z; simp only [ETData.map, dif_neg hi]
    rw [hfun]
    exact (E.contDiff_evP (E.freeIndex i (not_lt.mp hi))).of_le le_top

/-! ## §4. The Jacobian determinant -/

/-- The `i`-th coordinate of the system map has the `i`-th row of `E.jac z` as its derivative. -/
theorem map_coord_hasFDerivAt (i : Fin (N + 1)) (z : Fin (N + 1) → ℝ) :
    HasFDerivAt (fun w => E.map w i)
      (∑ c, E.jac z i c • (ContinuousLinearMap.proj c : (Fin (N + 1) → ℝ) →L[ℝ] ℝ)) z := by
  by_cases hi : (i : ℕ) < rt
  · have hfun : (fun w => E.map w i) = E.tanFun (E.tanIndex i hi) := by
      funext w; simp only [ETData.map, dif_pos hi]
    rw [hfun]
    refine (E.tanFun_hasFDerivAt (E.tanIndex i hi) z).congr_fderiv ?_
    apply Finset.sum_congr rfl
    intro c _
    rw [show E.jac z i c = E.jac z (E.tanCoord (E.tanIndex i hi)) c from by
      rw [E.tanCoord_tanIndex]]
    rw [E.jac_tan]
  · have hfun : (fun w => E.map w i) = E.evP (E.freeIndex i (not_lt.mp hi)) := by
      funext w; simp only [ETData.map, dif_neg hi]
    rw [hfun]
    refine (E.evP_hasFDerivAt (E.freeIndex i (not_lt.mp hi)) z).congr_fderiv ?_
    apply Finset.sum_congr rfl
    intro c _
    rw [show E.jac z i c = E.jac z (E.freeCoord (E.freeIndex i (not_lt.mp hi))) c from by
      rw [E.freeCoord_freeIndex]]
    rw [E.jac_free]

/-- The Fréchet derivative of the system map is the continuous linear map whose rows are the
rows of the symbolic Jacobian. -/
theorem map_hasFDerivAt (z : Fin (N + 1) → ℝ) :
    HasFDerivAt E.map (ContinuousLinearMap.pi (fun i =>
      ∑ c, E.jac z i c • (ContinuousLinearMap.proj c : (Fin (N + 1) → ℝ) →L[ℝ] ℝ))) z := by
  refine (hasFDerivAt_pi
    (φ := fun (i : Fin (N + 1)) (x : Fin (N + 1) → ℝ) => E.map x i)
    (φ' := fun i => ∑ c, E.jac z i c •
      (ContinuousLinearMap.proj c : (Fin (N + 1) → ℝ) →L[ℝ] ℝ))).mpr ?_
  intro i
  exact E.map_coord_hasFDerivAt i z

/-- The determinant of the Fréchet derivative of the system map is the determinant of the
symbolic Jacobian `E.jac z`. -/
theorem fderiv_map_det (z : Fin (N + 1) → ℝ) :
    (fderiv ℝ E.map z).det = (E.jac z).det := by
  rw [det_fderiv_eq E.map z]
  apply congrArg Matrix.det
  ext i j
  simp only [Matrix.of_apply]
  rw [(E.map_hasFDerivAt z).fderiv]
  simp only [ContinuousLinearMap.pi_apply]
  rw [sum_smul_proj_apply]
  have hterm : ∀ c, E.jac z i c * (Pi.single j (1 : ℝ) : Fin (N + 1) → ℝ) c
      = (if c = j then E.jac z i c else 0) := by
    intro c
    by_cases h : c = j
    · subst h; rw [Pi.single_eq_same, mul_one, if_pos rfl]
    · rw [Pi.single_eq_of_ne h, mul_zero, if_neg h]
  rw [Finset.sum_congr rfl (fun c _ => hterm c), Finset.sum_ite_eq']
  simp

end ETData

theorem contDiff_map_and_det {N rt n re : ℕ} (E : Work.WilE3K.ETData N rt n re) :
    ContDiff ℝ 2 E.map ∧ ∀ z : Fin (N + 1) → ℝ, (fderiv ℝ E.map z).det = (E.jac z).det :=
  ⟨E.contDiff_map, E.fderiv_map_det⟩

end Work.WilE3K
