import Mathlib
import Submission.Work.KT.Defs
import Submission.Work.KT.Basic
import Submission.Work.KT.diskQuot
import Submission.Work.KT.Dim2.Transfer
import Submission.Work.KT.D2.PsiRankOne
import Submission.Work.KT.Dim2.hopf_relation
import Submission.Work.KT.Fund.twoByTwo_idem_of_trace_det
import Submission.Work.KT.K0map.map_comp
import Submission.Work.KT.Rank.mvN_one_rank_v2
import Submission.Work.KT.hk_k0_eq_diff
import Submission.Work.KT.Dim2.mvN_similar_zero
import Submission.Work.KT.Dim2.idem_conj_of_contractible
import Submission.Work.KT.homotopy_inv
import Submission.Work.KT.K0map.map_id

set_option maxHeartbeats 1000000
set_option synthInstance.maxHeartbeats 400000

namespace Work.KT

noncomputable section

open Matrix

/-- The image of a block sum under a ring homomorphism. -/
lemma Mat.map_sumK {A B : Type} [Ring A] [Ring B] (φ : A →+* B) (p q : Mat A) :
    (p.sum q).map φ = (p.map φ).sum (q.map φ) := by
  unfold Mat.sum Mat.map
  simp only [Sigma.mk.injEq, heq_eq_eq, true_and]
  ext i j
  simp only [Matrix.map_apply, Matrix.reindex_apply, Matrix.submatrix_apply]
  rcases finSumFinEquiv.symm i with a | a <;> rcases finSumFinEquiv.symm j with b | b <;> simp

/-- The image of a Kronecker product under a ring homomorphism. -/
lemma Mat.map_kronK {A B : Type} [Ring A] [Ring B] (φ : A →+* B) (p q : Mat A) :
    (p.kron q).map φ = (p.map φ).kron (q.map φ) := by
  obtain ⟨n, M⟩ := p
  obtain ⟨k, N⟩ := q
  change (⟨n * k, (kronMat M N).map φ⟩ : Mat B) = ⟨n * k, kronMat (M.map φ) (N.map φ)⟩
  congr 1
  ext i j
  simp [kronMat, Matrix.reindex_apply, Matrix.map_apply, Matrix.kroneckerMap_apply]


namespace D2

open Matrix

/-! ## The Hopf idempotent in the disc model `Kpair ℝ²` -/

/-- The `i`-th Euclidean coordinate on the model sphere `S²` (a function on `ModelSphere 2`). -/
def mcE (i : Fin 2) : C(ModelSphere 2, ℂ) :=
  ⟨fun x => (((x.fst) i : ℝ) : ℂ), by
    exact Complex.continuous_ofReal.comp
      ((EuclideanSpace.proj i).continuous.comp (WithLp.fstL 2 ℝ (Euc 2) ℝ).continuous)⟩

/-- The last coordinate on the model sphere `S²`. -/
def mcR : C(ModelSphere 2, ℂ) :=
  ⟨fun x => ((x.snd : ℝ) : ℂ), by
    exact Complex.continuous_ofReal.comp (WithLp.sndL 2 ℝ (Euc 2) ℝ).continuous⟩

/-- The first two coordinates on `S²`, as functions on the sphere. -/
def scE (i : Fin 2) : C(Sph (ModelSphere 2), ℂ) :=
  (mcE i).comp ⟨Subtype.val, continuous_subtype_val⟩

/-- The third coordinate on `S²`, as a function on the sphere. -/
def scR : C(Sph (ModelSphere 2), ℂ) :=
  mcR.comp ⟨Subtype.val, continuous_subtype_val⟩

/-- The quotient map `D² → S²` collapsing the boundary circle to the north pole. -/
def qcMap : C(Ball (Euc 2), Sph (ModelSphere 2)) := qc 2

lemma qcMap_isQuot : Topology.IsQuotientMap qcMap :=
  Topology.IsQuotientMap.of_surjective_continuous (diskQuotSurj 2 (by norm_num)) (qc 2).continuous

lemma qcMap_bdry : ∀ x ∈ bdry (Euc 2), qcMap x = sphKT_northPole 2 := fun x hx => qc_bdry 2 x hx

lemma qcMap_fib : ∀ x x' : Ball (Euc 2), qcMap x = qcMap x' →
    x = x' ∨ (x ∈ bdry (Euc 2) ∧ x' ∈ bdry (Euc 2)) :=
  fun x x' h => (qc_eq_iff 2 x x').mp h

/-- The algebra isomorphism `C(S², ℂ) ≅ Kpair ℝ²` of the disc model, compatible with the
augmentations (evaluation at a boundary point corresponds to evaluation at the north pole). -/
def Psi : C(Sph (ModelSphere 2), ℂ) ≃ₐ[ℂ] Kpair (Euc 2) :=
  diskQuotAlgEquiv 2 qcMap qcMap_isQuot qcMap_fib qcMap_bdry

/-- Evaluation at a boundary point of the disc, via the north pole of `S²`. -/
lemma Psi_aug (y0 : Ball (Euc 2)) (hy0 : y0 ∈ bdry (Euc 2)) (h : C(Sph (ModelSphere 2), ℂ)) :
    augPair (Euc 2) y0 (Psi h) = evalC (sphKT_northPole 2) h :=
  diskQuotAlgEquiv_aug 2 qcMap qcMap_isQuot qcMap_fib qcMap_bdry y0 hy0 h

/-- The three coordinate functions of `S²`, pulled back to `Kpair ℝ² = C(D²/S¹)`. -/
def X0 : Kpair (Euc 2) := Psi (scE 0)
def X1 : Kpair (Euc 2) := Psi (scE 1)
def X2 : Kpair (Euc 2) := Psi scR

/-- The unit sphere relation on `S²`, read off the three coordinate functions. -/
lemma sphere_coord_sq (x : Sph (ModelSphere 2)) :
    (scE 0 x) ^ 2 + (scE 1 x) ^ 2 + (scR x) ^ 2 = 1 := by
  have hx : ‖(x : ModelSphere 2)‖ = 1 := by
    have h := Metric.mem_sphere.mp x.2
    rwa [dist_eq_norm, sub_zero] at h
  have hprod : ‖(x : ModelSphere 2)‖ ^ 2
      = ‖((x : ModelSphere 2).fst)‖ ^ 2 + ‖((x : ModelSphere 2).snd)‖ ^ 2 :=
    WithLp.prod_norm_sq_eq_of_L2 _
  have hfst : ‖((x : ModelSphere 2).fst)‖ ^ 2
      = (((x : ModelSphere 2).fst) 0) ^ 2 + (((x : ModelSphere 2).fst) 1) ^ 2 := by
    rw [PiLp.norm_sq_eq_of_L2 (fun _ : Fin 2 => ℝ) ((x : ModelSphere 2).fst), Fin.sum_univ_two]
    simp [Real.norm_eq_abs, sq_abs]
  have hsnd : ‖((x : ModelSphere 2).snd)‖ ^ 2 = ((x : ModelSphere 2).snd) ^ 2 := by
    rw [Real.norm_eq_abs, sq_abs]
  have hreal : (((x : ModelSphere 2).fst) 0) ^ 2 + (((x : ModelSphere 2).fst) 1) ^ 2
      + ((x : ModelSphere 2).snd) ^ 2 = 1 := by
    rw [← hfst, ← hsnd, ← hprod, hx]
    norm_num
  have hc := congrArg (fun r : ℝ => (r : ℂ)) hreal
  push_cast at hc
  simpa [scE, scR, mcE, mcR] using hc

/-- The coordinates of `S²` sum to `1` in `Kpair ℝ²`. -/
lemma X_sq_sum : X0 * X0 + X1 * X1 + X2 * X2 = 1 := by
  have h : scE 0 * scE 0 + scE 1 * scE 1 + scR * scR = (1 : C(Sph (ModelSphere 2), ℂ)) := by
    ext x
    simpa [ContinuousMap.add_apply, ContinuousMap.mul_apply, ContinuousMap.one_apply, pow_two]
      using sphere_coord_sq x
  have h2 := congrArg Psi h
  simp only [map_add, map_mul, map_one] at h2
  exact h2

/-- The Hopf idempotent of `S²` in the disc model, as a `2 × 2` matrix over `Kpair ℝ²`. -/
def PAM : Matrix (Fin 2) (Fin 2) (Kpair (Euc 2)) :=
  !![algebraMap ℂ (Kpair (Euc 2)) (1 / 2) * (1 + X2),
     algebraMap ℂ (Kpair (Euc 2)) (1 / 2)
       * (X0 - algebraMap ℂ (Kpair (Euc 2)) Complex.I * X1);
     algebraMap ℂ (Kpair (Euc 2)) (1 / 2)
       * (X0 + algebraMap ℂ (Kpair (Euc 2)) Complex.I * X1),
     algebraMap ℂ (Kpair (Euc 2)) (1 / 2) * (1 - X2)]

/-- The disc-model Hopf idempotent (the Bott class `[H]`). -/
def PA : Mat (Kpair (Euc 2)) := ⟨2, PAM⟩

/-- The trace of the disc-model Hopf idempotent is `1`. -/
lemma PAM_trace : PAM 0 0 + PAM 1 1 = 1 := by
  have h : algebraMap ℂ (Kpair (Euc 2)) (1 / 2 : ℂ) * (1 + X2)
      + algebraMap ℂ (Kpair (Euc 2)) (1 / 2 : ℂ) * (1 - X2) = 1 := by
    rw [← mul_add,
      show (1 + X2) + (1 - X2) = (2 : Kpair (Euc 2)) by ring,
      show (2 : Kpair (Euc 2)) = algebraMap ℂ (Kpair (Euc 2)) (2 : ℂ) from
        (map_ofNat _ 2).symm,
      ← map_mul, show ((1 : ℂ) / 2) * 2 = 1 by norm_num, map_one]
  simpa [PAM] using h

/-- The determinant of the disc-model Hopf idempotent vanishes. -/
lemma PAM_det : PAM 0 0 * PAM 1 1 = PAM 0 1 * PAM 1 0 := by
  have hI : algebraMap ℂ (Kpair (Euc 2)) Complex.I * algebraMap ℂ (Kpair (Euc 2)) Complex.I
      = -1 := by
    rw [← map_mul, Complex.I_mul_I, map_neg, map_one]
  have key : (1 + X2) * (1 - X2)
      = (X0 - algebraMap ℂ (Kpair (Euc 2)) Complex.I * X1)
        * (X0 + algebraMap ℂ (Kpair (Euc 2)) Complex.I * X1) := by
    linear_combination (-1 : Kpair (Euc 2)) * X_sq_sum + (X1 * X1) * hI
  have key2 : (algebraMap ℂ (Kpair (Euc 2)) (1 / 2 : ℂ) * (1 + X2))
        * (algebraMap ℂ (Kpair (Euc 2)) (1 / 2 : ℂ) * (1 - X2))
      = (algebraMap ℂ (Kpair (Euc 2)) (1 / 2 : ℂ)
          * (X0 - algebraMap ℂ (Kpair (Euc 2)) Complex.I * X1))
        * (algebraMap ℂ (Kpair (Euc 2)) (1 / 2 : ℂ)
          * (X0 + algebraMap ℂ (Kpair (Euc 2)) Complex.I * X1)) := by
    linear_combination (algebraMap ℂ (Kpair (Euc 2)) (1 / 2 : ℂ)
      * algebraMap ℂ (Kpair (Euc 2)) (1 / 2 : ℂ)) * key
  simpa [PAM] using key2

/-- The reduced Bott class in the disc model: `H = [Hopf] - 1`. -/
def H : K0 (Kpair (Euc 2)) := cls PA - cls (Mat.one (Kpair (Euc 2)) 1)


/-! ## The Bott relation, idempotency and the Adams operations in the disc model -/

/-- `K0.map` on the class of an idempotent, in terms of `Mat.map`. -/
lemma mapCls_idem {R S : Type} [Ring R] [Ring S] (φ : R →+* S) {p : Mat R}
    (hp : p.IsIdem) : K0.map φ (cls p) = cls (p.map φ) := by
  rw [map_cls_uncond φ p]
  classical
  unfold mapCls
  rw [if_pos hp]

/-- The rank-one ("swap") identity for a `2 × 2` matrix over a commutative ring with vanishing
determinant: `p i l * p j k = p i k * p j l`. -/
lemma rank_one_identity {R : Type} [CommRing R] (p : Matrix (Fin 2) (Fin 2) R)
    (hdet : p 0 0 * p 1 1 = p 0 1 * p 1 0) :
    ∀ i j k l : Fin 2, p i l * p j k = p i k * p j l := by
  have h2 : ∀ i : Fin 2, i = 0 ∨ i = 1 := by decide
  intro i j k l
  rcases h2 i with rfl | rfl <;> rcases h2 j with rfl | rfl <;>
    rcases h2 k with rfl | rfl <;> rcases h2 l with rfl | rfl <;>
    first
      | ring
      | exact hdet
      | exact hdet.symm
      | (rw [mul_comm (p 1 1) (p 0 0), mul_comm (p 1 0) (p 0 1)]; exact hdet)
      | (rw [mul_comm (p 1 0) (p 0 1), mul_comm (p 1 1) (p 0 0)]; exact hdet.symm)

lemma PAM_rank_one : ∀ i j k l : Fin 2, PAM i l * PAM j k = PAM i k * PAM j l :=
  rank_one_identity PAM PAM_det

/-- The disc-model Hopf idempotent is idempotent. -/
lemma PAM_idem : PAM * PAM = PAM :=
  Fund.twoByTwo_idem_of_trace_det PAM PAM_trace PAM_det

/-- The Bott relation `H ⊗ H ⊕ 1 ≅ H ⊕ H` in the disc model. -/
lemma PAM_bott :
    Mat.MvN ((Mat.kron (⟨2, PAM⟩ : Mat (Kpair (Euc 2))) ⟨2, PAM⟩).sum
        (Mat.one (Kpair (Euc 2)) 1))
      (Mat.sum (⟨2, PAM⟩ : Mat (Kpair (Euc 2))) ⟨2, PAM⟩) :=
  Work.KT.Dim2.hopf_relation_general PAM PAM_trace PAM_det

/-- `PA` is idempotent. -/
lemma PA_idem : PA.IsIdem := PAM_idem

/-! ## The augmentation of the Bott class -/

lemma X0_aug (y0 : Ball (Euc 2)) (hy0 : y0 ∈ bdry (Euc 2)) : augPair (Euc 2) y0 X0 = 0 := by
  rw [show X0 = Psi (scE 0) from rfl, Psi_aug y0 hy0]
  simp [scE, mcE, evalC, northPole_coe]

lemma X1_aug (y0 : Ball (Euc 2)) (hy0 : y0 ∈ bdry (Euc 2)) : augPair (Euc 2) y0 X1 = 0 := by
  rw [show X1 = Psi (scE 1) from rfl, Psi_aug y0 hy0]
  simp [scE, mcE, evalC, northPole_coe]

lemma X2_aug (y0 : Ball (Euc 2)) (hy0 : y0 ∈ bdry (Euc 2)) : augPair (Euc 2) y0 X2 = 1 := by
  rw [show X2 = Psi scR from rfl, Psi_aug y0 hy0]
  simp [scR, mcR, evalC, northPole_coe]

/-- The augmentation of the disc-model Hopf idempotent is the rank-one projection `diag(1,0)`. -/
lemma PAM_map_aug (y0 : Ball (Euc 2)) (hy0 : y0 ∈ bdry (Euc 2)) :
    PAM.map (⇑(augPair (Euc 2) y0)) = !![(1 : ℂ), 0; 0, 0] := by
  have hX0 : (augPair (Euc 2) y0) X0 = 0 := X0_aug y0 hy0
  have hX1 : (augPair (Euc 2) y0) X1 = 0 := X1_aug y0 hy0
  have hX2 : (augPair (Euc 2) y0) X2 = 1 := X2_aug y0 hy0
  have hI : (augPair (Euc 2) y0) (algebraMap ℂ (Kpair (Euc 2)) Complex.I) = Complex.I :=
    AlgHom.commutes (augPair (Euc 2) y0) Complex.I
  have hh : (augPair (Euc 2) y0) (algebraMap ℂ (Kpair (Euc 2)) (1 / 2 : ℂ)) = (1 / 2 : ℂ) :=
    AlgHom.commutes (augPair (Euc 2) y0) (1 / 2 : ℂ)
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp only [Matrix.map_apply, PAM, Matrix.of_apply, Matrix.cons_val', Matrix.cons_val_zero,
      Matrix.cons_val_one, Matrix.cons_val_fin_one, Matrix.head_cons, Matrix.empty_val',
      Matrix.zero_apply]
  · show (augPair (Euc 2) y0) (algebraMap ℂ (Kpair (Euc 2)) (1 / 2) * (1 + X2)) = 1
    rw [map_mul, map_add, map_one, hh, hX2]
    norm_num
  · show (augPair (Euc 2) y0)
        (algebraMap ℂ (Kpair (Euc 2)) (1 / 2)
          * (X0 - algebraMap ℂ (Kpair (Euc 2)) Complex.I * X1)) = 0
    rw [map_mul, map_sub, map_mul, hh, hX0, hI, hX1]
    norm_num
  · show (augPair (Euc 2) y0)
        (algebraMap ℂ (Kpair (Euc 2)) (1 / 2)
          * (X0 + algebraMap ℂ (Kpair (Euc 2)) Complex.I * X1)) = 0
    rw [map_mul, map_add, map_mul, hh, hX0, hI, hX1]
    norm_num
  · show (augPair (Euc 2) y0) (algebraMap ℂ (Kpair (Euc 2)) (1 / 2) * (1 - X2)) = 0
    rw [map_mul, map_sub, map_one, hh, hX2]
    norm_num

/-- `diag(1,0)` is idempotent. -/
lemma diag10_idem : Mat.IsIdem (⟨2, !![(1 : ℂ), 0; 0, 0]⟩ : Mat ℂ) := by
  show !![(1 : ℂ), 0; 0, 0] * !![(1 : ℂ), 0; 0, 0] = !![(1 : ℂ), 0; 0, 0]
  ext i j
  fin_cases i <;> fin_cases j <;> simp [Matrix.mul_apply, Fin.sum_univ_two]

/-- `diag(1,0)` is Murray–von Neumann equivalent to the rank-one identity. -/
lemma mvN_diag10_one : Mat.MvN (⟨2, !![(1 : ℂ), 0; 0, 0]⟩ : Mat ℂ) (Mat.one ℂ 1) := by
  change Mat.MvN (⟨2, !![(1 : ℂ), 0; 0, 0]⟩ : Mat ℂ)
    (⟨1, (1 : Matrix (Fin 1) (Fin 1) ℂ)⟩ : Mat ℂ)
  refine ⟨!![(1 : ℂ), 0], !![(1 : ℂ); 0], ?_, ?_⟩
  · ext i j
    fin_cases i <;> fin_cases j <;> simp [Matrix.mul_apply, Fin.sum_univ_one]
  · ext i j
    fin_cases i <;> fin_cases j <;> simp [Matrix.mul_apply, Fin.sum_univ_one]

/-- The augmentation of the class of the disc-model Hopf idempotent is trivial. -/
lemma mapA_PA_aug (y0 : Ball (Euc 2)) (hy0 : y0 ∈ bdry (Euc 2)) :
    K0.mapA (augPair (Euc 2) y0) (cls PA) = cls (Mat.one ℂ 1) := by
  rw [mapCls_idem _ PA_idem]
  show cls (Mat.map (augPair (Euc 2) y0).toRingHom PA) = cls (Mat.one ℂ 1)
  have hmap : Mat.map (augPair (Euc 2) y0).toRingHom PA
      = (⟨2, !![(1 : ℂ), 0; 0, 0]⟩ : Mat ℂ) := by
    show (⟨2, PAM.map (⇑(augPair (Euc 2) y0))⟩ : Mat ℂ)
      = (⟨2, !![(1 : ℂ), 0; 0, 0]⟩ : Mat ℂ)
    rw [PAM_map_aug y0 hy0]
  rw [hmap]
  exact cls_eq_of_mvN diag10_idem (Mat.one_isIdem ℂ 1) mvN_diag10_one

/-- The augmentation of the multiplicity-one class `1` is trivial. -/
lemma mapA_one_aug (y0 : Ball (Euc 2)) (hy0 : y0 ∈ bdry (Euc 2)) :
    K0.mapA (augPair (Euc 2) y0) (cls (Mat.one (Kpair (Euc 2)) 1)) = cls (Mat.one ℂ 1) := by
  rw [mapCls_idem _ (Mat.one_isIdem (Kpair (Euc 2)) 1)]
  have hmap : Mat.map (augPair (Euc 2) y0).toRingHom (Mat.one (Kpair (Euc 2)) 1)
      = Mat.one ℂ 1 := by
    refine Sigma.ext rfl ?_
    apply heq_of_eq
    exact Matrix.map_one ⇑(augPair (Euc 2) y0).toRingHom (map_zero _) (map_one _)
  rw [hmap]

/-- The augmentation of the reduced Bott class vanishes. -/
lemma H_aug (y0 : Ball (Euc 2)) (hy0 : y0 ∈ bdry (Euc 2)) :
    K0.mapA (augPair (Euc 2) y0) H = 0 := by
  rw [H, map_sub, mapA_PA_aug y0 hy0, mapA_one_aug y0 hy0, sub_self]

/-! ## The Adams operations on the reduced Bott class -/

/-- The Adams operations `ψ²`, `ψ³` act on the reduced Bott class by `2` and `3`. -/
lemma psi_on_H :
    (∀ ψ : K0 (Kpair (Euc 2)) →+ K0 (Kpair (Euc 2)), IsPsi2 ψ → ψ H = 2 • H) ∧
    (∀ ψ : K0 (Kpair (Euc 2)) →+ K0 (Kpair (Euc 2)), IsPsi3 ψ → ψ H = 3 • H) :=
  Work.KT.D2PR.psi_rank_one (A := Kpair (Euc 2)) (fun x y => mul_comm x y) PAM
    PAM_idem PAM_trace PAM_rank_one PAM_bott

/-- The unit circle `Sph ℝ²` sits inside the closed disc `Ball ℝ²`. -/
def inBall (x : Sph (Euc 2)) : Ball (Euc 2) :=
  ⟨(x : Euc 2), by
    rw [Metric.mem_closedBall, dist_zero_right]
    have h : ‖(x : Euc 2)‖ = 1 := by
      have h' := Metric.mem_sphere.mp x.2
      rwa [dist_eq_norm, sub_zero] at h'
    rw [h]⟩

@[simp] lemma inBall_coe (x : Sph (Euc 2)) : ((inBall x : Ball (Euc 2)) : Euc 2) = (x : Euc 2) := rfl

/-- The inclusion of the unit circle in the disc, as a continuous map. -/
def inBallCM : C(Sph (Euc 2), Ball (Euc 2)) :=
  ⟨inBall, Continuous.subtype_mk continuous_subtype_val _⟩

@[simp] lemma inBallCM_apply (x : Sph (Euc 2)) : inBallCM x = inBall x := rfl

/-- The boundary value of the disc-model Hopf idempotent, as a matrix over `ℂ`: it is the constant
rank-one projection `diag(1,0)`. -/
lemma PAM_bdry (y0 : Ball (Euc 2)) (hy0 : y0 ∈ bdry (Euc 2)) :
    PAM.map (augPair (Euc 2) y0) = !![(1 : ℂ), 0; 0, 0] :=
  PAM_map_aug y0 hy0

/-- The `2 × 2` identity-projection `diag(1,0)`, made into an idempotent of `Mat ℂ`. -/
def e0Mat : Mat ℂ := ⟨2, !![(1 : ℂ), 0; 0, 0]⟩

lemma e0Mat_idem : e0Mat.IsIdem := diag10_idem

lemma PAM_bdry_idem (y0 : Ball (Euc 2)) (hy0 : y0 ∈ bdry (Euc 2)) :
    (Mat.IsIdem ⟨2, PAM.map (augPair (Euc 2) y0)⟩) := by
  rw [PAM_bdry y0 hy0]; exact diag10_idem

end D2

end

end Work.KT
