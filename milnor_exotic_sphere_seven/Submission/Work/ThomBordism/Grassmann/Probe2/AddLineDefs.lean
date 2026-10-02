import Mathlib
import Submission.Work.ThomBordism.Grassmann.FibreBaseDefs
import Submission.Work.ThomBordism.Grassmann.blockMat_isSO
import Submission.Work.Thom.realSumStable

-- Lean v4.35.0-rc3: restore v4.34 instance-unification transparency (port).
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
set_option synthInstance.maxHeartbeats 400000

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 3000000
set_option linter.unusedVariables false

/-!
# The "add a line" map `Ω : G̃r_k(ℝ^{k+m}) → G̃r_{k+1}(ℝ^{k+m+1})` and the ρ-bookkeeping

This module collects, in a self-contained way, the linear algebra and the frame-level construction
of the stabilisation map `Ω : V ↦ V ⊕ ⟨baseVec⟩`.  It is modelled on
`Submission/Work/ThomBordism/Grassmann/fibreBaseHomeomorph.lean` (which proves the same map is a
homeomorphism onto the planes through `baseVec`), but defines its own copies because that file is
under construction.

Contents:

* the component description of `Work.Thom.rhoR k = finAddEquivProd.symm`;
* the **ρ-bookkeeping** `matLin (blockMat (k+1) A) = rhoR k ∘ (A × 1) ∘ (rhoR k)⁻¹`, which
  identifies the block matrix `diag(A,1)` with the `sumEpsR`-presentation of `A ⊕ 1`;
* the multiplicativity of `blockMat`, of its determinant, and its compatibility with the inverse;
* the frame map `alFrame`, its `SO`-equivariance, the induced map `alOmega : OG k m → OG (k+1) m`
  and its continuity.
-/

namespace Work.ThomBordism.Grassmann.Probe2

open scoped Topology
open Work.TangentClasses

noncomputable section

variable {k m : ℕ}

/-! ## The components of the splitting `rhoR` -/

@[simp] theorem rhoR_apply_castAdd (k : ℕ) (a : EuclideanSpace ℝ (Fin k)) (b : EuclideanSpace ℝ (Fin 1))
    (j : Fin k) :
    (Work.Thom.rhoR k (a, b)).ofLp (Fin.castAdd 1 j) = a.ofLp j := by
  simp [Work.Thom.rhoR, EuclideanSpace.finAddEquivProd, EuclideanSpace.sumEquivProd]

theorem rhoR_apply_natAdd (k : ℕ) (a : EuclideanSpace ℝ (Fin k)) (b : EuclideanSpace ℝ (Fin 1))
    (j : Fin 1) :
    (Work.Thom.rhoR k (a, b)).ofLp (Fin.natAdd k j) = b.ofLp j := by
  simp [Work.Thom.rhoR, EuclideanSpace.finAddEquivProd, EuclideanSpace.sumEquivProd]

@[simp] theorem rhoR_symm_fst (k : ℕ) (v : EuclideanSpace ℝ (Fin (k + 1))) (j : Fin k) :
    ((Work.Thom.rhoR k).symm v).1.ofLp j = v.ofLp (Fin.castAdd 1 j) := by
  simp [Work.Thom.rhoR, EuclideanSpace.finAddEquivProd, EuclideanSpace.sumEquivProd]

theorem rhoR_symm_snd (k : ℕ) (v : EuclideanSpace ℝ (Fin (k + 1))) (j : Fin 1) :
    ((Work.Thom.rhoR k).symm v).2.ofLp j = v.ofLp (Fin.natAdd k j) := by
  simp [Work.Thom.rhoR, EuclideanSpace.finAddEquivProd, EuclideanSpace.sumEquivProd]

/-- `ct` is `Fin.castAdd`. -/
theorem ct_eq_castAdd (j : Fin k) : ct (k + 1) (by omega) j = Fin.castAdd 1 j := rfl

/-- The last-coordinate form of `rhoR_apply_natAdd`. -/
@[simp] theorem rhoR_apply_last (k : ℕ) (a : EuclideanSpace ℝ (Fin k)) (b : EuclideanSpace ℝ (Fin 1)) :
    (Work.Thom.rhoR k (a, b)).ofLp (lastk (k + 1) (by omega)) = b.ofLp 0 := by
  rw [show lastk (k + 1) (by omega) = Fin.natAdd k 0 from
    Fin.ext (by simp [lastk, Fin.natAdd]), rhoR_apply_natAdd]

/-- The last-coordinate form of `rhoR_symm_snd`. -/
@[simp] theorem rhoR_symm_last (k : ℕ) (v : EuclideanSpace ℝ (Fin (k + 1))) :
    ((Work.Thom.rhoR k).symm v).2.ofLp 0 = v.ofLp (lastk (k + 1) (by omega)) := by
  rw [rhoR_symm_snd, show Fin.natAdd k 0 = lastk (k + 1) (by omega) from
    Fin.ext (by simp [lastk, Fin.natAdd])]

/-- `Matrix.mulVec` in component form. -/
@[simp] theorem mulVec_apply_sum {n : ℕ} (M : Matrix (Fin n) (Fin n) ℝ) (v : Fin n → ℝ) (i : Fin n) :
    (M.mulVec v) i = ∑ t, M i t * v t := by
  rw [Matrix.mulVec_apply, dotProduct]
  exact Finset.sum_congr rfl (fun t _ => by rw [Matrix.row_apply])

/-- `matLin` in component form. -/
theorem matLin_ofLp {n : ℕ} (M : Matrix (Fin n) (Fin n) ℝ) (v : Amb n) (i : Fin n) :
    (matLin M v).ofLp i = ∑ t, M i t * v.ofLp t := by
  rw [matLin_apply, WithLp.ofLp_toLp, mulVec_apply_sum]

/-! ## The ρ-bookkeeping for the block matrix -/

/-- **The block matrix `diag(A,1)` is the `rhoR`-conjugate of `A × 1`** (evaluation form). -/
theorem matLin_blockMat_apply (A : Matrix (Fin k) (Fin k) ℝ) (v : Amb (k + 1)) :
    matLin (k := k + 1) (blockMat (k + 1) A) v
      = (Work.Thom.rhoR k) ((matLin A).prodMap (ContinuousLinearMap.id ℝ (Amb 1))
          ((Work.Thom.rhoR k).symm v)) := by
  rw [matLin_apply]
  apply WithLp.ofLp_injective
  funext i
  rw [WithLp.ofLp_toLp, mulVec_apply_sum]
  rcases eq_lastk_or_eq_ct (k + 1) (by omega) i with hi | ⟨j, hi⟩
  · subst hi
    rw [sum_fin_eq (k + 1) (by omega)
        (fun t => blockMat (k + 1) A (lastk (k + 1) (by omega)) t * v.ofLp t),
      Finset.sum_eq_zero (fun t _ => by
        rw [blockMat_last_ct (k + 1) (by omega) A t, zero_mul]), zero_add]
    simp only [blockMat_last_last, one_mul, ContinuousLinearMap.coe_prodMap', Prod.map_apply',
      ContinuousLinearMap.id_apply, rhoR_apply_last, rhoR_symm_last]
  · subst hi
    rw [sum_fin_eq (k + 1) (by omega)
        (fun t => blockMat (k + 1) A (ct (k + 1) (by omega) j) t * v.ofLp t),
      blockMat_ct_last (k + 1) (by omega) A j, zero_mul, add_zero,
      ContinuousLinearMap.coe_prodMap', Prod.map_apply', ContinuousLinearMap.id_apply,
      show ct (k + 1) (by omega) j = Fin.castAdd 1 j from Fin.ext rfl, rhoR_apply_castAdd,
      matLin_ofLp]
    refine Finset.sum_congr rfl (fun t _ => ?_)
    rw [show Fin.castAdd 1 j = ct (k + 1) (by omega) j from Fin.ext rfl,
      blockMat_ct_ct (k + 1) (by omega) A j t, rhoR_symm_fst,
      show ct (k + 1) (by omega) t = Fin.castAdd 1 t from Fin.ext rfl]

/-- **The ρ-bookkeeping, as an identity of continuous linear maps.** -/
theorem matLin_blockMat (A : Matrix (Fin k) (Fin k) ℝ) :
    matLin (k := k + 1) (blockMat (k + 1) A)
      = ((Work.Thom.rhoR k : (Amb k × Amb 1) →L[ℝ] Amb (k + 1)).comp
          (((matLin A).prodMap (ContinuousLinearMap.id ℝ (Amb 1))).comp
            ((Work.Thom.rhoR k).symm : Amb (k + 1) →L[ℝ] (Amb k × Amb 1)))) := by
  apply ContinuousLinearMap.ext
  intro v
  rw [ContinuousLinearMap.comp_apply, ContinuousLinearMap.comp_apply]
  exact matLin_blockMat_apply A v

/-! ## The algebra of the block matrix -/

theorem blockMat_mul (A B : Matrix (Fin k) (Fin k) ℝ) :
    blockMat (k + 1) (A * B) = blockMat (k + 1) A * blockMat (k + 1) B := by
  rw [blockMat_eq_reindex (k + 1) (by omega) (A * B),
    blockMat_eq_reindex (k + 1) (by omega) A, blockMat_eq_reindex (k + 1) (by omega) B,
    Matrix.reindex_apply, Matrix.reindex_apply, Matrix.reindex_apply,
    Matrix.submatrix_mul_equiv, Matrix.fromBlocks_multiply]
  congr 1
  ext i j
  rcases i with i | i <;> rcases j with j | j <;> simp

theorem blockMat_one : blockMat (k + 1) (1 : Matrix (Fin k) (Fin k) ℝ) = 1 := by
  rw [blockMat_eq_reindex (k + 1) (by omega) (1 : Matrix (Fin k) (Fin k) ℝ),
    Matrix.reindex_apply, Matrix.fromBlocks_one]
  exact Matrix.submatrix_one_equiv (sumEquiv (k + 1) (by omega)).symm

theorem det_blockMat (A : Matrix (Fin k) (Fin k) ℝ) : (blockMat (k + 1) A).det = A.det := by
  rw [blockMat_eq_reindex (k + 1) (by omega) A, Matrix.det_reindex,
    show (sumEquiv (k + 1) (by omega)).trans (sumEquiv (k + 1) (by omega)).symm = 1 from
      Equiv.ext fun x => by simp,
    Equiv.Perm.sign_one, Matrix.det_fromBlocks_zero₁₂, Matrix.det_one]
  simp

/-- `blockMat` depends continuously on the matrix. -/
theorem continuous_blockMat (k : ℕ) :
    Continuous fun M : Matrix (Fin k) (Fin k) ℝ => blockMat (k + 1) M := by
  refine continuous_matrix fun i j => ?_
  by_cases hi : i.val < k
  · by_cases hj : j.val < k
    · rw [show (fun M : Matrix (Fin k) (Fin k) ℝ => blockMat (k + 1) M i j)
          = fun M => M ⟨i.val, hi⟩ ⟨j.val, hj⟩ from by funext M; simp [blockMat, hi, hj]]
      exact (continuous_apply (⟨j.val, hj⟩ : Fin k)).comp
        (continuous_apply (⟨i.val, hi⟩ : Fin k))
    · rw [show (fun M : Matrix (Fin k) (Fin k) ℝ => blockMat (k + 1) M i j) = fun _ => 0 from by
        funext M; simp [blockMat, hi, hj]]
      exact continuous_const
  · by_cases hj : j.val < k
    · rw [show (fun M : Matrix (Fin k) (Fin k) ℝ => blockMat (k + 1) M i j) = fun _ => 0 from by
        funext M; simp [blockMat, hi, hj]]
      exact continuous_const
    · rw [show (fun M : Matrix (Fin k) (Fin k) ℝ => blockMat (k + 1) M i j) = fun _ => 1 from by
        funext M; simp [blockMat, hi, hj]]
      exact continuous_const

theorem blockMat_mul_nonsing_inv (A : Matrix (Fin k) (Fin k) ℝ) (hA : IsUnit A.det) :
    blockMat (k + 1) A * blockMat (k + 1) A⁻¹ = 1 := by
  rw [← blockMat_mul, Matrix.mul_nonsing_inv A hA, blockMat_one]

theorem blockMat_inv_eq (A : Matrix (Fin k) (Fin k) ℝ) (hA : IsUnit A.det) :
    (blockMat (k + 1) A)⁻¹ = blockMat (k + 1) A⁻¹ := by
  refine Matrix.inv_eq_left_inv ?_
  rw [← blockMat_mul, Matrix.nonsing_inv_mul A hA, blockMat_one]

/-! ## The frame map and the map `Ω` -/

/-- **The frame obtained by adjoining `baseVec (k+1) m`**: the frame of the plane `V ⊕ ⟨baseVec⟩`. -/
def alFrame (k m : ℕ) (f : Stiefel k m) : Fin (k + 1) → Amb ((k + 1) + m) :=
  fun i => if hi : i.val < k then snocE (k + 1) m (by omega) (f.1 ⟨i.val, hi⟩)
    else baseVec (k + 1) m

theorem alFrame_ct (f : Stiefel k m) (j : Fin k) :
    alFrame k m f (ct (k + 1) (by omega) j) = snocE (k + 1) m (by omega) (f.1 j) := by
  rw [alFrame, dif_pos (by rw [ct_val]; exact j.isLt)]
  exact congrArg (fun a => snocE (k + 1) m (by omega) (f.1 a)) (Fin.ext rfl)

theorem alFrame_last (f : Stiefel k m) :
    alFrame k m f (lastk (k + 1) (by omega)) = baseVec (k + 1) m := by
  rw [alFrame, dif_neg (by rw [lastk_val]; omega)]

theorem orthonormal_alFrame (f : Stiefel k m) : Orthonormal ℝ (alFrame k m f) := by
  rw [orthonormal_iff_ite]
  intro i j
  by_cases hi : i.val < k
  · by_cases hj : j.val < k
    · rw [alFrame, dif_pos hi, alFrame, dif_pos hj, LinearIsometry.inner_map_map,
        (orthonormal_iff_ite.mp f.2) ⟨i.val, hi⟩ ⟨j.val, hj⟩]
      by_cases hij : i = j
      · subst hij; rw [if_pos rfl, if_pos rfl]
      · rw [if_neg hij, if_neg (fun hh => hij (Fin.ext (by simpa using congrArg Fin.val hh)))]
    · have hj' : j.val = k := by have := j.isLt; omega
      rw [alFrame, dif_pos hi, alFrame, dif_neg hj, inner_snocE_baseVec (k + 1) m (by omega),
        if_neg (fun hij => by have := congrArg Fin.val hij; simp [hj'] at this; omega)]
  · have hi' : i.val = k := by have := i.isLt; omega
    by_cases hj : j.val < k
    · rw [alFrame, dif_neg hi, alFrame, dif_pos hj, inner_baseVec_snocE (k + 1) m (by omega),
        if_neg (fun hij => by have := congrArg Fin.val hij; simp [hi'] at this; omega)]
    · have hij : i = j := Fin.ext (by omega)
      rw [alFrame, dif_neg hi, alFrame, dif_neg hj, inner_baseVec_self (k + 1) m (by omega),
        if_pos hij]

/-- **The frame map as a point of the Stiefel manifold**: the `SO(k) → SO(k+1)` upgrade. -/
def alFrameStiefel (k m : ℕ) (f : Stiefel k m) : Stiefel (k + 1) m :=
  ⟨alFrame k m f, orthonormal_alFrame f⟩

theorem continuous_alFrame (k m : ℕ) : Continuous (alFrame (k := k) (m := m)) := by
  refine continuous_pi fun i => ?_
  by_cases hi : i.val < k
  · have h1 : (fun f : Stiefel k m => alFrame k m f i)
        = fun f => snocE (k + 1) m (by omega) (f.1 ⟨i.val, hi⟩) := by
      funext f; rw [alFrame, dif_pos hi]
    rw [h1]
    exact (snocE (k + 1) m (by omega)).continuous.comp
      ((continuous_apply (⟨i.val, hi⟩ : Fin k)).comp continuous_subtype_val)
  · have h1 : (fun f : Stiefel k m => alFrame k m f i) = fun _ => baseVec (k + 1) m := by
      funext f; rw [alFrame, dif_neg hi]
    rw [h1]; exact continuous_const

theorem continuous_alFrameStiefel (k m : ℕ) :
    Continuous (alFrameStiefel (k := k) (m := m)) :=
  Continuous.subtype_mk (continuous_alFrame k m) (fun f => orthonormal_alFrame f)

/-- `snocE` is linear over finite sums. -/
theorem snocE_sum_smul (c : Fin k → ℝ) (v : Fin k → Amb (k + m)) :
    (∑ j, c j • snocE (k + 1) m (by omega) (v j))
      = snocE (k + 1) m (by omega) (∑ j, c j • v j) := by
  rw [map_sum]
  exact Finset.sum_congr rfl fun j _ => by rw [map_smul]

/-- The action of the block matrix `diag(B,1)` on the frame `alFrame f`, in the last coordinate. -/
theorem soAct_alFrame_last (B : Matrix (Fin k) (Fin k) ℝ) (f : Stiefel k m) :
    soActFun (blockMat (k + 1) B) (alFrame k m f) (lastk (k + 1) (by omega))
      = baseVec (k + 1) m := by
  rw [soActFun, sum_fin_eq (k + 1) (by omega)
      (fun t => blockMat (k + 1) B t (lastk (k + 1) (by omega)) • alFrame k m f t),
    Finset.sum_eq_zero (fun t _ => by
      rw [blockMat_ct_last (k + 1) (by omega) B t, zero_smul]),
    zero_add, blockMat_last_last (k + 1) (by omega) B, one_smul, alFrame_last]

/-- The action of the block matrix `diag(B,1)` on the frame `alFrame f`, in the `i`-th of the
first `k` coordinates. -/
theorem soAct_alFrame_ct (B : Matrix (Fin k) (Fin k) ℝ) (f : Stiefel k m) (i : Fin k) :
    soActFun (blockMat (k + 1) B) (alFrame k m f) (ct (k + 1) (by omega) i)
      = snocE (k + 1) m (by omega) (soActFun B f.1 i) := by
  rw [soActFun, sum_fin_eq (k + 1) (by omega)
      (fun t => blockMat (k + 1) B t (ct (k + 1) (by omega) i) • alFrame k m f t)]
  rw [Finset.sum_congr rfl (fun t _ => by
        rw [blockMat_ct_ct (k + 1) (by omega) B t i, alFrame_ct]),
    blockMat_last_ct (k + 1) (by omega) B i, zero_smul, add_zero]
  rw [soActFun, map_sum]
  exact Finset.sum_congr rfl (fun t _ => by rw [map_smul])

/-- **The frame map is `SO(k)`-equivariant** (with the block matrix `diag(A,1)`). -/
theorem alFrame_act (A : SOk k) (f : Stiefel k m) :
    alFrame k m (A.act f) = soActFun (blockMat (k + 1) A.1) (alFrame k m f) := by
  funext i
  rcases eq_lastk_or_eq_ct (k + 1) (by omega) i with hi | ⟨i', hi⟩
  · subst hi; rw [alFrame_last, soAct_alFrame_last]
  · subst hi
    rw [alFrame_ct, soAct_alFrame_ct]
    rfl

/-- The image of `[f]` under `Ω`. -/
def alOmegaMk (k m : ℕ) (f : Stiefel k m) : OG (k + 1) m :=
  Quotient.mk'' (alFrameStiefel k m f)

theorem alOmegaMk_act (A : SOk k) (f : Stiefel k m) : alOmegaMk k m (A.act f) = alOmegaMk k m f := by
  have hC : IsSO (blockMat (k + 1) A.1) := blockMat_isSO (k + 1) (by omega) A.1 A.2
  have hsub : alFrameStiefel k m (A.act f)
      = SOk.act (k := k + 1) ⟨blockMat (k + 1) A.1, hC⟩ (alFrameStiefel k m f) :=
    Subtype.ext (alFrame_act A f)
  have key : (Quotient.mk'' (alFrameStiefel k m f) : OG (k + 1) m)
      = Quotient.mk'' (alFrameStiefel k m (A.act f)) :=
    Quotient.sound (show (grassmannSetoid (k + 1) m).r (alFrameStiefel k m f)
      (alFrameStiefel k m (A.act f)) from ⟨⟨blockMat (k + 1) A.1, hC⟩, hsub⟩)
  exact key.symm

/-- **The "add a line" map `Ω : G̃r_k(ℝ^{k+m}) → G̃r_{k+1}(ℝ^{k+m+1})`**, `V ↦ V ⊕ ⟨baseVec⟩`. -/
def alOmega (k m : ℕ) : OG k m → OG (k + 1) m :=
  Quotient.lift (fun f => alOmegaMk k m f) fun f g hfg => by
    obtain ⟨A, rfl⟩ := hfg
    exact (alOmegaMk_act A f).symm

@[simp] theorem alOmega_mk (k m : ℕ) (f : Stiefel k m) :
    alOmega k m (Quotient.mk'' f) = alOmegaMk k m f := rfl

theorem continuous_alOmegaMk (k m : ℕ) : Continuous (alOmegaMk (k := k) (m := m)) :=
  continuous_quotient_mk'.comp (continuous_alFrameStiefel k m)

theorem continuous_alOmega (k m : ℕ) : Continuous (alOmega (k := k) (m := m)) := by
  refine (isQuotientMap_quotient_mk' (s := grassmannSetoid k m)).continuous_iff.mpr ?_
  show Continuous fun f : Stiefel k m => (Quotient.mk'' (alFrameStiefel k m f) : OG (k + 1) m)
  exact continuous_quotient_mk'.comp (continuous_alFrameStiefel k m)

/-- `Ω` as a continuous map. -/
def alOmegaCM (k m : ℕ) : C(OG k m, OG (k + 1) m) := ⟨alOmega k m, continuous_alOmega k m⟩

@[simp] theorem alOmegaCM_apply (k m : ℕ) (x : OG k m) : alOmegaCM k m x = alOmega k m x := rfl

/-! ## The chart bookkeeping for the "add a line" map -/

/-- The last coordinate of the big ambient space `ℝ^{(k+1)+m}`. -/
abbrev alLast (k m : ℕ) : Fin ((k + 1) + m) := lastk ((k + 1) + m) (by omega)

/-- The embedding of the old coordinates `Fin (k+m)` into the big ones (the plane
`baseVec ^⊥` is spanned by these coordinates). -/
def alIdx (k m : ℕ) : Fin (k + m) → Fin ((k + 1) + m) := fun j => ⟨j.val, by omega⟩

theorem alIdx_val (j : Fin (k + m)) : (alIdx k m j).val = j.val := rfl

theorem alIdx_injective (k m : ℕ) : Function.Injective (alIdx k m) :=
  fun a b h => Fin.ext (by simpa [alIdx] using congrArg Fin.val h)

theorem alIdx_ne_last (j : Fin (k + m)) : alIdx k m j ≠ alLast k m := by
  intro hh
  have h1 : (alIdx k m j).val = (alLast k m).val := congrArg Fin.val hh
  simp only [alIdx_val, alLast, lastk_val] at h1
  have := j.isLt
  omega

theorem alLast_val (k m : ℕ) : (alLast k m).val = k + m := by
  simp only [alLast, lastk_val]
  omega

/-- The position of the last coordinate in the enumeration of the chart `i`. -/
def alLastPos (i : ChartIdx (k + 1) m) (h : alLast k m ∈ i.1) : Fin (k + 1) :=
  i.1.equivFinOfCardEq i.2 ⟨alLast k m, h⟩

/-- The coordinate at position `jj` of the enumeration of the chart `i`. -/
def alChartVal (i : ChartIdx (k + 1) m) (jj : Fin (k + 1)) : Fin ((k + 1) + m) :=
  (((i.1.equivFinOfCardEq i.2).symm jj : ↥i.1) : Fin ((k + 1) + m))

theorem alChartVal_mem (i : ChartIdx (k + 1) m) (jj : Fin (k + 1)) : alChartVal i jj ∈ i.1 :=
  ((i.1.equivFinOfCardEq i.2).symm jj).2

theorem alChartVal_lastPos (i : ChartIdx (k + 1) m) (h : alLast k m ∈ i.1) :
    alChartVal i (alLastPos i h) = alLast k m := by
  rw [alChartVal, alLastPos, Equiv.symm_apply_apply]

theorem alChartVal_injective (i : ChartIdx (k + 1) m) : Function.Injective (alChartVal i) := by
  intro a b hab
  have h1 : ((i.1.equivFinOfCardEq i.2).symm a : ↥i.1)
      = ((i.1.equivFinOfCardEq i.2).symm b : ↥i.1) := Subtype.ext hab
  exact (i.1.equivFinOfCardEq i.2).symm.injective h1

theorem alChartVal_ne_last (i : ChartIdx (k + 1) m) (h : alLast k m ∈ i.1) {jj : Fin (k + 1)}
    (hjj : jj ≠ alLastPos i h) : alChartVal i jj ≠ alLast k m := by
  intro hh
  exact hjj (alChartVal_injective i (by rw [hh, alChartVal_lastPos i h]))

/-- The chart of `OG k m` obtained by dropping the last coordinate. -/
def downFinset (i : ChartIdx (k + 1) m) (h : alLast k m ∈ i.1) : Finset (Fin (k + m)) :=
  (i.1.erase (alLast k m)).preimage (alIdx k m) (alIdx_injective k m).injOn

theorem mem_downFinset {i : ChartIdx (k + 1) m} {h : alLast k m ∈ i.1} {j : Fin (k + m)} :
    j ∈ downFinset i h ↔ alIdx k m j ∈ i.1.erase (alLast k m) :=
  Finset.mem_preimage

theorem card_downFinset (i : ChartIdx (k + 1) m) (h : alLast k m ∈ i.1) :
    (downFinset i h).card = k := by
  have hfilter : (i.1.erase (alLast k m)).filter (fun x => x ∈ Set.range (alIdx k m))
      = i.1.erase (alLast k m) := by
    refine Finset.filter_true_of_mem (fun x hx => ?_)
    rw [Finset.mem_erase] at hx
    exact ⟨⟨x.val, by
      have h1 : x.val ≠ k + m := fun hh => hx.1 (Fin.ext (by rw [hh, alLast_val]))
      have := x.isLt
      omega⟩, Fin.ext rfl⟩
  rw [downFinset, Finset.card_preimage, hfilter, Finset.card_erase_of_mem h, i.2]
  omega

/-- The chart of `OG k m` corresponding to a chart of `OG (k+1) m` containing the last
coordinate. -/
def downChart (i : ChartIdx (k + 1) m) (h : alLast k m ∈ i.1) : ChartIdx k m :=
  ⟨downFinset i h, card_downFinset i h⟩

@[simp] theorem downChart_val (i : ChartIdx (k + 1) m) (h : alLast k m ∈ i.1) :
    (downChart i h).1 = downFinset i h := rfl

/-- The down-index of the coordinate at position `jj`. -/
def downIdx (i : ChartIdx (k + 1) m) (h : alLast k m ∈ i.1) (jj : Fin (k + 1))
    (hjj : jj ≠ alLastPos i h) : Fin (k + m) :=
  ⟨(alChartVal i jj).val, by
    have hne : alChartVal i jj ≠ alLast k m := alChartVal_ne_last i h hjj
    have h2 : (alChartVal i jj).val ≠ k + m := by
      intro hh
      exact hne (Fin.ext (by rw [hh, alLast_val]))
    have := (alChartVal i jj).isLt
    omega⟩

theorem alIdx_downIdx (i : ChartIdx (k + 1) m) (h : alLast k m ∈ i.1) (jj : Fin (k + 1))
    (hjj : jj ≠ alLastPos i h) : alIdx k m (downIdx i h jj hjj) = alChartVal i jj :=
  Fin.ext rfl

theorem downIdx_mem (i : ChartIdx (k + 1) m) (h : alLast k m ∈ i.1) (jj : Fin (k + 1))
    (hjj : jj ≠ alLastPos i h) : downIdx i h jj hjj ∈ (downChart i h).1 := by
  rw [downChart_val, mem_downFinset, Finset.mem_erase]
  exact ⟨alChartVal_ne_last i h hjj, by rw [alIdx_downIdx]; exact alChartVal_mem i jj⟩

/-- The position of the down-index in the enumeration of the corresponding chart. -/
def downVal (i : ChartIdx (k + 1) m) (h : alLast k m ∈ i.1) (jj : Fin (k + 1))
    (hjj : jj ≠ alLastPos i h) : Fin k :=
  ((downChart i h).1.equivFinOfCardEq (downChart i h).2)
    ⟨downIdx i h jj hjj, downIdx_mem i h jj hjj⟩

theorem downVal_symm (i : ChartIdx (k + 1) m) (h : alLast k m ∈ i.1) (jj : Fin (k + 1))
    (hjj : jj ≠ alLastPos i h) :
    (((downChart i h).1.equivFinOfCardEq (downChart i h).2).symm
      (downVal i h jj hjj) : Fin (k + m)) = downIdx i h jj hjj := by
  rw [downVal, Equiv.symm_apply_apply]

theorem downVal_injective (i : ChartIdx (k + 1) m) (h : alLast k m ∈ i.1) {jj jj' : Fin (k + 1)}
    (hjj : jj ≠ alLastPos i h) (hjj' : jj' ≠ alLastPos i h)
    (heq : downVal i h jj hjj = downVal i h jj' hjj') : jj = jj' := by
  have h1 : downIdx i h jj hjj = downIdx i h jj' hjj' := by
    rw [← downVal_symm i h jj hjj, ← downVal_symm i h jj' hjj', heq]
  exact alChartVal_injective i (by
    rw [← alIdx_downIdx i h jj hjj, ← alIdx_downIdx i h jj' hjj', h1])

/-- **The permutation of the enumerations**: the last vector goes to the last position, the other
`k` vectors follow the correspondence of the two charts. -/
def alPermFun (i : ChartIdx (k + 1) m) (h : alLast k m ∈ i.1) (jj : Fin (k + 1)) : Fin (k + 1) :=
  if hjj : jj = alLastPos i h then lastk (k + 1) (by omega)
    else ct (k + 1) (by omega) (downVal i h jj hjj)

theorem alPermFun_eq_last (i : ChartIdx (k + 1) m) (h : alLast k m ∈ i.1) {jj : Fin (k + 1)}
    (hjj : jj = alLastPos i h) : alPermFun i h jj = lastk (k + 1) (by omega) :=
  dif_pos hjj

theorem alPermFun_eq_ct (i : ChartIdx (k + 1) m) (h : alLast k m ∈ i.1) {jj : Fin (k + 1)}
    (hjj : jj ≠ alLastPos i h) :
    alPermFun i h jj = ct (k + 1) (by omega) (downVal i h jj hjj) :=
  dif_neg hjj

theorem alPermFun_injective (i : ChartIdx (k + 1) m) (h : alLast k m ∈ i.1) :
    Function.Injective (alPermFun i h) := by
  intro a b hab
  by_cases ha : a = alLastPos i h
  · subst ha
    rw [alPermFun_eq_last i h rfl] at hab
    by_cases hb : b = alLastPos i h
    · exact hb.symm
    · rw [alPermFun_eq_ct i h hb] at hab
      exact absurd hab.symm (ct_ne_lastk (k + 1) (by omega) (downVal i h b hb))
  · by_cases hb : b = alLastPos i h
    · rw [alPermFun_eq_ct i h ha, alPermFun_eq_last i h hb] at hab
      exact absurd hab (ct_ne_lastk (k + 1) (by omega) (downVal i h a ha))
    · rw [alPermFun_eq_ct i h ha, alPermFun_eq_ct i h hb] at hab
      exact downVal_injective i h ha hb (ct_injective (k + 1) (by omega) hab)

/-- **The permutation of the chart enumerations.** -/
def alPerm (i : ChartIdx (k + 1) m) (h : alLast k m ∈ i.1) : Equiv.Perm (Fin (k + 1)) :=
  Equiv.ofBijective (alPermFun i h) (by
    rw [Fintype.bijective_iff_injective_and_card]
    exact ⟨alPermFun_injective i h, rfl⟩)

@[simp] theorem alPerm_apply (i : ChartIdx (k + 1) m) (h : alLast k m ∈ i.1) (jj : Fin (k + 1)) :
    alPerm i h jj = alPermFun i h jj := rfl

/-- The permutation matrix of `alPerm`. -/
def alQ (i : ChartIdx (k + 1) m) (h : alLast k m ∈ i.1) : Matrix (Fin (k + 1)) (Fin (k + 1)) ℝ :=
  (alPerm i h).permMatrix ℝ

/-- The inverse permutation matrix. -/
def alQinv (i : ChartIdx (k + 1) m) (h : alLast k m ∈ i.1) :
    Matrix (Fin (k + 1)) (Fin (k + 1)) ℝ :=
  ((alPerm i h)⁻¹).permMatrix ℝ

theorem alQ_mul_alQinv (i : ChartIdx (k + 1) m) (h : alLast k m ∈ i.1) :
    alQ i h * alQinv i h = 1 := by
  rw [alQ, alQinv, ← Matrix.permMatrix_mul, inv_mul_cancel, Matrix.permMatrix_one]

theorem alQinv_mul_alQ (i : ChartIdx (k + 1) m) (h : alLast k m ∈ i.1) :
    alQinv i h * alQ i h = 1 := by
  rw [alQ, alQinv, ← Matrix.permMatrix_mul, mul_inv_cancel, Matrix.permMatrix_one]

theorem alQ_det_ne_zero (i : ChartIdx (k + 1) m) (h : alLast k m ∈ i.1) : (alQ i h).det ≠ 0 := by
  rw [alQ, Matrix.det_permutation]
  rcases Int.units_eq_one_or (Equiv.Perm.sign (alPerm i h)) with h1 | h1
  · rw [h1]; norm_num
  · rw [h1]; norm_num

/-! ## The frame-matrix identity -/

/-- The component formula for `baseVec`: it is the unit vector in the last coordinate. -/
theorem baseVec_ofLp (i : Fin ((k + 1) + m)) :
    (baseVec (k + 1) m).ofLp i = if i = alLast k m then 1 else 0 := by
  rw [baseVec_eq_single (k + 1) m (by omega), EuclideanSpace.single_apply]

/-- The component formula for `snocE`. -/
theorem snocE_ofLp (x : Amb (k + m)) (i : Fin ((k + 1) + m)) :
    (snocE (k + 1) m (by omega) x).ofLp i
      = if h : i.val < k + m then x.ofLp ⟨i.val, h⟩ else 0 := by
  by_cases h : i.val < k + m
  · rw [dif_pos h, snocE_apply_ofLp_lt (k + 1) m (by omega) x i h]
  · rw [dif_neg h]
    have hi : i = alLast k m := by
      apply Fin.ext
      simp only [alLast, lastk_val]
      have := i.isLt
      omega
    rw [hi, snocE_apply_ofLp_lastN (k + 1) m (by omega) x]

/-- The entries of the big frame matrix are the coordinates at `alChartVal`. -/
theorem frameMatrix_alChartVal (i : ChartIdx (k + 1) m)
    (g : Fin (k + 1) → Amb ((k + 1) + m)) (jj mm : Fin (k + 1)) :
    frameMatrix i g jj mm = (g mm).ofLp (alChartVal i jj) := by
  rw [frameMatrix_apply]
  rfl

/-- The entries of the small frame matrix, in the down-index. -/
theorem frameMatrix_downVal (i : ChartIdx (k + 1) m) (h : alLast k m ∈ i.1) (f : Stiefel k m)
    (jj : Fin (k + 1)) (hjj : jj ≠ alLastPos i h) (mm : Fin k) :
    frameMatrix (downChart i h) f.1 (downVal i h jj hjj) mm = (f.1 mm).ofLp (downIdx i h jj hjj) := by
  rw [frameMatrix_apply, downVal_symm i h jj hjj]

/-- **The frame-matrix identity**: in the chart `i` of `OG (k+1) m` (containing the last
coordinate), the frame `alFrame f` has frame matrix the block matrix `diag(A,1)` of the frame matrix
`A` of `f` in the corresponding chart of `OG k m`, with its rows permuted by `alPerm`. -/
theorem frameMatrix_alFrame (i : ChartIdx (k + 1) m) (h : alLast k m ∈ i.1) (f : Stiefel k m) :
    frameMatrix i (alFrame k m f)
      = (blockMat (k + 1) (frameMatrix (downChart i h) f.1)).submatrix (alPerm i h) id := by
  ext jj mm
  rw [Matrix.submatrix_apply, id_eq, frameMatrix_alChartVal, alPerm_apply]
  rcases eq_lastk_or_eq_ct (k + 1) (by omega) mm with hm | ⟨mm', hm⟩
  · subst hm
    rw [alFrame_last, baseVec_ofLp]
    by_cases hjj : jj = alLastPos i h
    · have hcond : alChartVal i jj = alLast k m := by rw [hjj, alChartVal_lastPos i h]
      rw [alPermFun_eq_last i h hjj, if_pos hcond, blockMat_last_last]
    · rw [alPermFun_eq_ct i h hjj, if_neg (alChartVal_ne_last i h hjj), blockMat_ct_last]
  · subst hm
    rw [alFrame_ct, snocE_ofLp]
    by_cases hjj : jj = alLastPos i h
    · rw [alPermFun_eq_last i h hjj, blockMat_last_ct,
        dif_neg (by rw [hjj, alChartVal_lastPos i h, alLast_val]; omega)]
    · rw [alPermFun_eq_ct i h hjj, blockMat_ct_ct, frameMatrix_downVal,
        dif_pos (by
          have hne : alChartVal i jj ≠ alLast k m := alChartVal_ne_last i h hjj
          have h1 : (alChartVal i jj).val ≠ k + m := fun hh =>
            hne (Fin.ext (by rw [hh, alLast_val]))
          have := (alChartVal i jj).isLt
          omega)]
      exact congrArg (fun x => (f.1 mm').ofLp x) (Fin.ext rfl)

/-- The product form of the frame-matrix identity. -/
theorem frameMatrix_alFrame_mul (i : ChartIdx (k + 1) m) (h : alLast k m ∈ i.1) (f : Stiefel k m) :
    frameMatrix i (alFrame k m f)
      = alQ i h * blockMat (k + 1) (frameMatrix (downChart i h) f.1) := by
  rw [frameMatrix_alFrame, alQ]
  exact (PEquiv.toMatrix_toPEquiv_mul (alPerm i h)
    (blockMat (k + 1) (frameMatrix (downChart i h) f.1))).symm

/-- The product form of the frame-matrix identity, for the Stiefel element. -/
theorem frameMatrix_alFrameStiefel_mul (i : ChartIdx (k + 1) m) (h : alLast k m ∈ i.1)
    (f : Stiefel k m) :
    frameMatrix i (alFrameStiefel k m f).1
      = alQ i h * blockMat (k + 1) (frameMatrix (downChart i h) f.1) :=
  frameMatrix_alFrame_mul i h f

/-- The determinant of the big frame matrix is the sign of the permutation times the determinant of
the small one. -/
theorem det_frameMatrix_alFrame (i : ChartIdx (k + 1) m) (h : alLast k m ∈ i.1) (f : Stiefel k m) :
    (frameMatrix i (alFrame k m f)).det
      = (alQ i h).det * (frameMatrix (downChart i h) f.1).det := by
  rw [frameMatrix_alFrame, Matrix.det_permute, det_blockMat, alQ, Matrix.det_permutation]

/-! ## The base sets -/

/-- **The pullback chart is the down-chart**: if `i` contains the last coordinate and `Ω b` lies in
the chart `i`, then `b` lies in the chart of `OG k m` obtained by dropping it. -/
theorem mem_baseSet_downChart_of_mem_alOmega (i : ChartIdx (k + 1) m) (h : alLast k m ∈ i.1)
    {b : OG k m} (hb : alOmega k m b ∈ baseSet i) : b ∈ baseSet (downChart i h) := by
  obtain ⟨f, rfl⟩ : ∃ f : Stiefel k m, Quotient.mk'' f = b := Quotient.exists_rep b
  have hb' : (frameMatrix i (alFrame k m f)).det ≠ 0 :=
    (mem_chartSet i (alFrameStiefel k m f)).mp
      ((mem_baseSet_iff i (alFrameStiefel k m f)).mp hb)
  refine (mem_baseSet_iff (downChart i h) f).mpr (fun hdet => ?_)
  exact hb' (by rw [det_frameMatrix_alFrame i h f, hdet, mul_zero])

theorem mem_baseSet_downChart_iff_alOmega (i : ChartIdx (k + 1) m) (h : alLast k m ∈ i.1)
    {b : OG k m} : alOmega k m b ∈ baseSet i ↔ b ∈ baseSet (downChart i h) := by
  refine ⟨fun hb => mem_baseSet_downChart_of_mem_alOmega i h hb, fun hb => ?_⟩
  obtain ⟨f, rfl⟩ : ∃ f : Stiefel k m, Quotient.mk'' f = b := Quotient.exists_rep b
  have hb' : (frameMatrix (downChart i h) f.1).det ≠ 0 :=
    (mem_chartSet (downChart i h) f).mp ((mem_baseSet_iff (downChart i h) f).mp hb)
  refine (mem_baseSet_iff i (alFrameStiefel k m f)).mpr ?_
  rw [mem_chartSet,
    show (frameMatrix i (alFrameStiefel k m f).1).det
      = (alQ i h).det * (frameMatrix (downChart i h) f.1).det from det_frameMatrix_alFrame i h f]
  exact mul_ne_zero (alQ_det_ne_zero i h) hb'

/-- The chart `i` of `OG (k+1) m` misses the image of `Ω` when it does not contain the last
coordinate. -/
theorem mem_alOmega_baseSet_eq_empty (i : ChartIdx (k + 1) m) (h : alLast k m ∉ i.1) :
    ∀ b : OG k m, alOmega k m b ∉ baseSet i := by
  intro b hb
  obtain ⟨f, rfl⟩ : ∃ f : Stiefel k m, Quotient.mk'' f = b := Quotient.exists_rep b
  have hb' : (frameMatrix i (alFrame k m f)).det ≠ 0 :=
    (mem_chartSet i (alFrameStiefel k m f)).mp
      ((mem_baseSet_iff i (alFrameStiefel k m f)).mp hb)
  refine hb' (Matrix.det_eq_zero_of_column_eq_zero (lastk (k + 1) (by omega)) (fun jj => ?_))
  rw [frameMatrix_alChartVal, alFrame_last, baseVec_ofLp, if_neg]
  exact fun hh => h (hh ▸ alChartVal_mem i jj)

theorem not_mem_last_of_mem_alOmega (i : ChartIdx (k + 1) m) {b : OG k m}
    (hb : alOmega k m b ∈ baseSet i) : alLast k m ∈ i.1 := by
  by_contra h
  exact mem_alOmega_baseSet_eq_empty i h b hb

theorem comap_baseSet_eq_downChart (i : ChartIdx (k + 1) m) (h : alLast k m ∈ i.1) :
    (Work.Thom.bundleComap (tautologicalBundle (k + 1) m) (alOmegaCM k m)).baseSet i
      = baseSet (downChart i h) := by
  ext b
  rw [Work.Thom.bundleComap_baseSet]
  change alOmega k m b ∈ baseSet i ↔ b ∈ baseSet (downChart i h)
  exact mem_baseSet_downChart_iff_alOmega i h

theorem comap_baseSet_eq_empty_of_not_mem_last (i : ChartIdx (k + 1) m) (h : alLast k m ∉ i.1) :
    (Work.Thom.bundleComap (tautologicalBundle (k + 1) m) (alOmegaCM k m)).baseSet i = ∅ := by
  refine Set.eq_empty_iff_forall_notMem.mpr (fun b hb => ?_)
  rw [Work.Thom.bundleComap_baseSet] at hb
  exact mem_alOmega_baseSet_eq_empty i h b hb

end

end Work.ThomBordism.Grassmann.Probe2
