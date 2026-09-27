import Mathlib
import Submission.Work.KT.Defs
import Submission.Work.KT.Basic
import Submission.Work.KT.HopfK.Basic
import Submission.Work.KT.HopfK.Cone
import Submission.Work.KT.hk_rotation
import Submission.Work.KT.rel_cancel
import Submission.Work.KT.homInv_cls_eq_of_conj
import Submission.Work.KT.hkWDefs
import Submission.Work.KT.hkW_diag
import Submission.Work.KT.hkW_class
import Submission.Work.KT.K0map.map_comp

set_option maxHeartbeats 4000000

namespace Work.KT

open Matrix

noncomputable section

/-! ## 1. `map` lemmas for the block matrices -/

lemma hk_reindex_map {R S : Type} [Ring R] [Ring S] (φ : R →+* S) {p : ℕ}
    (M : Matrix (Fin p ⊕ Fin p) (Fin p ⊕ Fin p) R) :
    (Matrix.reindex finSumFinEquiv finSumFinEquiv M).map φ
      = Matrix.reindex finSumFinEquiv finSumFinEquiv (M.map φ) := by
  rw [Matrix.reindex_apply, Matrix.reindex_apply, Matrix.submatrix_map]

lemma hk_one_sub_map {R S : Type} [Ring R] [Ring S] (φ : R →+* S) {p : ℕ}
    (C : Matrix (Fin p) (Fin p) R) :
    ((1 : Matrix (Fin p) (Fin p) R) - C).map φ = 1 - C.map φ := by
  rw [Matrix.map_sub (⇑φ) (fun a b => map_sub φ a b),
    Matrix.map_one (⇑φ) (map_zero φ) (map_one φ)]

lemma Wblk_map {R S : Type} [Ring R] [Ring S] (φ : R →+* S) {p : ℕ}
    (C : Matrix (Fin p) (Fin p) R) :
    (Wblk p C).map φ = Wblk p (C.map φ) := by
  unfold Wblk
  rw [hk_reindex_map φ, Matrix.fromBlocks_map C (1 - C) (1 - C) C (⇑φ), hk_one_sub_map φ C]

lemma Dblk_map {R S : Type} [Ring R] [Ring S] (φ : R →+* S) {p : ℕ}
    (X C : Matrix (Fin p) (Fin p) R) :
    (Dblk p X C).map φ = Dblk p (X.map φ) (C.map φ) := by
  unfold Dblk
  rw [hk_reindex_map φ, Matrix.fromBlocks_map X 0 0 (1 - C) (⇑φ),
    Matrix.map_zero (⇑φ) (map_zero φ), hk_one_sub_map φ C]

lemma rotMat_map {R S : Type} [CommRing R] [CommRing S] (φ : R →+* S) (p : ℕ)
    (c s : R) : (rotMat p c s).map φ = rotMat p (φ c) (φ s) := by
  have hc : (c • (1 : Matrix (Fin p) (Fin p) R)).map φ = (φ c) • (1 : Matrix (Fin p) (Fin p) S) := by
    rw [Matrix.map_smul' (⇑φ) c 1 (fun a b => map_mul φ a b),
      Matrix.map_one (⇑φ) (map_zero φ) (map_one φ)]
  have hs : (s • (1 : Matrix (Fin p) (Fin p) R)).map φ = (φ s) • (1 : Matrix (Fin p) (Fin p) S) := by
    rw [Matrix.map_smul' (⇑φ) s 1 (fun a b => map_mul φ a b),
      Matrix.map_one (⇑φ) (map_zero φ) (map_one φ)]
  have hns : ((-s) • (1 : Matrix (Fin p) (Fin p) R)).map φ
      = (-(φ s)) • (1 : Matrix (Fin p) (Fin p) S) := by
    rw [Matrix.map_smul' (⇑φ) (-s) 1 (fun a b => map_mul φ a b),
      Matrix.map_one (⇑φ) (map_zero φ) (map_one φ), map_neg]
  unfold rotMat
  rw [hk_reindex_map φ,
    Matrix.fromBlocks_map (c • (1 : Matrix (Fin p) (Fin p) R))
      ((-s) • (1 : Matrix (Fin p) (Fin p) R)) (s • (1 : Matrix (Fin p) (Fin p) R))
      (c • (1 : Matrix (Fin p) (Fin p) R)) (⇑φ)]
  rw [hc, hns, hs]

lemma rotMatInv_map {R S : Type} [CommRing R] [CommRing S] (φ : R →+* S) (p : ℕ)
    (c s : R) : (rotMatInv p c s).map φ = rotMatInv p (φ c) (φ s) := by
  have hc : (c • (1 : Matrix (Fin p) (Fin p) R)).map φ = (φ c) • (1 : Matrix (Fin p) (Fin p) S) := by
    rw [Matrix.map_smul' (⇑φ) c 1 (fun a b => map_mul φ a b),
      Matrix.map_one (⇑φ) (map_zero φ) (map_one φ)]
  have hs : (s • (1 : Matrix (Fin p) (Fin p) R)).map φ = (φ s) • (1 : Matrix (Fin p) (Fin p) S) := by
    rw [Matrix.map_smul' (⇑φ) s 1 (fun a b => map_mul φ a b),
      Matrix.map_one (⇑φ) (map_zero φ) (map_one φ)]
  have hns : ((-s) • (1 : Matrix (Fin p) (Fin p) R)).map φ
      = (-(φ s)) • (1 : Matrix (Fin p) (Fin p) S) := by
    rw [Matrix.map_smul' (⇑φ) (-s) 1 (fun a b => map_mul φ a b),
      Matrix.map_one (⇑φ) (map_zero φ) (map_one φ), map_neg]
  unfold rotMatInv
  rw [hk_reindex_map φ,
    Matrix.fromBlocks_map (c • (1 : Matrix (Fin p) (Fin p) R))
      (s • (1 : Matrix (Fin p) (Fin p) R)) ((-s) • (1 : Matrix (Fin p) (Fin p) R))
      (c • (1 : Matrix (Fin p) (Fin p) R)) (⇑φ)]
  rw [hc, hs, hns]

/-! ## 2. `diagMat` under `Mat.map` and class bookkeeping -/

lemma rotMat_map_eval {T : Type} [TopologicalSpace T] (t : T) (p : ℕ) (c s : C(T, ℂ)) :
    (rotMat p c s).map (evalC t) = rotMat p (c t) (s t) := by
  have h := rotMat_map (φ := (evalC t).toRingHom) p c s
  simpa using h

lemma rotMatInv_map_eval {T : Type} [TopologicalSpace T] (t : T) (p : ℕ) (c s : C(T, ℂ)) :
    (rotMatInv p c s).map (evalC t) = rotMatInv p (c t) (s t) := by
  have h := rotMatInv_map (φ := (evalC t).toRingHom) p c s
  simpa using h

lemma hk_reindex_map_eval {T : Type} [TopologicalSpace T] (t : T) {p : ℕ}
    (M : Matrix (Fin p ⊕ Fin p) (Fin p ⊕ Fin p) C(T, ℂ)) :
    (Matrix.reindex finSumFinEquiv finSumFinEquiv M).map (evalC t)
      = Matrix.reindex finSumFinEquiv finSumFinEquiv (M.map (evalC t)) :=
  hk_reindex_map (evalC t).toRingHom M

lemma map_kronMat_eval {T : Type} [TopologicalSpace T] (t : T) {n : ℕ}
    (M N : Matrix (Fin n) (Fin n) C(T, ℂ)) :
    (kronMat M N).map (evalC t) = kronMat (M.map (evalC t)) (N.map (evalC t)) :=
  map_kronMat (evalC t).toRingHom M N

lemma fromBlocks_kron_map {A B : Type} [Ring A] [Ring B] (φ : A →+* B) {n : ℕ}
    (P1 P2 Q1 Q2 : Matrix (Fin n) (Fin n) A) :
    (Matrix.reindex finSumFinEquiv finSumFinEquiv
        (Matrix.fromBlocks (kronMat P1 P2) 0 0 (kronMat Q1 Q2))).map φ
      = Matrix.reindex finSumFinEquiv finSumFinEquiv
        (Matrix.fromBlocks (kronMat (P1.map φ) (P2.map φ)) 0 0
          (kronMat (Q1.map φ) (Q2.map φ))) := by
  rw [hk_reindex_map, Matrix.fromBlocks_map, Matrix.map_zero (⇑φ) (map_zero φ),
    map_kronMat, map_kronMat]

lemma Mat.diagMat_map {R S : Type} [Ring R] [Ring S] (φ : R →+* S) (r n : ℕ) :
    (diagMat R r n).map φ = diagMat S r n := by
  unfold diagMat Mat.map
  simp only [Sigma.mk.injEq, heq_eq_eq, true_and]
  ext i j
  rw [Matrix.map_apply, Matrix.diagonal_apply, Matrix.diagonal_apply]
  by_cases h : i = j
  · subst h
    rw [if_pos rfl]
    by_cases hr : (i : ℕ) < r <;> simp [hr]
  · rw [if_neg h, if_neg h, map_zero]

lemma cls_diagMat_cast {R : Type} [Ring R] {r r' m k : ℕ} (hr : r = r') (hm : m = k) :
    cls (diagMat R r m) = cls (diagMat R r' k) := by
  rw [hr, hm]

/-! ## 3. The Tietze-setup: base coordinate functions -/

/-- The plain inclusion `∂D_V → S_V` (the boundary sphere inside the ball). -/
def sphBdry (V : Type) [NormedAddCommGroup V] : C(bdry V, Sph V) :=
  ⟨fun y => ⟨(y.1 : V), mem_sphere_zero_iff_norm.mpr y.2⟩,
   Continuous.subtype_mk (continuous_subtype_val.comp continuous_subtype_val) _⟩

lemma hk_continuous_tgtHeight (m : ℕ) : Continuous (tgtHeight m) := by
  unfold tgtHeight
  fun_prop

/-- The clamped height `t ↦ min 1 (max 0 (h t + 1/2)) ∈ [0,1]` on the target sphere. -/
def chiB (m : ℕ) : C(Tgt m, ℝ) :=
  ⟨fun t => min 1 (max 0 (tgtHeight m t + 1 / 2)), by
    exact continuous_const.min (continuous_const.max
      ((hk_continuous_tgtHeight m).add continuous_const))⟩

/-- `cos (π/2 · χ)`. -/
def hkCos (m : ℕ) : C(Tgt m, ℂ) :=
  ⟨fun t => (Real.cos (Real.pi / 2 * chiB m t) : ℂ), by
    exact Complex.continuous_ofReal.comp
      (Real.continuous_cos.comp (continuous_const.mul (chiB m).continuous))⟩

/-- `sin (π/2 · χ)`. -/
def hkSin (m : ℕ) : C(Tgt m, ℂ) :=
  ⟨fun t => (Real.sin (Real.pi / 2 * chiB m t) : ℂ), by
    exact Complex.continuous_ofReal.comp
      (Real.continuous_sin.comp (continuous_const.mul (chiB m).continuous))⟩

lemma chiB_apply (m : ℕ) (t : Tgt m) :
    chiB m t = min 1 (max 0 (tgtHeight m t + 1 / 2)) := rfl

@[simp] lemma hkCos_apply (m : ℕ) (t : Tgt m) :
    hkCos m t = (Real.cos (Real.pi / 2 * chiB m t) : ℂ) := rfl

@[simp] lemma hkSin_apply (m : ℕ) (t : Tgt m) :
    hkSin m t = (Real.sin (Real.pi / 2 * chiB m t) : ℂ) := rfl

lemma hkCos_sq_add_hkSin_sq (m : ℕ) : hkCos m * hkCos m + hkSin m * hkSin m = 1 := by
  ext t
  have h := Real.cos_sq_add_sin_sq (Real.pi / 2 * chiB m t)
  rw [pow_two, pow_two] at h
  simp only [ContinuousMap.mul_apply, ContinuousMap.add_apply, ContinuousMap.one_apply,
    hkCos_apply, hkSin_apply]
  rw [← Complex.ofReal_mul, ← Complex.ofReal_mul, ← Complex.ofReal_add, h, Complex.ofReal_one]

lemma chiB_eq_one (m : ℕ) {t : Tgt m} (h : 1 / 2 ≤ tgtHeight m t) : chiB m t = 1 := by
  have h1 : (1 : ℝ) ≤ max 0 (tgtHeight m t + 1 / 2) := le_trans (by linarith) (le_max_right _ _)
  have h2 : (0 : ℝ) ≤ tgtHeight m t + 1 / 2 := by linarith
  rw [chiB_apply, min_eq_left h1]

lemma chiB_eq_zero (m : ℕ) {t : Tgt m} (h : tgtHeight m t ≤ -(1 / 2)) : chiB m t = 0 := by
  have h1 : max 0 (tgtHeight m t + 1 / 2) = 0 := max_eq_left (by linarith)
  have h2 : (0 : ℝ) ≤ 1 := by norm_num
  rw [chiB_apply, h1, min_eq_right h2]

lemma hkCos_eq_zero_of (m : ℕ) {t : Tgt m} (h : 1 / 2 ≤ tgtHeight m t) : hkCos m t = 0 := by
  rw [hkCos_apply, chiB_eq_one m h, mul_one, Real.cos_pi_div_two, Complex.ofReal_zero]

lemma hkSin_eq_one_of (m : ℕ) {t : Tgt m} (h : 1 / 2 ≤ tgtHeight m t) : hkSin m t = 1 := by
  rw [hkSin_apply, chiB_eq_one m h, mul_one, Real.sin_pi_div_two, Complex.ofReal_one]

lemma hkCos_eq_one_of (m : ℕ) {t : Tgt m} (h : tgtHeight m t ≤ -(1 / 2)) : hkCos m t = 1 := by
  rw [hkCos_apply, chiB_eq_zero m h, mul_zero, Real.cos_zero, Complex.ofReal_one]

lemma hkSin_eq_zero_of (m : ℕ) {t : Tgt m} (h : tgtHeight m t ≤ -(1 / 2)) : hkSin m t = 0 := by
  rw [hkSin_apply, chiB_eq_zero m h, mul_zero, Real.sin_zero, Complex.ofReal_zero]



/-! ## 4. The rotation, the `W`-involution and the `W`-construction -/

lemma hk_diagMap {A B : Type} [Ring A] [Ring B] {n : ℕ} (φ : A →+* B) (d : Fin n → A) :
    (Matrix.diagonal d).map φ = Matrix.diagonal (fun i => φ (d i)) := by
  ext i j
  rw [Matrix.map_apply, Matrix.diagonal_apply, Matrix.diagonal_apply]
  by_cases h : i = j
  · subst h; simp
  · simp [h]

/-- The reindexed block matrix `diag(1_p, 0)` of size `p+p`. -/
def oneBlk (R : Type) [Ring R] (p : ℕ) : Matrix (Fin (p + p)) (Fin (p + p)) R :=
  Matrix.reindex finSumFinEquiv finSumFinEquiv
    (Matrix.fromBlocks (1 : Matrix (Fin p) (Fin p) R)
      (0 : Matrix (Fin p) (Fin p) R) (0 : Matrix (Fin p) (Fin p) R)
      (0 : Matrix (Fin p) (Fin p) R))

lemma reindex_fromBlocks_one_eq_map (T : Type) [TopologicalSpace T] (p : ℕ) :
    oneBlk C(T, ℂ) p = (oneBlk ℂ p).map (algebraMap ℂ C(T, ℂ)) := by
  unfold oneBlk
  rw [hk_reindex_map (algebraMap ℂ C(T, ℂ)), Matrix.fromBlocks_map,
    Matrix.map_one (⇑(algebraMap ℂ C(T, ℂ))) (map_zero _) (map_one _)]
  simp only [Matrix.map_zero (⇑(algebraMap ℂ C(T, ℂ))) (map_zero _)]

lemma reindex_fromBlocks_one_apply_const (T : Type) [TopologicalSpace T] (p : ℕ)
    (i j : Fin (p + p)) (s s' : T) :
    oneBlk C(T, ℂ) p i j s = oneBlk C(T, ℂ) p i j s' := by
  rw [reindex_fromBlocks_one_eq_map T p]
  simp only [Matrix.map_apply]
  rfl

/-- **Pointwise rotation identity of the `W`-construction.** -/
lemma hkW_rot_cases {n : ℕ} (P Q E : Matrix (Fin n) (Fin n) ℂ) (c s : ℂ)
    (hcs : c * c + s * s = 1)
    (hcase : (P = E ∧ c = 0 ∧ s = 1) ∨ (P = E ∧ Q = E) ∨ (Q = E ∧ c = 1 ∧ s = 0)) :
    rotMat (n * n) c s *
        (Matrix.reindex finSumFinEquiv finSumFinEquiv
          (Matrix.fromBlocks (kronMat P E) 0 0 (kronMat E Q)))
      * rotMatInv (n * n) c s
      = Matrix.reindex finSumFinEquiv finSumFinEquiv
          (Matrix.fromBlocks (kronMat P Q) 0 0 (kronMat E E)) := by
  rcases hcase with ⟨hPE, hc0, hs1⟩ | ⟨hPE, hQE⟩ | ⟨hQE, hc1, hs0⟩
  · rw [hPE, hc0, hs1]
    refine rotMat_conj (kronMat E E) (kronMat E Q) (kronMat E E) (kronMat E Q) 0 1 ?_ ?_ ?_
    · simp
    · simp
    · simp
  · rw [hPE, hQE]
    refine rotMat_conj (kronMat E E) (kronMat E E) (kronMat E E) (kronMat E E) c s ?_ ?_ ?_
    · rw [← add_smul, hcs, one_smul]
    · rw [sub_self, smul_zero]
    · rw [← add_smul, add_comm (s * s) (c * c), hcs, one_smul]
  · rw [hQE, hc1, hs0]
    refine rotMat_conj (kronMat P E) (kronMat P E) (kronMat E E) (kronMat E E) 1 0 ?_ ?_ ?_
    · simp
    · simp
    · simp

/-- **The disk side of the relative product** (for the Hopf construction `f = hopfKMap m μ`).
Let `p`, `q` be idempotent matrices over the mapping cone `C_f` which are the constant
`e = diag(1_r,0)` on the cell collars `{‖y‖ ≥ 1-δ}`, `{‖x‖ ≥ 1-δ}` and on the base caps
`{tgtHeight ≥ -1/2}`, `{tgtHeight ≤ 1/2}`.  Then there is an idempotent `Z` of size `4(n*n)`, built
from the *cell parts* of `p`, `q`, `e` and the rotation angle
`θ = clamp((‖y‖-‖x‖)/δ + 1/2, 0, 1)` by the `W`-construction (an explicit block matrix with entries
in `prodAlg (Eu m) (Eu m) ⊆ C(Ball (Eu m × Eu m), ℂ)`), such that

* `Z` is the constant `diag(1_{2n²},0)` on the boundary of the cell (so that it is an element of
  `Mat (Kpair (Eu m × Eu m))`, as asserted), and
* its class, pushed forward along `relToCone`, is the relative product
  `[p ⊗ q ⊕ e ⊗ e] - [p ⊗ e ⊕ e ⊗ q]` computed over `coneAlg f`.

Construction: `Q₁ = p ⊗ q ⊕ e ⊗ e`, `Q₂ = p ⊗ e ⊕ e ⊗ q`, `Q₂' = U Q₂ U⁻¹` with `U` the block
rotation by angle `(π/2)·θ`, `W = [[Q₂', 1-Q₂'],[1-Q₂',Q₂']]` (an involution) and
`Z = W (Q₁ ⊕ (1-Q₂')) W`.  The second bullet is proved by comparing with the same construction on
the cone: because θ depends only on `(‖x‖,‖y‖)` and `f` determines those on the boundary, θ is the
cell part of an element `χ ∈ coneAlg f`; the cone-level `W`-matrix is then the pair
`(const diag, Z) = relToCone Z`, and its class differs from `[diag]` by `[Q₁] - [Q₂]` because `W`
is an involution and `Q₂'` is conjugate to `Q₂`. -/
theorem hk_relprod (m : ℕ) (μ : C(Sph (Eu m) × Sph (Eu m), Sph (Eu m))) (n r : ℕ) (δ : ℝ)
    (hδ : 0 < δ)
    (p q : Matrix (Fin n) (Fin n) (coneAlg (hopfKMap m μ))) (hp : p * p = p) (hq : q * q = q)
    (hpc : ∀ z : Ball (Eu m × Eu m), 1 - δ ≤ ‖(z : Eu m × Eu m).2‖ →
      p.map (evalD m (hopfKMap m μ) z) = diagIdemMat r n)
    (hqc : ∀ z : Ball (Eu m × Eu m), 1 - δ ≤ ‖(z : Eu m × Eu m).1‖ →
      q.map (evalD m (hopfKMap m μ) z) = diagIdemMat r n)
    (hpb : ∀ t : Tgt m, t ∈ capTplus m →
      p.map (evalT m (hopfKMap m μ) t) = diagIdemMat r n)
    (hqb : ∀ t : Tgt m, t ∈ capTminus m →
      q.map (evalT m (hopfKMap m μ) t) = diagIdemMat r n)
    (y0 : Ball (Eu m × Eu m)) (hy0 : y0 ∈ bdry (Eu m × Eu m)) :
    ∃ Z : Mat (Kpair (Eu m × Eu m)), Mat.IsIdem Z ∧ Z.1 = 4 * (n * n) ∧
      K0.mapA (relToCone (hopfKMap m μ) y0 hy0)
          (cls Z - cls (diagMat (Kpair (Eu m × Eu m)) (2 * (n * n)) (4 * (n * n)))) =
        cls (Mat.sum (Mat.kron ⟨n, p⟩ ⟨n, q⟩)
          (Mat.kron (coneDiag m (hopfKMap m μ) r n) (coneDiag m (hopfKMap m μ) r n))) -
        cls (Mat.sum (Mat.kron ⟨n, p⟩ (coneDiag m (hopfKMap m μ) r n))
          (Mat.kron (coneDiag m (hopfKMap m μ) r n) ⟨n, q⟩)) := by
  classical
  -- A local commutative-ring structure on the mapping-cone algebra (needed for `rotMat`).
  letI : CommRing (coneAlg (hopfKMap m μ)) :=
    { (inferInstance : Ring (coneAlg (hopfKMap m μ))) with
      mul_comm := coneAlg_comm m (hopfKMap m μ) }
  -- ## The angle function: an element of the mapping-cone algebra
  have hclosed : IsClosed (bdry (Eu m × Eu m)) :=
    isClosed_eq (continuous_norm.comp continuous_subtype_val) continuous_const
  let phiR : C(bdry (Eu m × Eu m), ℝ) :=
    ⟨fun y => chiB m (hopfKMap m μ (sphBdry (Eu m × Eu m) y)),
      (chiB m).continuous.comp ((hopfKMap m μ).continuous.comp (sphBdry _).continuous)⟩
  obtain ⟨chiExt, hchiExt⟩ := ContinuousMap.exists_restrict_eq (Y := ℝ) hclosed phiR
  have hchiExt_apply : ∀ y : bdry (Eu m × Eu m), chiExt y = phiR y := by
    intro y
    have h := congrArg (fun g : C(bdry (Eu m × Eu m), ℝ) => g y) hchiExt
    rwa [ContinuousMap.restrict_apply] at h
  let chiBC : C(Tgt m, ℂ) :=
    ⟨fun t => (chiB m t : ℂ), Complex.continuous_ofReal.comp (chiB m).continuous⟩
  let cellChi : C(Ball (Eu m × Eu m), ℂ) :=
    ⟨fun z => (chiExt z : ℂ), Complex.continuous_ofReal.comp chiExt.continuous⟩
  have hchi_mem : (chiBC, cellChi) ∈ coneAlg (hopfKMap m μ) := by
    intro y hy
    show (chiExt y : ℂ) = chiBC (hopfKMap m μ ⟨(y : Eu m × Eu m), mem_sphere_zero_iff_norm.mpr hy⟩)
    rw [hchiExt_apply ⟨y, hy⟩]
    rfl
  let cellCos : C(Ball (Eu m × Eu m), ℂ) :=
    ⟨fun z => (Real.cos (Real.pi / 2 * chiExt z) : ℂ),
      Complex.continuous_ofReal.comp
        (Real.continuous_cos.comp (continuous_const.mul chiExt.continuous))⟩
  let cellSin : C(Ball (Eu m × Eu m), ℂ) :=
    ⟨fun z => (Real.sin (Real.pi / 2 * chiExt z) : ℂ),
      Complex.continuous_ofReal.comp
        (Real.continuous_sin.comp (continuous_const.mul chiExt.continuous))⟩
  have hc_mem : (hkCos m, cellCos) ∈ coneAlg (hopfKMap m μ) := by
    intro y hy
    show (Real.cos (Real.pi / 2 * chiExt y) : ℂ)
      = hkCos m (hopfKMap m μ ⟨(y : Eu m × Eu m), mem_sphere_zero_iff_norm.mpr hy⟩)
    rw [hchiExt_apply ⟨y, hy⟩]
    rfl
  have hs_mem : (hkSin m, cellSin) ∈ coneAlg (hopfKMap m μ) := by
    intro y hy
    show (Real.sin (Real.pi / 2 * chiExt y) : ℂ)
      = hkSin m (hopfKMap m μ ⟨(y : Eu m × Eu m), mem_sphere_zero_iff_norm.mpr hy⟩)
    rw [hchiExt_apply ⟨y, hy⟩]
    rfl
  let cA : coneAlg (hopfKMap m μ) := ⟨(hkCos m, cellCos), hc_mem⟩
  let sA : coneAlg (hopfKMap m μ) := ⟨(hkSin m, cellSin), hs_mem⟩
  have hcsA : cA * cA + sA * sA = 1 := by
    apply Subtype.ext
    refine Prod.ext ?_ ?_
    · show hkCos m * hkCos m + hkSin m * hkSin m = 1
      exact hkCos_sq_add_hkSin_sq m
    · ext z
      show (Real.cos (Real.pi / 2 * chiExt z) : ℂ) * (Real.cos (Real.pi / 2 * chiExt z) : ℂ)
        + (Real.sin (Real.pi / 2 * chiExt z) : ℂ) * (Real.sin (Real.pi / 2 * chiExt z) : ℂ) = 1
      have h := Real.cos_sq_add_sin_sq (Real.pi / 2 * chiExt z)
      rw [pow_two, pow_two] at h
      rw [← Complex.ofReal_mul, ← Complex.ofReal_mul, ← Complex.ofReal_add, h, Complex.ofReal_one]
  -- ## The matrices over the cone algebra
  let E : Mat (coneAlg (hopfKMap m μ)) := coneDiag m (hopfKMap m μ) r n
  have hEidem : E.IsIdem := coneDiag_isIdem m (hopfKMap m μ) r n
  have hpidem : Mat.IsIdem (⟨n, p⟩ : Mat (coneAlg (hopfKMap m μ))) := hp
  have hqidem : Mat.IsIdem (⟨n, q⟩ : Mat (coneAlg (hopfKMap m μ))) := hq
  let Q1m : Matrix (Fin (n * n + n * n)) (Fin (n * n + n * n)) (coneAlg (hopfKMap m μ)) :=
    Matrix.reindex finSumFinEquiv finSumFinEquiv
      (Matrix.fromBlocks (kronMat p q) 0 0 (kronMat E.2 E.2))
  let Q2m : Matrix (Fin (n * n + n * n)) (Fin (n * n + n * n)) (coneAlg (hopfKMap m μ)) :=
    Matrix.reindex finSumFinEquiv finSumFinEquiv
      (Matrix.fromBlocks (kronMat p E.2) 0 0 (kronMat E.2 q))
  let Q1 : Mat (coneAlg (hopfKMap m μ)) := ⟨n * n + n * n, Q1m⟩
  let Q2 : Mat (coneAlg (hopfKMap m μ)) := ⟨n * n + n * n, Q2m⟩
  have hQ1idem : Mat.IsIdem Q1 :=
    Mat.sum_idem
      (Mat.kron_idem (coneAlg_comm m (hopfKMap m μ)) (p := (⟨n, p⟩ : Mat _)) (q := (⟨n, q⟩ : Mat _)) hpidem hqidem)
      (Mat.kron_idem (coneAlg_comm m (hopfKMap m μ)) (p := E) (q := E) hEidem hEidem)
  have hQ2idem : Mat.IsIdem Q2 :=
    Mat.sum_idem
      (Mat.kron_idem (coneAlg_comm m (hopfKMap m μ)) (p := (⟨n, p⟩ : Mat _)) (q := E) hpidem hEidem)
      (Mat.kron_idem (coneAlg_comm m (hopfKMap m μ)) (p := E) (q := (⟨n, q⟩ : Mat _)) hEidem hqidem)
  let U : Matrix (Fin (n * n + n * n)) (Fin (n * n + n * n)) (coneAlg (hopfKMap m μ)) :=
    rotMat (n * n) cA sA
  let Q2' : Matrix (Fin (n * n + n * n)) (Fin (n * n + n * n)) (coneAlg (hopfKMap m μ)) :=
    U * Q2m * rotMatInv (n * n) cA sA
  have hinv : rotMatInv (n * n) cA sA * U = 1 :=
    rotMatInv_mul_rotMat (m := n * n) cA sA hcsA
  have hinv' : U * rotMatInv (n * n) cA sA = 1 :=
    rotMat_mul_rotMatInv (m := n * n) cA sA hcsA
  have hQ2'idem : Mat.IsIdem (⟨n * n + n * n, Q2'⟩ : Mat (coneAlg (hopfKMap m μ))) := by
    show Q2' * Q2' = Q2'
    have hkey : U * Q2m * rotMatInv (n * n) cA sA * (U * Q2m * rotMatInv (n * n) cA sA)
        = U * Q2m * (rotMatInv (n * n) cA sA * U) * Q2m * rotMatInv (n * n) cA sA := by
      noncomm_ring
    rw [hkey, hinv]
    simp only [Matrix.mul_one]
    show U * Q2m * Q2m * rotMatInv (n * n) cA sA = U * Q2m * rotMatInv (n * n) cA sA
    rw [Matrix.mul_assoc U Q2m Q2m, show Q2m * Q2m = Q2m from hQ2idem]
  have hCY : cls (⟨n * n + n * n, Q2'⟩ : Mat (coneAlg (hopfKMap m μ))) = cls Q2 := by
    refine homInv_cls_eq_of_conj (p := Q2') (q := Q2m)
      (show Q2' * Q2' = Q2' from hQ2'idem)
      (show Q2m * Q2m = Q2m from hQ2idem)
      ⟨U, rotMatInv (n * n) cA sA, hinv', hinv⟩ ?_
    show U * Q2m = U * Q2m * rotMatInv (n * n) cA sA * U
    simp only [Matrix.mul_assoc]
    rw [hinv, Matrix.mul_one]
  let Wm : Matrix (Fin ((n * n + n * n) + (n * n + n * n)))
      (Fin ((n * n + n * n) + (n * n + n * n))) (coneAlg (hopfKMap m μ)) :=
    Wblk (n * n + n * n) Q2'
  let Dm : Matrix (Fin ((n * n + n * n) + (n * n + n * n)))
      (Fin ((n * n + n * n) + (n * n + n * n))) (coneAlg (hopfKMap m μ)) :=
    Dblk (n * n + n * n) Q1m Q2'
  let ZAm : Matrix (Fin ((n * n + n * n) + (n * n + n * n)))
      (Fin ((n * n + n * n) + (n * n + n * n))) (coneAlg (hopfKMap m μ)) :=
    Wm * Dm * Wm
  have hZAidem : ZAm * ZAm = ZAm := by
    have hWidem : Wm * Wm = 1 := Wblk_mul_self (show Q2' * Q2' = Q2' from hQ2'idem)
    have hDidem : Dm * Dm = Dm :=
      Mat.sum_idem (p := Q1) (q := (⟨n * n + n * n, 1 - Q2'⟩ : Mat (coneAlg (hopfKMap m μ))))
        hQ1idem
        (Mat.isIdem_one_sub (p := (⟨n * n + n * n, Q2'⟩ : Mat (coneAlg (hopfKMap m μ))))
          hQ2'idem)
    have hkey : Wm * Dm * Wm * (Wm * Dm * Wm) = Wm * (Dm * (Wm * Wm) * Dm) * Wm := by
      noncomm_ring
    rw [hkey, hWidem]
    simp only [Matrix.mul_one]
    rw [hDidem]
  let ZA : Mat (coneAlg (hopfKMap m μ)) := ⟨(n * n + n * n) + (n * n + n * n), ZAm⟩
  have hclass : cls ZA = cls Q1 - cls Q2 + cls (diagMat (coneAlg (hopfKMap m μ))
      (n * n + n * n) ((n * n + n * n) + (n * n + n * n))) :=
    hkW_class (coneAlg_comm m (hopfKMap m μ)) Q1m Q2m Q2'
      (show Q1m * Q1m = Q1m from hQ1idem)
      (show Q2' * Q2' = Q2' from hQ2'idem) hCY
  have hclass' : cls ZA - cls (diagMat (coneAlg (hopfKMap m μ))
      (n * n + n * n) ((n * n + n * n) + (n * n + n * n))) = cls Q1 - cls Q2 := by
    rw [hclass]
    abel
  -- ## The base level: `Q₂'` restricts to `Q₁`
  have hbase : Q2'.map (coneToT (hopfKMap m μ)).toRingHom = Q1m.map (coneToT (hopfKMap m μ)).toRingHom := by
    have hUmap : U.map (coneToT (hopfKMap m μ)).toRingHom = rotMat (n * n) (hkCos m) (hkSin m) := by
      show (rotMat (n * n) cA sA).map (coneToT (hopfKMap m μ)).toRingHom = _
      rw [rotMat_map]
      congr 1
    have hUimap : (rotMatInv (n * n) cA sA).map (coneToT (hopfKMap m μ)).toRingHom
        = rotMatInv (n * n) (hkCos m) (hkSin m) := by
      rw [rotMatInv_map]
      congr 1
    show (U * Q2m * rotMatInv (n * n) cA sA).map (coneToT (hopfKMap m μ)).toRingHom
      = Q1m.map (coneToT (hopfKMap m μ)).toRingHom
    rw [Matrix.map_mul, Matrix.map_mul, hUmap, hUimap]
    apply rot_eq_of_eval
    intro t
    rw [rot_eval_map_mul, rot_eval_map_mul, rotMat_map_eval, rotMatInv_map_eval]
    rw [show (Q2m.map (coneToT (hopfKMap m μ)).toRingHom).map (evalC t)
          = Q2m.map (evalT m (hopfKMap m μ) t).toRingHom from by
        rw [Matrix.map_map]; rfl,
      show (Q1m.map (coneToT (hopfKMap m μ)).toRingHom).map (evalC t)
          = Q1m.map (evalT m (hopfKMap m μ) t).toRingHom from by
        rw [Matrix.map_map]; rfl]
    rw [show Q2m.map (evalT m (hopfKMap m μ) t).toRingHom
          = Matrix.reindex finSumFinEquiv finSumFinEquiv
            (Matrix.fromBlocks (kronMat (p.map (evalT m (hopfKMap m μ) t).toRingHom)
              (E.2.map (evalT m (hopfKMap m μ) t).toRingHom)) 0 0
              (kronMat (E.2.map (evalT m (hopfKMap m μ) t).toRingHom)
                (q.map (evalT m (hopfKMap m μ) t).toRingHom))) from by
        show (Matrix.reindex finSumFinEquiv finSumFinEquiv
            (Matrix.fromBlocks (kronMat p E.2) 0 0 (kronMat E.2 q))).map _ = _
        exact fromBlocks_kron_map (evalT m (hopfKMap m μ) t).toRingHom p E.2 E.2 q,
      show Q1m.map (evalT m (hopfKMap m μ) t).toRingHom
          = Matrix.reindex finSumFinEquiv finSumFinEquiv
            (Matrix.fromBlocks (kronMat (p.map (evalT m (hopfKMap m μ) t).toRingHom)
              (q.map (evalT m (hopfKMap m μ) t).toRingHom)) 0 0
              (kronMat (E.2.map (evalT m (hopfKMap m μ) t).toRingHom)
                (E.2.map (evalT m (hopfKMap m μ) t).toRingHom))) from by
        show (Matrix.reindex finSumFinEquiv finSumFinEquiv
            (Matrix.fromBlocks (kronMat p q) 0 0 (kronMat E.2 E.2))).map _ = _
        exact fromBlocks_kron_map (evalT m (hopfKMap m μ) t).toRingHom p q E.2 E.2]
    have hEev : E.2.map (evalT m (hopfKMap m μ) t).toRingHom = diagIdemMat r n := by
      have hdiag : diagIdemMat r n
          = Matrix.diagonal (fun i : Fin n => if (i : ℕ) < r then (1 : ℂ) else 0) := rfl
      have hE2 : E.2 = Matrix.diagonal
          (fun i : Fin n => if (i : ℕ) < r then (1 : coneAlg (hopfKMap m μ)) else 0) := rfl
      rw [hE2, hdiag]
      ext i j
      rw [Matrix.map_apply, Matrix.diagonal_apply, Matrix.diagonal_apply]
      by_cases hij : i = j
      · subst hij
        by_cases hi : (i : ℕ) < r <;> simp [hi]
      · rw [if_neg hij, if_neg hij, map_zero]
    rw [hEev]
    refine hkW_rot_cases _ _ (diagIdemMat r n) (hkCos m t) (hkSin m t) ?_ ?_
    · have h := congrArg (evalC t) (hkCos_sq_add_hkSin_sq m)
      simpa using h
    · by_cases h : (1 / 2 : ℝ) ≤ tgtHeight m t
      · exact Or.inl ⟨hpb t (by show -(1 / 2 : ℝ) ≤ tgtHeight m t; linarith),
          hkCos_eq_zero_of m h, hkSin_eq_one_of m h⟩
      · rw [not_le] at h
        by_cases h' : tgtHeight m t ≤ -(1 / 2 : ℝ)
        · exact Or.inr (Or.inr ⟨hqb t (by show tgtHeight m t ≤ (1 / 2 : ℝ); linarith),
            hkCos_eq_one_of m h', hkSin_eq_zero_of m h'⟩)
        · rw [not_le] at h'
          exact Or.inr (Or.inl ⟨hpb t (by show -(1 / 2 : ℝ) ≤ tgtHeight m t; linarith),
            hqb t (by show tgtHeight m t ≤ (1 / 2 : ℝ); linarith)⟩)
  -- ## `ZA` has constant base part
  have hZAbase : ZAm.map (coneToT (hopfKMap m μ)).toRingHom = oneBlk (C(Tgt m, ℂ)) (n * n + n * n) := by
    have hWmap : Wm.map (coneToT (hopfKMap m μ)).toRingHom = Wblk (n * n + n * n) (Q1m.map (coneToT (hopfKMap m μ)).toRingHom) := by
      show (Wblk (n * n + n * n) Q2').map (coneToT (hopfKMap m μ)).toRingHom
        = Wblk (n * n + n * n) (Q1m.map (coneToT (hopfKMap m μ)).toRingHom)
      rw [Wblk_map, hbase]
    have hDmap : Dm.map (coneToT (hopfKMap m μ)).toRingHom
        = Dblk (n * n + n * n) (Q1m.map (coneToT (hopfKMap m μ)).toRingHom) (Q1m.map (coneToT (hopfKMap m μ)).toRingHom) := by
      rw [show Dm = Dblk (n * n + n * n) Q1m Q2' from rfl, Dblk_map, hbase]
    show (Wm * Dm * Wm).map _ = _
    rw [Matrix.map_mul, Matrix.map_mul, hWmap, hDmap]
    exact hkW_diag (show (Q1m.map (coneToT (hopfKMap m μ)).toRingHom)
          * (Q1m.map (coneToT (hopfKMap m μ)).toRingHom)
          = Q1m.map (coneToT (hopfKMap m μ)).toRingHom from by
      rw [← Matrix.map_mul, show Q1m * Q1m = Q1m from hQ1idem])
  have hZAbase_const : ∀ (i j : Fin ((n * n + n * n) + (n * n + n * n))) (s s' : Tgt m),
      (ZAm i j).1.1 s = (ZAm i j).1.1 s' := by
    intro i j s s'
    have hentry : (coneToT (hopfKMap m μ)).toRingHom (ZAm i j)
        = oneBlk (C(Tgt m, ℂ)) (n * n + n * n) i j := by
      have h := congrFun (congrFun hZAbase i) j
      rwa [Matrix.map_apply] at h
    rw [show (coneToT (hopfKMap m μ)).toRingHom (ZAm i j) = (ZAm i j).1.1 from rfl] at hentry
    rw [hentry]
    exact reindex_fromBlocks_one_apply_const (Tgt m) (n * n + n * n) i j s s'
  have hcell_const : ∀ (i j : Fin ((n * n + n * n) + (n * n + n * n)))
      (y y' : Ball (Eu m × Eu m)), y ∈ bdry (Eu m × Eu m) → y' ∈ bdry (Eu m × Eu m) →
      (ZAm i j).1.2 y = (ZAm i j).1.2 y' := by
    intro i j y y' hy hy'
    calc (ZAm i j).1.2 y
        = (ZAm i j).1.1 (hopfKMap m μ ⟨(y : Eu m × Eu m), mem_sphere_zero_iff_norm.mpr hy⟩) :=
          (ZAm i j).2 y hy
      _ = (ZAm i j).1.1 (hopfKMap m μ ⟨(y' : Eu m × Eu m), mem_sphere_zero_iff_norm.mpr hy'⟩) :=
          hZAbase_const i j _ _
      _ = (ZAm i j).1.2 y' := ((ZAm i j).2 y' hy').symm
  -- ## The idempotent `Z` over `Kpair`
  let Zmat : Matrix (Fin ((n * n + n * n) + (n * n + n * n)))
      (Fin ((n * n + n * n) + (n * n + n * n))) (Kpair (Eu m × Eu m)) :=
    fun i j => ⟨(ZAm i j).1.2, fun y hy y' hy' => hcell_const i j y y' hy hy'⟩
  let Z : Mat (Kpair (Eu m × Eu m)) := ⟨(n * n + n * n) + (n * n + n * n), Zmat⟩
  have hinj : Function.Injective (relToCone (hopfKMap m μ) y0 hy0) := by
    intro a b hab
    refine Subtype.ext ?_
    have h := congrArg (fun x : coneAlg (hopfKMap m μ) =>
      (x : C(Tgt m, ℂ) × C(Ball (Eu m × Eu m), ℂ)).2) hab
    exact h
  have hmapZ : Zmat.map (relToCone (hopfKMap m μ) y0 hy0).toRingHom = ZAm := by
    apply Matrix.ext
    intro i j
    rw [Matrix.map_apply]
    show relToCone (hopfKMap m μ) y0 hy0 (Zmat i j) = ZAm i j
    refine Subtype.ext ?_
    refine Prod.ext ?_ ?_
    · ext s
      show (Zmat i j).val y0 = (ZAm i j).1.1 s
      rw [hZAbase_const i j _ (hopfKMap m μ ⟨(y0 : Eu m × Eu m), mem_sphere_zero_iff_norm.mpr hy0⟩)]
      exact (ZAm i j).2 y0 hy0
    · rfl
  have hZidem : Mat.IsIdem Z := by
    show Zmat * Zmat = Zmat
    apply Matrix.ext
    intro i j
    apply hinj
    have h : ((Zmat * Zmat).map (relToCone (hopfKMap m μ) y0 hy0).toRingHom) i j
        = (Zmat.map (relToCone (hopfKMap m μ) y0 hy0).toRingHom) i j := by
      rw [Matrix.map_mul, hmapZ, hZAidem]
    simpa [Matrix.map_apply] using h
  refine ⟨Z, hZidem, ?_, ?_⟩
  · show (n * n + n * n) + (n * n + n * n) = 4 * (n * n)
    ring
  · have hmapcls : K0.mapA (relToCone (hopfKMap m μ) y0 hy0) (cls Z) = cls ZA := by
      rw [K0map.map_cls]
      unfold mapCls
      rw [if_pos hZidem]
      have hZZ : Z.map (relToCone (hopfKMap m μ) y0 hy0).toRingHom = ZA := by
        show (⟨(n * n + n * n) + (n * n + n * n),
            Zmat.map (relToCone (hopfKMap m μ) y0 hy0).toRingHom⟩ :
              Mat (coneAlg (hopfKMap m μ)))
          = ⟨(n * n + n * n) + (n * n + n * n), ZAm⟩
        rw [hmapZ]
      exact congrArg cls hZZ
    have hmapclsD : K0.mapA (relToCone (hopfKMap m μ) y0 hy0)
        (cls (diagMat (Kpair (Eu m × Eu m)) (2 * (n * n)) (4 * (n * n))))
        = cls (diagMat (coneAlg (hopfKMap m μ)) (2 * (n * n)) (4 * (n * n))) := by
      rw [K0map.map_cls]
      unfold mapCls
      rw [if_pos (diagMat_isIdem (Kpair (Eu m × Eu m)) (2 * (n * n)) (4 * (n * n)))]
      exact congrArg cls (Mat.diagMat_map (relToCone (hopfKMap m μ) y0 hy0).toRingHom
        (2 * (n * n)) (4 * (n * n)))
    have hcast : cls (diagMat (coneAlg (hopfKMap m μ)) (n * n + n * n)
        ((n * n + n * n) + (n * n + n * n)))
        = cls (diagMat (coneAlg (hopfKMap m μ)) (2 * (n * n)) (4 * (n * n))) :=
      cls_diagMat_cast (by ring) (by ring)
    rw [map_sub, hmapcls, hmapclsD, ← hcast]
    exact hclass'

end

end Work.KT
