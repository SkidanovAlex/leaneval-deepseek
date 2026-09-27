import Mathlib
import Submission.Work.KT.Defs
import Submission.Work.KT.Basic
import Submission.Work.KT.HopfK.Basic
import Submission.Work.KT.homInv_cls_eq_of_conj

/-!
# `Work.KT.hk_rotation` — the rotation trick for relative products in `K₀`

Let `ξ : T → [0,1]` be continuous, `e₀` an idempotent matrix over `ℂ`, and `p, q` idempotent
matrices over `C(T,ℂ)` with `p = e₀` wherever `ξ > 0` and `q = e₀` wherever `ξ < 1`.  Then

  `p ⊗ q ⊕ e ⊗ e`   and   `p ⊗ e ⊕ e ⊗ q`   (`e` the constant `e₀`)

are conjugate by the block rotation of angle `(π/2)ξ` and hence have the same class in `K₀`.

The proof has three layers:

* `Work.KT.rotMat`, `Work.KT.rotMatInv` — the quarter-turn block matrices `[[c,-s],[s,c]]` and its
  inverse, together with `rotMat_mul_rotMatInv`, `rotMatInv_mul_rotMat` (they are inverse to each
  other as soon as `c*c + s*s = 1`) and the *conjugation identity* `rotMat_conj`, which is pure
  block-matrix algebra given the three scalar relations `(I) (II) (III)` below.
* `Work.KT.rot_eval_*` — evaluation of matrices over `C(T,ℂ)` at a point `t : T`, so that a matrix
  identity can be checked pointwise; `kronMat_apply'`, `map_kronMat` are the entrywise facts about
  Kronecker products.
* `Work.KT.rotIdem_I`, `rotIdem_II`, `rotIdem_III` — the three scalar relations, proved pointwise
  by splitting `T` into `{ξ = 0}`, `{0 < ξ < 1}`, `{ξ = 1}`: on `{ξ = 0}` one has `s = 0` and
  `q = e₀`; on `{ξ = 1}` one has `c = 0` and `p = e₀`; in between `p = q = e₀` and
  `cos² + sin² = 1` does the rest.

Finally `Work.KT.hk_rotation` feeds the conjugation identity into
`Work.KT.homInv_cls_eq_of_conj` (conjugate idempotents have the same `K₀`-class).
-/

namespace Work.KT

open Matrix

noncomputable section

/-! ## 1. Kronecker products and ring homomorphisms -/

lemma kronMat_apply' {A : Type} [Ring A] {n : ℕ} (M N : Matrix (Fin n) (Fin n) A)
    (i j : Fin (n * n)) :
    kronMat M N i j =
      M (finProdFinEquiv.symm i).1 (finProdFinEquiv.symm j).1 *
      N (finProdFinEquiv.symm i).2 (finProdFinEquiv.symm j).2 := by
  simp only [kronMat, Matrix.reindex_apply, Matrix.submatrix_apply, Matrix.kroneckerMap_apply]

lemma map_kronMat {A B : Type} [Ring A] [Ring B] (φ : A →+* B) {n : ℕ}
    (M N : Matrix (Fin n) (Fin n) A) :
    (kronMat M N).map φ = kronMat (M.map φ) (N.map φ) := by
  ext i j
  simp only [Matrix.map_apply, kronMat_apply', map_mul]

/-! ## 2. The quarter-turn block rotation -/

section BlockAlg

variable {R : Type} [CommRing R]

lemma rot_smul_one_mul {m : ℕ} (x : R) (M : Matrix (Fin m) (Fin m) R) :
    (x • (1 : Matrix (Fin m) (Fin m) R)) * M = x • M := by
  rw [Matrix.smul_mul, one_mul]

lemma rot_mul_smul_one {m : ℕ} (M : Matrix (Fin m) (Fin m) R) (x : R) :
    M * (x • (1 : Matrix (Fin m) (Fin m) R)) = x • M := by
  rw [Matrix.mul_smul, mul_one]

lemma rot_p3 {m : ℕ} (x y : R) :
    (x • (1 : Matrix (Fin m) (Fin m) R)) * (y • (1 : Matrix (Fin m) (Fin m) R))
      = (x * y) • (1 : Matrix (Fin m) (Fin m) R) := by
  rw [rot_smul_one_mul, smul_smul]

lemma rot_p4 {m : ℕ} (x y : R) (M : Matrix (Fin m) (Fin m) R) :
    (x • (1 : Matrix (Fin m) (Fin m) R)) * M * (y • (1 : Matrix (Fin m) (Fin m) R))
      = (y * x) • M := by
  rw [rot_smul_one_mul, rot_mul_smul_one, smul_smul]

lemma rot_smul_add_neg_smul {m : ℕ} (r : R) (A B : Matrix (Fin m) (Fin m) R) :
    r • A + (-r) • B = r • (A - B) := by
  rw [smul_sub, neg_smul, sub_eq_add_neg]

lemma rot_neg_smul_add_smul {m : ℕ} (r : R) (A B : Matrix (Fin m) (Fin m) R) :
    (-r) • A + r • B = r • (B - A) := by
  rw [neg_smul, smul_sub, add_comm, sub_eq_add_neg]

/-- The block rotation `[[c•1, (-s)•1], [s•1, c•1]]`, of size `(m+m) × (m+m)`. -/
def rotMat (m : ℕ) (c s : R) : Matrix (Fin (m + m)) (Fin (m + m)) R :=
  Matrix.reindex finSumFinEquiv finSumFinEquiv
    (Matrix.fromBlocks (c • (1 : Matrix (Fin m) (Fin m) R))
      ((-s) • (1 : Matrix (Fin m) (Fin m) R))
      (s • (1 : Matrix (Fin m) (Fin m) R)) (c • (1 : Matrix (Fin m) (Fin m) R)))

/-- The inverse block rotation `[[c•1, s•1], [(-s)•1, c•1]]`. -/
def rotMatInv (m : ℕ) (c s : R) : Matrix (Fin (m + m)) (Fin (m + m)) R :=
  Matrix.reindex finSumFinEquiv finSumFinEquiv
    (Matrix.fromBlocks (c • (1 : Matrix (Fin m) (Fin m) R))
      (s • (1 : Matrix (Fin m) (Fin m) R))
      ((-s) • (1 : Matrix (Fin m) (Fin m) R)) (c • (1 : Matrix (Fin m) (Fin m) R)))

lemma rot_reindex_one {m : ℕ} :
    Matrix.reindex finSumFinEquiv finSumFinEquiv
        (1 : Matrix (Fin m ⊕ Fin m) (Fin m ⊕ Fin m) R) = 1 := by
  rw [Matrix.reindex_apply,
    Matrix.submatrix_one finSumFinEquiv.symm finSumFinEquiv.symm.injective]

/-- `rotMat c s * rotMatInv c s = 1`. -/
theorem rotMat_mul_rotMatInv {m : ℕ} (c s : R) (hc : c * c + s * s = 1) :
    rotMat m c s * rotMatInv m c s = 1 := by
  have key : Matrix.fromBlocks (c • (1 : Matrix (Fin m) (Fin m) R))
        ((-s) • (1 : Matrix (Fin m) (Fin m) R))
        (s • (1 : Matrix (Fin m) (Fin m) R)) (c • (1 : Matrix (Fin m) (Fin m) R))
      * Matrix.fromBlocks (c • (1 : Matrix (Fin m) (Fin m) R))
        (s • (1 : Matrix (Fin m) (Fin m) R))
        ((-s) • (1 : Matrix (Fin m) (Fin m) R)) (c • (1 : Matrix (Fin m) (Fin m) R))
      = (1 : Matrix (Fin m ⊕ Fin m) (Fin m ⊕ Fin m) R) := by
    rw [Matrix.fromBlocks_multiply, ← Matrix.fromBlocks_one, Matrix.fromBlocks_inj]
    refine ⟨?_, ?_, ?_, ?_⟩
    · rw [rot_p3 c c, rot_p3 (-s) (-s), neg_mul_neg, ← add_smul, hc, one_smul]
    · rw [rot_p3 c s, rot_p3 (-s) c, neg_mul, mul_comm s c, rot_smul_add_neg_smul, sub_self,
        smul_zero]
    · rw [rot_p3 s c, rot_p3 c (-s), mul_neg, mul_comm s c, rot_smul_add_neg_smul, sub_self,
        smul_zero]
    · have h4 : s * s + c * c = 1 := by rw [add_comm (s * s), hc]
      rw [rot_p3 s s, rot_p3 c c, ← add_smul, h4, one_smul]
  rw [rotMat, rotMatInv, reindexMul, key, rot_reindex_one]

/-- `rotMatInv c s * rotMat c s = 1`. -/
theorem rotMatInv_mul_rotMat {m : ℕ} (c s : R) (hc : c * c + s * s = 1) :
    rotMatInv m c s * rotMat m c s = 1 := by
  have key : Matrix.fromBlocks (c • (1 : Matrix (Fin m) (Fin m) R))
        (s • (1 : Matrix (Fin m) (Fin m) R))
        ((-s) • (1 : Matrix (Fin m) (Fin m) R)) (c • (1 : Matrix (Fin m) (Fin m) R))
      * Matrix.fromBlocks (c • (1 : Matrix (Fin m) (Fin m) R))
        ((-s) • (1 : Matrix (Fin m) (Fin m) R))
        (s • (1 : Matrix (Fin m) (Fin m) R)) (c • (1 : Matrix (Fin m) (Fin m) R))
      = (1 : Matrix (Fin m ⊕ Fin m) (Fin m ⊕ Fin m) R) := by
    rw [Matrix.fromBlocks_multiply, ← Matrix.fromBlocks_one, Matrix.fromBlocks_inj]
    refine ⟨?_, ?_, ?_, ?_⟩
    · rw [rot_p3 c c, rot_p3 s s, ← add_smul, hc, one_smul]
    · rw [rot_p3 c (-s), rot_p3 s c, mul_neg, mul_comm s c, rot_neg_smul_add_smul, sub_self,
        smul_zero]
    · rw [rot_p3 (-s) c, rot_p3 c s, neg_mul, mul_comm s c, rot_neg_smul_add_smul, sub_self,
        smul_zero]
    · have h4 : s * s + c * c = 1 := by rw [add_comm (s * s), hc]
      rw [rot_p3 (-s) (-s), rot_p3 c c, neg_mul_neg, ← add_smul, h4, one_smul]
  rw [rotMatInv, rotMat, reindexMul, key, rot_reindex_one]

/-- **The rotation conjugation identity** (block level): if the scalar relations `(I)`, `(II)`,
`(III)` hold then the quarter turn conjugates `Z ⊕ Ee` into `X ⊕ Y`. -/
theorem rotMat_conj {m : ℕ} (Z X Y Ee : Matrix (Fin m) (Fin m) R) (c s : R)
    (hI : (c * c) • Z + (s * s) • Ee = X)
    (hII : (c * s) • (Z - Ee) = 0)
    (hIII : (s * s) • Z + (c * c) • Ee = Y) :
    rotMat m c s * Matrix.reindex finSumFinEquiv finSumFinEquiv (Matrix.fromBlocks Z 0 0 Ee)
        * rotMatInv m c s
      = Matrix.reindex finSumFinEquiv finSumFinEquiv (Matrix.fromBlocks X 0 0 Y) := by
  have key : Matrix.fromBlocks (c • (1 : Matrix (Fin m) (Fin m) R))
        ((-s) • (1 : Matrix (Fin m) (Fin m) R))
        (s • (1 : Matrix (Fin m) (Fin m) R)) (c • (1 : Matrix (Fin m) (Fin m) R))
      * Matrix.fromBlocks Z 0 0 Ee
      * Matrix.fromBlocks (c • (1 : Matrix (Fin m) (Fin m) R))
        (s • (1 : Matrix (Fin m) (Fin m) R))
        ((-s) • (1 : Matrix (Fin m) (Fin m) R)) (c • (1 : Matrix (Fin m) (Fin m) R))
      = Matrix.fromBlocks X 0 0 Y := by
    rw [Matrix.fromBlocks_multiply, Matrix.fromBlocks_multiply]
    simp only [Matrix.mul_zero, Matrix.zero_mul, add_zero, zero_add]
    rw [Matrix.fromBlocks_inj]
    refine ⟨?_, ?_, ?_, ?_⟩
    · rw [rot_p4 c c Z, rot_p4 (-s) (-s) Ee, neg_mul_neg]
      exact hI
    · rw [rot_p4 c s Z, rot_p4 (-s) c Ee, mul_neg, mul_comm s c, rot_smul_add_neg_smul]
      exact hII
    · rw [rot_p4 s c Z, rot_p4 c (-s) Ee, neg_mul, mul_comm s c, rot_smul_add_neg_smul]
      exact hII
    · rw [rot_p4 s s Z, rot_p4 c c Ee]
      exact hIII
  rw [rotMat, rotMatInv, reindexMul, reindexMul, key]

end BlockAlg

/-! ## 3. Pointwise evaluation of matrices over `C(T,ℂ)` -/

section Pointwise

variable {T : Type} [TopologicalSpace T]

lemma rot_eq_of_eval {m : ℕ} {M N : Matrix (Fin m) (Fin m) C(T, ℂ)}
    (h : ∀ t : T, M.map (evalC t) = N.map (evalC t)) : M = N := by
  refine Matrix.ext fun i j => ?_
  refine ContinuousMap.ext fun t => ?_
  have hh := congrFun (congrFun (h t) i) j
  simpa [Matrix.map_apply] using hh

lemma rot_eval_map_add {m : ℕ} (t : T) (M N : Matrix (Fin m) (Fin m) C(T, ℂ)) :
    (M + N).map (evalC t) = M.map (evalC t) + N.map (evalC t) :=
  Matrix.map_add (evalC t) (fun a b => map_add (evalC t) a b) M N

lemma rot_eval_map_sub {m : ℕ} (t : T) (M N : Matrix (Fin m) (Fin m) C(T, ℂ)) :
    (M - N).map (evalC t) = M.map (evalC t) - N.map (evalC t) :=
  Matrix.map_sub (evalC t) (fun a b => map_sub (evalC t) a b) M N

lemma rot_eval_map_mul {m : ℕ} (t : T) (M N : Matrix (Fin m) (Fin m) C(T, ℂ)) :
    (M * N).map (evalC t) = M.map (evalC t) * N.map (evalC t) := by
  ext i j
  simp only [Matrix.map_apply, Matrix.mul_apply]
  rw [map_sum]
  exact Finset.sum_congr rfl fun k _ => by rw [map_mul]

lemma rot_eval_map_smul {m : ℕ} (t : T) (x : C(T, ℂ)) (M : Matrix (Fin m) (Fin m) C(T, ℂ)) :
    (x • M).map (evalC t) = (evalC t x) • M.map (evalC t) := by
  rw [Matrix.smul_eq_mul_diagonal, Matrix.smul_eq_mul_diagonal, rot_eval_map_mul,
    Matrix.diagonal_map (map_zero (evalC t))]

lemma rot_eval_zero {m : ℕ} (t : T) :
    (0 : Matrix (Fin m) (Fin m) C(T, ℂ)).map (evalC t) = 0 :=
  Matrix.map_zero (evalC t) (map_zero (evalC t))

lemma rot_eval_map_kron {n : ℕ} (t : T) (M N : Matrix (Fin n) (Fin n) C(T, ℂ)) :
    (kronMat M N).map (evalC t) = kronMat (M.map (evalC t)) (N.map (evalC t)) :=
  map_kronMat (evalC t).toRingHom M N

lemma rot_matConst_map {n : ℕ} (t : T) (M : Matrix (Fin n) (Fin n) ℂ) :
    (matConst C(T, ℂ) M).map (evalC t) = M := by
  ext i j
  simp only [matConst, Matrix.map_apply]
  simpa using (evalC t).commutes (M i j)

end Pointwise

/-! ## 4. The three scalar identities -/

section Rotation

variable {T : Type} [TopologicalSpace T] (ξ : C(T, unitInterval))

/-- `θ = (π/2)·ξ`, as a continuous real function. -/
def thetaC : C(T, ℝ) :=
  ⟨fun t => Real.pi / 2 * ((ξ t : unitInterval) : ℝ),
    continuous_const.mul (continuous_subtype_val.comp ξ.continuous)⟩

/-- `cos θ ∈ C(T,ℂ)`. -/
def cosC : C(T, ℂ) :=
  ⟨fun t => ((Real.cos (thetaC ξ t) : ℝ) : ℂ),
    Complex.continuous_ofReal.comp (Real.continuous_cos.comp (thetaC ξ).continuous)⟩

/-- `sin θ ∈ C(T,ℂ)`. -/
def sinC : C(T, ℂ) :=
  ⟨fun t => ((Real.sin (thetaC ξ t) : ℝ) : ℂ),
    Complex.continuous_ofReal.comp (Real.continuous_sin.comp (thetaC ξ).continuous)⟩

@[simp] lemma thetaC_apply (t : T) :
    thetaC ξ t = Real.pi / 2 * ((ξ t : unitInterval) : ℝ) := rfl

@[simp] lemma evalC_cosC (t : T) :
    evalC t (cosC ξ) = ((Real.cos (thetaC ξ t) : ℝ) : ℂ) := rfl

@[simp] lemma evalC_sinC (t : T) :
    evalC t (sinC ξ) = ((Real.sin (thetaC ξ t) : ℝ) : ℂ) := rfl

lemma evalC_mul' (t : T) (x y : C(T, ℂ)) :
    evalC t (x * y) = evalC t x * evalC t y := map_mul (evalC t) x y

lemma ofReal_cos_sq_add_sin_sq (x : ℝ) :
    ((Real.cos x : ℝ) : ℂ) * ((Real.cos x : ℝ) : ℂ)
      + ((Real.sin x : ℝ) : ℂ) * ((Real.sin x : ℝ) : ℂ) = 1 := by
  have h := Real.cos_sq_add_sin_sq x
  simp only [pow_two] at h
  rw [← Complex.ofReal_mul, ← Complex.ofReal_mul, ← Complex.ofReal_add, h, Complex.ofReal_one]

lemma cosC_sq_add_sinC_sq : cosC ξ * cosC ξ + sinC ξ * sinC ξ = 1 := by
  refine ContinuousMap.ext fun t => ?_
  simp only [ContinuousMap.add_apply, ContinuousMap.mul_apply, ContinuousMap.one_apply,
    evalC_cosC, evalC_sinC]
  exact ofReal_cos_sq_add_sin_sq (thetaC ξ t)

lemma rotIdem_I (n : ℕ) (e₀ : Matrix (Fin n) (Fin n) ℂ)
    (p q : Matrix (Fin n) (Fin n) C(T, ℂ))
    (hp' : ∀ t : T, 0 < ((ξ t : unitInterval) : ℝ) → p.map (evalC t) = e₀)
    (hq' : ∀ t : T, ((ξ t : unitInterval) : ℝ) < 1 → q.map (evalC t) = e₀) :
    (cosC ξ * cosC ξ) • kronMat p q
        + (sinC ξ * sinC ξ) • kronMat (matConst C(T, ℂ) e₀) (matConst C(T, ℂ) e₀)
      = kronMat p (matConst C(T, ℂ) e₀) := by
  apply rot_eq_of_eval
  intro t
  simp only [rot_eval_map_add, rot_eval_map_smul, rot_eval_map_kron, rot_matConst_map, rot_eval_zero, evalC_mul']
  have hge : 0 ≤ ((ξ t : unitInterval) : ℝ) := (ξ t).2.1
  have hle : ((ξ t : unitInterval) : ℝ) ≤ 1 := (ξ t).2.2
  rcases eq_or_lt_of_le hge with h0 | hpos
  · have hQ : q.map (evalC t) = e₀ := hq' t (by rw [h0.symm]; norm_num)
    have hth : thetaC ξ t = 0 := by rw [thetaC_apply, h0.symm]; ring
    have hc : evalC t (cosC ξ) = 1 := by rw [evalC_cosC, hth, Real.cos_zero, Complex.ofReal_one]
    have hs : evalC t (sinC ξ) = 0 := by rw [evalC_sinC, hth, Real.sin_zero, Complex.ofReal_zero]
    simp only [hc, hs, hQ, mul_one, mul_zero, zero_smul, one_smul, add_zero]
  · rcases eq_or_lt_of_le hle with h1 | hlt1
    · have hP : p.map (evalC t) = e₀ := hp' t (by rw [h1]; norm_num)
      have hth : thetaC ξ t = Real.pi / 2 := by rw [thetaC_apply, h1]; ring
      have hc : evalC t (cosC ξ) = 0 := by
        rw [evalC_cosC, hth, Real.cos_pi_div_two, Complex.ofReal_zero]
      have hs : evalC t (sinC ξ) = 1 := by
        rw [evalC_sinC, hth, Real.sin_pi_div_two, Complex.ofReal_one]
      simp only [hP, hc, hs, mul_one, mul_zero, zero_smul, one_smul, zero_add]
    · have hP : p.map (evalC t) = e₀ := hp' t hpos
      have hQ : q.map (evalC t) = e₀ := hq' t hlt1
      have hcs : evalC t (cosC ξ) * evalC t (cosC ξ)
          + evalC t (sinC ξ) * evalC t (sinC ξ) = 1 := by
        rw [evalC_cosC, evalC_sinC]
        exact ofReal_cos_sq_add_sin_sq (thetaC ξ t)
      simp only [hP, hQ, ← add_smul, hcs, one_smul]

lemma rotIdem_II (n : ℕ) (e₀ : Matrix (Fin n) (Fin n) ℂ)
    (p q : Matrix (Fin n) (Fin n) C(T, ℂ))
    (hp' : ∀ t : T, 0 < ((ξ t : unitInterval) : ℝ) → p.map (evalC t) = e₀)
    (hq' : ∀ t : T, ((ξ t : unitInterval) : ℝ) < 1 → q.map (evalC t) = e₀) :
    (cosC ξ * sinC ξ)
        • (kronMat p q - kronMat (matConst C(T, ℂ) e₀) (matConst C(T, ℂ) e₀)) = 0 := by
  apply rot_eq_of_eval
  intro t
  simp only [rot_eval_map_smul, rot_eval_map_sub, rot_eval_map_kron, rot_matConst_map, rot_eval_zero, evalC_mul']
  have hge : 0 ≤ ((ξ t : unitInterval) : ℝ) := (ξ t).2.1
  have hle : ((ξ t : unitInterval) : ℝ) ≤ 1 := (ξ t).2.2
  rcases eq_or_lt_of_le hge with h0 | hpos
  · have hth : thetaC ξ t = 0 := by rw [thetaC_apply, h0.symm]; ring
    have hs : evalC t (sinC ξ) = 0 := by rw [evalC_sinC, hth, Real.sin_zero, Complex.ofReal_zero]
    simp only [hs, mul_zero, zero_smul]
  · rcases eq_or_lt_of_le hle with h1 | hlt1
    · have hth : thetaC ξ t = Real.pi / 2 := by rw [thetaC_apply, h1]; ring
      have hc : evalC t (cosC ξ) = 0 := by
        rw [evalC_cosC, hth, Real.cos_pi_div_two, Complex.ofReal_zero]
      simp only [hc, zero_mul, zero_smul]
    · have hP : p.map (evalC t) = e₀ := hp' t hpos
      have hQ : q.map (evalC t) = e₀ := hq' t hlt1
      simp only [hP, hQ, sub_self, smul_zero]

lemma rotIdem_III (n : ℕ) (e₀ : Matrix (Fin n) (Fin n) ℂ)
    (p q : Matrix (Fin n) (Fin n) C(T, ℂ))
    (hp' : ∀ t : T, 0 < ((ξ t : unitInterval) : ℝ) → p.map (evalC t) = e₀)
    (hq' : ∀ t : T, ((ξ t : unitInterval) : ℝ) < 1 → q.map (evalC t) = e₀) :
    (sinC ξ * sinC ξ) • kronMat p q
        + (cosC ξ * cosC ξ) • kronMat (matConst C(T, ℂ) e₀) (matConst C(T, ℂ) e₀)
      = kronMat (matConst C(T, ℂ) e₀) q := by
  apply rot_eq_of_eval
  intro t
  simp only [rot_eval_map_add, rot_eval_map_smul, rot_eval_map_kron, rot_matConst_map, rot_eval_zero, evalC_mul']
  have hge : 0 ≤ ((ξ t : unitInterval) : ℝ) := (ξ t).2.1
  have hle : ((ξ t : unitInterval) : ℝ) ≤ 1 := (ξ t).2.2
  rcases eq_or_lt_of_le hge with h0 | hpos
  · have hQ : q.map (evalC t) = e₀ := hq' t (by rw [h0.symm]; norm_num)
    have hth : thetaC ξ t = 0 := by rw [thetaC_apply, h0.symm]; ring
    have hc : evalC t (cosC ξ) = 1 := by rw [evalC_cosC, hth, Real.cos_zero, Complex.ofReal_one]
    have hs : evalC t (sinC ξ) = 0 := by rw [evalC_sinC, hth, Real.sin_zero, Complex.ofReal_zero]
    simp only [hc, hs, hQ, mul_one, mul_zero, zero_smul, one_smul, zero_add]
  · rcases eq_or_lt_of_le hle with h1 | hlt1
    · have hP : p.map (evalC t) = e₀ := hp' t (by rw [h1]; norm_num)
      have hth : thetaC ξ t = Real.pi / 2 := by rw [thetaC_apply, h1]; ring
      have hc : evalC t (cosC ξ) = 0 := by
        rw [evalC_cosC, hth, Real.cos_pi_div_two, Complex.ofReal_zero]
      have hs : evalC t (sinC ξ) = 1 := by
        rw [evalC_sinC, hth, Real.sin_pi_div_two, Complex.ofReal_one]
      simp only [hP, hc, hs, mul_one, mul_zero, zero_smul, one_smul, add_zero]
    · have hP : p.map (evalC t) = e₀ := hp' t hpos
      have hQ : q.map (evalC t) = e₀ := hq' t hlt1
      have hcs : evalC t (sinC ξ) * evalC t (sinC ξ)
          + evalC t (cosC ξ) * evalC t (cosC ξ) = 1 := by
        rw [evalC_cosC, evalC_sinC, add_comm]
        exact ofReal_cos_sq_add_sin_sq (thetaC ξ t)
      simp only [hP, hQ, ← add_smul, hcs, one_smul]

end Rotation

/-! ## 5. The rotation trick -/

/-- **The rotation trick (relative product).**  Let `ξ : T → [0,1]` be continuous, `e₀` an
idempotent matrix over `ℂ`, and `p`, `q` idempotent matrices over `C(T,ℂ)` which are equal to the
constant matrix `e₀` at every point with `ξ > 0`, resp. `ξ < 1`.  Then the two "distributions"
`p ⊗ q ⊕ e ⊗ e` and `p ⊗ e ⊕ e ⊗ q` (with `e` the constant `e₀`) are conjugate over `C(T,ℂ)` by
the block rotation of angle `(π/2)ξ`, and in particular have the same class in `K₀`. -/
theorem hk_rotation (T : Type) [TopologicalSpace T] (ξ : C(T, unitInterval)) (n : ℕ)
    (e₀ : Matrix (Fin n) (Fin n) ℂ) (he₀ : e₀ * e₀ = e₀)
    (p q : Matrix (Fin n) (Fin n) C(T, ℂ)) (hp : p * p = p) (hq : q * q = q)
    (hp' : ∀ t : T, 0 < ((ξ t : unitInterval) : ℝ) → p.map (evalC t) = e₀)
    (hq' : ∀ t : T, ((ξ t : unitInterval) : ℝ) < 1 → q.map (evalC t) = e₀) :
    cls (Mat.sum (Mat.kron ⟨n, p⟩ ⟨n, q⟩)
          (Mat.kron ⟨n, matConst C(T, ℂ) e₀⟩ ⟨n, matConst C(T, ℂ) e₀⟩)) =
      cls (Mat.sum (Mat.kron ⟨n, p⟩ ⟨n, matConst C(T, ℂ) e₀⟩)
          (Mat.kron ⟨n, matConst C(T, ℂ) e₀⟩ ⟨n, q⟩)) := by
  have hcs : cosC ξ * cosC ξ + sinC ξ * sinC ξ = 1 := cosC_sq_add_sinC_sq (ξ := ξ)
  have hI : (cosC ξ * cosC ξ) • kronMat p q
      + (sinC ξ * sinC ξ) • kronMat (matConst C(T, ℂ) e₀) (matConst C(T, ℂ) e₀)
      = kronMat p (matConst C(T, ℂ) e₀) :=
    rotIdem_I (ξ := ξ) (n := n) (e₀ := e₀) (p := p) (q := q) (hp' := hp') (hq' := hq')
  have hII : (cosC ξ * sinC ξ)
      • (kronMat p q - kronMat (matConst C(T, ℂ) e₀) (matConst C(T, ℂ) e₀)) = 0 :=
    rotIdem_II (ξ := ξ) (n := n) (e₀ := e₀) (p := p) (q := q) (hp' := hp') (hq' := hq')
  have hIII : (sinC ξ * sinC ξ) • kronMat p q
      + (cosC ξ * cosC ξ) • kronMat (matConst C(T, ℂ) e₀) (matConst C(T, ℂ) e₀)
      = kronMat (matConst C(T, ℂ) e₀) q :=
    rotIdem_III (ξ := ξ) (n := n) (e₀ := e₀) (p := p) (q := q) (hp' := hp') (hq' := hq')
  have hrot := rotMat_conj (kronMat p q) (kronMat p (matConst C(T, ℂ) e₀))
    (kronMat (matConst C(T, ℂ) e₀) q)
    (kronMat (matConst C(T, ℂ) e₀) (matConst C(T, ℂ) e₀)) (cosC ξ) (sinC ξ) hI hII hIII
  have hEidem : Mat.IsIdem (⟨n, matConst C(T, ℂ) e₀⟩ : Mat C(T, ℂ)) := by
    show matConst C(T, ℂ) e₀ * matConst C(T, ℂ) e₀ = matConst C(T, ℂ) e₀
    rw [← matConst_mul, he₀]
  have hpIdem : Mat.IsIdem (⟨n, p⟩ : Mat C(T, ℂ)) := hp
  have hqIdem : Mat.IsIdem (⟨n, q⟩ : Mat C(T, ℂ)) := hq
  have hZidem : Mat.IsIdem (Mat.kron (⟨n, p⟩ : Mat C(T, ℂ)) ⟨n, q⟩) :=
    Mat.kron_idem (fun x y => mul_comm x y) (p := (⟨n, p⟩ : Mat C(T, ℂ)))
      (q := (⟨n, q⟩ : Mat C(T, ℂ))) hpIdem hqIdem
  have hKEidem :
      Mat.IsIdem (Mat.kron (⟨n, p⟩ : Mat C(T, ℂ)) ⟨n, matConst C(T, ℂ) e₀⟩) :=
    Mat.kron_idem (fun x y => mul_comm x y) (p := (⟨n, p⟩ : Mat C(T, ℂ)))
      (q := (⟨n, matConst C(T, ℂ) e₀⟩ : Mat C(T, ℂ))) hpIdem hEidem
  have hEqidem :
      Mat.IsIdem (Mat.kron (⟨n, matConst C(T, ℂ) e₀⟩ : Mat C(T, ℂ)) ⟨n, q⟩) :=
    Mat.kron_idem (fun x y => mul_comm x y) (p := (⟨n, matConst C(T, ℂ) e₀⟩ : Mat C(T, ℂ)))
      (q := (⟨n, q⟩ : Mat C(T, ℂ))) hEidem hqIdem
  have hEEidem :
      Mat.IsIdem (Mat.kron (⟨n, matConst C(T, ℂ) e₀⟩ : Mat C(T, ℂ))
        ⟨n, matConst C(T, ℂ) e₀⟩) :=
    Mat.kron_idem (fun x y => mul_comm x y) (p := (⟨n, matConst C(T, ℂ) e₀⟩ : Mat C(T, ℂ)))
      (q := (⟨n, matConst C(T, ℂ) e₀⟩ : Mat C(T, ℂ))) hEidem hEidem
  let P1m : Matrix (Fin (n * n + n * n)) (Fin (n * n + n * n)) C(T, ℂ) :=
    Matrix.reindex finSumFinEquiv finSumFinEquiv
      (Matrix.fromBlocks (kronMat p q) 0 0
        (kronMat (matConst C(T, ℂ) e₀) (matConst C(T, ℂ) e₀)))
  let P2m : Matrix (Fin (n * n + n * n)) (Fin (n * n + n * n)) C(T, ℂ) :=
    Matrix.reindex finSumFinEquiv finSumFinEquiv
      (Matrix.fromBlocks (kronMat p (matConst C(T, ℂ) e₀)) 0 0
        (kronMat (matConst C(T, ℂ) e₀) q))
  have hidem1 : P1m * P1m = P1m := Mat.sum_idem hZidem hEEidem
  have hidem2 : P2m * P2m = P2m := Mat.sum_idem hKEidem hEqidem
  have hconj : rotMat (n * n) (cosC ξ) (sinC ξ) * P1m * rotMatInv (n * n) (cosC ξ) (sinC ξ)
      = P2m := hrot
  let u : (Matrix (Fin (n * n + n * n)) (Fin (n * n + n * n)) C(T, ℂ))ˣ :=
    Units.mk (rotMat (n * n) (cosC ξ) (sinC ξ)) (rotMatInv (n * n) (cosC ξ) (sinC ξ))
      (rotMat_mul_rotMatInv (m := n * n) (cosC ξ) (sinC ξ) hcs)
      (rotMatInv_mul_rotMat (m := n * n) (cosC ξ) (sinC ξ) hcs)
  have hu : (u : Matrix (Fin (n * n + n * n)) (Fin (n * n + n * n)) C(T, ℂ)) * P1m
      = P2m * (u : Matrix (Fin (n * n + n * n)) (Fin (n * n + n * n)) C(T, ℂ)) := by
    have huv : (u : Matrix (Fin (n * n + n * n)) (Fin (n * n + n * n)) C(T, ℂ))
        = rotMat (n * n) (cosC ξ) (sinC ξ) := rfl
    rw [huv]
    calc rotMat (n * n) (cosC ξ) (sinC ξ) * P1m
        = rotMat (n * n) (cosC ξ) (sinC ξ) * P1m * 1 := (Matrix.mul_one _).symm
      _ = rotMat (n * n) (cosC ξ) (sinC ξ) * P1m
            * (rotMatInv (n * n) (cosC ξ) (sinC ξ) * rotMat (n * n) (cosC ξ) (sinC ξ)) := by
          rw [rotMatInv_mul_rotMat (m := n * n) (cosC ξ) (sinC ξ) hcs]
      _ = rotMat (n * n) (cosC ξ) (sinC ξ) * P1m * rotMatInv (n * n) (cosC ξ) (sinC ξ)
            * rotMat (n * n) (cosC ξ) (sinC ξ) := by
          rw [← Matrix.mul_assoc]
      _ = P2m * rotMat (n * n) (cosC ξ) (sinC ξ) := by
          rw [hconj]
  have hfin := homInv_cls_eq_of_conj (p := P2m) (q := P1m) hidem2 hidem1 u hu
  exact hfin.symm

end

end Work.KT
