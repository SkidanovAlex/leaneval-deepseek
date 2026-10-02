import Mathlib

-- Lean v4.35.0-rc3: restore v4.34 instance-unification transparency (port).
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false

set_option autoImplicit false
set_option maxHeartbeats 800000

/-!
# The Stiefel manifold of orthonormal frames

This is the base layer of the **Grassmann** chapter (`Work.ThomBordism.Grassmann`): the raw material
out of which the oriented Grassmannian `G̃r_k(ℝ^{k+m})` and its tautological bundle are built.

* `Work.ThomBordism.Grassmann.Amb n` is the ambient Euclidean space `ℝⁿ`;
* `Work.ThomBordism.Grassmann.Stiefel k m = V_k(ℝ^{k+m})` is the set of **orthonormal `k`-frames**,
  a compact Hausdorff space;
* `Work.ThomBordism.Grassmann.soActFun A f` is the action `(A · f)_i = ∑_j A_{ji} f_j` of a `k × k`
  matrix on a frame;
* `Work.ThomBordism.Grassmann.IsSO A` is the predicate "`A ∈ SO(k)`"
  (`Aᵀ A = 1` and `det A = 1`), with its group laws;
* `Work.ThomBordism.Grassmann.ChartIdx k m` indexes the **standard charts** of the Grassmannian:
  the `k`-element subsets of the coordinates, and `Work.ThomBordism.Grassmann.frameMatrix S f` is
  the `k × k` matrix of the `S`-th coordinates of a frame — its determinant is the chart coordinate
  (the `k`-minor of the frame), so that `Work.ThomBordism.Grassmann.chartSet S` is the set of frames
  whose `S`-th coordinate projection is an isomorphism onto the plane.
-/

namespace Work.ThomBordism.Grassmann

open scoped Topology

noncomputable section

/-- The ambient Euclidean space `ℝⁿ`. -/
abbrev Amb (n : ℕ) := EuclideanSpace ℝ (Fin n)

/-- The **Stiefel manifold** `V_k(ℝ^{k+m})`: the set of orthonormal `k`-frames in `ℝ^{k+m}`. -/
abbrev Stiefel (k m : ℕ) : Type := {f : Fin k → Amb (k+m) // Orthonormal ℝ f}

/-- The action of a `k × k` matrix on a frame: `(A · f)_i = ∑_j A_{ji} f_j`. -/
def soActFun {k m : ℕ} (A : Matrix (Fin k) (Fin k) ℝ) (f : Fin k → Amb (k+m)) :
    Fin k → Amb (k+m) :=
  fun i => ∑ j, A j i • f j

/-- `A ∈ SO(k)`: `Aᵀ A = 1` (the columns of `A` are orthonormal) and `det A = 1`. -/
def IsSO {k : ℕ} (A : Matrix (Fin k) (Fin k) ℝ) : Prop := A.transpose * A = 1 ∧ A.det = 1

/-- The chart index set of the Grassmannian `G̃r_k(ℝ^{k+m})`: the `k`-element subsets of the
coordinates `Fin (k+m)`.  The cardinality of this (finite) type is `(k+m).choose k`. -/
def ChartIdx (k m : ℕ) : Type := {S : Finset (Fin (k+m)) // S.card = k}

instance (k m : ℕ) : Fintype (ChartIdx k m) := inferInstanceAs (Fintype {S : Finset (Fin (k+m)) // S.card = k})

/-- The `S`-rows of a frame: the `k × k` matrix whose `(i,j)` entry is the `i`-th coordinate (of the
enumeration of `S` induced by `Finset.equivFinOfCardEq`) of the `j`-th vector of the frame. -/
def frameMatrix {k m : ℕ} (S : ChartIdx k m) (f : Fin k → Amb (k+m)) : Matrix (Fin k) (Fin k) ℝ :=
  fun i j => EuclideanSpace.proj (𝕜 := ℝ)
    (((S.1.equivFinOfCardEq S.2).symm i : ↥S.1) : Fin (k+m)) (f j)

/-- The frames whose `S`-th coordinate projection is an isomorphism onto the plane: the preimage in
the Stiefel manifold of the chart `U_S` of the Grassmannian. -/
def chartSet {k m : ℕ} (S : ChartIdx k m) : Set (Stiefel k m) :=
  {f | (frameMatrix S f.1).det ≠ 0}

@[simp] theorem mem_chartSet {k m : ℕ} (S : ChartIdx k m) (f : Stiefel k m) :
    f ∈ chartSet S ↔ (frameMatrix S f.1).det ≠ 0 := Iff.rfl

/-! ## The group laws of `SO(k)` -/

theorem IsSO.one {k : ℕ} : IsSO (1 : Matrix (Fin k) (Fin k) ℝ) := by
  constructor <;> simp

theorem IsSO.mul_transpose_self {k : ℕ} {A : Matrix (Fin k) (Fin k) ℝ} (h : IsSO A) :
    A * A.transpose = 1 := by
  have hunit : IsUnit A.det := Matrix.isUnit_det_of_left_inverse h.1
  rw [← Matrix.inv_eq_left_inv h.1]
  exact Matrix.mul_nonsing_inv A hunit

theorem IsSO.transpose {k : ℕ} {A : Matrix (Fin k) (Fin k) ℝ} (h : IsSO A) :
    IsSO A.transpose := by
  constructor
  · simpa [Matrix.transpose_transpose] using h.mul_transpose_self
  · simpa using h.2

theorem IsSO.mul {k : ℕ} {A B : Matrix (Fin k) (Fin k) ℝ} (hA : IsSO A) (hB : IsSO B) :
    IsSO (A * B) := by
  constructor
  · rw [Matrix.transpose_mul, Matrix.mul_assoc B.transpose A.transpose (A * B),
      ← Matrix.mul_assoc A.transpose A B, hA.1, Matrix.one_mul]
    exact hB.1
  · rw [Matrix.det_mul, hA.2, hB.2, one_mul]

theorem IsSO.isUnit_det {k : ℕ} {A : Matrix (Fin k) (Fin k) ℝ} (h : IsSO A) : IsUnit A.det :=
  Matrix.isUnit_det_of_left_inverse h.1

theorem IsSO.det_ne_zero {k : ℕ} {A : Matrix (Fin k) (Fin k) ℝ} (h : IsSO A) : A.det ≠ 0 :=
  Matrix.det_ne_zero_of_left_inverse h.1

/-! ## The action on frames -/

@[simp] theorem soActFun_one {k m : ℕ} (f : Fin k → Amb (k+m)) :
    soActFun (1 : Matrix (Fin k) (Fin k) ℝ) f = f := by
  funext i
  rw [WithLp.ext_iff]
  funext x
  simp only [soActFun, WithLp.ofLp_sum, WithLp.ofLp_smul, Finset.sum_apply, Pi.smul_apply,
    smul_eq_mul]
  rw [Finset.sum_eq_single (s := Finset.univ) i]
  · rw [Matrix.one_apply_eq, one_mul]
  · intro j _ hj
    rw [Matrix.one_apply_ne hj, zero_mul]
  · intro h; exact absurd (Finset.mem_univ i) h

theorem soActFun_comp {k m : ℕ} (A B : Matrix (Fin k) (Fin k) ℝ) (f : Fin k → Amb (k+m)) :
    soActFun A (soActFun B f) = soActFun (B * A) f := by
  funext i
  rw [WithLp.ext_iff]
  funext x
  simp only [soActFun, WithLp.ofLp_sum, WithLp.ofLp_smul, Finset.sum_apply, Pi.smul_apply,
    smul_eq_mul]
  simp only [Finset.mul_sum]
  rw [Finset.sum_comm]
  refine Finset.sum_congr rfl fun l _ => ?_
  rw [Matrix.mul_apply, Finset.sum_mul]
  exact Finset.sum_congr rfl fun j _ => by ring

theorem frameMatrix_soActFun {k m : ℕ} (S : ChartIdx k m) (A : Matrix (Fin k) (Fin k) ℝ)
    (f : Fin k → Amb (k+m)) :
    frameMatrix S (soActFun A f) = frameMatrix S f * A := by
  ext i j
  simp only [frameMatrix, soActFun, Matrix.mul_apply, map_sum, map_smul]
  refine Finset.sum_congr rfl fun l _ => ?_
  rw [smul_eq_mul, mul_comm]

theorem det_frameMatrix_soActFun {k m : ℕ} (S : ChartIdx k m) (A : Matrix (Fin k) (Fin k) ℝ)
    (f : Fin k → Amb (k+m)) :
    (frameMatrix S (soActFun A f)).det = (frameMatrix S f).det * A.det := by
  rw [frameMatrix_soActFun, Matrix.det_mul]

/-! ## The Stiefel manifold is a nonempty compact Hausdorff space -/

theorem nonempty_stiefel (k m : ℕ) : Nonempty (Stiefel k m) := by
  classical
  refine ⟨⟨fun i => EuclideanSpace.basisFun (Fin (k+m)) ℝ
    (Fin.castLE (Nat.le_add_right k m) i), ?_⟩⟩
  exact (EuclideanSpace.basisFun (Fin (k+m)) ℝ).orthonormal.comp _
    (Fin.castLE_injective _)

theorem compactSpace_stiefel (k m : ℕ) : CompactSpace (Stiefel k m) :=
  isCompact_iff_compactSpace.mp (show IsCompact {f : Fin k → Amb (k+m) | Orthonormal ℝ f} from by
    rw [Metric.isCompact_iff_isClosed_bounded]
    constructor
    · have h1 : IsClosed {f : Fin k → Amb (k+m) | ∀ i, ‖f i‖ = 1} := by
        have hset1 : {f : Fin k → Amb (k+m) | ∀ i, ‖f i‖ = 1} = ⋂ i, {f | ‖f i‖ = 1} := by
          ext f; simp
        rw [hset1]
        exact isClosed_iInter fun i => isClosed_eq (continuous_apply i).norm continuous_const
      have h2 : IsClosed {f : Fin k → Amb (k+m) | ∀ i j, i ≠ j → inner ℝ (f i) (f j) = 0} := by
        have hset2 : {f : Fin k → Amb (k+m) | ∀ i j, i ≠ j → inner ℝ (f i) (f j) = 0}
            = ⋂ i, ⋂ (j : {j : Fin k // i ≠ j}), {f | inner ℝ (f i) (f j.1) = 0} := by
          ext f
          simp only [Set.mem_setOf_eq, Set.mem_iInter]
          constructor
          · intro h i j; exact h i j.1 j.2
          · intro h i j hij; exact h i ⟨j, hij⟩
        rw [hset2]
        exact isClosed_iInter fun i => isClosed_iInter fun j =>
          isClosed_eq ((continuous_apply i).inner (continuous_apply j.1)) continuous_const

      have hset : {f : Fin k → Amb (k+m) | Orthonormal ℝ f}
          = {f : Fin k → Amb (k+m) | ∀ i, ‖f i‖ = 1}
            ∩ {f : Fin k → Amb (k+m) | ∀ i j, i ≠ j → inner ℝ (f i) (f j) = 0} := by
        ext f; constructor
        · intro h; exact ⟨h.1, fun i j hij => h.2 hij⟩
        · rintro ⟨h1', h2'⟩; exact ⟨h1', fun i j hij => h2' i j hij⟩
      rw [hset]
      exact h1.inter h2
    · rw [isBounded_iff_forall_norm_le]
      refine ⟨1, fun f hf => ?_⟩
      rw [pi_norm_le_iff_of_nonneg (by norm_num)]
      intro i
      rw [hf.1 i])

/-! ## The action of `SO(k)` preserves orthonormality of frames -/

theorem orthonormal_soActFun {k m : ℕ} {A : Matrix (Fin k) (Fin k) ℝ}
    (hA : A.transpose * A = 1) {f : Fin k → Amb (k+m)} (hf : Orthonormal ℝ f) :
    Orthonormal ℝ (soActFun A f) := by
  rw [orthonormal_iff_ite] at hf ⊢
  intro i j
  have key : inner ℝ (soActFun A f i) (soActFun A f j) = (A.transpose * A) i j := by
    have h1 : inner ℝ (soActFun A f i) (soActFun A f j) = ∑ l, A l i * A l j := by
      simp only [soActFun]
      rw [sum_inner]
      refine Finset.sum_congr rfl fun l _ => ?_
      have h2 : inner ℝ (f l) (∑ n, A n j • f n) = A l j := by
        rw [inner_sum]
        rw [Finset.sum_eq_single l]
        · rw [inner_smul_right, hf, if_pos rfl, mul_one]
        · intro n _ hn
          rw [inner_smul_right, hf, if_neg (Ne.symm hn), mul_zero]
        · intro h; exact absurd (Finset.mem_univ l) h
      rw [inner_smul_left, h2]
      simp
    rw [h1, Matrix.mul_apply]
    exact Finset.sum_congr rfl fun l _ => by rw [Matrix.transpose_apply]
  rw [key, hA, Matrix.one_apply]

/-! ## Invariance of the transition matrices under the action -/

theorem frameMatrix_mul_inv_invariant {k m : ℕ} (S T : ChartIdx k m)
    (A : Matrix (Fin k) (Fin k) ℝ) (hA : IsSO A) (f : Fin k → Amb (k+m))
    (hT : (frameMatrix T f).det ≠ 0) :
    frameMatrix S (soActFun A f) * (frameMatrix T (soActFun A f))⁻¹ =
      frameMatrix S f * (frameMatrix T f)⁻¹ := by
  rw [frameMatrix_soActFun, frameMatrix_soActFun]
  have hunitA : IsUnit A.det := hA.isUnit_det
  have hunitT : IsUnit (frameMatrix T f).det := isUnit_iff_ne_zero.mpr hT
  have hinv : (frameMatrix T f * A)⁻¹ = A⁻¹ * (frameMatrix T f)⁻¹ := by
    refine Matrix.inv_eq_left_inv ?_
    calc A⁻¹ * (frameMatrix T f)⁻¹ * (frameMatrix T f * A)
        = A⁻¹ * ((frameMatrix T f)⁻¹ * frameMatrix T f) * A := by noncomm_ring
      _ = 1 := by
          rw [Matrix.nonsing_inv_mul _ hunitT]
          simp [Matrix.nonsing_inv_mul _ hunitA]
  rw [hinv]
  calc frameMatrix S f * A * (A⁻¹ * (frameMatrix T f)⁻¹)
      = frameMatrix S f * (A * A⁻¹) * (frameMatrix T f)⁻¹ := by noncomm_ring
    _ = frameMatrix S f * (frameMatrix T f)⁻¹ := by
        rw [Matrix.mul_nonsing_inv _ hunitA]
        simp

end

end Work.ThomBordism.Grassmann