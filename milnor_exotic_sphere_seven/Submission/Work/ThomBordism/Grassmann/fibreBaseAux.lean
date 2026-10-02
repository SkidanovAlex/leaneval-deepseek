import Mathlib
import Submission.Work.ThomBordism.Grassmann.FibreBaseDefs

-- Lean v4.35.0-rc3: restore v4.34 instance-unification transparency (port).
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
set_option synthInstance.maxHeartbeats 400000

set_option autoImplicit false
set_option maxHeartbeats 3000000
set_option backward.isDefEq.respectTransparency false

/-!
# Auxiliary linear algebra for `fibreBaseHomeomorph`

The isometry property of `v ↦ ∑ v_i • f_i` for an orthonormal frame `f`
(`norm_frameComb`), and the existence of a special-orthogonal matrix with prescribed last column
(`exists_SO_lastColumn`).
-/

namespace Work.ThomBordism.Grassmann

open scoped Topology

noncomputable section

variable {k m : ℕ}

/-- **The inner product of two combinations of an orthonormal frame**: the coefficients pair up. -/
theorem inner_frameComb (k m : ℕ) (f : Stiefel k m) (v : Amb k) :
    inner ℝ (∑ i : Fin k, v.ofLp i • f.1 i) (∑ i : Fin k, v.ofLp i • f.1 i)
      = ∑ i : Fin k, v.ofLp i * v.ofLp i := by
  rw [sum_inner]
  refine Finset.sum_congr rfl fun i _ => ?_
  rw [inner_smul_left, inner_sum, Finset.mul_sum]
  rw [Finset.sum_eq_single i]
  · rw [inner_smul_right, orthonormal_iff_ite.mp f.2 i i, if_pos rfl, mul_one]
    simp only [starRingEnd_apply, star_trivial]
  · intro b _ hb
    rw [inner_smul_right, orthonormal_iff_ite.mp f.2 i b, if_neg (fun hh => hb hh.symm),
      mul_zero, mul_zero]
  · intro hmem; exact absurd (Finset.mem_univ i) hmem

/-- **The map `v ↦ ∑ v_i • f_i` attached to an orthonormal frame is an isometry.** -/
theorem norm_frameComb (k m : ℕ) (f : Stiefel k m) (v : Amb k) :
    ‖∑ i : Fin k, v.ofLp i • f.1 i‖ = ‖v‖ := by
  have h1 : ‖∑ i : Fin k, v.ofLp i • f.1 i‖ ^ 2 = ‖v‖ ^ 2 := by
    rw [← real_inner_self_eq_norm_sq (∑ i : Fin k, v.ofLp i • f.1 i), inner_frameComb,
      PiLp.norm_sq_eq_of_L2]
    exact Finset.sum_congr rfl fun i _ => by rw [Real.norm_eq_abs, sq_abs]; ring
  nlinarith [norm_nonneg (∑ i : Fin k, v.ofLp i • f.1 i), norm_nonneg v]

/-- **The linear isometry `v ↦ ∑ v_i • f_i` attached to an orthonormal frame `f`.** -/
noncomputable def frameComb (k m : ℕ) (f : Stiefel k m) : Amb k →ₗᵢ[ℝ] Amb (k+m) :=
  LinearIsometry.mk
    { toFun := fun v => ∑ i : Fin k, v.ofLp i • f.1 i
      map_add' := by
        intro x y
        rw [show (∑ i : Fin k, (x + y).ofLp i • f.1 i)
            = ∑ i : Fin k, (x.ofLp i • f.1 i + y.ofLp i • f.1 i) from
          Finset.sum_congr rfl (fun i _ => by rw [WithLp.ofLp_add, Pi.add_apply, add_smul]),
          Finset.sum_add_distrib]
      map_smul' := by
        intro a x
        rw [show (∑ i : Fin k, (a • x).ofLp i • f.1 i)
            = ∑ i : Fin k, a • (x.ofLp i • f.1 i) from
          Finset.sum_congr rfl (fun i _ => by rw [WithLp.ofLp_smul, Pi.smul_apply, smul_eq_mul,
            mul_smul]),
          Finset.smul_sum]
        rfl }
    (fun v => norm_frameComb k m f v)

@[simp] theorem frameComb_apply (f : Stiefel k m) (v : Amb k) :
    frameComb k m f v = ∑ i : Fin k, v.ofLp i • f.1 i := rfl

/-- **A special-orthogonal matrix with prescribed last column.**  For `k ≥ 2` and a unit vector
`c ∈ ℝ^k` there is `M ∈ SO(k)` whose last column is `c`: take any orthonormal basis of `c^⊥`,
append `c`, and, if the resulting orthogonal matrix has determinant `-1`, multiply on the right by
`diag(-1,1,…,1)` (which fixes the last column and flips the determinant). -/
theorem exists_SO_lastColumn (k : ℕ) (hk : 2 ≤ k) (c : Amb k) (hc : ‖c‖ = 1) :
    ∃ M : Matrix (Fin k) (Fin k) ℝ, IsSO M ∧
      ∀ i : Fin k, M i (lastk k (by omega)) = c.ofLp i := by
  have hk1 : 1 ≤ k := by omega
  have h0lt : 0 < k := hk1
  have hc0 : c ≠ 0 := by
    intro h; rw [h, norm_zero] at hc; norm_num at hc
  set W : Submodule ℝ (Amb k) := (Submodule.span ℝ ({c} : Set (Amb k)))ᗮ with hW
  have hfin : Module.finrank ℝ ↥W = k - 1 := by
    have h := Submodule.finrank_add_finrank_orthogonal (Submodule.span ℝ ({c} : Set (Amb k)))
    rw [finrank_span_singleton hc0, finrank_euclideanSpace, Fintype.card_fin] at h
    rw [hW]; omega
  let b : OrthonormalBasis (Fin (k-1)) ℝ ↥W :=
    (stdOrthonormalBasis ℝ ↥W).reindex (finCongr hfin)
  let u : Fin k → Amb k := fun j => if hj : j.val < k-1 then (b ⟨j.val, hj⟩ : Amb k) else c
  have hu : Orthonormal ℝ u := by
    rw [orthonormal_iff_ite]
    intro i j
    by_cases hi : i.val < k-1
    · by_cases hj : j.val < k-1
      · rw [show u i = (b ⟨i.val, hi⟩ : Amb k) from by dsimp only [u]; rw [dif_pos hi],
          show u j = (b ⟨j.val, hj⟩ : Amb k) from by dsimp only [u]; rw [dif_pos hj],
          ← Submodule.coe_inner,
          (orthonormal_iff_ite.mp b.orthonormal) ⟨i.val, hi⟩ ⟨j.val, hj⟩]
        by_cases hij : i = j
        · subst hij; rw [if_pos rfl, if_pos rfl]
        · rw [if_neg hij, if_neg (fun hh => hij (Fin.ext (by simpa using congrArg Fin.val hh)))]
      · have hjc : j.val = k-1 := by have := j.isLt; omega
        rw [show u i = (b ⟨i.val, hi⟩ : Amb k) from by dsimp only [u]; rw [dif_pos hi],
          show u j = c from by dsimp only [u]; rw [dif_neg hj]]
        have h0 : inner ℝ ((b ⟨i.val, hi⟩ : ↥W) : Amb k) c = 0 := by
          have hmem : ((b ⟨i.val, hi⟩ : ↥W) : Amb k)
              ∈ (Submodule.span ℝ ({c} : Set (Amb k)))ᗮ := by
            rw [← hW]; exact (b ⟨i.val, hi⟩).2
          exact (Submodule.mem_orthogonal' (Submodule.span ℝ ({c} : Set (Amb k))) _).mp hmem c
            (Submodule.subset_span (Set.mem_singleton c))
        rw [h0, if_neg (fun hij => by have := congrArg Fin.val hij; simp [hjc] at this; omega)]
    · have hic : i.val = k-1 := by have := i.isLt; omega
      by_cases hj : j.val < k-1
      · rw [show u i = c from by dsimp only [u]; rw [dif_neg hi],
          show u j = (b ⟨j.val, hj⟩ : Amb k) from by dsimp only [u]; rw [dif_pos hj]]
        have h0 : inner ℝ c ((b ⟨j.val, hj⟩ : ↥W) : Amb k) = 0 := by
          have hmem : ((b ⟨j.val, hj⟩ : ↥W) : Amb k)
              ∈ (Submodule.span ℝ ({c} : Set (Amb k)))ᗮ := by
            rw [← hW]; exact (b ⟨j.val, hj⟩).2
          exact (Submodule.mem_orthogonal (Submodule.span ℝ ({c} : Set (Amb k))) _).mp hmem c
            (Submodule.subset_span (Set.mem_singleton c))
        rw [h0, if_neg (fun hij => by have := congrArg Fin.val hij; simp [hic] at this; omega)]
      · have hjc : j.val = k-1 := by have := j.isLt; omega
        have hij : i = j := Fin.ext (by omega)
        rw [show u i = c from by dsimp only [u]; rw [dif_neg hi],
          show u j = c from by dsimp only [u]; rw [dif_neg hj],
          if_pos hij, real_inner_self_eq_norm_sq c, hc]
        norm_num
  let M0 : Matrix (Fin k) (Fin k) ℝ := fun i j => (u j).ofLp i
  have hM0 : M0.transpose * M0 = 1 := by
    ext i j
    simp only [Matrix.mul_apply, Matrix.transpose_apply, Matrix.one_apply]
    rw [show (∑ l : Fin k, (u i).ofLp l * (u j).ofLp l) = inner ℝ (u i) (u j) from by
      rw [PiLp.inner_apply]
      exact Finset.sum_congr rfl fun l _ => by rw [Real.inner_apply]]
    rw [(orthonormal_iff_ite.mp hu) i j]
  have hM0col : ∀ i : Fin k, M0 i (lastk k (by omega)) = c.ofLp i := by
    intro i
    have hlt : ¬ ((lastk k (by omega)).val < k-1) := by rw [lastk_val]; omega
    simp only [M0, u, dif_neg hlt]
  have hdet2 : M0.det * M0.det = 1 := by
    have h := congrArg Matrix.det hM0
    rwa [Matrix.det_mul, Matrix.det_transpose, Matrix.det_one] at h
  set eps : ℝ := M0.det with heps
  set D : Matrix (Fin k) (Fin k) ℝ :=
    Matrix.diagonal (fun i => if i = (⟨0, h0lt⟩ : Fin k) then eps else 1) with hD
  have hDdet : D.det = eps := by
    rw [hD, Matrix.det_diagonal]
    rw [Finset.prod_eq_single (⟨0, h0lt⟩ : Fin k)]
    · rw [if_pos rfl]
    · intro b' _ hb; rw [if_neg hb]
    · intro hmem; exact absurd (Finset.mem_univ _) hmem
  have hDtD : D.transpose * D = 1 := by
    rw [hD, Matrix.diagonal_transpose, Matrix.diagonal_mul_diagonal, ← Matrix.diagonal_one]
    congr 1
    funext i
    by_cases hi : i = (⟨0, h0lt⟩ : Fin k)
    · rw [if_pos hi]; exact hdet2
    · rw [if_neg hi]; ring
  have hDlast : D (lastk k (by omega)) (lastk k (by omega)) = 1 := by
    have hne : lastk k (by omega) ≠ (⟨0, h0lt⟩ : Fin k) := by
      intro h; have := congrArg Fin.val h; rw [lastk_val] at this; simp at this; omega
    rw [hD, Matrix.diagonal_apply_eq, if_neg hne]
  refine ⟨M0 * D, ⟨?_, ?_⟩, ?_⟩
  · rw [Matrix.transpose_mul]
    calc D.transpose * M0.transpose * (M0 * D) = D.transpose * (M0.transpose * M0) * D := by
          noncomm_ring
      _ = 1 := by rw [hM0, Matrix.mul_one, hDtD]
  · rw [Matrix.det_mul, hDdet]
    exact hdet2
  · intro i
    rw [Matrix.mul_apply, Finset.sum_eq_single (lastk k (by omega))]
    · rw [hDlast, mul_one, hM0col i]
    · intro b' _ hb
      rw [hD, Matrix.diagonal_apply_ne _ hb, mul_zero]
    · intro hmem; exact absurd (Finset.mem_univ _) hmem

end

end Work.ThomBordism.Grassmann
