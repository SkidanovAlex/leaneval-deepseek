import Mathlib
import Submission.Work.ThomBordism.LeadChapter.TubeDetDefs

-- Lean v4.35.0-rc3: restore v4.34 instance-unification transparency (port).
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
set_option synthInstance.maxHeartbeats 400000

/-!
# The `SO(k)`-ambiguity of the frame of a point of the oriented Grassmannian (`ogFrameSO`)

`Work.ThomBordism.LeadChapter.ogFrameCLM Γ` is the orthonormal frame of the oriented `k`-plane `Γ`,
read from the `Classical.choice` representative `Quotient.out Γ` of the `SO(k)`-orbit of frames.
The point of this file is that the *ambiguity* of that choice is precisely an `SO(k)`-matrix acting
on the *coefficients*:

* if `f : Stiefel k m = V_k(ℝ^{k+m})` is any orthonormal frame, then the chosen representative of
  `ogMk k m ⟨f, _⟩` differs from `f` by some `A ∈ SO(k)`,
  `(Quotient.out (ogMk k m ⟨f, _⟩)).1 = soActFun Aᵀ f`, and consequently
  `ogFrameCLM (ogMk k m ⟨f, _⟩) = (∑ b, proj_b ⊗ f b) ∘ matLin Aᵀ` where `matLin` is the linear
  endomorphism of `ℝ^k` given by the matrix (`Grassmann/Coord.lean`) — this is the first half of
  `ogFrameSO`;
* for the orientation reversal `ogFlip` (the frame is multiplied by `diag(-1,1,…,1)`) the
  comparison with the *same* reference frame `∑ b, proj_b ⊗ f b` is by a matrix of determinant
  `-1` — the second half.

The two matrix identities are the content of `frameCLM_soAct` (the coefficient bookkeeping) and the
orthogonality/norm preservation `norm_matLin_of_orthogonal`.
-/

set_option maxHeartbeats 1600000

namespace Work.ThomBordism.LeadChapter

open Work.ThomBordism.Grassmann

noncomputable section

variable {k m : ℕ}

/-- The coordinate projection of the Euclidean space, as a `rfl` unfolding. -/
theorem eucProj_apply (i : Fin k) (v : EuclideanSpace ℝ (Fin k)) :
    (EuclideanSpace.proj i : EuclideanSpace ℝ (Fin k) →L[ℝ] ℝ) v = v.ofLp i := rfl

/-- **The vector identity behind the frame transport**: expanding `∑ b, c b • (∑ t, M t b • F t)`
by exchanging the two sums, in the form needed by `frameCLM_soAct`. -/
theorem sum_smul_soAct (M : Matrix (Fin k) (Fin k) ℝ) (F : Fin k → Amb (k + m))
    (c : Fin k → ℝ) :
    (∑ b : Fin k, c b • soActFun M F b)
      = ∑ b : Fin k, (∑ t : Fin k, M b t * c t) • F b := by
  have h1 : ∀ b : Fin k, c b • soActFun M F b = ∑ t : Fin k, (c b * M t b) • F t := by
    intro b
    rw [soActFun, Finset.smul_sum]
    exact Finset.sum_congr rfl fun t _ => by rw [smul_smul, mul_comm]
  calc (∑ b : Fin k, c b • soActFun M F b)
      = ∑ b : Fin k, ∑ t : Fin k, (c b * M t b) • F t :=
        Finset.sum_congr rfl fun b _ => h1 b
    _ = ∑ t : Fin k, ∑ b : Fin k, (c b * M t b) • F t := Finset.sum_comm
    _ = ∑ t : Fin k, (∑ b : Fin k, c b * M t b) • F t := by
        exact Finset.sum_congr rfl fun t _ => (Finset.sum_smul).symm
    _ = ∑ t : Fin k, (∑ b : Fin k, M t b * c b) • F t := by
        refine Finset.sum_congr rfl fun t _ => ?_
        rw [Finset.sum_congr rfl fun b _ => mul_comm (c b) (M t b)]
    _ = ∑ b : Fin k, (∑ t : Fin k, M b t * c t) • F b := rfl

/-- **The frame transport.** Replacing the reference frame `F` by `soActFun M F` in the frame
`∑ b, proj_b ⊗ ⋯` amounts to precomposing with the endomorphism `matLin M` of `ℝ^k`. -/
theorem frameCLM_soAct (M : Matrix (Fin k) (Fin k) ℝ)
    (F : Fin k → EuclideanSpace ℝ (Fin (k + m))) :
    (∑ b : Fin k, (EuclideanSpace.proj b : EuclideanSpace ℝ (Fin k) →L[ℝ] ℝ).smulRight
        (soActFun M F b))
      = (∑ b : Fin k, (EuclideanSpace.proj b : EuclideanSpace ℝ (Fin k) →L[ℝ] ℝ).smulRight
        (F b)).comp (matLin M) := by
  apply ContinuousLinearMap.ext
  intro v
  simp only [sum_apply, ContinuousLinearMap.smulRight_apply, ContinuousLinearMap.comp_apply,
    matLin_apply, eucProj_apply]
  rw [sum_smul_soAct]
  refine Finset.sum_congr rfl fun b _ => ?_
  rw [mulVec_apply_sum]

/-- `⟨v, v⟩ = v.ofLp ⬝ᵥ v.ofLp` on `ℝ^n`. -/
theorem inner_self_eq_dotProduct (v : EuclideanSpace ℝ (Fin k)) :
    inner ℝ v v = v.ofLp ⬝ᵥ v.ofLp := by
  rw [PiLp.inner_apply, dotProduct]
  refine Finset.sum_congr rfl fun i _ => ?_
  rw [RCLike.inner_apply]
  simp

/-- **An orthogonal matrix acts on `ℝ^k` by an isometry.** -/
theorem norm_matLin_of_orthogonal {M : Matrix (Fin k) (Fin k) ℝ}
    (hM : M.transpose * M = 1) (v : EuclideanSpace ℝ (Fin k)) :
    ‖matLin M v‖ = ‖v‖ := by
  have hinner : inner ℝ (matLin M v) (matLin M v) = inner ℝ v v := by
    rw [inner_self_eq_dotProduct, inner_self_eq_dotProduct, matLin_apply, WithLp.ofLp_toLp]
    calc (M.mulVec v.ofLp) ⬝ᵥ (M.mulVec v.ofLp)
        = Matrix.vecMul (M.mulVec v.ofLp) M ⬝ᵥ v.ofLp := Matrix.dotProduct_mulVec _ _ _
      _ = Matrix.vecMul v.ofLp (M.transpose * M) ⬝ᵥ v.ofLp := by rw [Matrix.vecMul_mulVec]
      _ = Matrix.vecMul v.ofLp 1 ⬝ᵥ v.ofLp := by rw [hM]
      _ = v.ofLp ⬝ᵥ v.ofLp := by rw [Matrix.vecMul_one]
  have hsq : ‖matLin M v‖ ^ 2 = ‖v‖ ^ 2 := by
    rw [← real_inner_self_eq_norm_sq, ← real_inner_self_eq_norm_sq, hinner]
  rcases sq_eq_sq_iff_eq_or_eq_neg.mp hsq with h | h
  · exact h
  · have h1 : 0 ≤ ‖matLin M v‖ := norm_nonneg _
    have h2 : 0 ≤ ‖v‖ := norm_nonneg _
    linarith

/-- The determinant of the orientation reversing diagonal matrix `diag(-1,1,…,1)`. -/
theorem flipMat_det_neg (hk : 0 < k) : (flipMat k).det = -1 := by
  rw [flipMat, Matrix.det_diagonal]
  refine (Finset.prod_eq_single (⟨0, hk⟩ : Fin k) ?_ ?_).trans ?_
  · intro b _ hb
    rw [if_neg (fun h => hb (Fin.ext h))]
  · intro hmem; exact absurd (Finset.mem_univ _) hmem
  · rw [if_pos rfl]

/-- **The chosen representative of `ogMk k m f` is `f` acted on by an `SO(k)`-matrix.** -/
theorem exists_so_matrix {k m : ℕ} (f : Stiefel k m) :
    ∃ M : Matrix (Fin k) (Fin k) ℝ, IsSO M ∧
      (Quotient.out (Quotient.mk'' (s₁ := grassmannSetoid k m) f)).1 = soActFun M f.1 := by
  obtain ⟨A, hA⟩ :=
    Quotient.exact (Quotient.out_eq (s := grassmannSetoid k m) (Quotient.mk'' f))
  refine ⟨A.1.transpose, A.2.transpose, ?_⟩
  have h2 : A.transpose.act f = Quotient.out (Quotient.mk'' f) :=
    (congrArg (fun x => A.transpose.act x) hA).trans (SOk.act_transpose_act A _)
  rw [← h2]
  rfl

/-- **The chosen representative of `ogFlip (ogMk k m f)` is `f` acted on by a matrix of determinant
`-1`** (it differs from `diag(-1,1,…,1) · Aᵀ` by an `SO(k)`-matrix). -/
theorem exists_so_matrix_flip {k m : ℕ} (hk : 0 < k) (f : Stiefel k m) :
    ∃ M : Matrix (Fin k) (Fin k) ℝ, M.det = -1 ∧
      (Quotient.out (ogFlip k m (Quotient.mk'' (s₁ := grassmannSetoid k m) f))).1
        = soActFun M f.1 := by
  let G' : Stiefel k m :=
    ⟨soActFun (flipMat k) f.1, orthonormal_soActFun (flipMat_transpose_mul k) f.2⟩
  have hfl : ogFlip k m (Quotient.mk'' f) = Quotient.mk'' G' := ogFlip_mk f
  obtain ⟨A, hA⟩ :=
    Quotient.exact (Quotient.out_eq (s := grassmannSetoid k m) (Quotient.mk'' G'))
  refine ⟨flipMat k * A.1.transpose, ?_, ?_⟩
  · rw [Matrix.det_mul, Matrix.det_transpose, A.2.2, mul_one]
    exact flipMat_det_neg hk
  · have h2 : A.transpose.act G' = Quotient.out (Quotient.mk'' G') :=
      (congrArg (fun x => A.transpose.act x) hA).trans (SOk.act_transpose_act A _)
    rw [hfl, ← h2]
    show soActFun A.1.transpose G'.1 = soActFun (flipMat k * A.1.transpose) f.1
    rw [show G'.1 = soActFun (flipMat k) f.1 from rfl, soActFun_comp]

/-- **The frame of `Γ`, read against a reference frame.** If the chosen representative of `Γ` is
`soActFun M F`, then `ogFrameCLM Γ` is the frame `∑ b, proj_b ⊗ F b` precomposed with `matLin M`. -/
theorem ogFrameCLM_out_eq {k m : ℕ} (Γ : OG k m) (M : Matrix (Fin k) (Fin k) ℝ)
    (F : Fin k → EuclideanSpace ℝ (Fin (k + m)))
    (h : (Quotient.out Γ).1 = soActFun M F) :
    ogFrameCLM Γ = (∑ b : Fin k, (EuclideanSpace.proj b : EuclideanSpace ℝ (Fin k) →L[ℝ] ℝ).smulRight
        (F b)).comp (matLin M) := by
  show (∑ a : Fin k, (EuclideanSpace.proj a : EuclideanSpace ℝ (Fin k) →L[ℝ] ℝ).smulRight
      ((Quotient.out Γ).1 a)) = _
  rw [h]
  exact frameCLM_soAct M F

/-- **The ambiguity of `ogFrameCLM` is a precomposition by an `SO(k)`-matrix** (and by an
orientation reversing matrix for the orientation reversal of the plane). -/
theorem ogFrameSO {k m : ℕ} (hk : 0 < k) (F : Fin k → EuclideanSpace ℝ (Fin (k + m)))
    (hF : Orthonormal ℝ F) :
    (∃ e : EuclideanSpace ℝ (Fin k) →L[ℝ] EuclideanSpace ℝ (Fin k),
        LinearMap.det e.toLinearMap = 1 ∧ (∀ v, ‖e v‖ = ‖v‖) ∧
        Work.ThomBordism.LeadChapter.ogFrameCLM (Work.ThomBordism.Grassmann.ogMk k m ⟨F, hF⟩)
          = (∑ b : Fin k, (EuclideanSpace.proj b : EuclideanSpace ℝ (Fin k) →L[ℝ] ℝ).smulRight
              (F b)).comp e) ∧
    (∃ e : EuclideanSpace ℝ (Fin k) →L[ℝ] EuclideanSpace ℝ (Fin k),
        LinearMap.det e.toLinearMap = -1 ∧
        Work.ThomBordism.LeadChapter.ogFrameCLM (Work.ThomBordism.Grassmann.ogFlip k m
            (Work.ThomBordism.Grassmann.ogMk k m ⟨F, hF⟩))
          = (Work.ThomBordism.LeadChapter.ogFrameCLM
              (Work.ThomBordism.Grassmann.ogMk k m ⟨F, hF⟩)).comp e) := by
  classical
  obtain ⟨M, hM, hMout⟩ := exists_so_matrix (⟨F, hF⟩ : Stiefel k m)
  obtain ⟨M', hM'det, hM'out⟩ := exists_so_matrix_flip hk (⟨F, hF⟩ : Stiefel k m)
  have hbase := ogFrameCLM_out_eq (ogMk k m (⟨F, hF⟩ : Stiefel k m)) M F hMout
  have hflip := ogFrameCLM_out_eq (ogFlip k m (ogMk k m (⟨F, hF⟩ : Stiefel k m))) M' F hM'out
  have hmul : M * (M.transpose * M') = M' := by
    rw [← Matrix.mul_assoc, IsSO.mul_transpose_self hM, Matrix.one_mul]
  refine ⟨⟨matLin M, ?_, ?_, hbase⟩, ⟨matLin (M.transpose * M'), ?_, ?_⟩⟩
  · rw [det_matLin]; exact hM.2
  · exact norm_matLin_of_orthogonal hM.1
  · rw [det_matLin, Matrix.det_mul, Matrix.det_transpose, hM.2, one_mul]
    exact hM'det
  · rw [hflip, hbase, ContinuousLinearMap.comp_assoc, ← matLin_mul, hmul]

end

end Work.ThomBordism.LeadChapter
