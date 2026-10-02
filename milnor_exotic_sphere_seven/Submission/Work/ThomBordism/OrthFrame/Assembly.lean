import Mathlib
import Submission.Work.ThomBordism.OrthFrame.FrameAlgebra
import Submission.Work.ThomBordism.tangentFrameSigns

-- Lean v4.35.0-rc3: restore v4.34 instance-unification transparency (port).
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
set_option synthInstance.maxHeartbeats 400000

set_option autoImplicit false
set_option maxHeartbeats 3200000
set_option linter.unusedVariables false
set_option linter.unusedSimpArgs false

/-!
# Assembly of the orientation correction of the normal frames

See `Submission/Work/ThomBordism/orthFrameOrientation.lean` for the mathematical content.  Here we
build the signs `ε i x = δ i.1 x · pairSign (tanFrame E i x) (orthFrame E ND i x)` — with `δ` the
chart-atlas signs of `Work.ThomBordism.tangentFrameSigns` — and prove the three conjuncts of
`Work.ThomBordism.orthFrameOrientation`.
-/

open scoped Manifold ContDiff Topology BigOperators

namespace Work.ThomBordism

open Work.ThomBordism.PontryaginThom Work.ThomBordism.OrthFrame Work.ThomBordism.Grassmann

noncomputable section

variable {V : Man8} {k : ℕ}

/-- `Real.sign` is continuous off `0`. -/
theorem continuousOn_sign_compl_zero : ContinuousOn Real.sign {t : ℝ | t ≠ 0} := by
  have h1 : ContinuousOn Real.sign (Set.Ioi 0) :=
    ContinuousOn.congr (s := Set.Ioi 0) (continuousOn_const (c := (1 : ℝ)))
      (fun t ht => Real.sign_of_pos ht)
  have h2 : ContinuousOn Real.sign (Set.Iio 0) :=
    ContinuousOn.congr (s := Set.Iio 0) (continuousOn_const (c := (-1 : ℝ)))
      (fun t ht => Real.sign_of_neg ht)
  have hunion : ({t : ℝ | t ≠ 0} : Set ℝ) = Set.Ioi 0 ∪ Set.Iio 0 := by
    ext t
    constructor
    · intro h
      rcases lt_trichotomy t 0 with hlt | heq | hgt
      · exact Or.inr hlt
      · exact absurd heq h
      · exact Or.inl hgt
    · rintro (h | h)
      · exact ne_of_gt h
      · exact ne_of_lt h
  rw [hunion]
  exact h1.union_of_isOpen h2 isOpen_Ioi isOpen_Iio

/-- The sign of the pair frame of an index: the candidate orientation correction. -/
def framePairSign (E : EmbeddingData V (8 + k)) (ND : NormalData V k E.e) (i : CoverIdx V k)
    (x : V.pt) : ℝ :=
  pairSign (tanFrame E i x) (Work.Tubular.orthFrame E ND i x)

/-- The determinant of the pair frame of an index does not vanish on the base set. -/
theorem pairMat_det_ne_zero (E : EmbeddingData V (8 + k)) (ND : NormalData V k E.e)
    (i : CoverIdx V k) {x : V.pt} (hx : x ∈ ND.D.baseSet i) :
    (pairMat (tanFrame E i x) (Work.Tubular.orthFrame E ND i x)).det ≠ 0 := by
  have hli := linearIndependent_pairFrame E ND i hx
  have hker : LinearMap.ker (Matrix.toLin'
      (pairMat (tanFrame E i x) (Work.Tubular.orthFrame E ND i x))) = ⊥ := by
    rw [LinearMap.ker_eq_bot']
    intro v hv
    have hmv : (pairMat (tanFrame E i x) (Work.Tubular.orthFrame E ND i x)).mulVec v
        = fun r => eucToFun (8 + k) (∑ c, v c • pairFrame (tanFrame E i x)
            (Work.Tubular.orthFrame E ND i x) c) (finSumFinEquiv r) := by
      funext r
      rw [Matrix.mulVec, dotProduct]
      simp only [pairMat_apply, Finset.sum_apply, Pi.smul_apply, smul_eq_mul, map_sum,
        ContinuousLinearMap.coe_sum', Finset.sum_apply, map_smul, ContinuousLinearMap.coe_smul',
        Pi.smul_apply, smul_eq_mul, mul_comm]
    have hv0 : Matrix.toLin' (pairMat (tanFrame E i x) (Work.Tubular.orthFrame E ND i x)) v = 0 :=
      hv
    rw [Matrix.toLin'_apply, hmv] at hv0
    have hsum0 : (∑ c, v c • pairFrame (tanFrame E i x)
        (Work.Tubular.orthFrame E ND i x) c) = 0 := by
      have h4 : eucToFun (8 + k) (∑ c, v c • pairFrame (tanFrame E i x)
          (Work.Tubular.orthFrame E ND i x) c) = 0 := by
        funext r
        have h3 := congrFun hv0 (finSumFinEquiv.symm r)
        simpa using h3
      have h5 := congrArg (funToEuc (8 + k)) h4
      simpa using h5
    funext i
    exact (Fintype.linearIndependent_iff.mp hli v hsum0) i
  have hdet : LinearMap.det (Matrix.toLin'
      (pairMat (tanFrame E i x) (Work.Tubular.orthFrame E ND i x))) ≠ 0 := by
    rw [Ne, LinearMap.det_eq_zero_iff_ker_ne_bot]
    exact fun h => h hker
  rwa [LinearMap.det_toLin'] at hdet

/-- The pair sign is `±1` on the base set. -/
theorem framePairSign_eq_one_or (E : EmbeddingData V (8 + k)) (ND : NormalData V k E.e)
    (i : CoverIdx V k) {x : V.pt} (hx : x ∈ ND.D.baseSet i) :
    framePairSign E ND i x = 1 ∨ framePairSign E ND i x = -1 :=
  pairSign_eq_one_or _ _ (pairMat_det_ne_zero E ND i hx)

/-- The pair sign is continuous on the base set. -/
theorem continuousOn_framePairSign (E : EmbeddingData V (8 + k)) (ND : NormalData V k E.e)
    (i : CoverIdx V k) :
    ContinuousOn (fun x => framePairSign E ND i x) (ND.D.baseSet i) := by
  have hdet : ContinuousOn
      (fun x => (pairMat (tanFrame E i x) (Work.Tubular.orthFrame E ND i x)).det)
      (ND.D.baseSet i) := by
    rw [continuousOn_iff_continuous_domRestrict]
    refine Continuous.matrix_det ?_
    refine continuous_pi fun r => continuous_pi fun c => ?_
    rcases c with a | b
    · simp only [pairMat_inl, pairFrame_inl]
      have hv : Continuous fun p : ↥(ND.D.baseSet i) => tanFrame E i p.1 a :=
        continuousOn_iff_continuous_domRestrict.mp (continuousOn_tanFrame E ND i a)
      exact (continuous_apply (finSumFinEquiv r)).comp
        ((eucToFun (8 + k)).continuous.comp hv)
    · simp only [pairMat_inr, pairFrame_inr]
      have hv : Continuous fun p : ↥(ND.D.baseSet i) =>
          Work.Tubular.orthFrame E ND i p.1 b :=
        continuousOn_iff_continuous_domRestrict.mp
          (Work.Tubular.continuousOn_orthFrame E ND i b)
      exact (continuous_apply (finSumFinEquiv r)).comp
        ((eucToFun (8 + k)).continuous.comp hv)
  refine ContinuousOn.comp (g := Real.sign)
    (f := fun x => (pairMat (tanFrame E i x) (Work.Tubular.orthFrame E ND i x)).det)
    continuousOn_sign_compl_zero hdet ?_
  intro x hx
  exact pairMat_det_ne_zero E ND i hx

/-- The change-of-frame matrix of the normal frames of two indices. -/
def frameChange (E : EmbeddingData V (8 + k)) (ND : NormalData V k E.e)
    (i j : CoverIdx V k) (x : V.pt) : Matrix (Fin k) (Fin k) ℝ :=
  fun b a => inner ℝ (Work.Tubular.orthFrame E ND j x b) (Work.Tubular.orthFrame E ND i x a)

/-- The `i`-frame expands in the `j`-frame with coefficients the change matrix. -/
theorem frameChange_expand (E : EmbeddingData V (8 + k)) (ND : NormalData V k E.e)
    (i j : CoverIdx V k) {x : V.pt} (hx : x ∈ ND.D.baseSet i ∩ ND.D.baseSet j) :
    ∀ a, Work.Tubular.orthFrame E ND i x a
      = ∑ b, frameChange E ND i j x b a • Work.Tubular.orthFrame E ND j x b := by
  intro a
  exact (Work.Tubular.sum_inner_smul_eq_self_of_mem_span
    (Work.Tubular.orthFrame_orthonormal E ND j hx.2)
    (by rw [Work.Tubular.span_orthFrame E ND j hx.2,
      ← Work.Tubular.span_orthFrame E ND i hx.1]
        exact Submodule.subset_span ⟨a, rfl⟩)).symm

/-- The change matrix is orthogonal (entrywise form). -/
theorem frameChange_entry (E : EmbeddingData V (8 + k)) (ND : NormalData V k E.e)
    (i j : CoverIdx V k) {x : V.pt} (hx : x ∈ ND.D.baseSet i ∩ ND.D.baseSet j)
    (c a : Fin k) :
    (∑ b, frameChange E ND i j x b c * frameChange E ND i j x b a) = if c = a then 1 else 0 := by
  have hexp := frameChange_expand E ND i j hx
  have hu := Work.Tubular.orthFrame_orthonormal E ND i hx.1
  have key : (∑ b, frameChange E ND i j x b c * frameChange E ND i j x b a)
      = inner ℝ (Work.Tubular.orthFrame E ND i x c) (Work.Tubular.orthFrame E ND i x a) := by
    conv_rhs => rw [hexp c]
    rw [sum_inner]
    refine Finset.sum_congr rfl fun b _ => ?_
    rw [inner_smul_left]
    rfl
  rw [key, orthonormal_iff_ite.mp hu c a]

/-- The change matrix is orthogonal. -/
theorem frameChange_transpose_mul (E : EmbeddingData V (8 + k)) (ND : NormalData V k E.e)
    (i j : CoverIdx V k) {x : V.pt} (hx : x ∈ ND.D.baseSet i ∩ ND.D.baseSet j) :
    Matrix.transpose (frameChange E ND i j x) * (frameChange E ND i j x) = 1 := by
  ext c a
  rw [Matrix.mul_apply, Matrix.one_apply]
  trans ∑ b, frameChange E ND i j x b c * frameChange E ND i j x b a
  · refine Finset.sum_congr rfl fun b _ => ?_
    rw [Matrix.transpose_apply]
  · exact frameChange_entry E ND i j hx c a

/-- The determinant of the change matrix is nonzero. -/
theorem frameChange_det_ne_zero (E : EmbeddingData V (8 + k)) (ND : NormalData V k E.e)
    (i j : CoverIdx V k) {x : V.pt} (hx : x ∈ ND.D.baseSet i ∩ ND.D.baseSet j) :
    (frameChange E ND i j x).det ≠ 0 := by
  intro h0
  have h1 := congrArg Matrix.det (frameChange_transpose_mul E ND i j hx)
  rw [Matrix.det_mul, h0, mul_zero, Matrix.det_one] at h1
  exact one_ne_zero h1.symm

/-- The special orthogonal structure on a scalar multiple of an orthogonal matrix. -/
theorem isSO_smul_of_det (c : ℝ) (hc : c = 1 ∨ c = -1) {M : Matrix (Fin k) (Fin k) ℝ}
    (horth : Matrix.transpose M * M = 1) (hdet : c = M.det) (hk : Odd k) :
    IsSO (c • M) := by
  constructor
  · rw [Matrix.transpose_smul, Matrix.smul_mul, Matrix.mul_smul, horth]
    rcases hc with hc | hc <;> rw [hc] <;> simp [smul_smul, one_smul]
  · rw [Matrix.det_smul, Fintype.card_fin, ← hdet]
    rcases hc with hc | hc
    · rw [hc, one_pow, one_mul]
    · rw [hc, ← pow_succ]
      exact Even.neg_one_pow (hk.add_odd odd_one)

end

end Work.ThomBordism
