import Mathlib
import Submission.Work.Drive.Whitney.exists_anchoredFrameOfFlagFamily
import Submission.Work.Drive.Whitney.glPathSolid
import Submission.Work.Drive.Whitney.stabilizerExtension
import Submission.Work.Drive.Whitney.detSignConst

open scoped Matrix.Norms.Elementwise

namespace Work.Drive.Whitney

open scoped ContDiff

variable {m k : ℕ}

/-- The `i`-th standard basis vector of `EuclideanSpace ℝ (Fin m)` seen among the first `k` vectors of
the standard frame. -/
noncomputable abbrev bvec (hkm : k ≤ m) (i : Fin k) : EuclideanSpace ℝ (Fin m) :=
  (EuclideanSpace.basisFun (Fin m) ℝ) (Fin.castLE hkm i)

/-- **The `G`-condition**: a linear equivalence fixes each of the first `k` standard basis vectors. -/
def GVal (hkm : k ≤ m)
    (Z : EuclideanSpace ℝ (Fin m) ≃L[ℝ] EuclideanSpace ℝ (Fin m)) : Prop :=
  ∀ i : Fin k, Z (bvec hkm i) = bvec hkm i

/-- The `G`-condition is preserved by composition. -/
theorem GVal_trans {hkm : k ≤ m}
    {Z W : EuclideanSpace ℝ (Fin m) ≃L[ℝ] EuclideanSpace ℝ (Fin m)}
    (hZ : GVal hkm Z) (hW : GVal hkm W) : GVal hkm (Z.trans W) := by
  intro i
  rw [ContinuousLinearEquiv.trans_apply, hZ i, hW i]

/-- A `G`-valued family is injective on the first `k` basis vectors. -/
theorem GVal_symm {hkm : k ≤ m}
    {Z : EuclideanSpace ℝ (Fin m) ≃L[ℝ] EuclideanSpace ℝ (Fin m)} (hZ : GVal hkm Z) :
    ∀ i : Fin k, Z.symm (bvec hkm i) = bvec hkm i := by
  intro i
  rw [← hZ i, ContinuousLinearEquiv.symm_apply_apply, hZ i]

/-- **The boundary correction.**  Given `G`-valued data `A`, `B` on the two edges and a `G`-valued
path `C` with `C 0 = (B 0)⁻¹` and `C 1 = (A 0)⁻¹`, the family
`σ s t = A (t * (1 - smoothTransition s)) * C s * B (t * smoothTransition s)`
is `G`-valued and has the prescribed values on the two edges. -/
theorem exists_boundaryCorrection {m k : ℕ} (hkm : k ≤ m)
    (A B C : ℝ → (EuclideanSpace ℝ (Fin m) ≃L[ℝ] EuclideanSpace ℝ (Fin m)))
    (hA : ContDiff ℝ ((⊤ : ℕ∞) : WithTop ℕ∞)
      (fun t : ℝ => (A t : EuclideanSpace ℝ (Fin m) →L[ℝ] EuclideanSpace ℝ (Fin m))))
    (hB : ContDiff ℝ ((⊤ : ℕ∞) : WithTop ℕ∞)
      (fun t : ℝ => (B t : EuclideanSpace ℝ (Fin m) →L[ℝ] EuclideanSpace ℝ (Fin m))))
    (hC : ContDiff ℝ ((⊤ : ℕ∞) : WithTop ℕ∞)
      (fun t : ℝ => (C t : EuclideanSpace ℝ (Fin m) →L[ℝ] EuclideanSpace ℝ (Fin m))))
    (hAf : ∀ t, GVal hkm (A t)) (hBf : ∀ t, GVal hkm (B t)) (hCf : ∀ t, GVal hkm (C t))
    (hC0 : C 0 = (B 0).symm) (hC1 : C 1 = (A 0).symm) :
    ∃ σ : ℝ → ℝ → (EuclideanSpace ℝ (Fin m) ≃L[ℝ] EuclideanSpace ℝ (Fin m)),
      ContDiff ℝ ((⊤ : ℕ∞) : WithTop ℕ∞)
        (fun p : ℝ × ℝ =>
          (σ p.1 p.2 : EuclideanSpace ℝ (Fin m) →L[ℝ] EuclideanSpace ℝ (Fin m))) ∧
      (∀ s t, GVal hkm (σ s t)) ∧
      (∀ t : ℝ, σ 0 t = A t) ∧ (∀ t : ℝ, σ 1 t = B t) := by
  classical
  refine ⟨fun s t => (A (t * (1 - Real.smoothTransition s))).trans
    ((C s).trans (B (t * Real.smoothTransition s))), ?_, ?_, ?_, ?_⟩
  · have h1 : ContDiff ℝ ((⊤ : ℕ∞) : WithTop ℕ∞)
        (fun p : ℝ × ℝ => (A (p.2 * (1 - Real.smoothTransition p.1)) :
          EuclideanSpace ℝ (Fin m) →L[ℝ] EuclideanSpace ℝ (Fin m))) :=
      hA.comp (by fun_prop)
    have h2 : ContDiff ℝ ((⊤ : ℕ∞) : WithTop ℕ∞)
        (fun p : ℝ × ℝ => (C p.1 : EuclideanSpace ℝ (Fin m) →L[ℝ] EuclideanSpace ℝ (Fin m))) :=
      hC.comp (by fun_prop)
    have h3 : ContDiff ℝ ((⊤ : ℕ∞) : WithTop ℕ∞)
        (fun p : ℝ × ℝ => (B (p.2 * Real.smoothTransition p.1) :
          EuclideanSpace ℝ (Fin m) →L[ℝ] EuclideanSpace ℝ (Fin m))) :=
      hB.comp (by fun_prop)
    have h123 := (h3.clm_comp h2).clm_comp h1
    have hfun : (fun p : ℝ × ℝ =>
          ((A (p.2 * (1 - Real.smoothTransition p.1))).trans
            ((C p.1).trans (B (p.2 * Real.smoothTransition p.1))) :
            EuclideanSpace ℝ (Fin m) →L[ℝ] EuclideanSpace ℝ (Fin m)))
        = fun p : ℝ × ℝ =>
          ((B (p.2 * Real.smoothTransition p.1) :
              EuclideanSpace ℝ (Fin m) →L[ℝ] EuclideanSpace ℝ (Fin m))).comp
            (((C p.1 : EuclideanSpace ℝ (Fin m) →L[ℝ] EuclideanSpace ℝ (Fin m))).comp
              (A (p.2 * (1 - Real.smoothTransition p.1)) :
                EuclideanSpace ℝ (Fin m) →L[ℝ] EuclideanSpace ℝ (Fin m))) := by
      funext p
      ext x
      simp [ContinuousLinearEquiv.trans_apply]
    rw [hfun]
    exact h123
  · intro s t
    exact GVal_trans (hAf _) (GVal_trans (hCf _) (hBf _))
  · intro t
    show (A (t * (1 - Real.smoothTransition (0 : ℝ)))).trans
      ((C 0).trans (B (t * Real.smoothTransition (0 : ℝ)))) = A t
    rw [Real.smoothTransition.zero, mul_zero, sub_zero, mul_one]
    ext x
    simp only [ContinuousLinearEquiv.trans_apply]
    rw [hC0]
    simp
  · intro t
    show (A (t * (1 - Real.smoothTransition (1 : ℝ)))).trans
      ((C 1).trans (B (t * Real.smoothTransition (1 : ℝ)))) = B t
    rw [Real.smoothTransition.one, sub_self, mul_zero, mul_one]
    ext x
    simp only [ContinuousLinearEquiv.trans_apply]
    rw [hC1]
    simp

end Work.Drive.Whitney

namespace Work.Drive.Whitney

open scoped ContDiff

variable {m k : ℕ}

/-- The inverse of a smooth family of linear equivalences is smooth. -/
theorem contDiff_symm_of_contDiff {n : ℕ}
    (Z : ℝ → (EuclideanSpace ℝ (Fin n) ≃L[ℝ] EuclideanSpace ℝ (Fin n)))
    (hZ : ContDiff ℝ ((⊤ : ℕ∞) : WithTop ℕ∞)
      (fun t : ℝ => (Z t : EuclideanSpace ℝ (Fin n) →L[ℝ] EuclideanSpace ℝ (Fin n)))) :
    ContDiff ℝ ((⊤ : ℕ∞) : WithTop ℕ∞)
      (fun t : ℝ => ((Z t).symm : EuclideanSpace ℝ (Fin n) →L[ℝ] EuclideanSpace ℝ (Fin n))) := by
  have hfun : (fun t : ℝ =>
        ContinuousLinearMap.inverse (Z t : EuclideanSpace ℝ (Fin n) →L[ℝ] EuclideanSpace ℝ (Fin n)))
      = fun t : ℝ => (((Z t).symm : EuclideanSpace ℝ (Fin n) ≃L[ℝ] EuclideanSpace ℝ (Fin n)) :
        EuclideanSpace ℝ (Fin n) →L[ℝ] EuclideanSpace ℝ (Fin n)) := by
    funext t
    refine ContinuousLinearMap.inverse_eq ?_ ?_
    · ext x
      simp [ContinuousLinearEquiv.symm_apply_apply]
    · ext x
      simp [ContinuousLinearEquiv.apply_symm_apply]
  rw [contDiff_iff_contDiffAt]
  intro t
  have hI : (Z t : EuclideanSpace ℝ (Fin n) →L[ℝ] EuclideanSpace ℝ (Fin n)).IsInvertible :=
    ⟨Z t, rfl⟩
  have h := (hI.contDiffAt_map_inverse).comp t hZ.contDiffAt
  rw [← hfun]
  exact h

end Work.Drive.Whitney


/-! ## The corner path inside the stabiliser

The auxiliary development below proves `Work.Drive.Whitney.FB.stabilizerPath`, the smooth
path-connectedness of the stabiliser of the first `k` standard basis vectors, used (through
`exists_boundaryCorrection`) to reconcile the two edge data in `frameExtensionBoundary`.
-/

namespace Work.Drive.Whitney.FB

open scoped Matrix.Norms.Elementwise

abbrev CInf : WithTop ℕ∞ := ((⊤ : ℕ∞) : WithTop ℕ∞)

noncomputable def matOf {N : ℕ}
    (Z : EuclideanSpace ℝ (Fin N) →L[ℝ] EuclideanSpace ℝ (Fin N)) : Matrix (Fin N) (Fin N) ℝ :=
  (Matrix.toEuclideanCLM (n := Fin N) (𝕜 := ℝ)).symm Z

@[simp] lemma toEuclideanCLM_matOf {N : ℕ}
    (Z : EuclideanSpace ℝ (Fin N) →L[ℝ] EuclideanSpace ℝ (Fin N)) :
    Matrix.toEuclideanCLM (n := Fin N) (𝕜 := ℝ) (matOf Z) = Z := by
  simp [matOf]

lemma ofLp_single {N : ℕ} (j : Fin N) : (EuclideanSpace.single j (1:ℝ)).ofLp = Pi.single j 1 := by
  simp [EuclideanSpace.single, Pi.single]

lemma matOf_apply {N : ℕ}
    (Z : EuclideanSpace ℝ (Fin N) →L[ℝ] EuclideanSpace ℝ (Fin N)) (i j : Fin N) :
    matOf Z i j = (Z (EuclideanSpace.single j 1)).ofLp i := by
  have h := Matrix.ofLp_toEuclideanCLM (matOf Z) (EuclideanSpace.single j 1)
  rw [toEuclideanCLM_matOf] at h
  rw [h, ofLp_single, Matrix.mulVec_single_one]
  rfl

lemma det_toEuclideanCLM {N : ℕ} (M : Matrix (Fin N) (Fin N) ℝ) :
    LinearMap.det ((Matrix.toEuclideanCLM (n := Fin N) (𝕜 := ℝ) M :
      EuclideanSpace ℝ (Fin N) →L[ℝ] EuclideanSpace ℝ (Fin N)) :
      EuclideanSpace ℝ (Fin N) →ₗ[ℝ] EuclideanSpace ℝ (Fin N)) = M.det := by
  rw [show ((Matrix.toEuclideanCLM (n := Fin N) (𝕜 := ℝ) M :
      EuclideanSpace ℝ (Fin N) →L[ℝ] EuclideanSpace ℝ (Fin N)) :
      EuclideanSpace ℝ (Fin N) →ₗ[ℝ] EuclideanSpace ℝ (Fin N)) = Matrix.toEuclideanLin M from
    Matrix.coe_toEuclideanCLM_eq_toEuclideanLin M]
  rw [Matrix.toEuclideanLin_eq_toLin_orthonormal]
  exact LinearMap.det_toLin _ _

lemma det_matOf {N : ℕ} (Z : EuclideanSpace ℝ (Fin N) →L[ℝ] EuclideanSpace ℝ (Fin N)) :
    LinearMap.det (Z : EuclideanSpace ℝ (Fin N) →ₗ[ℝ] EuclideanSpace ℝ (Fin N)) =
      (matOf Z).det := by
  conv_lhs => rw [← toEuclideanCLM_matOf Z]
  exact det_toEuclideanCLM (matOf Z)

lemma unitsEquiv_coe_gen {R : Type*} {M : Type*} [Semiring R] [AddCommMonoid M] [Module R M]
    [TopologicalSpace M] (f : (M →L[R] M)ˣ) :
    ((ContinuousLinearEquiv.unitsEquiv R M f : M →L[R] M)) = (f : M →L[R] M) := rfl

noncomputable def matEquiv {N : ℕ} (M : Matrix (Fin N) (Fin N) ℝ) (h : M.det ≠ 0) :
    EuclideanSpace ℝ (Fin N) ≃L[ℝ] EuclideanSpace ℝ (Fin N) :=
  ContinuousLinearEquiv.unitsEquiv ℝ (EuclideanSpace ℝ (Fin N))
    (IsUnit.unit (IsUnit.map
      (RingEquiv.toMonoidHom (Matrix.toEuclideanCLM (n := Fin N) (𝕜 := ℝ)).toAlgEquiv.toRingEquiv)
      ((Matrix.isUnit_iff_isUnit_det M).mpr (isUnit_iff_ne_zero.mpr h))))

lemma matEquiv_coe {N : ℕ} (M : Matrix (Fin N) (Fin N) ℝ) (h : M.det ≠ 0) :
    (matEquiv M h : EuclideanSpace ℝ (Fin N) →L[ℝ] EuclideanSpace ℝ (Fin N)) =
      Matrix.toEuclideanCLM (n := Fin N) (𝕜 := ℝ) M := by
  rw [matEquiv, unitsEquiv_coe_gen, IsUnit.unit_spec]
  rfl

lemma matOf_matEquiv {N : ℕ} (M : Matrix (Fin N) (Fin N) ℝ) (h : M.det ≠ 0) :
    matOf (matEquiv M h) = M := by
  simp [matOf, matEquiv_coe]

lemma toEuclideanCLM_apply_single {N : ℕ} (M : Matrix (Fin N) (Fin N) ℝ) (j : Fin N)
    (hcol : ∀ a, M a j = if a = j then 1 else 0) :
    Matrix.toEuclideanCLM (n := Fin N) (𝕜 := ℝ) M (EuclideanSpace.single j 1) =
      EuclideanSpace.single j 1 := by
  apply WithLp.ofLp_injective
  rw [Matrix.ofLp_toEuclideanCLM, ofLp_single, Matrix.mulVec_single_one]
  funext a
  rw [Matrix.col_apply, hcol a, Pi.single_apply]

noncomputable def entryLM {N : ℕ} (a b : Fin N) :
    (EuclideanSpace ℝ (Fin N) →L[ℝ] EuclideanSpace ℝ (Fin N)) →ₗ[ℝ] ℝ :=
  (LinearMap.proj a).comp ((WithLp.linearEquiv 2 ℝ (Fin N → ℝ)).toLinearMap.comp
    ((ContinuousLinearMap.apply ℝ (EuclideanSpace ℝ (Fin N))
      (EuclideanSpace.single b 1)).toLinearMap))

noncomputable def entryCLF {N : ℕ} (a b : Fin N) :
    (EuclideanSpace ℝ (Fin N) →L[ℝ] EuclideanSpace ℝ (Fin N)) →L[ℝ] ℝ :=
  LinearMap.toContinuousLinearMap (entryLM a b)

lemma entryCLF_apply {N : ℕ} (a b : Fin N)
    (Z : EuclideanSpace ℝ (Fin N) →L[ℝ] EuclideanSpace ℝ (Fin N)) :
    entryCLF a b Z = matOf Z a b := by
  rw [matOf_apply]
  simp [entryCLF, entryLM, LinearMap.toContinuousLinearMap]

theorem contDiff_matCLM {N : ℕ} {M : ℝ → Matrix (Fin N) (Fin N) ℝ}
    (hM : ContDiff ℝ CInf M) :
    ContDiff ℝ CInf (fun t => Matrix.toEuclideanCLM (n := Fin N) (𝕜 := ℝ) (M t)) := by
  rw [contDiff_clm_apply_iff]
  intro y
  rw [contDiff_piLp (p := 2)]
  intro i
  have hentry : ∀ i j : Fin N, ContDiff ℝ CInf (fun t : ℝ => M t i j) := by
    intro i j
    exact (contDiff_pi.mp (contDiff_pi.mp hM i)) j
  have h2 : ContDiff ℝ CInf (fun t : ℝ => Matrix.mulVec (M t) (fun j => y j) i) := by
    rw [show (fun t : ℝ => Matrix.mulVec (M t) (fun j => y j) i)
        = (fun t : ℝ => ∑ j, M t i j * y j) from by
      funext t; simp [Matrix.mulVec, dotProduct]]
    exact ContDiff.sum fun j _ => (hentry i j).mul contDiff_const
  convert h2 using 1
  ext t
  have h : WithLp.ofLp (Matrix.toEuclideanCLM (n := Fin N) (𝕜 := ℝ) (M t) y)
      = Matrix.mulVec (M t) (WithLp.ofLp y) :=
    Matrix.ofLp_toEuclideanCLM (n := Fin N) (𝕜 := ℝ) (M t) y
  have h2' := congrFun h i
  simpa [Matrix.mulVec, dotProduct, Finset.sum_apply] using h2'

theorem stabilizerPath {m k : ℕ} (hkm : k ≤ m)
    (X Y : EuclideanSpace ℝ (Fin m) ≃L[ℝ] EuclideanSpace ℝ (Fin m))
    (hX : ∀ i : Fin k, X ((EuclideanSpace.basisFun (Fin m) ℝ) (Fin.castLE hkm i)) =
      (EuclideanSpace.basisFun (Fin m) ℝ) (Fin.castLE hkm i))
    (hY : ∀ i : Fin k, Y ((EuclideanSpace.basisFun (Fin m) ℝ) (Fin.castLE hkm i)) =
      (EuclideanSpace.basisFun (Fin m) ℝ) (Fin.castLE hkm i))
    (hdet : 0 < (LinearMap.det (X : EuclideanSpace ℝ (Fin m) →ₗ[ℝ] EuclideanSpace ℝ (Fin m))) *
      (LinearMap.det (Y : EuclideanSpace ℝ (Fin m) →ₗ[ℝ] EuclideanSpace ℝ (Fin m)))) :
    ∃ h : ℝ → (EuclideanSpace ℝ (Fin m) ≃L[ℝ] EuclideanSpace ℝ (Fin m)),
      h 0 = X ∧ h 1 = Y ∧
      (∀ (r : ℝ) (i : Fin k),
        (h r) ((EuclideanSpace.basisFun (Fin m) ℝ) (Fin.castLE hkm i)) =
          (EuclideanSpace.basisFun (Fin m) ℝ) (Fin.castLE hkm i)) ∧
      ContDiff ℝ CInf
        (fun r : ℝ => (h r : EuclideanSpace ℝ (Fin m) →L[ℝ] EuclideanSpace ℝ (Fin m))) := by
  classical
  have hbvec : ∀ i : Fin k, (EuclideanSpace.basisFun (Fin m) ℝ) (Fin.castLE hkm i) =
      EuclideanSpace.single (Fin.castLE hkm i) 1 := fun i => EuclideanSpace.basisFun_apply _ _ _
  set MX : Matrix (Fin m) (Fin m) ℝ :=
    matOf (X : EuclideanSpace ℝ (Fin m) →L[ℝ] EuclideanSpace ℝ (Fin m)) with hMXdef
  set MY : Matrix (Fin m) (Fin m) ℝ :=
    matOf (Y : EuclideanSpace ℝ (Fin m) →L[ℝ] EuclideanSpace ℝ (Fin m)) with hMYdef
  have hXclm : ∀ i : Fin k, (X : EuclideanSpace ℝ (Fin m) →L[ℝ] EuclideanSpace ℝ (Fin m))
      ((EuclideanSpace.basisFun (Fin m) ℝ) (Fin.castLE hkm i)) =
      (EuclideanSpace.basisFun (Fin m) ℝ) (Fin.castLE hkm i) := by
    intro i
    show X ((EuclideanSpace.basisFun (Fin m) ℝ) (Fin.castLE hkm i)) =
      (EuclideanSpace.basisFun (Fin m) ℝ) (Fin.castLE hkm i)
    exact hX i
  have hYclm : ∀ i : Fin k, (Y : EuclideanSpace ℝ (Fin m) →L[ℝ] EuclideanSpace ℝ (Fin m))
      ((EuclideanSpace.basisFun (Fin m) ℝ) (Fin.castLE hkm i)) =
      (EuclideanSpace.basisFun (Fin m) ℝ) (Fin.castLE hkm i) := by
    intro i
    show Y ((EuclideanSpace.basisFun (Fin m) ℝ) (Fin.castLE hkm i)) =
      (EuclideanSpace.basisFun (Fin m) ℝ) (Fin.castLE hkm i)
    exact hY i
  have hMXcol : ∀ (i : Fin k) (j : Fin m),
      MX j (Fin.castLE hkm i) = if j = Fin.castLE hkm i then 1 else 0 := by
    intro i j
    rw [hMXdef, matOf_apply, ← hbvec i, hXclm i, hbvec i, ofLp_single, Pi.single_apply]
  have hMYcol : ∀ (i : Fin k) (j : Fin m),
      MY j (Fin.castLE hkm i) = if j = Fin.castLE hkm i then 1 else 0 := by
    intro i j
    rw [hMYdef, matOf_apply, ← hbvec i, hYclm i, hbvec i, ofLp_single, Pi.single_apply]
  have hMXdet : MX.det = LinearMap.det
      (X : EuclideanSpace ℝ (Fin m) →ₗ[ℝ] EuclideanSpace ℝ (Fin m)) := by
    rw [hMXdef]; exact (det_matOf _).symm
  have hMYdet : MY.det = LinearMap.det
      (Y : EuclideanSpace ℝ (Fin m) →ₗ[ℝ] EuclideanSpace ℝ (Fin m)) := by
    rw [hMYdef]; exact (det_matOf _).symm
  set p : Fin m → Prop := fun i => (i : ℕ) < k with hpdef
  haveI : DecidablePred p := fun i => Nat.decLt _ _
  -- the lower-left block vanishes
  have hzeroX : ∀ i, ¬ p i → ∀ j, p j → MX i j = 0 := by
    intro i hi j hj
    have h1 := hMXcol ⟨j.1, hj⟩ i
    rw [show Fin.castLE hkm ⟨j.1, hj⟩ = j from Fin.ext rfl] at h1
    rw [h1, if_neg]
    intro hcon
    exact hi (by rw [hpdef] at hj ⊢; rw [hcon]; exact hj)
  have hzeroY : ∀ i, ¬ p i → ∀ j, p j → MY i j = 0 := by
    intro i hi j hj
    have h1 := hMYcol ⟨j.1, hj⟩ i
    rw [show Fin.castLE hkm ⟨j.1, hj⟩ = j from Fin.ext rfl] at h1
    rw [h1, if_neg]
    intro hcon
    exact hi (by rw [hpdef] at hj ⊢; rw [hcon]; exact hj)
  have htwoX : MX.det = (MX.toSquareBlockProp p).det *
      (MX.toSquareBlockProp (fun i => ¬ p i)).det := Matrix.twoBlockTriangular_det MX p hzeroX
  have htwoY : MY.det = (MY.toSquareBlockProp p).det *
      (MY.toSquareBlockProp (fun i => ¬ p i)).det := Matrix.twoBlockTriangular_det MY p hzeroY
  have htopX : MX.toSquareBlockProp p = 1 := by
    ext a b
    rw [Matrix.toSquareBlockProp, Matrix.toBlock_apply]
    have h1 := hMXcol ⟨(b : Fin m).1, b.2⟩ (a : Fin m)
    rw [show Fin.castLE hkm ⟨(b : Fin m).1, b.2⟩ = (b : Fin m) from Fin.ext rfl] at h1
    rw [h1, Matrix.one_apply]
    by_cases hab : (a : Fin m) = (b : Fin m)
    · rw [if_pos hab, if_pos (Subtype.ext hab)]
    · rw [if_neg hab, if_neg (fun h => hab (Subtype.ext_iff.mp h))]
  have htopY : MY.toSquareBlockProp p = 1 := by
    ext a b
    rw [Matrix.toSquareBlockProp, Matrix.toBlock_apply]
    have h1 := hMYcol ⟨(b : Fin m).1, b.2⟩ (a : Fin m)
    rw [show Fin.castLE hkm ⟨(b : Fin m).1, b.2⟩ = (b : Fin m) from Fin.ext rfl] at h1
    rw [h1, Matrix.one_apply]
    by_cases hab : (a : Fin m) = (b : Fin m)
    · rw [if_pos hab, if_pos (Subtype.ext hab)]
    · rw [if_neg hab, if_neg (fun h => hab (Subtype.ext_iff.mp h))]
  -- the index type of the lower-right block
  let N : ℕ := Fintype.card {i : Fin m // ¬ p i}
  let eS : {i : Fin m // ¬ p i} ≃ Fin N := Fintype.equivFin _
  let BX : Matrix (Fin N) (Fin N) ℝ :=
    Matrix.reindex eS eS (MX.toSquareBlockProp (fun i => ¬ p i))
  let BY : Matrix (Fin N) (Fin N) ℝ :=
    Matrix.reindex eS eS (MY.toSquareBlockProp (fun i => ¬ p i))
  have hBXdet : BX.det = MX.det := by
    rw [show BX = Matrix.reindex eS eS (MX.toSquareBlockProp (fun i => ¬ p i)) from rfl,
      Matrix.det_reindex_self, htwoX, htopX, Matrix.det_one, one_mul]
  have hBYdet : BY.det = MY.det := by
    rw [show BY = Matrix.reindex eS eS (MY.toSquareBlockProp (fun i => ¬ p i)) from rfl,
      Matrix.det_reindex_self, htwoY, htopY, Matrix.det_one, one_mul]
  have hXdetne : LinearMap.det (X : EuclideanSpace ℝ (Fin m) →ₗ[ℝ] EuclideanSpace ℝ (Fin m)) ≠ 0 :=
    (LinearEquiv.isUnit_det' X.toLinearEquiv).ne_zero
  have hYdetne : LinearMap.det (Y : EuclideanSpace ℝ (Fin m) →ₗ[ℝ] EuclideanSpace ℝ (Fin m)) ≠ 0 :=
    (LinearEquiv.isUnit_det' Y.toLinearEquiv).ne_zero
  have hBXne : BX.det ≠ 0 := by rw [hBXdet, hMXdet]; exact hXdetne
  have hBYne : BY.det ≠ 0 := by rw [hBYdet, hMYdet]; exact hYdetne
  let NX : EuclideanSpace ℝ (Fin N) ≃L[ℝ] EuclideanSpace ℝ (Fin N) := matEquiv BX hBXne
  let NY : EuclideanSpace ℝ (Fin N) ≃L[ℝ] EuclideanSpace ℝ (Fin N) := matEquiv BY hBYne
  have hNXdet : LinearMap.det
      (NX : EuclideanSpace ℝ (Fin N) →ₗ[ℝ] EuclideanSpace ℝ (Fin N)) = BX.det := by
    rw [show (NX : EuclideanSpace ℝ (Fin N) →ₗ[ℝ] EuclideanSpace ℝ (Fin N)) =
      ((NX : EuclideanSpace ℝ (Fin N) →L[ℝ] EuclideanSpace ℝ (Fin N)) :
        EuclideanSpace ℝ (Fin N) →ₗ[ℝ] EuclideanSpace ℝ (Fin N)) from rfl]
    rw [det_matOf]
    rw [show matOf (NX : EuclideanSpace ℝ (Fin N) →L[ℝ] EuclideanSpace ℝ (Fin N)) = BX from by
      rw [show (NX : EuclideanSpace ℝ (Fin N) →L[ℝ] EuclideanSpace ℝ (Fin N)) =
        matEquiv BX hBXne from rfl, matOf_matEquiv]]
  have hNYdet : LinearMap.det
      (NY : EuclideanSpace ℝ (Fin N) →ₗ[ℝ] EuclideanSpace ℝ (Fin N)) = BY.det := by
    rw [show (NY : EuclideanSpace ℝ (Fin N) →ₗ[ℝ] EuclideanSpace ℝ (Fin N)) =
      ((NY : EuclideanSpace ℝ (Fin N) →L[ℝ] EuclideanSpace ℝ (Fin N)) :
        EuclideanSpace ℝ (Fin N) →ₗ[ℝ] EuclideanSpace ℝ (Fin N)) from rfl]
    rw [det_matOf]
    rw [show matOf (NY : EuclideanSpace ℝ (Fin N) →L[ℝ] EuclideanSpace ℝ (Fin N)) = BY from by
      rw [show (NY : EuclideanSpace ℝ (Fin N) →L[ℝ] EuclideanSpace ℝ (Fin N)) =
        matEquiv BY hBYne from rfl, matOf_matEquiv]]
  have hdet' : 0 < LinearMap.det
        (NX : EuclideanSpace ℝ (Fin N) →ₗ[ℝ] EuclideanSpace ℝ (Fin N)) *
      LinearMap.det (NY : EuclideanSpace ℝ (Fin N) →ₗ[ℝ] EuclideanSpace ℝ (Fin N)) := by
    rw [hNXdet, hNYdet, hBXdet, hBYdet, hMXdet, hMYdet]
    exact hdet
  obtain ⟨g, hg0, hg1, hgcont⟩ := glPathSolid (N := N) NX NY hdet'
  let Bmat : ℝ → Matrix {i : Fin m // ¬ p i} {i : Fin m // ¬ p i} ℝ :=
    fun r a b => matOf (g r : EuclideanSpace ℝ (Fin N) →L[ℝ] EuclideanSpace ℝ (Fin N)) (eS a) (eS b)
  have hBmat0 : Bmat 0 = MX.toSquareBlockProp (fun i => ¬ p i) := by
    ext a b
    rw [show Bmat 0 a b = matOf (g 0 : EuclideanSpace ℝ (Fin N) →L[ℝ] EuclideanSpace ℝ (Fin N))
      (eS a) (eS b) from rfl, hg0]
    rw [show matOf (NX : EuclideanSpace ℝ (Fin N) →L[ℝ] EuclideanSpace ℝ (Fin N)) = BX from by
      rw [show (NX : EuclideanSpace ℝ (Fin N) →L[ℝ] EuclideanSpace ℝ (Fin N)) =
        matEquiv BX hBXne from rfl, matOf_matEquiv]]
    rw [show BX = Matrix.reindex eS eS (MX.toSquareBlockProp (fun i => ¬ p i)) from rfl,
      Matrix.reindex_apply, Matrix.submatrix_apply, Equiv.symm_apply_apply, Equiv.symm_apply_apply]
  have hBmat1 : Bmat 1 = MY.toSquareBlockProp (fun i => ¬ p i) := by
    ext a b
    rw [show Bmat 1 a b = matOf (g 1 : EuclideanSpace ℝ (Fin N) →L[ℝ] EuclideanSpace ℝ (Fin N))
      (eS a) (eS b) from rfl, hg1]
    rw [show matOf (NY : EuclideanSpace ℝ (Fin N) →L[ℝ] EuclideanSpace ℝ (Fin N)) = BY from by
      rw [show (NY : EuclideanSpace ℝ (Fin N) →L[ℝ] EuclideanSpace ℝ (Fin N)) =
        matEquiv BY hBYne from rfl, matOf_matEquiv]]
    rw [show BY = Matrix.reindex eS eS (MY.toSquareBlockProp (fun i => ¬ p i)) from rfl,
      Matrix.reindex_apply, Matrix.submatrix_apply, Equiv.symm_apply_apply, Equiv.symm_apply_apply]
  have hBmatre : ∀ r, Bmat r = Matrix.reindex eS.symm eS.symm
      (matOf (g r : EuclideanSpace ℝ (Fin N) →L[ℝ] EuclideanSpace ℝ (Fin N))) := by
    intro r
    ext a b
    show matOf (g r : EuclideanSpace ℝ (Fin N) →L[ℝ] EuclideanSpace ℝ (Fin N)) (eS a) (eS b) =
      (Matrix.reindex eS.symm eS.symm
        (matOf (g r : EuclideanSpace ℝ (Fin N) →L[ℝ] EuclideanSpace ℝ (Fin N)))) a b
    rw [Matrix.reindex_apply, Matrix.submatrix_apply]
    rfl
  have hBmatne : ∀ r, (Bmat r).det ≠ 0 := by
    intro r
    rw [hBmatre r, Matrix.det_reindex_self, ← det_matOf
      (g r : EuclideanSpace ℝ (Fin N) →L[ℝ] EuclideanSpace ℝ (Fin N))]
    exact (LinearEquiv.isUnit_det' (g r).toLinearEquiv).ne_zero
  let M : ℝ → Matrix (Fin m) (Fin m) ℝ := fun r i j =>
    if hj : p j then (if i = j then 1 else 0)
    else if hi : p i then
      ((1 - r) • (MX.toBlock p (fun i => ¬ p i)) ⟨i, hi⟩ ⟨j, hj⟩
        + r • (MY.toBlock p (fun i => ¬ p i)) ⟨i, hi⟩ ⟨j, hj⟩)
    else Bmat r ⟨i, hi⟩ ⟨j, hj⟩
  have hM0 : M 0 = MX := by
    ext i j
    dsimp only [M]
    by_cases hj : p j
    · rw [dif_pos hj]
      have h1 := hMXcol ⟨(j : Fin m).1, hj⟩ i
      rw [show Fin.castLE hkm ⟨(j : Fin m).1, hj⟩ = (j : Fin m) from Fin.ext rfl] at h1
      rw [h1]
    · rw [dif_neg hj]
      by_cases hi : p i
      · rw [dif_pos hi]
        simp only [sub_zero, one_smul, zero_smul, add_zero]
        rw [Matrix.toBlock_apply]
      · rw [dif_neg hi, hBmat0, Matrix.toSquareBlockProp, Matrix.toBlock_apply]
  have hM1 : M 1 = MY := by
    ext i j
    dsimp only [M]
    by_cases hj : p j
    · rw [dif_pos hj]
      have h1 := hMYcol ⟨(j : Fin m).1, hj⟩ i
      rw [show Fin.castLE hkm ⟨(j : Fin m).1, hj⟩ = (j : Fin m) from Fin.ext rfl] at h1
      rw [h1]
    · rw [dif_neg hj]
      by_cases hi : p i
      · rw [dif_pos hi]
        simp only [sub_self, zero_smul, one_smul, zero_add]
        rw [Matrix.toBlock_apply]
      · rw [dif_neg hi, hBmat1, Matrix.toSquareBlockProp, Matrix.toBlock_apply]
  have hMdet : ∀ r, (M r).det = (Bmat r).det := by
    intro r
    have hz : ∀ i, ¬ p i → ∀ j, p j → M r i j = 0 := by
      intro i hi j hj
      dsimp only [M]
      rw [dif_pos hj, if_neg]
      intro hcon
      exact hi (by rw [hpdef] at hj ⊢; rw [hcon]; exact hj)
    have htwo := Matrix.twoBlockTriangular_det (M r) p hz
    have htop : (M r).toSquareBlockProp p = 1 := by
      ext a b
      rw [Matrix.toSquareBlockProp, Matrix.toBlock_apply]
      dsimp only [M]
      rw [dif_pos b.2, Matrix.one_apply]
      by_cases hab : (a : Fin m) = (b : Fin m)
      · rw [if_pos hab, if_pos (Subtype.ext hab)]
      · rw [if_neg hab, if_neg (fun h => hab (Subtype.ext_iff.mp h))]
    have hbot : (M r).toSquareBlockProp (fun i => ¬ p i) = Bmat r := by
      ext a b
      rw [Matrix.toSquareBlockProp, Matrix.toBlock_apply]
      dsimp only [M]
      rw [dif_neg b.2, dif_neg a.2]
    rw [htwo, htop, Matrix.det_one, one_mul, hbot]
  have hMcol : ∀ (r : ℝ) (i : Fin k) (a : Fin m),
      M r a (Fin.castLE hkm i) = if a = Fin.castLE hkm i then 1 else 0 := by
    intro r i a
    dsimp only [M]
    rw [dif_pos (show p (Fin.castLE hkm i) from i.2)]
  have hMne : ∀ r, (M r).det ≠ 0 := fun r => by rw [hMdet r]; exact hBmatne r
  refine ⟨fun r => matEquiv (M r) (hMne r), ?_, ?_, ?_, ?_⟩
  · apply ContinuousLinearEquiv.coe_injective
    rw [show ((matEquiv (M 0) (hMne 0) : EuclideanSpace ℝ (Fin m) ≃L[ℝ] EuclideanSpace ℝ (Fin m)) :
        EuclideanSpace ℝ (Fin m) →L[ℝ] EuclideanSpace ℝ (Fin m))
        = Matrix.toEuclideanCLM (n := Fin m) (𝕜 := ℝ) (M 0) from matEquiv_coe _ _]
    rw [hM0, hMXdef]
    exact toEuclideanCLM_matOf _
  · apply ContinuousLinearEquiv.coe_injective
    rw [show ((matEquiv (M 1) (hMne 1) : EuclideanSpace ℝ (Fin m) ≃L[ℝ] EuclideanSpace ℝ (Fin m)) :
        EuclideanSpace ℝ (Fin m) →L[ℝ] EuclideanSpace ℝ (Fin m))
        = Matrix.toEuclideanCLM (n := Fin m) (𝕜 := ℝ) (M 1) from matEquiv_coe _ _]
    rw [hM1, hMYdef]
    exact toEuclideanCLM_matOf _
  · intro r i
    show (matEquiv (M r) (hMne r) :
      EuclideanSpace ℝ (Fin m) →L[ℝ] EuclideanSpace ℝ (Fin m))
      ((EuclideanSpace.basisFun (Fin m) ℝ) (Fin.castLE hkm i)) = _
    rw [matEquiv_coe, hbvec i]
    exact toEuclideanCLM_apply_single (M r) (Fin.castLE hkm i) (fun a => hMcol r i a)
  · have hfun : (fun r : ℝ => ((matEquiv (M r) (hMne r) :
        EuclideanSpace ℝ (Fin m) ≃L[ℝ] EuclideanSpace ℝ (Fin m)) :
        EuclideanSpace ℝ (Fin m) →L[ℝ] EuclideanSpace ℝ (Fin m)))
        = fun r : ℝ => Matrix.toEuclideanCLM (n := Fin m) (𝕜 := ℝ) (M r) := by
      funext r
      exact matEquiv_coe _ _
    rw [hfun]
    refine contDiff_toEuclideanCLM_comp ?_
    change ContDiff ℝ CInf (fun r : ℝ => fun i : Fin m => fun j : Fin m => M r i j)
    rw [contDiff_pi]
    intro i
    rw [contDiff_pi]
    intro j
    by_cases hj : p j
    · rw [show (fun r : ℝ => M r i j) = (fun _ : ℝ => (if i = j then (1:ℝ) else 0)) from by
        funext r
        dsimp only [M]
        rw [dif_pos hj]]
      fun_prop
    · by_cases hi : p i
      · rw [show (fun r : ℝ => M r i j) = (fun r : ℝ =>
          ((1 - r) • (MX.toBlock p (fun i => ¬ p i)) ⟨i, hi⟩ ⟨j, hj⟩
            + r • (MY.toBlock p (fun i => ¬ p i)) ⟨i, hi⟩ ⟨j, hj⟩)) from by
          funext r
          dsimp only [M]
          rw [dif_neg hj, dif_pos hi]]
        fun_prop
      · rw [show (fun r : ℝ => M r i j) = (fun r : ℝ => Bmat r ⟨i, hi⟩ ⟨j, hj⟩) from by
          funext r
          dsimp only [M]
          rw [dif_neg hj, dif_neg hi]]
        rw [show (fun r : ℝ => Bmat r ⟨i, hi⟩ ⟨j, hj⟩) = (fun r : ℝ =>
          entryCLF (eS ⟨i, hi⟩) (eS ⟨j, hj⟩)
            (g r : EuclideanSpace ℝ (Fin N) →L[ℝ] EuclideanSpace ℝ (Fin N))) from by
          funext r
          show matOf (g r : EuclideanSpace ℝ (Fin N) →L[ℝ] EuclideanSpace ℝ (Fin N))
            (eS ⟨i, hi⟩) (eS ⟨j, hj⟩) = _
          rw [entryCLF_apply]]
        exact (entryCLF (eS ⟨i, hi⟩) (eS ⟨j, hj⟩)).contDiff.comp hgcont


end Work.Drive.Whitney.FB

namespace Work.Drive.Whitney

open scoped ContDiff

variable {m k : ℕ}

/-- **Smooth frame extension with prescribed values on the two edges.** -/
theorem frameExtensionBoundary {m k : ℕ} (hkm : k ≤ m)
    (b : ℝ → ℝ → (Fin k → EuclideanSpace ℝ (Fin m)))
    (hb : ∀ i : Fin k,
      ContDiff ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) (fun p : ℝ × ℝ => b p.1 p.2 i))
    (hind : ∀ p : ℝ × ℝ, LinearIndependent ℝ (b p.1 p.2))
    (hbnd0 : ∀ t ∈ Set.Icc (0 : ℝ) 1,
      b 0 t = fun i => (EuclideanSpace.basisFun (Fin m) ℝ) (Fin.castLE hkm i))
    (hbnd1 : ∀ t ∈ Set.Icc (0 : ℝ) 1,
      b 1 t = fun i => (EuclideanSpace.basisFun (Fin m) ℝ) (Fin.castLE hkm i)) :
    ∃ Ψ : ℝ → ℝ → (EuclideanSpace ℝ (Fin m) ≃L[ℝ] EuclideanSpace ℝ (Fin m)),
      ContDiff ℝ ((⊤ : ℕ∞) : WithTop ℕ∞)
        (fun p : ℝ × ℝ =>
          (Ψ p.1 p.2 : EuclideanSpace ℝ (Fin m) →L[ℝ] EuclideanSpace ℝ (Fin m))) ∧
      (∀ p : ℝ × ℝ, ∀ i : Fin k,
        Ψ p.1 p.2 ((EuclideanSpace.basisFun (Fin m) ℝ) (Fin.castLE hkm i)) = b p.1 p.2 i) ∧
      (∀ t ∈ Set.Icc (0 : ℝ) 1, Ψ 0 t = 1) ∧
      (∀ t ∈ Set.Icc (0 : ℝ) 1, Ψ 1 t = 1) := by
  classical
  obtain ⟨Ψg, hΨg_sm, hΨg_col⟩ := exists_smoothFrame_extension_local hkm b hb hind
  -- the smoothness of the two edge data as families of continuous linear maps
  have hA_sm : ContDiff ℝ ((⊤ : ℕ∞) : WithTop ℕ∞)
      (fun t : ℝ => ((Ψg 0 t).symm :
        EuclideanSpace ℝ (Fin m) →L[ℝ] EuclideanSpace ℝ (Fin m))) :=
    contDiff_symm_of_contDiff _ (hΨg_sm.comp (contDiff_const.prodMk contDiff_id))
  have hB_sm : ContDiff ℝ ((⊤ : ℕ∞) : WithTop ℕ∞)
      (fun t : ℝ => ((Ψg 1 t).symm :
        EuclideanSpace ℝ (Fin m) →L[ℝ] EuclideanSpace ℝ (Fin m))) :=
    contDiff_symm_of_contDiff _ (hΨg_sm.comp (contDiff_const.prodMk contDiff_id))
  -- the `G`-condition on the strip
  have hcol0 : ∀ t ∈ Set.Icc (0 : ℝ) 1, ∀ i : Fin k,
      Ψg 0 t (bvec hkm i) = bvec hkm i := by
    intro t ht i
    rw [hΨg_col (0, t) i]
    exact congrFun (hbnd0 t ht) i
  have hcol1 : ∀ t ∈ Set.Icc (0 : ℝ) 1, ∀ i : Fin k,
      Ψg 1 t (bvec hkm i) = bvec hkm i := by
    intro t ht i
    rw [hΨg_col (1, t) i]
    exact congrFun (hbnd1 t ht) i
  have hAf : ∀ t ∈ Set.Icc (0 : ℝ) 1, ∀ i : Fin k,
      (Ψg 0 t).symm (bvec hkm i) = bvec hkm i := by
    intro t ht i
    rw [ContinuousLinearEquiv.symm_apply_eq]
    exact (hcol0 t ht i).symm
  have hBf : ∀ t ∈ Set.Icc (0 : ℝ) 1, ∀ i : Fin k,
      (Ψg 1 t).symm (bvec hkm i) = bvec hkm i := by
    intro t ht i
    rw [ContinuousLinearEquiv.symm_apply_eq]
    exact (hcol1 t ht i).symm
  -- extend the data off the strip
  obtain ⟨Ae, hAe_sm, hAe_eq, hAe_fix⟩ :=
    stabilizerExtension hkm (fun t => (Ψg 0 t).symm) hA_sm hAf
  obtain ⟨Be, hBe_sm, hBe_eq, hBe_fix⟩ :=
    stabilizerExtension hkm (fun t => (Ψg 1 t).symm) hB_sm hBf
  -- the corner path, from `Ψg 1 0 = (Be 0)⁻¹` to `Ψg 0 0 = (Ae 0)⁻¹`
  have h03 : (0 : ℝ) ∈ Set.Icc (0 : ℝ) 1 := ⟨le_rfl, zero_le_one⟩
  have hX : ∀ i : Fin k, Ψg 1 0 (bvec hkm i) = bvec hkm i := hcol1 0 h03
  have hY : ∀ i : Fin k, Ψg 0 0 (bvec hkm i) = bvec hkm i := hcol0 0 h03
  obtain ⟨C, hC0', hC1', hC_fix, hC_sm⟩ :=
    FB.stabilizerPath hkm (Ψg 1 0) (Ψg 0 0) hX hY
      (detSignConst (fun p : ℝ × ℝ => Ψg p.1 p.2) hΨg_sm (1, 0) (0, 0))
  -- the boundary correction
  obtain ⟨σ, hσ_sm, hσ_fix, hσ0, hσ1⟩ :=
    exists_boundaryCorrection hkm Ae Be C hAe_sm hBe_sm hC_sm hAe_fix hBe_fix hC_fix
      (by rw [hC0', hBe_eq 0 ⟨le_rfl, zero_le_one⟩]; simp)
      (by rw [hC1', hAe_eq 0 ⟨le_rfl, zero_le_one⟩]; simp)
  -- the final family
  refine ⟨fun s t => (σ s t).trans (Ψg s t), ?_, ?_, ?_, ?_⟩
  · -- smoothness
    have h1 : ContDiff ℝ ((⊤ : ℕ∞) : WithTop ℕ∞)
        (fun p : ℝ × ℝ => (Ψg p.1 p.2 :
          EuclideanSpace ℝ (Fin m) →L[ℝ] EuclideanSpace ℝ (Fin m))) := hΨg_sm
    have h2 : ContDiff ℝ ((⊤ : ℕ∞) : WithTop ℕ∞)
        (fun p : ℝ × ℝ => (σ p.1 p.2 :
          EuclideanSpace ℝ (Fin m) →L[ℝ] EuclideanSpace ℝ (Fin m))) := hσ_sm
    have h12 := h1.clm_comp h2
    have hfun : (fun p : ℝ × ℝ =>
          (((σ p.1 p.2).trans (Ψg p.1 p.2)) :
            EuclideanSpace ℝ (Fin m) →L[ℝ] EuclideanSpace ℝ (Fin m)))
        = fun p : ℝ × ℝ =>
          ((Ψg p.1 p.2 : EuclideanSpace ℝ (Fin m) →L[ℝ] EuclideanSpace ℝ (Fin m))).comp
            ((σ p.1 p.2 : EuclideanSpace ℝ (Fin m) →L[ℝ] EuclideanSpace ℝ (Fin m))) := by
      funext p
      ext x
      simp [ContinuousLinearEquiv.trans_apply]
    rw [hfun]
    exact h12
  · intro p i
    show (σ p.1 p.2).trans (Ψg p.1 p.2) ((EuclideanSpace.basisFun (Fin m) ℝ) (Fin.castLE hkm i))
      = b p.1 p.2 i
    rw [ContinuousLinearEquiv.trans_apply, hσ_fix p.1 p.2 i, hΨg_col p i]
  · intro t ht
    show (σ 0 t).trans (Ψg 0 t) = 1
    rw [hσ0 t, hAe_eq t ht, ContinuousLinearEquiv.symm_trans_self]
    rfl
  · intro t ht
    show (σ 1 t).trans (Ψg 1 t) = 1
    rw [hσ1 t, hBe_eq t ht, ContinuousLinearEquiv.symm_trans_self]
    rfl

end Work.Drive.Whitney
