import Mathlib
import Submission.Work.ThomBordism.Grassmann.p1RatAux
import Submission.Work.Gen.EulerBundles
import Submission.Work.Gen.tautDual_iso_conjLine
import Submission.Work.Whitney.nonempty_bundleIso_whitneySum_comm
import Submission.Work.Thom.complexification
import Submission.Work.Thom.Iso
import Submission.Work.Thom.exists_rhoC_compat

-- Lean v4.35.0-rc3: restore v4.34 instance-unification transparency (port).
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
set_option synthInstance.maxHeartbeats 400000

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 1000000

/-!
# The explicit model of the isomorphism `zStd ⊗_ℝ ℂ ≅ O(1) ⊕ O(-1)` over `ℂP²`

This module fixes the fibre- and base-level vocabulary for
`Work.ThomBordism.Grassmann.zStd_complexification_iso`:

* `expC` — the **explicit** ℝ-linear iso `ℂ ≅ ℝ²`, `z ↦ (Re z, Im z)`;
* `expCMul c` — the conjugation `expC ∘ (c ·) ∘ expC⁻¹` on `ℝ²`;
* `cMat c` — the ℂ-linear map of `ℂ²` with matrix `[[Re c, -Im c],[Im c, Re c]]`;
* `qMat`, `qMatInv` — the change of basis diagonalising `cMat c`;
* `diagP μ ν`, `diag2 μ ν` — the diagonal scaling of the two summands of `ℂ²` in the
  presentation of the Whitney sum `Work.Whitney.sumFibreC 1 1` and in the coordinates of `ℂ²`;
* `Gm`, `GmInv` — the complexifications `cxTrans (equivC1R2 ∘ expC⁻¹)`,
  `cxTrans (expC ∘ equivC1R2⁻¹)`;
* `gaugeDiag`, `Phi`, `Phiinv` — the gauge family of the sought isomorphism
  `complexificationCore zStd ≅ O(1) ⊕ O(-1)`.
-/

open Work.TangentClasses Work.Thom

namespace Work.ThomBordism.Grassmann

noncomputable section

/-! ## 1. The explicit identification `ℂ ≅ ℝ²` -/

/-- The explicit ℝ-linear iso `ℂ¹ ≅ ℝ²`, `z ↦ (Re z, Im z)`. -/
def expLM : EuclideanSpace ℂ (Fin 1) →ₗ[ℝ] EuclideanSpace ℝ (Fin 2) where
  toFun z := WithLp.toLp 2 ![(z.ofLp 0).re, (z.ofLp 0).im]
  map_add' z w := by ext i; fin_cases i <;> simp [Complex.add_re, Complex.add_im]
  map_smul' c z := by ext i; fin_cases i <;> simp [Complex.mul_re, Complex.mul_im]

/-- The explicit ℝ-linear iso `ℂ¹ ≅ ℝ²`, `z ↦ (Re z, Im z)`. -/
noncomputable def expC : EuclideanSpace ℂ (Fin 1) ≃L[ℝ] EuclideanSpace ℝ (Fin 2) :=
  (LinearEquiv.ofBijective expLM
    ⟨fun z w h => by
      have h0 : (z.ofLp 0).re = (w.ofLp 0).re := by
        have := congrArg (fun x : EuclideanSpace ℝ (Fin 2) => x.ofLp 0) h
        simpa [expLM] using this
      have h1 : (z.ofLp 0).im = (w.ofLp 0).im := by
        have := congrArg (fun x : EuclideanSpace ℝ (Fin 2) => x.ofLp 1) h
        simpa [expLM] using this
      ext i; fin_cases i; exact Complex.ext h0 h1,
     fun x => ⟨WithLp.toLp 2 (fun _ : Fin 1 =>
        ((x.ofLp 0 : ℝ) : ℂ) + ((x.ofLp 1 : ℝ) : ℂ) * Complex.I),
      by ext i; fin_cases i <;>
        simp [expLM, Complex.add_re, Complex.add_im, Complex.mul_re, Complex.mul_im]⟩⟩).toContinuousLinearEquiv

@[simp] lemma expC_apply (z : EuclideanSpace ℂ (Fin 1)) :
    expC z = WithLp.toLp 2 ![(z.ofLp 0).re, (z.ofLp 0).im] := rfl

lemma expC_symm_ofLp (x : EuclideanSpace ℝ (Fin 2)) :
    (expC.symm x).ofLp 0 = ((x.ofLp 0 : ℝ) : ℂ) + ((x.ofLp 1 : ℝ) : ℂ) * Complex.I := by
  have hw : expC (WithLp.toLp 2 (fun _ : Fin 1 =>
      ((x.ofLp 0 : ℝ) : ℂ) + ((x.ofLp 1 : ℝ) : ℂ) * Complex.I)) = x := by
    ext i; fin_cases i <;>
      simp [expC_apply, Complex.add_re, Complex.add_im, Complex.mul_re, Complex.mul_im]
  have hsymm : expC.symm x = WithLp.toLp 2 (fun _ : Fin 1 =>
      ((x.ofLp 0 : ℝ) : ℂ) + ((x.ofLp 1 : ℝ) : ℂ) * Complex.I) := by
    rw [ContinuousLinearEquiv.symm_apply_eq]; exact hw.symm
  rw [hsymm]

/-- Multiplication by `c` on `ℂ¹`, as an ℝ-linear map. -/
def cmulLin (c : ℂ) : EuclideanSpace ℂ (Fin 1) →ₗ[ℝ] EuclideanSpace ℂ (Fin 1) where
  toFun z := c • z
  map_add' z w := smul_add c z w
  map_smul' r z := (smul_comm r c z).symm

/-- Multiplication by `c` on `ℂ¹`, as a continuous ℝ-linear map. -/
noncomputable def cmulLM (c : ℂ) : EuclideanSpace ℂ (Fin 1) →L[ℝ] EuclideanSpace ℂ (Fin 1) :=
  LinearMap.toContinuousLinearMap (cmulLin c)

@[simp] lemma cmulLM_apply (c : ℂ) (z : EuclideanSpace ℂ (Fin 1)) : cmulLM c z = c • z := rfl

/-- **The conjugation of multiplication by `c` by the explicit identification `expC`**: the
ℝ-linear endomorphism of `ℝ²` with matrix `[[Re c, -Im c],[Im c, Re c]]`. -/
noncomputable def expCMul (c : ℂ) : EuclideanSpace ℝ (Fin 2) →L[ℝ] EuclideanSpace ℝ (Fin 2) :=
  (expC : EuclideanSpace ℂ (Fin 1) →L[ℝ] EuclideanSpace ℝ (Fin 2)).comp
    ((cmulLM c).comp (expC.symm : EuclideanSpace ℝ (Fin 2) →L[ℝ] EuclideanSpace ℂ (Fin 1)))

lemma expCMul_apply (c : ℂ) (x : EuclideanSpace ℝ (Fin 2)) :
    expCMul c x = WithLp.toLp 2 ![c.re * x.ofLp 0 - c.im * x.ofLp 1,
      c.im * x.ofLp 0 + c.re * x.ofLp 1] := by
  have harg : c • ((expC.symm : EuclideanSpace ℝ (Fin 2) →L[ℝ] EuclideanSpace ℂ (Fin 1)) x) =
      WithLp.toLp 2 (fun _ : Fin 1 =>
        c * (((x.ofLp 0 : ℝ) : ℂ) + ((x.ofLp 1 : ℝ) : ℂ) * Complex.I)) := by
    ext i; fin_cases i
    simp [expC_symm_ofLp]
  simp only [expCMul, ContinuousLinearMap.comp_apply, cmulLM_apply, harg,
    ContinuousLinearEquiv.coe_coe, expC_apply]
  ext i; fin_cases i <;>
    simp [expC_symm_ofLp, Complex.mul_re, Complex.mul_im, Complex.add_re, Complex.add_im] <;> ring

@[simp] lemma expCMul_one : expCMul 1 = 1 := by
  apply ContinuousLinearMap.ext
  intro x
  rw [expCMul_apply]
  ext i; fin_cases i <;> simp

/-! ## 2. The model ℂ-linear map `cMat c` -/

/-- The ℂ-linear "quarter turn" `(v₀, v₁) ↦ (-v₁, v₀)` of `ℂ²`. -/
noncomputable def Jrot : EuclideanSpace ℂ (Fin 2) →L[ℂ] EuclideanSpace ℂ (Fin 2) :=
  Work.Gen.pair2CLM.comp ((-(Work.Gen.c1CLM)).prod Work.Gen.c0CLM)

/-- **The model ℂ-linear map with matrix `[[Re c, -Im c],[Im c, Re c]]**:
`cMat c = Re c • 1 + Im c • Jrot`. -/
noncomputable def cMat (c : ℂ) : EuclideanSpace ℂ (Fin 2) →L[ℂ] EuclideanSpace ℂ (Fin 2) :=
  (c.re : ℂ) • (1 : EuclideanSpace ℂ (Fin 2) →L[ℂ] EuclideanSpace ℂ (Fin 2)) +
    (c.im : ℂ) • Jrot

@[simp] lemma Jrot_apply (v : EuclideanSpace ℂ (Fin 2)) :
    Jrot v = Work.Gen.pair2CLM (-(Work.Gen.c1CLM v), Work.Gen.c0CLM v) := rfl

@[simp] lemma cMat_apply (c : ℂ) (v : EuclideanSpace ℂ (Fin 2)) :
    cMat c v = (c.re : ℂ) • v + (c.im : ℂ) • Jrot v := by
  simp [cMat]

lemma c0CLM_ofLp (v : EuclideanSpace ℂ (Fin 2)) : Work.Gen.c0CLM v = v.ofLp 0 := rfl

lemma c1CLM_ofLp (v : EuclideanSpace ℂ (Fin 2)) : Work.Gen.c1CLM v = v.ofLp 1 := rfl

lemma c0CLM_Jrot (v : EuclideanSpace ℂ (Fin 2)) :
    Work.Gen.c0CLM (Jrot v) = -Work.Gen.c1CLM v := by
  rw [Jrot_apply, Work.Gen.c0CLM_pair2]

lemma c1CLM_Jrot (v : EuclideanSpace ℂ (Fin 2)) :
    Work.Gen.c1CLM (Jrot v) = Work.Gen.c0CLM v := by
  rw [Jrot_apply, Work.Gen.c1CLM_pair2]

lemma Jrot_ofLp_zero (v : EuclideanSpace ℂ (Fin 2)) : (Jrot v).ofLp 0 = -(v.ofLp 1) := by
  have h : Work.Gen.c0CLM (Jrot v) = -Work.Gen.c1CLM v := c0CLM_Jrot v
  rw [c0CLM_ofLp, c1CLM_ofLp] at h
  exact h

lemma Jrot_ofLp_one (v : EuclideanSpace ℂ (Fin 2)) : (Jrot v).ofLp 1 = v.ofLp 0 := by
  have h : Work.Gen.c1CLM (Jrot v) = Work.Gen.c0CLM v := c1CLM_Jrot v
  rw [c1CLM_ofLp, c0CLM_ofLp] at h
  exact h

lemma c0CLM_cMat (c : ℂ) (v : EuclideanSpace ℂ (Fin 2)) :
    Work.Gen.c0CLM (cMat c v) =
      (c.re : ℂ) * Work.Gen.c0CLM v - (c.im : ℂ) * Work.Gen.c1CLM v := by
  rw [cMat_apply, map_add, map_smul, map_smul, c0CLM_ofLp, c0CLM_Jrot]
  ring

lemma c1CLM_cMat (c : ℂ) (v : EuclideanSpace ℂ (Fin 2)) :
    Work.Gen.c1CLM (cMat c v) =
      (c.im : ℂ) * Work.Gen.c0CLM v + (c.re : ℂ) * Work.Gen.c1CLM v := by
  rw [cMat_apply, map_add, map_smul, map_smul, c1CLM_ofLp, c1CLM_Jrot]
  ring

lemma cMat_ofLp_zero (c : ℂ) (v : EuclideanSpace ℂ (Fin 2)) :
    (cMat c v).ofLp 0 = (c.re : ℂ) * v.ofLp 0 - (c.im : ℂ) * v.ofLp 1 := by
  have h : Work.Gen.c0CLM (cMat c v) =
      (c.re : ℂ) * Work.Gen.c0CLM v - (c.im : ℂ) * Work.Gen.c1CLM v := c0CLM_cMat c v
  rw [c0CLM_ofLp, c1CLM_ofLp] at h
  exact h

lemma cMat_ofLp_one (c : ℂ) (v : EuclideanSpace ℂ (Fin 2)) :
    (cMat c v).ofLp 1 = (c.im : ℂ) * v.ofLp 0 + (c.re : ℂ) * v.ofLp 1 := by
  have h : Work.Gen.c1CLM (cMat c v) =
      (c.im : ℂ) * Work.Gen.c0CLM v + (c.re : ℂ) * Work.Gen.c1CLM v := c1CLM_cMat c v
  rw [c1CLM_ofLp, c0CLM_ofLp] at h
  exact h

lemma Jrot_comp_Jrot :
    Jrot.comp Jrot = -(1 : EuclideanSpace ℂ (Fin 2) →L[ℂ] EuclideanSpace ℂ (Fin 2)) := by
  apply ContinuousLinearMap.ext
  intro v
  ext i
  fin_cases i
  · show (Jrot (Jrot v)).ofLp (0 : Fin 2) =
      ((-1 : EuclideanSpace ℂ (Fin 2) →L[ℂ] EuclideanSpace ℂ (Fin 2)) v).ofLp 0
    rw [Jrot_ofLp_zero, Jrot_ofLp_one]
    simp
  · show (Jrot (Jrot v)).ofLp (1 : Fin 2) =
      ((-1 : EuclideanSpace ℂ (Fin 2) →L[ℂ] EuclideanSpace ℂ (Fin 2)) v).ofLp 1
    rw [Jrot_ofLp_one, Jrot_ofLp_zero]
    simp

/-- `cMat` is multiplicative. -/
lemma cMat_mul (a b : ℂ) : cMat (a * b) = (cMat a).comp (cMat b) := by
  apply ContinuousLinearMap.ext
  intro v
  ext i
  fin_cases i
  · show (cMat (a * b) v).ofLp (0 : Fin 2) = ((cMat a) ((cMat b) v)).ofLp 0
    rw [cMat_ofLp_zero, cMat_ofLp_zero, cMat_ofLp_zero, cMat_ofLp_one, Complex.mul_re,
      Complex.mul_im]
    push_cast
    ring
  · show (cMat (a * b) v).ofLp (1 : Fin 2) = ((cMat a) ((cMat b) v)).ofLp 1
    rw [cMat_ofLp_one, cMat_ofLp_one, cMat_ofLp_zero, cMat_ofLp_one, Complex.mul_re,
      Complex.mul_im]
    push_cast
    ring

@[simp] lemma cMat_zero : cMat 0 = 0 := by
  ext v i
  simp [cMat]

@[simp] lemma cMat_one : cMat 1 = 1 := by
  ext v i
  simp [cMat]

lemma continuous_cMat : Continuous (fun c : ℂ => cMat c) := by
  refine Work.Thom.continuous_clm_of_continuous_apply_gen (fun c : ℂ => cMat c) ?_
  have h1 : Continuous fun p : ℂ × EuclideanSpace ℂ (Fin 2) =>
      ((p.1.re : ℂ) • p.2 + (p.1.im : ℂ) • Jrot p.2) := by
    refine Continuous.add ?_ ?_
    · exact ((Complex.continuous_ofReal.comp Complex.continuous_re).comp continuous_fst).smul
        continuous_snd
    · exact ((Complex.continuous_ofReal.comp Complex.continuous_im).comp continuous_fst).smul
        (Jrot.continuous.comp continuous_snd)
  simpa only [cMat_apply] using h1

/-! ## 3. The diagonalising change of basis -/

/-- The change of basis `(v₀, v₁) ↦ (v₀ + v₁, i(v₁ - v₀))`, with eigenvectors `(1, ∓i)`. -/
noncomputable def qMat : EuclideanSpace ℂ (Fin 2) →L[ℂ] EuclideanSpace ℂ (Fin 2) :=
  Work.Gen.pair2CLM.comp ((Work.Gen.c0CLM + Work.Gen.c1CLM).prod
    (Complex.I • (Work.Gen.c1CLM - Work.Gen.c0CLM)))

/-- Its inverse `(v₀, v₁) ↦ ((v₀ + i v₁)/2, (v₀ - i v₁)/2)`. -/
noncomputable def qMatInv : EuclideanSpace ℂ (Fin 2) →L[ℂ] EuclideanSpace ℂ (Fin 2) :=
  Work.Gen.pair2CLM.comp
    (((2⁻¹ : ℂ) • (Work.Gen.c0CLM + Complex.I • Work.Gen.c1CLM)).prod
      ((2⁻¹ : ℂ) • (Work.Gen.c0CLM - Complex.I • Work.Gen.c1CLM)))

lemma c0CLM_qMat (v : EuclideanSpace ℂ (Fin 2)) :
    Work.Gen.c0CLM (qMat v) = Work.Gen.c0CLM v + Work.Gen.c1CLM v := by
  simp only [qMat, ContinuousLinearMap.comp_apply, Work.Gen.c0CLM_pair2,
    ContinuousLinearMap.prod_apply]
  rfl

lemma c1CLM_qMat (v : EuclideanSpace ℂ (Fin 2)) :
    Work.Gen.c1CLM (qMat v) = Complex.I * (Work.Gen.c1CLM v - Work.Gen.c0CLM v) := by
  simp only [qMat, ContinuousLinearMap.comp_apply, Work.Gen.c1CLM_pair2,
    ContinuousLinearMap.prod_apply, ContinuousLinearMap.smul_apply]
  rfl

lemma c0CLM_qMatInv (v : EuclideanSpace ℂ (Fin 2)) :
    Work.Gen.c0CLM (qMatInv v) =
      2⁻¹ * (Work.Gen.c0CLM v + Complex.I * Work.Gen.c1CLM v) := by
  simp only [qMatInv, ContinuousLinearMap.comp_apply, Work.Gen.c0CLM_pair2,
    ContinuousLinearMap.prod_apply, ContinuousLinearMap.smul_apply, smul_eq_mul]
  rfl

lemma c1CLM_qMatInv (v : EuclideanSpace ℂ (Fin 2)) :
    Work.Gen.c1CLM (qMatInv v) =
      2⁻¹ * (Work.Gen.c0CLM v - Complex.I * Work.Gen.c1CLM v) := by
  simp only [qMatInv, ContinuousLinearMap.comp_apply, Work.Gen.c1CLM_pair2,
    ContinuousLinearMap.prod_apply, ContinuousLinearMap.smul_apply, smul_eq_mul]
  rfl

lemma qMat_ofLp_zero (v : EuclideanSpace ℂ (Fin 2)) :
    (qMat v).ofLp 0 = v.ofLp 0 + v.ofLp 1 := by
  have h : Work.Gen.c0CLM (qMat v) = Work.Gen.c0CLM v + Work.Gen.c1CLM v := c0CLM_qMat v
  rw [c0CLM_ofLp, c1CLM_ofLp] at h
  exact h

lemma qMat_ofLp_one (v : EuclideanSpace ℂ (Fin 2)) :
    (qMat v).ofLp 1 = Complex.I * (v.ofLp 1 - v.ofLp 0) := by
  have h : Work.Gen.c1CLM (qMat v) = Complex.I * (Work.Gen.c1CLM v - Work.Gen.c0CLM v) :=
    c1CLM_qMat v
  rw [c1CLM_ofLp, c0CLM_ofLp] at h
  exact h

lemma qMatInv_ofLp_zero (v : EuclideanSpace ℂ (Fin 2)) :
    (qMatInv v).ofLp 0 = 2⁻¹ * (v.ofLp 0 + Complex.I * v.ofLp 1) := by
  have h : Work.Gen.c0CLM (qMatInv v) =
      2⁻¹ * (Work.Gen.c0CLM v + Complex.I * Work.Gen.c1CLM v) := c0CLM_qMatInv v
  rw [c0CLM_ofLp, c1CLM_ofLp] at h
  exact h

lemma qMatInv_ofLp_one (v : EuclideanSpace ℂ (Fin 2)) :
    (qMatInv v).ofLp 1 = 2⁻¹ * (v.ofLp 0 - Complex.I * v.ofLp 1) := by
  have h : Work.Gen.c1CLM (qMatInv v) =
      2⁻¹ * (Work.Gen.c0CLM v - Complex.I * Work.Gen.c1CLM v) := c1CLM_qMatInv v
  rw [c1CLM_ofLp, c0CLM_ofLp] at h
  exact h

/-- **The diagonal scaling of the two summands of `ℂ²`** as presented by the Whitney sum
splitting `Work.Whitney.sumFibreC 1 1`. -/
noncomputable def diagP (μ ν : ℂ) : EuclideanSpace ℂ (Fin 2) →L[ℂ] EuclideanSpace ℂ (Fin 2) :=
  ((Work.Whitney.sumFibreC 1 1 : (EuclideanSpace ℂ (Fin 1) × EuclideanSpace ℂ (Fin 1)) →L[ℂ]
      EuclideanSpace ℂ (Fin 2)).comp
    (((μ • (1 : EuclideanSpace ℂ (Fin 1) →L[ℂ] EuclideanSpace ℂ (Fin 1))).prodMap
      (ν • (1 : EuclideanSpace ℂ (Fin 1) →L[ℂ] EuclideanSpace ℂ (Fin 1)))).comp
      ((Work.Whitney.sumFibreC 1 1).symm : EuclideanSpace ℂ (Fin 2) →L[ℂ]
        (EuclideanSpace ℂ (Fin 1) × EuclideanSpace ℂ (Fin 1)))))

/-- The same diagonal scaling in the *coordinates* of `ℂ²`. -/
noncomputable def diag2 (μ ν : ℂ) : EuclideanSpace ℂ (Fin 2) →L[ℂ] EuclideanSpace ℂ (Fin 2) :=
  Work.Gen.pair2CLM.comp ((μ • Work.Gen.c0CLM).prod (ν • Work.Gen.c1CLM))

lemma c0CLM_diag2 (μ ν : ℂ) (v : EuclideanSpace ℂ (Fin 2)) :
    Work.Gen.c0CLM (diag2 μ ν v) = μ * Work.Gen.c0CLM v := by
  simp only [diag2, ContinuousLinearMap.comp_apply, Work.Gen.c0CLM_pair2,
    ContinuousLinearMap.prod_apply, ContinuousLinearMap.smul_apply, smul_eq_mul]

lemma c1CLM_diag2 (μ ν : ℂ) (v : EuclideanSpace ℂ (Fin 2)) :
    Work.Gen.c1CLM (diag2 μ ν v) = ν * Work.Gen.c1CLM v := by
  simp only [diag2, ContinuousLinearMap.comp_apply, Work.Gen.c1CLM_pair2,
    ContinuousLinearMap.prod_apply, ContinuousLinearMap.smul_apply, smul_eq_mul]

lemma diag2_ofLp_zero (μ ν : ℂ) (v : EuclideanSpace ℂ (Fin 2)) :
    (diag2 μ ν v).ofLp 0 = μ * v.ofLp 0 := by
  have h : Work.Gen.c0CLM (diag2 μ ν v) = μ * Work.Gen.c0CLM v := c0CLM_diag2 μ ν v
  rw [c0CLM_ofLp] at h
  exact h

lemma diag2_ofLp_one (μ ν : ℂ) (v : EuclideanSpace ℂ (Fin 2)) :
    (diag2 μ ν v).ofLp 1 = ν * v.ofLp 1 := by
  have h : Work.Gen.c1CLM (diag2 μ ν v) = ν * Work.Gen.c1CLM v := c1CLM_diag2 μ ν v
  rw [c1CLM_ofLp] at h
  exact h

/-! ## 4. The complexifications `Gm`, `GmInv` -/

/-- `cxTrans (equivC1R2 ∘ expC⁻¹)`: the complexified comparison of the abstract identification
`equivC1R2` of `zStd` with the explicit one `expC`. -/
noncomputable def Gm : EuclideanSpace ℂ (Fin 2) →L[ℂ] EuclideanSpace ℂ (Fin 2) :=
  cxTrans ((equivC1R2 : EuclideanSpace ℂ (Fin 1) →L[ℝ] EuclideanSpace ℝ (Fin 2)).comp
    (expC.symm : EuclideanSpace ℝ (Fin 2) →L[ℝ] EuclideanSpace ℂ (Fin 1)))

/-- Its inverse `cxTrans (expC ∘ equivC1R2⁻¹)`. -/
noncomputable def GmInv : EuclideanSpace ℂ (Fin 2) →L[ℂ] EuclideanSpace ℂ (Fin 2) :=
  cxTrans ((expC : EuclideanSpace ℂ (Fin 1) →L[ℝ] EuclideanSpace ℝ (Fin 2)).comp
    (equivC1R2.symm : EuclideanSpace ℝ (Fin 2) →L[ℝ] EuclideanSpace ℂ (Fin 1)))

/-! ## 5. The gauge of the isomorphism -/

/-- The diagonal-reference gauge in the source chart `i`. -/
noncomputable def gaugeDiag (i : Fin 3) (b : Work.Projective.CP 2) :
    EuclideanSpace ℂ (Fin 2) →L[ℂ] EuclideanSpace ℂ (Fin 2) :=
  (diagP 1 (((Work.Gen.gaugeFun 2 i b : ℝ) : ℂ)⁻¹)).comp qMatInv

/-- Its inverse. -/
noncomputable def gaugeDiagInv (i : Fin 3) (b : Work.Projective.CP 2) :
    EuclideanSpace ℂ (Fin 2) →L[ℂ] EuclideanSpace ℂ (Fin 2) :=
  qMat.comp (diagP 1 (((Work.Gen.gaugeFun 2 i b : ℝ) : ℂ)))

/-- The forward gauge family, in the source chart `i` and the target chart `t`. -/
noncomputable def Phi (i : Fin 3) (t : Fin 3 × Fin 3) (b : Work.Projective.CP 2) :
    EuclideanSpace ℂ (Fin 2) →L[ℂ] EuclideanSpace ℂ (Fin 2) :=
  ((Work.Whitney.whitneySum (Work.Gen.tautDual 2) (Work.Gen.tautLine 2)).coordChange
      (i, i) t b).comp ((gaugeDiag i b).comp GmInv)

/-- The inverse gauge family. -/
noncomputable def Phiinv (i : Fin 3) (t : Fin 3 × Fin 3) (b : Work.Projective.CP 2) :
    EuclideanSpace ℂ (Fin 2) →L[ℂ] EuclideanSpace ℂ (Fin 2) :=
  (Gm.comp (gaugeDiagInv i b)).comp
    ((Work.Whitney.whitneySum (Work.Gen.tautDual 2) (Work.Gen.tautLine 2)).coordChange
      t (i, i) b)

end

end Work.ThomBordism.Grassmann
