import Mathlib
import Submission.Work.KT.D2.PAMDefs
-- TEMPORARY: the child module is being edited
-- import Submission.Work.KT.D2.PAMHopfAlg
import Submission.Work.KT.D2.PAMSphCoords
import Submission.Work.KT.D2.PAMSphCoordPos
import Submission.Work.KT.D2.PAMCentre
import Submission.Work.KT.D2.PAMCentreSmall
import Submission.Work.KT.D2.PAMCentreGap
-- import Submission.Work.KT.D2.PAMInnerLoop
-- import Submission.Work.KT.D2.LoopTools
import Submission.Work.KT.D2.PAMSphCoordPos
import Submission.Work.KT.D2.TrigAux
import Submission.Work.KT.Dim2.circle_log_facts

/-!
# The disc-model Hopf clutching function is not null-homotopic

Let `u : D² → M₂(ℂ)` be continuous with unit values and `u y * e₀ = PAM(y) * u y`, and let
`f : S¹ → ℂˣ` be the boundary loop `x ↦ (u (inBall x)) 0 0`.  Then `f` is not null-homotopic.
-/

namespace Work.KT.D2

open Matrix

set_option maxHeartbeats 1000000
set_option synthInstance.maxHeartbeats 400000

noncomputable section

/-! ## TEMPORARY stand-in for `PAMHopfAlg` while the delegated module is being proved -/

lemma PyA_e00 (y : Dc) :
    PyA y 0 0 = (1 / 2 : ℂ) * (1 + (sphCoordR y : ℂ)) := by
  simp only [PyA, Matrix.map_apply, PAMA, Matrix.of_apply, Matrix.cons_val',
    Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.cons_val_fin_one, Matrix.head_cons,
    Matrix.empty_val', Matrix.zero_apply]
  simp only [map_mul, map_add, map_one, AlgHom.commutes, X2A, augPair_PsiA, scRA, mcRA,
    sphCoordR]
  rfl

lemma PyA_e01 (y : Dc) :
    PyA y 0 1 = (1 / 2 : ℂ) * ((sphCoord 0 y : ℂ) - Complex.I * (sphCoord 1 y : ℂ)) := by
  simp only [PyA, Matrix.map_apply, PAMA, Matrix.of_apply, Matrix.cons_val',
    Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.cons_val_fin_one, Matrix.head_cons,
    Matrix.empty_val', Matrix.zero_apply]
  simp only [map_mul, map_sub, map_add, map_one, AlgHom.commutes, X0A, X1A, augPair_PsiA,
    scEA, mcEA, sphCoord]
  rfl

lemma PyA_e10 (y : Dc) :
    PyA y 1 0 = (1 / 2 : ℂ) * ((sphCoord 0 y : ℂ) + Complex.I * (sphCoord 1 y : ℂ)) := by
  simp only [PyA, Matrix.map_apply, PAMA, Matrix.of_apply, Matrix.cons_val',
    Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.cons_val_fin_one, Matrix.head_cons,
    Matrix.empty_val', Matrix.zero_apply]
  simp only [map_mul, map_sub, map_add, map_one, AlgHom.commutes, X0A, X1A, augPair_PsiA,
    scEA, mcEA, sphCoord]
  rfl

lemma PyA_e11 (y : Dc) :
    PyA y 1 1 = (1 / 2 : ℂ) * (1 - (sphCoordR y : ℂ)) := by
  simp only [PyA, Matrix.map_apply, PAMA, Matrix.of_apply, Matrix.cons_val',
    Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.cons_val_fin_one, Matrix.head_cons,
    Matrix.empty_val', Matrix.zero_apply]
  simp only [map_mul, map_sub, map_add, map_one, AlgHom.commutes, X2A, augPair_PsiA, scRA,
    mcRA, sphCoordR]
  rfl

/-- The sphere relation, in `ℂ`. -/
lemma sphCoord_sq_C (y : Dc) :
    ((sphCoord 0 y : ℂ)) ^ 2 + ((sphCoord 1 y : ℂ)) ^ 2 = 1 - ((sphCoordR y : ℂ)) ^ 2 := by
  have hs := sphCoord_sq y
  have h : ((sphCoord 0 y : ℝ)) ^ 2 + ((sphCoord 1 y : ℝ)) ^ 2
      = 1 - ((sphCoordR y : ℝ)) ^ 2 := by linarith [hs]
  exact_mod_cast h

lemma mul_I_sub_add (a b : ℝ) :
    ((a : ℂ) - Complex.I * (b : ℂ)) * ((a : ℂ) + Complex.I * (b : ℂ))
      = ((a : ℂ) ^ 2) + (b : ℂ) ^ 2 := by
  apply Complex.ext <;>
    simp only [Complex.mul_re, Complex.mul_im, Complex.sub_re, Complex.sub_im, Complex.add_re,
      Complex.add_im, Complex.ofReal_re, Complex.ofReal_im, Complex.I_re, Complex.I_im,
      pow_two] <;> ring

lemma star_add_I (a b : ℝ) :
    star ((a : ℂ) + Complex.I * (b : ℂ)) = (a : ℂ) - Complex.I * (b : ℂ) := by
  apply Complex.ext <;>
    simp only [Complex.star_def, Complex.conj_re, Complex.conj_im, Complex.add_re,
      Complex.add_im, Complex.ofReal_re, Complex.ofReal_im, Complex.I_re, Complex.I_im,
      Complex.sub_re, Complex.sub_im, Complex.mul_re, Complex.mul_im] <;>
    norm_num <;> ring

lemma star_half_one_add (r : ℝ) :
    star ((1 / 2 : ℂ) * (1 + (r : ℂ))) = (1 / 2 : ℂ) * (1 + (r : ℂ)) := by
  apply Complex.ext <;>
    simp only [Complex.star_def, Complex.conj_re, Complex.conj_im, Complex.mul_re,
      Complex.mul_im, Complex.add_re, Complex.add_im, Complex.one_re, Complex.one_im,
      Complex.ofReal_re, Complex.ofReal_im] <;>
    norm_num <;> ring

lemma star_half_one_sub (r : ℝ) :
    star ((1 / 2 : ℂ) * (1 - (r : ℂ))) = (1 / 2 : ℂ) * (1 - (r : ℂ)) := by
  apply Complex.ext <;>
    simp only [Complex.star_def, Complex.conj_re, Complex.conj_im, Complex.mul_re,
      Complex.mul_im, Complex.sub_re, Complex.sub_im, Complex.one_re, Complex.one_im,
      Complex.ofReal_re, Complex.ofReal_im] <;>
    norm_num <;> ring

lemma star_half_sub_I (a b : ℝ) :
    star ((1 / 2 : ℂ) * ((a : ℂ) - Complex.I * (b : ℂ)))
      = (1 / 2 : ℂ) * ((a : ℂ) + Complex.I * (b : ℂ)) := by
  apply Complex.ext <;>
    simp only [Complex.star_def, Complex.conj_re, Complex.conj_im, Complex.mul_re,
      Complex.mul_im, Complex.sub_re, Complex.sub_im, Complex.add_re, Complex.add_im,
      Complex.ofReal_re, Complex.ofReal_im, Complex.I_re, Complex.I_im] <;>
    norm_num <;> ring

lemma star_half_add_I (a b : ℝ) :
    star ((1 / 2 : ℂ) * ((a : ℂ) + Complex.I * (b : ℂ)))
      = (1 / 2 : ℂ) * ((a : ℂ) - Complex.I * (b : ℂ)) := by
  apply Complex.ext <;>
    simp only [Complex.star_def, Complex.conj_re, Complex.conj_im, Complex.mul_re,
      Complex.mul_im, Complex.sub_re, Complex.sub_im, Complex.add_re, Complex.add_im,
      Complex.ofReal_re, Complex.ofReal_im, Complex.I_re, Complex.I_im] <;>
    norm_num <;> ring

lemma hopfU_e00 (y : Dc) : hopfU y 0 0 = (hv1 y : ℂ) := by simp [hopfU]
lemma hopfU_e01 (y : Dc) : hopfU y 0 1 = -star (hv2 y) := by simp [hopfU]
lemma hopfU_e10 (y : Dc) : hopfU y 1 0 = hv2 y := by simp [hopfU]
lemma hopfU_e11 (y : Dc) : hopfU y 1 1 = star (hv1 y : ℂ) := by simp [hopfU]
lemma e0_e00 : e0 0 0 = (1 : ℂ) := by simp [e0]
lemma e0_e01 : e0 0 1 = (0 : ℂ) := by simp [e0]
lemma e0_e10 : e0 1 0 = (0 : ℂ) := by simp [e0]
lemma e0_e11 : e0 1 1 = (0 : ℂ) := by simp [e0]

/-- The evaluated Hopf idempotent is Hermitian. -/
lemma PyA_herm_tmp (y : Dc) : Matrix.conjTranspose (PyA y) = PyA y := by
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp only [Matrix.conjTranspose_apply, PyA_e00, PyA_e01, PyA_e10, PyA_e11]
  · exact star_half_one_add (sphCoordR y)
  · exact star_half_add_I (sphCoord 0 y) (sphCoord 1 y)
  · exact star_half_sub_I (sphCoord 0 y) (sphCoord 1 y)
  · exact star_half_one_sub (sphCoordR y)

lemma star_hv1 (y : Dc) : star ((hv1 y : ℂ)) = (hv1 y : ℂ) := by
  rw [show (hv1 y : ℂ) = ((hv1 y : ℝ) : ℂ) from rfl, Complex.star_def]
  exact Complex.conj_ofReal (hv1 y)

lemma star_hv2 (y : Dc) :
    star (hv2 y) = ((sphCoord 0 y : ℂ) - Complex.I * (sphCoord 1 y : ℂ)) := by
  rw [hv2]
  exact star_add_I (sphCoord 0 y) (sphCoord 1 y)

/-! ## Homotopies of loops in `ℂˣ` on `S¹ ⊂ ℝ²` -/

/-- A continuous nowhere-vanishing family `e : [0,1] × S¹ → ℂ` defines a homotopy between the
loops obtained by evaluating its endpoints. -/
lemma pam_family_homotopic (e : unitInterval × Sc → ℂ) (he : Continuous e)
    (hne : ∀ p, e p ≠ 0) {g₀ g₁ : C(Sc, ℂˣ)}
    (h₀ : ∀ x, (g₀ x : ℂ) = e (0, x)) (h₁ : ∀ x, (g₁ x : ℂ) = e (1, x)) :
    ContinuousMap.Homotopic g₀ g₁ := by
  refine ⟨ContinuousMap.Homotopy.mk
    ⟨fun p => Units.mk0 (e p) (hne p), continuous_units_mk0 he hne⟩ ?_ ?_⟩
  · intro x
    exact Units.ext (h₀ x).symm
  · intro x
    exact Units.ext (h₁ x).symm

/-- The pointwise product of homotopic loops is homotopic. -/
lemma pam_mul_homotopic {f₀ f₁ g₀ g₁ : C(Sc, ℂˣ)}
    (hf : ContinuousMap.Homotopic f₀ f₁) (hg : ContinuousMap.Homotopic g₀ g₁) :
    ContinuousMap.Homotopic (f₀ * g₀) (f₁ * g₁) := by
  obtain ⟨F⟩ := hf
  obtain ⟨G⟩ := hg
  refine ⟨ContinuousMap.Homotopy.mk (F.toContinuousMap * G.toContinuousMap) ?_ ?_⟩
  · intro x
    change (F.toContinuousMap : C(unitInterval × Sc, ℂˣ)) (0, x) * G.toContinuousMap (0, x)
      = f₀ x * g₀ x
    rw [show F.toContinuousMap (0, x) = f₀ x from F.map_zero_left x,
      show G.toContinuousMap (0, x) = g₀ x from G.map_zero_left x]
  · intro x
    change (F.toContinuousMap : C(unitInterval × Sc, ℂˣ)) (1, x) * G.toContinuousMap (1, x)
      = f₁ x * g₁ x
    rw [show F.toContinuousMap (1, x) = f₁ x from F.map_one_left x,
      show G.toContinuousMap (1, x) = g₁ x from G.map_one_left x]

/-- Any two constant loops in `ℂˣ` are homotopic. -/
lemma pam_const_homotopic (c d : ℂˣ) :
    ContinuousMap.Homotopic (ContinuousMap.const Sc c) (ContinuousMap.const Sc d) := by
  have γ : Path c d := PathConnectedSpace.somePath c d
  refine ⟨ContinuousMap.Homotopy.mk
    ⟨fun p : unitInterval × Sc => γ p.1,
      γ.toContinuousMap.continuous.comp continuous_fst⟩ ?_ ?_⟩
  · intro x
    exact γ.source'
  · intro x
    exact γ.target'
lemma mul_add_I_sub_I (a b : ℝ) :
    ((a : ℂ) + Complex.I * (b : ℂ)) * ((a : ℂ) - Complex.I * (b : ℂ))
      = ((a : ℂ) ^ 2) + (b : ℂ) ^ 2 := by
  rw [mul_comm ((a : ℂ) + Complex.I * (b : ℂ)) ((a : ℂ) - Complex.I * (b : ℂ))]
  exact mul_I_sub_add a b

lemma hopfU_rel_tmp (y : Dc) : hopfU y * e0 = PyA y * hopfU y := by
  have hrel := sphCoord_sq_C y
  have hI := mul_I_sub_add (sphCoord 0 y) (sphCoord 1 y)
  have hI' := mul_add_I_sub_I (sphCoord 0 y) (sphCoord 1 y)
  have hs1 := star_hv1 y
  have hs2 := star_hv2 y
  ext i j
  fin_cases i <;> fin_cases j
  · rw [Matrix.mul_apply, Matrix.mul_apply, Fin.sum_univ_two, Fin.sum_univ_two]
    show hopfU y 0 0 * e0 0 0 + hopfU y 0 1 * e0 1 0
      = PyA y 0 0 * hopfU y 0 0 + PyA y 0 1 * hopfU y 1 0
    rw [hopfU_e00 y, hopfU_e10 y, e0_e00, e0_e10, PyA_e00 y, PyA_e01 y]
    simp only [hv1, hv2, mul_assoc]
    simp only [hI, hrel]
    push_cast
    ring
  · rw [Matrix.mul_apply, Matrix.mul_apply, Fin.sum_univ_two, Fin.sum_univ_two]
    show hopfU y 0 0 * e0 0 1 + hopfU y 0 1 * e0 1 1
      = PyA y 0 0 * hopfU y 0 1 + PyA y 0 1 * hopfU y 1 1
    rw [hopfU_e00 y, hopfU_e01 y, hopfU_e11 y, e0_e01, e0_e11, hs1, hs2,
      PyA_e00 y, PyA_e01 y]
    simp only [hv1, hv2]
    push_cast
    ring
  · rw [Matrix.mul_apply, Matrix.mul_apply, Fin.sum_univ_two, Fin.sum_univ_two]
    show hopfU y 1 0 * e0 0 0 + hopfU y 1 1 * e0 1 0
      = PyA y 1 0 * hopfU y 0 0 + PyA y 1 1 * hopfU y 1 0
    rw [hopfU_e00 y, hopfU_e10 y, hopfU_e11 y, e0_e00, e0_e10, hs1,
      PyA_e10 y, PyA_e11 y]
    simp only [hv1, hv2]
    push_cast
    ring
  · rw [Matrix.mul_apply, Matrix.mul_apply, Fin.sum_univ_two, Fin.sum_univ_two]
    show hopfU y 1 0 * e0 0 1 + hopfU y 1 1 * e0 1 1
      = PyA y 1 0 * hopfU y 0 1 + PyA y 1 1 * hopfU y 1 1
    rw [hopfU_e01 y, hopfU_e10 y, hopfU_e11 y, e0_e01, e0_e11, hs1, hs2,
      PyA_e10 y, PyA_e11 y]
    simp only [hv1, hv2, mul_assoc, mul_neg]
    simp only [hI', hrel]
    push_cast
    ring

lemma hopfU_det_tmp (y : Dc) : Matrix.det (hopfU y) = ((hvN2 y : ℝ) : ℂ) := by
  have hrel : ((sphCoord 0 y : ℂ)) ^ 2 + ((sphCoord 1 y : ℂ)) ^ 2
      = 1 - ((sphCoordR y : ℂ)) ^ 2 := sphCoord_sq_C y
  have hI := mul_I_sub_add (sphCoord 0 y) (sphCoord 1 y)
  have hs1 := star_hv1 y
  have hs2 := star_hv2 y
  rw [Matrix.det_fin_two, hopfU_e00 y, hopfU_e01 y, hopfU_e10 y, hopfU_e11 y, hs1, hs2]
  simp only [hv2, hvN2_eq, hv1, neg_mul, mul_assoc]
  simp only [hI, hrel]
  push_cast
  ring

/-! ## The clutching family is block diagonal and invertible off the centre -/

/-- `diag(1,0)` is self-adjoint. -/
lemma e0_conjTranspose : Matrix.conjTranspose e0 = e0 := by
  ext i j
  fin_cases i <;> fin_cases j <;> simp [e0, Matrix.conjTranspose_apply]

/-- The off-diagonal entries of a matrix commuting with `e0` vanish. -/
lemma offdiag_of_comm_e0 {A : Matrix (Fin 2) (Fin 2) ℂ} (h : A * e0 = e0 * A) :
    A 0 1 = 0 ∧ A 1 0 = 0 := by
  constructor
  · have h' := congrArg (fun M : Matrix (Fin 2) (Fin 2) ℂ => M 0 1) h
    have h2 : (0 : ℂ) = A 0 1 := by
      simpa [e0, Matrix.mul_apply, Fin.sum_univ_two] using h'
    exact h2.symm
  · have h' := congrArg (fun M : Matrix (Fin 2) (Fin 2) ℂ => M 1 0) h
    have h2 : A 1 0 = 0 := by
      simpa [e0, Matrix.mul_apply, Fin.sum_univ_two] using h'
    exact h2

/-- The clutching family `Cm u` is block diagonal. -/
lemma Cm_comm (u : C(Dc, Matrix (Fin 2) (Fin 2) ℂ))
    (hconj : ∀ y, u y * e0 = PyA y * u y) (y : Dc) : Cm u y * e0 = e0 * Cm u y := by
  have hU : hopfU y * e0 = PyA y * hopfU y := hopfU_rel_tmp y
  have hA : Matrix.conjTranspose (PyA y) = PyA y := PyA_herm_tmp y
  have h1 : Matrix.conjTranspose (hopfU y) * PyA y = e0 * Matrix.conjTranspose (hopfU y) := by
    have h := congrArg Matrix.conjTranspose hU
    rw [Matrix.conjTranspose_mul, Matrix.conjTranspose_mul, hA, e0_conjTranspose] at h
    exact h.symm
  calc Cm u y * e0
      = ((hvN2 y : ℂ))⁻¹ • (Matrix.conjTranspose (hopfU y) * (u y * e0)) := by
        simp only [Cm, Matrix.smul_mul, Matrix.mul_assoc]
    _ = ((hvN2 y : ℂ))⁻¹ • (Matrix.conjTranspose (hopfU y) * (PyA y * u y)) := by
        rw [hconj y]
    _ = ((hvN2 y : ℂ))⁻¹ • ((e0 * Matrix.conjTranspose (hopfU y)) * u y) := by
        rw [← Matrix.mul_assoc, h1, Matrix.mul_assoc]
    _ = e0 * Cm u y := by
        simp only [Cm, Matrix.mul_smul, Matrix.mul_assoc]

/-- The determinant of the clutching family does not vanish off the centre. -/
lemma Cm_det_ne_zero (u : C(Dc, Matrix (Fin 2) (Fin 2) ℂ)) (hunit : ∀ y, IsUnit (u y))
    (hconj : ∀ y, u y * e0 = PyA y * u y) {y : Dc} (hy : y ≠ dctr) :
    (Cm u y).det ≠ 0 := by
  have hc : ((hvN2 y : ℂ)) ≠ 0 := by
    exact_mod_cast ne_of_gt (PAMSphCoordPos y hy).2
  have hCm : Cm u y = (((hvN2 y : ℂ))⁻¹ • Matrix.conjTranspose (hopfU y)) * u y := by
    rw [Cm, Matrix.smul_mul]
  rw [hCm, Matrix.det_mul]
  refine mul_ne_zero ?_ ?_
  · rw [Matrix.det_smul, Matrix.det_conjTranspose, hopfU_det_tmp y]
    simp only [Fintype.card_fin]
    refine mul_ne_zero (pow_ne_zero 2 (inv_ne_zero hc)) ?_
    rwa [star_ne_zero]
  · rw [← isUnit_iff_ne_zero, ← Matrix.isUnit_iff_isUnit_det]
    exact hunit y

/-- The `(0,0)`-entry of the clutching family does not vanish off the centre. -/
lemma Cm_00_ne_zero (u : C(Dc, Matrix (Fin 2) (Fin 2) ℂ)) (hunit : ∀ y, IsUnit (u y))
    (hconj : ∀ y, u y * e0 = PyA y * u y) {y : Dc} (hy : y ≠ dctr) :
    (Cm u y) 0 0 ≠ 0 := by
  obtain ⟨h01, h10⟩ := offdiag_of_comm_e0 (Cm_comm u hconj y)
  have hdet : (Cm u y).det = (Cm u y) 0 0 * (Cm u y) 1 1 := by
    rw [Matrix.det_fin_two, h01, h10]; ring
  intro h00
  have hne := Cm_det_ne_zero u hunit hconj hy
  rw [hdet, h00, zero_mul] at hne
  exact hne rfl

/-- The matrix `hopfU` is continuous. -/
lemma continuous_hopfU : Continuous hopfU := by
  refine continuous_matrix fun i j => ?_
  fin_cases i <;> fin_cases j <;>
    simp only [hopfU, Matrix.of_apply, Matrix.cons_val', Matrix.cons_val_zero,
      Matrix.cons_val_one, Matrix.cons_val_fin_one, Matrix.head_cons, Matrix.empty_val',
      Matrix.zero_apply]
  · exact Complex.continuous_ofReal.comp continuous_hv1
  · exact ((continuous_star : Continuous (star : ℂ → ℂ)).comp continuous_hv2).neg
  · exact continuous_hv2
  · exact (continuous_star : Continuous (star : ℂ → ℂ)).comp
      (Complex.continuous_ofReal.comp continuous_hv1)

/-- The clutching family is continuous off the centre. -/
lemma continuousAt_Cm (u : C(Dc, Matrix (Fin 2) (Fin 2) ℂ)) (y : Dc) (hy : y ≠ dctr) :
    ContinuousAt (Cm u) y := by
  have hc : ((hvN2 y : ℂ)) ≠ 0 := by
    exact_mod_cast ne_of_gt (PAMSphCoordPos y hy).2
  have h1 : ContinuousAt (fun z : Dc => ((hvN2 z : ℂ))⁻¹) y :=
    ContinuousAt.inv₀ (Complex.continuous_ofReal.comp continuous_hvN2).continuousAt hc
  have h2 : ContinuousAt (fun z : Dc => Matrix.conjTranspose (hopfU z) * u z) y :=
    ContinuousAt.mul (Continuous.matrix_conjTranspose continuous_hopfU).continuousAt
      u.continuous.continuousAt
  exact h1.smul h2

/-! ## The boundary value of the clutching family -/

/-- The norm of the radial point `r • x` is `r`. -/
lemma norm_radCM (r : unitInterval) (x : Sc) : ‖((radCM r x : Dc) : E2)‖ = (r : ℝ) := by
  rw [radCM_coe, norm_smul, Real.norm_eq_abs, abs_of_nonneg r.2.1, norm_coe_sphere, mul_one]

/-- On the boundary circle the `(0,0)`-entry of the clutching family is half the `(0,0)`-entry
of `u`: the Hopf vector there is `(2,0)`, so `hvN2 = 4` and `hv1 = 2`. -/
lemma Cm_boundary (u : C(Dc, Matrix (Fin 2) (Fin 2) ℂ)) (x : Sc) :
    (Cm u (inBallA x)) 0 0 = (1 / 2 : ℂ) * (u (inBallA x)) 0 0 := by
  obtain ⟨hR, h0, h1⟩ := PAMSphCoords.2.2 x
  have hv1b : hv1 (inBallA x) = 2 := by rw [hv1, hR]; norm_num
  have hv2b : hv2 (inBallA x) = 0 := by simp [hv2, h0, h1]
  have hNb : hvN2 (inBallA x) = 4 := by rw [hvN2_eq, hv1b]; norm_num
  rw [Cm_00, hv1b, hv2b, hNb, star_zero, zero_mul, add_zero]
  have hnum : (((4 : ℝ)) : ℂ)⁻¹ * (((2 : ℝ)) : ℂ) = 1 / 2 := by norm_num
  rw [← mul_assoc, hnum]

/-! ## The conjugate direction loop `x ↦ x₀ - i x₁` -/

/-- The conjugate direction `x₀ - i x₁` of a point `x` of the circle. -/
def xiC (x : Sc) : ℂ := ((x : E2) 0 : ℂ) - Complex.I * ((x : E2) 1 : ℂ)

lemma norm_xiC (x : Sc) : ‖xiC x‖ = 1 := by
  have hx : ‖(x : E2)‖ = 1 := norm_coe_sphere x
  have h2 : ((x : E2) 0) ^ 2 + ((x : E2) 1) ^ 2 = 1 := by
    have h : ‖(x : E2)‖ ^ 2 = ((x : E2) 0) ^ 2 + ((x : E2) 1) ^ 2 := by
      rw [PiLp.norm_sq_eq_of_L2, Fin.sum_univ_two]
      simp [Real.norm_eq_abs, sq_abs]
    rw [hx, one_pow] at h
    exact h.symm
  have hrew : xiC x = (((x : E2) 0 : ℝ) : ℂ) + (((-(x : E2) 1) : ℝ)) * Complex.I := by
    simp only [xiC]
    push_cast
    ring
  have h3 : Complex.normSq (xiC x) = ((x : E2) 0) ^ 2 + ((x : E2) 1) ^ 2 := by
    rw [hrew, Complex.normSq_add_mul_I]
    ring
  have h4 : ‖xiC x‖ ^ 2 = 1 := by
    rw [← Complex.normSq_eq_norm_sq, h3, h2]
  nlinarith [norm_nonneg (xiC x)]

lemma xiC_ne_zero (x : Sc) : xiC x ≠ 0 := by
  intro h
  have h1 := norm_xiC x
  rw [h, norm_zero] at h1
  exact one_ne_zero h1.symm

lemma continuous_xiC : Continuous xiC := by
  have h0 : Continuous fun x : Sc => Complex.ofReal ((x : E2) 0) :=
    Complex.continuous_ofReal.comp
      ((EuclideanSpace.proj (0 : Fin 2)).continuous.comp continuous_subtype_val)
  have h1 : Continuous fun x : Sc => Complex.I * Complex.ofReal ((x : E2) 1) :=
    continuous_const.mul (Complex.continuous_ofReal.comp
      ((EuclideanSpace.proj (1 : Fin 2)).continuous.comp continuous_subtype_val))
  refine (h0.sub h1).congr ?_
  intro x
  simp [xiC]

/-- The loop `x ↦ x₀ - i x₁` in `ℂˣ`. -/
def loopA : C(Sc, ℂˣ) :=
  ⟨fun x => Units.mk0 (xiC x) (xiC_ne_zero x), continuous_units_mk0 continuous_xiC xiC_ne_zero⟩

@[simp] lemma loopA_coe (x : Sc) : ((loopA x : ℂˣ) : ℂ) = xiC x := rfl

/-! ## The map `S¹ ⊂ ℂ → S¹ ⊂ ℝ²` -/

/-- The continuous map `S¹ ⊂ ℂ → S¹ ⊂ ℝ²`, `z ↦ (re z, im z)`. -/
def circToSph : C(Circ, Sc) where
  toFun z := ⟨WithLp.toLp 2 (fun i : Fin 2 => if i = 0 then (z : ℂ).re else (z : ℂ).im), by
    have hz : ‖(z : ℂ)‖ = 1 := by
      have h := Metric.mem_sphere.mp z.2
      rwa [dist_eq_norm, sub_zero] at h
    have hsum : (z : ℂ).re ^ 2 + (z : ℂ).im ^ 2 = 1 := by
      have h4 := Complex.normSq_eq_norm_sq (z : ℂ)
      rw [Complex.normSq_apply, hz] at h4
      nlinarith [h4]
    have h2 : ‖(WithLp.toLp 2 (fun i : Fin 2 =>
        if i = 0 then (z : ℂ).re else (z : ℂ).im) : E2)‖ ^ 2
        = (z : ℂ).re ^ 2 + (z : ℂ).im ^ 2 := by
      rw [PiLp.norm_sq_eq_of_L2, Fin.sum_univ_two]; simp
    have h3 : ‖(WithLp.toLp 2 (fun i : Fin 2 =>
        if i = 0 then (z : ℂ).re else (z : ℂ).im) : E2)‖ ^ 2 = 1 := by
      rw [h2, hsum]
    rw [Metric.mem_sphere, dist_eq_norm, sub_zero]
    nlinarith [norm_nonneg (WithLp.toLp 2 (fun i : Fin 2 =>
      if i = 0 then (z : ℂ).re else (z : ℂ).im) : E2)]⟩
  continuous_toFun := by
    refine Continuous.subtype_mk ?_ _
    refine (PiLp.continuous_toLp 2 (fun _ : Fin 2 => ℝ)).comp ?_
    refine continuous_pi fun i => ?_
    fin_cases i
    · exact Complex.continuous_re.comp continuous_subtype_val
    · exact Complex.continuous_im.comp continuous_subtype_val

/-- The conjugate direction of the image of `z ∈ S¹ ⊂ ℂ` is `conj z`. -/
lemma xiC_circToSph (z : Circ) : xiC (circToSph z) = starRingEnd ℂ (z : ℂ) := by
  have h0 : ((circToSph z : Sc) : E2) 0 = (z : ℂ).re := rfl
  have h1 : ((circToSph z : Sc) : E2) 1 = (z : ℂ).im := rfl
  rw [xiC, h0, h1]
  apply Complex.ext <;>
    simp only [Complex.sub_re, Complex.sub_im, Complex.mul_re, Complex.mul_im,
      Complex.ofReal_re, Complex.ofReal_im, Complex.I_re, Complex.I_im, Complex.zero_re,
      Complex.zero_im, Complex.conj_re, Complex.conj_im] <;>
    ring

lemma starRingEnd_ne_zero_of_circ (z : Circ) : starRingEnd ℂ (z : ℂ) ≠ 0 := by
  have hz : ‖(z : ℂ)‖ = 1 := by
    have h := Metric.mem_sphere.mp z.2
    rwa [dist_eq_norm, sub_zero] at h
  have hc : ‖starRingEnd ℂ (z : ℂ)‖ = 1 := by rw [RCLike.norm_conj, hz]
  exact norm_ne_zero_iff.mp (by rw [hc]; exact one_ne_zero)

lemma continuous_starRingEnd_circ :
    Continuous fun z : Circ => starRingEnd ℂ (z : ℂ) := by
  have h : Continuous fun z : Circ => star ((z : ℂ)) :=
    (continuous_star : Continuous (star : ℂ → ℂ)).comp continuous_subtype_val
  exact h.congr fun z => rfl

/-- The loop `z ↦ conj z` in `ℂˣ`. -/
def conjLoop : C(Circ, ℂˣ) :=
  ⟨fun z => Units.mk0 (starRingEnd ℂ (z : ℂ)) (starRingEnd_ne_zero_of_circ z),
   continuous_units_mk0 continuous_starRingEnd_circ starRingEnd_ne_zero_of_circ⟩

lemma loopA_comp_circToSph : loopA.comp circToSph = conjLoop := by
  ext z
  rw [ContinuousMap.comp_apply, loopA_coe, xiC_circToSph]
  rfl

/-! ## The radial paths of radii -/

/-- The radial path of radii from `1` down to `r`. -/
def radPath (r : ℝ) (hr0 : 0 ≤ r) (hr1 : r ≤ 1) : C(unitInterval, unitInterval) where
  toFun t := ⟨(1 - (t : ℝ)) + (t : ℝ) * r, by
    refine ⟨?_, ?_⟩
    · have := t.2.1; have := t.2.2; nlinarith
    · have := t.2.1; have := t.2.2; nlinarith⟩
  continuous_toFun := by
    refine Continuous.subtype_mk ?_ _
    exact (continuous_const.sub continuous_subtype_val).add
      (continuous_subtype_val.mul continuous_const)

lemma radPath_zero (r : ℝ) (hr0 : 0 ≤ r) (hr1 : r ≤ 1) :
    ((radPath r hr0 hr1 0 : unitInterval) : ℝ) = 1 := by
  show (1 - ((0 : unitInterval) : ℝ)) + ((0 : unitInterval) : ℝ) * r = 1
  norm_num

lemma radPath_one (r : ℝ) (hr0 : 0 ≤ r) (hr1 : r ≤ 1) :
    ((radPath r hr0 hr1 1 : unitInterval) : ℝ) = r := by
  show (1 - ((1 : unitInterval) : ℝ)) + ((1 : unitInterval) : ℝ) * r = r
  norm_num

lemma radPath_pos (r : ℝ) (hr0 : 0 < r) (hr1 : r ≤ 1) (t : unitInterval) :
    0 < ((radPath r hr0.le hr1 t : unitInterval) : ℝ) := by
  have ht0 := t.2.1
  have ht1 := t.2.2
  show 0 < (1 - (t : ℝ)) + (t : ℝ) * r
  nlinarith

/-- The path of radii from `r` down to `0`. -/
def shrink (r : ℝ) (hr0 : 0 ≤ r) (hr1 : r ≤ 1) : C(unitInterval, unitInterval) where
  toFun t := ⟨(1 - (t : ℝ)) * r, by
    refine ⟨?_, ?_⟩
    · have := t.2.1; have := t.2.2; nlinarith
    · have := t.2.1; have := t.2.2; nlinarith⟩
  continuous_toFun := by
    refine Continuous.subtype_mk ?_ _
    exact (continuous_const.sub continuous_subtype_val).mul continuous_const

lemma shrink_zero (r : ℝ) (hr0 : 0 ≤ r) (hr1 : r ≤ 1) :
    ((shrink r hr0 hr1 0 : unitInterval) : ℝ) = r := by
  show (1 - ((0 : unitInterval) : ℝ)) * r = r
  norm_num

lemma shrink_one (r : ℝ) (hr0 : 0 ≤ r) (hr1 : r ≤ 1) :
    ((shrink r hr0 hr1 1 : unitInterval) : ℝ) = 0 := by
  show (1 - ((1 : unitInterval) : ℝ)) * r = 0
  norm_num

lemma radCM_congr {r r' : unitInterval} (h : (r : ℝ) = (r' : ℝ)) (x : Sc) :
    radCM r x = radCM r' x := by
  apply Subtype.ext
  simp only [radCM_coe]
  rw [h]

/-- The radial homotopy between the boundary loop and the loop of radius `r`. -/
lemma loopC_radial (u : C(Dc, Matrix (Fin 2) (Fin 2) ℂ)) (hunit : ∀ y, IsUnit (u y))
    (hconj : ∀ y, u y * e0 = PyA y * u y) {r : ℝ} (hr0 : 0 < r) (hr1 : r ≤ 1) :
    ContinuousMap.Homotopic
      (loopC u 1 (by norm_num) (fun y hy => Cm_00_ne_zero u hunit hconj hy)
        (fun y hy => continuousAt_Cm u y hy))
      (loopC u ⟨r, hr0.le, hr1⟩ (ne_of_gt hr0) (fun y hy => Cm_00_ne_zero u hunit hconj hy)
        (fun y hy => continuousAt_Cm u y hy)) := by
  have hpos : ∀ t : unitInterval, 0 < ((radPath r hr0.le hr1 t : unitInterval) : ℝ) :=
    fun t => radPath_pos r hr0 hr1 t
  have hne : ∀ p : unitInterval × Sc,
      (Cm u (radCM (radPath r hr0.le hr1 p.1) p.2)) 0 0 ≠ 0 := fun p =>
    Cm_00_ne_zero u hunit hconj (radCM_ne_ctr (ne_of_gt (hpos p.1)) p.2)
  have hrad : Continuous fun q : unitInterval × Sc =>
      radCM (radPath r hr0.le hr1 q.1) q.2 := by
    refine Continuous.subtype_mk ?_ _
    have h1 : Continuous fun q : unitInterval × Sc =>
        ((radPath r hr0.le hr1 q.1 : unitInterval) : ℝ) :=
      continuous_subtype_val.comp ((radPath r hr0.le hr1).continuous.comp continuous_fst)
    have h2 : Continuous fun q : unitInterval × Sc => (q.2 : E2) :=
      continuous_subtype_val.comp continuous_snd
    exact h1.smul h2
  have hc : Continuous fun q : unitInterval × Sc =>
      Cm u (radCM (radPath r hr0.le hr1 q.1) q.2) := by
    rw [continuous_iff_continuousAt]
    intro q
    exact ContinuousAt.comp (x := q)
      (g := Cm u)
      (f := fun q' : unitInterval × Sc => radCM (radPath r hr0.le hr1 q'.1) q'.2)
      (continuousAt_Cm u _ (radCM_ne_ctr (ne_of_gt (hpos q.1)) q.2)) hrad.continuousAt
  have hcont : Continuous fun q : unitInterval × Sc =>
      (Cm u (radCM (radPath r hr0.le hr1 q.1) q.2)) 0 0 :=
    (continuous_apply (0 : Fin 2)).comp ((continuous_apply (0 : Fin 2)).comp hc)
  refine pam_family_homotopic (fun p : unitInterval × Sc =>
      (Cm u (radCM (radPath r hr0.le hr1 p.1) p.2)) 0 0)
    hcont hne ?_ ?_
  · intro x
    have hpt : radCM (1 : unitInterval) x = radCM (radPath r hr0.le hr1 0) x :=
      radCM_congr (by rw [radPath_zero]; rfl) x
    rw [loopC_coe, hpt]
  · intro x
    have hpt : radCM ⟨r, hr0.le, hr1⟩ x = radCM (radPath r hr0.le hr1 1) x :=
      radCM_congr (by rw [radPath_one]) x
    rw [loopC_coe, hpt]

/-! ## The inner loop

For small `r` the loop `x ↦ Cm u (r x) 0 0` is homotopic to `x ↦ x̄ · u (r x) 1 0`. -/

lemma norm_ofReal_C (a : ℝ) : ‖((a : ℝ) : ℂ)‖ = |a| := by
  have h : ‖((a : ℝ) : ℂ)‖ ^ 2 = a ^ 2 := by
    rw [← Complex.normSq_eq_norm_sq, Complex.normSq_ofReal]
    ring
  rw [← Real.sqrt_sq_eq_abs a, ← h, Real.sqrt_sq (norm_nonneg _)]

/-- The inner-loop homotopy. -/
lemma pamInnerLoop_aux (u : C(Dc, Matrix (Fin 2) (Fin 2) ℂ)) (hunit : ∀ y, IsUnit (u y))
    (hconj : ∀ y, u y * e0 = PyA y * u y)
    (r : unitInterval) (hr0 : 0 < (r : ℝ)) (hr1 : (r : ℝ) < 1 / 2)
    (c d : ℝ) (hc : 0 < c) (hcd : c < d)
    (hsmall : ∀ y : Dc, ‖(y : E2)‖ ≤ (r : ℝ) → ‖u y 0 0‖ < c ∧ d < ‖u y 1 0‖)
    (hcoord : ∀ x : Sc,
      sphCoord 0 (radCM r x) = Real.sin (Real.pi * (r : ℝ)) * (x : E2) 0 ∧
      sphCoord 1 (radCM r x) = Real.sin (Real.pi * (r : ℝ)) * (x : E2) 1 ∧
      sphCoordR (radCM r x) = -Real.cos (Real.pi * (r : ℝ)))
    (htrig : 1 - Real.cos (Real.pi * (r : ℝ)) < Real.sin (Real.pi * (r : ℝ))) :
    ∃ H : C(unitInterval × Sc, ℂˣ),
      (∀ x, (H (0, x) : ℂ) = (Cm u (radCM r x)) 0 0) ∧
      (∀ x, (H (1, x) : ℂ) =
        (((x : E2) 0 : ℂ) - Complex.I * ((x : E2) 1 : ℂ)) * (u (radCM r x)) 1 0) := by
  set A : ℝ := 1 - Real.cos (Real.pi * (r : ℝ)) with hA
  set B : ℝ := Real.sin (Real.pi * (r : ℝ)) with hB
  have hApos : 0 < A := by
    rw [hA]
    have h := cos_pi_mul_lt_one (r := (r : ℝ)) hr0 (by linarith)
    linarith
  have hBpos : 0 < B := by
    rw [hB]
    exact Real.sin_pos_of_pos_of_lt_pi (by positivity) (by nlinarith [Real.pi_pos, hr1])
  have hBA : 1 / 2 < B / (2 * A) := by
    rw [lt_div_iff₀ (by linarith : (0 : ℝ) < 2 * A)]
    linarith [htrig]
  have hR : ∀ x : Sc, sphCoordR (radCM r x) = -Real.cos (Real.pi * (r : ℝ)) :=
    fun x => (hcoord x).2.2
  have hs0 : ∀ x : Sc, sphCoord 0 (radCM r x) = B * (x : E2) 0 := fun x => by
    rw [hB]; exact (hcoord x).1
  have hs1 : ∀ x : Sc, sphCoord 1 (radCM r x) = B * (x : E2) 1 := fun x => by
    rw [hB]; exact (hcoord x).2.1
  have hN : ∀ x : Sc, ((hvN2 (radCM r x) : ℂ)) = ((2 * A : ℝ) : ℂ) := by
    intro x
    have h2 : (1 + -Real.cos (Real.pi * (r : ℝ))) = A := by rw [hA]; ring
    rw [hvN2_eq, hv1, hR x, h2]
  have hsin : ∀ x : Sc, star (hv2 (radCM r x)) = ((B : ℂ)) * xiC x := by
    intro x
    have h1 : hv2 (radCM r x)
        = (((B * (x : E2) 0 : ℝ)) : ℂ) + Complex.I * (((B * (x : E2) 1 : ℝ)) : ℂ) := by
      rw [hv2, hs0 x, hs1 x]
    rw [h1, star_add_I (B * (x : E2) 0) (B * (x : E2) 1), xiC]
    push_cast
    ring
  have hCm : ∀ x : Sc, (Cm u (radCM r x)) 0 0
      = (1 / 2 : ℂ) * (u (radCM r x)) 0 0
        + ((B : ℂ) / (2 * A)) * (xiC x * (u (radCM r x)) 1 0) := by
    intro x
    have h2A : ((2 * A : ℝ) : ℂ) ≠ 0 := by
      have hpos : (0 : ℝ) < 2 * A := by linarith
      exact_mod_cast hpos.ne'
    have hAne : ((A : ℝ) : ℂ) ≠ 0 := by exact_mod_cast (ne_of_gt hApos)
    rw [Cm_00, hv1, hR x, hN x, hsin x,
      show (1 + -Real.cos (Real.pi * (r : ℝ))) = A by rw [hA]; ring]
    field_simp [h2A, hAne]
    push_cast
    ring
  have hsmall' : ∀ x : Sc, ‖(u (radCM r x)) 0 0‖ < ‖(u (radCM r x)) 1 0‖ := by
    intro x
    have h1 := (hsmall _ (le_of_eq (norm_radCM r x))).1
    have h2 := (hsmall _ (le_of_eq (norm_radCM r x))).2
    linarith
  let F : unitInterval × Sc → ℂ := fun p =>
    (((1 - (p.1 : ℝ)) * (1 / 2) : ℝ) : ℂ) * (u (radCM r p.2)) 0 0
      + ((((1 - (p.1 : ℝ)) * (B / (2 * A)) + (p.1 : ℝ) : ℝ)) : ℂ)
        * (xiC p.2 * (u (radCM r p.2)) 1 0)
  have hFcont : Continuous F := by
    have ht : Continuous fun p : unitInterval × Sc => (1 - (p.1 : ℝ)) :=
      continuous_const.sub (continuous_subtype_val.comp continuous_fst)
    have ht' : Continuous fun p : unitInterval × Sc => (p.1 : ℝ) :=
      continuous_subtype_val.comp continuous_fst
    have hu00 : Continuous fun p : unitInterval × Sc => (u (radCM r p.2)) 0 0 :=
      (continuous_apply (0 : Fin 2)).comp ((continuous_apply (0 : Fin 2)).comp
        (u.continuous.comp ((radCM r).continuous.comp continuous_snd)))
    have hu10 : Continuous fun p : unitInterval × Sc => (u (radCM r p.2)) 1 0 :=
      (continuous_apply (0 : Fin 2)).comp ((continuous_apply (1 : Fin 2)).comp
        (u.continuous.comp ((radCM r).continuous.comp continuous_snd)))
    have hxi : Continuous fun p : unitInterval × Sc => xiC p.2 :=
      continuous_xiC.comp continuous_snd
    exact ((Complex.continuous_ofReal.comp (ht.mul continuous_const)).mul hu00).add
      ((Complex.continuous_ofReal.comp ((ht.mul continuous_const).add ht')).mul (hxi.mul hu10))
  have hFne : ∀ p : unitInterval × Sc, F p ≠ 0 := by
    intro p
    have ht0 : (0 : ℝ) ≤ (p.1 : ℝ) := p.1.2.1
    have ht1 : (p.1 : ℝ) ≤ 1 := p.1.2.2
    have hαnn : 0 ≤ (1 - (p.1 : ℝ)) * (1 / 2) := by linarith
    have hβnn : 0 ≤ (1 - (p.1 : ℝ)) * (B / (2 * A)) + (p.1 : ℝ) := by
      have h1 : 0 ≤ (1 - (p.1 : ℝ)) * (B / (2 * A)) :=
        mul_nonneg (by linarith) (le_of_lt (by linarith [hApos, hBA]))
      linarith
    have hαle : (1 - (p.1 : ℝ)) * (1 / 2) ≤ 1 / 2 := by linarith
    have hβge : 1 / 2 ≤ (1 - (p.1 : ℝ)) * (B / (2 * A)) + (p.1 : ℝ) := by
      have h1 : (1 - (p.1 : ℝ)) * (1 / 2) ≤ (1 - (p.1 : ℝ)) * (B / (2 * A)) :=
        mul_le_mul_of_nonneg_left (le_of_lt hBA) (by linarith)
      linarith
    have hlt : ‖(((1 - (p.1 : ℝ)) * (1 / 2) : ℝ) : ℂ) * (u (radCM r p.2)) 0 0‖
        < ‖((((1 - (p.1 : ℝ)) * (B / (2 * A)) + (p.1 : ℝ) : ℝ)) : ℂ)
            * (xiC p.2 * (u (radCM r p.2)) 1 0)‖ := by
      rw [norm_mul, norm_mul, norm_ofReal_C, norm_ofReal_C, abs_of_nonneg hαnn,
        abs_of_nonneg hβnn, norm_mul, norm_xiC, one_mul]
      have h1 : (1 - (p.1 : ℝ)) * (1 / 2) * ‖(u (radCM r p.2)) 0 0‖
          ≤ (1 / 2) * ‖(u (radCM r p.2)) 0 0‖ :=
        mul_le_mul_of_nonneg_right hαle (norm_nonneg _)
      have h2 : (1 / 2) * ‖(u (radCM r p.2)) 0 0‖
          < (1 / 2) * ‖(u (radCM r p.2)) 1 0‖ := by
        exact mul_lt_mul_of_pos_left (hsmall' p.2) (by norm_num)
      have h3 : (1 / 2) * ‖(u (radCM r p.2)) 1 0‖
          ≤ ((1 - (p.1 : ℝ)) * (B / (2 * A)) + (p.1 : ℝ)) * ‖(u (radCM r p.2)) 1 0‖ :=
        mul_le_mul_of_nonneg_right hβge (norm_nonneg _)
      linarith
    intro hzero
    have hsum : ‖(((1 - (p.1 : ℝ)) * (1 / 2) : ℝ) : ℂ) * (u (radCM r p.2)) 0 0‖
        = ‖((((1 - (p.1 : ℝ)) * (B / (2 * A)) + (p.1 : ℝ) : ℝ)) : ℂ)
            * (xiC p.2 * (u (radCM r p.2)) 1 0)‖ := by
      have hneg : (((1 - (p.1 : ℝ)) * (1 / 2) : ℝ) : ℂ) * (u (radCM r p.2)) 0 0
          = - (((((1 - (p.1 : ℝ)) * (B / (2 * A)) + (p.1 : ℝ) : ℝ)) : ℂ)
              * (xiC p.2 * (u (radCM r p.2)) 1 0)) := by
        have := hzero
        simp only [F, Prod.fst, Prod.snd] at this
        exact eq_neg_of_add_eq_zero_left this
      rw [hneg, norm_neg]
    linarith
  have hFa : ∀ x : Sc, F (0, x) = (Cm u (radCM r x)) 0 0 := by
    intro x
    show (((1 - ((0 : unitInterval) : ℝ)) * (1 / 2) : ℝ) : ℂ) * (u (radCM r x)) 0 0
        + ((((1 - ((0 : unitInterval) : ℝ)) * (B / (2 * A)) + ((0 : unitInterval) : ℝ) : ℝ)) : ℂ)
          * (xiC x * (u (radCM r x)) 1 0) = (Cm u (radCM r x)) 0 0
    norm_num
    exact (hCm x).symm
  have hFb : ∀ x : Sc, F (1, x) = (((x : E2) 0 : ℂ) - Complex.I * ((x : E2) 1 : ℂ))
      * (u (radCM r x)) 1 0 := by
    intro x
    show (((1 - ((1 : unitInterval) : ℝ)) * (1 / 2) : ℝ) : ℂ) * (u (radCM r x)) 0 0
        + ((((1 - ((1 : unitInterval) : ℝ)) * (B / (2 * A)) + ((1 : unitInterval) : ℝ) : ℝ)) : ℂ)
          * (xiC x * (u (radCM r x)) 1 0)
        = xiC x * (u (radCM r x)) 1 0
    norm_num
  refine ⟨⟨fun p => Units.mk0 (F p) (hFne p),
    continuous_units_mk0 hFcont hFne⟩, ?_, ?_⟩
  · intro x
    show ((Units.mk0 (F (0, x)) (hFne (0, x)) : ℂˣ) : ℂ) = (Cm u (radCM r x)) 0 0
    rw [Units.val_mk0]
    exact hFa x
  · intro x
    show ((Units.mk0 (F (1, x)) (hFne (1, x)) : ℂˣ) : ℂ)
      = (((x : E2) 0 : ℂ) - Complex.I * ((x : E2) 1 : ℂ)) * (u (radCM r x)) 1 0
    rw [Units.val_mk0]
    exact hFb x

/-! ## The main theorem -/

/-- **The disc-model Hopf clutching function is not null-homotopic.**  Let `u : D² → M₂(ℂ)` be a
continuous family of invertible matrices carrying the constant rank-one projection `e₀ = diag(1,0)`
to the disc-model Hopf idempotent `PyA`, and let `f : S¹ → ℂˣ` be the boundary loop
`x ↦ (u (inBallA x)) 0 0`.  Then `f` is not null-homotopic. -/
theorem PAMA_clutching_not_nullhomotopic
    (u : C(Dc, Matrix (Fin 2) (Fin 2) ℂ)) (hunit : ∀ y, IsUnit (u y))
    (hconj : ∀ y, u y * e0 = PyA y * u y)
    (f : C(Sc, ℂˣ)) (hf : ∀ x : Sc, ((f x : ℂˣ) : ℂ) = (u (inBallA x)) 0 0) :
    ¬ ContinuousMap.Homotopic f (ContinuousMap.const Sc 1) := by
  intro hhom
  have hneCm : ∀ y : Dc, y ≠ dctr → (Cm u y) 0 0 ≠ 0 :=
    fun y hy => Cm_00_ne_zero u hunit hconj hy
  have hcontCm : ∀ y : Dc, y ≠ dctr → ContinuousAt (Cm u) y :=
    fun y hy => continuousAt_Cm u y hy
  obtain ⟨hC00, hC10⟩ := PAMCentre u hunit hconj
  obtain ⟨ε, hε0, hε14, hεA, hεB⟩ := PAMCentreGap u hunit hconj
  set r₀ : ℝ := ε / 2 with hr₀def
  have hr₀pos : 0 < r₀ := by rw [hr₀def]; linarith
  have hr₀lt : r₀ < 1 / 2 := by rw [hr₀def]; linarith
  have hr₀le : r₀ ≤ ε := by rw [hr₀def]; linarith
  have hr₀le1 : r₀ ≤ 1 := by linarith
  set R₀ : unitInterval := ⟨r₀, hr₀pos.le, hr₀le1⟩ with hR₀def
  have hR₀val : (R₀ : ℝ) = r₀ := rfl
  have hR₀ne : (R₀ : ℝ) ≠ 0 := by rw [hR₀val]; exact ne_of_gt hr₀pos
  have hdpos : 0 < ‖u dctr 1 0‖ := norm_pos_iff.mpr hC10
  set c : ℝ := ‖u dctr 1 0‖ / 8 with hcdef
  set d : ℝ := ‖u dctr 1 0‖ / 4 with hddef
  have hc : 0 < c := by rw [hcdef]; linarith
  have hcd : c < d := by rw [hcdef, hddef]; linarith
  have hdpos' : 0 < d := by rw [hddef]; linarith
  have hsmall : ∀ y : Dc, ‖(y : E2)‖ ≤ (R₀ : ℝ) → ‖u y 0 0‖ < c ∧ d < ‖u y 1 0‖ := by
    intro y hy
    have hyε : ‖(y : E2)‖ ≤ ε := by
      rw [hR₀val] at hy
      exact le_trans hy hr₀le
    exact ⟨by rw [hcdef]; linarith [hεA y hyε], by rw [hddef]; exact hεB y hyε⟩
  have hne10 : ∀ x : Sc, (u (radCM R₀ x)) 1 0 ≠ 0 := by
    intro x
    have hnorm : ‖((radCM R₀ x : Dc) : E2)‖ = (R₀ : ℝ) := norm_radCM R₀ x
    exact norm_ne_zero_iff.mp (ne_of_gt (lt_trans hdpos' (hsmall _ (le_of_eq hnorm)).2))
  have hcont10 : Continuous fun x : Sc => (u (radCM R₀ x)) 1 0 :=
    (continuous_apply (0 : Fin 2)).comp ((continuous_apply (1 : Fin 2)).comp
      (u.continuous.comp (radCM R₀).continuous))
  -- the inner loop `x ↦ x̄ · u (r₀ x) 1 0`
  let blo : C(Sc, ℂˣ) :=
    ⟨fun x => Units.mk0 (xiC x * (u (radCM R₀ x)) 1 0)
        (mul_ne_zero (xiC_ne_zero x) (hne10 x)),
      continuous_units_mk0 (continuous_xiC.mul hcont10)
        (fun x => mul_ne_zero (xiC_ne_zero x) (hne10 x))⟩
  -- step 1: `f` is homotopic to the boundary loop `loopC u 1`
  have hstep1 : ContinuousMap.Homotopic f (loopC u 1 (by norm_num) hneCm hcontCm) := by
    refine pam_family_homotopic (fun p : unitInterval × Sc =>
      (((1 - (p.1 : ℝ)) + (p.1 : ℝ) * (1 / 2) : ℝ) : ℂ) * (f p.2 : ℂ)) ?_ ?_ ?_ ?_
    · have hreal : Continuous fun p : unitInterval × Sc =>
          (1 - (p.1 : ℝ)) + (p.1 : ℝ) * (1 / 2) :=
        (continuous_const.sub (continuous_subtype_val.comp continuous_fst)).add
          ((continuous_subtype_val.comp continuous_fst).mul continuous_const)
      exact (Complex.continuous_ofReal.comp hreal).mul
        (Units.continuous_val.comp (f.continuous.comp continuous_snd))
    · intro p
      refine mul_ne_zero ?_ (Units.ne_zero _)
      exact_mod_cast ne_of_gt (by have h1 := p.1.2.2; linarith)
    · intro x
      simp
    · intro x
      rw [loopC_coe,
        show radCM (1 : unitInterval) x = inBallA x from (inBallA_eq_radCM_one x).symm,
        Cm_boundary, ← hf x]
      have hcoef : (((1 - ((1 : unitInterval) : ℝ)) + ((1 : unitInterval) : ℝ) * (1 / 2) : ℝ)
          : ℂ) = 1 / 2 := by
        have h1c : ((1 : unitInterval) : ℝ) = 1 := rfl
        rw [h1c]; norm_num
      rw [hcoef]
  -- step 2: radial homotopy from the boundary loop to the loop of radius `r₀`
  have hstep2 : ContinuousMap.Homotopic (loopC u 1 (by norm_num) hneCm hcontCm)
      (loopC u R₀ hR₀ne hneCm hcontCm) :=
    loopC_radial u hunit hconj (r := r₀) hr₀pos hr₀le1
  -- step 3: the loop of radius `r₀` is homotopic to the inner loop `blo`
  have hcoord : ∀ x : Sc,
      sphCoord 0 (radCM R₀ x) = Real.sin (Real.pi * (R₀ : ℝ)) * (x : E2) 0 ∧
      sphCoord 1 (radCM R₀ x) = Real.sin (Real.pi * (R₀ : ℝ)) * (x : E2) 1 ∧
      sphCoordR (radCM R₀ x) = -Real.cos (Real.pi * (R₀ : ℝ)) :=
    fun x => PAMSphCoords.2.1 R₀ x
  have htrig : 1 - Real.cos (Real.pi * (R₀ : ℝ)) < Real.sin (Real.pi * (R₀ : ℝ)) :=
    TrigAux (by rw [hR₀val]; positivity)
      (by rw [hR₀val]; nlinarith [Real.pi_pos, hr₀lt])
  obtain ⟨H, hH0, hH1⟩ := pamInnerLoop_aux u hunit hconj R₀
    (by rw [hR₀val]; exact hr₀pos) (by rw [hR₀val]; exact hr₀lt) c d hc hcd hsmall hcoord htrig
  have hstep3 : ContinuousMap.Homotopic (loopC u R₀ hR₀ne hneCm hcontCm) blo := by
    refine pam_family_homotopic (fun p : unitInterval × Sc => (H p : ℂ))
      (Units.continuous_val.comp H.continuous) (fun p => Units.ne_zero _) ?_ ?_
    · intro x
      rw [loopC_coe, ← hH0 x]
    · intro x
      rw [show ((blo x : ℂˣ) : ℂ)
          = (((x : E2) 0 : ℂ) - Complex.I * ((x : E2) 1 : ℂ)) * (u (radCM R₀ x)) 1 0 from rfl,
        ← hH1 x]
  -- step 4: `blo` is homotopic to the conjugate direction loop `loopA`
  let b10 : C(Sc, ℂˣ) :=
    ⟨fun x => Units.mk0 ((u (radCM R₀ x)) 1 0) (hne10 x),
      continuous_units_mk0 hcont10 hne10⟩
  have hblo_eq : blo = loopA * b10 := by
    ext x
    rfl
  have hb10raw : ContinuousMap.Homotopic b10
      (ContinuousMap.const Sc (Units.mk0 ((u dctr) 1 0) hC10)) := by
    refine pam_family_homotopic (fun p : unitInterval × Sc =>
      (u (radCM (shrink r₀ hr₀pos.le hr₀le1 p.1) p.2)) 1 0) ?_ ?_ ?_ ?_
    · have hrad : Continuous fun q : unitInterval × Sc =>
          radCM (shrink r₀ hr₀pos.le hr₀le1 q.1) q.2 := by
        refine Continuous.subtype_mk ?_ _
        have h1 : Continuous fun q : unitInterval × Sc =>
            ((shrink r₀ hr₀pos.le hr₀le1 q.1 : unitInterval) : ℝ) :=
          continuous_subtype_val.comp ((shrink r₀ hr₀pos.le hr₀le1).continuous.comp continuous_fst)
        have h2 : Continuous fun q : unitInterval × Sc => (q.2 : E2) :=
          continuous_subtype_val.comp continuous_snd
        exact h1.smul h2
      exact (continuous_apply (0 : Fin 2)).comp ((continuous_apply (1 : Fin 2)).comp
        (u.continuous.comp hrad))
    · intro p
      refine norm_ne_zero_iff.mp (ne_of_gt (lt_trans hdpos' (hsmall _ ?_).2))
      rw [norm_radCM, hR₀val]
      have ht0 := p.1.2.1
      show (1 - (p.1 : ℝ)) * r₀ ≤ r₀
      nlinarith
    · intro x
      show ((b10 x : ℂˣ) : ℂ)
        = (u (radCM (shrink r₀ hr₀pos.le hr₀le1 0) x)) 1 0
      have hpt : radCM (shrink r₀ hr₀pos.le hr₀le1 0) x = radCM R₀ x :=
        radCM_congr (by rw [shrink_zero, hR₀val]) x
      rw [hpt]
      rfl
    · intro x
      show ((Units.mk0 ((u dctr) 1 0) hC10 : ℂˣ) : ℂ)
        = (u (radCM (shrink r₀ hr₀pos.le hr₀le1 1) x)) 1 0
      have hpt : radCM (shrink r₀ hr₀pos.le hr₀le1 1) x = dctr := by
        apply Subtype.ext
        simp only [radCM_coe, shrink_one, dctr_coe]
        simp
      rw [hpt]
      rfl
  have hb10 : ContinuousMap.Homotopic b10 (ContinuousMap.const Sc 1) :=
    hb10raw.trans (pam_const_homotopic (Units.mk0 ((u dctr) 1 0) hC10) 1)
  have hstep4 : ContinuousMap.Homotopic blo loopA := by
    have h1 : ContinuousMap.Homotopic (loopA * b10) loopA := by
      have h := pam_mul_homotopic (ContinuousMap.Homotopic.refl loopA) hb10
      rwa [show loopA * ContinuousMap.const Sc 1 = loopA from by ext x; simp] at h
    rw [hblo_eq]
    exact h1
  -- assembling: `loopA` is null-homotopic
  have ha : ContinuousMap.Homotopic loopA (ContinuousMap.const Sc 1) :=
    hstep4.symm.trans (hstep3.symm.trans (hstep2.symm.trans (hstep1.symm.trans hhom)))
  -- transport along `S¹ ⊂ ℂ → S¹ ⊂ ℝ²` and contradict `zpowLogZero`
  have hcomp : ContinuousMap.Homotopic (loopA.comp circToSph) (ContinuousMap.const Circ 1) := by
    have h := ha.comp (ContinuousMap.Homotopic.refl circToSph)
    rwa [ContinuousMap.const_comp] at h
  have hhomolog : ContinuousMap.Homotopic conjLoop (ContinuousMap.const Circ 1) := by
    rw [← loopA_comp_circToSph]
    exact hcomp
  obtain ⟨F, hF⟩ := (Work.KT.Dim2.circle_log_facts).2.1 conjLoop hhomolog
  have hG : ∀ z : Circ, Complex.exp ((-F) z) = (z : ℂ) := by
    intro z
    have hz : ‖(z : ℂ)‖ = 1 := by
      have h := Metric.mem_sphere.mp z.2
      rwa [dist_eq_norm, sub_zero] at h
    have hmul : (z : ℂ) * starRingEnd ℂ (z : ℂ) = 1 := by
      have h1 := Complex.mul_conj (z : ℂ)
      rw [Complex.normSq_eq_norm_sq, hz, one_pow] at h1
      simpa using h1
    have hval : (conjLoop z : ℂ) = starRingEnd ℂ (z : ℂ) := rfl
    rw [ContinuousMap.neg_apply, Complex.exp_neg, hF z, hval]
    exact inv_eq_of_mul_eq_one_left hmul
  have hw : ∃ F' : C(Circ, ℂ), ∀ z, Complex.exp (F' z) = (z : ℂ) ^ (1 : ℤ) :=
    ⟨-F, fun z => by rw [zpow_one]; exact hG z⟩
  exact one_ne_zero (((Work.KT.Dim2.circle_log_facts).2.2 1).mp hw)

end

end Work.KT.D2
