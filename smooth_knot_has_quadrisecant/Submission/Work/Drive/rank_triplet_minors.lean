import Mathlib
import Submission.Work.Drive.qwDefs
import Submission.Work.Drive.qwCollRow
import Submission.Work.Drive.rank_triplet_Xa
import Submission.Work.Drive.collRowSlotBreakNormal
import Submission.Work.Drive.exists_det_submatrix_ne_zero
import Submission.Work.Drive.contDiff_qPsiM
import Submission.Work.Drive.tangencyBadSet
import Submission.Commons.Analysis.CrossProduct.cross3_contDiff
import Submission.Commons.Analysis.CrossProduct.cross3_eq_zero_iff_smul
import Submission.Commons.Analysis.Calculus.FDeriv.fderiv_along_axis_eq_deriv

namespace Work.Drive

section Helpers
open LeanEval.KnotTheory.Quadrisecant

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option linter.unusedSimpArgs false

/-! ## Elementary cross-product identities in the collinear frame -/

theorem qw_cross3_neg_smul_add (U V : Space) (β : ℝ) :
    cross3 (-V) (β • U) + cross3 U (-V) = (β - 1) • cross3 U V := by
  rw [cross3_neg_left, cross3_smul_right, cross3_neg_right, cross3_anticomm U V]
  simp only [smul_neg, neg_neg]
  rw [sub_smul, one_smul]
  abel

theorem qw_cross3_smul_right_neg (U V : Space) (β : ℝ) :
    cross3 V (β • U) = -β • cross3 U V := by
  rw [cross3_smul_right, cross3_anticomm U V]
  simp only [smul_neg, neg_smul, neg_neg]

/-! ## The perturbed curve along a coefficient line -/

theorem qw_perturbCorr_add_smul (c dc : Coeff) (s t : ℝ) :
    perturbCorr (eCoeff (c + s • dc)) t
      = perturbCorr (eCoeff c) t + s • ((linSum (fun j : Fin 9 => trigBasis j t)) dc) := by
  have h1 : eCoeff (c + s • dc) = eCoeff c + s • eCoeff dc := by rw [map_add, map_smul]
  simp only [perturbCorr, h1, Pi.add_apply, Pi.smul_apply, smul_add, Finset.sum_add_distrib,
    Finset.smul_sum, linSum_apply, coeffProj_apply]
  congr 1
  exact Finset.sum_congr rfl fun j _ => by rw [smul_comm]

theorem qw_perturbVelCorr_add_smul (c dc : Coeff) (s t : ℝ) :
    perturbVelCorr (eCoeff (c + s • dc)) t
      = perturbVelCorr (eCoeff c) t + s • ((linSum (fun j : Fin 9 => trigBasisD j t)) dc) := by
  have h1 : eCoeff (c + s • dc) = eCoeff c + s • eCoeff dc := by rw [map_add, map_smul]
  simp only [perturbVelCorr, h1, Pi.add_apply, Pi.smul_apply, smul_add, Finset.sum_add_distrib,
    Finset.smul_sum, linSum_apply, coeffProj_apply]
  congr 1
  exact Finset.sum_congr rfl fun j _ => by rw [smul_comm]

theorem qw_pertV_add_smul (r : ℝ → Space) (c dc : Coeff) (s t : ℝ) :
    pertV r (c + s • dc) t = pertV r c t + s • ((linSum (fun j : Fin 9 => trigBasis j t)) dc) := by
  simp only [pertV, perturb]
  rw [qw_perturbCorr_add_smul, add_assoc]

theorem qw_pertVelV_add_smul (r : ℝ → Space) (c dc : Coeff) (s t : ℝ) :
    pertVelV r (c + s • dc) t
      = pertVelV r c t + s • ((linSum (fun j : Fin 9 => trigBasisD j t)) dc) := by
  simp only [pertVelV, perturbVel]
  rw [qw_perturbVelCorr_add_smul, add_assoc]

/-! ## The partial formula in the collinear frame -/

/-- The four transverse chord-tangent vectors at the window `x`. -/
noncomputable def qwPartialVel (r : ℝ → Space) (x : Coeff × QP) : Fin 4 → Space :=
  fun i => cross3 (qU r x) (pertVelV r x.1 (qtp x.2 i))

/-- The change of the four transverse chord-tangent vectors in a coefficient direction. -/
noncomputable def qwVelChange (r : ℝ → Space) (x : Coeff × QP) (dc : Coeff) : Fin 4 → Space :=
  fun i => cross3 (qU r x) ((linSum (fun j : Fin 9 => trigBasisD j (qtp x.2 i))) dc)

@[simp] theorem qwPartialVel_zero (r : ℝ → Space) (x : Coeff × QP) :
    qwPartialVel r x 0 = cross3 (qU r x) (pertVelV r x.1 (qA x.2)) := rfl
@[simp] theorem qwPartialVel_one (r : ℝ → Space) (x : Coeff × QP) :
    qwPartialVel r x 1 = cross3 (qU r x) (pertVelV r x.1 (qZ x.2)) := rfl
@[simp] theorem qwPartialVel_two (r : ℝ → Space) (x : Coeff × QP) :
    qwPartialVel r x 2 = cross3 (qU r x) (pertVelV r x.1 (qW x.2)) := rfl
@[simp] theorem qwPartialVel_three (r : ℝ → Space) (x : Coeff × QP) :
    qwPartialVel r x 3 = cross3 (qU r x) (pertVelV r x.1 (qB x.2)) := rfl

/-- **The four partials in the collinear frame.** -/
theorem qPartial_eq_collRow {r : ℝ → Space} (hr : IsSmoothKnot r) {x : Coeff × QP} {β γ : ℝ}
    (hv : qV r x = β • qU r x) (hs : qS r x = γ • qU r x) :
    qPartial r x = collRow β γ (qwPartialVel r x) := by
  funext i
  obtain ⟨k, hk⟩ := i
  interval_cases k <;>
    simp only [qPartial, quadPartial.eq_1, quadPartial.eq_2, quadPartial.eq_3, quadPartial.eq_4,
      velocity, deriv_pertV_eq hr]
  · show (cross3 (-(pertVelV r x.1 (qA x.2))) (qV r x)
        + cross3 (qU r x) (-(pertVelV r x.1 (qA x.2))),
      cross3 (-(pertVelV r x.1 (qA x.2))) (qS r x)
        + cross3 (qU r x) (-(pertVelV r x.1 (qA x.2))))
      = collRow β γ (qwPartialVel r x) ⟨0, hk⟩
    rw [hv, hs, collRow_apply_zero]
    exact Prod.ext (qw_cross3_neg_smul_add (qU r x) (pertVelV r x.1 (qA x.2)) β)
      (qw_cross3_neg_smul_add (qU r x) (pertVelV r x.1 (qA x.2)) γ)
  · show (cross3 (pertVelV r x.1 (qZ x.2)) (qV r x),
      cross3 (pertVelV r x.1 (qZ x.2)) (qS r x)) = collRow β γ (qwPartialVel r x) ⟨1, hk⟩
    rw [hv, hs, collRow_apply_one]
    exact Prod.ext (qw_cross3_smul_right_neg (qU r x) (pertVelV r x.1 (qZ x.2)) β)
      (qw_cross3_smul_right_neg (qU r x) (pertVelV r x.1 (qZ x.2)) γ)
  · show (cross3 (qU r x) (pertVelV r x.1 (qW x.2)), 0) = collRow β γ (qwPartialVel r x) ⟨2, hk⟩
    rw [collRow_apply_two, qwPartialVel_two]
  · show (0, cross3 (qU r x) (pertVelV r x.1 (qB x.2))) = collRow β γ (qwPartialVel r x) ⟨3, hk⟩
    rw [collRow_apply_three, qwPartialVel_three]

/-! ## Position invariance along a value-preserving coefficient line -/

theorem qw_pertV_qtp_add_smul {r : ℝ → Space} {c dc : Coeff} {τ : QP}
    (hval : ∀ i : Fin 4, (linSum (fun j : Fin 9 => trigBasis j (qtp τ i))) dc = 0)
    (s : ℝ) (i : Fin 4) :
    pertV r (c + s • dc) (qtp τ i) = pertV r c (qtp τ i) := by
  rw [qw_pertV_add_smul, hval i, smul_zero, add_zero]

theorem qw_qPA_add_smul {r : ℝ → Space} {c dc : Coeff} {τ : QP}
    (hval : ∀ i : Fin 4, (linSum (fun j : Fin 9 => trigBasis j (qtp τ i))) dc = 0) (s : ℝ) :
    qPA r (c + s • dc, τ) = qPA r (c, τ) := by
  simp only [qPA]
  exact qw_pertV_qtp_add_smul hval s 0

theorem qw_qPZ_add_smul {r : ℝ → Space} {c dc : Coeff} {τ : QP}
    (hval : ∀ i : Fin 4, (linSum (fun j : Fin 9 => trigBasis j (qtp τ i))) dc = 0) (s : ℝ) :
    qPZ r (c + s • dc, τ) = qPZ r (c, τ) := by
  simp only [qPZ]
  exact qw_pertV_qtp_add_smul hval s 1

theorem qw_qPW_add_smul {r : ℝ → Space} {c dc : Coeff} {τ : QP}
    (hval : ∀ i : Fin 4, (linSum (fun j : Fin 9 => trigBasis j (qtp τ i))) dc = 0) (s : ℝ) :
    qPW r (c + s • dc, τ) = qPW r (c, τ) := by
  simp only [qPW]
  exact qw_pertV_qtp_add_smul hval s 2

theorem qw_qPB_add_smul {r : ℝ → Space} {c dc : Coeff} {τ : QP}
    (hval : ∀ i : Fin 4, (linSum (fun j : Fin 9 => trigBasis j (qtp τ i))) dc = 0) (s : ℝ) :
    qPB r (c + s • dc, τ) = qPB r (c, τ) := by
  simp only [qPB]
  exact qw_pertV_qtp_add_smul hval s 3

theorem qw_qU_add_smul {r : ℝ → Space} {c dc : Coeff} {τ : QP}
    (hval : ∀ i : Fin 4, (linSum (fun j : Fin 9 => trigBasis j (qtp τ i))) dc = 0) (s : ℝ) :
    qU r (c + s • dc, τ) = qU r (c, τ) := by
  simp only [qU]
  rw [qw_qPZ_add_smul hval s, qw_qPA_add_smul hval s]

theorem qw_qV_add_smul {r : ℝ → Space} {c dc : Coeff} {τ : QP}
    (hval : ∀ i : Fin 4, (linSum (fun j : Fin 9 => trigBasis j (qtp τ i))) dc = 0) (s : ℝ) :
    qV r (c + s • dc, τ) = qV r (c, τ) := by
  simp only [qV]
  rw [qw_qPW_add_smul hval s, qw_qPA_add_smul hval s]

theorem qw_qS_add_smul {r : ℝ → Space} {c dc : Coeff} {τ : QP}
    (hval : ∀ i : Fin 4, (linSum (fun j : Fin 9 => trigBasis j (qtp τ i))) dc = 0) (s : ℝ) :
    qS r (c + s • dc, τ) = qS r (c, τ) := by
  simp only [qS]
  rw [qw_qPB_add_smul hval s, qw_qPA_add_smul hval s]

/-! ## The affine formula for the partials along a coefficient line -/

theorem qwPartialVel_add_smul {r : ℝ → Space} {c dc : Coeff} {τ : QP}
    (hval : ∀ i : Fin 4, (linSum (fun j : Fin 9 => trigBasis j (qtp τ i))) dc = 0) (s : ℝ) :
    qwPartialVel r (c + s • dc, τ)
      = fun i => qwPartialVel r (c, τ) i + s • qwVelChange r (c, τ) dc i := by
  have hq : qU r (c + s • dc, τ) = qU r (c, τ) := qw_qU_add_smul hval s
  funext i
  simp only [qwPartialVel, qwVelChange, hq, qw_pertVelV_add_smul, cross3_add_right,
    cross3_smul_right]

theorem qPartial_line {r : ℝ → Space} (hr : IsSmoothKnot r) {c dc : Coeff} {τ : QP} {β γ : ℝ}
    (hv : qV r (c, τ) = β • qU r (c, τ)) (hs : qS r (c, τ) = γ • qU r (c, τ))
    (hval : ∀ i : Fin 4, (linSum (fun j : Fin 9 => trigBasis j (qtp τ i))) dc = 0) (s : ℝ) :
    qPartial r (c + s • dc, τ)
      = fun i => qPartial r (c, τ) i + s • collRow β γ (qwVelChange r (c, τ) dc) i := by
  have hv' : qV r (c + s • dc, τ) = β • qU r (c + s • dc, τ) := by
    rw [qw_qV_add_smul hval s, qw_qU_add_smul hval s, hv]
  have hs' : qS r (c + s • dc, τ) = γ • qU r (c + s • dc, τ) := by
    rw [qw_qS_add_smul hval s, qw_qU_add_smul hval s, hs]
  rw [qPartial_eq_collRow hr hv' hs', qPartial_eq_collRow hr hv hs, qwPartialVel_add_smul hval s]
  have harg : (fun i => qwPartialVel r (c, τ) i + s • qwVelChange r (c, τ) dc i)
      = qwPartialVel r (c, τ) + s • qwVelChange r (c, τ) dc := rfl
  rw [harg, collRow_add, collRow_smul]
  rfl

/-! ## The derivative of a determinant along an affine line -/

/-- If only the `i₀`-th row of `s ↦ A + s • D` is varied, the derivative of the determinant at
`s = 0` is the determinant of `A` with the `i₀`-th row replaced by the `i₀`-th row of `D`. -/
theorem deriv_det_affine_updateRow {m : ℕ} (A D : Matrix (Fin m) (Fin m) ℝ) (i₀ : Fin m)
    (hD : ∀ i, i ≠ i₀ → ∀ j, D i j = 0) :
    deriv (fun s : ℝ => (A + s • D).det) 0 = (A.updateRow i₀ (D i₀)).det := by
  have hmat : ∀ s : ℝ, A + s • D = A.updateRow i₀ (A i₀ + s • D i₀) := by
    intro s
    ext i j
    by_cases h : i = i₀
    · subst h
      simp [Matrix.updateRow_self]
    · simp only [Matrix.add_apply, Matrix.smul_apply, Matrix.updateRow_ne h]
      rw [hD i h j]
      simp
  have hfun : (fun s : ℝ => (A + s • D).det)
      = fun s : ℝ => (A.updateRow i₀ (A i₀)).det + s * (A.updateRow i₀ (D i₀)).det := by
    funext s
    rw [hmat s, Matrix.det_updateRow_add, Matrix.det_updateRow_smul]
  rw [hfun]
  have hd : HasDerivAt (fun s : ℝ => (A.updateRow i₀ (A i₀)).det
      + s * (A.updateRow i₀ (D i₀)).det) ((A.updateRow i₀ (D i₀)).det) 0 := by
    simpa using (((hasDerivAt_id (0 : ℝ)).mul_const ((A.updateRow i₀ (D i₀)).det)).const_add
      ((A.updateRow i₀ (A i₀)).det))
  exact hd.deriv

/-! ## The minor along a coefficient line, and its derivative -/

theorem qPartial_line_apply {r : ℝ → Space} (hr : IsSmoothKnot r) {c dc : Coeff} {τ : QP}
    {β γ : ℝ} (hv : qV r (c, τ) = β • qU r (c, τ)) (hs : qS r (c, τ) = γ • qU r (c, τ))
    (hval : ∀ i : Fin 4, (linSum (fun j : Fin 9 => trigBasis j (qtp τ i))) dc = 0)
    (s : ℝ) (i : Fin 4) :
    qPartial r (c + s • dc, τ) i
      = qPartial r (c, τ) i + s • collRow β γ (qwVelChange r (c, τ) dc) i := by
  rw [qPartial_line hr hv hs hval s]

/-- **The `m`-minor along a coefficient line** is the determinant of an affine matrix. -/
theorem qMinor_line {r : ℝ → Space} (hr : IsSmoothKnot r) {c dc : Coeff} {τ : QP} {β γ : ℝ}
    (hv : qV r (c, τ) = β • qU r (c, τ)) (hs : qS r (c, τ) = γ • qU r (c, τ))
    (hval : ∀ i : Fin 4, (linSum (fun j : Fin 9 => trigBasis j (qtp τ i))) dc = 0)
    (m : ℕ) (a : Fin m → Fin 4) (b : Fin m → Fin 6) (s : ℝ) :
    qMinor r (c + s • dc, τ) m (a, b)
      = (Matrix.of (fun i j : Fin m => (eTgt (qPartial r (c, τ) (a i)
          + s • collRow β γ (qwVelChange r (c, τ) dc) (a i))).ofLp (b j))).det := by
  simp only [qMinor]
  congr 1
  ext i j
  simp only [Matrix.of_apply]
  rw [qPartial_line_apply hr hv hs hval s]

/-- **The derivative of the `m`-minor in a coefficient direction** in which only one of the
enumerated rows (`i₀`) changes. -/
theorem deriv_qMinor_line {r : ℝ → Space} (hr : IsSmoothKnot r) {c dc : Coeff} {τ : QP}
    {β γ : ℝ} (hv : qV r (c, τ) = β • qU r (c, τ)) (hs : qS r (c, τ) = γ • qU r (c, τ))
    (hval : ∀ i : Fin 4, (linSum (fun j : Fin 9 => trigBasis j (qtp τ i))) dc = 0)
    (m : ℕ) (a : Fin m → Fin 4) (b : Fin m → Fin 6) (i₀ : Fin m)
    (hN : ∀ i, i ≠ i₀ → collRow β γ (qwVelChange r (c, τ) dc) (a i) = 0) :
    deriv (fun s : ℝ => qMinor r (c + s • dc, τ) m (a, b)) 0
      = ((Matrix.of (fun i j : Fin m => (eTgt (qPartial r (c, τ) (a i))).ofLp (b j))).updateRow i₀
          (fun j => (eTgt (collRow β γ (qwVelChange r (c, τ) dc) (a i₀))).ofLp (b j))).det := by
  have hfun : (fun s : ℝ => qMinor r (c + s • dc, τ) m (a, b))
      = fun s : ℝ => ((Matrix.of (fun i j : Fin m => (eTgt (qPartial r (c, τ) (a i))).ofLp (b j)))
          + s • (Matrix.of (fun i j : Fin m =>
              (eTgt (collRow β γ (qwVelChange r (c, τ) dc) (a i))).ofLp (b j)))).det := by
    funext s
    rw [qMinor_line hr hv hs hval m a b s]
    congr 1
    ext i j
    simp only [Matrix.add_apply, Matrix.smul_apply, Matrix.of_apply, map_add, map_smul,
      ContinuousLinearEquiv.coe_coe, LinearIsometryEquiv.map_smul]
    rw [smul_eq_mul]
    simp
  rw [hfun]
  refine deriv_det_affine_updateRow _ _ i₀ ?_
  intro i hi j
  simp only [Matrix.of_apply]
  rw [hN i hi]
  simp


/-! ## The nonzero minor derivative in the escaping coefficient direction -/

/-- The coordinate map `(Space × Space) → ℝ⁶` of `eTgt`. -/
noncomputable def coordMap : (Space × Space) →ₗ[ℝ] (Fin 6 → ℝ) where
  toFun v := fun j => (eTgt v).ofLp j
  map_add' v w := by
    funext j
    simp
  map_smul' c v := by
    funext j
    simp

theorem coordMap_ker : LinearMap.ker coordMap = ⊥ := by
  rw [LinearMap.ker_eq_bot']
  intro v hv
  have h1 : (fun j : Fin 6 => (eTgt v).ofLp j) = 0 := hv
  have h2 : eTgt v = 0 := PiLp.ext fun j => congrFun h1 j
  exact eTgt.injective (by simpa using h2)

/-- **The escaping direction moves an `m`-minor.**  If, along the coefficient line
`c + s • dc`, all the enumerated rows but the `i₀`-th stay fixed and the resulting `m`-tuple of rows
(the `i₀`-th being the change `N`) is linearly independent, then some `m`-minor has nonzero
derivative at `s = 0`. -/
theorem exists_qMinor_deriv_ne_zero {r : ℝ → Space} (hr : IsSmoothKnot r) {c dc : Coeff} {τ : QP}
    {β γ : ℝ} (hv : qV r (c, τ) = β • qU r (c, τ)) (hs : qS r (c, τ) = γ • qU r (c, τ))
    (hval : ∀ i : Fin 4, (linSum (fun j : Fin 9 => trigBasis j (qtp τ i))) dc = 0)
    {m : ℕ} (a : Fin m → Fin 4) (i₀ : Fin m) {N : Space × Space}
    (haN : N = collRow β γ (qwVelChange r (c, τ) dc) (a i₀))
    (hzero : ∀ i, i ≠ i₀ → collRow β γ (qwVelChange r (c, τ) dc) (a i) = 0)
    (hY : LinearIndependent ℝ (fun i : Fin m =>
      if i = i₀ then N else qPartial r (c, τ) (a i))) :
    ∃ b : Fin m → Fin 6, deriv (fun s : ℝ => qMinor r (c + s • dc, τ) m (a, b)) 0 ≠ 0 := by
  have hYc : LinearIndependent ℝ (fun i : Fin m =>
      fun j : Fin 6 => (eTgt (if i = i₀ then N else qPartial r (c, τ) (a i))).ofLp j) :=
    hY.map' coordMap coordMap_ker
  obtain ⟨b, -, hbdet⟩ := exists_det_submatrix_ne_zero (m := m) (n := 6) (v := fun i : Fin m =>
      fun j : Fin 6 => (eTgt (if i = i₀ then N else qPartial r (c, τ) (a i))).ofLp j) hYc
  have hmat : (Matrix.of (fun i j : Fin m =>
        (eTgt (if i = i₀ then N else qPartial r (c, τ) (a i))).ofLp (b j)))
      = (Matrix.of (fun i j : Fin m => (eTgt (qPartial r (c, τ) (a i))).ofLp (b j))).updateRow i₀
          (fun j => (eTgt (collRow β γ (qwVelChange r (c, τ) dc) (a i₀))).ofLp (b j)) := by
    ext i j
    simp only [Matrix.updateRow_apply, Matrix.of_apply]
    by_cases h : i = i₀
    · subst h
      rw [if_pos rfl, if_pos rfl, haN]
    · rw [if_neg h, if_neg h]
  refine ⟨b, ?_⟩
  rw [deriv_qMinor_line hr hv hs hval m a b i₀ hzero, ← hmat]
  exact hbdet


/-! ## Transport of the rank of the partial span -/

theorem finrank_span_toLp {ι : Type*} (v : ι → (Space × Space)) :
    Module.finrank ℝ (Submodule.span ℝ (Set.range (fun i => WithLp.toLp 2 (v i))))
      = Module.finrank ℝ (Submodule.span ℝ (Set.range v)) := by
  have hspan : Submodule.span ℝ (Set.range (fun i => WithLp.toLp 2 (v i)))
      = (Submodule.span ℝ (Set.range v)).map
          (↑(WithLp.linearEquiv 2 ℝ (Space × Space)).symm : (Space × Space) →ₗ[ℝ] _) := by
    rw [Submodule.map_span]
    congr 1
    ext y
    simp only [Set.mem_range, Set.mem_image]
    constructor
    · rintro ⟨i, rfl⟩
      exact ⟨v i, ⟨i, rfl⟩,
        congrFun (WithLp.coe_symm_linearEquiv (p := 2) (K := ℝ) (V := Space × Space)) (v i)⟩
    · rintro ⟨x, ⟨i, rfl⟩, hxy⟩
      exact ⟨i, (congrFun (WithLp.coe_symm_linearEquiv (p := 2) (K := ℝ)
        (V := Space × Space)) (v i)).trans hxy⟩
  rw [hspan, LinearEquiv.finrank_map_eq]

theorem finrank_qSpan_eq (r : ℝ → Space) (x : Coeff × QP) :
    Module.finrank ℝ (qSpan r x)
      = Module.finrank ℝ (Submodule.span ℝ (Set.range (fun i : Fin 4 => qPartial r x i))) := by
  simp only [qSpan, qPartialW]
  exact finrank_span_toLp (fun i : Fin 4 => qPartial r x i)

/-- A row of `collRow` vanishes as soon as the corresponding transverse vector does. -/
theorem collRow_apply_eq_zero {β γ : ℝ} {A : Fin 4 → Space} {j : Fin 4} (h : A j = 0) :
    collRow β γ A j = 0 := by
  fin_cases j <;> simp_all [collRow]

/-! ## The direction of the augmented derivative that moves a minor -/

theorem fderiv_triplet_coeff_eq_zero {r : ℝ → Space} (hr : IsSmoothKnot r) {x : Coeff × QP}
    {dc : Coeff} (hval : ∀ i : Fin 4, (linSum (fun j : Fin 9 => trigBasis j (qtp x.2 i))) dc = 0) :
    (fderiv ℝ (fun p : Coeff × QP => triplet r p) x) (dc, 0) = 0 := by
  have hA0 : (linSum fun j : Fin 9 => trigBasis j (qA x.2)) dc = 0 := by simpa using hval 0
  have hZ1 : (linSum fun j : Fin 9 => trigBasis j (qZ x.2)) dc = 0 := by simpa using hval 1
  have hW2 : (linSum fun j : Fin 9 => trigBasis j (qW x.2)) dc = 0 := by simpa using hval 2
  have hB3 : (linSum fun j : Fin 9 => trigBasis j (qB x.2)) dc = 0 := by simpa using hval 3
  rw [fderiv_triplet_coeff hr x dc]
  simp only [tripletCoeffDeriv, hA0, hZ1, hW2, hB3, sub_self, cross3_zero_left,
    cross3_zero_right, zero_add, add_zero]
  rfl

theorem fderiv_qMinor_coeff {r : ℝ → Space} (hr : IsSmoothKnot r) (x : Coeff × QP) (m : ℕ)
    (a : Fin m → Fin 4) (b : Fin m → Fin 6) (dc : Coeff) :
    fderiv ℝ (fun p : Coeff × QP => qMinor r p m (a, b)) x (dc, 0)
      = deriv (fun s : ℝ => qMinor r (x.1 + s • dc, x.2) m (a, b)) 0 := by
  have hd : DifferentiableAt ℝ (fun p : Coeff × QP => qMinor r p m (a, b)) x :=
    ((contDiff_qMinor hr m a b).differentiable (by simp)).differentiableAt
  have h1 := Commons.Analysis.Calculus.FDeriv.fderiv_along_axis_eq_deriv
    (H := fun p : Coeff × QP => qMinor r p m (a, b)) (p := x) (e := (dc, (0 : QP))) hd
  have h2 : (fun s : ℝ => qMinor r (x + s • ((dc, (0 : QP)) : Coeff × QP)) m (a, b))
      = fun s : ℝ => qMinor r (x.1 + s • dc, x.2) m (a, b) := by
    funext s
    rw [prod_add_smul_left]
  rw [← h2, h1.deriv]


/-! ## The vector triple product on `Space` -/

theorem qw_cross3_triple (U p : Space) :
    cross3 U (cross3 U p) = (inner ℝ U p) • U - (inner ℝ U U) • p := by
  rw [show cross3 U (cross3 U p)
      = WithLp.toLp 2 (crossProduct (WithLp.ofLp U) (crossProduct (WithLp.ofLp U) (WithLp.ofLp p))) from rfl]
  rw [cross_cross_eq_smul_sub_smul' (WithLp.ofLp U) (WithLp.ofLp U) (WithLp.ofLp p)]
  simp only [WithLp.toLp_sub, WithLp.toLp_smul, WithLp.toLp_ofLp]
  congr 2 <;> simp [PiLp.inner_apply, dotProduct, mul_comm]

/-- Every vector orthogonal to `U` is the cross product of `U` with some vector. -/
theorem exists_cross3_eq_of_inner_eq_zero {U p : Space} (hU : U ≠ 0)
    (hp : inner ℝ p U = 0) : ∃ Δ : Space, cross3 U Δ = p := by
  have hUU : inner ℝ U U ≠ 0 := by
    intro h
    exact hU (inner_self_eq_zero.mp h)
  refine ⟨-((inner ℝ U U)⁻¹) • cross3 U p, ?_⟩
  have hcross : cross3 U (cross3 U p) = -((inner ℝ U U)) • p := by
    rw [qw_cross3_triple, show inner ℝ U p = 0 from by rw [real_inner_comm]; exact hp,
      zero_smul, zero_sub, neg_smul]
  rw [cross3_smul_right, hcross, smul_smul, neg_mul_neg, inv_mul_cancel₀ hUU, one_smul]


theorem fderiv_qMinorPi_apply {r : ℝ → Space} (hr : IsSmoothKnot r) (x : Coeff × QP) (m : ℕ)
    (v : Coeff × QP) (a : Fin m → Fin 4) (b : Fin m → Fin 6) :
    (fderiv ℝ (fun p : Coeff × QP => fun (a : Fin m → Fin 4) (b : Fin m → Fin 6) =>
        qMinor r p m (a, b)) x v) a b
      = fderiv ℝ (fun p : Coeff × QP => qMinor r p m (a, b)) x v := by
  have hpi := fderiv_pi (𝕜 := ℝ) (x := x)
    (φ := fun (a : Fin m → Fin 4) => fun p : Coeff × QP => fun (b : Fin m → Fin 6) =>
      qMinor r p m (a, b)) (by
      intro a
      have h : ContDiff ℝ ⊤ (fun p : Coeff × QP => fun (b : Fin m → Fin 6) =>
          qMinor r p m (a, b)) := by
        apply contDiff_pi.2
        intro b
        exact contDiff_qMinor hr m a b
      exact (h.differentiable (by simp)).differentiableAt)
  have hpi2 := fderiv_pi (𝕜 := ℝ) (x := x)
    (φ := fun (b : Fin m → Fin 6) => fun p : Coeff × QP => qMinor r p m (a, b))
    (fun b => ((contDiff_qMinor hr m a b).differentiable (by simp)).differentiableAt)
  rw [hpi, ContinuousLinearMap.pi_apply, hpi2, ContinuousLinearMap.pi_apply]


end Helpers


set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000

open Work.Drive LeanEval.KnotTheory.Quadrisecant in
/-- **The rank of the level-`m` augmented derivative at a collinear window of partial rank `m-1`.**

At a collinear window (`qU ≠ 0`, `qV = β • qU`, `qS = γ • qU`, `β ≠ γ`) whose four perturbed points
`pertV r c (qtp τ i)` are pairwise distinct (`hpts`), whose four partials `quadPartial` span a space
of dimension exactly `m - 1` (`1 ≤ m ≤ 4`), and for which the coefficient directions realize (a)
every prescribed four-tuple of values at the four window parameters and (b) every prescribed
four-tuple of *velocity* changes at those parameters while keeping the values fixed, the derivative
of the augmented map `p ↦ (triplet r p, all m-minors of the partial matrix)` has rank at least `5`.

Rationale.  The image of the derivative of `triplet` alone is the four-dimensional space
`V = {(x,y,z) ∈ (qU^⊥)³ : z = βy - γx}`.  It remains to find a direction in `ker d(triplet)` along
which some `m`-minor changes.  In the collinear frame with `u = qU`, the partial matrix is
`P_a = ((1-β)X_a,(1-γ)X_a)`, `P_z = (β X_z, γ X_z)`, `P_w = (u×v_w, 0)`, `P_b = (0, u×v_b)` with
`X_k = v_k × u ∈ u^⊥`; the `hcomb` directions change `X_k` freely inside `u^⊥` while fixing the
positions.  Writing the `m`-minor determinant by its cofactor `C` (of rank one when the partials
have rank `m-1`), the condition that *every* `m`-minor be stationary on the velocity directions is a
system of four linear conditions on `C`; a two-case analysis shows that they force the partials to
have rank at most `m - 2`, contradicting `hrk`.  (A reviewer verified the case `m = 4` by an
exhaustive exact rational computation over all rank-3 configurations with `β, γ ∉ {0,1}` and
`β ≠ γ`, finding stationary configurations only when `β = γ`.) -/
theorem rank_triplet_minors {r : ℝ → Space} (hr : IsSmoothKnot r) {c : Coeff} {τ : QP} {β γ : ℝ}
    (hU : qU r (c, τ) ≠ 0)
    (hv : qV r (c, τ) = β • qU r (c, τ))
    (hs : qS r (c, τ) = γ • qU r (c, τ))
    (hbγ : β ≠ γ)
    (hpts : ∀ i j : Fin 4, i ≠ j → pertV r c (qtp τ i) ≠ pertV r c (qtp τ j))
    (hsurj : Function.Surjective fun dc : Coeff => fun i : Fin 4 =>
      (linSum (fun j : Fin 9 => trigBasis j (qtp τ i))) dc)
    (hcomb : ∀ w : Fin 4 → Space, ∃ dc : Coeff,
      (∀ i : Fin 4, (linSum (fun j : Fin 9 => trigBasis j (qtp τ i))) dc = 0) ∧
      (∀ i : Fin 4, (linSum (fun j : Fin 9 => trigBasisD j (qtp τ i))) dc = w i))
    {m : ℕ} (hm1 : 1 ≤ m) (hm4 : m ≤ 4)
    (hrk : Module.finrank ℝ (qSpan r (c, τ)) = m - 1) :
    5 ≤ Module.finrank ℝ
      (LinearMap.range
        ((fderiv ℝ (fun p : Coeff × QP => qPsiM r m p) (c, τ)).toLinearMap)) := by
  classical
  -- ## 0. basic collinearity data
  have hqV_ne : qV r (c, τ) ≠ 0 := by
    show qPW r (c, τ) - qPA r (c, τ) ≠ 0
    rw [sub_ne_zero]
    exact hpts 2 0 (by decide)
  have hqUqV : qU r (c, τ) ≠ qV r (c, τ) := by
    intro h
    have hh : qPZ r (c, τ) - qPA r (c, τ) = qPW r (c, τ) - qPA r (c, τ) := h
    have hh' : qPZ r (c, τ) = qPW r (c, τ) := by
      have h2 := congrArg (fun z : Space => z + qPA r (c, τ)) hh
      simpa using h2
    exact hpts 1 2 (by decide) (by simpa [qPZ, qPW, qtp] using hh')
  have hqUqS : qU r (c, τ) ≠ qS r (c, τ) := by
    intro h
    have hh : qPZ r (c, τ) - qPA r (c, τ) = qPB r (c, τ) - qPA r (c, τ) := h
    have hh' : qPZ r (c, τ) = qPB r (c, τ) := by
      have h2 := congrArg (fun z : Space => z + qPA r (c, τ)) hh
      simpa using h2
    exact hpts 1 3 (by decide) (by simpa [qPZ, qPB, qtp] using hh')
  have hqS_ne : qS r (c, τ) ≠ 0 := by
    show qPB r (c, τ) - qPA r (c, τ) ≠ 0
    rw [sub_ne_zero]
    exact fun h => hpts 0 3 (by decide) (by simpa [qPB, qPA, qtp] using h.symm)
  have hβ0 : β ≠ 0 := fun h => hqV_ne (by rw [hv, h, zero_smul])
  have hβ1 : β ≠ 1 := fun h => hqUqV (by rw [hv, h, one_smul])
  have hγ0 : γ ≠ 0 := fun h => hqS_ne (by rw [hs, h, zero_smul])
  have hγ1 : γ ≠ 1 := fun h => hqUqS (by rw [hs, h, one_smul])
  -- ## 1. the rank of the partials in the collinear frame
  have hAr : collRow β γ (qwPartialVel r (c, τ)) = qPartial r (c, τ) :=
    (qPartial_eq_collRow hr hv hs).symm
  have hrkA : Module.finrank ℝ
      (Submodule.span ℝ (Set.range (collRow β γ (qwPartialVel r (c, τ))))) = m - 1 := by
    rw [hAr, ← finrank_qSpan_eq r (c, τ), hrk]
  -- ## 2. the escaping slot
  obtain ⟨k, f, hf_inj, hf_ne, hf_ind, p, hpU, hp_esc⟩ :=
    collRowSlotBreakNormal hU hβ0 hβ1 hγ0 hγ1 hbγ (qwPartialVel r (c, τ)) hm1 hm4 hrkA
  -- ## 3. realise `p` as a transverse change
  obtain ⟨Δ, hΔ⟩ := exists_cross3_eq_of_inner_eq_zero hU hpU
  -- ## 4. the coefficient direction
  obtain ⟨dc, hdc_val, hdc_vel⟩ := hcomb (Pi.single k Δ)
  have hvc : qwVelChange r (c, τ) dc = Pi.single (M := fun _ : Fin 4 => Space) k p := by
    funext i
    show cross3 (qU r (c, τ)) ((linSum (fun j : Fin 9 => trigBasisD j (qtp τ i))) dc)
      = Pi.single (M := fun _ : Fin 4 => Space) k p i
    rw [hdc_vel i]
    by_cases h : i = k
    · subst h
      rw [Pi.single_apply i Δ i, Pi.single_apply i p i, if_pos rfl, if_pos rfl]
      exact hΔ
    · simp [h, cross3_zero_right]
  -- ## 5. the escape, in terms of the partials
  have hfam : (fun i : Fin (m - 1) => collRow β γ (qwPartialVel r (c, τ)) (f i))
      = fun i => qPartial r (c, τ) (f i) := by
    funext i
    rw [hAr]
  have hesc : collRow β γ (Pi.single k p) k ∉
      Submodule.span ℝ (Set.range (fun i : Fin (m - 1) => qPartial r (c, τ) (f i))) := by
    rw [← hfam]
    exact hp_esc
  -- ## 6. the escaping minor derivative
  have hescape : ∃ (a : Fin m → Fin 4) (b : Fin m → Fin 6),
      deriv (fun s : ℝ => qMinor r (c + s • dc, τ) m (a, b)) 0 ≠ 0 := by
    interval_cases m
    · refine ⟨fun _ : Fin 1 => k, ?_⟩
      refine exists_qMinor_deriv_ne_zero hr hv hs hdc_val (a := fun _ : Fin 1 => k) (i₀ := 0)
        (N := collRow β γ (Pi.single k p) k) ?_ ?_ ?_
      · show collRow β γ (Pi.single k p) k = collRow β γ (qwVelChange r (c, τ) dc) k
        rw [hvc]
      · intro i hi
        exact absurd (Subsingleton.elim i 0) hi
      · have hN0 : collRow β γ (Pi.single k p) k ≠ 0 := by
          intro h0
          exact hesc (h0 ▸ Submodule.zero_mem _)
        rw [show (fun i : Fin 1 => if i = 0 then collRow β γ (Pi.single k p) k
            else qPartial r (c, τ) (k)) = fun _ : Fin 1 => collRow β γ (Pi.single k p) k
          from by funext i; fin_cases i; simp]
        rw [linearIndependent_unique_iff]
        exact hN0
    · refine ⟨![k, f 0], ?_⟩
      refine exists_qMinor_deriv_ne_zero hr hv hs hdc_val (a := ![k, f 0]) (i₀ := 0)
        (N := collRow β γ (Pi.single k p) k) ?_ ?_ ?_
      · show collRow β γ (Pi.single k p) k = collRow β γ (qwVelChange r (c, τ) dc) (![k, f 0] 0)
        rw [show (![k, f 0] : Fin 2 → Fin 4) 0 = k from by simp, hvc]
      · intro i hi
        fin_cases i
        · exact absurd rfl hi
        · show collRow β γ (qwVelChange r (c, τ) dc) (f 0) = 0
          rw [hvc]
          exact collRow_apply_eq_zero (by rw [Pi.single_apply, if_neg (hf_ne 0)])
      · rw [show (fun i : Fin 2 => if i = 0 then collRow β γ (Pi.single k p) k
            else qPartial r (c, τ) (![k, f 0] i))
            = Fin.cons (collRow β γ (Pi.single k p) k) (fun i : Fin 1 => qPartial r (c, τ) (f i))
          from by
            funext i
            fin_cases i
            · simp
            · show qPartial r (c, τ) (f 0) = (Fin.cons (collRow β γ (Pi.single k p) k)
                (fun i : Fin 1 => qPartial r (c, τ) (f i)) : Fin 2 → Space × Space) 1
              rw [Fin.cons_one]]
        refine linearIndependent_finCons.mpr ⟨?_, hesc⟩
        rw [← hfam]
        exact hf_ind
    · refine ⟨![k, f 0, f 1], ?_⟩
      refine exists_qMinor_deriv_ne_zero hr hv hs hdc_val (a := ![k, f 0, f 1]) (i₀ := 0)
        (N := collRow β γ (Pi.single k p) k) ?_ ?_ ?_
      · show collRow β γ (Pi.single k p) k = collRow β γ (qwVelChange r (c, τ) dc) (![k, f 0, f 1] 0)
        rw [show (![k, f 0, f 1] : Fin 3 → Fin 4) 0 = k from by simp, hvc]
      · intro i hi
        fin_cases i
        · exact absurd rfl hi
        · show collRow β γ (qwVelChange r (c, τ) dc) (f 0) = 0
          rw [hvc]
          exact collRow_apply_eq_zero (by rw [Pi.single_apply, if_neg (hf_ne 0)])
        · show collRow β γ (qwVelChange r (c, τ) dc) (f 1) = 0
          rw [hvc]
          exact collRow_apply_eq_zero (by rw [Pi.single_apply, if_neg (hf_ne 1)])
      · rw [show (fun i : Fin 3 => if i = 0 then collRow β γ (Pi.single k p) k
            else qPartial r (c, τ) (![k, f 0, f 1] i))
            = Fin.cons (collRow β γ (Pi.single k p) k) (fun i : Fin 2 => qPartial r (c, τ) (f i))
          from by
            funext i
            fin_cases i
            · simp
            · show qPartial r (c, τ) (f 0) = (Fin.cons (collRow β γ (Pi.single k p) k)
                (fun i : Fin 2 => qPartial r (c, τ) (f i)) : Fin 3 → Space × Space) 1
              rw [Fin.cons_one]
            · show qPartial r (c, τ) (f 1) = (Fin.cons (collRow β γ (Pi.single k p) k)
                (fun i : Fin 2 => qPartial r (c, τ) (f i)) : Fin 3 → Space × Space) 2
              rw [show (2 : Fin 3) = Fin.succ 1 from rfl, Fin.cons_succ]]
        refine linearIndependent_finCons.mpr ⟨?_, hesc⟩
        rw [← hfam]
        exact hf_ind
    · refine ⟨![k, f 0, f 1, f 2], ?_⟩
      refine exists_qMinor_deriv_ne_zero hr hv hs hdc_val (a := ![k, f 0, f 1, f 2]) (i₀ := 0)
        (N := collRow β γ (Pi.single k p) k) ?_ ?_ ?_
      · show collRow β γ (Pi.single k p) k
          = collRow β γ (qwVelChange r (c, τ) dc) (![k, f 0, f 1, f 2] 0)
        rw [show (![k, f 0, f 1, f 2] : Fin 4 → Fin 4) 0 = k from by simp, hvc]
      · intro i hi
        fin_cases i
        · exact absurd rfl hi
        · show collRow β γ (qwVelChange r (c, τ) dc) (f 0) = 0
          rw [hvc]
          exact collRow_apply_eq_zero (by rw [Pi.single_apply, if_neg (hf_ne 0)])
        · show collRow β γ (qwVelChange r (c, τ) dc) (f 1) = 0
          rw [hvc]
          exact collRow_apply_eq_zero (by rw [Pi.single_apply, if_neg (hf_ne 1)])
        · show collRow β γ (qwVelChange r (c, τ) dc) (f 2) = 0
          rw [hvc]
          exact collRow_apply_eq_zero (by rw [Pi.single_apply, if_neg (hf_ne 2)])
      · rw [show (fun i : Fin 4 => if i = 0 then collRow β γ (Pi.single k p) k
            else qPartial r (c, τ) (![k, f 0, f 1, f 2] i))
            = Fin.cons (collRow β γ (Pi.single k p) k)
                (fun i : Fin 3 => qPartial r (c, τ) (f i))
          from by
            funext i
            fin_cases i
            · simp
            · show qPartial r (c, τ) (f 0) = (Fin.cons (collRow β γ (Pi.single k p) k)
                (fun i : Fin 3 => qPartial r (c, τ) (f i)) : Fin 4 → Space × Space) 1
              rw [Fin.cons_one]
            · show qPartial r (c, τ) (f 1) = (Fin.cons (collRow β γ (Pi.single k p) k)
                (fun i : Fin 3 => qPartial r (c, τ) (f i)) : Fin 4 → Space × Space) 2
              rw [show (2 : Fin 4) = Fin.succ 1 from rfl, Fin.cons_succ]
            · show qPartial r (c, τ) (f 2) = (Fin.cons (collRow β γ (Pi.single k p) k)
                (fun i : Fin 3 => qPartial r (c, τ) (f i)) : Fin 4 → Space × Space) 3
              rw [show (3 : Fin 4) = Fin.succ 2 from rfl, Fin.cons_succ]]
        refine linearIndependent_finCons.mpr ⟨?_, hesc⟩
        rw [← hfam]
        exact hf_ind
  -- ## 7. the direction kills the triplet and moves a minor
  obtain ⟨a₀, b₀, hb₀⟩ := hescape
  let qmin : Coeff × QP → (Fin m → Fin 4) → (Fin m → Fin 6) → ℝ :=
    fun p a b => qMinor r p m (a, b)
  have hqmin_diff : DifferentiableAt ℝ qmin (c, τ) := by
    have h : ContDiff ℝ ⊤ qmin := by
      apply contDiff_pi.2
      intro a
      apply contDiff_pi.2
      intro b
      exact contDiff_qMinor hr m a b
    exact (h.differentiable (by simp)).differentiableAt
  have hDmin : fderiv ℝ qmin (c, τ) (dc, 0) ≠ 0 := by
    intro h0
    have hcomp : fderiv ℝ qmin (c, τ) (dc, 0) a₀ b₀ = 0 := by
      rw [h0]
      rfl
    have hcomp' : fderiv ℝ (fun p : Coeff × QP => qMinor r p m (a₀, b₀)) (c, τ) (dc, 0) = 0 := by
      rw [← fderiv_qMinorPi_apply hr (c, τ) m (dc, 0) a₀ b₀]
      exact hcomp
    rw [fderiv_qMinor_coeff hr (c, τ) m a₀ b₀ dc] at hcomp'
    exact hb₀ hcomp'
  -- ## 8. the derivative splits
  have hsplit : fderiv ℝ (fun p : Coeff × QP => qPsiM r m p) (c, τ)
      = (fderiv ℝ (fun p : Coeff × QP => triplet r p) (c, τ)).prod
        (fderiv ℝ qmin (c, τ)) := by
    have h1 : DifferentiableAt ℝ (fun p : Coeff × QP => triplet r p) (c, τ) :=
      ((contDiff_triplet hr).differentiable (by simp)).differentiableAt
    rw [show qPsiM r m = fun p => (triplet r p, qmin p) from rfl]
    exact h1.fderiv_prodMk hqmin_diff
  -- ## 9. the rank computation
  set D : (Coeff × QP) →ₗ[ℝ] (Space × Space × Space) ×
      ((Fin m → Fin 4) → (Fin m → Fin 6) → ℝ) :=
    (fderiv ℝ (fun p : Coeff × QP => qPsiM r m p) (c, τ)).toLinearMap with hDdef
  have hDfst : ∀ v : Coeff × QP, (D v).1
      = (fderiv ℝ (fun p : Coeff × QP => triplet r p) (c, τ)) v := by
    intro v
    rw [hDdef, hsplit]
    rfl
  have hDsnd : ∀ v : Coeff × QP, (D v).2 = (fderiv ℝ qmin (c, τ)) v := by
    intro v
    rw [hDdef, hsplit]
    rfl
  have hDdc : D (dc, (0 : QP)) ≠ 0 := by
    intro h0
    apply hDmin
    have h1 := congrArg Prod.snd h0
    rw [hDsnd (dc, (0 : QP))] at h1
    rw [h1]
    rfl
  obtain ⟨g0, hg0⟩ := LinearMap.exists_rightInverse_of_surjective (valLin4 τ)
    (LinearMap.range_eq_top.mpr (valLin4_surjective hsurj))
  obtain ⟨K', hK'⟩ := Submodule.exists_isCompl (LinearMap.ker (crossUL (qU r (c, τ))))
  have hK'2 : Module.finrank ℝ K' = 2 := by
    have hker : Module.finrank ℝ (LinearMap.ker (crossUL (qU r (c, τ)))) = 1 :=
      finrank_ker_crossUL hU
    have hsup : LinearMap.ker (crossUL (qU r (c, τ))) ⊔ K' = ⊤ :=
      codisjoint_iff.mp hK'.codisjoint
    have hinf : LinearMap.ker (crossUL (qU r (c, τ))) ⊓ K' = ⊥ :=
      disjoint_iff.mp hK'.disjoint
    have h1 := Submodule.finrank_sup_add_finrank_inf_eq
      (LinearMap.ker (crossUL (qU r (c, τ)))) K'
    rw [hsup, hinf, hker, finrank_top, finrank_bot] at h1
    have hdim : Module.finrank ℝ Space = 3 := by simp [Space]
    rw [hdim] at h1
    omega
  have hK'inj : ∀ p : K', crossUL (qU r (c, τ)) (p : Space) = 0 → p = 0 := by
    intro p hp
    have hmem : (p : Space) ∈ LinearMap.ker (crossUL (qU r (c, τ))) ⊓ K' := ⟨hp, p.2⟩
    rw [disjoint_iff.mp hK'.disjoint] at hmem
    exact Subtype.ext ((Submodule.mem_bot ℝ).mp hmem)
  let dirV : Space →ₗ[ℝ] Coeff := slotDir g0 2
  let dirS : Space →ₗ[ℝ] Coeff := slotDir g0 3
  let phi : K' × K' × ℝ →ₗ[ℝ] Coeff × QP :=
    (((dirV.comp K'.subtype).comp (LinearMap.fst ℝ K' (K' × ℝ)))
        + ((dirS.comp K'.subtype).comp ((LinearMap.fst ℝ K' ℝ).comp
            (LinearMap.snd ℝ K' (K' × ℝ))))
        + ((LinearMap.toSpanSingleton ℝ Coeff dc).comp ((LinearMap.snd ℝ K' ℝ).comp
            (LinearMap.snd ℝ K' (K' × ℝ))))).prod 0
  have hphi : ∀ w : K' × K' × ℝ, phi w
      = ((dirV (w.1 : Space) + dirS (w.2.1 : Space) + w.2.2 • dc, (0 : QP)) : Coeff × QP) := by
    intro w
    simp [phi, dirV, dirS, LinearMap.toSpanSingleton]
  have hcoef0 : (fderiv ℝ (fun q : Coeff × QP => triplet r q) (c, τ))
      ((dc, (0 : QP)) : Coeff × QP) = 0 :=
    fderiv_triplet_coeff_eq_zero hr hdc_val
  have hdirV1 : ∀ p : Space,
      ((fderiv ℝ (fun q : Coeff × QP => triplet r q) (c, τ))
        ((dirV p, (0 : QP)) : Coeff × QP)).1 = crossUL (qU r (c, τ)) p :=
    fun p => fderiv_triplet_dirV_fst hr (c, τ) hg0 p
  have hdirV2 : ∀ p : Space,
      ((fderiv ℝ (fun q : Coeff × QP => triplet r q) (c, τ))
        ((dirV p, (0 : QP)) : Coeff × QP)).2.1 = 0 :=
    fun p => fderiv_triplet_dirV_snd hr (c, τ) hg0 p
  have hdirS1 : ∀ p : Space,
      ((fderiv ℝ (fun q : Coeff × QP => triplet r q) (c, τ))
        ((dirS p, (0 : QP)) : Coeff × QP)).1 = 0 :=
    fun p => fderiv_triplet_dirS_fst hr (c, τ) hg0 p
  have hdirS2 : ∀ p : Space,
      ((fderiv ℝ (fun q : Coeff × QP => triplet r q) (c, τ))
        ((dirS p, (0 : QP)) : Coeff × QP)).2.1 = crossUL (qU r (c, τ)) p :=
    fun p => fderiv_triplet_dirS_snd hr (c, τ) hg0 p
  have hdc1 : ∀ s : ℝ,
      ((fderiv ℝ (fun q : Coeff × QP => triplet r q) (c, τ))
        ((s • dc, (0 : QP)) : Coeff × QP)).1 = 0 := by
    intro s
    have h1 : ((s • dc, (0 : QP)) : Coeff × QP) = s • ((dc, (0 : QP)) : Coeff × QP) := by
      ext <;> simp
    rw [h1, map_smul, hcoef0, smul_zero]
    rfl
  have hdc2 : ∀ s : ℝ,
      ((fderiv ℝ (fun q : Coeff × QP => triplet r q) (c, τ))
        ((s • dc, (0 : QP)) : Coeff × QP)).2.1 = 0 := by
    intro s
    have h1 : ((s • dc, (0 : QP)) : Coeff × QP) = s • ((dc, (0 : QP)) : Coeff × QP) := by
      ext <;> simp
    rw [h1, map_smul, hcoef0, smul_zero]
    rfl
  have hcomp1 : ∀ w : K' × K' × ℝ,
      (D (phi w)).1.1 = crossUL (qU r (c, τ)) (w.1 : Space) := by
    intro w
    have hsp : phi w = ((dirV (w.1 : Space), (0 : QP)) + (dirS (w.2.1 : Space), (0 : QP))
        + ((w.2.2 • dc, (0 : QP)) : Coeff × QP)) := by
      rw [hphi w]
      ext <;> simp
    rw [hDfst (phi w), hsp, map_add, map_add]
    simp only [Prod.fst_add]
    rw [hdirV1, hdirS1, hdc1]
    simp
  have hcomp2 : ∀ w : K' × K' × ℝ,
      (D (phi w)).1.2.1 = crossUL (qU r (c, τ)) (w.2.1 : Space) := by
    intro w
    have hsp : phi w = ((dirV (w.1 : Space), (0 : QP)) + (dirS (w.2.1 : Space), (0 : QP))
        + ((w.2.2 • dc, (0 : QP)) : Coeff × QP)) := by
      rw [hphi w]
      ext <;> simp
    rw [hDfst (phi w), hsp, map_add, map_add]
    simp only [Prod.snd_add, Prod.fst_add]
    rw [hdirV2, hdirS2, hdc2]
    simp
  have hker : ∀ w : K' × K' × ℝ, (D.comp phi) w = 0 → w = 0 := by
    intro w hw
    have hDw : D (phi w) = 0 := hw
    have hw1 : w.1 = 0 := by
      refine hK'inj w.1 ?_
      have h1 : (D (phi w)).1.1 = 0 := by rw [hDw]; rfl
      rw [hcomp1 w] at h1
      exact h1
    have hw2 : w.2.1 = 0 := by
      refine hK'inj w.2.1 ?_
      have h1 : (D (phi w)).1.2.1 = 0 := by rw [hDw]; rfl
      rw [hcomp2 w] at h1
      exact h1
    have hw3 : w.2.2 = 0 := by
      have hphiz : phi w = ((w.2.2 • dc, (0 : QP)) : Coeff × QP) := by
        rw [hphi w, hw1, hw2]
        simp
      have h4 : D (((w.2.2 • dc, (0 : QP)) : Coeff × QP)) = 0 := by
        rw [← hphiz, hDw]
      rw [show (((w.2.2 • dc, (0 : QP)) : Coeff × QP))
          = w.2.2 • ((dc, (0 : QP)) : Coeff × QP) from by ext <;> simp, map_smul] at h4
      rcases smul_eq_zero.mp h4 with h | h
      · exact h
      · exact absurd h hDdc
    exact Prod.ext hw1 (Prod.ext hw2 hw3)
  have hinj : Function.Injective (D.comp phi) := by
    intro u v huv
    have h0 : (D.comp phi) (u - v) = 0 := by rw [map_sub, huv, sub_self]
    exact sub_eq_zero.mp (hker (u - v) h0)
  have hfin5 : Module.finrank ℝ (K' × K' × ℝ) = 5 := by
    rw [Module.finrank_prod, Module.finrank_prod, hK'2, Module.finrank_self]
  have hrank : Module.finrank ℝ (LinearMap.range (D.comp phi))
      = Module.finrank ℝ (K' × K' × ℝ) := by
    have h := LinearMap.finrank_range_add_finrank_ker (D.comp phi)
    rw [LinearMap.ker_eq_bot.mpr hinj, finrank_bot, add_zero] at h
    exact h
  have hmono : Module.finrank ℝ (LinearMap.range (D.comp phi))
      ≤ Module.finrank ℝ (LinearMap.range D) :=
    Submodule.finrank_mono (LinearMap.range_comp_le_range phi D)
  rw [← hfin5, ← hrank]
  exact hmono


end Work.Drive
