import Mathlib
import Submission.Work.Mostow.cuspDefs
import Submission.Work.Mostow.Hyper
import Submission.Work.Mostow.BaryBase
import Submission.Work.Mostow.ematFix
import Submission.Work.Mostow.ematSpec
import Submission.Work.Mostow.eigNull
import Submission.Work.Mostow.eigRecip
import Submission.Work.Mostow.deepCusp
import Submission.Work.Mostow.cruxFixedPoint
import Submission.Work.Mostow.pairStabDefs
import Submission.Work.Mostow.bdFixIff
import Submission.Work.Mostow.poAux

/-!
# Two fixed boundary points of a loxodromic `PO(n,1)`-element

`Work.Mostow.cuspTwoFixed`: an isometry `g` of `ℍⁿ` (`n ≥ 3`) with no fixed point in `ℍⁿ` and
displacement bounded below by a positive constant fixes **two distinct** points of the boundary
sphere, and the Busemann cocycle of the first of them does not vanish.

The classification input is assembled from the matrix (Lorentz) model:

* `cruxFixedPoint` gives one boundary fixed point `ξ`;
* the hypothesis `∃ δ > 0, δ ≤ hdist u (g • u)` rules out the parabolic case: by `deepCusp`, `g`
  cannot preserve the Busemann function of a fixed point `ξ`, whence the Busemann cocycle
  `busemann ξ (g • 0)` is non-zero;
* an eigenvector `θ ξ = (ξ,1)` of the lift `emat g` has eigenvalue `lam`, and
  `lev_emat_eigen` computes it: `busemann ξ (g • 0) = - log lam`, with `lam > 0`.  Hence
  `lam ≠ 1`, so `lam ^ 2 ≠ 1`.
* `J`-orthogonality of the lift (`emat_isJOrth`) produces an eigenvector `w ≠ 0` for the
  reciprocal eigenvalue `lam⁻¹` (`exists_eigen_inv`), and `mform_self_eq_zero_of_eigen` shows
  `w` is null.  A non-zero null vector with non-zero time coordinate is a multiple of some
  `θ η` (`exists_sph_eq_smul_theta`), so `η ∈ Sph n` is a second fixed point, distinct from `ξ`
  because the two eigen-vectors have distinct eigenvalues.
-/

namespace Work.Mostow

open LeanEval.Geometry.MostowRigidity Submission.Mostow MeasureTheory
open Matrix

noncomputable section

variable {n : ℕ}

/-! ## Eigenvector lemmas for a `J`-orthogonal matrix -/

/-- A non-zero eigenvector of a Minkowski-isometry for an eigenvalue `lam` with
`lam ^ 2 ≠ 1` is a **null** vector. -/
lemma mform_self_eq_zero_of_eigen {M : Matrix (Fin n ⊕ Fin 1) (Fin n ⊕ Fin 1) ℝ}
    (hM : ∀ x y : Fin n ⊕ Fin 1 → ℝ, mform (M *ᵥ x) (M *ᵥ y) = mform x y)
    (lam : ℝ) (v : Fin n ⊕ Fin 1 → ℝ) (hv : v ≠ 0)
    (heig : M *ᵥ v = lam • v) (hlam : lam ^ 2 ≠ 1) : mform v v = 0 := by
  have hpair : mform v v = lam * lam * mform v v :=
    calc mform v v = mform (M *ᵥ v) (M *ᵥ v) := (hM v v).symm
      _ = mform (lam • v) (lam • v) := by rw [heig]
      _ = lam * lam * mform v v := mform_smul lam lam v v
  have hne : lam * lam - 1 ≠ 0 := fun h => hlam (by rw [pow_two]; exact sub_eq_zero.mp h)
  have hzero : (lam * lam - 1) * mform v v = 0 := by nlinarith [hpair]
  rcases mul_eq_zero.mp hzero with h | h
  · exact absurd h hne
  · exact h

private lemma charpoly_eval_eq_det_cusp {ι : Type*} [Fintype ι] [DecidableEq ι]
    (M : Matrix ι ι ℝ) (t : ℝ) : M.charpoly.eval t = (t • 1 - M).det := by
  rw [Matrix.eval_charpoly, Matrix.scalar_apply, ← Matrix.smul_one_eq_diagonal]

/-- Eigenvalues of a `J`-orthogonal matrix occur in reciprocal pairs: if `lam` is an eigenvalue
with a non-zero eigenvector, so is `lam⁻¹`. -/
lemma exists_eigen_inv (M : Matrix (Fin n ⊕ Fin 1) (Fin n ⊕ Fin 1) ℝ) (hO : IsJOrth M)
    (lam : ℝ) (h : ∃ v : Fin n ⊕ Fin 1 → ℝ, v ≠ 0 ∧ M *ᵥ v = lam • v) :
    ∃ w : Fin n ⊕ Fin 1 → ℝ, w ≠ 0 ∧ M *ᵥ w = lam⁻¹ • w := by
  obtain ⟨v, hv, hvev⟩ := h
  have hJJm : Mᵀ * (pmOneMat (p := Fin n) (q := Fin 1) (α := ℝ)) * M
      = pmOneMat (p := Fin n) (q := Fin 1) (α := ℝ) := hO
  set J : Matrix (Fin n ⊕ Fin 1) (Fin n ⊕ Fin 1) ℝ :=
    pmOneMat (p := Fin n) (q := Fin 1) (α := ℝ) with hJdef
  have hJJ : J * J = 1 := by
    rw [hJdef]
    exact pmOneMat_mul_pmOneMat (Fin n) (Fin 1) ℝ
  have hJ' : Mᵀ * J * M = J := by
    rw [hJdef]
    exact hJJm
  have hx : J *ᵥ v ≠ 0 := by
    intro hz
    have h2 : v = 0 := by
      have h3 : J *ᵥ (J *ᵥ v) = 0 := by rw [hz, Matrix.mulVec_zero]
      rwa [Matrix.mulVec_mulVec, hJJ, Matrix.one_mulVec] at h3
    exact hv h2
  have hrel : lam • (Mᵀ *ᵥ (J *ᵥ v)) = J *ᵥ v := by
    have h4 : (Mᵀ * J * M) *ᵥ v = J *ᵥ v := by rw [hJ']
    rw [← Matrix.mulVec_mulVec, ← Matrix.mulVec_mulVec] at h4
    simp only [hvev, Matrix.mulVec_smul] at h4
    exact h4
  have hlam : lam ≠ 0 := by
    intro h0
    refine hx ?_
    rw [← hrel, h0, zero_smul]
  have htrans : Mᵀ *ᵥ (J *ᵥ v) = lam⁻¹ • (J *ᵥ v) := by
    have h5 := congrArg (fun z : Fin n ⊕ Fin 1 → ℝ => lam⁻¹ • z) hrel
    simpa only [smul_smul, inv_mul_cancel₀ hlam, one_smul] using h5
  have hker : (lam⁻¹ • 1 - Mᵀ) *ᵥ (J *ᵥ v) = 0 := by
    rw [Matrix.sub_mulVec, Matrix.smul_mulVec, Matrix.one_mulVec, htrans, sub_self]
  have hdetT : (lam⁻¹ • 1 - Mᵀ).det = 0 :=
    (Matrix.exists_mulVec_eq_zero_iff (M := lam⁻¹ • 1 - Mᵀ)).mp ⟨J *ᵥ v, hx, hker⟩
  have hdet : (lam⁻¹ • 1 - M).det = 0 := by
    have hh := hdetT
    rw [← charpoly_eval_eq_det_cusp Mᵀ lam⁻¹, Matrix.charpoly_transpose M,
      charpoly_eval_eq_det_cusp M lam⁻¹] at hh
    exact hh
  obtain ⟨w, hw, hw0⟩ :=
    (Matrix.exists_mulVec_eq_zero_iff (M := lam⁻¹ • 1 - M)).mpr hdet
  refine ⟨w, hw, ?_⟩
  have hsub : lam⁻¹ • w - M *ᵥ w = 0 := by
    simpa only [Matrix.sub_mulVec, Matrix.smul_mulVec, Matrix.one_mulVec] using hw0
  exact (sub_eq_zero.mp hsub).symm

/-- The lift `emat g` preserves the Minkowski form. -/
lemma mform_emat_mink (g : PO n 1) (x y : Fin n ⊕ Fin 1 → ℝ) :
    mform (emat g *ᵥ x) (emat g *ᵥ y) = mform x y := mform_emat g x y

/-! ## Non-zero null vectors are positive multiples of `θ η` -/

/-- A non-zero null vector with vanishing time coordinate does not exist
(`eq_zero_of_mform_self_eq_zero`); consequently a non-zero null vector is a positive multiple of
`θ η` for a unique boundary point `η ∈ Sph n`. -/
lemma exists_sph_eq_smul_theta (w : Fin n ⊕ Fin 1 → ℝ) (hw : w ≠ 0) (hww : mform w w = 0) :
    ∃ η : E n, η ∈ Sph n ∧ w (Sum.inr 0) ≠ 0 ∧ w = w (Sum.inr 0) • theta η := by
  have ht : w (Sum.inr 0) ≠ 0 := fun h0 => hw (eq_zero_of_mform_self_eq_zero w hww h0)
  set η : E n := WithLp.toLp 2 (fun i : Fin n => w (Sum.inl i) / w (Sum.inr 0)) with hηdef
  refine ⟨η, ?_, ht, ?_⟩
  · rw [mem_Sph_iff]
    have hsm : w = w (Sum.inr 0) • theta η := by
      rw [hηdef]
      exact smul_theta_of_time_ne_zero w ht
    have h1 : w (Sum.inr 0) * w (Sum.inr 0) * (‖η‖ ^ 2 - 1) = 0 := by
      have h2 : mform (w (Sum.inr 0) • theta η) (w (Sum.inr 0) • theta η) = 0 := by
        rw [← hsm]
        exact hww
      rwa [mform_smul, theta_self] at h2
    rcases mul_eq_zero.mp h1 with h2 | h2
    · rcases mul_eq_zero.mp h2 with h3 | h3 <;> exact absurd h3 ht
    · have h4 : ‖η‖ ^ 2 = 1 := by linarith
      rcases sq_eq_one_iff.mp h4 with h5 | h5
      · exact h5
      · have h6 := norm_nonneg η; linarith
  · exact smul_theta_of_time_ne_zero w ht

/-! ## The main theorem -/

theorem cuspTwoFixed (n : ℕ) (hn : 3 ≤ n) (hA : POActionProp n) (hI : HypIsometryProp n)
    (g : PO n 1) (hne : ∀ u : E n, g • u ≠ u)
    (hpos : ∃ δ : ℝ, 0 < δ ∧ ∀ u : E n, δ ≤ hdist u (g • u)) :
    ∃ ξ η : E n, ξ ∈ Sph n ∧ η ∈ Sph n ∧ ξ ≠ η ∧ bd g ξ = ξ ∧ bd g η = η ∧
      busemann ξ (g • (0 : E n)) ≠ 0 := by
  obtain ⟨δ, hδ0, hδ⟩ := hpos
  have hId : HypIsoData n := HypIsoData.ofProp hI
  -- (1) a boundary fixed point
  obtain ⟨ξ, hξS, hξfix⟩ := cruxFixedPoint n (by omega) hA hI g hne ⟨δ, hδ0, hδ⟩
  -- (2) the Busemann cocycle at `ξ` is non-zero (else `deepCusp` gives small displacement)
  have hbus : busemann ξ (g • (0 : E n)) ≠ 0 := by
    intro h0
    have hpres : ∀ u : E n, busemann ξ (g • u) = busemann ξ u := by
      intro u
      have h := hId.busemann_cocycle g ξ u hξS
      rw [hξfix] at h
      rw [h, h0, add_zero]
    obtain ⟨u, hu⟩ := deepCusp n (by omega) hA hI g ξ hξS hξfix hpres (δ / 2) (by linarith)
    have hdu := hδ u
    linarith
  -- (3) the eigenvalue of the lift on `θ ξ`
  obtain ⟨lam, _hlam0, hlameig⟩ := emat_eigen_of_bd g hξS hξfix
  obtain ⟨_hlev, hlampos, hbuslog⟩ := lev_emat_eigen g hξS hlameig
  have hlam1 : lam ≠ 1 := by
    intro h
    rw [h, Real.log_one, neg_zero] at hbuslog
    exact hbus hbuslog
  have hlam_sq : lam ^ 2 ≠ 1 := by
    intro h
    rcases sq_eq_one_iff.mp h with h1 | h1
    · exact hlam1 h1
    · linarith
  have hlinv_sq : lam⁻¹ ^ 2 ≠ 1 := by
    intro h
    rcases sq_eq_one_iff.mp h with h1 | h1
    · refine hlam1 ?_
      have h3 := congrArg (fun x : ℝ => lam * x) h1
      rw [mul_inv_cancel₀ (ne_of_gt hlampos), mul_one] at h3
      exact h3.symm
    · have h3 := congrArg (fun x : ℝ => lam * x) h1
      rw [mul_inv_cancel₀ (ne_of_gt hlampos), mul_neg, mul_one] at h3
      linarith
  -- (4) the reciprocal eigenvalue and its null eigenvector `w`
  obtain ⟨w, hw0, hweig⟩ :=
    exists_eigen_inv (emat g) (emat_isJOrth g) lam ⟨theta ξ, nvec_ne_zero ξ, hlameig⟩
  have hww : mform w w = 0 :=
    mform_self_eq_zero_of_eigen (mform_emat_mink g) lam⁻¹ w hw0 hweig hlinv_sq
  -- (5) the corresponding boundary point `η`
  obtain ⟨η, hηS, ht, hwη⟩ := exists_sph_eq_smul_theta w hw0 hww
  have heta : emat g *ᵥ theta η = lam⁻¹ • theta η := by
    have h1 : emat g *ᵥ (w (Sum.inr 0) • theta η) = lam⁻¹ • (w (Sum.inr 0) • theta η) := by
      rw [← hwη]
      exact hweig
    rw [Matrix.mulVec_smul, smul_smul] at h1
    have h3 := congrArg (fun z : Fin n ⊕ Fin 1 → ℝ => (w (Sum.inr 0))⁻¹ • z) h1
    rw [smul_smul, smul_smul, inv_mul_cancel₀ ht, one_smul] at h3
    have h4 : (w (Sum.inr 0))⁻¹ * (lam⁻¹ * w (Sum.inr 0)) = lam⁻¹ := by
      rw [mul_comm lam⁻¹ (w (Sum.inr 0)), ← mul_assoc, inv_mul_cancel₀ ht, one_mul]
    rw [h4] at h3
    exact h3
  have hηfix : bd g η = η :=
    (bdFixIff n (by omega) hA g η hηS).mpr
      ⟨lam⁻¹, inv_ne_zero (ne_of_gt hlampos), heta⟩
  -- (6) the two points differ
  have hξη : ξ ≠ η := by
    intro h
    have heta' : emat g *ᵥ theta ξ = lam⁻¹ • theta ξ := by
      rw [h]
      exact heta
    have heq : lam • theta ξ = lam⁻¹ • theta ξ := hlameig.symm.trans heta'
    have hs : (lam - lam⁻¹) • theta ξ = 0 := by
      rw [sub_smul, sub_eq_zero]
      exact heq
    have hlam_eq : lam = lam⁻¹ := by
      rcases smul_eq_zero.mp hs with h2 | h2
      · exact sub_eq_zero.mp h2
      · exact absurd h2 (nvec_ne_zero ξ)
    have : lam ^ 2 = 1 := by
      have h3 := congrArg (fun x : ℝ => lam * x) hlam_eq
      rw [mul_inv_cancel₀ (ne_of_gt hlampos)] at h3
      rw [pow_two]
      exact h3
    exact hlam_sq this
  exact ⟨ξ, η, hξS, hηS, hξη, hξfix, hηfix, hbus⟩

end

end Work.Mostow
