import Mathlib
import Submission.Work.Mostow.homoExtAux

/-!
# Conformality of the boundary action `phiFun g` on the unit sphere

`phiFun g ξ = (sMat g *ᵥ (ξ,1))_sp / dfun g ξ` is the explicit chart formula for the boundary
action `bd g` on `Sph n` (it agrees with `bd g` there).  This file proves that its Fréchet
derivative at a point `ξ` of the unit sphere is a **similarity onto the tangent space**: for every
vector `h` tangent to the sphere at `ξ` (i.e. `⟪ξ,h⟫ = 0`),

  `⟪phiFun g ξ, d(phiFun g)_ξ h⟫ = 0`  and  `‖d(phiFun g)_ξ h‖ = ‖h‖ / dfun g ξ`.

This is the conformality of the Möbius action of `PO(n,1)` on the boundary sphere, in the form
needed by the Jacobian computation for the homogeneous extension `homoExt g`
(see `Submission.Work.Mostow.homoExtJac`).

## Proof outline

Everything is linear algebra with the Minkowski form `⟨x,y⟩ = Σ xᵢyᵢ − x₀y₀` on `ℝ^{n+1}`
(`Hyper.mink`).  Write `A = sMat g`, so that `wvec_visualDefs g x = A *ᵥ (x,1)` and
`phiFun g x = (A *ᵥ (x,1))_sp / (A *ᵥ (x,1))_t`.  For the *chart-linear* part
`hv0 v = (v,0)` define `Sp v = (A *ᵥ (v,0))_sp` and `T v = (A *ᵥ (v,0))_t`; these are
continuous linear maps `linSp g` and `linT g`.  The derivative of `phiFun g` at `ξ` is

  `d(phiFun g)_ξ v = (dfun g ξ)⁻¹ • Sp v − (T v) • ((dfun g ξ)⁻¹ • phiFun g ξ)`,

written `dPhi g ξ`.

Since `A` preserves `⟨·,·⟩` and `⟨(ξ,1),(h,0)⟩ = ⟪ξ,h⟫ = 0` (hypothesis), the vectors
`X = A *ᵥ (ξ,1)` and `Y = A *ᵥ (h,0)` satisfy `⟨X,Y⟩ = 0` and `⟨Y,Y⟩ = ‖h‖²`.  Reading these
Minkowski identities in terms of `Sp`, `T`, `dfun` and `phiFun` (note `(A *ᵥ (ξ,1))_sp = dfun g ξ • phiFun g ξ`)
gives exactly

  `⟪phiFun g ξ, Sp h⟫ = T h`  and  `‖Sp h‖² − (T h)² = ‖h‖²`,

and the two claimed identities follow by a short algebraic computation.
-/

namespace Work.Mostow

open Submission.Mostow LeanEval.Geometry.MostowRigidity MeasureTheory

noncomputable section

/-- The chart-linear lift `v ↦ (v,0)` of a tangent vector to `ℝ^{n+1}`, with zero time component. -/
private def phiCf_hv0 {n : ℕ} (v : E n) : Fin n ⊕ Fin 1 → ℝ :=
  Sum.elim (fun i => v i) (fun _ => 0)

/-- The `k`-th column of the spatial block `(sMat g) k (inl ·)`, as a vector of `E n`. -/
private def phiCf_Acol {n : ℕ} (g : PO n 1) (k : Fin n ⊕ Fin 1) : E n :=
  WithLp.toLp 2 (fun i : Fin n => (sMat g) k (Sum.inl i))

/-- The spatial part of the chart-linear action: `v ↦ (sMat g *ᵥ (v,0))_sp`. -/
private def phiCf_linSp {n : ℕ} (g : PO n 1) : E n →L[ℝ] E n :=
  (PiLp.continuousLinearEquiv 2 ℝ (fun _ : Fin n => ℝ)).symm.toContinuousLinearMap ∘L
    (ContinuousLinearMap.pi (fun i : Fin n => innerSL ℝ (phiCf_Acol g (Sum.inl i))))

/-- The time part of the chart-linear action: `v ↦ (sMat g *ᵥ (v,0))_t`. -/
private def phiCf_linT {n : ℕ} (g : PO n 1) : E n →L[ℝ] ℝ :=
  innerSL ℝ (phiCf_Acol g (Sum.inr 0))

/-- The derivative of the `i`-th coordinate of `phiFun g` at `ξ`. -/
private def phiCf_dPhiCoord {n : ℕ} (g : PO n 1) (ξ : E n) (i : Fin n) : E n →L[ℝ] ℝ :=
  (wvec_visualDefs g ξ (Sum.inl i)) • ((-((dfun g ξ) ^ 2)⁻¹) • innerSL ℝ (phiCf_Acol g (Sum.inr 0)))
    + (dfun g ξ)⁻¹ • innerSL ℝ (phiCf_Acol g (Sum.inl i))

/-- The Fréchet derivative of `phiFun g` at `ξ`, as an explicit continuous linear map. -/
private def phiCf_dPhi {n : ℕ} (g : PO n 1) (ξ : E n) : E n →L[ℝ] E n :=
  (dfun g ξ)⁻¹ • phiCf_linSp g -
    ContinuousLinearMap.smulRight (phiCf_linT g) ((dfun g ξ)⁻¹ • phiFun g ξ)

/-- Each entry of `sMat g` on a spatial column. -/
private lemma phiCf_Acol_apply {n : ℕ} (g : PO n 1) (k : Fin n ⊕ Fin 1) (i : Fin n) :
    (phiCf_Acol g k) i = (sMat g) k (Sum.inl i) := by
  simp [phiCf_Acol]

/-- `wvec_visualDefs g · k` is an affine function of `x` whose linear part is `⟪phiCf_Acol g k, ·⟫`. -/
private lemma phiCf_wvec_coord_eq {n : ℕ} (g : PO n 1) (x : E n) (k : Fin n ⊕ Fin 1) :
    wvec_visualDefs g x k = (innerSL ℝ (phiCf_Acol g k)) x + (wvec_visualDefs g 0) k := by
  have h1 : wvec_visualDefs g x k = inner ℝ (phiCf_Acol g k) x + (sMat g) k (Sum.inr 0) := by
    rw [wvec_visualDefs, Matrix.mulVec, dotProduct, Fintype.sum_sum_type, Fin.sum_univ_one]
    simp only [hvec, Sum.elim_inl, Sum.elim_inr, mul_one]
    rw [Hyper.inner_eq_sum]
    simp only [phiCf_Acol, PiLp.toLp_apply]
  have h2 : wvec_visualDefs g 0 k = (sMat g) k (Sum.inr 0) := by
    rw [wvec_visualDefs, Matrix.mulVec, dotProduct, Fintype.sum_sum_type, Fin.sum_univ_one]
    simp [hvec]
  rw [h1, h2, innerSL_apply_apply]

/-- The derivative of a coordinate of `wvec_visualDefs g`. -/
private lemma phiCf_hasFDerivAt_wvec_coord {n : ℕ} (g : PO n 1) (ξ : E n)
    (k : Fin n ⊕ Fin 1) :
    HasFDerivAt (fun x => wvec_visualDefs g x k) (innerSL ℝ (phiCf_Acol g k)) ξ := by
  have h : HasFDerivAt (fun x : E n => (innerSL ℝ (phiCf_Acol g k)) x + (wvec_visualDefs g 0) k)
      (innerSL ℝ (phiCf_Acol g k)) ξ :=
    ((innerSL ℝ (phiCf_Acol g k)).hasFDerivAt (x := ξ)).add_const ((wvec_visualDefs g 0) k)
  convert h using 1
  ext x
  exact phiCf_wvec_coord_eq g x k

/-- The derivative of `(dfun g ·)⁻¹`. -/
private lemma phiCf_hasFDerivAt_dfun_inv {n : ℕ} (g : PO n 1) (ξ : E n)
    (hD : dfun g ξ ≠ 0) :
    HasFDerivAt (fun x => (dfun g x)⁻¹)
      ((-((dfun g ξ) ^ 2)⁻¹) • innerSL ℝ (phiCf_Acol g (Sum.inr 0))) ξ := by
  have hden : HasFDerivAt (fun x => dfun g x) (innerSL ℝ (phiCf_Acol g (Sum.inr 0))) ξ :=
    phiCf_hasFDerivAt_wvec_coord g ξ (Sum.inr 0)
  have hcomp := (hasFDerivAt_inv (𝕜 := ℝ) (x := dfun g ξ) hD).comp ξ hden
  have hfun : ((fun y : ℝ => y⁻¹) ∘ fun x => dfun g x) = fun x => (dfun g x)⁻¹ := rfl
  rw [hfun] at hcomp
  convert hcomp using 1
  ext v
  simp [ContinuousLinearMap.toSpanSingleton_apply, mul_comm]

/-- The `i`-th coordinate of `linSp g` is `(phiCf_Acol g (inl i))` tested against the argument. -/
private lemma phiCf_linSp_apply_coord {n : ℕ} (g : PO n 1) (v : E n) (i : Fin n) :
    (phiCf_linSp g v) i = (innerSL ℝ (phiCf_Acol g (Sum.inl i))) v := by
  simp [phiCf_linSp, PiLp.continuousLinearEquiv_symm_apply]

/-- Definitional unfolding of `phiCf_linT`. -/
private lemma phiCf_linT_apply {n : ℕ} (g : PO n 1) (v : E n) :
    phiCf_linT g v = (innerSL ℝ (phiCf_Acol g (Sum.inr 0))) v := rfl

/-- Explicit coordinate formula for the chart boundary map. -/
private lemma phiCf_phiFun_coord {n : ℕ} (g : PO n 1) (x : E n) (i : Fin n) :
    (phiFun g x) i = wvec_visualDefs g x (Sum.inl i) / dfun g x := by
  simp [phiFun, dfun, PiLp.toLp_apply]

/-- The derivative of a coordinate of `phiFun g`. -/
private lemma phiCf_hasFDerivAt_phiCoord {n : ℕ} (g : PO n 1) (ξ : E n)
    (hD : dfun g ξ ≠ 0) (i : Fin n) :
    HasFDerivAt (fun x => phiFun g x i) (phiCf_dPhiCoord g ξ i) ξ := by
  have hnum : HasFDerivAt (fun x => wvec_visualDefs g x (Sum.inl i))
      (innerSL ℝ (phiCf_Acol g (Sum.inl i))) ξ :=
    phiCf_hasFDerivAt_wvec_coord g ξ (Sum.inl i)
  have hinv := phiCf_hasFDerivAt_dfun_inv g ξ hD
  have hmul := hnum.mul hinv
  convert hmul using 1
  · ext x
    simp [phiFun, div_eq_mul_inv]
  · simp only [phiCf_dPhiCoord, smul_smul]

/-- Value of `phiCf_dPhi`. -/
private lemma phiCf_dPhi_apply {n : ℕ} (g : PO n 1) (ξ v : E n) :
    phiCf_dPhi g ξ v =
      (dfun g ξ)⁻¹ • (phiCf_linSp g v) - (phiCf_linT g v) • ((dfun g ξ)⁻¹ • phiFun g ξ) := by
  simp [phiCf_dPhi]

/-- `phiCf_dPhiCoord g ξ i` is the `i`-th coordinate of `phiCf_dPhi g ξ`. -/
private lemma phiCf_dPhiCoord_eq_proj {n : ℕ} (g : PO n 1) (ξ : E n) (i : Fin n) :
    phiCf_dPhiCoord g ξ i = (PiLp.proj 2 (fun _ : Fin n => ℝ) i) ∘SL (phiCf_dPhi g ξ) := by
  ext v
  rw [ContinuousLinearMap.comp_apply, PiLp.proj_apply, phiCf_dPhi_apply]
  simp only [WithLp.ofLp_sub, WithLp.ofLp_smul, phiCf_phiFun_coord, phiCf_linSp_apply_coord,
    phiCf_linT_apply, phiCf_dPhiCoord, smul_apply, ContinuousLinearMap.smulRight_apply,
    innerSL_apply_apply, ContinuousLinearMap.add_apply, Pi.sub_apply, Pi.smul_apply]
  ring

/-- Coordinate formula for `WithLp.toLp 2` composed with the linear equivalence. -/
private lemma phiCf_symm_toLp_ofLp_apply {n : ℕ} (w : Fin n → ℝ) (i : Fin n) :
    (((PiLp.continuousLinearEquiv 2 ℝ (fun _ : Fin n => ℝ)).symm.toContinuousLinearMap) w).ofLp i
      = w i := by
  change ((PiLp.continuousLinearEquiv 2 ℝ (fun _ : Fin n => ℝ)).symm w).ofLp i = w i
  rw [PiLp.continuousLinearEquiv_symm_apply, WithLp.ofLp_toLp]

/-- The assembled derivative of the coordinatewise description is `phiCf_dPhi g ξ`. -/
private lemma phiCf_dPhi_eq_symm_pi {n : ℕ} (g : PO n 1) (ξ : E n) :
    (PiLp.continuousLinearEquiv 2 ℝ (fun _ : Fin n => ℝ)).symm.toContinuousLinearMap ∘SL
      (ContinuousLinearMap.pi (fun i : Fin n => phiCf_dPhiCoord g ξ i)) = phiCf_dPhi g ξ := by
  ext v i
  have h1 : (((PiLp.continuousLinearEquiv 2 ℝ (fun _ : Fin n => ℝ)).symm.toContinuousLinearMap)
      ((ContinuousLinearMap.pi (fun i => phiCf_dPhiCoord g ξ i)) v)).ofLp i
      = phiCf_dPhiCoord g ξ i v := by
    rw [phiCf_symm_toLp_ofLp_apply, ContinuousLinearMap.pi_apply]
  have h2 : ((phiCf_dPhi g ξ) v).ofLp i = phiCf_dPhiCoord g ξ i v := by
    have := congrArg (fun (L : E n →L[ℝ] ℝ) => L v) (phiCf_dPhiCoord_eq_proj g ξ i)
    simpa [ContinuousLinearMap.comp_apply, PiLp.proj_apply] using this.symm
  rw [ContinuousLinearMap.comp_apply, h1, h2]

/-- **The derivative of `phiFun g`.** -/
private lemma phiCf_hasFDerivAt_phiFun {n : ℕ} (g : PO n 1) (ξ : E n)
    (hd : dfun g ξ ≠ 0) :
    HasFDerivAt (phiFun g) (phiCf_dPhi g ξ) ξ := by
  have hcoord : ∀ i : Fin n, HasFDerivAt (fun x => phiFun g x i) (phiCf_dPhiCoord g ξ i) ξ :=
    fun i => phiCf_hasFDerivAt_phiCoord g ξ hd i
  have hpi : HasFDerivAt (fun x => fun i => phiFun g x i)
      (ContinuousLinearMap.pi (fun i : Fin n => phiCf_dPhiCoord g ξ i)) ξ :=
    hasFDerivAt_pi.mpr hcoord
  have htoLp := PiLp.hasFDerivAt_toLp (𝕜 := ℝ) (E := fun _ : Fin n => ℝ) 2
    (fun i : Fin n => phiFun g ξ i)
  have hcomp := htoLp.comp ξ hpi
  rw [phiCf_dPhi_eq_symm_pi] at hcomp
  convert hcomp using 1
  ext x i
  simp

/-! ## Minkowski-form identities -/

/-- The Minkowski form through the spatial part and the time coordinate. -/
private lemma phiCf_mink_eq_inner_sub {n : ℕ} (x y : Fin n ⊕ Fin 1 → ℝ) :
    Hyper.mink x y = inner ℝ (Hyper.spat x) (Hyper.spat y) - x (Sum.inr 0) * y (Sum.inr 0) := by
  rw [Hyper.mink_apply, Hyper.inner_eq_sum]
  simp only [Hyper.spat, PiLp.toLp_apply]

/-- The spatial part of `wvec_visualDefs g ξ` is `dfun g ξ • phiFun g ξ`. -/
private lemma phiCf_spat_wvec {n : ℕ} (g : PO n 1) (ξ : E n) (hd : dfun g ξ ≠ 0) :
    Hyper.spat (wvec_visualDefs g ξ) = dfun g ξ • phiFun g ξ := by
  ext i
  simp only [Hyper.spat, PiLp.toLp_apply, phiCf_phiFun_coord, WithLp.ofLp_smul, Pi.smul_apply,
    smul_eq_mul]
  rw [mul_div_cancel₀ _ hd]

/-- The spatial part of the chart-linear action is `linSp g`. -/
private lemma phiCf_linSp_eq_spat {n : ℕ} (g : PO n 1) (v : E n) :
    phiCf_linSp g v = Hyper.spat ((sMat g).mulVec (phiCf_hv0 v)) := by
  ext i
  rw [phiCf_linSp_apply_coord, innerSL_apply_apply, Hyper.inner_eq_sum]
  simp only [phiCf_Acol, PiLp.toLp_apply]
  simp only [Hyper.spat, PiLp.toLp_apply, Matrix.mulVec, dotProduct, Fintype.sum_sum_type,
    Fin.sum_univ_one, phiCf_hv0, Sum.elim_inl, Sum.elim_inr, mul_zero, add_zero]

/-- The time part of the chart-linear action is `linT g`. -/
private lemma phiCf_linT_eq {n : ℕ} (g : PO n 1) (v : E n) :
    phiCf_linT g v = ((sMat g).mulVec (phiCf_hv0 v)) (Sum.inr 0) := by
  rw [phiCf_linT, innerSL_apply_apply, Hyper.inner_eq_sum]
  simp only [phiCf_Acol, PiLp.toLp_apply, Matrix.mulVec, dotProduct, Fintype.sum_sum_type,
    Fin.sum_univ_one, phiCf_hv0, Sum.elim_inl, Sum.elim_inr, mul_zero, add_zero]

/-- Minkowski pairing of `wvec_visualDefs g ξ` with the chart-linear image of a tangent vector `h`. -/
private lemma phiCf_mink_wvec_hv0 {n : ℕ} (g : PO n 1) (ξ h : E n)
    (hh : inner ℝ ξ h = 0) :
    Hyper.mink (wvec_visualDefs g ξ) ((sMat g).mulVec (phiCf_hv0 h)) = 0 := by
  rw [wvec_visualDefs, sMat_mink, Hyper.mink_apply]
  simp only [hvec, phiCf_hv0, Sum.elim_inl, Sum.elim_inr, mul_zero]
  rw [← Hyper.inner_eq_sum, hh, sub_zero]

/-- Minkowski square of the chart-linear image of a tangent vector `h`. -/
private lemma phiCf_mink_hv0_self {n : ℕ} (g : PO n 1) (h : E n) :
    Hyper.mink ((sMat g).mulVec (phiCf_hv0 h)) ((sMat g).mulVec (phiCf_hv0 h)) = ‖h‖ ^ 2 := by
  rw [sMat_mink, Hyper.mink_apply]
  simp only [phiCf_hv0, Sum.elim_inl, Sum.elim_inr, mul_zero, sub_zero]
  rw [Hyper.norm_sq_eq_sum]

/-! ## The main theorem -/

theorem phiFunConformal (n : ℕ) (g : LeanEval.Geometry.MostowRigidity.PO n 1)
    (ξ : Submission.Mostow.E n) (hξ : ξ ∈ Submission.Mostow.Sph n)
    (hd : Work.Mostow.dfun g ξ ≠ 0) (h : Submission.Mostow.E n)
    (hh : inner ℝ ξ h = 0) :
    inner ℝ (Work.Mostow.phiFun g ξ) (fderiv ℝ (Work.Mostow.phiFun g) ξ h) = 0 ∧
      ‖fderiv ℝ (Work.Mostow.phiFun g) ξ h‖ = ‖h‖ / Work.Mostow.dfun g ξ := by
  have hDpos : 0 < dfun g ξ := dfunPosAux n g ξ hξ
  have hφnorm : ‖phiFun g ξ‖ = 1 := phiFunUnitAux n g ξ hξ
  have hder : fderiv ℝ (phiFun g) ξ = phiCf_dPhi g ξ := (phiCf_hasFDerivAt_phiFun g ξ hd).fderiv
  -- The two Minkowski identities, read in the chart.
  have hrel1 : inner ℝ (phiFun g ξ) (phiCf_linSp g h) = phiCf_linT g h := by
    have hm1 := phiCf_mink_wvec_hv0 g ξ h hh
    rw [phiCf_mink_eq_inner_sub, phiCf_spat_wvec g ξ hd, ← phiCf_linSp_eq_spat,
      ← phiCf_linT_eq] at hm1
    rw [real_inner_smul_left] at hm1
    simp only [dfun] at hm1
    have h2 : wvec_visualDefs g ξ (Sum.inr 0) * inner ℝ (phiFun g ξ) (phiCf_linSp g h)
        = wvec_visualDefs g ξ (Sum.inr 0) * phiCf_linT g h := by
      linarith
    exact mul_left_cancel₀ (show wvec_visualDefs g ξ (Sum.inr 0) ≠ 0 from hd) h2
  have hrel2 : ‖phiCf_linSp g h‖ ^ 2 - (phiCf_linT g h) ^ 2 = ‖h‖ ^ 2 := by
    have hm2 := phiCf_mink_hv0_self g h
    rw [phiCf_mink_eq_inner_sub, ← phiCf_linSp_eq_spat, ← phiCf_linT_eq,
      real_inner_self_eq_norm_sq] at hm2
    nlinarith [hm2]
  rw [hder]
  refine ⟨?_, ?_⟩
  · rw [phiCf_dPhi_apply g ξ h, inner_sub_right, real_inner_smul_right, real_inner_smul_right,
      real_inner_smul_right, hrel1, real_inner_self_eq_norm_sq, hφnorm]
    ring
  · have hdh : (dfun g ξ)⁻¹ • phiCf_linSp g h - (phiCf_linT g h) • ((dfun g ξ)⁻¹ • phiFun g ξ)
        = (dfun g ξ)⁻¹ • (phiCf_linSp g h - (phiCf_linT g h) • phiFun g ξ) := by
      module
    rw [phiCf_dPhi_apply g ξ h, hdh, norm_smul,
      Real.norm_of_nonneg (inv_nonneg.mpr hDpos.le), div_eq_inv_mul]
    congr 1
    have h2 : ‖phiCf_linSp g h - (phiCf_linT g h) • phiFun g ξ‖ ^ 2 = ‖h‖ ^ 2 := by
      have e1 : ‖phiCf_linSp g h - (phiCf_linT g h) • phiFun g ξ‖ ^ 2
          = ‖phiCf_linSp g h‖ ^ 2 - (phiCf_linT g h) ^ 2 := by
        rw [norm_sub_sq_real, real_inner_smul_right, real_inner_comm, hrel1, norm_smul,
          hφnorm, mul_one, Real.norm_eq_abs, sq_abs]
        ring
      rw [e1, hrel2]
    rw [← Real.sqrt_sq (norm_nonneg _), h2, Real.sqrt_sq (norm_nonneg h)]

end

end Work.Mostow
