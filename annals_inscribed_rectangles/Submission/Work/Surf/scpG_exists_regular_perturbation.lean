import Mathlib
import Submission.Work.Surf.scpDefs
import Submission.Work.Sard.weak_interior_empty_open_prod

/-!
# Existence of a regularizing perturbation of the auxiliary family `scpG`

This file proves `Work.Surf.scpG_exists_regular_perturbation`: for the auxiliary family

`scpG F v w (σ,x) = F x - σ • v - σ (1-σ) χ x • w`

on the cube `[0,1]³` there is a perturbation value `w` such that every *interior* zero of `scpG F v w`
is a regular point, i.e. `fderiv ℝ (scpG F v w) z` is surjective there.  Nothing is required on the
boundary of the cube: the perturbation `σ (1-σ) χ x • w` vanishes on the side faces `σ = 0`, `σ = 1`
(factor `σ(1-σ)`) and on the lateral faces (the bump `χ` is supported on the interior of the square),
so the boundary zeros are those of `cutMap F v`, handled separately.

## The route

The factor `α z = σ (1-σ) χ x` is *positive* on

`scpU = {z | 0 < σ < 1 ∧ 0 < χ x}`,

an open set containing every interior point of the cube, and on `scpU` the **solution map**

`scpSol F v z = (α z)⁻¹ • (F x - σ • v)`

is `C^∞`.  At a zero `z ∈ scpU` of `scpG F v w` one has `scpSol F v z = w`, and the product rule gives

`fderiv ℝ (scpSol F v) z = (α z)⁻¹ • fderiv ℝ (scpG F v w) z`

(`scpSol_fderiv_eq`), so that `w` is a *critical value* of `scpSol F v` on `scpU` exactly when some
interior zero of `scpG F v w` is non-regular.  Weak Sard's theorem (the chapter
`Submission/Work/Sard/`, in the general form `Work.Sard.prod.weakSard_all`) says that the critical
values of the `C^∞` map `scpSol F v : 𝔼³ → 𝔼²` on the open set `scpU` have empty interior, so their
complement is dense and we may choose `w` outside them.
-/

namespace Work.Surf

open scoped ContDiff Topology
open Set

noncomputable section

/-! ## Elementary properties of the bump factors -/

theorem contDiff_scpPhi : ContDiff ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) scpPhi := by
  unfold scpPhi
  fun_prop

theorem contDiff_scpChi : ContDiff ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) scpChi := by
  unfold scpChi scpPhi
  fun_prop

theorem continuous_scpChi : Continuous scpChi := contDiff_scpChi.continuous

/-- `φ t = smoothTransition t * smoothTransition (1-t)` is positive exactly on `(0,1)`. -/
theorem scpPhi_pos {t : ℝ} (h0 : 0 < t) (h1 : t < 1) : 0 < scpPhi t := by
  unfold scpPhi
  exact mul_pos (Real.smoothTransition.pos_of_pos h0)
    (Real.smoothTransition.pos_of_pos (by linarith))

theorem scpPhi_eq_zero_iff {t : ℝ} : scpPhi t = 0 ↔ t ≤ 0 ∨ 1 ≤ t := by
  unfold scpPhi
  rw [mul_eq_zero, Real.smoothTransition.zero_iff_nonpos, Real.smoothTransition.zero_iff_nonpos]
  constructor
  · rintro (h | h)
    · exact Or.inl h
    · exact Or.inr (by linarith)
  · rintro (h | h)
    · exact Or.inl h
    · exact Or.inr (by linarith)

theorem scpPhi_ne_zero_iff {t : ℝ} : scpPhi t ≠ 0 ↔ 0 < t ∧ t < 1 := by
  rw [ne_eq, scpPhi_eq_zero_iff, not_or]
  constructor
  · rintro ⟨h0, h1⟩
    exact ⟨not_le.mp h0, not_le.mp h1⟩
  · rintro ⟨h0, h1⟩
    exact ⟨not_le.mpr h0, not_le.mpr h1⟩

/-- `χ` is positive at a point of the open square. -/
theorem scpChi_pos_of {x : EuclideanSpace ℝ (Fin 2)} (h : ∀ i, 0 < x i ∧ x i < 1) :
    0 < scpChi x := by
  have h0 := h 0
  have h1 := h 1
  unfold scpChi
  exact mul_pos (scpPhi_pos h0.1 h0.2) (scpPhi_pos h1.1 h1.2)

/-! ## The factor `α` and the unperturbed part `A` of `scpG` -/

/-- The scalar factor `α z = σ (1-σ) χ x` of the perturbation, `z = (σ,x)`. -/
def scpAlpha (z : EuclideanSpace ℝ (Fin 3)) : ℝ :=
  Work.Drive.ezPhi (cutSig z) * scpChi (cutSp z)

/-- The unperturbed part `A z = F x - σ • v` of the family, `z = (σ,x)`. -/
def scpA (F : EuclideanSpace ℝ (Fin 2) → EuclideanSpace ℝ (Fin 2))
    (v : EuclideanSpace ℝ (Fin 2)) (z : EuclideanSpace ℝ (Fin 3)) : EuclideanSpace ℝ (Fin 2) :=
  F (cutSp z) - cutSig z • v

theorem scpSol_eq (F : EuclideanSpace ℝ (Fin 2) → EuclideanSpace ℝ (Fin 2))
    (v : EuclideanSpace ℝ (Fin 2)) (z : EuclideanSpace ℝ (Fin 3)) :
    scpSol F v z = (scpAlpha z)⁻¹ • scpA F v z := rfl

theorem scpG_eq (F : EuclideanSpace ℝ (Fin 2) → EuclideanSpace ℝ (Fin 2))
    (v w : EuclideanSpace ℝ (Fin 2)) (z : EuclideanSpace ℝ (Fin 3)) :
    scpG F v w z = scpA F v z - scpAlpha z • w := rfl

/-- `α` is positive on `scpU`. -/
theorem scpAlpha_pos {z : EuclideanSpace ℝ (Fin 3)} (hz : z ∈ scpU) : 0 < scpAlpha z := by
  obtain ⟨h0, h1, h2⟩ := hz
  unfold scpAlpha
  exact mul_pos (Work.Drive.ezPhi_pos h0 h1) h2

theorem contDiff_scpAlpha : ContDiff ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) scpAlpha := by
  unfold scpAlpha scpChi scpPhi Work.Drive.ezPhi
  fun_prop

theorem contDiff_scpA (F : EuclideanSpace ℝ (Fin 2) → EuclideanSpace ℝ (Fin 2))
    (hF : ContDiff ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) F) (v : EuclideanSpace ℝ (Fin 2)) :
    ContDiff ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) (scpA F v) := by
  unfold scpA
  exact (hF.comp cutSp.contDiff).sub (cutSig.contDiff.smul contDiff_const)

/-! ## `scpU` is open and `scpSol` is smooth on it -/

theorem isOpen_scpU : IsOpen scpU := by
  have h1 : IsOpen {z : EuclideanSpace ℝ (Fin 3) | 0 < cutSig z ∧ cutSig z < 1} :=
    (isOpen_lt continuous_const cutSig.continuous).inter
      (isOpen_lt cutSig.continuous continuous_const)
  have h2 : IsOpen {z : EuclideanSpace ℝ (Fin 3) | 0 < scpChi (cutSp z)} :=
    isOpen_lt continuous_const (continuous_scpChi.comp cutSp.continuous)
  have h : scpU = {z : EuclideanSpace ℝ (Fin 3) | 0 < cutSig z ∧ cutSig z < 1} ∩
      {z : EuclideanSpace ℝ (Fin 3) | 0 < scpChi (cutSp z)} := by
    ext z
    simp only [scpU, mem_ofPred_eq, mem_inter_iff, and_assoc]
  rw [h]
  exact h1.inter h2

theorem contDiffOn_scpSol (F : EuclideanSpace ℝ (Fin 2) → EuclideanSpace ℝ (Fin 2))
    (hF : ContDiff ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) F) (v : EuclideanSpace ℝ (Fin 2)) :
    ContDiffOn ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) (scpSol F v) scpU := by
  have h : scpSol F v = (scpAlpha)⁻¹ • (scpA F v) := by
    funext z
    exact scpSol_eq F v z
  rw [h]
  refine ContDiffOn.smul (𝕜 := ℝ) (𝕜' := ℝ) ?_ (contDiff_scpA F hF v).contDiffOn
  exact ContDiffOn.inv contDiff_scpAlpha.contDiffOn
    (fun z hz => ne_of_gt (scpAlpha_pos hz))

/-! ## The derivative of the solution map at a zero

The general algebraic fact: if `A z = α z • w` and `α z ≠ 0`, then differentiating the identity
`α⁻¹ • (α • w) = w` shows that the derivative of `α⁻¹ • A` at `z` is `α⁻¹` times the derivative of
`A - α • w`. -/

theorem fderiv_inv_smul_sub {E F : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    [NormedAddCommGroup F] [NormedSpace ℝ F] (α : E → ℝ) (A : E → F) (w : F) (z : E)
    (hα : DifferentiableAt ℝ α z) (hA : DifferentiableAt ℝ A z) (hαne : α z ≠ 0)
    (hz : A z = α z • w) :
    fderiv ℝ (fun y => (α y)⁻¹ • A y) z
      = (α z)⁻¹ • fderiv ℝ (fun y => A y - α y • w) z := by
  change fderiv ℝ ((fun y => (α y)⁻¹) • A) z
      = (α z)⁻¹ • fderiv ℝ (A - fun y => α y • w) z
  have hαinv : HasFDerivAt (fun y => (α y)⁻¹)
      ((ContinuousLinearMap.toSpanSingleton ℝ (-(α z ^ 2)⁻¹)).comp (fderiv ℝ α z)) z :=
    (hasFDerivAt_inv hαne).comp z hα.hasFDerivAt
  have hprod := hαinv.smul hA.hasFDerivAt
  have hw : HasFDerivAt (fun y => α y • w) ((fderiv ℝ α z).smulRight w) z :=
    hα.hasFDerivAt.smul_const w
  have hsub := hA.hasFDerivAt.sub hw
  rw [hprod.fderiv, hsub.fderiv]
  have key : ((ContinuousLinearMap.toSpanSingleton ℝ (-(α z ^ 2)⁻¹)).comp
        (fderiv ℝ α z)).smulRight (α z • w)
      = -((α z)⁻¹ • ((fderiv ℝ α z).smulRight w)) := by
    refine ContinuousLinearMap.ext fun v => ?_
    simp only [ContinuousLinearMap.smulRight_apply, ContinuousLinearMap.comp_apply,
      ContinuousLinearMap.toSpanSingleton_apply, smul_apply, neg_apply]
    rw [smul_smul, smul_smul, ← neg_smul]
    congr 1
    rw [smul_eq_mul]
    have h2' : (α z ^ 2)⁻¹ * α z = (α z)⁻¹ := by field_simp
    rw [show (fderiv ℝ α z) v * -(α z ^ 2)⁻¹ * α z
        = -((α z ^ 2)⁻¹ * α z * (fderiv ℝ α z) v) from by ring, h2']
  rw [hz, key, smul_sub, sub_eq_add_neg]

/-- **Derivative of the solution map at a zero of `scpG`** (in the interior of the cube). -/
theorem scpSol_fderiv_eq (F : EuclideanSpace ℝ (Fin 2) → EuclideanSpace ℝ (Fin 2))
    (hF : ContDiff ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) F) (v w : EuclideanSpace ℝ (Fin 2))
    {z : EuclideanSpace ℝ (Fin 3)} (hzU : z ∈ scpU) (hzero : scpG F v w z = 0) :
    fderiv ℝ (scpSol F v) z = (scpAlpha z)⁻¹ • fderiv ℝ (scpG F v w) z := by
  have hαne : scpAlpha z ≠ 0 := ne_of_gt (scpAlpha_pos hzU)
  have hα : DifferentiableAt ℝ scpAlpha z :=
    (contDiff_scpAlpha.differentiable (by simp)).differentiableAt
  have hA : DifferentiableAt ℝ (scpA F v) z :=
    (contDiff_scpA F hF v).differentiable (by simp) |>.differentiableAt
  have hAz : scpA F v z = scpAlpha z • w := by
    have h := scpG_eq F v w z
    rw [hzero] at h
    exact sub_eq_zero.mp h.symm
  have hmain := fderiv_inv_smul_sub scpAlpha (scpA F v) w z hα hA hαne hAz
  change fderiv ℝ (fun y => (scpAlpha y)⁻¹ • scpA F v y) z
      = (scpAlpha z)⁻¹ • fderiv ℝ (fun y => scpA F v y - scpAlpha y • w) z
  have h2 : scpG F v w = fun y => scpA F v y - scpAlpha y • w := by
    funext y
    exact scpG_eq F v w y
  rw [← h2]
  exact hmain

/-! ## The main theorem -/

/-- **Existence of a regularizing perturbation of the auxiliary family.**  There is `w` such that
every *interior* zero of `scpG F v w` (the perturbed family `(σ,x) ↦ F x - σ • v - σ(1-σ) χ x • w` on
the cube `[0,1]³`) is a regular point. -/
theorem scpG_exists_regular_perturbation
    (F : EuclideanSpace ℝ (Fin 2) → EuclideanSpace ℝ (Fin 2))
    (hF : ContDiff ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) F)
    (v : EuclideanSpace ℝ (Fin 2)) :
    ∃ w : EuclideanSpace ℝ (Fin 2), ∀ z ∈ Submission.Drive.unitBox 2,
      (∀ i : Fin 3, 0 < z i ∧ z i < 1) → scpG F v w z = 0 →
      Function.Surjective (fderiv ℝ (scpG F v w) z) := by
  -- the set of critical values of the solution map on `scpU`
  set B : Set (EuclideanSpace ℝ (Fin 2)) :=
    scpSol F v '' (scpU ∩ {z | ¬ Function.Surjective (fderivWithin ℝ (scpSol F v) scpU z)})
    with hB
  have hsard : interior B = ∅ := by
    rw [hB]
    exact (Work.Sard.prod.weakSard_all 2) (EuclideanSpace ℝ (Fin 3))
      (EuclideanSpace ℝ (Fin 2))
      (by simp [finrank_euclideanSpace_fin])
      (by simp [finrank_euclideanSpace_fin])
      scpU isOpen_scpU (scpSol F v) (contDiffOn_scpSol F hF v)
  have hdense : Dense Bᶜ := (interior_eq_empty_iff_dense_compl).mp hsard
  obtain ⟨w, hw⟩ := hdense.nonempty
  refine ⟨w, fun z _ hint hzero => ?_⟩
  -- every interior point of the cube lies in `scpU`
  have hzU : z ∈ scpU := by
    refine ⟨?_, ?_, ?_⟩
    · rw [cutSig_apply]; exact (hint 0).1
    · rw [cutSig_apply]; exact (hint 0).2
    · exact scpChi_pos_of (fun i => by
        have := hint i.succ
        simpa only [cutSp_apply] using this)
  have hαne : scpAlpha z ≠ 0 := ne_of_gt (scpAlpha_pos hzU)
  have hAz : scpA F v z = scpAlpha z • w := by
    have h := scpG_eq F v w z
    rw [hzero] at h
    exact sub_eq_zero.mp h.symm
  -- the zero of `scpG` is the value `w` of the solution map
  have hsolw : scpSol F v z = w := by
    rw [scpSol_eq, hAz, smul_smul, inv_mul_cancel₀ hαne, one_smul]
  -- `w` is not a critical value, so `z` is a regular point of `scpSol`
  have hsurjWithin : Function.Surjective (fderivWithin ℝ (scpSol F v) scpU z) := by
    by_contra hns
    exact hw ⟨z, ⟨hzU, hns⟩, hsolw⟩
  have hsurj : Function.Surjective (fderiv ℝ (scpSol F v) z) := by
    rwa [fderivWithin_of_isOpen isOpen_scpU hzU] at hsurjWithin
  -- transfer surjectivity through the scalar multiple
  have hkey : fderiv ℝ (scpG F v w) z = scpAlpha z • fderiv ℝ (scpSol F v) z := by
    rw [scpSol_fderiv_eq F hF v w hzU hzero, smul_smul, mul_inv_cancel₀ hαne, one_smul]
  rw [hkey]
  intro y
  obtain ⟨v', hv'⟩ := hsurj ((scpAlpha z)⁻¹ • y)
  refine ⟨v', ?_⟩
  rw [smul_apply, hv', smul_smul, mul_inv_cancel₀ hαne, one_smul]

end

end Work.Surf
