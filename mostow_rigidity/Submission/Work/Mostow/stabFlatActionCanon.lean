import Mathlib
import Submission.Work.Mostow.QIDefs
import Submission.Work.Mostow.hptOf_level
import Submission.Work.Mostow.hptOf_yc
import Submission.Work.Mostow.StabHoroForm
import Submission.Work.Mostow.StabLift
import Submission.Work.Mostow.LambdaMat_theta_eq_exp_smul
import Submission.Work.Mostow.stabFlatDefs

open Matrix
open scoped Matrix

/-!
# The canonical flat (horospherical) action of an element fixing a boundary point

If `γ ∈ PO(n,1)` fixes `ζ ∈ Sph n` and does not shift the horospheres at `ζ`
(`busemann ζ (γ • 0) = 0`), then `γ` preserves every horosphere of `ζ` and acts on the flat
coordinate `yc ζ ·` of each of them by the *canonical* affine isometry
`y ↦ flatLin ζ (LambdaMat γ) y + flatTrans ζ (LambdaMat γ)` of `ζ^⊥`.

This is the canonical (i.e. `Λ`-matrix) form of `Work.Mostow.stabFlatAction`, whose existential
pair is exactly this one; here the pair is exhibited explicitly so that the identification is
usable downstream.

The proof goes through the lift `LambdaMat γ`: the hypothesis says that the null vector
`θ_ζ = (ζ,1)` is fixed, and the normal form of `O(n,1)` matrices fixing `θ_ζ`
(`O1_parab_eta`, `parabQ_isom` in `StabHoroForm`) turns the action into the affine one.
-/

namespace Work.Mostow

open Submission.Mostow LeanEval.Geometry.MostowRigidity

noncomputable section

variable {n : ℕ}

/-! ## Elementary chart identities -/

@[simp] private lemma sfa_wvec_add (a b : E n) : wvec (a + b) = wvec a + wvec b := by
  ext z; rcases z with i | j <;> simp [wvec]

@[simp] private lemma sfa_wvec_smul (c : ℝ) (a : E n) : wvec (c • a) = c • wvec a := by
  ext z; rcases z with i | j <;> simp [wvec]

@[simp] private lemma sfa_hspat_wvec (y : E n) : hspat (wvec y) = y := rfl

@[simp] private lemma sfa_htime_wvec (y : E n) : htime (wvec y) = 0 := rfl

/-- The chart map `hlift` is injective. -/
private lemma sfa_hlift_inj {u v : E n} (h : hlift u = hlift v) : u = v := by
  ext i
  exact congrFun h (Sum.inl i)

private lemma sfa_norm_half_smul (x : E n) :
    ‖(-(1/2) : ℝ) • x‖ = (1/2) * ‖x‖ := by
  rw [norm_smul, Real.norm_eq_abs, abs_neg, abs_of_pos (by norm_num : (0:ℝ) < (1/2))]

/-! ## `V^⊥` and the decomposition of `ℝ^{n+1}` -/

private lemma sfa_horoProj_wvec {ξ y : E n} (hy : inner ℝ y ξ = 0) :
    horoProj ξ (wvec y) = wvec y := by
  have h1 : mform (wvec y) (theta ξ) = 0 := by
    rw [mform_eq]; simp [hy]
  have h2 : mform (wvec y) (horoEta ξ) = 0 := by
    rw [mform_eq]; simp [hy]
  rw [horoProj, h1, h2]
  simp

private lemma sfa_eq_wvec_hspat_of_horoProj {ξ : E n} (hξ : ξ ∈ Sph n)
    {x : Fin n ⊕ Fin 1 → ℝ} (hx : horoProj ξ x = x) : x = wvec (hspat x) := by
  have h0 : htime x = 0 := htime_eq_zero_of_horoProj ξ hξ hx
  funext z
  rcases z with i | j
  · show x (Sum.inl i) = (wvec (hspat x)) (Sum.inl i)
    rfl
  · obtain rfl : j = 0 := Subsingleton.elim _ _
    simpa [wvec, htime] using h0

private lemma sfa_hspat_inner_zero_of_horoProj {ξ : E n} (hξ : ξ ∈ Sph n)
    {x : Fin n ⊕ Fin 1 → ℝ} (hx : horoProj ξ x = x) : inner ℝ (hspat x) ξ = 0 := by
  have hθ : mform (horoProj ξ x) (theta ξ) = 0 := mform_horoProj_theta ξ hξ x
  rw [hx] at hθ
  have ht : htime x = 0 := htime_eq_zero_of_horoProj ξ hξ hx
  rw [mform_eq] at hθ
  simpa [ht] using hθ

private lemma sfa_eq_wvec_add_theta {ξ : E n} (hξ : ξ ∈ Sph n)
    {x : Fin n ⊕ Fin 1 → ℝ} (hx : mform x (theta ξ) = 0) :
    x = wvec (hspat (horoProj ξ x)) + (mform x (horoEta ξ) / 2) • theta ξ := by
  have hπ : wvec (hspat (horoProj ξ x)) = horoProj ξ x :=
    (sfa_eq_wvec_hspat_of_horoProj hξ (horoProj_idem ξ hξ x)).symm
  have hdec := horoProj_decomp ξ x
  rw [hx] at hdec
  simp only [zero_div, zero_smul, add_zero] at hdec
  rw [hπ]
  exact hdec.symm

/-- If `M` fixes `θ_ξ` then it preserves `θ_ξ^⊥`. -/
private lemma sfa_mform_mulVec_theta_zero {ξ : E n} (_hξ : ξ ∈ Sph n)
    {M : Matrix (Fin n ⊕ Fin 1) (Fin n ⊕ Fin 1) ℝ} (hO : IsJOrth M)
    (hθ : M.mulVec (theta ξ) = theta ξ) {x : Fin n ⊕ Fin 1 → ℝ}
    (hx : mform x (theta ξ) = 0) : mform (M.mulVec x) (theta ξ) = 0 := by
  have hJMJ : (pmOneMat : Matrix (Fin n ⊕ Fin 1) (Fin n ⊕ Fin 1) ℝ) * M.transpose * pmOneMat
      * M = 1 := by
    have h1 : (pmOneMat : Matrix (Fin n ⊕ Fin 1) (Fin n ⊕ Fin 1) ℝ) * M.transpose * pmOneMat * M
        = pmOneMat * (M.transpose * pmOneMat * M) := by simp only [Matrix.mul_assoc]
    rw [h1, hO, pmOneMat_mul_pmOneMat]
  have hJθ : ((pmOneMat : Matrix (Fin n ⊕ Fin 1) (Fin n ⊕ Fin 1) ℝ) * M.transpose
      * pmOneMat).mulVec (theta ξ) = theta ξ := by
    have h := congrArg (fun m : Matrix (Fin n ⊕ Fin 1) (Fin n ⊕ Fin 1) ℝ =>
      m.mulVec (theta ξ)) hJMJ
    rw [Matrix.one_mulVec] at h
    rw [← Matrix.mulVec_mulVec] at h
    rwa [hθ] at h
  rw [mform_mulVec_left, hJθ, hx]

/-! ## The chart point `hptOf` in the `(V^⊥, θ, η)` decomposition -/

private lemma sfa_tpart_hptOf {ξ : E n} (hξ : ξ ∈ Sph n) {y : E n} (hy : inner ℝ y ξ = 0)
    {D : ℝ} (hD : 0 < D) :
    tpart (hptOf ξ y D) = (1 + D ^ 2 * ‖y‖ ^ 2) / (2 * D) + D / 2 := by
  set A : ℝ := (1 + D ^ 2 * ‖y‖ ^ 2) / (2 * D) - D / 2 with hA
  have hξ1 : inner ℝ ξ ξ = 1 := hptOf_level_aux_inner_self hξ
  have hy' : inner ℝ ξ y = 0 := by rw [real_inner_comm]; exact hy
  have hpt : hptOf ξ y D = A • ξ + D • y := by rw [hptOf, ← hA]
  have h2 : inner ℝ (A • ξ + D • y) (A • ξ + D • y) = A ^ 2 + D ^ 2 * inner ℝ y y := by
    simp only [inner_add_left, inner_add_right, real_inner_smul_left, real_inner_smul_right,
      hξ1, hy, hy']
    ring
  have hnorm : ‖hptOf ξ y D‖ ^ 2 = A ^ 2 + D ^ 2 * ‖y‖ ^ 2 := by
    rw [← real_inner_self_eq_norm_sq (hptOf ξ y D), hpt, h2, real_inner_self_eq_norm_sq y]
  have hsq : 1 + ‖hptOf ξ y D‖ ^ 2 = (A + D) ^ 2 := by
    rw [hnorm, hA]; field_simp; ring
  have hpos : 0 < A + D := by
    have h : A + D = (1 + D ^ 2 * ‖y‖ ^ 2) / (2 * D) + D / 2 := by rw [hA]; ring
    rw [h]; positivity
  have htp : tpart (hptOf ξ y D) = A + D := by rw [tpart, hsq, Real.sqrt_sq hpos.le]
  rw [htp, hA]; ring

private lemma sfa_hlift_hptOf {ξ : E n} (hξ : ξ ∈ Sph n) {y : E n} (hy : inner ℝ y ξ = 0)
    {D : ℝ} (hD : 0 < D) :
    hlift (hptOf ξ y D)
      = D • wvec y + ((1 + D ^ 2 * ‖y‖ ^ 2) / (2 * D)) • theta ξ - (D / 2) • horoEta ξ := by
  funext z
  rcases z with i | j
  · simp only [hlift, Sum.elim_inl, hptOf, wvec, theta, horoEta, Pi.add_apply, Pi.sub_apply,
      Pi.smul_apply, smul_eq_mul, WithLp.ofLp_add, WithLp.ofLp_smul]
    ring
  · obtain rfl : j = 0 := Subsingleton.elim _ _
    simp only [hlift, Sum.elim_inr, wvec, theta, horoEta, Pi.add_apply, Pi.sub_apply,
      Pi.smul_apply, smul_eq_mul]
    rw [sfa_tpart_hptOf hξ hy hD]
    ring

/-! ## The flat action -/

private lemma sfa_flatLin_inner_zero (ξ : E n) (hξ : ξ ∈ Sph n)
    (M : Matrix (Fin n ⊕ Fin 1) (Fin n ⊕ Fin 1) ℝ) (y : E n) :
    inner ℝ (flatLin ξ M y) ξ = 0 := by
  rw [flatLin_apply]
  exact sfa_hspat_inner_zero_of_horoProj hξ (horoProj_idem ξ hξ (M.mulVec (wvec y)))

private lemma sfa_flatTrans_inner_zero (ξ : E n) (hξ : ξ ∈ Sph n)
    (M : Matrix (Fin n ⊕ Fin 1) (Fin n ⊕ Fin 1) ℝ) :
    inner ℝ (flatTrans ξ M) ξ = 0 := by
  have h : inner ℝ (hspat (horoProj ξ (M.mulVec (horoEta ξ)))) ξ = 0 :=
    sfa_hspat_inner_zero_of_horoProj hξ (horoProj_idem ξ hξ (M.mulVec (horoEta ξ)))
  rw [flatTrans_apply, real_inner_smul_left, h, mul_zero]

private lemma sfa_flatLin_norm (ξ : E n) (hξ : ξ ∈ Sph n)
    {M : Matrix (Fin n ⊕ Fin 1) (Fin n ⊕ Fin 1) ℝ} (hO : IsJOrth M)
    (hθ : M.mulVec (theta ξ) = theta ξ) {y : E n} (hy : inner ℝ y ξ = 0) :
    ‖flatLin ξ M y‖ = ‖y‖ := by
  have hproj : horoProj ξ (wvec y) = wvec y := sfa_horoProj_wvec hy
  have hparab : mform (horoProj ξ (M.mulVec (wvec y))) (horoProj ξ (M.mulVec (wvec y)))
      = mform (wvec y) (wvec y) := by
    have h := parabQ_isom ξ hξ (M := M) hO (w := (1:ℝ)) (by simpa using hθ) (by norm_num)
      hproj hproj
    simpa [parabQ] using h
  have hmm : mform (horoProj ξ (M.mulVec (wvec y))) (horoProj ξ (M.mulVec (wvec y)))
      = ‖flatLin ξ M y‖ ^ 2 := by
    rw [mform_eq_norm_sq_of_horoProj ξ hξ (horoProj_idem ξ hξ (M.mulVec (wvec y))),
      flatLin_apply]
  have h2 : mform (wvec y) (wvec y) = ‖y‖ ^ 2 := by
    rw [mform_eq]
    simp
  have hs : ‖flatLin ξ M y‖ ^ 2 = ‖y‖ ^ 2 := by rw [← hmm, hparab, h2]
  have hsqrt : Real.sqrt (‖flatLin ξ M y‖ ^ 2) = Real.sqrt (‖y‖ ^ 2) := by rw [hs]
  rwa [Real.sqrt_sq (norm_nonneg _), Real.sqrt_sq (norm_nonneg _)] at hsqrt

/-- The core: the lift of `M` sends the horosphere at `ξ` of level `D` to itself, acting on the
flat coordinate by `y ↦ flatLin ξ M y + flatTrans ξ M`. -/
private lemma sfa_flat_action {ξ : E n} (hξ : ξ ∈ Sph n)
    {M : Matrix (Fin n ⊕ Fin 1) (Fin n ⊕ Fin 1) ℝ} (hO : IsJOrth M)
    (hθ : M.mulVec (theta ξ) = theta ξ) {y : E n} (hy : inner ℝ y ξ = 0)
    {D : ℝ} (hD : 0 < D) :
    M.mulVec (hlift (hptOf ξ y D))
      = hlift (hptOf ξ (flatLin ξ M y + flatTrans ξ M) D) := by
  set s : Fin n ⊕ Fin 1 → ℝ := horoProj ξ (M.mulVec (horoEta ξ)) with hs
  set β : ℝ := mform (M.mulVec (wvec y)) (horoEta ξ) / 2 with hβ
  set A : E n := flatLin ξ M y with hA
  set v : E n := flatTrans ξ M with hv
  -- the `η`-row in normal form
  have hη : M.mulVec (horoEta ξ) = horoEta ξ + s - (mform s s / 4) • theta ξ := by
    have h := O1_parab_eta ξ hξ (M := M) hO (w := (1:ℝ)) (by simpa using hθ) (by norm_num)
    simpa [hs] using h
  -- `M (wvec y)` lies in `θ^⊥`, and its decomposition
  have hxw : mform (wvec y) (theta ξ) = 0 := by
    rw [mform_eq]; simp [hy]
  have hmθ : mform (M.mulVec (wvec y)) (theta ξ) = 0 :=
    sfa_mform_mulVec_theta_zero hξ hO hθ hxw
  have hdec : M.mulVec (wvec y) = wvec A + β • theta ξ := by
    have h := sfa_eq_wvec_add_theta hξ hmθ
    rw [← flatLin_apply ξ M y, ← hA] at h
    simpa [hβ] using h
  -- orthogonality data
  have hAξ : inner ℝ A ξ = 0 := by rw [hA]; exact sfa_flatLin_inner_zero ξ hξ M y
  have hs_idem : horoProj ξ s = s := by rw [hs]; exact horoProj_idem ξ hξ (M.mulVec (horoEta ξ))
  have hs_wvec : s = wvec (hspat s) := sfa_eq_wvec_hspat_of_horoProj hξ hs_idem
  have hmm : mform s s = ‖hspat s‖ ^ 2 := mform_eq_norm_sq_of_horoProj ξ hξ hs_idem
  -- the cross relation `⟪A, hspat s⟫ + 2 β = 0`
  have hcross : inner ℝ A (hspat s) + 2 * β = 0 := by
    have hpres := mform_mulVec_mulVec hO (wvec y) (horoEta ξ)
    have h1 : mform (wvec A) (theta ξ) = 0 := by rw [mform_eq]; simp [hAξ]
    have h2 : mform (wvec A) (horoEta ξ) = 0 := by rw [mform_eq]; simp [hAξ]
    have h3 : mform (wvec A) s = inner ℝ A (hspat s) := by
      rw [mform_eq]
      simp [htime_eq_zero_of_horoProj ξ hξ hs_idem]
    have h4 : mform (theta ξ) (theta ξ) = 0 := mform_theta_theta_sph ξ hξ
    have h5 : mform (theta ξ) (horoEta ξ) = 2 := mform_theta_eta_sph ξ hξ
    have h6 : mform (theta ξ) s = 0 := by
      rw [hs]; exact mform_theta_horoProj ξ hξ _
    have hexp : mform (wvec A + β • theta ξ) (horoEta ξ + s - (mform s s / 4) • theta ξ)
        = inner ℝ A (hspat s) + 2 * β := by
      simp only [mform_add_left, mform_sub_right, mform_add_right, mform_smul_right,
        mform_smul_left, h1, h2, h3, h4, h5, h6]
      ring
    have hrhs : mform (wvec y) (horoEta ξ) = 0 := by
      rw [mform_eq]; simp [hy]
    rw [hdec, hη, hexp, hrhs] at hpres
    exact hpres
  have hw : inner ℝ A (hspat s) = -2 * β := by linarith [hcross]
  -- norms
  have hAnorm : ‖A‖ = ‖y‖ := by rw [hA]; exact sfa_flatLin_norm ξ hξ hO hθ hy
  have hv_eq : v = (-(1/2) : ℝ) • hspat s := by rw [hv, flatTrans_apply, ← hs]
  have hnorm2 : ‖A + v‖ ^ 2 = ‖y‖ ^ 2 + 2 * β + mform s s / 4 := by
    rw [norm_add_sq_real, hAnorm, hv_eq, real_inner_smul_right, hw, sfa_norm_half_smul, hmm]
    ring
  have hA0eq : (1 + D ^ 2 * ‖A + v‖ ^ 2) / (2 * D)
      = D * β + (1 + D ^ 2 * ‖y‖ ^ 2) / (2 * D) + D * mform s s / 8 := by
    rw [hnorm2]
    field_simp
    ring
  have hDv_eq : D • wvec (A + v) = D • wvec A - (D / 2) • s := by
    have hwv : wvec (A + v) = wvec A - (1/2 : ℝ) • s := by
      rw [sfa_wvec_add, hv_eq, sfa_wvec_smul, ← hs_wvec, neg_smul, sub_eq_add_neg]
    have hsc : D * (1/2) = D / 2 := by ring
    rw [hwv, smul_sub, smul_smul, hsc]
  have hy' : inner ℝ (A + v) ξ = 0 := by
    rw [inner_add_left, hAξ, sfa_flatTrans_inner_zero ξ hξ M, add_zero]
  calc M.mulVec (hlift (hptOf ξ y D))
      = M.mulVec (D • wvec y + ((1 + D ^ 2 * ‖y‖ ^ 2) / (2 * D)) • theta ξ
            - (D / 2) • horoEta ξ) := by rw [sfa_hlift_hptOf hξ hy hD]
    _ = D • M.mulVec (wvec y) + ((1 + D ^ 2 * ‖y‖ ^ 2) / (2 * D)) • M.mulVec (theta ξ)
          - (D / 2) • M.mulVec (horoEta ξ) := by
        rw [Matrix.mulVec_sub, Matrix.mulVec_add, Matrix.mulVec_smul, Matrix.mulVec_smul,
          Matrix.mulVec_smul]
    _ = D • (wvec A + β • theta ξ) + ((1 + D ^ 2 * ‖y‖ ^ 2) / (2 * D)) • theta ξ
          - (D / 2) • (horoEta ξ + s - (mform s s / 4) • theta ξ) := by rw [hdec, hθ, hη]
    _ = D • wvec A - (D / 2) • s
          + (D * β + (1 + D ^ 2 * ‖y‖ ^ 2) / (2 * D) + D * mform s s / 8) • theta ξ
          - (D / 2) • horoEta ξ := by module
    _ = D • wvec (A + v) + ((1 + D ^ 2 * ‖A + v‖ ^ 2) / (2 * D)) • theta ξ
          - (D / 2) • horoEta ξ := by rw [hDv_eq, hA0eq]; try module
    _ = hlift (hptOf ξ (A + v) D) := (sfa_hlift_hptOf hξ hy' hD).symm

theorem stabFlatActionCanon (n : ℕ) (hA : Submission.Mostow.POActionProp n) (hI : Submission.Mostow.HypIsometryProp n) (ζ : Submission.Mostow.E n) (hζ : ζ ∈ Submission.Mostow.Sph n) (γ : LeanEval.Geometry.MostowRigidity.PO n 1) (hγ : Submission.Mostow.bd γ ζ = ζ) (hβ : Submission.Mostow.busemann ζ (γ • (0 : Submission.Mostow.E n)) = 0) : inner ℝ (Work.Mostow.flatTrans ζ (Work.Mostow.LambdaMat γ)) ζ = 0 ∧ (∀ y : Submission.Mostow.E n, inner ℝ y ζ = 0 → inner ℝ (Work.Mostow.flatLin ζ (Work.Mostow.LambdaMat γ) y) ζ = 0) ∧ (∀ y : Submission.Mostow.E n, inner ℝ y ζ = 0 → ‖Work.Mostow.flatLin ζ (Work.Mostow.LambdaMat γ) y‖ = ‖y‖) ∧ (∀ (y : Submission.Mostow.E n) (D : ℝ), inner ℝ y ζ = 0 → 0 < D → Work.Mostow.lev ζ (γ • Work.Mostow.hptOf ζ y D) = D ∧ Work.Mostow.yc ζ (γ • Work.Mostow.hptOf ζ y D) = Work.Mostow.flatLin ζ (Work.Mostow.LambdaMat γ) y + Work.Mostow.flatTrans ζ (Work.Mostow.LambdaMat γ)) := by
  have hM : IsJOrth (LambdaMat γ) := LambdaMat_isJOrth γ
  have hbC : bCocy γ ζ = 0 := by rw [bCocy, hγ, hβ]
  have hθ : (LambdaMat γ).mulVec (theta ζ) = theta ζ := by
    have h := LambdaMat_theta_eq_exp_smul n hA hI γ ζ hζ hγ
    rw [hbC, neg_zero, Real.exp_zero, one_smul] at h
    exact h
  refine ⟨sfa_flatTrans_inner_zero ζ hζ (LambdaMat γ), ?_, ?_, ?_⟩
  · intro y hy
    exact sfa_flatLin_inner_zero ζ hζ (LambdaMat γ) y
  · intro y hy
    exact sfa_flatLin_norm ζ hζ hM hθ hy
  · intro y D hy hD
    have hy' : inner ℝ (flatLin ζ (LambdaMat γ) y + flatTrans ζ (LambdaMat γ)) ζ = 0 := by
      rw [inner_add_left, sfa_flatLin_inner_zero ζ hζ (LambdaMat γ) y,
        sfa_flatTrans_inner_zero ζ hζ (LambdaMat γ), add_zero]
    have hstep := sfa_flat_action hζ hM hθ hy hD
    have hpt : γ • hptOf ζ y D
        = hptOf ζ (flatLin ζ (LambdaMat γ) y + flatTrans ζ (LambdaMat γ)) D := by
      refine sfa_hlift_inj ?_
      rw [hlift_LambdaMat hA γ (hptOf ζ y D)]
      exact hstep
    rw [hpt]
    exact hptOf_level ζ hζ D hD _ hy'

end

end Work.Mostow
