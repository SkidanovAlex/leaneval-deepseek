import Mathlib
import Submission.Work.RPCore.Defs

/-!
# Generating-function route: CORE node `exists_type2GF`, basic vocabulary

This file sets up the vocabulary for the construction of a global type-2 generating
function of a near-identity symplectic map `ψ : PS → PS` (node C1 of the route design,
`RECTPEG_ROUTE_LEAD.md` §4.3).

Recall `PS = T^*ℝ² = ℝ⁴` with points written `((q₁,q₂),(p₁,p₂))` (see `Work.RPV.Defs`).

Given `ψ : PS → PS` we write `ψ(q,p) = (Q, P)` and

* `gproj ψ x = (x.1, (ψ x).2)`, the map `(q,p) ↦ (q,P)`;
* `gdisp ψ = gproj ψ - id`;
* `invMap ψ` is a (set-theoretic) inverse of `gproj ψ`, and we write
  `invMap ψ y = (y.1, pfun ψ y)`;
* `Qfun ψ y = (ψ (invMap ψ y)).1`;
* `bvec ψ y = (pfun ψ y - y.2, Qfun ψ y - y.1)`, the vector field whose primitive is the
  type-2 generating function of `ψ`.

The elementary lemmas here are used both by the main proof and by the delegated
"chapter" lemmas (`rayPrimitive`, `slab_preconnected`, ...).
-/

set_option autoImplicit false

noncomputable section

open Work.RPV

open scoped NNReal

namespace Work.RPCore.GenFun

/-! ## The Euclidean structure, written out in coordinates -/

/-- The dot product on `PS = ℝ⁴` written out in coordinates. -/
def dot (u v : PS) : ℝ :=
  u.1.1 * v.1.1 + u.1.2 * v.1.2 + u.2.1 * v.2.1 + u.2.2 * v.2.2

theorem dot_apply (u v : PS) :
    dot u v = u.1.1 * v.1.1 + u.1.2 * v.1.2 + u.2.1 * v.2.1 + u.2.2 * v.2.2 := rfl

theorem dot_comm (u v : PS) : dot u v = dot v u := by
  simp only [dot_apply]; ring

/-- `dotL u = (v ↦ dot u v)` as a continuous linear map. -/
def dotL (u : PS) : PS →L[ℝ] ℝ :=
  u.1.1 • ((ContinuousLinearMap.fst ℝ ℝ ℝ).comp (ContinuousLinearMap.fst ℝ (ℝ × ℝ) (ℝ × ℝ))) +
  u.1.2 • ((ContinuousLinearMap.snd ℝ ℝ ℝ).comp (ContinuousLinearMap.fst ℝ (ℝ × ℝ) (ℝ × ℝ))) +
  u.2.1 • ((ContinuousLinearMap.fst ℝ ℝ ℝ).comp (ContinuousLinearMap.snd ℝ (ℝ × ℝ) (ℝ × ℝ))) +
  u.2.2 • ((ContinuousLinearMap.snd ℝ ℝ ℝ).comp (ContinuousLinearMap.snd ℝ (ℝ × ℝ) (ℝ × ℝ)))

@[simp] theorem dotL_apply (u v : PS) : dotL u v = dot u v := by
  simp [dotL, dot]

/-! ## The projection `gproj` and its derivative -/

/-- The projection `gproj ψ : (q,p) ↦ (q, P)` where `ψ (q,p) = (Q,P)`. -/
def gproj (ψ : PS → PS) (x : PS) : PS := (x.1, (ψ x).2)

@[simp] theorem gproj_apply (ψ : PS → PS) (x : PS) : gproj ψ x = (x.1, (ψ x).2) := rfl

/-- The displacement `gproj ψ - id`. -/
def gdisp (ψ : PS → PS) (x : PS) : PS := gproj ψ x - x

theorem gdisp_apply (ψ : PS → PS) (x : PS) : gdisp ψ x = ((0, 0), (ψ x).2 - x.2) := by
  simp [gdisp, gproj, Prod.ext_iff]

theorem gproj_eq_add_gdisp (ψ : PS → PS) (x : PS) : gproj ψ x = x + gdisp ψ x := by
  rw [gdisp]; abel

/-- The linear map `(q,p) ↦ (q, (A (q,p)).2)` for a continuous linear map `A`. -/
def gprojLin (A : PS →L[ℝ] PS) : PS →L[ℝ] PS :=
  (ContinuousLinearMap.fst ℝ (ℝ × ℝ) (ℝ × ℝ)).prod
    ((ContinuousLinearMap.snd ℝ (ℝ × ℝ) (ℝ × ℝ)).comp A)

@[simp] theorem gprojLin_apply (A : PS →L[ℝ] PS) (v : PS) :
    gprojLin A v = (v.1, (A v).2) := rfl

/-- The projection `(q,p) ↦ (0, p)`. -/
def projSnd : PS →L[ℝ] PS :=
  (0 : PS →L[ℝ] ℝ × ℝ).prod (ContinuousLinearMap.snd ℝ (ℝ × ℝ) (ℝ × ℝ))

@[simp] theorem projSnd_apply (v : PS) : projSnd v = ((0, 0), v.2) := rfl

theorem norm_projSnd_le_one : ‖projSnd‖ ≤ 1 := by
  apply ContinuousLinearMap.opNorm_le_bound _ zero_le_one
  intro v
  rw [one_mul]
  have h : ‖projSnd v‖ = ‖v.2‖ := by simp [projSnd, Prod.norm_def]
  rw [h, Prod.norm_def]
  exact le_max_right _ _

theorem gprojLin_sub_one (A : PS →L[ℝ] PS) : gprojLin A - 1 = projSnd.comp (A - 1) := by
  apply ContinuousLinearMap.ext
  intro v
  simp only [ContinuousLinearMap.comp_apply, gprojLin_apply, projSnd_apply, map_sub, map_one]
  ext <;> simp

theorem norm_gprojLin_sub_one_le (A : PS →L[ℝ] PS) : ‖gprojLin A - 1‖ ≤ ‖A - 1‖ := by
  rw [gprojLin_sub_one]
  calc ‖projSnd.comp (A - 1)‖ ≤ ‖projSnd‖ * ‖A - 1‖ :=
        ContinuousLinearMap.opNorm_comp_le projSnd (A - 1)
    _ ≤ 1 * ‖A - 1‖ := by gcongr; exact norm_projSnd_le_one
    _ = ‖A - 1‖ := one_mul _

/-! ## `gproj` and `gdisp` are smooth; `gdisp` has small derivative -/

theorem contDiff_gproj {ψ : PS → PS} (hψ : ContDiff ℝ 3 ψ) : ContDiff ℝ 3 (gproj ψ) := by
  have h : (gproj ψ) = fun x : PS => (x.1, (ψ x).2) := rfl
  rw [h]
  exact ContDiff.prodMk contDiff_fst (contDiff_snd.comp hψ)

theorem hasFDerivAt_gproj (ψ : PS → PS) (hψ : ContDiff ℝ 3 ψ) (x : PS) :
    HasFDerivAt (gproj ψ) (gprojLin (fderiv ℝ ψ x)) x := by
  have hd : Differentiable ℝ ψ := hψ.differentiable (by norm_num)
  have h1 : HasFDerivAt (fun y : PS => y.1)
      (ContinuousLinearMap.fst ℝ (ℝ × ℝ) (ℝ × ℝ)) x := hasFDerivAt_fst
  have h2 : HasFDerivAt (fun y : PS => (ψ y).2)
      ((ContinuousLinearMap.snd ℝ (ℝ × ℝ) (ℝ × ℝ)).comp (fderiv ℝ ψ x)) x :=
    (hd x).hasFDerivAt.snd
  have h3 := h1.prodMk h2
  exact h3

theorem fderiv_gproj (ψ : PS → PS) (hψ : ContDiff ℝ 3 ψ) (x : PS) :
    fderiv ℝ (gproj ψ) x = gprojLin (fderiv ℝ ψ x) :=
  (hasFDerivAt_gproj ψ hψ x).fderiv

theorem contDiff_gdisp {ψ : PS → PS} (hψ : ContDiff ℝ 3 ψ) : ContDiff ℝ 3 (gdisp ψ) := by
  have h : (gdisp ψ) = fun x : PS => gproj ψ x - x := rfl
  rw [h]
  exact (contDiff_gproj hψ).sub contDiff_id

theorem hasFDerivAt_gdisp (ψ : PS → PS) (hψ : ContDiff ℝ 3 ψ) (x : PS) :
    HasFDerivAt (gdisp ψ) (gprojLin (fderiv ℝ ψ x) - 1) x := by
  have h1 : HasFDerivAt (fun y : PS => gproj ψ y - y)
      (gprojLin (fderiv ℝ ψ x) - 1) x :=
    (hasFDerivAt_gproj ψ hψ x).sub (hasFDerivAt_id x)
  exact h1

theorem fderiv_gdisp (ψ : PS → PS) (hψ : ContDiff ℝ 3 ψ) (x : PS) :
    fderiv ℝ (gdisp ψ) x = gprojLin (fderiv ℝ ψ x) - 1 :=
  (hasFDerivAt_gdisp ψ hψ x).fderiv

theorem norm_fderiv_gdisp_le (ψ : PS → PS) (hψ : ContDiff ℝ 3 ψ)
    (hnear : ∀ x, ‖fderiv ℝ ψ x - ContinuousLinearMap.id ℝ PS‖ ≤ 1 / 4) (x : PS) :
    ‖fderiv ℝ (gdisp ψ) x‖ ≤ 1 / 4 := by
  rw [fderiv_gdisp ψ hψ x]
  calc ‖gprojLin (fderiv ℝ ψ x) - 1‖ ≤ ‖fderiv ℝ ψ x - 1‖ := norm_gprojLin_sub_one_le _
    _ ≤ 1 / 4 := hnear x

theorem lipschitzWith_gdisp (ψ : PS → PS) (hψ : ContDiff ℝ 3 ψ)
    (hnear : ∀ x, ‖fderiv ℝ ψ x - ContinuousLinearMap.id ℝ PS‖ ≤ 1 / 4) :
    LipschitzWith (1 / 4 : ℝ≥0) (gdisp ψ) := by
  apply lipschitzWith_of_nnnorm_fderiv_le
    ((contDiff_gdisp hψ).differentiable (by norm_num))
  intro x
  rw [← NNReal.coe_le_coe, coe_nnnorm]
  exact norm_fderiv_gdisp_le ψ hψ hnear x

/-! ## The linear equivalence attached to `fderiv (gproj ψ) x` -/

theorem isUnit_gprojLin (A : PS →L[ℝ] PS) (hA : ‖A - 1‖ ≤ 1 / 4) : IsUnit (gprojLin A) := by
  have h : ‖(1 : PS →L[ℝ] PS) - gprojLin A‖ < 1 := by
    rw [norm_sub_rev]
    calc ‖gprojLin A - 1‖ ≤ ‖A - 1‖ := norm_gprojLin_sub_one_le A
      _ ≤ 1 / 4 := hA
      _ < 1 := by norm_num
  simpa using isUnit_one_sub_of_norm_lt_one h

/-- The continuous linear equivalence `gprojLin A : PS ≃L[ℝ] PS`, available whenever
`‖A - 1‖ ≤ 1/4`. -/
def dgequivLin (A : PS →L[ℝ] PS) (hA : ‖A - 1‖ ≤ 1 / 4) : PS ≃L[ℝ] PS :=
  ContinuousLinearEquiv.ofUnit (isUnit_gprojLin A hA).unit

@[simp] theorem coe_dgequivLin (A : PS →L[ℝ] PS) (hA : ‖A - 1‖ ≤ 1 / 4) :
    ↑(dgequivLin A hA) = gprojLin A :=
  (isUnit_gprojLin A hA).unit_spec

/-! ## The set-theoretic inverse of `gproj ψ` -/

/-- A set-theoretic inverse of `gproj ψ`. -/
def invMap (ψ : PS → PS) : PS → PS := Function.invFun (gproj ψ)

/-- The momentum coordinate `p` of `invMap ψ y`. -/
def pfun (ψ : PS → PS) (y : PS) : ℝ × ℝ := (invMap ψ y).2

/-- The position coordinate `Q` of `ψ (invMap ψ y)`. -/
def Qfun (ψ : PS → PS) (y : PS) : ℝ × ℝ := (ψ (invMap ψ y)).1

/-- The coefficient vector field of the 1-form `β = (Q-q)dP + (p-P)dq` on the `(q,P)` chart. -/
def bvec (ψ : PS → PS) (y : PS) : PS := (pfun ψ y - y.2, Qfun ψ y - y.1)

theorem invMap_fst (ψ : PS → PS) {y : PS} (h : gproj ψ (invMap ψ y) = y) :
    (invMap ψ y).1 = y.1 := by
  simpa using congrArg Prod.fst h

theorem invMap_eq (ψ : PS → PS) {y : PS} (h : gproj ψ (invMap ψ y) = y) :
    invMap ψ y = (y.1, pfun ψ y) := by
  rw [← invMap_fst ψ h]; rfl

theorem psi_invMap (ψ : PS → PS) {y : PS} (h : gproj ψ (invMap ψ y) = y) :
    ψ (invMap ψ y) = (Qfun ψ y, y.2) := by
  have := congrArg Prod.snd h
  simp only [gproj_apply, Qfun] at this ⊢
  rw [← this]

end Work.RPCore.GenFun
