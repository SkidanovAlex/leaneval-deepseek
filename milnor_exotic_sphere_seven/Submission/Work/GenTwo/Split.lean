import Mathlib
import Submission.Work.Gen.EulerSplit
import Submission.Work.Gen.Euler
import Submission.Work.Thom.complexification
import Submission.Work.Projective.Model

-- Lean v4.35.0-rc3: restore v4.34 instance-unification transparency (port).
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
set_option synthInstance.maxHeartbeats 400000

set_option autoImplicit false
set_option maxHeartbeats 1600000
set_option linter.unusedSectionVars false
set_option linter.style.haveILetI false

/-!
# The holomorphic / antiholomorphic splitting of `ℂ ⊗_ℝ ℝ^{2n}`, in every dimension

This is the dimension-`n` version of `Submission/Work/Gen/EulerSplit.lean` (which is the case
`n = 4`): for the Euler sequence of `ℂPⁿ` one must compare the *complexified tangent space*, in the
real coordinates of the Euclidean chart, with two copies of `ℂⁿ` — the holomorphic and the
antiholomorphic tangent space.  We keep everything generic in `n` so that it can be instantiated at
`n = 2` (the case needed for the `c₂` of `ℂP²`) as well as at `n = 4`.
-/

namespace Work.Gen.E2

open Work.Projective Work.Thom

noncomputable section

variable {n : ℕ}

/-- The chosen real-linear isomorphism `ℂⁿ ≃L[ℝ] ℝ^{2n}` of the Euclidean chart of `ℂPⁿ`. -/
def E (n : ℕ) : (Fin n → ℂ) ≃L[ℝ] EuclideanSpace ℝ (Fin (2 * n)) := euclidEquiv n

/-! ## The splitting map and its inverse -/

/-- The candidate isomorphism `ℂⁿ × ℂⁿ → ℂ ⊗_ℝ ℝ^{2n}`. -/
def XiFun (h y : Fin n → ℂ) : EuclideanSpace ℂ (Fin (2 * n)) :=
  cxOfReal (E n (h + star y)) + cxMulI (cxOfReal (E n (Complex.I • (star y - h))))

theorem XiFun_add (h₁ h₂ y₁ y₂ : Fin n → ℂ) :
    XiFun (h₁ + h₂) (y₁ + y₂) = XiFun h₁ y₁ + XiFun h₂ y₂ := by
  have e1 : h₁ + h₂ + star (y₁ + y₂) = (h₁ + star y₁) + (h₂ + star y₂) := by
    rw [star_add]; abel
  have e2 : (Complex.I : ℂ) • (star (y₁ + y₂) - (h₁ + h₂))
      = (Complex.I : ℂ) • (star y₁ - h₁) + (Complex.I : ℂ) • (star y₂ - h₂) := by
    have h3 : star (y₁ + y₂) - (h₁ + h₂) = (star y₁ - h₁) + (star y₂ - h₂) := by
      rw [star_add]; abel
    rw [h3, smul_add]
  unfold XiFun
  simp only [e1, e2, map_add]
  abel

theorem XiFun_smul_real (r : ℝ) (h y : Fin n → ℂ) :
    XiFun (r • h) (r • y) = r • XiFun h y := by
  have hs : star (r • y) = r • star y := Work.Gen.star_smul_real r y
  have e1 : r • h + r • star y = r • (h + star y) := by rw [smul_add]
  have e2 : (Complex.I : ℂ) • (r • star y - r • h) = r • ((Complex.I : ℂ) • (star y - h)) := by
    rw [← smul_sub, smul_comm]
  unfold XiFun
  rw [hs]
  rw [e1]
  rw [e2]
  simp only [map_smul]
  rw [smul_add]

theorem XiFun_smul_I (h y : Fin n → ℂ) :
    XiFun ((Complex.I : ℂ) • h) ((Complex.I : ℂ) • y) = (Complex.I : ℂ) • XiFun h y := by
  have hs : star ((Complex.I : ℂ) • y) = -((Complex.I : ℂ) • star y) := Work.Gen.star_smul_I y
  have e1 : (Complex.I : ℂ) • h + -((Complex.I : ℂ) • star y)
      = (Complex.I : ℂ) • (h - star y) := by
    rw [← smul_neg, ← smul_add, sub_eq_add_neg]
  have e2 : (Complex.I : ℂ) • (-((Complex.I : ℂ) • star y) - (Complex.I : ℂ) • h)
      = star y + h := by
    have h3 : -((Complex.I : ℂ) • star y) - (Complex.I : ℂ) • h
        = -((Complex.I : ℂ) • (star y + h)) := by rw [smul_add]; abel
    rw [h3, smul_neg, smul_smul, Complex.I_mul_I, neg_one_smul, neg_neg]
  have e3 : E n ((Complex.I : ℂ) • (h - star y)) = -E n ((Complex.I : ℂ) • (star y - h)) := by
    rw [show (Complex.I : ℂ) • (h - star y) = -((Complex.I : ℂ) • (star y - h)) from by
      rw [← smul_neg]; congr 1; abel, map_neg]
  have e4 : E n (star y + h) = E n (h + star y) := by rw [add_comm]
  unfold XiFun
  rw [hs]
  rw [e1]
  rw [e2]
  rw [e3]
  rw [e4]
  rw [map_neg]
  rw [smul_add]
  rw [Work.Gen.smul_I_eq_cxMulI]
  rw [← Work.Gen.smul_I_eq_cxMulI (cxOfReal (E n ((Complex.I : ℂ) • (star y - h))))]
  rw [smul_smul, Complex.I_mul_I, neg_one_smul]
  abel

theorem XiFun_smul (c : ℂ) (h y : Fin n → ℂ) :
    XiFun (c • h) (c • y) = c • XiFun h y := by
  nth_rewrite 1 [Work.Gen.smul_eq_re_smul_add_im_smul_I c h]
  nth_rewrite 1 [Work.Gen.smul_eq_re_smul_add_im_smul_I c y]
  rw [XiFun_add]
  rw [XiFun_smul_real c.re]
  rw [XiFun_smul_real c.im]
  rw [XiFun_smul_I]
  rw [Work.Gen.smul_I_eq_cxMulI]
  exact (cx_complex_smul_eq c (XiFun h y)).symm

/-- The splitting map, as a `ℂ`-linear map. -/
def Xi : ((Fin n → ℂ) × (Fin n → ℂ)) →ₗ[ℂ] EuclideanSpace ℂ (Fin (2 * n)) where
  toFun p := XiFun p.1 p.2
  map_add' p q := by
    obtain ⟨h₁, y₁⟩ := p
    obtain ⟨h₂, y₂⟩ := q
    exact XiFun_add h₁ h₂ y₁ y₂
  map_smul' c p := by
    obtain ⟨h, y⟩ := p
    exact XiFun_smul c h y

/-- The inverse of `XiFun`. -/
def XiInvFun (ξ : EuclideanSpace ℂ (Fin (2 * n))) : (Fin n → ℂ) × (Fin n → ℂ) :=
  ((2 : ℂ)⁻¹ • ((E n).symm (cxRePart ξ) + (Complex.I : ℂ) • (E n).symm (cxImPart ξ)),
    star ((2 : ℂ)⁻¹ • ((E n).symm (cxRePart ξ) - (Complex.I : ℂ) • (E n).symm (cxImPart ξ))))

theorem cxRePart_XiFun (h y : Fin n → ℂ) :
    cxRePart (XiFun h y) = E n (h + star y) := by
  unfold XiFun
  simp only [map_add, cxRePart_cxMulI, cxRePart_cxOfReal, cxImPart_cxOfReal, neg_zero, add_zero]

theorem cxImPart_XiFun (h y : Fin n → ℂ) :
    cxImPart (XiFun h y) = E n ((Complex.I : ℂ) • (star y - h)) := by
  unfold XiFun
  simp only [map_add, cxImPart_cxMulI, cxImPart_cxOfReal, cxRePart_cxOfReal, zero_add]

theorem XiInvFun_XiFun (h y : Fin n → ℂ) : XiInvFun (XiFun h y) = (h, y) := by
  have h1 := cxRePart_XiFun (n := n) h y
  have h2 := cxImPart_XiFun (n := n) h y
  have hII : (Complex.I : ℂ) • ((Complex.I : ℂ) • (star y - h)) = -(star y - h) := by
    rw [smul_smul, Complex.I_mul_I, neg_one_smul]
  rw [XiInvFun]
  rw [h1, h2, ContinuousLinearEquiv.symm_apply_apply, ContinuousLinearEquiv.symm_apply_apply]
  rw [hII]
  refine Prod.ext ?_ ?_
  · have aux : (h + star y) + -(star y - h) = h + h := by abel
    rw [aux, ← two_smul ℂ h, smul_smul, inv_mul_cancel₀ (two_ne_zero), one_smul]
  · have aux : (h + star y) - -(star y - h) = star y + star y := by abel
    rw [aux, ← two_smul ℂ (star y), smul_smul, inv_mul_cancel₀ (two_ne_zero), one_smul,
      star_star]

theorem XiFun_XiInvFun (ξ : EuclideanSpace ℂ (Fin (2 * n))) :
    XiFun (XiInvFun ξ).1 (XiInvFun ξ).2 = ξ := by
  set a : Fin n → ℂ := (E n).symm (cxRePart ξ) with ha
  set b : Fin n → ℂ := (E n).symm (cxImPart ξ) with hb
  have h1 : (XiInvFun ξ).1 = (2 : ℂ)⁻¹ • (a + (Complex.I : ℂ) • b) := by
    rw [XiInvFun]
  have h2 : (XiInvFun ξ).2 = star ((2 : ℂ)⁻¹ • (a - (Complex.I : ℂ) • b)) := by
    rw [XiInvFun]
  have e1 : (2 : ℂ)⁻¹ • (a + (Complex.I : ℂ) • b)
      + star (star ((2 : ℂ)⁻¹ • (a - (Complex.I : ℂ) • b))) = a := by
    rw [star_star, ← smul_add]
    have aux : (a + (Complex.I : ℂ) • b) + (a - (Complex.I : ℂ) • b) = (2 : ℂ) • a := by
      rw [two_smul ℂ a]; abel
    rw [aux, smul_smul, inv_mul_cancel₀ (two_ne_zero), one_smul]
  have e2 : (Complex.I : ℂ) •
      (star (star ((2 : ℂ)⁻¹ • (a - (Complex.I : ℂ) • b)))
        - (2 : ℂ)⁻¹ • (a + (Complex.I : ℂ) • b)) = b := by
    rw [star_star, ← smul_sub]
    have aux : (a - (Complex.I : ℂ) • b) - (a + (Complex.I : ℂ) • b)
        = -((2 : ℂ) • ((Complex.I : ℂ) • b)) := by
      rw [two_smul ℂ ((Complex.I : ℂ) • b)]; abel
    have hsc : (Complex.I * (2 : ℂ)⁻¹) * (2 * Complex.I) = -1 := by
      rw [mul_assoc, ← mul_assoc (2 : ℂ)⁻¹ (2 : ℂ) Complex.I, inv_mul_cancel₀ (two_ne_zero),
        one_mul, Complex.I_mul_I]
    rw [aux, ← smul_neg, smul_neg, smul_smul, smul_smul, smul_neg, smul_smul, hsc,
      neg_one_smul, neg_neg]
  rw [h1, h2]
  unfold XiFun
  rw [e1, e2]
  rw [ha, hb, ContinuousLinearEquiv.apply_symm_apply, ContinuousLinearEquiv.apply_symm_apply]
  rw [cxOfReal_cxRePart_add_cxMulI_cxImPart]

theorem XiInvFun_Xi (p : (Fin n → ℂ) × (Fin n → ℂ)) : XiInvFun (Xi p) = p := by
  obtain ⟨h, y⟩ := p
  exact XiInvFun_XiFun h y

/-- **The `ℂ`-linear isomorphism `ℂⁿ × ℂⁿ ≃ ℂ ⊗_ℝ ℝ^{2n}`** underlying the holomorphic /
antiholomorphic splitting of the complexified tangent space. -/
def XiEquiv : ((Fin n → ℂ) × (Fin n → ℂ)) ≃L[ℂ] EuclideanSpace ℂ (Fin (2 * n)) :=
  (LinearEquiv.ofBijective Xi
    ⟨fun p q h => by
      have hh := congrArg XiInvFun h
      rw [XiInvFun_Xi, XiInvFun_Xi] at hh
      exact hh,
     fun ξ => ⟨XiInvFun ξ, XiFun_XiInvFun ξ⟩⟩).toContinuousLinearEquiv

theorem XiEquiv_apply (h y : Fin n → ℂ) : XiEquiv (h, y) = XiFun h y := rfl

theorem XiEquiv_symm_apply (ξ : EuclideanSpace ℂ (Fin (2 * n))) : XiEquiv.symm ξ = XiInvFun ξ := by
  apply XiEquiv.injective
  rw [ContinuousLinearEquiv.apply_symm_apply, XiEquiv_apply, XiFun_XiInvFun]

/-- The holomorphic coordinate of `ξ`. -/
def holPart : EuclideanSpace ℂ (Fin (2 * n)) →L[ℂ] (Fin n → ℂ) :=
  (ContinuousLinearMap.fst ℂ _ _).comp XiEquiv.symm.toContinuousLinearMap

/-- The (conjugated) antiholomorphic coordinate of `ξ`. -/
def antiPart : EuclideanSpace ℂ (Fin (2 * n)) →L[ℂ] (Fin n → ℂ) :=
  (ContinuousLinearMap.snd ℂ _ _).comp XiEquiv.symm.toContinuousLinearMap

theorem holPart_mk (h y : Fin n → ℂ) : holPart (XiEquiv (h, y)) = h := by
  simp [holPart]

theorem antiPart_mk (h y : Fin n → ℂ) : antiPart (XiEquiv (h, y)) = y := by
  simp [antiPart]

theorem holPart_XiFun (h y : Fin n → ℂ) : holPart (XiFun h y) = h := by
  rw [← XiEquiv_apply h y, holPart_mk]

theorem antiPart_XiFun (h y : Fin n → ℂ) : antiPart (XiFun h y) = y := by
  rw [← XiEquiv_apply h y, antiPart_mk]

theorem holPart_apply (ξ : EuclideanSpace ℂ (Fin (2 * n))) : holPart ξ = (XiInvFun ξ).1 := by
  simp [holPart, XiEquiv_symm_apply]

theorem antiPart_apply (ξ : EuclideanSpace ℂ (Fin (2 * n))) : antiPart ξ = (XiInvFun ξ).2 := by
  simp [antiPart, XiEquiv_symm_apply]

theorem holPart_antiPart (ξ : EuclideanSpace ℂ (Fin (2 * n))) :
    (holPart ξ, antiPart ξ) = XiEquiv.symm ξ := by
  rw [holPart_apply, antiPart_apply, Prod.mk.eta, XiEquiv_symm_apply]

theorem XiEquiv_holPart_antiPart (ξ : EuclideanSpace ℂ (Fin (2 * n))) :
    XiEquiv (holPart ξ, antiPart ξ) = ξ := by
  rw [holPart_antiPart, ContinuousLinearEquiv.apply_symm_apply]

/-! ## Equivariance under the complexification of a holomorphic transition -/

/-- The complexified real-linear endomorphism attached to a `ℂ`-linear `L : ℂⁿ → ℂⁿ`. -/
def T (L : (Fin n → ℂ) →L[ℂ] (Fin n → ℂ)) :
    EuclideanSpace ℝ (Fin (2 * n)) →L[ℝ] EuclideanSpace ℝ (Fin (2 * n)) :=
  (E n).toContinuousLinearMap.comp
    ((ContinuousLinearMap.restrictScalars ℝ L).comp (E n).symm.toContinuousLinearMap)

theorem T_apply (L : (Fin n → ℂ) →L[ℂ] (Fin n → ℂ)) (z : Fin n → ℂ) :
    T L (E n z) = E n (L z) := by
  simp [T]

/-- **The equivariance of `Ξ`** under `cxTrans (E L E⁻¹)`: the first coordinate transforms by
`L`, the second by the conjugate `star ∘ L ∘ star`. -/
theorem XiFun_cxTrans (L : (Fin n → ℂ) →L[ℂ] (Fin n → ℂ)) (h y : Fin n → ℂ) :
    XiFun (L h) (star (L (star y))) = cxTrans (T L) (XiFun h y) := by
  have e1 : L h + star (star (L (star y))) = L (h + star y) := by
    rw [star_star, map_add]
  have e2 : (Complex.I : ℂ) • (star (star (L (star y))) - L h)
      = L ((Complex.I : ℂ) • (star y - h)) := by
    rw [star_star, ← map_sub, ← map_smul]
  rw [cxTrans_apply]
  rw [cxRePart_XiFun, cxImPart_XiFun, T_apply, T_apply]
  unfold XiFun
  rw [e1]
  rw [e2]

/-- **The transition law of the `T^{1,0}` part.** -/
theorem holPart_cxTrans (L : (Fin n → ℂ) →L[ℂ] (Fin n → ℂ))
    (ξ : EuclideanSpace ℂ (Fin (2 * n))) :
    holPart (cxTrans (T L) ξ) = L (holPart ξ) := by
  nth_rewrite 1 [← XiEquiv_holPart_antiPart ξ]
  rw [XiEquiv_apply, ← XiFun_cxTrans L (holPart ξ) (antiPart ξ), holPart_XiFun]

/-- **The transition law of the `T^{0,1}` part.** -/
theorem antiPart_cxTrans (L : (Fin n → ℂ) →L[ℂ] (Fin n → ℂ))
    (ξ : EuclideanSpace ℂ (Fin (2 * n))) :
    antiPart (cxTrans (T L) ξ) = star (L (star (antiPart ξ))) := by
  nth_rewrite 1 [← XiEquiv_holPart_antiPart ξ]
  rw [XiEquiv_apply, ← XiFun_cxTrans L (holPart ξ) (antiPart ξ), antiPart_XiFun]

end

end Work.Gen.E2
