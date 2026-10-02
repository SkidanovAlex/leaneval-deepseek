import Mathlib
import Submission.Work.Gen.EulerGauge
import Submission.Work.Gen.EulerModel
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
# The holomorphic / antiholomorphic splitting of `ℂ ⊗_ℝ ℝ⁸`

For the Euler sequence we must compare the *complexified tangent space* of `ℂP⁴` — presented as
`ℂ⁸ = ℂ ⊗_ℝ ℝ⁸`, in the real coordinates of the Euclidean chart `euclidChart 4 p` — with two
copies of `ℂ⁴`: the holomorphic and the antiholomorphic tangent space.

The real chart coordinates are related to the complex chart coordinates by the (arbitrary but
fixed) real isomorphism `E4 = euclidEquiv 4 : ℂ⁴ ≃L[ℝ] ℝ⁸`.  The complex structure on the tangent
space is `J = E4 J₀ E4⁻¹` (`J₀` = multiplication by `I` on `ℂ⁴`), and its `ℂ`-linear extension to
`ℂ⁸` is `cxTrans J`.  The `(1,0)` and `(0,1)` parts of `cxTrans J` are the holomorphic and the
antiholomorphic tangent space, and

`Ξ : ℂ⁴ × ℂ⁴ → ℂ⁸`,  `Ξ (h, y) = cxOfReal (E4 (h + star y)) + cxMulI (cxOfReal (E4 (I • (star y - h))))`

is the corresponding `ℂ`-linear isomorphism, with inverse

`Ξ⁻¹ ξ = ((E4⁻¹ (re ξ) + I • E4⁻¹ (im ξ)) / 2, star ((E4⁻¹ (re ξ) - I • E4⁻¹ (im ξ)) / 2))`.

The component functionals `holPart`, `antiPart` are the two coordinates of `Ξ⁻¹`, and the point of
the file is the equivariance

`holPart (cxTrans (E4 ∘L (L : ℂ⁴ →_ℂ ℂ⁴) ∘L E4⁻¹) ξ) = L (holPart ξ)`,
`antiPart (cxTrans (E4 ∘L (L : ℂ⁴ →_ℂ ℂ⁴) ∘L E4⁻¹) ξ) = star (L (star (antiPart ξ)))`

for every `ℂ`-linear `L` — exactly the transition laws of the `T^{1,0}` and `T^{0,1}` parts of the
complexified tangent bundle of `ℂP⁴`.
-/

namespace Work.Gen

open Work.Projective Work.Thom

noncomputable section

/-- The chosen real-linear isomorphism `ℂ⁴ ≃L[ℝ] ℝ⁸` of the Euclidean chart of `ℂP⁴`. -/
def E4 : (Fin 4 → ℂ) ≃L[ℝ] EuclideanSpace ℝ (Fin 8) := euclidEquiv 4

/-! ## Elementary computations with the scalar action -/

theorem smul_eq_re_smul_add_im_smul_I {k : ℕ} (c : ℂ) (v : Fin k → ℂ) :
    c • v = c.re • v + c.im • (Complex.I • v) := by
  nth_rewrite 1 [← Complex.re_add_im c]
  rw [add_smul, mul_smul]
  simp

theorem star_smul_real {k : ℕ} (r : ℝ) (v : Fin k → ℂ) : star (r • v) = r • star v := by
  rw [star_smul]; simp

theorem star_smul_I {k : ℕ} (v : Fin k → ℂ) :
    star (Complex.I • v) = -((Complex.I : ℂ) • star v) := by
  rw [star_smul]; simp [Complex.conj_I]

theorem smul_I_eq_cxMulI {k : ℕ} (v : EuclideanSpace ℂ (Fin k)) :
    (Complex.I : ℂ) • v = cxMulI v := by
  ext t; simp [cxMulI]

/-! ## The splitting map and its inverse -/

/-- The candidate isomorphism `ℂ⁴ × ℂ⁴ → ℂ ⊗_ℝ ℝ⁸`. -/
def XiFun (h y : Fin 4 → ℂ) : EuclideanSpace ℂ (Fin 8) :=
  cxOfReal (E4 (h + star y)) + cxMulI (cxOfReal (E4 (Complex.I • (star y - h))))

theorem XiFun_add (h₁ h₂ y₁ y₂ : Fin 4 → ℂ) :
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

theorem XiFun_smul_real (r : ℝ) (h y : Fin 4 → ℂ) :
    XiFun (r • h) (r • y) = r • XiFun h y := by
  have hs : star (r • y) = r • star y := star_smul_real r y
  have e1 : r • h + r • star y = r • (h + star y) := by rw [smul_add]
  have e2 : (Complex.I : ℂ) • (r • star y - r • h) = r • ((Complex.I : ℂ) • (star y - h)) := by
    rw [← smul_sub, smul_comm]
  unfold XiFun
  rw [hs]
  rw [e1]
  rw [e2]
  simp only [map_smul]
  rw [smul_add]

theorem XiFun_smul_I (h y : Fin 4 → ℂ) :
    XiFun ((Complex.I : ℂ) • h) ((Complex.I : ℂ) • y) = (Complex.I : ℂ) • XiFun h y := by
  have hs : star ((Complex.I : ℂ) • y) = -((Complex.I : ℂ) • star y) := star_smul_I y
  have e1 : (Complex.I : ℂ) • h + -((Complex.I : ℂ) • star y)
      = (Complex.I : ℂ) • (h - star y) := by
    rw [← smul_neg, ← smul_add, sub_eq_add_neg]
  have e2 : (Complex.I : ℂ) • (-((Complex.I : ℂ) • star y) - (Complex.I : ℂ) • h)
      = star y + h := by
    have h3 : -((Complex.I : ℂ) • star y) - (Complex.I : ℂ) • h
        = -((Complex.I : ℂ) • (star y + h)) := by rw [smul_add]; abel
    rw [h3, smul_neg, smul_smul, Complex.I_mul_I, neg_one_smul, neg_neg]
  have e3 : E4 ((Complex.I : ℂ) • (h - star y)) = -E4 ((Complex.I : ℂ) • (star y - h)) := by
    rw [show (Complex.I : ℂ) • (h - star y) = -((Complex.I : ℂ) • (star y - h)) from by
      rw [← smul_neg]; congr 1; abel, map_neg]
  have e4 : E4 (star y + h) = E4 (h + star y) := by rw [add_comm]
  unfold XiFun
  rw [hs]
  rw [e1]
  rw [e2]
  rw [e3]
  rw [e4]
  rw [map_neg]
  rw [smul_add]
  rw [smul_I_eq_cxMulI]
  rw [← smul_I_eq_cxMulI (cxOfReal (E4 ((Complex.I : ℂ) • (star y - h))))]
  rw [smul_smul, Complex.I_mul_I, neg_one_smul]
  abel

theorem XiFun_smul (c : ℂ) (h y : Fin 4 → ℂ) :
    XiFun (c • h) (c • y) = c • XiFun h y := by
  nth_rewrite 1 [smul_eq_re_smul_add_im_smul_I c h]
  nth_rewrite 1 [smul_eq_re_smul_add_im_smul_I c y]
  rw [XiFun_add]
  rw [XiFun_smul_real c.re]
  rw [XiFun_smul_real c.im]
  rw [XiFun_smul_I]
  rw [smul_I_eq_cxMulI]
  exact (cx_complex_smul_eq c (XiFun h y)).symm

/-- The splitting map, as a `ℂ`-linear map. -/
def Xi : ((Fin 4 → ℂ) × (Fin 4 → ℂ)) →ₗ[ℂ] EuclideanSpace ℂ (Fin 8) where
  toFun p := XiFun p.1 p.2
  map_add' p q := by
    obtain ⟨h₁, y₁⟩ := p
    obtain ⟨h₂, y₂⟩ := q
    exact XiFun_add h₁ h₂ y₁ y₂
  map_smul' c p := by
    obtain ⟨h, y⟩ := p
    exact XiFun_smul c h y

/-- The inverse of `XiFun`. -/
def XiInvFun (ξ : EuclideanSpace ℂ (Fin 8)) : (Fin 4 → ℂ) × (Fin 4 → ℂ) :=
  ((2 : ℂ)⁻¹ • (E4.symm (cxRePart ξ) + (Complex.I : ℂ) • E4.symm (cxImPart ξ)),
    star ((2 : ℂ)⁻¹ • (E4.symm (cxRePart ξ) - (Complex.I : ℂ) • E4.symm (cxImPart ξ))))

theorem cxRePart_XiFun (h y : Fin 4 → ℂ) :
    cxRePart (XiFun h y) = E4 (h + star y) := by
  unfold XiFun
  simp only [map_add, cxRePart_cxMulI, cxRePart_cxOfReal, cxImPart_cxOfReal, neg_zero, add_zero]

theorem cxImPart_XiFun (h y : Fin 4 → ℂ) :
    cxImPart (XiFun h y) = E4 ((Complex.I : ℂ) • (star y - h)) := by
  unfold XiFun
  simp only [map_add, cxImPart_cxMulI, cxImPart_cxOfReal, cxRePart_cxOfReal, zero_add]

theorem XiInvFun_XiFun (h y : Fin 4 → ℂ) : XiInvFun (XiFun h y) = (h, y) := by
  have h1 := cxRePart_XiFun h y
  have h2 := cxImPart_XiFun h y
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

theorem XiFun_XiInvFun (ξ : EuclideanSpace ℂ (Fin 8)) :
    XiFun (XiInvFun ξ).1 (XiInvFun ξ).2 = ξ := by
  set a : Fin 4 → ℂ := E4.symm (cxRePart ξ) with ha
  set b : Fin 4 → ℂ := E4.symm (cxImPart ξ) with hb
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

theorem XiInvFun_Xi (p : (Fin 4 → ℂ) × (Fin 4 → ℂ)) : XiInvFun (Xi p) = p := by
  obtain ⟨h, y⟩ := p
  exact XiInvFun_XiFun h y

/-- **The `ℂ`-linear isomorphism `ℂ⁴ × ℂ⁴ ≃ ℂ ⊗_ℝ ℝ⁸`** underlying the holomorphic /
antiholomorphic splitting of the complexified tangent space. -/
def XiEquiv : ((Fin 4 → ℂ) × (Fin 4 → ℂ)) ≃L[ℂ] EuclideanSpace ℂ (Fin 8) :=
  (LinearEquiv.ofBijective Xi
    ⟨fun p q h => by
      have hh := congrArg XiInvFun h
      rw [XiInvFun_Xi, XiInvFun_Xi] at hh
      exact hh,
     fun ξ => ⟨XiInvFun ξ, XiFun_XiInvFun ξ⟩⟩).toContinuousLinearEquiv

theorem XiEquiv_apply (h y : Fin 4 → ℂ) : XiEquiv (h, y) = XiFun h y := rfl

theorem XiEquiv_symm_apply (ξ : EuclideanSpace ℂ (Fin 8)) : XiEquiv.symm ξ = XiInvFun ξ := by
  apply XiEquiv.injective
  rw [ContinuousLinearEquiv.apply_symm_apply, XiEquiv_apply, XiFun_XiInvFun]

/-- The holomorphic coordinate of `ξ`. -/
def holPart : EuclideanSpace ℂ (Fin 8) →L[ℂ] (Fin 4 → ℂ) :=
  (ContinuousLinearMap.fst ℂ _ _).comp XiEquiv.symm.toContinuousLinearMap

/-- The (conjugated) antiholomorphic coordinate of `ξ`. -/
def antiPart : EuclideanSpace ℂ (Fin 8) →L[ℂ] (Fin 4 → ℂ) :=
  (ContinuousLinearMap.snd ℂ _ _).comp XiEquiv.symm.toContinuousLinearMap

theorem holPart_mk (h y : Fin 4 → ℂ) : holPart (XiEquiv (h, y)) = h := by
  simp [holPart]

theorem antiPart_mk (h y : Fin 4 → ℂ) : antiPart (XiEquiv (h, y)) = y := by
  simp [antiPart]

theorem holPart_XiFun (h y : Fin 4 → ℂ) : holPart (XiFun h y) = h := by
  rw [← XiEquiv_apply h y, holPart_mk]

theorem antiPart_XiFun (h y : Fin 4 → ℂ) : antiPart (XiFun h y) = y := by
  rw [← XiEquiv_apply h y, antiPart_mk]

theorem holPart_apply (ξ : EuclideanSpace ℂ (Fin 8)) : holPart ξ = (XiInvFun ξ).1 := by
  simp [holPart, XiEquiv_symm_apply]

theorem antiPart_apply (ξ : EuclideanSpace ℂ (Fin 8)) : antiPart ξ = (XiInvFun ξ).2 := by
  simp [antiPart, XiEquiv_symm_apply]

theorem holPart_antiPart (ξ : EuclideanSpace ℂ (Fin 8)) :
    (holPart ξ, antiPart ξ) = XiEquiv.symm ξ := by
  rw [holPart_apply, antiPart_apply, Prod.mk.eta, XiEquiv_symm_apply]

theorem XiEquiv_holPart_antiPart (ξ : EuclideanSpace ℂ (Fin 8)) :
    XiEquiv (holPart ξ, antiPart ξ) = ξ := by
  rw [holPart_antiPart, ContinuousLinearEquiv.apply_symm_apply]

/-! ## Equivariance under the complexification of a holomorphic transition -/

/-- The complexified real-linear endomorphism attached to a `ℂ`-linear `L : ℂ⁴ → ℂ⁴`. -/
def T4 (L : (Fin 4 → ℂ) →L[ℂ] (Fin 4 → ℂ)) :
    EuclideanSpace ℝ (Fin 8) →L[ℝ] EuclideanSpace ℝ (Fin 8) :=
  E4.toContinuousLinearMap.comp
    ((ContinuousLinearMap.restrictScalars ℝ L).comp E4.symm.toContinuousLinearMap)

theorem T4_apply (L : (Fin 4 → ℂ) →L[ℂ] (Fin 4 → ℂ)) (z : Fin 4 → ℂ) :
    T4 L (E4 z) = E4 (L z) := by
  simp [T4]

/-- **The equivariance of `Ξ`** under `cxTrans (E4 L E4⁻¹)`: the first coordinate transforms by
`L`, the second by the conjugate `star ∘ L ∘ star`. -/
theorem XiFun_cxTrans (L : (Fin 4 → ℂ) →L[ℂ] (Fin 4 → ℂ)) (h y : Fin 4 → ℂ) :
    XiFun (L h) (star (L (star y))) = cxTrans (T4 L) (XiFun h y) := by
  have e1 : L h + star (star (L (star y))) = L (h + star y) := by
    rw [star_star, map_add]
  have e2 : (Complex.I : ℂ) • (star (star (L (star y))) - L h)
      = L ((Complex.I : ℂ) • (star y - h)) := by
    rw [star_star, ← map_sub, ← map_smul]
  rw [cxTrans_apply]
  rw [cxRePart_XiFun, cxImPart_XiFun, T4_apply, T4_apply]
  unfold XiFun
  rw [e1]
  rw [e2]

/-- **The transition law of the `T^{1,0}` part.** -/
theorem holPart_cxTrans (L : (Fin 4 → ℂ) →L[ℂ] (Fin 4 → ℂ)) (ξ : EuclideanSpace ℂ (Fin 8)) :
    holPart (cxTrans (T4 L) ξ) = L (holPart ξ) := by
  nth_rewrite 1 [← XiEquiv_holPart_antiPart ξ]
  rw [XiEquiv_apply, ← XiFun_cxTrans L (holPart ξ) (antiPart ξ), holPart_XiFun]

/-- **The transition law of the `T^{0,1}` part.** -/
theorem antiPart_cxTrans (L : (Fin 4 → ℂ) →L[ℂ] (Fin 4 → ℂ)) (ξ : EuclideanSpace ℂ (Fin 8)) :
    antiPart (cxTrans (T4 L) ξ) = star (L (star (antiPart ξ))) := by
  nth_rewrite 1 [← XiEquiv_holPart_antiPart ξ]
  rw [XiEquiv_apply, ← XiFun_cxTrans L (holPart ξ) (antiPart ξ), antiPart_XiFun]

end

end Work.Gen
