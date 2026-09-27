import Mathlib
import Submission.Work.Drive.cappingProjCoords
import Submission.Work.Drive.confProjVecOf_fderiv_span

/-!
# The differential of `y ↦ confProjVecOf (U y) (D y)`

`Work.Drive.confProjVecOf u d = (u · √(1 - ‖d‖²/2), ū · d/√2)` is the sphere lift of a configuration
point `(d, η)` of the capping (`u² = circleOf η`); see `Submission/Work/Drive/cappingProjCoords`.
Here `U : ℝ² → ℂ` is a unit complex-valued map and `D : ℝ² → ℂ` a map into the disc, and the file
proves that the composite `y ↦ confProjVecOf (U y) (D y)` is a *linear* immersion at every point at
which the pair `(U, D)` is an immersion: if its differential at `x` applied to `w` is radial, i.e.
lies in the line spanned by the value `confProjVecOf (U x) (D x)`, then `w = 0`.

The mathematical content is the explicit computation of the differentials of the two coordinates
`(u, d) ↦ u · √(1 - ‖d‖²/2)` and `(u, d) ↦ ū · d/√2` at a point with `‖u‖ = 1`, `‖d‖² < 2`, from
which one gets, for `d(confProjVecOf)` applied to `(a, b)`,

* second coordinate: `(ā · d + ū · b)/√2 = 0`,
* first coordinate: `a · √(1 - ‖d‖²/2) - u · ⟪d, b⟫/(2√(1 - ‖d‖²/2)) = 0`;

together these force `a = b = 0`.  The ingredient isolating `b` is the derivative of the real
square-root factor, `d(√(1 - ‖z‖²/2))_z(b) = -⟪z, b⟫/(2√(1 - ‖z‖²/2))`, which is why the real inner
product of `ℂ` appears.  The passage from the sphere constraint to `λ = 0` is the standard
"the differential of a curve on the unit sphere is tangent to the sphere".
-/

namespace Work.Drive

open scoped Topology

noncomputable section

/-- The square-root factor `√(1 - ‖z‖²/2)` of `confProjVecOf`, as a complex number.  It is an
`abbrev` so that it unfolds definitionally inside `confProjVecOf`. -/
abbrev confProjSF (z : ℂ) : ℂ := ((Real.sqrt (1 - ‖z‖ ^ 2 / 2) : ℝ) : ℂ)

/-! ### Smoothness and derivative of the square-root factor -/

lemma contDiffAt_confProjSF (d : ℂ) (hd : 1 - ‖d‖ ^ 2 / 2 ≠ 0) {n : WithTop ℕ∞} :
    ContDiffAt ℝ n confProjSF d := by
  have hnorm2 : ContDiffAt ℝ n (fun z : ℂ => ‖z‖ ^ 2) d :=
    (contDiff_norm_sq ℝ (E := ℂ) (n := n)).contDiffAt
  have hinner : ContDiffAt ℝ n (fun z : ℂ => 1 - ‖z‖ ^ 2 / 2) d :=
    contDiffAt_const.sub (hnorm2.div_const 2)
  have hsq : ContDiffAt ℝ n (fun z : ℂ => Real.sqrt (1 - ‖z‖ ^ 2 / 2)) d :=
    (Real.contDiffAt_sqrt hd).comp d hinner
  exact (Complex.ofRealCLM.contDiff.contDiffAt).comp d hsq

lemma hasFDerivAt_confProjSF (d : ℂ) (hd : 1 - ‖d‖ ^ 2 / 2 ≠ 0) :
    HasFDerivAt confProjSF
      (Complex.ofRealCLM.comp ((1 / (2 * Real.sqrt (1 - ‖d‖ ^ 2 / 2))) • (-innerSL ℝ d))) d := by
  have hsq : HasFDerivAt (fun z : ℂ => ‖z‖ ^ 2) ((2 : ℕ) • innerSL ℝ d) d := by
    have h := (hasFDerivAt_id (𝕜 := ℝ) d).norm_sq
    simpa using h
  have h2 : HasFDerivAt (fun z : ℂ => ‖z‖ ^ 2 / 2) (((2 : ℝ)⁻¹) • ((2 : ℕ) • innerSL ℝ d)) d := by
    have h := hsq.mul_const ((2 : ℝ)⁻¹)
    simpa [div_eq_mul_inv] using h
  have hT : HasFDerivAt (fun z : ℂ => (1 - ‖z‖ ^ 2 / 2 : ℝ))
      (0 - ((2 : ℝ)⁻¹) • ((2 : ℕ) • innerSL ℝ d)) d :=
    (hasFDerivAt_const (1 : ℝ) d).sub h2
  have hT' : HasFDerivAt (fun z : ℂ => (1 - ‖z‖ ^ 2 / 2 : ℝ)) (- innerSL ℝ d) d := by
    convert hT using 2
    rw [zero_sub, neg_inj, ← Nat.cast_smul_eq_nsmul ℝ 2 (innerSL ℝ d), smul_smul]
    norm_num
  have hsqrt := hT'.sqrt hd
  exact Complex.ofRealCLM.hasFDerivAt.comp d hsqrt

/-- The derivative of the square-root factor `√(1 - ‖z‖²/2)`, evaluated on `b`. -/
lemma fderiv_confProjSF (d : ℂ) (hd : 0 < 1 - ‖d‖ ^ 2 / 2) (b : ℂ) :
    fderiv ℝ confProjSF d b = ((-(inner ℝ d b) / (2 * Real.sqrt (1 - ‖d‖ ^ 2 / 2)) : ℝ) : ℂ) := by
  have h := hasFDerivAt_confProjSF d (ne_of_gt hd)
  rw [h.fderiv]
  simp only [ContinuousLinearMap.comp_apply, smul_apply, neg_apply, innerSL_apply_apply,
    Complex.ofRealCLM_apply]
  rw [smul_eq_mul]
  exact congrArg (fun x : ℝ => (x : ℂ)) (by ring)

/-! ### The first complex coordinate as a continuous linear map -/

/-- The first complex coordinate `c₁` as a continuous linear map `Eucl 3 →L[ℝ] ℂ`. -/
def confProjVecOf_c₁CLM : Eucl 3 →L[ℝ] ℂ :=
  (Complex.equivRealProdCLM : ℂ ≃L[ℝ] ℝ × ℝ).symm.toContinuousLinearMap.comp
    ((PiLp.proj 2 (fun _ : Fin 4 => ℝ) (0 : Fin 4)).prod
      (PiLp.proj 2 (fun _ : Fin 4 => ℝ) (1 : Fin 4)))

@[simp] lemma confProjVecOf_c₁CLM_apply (v : Eucl 3) : confProjVecOf_c₁CLM v = c₁ v := by
  show Complex.equivRealProdCLM.symm (v.ofLp 0, v.ofLp 1) = _
  simp only [c₁, Complex.equivRealProdCLM_symm_apply]

/-! ### Smoothness of `(u, d) ↦ confProjVecOf u d` -/

lemma contDiffAt_star_fst {n : WithTop ℕ∞} (p : ℂ × ℂ) :
    ContDiffAt ℝ n (fun q : ℂ × ℂ => star q.1) p := by
  have h0 := (Complex.conjCLE.contDiff (n := n)).contDiffAt.comp p
    (contDiffAt_fst (n := n) (p := p))
  have h1 : ContDiffAt ℝ n (fun q : ℂ × ℂ => Complex.conjCLE q.1) p := by
    simpa [Function.comp_def] using h0
  simpa only [Complex.star_def, Complex.conjCLE_apply] using h1

lemma contDiffAt_confProjVecOf_prod (u d : ℂ) (hd : 1 - ‖d‖ ^ 2 / 2 ≠ 0) {n : WithTop ℕ∞} :
    ContDiffAt ℝ n (fun p : ℂ × ℂ => confProjVecOf p.1 p.2) (u, d) := by
  have hA : ContDiffAt ℝ n (fun p : ℂ × ℂ => p.1 * confProjSF p.2) (u, d) :=
    contDiffAt_fst.mul ((contDiffAt_confProjSF d hd).comp (u, d) contDiffAt_snd)
  have hB : ContDiffAt ℝ n (fun p : ℂ × ℂ => star p.1 * p.2 / ((Real.sqrt 2 : ℝ) : ℂ))
      (u, d) :=
    (contDiffAt_star_fst (n := n) (u, d)).mul contDiffAt_snd |>.div_const _
  exact confProjVecOf_contDiffAt_ofComplex hA hB

/-! ### The two coordinate differentials -/

lemma fderiv_confProjVecOf_fst (u d a b : ℂ) (hd : 0 < 1 - ‖d‖ ^ 2 / 2) :
    fderiv ℝ (fun p : ℂ × ℂ => p.1 * confProjSF p.2) (u, d) (a, b)
      = u * ((-(inner ℝ d b) / (2 * Real.sqrt (1 - ‖d‖ ^ 2 / 2)) : ℝ) : ℂ)
        + confProjSF d * a := by
  have hsC : HasFDerivAt confProjSF (fderiv ℝ confProjSF d) d :=
    (hasFDerivAt_confProjSF d (ne_of_gt hd)).differentiableAt.hasFDerivAt
  have h2' := hsC.comp (u, d) (hasFDerivAt_snd (𝕜 := ℝ) (p := (u, d)))
  have h2 : HasFDerivAt (fun p : ℂ × ℂ => confProjSF p.2)
      ((fderiv ℝ confProjSF d).comp (ContinuousLinearMap.snd ℝ ℂ ℂ)) (u, d) := by
    simpa [Function.comp_def] using h2'
  have h1 := (hasFDerivAt_fst (𝕜 := ℝ) (p := (u, d))).mul h2
  have h1' : HasFDerivAt (fun p : ℂ × ℂ => p.1 * confProjSF p.2)
      (u • ((fderiv ℝ confProjSF d).comp (ContinuousLinearMap.snd ℝ ℂ ℂ))
        + confProjSF d • (ContinuousLinearMap.fst ℝ ℂ ℂ)) (u, d) := by
    rw [show (Prod.fst * (fun p : ℂ × ℂ => confProjSF p.2))
        = (fun p : ℂ × ℂ => p.1 * confProjSF p.2) from by funext p; rfl] at h1
    exact h1
  rw [h1'.fderiv]
  simp only [smul_apply, add_apply, ContinuousLinearMap.comp_apply]
  have e1 : (ContinuousLinearMap.snd ℝ ℂ ℂ) (a, b) = b := rfl
  have e2 : (ContinuousLinearMap.fst ℝ ℂ ℂ) (a, b) = a := rfl
  rw [e1, e2, fderiv_confProjSF d hd b]
  simp only [smul_eq_mul]

lemma fderiv_confProjVecOf_snd (u d a b : ℂ) :
    fderiv ℝ (fun p : ℂ × ℂ => star p.1 * p.2 / ((Real.sqrt 2 : ℝ) : ℂ)) (u, d) (a, b)
      = (star u * b + d * star a) * (((Real.sqrt 2 : ℝ) : ℂ))⁻¹ := by
  have h1 := (hasFDerivAt_fst (𝕜 := ℝ) (p := (u, d))).star
  have h2 : HasFDerivAt (fun p : ℂ × ℂ => p.2) (ContinuousLinearMap.snd ℝ ℂ ℂ) (u, d) :=
    hasFDerivAt_snd
  have hmul := h1.mul h2
  have h4 : HasFDerivAt (fun p : ℂ × ℂ => star p.1 * p.2 / ((Real.sqrt 2 : ℝ) : ℂ))
      (((Real.sqrt 2 : ℝ) : ℂ)⁻¹ • (star (u, d).1 • ContinuousLinearMap.snd ℝ ℂ ℂ
        + (u, d).2 • ((starL' ℝ : ℂ ≃L[ℝ] ℂ) : ℂ →L[ℝ] ℂ) ∘SL
            ContinuousLinearMap.fst ℝ ℂ ℂ)) (u, d) := by
    have h := hmul.mul_const (((Real.sqrt 2 : ℝ) : ℂ))⁻¹
    simpa [Pi.mul_apply, div_eq_mul_inv] using h
  rw [h4.fderiv]
  have e1 : (ContinuousLinearMap.snd ℝ ℂ ℂ) (a, b) = b := rfl
  have e2 : (ContinuousLinearMap.fst ℝ ℂ ℂ) (a, b) = a := rfl
  have e3 : (((starL' ℝ : ℂ ≃L[ℝ] ℂ) : ℂ →L[ℝ] ℂ)) a = star a := starL'_apply ℝ a
  simp only [smul_apply, add_apply, ContinuousLinearMap.comp_apply]
  rw [e1, e2, e3]
  ring

/-! ### The differential of `(u, d) ↦ confProjVecOf u d` is injective -/

/-- **Injectivity of the differential of the configuration chart.**  For `‖u‖ = 1` and
`‖d‖² < 2`, the differential of `(u, d) ↦ confProjVecOf u d` at `(u, d)` vanishes only on `0`. -/
theorem confProjVecOf_fderiv_pair_eq_zero {u d : ℂ} (hu : ‖u‖ = 1)
    (hd : 0 < 1 - ‖d‖ ^ 2 / 2) {a b : ℂ}
    (h : fderiv ℝ (fun p : ℂ × ℂ => confProjVecOf p.1 p.2) (u, d) (a, b) = 0) :
    a = 0 ∧ b = 0 := by
  have hd' : (1 : ℝ) - ‖d‖ ^ 2 / 2 ≠ 0 := ne_of_gt hd
  have hΨdiff : DifferentiableAt ℝ (fun p : ℂ × ℂ => confProjVecOf p.1 p.2) (u, d) :=
    (contDiffAt_confProjVecOf_prod u d hd' (n := 1)).differentiableAt_one
  have hΨ := hΨdiff.hasFDerivAt
  -- the first coordinate of the differential
  have hAfun : (fun p : ℂ × ℂ => confProjVecOf_c₁CLM (confProjVecOf p.1 p.2))
      = fun p : ℂ × ℂ => p.1 * confProjSF p.2 := by
    funext p
    rw [confProjVecOf_c₁CLM_apply, c₁_confProjVecOf]
  have hA0 : fderiv ℝ (fun p : ℂ × ℂ => p.1 * confProjSF p.2) (u, d) (a, b) = 0 := by
    have hcomp := confProjVecOf_c₁CLM.hasFDerivAt.comp (u, d) hΨ
    have hfun : (confProjVecOf_c₁CLM ∘ fun p : ℂ × ℂ => confProjVecOf p.1 p.2)
        = fun p : ℂ × ℂ => p.1 * confProjSF p.2 := by
      funext p
      exact congrFun hAfun p
    rw [← hfun, hcomp.fderiv, ContinuousLinearMap.comp_apply, h, map_zero]
  -- the second coordinate of the differential
  have hBfun : (fun p : ℂ × ℂ => confProjVecOf_c₂CLM (confProjVecOf p.1 p.2))
      = fun p : ℂ × ℂ => star p.1 * p.2 / ((Real.sqrt 2 : ℝ) : ℂ) := by
    funext p
    rw [confProjVecOf_c₂CLM_apply, c₂_confProjVecOf]
  have hB0 : fderiv ℝ (fun p : ℂ × ℂ => star p.1 * p.2 / ((Real.sqrt 2 : ℝ) : ℂ))
      (u, d) (a, b) = 0 := by
    have hcomp := confProjVecOf_c₂CLM.hasFDerivAt.comp (u, d) hΨ
    have hfun : (confProjVecOf_c₂CLM ∘ fun p : ℂ × ℂ => confProjVecOf p.1 p.2)
        = fun p : ℂ × ℂ => star p.1 * p.2 / ((Real.sqrt 2 : ℝ) : ℂ) := by
      funext p
      exact congrFun hBfun p
    rw [← hfun, hcomp.fderiv, ContinuousLinearMap.comp_apply, h, map_zero]
  have hAv := fderiv_confProjVecOf_fst u d a b hd
  have hBv := fderiv_confProjVecOf_snd u d a b
  have heqA : u * ((-(inner ℝ d b) / (2 * Real.sqrt (1 - ‖d‖ ^ 2 / 2)) : ℝ) : ℂ)
      + ((Real.sqrt (1 - ‖d‖ ^ 2 / 2) : ℝ) : ℂ) * a = 0 := by
    rw [← hAv]; exact hA0
  have heqB : (star u * b + d * star a) * (((Real.sqrt 2 : ℝ) : ℂ))⁻¹ = 0 := by
    rw [← hBv]; exact hB0
  -- abbreviations
  set s : ℝ := Real.sqrt (1 - ‖d‖ ^ 2 / 2) with hs
  set r : ℝ := inner ℝ d b with hr
  have hs0 : s ≠ 0 := by rw [hs]; exact ne_of_gt (Real.sqrt_pos.mpr hd)
  have hs2 : s ^ 2 = 1 - ‖d‖ ^ 2 / 2 := by rw [hs]; exact Real.sq_sqrt (le_of_lt hd)
  have hu2 : u * star u = 1 := by
    rw [Complex.star_def, Complex.mul_conj, Complex.normSq_eq_norm_sq, hu]
    norm_num
  -- (B) gives `b = -(u * star a * d)`
  have hs2c : (((Real.sqrt 2 : ℝ) : ℂ))⁻¹ ≠ 0 := by
    apply inv_ne_zero
    exact Complex.ofReal_ne_zero.mpr (ne_of_gt (Real.sqrt_pos.mpr (by norm_num : (0 : ℝ) < 2)))
  have hb0 : star u * b + d * star a = 0 := (mul_eq_zero.mp heqB).resolve_right hs2c
  have hb : b = -(u * star a * d) := by
    have h1 : u * (star u * b) + u * (d * star a) = 0 := by
      have h3 : u * (star u * b + d * star a) = 0 := by rw [hb0, mul_zero]
      rwa [mul_add] at h3
    rw [← mul_assoc, hu2, one_mul] at h1
    have h2 : b = -(u * (d * star a)) := eq_neg_of_add_eq_zero_left h1
    rw [h2]; ring
  -- (A) gives `s * a = u * (r / (2s))`
  have ha1 : (s : ℂ) * a = u * ((r / (2 * s) : ℝ) : ℂ) := by
    have h : u * ((-r / (2 * s) : ℝ) : ℂ) + (s : ℂ) * a = 0 := heqA
    have hneg : ((-r / (2 * s) : ℝ) : ℂ) = -(((r / (2 * s) : ℝ) : ℂ)) := by
      rw [show (-r / (2 * s) : ℝ) = -(r / (2 * s)) by ring, Complex.ofReal_neg]
    rw [hneg, mul_neg] at h
    have h3 := eq_neg_of_add_eq_zero_left h
    rw [neg_inj] at h3
    exact h3.symm
  have ha1s : star a * (s : ℂ) = star u * ((r / (2 * s) : ℝ) : ℂ) := by
    have h := congrArg star ha1
    simpa [star_mul, mul_comm] using h
  have hkey : u * star a * (s : ℂ) = ((r / (2 * s) : ℝ) : ℂ) := by
    have h' : (u * star u) * ((r / (2 * s) : ℝ) : ℂ) = ((r / (2 * s) : ℝ) : ℂ) := by
      rw [hu2, one_mul]
    calc u * star a * (s : ℂ) = u * (star a * (s : ℂ)) := by ring
      _ = u * (star u * ((r / (2 * s) : ℝ) : ℂ)) := by rw [ha1s]
      _ = (u * star u) * ((r / (2 * s) : ℝ) : ℂ) := by rw [mul_assoc]
      _ = ((r / (2 * s) : ℝ) : ℂ) := h'
  have hbs : (s : ℂ) * b = -(((r / (2 * s) : ℝ) : ℂ) * d) := by
    rw [hb, mul_neg]
    congr 1
    rw [show (s : ℂ) * (u * star a * d) = (u * star a * (s : ℂ)) * d by ring]
    rw [hkey]
  -- the inner-product consequence
  have hinner : s * r = -((r / (2 * s)) * ‖d‖ ^ 2) := by
    have h1 : inner ℝ d ((s : ℂ) * b) = inner ℝ d (-(((r / (2 * s) : ℝ) : ℂ) * d)) := by
      rw [hbs]
    rw [← Complex.real_smul, ← Complex.real_smul, ← neg_smul] at h1
    rw [real_inner_smul_right, real_inner_smul_right, real_inner_self_eq_norm_sq, ← hr] at h1
    simpa using h1
  have hr0 : r = 0 := by
    have h2 : 2 * s ^ 2 * r = -(r * ‖d‖ ^ 2) := by
      have h := congrArg (fun x : ℝ => x * (2 * s)) hinner
      have hL : (s * r) * (2 * s) = 2 * s ^ 2 * r := by ring
      have hR : (-((r / (2 * s)) * ‖d‖ ^ 2)) * (2 * s) = -(r * ‖d‖ ^ 2) := by
        field_simp
      rw [hL, hR] at h
      exact h
    have h3 : s ^ 2 * r = r - r * ‖d‖ ^ 2 / 2 := by rw [hs2]; ring
    nlinarith [h2, h3]
  have ha0 : a = 0 := by
    have hzero : (s : ℂ) * a = 0 := by
      have h := ha1
      rw [hr0] at h
      simpa using h
    exact (mul_eq_zero.mp hzero).resolve_left (Complex.ofReal_ne_zero.mpr hs0)
  refine ⟨ha0, ?_⟩
  rw [hb, ha0]
  simp

/-! ### The composite `y ↦ confProjVecOf (U y) (D y)` is an immersion -/

theorem confProjVecOf_data_span {U D : EuclideanSpace ℝ (Fin 2) → ℂ}
    (hU : ∀ x, ‖U x‖ = 1) (hD : ∀ x, 0 < 1 - ‖D x‖ ^ 2 / 2)
    (hUd : ContDiff ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) U)
    (hDd : ContDiff ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) D)
    (hι : ∀ x w, (∃ l : ℝ, fderiv ℝ U x w = l • U x) → fderiv ℝ D x w = 0 → w = 0)
    (x : EuclideanSpace ℝ (Fin 2)) {w : EuclideanSpace ℝ (Fin 2)}
    (hw : fderiv ℝ (fun y => Work.Drive.confProjVecOf (U y) (D y)) x w
      ∈ Submodule.span ℝ ({Work.Drive.confProjVecOf (U x) (D x)} : Set (Work.Drive.Eucl 3))) :
    w = 0 := by
  have hdx : 0 < 1 - ‖D x‖ ^ 2 / 2 := hD x
  have hdx' : (1 : ℝ) - ‖D x‖ ^ 2 / 2 ≠ 0 := ne_of_gt hdx
  have hUd' : DifferentiableAt ℝ U x := (hUd.contDiffAt).differentiableAt (by simp)
  have hDd' : DifferentiableAt ℝ D x := (hDd.contDiffAt).differentiableAt (by simp)
  have hΨ : HasFDerivAt (fun p : ℂ × ℂ => confProjVecOf p.1 p.2)
      (fderiv ℝ (fun p : ℂ × ℂ => confProjVecOf p.1 p.2) (U x, D x)) (U x, D x) :=
    ((contDiffAt_confProjVecOf_prod (U x) (D x) hdx' (n := 1)).differentiableAt_one).hasFDerivAt
  have hA : HasFDerivAt (fun y : EuclideanSpace ℝ (Fin 2) => (U y, D y))
      ((fderiv ℝ U x).prod (fderiv ℝ D x)) x :=
    hUd'.hasFDerivAt.prodMk hDd'.hasFDerivAt
  have hchain : HasFDerivAt (fun y => confProjVecOf (U y) (D y))
      ((fderiv ℝ (fun p : ℂ × ℂ => confProjVecOf p.1 p.2) (U x, D x)).comp
        ((fderiv ℝ U x).prod (fderiv ℝ D x))) x := by
    have h := hΨ.comp x hA
    simpa only [Function.comp_def] using h
  have hDnhds : ∀ᶠ y in 𝓝 x, 0 < 1 - ‖D y‖ ^ 2 / 2 := by
    have hopen : IsOpen {z : ℂ | 0 < 1 - ‖z‖ ^ 2 / 2} :=
      isOpen_lt continuous_const (continuous_const.sub ((continuous_norm.pow 2).div_const 2))
    exact hDd.continuous.continuousAt.preimage_mem_nhds (hopen.mem_nhds hdx)
  have hnorm1 : (fun y : EuclideanSpace ℝ (Fin 2) => ‖confProjVecOf (U y) (D y)‖ ^ 2)
      =ᶠ[𝓝 x] (fun _ => (1 : ℝ)) := by
    filter_upwards [hDnhds] with y hy
    exact norm_sq_confProjVecOf_of_nonneg (hU y) (le_of_lt hy)
  have hP0 : fderiv ℝ (fun y => ‖confProjVecOf (U y) (D y)‖ ^ 2) x = 0 := by
    rw [hnorm1.fderiv_eq]; simp
  have hperp : ∀ y, inner ℝ (confProjVecOf (U x) (D x))
      (((fderiv ℝ (fun p : ℂ × ℂ => confProjVecOf p.1 p.2) (U x, D x)).comp
        ((fderiv ℝ U x).prod (fderiv ℝ D x))) y) = 0 := by
    intro y
    have hdercomp : fderiv ℝ (fun y => ‖confProjVecOf (U y) (D y)‖ ^ 2) x
        = ((2 : ℕ) • innerSL ℝ (confProjVecOf (U x) (D x))) ∘SL
          ((fderiv ℝ (fun p : ℂ × ℂ => confProjVecOf p.1 p.2) (U x, D x)).comp
            ((fderiv ℝ U x).prod (fderiv ℝ D x))) :=
      hchain.norm_sq.fderiv
    have h : (((2 : ℕ) • innerSL ℝ (confProjVecOf (U x) (D x))) ∘SL
          ((fderiv ℝ (fun p : ℂ × ℂ => confProjVecOf p.1 p.2) (U x, D x)).comp
            ((fderiv ℝ U x).prod (fderiv ℝ D x)))) y = 0 := by
      rw [← hdercomp, hP0]; simp
    simp only [ContinuousLinearMap.comp_apply, smul_apply] at h ⊢
    rw [innerSL_apply_apply, two_nsmul] at h
    linarith
  rcases Submodule.mem_span_singleton.mp hw with ⟨lam, hlam⟩
  have hlam0 : lam = 0 := by
    have h1 := hperp w
    rw [← hchain.fderiv] at h1
    rw [← hlam] at h1
    rw [real_inner_smul_right, real_inner_self_eq_norm_sq, hnorm1.eq_of_nhds, mul_one] at h1
    exact h1
  have hFzero : fderiv ℝ (fun y => confProjVecOf (U y) (D y)) x w = 0 := by
    rw [← hlam, hlam0]; simp
  have hcomp : (fderiv ℝ (fun p : ℂ × ℂ => confProjVecOf p.1 p.2) (U x, D x))
      ((fderiv ℝ U x w, fderiv ℝ D x w)) = 0 := by
    have h1 : ((fderiv ℝ (fun p : ℂ × ℂ => confProjVecOf p.1 p.2) (U x, D x)).comp
        ((fderiv ℝ U x).prod (fderiv ℝ D x))) w = 0 := by
      rw [← hchain.fderiv]; exact hFzero
    simpa only [ContinuousLinearMap.comp_apply, ContinuousLinearMap.prod_apply] using h1
  have hpair := confProjVecOf_fderiv_pair_eq_zero (hU x) hdx hcomp
  exact hι x w ⟨0, by rw [hpair.1]; simp⟩ hpair.2

end

end Work.Drive
