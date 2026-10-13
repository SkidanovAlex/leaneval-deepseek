import Mathlib.Algebra.Order.Star.Real
import Mathlib.Analysis.LocallyConvex.AbsConvexOpen
import Mathlib.Analysis.Normed.Lp.MeasurableSpace
import Mathlib.Analysis.SpecialFunctions.Trigonometric.Arctan
import Mathlib.MeasureTheory.Integral.CurveIntegral.Poincare
import Mathlib.RingTheory.Etale.Weakly
import Mathlib.RingTheory.Flat.TorsionFree
import Mathlib.RingTheory.TotallySplit
import Submission.Work.Cyl
import Submission.Work.Cyl.Elliptic
import Submission.Work.Cyl.Coords
import Submission.Work.LWP.Inputs
import Submission.Work.LWP.Main
import Submission.Work.LWP.BiotSavart.biotSavart_reflZ
import Submission.Work.ConstructionInstance.isAxiNoSwirl_biotSavart
import Submission.Work.ConstructionInstance.profiles_of_axiNoSwirl_div
import Submission.Work.ConstructionInstance.psiField_of_potential

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

set_option autoImplicit false
set_option linter.unusedVariables false

namespace Work.ConstructionInstance

open FiniteTimeSingularity MeasureTheory Filter
open scoped Topology

/-! ## The right half plane in `ℝ² = ℝ × ℝ` -/

/-- The open right half plane `{p : ℝ × ℝ | 0 < p.1}`, the domain of the meridian coordinates
`(r, x₃)` on which the stream function is constructed. -/
def halfPlane : Set (ℝ × ℝ) := {p | 0 < p.1}

lemma convex_halfPlane : Convex ℝ halfPlane := by
  have hf : IsLinearMap ℝ (fun p : ℝ × ℝ => p.1) :=
    ⟨fun x y => by simp, fun c x => by simp⟩
  simpa [halfPlane] using convex_halfSpace_gt hf 0

lemma isOpen_halfPlane : IsOpen halfPlane := by
  simpa [halfPlane] using isOpen_lt continuous_const continuous_fst

/-! ## Derivatives of curried functions along the coordinate directions -/

/-- The `r`-derivative of a curried function, as the Fréchet derivative in the first coordinate. -/
lemma fderiv_curry_e0 (f : ℝ → ℝ → ℝ) (a : ℝ × ℝ)
    (hf : DifferentiableAt ℝ (fun p : ℝ × ℝ => f p.1 p.2) a) :
    fderiv ℝ (fun p : ℝ × ℝ => f p.1 p.2) a (⟨(1:ℝ),0⟩ : ℝ × ℝ) = Work.Cyl.pdR f a.1 a.2 := by
  rw [Work.Cyl.fderiv_apply_eq_deriv_line _ _ _ hf]
  rw [show (fun t : ℝ => (fun p : ℝ × ℝ => f p.1 p.2) (a + t • (⟨(1:ℝ),0⟩ : ℝ × ℝ)))
      = (fun t => f (a.1 + t) a.2) by funext t; simp]
  rw [Work.Cyl.pdR]
  simpa using deriv_comp_const_add (fun r => f r a.2) a.1 0

/-- The `x₃`-derivative of a curried function, as the Fréchet derivative in the second coordinate. -/
lemma fderiv_curry_e1 (f : ℝ → ℝ → ℝ) (a : ℝ × ℝ)
    (hf : DifferentiableAt ℝ (fun p : ℝ × ℝ => f p.1 p.2) a) :
    fderiv ℝ (fun p : ℝ × ℝ => f p.1 p.2) a (⟨(0:ℝ),1⟩ : ℝ × ℝ) = Work.Cyl.pdZ f a.1 a.2 := by
  rw [Work.Cyl.fderiv_apply_eq_deriv_line _ _ _ hf]
  rw [show (fun t : ℝ => (fun p : ℝ × ℝ => f p.1 p.2) (a + t • (⟨(0:ℝ),1⟩ : ℝ × ℝ)))
      = (fun t => f a.1 (a.2 + t)) by funext t; simp]
  rw [Work.Cyl.pdZ]
  simpa using deriv_comp_const_add (fun z => f a.1 z) a.2 0

/-! ## Derivatives of `p ↦ p.1 * f p.1 p.2` -/

lemma fderiv_fst_mul_e0 (f : ℝ → ℝ → ℝ) (a : ℝ × ℝ)
    (hf : DifferentiableAt ℝ (fun p : ℝ × ℝ => f p.1 p.2) a) :
    fderiv ℝ (fun p : ℝ × ℝ => p.1 * f p.1 p.2) a (⟨(1:ℝ),0⟩ : ℝ × ℝ)
      = f a.1 a.2 + a.1 * Work.Cyl.pdR f a.1 a.2 := by
  have hmain : HasFDerivAt (fun p : ℝ × ℝ => p.1 * f p.1 p.2)
      (a.1 • fderiv ℝ (fun p : ℝ × ℝ => f p.1 p.2) a
        + (f a.1 a.2) • (ContinuousLinearMap.fst ℝ ℝ ℝ)) a :=
    hasFDerivAt_fst.mul hf.hasFDerivAt
  rw [hmain.fderiv]
  simp only [add_apply, smul_apply]
  rw [fderiv_curry_e0 f a hf]
  simp only [smul_eq_mul]
  rw [show (ContinuousLinearMap.fst ℝ ℝ ℝ) (⟨(1:ℝ),0⟩ : ℝ × ℝ) = 1 from rfl, mul_one]
  ring

lemma fderiv_fst_mul_e1 (f : ℝ → ℝ → ℝ) (a : ℝ × ℝ)
    (hf : DifferentiableAt ℝ (fun p : ℝ × ℝ => f p.1 p.2) a) :
    fderiv ℝ (fun p : ℝ × ℝ => p.1 * f p.1 p.2) a (⟨(0:ℝ),1⟩ : ℝ × ℝ)
      = a.1 * Work.Cyl.pdZ f a.1 a.2 := by
  have hmain : HasFDerivAt (fun p : ℝ × ℝ => p.1 * f p.1 p.2)
      (a.1 • fderiv ℝ (fun p : ℝ × ℝ => f p.1 p.2) a
        + (f a.1 a.2) • (ContinuousLinearMap.fst ℝ ℝ ℝ)) a :=
    hasFDerivAt_fst.mul hf.hasFDerivAt
  rw [hmain.fderiv]
  simp only [add_apply, smul_apply]
  rw [fderiv_curry_e1 f a hf]
  simp

/-! ## The scalar multiplication form of `fderiv` -/

lemma fderiv_smul_const_apply (c : ℝ × ℝ → ℝ) (f : (ℝ × ℝ) →L[ℝ] ℝ) (a x y : ℝ × ℝ)
    (hc : DifferentiableAt ℝ c a) :
    fderiv ℝ (fun p : ℝ × ℝ => c p • f) a x y = fderiv ℝ c a x * f y := by
  rw [fderiv_smul_const hc f]
  simp [ContinuousLinearMap.smulRight_apply]

/-! ## Symmetry of a bilinear form on `ℝ × ℝ` from its `(e₀,e₁)`-entry -/

lemma pair_symm (L : (ℝ × ℝ) →L[ℝ] ((ℝ × ℝ) →L[ℝ] ℝ))
    (h : L (⟨(1:ℝ),0⟩ : ℝ × ℝ) (⟨(0:ℝ),1⟩ : ℝ × ℝ)
        = L (⟨(0:ℝ),1⟩ : ℝ × ℝ) (⟨(1:ℝ),0⟩ : ℝ × ℝ)) :
    ∀ x y : ℝ × ℝ, L x y = L y x := by
  intro x y
  have hx : x = x.1 • (⟨(1:ℝ),0⟩ : ℝ × ℝ) + x.2 • (⟨(0:ℝ),1⟩ : ℝ × ℝ) := by ext <;> simp
  have hy : y = y.1 • (⟨(1:ℝ),0⟩ : ℝ × ℝ) + y.2 • (⟨(0:ℝ),1⟩ : ℝ × ℝ) := by ext <;> simp
  conv_lhs => rw [hx, hy]
  conv_rhs => rw [hy, hx]
  simp only [map_add, map_smul, add_apply, smul_apply]
  rw [h]
  ring

/-! ## The Poincaré step: a primitive for the meridian 1-form -/

/-- If the meridian profiles `ur, uz` are `C¹` on the right half plane and satisfy the
divergence-free identity `∂_r u_r + u_r/r + ∂_z u_z = 0` there, then the `1`-form
`(-(r u_z)) dr + (r u_r) dz` is closed and hence exact: it has a primitive `φ` with
`∂_r φ = -r u_z`, `∂_z φ = r u_r` on the half plane. -/
theorem exists_potential_of_profiles (ur uz : ℝ → ℝ → ℝ)
    (hUr : DifferentiableOn ℝ (fun p : ℝ × ℝ => ur p.1 p.2) halfPlane)
    (hUz : DifferentiableOn ℝ (fun p : ℝ × ℝ => uz p.1 p.2) halfPlane)
    (hdiv : ∀ p ∈ halfPlane,
      Work.Cyl.pdR ur p.1 p.2 + ur p.1 p.2 / p.1 + Work.Cyl.pdZ uz p.1 p.2 = 0) :
    ∃ φ : ℝ × ℝ → ℝ, ∀ p ∈ halfPlane,
      HasFDerivAt φ ((-(p.1 * uz p.1 p.2)) • (ContinuousLinearMap.fst ℝ ℝ ℝ)
        + (p.1 * ur p.1 p.2) • (ContinuousLinearMap.snd ℝ ℝ ℝ)) p := by
  let F : (ℝ × ℝ) →L[ℝ] ℝ := ContinuousLinearMap.fst ℝ ℝ ℝ
  let G : (ℝ × ℝ) →L[ℝ] ℝ := ContinuousLinearMap.snd ℝ ℝ ℝ
  let c1 : ℝ × ℝ → ℝ := fun p => -(p.1 * uz p.1 p.2)
  let c2 : ℝ × ℝ → ℝ := fun p => p.1 * ur p.1 p.2
  let Om : (ℝ × ℝ) → (ℝ × ℝ) →L[ℝ] ℝ := fun p => c1 p • F + c2 p • G
  have hfst : DifferentiableOn ℝ (fun p : ℝ × ℝ => p.1) halfPlane :=
    ((ContinuousLinearMap.fst ℝ ℝ ℝ).differentiable).differentiableOn
  have hc1 : DifferentiableOn ℝ c1 halfPlane := (hfst.mul hUz).neg
  have hc2 : DifferentiableOn ℝ c2 halfPlane := hfst.mul hUr
  have hOm_diff : DifferentiableOn ℝ Om halfPlane := by
    have h := (hc1.smul_const F).add (hc2.smul_const G)
    convert h using 1
  have hOm_symm : ∀ a ∈ halfPlane, ∀ x y : ℝ × ℝ, fderiv ℝ Om a x y = fderiv ℝ Om a y x := by
    intro a ha
    have hna : halfPlane ∈ 𝓝 a := isOpen_halfPlane.mem_nhds ha
    have hUz_at : DifferentiableAt ℝ (fun p : ℝ × ℝ => uz p.1 p.2) a := hUz.differentiableAt hna
    have hUr_at : DifferentiableAt ℝ (fun p : ℝ × ℝ => ur p.1 p.2) a := hUr.differentiableAt hna
    have hc1_at : DifferentiableAt ℝ c1 a := hc1.differentiableAt hna
    have hc2_at : DifferentiableAt ℝ c2 a := hc2.differentiableAt hna
    have hval : ∀ x y : ℝ × ℝ,
        fderiv ℝ Om a x y = (fderiv ℝ c1 a x) * y.1 + (fderiv ℝ c2 a x) * y.2 := by
      intro x y
      rw [show Om = (fun p : ℝ × ℝ => c1 p • F) + (fun p : ℝ × ℝ => c2 p • G) from rfl,
        fderiv_add (hc1_at.smul_const F) (hc2_at.smul_const G)]
      simp only [add_apply]
      rw [fderiv_smul_const_apply c1 F a x y hc1_at, fderiv_smul_const_apply c2 G a x y hc2_at]
      simp [F, G]
    have hc2e0 : fderiv ℝ c2 a (⟨(1:ℝ),0⟩ : ℝ × ℝ)
        = ur a.1 a.2 + a.1 * Work.Cyl.pdR ur a.1 a.2 := by
      rw [show c2 = (fun p : ℝ × ℝ => p.1 * ur p.1 p.2) from rfl]
      exact fderiv_fst_mul_e0 ur a hUr_at
    have hc1e1 : fderiv ℝ c1 a (⟨(0:ℝ),1⟩ : ℝ × ℝ)
        = -(a.1 * Work.Cyl.pdZ uz a.1 a.2) := by
      rw [show c1 = -(fun p : ℝ × ℝ => p.1 * uz p.1 p.2) from rfl, fderiv_neg]
      simp only [neg_apply]
      rw [fderiv_fst_mul_e1 uz a hUz_at]
    have hkey : fderiv ℝ Om a (⟨(1:ℝ),0⟩ : ℝ × ℝ) (⟨(0:ℝ),1⟩ : ℝ × ℝ)
              = fderiv ℝ Om a (⟨(0:ℝ),1⟩ : ℝ × ℝ) (⟨(1:ℝ),0⟩ : ℝ × ℝ) := by
      rw [hval (⟨(1:ℝ),0⟩ : ℝ × ℝ) (⟨(0:ℝ),1⟩ : ℝ × ℝ),
          hval (⟨(0:ℝ),1⟩ : ℝ × ℝ) (⟨(1:ℝ),0⟩ : ℝ × ℝ)]
      simp only [mul_zero, mul_one, add_zero, zero_add]
      rw [hc2e0, hc1e1]
      have h5 : a.1 * Work.Cyl.pdR ur a.1 a.2 + a.1 * Work.Cyl.pdZ uz a.1 a.2 = - ur a.1 a.2 := by
        have ha1 : a.1 ≠ 0 := ne_of_gt ha
        have h4 : Work.Cyl.pdR ur a.1 a.2 + ur a.1 a.2 / a.1 + Work.Cyl.pdZ uz a.1 a.2 = 0 :=
          hdiv a ha
        field_simp [ha1] at h4
        linarith
      linarith
    intro x y
    exact pair_symm (fderiv ℝ Om a) hkey x y
  exact Convex.exists_forall_hasFDerivAt_of_fderiv_symmetric convex_halfPlane isOpen_halfPlane
    hOm_diff hOm_symm

theorem exists_psiField_eq_biotSavart {α : NNReal} {W : ℝ → ℝ → ℝ}
    {ω : Work.ConstructionInstance.R3 → Work.ConstructionInstance.R3}
    (hshape : ∀ x : Work.ConstructionInstance.R3,
      ω x = W (Work.Cyl.rho x) (Work.Cyl.theta x) • Work.Cyl.eTheta x)
    (hodd : Work.LWP.IsOddVorticity ω) (hlaw : Work.LWP.BiotSavartLaw)
    (hsch : Work.LWP.BiotSavartSchauder α) (hlder : Holder α ω)
    (hint : MeasureTheory.Integrable ω) (hbdd : IsBoundedFun ω)
    (hdiv : ∀ x : Work.ConstructionInstance.R3, FiniteTimeSingularity.div ω x = 0) :
    ∃ ψ : ℝ → ℝ → ℝ, ∀ x : Work.ConstructionInstance.R3, 0 < Work.Cyl.radial x →
      Work.LWP.biotSavart ω x = Work.Cyl.psiField ψ x := by
  -- rewrite the meridian profile as a function of `(radial, axial)`
  have hshape' : ∀ x : Work.ConstructionInstance.R3,
      ω x = (fun r z => W (Real.sqrt (r^2 + z^2)) (Real.arctan (z/r)))
              (Work.Cyl.radial x) (Work.Cyl.axial x) • Work.Cyl.eTheta x := by
    intro x
    rw [hshape x]
    show W (Work.Cyl.rho x) (Work.Cyl.theta x) • Work.Cyl.eTheta x
        = W (Real.sqrt (Work.Cyl.radial x ^ 2 + Work.Cyl.axial x ^ 2))
            (Real.arctan (Work.Cyl.axial x / Work.Cyl.radial x)) • Work.Cyl.eTheta x
    rw [Work.Cyl.rho, Work.Cyl.radial_sq, Work.Cyl.theta]
  -- `u = biotSavart ω` is a `C¹`, divergence-free, axisymmetric no-swirl field
  have haxi : Work.Cyl.IsAxiNoSwirl (Work.LWP.biotSavart ω) := isAxiNoSwirl_biotSavart (f := fun r z => W (Real.sqrt (r^2 + z^2)) (Real.arctan (z/r))) hshape'
  have hcont : ContDiff ℝ 1 (Work.LWP.biotSavart ω) := (hsch ω hint hbdd hlder hdiv).1
  have hdivu : ∀ x, FiniteTimeSingularity.div (Work.LWP.biotSavart ω) x = 0 :=
    (hlaw ω hint hbdd hdiv).2
  -- extract the meridian profiles
  obtain ⟨ur, uz, hcyl, hUr, hUz, hdivp⟩ :=
    profiles_of_axiNoSwirl_div (Work.LWP.biotSavart ω) hcont haxi hdivu
  -- the closed meridian 1-form has a primitive
  obtain ⟨φ, hφ⟩ := exists_potential_of_profiles ur uz hUr hUz (fun p hp => hdivp p hp)
  -- a primitive of `(-(r u_z)) dr + (r u_r) dz` is a stream function
  obtain ⟨ψ, hψ⟩ := psiField_of_potential ur uz φ (fun p hp => hφ p hp)
  exact ⟨ψ, fun x hx => by rw [hcyl x hx]; exact hψ x hx⟩

end Work.ConstructionInstance
