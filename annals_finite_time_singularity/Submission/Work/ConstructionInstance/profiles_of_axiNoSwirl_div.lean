import Mathlib.Analysis.Calculus.ContDiff.WithLp
import Mathlib.Analysis.Calculus.FDeriv.Mul
import Mathlib.Analysis.InnerProductSpace.PiL2
import Mathlib.LinearAlgebra.Trace
import Submission.Work.Cyl.Coords
import Submission.Work.Cyl.Basic
import Submission.Work.Cyl.FieldDeriv

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

/-!
# Profiles of an axisymmetric no-swirl divergence-free field

Given a `C¹` axisymmetric no-swirl field `u : ℝ³ → ℝ³` which is divergence free, we extract its
radial and axial profiles `u_r, u_z : ℝ → ℝ → ℝ` (functions of the coordinates `(r, x₃)` of the
meridian half plane).  Off the symmetry axis `u = u_r e_r + u_z e₃`, the profiles are differentiable
on `r > 0`, and the divergence-free condition becomes the cylindrical divergence identity

  `∂_r u_r + u_r / r + ∂_z u_z = 0`.

The profiles are read off on the meridian `θ = 0`, where `u_r` and `u_z` are exactly the first and
third coordinates of `u` (the reflection symmetry of a no-swirl field kills the angular component
there), so no quotient by `r` is needed in their definition.
-/

set_option autoImplicit false

open Work.Cyl
open Filter
open scoped Topology

namespace Work.ConstructionInstance

/-- The point of the meridian `θ = 0` with radial coordinate `r` and axial coordinate `z`. -/
def mer (r z : ℝ) : R3 := !₂[r, 0, z]

@[simp] lemma mer_apply_zero (r z : ℝ) : (mer r z) 0 = r := by simp [mer]
@[simp] lemma mer_apply_one (r z : ℝ) : (mer r z) 1 = 0 := by simp [mer]
@[simp] lemma mer_apply_two (r z : ℝ) : (mer r z) 2 = z := by simp [mer]

lemma radial_mer (r z : ℝ) : radial (mer r z) = |r| := by
  rw [radial, show radSq (mer r z) = r ^ 2 by simp [radSq, mer]]
  exact Real.sqrt_sq_eq_abs r

lemma axial_mer (r z : ℝ) : axial (mer r z) = z := by simp [axial, mer]

lemma mer_eq (r z : ℝ) : mer r z = r • e0 + z • eZ := by
  ext i; fin_cases i <;> simp [mer, e0, eZ, FiniteTimeSingularity.e]

lemma differentiable_mer : Differentiable ℝ (fun p : ℝ × ℝ => mer p.1 p.2) := by
  have h : (fun p : ℝ × ℝ => mer p.1 p.2) = fun p => p.1 • e0 + p.2 • eZ := by
    funext p; exact mer_eq p.1 p.2
  rw [h]
  fun_prop

/-- The radial profile of a no-swirl field, read off on the meridian `θ = 0`. -/
def profR (u : R3 → R3) : ℝ → ℝ → ℝ := fun r z => (u (mer r z)) 0

/-- The axial profile of a no-swirl field, read off on the meridian `θ = 0`. -/
def profZ (u : R3 → R3) : ℝ → ℝ → ℝ := fun r z => (u (mer r z)) 2

/-- The radial profile of `u = cylField ur uz` agrees with `ur` on `r > 0`. -/
lemma profR_eq_of_pos {u : R3 → R3} {ur uz : ℝ → ℝ → ℝ} (hu_eq : u = cylField ur uz)
    {r : ℝ} (hr : 0 < r) (z : ℝ) : profR u r z = ur r z := by
  show (u (mer r z)) 0 = ur r z
  rw [hu_eq, cylField_zero, radial_mer, axial_mer, mer_apply_zero, abs_of_pos hr]
  exact mul_div_cancel_right₀ _ (ne_of_gt hr)

/-- The axial profile of `u = cylField ur uz` agrees with `uz` on `r > 0`. -/
lemma profZ_eq_of_pos {u : R3 → R3} {ur uz : ℝ → ℝ → ℝ} (hu_eq : u = cylField ur uz)
    {r : ℝ} (hr : 0 < r) (z : ℝ) : profZ u r z = uz r z := by
  show (u (mer r z)) 2 = uz r z
  rw [hu_eq, cylField_two, radial_mer, axial_mer, abs_of_pos hr]

/-- Off the axis, `u = cylField ur uz` is recovered from the meridian profiles. -/
lemma eq_cylField_of_pos {u : R3 → R3} {ur uz : ℝ → ℝ → ℝ} (hu_eq : u = cylField ur uz)
    {x : R3} (hrx : 0 < radial x) : u x = cylField (profR u) (profZ u) x := by
  rw [congrFun hu_eq x]
  simp only [cylField]
  rw [profR_eq_of_pos hu_eq hrx (axial x), profZ_eq_of_pos hu_eq hrx (axial x)]

/-- The (uncurried) radial profile is differentiable everywhere. -/
lemma differentiable_profR (u : R3 → R3) (hu : ContDiff ℝ 1 u) :
    Differentiable ℝ (fun p : ℝ × ℝ => profR u p.1 p.2) := by
  have hud : Differentiable ℝ u := hu.differentiable (by norm_num)
  have hcomp : Differentiable ℝ (fun p : ℝ × ℝ => u (mer p.1 p.2)) := hud.comp differentiable_mer
  have hproj : Differentiable ℝ (fun (y : R3) => y 0) := by fun_prop
  exact hproj.comp hcomp

/-- The (uncurried) axial profile is differentiable everywhere. -/
lemma differentiable_profZ (u : R3 → R3) (hu : ContDiff ℝ 1 u) :
    Differentiable ℝ (fun p : ℝ × ℝ => profZ u p.1 p.2) := by
  have hud : Differentiable ℝ u := hu.differentiable (by norm_num)
  have hcomp : Differentiable ℝ (fun p : ℝ × ℝ => u (mer p.1 p.2)) := hud.comp differentiable_mer
  have hproj : Differentiable ℝ (fun (y : R3) => y 2) := by fun_prop
  exact hproj.comp hcomp

/-- The radial coordinate is continuous. -/
lemma continuous_radial_prof : Continuous (radial : R3 → ℝ) := by
  rw [show (radial : R3 → ℝ) = fun x => Real.sqrt (x 0 ^ 2 + x 1 ^ 2) by
    funext x; rw [radial, radSq]]
  fun_prop

/-- The divergence-free condition in cylindrical coordinates. -/
lemma div_identity (u : R3 → R3) (hu : ContDiff ℝ 1 u) {ur uz : ℝ → ℝ → ℝ}
    (hu_eq : u = cylField ur uz) (hdiv : ∀ x, FiniteTimeSingularity.div u x = 0) :
    ∀ p : ℝ × ℝ, 0 < p.1 →
      pdR (profR u) p.1 p.2 + profR u p.1 p.2 / p.1 + pdZ (profZ u) p.1 p.2 = 0 := by
  intro p hp
  obtain ⟨r, z⟩ := p
  have hrx : 0 < radial (mer r z) := by rw [radial_mer, abs_of_pos hp]; exact hp
  have hdR : DiffAt2 (profR u) (radial (mer r z)) (axial (mer r z)) :=
    (differentiable_profR u hu).differentiableAt
  have hdZ : DiffAt2 (profZ u) (radial (mer r z)) (axial (mer r z)) :=
    (differentiable_profZ u hu).differentiableAt
  have hcyl := div_cylField (profR u) (profZ u) (mer r z) hdR hdZ hrx
  have hmem : {y : R3 | 0 < radial y} ∈ 𝓝 (mer r z) :=
    (isOpen_lt continuous_const continuous_radial_prof).mem_nhds hrx
  have hEv : (cylField (profR u) (profZ u)) =ᶠ[𝓝 (mer r z)] u :=
    Filter.mem_of_superset hmem (fun y hy => (eq_cylField_of_pos hu_eq hy).symm)
  have hdiv_eq : FiniteTimeSingularity.div (cylField (profR u) (profZ u)) (mer r z)
      = FiniteTimeSingularity.div u (mer r z) := by
    show (fderiv ℝ (cylField (profR u) (profZ u)) (mer r z)).trace ℝ R3
      = (fderiv ℝ u (mer r z)).trace ℝ R3
    rw [hEv.fderiv_eq]
  rw [hdiv_eq, hdiv] at hcyl
  rw [radial_mer, abs_of_pos hp, axial_mer] at hcyl
  exact hcyl.symm

theorem profiles_of_axiNoSwirl_div (u : Work.Cyl.R3 → Work.Cyl.R3) (hu : ContDiff ℝ 1 u)
    (haxi : Work.Cyl.IsAxiNoSwirl u) (hdiv : ∀ x, FiniteTimeSingularity.div u x = 0) :
    ∃ ur uz : ℝ → ℝ → ℝ,
      (∀ x, 0 < Work.Cyl.radial x → u x = Work.Cyl.cylField ur uz x) ∧
      DifferentiableOn ℝ (fun p : ℝ × ℝ => ur p.1 p.2) {p | 0 < p.1} ∧
      DifferentiableOn ℝ (fun p : ℝ × ℝ => uz p.1 p.2) {p | 0 < p.1} ∧
      (∀ p : ℝ × ℝ, 0 < p.1 →
        Work.Cyl.pdR ur p.1 p.2 + ur p.1 p.2 / p.1 + Work.Cyl.pdZ uz p.1 p.2 = 0) := by
  obtain ⟨ur₀, uz₀, hu_eq⟩ := haxi
  exact ⟨profR u, profZ u,
    (fun x hrx => eq_cylField_of_pos hu_eq hrx),
    (differentiable_profR u hu).differentiableOn,
    (differentiable_profZ u hu).differentiableOn,
    (div_identity u hu hu_eq hdiv)⟩

end Work.ConstructionInstance
