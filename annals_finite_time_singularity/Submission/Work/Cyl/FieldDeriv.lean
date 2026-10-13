import Mathlib.Analysis.Calculus.ContDiff.WithLp
import Mathlib.Analysis.Calculus.Deriv.Add
import Mathlib.Analysis.Calculus.Deriv.Inv
import Mathlib.Analysis.Calculus.Deriv.Prod
import Mathlib.Analysis.Calculus.FDeriv.WithLp
import Mathlib.Analysis.Calculus.Gradient.Basic
import Mathlib.Analysis.SpecialFunctions.Sqrt
import Submission.Work.Cyl.Basic

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

/-!
# Derivatives of the no-swirl field `cylField ur uz`
-/

set_option autoImplicit false
set_option linter.unusedSimpArgs false

open scoped Matrix
open Work.Cyl

namespace Work.Cyl

/-! ## The two-variable chain rule -/

/-- The first slice of a differentiable two-variable function is differentiable. -/
theorem differentiableAt_slice_fst (f : ℝ → ℝ → ℝ) (r z : ℝ) (hf : DiffAt2 f r z) :
    DifferentiableAt ℝ (fun s : ℝ => f s z) r := by
  have hpair : HasFDerivAt (fun s : ℝ => ((s, z) : ℝ × ℝ))
      ((1 : ℝ →L[ℝ] ℝ).prod (0 : ℝ →L[ℝ] ℝ)) r :=
    (hasFDerivAt_id (x := r)).prodMk (hasFDerivAt_const (x := r) z)
  exact (hf.hasFDerivAt.comp r hpair).differentiableAt

/-- The second slice of a differentiable two-variable function is differentiable. -/
theorem differentiableAt_slice_snd (f : ℝ → ℝ → ℝ) (r z : ℝ) (hf : DiffAt2 f r z) :
    DifferentiableAt ℝ (fun s : ℝ => f r s) z := by
  have hpair : HasFDerivAt (fun s : ℝ => ((r, s) : ℝ × ℝ))
      ((0 : ℝ →L[ℝ] ℝ).prod (1 : ℝ →L[ℝ] ℝ)) z :=
    (hasFDerivAt_const (x := z) r).prodMk (hasFDerivAt_id (x := z))
  exact (hf.hasFDerivAt.comp z hpair).differentiableAt

theorem fderiv_prod_apply_fst (f : ℝ → ℝ → ℝ) (r z : ℝ) (hf : DiffAt2 f r z) :
    fderiv ℝ (fun p : ℝ × ℝ => f p.1 p.2) (r, z) (1, 0) = pdR f r z := by
  rw [fderiv_apply_eq_deriv_line _ _ _ hf]
  have hfun : (fun t : ℝ => (fun p : ℝ × ℝ => f p.1 p.2) ((r, z) + t • (1, 0))) =
      fun t : ℝ => f (r + t) z := by
    funext t; simp
  rw [hfun, pdR]
  have hpair : HasFDerivAt (fun s : ℝ => ((s, z) : ℝ × ℝ))
      ((1 : ℝ →L[ℝ] ℝ).prod (0 : ℝ →L[ℝ] ℝ)) r :=
    (hasFDerivAt_id (x := r)).prodMk (hasFDerivAt_const (x := r) z)
  have hd : DifferentiableAt ℝ (fun s : ℝ => f s z) r :=
    (HasFDerivAt.comp (x := r) (f := fun s : ℝ => ((s, z) : ℝ × ℝ))
      (g := fun p : ℝ × ℝ => f p.1 p.2) hf.hasFDerivAt hpair).differentiableAt
  have hd' : DifferentiableAt ℝ (fun s : ℝ => f s z) (r + 0) := by simpa using hd
  have hshift : HasDerivAt (fun t : ℝ => r + t) 1 0 := by
    simpa using (hasDerivAt_id (0 : ℝ)).const_add r
  have h := hd'.hasFDerivAt.comp_hasDerivAt 0 hshift
  have hval : (fderiv ℝ (fun s : ℝ => f s z) (r + 0)) 1 = deriv (fun s : ℝ => f s z) r := by
    rw [show r + 0 = r from add_zero r]
    exact (hd.hasFDerivAt.hasDerivAt).deriv.symm
  change deriv ((fun s : ℝ => f s z) ∘ fun t : ℝ => r + t) 0 = deriv (fun r' : ℝ => f r' z) r
  rw [h.deriv, hval]

theorem fderiv_prod_apply_snd (f : ℝ → ℝ → ℝ) (r z : ℝ) (hf : DiffAt2 f r z) :
    fderiv ℝ (fun p : ℝ × ℝ => f p.1 p.2) (r, z) (0, 1) = pdZ f r z := by
  rw [fderiv_apply_eq_deriv_line _ _ _ hf]
  have hfun : (fun t : ℝ => (fun p : ℝ × ℝ => f p.1 p.2) ((r, z) + t • (0, 1))) =
      fun t : ℝ => f r (z + t) := by
    funext t; simp
  rw [hfun, pdZ]
  have hpair : HasFDerivAt (fun s : ℝ => ((r, s) : ℝ × ℝ))
      ((0 : ℝ →L[ℝ] ℝ).prod (1 : ℝ →L[ℝ] ℝ)) z :=
    (hasFDerivAt_const (x := z) r).prodMk (hasFDerivAt_id (x := z))
  have hd : DifferentiableAt ℝ (fun s : ℝ => f r s) z :=
    (HasFDerivAt.comp (x := z) (f := fun s : ℝ => ((r, s) : ℝ × ℝ))
      (g := fun p : ℝ × ℝ => f p.1 p.2) hf.hasFDerivAt hpair).differentiableAt
  have hd' : DifferentiableAt ℝ (fun s : ℝ => f r s) (z + 0) := by simpa using hd
  have hshift : HasDerivAt (fun t : ℝ => z + t) 1 0 := by
    simpa using (hasDerivAt_id (0 : ℝ)).const_add z
  have h := hd'.hasFDerivAt.comp_hasDerivAt 0 hshift
  have hval : (fderiv ℝ (fun s : ℝ => f r s) (z + 0)) 1 = deriv (fun s : ℝ => f r s) z := by
    rw [show z + 0 = z from add_zero z]
    exact (hd.hasFDerivAt.hasDerivAt).deriv.symm
  change deriv ((fun s : ℝ => f r s) ∘ fun t : ℝ => z + t) 0 = deriv (fun z' : ℝ => f r z') z
  rw [h.deriv, hval]

/-- Chain rule for the composition of a two-variable function with a pair of curves. -/
theorem hasDerivAt_comp_two (f : ℝ → ℝ → ℝ) (R Z : ℝ → ℝ) (r' z' t₀ : ℝ)
    (hf : DiffAt2 f (R t₀) (Z t₀)) (hR : HasDerivAt R r' t₀) (hZ : HasDerivAt Z z' t₀) :
    HasDerivAt (fun t => f (R t) (Z t))
      (pdR f (R t₀) (Z t₀) * r' + pdZ f (R t₀) (Z t₀) * z') t₀ := by
  have hpair : HasDerivAt (fun t : ℝ => (R t, Z t)) (r', z') t₀ := hR.prodMk hZ
  have hcomp := hf.hasFDerivAt.comp_hasDerivAt t₀ hpair
  have hval : fderiv ℝ (fun p : ℝ × ℝ => f p.1 p.2) (R t₀, Z t₀) (r', z') =
      pdR f (R t₀) (Z t₀) * r' + pdZ f (R t₀) (Z t₀) * z' := by
    have h1 := fderiv_prod_apply_fst f (R t₀) (Z t₀) hf
    have h2 := fderiv_prod_apply_snd f (R t₀) (Z t₀) hf
    have hsplit : (r', z') = r' • ((1 : ℝ), (0 : ℝ)) + z' • ((0 : ℝ), (1 : ℝ)) := by
      simp
    rw [hsplit, map_add, map_smul, map_smul, h1, h2]
    ring
  rw [hval] at hcomp
  exact hcomp

/-! ## Coordinates of the shifted point -/

section LineFacts

variable (x : R3)

@[simp] lemma e0_apply_zero : (e0 : R3) 0 = 1 := by simp [e0, FiniteTimeSingularity.e]
@[simp] lemma e0_apply_one : (e0 : R3) 1 = 0 := by simp [e0, FiniteTimeSingularity.e]
@[simp] lemma e0_apply_two : (e0 : R3) 2 = 0 := by simp [e0, FiniteTimeSingularity.e]
@[simp] lemma e1_apply_zero : (e1 : R3) 0 = 0 := by simp [e1, FiniteTimeSingularity.e]
@[simp] lemma e1_apply_one : (e1 : R3) 1 = 1 := by simp [e1, FiniteTimeSingularity.e]
@[simp] lemma e1_apply_two : (e1 : R3) 2 = 0 := by simp [e1, FiniteTimeSingularity.e]

@[simp] lemma add_smul_e0_apply_zero (t : ℝ) : (x + t • e0) 0 = x 0 + t := by
  simp [e0, FiniteTimeSingularity.e]
@[simp] lemma add_smul_e0_apply_one (t : ℝ) : (x + t • e0) 1 = x 1 := by
  simp [e0, FiniteTimeSingularity.e]
@[simp] lemma add_smul_e0_apply_two (t : ℝ) : (x + t • e0) 2 = x 2 := by
  simp [e0, FiniteTimeSingularity.e]
@[simp] lemma add_smul_e1_apply_zero (t : ℝ) : (x + t • e1) 0 = x 0 := by
  simp [e1, FiniteTimeSingularity.e]
@[simp] lemma add_smul_e1_apply_one (t : ℝ) : (x + t • e1) 1 = x 1 + t := by
  simp [e1, FiniteTimeSingularity.e]
@[simp] lemma add_smul_e1_apply_two (t : ℝ) : (x + t • e1) 2 = x 2 := by
  simp [e1, FiniteTimeSingularity.e]
@[simp] lemma add_smul_eZ_apply_zero (t : ℝ) : (x + t • eZ) 0 = x 0 := by
  simp [eZ, FiniteTimeSingularity.e]
@[simp] lemma add_smul_eZ_apply_one (t : ℝ) : (x + t • eZ) 1 = x 1 := by
  simp [eZ, FiniteTimeSingularity.e]
@[simp] lemma add_smul_eZ_apply_two (t : ℝ) : (x + t • eZ) 2 = x 2 + t := by
  simp [eZ, FiniteTimeSingularity.e]

lemma radSq_add_smul_e0 (t : ℝ) : radSq (x + t • e0) = (x 0 + t) ^ 2 + x 1 ^ 2 := by
  change (x + t • e0) 0 ^ 2 + (x + t • e0) 1 ^ 2 = (x 0 + t) ^ 2 + x 1 ^ 2
  rw [add_smul_e0_apply_zero, add_smul_e0_apply_one]
lemma radSq_add_smul_e1 (t : ℝ) : radSq (x + t • e1) = x 0 ^ 2 + (x 1 + t) ^ 2 := by
  change (x + t • e1) 0 ^ 2 + (x + t • e1) 1 ^ 2 = x 0 ^ 2 + (x 1 + t) ^ 2
  rw [add_smul_e1_apply_zero, add_smul_e1_apply_one]
lemma radSq_add_smul_eZ (t : ℝ) : radSq (x + t • eZ) = radSq x := by
  change (x + t • eZ) 0 ^ 2 + (x + t • eZ) 1 ^ 2 = radSq x
  rw [add_smul_eZ_apply_zero, add_smul_eZ_apply_one]
  rfl

lemma radial_add_smul_e0 (t : ℝ) : radial (x + t • e0) = Real.sqrt ((x 0 + t) ^ 2 + x 1 ^ 2) := by
  rw [radial, radSq_add_smul_e0]
lemma radial_add_smul_e1 (t : ℝ) : radial (x + t • e1) = Real.sqrt (x 0 ^ 2 + (x 1 + t) ^ 2) := by
  rw [radial, radSq_add_smul_e1]
lemma radial_add_smul_eZ (t : ℝ) : radial (x + t • eZ) = radial x := by
  rw [radial, radSq_add_smul_eZ, ← radial]

@[simp] lemma axial_add_smul_e0 (t : ℝ) : axial (x + t • e0) = axial x := by
  simp [axial]
@[simp] lemma axial_add_smul_e1 (t : ℝ) : axial (x + t • e1) = axial x := by
  simp [axial]
lemma axial_add_smul_eZ (t : ℝ) : axial (x + t • eZ) = axial x + t := by
  simp [axial]

end LineFacts

/-! ## Derivatives of the coordinate functions along coordinate lines -/

theorem hasDerivAt_radial_line_e0 (x : R3) (hr : radial x ≠ 0) :
    HasDerivAt (fun t : ℝ => radial (x + t • e0)) (x 0 / radial x) 0 := by
  have hlin : HasDerivAt (fun t : ℝ => x 0 + t) 1 0 := by
    simpa using (hasDerivAt_id (0 : ℝ)).const_add (x 0)
  have hsq : HasDerivAt (fun t : ℝ => (x 0 + t) * (x 0 + t)) (2 * x 0) 0 := by
    have hm := hlin.mul hlin
    convert hm using 1
    ring
  have hinner : HasDerivAt (fun t : ℝ => (x 0 + t) ^ 2 + x 1 ^ 2) (2 * x 0) 0 := by
    have h2 : (fun t : ℝ => (x 0 + t) ^ 2 + x 1 ^ 2) =
        fun t : ℝ => (x 0 + t) * (x 0 + t) + x 1 ^ 2 := by
      funext t; ring
    rw [h2]
    simpa using hsq.add_const (x 1 ^ 2)
  have hx0 : (x 0 + (0 : ℝ)) ^ 2 + x 1 ^ 2 ≠ 0 := by
    rw [add_zero]
    change radSq x ≠ 0
    rw [← radial_sq]
    exact pow_ne_zero 2 hr
  have hsqrt := hinner.sqrt hx0
  rw [show (fun t : ℝ => radial (x + t • e0)) =
      fun t : ℝ => Real.sqrt ((x 0 + t) ^ 2 + x 1 ^ 2) from funext fun t => radial_add_smul_e0 x t]
  convert hsqrt using 1
  rw [add_zero, radial, radSq]
  field_simp

theorem hasDerivAt_radial_line_e1 (x : R3) (hr : radial x ≠ 0) :
    HasDerivAt (fun t : ℝ => radial (x + t • e1)) (x 1 / radial x) 0 := by
  have hlin : HasDerivAt (fun t : ℝ => x 1 + t) 1 0 := by
    simpa using (hasDerivAt_id (0 : ℝ)).const_add (x 1)
  have hsq : HasDerivAt (fun t : ℝ => (x 1 + t) * (x 1 + t)) (2 * x 1) 0 := by
    have hm := hlin.mul hlin
    convert hm using 1
    ring
  have hinner : HasDerivAt (fun t : ℝ => x 0 ^ 2 + (x 1 + t) ^ 2) (2 * x 1) 0 := by
    have h2 : (fun t : ℝ => x 0 ^ 2 + (x 1 + t) ^ 2) =
        fun t : ℝ => x 0 ^ 2 + (x 1 + t) * (x 1 + t) := by
      funext t; ring
    rw [h2]
    simpa using (hsq.const_add (x 0 ^ 2))
  have hx0 : x 0 ^ 2 + (x 1 + (0 : ℝ)) ^ 2 ≠ 0 := by
    rw [add_zero]
    change radSq x ≠ 0
    rw [← radial_sq]
    exact pow_ne_zero 2 hr
  have hsqrt := hinner.sqrt hx0
  rw [show (fun t : ℝ => radial (x + t • e1)) =
      fun t : ℝ => Real.sqrt (x 0 ^ 2 + (x 1 + t) ^ 2) from funext fun t => radial_add_smul_e1 x t]
  convert hsqrt using 1
  rw [add_zero, radial, radSq]
  field_simp

theorem hasDerivAt_radial_line_eZ (x : R3) :
    HasDerivAt (fun t : ℝ => radial (x + t • eZ)) 0 0 := by
  have h : (fun t : ℝ => radial (x + t • eZ)) = fun _ => radial x := by
    funext t; rw [radial_add_smul_eZ]
  rw [h]
  exact hasDerivAt_const (0 : ℝ) (radial x)

theorem hasDerivAt_axial_line_e0 (x : R3) :
    HasDerivAt (fun t : ℝ => axial (x + t • e0)) 0 0 := by
  have h : (fun t : ℝ => axial (x + t • e0)) = fun _ => axial x := by
    funext t; rw [axial_add_smul_e0]
  rw [h]
  exact hasDerivAt_const (0 : ℝ) (axial x)

theorem hasDerivAt_axial_line_e1 (x : R3) :
    HasDerivAt (fun t : ℝ => axial (x + t • e1)) 0 0 := by
  have h : (fun t : ℝ => axial (x + t • e1)) = fun _ => axial x := by
    funext t; rw [axial_add_smul_e1]
  rw [h]
  exact hasDerivAt_const (0 : ℝ) (axial x)

theorem hasDerivAt_axial_line_eZ (x : R3) :
    HasDerivAt (fun t : ℝ => axial (x + t • eZ)) 1 0 := by
  have h : (fun t : ℝ => axial (x + t • eZ)) = fun t => axial x + t := by
    funext t; rw [axial_add_smul_eZ]
  rw [h]
  simpa using (hasDerivAt_id (0 : ℝ)).const_add (axial x)

/-! ## The composite chain rule along coordinate lines -/

theorem hasDerivAt_comp_cyl_e0 (g : ℝ → ℝ → ℝ) (x : R3) (hg : DiffAt2 g (radial x) (axial x))
    (hr : 0 < radial x) :
    HasDerivAt (fun t : ℝ => g (radial (x + t • e0)) (axial (x + t • e0)))
      (pdR g (radial x) (axial x) * (x 0 / radial x)) 0 := by
  have hg' : DiffAt2 g (radial (x + (0:ℝ) • e0)) (axial (x + (0:ℝ) • e0)) := by simpa using hg
  have h := hasDerivAt_comp_two g (fun t : ℝ => radial (x + t • e0))
    (fun t : ℝ => axial (x + t • e0)) (x 0 / radial x) (0 : ℝ) (0 : ℝ) hg'
    (hasDerivAt_radial_line_e0 x (ne_of_gt hr)) (hasDerivAt_axial_line_e0 x)
  simpa using h

theorem hasDerivAt_comp_cyl_e1 (g : ℝ → ℝ → ℝ) (x : R3) (hg : DiffAt2 g (radial x) (axial x))
    (hr : 0 < radial x) :
    HasDerivAt (fun t : ℝ => g (radial (x + t • e1)) (axial (x + t • e1)))
      (pdR g (radial x) (axial x) * (x 1 / radial x)) 0 := by
  have hg' : DiffAt2 g (radial (x + (0:ℝ) • e1)) (axial (x + (0:ℝ) • e1)) := by simpa using hg
  have h := hasDerivAt_comp_two g (fun t : ℝ => radial (x + t • e1))
    (fun t : ℝ => axial (x + t • e1)) (x 1 / radial x) (0 : ℝ) (0 : ℝ) hg'
    (hasDerivAt_radial_line_e1 x (ne_of_gt hr)) (hasDerivAt_axial_line_e1 x)
  simpa using h

theorem hasDerivAt_comp_cyl_eZ (g : ℝ → ℝ → ℝ) (x : R3) (hg : DiffAt2 g (radial x) (axial x))
    (_hr : 0 < radial x) :
    HasDerivAt (fun t : ℝ => g (radial (x + t • eZ)) (axial (x + t • eZ)))
      (pdZ g (radial x) (axial x)) 0 := by
  have hg' : DiffAt2 g (radial (x + (0:ℝ) • eZ)) (axial (x + (0:ℝ) • eZ)) := by simpa using hg
  have h := hasDerivAt_comp_two g (fun t : ℝ => radial (x + t • eZ))
    (fun t : ℝ => axial (x + t • eZ)) (0 : ℝ) (1 : ℝ) (0 : ℝ) hg'
    (hasDerivAt_radial_line_eZ x) (hasDerivAt_axial_line_eZ x)
  simpa using h


/-! ## The nine partial derivatives of `cylField ur uz` -/

lemma redR_apply (ur : ℝ → ℝ → ℝ) (r z : ℝ) : redR ur r z = ur r z / r := rfl

lemma pdR_redR {ur : ℝ → ℝ → ℝ} {r z : ℝ} (hur : DiffAt2 ur r z) (hr : r ≠ 0) :
    pdR (redR ur) r z = pdR ur r z / r - ur r z / r ^ 2 := by
  have hf : DifferentiableAt ℝ (fun r' : ℝ => ur r' z) r := differentiableAt_slice_fst ur r z hur
  have hg : DifferentiableAt ℝ (fun r' : ℝ => r') r := differentiableAt_id
  have h2 : deriv ((fun r' : ℝ => ur r' z) / (fun r' : ℝ => r')) r =
      (deriv (fun r' : ℝ => ur r' z) r * r - ur r z * deriv (fun r' : ℝ => r') r) / r ^ 2 :=
    deriv_div hf hg hr
  have h3 : deriv (fun r' : ℝ => r') r = 1 := by simp
  rw [pdR, show (fun r' : ℝ => redR ur r' z) =
    ((fun r' : ℝ => ur r' z) / fun r' : ℝ => r') from rfl, h2, h3, pdR]
  field_simp

lemma pdZ_redR (ur : ℝ → ℝ → ℝ) (r z : ℝ) : pdZ (redR ur) r z = pdZ ur r z / r := by
  have hfun : (fun z' : ℝ => redR ur r z') = fun z' : ℝ => ur r z' / r := by funext z'; rfl
  rw [pdZ, hfun, pdZ, deriv_div_const]

lemma cylField_apply_zero' (ur uz : ℝ → ℝ → ℝ) (x : R3) :
    (cylField ur uz x) 0 = redR ur (radial x) (axial x) * x 0 := by
  rw [cylField_zero]; simp only [redR]; ring

lemma cylField_apply_one' (ur uz : ℝ → ℝ → ℝ) (x : R3) :
    (cylField ur uz x) 1 = redR ur (radial x) (axial x) * x 1 := by
  rw [cylField_one]; simp only [redR]; ring

lemma cylField_apply_two' (ur uz : ℝ → ℝ → ℝ) (x : R3) :
    (cylField ur uz x) 2 = uz (radial x) (axial x) := cylField_two ur uz x

theorem pd_cylField_00 (ur uz : ℝ → ℝ → ℝ) (x : R3)
    (hur : DiffAt2 ur (radial x) (axial x)) (hr : 0 < radial x) :
    pd 0 (fun y => (cylField ur uz y) 0) x =
      pdR (redR ur) (radial x) (axial x) * (x 0 ^ 2 / radial x)
        + redR ur (radial x) (axial x) := by
  have hrne : radial x ≠ 0 := ne_of_gt hr
  have hcomp := hasDerivAt_comp_cyl_e0 ur x hur hr
  have hlin : HasDerivAt (fun t : ℝ => x 0 + t) 1 0 := by
    simpa using (hasDerivAt_id (0 : ℝ)).const_add (x 0)
  have hnum := hcomp.mul hlin
  have hden := hasDerivAt_radial_line_e0 x hrne
  have hx0 : (fun t : ℝ => radial (x + t • e0)) (0 : ℝ) ≠ 0 := by simpa using hrne
  have hquot := hnum.div hden hx0
  simp only [zero_smul, add_zero, Pi.mul_apply] at hquot
  have hfun : (fun t : ℝ => (cylField ur uz (x + t • basisVec 0)) 0) = fun t : ℝ =>
      ur (radial (x + t • e0)) (axial (x + t • e0)) * (x 0 + t) / radial (x + t • e0) := by
    funext t
    rw [show x + t • basisVec 0 = x + t • e0 from rfl, cylField_zero]
    simp only [add_smul_e0_apply_zero, add_smul_e0_apply_one]
  rw [pd, hfun]
  change deriv (((fun t : ℝ => ur (radial (x + t • e0)) (axial (x + t • e0))) *
      fun t : ℝ => x 0 + t) / fun t : ℝ => radial (x + t • e0)) 0 = _
  rw [hquot.deriv, pdR_redR hur hrne]
  simp only [redR]
  field_simp
  ring

theorem pd_cylField_01 (ur uz : ℝ → ℝ → ℝ) (x : R3)
    (hur : DiffAt2 ur (radial x) (axial x)) (hr : 0 < radial x) :
    pd 0 (fun y => (cylField ur uz y) 1) x =
      pdR (redR ur) (radial x) (axial x) * (x 0 * x 1 / radial x) := by
  have hrne : radial x ≠ 0 := ne_of_gt hr
  have hcomp := hasDerivAt_comp_cyl_e0 ur x hur hr
  have hconst : HasDerivAt (fun _ : ℝ => x 1) 0 0 := hasDerivAt_const (0 : ℝ) (x 1)
  have hnum := hcomp.mul hconst
  have hden := hasDerivAt_radial_line_e0 x hrne
  have hx0 : (fun t : ℝ => radial (x + t • e0)) (0 : ℝ) ≠ 0 := by simpa using hrne
  have hquot := hnum.div hden hx0
  simp only [zero_smul, add_zero, Pi.mul_apply] at hquot
  have hfun : (fun t : ℝ => (cylField ur uz (x + t • basisVec 0)) 1) = fun t : ℝ =>
      ur (radial (x + t • e0)) (axial (x + t • e0)) * x 1 / radial (x + t • e0) := by
    funext t
    rw [show x + t • basisVec 0 = x + t • e0 from rfl, cylField_one]
    simp only [add_smul_e0_apply_zero, add_smul_e0_apply_one]
  rw [pd, hfun]
  change deriv (((fun t : ℝ => ur (radial (x + t • e0)) (axial (x + t • e0))) *
      fun _ : ℝ => x 1) / fun t : ℝ => radial (x + t • e0)) 0 = _
  rw [hquot.deriv, pdR_redR hur hrne]
  simp only [redR]
  field_simp
  ring

theorem pd_cylField_02 (ur uz : ℝ → ℝ → ℝ) (x : R3)
    (huz : DiffAt2 uz (radial x) (axial x)) (hr : 0 < radial x) :
    pd 0 (fun y => (cylField ur uz y) 2) x =
      pdR uz (radial x) (axial x) * (x 0 / radial x) := by
  have hcomp := hasDerivAt_comp_cyl_e0 uz x huz hr
  have hfun : (fun t : ℝ => (cylField ur uz (x + t • basisVec 0)) 2) =
      fun t : ℝ => uz (radial (x + t • e0)) (axial (x + t • e0)) := by
    funext t
    rw [show x + t • basisVec 0 = x + t • e0 from rfl, cylField_apply_two']
  rw [pd, hfun, hcomp.deriv]

theorem pd_cylField_10 (ur uz : ℝ → ℝ → ℝ) (x : R3)
    (hur : DiffAt2 ur (radial x) (axial x)) (hr : 0 < radial x) :
    pd 1 (fun y => (cylField ur uz y) 0) x =
      pdR (redR ur) (radial x) (axial x) * (x 0 * x 1 / radial x) := by
  have hrne : radial x ≠ 0 := ne_of_gt hr
  have hcomp := hasDerivAt_comp_cyl_e1 ur x hur hr
  have hconst : HasDerivAt (fun _ : ℝ => x 0) 0 0 := hasDerivAt_const (0 : ℝ) (x 0)
  have hnum := hcomp.mul hconst
  have hden := hasDerivAt_radial_line_e1 x hrne
  have hx0 : (fun t : ℝ => radial (x + t • e1)) (0 : ℝ) ≠ 0 := by simpa using hrne
  have hquot := hnum.div hden hx0
  simp only [zero_smul, add_zero, Pi.mul_apply] at hquot
  have hfun : (fun t : ℝ => (cylField ur uz (x + t • basisVec 1)) 0) = fun t : ℝ =>
      ur (radial (x + t • e1)) (axial (x + t • e1)) * x 0 / radial (x + t • e1) := by
    funext t
    rw [show x + t • basisVec 1 = x + t • e1 from rfl, cylField_zero]
    simp only [add_smul_e1_apply_zero, add_smul_e1_apply_one]
  rw [pd, hfun]
  change deriv (((fun t : ℝ => ur (radial (x + t • e1)) (axial (x + t • e1))) *
      fun _ : ℝ => x 0) / fun t : ℝ => radial (x + t • e1)) 0 = _
  rw [hquot.deriv, pdR_redR hur hrne]
  simp only [redR]
  field_simp
  ring

theorem pd_cylField_11 (ur uz : ℝ → ℝ → ℝ) (x : R3)
    (hur : DiffAt2 ur (radial x) (axial x)) (hr : 0 < radial x) :
    pd 1 (fun y => (cylField ur uz y) 1) x =
      pdR (redR ur) (radial x) (axial x) * (x 1 ^ 2 / radial x)
        + redR ur (radial x) (axial x) := by
  have hrne : radial x ≠ 0 := ne_of_gt hr
  have hcomp := hasDerivAt_comp_cyl_e1 ur x hur hr
  have hlin : HasDerivAt (fun t : ℝ => x 1 + t) 1 0 := by
    simpa using (hasDerivAt_id (0 : ℝ)).const_add (x 1)
  have hnum := hcomp.mul hlin
  have hden := hasDerivAt_radial_line_e1 x hrne
  have hx0 : (fun t : ℝ => radial (x + t • e1)) (0 : ℝ) ≠ 0 := by simpa using hrne
  have hquot := hnum.div hden hx0
  simp only [zero_smul, add_zero, Pi.mul_apply] at hquot
  have hfun : (fun t : ℝ => (cylField ur uz (x + t • basisVec 1)) 1) = fun t : ℝ =>
      ur (radial (x + t • e1)) (axial (x + t • e1)) * (x 1 + t) / radial (x + t • e1) := by
    funext t
    rw [show x + t • basisVec 1 = x + t • e1 from rfl, cylField_one]
    simp only [add_smul_e1_apply_zero, add_smul_e1_apply_one]
  rw [pd, hfun]
  change deriv (((fun t : ℝ => ur (radial (x + t • e1)) (axial (x + t • e1))) *
      fun t : ℝ => x 1 + t) / fun t : ℝ => radial (x + t • e1)) 0 = _
  rw [hquot.deriv, pdR_redR hur hrne]
  simp only [redR]
  field_simp
  ring

theorem pd_cylField_12 (ur uz : ℝ → ℝ → ℝ) (x : R3)
    (huz : DiffAt2 uz (radial x) (axial x)) (hr : 0 < radial x) :
    pd 1 (fun y => (cylField ur uz y) 2) x =
      pdR uz (radial x) (axial x) * (x 1 / radial x) := by
  have hcomp := hasDerivAt_comp_cyl_e1 uz x huz hr
  have hfun : (fun t : ℝ => (cylField ur uz (x + t • basisVec 1)) 2) =
      fun t : ℝ => uz (radial (x + t • e1)) (axial (x + t • e1)) := by
    funext t
    rw [show x + t • basisVec 1 = x + t • e1 from rfl, cylField_apply_two']
  rw [pd, hfun, hcomp.deriv]

theorem pd_cylField_20 (ur uz : ℝ → ℝ → ℝ) (x : R3)
    (hur : DiffAt2 ur (radial x) (axial x)) (hr : 0 < radial x) :
    pd 2 (fun y => (cylField ur uz y) 0) x =
      pdZ (redR ur) (radial x) (axial x) * x 0 := by
  have hcomp := hasDerivAt_comp_cyl_eZ ur x hur hr
  have hd : HasDerivAt (fun t : ℝ => ur (radial (x + t • eZ)) (axial (x + t • eZ)) / radial x)
      (pdZ ur (radial x) (axial x) / radial x) 0 := hcomp.div_const (radial x)
  have h2 : HasDerivAt (fun t : ℝ =>
      ur (radial (x + t • eZ)) (axial (x + t • eZ)) / radial x * x 0)
      (pdZ ur (radial x) (axial x) / radial x * x 0) 0 := hd.mul_const (x 0)
  have hfun : (fun t : ℝ => (cylField ur uz (x + t • basisVec 2)) 0) = fun t : ℝ =>
      ur (radial (x + t • eZ)) (axial (x + t • eZ)) / radial x * x 0 := by
    funext t
    rw [show x + t • basisVec 2 = x + t • eZ from rfl, cylField_zero, radial_add_smul_eZ]
    simp only [add_smul_eZ_apply_zero]
    ring
  rw [pd, hfun, h2.deriv, pdZ_redR]

theorem pd_cylField_21 (ur uz : ℝ → ℝ → ℝ) (x : R3)
    (hur : DiffAt2 ur (radial x) (axial x)) (hr : 0 < radial x) :
    pd 2 (fun y => (cylField ur uz y) 1) x =
      pdZ (redR ur) (radial x) (axial x) * x 1 := by
  have hcomp := hasDerivAt_comp_cyl_eZ ur x hur hr
  have hd : HasDerivAt (fun t : ℝ => ur (radial (x + t • eZ)) (axial (x + t • eZ)) / radial x)
      (pdZ ur (radial x) (axial x) / radial x) 0 := hcomp.div_const (radial x)
  have h2 : HasDerivAt (fun t : ℝ =>
      ur (radial (x + t • eZ)) (axial (x + t • eZ)) / radial x * x 1)
      (pdZ ur (radial x) (axial x) / radial x * x 1) 0 := hd.mul_const (x 1)
  have hfun : (fun t : ℝ => (cylField ur uz (x + t • basisVec 2)) 1) = fun t : ℝ =>
      ur (radial (x + t • eZ)) (axial (x + t • eZ)) / radial x * x 1 := by
    funext t
    rw [show x + t • basisVec 2 = x + t • eZ from rfl, cylField_one, radial_add_smul_eZ]
    simp only [add_smul_eZ_apply_one]
    ring
  rw [pd, hfun, h2.deriv, pdZ_redR]

theorem pd_cylField_22 (ur uz : ℝ → ℝ → ℝ) (x : R3)
    (huz : DiffAt2 uz (radial x) (axial x)) (hr : 0 < radial x) :
    pd 2 (fun y => (cylField ur uz y) 2) x = pdZ uz (radial x) (axial x) := by
  have hcomp := hasDerivAt_comp_cyl_eZ uz x huz hr
  have hfun : (fun t : ℝ => (cylField ur uz (x + t • basisVec 2)) 2) =
      fun t : ℝ => uz (radial (x + t • eZ)) (axial (x + t • eZ)) := by
    funext t
    rw [show x + t • basisVec 2 = x + t • eZ from rfl, cylField_apply_two']
  rw [pd, hfun, hcomp.deriv]

/-! ## Differentiability of the field -/

lemma differentiableAt_radial (x : R3) (hr : radial x ≠ 0) : DifferentiableAt ℝ radial x := by
  have h1 : DifferentiableAt ℝ (fun y : R3 => radSq y) x := by
    have h : (fun y : R3 => radSq y) = fun y : R3 => y 0 ^ 2 + y 1 ^ 2 := by
      funext y; rfl
    rw [h]
    fun_prop
  have h2 : (fun y : R3 => radSq y) x ≠ 0 := by
    have : radSq x ≠ 0 := by rw [← radial_sq]; exact pow_ne_zero 2 hr
    simpa using this
  have h3 := h1.sqrt h2
  convert h3 using 1
  funext y; rfl

lemma differentiableAt_axial (x : R3) : DifferentiableAt ℝ axial x := by
  have h : axial = fun y : R3 => y 2 := rfl
  rw [h]
  exact (PiLp.hasFDerivAt_apply (𝕜 := ℝ) (p := 2) x 2).differentiableAt

lemma differentiableAt_radialVec (x : R3) : DifferentiableAt ℝ radialVec x := by
  have hcoord : ∀ j : Fin 3, DifferentiableAt ℝ (fun y : R3 => y j) x := fun j =>
    (PiLp.hasFDerivAt_apply (𝕜 := ℝ) (p := 2) x j).differentiableAt
  rw [show radialVec = fun y : R3 => (y 0) • e0 + (y 1) • e1 from by
    funext y
    apply PiLp.ext
    intro i
    fin_cases i <;> simp [radialVec, e0, e1, FiniteTimeSingularity.e]]
  exact ((hcoord 0).smul_const e0).add ((hcoord 1).smul_const e1)

theorem differentiableAt_cylField (ur uz : ℝ → ℝ → ℝ) (x : R3)
    (hur : DiffAt2 ur (radial x) (axial x)) (huz : DiffAt2 uz (radial x) (axial x))
    (hr : 0 < radial x) :
    DifferentiableAt ℝ (cylField ur uz) x := by
  have hrne : radial x ≠ 0 := ne_of_gt hr
  have hrad := differentiableAt_radial x hrne
  have hax := differentiableAt_axial x
  have hpair : DifferentiableAt ℝ (fun y : R3 => (radial y, axial y)) x :=
    (hrad.hasFDerivAt.prodMk hax.hasFDerivAt).differentiableAt
  have hur' : DifferentiableAt ℝ (fun y : R3 => ur (radial y) (axial y)) x := by
    have h := hur.comp x hpair
    convert h using 1
    funext y; rfl
  have huz' : DifferentiableAt ℝ (fun y : R3 => uz (radial y) (axial y)) x := by
    have h := huz.comp x hpair
    convert h using 1
    funext y; rfl
  have hinv : DifferentiableAt ℝ (fun y : R3 => (radial y)⁻¹) x :=
    hrad.inv (by simpa using hrne)
  have hA : DifferentiableAt ℝ (fun y : R3 => ur (radial y) (axial y) * (radial y)⁻¹) x :=
    hur'.mul hinv
  rw [show cylField ur uz = fun y : R3 =>
      (ur (radial y) (axial y) * (radial y)⁻¹) • radialVec y + uz (radial y) (axial y) • eZ from by
    funext y
    rw [cylField, div_eq_mul_inv]]
  exact (hA.smul (differentiableAt_radialVec x)).add
    (huz'.smul (differentiableAt_const eZ))

/-! ## The divergence of the field -/

theorem div_cylField (ur uz : ℝ → ℝ → ℝ) (x : R3)
    (hur : DiffAt2 ur (radial x) (axial x)) (huz : DiffAt2 uz (radial x) (axial x))
    (hr : 0 < radial x) :
    FiniteTimeSingularity.div (cylField ur uz) x =
      pdR ur (radial x) (axial x) + ur (radial x) (axial x) / radial x
        + pdZ uz (radial x) (axial x) := by
  have hrne : radial x ≠ 0 := ne_of_gt hr
  have hd := differentiableAt_cylField ur uz x hur huz hr
  rw [div_eq_sum_partials _ _ hd, Fin.sum_univ_three]
  change pd 0 (fun y => (cylField ur uz y) 0) x + pd 1 (fun y => (cylField ur uz y) 1) x
    + pd 2 (fun y => (cylField ur uz y) 2) x = _
  rw [pd_cylField_00 ur uz x hur hr, pd_cylField_11 ur uz x hur hr, pd_cylField_22 ur uz x huz hr,
    pdR_redR hur hrne]
  simp only [redR]
  have h2 : x 0 ^ 2 + x 1 ^ 2 = radial x ^ 2 := (radial_sq x).symm
  field_simp
  linear_combination
    (pdR ur (radial x) (axial x) * radial x - ur (radial x) (axial x)) * h2

/-! ## The curl of the field -/

theorem vorticity_cylField (ur uz : ℝ → ℝ → ℝ) (x : R3)
    (hur : DiffAt2 ur (radial x) (axial x)) (huz : DiffAt2 uz (radial x) (axial x))
    (hr : 0 < radial x) :
    FiniteTimeSingularity.vorticity (cylField ur uz) x =
      vortTheta ur uz (radial x) (axial x) • eTheta x := by
  have hrne : radial x ≠ 0 := ne_of_gt hr
  have hd := differentiableAt_cylField ur uz x hur huz hr
  rw [vorticity_eq_coordinates]
  refine ext_coord ?_ ?_ ?_
  · show (fderiv ℝ (cylField ur uz) x (basisVec 1)) 2
        - (fderiv ℝ (cylField ur uz) x (basisVec 2)) 1
      = (vortTheta ur uz (radial x) (axial x) • eTheta x) 0
    rw [fderiv_apply_coord (cylField ur uz) x 1 2 hd,
      fderiv_apply_coord (cylField ur uz) x 2 1 hd,
      pd_cylField_12 ur uz x huz hr, pd_cylField_21 ur uz x hur hr, pdZ_redR]
    simp only [vortTheta, eTheta_apply_zero, WithLp.ofLp_smul, Pi.smul_apply, smul_eq_mul, redR]
    field_simp
    nlinarith [radial_sq x]
  · show (fderiv ℝ (cylField ur uz) x (basisVec 2)) 0
        - (fderiv ℝ (cylField ur uz) x (basisVec 0)) 2
      = (vortTheta ur uz (radial x) (axial x) • eTheta x) 1
    rw [fderiv_apply_coord (cylField ur uz) x 2 0 hd,
      fderiv_apply_coord (cylField ur uz) x 0 2 hd,
      pd_cylField_20 ur uz x hur hr, pd_cylField_02 ur uz x huz hr, pdZ_redR]
    simp only [vortTheta, eTheta_apply_one, WithLp.ofLp_smul, Pi.smul_apply, smul_eq_mul, redR]
    field_simp
  · show (fderiv ℝ (cylField ur uz) x (basisVec 0)) 1
        - (fderiv ℝ (cylField ur uz) x (basisVec 1)) 0
      = (vortTheta ur uz (radial x) (axial x) • eTheta x) 2
    rw [fderiv_apply_coord (cylField ur uz) x 0 1 hd,
      fderiv_apply_coord (cylField ur uz) x 1 0 hd,
      pd_cylField_01 ur uz x hur hr, pd_cylField_10 ur uz x hur hr]
    simp only [vortTheta, eTheta_apply_two, WithLp.ofLp_smul, Pi.smul_apply, smul_eq_mul]
    ring

/-- A no-swirl axisymmetric field is divergence free iff its cylindrical divergence formula
`∂_r u_r + u_r/r + ∂_z u_z` vanishes (`div u = (1/r)∂_r(r u_r) + ∂_z u_z`). -/
theorem div_cylField_eq_zero (ur uz : ℝ → ℝ → ℝ) (x : R3)
    (hur : DiffAt2 ur (radial x) (axial x)) (huz : DiffAt2 uz (radial x) (axial x))
    (hr : 0 < radial x) :
    FiniteTimeSingularity.div (cylField ur uz) x = 0 ↔
      pdR ur (radial x) (axial x) + ur (radial x) (axial x) / radial x
        + pdZ uz (radial x) (axial x) = 0 := by
  rw [div_cylField ur uz x hur huz hr]

/-- The pointwise norm of the vorticity of a no-swirl axisymmetric field is the absolute value of
the scalar vorticity `ω^θ = ∂_z u_r - ∂_r u_z`. -/
theorem norm_vorticity_cylField (ur uz : ℝ → ℝ → ℝ) (x : R3)
    (hur : DiffAt2 ur (radial x) (axial x)) (huz : DiffAt2 uz (radial x) (axial x))
    (hr : 0 < radial x) :
    ‖FiniteTimeSingularity.vorticity (cylField ur uz) x‖ =
      |vortTheta ur uz (radial x) (axial x)| := by
  rw [vorticity_cylField ur uz x hur huz hr, norm_smul, Real.norm_eq_abs,
    norm_eTheta x (ne_of_gt hr), mul_one]

end Work.Cyl
