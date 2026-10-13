/-
# Symmetries of `ℝ³` used in the axisymmetry of the Biot–Savart field

This module collects the two families of symmetries of `ℝ³` that are used to prove
`Work.ConstructionInstance.isAxiNoSwirl_biotSavart`, namely

* the rotations `rotLE φ` about the `x₃`-axis by the angle `φ`, and
* the reflection `flip1LE` flipping the second coordinate `x₁ ↦ -x₁`,

together with their coordinate computations (cross-product compatibility, preservation of the
cylindrical frame `e_θ`, and the equivariance of the cylindrical coordinates).

These are pure linear-algebra/trigonometric facts; the analytic content (the equivariance of the
Biot–Savart integral) is in the sibling files.
-/
import Mathlib.Algebra.Order.Star.Real
import Mathlib.Analysis.CStarAlgebra.Classes
import Mathlib.Analysis.InnerProductSpace.PiL2
import Mathlib.LinearAlgebra.CrossProduct
import Submission.Work.ConstructionInstance.Defs

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

noncomputable section
open scoped Matrix

namespace Work.ConstructionInstance

/-! ## The rotation about the symmetry axis -/

/-- The coordinate action of the rotation about the `x₃`-axis by the angle `φ`,
`(v₀,v₁,v₂) ↦ (cos φ · v₀ - sin φ · v₁, sin φ · v₀ + cos φ · v₁, v₂)`. -/
def rotCoord (φ : ℝ) : (Fin 3 → ℝ) → (Fin 3 → ℝ) :=
  fun v => ![Real.cos φ * v 0 - Real.sin φ * v 1,
              Real.sin φ * v 0 + Real.cos φ * v 1,
              v 2]

@[simp] lemma rotCoord_apply_zero (φ : ℝ) (v : Fin 3 → ℝ) :
    rotCoord φ v 0 = Real.cos φ * v 0 - Real.sin φ * v 1 := rfl
@[simp] lemma rotCoord_apply_one (φ : ℝ) (v : Fin 3 → ℝ) :
    rotCoord φ v 1 = Real.sin φ * v 0 + Real.cos φ * v 1 := rfl
@[simp] lemma rotCoord_apply_two (φ : ℝ) (v : Fin 3 → ℝ) : rotCoord φ v 2 = v 2 := rfl

lemma rotCoord_add (φ : ℝ) (a b : Fin 3 → ℝ) :
    rotCoord φ (a + b) = rotCoord φ a + rotCoord φ b := by
  funext i
  fin_cases i <;> simp [rotCoord] <;> ring

lemma rotCoord_smul (φ : ℝ) (c : ℝ) (a : Fin 3 → ℝ) :
    rotCoord φ (c • a) = c • rotCoord φ a := by
  funext i
  fin_cases i <;> simp [rotCoord] <;> ring

lemma rotCoord_neg_comp (φ : ℝ) (v : Fin 3 → ℝ) : rotCoord (-φ) (rotCoord φ v) = v := by
  funext i
  fin_cases i
  · show rotCoord (-φ) (rotCoord φ v) 0 = v 0
    simp only [rotCoord_apply_zero, rotCoord_apply_one, Real.cos_neg, Real.sin_neg]
    ring_nf
    linear_combination (v 0) * Real.cos_sq_add_sin_sq φ
  · show rotCoord (-φ) (rotCoord φ v) 1 = v 1
    simp only [rotCoord_apply_zero, rotCoord_apply_one, Real.cos_neg, Real.sin_neg]
    ring_nf
    linear_combination (v 1) * Real.cos_sq_add_sin_sq φ
  · show rotCoord (-φ) (rotCoord φ v) 2 = v 2
    simp [rotCoord]

lemma rotCoord_comp_neg (φ : ℝ) (v : Fin 3 → ℝ) : rotCoord φ (rotCoord (-φ) v) = v := by
  simpa using rotCoord_neg_comp (-φ) v

/-- The rotation preserves the Euclidean norm. -/
lemma rotCoord_norm (φ : ℝ) (v : Fin 3 → ℝ) :
    ‖(WithLp.toLp 2 (rotCoord φ v) : R3)‖ = ‖(WithLp.toLp 2 v : R3)‖ := by
  have h : ‖(WithLp.toLp 2 (rotCoord φ v) : R3)‖ ^ 2
      = ‖(WithLp.toLp 2 v : R3)‖ ^ 2 := by
    rw [EuclideanSpace.real_norm_sq_eq, EuclideanSpace.real_norm_sq_eq]
    rw [Fin.sum_univ_three, Fin.sum_univ_three]
    simp [rotCoord]
    ring_nf
    linear_combination (v 0 ^ 2 + v 1 ^ 2) * Real.cos_sq_add_sin_sq φ
  nlinarith [norm_nonneg (WithLp.toLp 2 (rotCoord φ v) : R3),
    norm_nonneg (WithLp.toLp 2 v : R3)]

/-- The rotation is compatible with the cross product. -/
lemma rotCoord_cross (φ : ℝ) (a b : Fin 3 → ℝ) :
    rotCoord φ a ⨯₃ rotCoord φ b = rotCoord φ (a ⨯₃ b) := by
  funext i
  fin_cases i <;> simp [rotCoord, cross_apply]
  · ring
  · ring
  · ring_nf
    linear_combination (a 0 * b 1 - a 1 * b 0) * Real.cos_sq_add_sin_sq φ

/-- The rotation about the `x₃`-axis by the angle `φ`, as a linear isometry equivalence of `ℝ³`. -/
noncomputable def rotLE (φ : ℝ) : R3 ≃ₗᵢ[ℝ] R3 where
  toFun x := WithLp.toLp 2 (rotCoord φ x.ofLp)
  invFun x := WithLp.toLp 2 (rotCoord (-φ) x.ofLp)
  left_inv x := by
    show WithLp.toLp 2 (rotCoord (-φ) (rotCoord φ x.ofLp)) = x
    rw [rotCoord_neg_comp, WithLp.toLp_ofLp]
  right_inv x := by
    show WithLp.toLp 2 (rotCoord φ (rotCoord (-φ) x.ofLp)) = x
    rw [rotCoord_comp_neg, WithLp.toLp_ofLp]
  map_add' x y := by
    show WithLp.toLp 2 (rotCoord φ (x + y).ofLp) = WithLp.toLp 2 (rotCoord φ x.ofLp)
      + WithLp.toLp 2 (rotCoord φ y.ofLp)
    rw [WithLp.ofLp_add, ← WithLp.toLp_add, rotCoord_add]
  map_smul' c x := by
    show WithLp.toLp 2 (rotCoord φ (c • x).ofLp) = c • WithLp.toLp 2 (rotCoord φ x.ofLp)
    rw [WithLp.ofLp_smul, ← WithLp.toLp_smul, rotCoord_smul]
  norm_map' x := by
    show ‖WithLp.toLp 2 (rotCoord φ x.ofLp)‖ = ‖x‖
    rw [rotCoord_norm, WithLp.toLp_ofLp]

@[simp] lemma rotLE_apply (φ : ℝ) (x : R3) :
    rotLE φ x = WithLp.toLp 2 (rotCoord φ x.ofLp) := rfl

@[simp] lemma rotLE_symm_apply (φ : ℝ) (x : R3) :
    (rotLE φ).symm x = WithLp.toLp 2 (rotCoord (-φ) x.ofLp) := rfl

@[simp] lemma rotLE_ofLp (φ : ℝ) (x : R3) : (rotLE φ x).ofLp = rotCoord φ x.ofLp := by
  rw [rotLE_apply, WithLp.ofLp_toLp]



/-! ## The rotation and the cylindrical frame -/

lemma radSq_rotLE (φ : ℝ) (x : R3) :
    Work.Cyl.radSq (rotLE φ x) = Work.Cyl.radSq x := by
  simp only [Work.Cyl.radSq, rotLE_apply, PiLp.toLp_apply, rotCoord_apply_zero,
    rotCoord_apply_one]
  ring_nf
  linear_combination ((x.ofLp 0) ^ 2 + (x.ofLp 1) ^ 2) * Real.cos_sq_add_sin_sq φ

lemma radial_rotLE (φ : ℝ) (x : R3) :
    Work.Cyl.radial (rotLE φ x) = Work.Cyl.radial x := by
  simp only [Work.Cyl.radial, radSq_rotLE]

lemma axial_rotLE (φ : ℝ) (x : R3) :
    Work.Cyl.axial (rotLE φ x) = Work.Cyl.axial x := by
  simp [Work.Cyl.axial, rotLE_apply, rotCoord]

lemma angularVec_rotLE (φ : ℝ) (x : R3) :
    Work.Cyl.angularVec (rotLE φ x) = rotLE φ (Work.Cyl.angularVec x) := by
  ext i
  fin_cases i <;>
    simp [Work.Cyl.angularVec, rotLE_apply, rotCoord] <;>
    ring

lemma eTheta_rotLE (φ : ℝ) (x : R3) :
    Work.Cyl.eTheta (rotLE φ x) = rotLE φ (Work.Cyl.eTheta x) := by
  rw [Work.Cyl.eTheta, Work.Cyl.eTheta, radial_rotLE, angularVec_rotLE]
  exact (map_smul (rotLE φ) (1 / Work.Cyl.radial x) (Work.Cyl.angularVec x)).symm

/-! ## The reflection `x ↦ (x₀, -x₁, x₃)` -/

/-- The reflection `x ↦ (x₀, -x₁, x₃)` of `ℝ³`. -/
def flip1 (x : R3) : R3 := !₂[x 0, - x 1, x 2]

@[simp] lemma flip1_zero (x : R3) : (flip1 x) 0 = x 0 := by simp [flip1]
@[simp] lemma flip1_one (x : R3) : (flip1 x) 1 = - x 1 := by simp [flip1]
@[simp] lemma flip1_two (x : R3) : (flip1 x) 2 = x 2 := by simp [flip1]

lemma flip1_add (a b : R3) : flip1 (a + b) = flip1 a + flip1 b := by
  ext i
  fin_cases i <;> simp [flip1] <;> ring

lemma flip1_smul (c : ℝ) (a : R3) : flip1 (c • a) = c • flip1 a := by
  ext i
  fin_cases i <;> simp [flip1]

lemma flip1_flip1 (v : R3) : flip1 (flip1 v) = v := by
  ext i
  fin_cases i <;> simp [flip1]

lemma flip1_norm (x : R3) : ‖flip1 x‖ = ‖x‖ := by
  rw [EuclideanSpace.norm_eq, EuclideanSpace.norm_eq]
  congr 1
  rw [Fin.sum_univ_three, Fin.sum_univ_three]
  simp [flip1]

/-- The reflection `x ↦ (x₀, -x₁, x₃)`, as a linear isometry equivalence of `ℝ³`. -/
noncomputable def flip1LE : R3 ≃ₗᵢ[ℝ] R3 where
  toFun := flip1
  invFun := flip1
  left_inv := flip1_flip1
  right_inv := flip1_flip1
  map_add' := flip1_add
  map_smul' := flip1_smul
  norm_map' := flip1_norm

@[simp] lemma flip1LE_apply (v : R3) : flip1LE v = flip1 v := rfl
@[simp] lemma flip1LE_symm : (flip1LE : R3 ≃ₗᵢ[ℝ] R3).symm = flip1LE := rfl

/-- The coordinate action of `flip1`. -/
def flip1Coord : (Fin 3 → ℝ) → (Fin 3 → ℝ) := fun v => ![v 0, - v 1, v 2]

@[simp] lemma flip1Coord_zero (v : Fin 3 → ℝ) : flip1Coord v 0 = v 0 := rfl
@[simp] lemma flip1Coord_one (v : Fin 3 → ℝ) : flip1Coord v 1 = - v 1 := rfl
@[simp] lemma flip1Coord_two (v : Fin 3 → ℝ) : flip1Coord v 2 = v 2 := rfl

lemma flip1Coord_smul (c : ℝ) (a : Fin 3 → ℝ) : flip1Coord (c • a) = c • flip1Coord a := by
  funext i
  fin_cases i <;> simp [flip1Coord]

lemma flip1Coord_add (a b : Fin 3 → ℝ) : flip1Coord (a + b) = flip1Coord a + flip1Coord b := by
  funext i
  fin_cases i <;> simp [flip1Coord] <;> ring

@[simp] lemma flip1_ofLp (x : R3) : (flip1 x).ofLp = flip1Coord x.ofLp := rfl

lemma flip1Coord_sub (a b : Fin 3 → ℝ) :
    flip1Coord (a - b) = flip1Coord a - flip1Coord b := by
  funext i
  fin_cases i <;> simp [flip1Coord] <;> ring

/-- `flip1` reverses the cross product. -/
lemma flip1Coord_cross (a b : Fin 3 → ℝ) :
    flip1Coord a ⨯₃ flip1Coord b = - flip1Coord (a ⨯₃ b) := by
  funext i
  fin_cases i <;> simp [flip1Coord, cross_apply] <;> ring

/-! ## An angle with prescribed cosine and sine -/

/-! ## Components of `rotLE` -/

@[simp] lemma rotLE_apply_zero (φ : ℝ) (x : R3) :
    (rotLE φ x) 0 = Real.cos φ * x 0 - Real.sin φ * x 1 := by
  simp [rotLE_apply, rotCoord]

@[simp] lemma rotLE_apply_one (φ : ℝ) (x : R3) :
    (rotLE φ x) 1 = Real.sin φ * x 0 + Real.cos φ * x 1 := by
  simp [rotLE_apply, rotCoord]

@[simp] lemma rotLE_apply_two (φ : ℝ) (x : R3) : (rotLE φ x) 2 = x 2 := by
  simp [rotLE_apply, rotCoord]

@[simp] lemma rotLE_zero_apply (x : R3) : rotLE 0 x = x := by
  ext i; fin_cases i <;> simp [rotLE_apply, rotCoord]

/-! ## The reflection and the cylindrical frame -/

lemma radial_flip1 (x : R3) : Work.Cyl.radial (flip1 x) = Work.Cyl.radial x := by
  simp only [Work.Cyl.radial, Work.Cyl.radSq, flip1_zero, flip1_one]
  ring_nf

lemma axial_flip1 (x : R3) : Work.Cyl.axial (flip1 x) = Work.Cyl.axial x := by
  simp [Work.Cyl.axial, flip1]

lemma angularVec_flip1 (x : R3) :
    Work.Cyl.angularVec (flip1 x) = - flip1 (Work.Cyl.angularVec x) := by
  ext i
  fin_cases i <;> simp [Work.Cyl.angularVec, flip1]

lemma eTheta_flip1 (x : R3) :
    Work.Cyl.eTheta (flip1 x) = - flip1 (Work.Cyl.eTheta x) := by
  rw [Work.Cyl.eTheta, Work.Cyl.eTheta, radial_flip1, angularVec_flip1, flip1_smul, smul_neg]

/-! ## The vorticity profile is equivariant -/

lemma omega_rotLE {ω : R3 → R3} {f : ℝ → ℝ → ℝ}
    (hω : ∀ x : R3, ω x = f (Work.Cyl.radial x) (Work.Cyl.axial x) • Work.Cyl.eTheta x)
    (φ : ℝ) (x : R3) : ω (rotLE φ x) = rotLE φ (ω x) := by
  rw [hω (rotLE φ x), hω x, radial_rotLE, axial_rotLE, eTheta_rotLE, map_smul]

lemma omega_flip1 {ω : R3 → R3} {f : ℝ → ℝ → ℝ}
    (hω : ∀ x : R3, ω x = f (Work.Cyl.radial x) (Work.Cyl.axial x) • Work.Cyl.eTheta x)
    (x : R3) : ω (flip1 x) = - flip1 (ω x) := by
  rw [hω (flip1 x), hω x, radial_flip1, axial_flip1, eTheta_flip1, flip1_smul, smul_neg]

/-! ## No-swirl axisymmetry from the rotation and reflection symmetries -/

/-- **A field equivariant under all rotations about the `x₃`-axis and invariant under the
reflection `x ↦ (x₀,-x₁,x₃)` is axisymmetric without swirl.**

Writing `B(x) = !₂[r(x), 0, x₃(x)]` for the point of the meridian `θ = 0` with the same `(ρ,x₃)`,
the profiles are `u_r(r,z) = (u B)₀` and `u_z(r,z) = (u B)₂`: the reflection identity kills the
second component of `u B` (`hbase1`), the rotation by `π` kills the first one on the axis
(`h0`), and on `r > 0` the rotation equivariance transports the meridian value to `x`. -/
theorem isAxiNoSwirl_of_rot_flip (u : R3 → R3)
    (hrot : ∀ (φ : ℝ) (x : R3), u (rotLE φ x) = rotLE φ (u x))
    (hflip : ∀ x : R3, u (flip1 x) = flip1 (u x))
    (hsurj : ∀ x : R3, 0 < Work.Cyl.radial x →
      ∃ φ : ℝ, rotLE φ !₂[Work.Cyl.radial x, 0, Work.Cyl.axial x] = x) :
    Work.Cyl.IsAxiNoSwirl u := by
  refine ⟨fun r z => u !₂[r, 0, z] 0, fun r z => u !₂[r, 0, z] 2, ?_⟩
  funext x
  have hbase1 : (u !₂[Work.Cyl.radial x, 0, Work.Cyl.axial x]) 1 = 0 := by
    have hflipB : flip1 (!₂[Work.Cyl.radial x, 0, Work.Cyl.axial x] : R3)
        = !₂[Work.Cyl.radial x, 0, Work.Cyl.axial x] := by
      ext i; fin_cases i <;> simp [flip1]
    have h := hflip (!₂[Work.Cyl.radial x, 0, Work.Cyl.axial x] : R3)
    rw [hflipB] at h
    have h' := congrArg (fun v : R3 => v 1) h
    have h2 : (u !₂[Work.Cyl.radial x, 0, Work.Cyl.axial x]) 1
        = - (u !₂[Work.Cyl.radial x, 0, Work.Cyl.axial x]) 1 := by
      simpa [flip1] using h'
    linarith
  by_cases hr : Work.Cyl.radial x = 0
  · have hx01 := (Work.Cyl.radial_eq_zero_iff x).mp hr
    have hx0 : x 0 = 0 := hx01.1
    have hx1 : x 1 = 0 := hx01.2
    have hfixπ : rotLE Real.pi x = x := by
      ext i; fin_cases i <;> simp [hx0, hx1]
    have h0 : (u x) 0 = 0 := by
      have h := hrot Real.pi x
      rw [hfixπ] at h
      have h' := congrArg (fun v : R3 => v 0) h
      have h2 : (u x) 0 = - (u x) 0 := by simpa [rotLE_apply_zero] using h'
      linarith
    have h1 : (u x) 1 = 0 := by
      have hflipx : flip1 x = x := by
        ext i; fin_cases i <;> simp [flip1, hx1]
      have h := hflip x
      rw [hflipx] at h
      have h' := congrArg (fun v : R3 => v 1) h
      have h2 : (u x) 1 = - (u x) 1 := by simpa [flip1] using h'
      linarith
    have hxeq : x = !₂[Work.Cyl.radial x, 0, Work.Cyl.axial x] := by
      ext i; fin_cases i <;> simp [hx0, hx1, hr, Work.Cyl.axial]
    have hxB : (u x) 2 = (u !₂[Work.Cyl.radial x, 0, Work.Cyl.axial x]) 2 :=
      congrArg (fun v : R3 => (u v) 2) hxeq
    have hc0 : (u x) 0 = (Work.Cyl.cylField (fun r z => u !₂[r, 0, z] 0)
        (fun r z => u !₂[r, 0, z] 2) x) 0 := by
      rw [Work.Cyl.cylField_zero, h0, hr]; simp
    have hc1 : (u x) 1 = (Work.Cyl.cylField (fun r z => u !₂[r, 0, z] 0)
        (fun r z => u !₂[r, 0, z] 2) x) 1 := by
      rw [Work.Cyl.cylField_one, h1, hr]; simp
    have hc2 : (u x) 2 = (Work.Cyl.cylField (fun r z => u !₂[r, 0, z] 0)
        (fun r z => u !₂[r, 0, z] 2) x) 2 := by
      rw [Work.Cyl.cylField_two]; exact hxB
    ext i; fin_cases i
    · exact hc0
    · exact hc1
    · exact hc2
  · have hrpos : 0 < Work.Cyl.radial x :=
      lt_of_le_of_ne (Work.Cyl.radial_nonneg x) (Ne.symm hr)
    obtain ⟨φ, hφ⟩ := hsurj x hrpos
    have hux : u x = rotLE φ (u !₂[Work.Cyl.radial x, 0, Work.Cyl.axial x]) := by
      have h := hrot φ (!₂[Work.Cyl.radial x, 0, Work.Cyl.axial x] : R3)
      rwa [hφ] at h
    have hx0 : Real.cos φ * Work.Cyl.radial x = x 0 := by
      have h := congrArg (fun v : R3 => v 0) hφ
      simpa [rotLE_apply_zero] using h
    have hx1 : Real.sin φ * Work.Cyl.radial x = x 1 := by
      have h := congrArg (fun v : R3 => v 1) hφ
      simpa [rotLE_apply_one] using h
    have hc0 : (u x) 0 = (Work.Cyl.cylField (fun r z => u !₂[r, 0, z] 0)
        (fun r z => u !₂[r, 0, z] 2) x) 0 := by
      rw [Work.Cyl.cylField_zero, hux, rotLE_apply_zero, hbase1, mul_zero, sub_zero, ← hx0]
      try field_simp
      try ring
    have hc1 : (u x) 1 = (Work.Cyl.cylField (fun r z => u !₂[r, 0, z] 0)
        (fun r z => u !₂[r, 0, z] 2) x) 1 := by
      rw [Work.Cyl.cylField_one, hux, rotLE_apply_one, hbase1, mul_zero, add_zero, ← hx1]
      try field_simp
      try ring
    have hc2 : (u x) 2 = (Work.Cyl.cylField (fun r z => u !₂[r, 0, z] 0)
        (fun r z => u !₂[r, 0, z] 2) x) 2 := by
      rw [Work.Cyl.cylField_two, hux, rotLE_apply_two]
    ext i; fin_cases i
    · exact hc0
    · exact hc1
    · exact hc2

/-- Given `a² + b² = 1` there is `φ` with `cos φ = a` and `sin φ = b`. -/
lemma exists_cos_sin {a b : ℝ} (h : a ^ 2 + b ^ 2 = 1) :
    ∃ φ : ℝ, Real.cos φ = a ∧ Real.sin φ = b := by
  set z : ℂ := (a : ℂ) + b * Complex.I with hz
  have hnormSq : Complex.normSq z = 1 := by
    rw [hz, Complex.normSq_apply]
    simp
    nlinarith [h]
  have hnorm : ‖z‖ = 1 := by
    have h2 : ‖z‖ ^ 2 = 1 := by rw [← Complex.normSq_eq_norm_sq]; exact hnormSq
    nlinarith [norm_nonneg z]
  have hz0 : z ≠ 0 := by
    intro h0
    rw [h0] at hnorm
    simp at hnorm
  refine ⟨z.arg, ?_, ?_⟩
  · rw [Complex.cos_arg hz0, hnorm, hz]; simp
  · rw [Complex.sin_arg, hnorm, hz]; simp

end Work.ConstructionInstance
