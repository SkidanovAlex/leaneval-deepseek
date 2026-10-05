import Mathlib
import ChallengeDeps

open scoped Real

set_option autoImplicit false
noncomputable section

namespace Work.RPB.Port.Geometry

/-! # Part B: Euclidean plane geometry bridge

We develop the Euclidean geometry of `ℝ × ℝ` (Euclidean norm / dot product, written
explicitly with coordinates, since the default norm on `ℝ × ℝ` is the sup norm) needed to
turn the "two chords with a common midpoint, equal length and directions whose (acute) angle
is `θ/2`" data produced by the configuration map into an inscribed rectangle of aspect ratio
`tan (θ/4)`.
-/

/-- Euclidean dot product of two points of `ℝ × ℝ`. -/
def eucDot (x y : ℝ × ℝ) : ℝ := x.1 * y.1 + x.2 * y.2

/-- Euclidean norm of a point of `ℝ × ℝ`. -/
def eucNorm (x : ℝ × ℝ) : ℝ := Real.sqrt (eucDot x x)

@[simp] lemma eucDot_mk (a b c d : ℝ) : eucDot (a, b) (c, d) = a * c + b * d := rfl

@[simp] lemma eucDot_self (x : ℝ × ℝ) : eucDot x x = x.1 ^ 2 + x.2 ^ 2 := by
  simp [eucDot, pow_two]

lemma eucDot_comm (x y : ℝ × ℝ) : eucDot x y = eucDot y x := by
  simp [eucDot, mul_comm]

lemma eucDot_add_left (x y z : ℝ × ℝ) : eucDot (x + y) z = eucDot x z + eucDot y z := by
  simp [eucDot]; ring

lemma eucDot_smul_left (a : ℝ) (x y : ℝ × ℝ) : eucDot (a • x) y = a * eucDot x y := by
  simp [eucDot]; ring

lemma eucDot_self_nonneg (x : ℝ × ℝ) : 0 ≤ eucDot x x := by
  simp; positivity

lemma eucNorm_sq (x : ℝ × ℝ) : eucNorm x ^ 2 = eucDot x x := by
  unfold eucNorm
  rw [Real.sq_sqrt (eucDot_self_nonneg x)]

lemma eucNorm_nonneg (x : ℝ × ℝ) : 0 ≤ eucNorm x := by
  unfold eucNorm
  exact Real.sqrt_nonneg _

lemma eucNorm_eq_zero {x : ℝ × ℝ} : eucNorm x = 0 ↔ x = 0 := by
  constructor
  · intro h
    have hsq := congrArg (fun t : ℝ => t ^ 2) h
    rw [eucNorm_sq, eucDot_self] at hsq
    have hx1 : x.1 ^ 2 = 0 := by nlinarith [sq_nonneg x.1, sq_nonneg x.2]
    have hx2 : x.2 ^ 2 = 0 := by nlinarith [sq_nonneg x.1, sq_nonneg x.2]
    have hx1' : x.1 = 0 := (sq_eq_zero_iff.mp hx1)
    have hx2' : x.2 = 0 := (sq_eq_zero_iff.mp hx2)
    ext <;> simp [hx1', hx2']
  · intro h
    rw [h]
    simp [eucNorm, eucDot]

lemma eucNorm_pos {x : ℝ × ℝ} (hx : x ≠ 0) : 0 < eucNorm x := by
  by_contra h
  have : eucNorm x = 0 := le_antisymm (not_lt.mp h) (eucNorm_nonneg x)
  exact hx (eucNorm_eq_zero.mp this)

lemma eucNorm_eq_of_sq_eq {x y : ℝ × ℝ} (h : eucNorm x ^ 2 = eucNorm y ^ 2) : eucNorm x = eucNorm y := by
  have habs : |eucNorm x| = |eucNorm y| := (sq_eq_sq_iff_abs_eq_abs _ _).mp h
  rwa [abs_of_nonneg (eucNorm_nonneg x), abs_of_nonneg (eucNorm_nonneg y)] at habs

-- rotation in coordinates (E = ℝ in the Fernique definition)
lemma rot_apply (θ : ℝ) (x : ℝ × ℝ) :
    ContinuousLinearMap.rotation θ x =
      (Real.cos θ * x.1 + Real.sin θ * x.2, -(Real.sin θ) * x.1 + Real.cos θ * x.2) := by
  rw [ContinuousLinearMap.rotation_apply]
  simp

lemma rot_pres_eucDot (θ : ℝ) (x y : ℝ × ℝ) :
    eucDot (ContinuousLinearMap.rotation θ x) (ContinuousLinearMap.rotation θ y) = eucDot x y := by
  rw [rot_apply, rot_apply]
  rcases x with ⟨x1, x2⟩; rcases y with ⟨y1, y2⟩
  simp only [eucDot_mk]
  ring_nf
  have hc2 : Real.cos θ ^ 2 = 1 - Real.sin θ ^ 2 := by
    nlinarith [Real.cos_sq_add_sin_sq θ]
  rw [hc2]
  ring

lemma rot_pres_eucNorm (θ : ℝ) (x : ℝ × ℝ) :
    eucNorm (ContinuousLinearMap.rotation θ x) = eucNorm x := by
  apply eucNorm_eq_of_sq_eq
  rw [eucNorm_sq, eucNorm_sq]
  exact rot_pres_eucDot θ x x

lemma rot_add (θ : ℝ) (x y : ℝ × ℝ) :
    ContinuousLinearMap.rotation θ (x + y) = ContinuousLinearMap.rotation θ x +
      ContinuousLinearMap.rotation θ y := by
  ext <;> simp [rot_apply] <;> ring

lemma rot_smul (θ a : ℝ) (x : ℝ × ℝ) :
    ContinuousLinearMap.rotation θ (a • x) = a • ContinuousLinearMap.rotation θ x := by
  ext <;> simp [rot_apply]

lemma rot_sub (θ : ℝ) (x y : ℝ × ℝ) :
    ContinuousLinearMap.rotation θ (x - y) = ContinuousLinearMap.rotation θ x -
      ContinuousLinearMap.rotation θ y := by
  rw [sub_eq_add_neg, rot_add]
  have hneg : ContinuousLinearMap.rotation θ (-y) = - ContinuousLinearMap.rotation θ y := by
    simpa using rot_smul θ (-1 : ℝ) y
  rw [hneg]
  ring

-- rotation by (-θ) after rotation by θ is the identity (so rotation is injective)
lemma rot_neg_comp (θ : ℝ) (x : ℝ × ℝ) :
    ContinuousLinearMap.rotation (-θ) (ContinuousLinearMap.rotation θ x) = x := by
  rw [rot_apply, rot_apply]
  rcases x with ⟨x1, x2⟩
  simp only [Real.cos_neg, Real.sin_neg]
  ring_nf
  have hc2 : Real.cos θ ^ 2 = 1 - Real.sin θ ^ 2 := by
    nlinarith [Real.cos_sq_add_sin_sq θ]
  rw [hc2]
  ring

lemma rot_injective (θ : ℝ) : Function.Injective (ContinuousLinearMap.rotation (E := ℝ) θ) := by
  intro x y h
  apply_fun (fun z : ℝ × ℝ => ContinuousLinearMap.rotation (-θ) z) at h
  rw [rot_neg_comp θ x, rot_neg_comp θ y] at h
  exact h

lemma rot_inj_iff {θ : ℝ} {x y : ℝ × ℝ} :
    ContinuousLinearMap.rotation θ x = ContinuousLinearMap.rotation θ y ↔ x = y :=
  (rot_injective θ).eq_iff

section B2

/-- The unit direction vector at angle `φ`. -/
def uv (φ : ℝ) : ℝ × ℝ := (Real.cos φ, Real.sin φ)

/-- Counter-clockwise quarter-turn. -/
def perp (x : ℝ × ℝ) : ℝ × ℝ := (-x.2, x.1)

@[simp] lemma uv_mk (φ : ℝ) : uv φ = (Real.cos φ, Real.sin φ) := rfl

@[simp] lemma perp_mk (x : ℝ × ℝ) : perp x = (-x.2, x.1) := rfl

lemma perp_perp (x : ℝ × ℝ) : perp (perp x) = -x := by
  rcases x with ⟨x1, x2⟩
  ext <;> simp [perp] <;> ring

lemma uv_perp (φ : ℝ) : perp (uv φ) = (-Real.sin φ, Real.cos φ) := by
  simp [uv, perp]

lemma eucDot_perp (u v : ℝ × ℝ) : eucDot (perp u) (perp v) = eucDot u v := by
  rcases u with ⟨x, y⟩; rcases v with ⟨a, b⟩
  simp [eucDot, perp]; ring

lemma eucNorm_perp (u : ℝ × ℝ) : eucNorm (perp u) = eucNorm u := by
  apply eucNorm_eq_of_sq_eq
  rw [eucNorm_sq, eucNorm_sq, eucDot_perp]

lemma uv_decomp_add (ψ δ : ℝ) :
    uv (ψ + δ) = Real.cos δ • uv ψ + Real.sin δ • perp (uv ψ) := by
  ext <;> simp [uv, perp] <;> (first | rw [Real.cos_add] | rw [Real.sin_add]) <;> ring

lemma uv_decomp_sub (ψ δ : ℝ) :
    uv (ψ - δ) = Real.cos δ • uv ψ - Real.sin δ • perp (uv ψ) := by
  ext <;> simp [uv, perp] <;> (first | rw [Real.cos_sub] | rw [Real.sin_sub]) <;> ring

lemma eucNorm_uv (φ : ℝ) : eucNorm (uv φ) = 1 := by
  unfold eucNorm
  rw [eucDot_self]
  simp [uv, Real.cos_sq_add_sin_sq φ]

lemma cos_neg_sub_pi_div_two (ψ : ℝ) : Real.cos (-ψ - π / 2) = -Real.sin ψ := by
  rw [Real.cos_sub]; simp

lemma sin_neg_sub_pi_div_two (ψ : ℝ) : Real.sin (-ψ - π / 2) = -Real.cos ψ := by
  rw [Real.sin_sub]; simp

-- The rotation by `-ψ - π/2` maps the axes to the `perp (uv ψ)`, `-uv ψ` frame.
lemma rot_frame_e1 (ψ : ℝ) :
    ContinuousLinearMap.rotation (-ψ - π / 2) (1, 0) = perp (uv ψ) := by
  rw [ContinuousLinearMap.rotation_apply]
  rw [cos_neg_sub_pi_div_two, sin_neg_sub_pi_div_two]
  simp [uv, perp, smul_eq_mul]

lemma rot_frame_e2 (ψ : ℝ) :
    ContinuousLinearMap.rotation (-ψ - π / 2) (0, 1) = -uv ψ := by
  rw [ContinuousLinearMap.rotation_apply]
  rw [cos_neg_sub_pi_div_two, sin_neg_sub_pi_div_two]
  simp [uv, perp, smul_eq_mul]

-- decomposing a point as a linear combination of the standard basis
lemma pair_eq_basis (s t : ℝ) : (s, t) = s • ((1 : ℝ), (0 : ℝ)) + t • ((0 : ℝ), (1 : ℝ)) := by
  ext <;> simp [smul_eq_mul]

-- half-side extents of the axis aligned preimage rectangle: x-direction short, y-direction long
def halfShort (c θ : ℝ) : ℝ := c * Real.sin (θ / 4)
def halfLong (c θ : ℝ) : ℝ := c * Real.cos (θ / 4)

-- the rotation angle that turns the x-axis into the short side direction
def rectRot (φ θ : ℝ) : ℝ := θ / 4 - φ - π / 2

lemma rectRot_eq (φ θ : ℝ) : rectRot φ θ = -(φ - θ / 4) - π / 2 := by
  unfold rectRot
  ring

lemma rot_e1_rect (φ θ : ℝ) :
    ContinuousLinearMap.rotation (rectRot φ θ) (1, 0) = perp (uv (φ - θ / 4)) := by
  rw [rectRot_eq]
  exact rot_frame_e1 (φ - θ / 4)

lemma rot_e2_rect (φ θ : ℝ) :
    ContinuousLinearMap.rotation (rectRot φ θ) (0, 1) = -uv (φ - θ / 4) := by
  rw [rectRot_eq]
  exact rot_frame_e2 (φ - θ / 4)

-- sin and cos of θ/4 in [0, π/4]
lemma sin_quarter_nonneg {θ : ℝ} (hθ0 : 0 ≤ θ) (hθπ : θ ≤ π) : 0 ≤ Real.sin (θ / 4) := by
  have h1 : 0 ≤ θ / 4 := by positivity
  have h2 : θ / 4 ≤ Real.pi := by
    have h2a : θ / 4 ≤ Real.pi / 4 := div_le_div_of_nonneg_right hθπ (by norm_num : (0 : ℝ) ≤ 4)
    have hpi : 0 < Real.pi := Real.pi_pos
    linarith
  exact Real.sin_nonneg_of_mem_Icc ⟨h1, h2⟩

lemma cos_quarter_pos {θ : ℝ} (hθ0 : 0 ≤ θ) (hθπ : θ ≤ π) : 0 < Real.cos (θ / 4) := by
  have h1 : -(Real.pi / 2) < θ / 4 := by
    have hpi : 0 < Real.pi := Real.pi_pos
    nlinarith
  have h2 : θ / 4 < Real.pi / 2 := by
    have h2a : θ / 4 ≤ Real.pi / 4 := div_le_div_of_nonneg_right hθπ (by norm_num : (0 : ℝ) ≤ 4)
    have hpi : 0 < Real.pi := Real.pi_pos
    linarith
  exact Real.cos_pos_of_mem_Ioo ⟨h1, h2⟩

lemma halfShort_nonneg {c θ : ℝ} (hc : 0 < c) (hθ0 : 0 ≤ θ) (hθπ : θ ≤ π) :
    0 ≤ halfShort c θ := by
  unfold halfShort
  exact mul_nonneg hc.le (sin_quarter_nonneg hθ0 hθπ)

lemma halfShort_pos {c θ : ℝ} (hc : 0 < c) (hθ0 : 0 < θ) (hθπ : θ ≤ π) :
    0 < halfShort c θ := by
  unfold halfShort
  exact mul_pos hc (Real.sin_pos_of_pos_of_lt_pi (by linarith : 0 < θ / 4) (by linarith : θ / 4 < Real.pi))

lemma halfLong_pos {c θ : ℝ} (hc : 0 < c) (hθ0 : 0 ≤ θ) (hθπ : θ ≤ π) :
    0 < halfLong c θ := by
  unfold halfLong
  exact mul_pos hc (cos_quarter_pos hθ0 hθπ)

lemma rot_neg_comp' (α : ℝ) (x : ℝ × ℝ) :
    ContinuousLinearMap.rotation α (ContinuousLinearMap.rotation (-α) x) = x := by
  simpa using rot_neg_comp (-α) x

lemma rot_lincomb (θ s t : ℝ) :
    ContinuousLinearMap.rotation θ (s • ((1 : ℝ), (0 : ℝ)) + t • ((0 : ℝ), (1 : ℝ))) =
      s • ContinuousLinearMap.rotation θ ((1 : ℝ), (0 : ℝ)) +
        t • ContinuousLinearMap.rotation θ ((0 : ℝ), (1 : ℝ)) := by
  rw [rot_add, rot_smul, rot_smul]

lemma rectRot_center (φ θ : ℝ) (m : ℝ × ℝ) :
    ContinuousLinearMap.rotation (rectRot φ θ) (ContinuousLinearMap.rotation (-rectRot φ θ) m) = m :=
  rot_neg_comp' (rectRot φ θ) m

end B2

end Work.RPB.Port.Geometry
