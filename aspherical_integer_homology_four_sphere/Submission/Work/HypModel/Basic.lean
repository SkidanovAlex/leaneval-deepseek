import Mathlib

-- Lean v4.35.0-rc3 / Mathlib 5e0c4e5 made `isDefEq` respect transparency when unifying instances; with it,
-- `ZMod.instField` and `ZMod.commRing` (and `Neg (ZMod p)` via `SubtractionMonoid`) no longer unify, which
-- breaks `ring`/`rw`/module-instance search on `ZMod p`. Restore the v4.34 behaviour for this file.
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false


/-!
# Definition layer for the hyperbolic models `Work.HypModel`

This is the *definition* file of the chapter `Work.HypModel`; it contains the model spaces of
hyperbolic 4-geometry used in the Ratcliffe–Tschantz construction of an aspherical integer homology
4-sphere, and no theorem whose proof is more than a computation.

Conventions (fixed once and for all):

* `V5 := Fin 5 → ℝ` — the ambient Lorentz space; coordinates are `0,1,2,3,4` and the *timelike*
  coordinate is `4`.  The Lorentz form is `⟨x,y⟩ = x₀y₀ + x₁y₁ + x₂y₂ + x₃y₃ − x₄y₄`.
* `E4 := EuclideanSpace ℝ (Fin 4)` — the coordinate space of the Klein ball and of the upper half
  space model.  `ball` is the open unit ball (the Klein model); in the upper half space model the
  *height* is the coordinate `q 3` and the point `∞` is the null vector `infty = (0,0,0,1,1) ∈ V5`.
* `upperSheet = {x : ⟨x,x⟩ = -1, x₄ > 0}` is the hyperboloid model.
* `hypOfKlein : ball → upperSheet` is the Klein lift `y ↦ (y,1)/√(1−|y|²)`.
* `hypOfUHS : {q : 0 < q 3} → upperSheet` is the isometry
  `(x,s) ↦ (x/s, (‖q‖²−1)/(2s), (‖q‖²+1)/(2s))`, and `uhsOfHyp` is its inverse.
* `uhsMetric q v w = (q 3)⁻²⟪v,w⟫` is the hyperbolic metric `(|dx|²+ds²)/s²` of the upper half
  space model.
* `mobius A q = uhsOfHyp (A *ᵥ hypOfUHS q)` is the action of a Lorentz matrix on the upper half
  space; `mobiusKlein A y = uhsOfHyp (A *ᵥ hypOfKlein y)` is its action on a Klein point.
* `uhsTranslation b`, `uhsRotation O` and `lorentzReflection v` are the Lorentz matrices of the
  horospherical translations `x ↦ x + b`, of the rotations of `x`, and of the reflection in the
  geodesic hyperplane `{⟨x,v⟩ = 0}`.
* `warpedMetric f h` and `polarToUHS C D` implement the polar ↔ upper-half-space comparison for the
  warped metric `dr² + f(r)²dθ² + h(r)²|dw|²`.
-/

noncomputable section

namespace Work.HypModel

open scoped Matrix InnerProductSpace
open Matrix

/-- The ambient Lorentz space `ℝ^{1,4}`. -/
abbrev V5 := Fin 5 → ℝ

/-- Coordinate space for the Klein ball and the upper half space model. -/
abbrev E4 := EuclideanSpace ℝ (Fin 4)

/-- The open unit ball, the Klein model of hyperbolic 4-space. -/
def ball : Set E4 := {y | ‖y‖ < 1}

/-- The upper half space `{q : q 3 > 0}`. -/
def upperHalfSpace : Set E4 := {q | 0 < q 3}

/-! ### The Lorentz form -/

/-- The Lorentz bilinear form `⟨x,y⟩ = x₀y₀+x₁y₁+x₂y₂+x₃y₃ − x₄y₄` on `ℝ⁵`. -/
def lorentz (x y : V5) : ℝ := x 0 * y 0 + x 1 * y 1 + x 2 * y 2 + x 3 * y 3 - x 4 * y 4

@[simp] theorem lorentz_apply (x y : V5) :
    lorentz x y = x 0 * y 0 + x 1 * y 1 + x 2 * y 2 + x 3 * y 3 - x 4 * y 4 := rfl

theorem lorentz_comm (x y : V5) : lorentz x y = lorentz y x := by
  simp only [lorentz]; ring

@[simp] theorem lorentz_zero_left (y : V5) : lorentz 0 y = 0 := by simp [lorentz]

@[simp] theorem lorentz_zero_right (x : V5) : lorentz x 0 = 0 := by simp [lorentz]

theorem lorentz_add_left (x x' y : V5) : lorentz (x + x') y = lorentz x y + lorentz x' y := by
  simp only [lorentz, Pi.add_apply]; ring

theorem lorentz_add_right (x y y' : V5) : lorentz x (y + y') = lorentz x y + lorentz x y' := by
  simp only [lorentz, Pi.add_apply]; ring

theorem lorentz_smul_left (c : ℝ) (x y : V5) : lorentz (c • x) y = c * lorentz x y := by
  simp only [lorentz, Pi.smul_apply, smul_eq_mul]; ring

theorem lorentz_smul_right (c : ℝ) (x y : V5) : lorentz x (c • y) = c * lorentz x y := by
  simp only [lorentz, Pi.smul_apply, smul_eq_mul]; ring

theorem lorentz_neg_left (x y : V5) : lorentz (-x) y = - lorentz x y := by
  simp only [lorentz, Pi.neg_apply]; ring

theorem lorentz_neg_right (x y : V5) : lorentz x (-y) = - lorentz x y := by
  simp only [lorentz, Pi.neg_apply]; ring

theorem lorentz_sub_left (x x' y : V5) : lorentz (x - x') y = lorentz x y - lorentz x' y := by
  simp only [lorentz, Pi.sub_apply]; ring

theorem lorentz_sub_right (x y y' : V5) : lorentz x (y - y') = lorentz x y - lorentz x y' := by
  simp only [lorentz, Pi.sub_apply]; ring

/-- The Gram matrix `J = diag(1,1,1,1,-1)` of the Lorentz form. -/
def J : Matrix (Fin 5) (Fin 5) ℝ := Matrix.diagonal (fun i => if i = 4 then -1 else 1)

@[simp] theorem J_apply_self (i : Fin 5) : J i i = if i = 4 then -1 else 1 := by simp [J]

@[simp] theorem J_apply_of_ne {i j : Fin 5} (h : i ≠ j) : J i j = 0 := by simp [J, h]

theorem J_mulVec (y : V5) : J *ᵥ y = fun i => (if i = 4 then -1 else 1) * y i := by
  ext i
  rw [show J = Matrix.diagonal (fun i => if i = 4 then -1 else 1) from rfl, mulVec_diagonal]

/-- `lorentz x y = x ⬝ᵥ (J *ᵥ y)`. -/
theorem lorentz_eq_dotProduct (x y : V5) : lorentz x y = x ⬝ᵥ (J *ᵥ y) := by
  rw [J_mulVec]
  simp only [dotProduct, Fin.sum_univ_five, Fin.isValue]
  norm_num
  ring

/-! ### The Lorentz group -/

/-- Matrices lying in the Lorentz group *and* preserving the upper sheet: `Aᵀ J A = J` and
`A 4 4 > 0`. -/
def IsLorentzMat (A : Matrix (Fin 5) (Fin 5) ℝ) : Prop := Aᵀ * J * A = J ∧ 0 < A 4 4

theorem IsLorentzMat.isometry {A : Matrix (Fin 5) (Fin 5) ℝ} (hA : IsLorentzMat A) :
    Aᵀ * J * A = J := hA.1

theorem IsLorentzMat.pos {A : Matrix (Fin 5) (Fin 5) ℝ} (hA : IsLorentzMat A) :
    0 < A 4 4 := hA.2

@[simp] theorem IsLorentzMat_one : IsLorentzMat 1 :=
  ⟨by simp, by simp⟩

/-- Adjointness of `mulVec` against the Euclidean dot product. -/
theorem dotProduct_mulVec_transpose (A : Matrix (Fin 5) (Fin 5) ℝ) (x y : V5) :
    (A *ᵥ x) ⬝ᵥ y = x ⬝ᵥ (Aᵀ *ᵥ y) := by
  rw [dotProduct_comm, Matrix.dotProduct_mulVec, Matrix.mulVec_transpose, dotProduct_comm]

/-- The first four coordinates of a point of `ℝ⁵`, as an element of `E4`. -/
def proj4 (x : V5) : E4 := !₂[x 0, x 1, x 2, x 3]

@[simp] theorem proj4_apply_zero (x : V5) : proj4 x 0 = x 0 := rfl
@[simp] theorem proj4_apply_one (x : V5) : proj4 x 1 = x 1 := rfl
@[simp] theorem proj4_apply_two (x : V5) : proj4 x 2 = x 2 := rfl
@[simp] theorem proj4_apply_three (x : V5) : proj4 x 3 = x 3 := rfl

/-- The Euclidean inner product on `E4` is the dot product of coordinates. -/
theorem inner_eq_dotProduct (a b : E4) : ⟪a, b⟫_ℝ = a ⬝ᵥ b := by
  simp [dotProduct, PiLp.inner_apply, mul_comm]

theorem lorentz_eq_dotProduct_proj4 (x y : V5) :
    lorentz x y = (proj4 x ⬝ᵥ proj4 y) - x 4 * y 4 := by
  simp only [lorentz, proj4, dotProduct]
  simp [Fin.sum_univ_four]

/-- The upper sheet of the hyperboloid: `⟨x,x⟩ = -1` and `x₄ > 0`. -/
def upperSheet : Set V5 := {x | lorentz x x = -1 ∧ 0 < x 4}

theorem upperSheet_lorentz_self {x : V5} (hx : x ∈ upperSheet) : lorentz x x = -1 := hx.1

theorem upperSheet_four_pos {x : V5} (hx : x ∈ upperSheet) : 0 < x 4 := hx.2

/-- The timelike basis vector `e₄ = (0,0,0,0,1)`, which lies on the upper sheet. -/
def timeVec : V5 := ![0, 0, 0, 0, 1]

@[simp] theorem timeVec_apply_four : timeVec 4 = 1 := rfl

@[simp] theorem lorentz_left_timeVec (x : V5) : lorentz x timeVec = - x 4 := by
  simp [lorentz, timeVec]

@[simp] theorem lorentz_right_timeVec (x : V5) : lorentz timeVec x = - x 4 := by
  simp [lorentz, timeVec]

@[simp] theorem lorentz_timeVec_self : lorentz timeVec timeVec = -1 := by simp [lorentz, timeVec]

/-- The `4`-th coordinate of `A *ᵥ e₄` is `A 4 4`. -/
@[simp] theorem mulVec_timeVec_four (A : Matrix (Fin 5) (Fin 5) ℝ) : (A *ᵥ timeVec) 4 = A 4 4 := by
  simp [Matrix.mulVec, dotProduct, timeVec, Fin.sum_univ_five]


theorem timeVec_mem_upperSheet : timeVec ∈ upperSheet := ⟨lorentz_timeVec_self, by simp⟩

/-- The null vector `∞ = (0,0,0,1,1)` of the upper half space model. -/
def infty : V5 := ![0, 0, 0, 1, 1]

@[simp] theorem infty_apply_zero : infty 0 = 0 := rfl
@[simp] theorem infty_apply_one : infty 1 = 0 := rfl
@[simp] theorem infty_apply_two : infty 2 = 0 := rfl
@[simp] theorem infty_apply_three : infty 3 = 1 := rfl
@[simp] theorem infty_apply_four : infty 4 = 1 := rfl

@[simp] theorem lorentz_left_infty (x : V5) : lorentz x infty = x 3 - x 4 := by
  simp [lorentz, infty]

@[simp] theorem lorentz_right_infty (x : V5) : lorentz infty x = x 3 - x 4 := by
  simp [lorentz, infty]

@[simp] theorem lorentz_infty_self : lorentz infty infty = 0 := by simp [lorentz, infty]

theorem lorentz_left_infty' (x : V5) : lorentz x infty = - (x 4 - x 3) := by
  simp [lorentz, infty]

/-! ### The null ray over a point of `E4` -/

/-- The null ray over `y ∈ E4`: the vector `(y,1) ∈ ℝ⁵`.  It is null exactly when `‖y‖ = 1`. -/
def ray (y : E4) : V5 := ![y 0, y 1, y 2, y 3, 1]

@[simp] theorem ray_apply_zero (y : E4) : ray y 0 = y 0 := rfl
@[simp] theorem ray_apply_one (y : E4) : ray y 1 = y 1 := rfl
@[simp] theorem ray_apply_two (y : E4) : ray y 2 = y 2 := rfl
@[simp] theorem ray_apply_three (y : E4) : ray y 3 = y 3 := rfl
@[simp] theorem ray_apply_four (y : E4) : ray y 4 = 1 := rfl

theorem proj4_ray (x : E4) : proj4 (ray x) = x := by
  ext i
  fin_cases i <;> simp [proj4, ray]

theorem lorentz_ray (x y : E4) : lorentz (ray x) (ray y) = ⟪x, y⟫_ℝ - 1 := by
  rw [lorentz_eq_dotProduct_proj4, inner_eq_dotProduct, proj4_ray, proj4_ray]
  simp

theorem lorentz_ray_self (y : E4) : lorentz (ray y) (ray y) = ‖y‖ ^ 2 - 1 := by
  rw [lorentz_ray, real_inner_self_eq_norm_sq]


/-- The linear action of a `4 × 4` matrix on `E4`. -/
def rot4 (O : Matrix (Fin 4) (Fin 4) ℝ) (y : E4) : E4 :=
  !₂[∑ j : Fin 4, O 0 j * y j, ∑ j : Fin 4, O 1 j * y j, ∑ j : Fin 4, O 2 j * y j,
     ∑ j : Fin 4, O 3 j * y j]


/-- The Euclidean inner product of two points of `E4`, as a plain function (use this in statements
that are elaborated without `open scoped InnerProductSpace`). -/
def euclid (x y : E4) : ℝ := ⟪x, y⟫_ℝ

@[simp] theorem euclid_apply (x y : E4) : euclid x y = ⟪x, y⟫_ℝ := rfl

theorem euclid_comm (x y : E4) : euclid x y = euclid y x := by
  simp [euclid, real_inner_comm]

theorem euclid_self (x : E4) : euclid x x = ‖x‖ ^ 2 := by
  simp [euclid, real_inner_self_eq_norm_sq]


/-- The null ray over an ideal vertex: for `‖w‖ = 1` the vector `ray w = (w,1)` is null. -/
theorem lorentz_ray_self_eq_zero {w : E4} (hw : ‖w‖ = 1) : lorentz (ray w) (ray w) = 0 := by
  rw [lorentz_ray_self, hw]
  norm_num

/-! ### The Klein model -/

/-- The Klein lift: `y ↦ (y,1)/√(1−|y|²)`.  For `y` in the open unit ball this is a point of the
upper sheet of the hyperboloid. -/
def hypOfKlein (y : E4) : V5 := (Real.sqrt (1 - ‖y‖ ^ 2))⁻¹ • ray y

@[simp] theorem hypOfKlein_apply_zero (y : E4) :
    hypOfKlein y 0 = (Real.sqrt (1 - ‖y‖ ^ 2))⁻¹ * y 0 := by simp [hypOfKlein, ray]
@[simp] theorem hypOfKlein_apply_one (y : E4) :
    hypOfKlein y 1 = (Real.sqrt (1 - ‖y‖ ^ 2))⁻¹ * y 1 := by simp [hypOfKlein, ray]
@[simp] theorem hypOfKlein_apply_two (y : E4) :
    hypOfKlein y 2 = (Real.sqrt (1 - ‖y‖ ^ 2))⁻¹ * y 2 := by simp [hypOfKlein, ray]
@[simp] theorem hypOfKlein_apply_three (y : E4) :
    hypOfKlein y 3 = (Real.sqrt (1 - ‖y‖ ^ 2))⁻¹ * y 3 := by simp [hypOfKlein, ray]
@[simp] theorem hypOfKlein_apply_four (y : E4) :
    hypOfKlein y 4 = (Real.sqrt (1 - ‖y‖ ^ 2))⁻¹ := by simp [hypOfKlein, ray]

/-- The central projection of the hyperboloid to the plane `x₄ = 1`: the inverse of the Klein
lift on the hyperboloid. -/
def kleinOfHyp (P : V5) : E4 := (P 4)⁻¹ • proj4 P

@[simp] theorem kleinOfHyp_apply_zero (P : V5) : kleinOfHyp P 0 = (P 4)⁻¹ * P 0 := by
  simp [kleinOfHyp, proj4]
@[simp] theorem kleinOfHyp_apply_one (P : V5) : kleinOfHyp P 1 = (P 4)⁻¹ * P 1 := by
  simp [kleinOfHyp, proj4]
@[simp] theorem kleinOfHyp_apply_two (P : V5) : kleinOfHyp P 2 = (P 4)⁻¹ * P 2 := by
  simp [kleinOfHyp, proj4]
@[simp] theorem kleinOfHyp_apply_three (P : V5) : kleinOfHyp P 3 = (P 4)⁻¹ * P 3 := by
  simp [kleinOfHyp, proj4]

/-! ### The upper half space model -/

/-- **The isometry from the upper half space to the hyperboloid.**
`(x, s) ↦ (x/s, (‖q‖²−1)/(2s), (‖q‖²+1)/(2s))`, where `‖q‖² = |x|² + s²`. -/
def hypOfUHS (q : E4) : V5 :=
  ![q 0 / q 3, q 1 / q 3, q 2 / q 3, (‖q‖ ^ 2 - 1) / (2 * q 3), (‖q‖ ^ 2 + 1) / (2 * q 3)]

@[simp] theorem hypOfUHS_apply_zero (q : E4) : hypOfUHS q 0 = q 0 / q 3 := rfl
@[simp] theorem hypOfUHS_apply_one (q : E4) : hypOfUHS q 1 = q 1 / q 3 := rfl
@[simp] theorem hypOfUHS_apply_two (q : E4) : hypOfUHS q 2 = q 2 / q 3 := rfl
@[simp] theorem hypOfUHS_apply_three (q : E4) : hypOfUHS q 3 = (‖q‖ ^ 2 - 1) / (2 * q 3) := rfl
@[simp] theorem hypOfUHS_apply_four (q : E4) : hypOfUHS q 4 = (‖q‖ ^ 2 + 1) / (2 * q 3) := rfl

/-- The inverse of `Π` on the hyperboloid: `P ↦ (P₀,P₁,P₂,P₄−P₃)/(P₄−P₃)`. -/
def uhsOfHyp (P : V5) : E4 :=
  let s := (P 4 - P 3)⁻¹
  !₂[P 0 * s, P 1 * s, P 2 * s, s]

@[simp] theorem uhsOfHyp_apply_zero (P : V5) : uhsOfHyp P 0 = P 0 * (P 4 - P 3)⁻¹ := by
  simp [uhsOfHyp]
@[simp] theorem uhsOfHyp_apply_one (P : V5) : uhsOfHyp P 1 = P 1 * (P 4 - P 3)⁻¹ := by
  simp [uhsOfHyp]
@[simp] theorem uhsOfHyp_apply_two (P : V5) : uhsOfHyp P 2 = P 2 * (P 4 - P 3)⁻¹ := by
  simp [uhsOfHyp]
@[simp] theorem uhsOfHyp_apply_three (P : V5) : uhsOfHyp P 3 = (P 4 - P 3)⁻¹ := by
  simp [uhsOfHyp]

/-- The pairing with the null vector `∞` reads off the height: `⟨Π(q), ∞⟩ = −1/q 3`.  Thus `Π(q)`
reaches the boundary point `∞` exactly as the height `q 3` tends to `0`. -/
theorem lorentz_hypOfUHS_infty (q : E4) : lorentz (hypOfUHS q) infty = - (q 3)⁻¹ := by
  rw [lorentz_left_infty, hypOfUHS_apply_three, hypOfUHS_apply_four]
  field_simp
  ring

/-- On the upper sheet, the height `P₄ − P₃` is positive. -/
theorem upperSheet_four_sub_three_pos {P : V5} (hP : P ∈ upperSheet) : 0 < P 4 - P 3 := by
  have h1 : P 0 * P 0 + P 1 * P 1 + P 2 * P 2 + P 3 * P 3 - P 4 * P 4 = -1 := hP.1
  have h2 : P 0 ^ 2 + P 1 ^ 2 + P 2 ^ 2 ≥ 0 := by positivity
  nlinarith [hP.2, sq_nonneg (P 3), h2]


/-- The Klein model metric at `y`: `(1−|y|²)⁻¹⟪v,w⟫ + (1−|y|²)⁻²⟪y,v⟫⟪y,w⟫`.  It is the pullback
of the Lorentz form along `hypOfKlein` (see `lorentz_hypOfKlein`). -/
def kleinMetric (y : E4) (v w : E4) : ℝ :=
  (1 - ‖y‖ ^ 2)⁻¹ * ⟪v, w⟫_ℝ + ((1 - ‖y‖ ^ 2)⁻¹) ^ 2 * (⟪y, v⟫_ℝ * ⟪y, w⟫_ℝ)

/-! ### The upper half space metric -/

/-- The hyperbolic metric of the upper half space model: `(|dx|² + ds²)/s²` with `s = q 3`. -/
def uhsMetric (q : E4) (v w : E4) : ℝ := ((q 3)⁻¹) ^ 2 * ⟪v, w⟫_ℝ

@[simp] theorem uhsMetric_apply (q v w : E4) :
    uhsMetric q v w = ((q 3)⁻¹) ^ 2 * ⟪v, w⟫_ℝ := rfl

theorem uhsMetric_comm (q v w : E4) : uhsMetric q v w = uhsMetric q w v := by
  simp [uhsMetric, real_inner_comm]

/-! ### Explicit derivatives -/

/-- The explicit derivative of `hypOfUHS` at `q` (valid for `q 3 ≠ 0`). -/
def dHypOfUHS (q : E4) : E4 →L[ℝ] V5 :=
  LinearMap.toContinuousLinearMap
  { toFun v := ![(v 0 * q 3 - q 0 * v 3) / q 3 ^ 2, (v 1 * q 3 - q 1 * v 3) / q 3 ^ 2,
      (v 2 * q 3 - q 2 * v 3) / q 3 ^ 2,
      (2 * ⟪q, v⟫_ℝ * q 3 - (‖q‖ ^ 2 - 1) * v 3) / (2 * q 3 ^ 2),
      (2 * ⟪q, v⟫_ℝ * q 3 - (‖q‖ ^ 2 + 1) * v 3) / (2 * q 3 ^ 2)]
    map_add' v w := by
      ext i
      fin_cases i <;> simp [inner_add_right] <;> ring
    map_smul' c v := by
      ext i
      fin_cases i <;> simp [inner_smul_right] <;> ring }

@[simp] theorem dHypOfUHS_apply_zero (q v : E4) :
    dHypOfUHS q v 0 = (v 0 * q 3 - q 0 * v 3) / q 3 ^ 2 := by simp [dHypOfUHS]
@[simp] theorem dHypOfUHS_apply_one (q v : E4) :
    dHypOfUHS q v 1 = (v 1 * q 3 - q 1 * v 3) / q 3 ^ 2 := by simp [dHypOfUHS]
@[simp] theorem dHypOfUHS_apply_two (q v : E4) :
    dHypOfUHS q v 2 = (v 2 * q 3 - q 2 * v 3) / q 3 ^ 2 := by simp [dHypOfUHS]
@[simp] theorem dHypOfUHS_apply_three (q v : E4) :
    dHypOfUHS q v 3 = (2 * ⟪q, v⟫_ℝ * q 3 - (‖q‖ ^ 2 - 1) * v 3) / (2 * q 3 ^ 2) := by
  simp [dHypOfUHS]
@[simp] theorem dHypOfUHS_apply_four (q v : E4) :
    dHypOfUHS q v 4 = (2 * ⟪q, v⟫_ℝ * q 3 - (‖q‖ ^ 2 + 1) * v 3) / (2 * q 3 ^ 2) := by
  simp [dHypOfUHS]

/-- The explicit derivative of `uhsOfHyp` at `P` (valid for `P₄ − P₃ ≠ 0`). -/
def dUhsOfHyp (P : V5) : V5 →L[ℝ] E4 :=
  LinearMap.toContinuousLinearMap
  { toFun v :=
      let δ := P 4 - P 3
      !₂[v 0 / δ - P 0 * (v 4 - v 3) / δ ^ 2, v 1 / δ - P 1 * (v 4 - v 3) / δ ^ 2,
        v 2 / δ - P 2 * (v 4 - v 3) / δ ^ 2, -(v 4 - v 3) / δ ^ 2]
    map_add' v w := by
      ext i
      fin_cases i <;> simp <;> ring
    map_smul' c v := by
      ext i
      fin_cases i <;> simp <;> ring }

/-! ### Möbius transformations -/

/-- The Möbius transformation of the upper half space induced by a Lorentz matrix:
`q ↦ uhsOfHyp (A *ᵥ hypOfUHS q)`. -/
def mobius (A : Matrix (Fin 5) (Fin 5) ℝ) (q : E4) : E4 := uhsOfHyp (A *ᵥ hypOfUHS q)

/-- The action of a Lorentz matrix on the Klein model: `y ↦ uhsOfHyp (A *ᵥ (y,1)/√(1−|y|²))`.
The image is expressed in upper half space coordinates. -/
def mobiusKlein (A : Matrix (Fin 5) (Fin 5) ℝ) (y : E4) : E4 := uhsOfHyp (A *ᵥ hypOfKlein y)

/-- The Lorentz matrix of the horospherical translation `x ↦ x + b`, `s ↦ s` of the upper half
space model (it fixes `infty`).  Only the first three coordinates of `b` are used. -/
def uhsTranslation (b : E4) : Matrix (Fin 5) (Fin 5) ℝ :=
  !![1, 0, 0, -b 0, b 0;
     0, 1, 0, -b 1, b 1;
     0, 0, 1, -b 2, b 2;
     b 0, b 1, b 2, 1 - (b 0 ^ 2 + b 1 ^ 2 + b 2 ^ 2) / 2, (b 0 ^ 2 + b 1 ^ 2 + b 2 ^ 2) / 2;
     b 0, b 1, b 2, -(b 0 ^ 2 + b 1 ^ 2 + b 2 ^ 2) / 2, 1 + (b 0 ^ 2 + b 1 ^ 2 + b 2 ^ 2) / 2]

/-- The Lorentz matrix of the rotation `x ↦ O x` of the horizontal coordinates of the upper half
space model, `s` fixed. -/
def uhsRotation (O : Matrix (Fin 3) (Fin 3) ℝ) : Matrix (Fin 5) (Fin 5) ℝ :=
  !![O 0 0, O 0 1, O 0 2, 0, 0;
     O 1 0, O 1 1, O 1 2, 0, 0;
     O 2 0, O 2 1, O 2 2, 0, 0;
     0, 0, 0, 1, 0;
     0, 0, 0, 0, 1]

/-- The reflection `x ↦ x − 2⟨x,v⟩/⟨v,v⟩ · v` in the geodesic hyperplane `{x : ⟨x,v⟩ = 0}`
(spacelike `v`). -/
def lorentzReflection (v : V5) : Matrix (Fin 5) (Fin 5) ℝ :=
  1 - (2 * (lorentz v v)⁻¹) • Matrix.vecMulVec v (J *ᵥ v)

/-- The Euclidean part of a Möbius transformation fixing `infty`: `x ↦ O x + b`, `s` fixed. -/
def euclidAction (O : Matrix (Fin 3) (Fin 3) ℝ) (b : E4) (q : E4) : E4 :=
  !₂[∑ j : Fin 3, O 0 j * q j.castSucc + b 0, ∑ j : Fin 3, O 1 j * q j.castSucc + b 1,
     ∑ j : Fin 3, O 2 j * q j.castSucc + b 2, q 3]


/-- The Lorentz matrix `diag(O,1)` extending an orthogonal transformation of the Klein coordinates
to a Lorentz transformation of `ℝ⁵`. -/
def blockLast (O : Matrix (Fin 4) (Fin 4) ℝ) : Matrix (Fin 5) (Fin 5) ℝ :=
  fun i j =>
    if hi : (i : ℕ) < 4 then (if hj : (j : ℕ) < 4 then O ⟨i, hi⟩ ⟨j, hj⟩ else 0)
    else (if hj : (j : ℕ) < 4 then 0 else 1)

/-- The upper half space position of a point `P` of the hyperboloid, as seen from the ideal vertex
`w ∈ E4`: the orthogonal projection of the first four coordinates of `P` onto the hyperplane
`w^⊥ ⊆ ℝ⁴`, divided by `P₄ − w·P₀₁₂₃`.  With `W := w^⊥ ≅ ℝ³` this is the position of `P` in the
upper half space chart centred at `w` (the height is `(P₄ − w·P₀₁₂₃)⁻¹`). -/
def uhsPositionAt (w : E4) (P : V5) : E4 :=
  (P 4 - ⟪w, proj4 P⟫_ℝ)⁻¹ • (proj4 P - ⟪w, proj4 P⟫_ℝ • w)

/-! ### Warped metrics and polar coordinates -/

/-- The warped metric `dr² + f(r)² dθ² + h(r)² |dw|²` on `(r,θ,w₁,w₂)`. -/
def warpedMetric (f h : ℝ → ℝ) (q : E4) (v w : E4) : ℝ :=
  v 0 * w 0 + f (q 0) ^ 2 * (v 1 * w 1) + h (q 0) ^ 2 * (v 2 * w 2 + v 3 * w 3)

/-- The flat metric of the core of the filling: `da² + db² + h₀²|dw|²` in Cartesian coordinates
`(a,b,w₁,w₂)`. -/
def flatMetric (h₀ : ℝ) (q : E4) (v w : E4) : ℝ :=
  v 0 * w 0 + v 1 * w 1 + h₀ ^ 2 * (v 2 * w 2 + v 3 * w 3)

/-- The polar-to-Cartesian map of the flat core: `(r,θ,w₁,w₂) ↦ (r cos θ, r sin θ, w₁, w₂)`. -/
def polarToCartesian (p : E4) : E4 :=
  !₂[p 0 * Real.cos (p 1), p 0 * Real.sin (p 1), p 2, p 3]

/-- The polar-to-upper-half-space map realising the warped metric with `f = C e^r`, `h = D e^r`
as the upper half space model: `(r,θ,w₁,w₂) ↦ ((C/D)θ, w₁, w₂, (1/D)e^{−r})`.  Here the horizontal
coordinates are written in the orthonormal frame whose first vector is the angle direction `σ̂`, and
`r, θ, w` are the coordinates of `(dr² + f(r)²dθ² + h(r)²|dw|²)`. -/
def polarToUHS (C D : ℝ) (p : E4) : E4 :=
  !₂[C / D * p 1, p 2, p 3, D⁻¹ * Real.exp (-(p 0))]

end Work.HypModel
