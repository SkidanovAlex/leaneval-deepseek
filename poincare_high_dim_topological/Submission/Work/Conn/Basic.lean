import Mathlib

/-!
# Connectivity of spheres and manifolds: basic definitions

This chapter (`Work.Conn`) collects the connectivity statements used in the
Stallings–Zeeman–Newman engulfing proof of the generalized topological Poincaré
conjecture in dimensions `≥ 5`.

## Main definitions

* `Work.Conn.Sph n` : the standard `n`-sphere `𝕊ⁿ ⊂ ℝⁿ⁺¹`, used as a type through the
  subtype coercion, exactly as in the challenge statement.
* `Work.Conn.Ball n` : the standard closed `n`-ball `𝔻ⁿ ⊂ ℝⁿ`.
* `Work.Conn.AntipodalFree f g` : no value of `f` is the antipode of a value of `g`.

## Main results of this file

* `Work.Conn.homotopic_of_antipodalFree` : antipodal-free maps into a sphere are homotopic
  (straight-line homotopy in the ambient Euclidean space, renormalised).
* `Work.Conn.nullhomotopic_of_ne` : a map into a sphere that misses a point is null-homotopic.
-/

open Metric (sphere closedBall)
open ContinuousMap

namespace Work.Conn

/-- The standard `n`-sphere `𝕊ⁿ`, as the unit sphere of `ℝⁿ⁺¹ = EuclideanSpace ℝ (Fin (n+1))`.
Used as a type through the subtype coercion, exactly as in the challenge statement. -/
abbrev Sph (n : ℕ) : Set (EuclideanSpace ℝ (Fin (n + 1))) :=
  sphere (0 : EuclideanSpace ℝ (Fin (n + 1))) 1

/-- The standard closed `n`-ball `𝔻ⁿ ⊂ ℝⁿ`. -/
abbrev Ball (n : ℕ) : Set (EuclideanSpace ℝ (Fin n)) :=
  closedBall (0 : EuclideanSpace ℝ (Fin n)) 1

@[simp] theorem mem_Sph_iff {n : ℕ} {x : EuclideanSpace ℝ (Fin (n + 1))} :
    x ∈ Sph n ↔ ‖x‖ = 1 := by
  simp [Sph]

@[simp] theorem mem_Ball_iff {n : ℕ} {x : EuclideanSpace ℝ (Fin n)} :
    x ∈ Ball n ↔ ‖x‖ ≤ 1 := by
  simp [Ball]


/-- The inclusion `𝕊ᵐ ↪ 𝔻ᵐ⁺¹` of the unit sphere in the closed unit ball of the same ambient
space `ℝᵐ⁺¹`. -/
def SphToBall (m : ℕ) : C(Sph m, Ball (m + 1)) where
  toFun x := ⟨(x : EuclideanSpace ℝ (Fin (m + 1))),
    mem_Ball_iff.mpr (le_of_eq (mem_Sph_iff.mp x.2))⟩
  continuous_toFun := Continuous.subtype_mk continuous_subtype_val _

@[simp] theorem coe_SphToBall (m : ℕ) (x : Sph m) :
    ((SphToBall m x : Ball (m + 1)) : EuclideanSpace ℝ (Fin (m + 1))) =
      (x : EuclideanSpace ℝ (Fin (m + 1))) := rfl

/-- Two maps into `𝕊ⁿ` are *antipodal-free* when no value of the first is the antipode of a value
of the second. -/
def AntipodalFree {X : Type*} [TopologicalSpace X] {n : ℕ} (f g : C(X, Sph n)) : Prop :=
  ∀ x, (f x : EuclideanSpace ℝ (Fin (n + 1))) ≠ -(g x : EuclideanSpace ℝ (Fin (n + 1)))

theorem norm_coe_Sph (n : ℕ) (x : Sph n) : ‖(x : EuclideanSpace ℝ (Fin (n + 1)))‖ = 1 :=
  mem_Sph_iff.mp x.2

/-- The antipode of a point of `𝕊ⁿ` lies on `𝕊ⁿ`. -/
def sphNeg (n : ℕ) (x : Sph n) : Sph n :=
  ⟨-(x : EuclideanSpace ℝ (Fin (n + 1))), mem_Sph_iff.mpr (by rw [norm_neg, norm_coe_Sph])⟩

@[simp] theorem coe_sphNeg (n : ℕ) (x : Sph n) :
    (sphNeg n x : EuclideanSpace ℝ (Fin (n + 1))) = -(x : EuclideanSpace ℝ (Fin (n + 1))) := rfl

@[simp] theorem sphNeg_sphNeg (n : ℕ) (x : Sph n) : sphNeg n (sphNeg n x) = x := by
  apply Subtype.ext
  simp

/-- A vector of norm one is fixed by the normalisation map. -/
theorem inv_norm_smul_self_of_norm_eq_one {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    {y : E} (h : ‖y‖ = 1) : (‖y‖)⁻¹ • y = y := by
  rw [h, inv_one, one_smul]

/-- The normalisation of a nonzero vector is a unit vector. -/
theorem norm_inv_norm_smul {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] {y : E}
    (h : y ≠ 0) : ‖(‖y‖)⁻¹ • y‖ = 1 := by
  rw [norm_smul, Real.norm_eq_abs, abs_inv, abs_of_nonneg (norm_nonneg y),
    inv_mul_cancel₀ (norm_ne_zero_iff.mpr h)]

/-- The straight line between two points of `𝕊ⁿ` that are not antipodal never meets the origin. -/
theorem smul_add_smul_ne_zero {n : ℕ} {x y : EuclideanSpace ℝ (Fin (n + 1))}
    (hx : ‖x‖ = 1) (hy : ‖y‖ = 1) (hxy : x ≠ -y) {t : ℝ} (ht0 : 0 ≤ t) (ht1 : t ≤ 1) :
    (1 - t) • x + t • y ≠ 0 := by
  intro hzero
  have h1 : (1 - t) • x = -(t • y) := by
    rw [eq_neg_iff_add_eq_zero]
    exact hzero
  have hnorm : |1 - t| * ‖x‖ = |t| * ‖y‖ := by
    calc |1 - t| * ‖x‖ = ‖(1 - t) • x‖ := by rw [norm_smul, Real.norm_eq_abs]
      _ = ‖t • y‖ := by rw [h1, norm_neg]
      _ = |t| * ‖y‖ := by rw [norm_smul, Real.norm_eq_abs]
  rw [hx, hy, mul_one, mul_one] at hnorm
  have ht : t = 1 / 2 := by
    rw [abs_of_nonneg (by linarith : (0:ℝ) ≤ 1 - t), abs_of_nonneg ht0] at hnorm
    linarith
  subst ht
  have h3 : x + y = 0 := by
    have h2 : (1 / 2 : ℝ) • (x + y) = 0 := by
      have h4 : (1 - 1 / 2 : ℝ) • x + (1 / 2 : ℝ) • y = 0 := hzero
      rw [show (1 - 1 / 2 : ℝ) = 1 / 2 by norm_num, ← smul_add] at h4
      exact h4
    exact (smul_eq_zero.mp h2).resolve_left (by norm_num)
  exact hxy (by rw [eq_neg_iff_add_eq_zero]; exact h3)

variable {X : Type*} [TopologicalSpace X] {n : ℕ}

/-- The straight line (linear interpolation) in the ambient Euclidean space between the images
of two maps into `𝕊ⁿ`, parametrised by the unit interval. -/
def linInterp (f g : C(X, Sph n)) (p : unitInterval × X) :
    EuclideanSpace ℝ (Fin (n + 1)) :=
  (1 - ((p.1 : unitInterval) : ℝ)) • (f p.2 : EuclideanSpace ℝ (Fin (n + 1))) +
    (((p.1 : unitInterval) : ℝ)) • (g p.2 : EuclideanSpace ℝ (Fin (n + 1)))

@[simp] theorem linInterp_zero (f g : C(X, Sph n)) (x : X) :
    linInterp f g (0, x) = (f x : EuclideanSpace ℝ (Fin (n + 1))) := by
  simp [linInterp]

@[simp] theorem linInterp_one (f g : C(X, Sph n)) (x : X) :
    linInterp f g (1, x) = (g x : EuclideanSpace ℝ (Fin (n + 1))) := by
  simp [linInterp]

theorem continuous_linInterp (f g : C(X, Sph n)) : Continuous (linInterp f g) := by
  change Continuous fun p : unitInterval × X =>
    (1 - ((p.1 : unitInterval) : ℝ)) • (f p.2 : EuclideanSpace ℝ (Fin (n + 1))) +
      (((p.1 : unitInterval) : ℝ)) • (g p.2 : EuclideanSpace ℝ (Fin (n + 1)))
  fun_prop

theorem linInterp_ne_zero {f g : C(X, Sph n)} (h : AntipodalFree f g)
    (p : unitInterval × X) : linInterp f g p ≠ 0 :=
  smul_add_smul_ne_zero (norm_coe_Sph n (f p.2)) (norm_coe_Sph n (g p.2)) (h p.2)
    p.1.2.1 p.1.2.2

/-- The normalisation of `linInterp`, as a map into `𝕊ⁿ`. -/
noncomputable def normLinInterp {f g : C(X, Sph n)} (h : AntipodalFree f g) (p : unitInterval × X) : Sph n :=
  ⟨(‖linInterp f g p‖)⁻¹ • linInterp f g p,
    mem_Sph_iff.mpr (norm_inv_norm_smul (linInterp_ne_zero h p))⟩

@[simp] theorem coe_normLinInterp {f g : C(X, Sph n)} (h : AntipodalFree f g)
    (p : unitInterval × X) :
    (normLinInterp h p : EuclideanSpace ℝ (Fin (n + 1))) =
      (‖linInterp f g p‖)⁻¹ • linInterp f g p := rfl

theorem continuous_normLinInterp {f g : C(X, Sph n)} (h : AntipodalFree f g) :
    Continuous (normLinInterp h) :=
  Continuous.subtype_mk (((continuous_linInterp f g).norm.inv₀
      (fun p => norm_ne_zero_iff.mpr (linInterp_ne_zero h p))).smul (continuous_linInterp f g))
    (fun p => mem_Sph_iff.mpr (norm_inv_norm_smul (linInterp_ne_zero h p)))

/-- **Antipodal-free maps into a sphere are homotopic.**  Run the straight segment from `f x` to
`g x` in `ℝⁿ⁺¹` and renormalise; the segment avoids the origin because the two endpoints are
never antipodal. -/
theorem homotopic_of_antipodalFree {f g : C(X, Sph n)} (h : AntipodalFree f g) :
    f.Homotopic g := by
  refine ⟨ContinuousMap.Homotopy.mk
    { toFun := normLinInterp h, continuous_toFun := continuous_normLinInterp h } ?_ ?_⟩
  · intro x
    apply Subtype.ext
    rw [coe_normLinInterp, linInterp_zero,
      inv_norm_smul_self_of_norm_eq_one (norm_coe_Sph n (f x))]
  · intro x
    apply Subtype.ext
    rw [coe_normLinInterp, linInterp_one,
      inv_norm_smul_self_of_norm_eq_one (norm_coe_Sph n (g x))]

/-- A map into `𝕊ⁿ` that misses a point is null-homotopic: it is antipodal-free from the constant
map at the antipode of the missed point. -/
theorem nullhomotopic_of_ne (f : C(X, Sph n)) (q : Sph n) (h : ∀ x, f x ≠ q) :
    f.Nullhomotopic := by
  refine ⟨sphNeg n q, homotopic_of_antipodalFree fun x hx => h x (Subtype.ext ?_)⟩
  simpa [AntipodalFree, coe_sphNeg] using hx


end Work.Conn
