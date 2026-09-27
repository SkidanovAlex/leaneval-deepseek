import Mathlib
import Submission.Work.KT.ClutchGeom

/-!
# The two hemispheres of the `ℓ²`-sphere of `V × ℝ`

For a normed space `V` the unit sphere `Sph (WithLp 2 (V × ℝ))` is covered by its two closed
hemispheres: the points `(v, t)` with `t ≥ 0` are the image of the closed unit ball `Ball V` of `V`
under `v ↦ (v, √(1 - ‖v‖²))`, and the points with `t ≤ 0` are its image under
`v ↦ (v, -√(1 - ‖v‖²))`.  The two parametrisations agree on the boundary sphere `Sph V` (both send
`v` with `‖v‖ = 1` to `(v, 0)`), and the projection `(v, t) ↦ v` is inverse to either of them.

These are the maps along which the algebra `C(Sph (WithLp 2 (V × ℝ)), ℂ)` of the sphere is identified
with the algebra `Work.KT.TwoDisk V` of two disks glued along their boundary spheres.
-/

namespace Work.KT

noncomputable section

variable {V : Type} [NormedAddCommGroup V]

/-- The parametrisation `v ↦ (v, √(1 - ‖v‖²))` of the upper hemisphere, evaluated in
`WithLp 2 (V × ℝ)`. -/
def hemiUpFun (v : Ball V) : WithLp 2 (V × ℝ) :=
  WithLp.toLp 2 ((v : V), √(1 - ‖(v : V)‖ ^ 2))

/-- The parametrisation `v ↦ (v, -√(1 - ‖v‖²))` of the lower hemisphere. -/
def hemiDownFun (v : Ball V) : WithLp 2 (V × ℝ) :=
  WithLp.toLp 2 ((v : V), -√(1 - ‖(v : V)‖ ^ 2))

/-- The projection `(v, t) ↦ v`, from the unit sphere of `V × ℝ` to the closed unit ball of `V`. -/
def hemiProj (x : Sph (WithLp 2 (V × ℝ))) : Ball V :=
  ⟨(x : WithLp 2 (V × ℝ)).fst, by
    rw [Metric.mem_closedBall, dist_zero_right]
    have hx : ‖(x : WithLp 2 (V × ℝ))‖ = 1 := by
      have h := Metric.mem_sphere.mp x.2
      rwa [dist_eq_norm, sub_zero] at h
    exact (WithLp.norm_fst_le V _).trans (le_of_eq hx)⟩

lemma norm_hemiUpFun (v : Ball V) : ‖hemiUpFun v‖ = 1 := by
  have hv : ‖(v : V)‖ ≤ 1 := by
    have h := Metric.mem_closedBall.mp v.2
    rwa [dist_eq_norm, sub_zero] at h
  have h1 : (0 : ℝ) ≤ 1 - ‖(v : V)‖ ^ 2 := by nlinarith [hv, norm_nonneg (v : V)]
  have h2 : ‖hemiUpFun v‖ ^ 2 = 1 := by
    rw [hemiUpFun, WithLp.prod_norm_sq_eq_of_L2, WithLp.toLp_fst, WithLp.toLp_snd,
      Real.norm_of_nonneg (Real.sqrt_nonneg _), Real.sq_sqrt h1]
    ring
  nlinarith [norm_nonneg (hemiUpFun v), h2]

lemma norm_hemiDownFun (v : Ball V) : ‖hemiDownFun v‖ = 1 := by
  have hv : ‖(v : V)‖ ≤ 1 := by
    have h := Metric.mem_closedBall.mp v.2
    rwa [dist_eq_norm, sub_zero] at h
  have h1 : (0 : ℝ) ≤ 1 - ‖(v : V)‖ ^ 2 := by nlinarith [hv, norm_nonneg (v : V)]
  have h2 : ‖hemiDownFun v‖ ^ 2 = 1 := by
    rw [hemiDownFun, WithLp.prod_norm_sq_eq_of_L2, WithLp.toLp_fst, WithLp.toLp_snd, norm_neg,
      Real.norm_of_nonneg (Real.sqrt_nonneg _), Real.sq_sqrt h1]
    ring
  nlinarith [norm_nonneg (hemiDownFun v), h2]

/-- The upper hemisphere parametrisation, as a point of the unit sphere. -/
def hemiUp (v : Ball V) : Sph (WithLp 2 (V × ℝ)) :=
  ⟨hemiUpFun v, by rw [Metric.mem_sphere]; simpa [dist_eq_norm] using norm_hemiUpFun v⟩

/-- The lower hemisphere parametrisation, as a point of the unit sphere. -/
def hemiDown (v : Ball V) : Sph (WithLp 2 (V × ℝ)) :=
  ⟨hemiDownFun v, by rw [Metric.mem_sphere]; simpa [dist_eq_norm] using norm_hemiDownFun v⟩

@[simp] lemma hemiUp_coe (v : Ball V) :
    ((hemiUp v : Sph (WithLp 2 (V × ℝ))) : WithLp 2 (V × ℝ)) = hemiUpFun v := rfl

@[simp] lemma hemiDown_coe (v : Ball V) :
    ((hemiDown v : Sph (WithLp 2 (V × ℝ))) : WithLp 2 (V × ℝ)) = hemiDownFun v := rfl

@[simp] lemma hemiProj_coe (x : Sph (WithLp 2 (V × ℝ))) :
    ((hemiProj x : Ball V) : V) = (x : WithLp 2 (V × ℝ)).fst := rfl

@[simp] lemma hemiUpFun_fst (v : Ball V) : (hemiUpFun v).fst = (v : V) := rfl

@[simp] lemma hemiUpFun_snd (v : Ball V) :
    (hemiUpFun v).snd = √(1 - ‖(v : V)‖ ^ 2) := rfl

@[simp] lemma hemiDownFun_fst (v : Ball V) : (hemiDownFun v).fst = (v : V) := rfl

@[simp] lemma hemiDownFun_snd (v : Ball V) :
    (hemiDownFun v).snd = -√(1 - ‖(v : V)‖ ^ 2) := rfl

end

end Work.KT
