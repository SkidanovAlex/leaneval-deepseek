import Mathlib
import Submission.Work.KT.SphereSetup

/-!
# The quotient map `D^d → S^d`

This file builds the standard quotient map collapsing the boundary sphere `S^{d-1}` of the closed
unit disc `D^d = Ball (Euc d)` to a single point, namely the north pole of the model sphere
`S^d = Sph (ModelSphere d)`, where `ModelSphere d = ℝ^d × ℝ` is given the `ℓ²` product norm.

The map is the classical one
`x ↦ (sin (π ‖x‖) • (x/‖x‖), -cos (π ‖x‖))`, written without division as
`x ↦ (sfun ‖x‖ • x, -cos (π ‖x‖))` with `sfun r = π · sinc (π r)` the continuous extension of
`sin (π r)/r` to `r = 0`.

The lemmas collected here (`sfun_*`, `radialAngle_*`, `qMapDisk_*`, `qc_*`) are the shared vocabulary for
the main statement `Work.KT.diskQuot`.
-/

namespace Work.KT

noncomputable section

/-! ## The radial scalar `sfun` -/

/-- `sfun r = π · sinc (π r)`: the continuous extension of `sin (π r) / r` to `r = 0`. -/
def sfun (r : ℝ) : ℝ := Real.pi * Real.sinc (Real.pi * r)

lemma continuous_sfun : Continuous sfun :=
  continuous_const.mul (Real.continuous_sinc.comp (continuous_const.mul continuous_id))

@[simp] lemma sfun_zero : sfun 0 = Real.pi := by simp [sfun]

/-- The defining property of `sfun`: `sfun r * r = sin (π r)`. -/
lemma sfun_mul (r : ℝ) : sfun r * r = Real.sin (Real.pi * r) := by
  rcases eq_or_ne r 0 with hr | hr
  · subst hr; simp [sfun]
  · rw [sfun, Real.sinc_of_ne_zero (mul_ne_zero Real.pi_ne_zero hr)]
    field_simp

@[simp] lemma sfun_one : sfun 1 = 0 := by
  rw [sfun, show Real.pi * 1 = Real.pi by ring]
  rw [Real.sinc_of_ne_zero Real.pi_ne_zero, Real.sin_pi, zero_div, mul_zero]

/-- `sfun` does not vanish on `[0, 1)`. -/
lemma sfun_ne_zero {r : ℝ} (h0 : 0 ≤ r) (h1 : r < 1) : sfun r ≠ 0 := by
  intro h
  have hmul : Real.sin (Real.pi * r) = 0 := by rw [← sfun_mul, h, zero_mul]
  obtain ⟨n, hn⟩ := Real.sin_eq_zero_iff.mp hmul
  have hr : r = (n : ℝ) := by
    have h' : Real.pi * (n : ℝ) = Real.pi * r := by
      rw [mul_comm Real.pi (n : ℝ)]; exact hn
    exact (mul_left_cancel₀ Real.pi_ne_zero h').symm
  have hn0 : (0 : ℝ) ≤ (n : ℝ) := by rw [← hr]; exact h0
  have hn1 : (n : ℝ) < 1 := by rw [← hr]; exact h1
  have hnz : n = 0 := by
    have h0' : (0 : ℤ) ≤ n := by exact_mod_cast hn0
    have h1' : n < 1 := by exact_mod_cast hn1
    omega
  have : r = 0 := by rw [hr, hnz]; norm_num
  rw [this, sfun_zero] at h
  exact Real.pi_ne_zero h

/-! ## The radial angle -/

/-- The radial angle `arccos (-t)/π`, used to parametrise the target sphere. -/
def radialAngle (t : ℝ) : ℝ := Real.arccos (-t) / Real.pi

lemma radialAngle_nonneg (t : ℝ) : 0 ≤ radialAngle t :=
  div_nonneg (Real.arccos_nonneg _) Real.pi_pos.le

lemma radialAngle_le_one (t : ℝ) : radialAngle t ≤ 1 := by
  rw [radialAngle, div_le_one Real.pi_pos]
  simpa using Real.arccos_le_pi (-t)

lemma pi_mul_radialAngle (t : ℝ) : Real.pi * radialAngle t = Real.arccos (-t) := by
  rw [radialAngle]
  field_simp

lemma cos_radialAngle {t : ℝ} (h1 : -1 ≤ t) (h2 : t ≤ 1) :
    Real.cos (Real.pi * radialAngle t) = -t := by
  rw [pi_mul_radialAngle, Real.cos_arccos (by linarith) (by linarith)]

lemma sin_radialAngle (t : ℝ) :
    Real.sin (Real.pi * radialAngle t) = Real.sqrt (1 - t ^ 2) := by
  rw [pi_mul_radialAngle, Real.sin_arccos]
  congr 1
  ring

/-! ## A fixed unit vector -/

/-- A fixed unit vector of `ℝ^d`, available when `d ≥ 1`. -/
def unitVec (d : ℕ) (hd : 1 ≤ d) : Euc d :=
  PiLp.single 2 ⟨0, Nat.lt_of_lt_of_le Nat.zero_lt_one hd⟩ (1 : ℝ)

lemma norm_unitVec (d : ℕ) (hd : 1 ≤ d) : ‖unitVec d hd‖ = 1 := by
  rw [unitVec, PiLp.norm_single]
  norm_num

/-! ## The quotient map -/

/-- The (unbundled) quotient map `D^d → S^d`. -/
def qMapDisk (d : ℕ) (x : Ball (Euc d)) : ModelSphere d :=
  WithLp.toLp 2 (sfun ‖(x : Euc d)‖ • (x : Euc d),
    -Real.cos (Real.pi * ‖(x : Euc d)‖))

lemma continuous_qMapDisk (d : ℕ) : Continuous (qMapDisk d) := by
  unfold qMapDisk
  apply (WithLp.prod_continuous_toLp 2 (Euc d) ℝ).comp
  refine Continuous.prodMk ?_ ?_
  · exact (continuous_sfun.comp (continuous_norm.comp continuous_subtype_val)).smul
      continuous_subtype_val
  · exact (Real.continuous_cos.comp
      (continuous_const.mul (continuous_norm.comp continuous_subtype_val))).neg

lemma norm_qMapDisk (d : ℕ) (x : Ball (Euc d)) : ‖qMapDisk d x‖ = 1 := by
  rw [qMapDisk, WithLp.prod_norm_eq_of_L2]
  change √(‖sfun ‖(x : Euc d)‖ • (x : Euc d)‖ ^ 2
      + ‖-(Real.cos (Real.pi * ‖(x : Euc d)‖))‖ ^ 2) = 1
  have h1 : ‖sfun ‖(x : Euc d)‖ • (x : Euc d)‖ ^ 2
      = (Real.sin (Real.pi * ‖(x : Euc d)‖)) ^ 2 := by
    rw [norm_smul, Real.norm_eq_abs, mul_pow, sq_abs, ← mul_pow, sfun_mul]
  have h2 : ‖-(Real.cos (Real.pi * ‖(x : Euc d)‖))‖ ^ 2
      = (Real.cos (Real.pi * ‖(x : Euc d)‖)) ^ 2 := by
    rw [norm_neg, Real.norm_eq_abs, sq_abs]
  rw [h1, h2, Real.sin_sq_add_cos_sq, Real.sqrt_one]

/-- The quotient map `D^d → S^d` as a continuous map. -/
def qc (d : ℕ) : C(Ball (Euc d), Sph (ModelSphere d)) where
  toFun x := ⟨qMapDisk d x, mem_sphere_zero_iff_norm.mpr (norm_qMapDisk d x)⟩
  continuous_toFun := (continuous_qMapDisk d).subtype_mk _

@[simp] lemma qc_apply (d : ℕ) (x : Ball (Euc d)) :
    (qc d x : ModelSphere d) = qMapDisk d x := rfl

/-- Coordinates of `qMapDisk`: `qMapDisk d x = qMapDisk d x'` iff both coordinates agree. -/
lemma qMapDisk_eq_iff_disk (d : ℕ) (x x' : Ball (Euc d)) :
    qMapDisk d x = qMapDisk d x' ↔
      (sfun ‖(x : Euc d)‖ • (x : Euc d) = sfun ‖(x' : Euc d)‖ • (x' : Euc d) ∧
       Real.cos (Real.pi * ‖(x : Euc d)‖) = Real.cos (Real.pi * ‖(x' : Euc d)‖)) := by
  rw [qMapDisk, qMapDisk, (WithLp.toLp_injective 2).eq_iff, Prod.mk.injEq]
  simp only [neg_inj]

/-- A point of the ball has norm at most one. -/
lemma norm_le_one_of_mem_ball (d : ℕ) (x : Ball (Euc d)) : ‖(x : Euc d)‖ ≤ 1 := by
  have := Metric.mem_closedBall.mp x.2
  simpa [dist_eq_norm] using this

/-- On the boundary the value of `qMapDisk` is the north pole. -/
lemma qMapDisk_bdry_val (d : ℕ) (x : Ball (Euc d)) (hv : ‖(x : Euc d)‖ = 1) :
    qMapDisk d x = WithLp.toLp 2 ((0 : Euc d), (1 : ℝ)) := by
  unfold qMapDisk
  rw [hv, sfun_one, zero_smul, mul_one, Real.cos_pi, neg_neg]

/-- The boundary of the disc maps to the north pole. -/
lemma qc_bdry (d : ℕ) (x : Ball (Euc d)) (hx : x ∈ bdry (Euc d)) : qc d x = sphKT_northPole d := by
  apply Subtype.ext
  rw [qc_apply, qMapDisk_bdry_val d x hx, northPole_coe]

end

end Work.KT
