import Mathlib
import Submission.Work.Bicollar.Defs
import Submission.Work.CoreTopology.standardTorusSides
import Submission.Work.CoreTopology.horizVec_torusMap_div_norm
import Submission.Work.CoreTopology.meridVec_torusMap_div_norm

/-!
# The standard torus as a product: tube coordinates

The standard torus of revolution `Σ = standard.carrier` is the level set `{R = 1}` of the
*meridian radius* `R x = ‖meridVec x‖`, where `meridVec x = ⟨r - 2, x 2⟩` is the projection of
`x` onto the meridian half-plane (`r = ‖horizVec x‖` is the horizontal radius).  Equivalently
`Σ` is the image of the parametrisation `torusMap θ φ`.

Away from the axis `{r = 0}` and from the core circle `{meridVec = 0}` the point `x` of `ℝ³` is
determined by the triple

* `u = horizVec x / ‖horizVec x‖ ∈ S¹` — the longitude,
* `v = meridVec x / ‖meridVec x‖ ∈ S¹` — the meridian direction,
* `s = ‖meridVec x‖ ∈ (0,∞)` — the meridian radius,

namely `x = tubePt u v s`, the point at longitude `u`, meridian direction `v` and meridian
radius `s`.  This file sets up that parametrisation and its elementary properties
(`horizVec_tubePt`, `meridVec_tubePt`, `tubePt_reconstruct`, ...), together with the
regular-neighbourhood region

`tubeU = {x | 0 < ‖meridVec x‖ ∧ ‖meridVec x‖ < 2}`

(the punctured open solid torus of radius `2`, a neighbourhood of `Σ` on which the tube
coordinates are a genuine product), and the homeomorphism `(0,2) ≅ ℝ` that turns the meridian
radius into an honest normal coordinate.
-/

open Set
open Work.CoreTopology

namespace Work.Bicollar

noncomputable section

/-! ## The tube parametrisation -/

/-- **The tube point** at longitude `u`, meridian direction `v` and meridian radius `s`: the
point of `ℝ³` whose horizontal projection is `(2 + s · v.re) · u` and whose `z`-coordinate is
`s · v.im`.  When `u = circlePoint θ`, `v = circlePoint φ` this is
`((2 + s cos φ) cos θ, (2 + s cos φ) sin θ, s sin φ)`; for `s = 1` it is `torusMap θ φ`. -/
def tubePt (u v : Circle) (s : ℝ) : R3 :=
  WithLp.toLp 2 (fun i : Fin 3 =>
    if i.val = 0 then (2 + s * (v : ℂ).re) * (u : ℂ).re
    else if i.val = 1 then (2 + s * (v : ℂ).re) * (u : ℂ).im
    else s * (v : ℂ).im)

@[simp] theorem tubePt_apply_zero (u v : Circle) (s : ℝ) :
    tubePt u v s 0 = (2 + s * (v : ℂ).re) * (u : ℂ).re := by
  simp [tubePt]

@[simp] theorem tubePt_apply_one (u v : Circle) (s : ℝ) :
    tubePt u v s 1 = (2 + s * (v : ℂ).re) * (u : ℂ).im := by
  simp [tubePt]

@[simp] theorem tubePt_apply_two (u v : Circle) (s : ℝ) :
    tubePt u v s 2 = s * (v : ℂ).im := by
  simp [tubePt]

/-- The norm of a point of the circle, as a complex number. -/
theorem norm_coe_circle (u : Circle) : ‖(u : ℂ)‖ = 1 :=
  mem_sphere_zero_iff_norm.mp u.2

/-- The real part of a point of the circle is at least `-1`. -/
theorem neg_one_le_re_circle (v : Circle) : -1 ≤ (v : ℂ).re := by
  have h := Complex.abs_re_le_norm (v : ℂ)
  rw [norm_coe_circle v] at h
  linarith [neg_abs_le (v : ℂ).re]

/-- The horizontal projection of a tube point. -/
theorem horizVec_tubePt (u v : Circle) (s : ℝ) :
    horizVec (tubePt u v s) = (((2 + s * (v : ℂ).re : ℝ)) : ℂ) * (u : ℂ) := by
  apply Complex.ext <;>
    simp [horizVec, Complex.mul_re, Complex.mul_im]

/-- The horizontal radius of a tube point is `2 + s · v.re` (which is positive as soon as
`s < 2`). -/
theorem horizRadius_tubePt {u v : Circle} {s : ℝ} (h : 0 < 2 + s * (v : ℂ).re) :
    horizRadius (tubePt u v s) = 2 + s * (v : ℂ).re := by
  rw [← norm_horizVec, horizVec_tubePt, Complex.norm_mul, Complex.norm_real, Real.norm_eq_abs,
    abs_of_pos h, norm_coe_circle, mul_one]

/-- The meridian projection of a tube point is `s · v`. -/
theorem meridVec_tubePt {u v : Circle} {s : ℝ} (h : 0 < 2 + s * (v : ℂ).re) :
    meridVec (tubePt u v s) = (s : ℂ) * (v : ℂ) := by
  have hr := horizRadius_tubePt (u := u) (v := v) (s := s) h
  apply Complex.ext <;> simp [meridVec, hr, Complex.mul_re, Complex.mul_im]

/-- The meridian radius of a tube point is `|s|`. -/
theorem norm_meridVec_tubePt {u v : Circle} {s : ℝ} (h : 0 < 2 + s * (v : ℂ).re) :
    ‖meridVec (tubePt u v s)‖ = |s| := by
  rw [meridVec_tubePt h, Complex.norm_mul, Complex.norm_real, Real.norm_eq_abs,
    norm_coe_circle, mul_one]

/-- The horizontal radius of a tube point is positive when `s < 2`. -/
theorem two_add_mul_re_pos {v : Circle} {s : ℝ} (h0 : 0 < s) (h2 : s < 2) :
    0 < 2 + s * (v : ℂ).re := by
  have h := neg_one_le_re_circle v
  nlinarith [mul_le_mul_of_nonneg_left h (le_of_lt h0)]

/-! ## The tube coordinates of a point -/

/-- **The tube coordinates of a point `x` with `horizVec x ≠ 0` and `meridVec x ≠ 0` recover
`x`**: the point at longitude `horizVec x / ‖horizVec x‖`, meridian direction
`meridVec x / ‖meridVec x‖` and meridian radius `‖meridVec x‖` is `x`. -/
theorem tubePt_reconstruct (X : R3) (h1 : horizVec X ≠ 0) (h2 : meridVec X ≠ 0) :
    tubePt (normCircle (horizVec X) h1)
      (normCircle (meridVec X) h2) ‖meridVec X‖ = X := by
  have hsne : ((‖meridVec X‖ : ℝ) : ℂ) ≠ 0 :=
    Complex.ofReal_ne_zero.mpr (norm_ne_zero_iff.mpr h2)
  have hu : (((‖horizVec X‖ : ℝ)) : ℂ) *
      (normCircle (horizVec X) h1 : ℂ) = horizVec X := by
    rw [normCircle_coe, mul_div_assoc',
      mul_div_cancel_left₀ (horizVec X)
        (Complex.ofReal_ne_zero.mpr (norm_ne_zero_iff.mpr h1))]
  have hv : (((‖meridVec X‖ : ℝ)) : ℂ) *
      (normCircle (meridVec X) h2 : ℂ) = meridVec X := by
    rw [normCircle_coe, mul_div_assoc',
      mul_div_cancel_left₀ (meridVec X)
        (Complex.ofReal_ne_zero.mpr (norm_ne_zero_iff.mpr h2))]
  have hure := congrArg Complex.re hu
  have huim := congrArg Complex.im hu
  have hvre := congrArg Complex.re hv
  have hvim := congrArg Complex.im hv
  simp only [Complex.mul_re, Complex.ofReal_re, Complex.ofReal_im, zero_mul, sub_zero] at hure hvre
  simp only [Complex.mul_im, Complex.ofReal_re, Complex.ofReal_im, zero_mul, add_zero] at huim hvim
  rw [norm_horizVec, horizVec_re] at hure
  rw [norm_horizVec, horizVec_im] at huim
  rw [meridVec_re] at hvre
  rw [meridVec_im] at hvim
  have hkey : (2 : ℝ) + ‖meridVec X‖ *
      (normCircle (meridVec X) h2 : ℂ).re = horizRadius X := by
    rw [hvre]; ring
  rw [WithLp.ext_iff]
  funext i
  fin_cases i
  · show (2 + ‖meridVec X‖ * (normCircle (meridVec X) h2 : ℂ).re) *
      (normCircle (horizVec X) h1 : ℂ).re = X 0
    rw [hkey]; exact hure
  · show (2 + ‖meridVec X‖ * (normCircle (meridVec X) h2 : ℂ).re) *
      (normCircle (horizVec X) h1 : ℂ).im = X 1
    rw [hkey]; exact huim
  · show ‖meridVec X‖ * (normCircle (meridVec X) h2 : ℂ).im = X 2
    exact hvim

/-- `normCircle` does not depend on the proof of non-vanishing. -/
theorem normCircle_proof_irrel (w : ℂ) (h1 h2 : w ≠ 0) :
    normCircle w h1 = normCircle w h2 := Subtype.ext rfl

/-- The longitude of a tube point is its longitude. -/
theorem normCircle_horizVec_tubePt {u v : Circle} {s : ℝ} (h : 0 < 2 + s * (v : ℂ).re)
    {hw : horizVec (tubePt u v s) ≠ 0} :
    normCircle (horizVec (tubePt u v s)) hw = u := by
  apply Subtype.ext
  rw [normCircle_coe, horizVec_tubePt, Complex.norm_mul, Complex.norm_real, Real.norm_eq_abs,
    abs_of_pos h, norm_coe_circle, mul_one,
    mul_div_cancel_left₀ (u : ℂ) (Complex.ofReal_ne_zero.mpr (ne_of_gt h))]

/-- The meridian direction of a tube point is its meridian direction. -/
theorem normCircle_meridVec_tubePt {u v : Circle} {s : ℝ} (h : 0 < 2 + s * (v : ℂ).re)
    (hs : 0 < s) {hw : meridVec (tubePt u v s) ≠ 0} :
    normCircle (meridVec (tubePt u v s)) hw = v := by
  apply Subtype.ext
  rw [normCircle_coe, meridVec_tubePt h, Complex.norm_mul, Complex.norm_real, Real.norm_eq_abs,
    abs_of_pos hs, norm_coe_circle, mul_one,
    mul_div_cancel_left₀ (v : ℂ) (Complex.ofReal_ne_zero.mpr (ne_of_gt hs))]

/-! ## The regular-neighbourhood region -/

/-- **The tube region**: the punctured open solid torus of meridian radius `2`.  It is an open
neighbourhood of the standard torus, and on it the tube coordinates are a product
`S¹ × S¹ × (0,2)`. -/
def tubeU : Set R3 := {X | 0 < ‖meridVec X‖ ∧ ‖meridVec X‖ < 2}

theorem mem_tubeU_iff {X : R3} :
    X ∈ tubeU ↔ 0 < ‖meridVec X‖ ∧ ‖meridVec X‖ < 2 := Iff.rfl

theorem isOpen_tubeU : IsOpen tubeU := by
  refine IsOpen.inter ?_ ?_
  · exact isOpen_Ioi.preimage continuous_meridVec.norm
  · exact isOpen_Iio.preimage continuous_meridVec.norm

/-- The standard torus lies in the tube region. -/
theorem carrier_subset_tubeU : standard.carrier ⊆ tubeU := by
  intro a ha
  have h : ‖meridVec a‖ = 1 := norm_meridVec_eq_one_iff.mpr ha
  refine ⟨by rw [h]; norm_num, by rw [h]; norm_num⟩

/-- On the standard torus the horizontal radius is at least `1`. -/
theorem one_le_horizRadius_of_mem_carrier {a : R3}
    (ha : a ∈ standard.carrier) : 1 ≤ horizRadius a := by
  have h := (mem_carrier_iff_torusHeight_eq_one).mp ha
  rw [torusHeight_apply] at h
  have h2 : (horizRadius a - 2) ^ 2 ≤ (1 : ℝ) ^ 2 := by
    nlinarith [sq_nonneg (a 2)]
  have h3 : |horizRadius a - 2| ≤ 1 := by
    have := (sq_le_sq).mp h2
    simpa using this
  linarith [(abs_le.mp h3).1]

/-- On the tube region the horizontal radius is positive. -/
theorem horizRadius_pos_of_mem_tubeU {X : R3} (hX : X ∈ tubeU) : 0 < horizRadius X := by
  have h : ‖meridVec X‖ ^ 2 < 4 := by
    nlinarith [norm_nonneg (meridVec X), hX.2]
  rw [norm_meridVec_sq, torusHeight_apply] at h
  by_contra hc
  push_neg at hc
  have hρ : horizRadius X = 0 := le_antisymm hc (horizRadius_nonneg X)
  rw [hρ] at h
  nlinarith [sq_nonneg (X 2)]

theorem horizVec_ne_zero_of_mem_tubeU {X : R3} (hX : X ∈ tubeU) : horizVec X ≠ 0 :=
  (horizVec_ne_zero_iff X).mpr (ne_of_gt (horizRadius_pos_of_mem_tubeU hX))

theorem meridVec_ne_zero_of_mem_tubeU {X : R3} (hX : X ∈ tubeU) : meridVec X ≠ 0 :=
  norm_ne_zero_iff.mp (ne_of_gt hX.1)

theorem horizVec_ne_zero_of_mem_carrier {a : R3}
    (ha : a ∈ standard.carrier) : horizVec a ≠ 0 := by
  refine (horizVec_ne_zero_iff a).mpr ?_
  have h := one_le_horizRadius_of_mem_carrier ha
  linarith

theorem meridVec_ne_zero_of_mem_carrier {a : R3}
    (ha : a ∈ standard.carrier) : meridVec a ≠ 0 :=
  norm_ne_zero_iff.mp (by
    rw [norm_meridVec_eq_one_iff.mpr ha]; norm_num)

/-! ## Tube points of the standard torus and of the tube region -/

/-- A tube point of meridian radius `1` lies on the standard torus. -/
theorem tubePt_one_mem_carrier (u v : Circle) :
    tubePt u v 1 ∈ standard.carrier := by
  rw [← norm_meridVec_eq_one_iff,
    norm_meridVec_tubePt (u := u) (v := v) (s := 1)
      (two_add_mul_re_pos (v := v) (s := 1) one_pos one_lt_two)]
  simp

/-- A tube point of meridian radius `s ∈ (0,2)` lies in the tube region. -/
theorem tubePt_mem_tubeU {u v : Circle} {s : ℝ} (h0 : 0 < s) (h2 : s < 2) :
    tubePt u v s ∈ tubeU := by
  have h := two_add_mul_re_pos (v := v) (s := s) h0 h2
  rw [mem_tubeU_iff, norm_meridVec_tubePt h, abs_of_pos h0]
  exact ⟨h0, h2⟩

/-! ## Continuity -/

theorem continuous_tubePt :
    Continuous (fun p : Circle × Circle × ℝ => tubePt p.1 p.2.1 p.2.2) := by
  have h : Continuous (fun p : Circle × Circle × ℝ => fun i : Fin 3 =>
      (if i.val = 0 then (2 + p.2.2 * (p.2.1 : ℂ).re) * (p.1 : ℂ).re
       else if i.val = 1 then (2 + p.2.2 * (p.2.1 : ℂ).re) * (p.1 : ℂ).im
       else p.2.2 * (p.2.1 : ℂ).im : ℝ)) := by
    apply continuous_pi
    intro i
    fin_cases i <;> simp <;> fun_prop
  exact (PiLp.continuous_toLp (p := 2) (β := fun _ : Fin 3 => ℝ)).comp h

/-! ## The tube-coordinate homeomorphism -/

/-- The tube coordinates of a point of the tube region: longitude, meridian direction and
meridian radius. -/
def tubeCoordFun (X : tubeU) : (Circle × Circle) × Set.Ioo (0 : ℝ) 2 :=
  ((normCircle (horizVec (X : R3)) (horizVec_ne_zero_of_mem_tubeU X.2),
    normCircle (meridVec (X : R3)) (meridVec_ne_zero_of_mem_tubeU X.2)),
   ⟨‖meridVec (X : R3)‖, X.2⟩)

/-- The inverse of the tube coordinates: `(u, v, s) ↦ tubePt u v s`. -/
def tubeCoordInv (q : (Circle × Circle) × Set.Ioo (0 : ℝ) 2) : tubeU :=
  ⟨tubePt q.1.1 q.1.2 (q.2 : ℝ), tubePt_mem_tubeU q.2.2.1 q.2.2.2⟩

theorem tubeCoord_left_inv (X : tubeU) : tubeCoordInv (tubeCoordFun X) = X := by
  apply Subtype.ext
  exact tubePt_reconstruct (X : R3) (horizVec_ne_zero_of_mem_tubeU X.2)
    (meridVec_ne_zero_of_mem_tubeU X.2)

theorem tubeCoord_right_inv (q : (Circle × Circle) × Set.Ioo (0 : ℝ) 2) :
    tubeCoordFun (tubeCoordInv q) = q := by
  obtain ⟨⟨u, v⟩, s⟩ := q
  have h := two_add_mul_re_pos (v := v) (s := (s : ℝ)) s.2.1 s.2.2
  have h1 : normCircle (horizVec (tubePt u v (s : ℝ)))
      (horizVec_ne_zero_of_mem_tubeU (tubePt_mem_tubeU s.2.1 s.2.2)) = u :=
    normCircle_horizVec_tubePt h
  have h2 : normCircle (meridVec (tubePt u v (s : ℝ)))
      (meridVec_ne_zero_of_mem_tubeU (tubePt_mem_tubeU s.2.1 s.2.2)) = v :=
    normCircle_meridVec_tubePt h s.2.1
  have h3 : (⟨‖meridVec (tubePt u v (s : ℝ))‖,
      tubePt_mem_tubeU s.2.1 s.2.2⟩ : Set.Ioo (0 : ℝ) 2) = s := by
    apply Subtype.ext
    show ‖meridVec (tubePt u v (s : ℝ))‖ = (s : ℝ)
    rw [norm_meridVec_tubePt h, abs_of_pos s.2.1]
  simp only [tubeCoordFun, tubeCoordInv]
  rw [h1, h2, h3]

theorem continuous_tubeCoordFun : Continuous tubeCoordFun := by
  refine Continuous.prodMk (Continuous.prodMk ?_ ?_) ?_
  · exact continuous_normCircle (fun X : tubeU => horizVec (X : R3))
      (continuous_horizVec.comp continuous_subtype_val)
      (fun X => horizVec_ne_zero_of_mem_tubeU X.2)
  · exact continuous_normCircle (fun X : tubeU => meridVec (X : R3))
      (continuous_meridVec.comp continuous_subtype_val)
      (fun X => meridVec_ne_zero_of_mem_tubeU X.2)
  · exact Continuous.subtype_mk (continuous_meridVec.norm.comp continuous_subtype_val)
      (fun X => X.2)

theorem continuous_tubeCoordInv : Continuous tubeCoordInv := by
  refine Continuous.subtype_mk ?_ (fun q => tubePt_mem_tubeU q.2.2.1 q.2.2.2)
  have hcont : Continuous fun q : (Circle × Circle) × Set.Ioo (0 : ℝ) 2 =>
      (q.1.1, q.1.2, (q.2 : ℝ)) := by
    refine Continuous.prodMk ?_ (Continuous.prodMk ?_ ?_)
    · exact continuous_fst.comp continuous_fst
    · exact continuous_snd.comp continuous_fst
    · exact continuous_subtype_val.comp continuous_snd
  exact continuous_tubePt.comp hcont

/-- **The tube coordinates of a point of the tube region**: the longitude, the meridian
direction and the meridian radius give a homeomorphism `tubeU ≃ₜ (S¹ × S¹) × (0,2)`, whose
inverse is `(u, v, s) ↦ tubePt u v s`. -/
noncomputable def tubeCoord : tubeU ≃ₜ (Circle × Circle) × Set.Ioo (0 : ℝ) 2 where
  toFun := tubeCoordFun
  invFun := tubeCoordInv
  left_inv := tubeCoord_left_inv
  right_inv := tubeCoord_right_inv
  continuous_toFun := continuous_tubeCoordFun
  continuous_invFun := continuous_tubeCoordInv

@[simp] theorem tubeCoord_apply (X : tubeU) :
    tubeCoord X =
      ((normCircle (horizVec (X : R3)) (horizVec_ne_zero_of_mem_tubeU X.2),
        normCircle (meridVec (X : R3)) (meridVec_ne_zero_of_mem_tubeU X.2)),
       ⟨‖meridVec (X : R3)‖, X.2⟩) := rfl

@[simp] theorem tubeCoord_symm_apply (q : (Circle × Circle) × Set.Ioo (0 : ℝ) 2) :
    ((tubeCoord.symm q : tubeU) : R3) = tubePt q.1.1 q.1.2 (q.2 : ℝ) := rfl

/-! ## The homeomorphism `(0,2) ≅ ℝ` -/

/-- The point of `(0,2)` whose logarithm parameter is `t`: the inverse of
`s ↦ log s - log (2 - s)`. -/
def iooPoint (t : ℝ) : Set.Ioo (0 : ℝ) 2 :=
  ⟨2 * Real.exp t / (1 + Real.exp t), by
    refine ⟨by positivity, ?_⟩
    rw [div_lt_iff₀ (by positivity : (0:ℝ) < 1 + Real.exp t)]
    nlinarith [Real.exp_pos t]⟩

@[simp] theorem iooPoint_coe (t : ℝ) :
    ((iooPoint t : Set.Ioo (0 : ℝ) 2) : ℝ) = 2 * Real.exp t / (1 + Real.exp t) := rfl

/-- **The interval `(0,2)` is homeomorphic to `ℝ`**, via `s ↦ log s - log (2 - s)`. -/
noncomputable def iooHomeo : Set.Ioo (0 : ℝ) 2 ≃ₜ ℝ where
  toFun s := Real.log (s : ℝ) - Real.log (2 - (s : ℝ))
  invFun := iooPoint
  left_inv s := by
    refine Subtype.ext ?_
    have h1 : 0 < (s : ℝ) := s.2.1
    have h2 : 0 < 2 - (s : ℝ) := by linarith [s.2.2]
    rw [iooPoint_coe, Real.exp_sub, Real.exp_log h1, Real.exp_log h2]
    field_simp <;> ring
  right_inv t := by
    show Real.log (iooPoint t : ℝ) - Real.log (2 - (iooPoint t : ℝ)) = t
    rw [iooPoint_coe]
    have h2 : 2 - 2 * Real.exp t / (1 + Real.exp t) = 2 / (1 + Real.exp t) := by
      field_simp <;> ring
    rw [h2, ← Real.log_div (by positivity) (by positivity)]
    have h3 : 2 * Real.exp t / (1 + Real.exp t) / (2 / (1 + Real.exp t)) = Real.exp t := by
      field_simp <;> ring
    rw [h3, Real.log_exp]
  continuous_toFun := by
    have h1 : Continuous fun s : Set.Ioo (0 : ℝ) 2 => Real.log (s : ℝ) :=
      Continuous.log continuous_subtype_val (fun s => ne_of_gt s.2.1)
    have h2 : Continuous fun s : Set.Ioo (0 : ℝ) 2 => Real.log (2 - (s : ℝ)) :=
      Continuous.log (continuous_const.sub continuous_subtype_val)
        (fun s => ne_of_gt (by linarith [s.2.2] : (0 : ℝ) < 2 - s))
    exact h1.sub h2
  continuous_invFun := by
    refine Continuous.subtype_mk (f := fun t : ℝ => 2 * Real.exp t / (1 + Real.exp t)) ?_
      (fun t => (iooPoint t).2)
    exact (continuous_const.mul Real.continuous_exp).div
      (continuous_const.add Real.continuous_exp) (fun t => by positivity)

/-! ## Elementary facts about `iooHomeo` -/

@[simp] theorem iooHomeo_apply (s : Set.Ioo (0 : ℝ) 2) :
    iooHomeo s = Real.log (s : ℝ) - Real.log (2 - (s : ℝ)) := rfl

theorem iooHomeo_one : iooHomeo ⟨1, by norm_num⟩ = 0 := by
  rw [iooHomeo_apply]
  norm_num

/-- The normal coordinate `log s - log (2 - s)` vanishes exactly at `s = 1`. -/
theorem iooHomeo_eq_zero_iff (s : Set.Ioo (0 : ℝ) 2) :
    iooHomeo s = 0 ↔ (s : ℝ) = 1 := by
  constructor
  · intro h
    have h' : s = ⟨1, by norm_num⟩ := iooHomeo.injective (by rw [h, iooHomeo_one])
    exact congrArg Subtype.val h'
  · intro h
    rw [show s = ⟨1, by norm_num⟩ from Subtype.ext h, iooHomeo_one]

theorem iooHomeo_symm_apply (t : ℝ) :
    ((iooHomeo.symm t : Set.Ioo (0 : ℝ) 2) : ℝ) = 2 * Real.exp t / (1 + Real.exp t) := rfl

/-! ## The standard torus as `S¹ × S¹` -/

/-- The parametrisation `S¹ × S¹ → Σ`, `(u, v) ↦ tubePt u v 1`, as a map onto the carrier. -/
def circleTorusFun (p : Circle × Circle) : standard.carrier :=
  ⟨tubePt p.1 p.2 1, tubePt_one_mem_carrier p.1 p.2⟩

/-- The parameters of a point of the standard torus: its longitude and its meridian direction. -/
def circleTorusInv (a : standard.carrier) : Circle × Circle :=
  (normCircle (horizVec (a : R3)) (horizVec_ne_zero_of_mem_carrier a.2),
   normCircle (meridVec (a : R3)) (meridVec_ne_zero_of_mem_carrier a.2))

theorem circleTorus_left_inv (p : Circle × Circle) :
    circleTorusInv (circleTorusFun p) = p := by
  obtain ⟨u, v⟩ := p
  have h := two_add_mul_re_pos (v := v) (s := 1) one_pos one_lt_two
  refine Prod.ext ?_ ?_
  · show normCircle (horizVec (tubePt u v 1))
      (horizVec_ne_zero_of_mem_tubeU (tubePt_mem_tubeU one_pos one_lt_two)) = u
    exact normCircle_horizVec_tubePt h
  · show normCircle (meridVec (tubePt u v 1))
      (meridVec_ne_zero_of_mem_tubeU (tubePt_mem_tubeU one_pos one_lt_two)) = v
    exact normCircle_meridVec_tubePt h one_pos

theorem circleTorus_right_inv (a : standard.carrier) :
    circleTorusFun (circleTorusInv a) = a := by
  have h1 : horizVec (a : R3) ≠ 0 := horizVec_ne_zero_of_mem_carrier a.2
  have h2 : meridVec (a : R3) ≠ 0 := meridVec_ne_zero_of_mem_carrier a.2
  have h3 : ‖meridVec (a : R3)‖ = 1 := norm_meridVec_eq_one_iff.mpr a.2
  have key := tubePt_reconstruct (a : R3) h1 h2
  rw [h3] at key
  refine Subtype.ext ?_
  show tubePt (normCircle (horizVec (a : R3)) h1) (normCircle (meridVec (a : R3)) h2) 1 = (a : R3)
  exact key

theorem continuous_circleTorusFun : Continuous circleTorusFun := by
  refine Continuous.subtype_mk ?_ (fun p : Circle × Circle => tubePt_one_mem_carrier p.1 p.2)
  exact continuous_tubePt.comp
    (Continuous.prodMk continuous_fst (Continuous.prodMk continuous_snd continuous_const))

theorem continuous_circleTorusInv : Continuous circleTorusInv := by
  refine Continuous.prodMk ?_ ?_
  · exact continuous_normCircle (fun a : standard.carrier => horizVec (a : R3))
      (continuous_horizVec.comp continuous_subtype_val)
      (fun a => horizVec_ne_zero_of_mem_carrier a.2)
  · exact continuous_normCircle (fun a : standard.carrier => meridVec (a : R3))
      (continuous_meridVec.comp continuous_subtype_val)
      (fun a => meridVec_ne_zero_of_mem_carrier a.2)

/-- **The standard torus is `S¹ × S¹`**: the parametrisation `(u, v) ↦ tubePt u v 1` is a
homeomorphism onto `standard.carrier`. -/
noncomputable def circleTorusHomeo : (Circle × Circle) ≃ₜ standard.carrier where
  toFun := circleTorusFun
  invFun := circleTorusInv
  left_inv := circleTorus_left_inv
  right_inv := circleTorus_right_inv
  continuous_toFun := continuous_circleTorusFun
  continuous_invFun := continuous_circleTorusInv

@[simp] theorem circleTorusHomeo_apply (u v : Circle) :
    ((circleTorusHomeo (u, v)) : R3) = tubePt u v 1 := rfl

end

end Work.Bicollar
