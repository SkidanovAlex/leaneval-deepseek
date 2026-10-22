/-
Copyright (c) 2026. All rights reserved.
Released under Apache 2.0 license.
-/
import Mathlib
import Submission.Work.CWTOP.Closed

/-!
# The band of a model sphere is homotopy equivalent to the model sphere

The norm on `Fin k → ℝ` that is in force in this development is the sup norm, so the model sphere
`modelSphere (n + 1) = {y | ‖y‖ = 1}` is the boundary of the cube `[-1,1]^{n+2}`.  This file
studies the *band*

`band n = {y : modelSphere (n + 1) // y 0 < 1 ∧ -1 < y 0}`,

that is, that boundary with the two faces `y 0 = 1` and `y 0 = -1` removed, and shows that it is
homotopy equivalent to the model sphere `modelSphere n` of one dimension less.

Since the first coordinate of a point of the band has absolute value `< 1`, its tail (the remaining
`n + 1` coordinates) already has sup norm `1`.  Hence dropping the first coordinate is a well
defined map `band n → modelSphere n`, and prepending a `0` is a section of it.  The band
deformation retracts onto its equator `y 0 = 0` — the image of the second map — by scaling the
first coordinate to `0`; this provides the two homotopies.
-/

open CategoryTheory Topology Set Function Metric
open scoped unitInterval

noncomputable section

namespace Work.CWTOP

/-- The band of `modelSphere (n + 1)`: the points whose first coordinate is strictly between `-1`
and `1`. -/
abbrev band (n : ℕ) := {y : modelSphere (n + 1) // y.1 0 < 1 ∧ -1 < y.1 0}

/-! ## §1 Norms in the sup norm on `Fin k → ℝ` -/

@[simp] lemma fin_tail_apply {n : ℕ} {α : Type*} (q : Fin (n + 1) → α) (i : Fin n) :
    Fin.tail q i = q i.succ := rfl

lemma mem_modelSphere_iff {n : ℕ} {f : Fin (n + 1) → ℝ} : f ∈ modelSphere n ↔ ‖f‖ = 1 := by
  rw [modelSphere, Metric.mem_sphere, dist_eq_norm, sub_zero]

lemma norm_coe_modelSphere {n : ℕ} (y : modelSphere n) : ‖(y.1 : Fin (n + 1) → ℝ)‖ = 1 :=
  mem_modelSphere_iff.mp y.2

lemma abs_coe_band_lt_one {n : ℕ} (y : band n) : |(y.1.1 : Fin (n + 2) → ℝ) 0| < 1 :=
  abs_lt.mpr ⟨y.2.2, y.2.1⟩

lemma abs_mul_le_of_mem_Icc {t x : ℝ} (ht0 : 0 ≤ t) (ht1 : t ≤ 1) : |t * x| ≤ |x| := by
  calc |t * x| = t * |x| := by rw [abs_mul, abs_of_nonneg ht0]
    _ ≤ 1 * |x| := mul_le_mul_of_nonneg_right ht1 (abs_nonneg x)
    _ = |x| := one_mul _

lemma exists_norm_apply_eq_norm {n : ℕ} (f : Fin (n + 1) → ℝ) : ∃ i, ‖f i‖ = ‖f‖ := by
  haveI : Nonempty (Fin (n + 1)) := ⟨0⟩
  exact (IsGreatest.pi_norm f).1

/-- A vector of sup norm `1` whose first coordinate has absolute value `< 1` has one of its last
`n + 1` coordinates of absolute value `1`. -/
lemma exists_succ_abs_eq_one {n : ℕ} {f : Fin (n + 2) → ℝ} (hf : ‖f‖ = 1) (h0 : |f 0| < 1) :
    ∃ j : Fin (n + 1), |f j.succ| = 1 := by
  obtain ⟨i, hi⟩ := exists_norm_apply_eq_norm f
  have hi0 : i ≠ 0 := by
    rintro rfl
    rw [Real.norm_eq_abs, hf] at hi
    exact absurd hi (ne_of_lt h0)
  obtain ⟨j, hj⟩ := Fin.exists_succ_eq.mpr hi0
  exact ⟨j, by rw [hj, ← Real.norm_eq_abs, hi, hf]⟩

/-- The tail of a vector of sup norm `1` whose first coordinate has absolute value `< 1` again has
sup norm `1`. -/
lemma norm_tail_of_norm_eq_one {n : ℕ} {f : Fin (n + 2) → ℝ} (hf : ‖f‖ = 1) (h0 : |f 0| < 1) :
    ‖(Fin.tail f : Fin (n + 1) → ℝ)‖ = 1 := by
  refine le_antisymm ?_ ?_
  · rw [pi_norm_le_iff_of_nonneg (by norm_num : (0 : ℝ) ≤ 1)]
    intro i
    exact (norm_le_pi_norm f i.succ).trans (le_of_eq hf)
  · obtain ⟨j, hj⟩ := exists_succ_abs_eq_one hf h0
    have h1 : ‖(Fin.tail f : Fin (n + 1) → ℝ) j‖ = 1 := by
      simpa [Real.norm_eq_abs] using hj
    exact le_trans (le_of_eq h1.symm) (norm_le_pi_norm (Fin.tail f : Fin (n + 1) → ℝ) j)

/-- Prepending a zero to a vector of sup norm `1` again gives a vector of sup norm `1`. -/
lemma norm_cons_zero_of_norm_eq_one {n : ℕ} {z : Fin (n + 1) → ℝ} (hz : ‖z‖ = 1) :
    ‖(Fin.cons (0 : ℝ) z : Fin (n + 2) → ℝ)‖ = 1 := by
  refine le_antisymm ?_ ?_
  · rw [pi_norm_le_iff_of_nonneg (by norm_num : (0 : ℝ) ≤ 1)]
    intro i
    by_cases hi : i = 0
    · rw [hi, Fin.cons_zero, Real.norm_eq_abs]
      norm_num
    · obtain ⟨j, hj⟩ := Fin.exists_succ_eq.mpr hi
      rw [← hj, Fin.cons_succ]
      exact (norm_le_pi_norm z j).trans (le_of_eq hz)
  · obtain ⟨j, hj⟩ := exists_norm_apply_eq_norm z
    have h1 : ‖(Fin.cons (0 : ℝ) z : Fin (n + 2) → ℝ) j.succ‖ = 1 := by
      rw [Fin.cons_succ]
      exact hj.trans hz
    exact le_trans (le_of_eq h1.symm)
      (norm_le_pi_norm (Fin.cons (0 : ℝ) z : Fin (n + 2) → ℝ) j.succ)

/-- Prepending a coordinate whose absolute value is at most that of the first coordinate of a
vector of sup norm `1` (the first coordinate itself having absolute value `< 1`) again gives sup
norm `1`. -/
lemma norm_cons_tail_of_le {n : ℕ} {f : Fin (n + 2) → ℝ} {c : ℝ} (hf : ‖f‖ = 1)
    (h0 : |f 0| < 1) (hc : |c| ≤ |f 0|) :
    ‖(Fin.cons c (Fin.tail f) : Fin (n + 2) → ℝ)‖ = 1 := by
  refine le_antisymm ?_ ?_
  · rw [pi_norm_le_iff_of_nonneg (by norm_num : (0 : ℝ) ≤ 1)]
    intro i
    by_cases hi : i = 0
    · rw [hi, Fin.cons_zero, Real.norm_eq_abs]
      exact le_of_lt (lt_of_le_of_lt hc h0)
    · obtain ⟨j, hj⟩ := Fin.exists_succ_eq.mpr hi
      rw [← hj, Fin.cons_succ]
      exact (norm_le_pi_norm f j.succ).trans (le_of_eq hf)
  · obtain ⟨j, hj⟩ := exists_succ_abs_eq_one hf h0
    have h1 : ‖(Fin.cons c (Fin.tail f) : Fin (n + 2) → ℝ) j.succ‖ = 1 := by
      rw [Fin.cons_succ]
      simpa [Real.norm_eq_abs] using hj
    exact le_trans (le_of_eq h1.symm)
      (norm_le_pi_norm (Fin.cons c (Fin.tail f) : Fin (n + 2) → ℝ) j.succ)

/-! ## §2 Continuity of the elementary constructions -/

lemma continuous_tail {n : ℕ} {Z : Type*} [TopologicalSpace Z] {f : Z → Fin (n + 1) → ℝ}
    (hf : Continuous f) : Continuous fun z => (Fin.tail (f z) : Fin n → ℝ) := by
  apply continuous_pi
  intro i
  exact (continuous_apply i.succ).comp hf

lemma continuous_cons {n : ℕ} {Z : Type*} [TopologicalSpace Z] {c : Z → ℝ}
    {f : Z → Fin n → ℝ} (hc : Continuous c) (hf : Continuous f) :
    Continuous fun z => (Fin.cons (c z) (f z) : Fin (n + 1) → ℝ) := by
  apply continuous_pi
  intro i
  by_cases hi : i = 0
  · rw [hi]
    have h : (fun z => (Fin.cons (c z) (f z) : Fin (n + 1) → ℝ) 0) = c := by
      funext z
      rw [Fin.cons_zero]
    rw [h]
    exact hc
  · obtain ⟨j, hj⟩ := Fin.exists_succ_eq.mpr hi
    rw [← hj]
    have h : (fun z => (Fin.cons (c z) (f z) : Fin (n + 1) → ℝ) j.succ) = fun z => f z j := by
      funext z
      rw [Fin.cons_succ]
    rw [h]
    exact (continuous_apply j).comp hf

/-! ## §3 The two maps -/

/-- Dropping the first coordinate: the projection of the band onto the model sphere. -/
def bandToSphereFun (n : ℕ) (y : band n) : modelSphere n :=
  ⟨(Fin.tail (y.1.1 : Fin (n + 2) → ℝ) : Fin (n + 1) → ℝ),
    mem_modelSphere_iff.mpr
      (norm_tail_of_norm_eq_one (norm_coe_modelSphere y.1) (abs_coe_band_lt_one y))⟩

@[simp] lemma bandToSphereFun_apply (n : ℕ) (y : band n) :
    (bandToSphereFun n y).1 = (Fin.tail (y.1.1 : Fin (n + 2) → ℝ) : Fin (n + 1) → ℝ) := rfl

/-- Dropping the first coordinate, as a continuous map. -/
def bandToSphere (n : ℕ) : C(band n, modelSphere n) where
  toFun := bandToSphereFun n
  continuous_toFun := by
    have hv : Continuous fun y : band n => (y.1.1 : Fin (n + 2) → ℝ) :=
      (continuous_subtype_val : Continuous (Subtype.val :
          modelSphere (n + 1) → Fin (n + 2) → ℝ)).comp
        (continuous_subtype_val : Continuous (Subtype.val : band n → modelSphere (n + 1)))
    refine Continuous.subtype_mk
      (f := fun y : band n => (Fin.tail (y.1.1 : Fin (n + 2) → ℝ) : Fin (n + 1) → ℝ))
      (continuous_tail hv) (fun y => (bandToSphereFun n y).2)

/-- Prepending a `0`: the inclusion of the model sphere as the equator of the band. -/
def sphereToBandFun (n : ℕ) (z : modelSphere n) : band n :=
  ⟨⟨(Fin.cons (0 : ℝ) z.1 : Fin (n + 2) → ℝ),
      mem_modelSphere_iff.mpr (norm_cons_zero_of_norm_eq_one (norm_coe_modelSphere z))⟩,
    by
      constructor
      · show (Fin.cons (0 : ℝ) z.1 : Fin (n + 2) → ℝ) 0 < 1
        rw [Fin.cons_zero]
        norm_num
      · show -1 < (Fin.cons (0 : ℝ) z.1 : Fin (n + 2) → ℝ) 0
        rw [Fin.cons_zero]
        norm_num⟩

@[simp] lemma sphereToBandFun_apply (n : ℕ) (z : modelSphere n) :
    (sphereToBandFun n z).1.1 = (Fin.cons (0 : ℝ) z.1 : Fin (n + 2) → ℝ) := rfl

/-- Prepending a `0`, as a continuous map. -/
def sphereToBand (n : ℕ) : C(modelSphere n, band n) where
  toFun := sphereToBandFun n
  continuous_toFun := by
    have hz : Continuous fun z : modelSphere n => (z.1 : Fin (n + 1) → ℝ) :=
      (continuous_subtype_val : Continuous (Subtype.val : modelSphere n → Fin (n + 1) → ℝ))
    have hsphere : ∀ z : modelSphere n,
        (Fin.cons (0 : ℝ) z.1 : Fin (n + 2) → ℝ) ∈ modelSphere (n + 1) :=
      fun z => mem_modelSphere_iff.mpr (norm_cons_zero_of_norm_eq_one (norm_coe_modelSphere z))
    have hinner : Continuous fun z : modelSphere n =>
        (⟨(Fin.cons (0 : ℝ) z.1 : Fin (n + 2) → ℝ), hsphere z⟩ : modelSphere (n + 1)) :=
      Continuous.subtype_mk (continuous_cons continuous_const hz) hsphere
    refine Continuous.subtype_mk
      (f := fun z : modelSphere n =>
        (⟨(Fin.cons (0 : ℝ) z.1 : Fin (n + 2) → ℝ), hsphere z⟩ : modelSphere (n + 1)))
      hinner (fun z => (sphereToBandFun n z).2)

/-- Dropping the first coordinate after prepending a `0` is the identity. -/
theorem bandToSphere_comp_sphereToBand (n : ℕ) :
    (bandToSphere n).comp (sphereToBand n) = ContinuousMap.id (modelSphere n) := by
  apply ContinuousMap.ext
  intro z
  apply Subtype.ext
  show (Fin.tail (Fin.cons (0 : ℝ) z.1 : Fin (n + 2) → ℝ) : Fin (n + 1) → ℝ)
      = (z.1 : Fin (n + 1) → ℝ)
  rw [Fin.tail_cons]

/-! ## §4 The deformation retraction onto the equator -/

/-- The deformation of the band onto its equator: the first coordinate is scaled by the parameter
of the interval, the others are kept. -/
def bandDeformationFun (n : ℕ) (p : unitInterval × band n) : band n :=
  ⟨⟨(Fin.cons ((p.1 : ℝ) * ((p.2 : band n).1.1 : Fin (n + 2) → ℝ) 0)
        (Fin.tail ((p.2 : band n).1.1 : Fin (n + 2) → ℝ)) : Fin (n + 2) → ℝ),
      mem_modelSphere_iff.mpr
        (norm_cons_tail_of_le (norm_coe_modelSphere p.2.1) (abs_coe_band_lt_one p.2)
          (abs_mul_le_of_mem_Icc p.1.2.1 p.1.2.2))⟩,
    by
      have hlt : |(p.1 : ℝ) * ((p.2 : band n).1.1 : Fin (n + 2) → ℝ) 0| < 1 :=
        lt_of_le_of_lt (abs_mul_le_of_mem_Icc p.1.2.1 p.1.2.2) (abs_coe_band_lt_one p.2)
      constructor
      · show (Fin.cons ((p.1 : ℝ) * ((p.2 : band n).1.1 : Fin (n + 2) → ℝ) 0)
            (Fin.tail ((p.2 : band n).1.1 : Fin (n + 2) → ℝ)) : Fin (n + 2) → ℝ) 0 < 1
        rw [Fin.cons_zero]
        exact (abs_lt.mp hlt).2
      · show -1 < (Fin.cons ((p.1 : ℝ) * ((p.2 : band n).1.1 : Fin (n + 2) → ℝ) 0)
            (Fin.tail ((p.2 : band n).1.1 : Fin (n + 2) → ℝ)) : Fin (n + 2) → ℝ) 0
        rw [Fin.cons_zero]
        exact (abs_lt.mp hlt).1⟩

@[simp] lemma bandDeformationFun_apply (n : ℕ) (p : unitInterval × band n) :
    (bandDeformationFun n p).1.1
      = (Fin.cons ((p.1 : ℝ) * ((p.2 : band n).1.1 : Fin (n + 2) → ℝ) 0)
          (Fin.tail ((p.2 : band n).1.1 : Fin (n + 2) → ℝ)) : Fin (n + 2) → ℝ) := rfl

/-- The deformation of the band onto its equator, as a continuous map. -/
def bandDeformation (n : ℕ) : C(unitInterval × band n, band n) where
  toFun := bandDeformationFun n
  continuous_toFun := by
    have hvec : Continuous fun p : unitInterval × band n =>
        ((p.2 : band n).1.1 : Fin (n + 2) → ℝ) :=
      (continuous_subtype_val : Continuous (Subtype.val :
          modelSphere (n + 1) → Fin (n + 2) → ℝ)).comp
        ((continuous_subtype_val : Continuous (Subtype.val : band n → modelSphere (n + 1))).comp
          continuous_snd)
    have ht : Continuous fun p : unitInterval × band n => (p.1 : ℝ) :=
      (continuous_subtype_val : Continuous (Subtype.val : unitInterval → ℝ)).comp continuous_fst
    have hc : Continuous fun p : unitInterval × band n =>
        (p.1 : ℝ) * ((p.2 : band n).1.1 : Fin (n + 2) → ℝ) 0 :=
      ht.mul ((continuous_apply (0 : Fin (n + 2))).comp hvec)
    have hsphere : ∀ p : unitInterval × band n,
        (Fin.cons ((p.1 : ℝ) * ((p.2 : band n).1.1 : Fin (n + 2) → ℝ) 0)
          (Fin.tail ((p.2 : band n).1.1 : Fin (n + 2) → ℝ)) : Fin (n + 2) → ℝ)
          ∈ modelSphere (n + 1) :=
      fun p => mem_modelSphere_iff.mpr
        (norm_cons_tail_of_le (norm_coe_modelSphere p.2.1) (abs_coe_band_lt_one p.2)
          (abs_mul_le_of_mem_Icc p.1.2.1 p.1.2.2))
    have hinner : Continuous fun p : unitInterval × band n =>
        (⟨(Fin.cons ((p.1 : ℝ) * ((p.2 : band n).1.1 : Fin (n + 2) → ℝ) 0)
            (Fin.tail ((p.2 : band n).1.1 : Fin (n + 2) → ℝ)) : Fin (n + 2) → ℝ),
          hsphere p⟩ : modelSphere (n + 1)) :=
      Continuous.subtype_mk (continuous_cons hc (continuous_tail hvec)) hsphere
    refine Continuous.subtype_mk
      (f := fun p : unitInterval × band n =>
        (⟨(Fin.cons ((p.1 : ℝ) * ((p.2 : band n).1.1 : Fin (n + 2) → ℝ) 0)
            (Fin.tail ((p.2 : band n).1.1 : Fin (n + 2) → ℝ)) : Fin (n + 2) → ℝ),
          hsphere p⟩ : modelSphere (n + 1))) hinner (fun p => (bandDeformationFun n p).2)

/-- The deformation is a homotopy from `sphereToBand ∘ bandToSphere` to the identity of the
band. -/
def bandDeformationHomotopy (n : ℕ) :
    ContinuousMap.Homotopy ((sphereToBand n).comp (bandToSphere n))
      (ContinuousMap.id (band n)) where
  toContinuousMap := bandDeformation n
  map_zero_left y := by
    change bandDeformationFun n (0, y) = sphereToBandFun n (bandToSphereFun n y)
    apply Subtype.ext
    apply Subtype.ext
    simp only [bandDeformationFun_apply, sphereToBandFun_apply, bandToSphereFun_apply,
      Set.Icc.coe_zero, zero_mul]
  map_one_left y := by
    change bandDeformationFun n (1, y) = y
    apply Subtype.ext
    apply Subtype.ext
    simp only [bandDeformationFun_apply, Set.Icc.coe_one, one_mul, Fin.cons_self_tail]

/-! ## §5 The homotopy equivalence -/

/-- The band is homotopy equivalent to the model sphere of one dimension less. -/
def bandHomotopyEquiv (n : ℕ) :
    ContinuousMap.HomotopyEquiv (TopCat.of (band n)) (TopCat.of (modelSphere n)) where
  toFun := bandToSphere n
  invFun := sphereToBand n
  left_inv := ⟨bandDeformationHomotopy n⟩
  right_inv := by rw [bandToSphere_comp_sphereToBand n]

theorem homotopyEquiv_band_modelSphere (n : ℕ) :
    Nonempty (ContinuousMap.HomotopyEquiv
      (TopCat.of {y : Work.CWTOP.modelSphere (n + 1) // y.1 0 < 1 ∧ -1 < y.1 0})
      (TopCat.of (Work.CWTOP.modelSphere n))) :=
  ⟨bandHomotopyEquiv n⟩

end Work.CWTOP
