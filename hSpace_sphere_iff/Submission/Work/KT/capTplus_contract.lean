/-
Copyright (c) 2025. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: hSpace_sphere_iff team
-/
import Mathlib
import Submission.Work.KT.Defs
import Submission.Work.KT.HopfK.Basic
import Submission.Work.KT.cap_arith

/-!
# The closed cap `{tgtHeight ≥ -1/2}` of `Tgt m = S^{2m}` is contractible

The cap `capTplus m = {tgtHeight ≥ -1/2}` of the sphere `Tgt m = S^{2m}` (the target of the Hopf
construction) is the sphere with an open disc of radius `1/2` around the south pole removed; it is
therefore a closed disc, in particular contractible.  Here we give an *explicit* contraction to an
arbitrary point `t0` of the cap.

In the model `WithLp 2 (Eu m × ℝ)` of `ℝ^{2m} × ℝ`, in which the height `tgtHeight` is the second
coordinate, a point `w` of the unit sphere of height `p ≥ -1/2` is moved along the normalized convex
combination

`s ↦ (s • (0,1) + (1 - s) • w) / ‖s • (0,1) + (1 - s) • w‖`

which starts at `w` (at `s = 0`, weights `α = 0`, `β = 1`) and ends at the north pole `(0,1)`
(at `s = 1`, weights `α = 1`, `β = 0`).  The estimate that this path never leaves the cap
(`cap_comb_height`) is exactly the arithmetic statement `cap_arith` of
`Submission/Work/KT/cap_arith.lean`.  Contracting to the north pole and then running the same path
from `t0` backwards gives the contraction of the cap to the arbitrary point `t0`.
-/

namespace Work.KT

open scoped Topology

noncomputable section

/-! ## The model space and the north pole -/

/-- The model space of `Tgt m`: `ℝ^{2m} × ℝ` with the `ℓ²`-norm, in which the height `tgtHeight` is
the second coordinate. -/
abbrev CapModel (m : ℕ) : Type := WithLp 2 (Eu m × ℝ)

/-- The vector `(0, 1)` of the model space: the "north pole" of the cap, of height `1`. -/
def northVec (m : ℕ) : CapModel m := WithLp.toLp 2 ((0 : Eu m), (1 : ℝ))

lemma norm_northVec (m : ℕ) : ‖northVec m‖ = 1 := by
  have h : ‖northVec m‖ ^ 2 = 1 := by
    rw [northVec, WithLp.prod_norm_sq_eq_of_L2]
    simp
  nlinarith [norm_nonneg (northVec m)]

/-- The north pole `(0,1)` of `Tgt m = S^{2m}`. -/
def northPt (m : ℕ) : Tgt m :=
  ⟨euclTgtIso m (northVec m), by
    rw [Metric.mem_sphere, dist_eq_norm, sub_zero, (euclTgtIso m).norm_map, norm_northVec m]⟩

lemma tgtHeight_northPt (m : ℕ) : tgtHeight m (northPt m) = 1 := by
  simp [tgtHeight, northPt, northVec]

lemma northPt_mem_capTplus (m : ℕ) : northPt m ∈ capTplus m := by
  show tgtHeight m (northPt m) ≥ -(1 / 2)
  rw [tgtHeight_northPt]
  norm_num

/-- The north pole, as a point of the cap. -/
def northCap (m : ℕ) : capTplus m := ⟨northPt m, northPt_mem_capTplus m⟩

/-! ## Model coordinates of a point of `Tgt m` -/

/-- The model coordinates of a point of `Tgt m`. -/
def tgtVec (m : ℕ) (x : Tgt m) : CapModel m :=
  (euclTgtIso m).symm (x : EuclideanSpace ℝ (Fin (2 * m + 1)))

lemma tgtVec_snd (m : ℕ) (x : Tgt m) : (tgtVec m x).snd = tgtHeight m x := rfl

lemma norm_tgtVec (m : ℕ) (x : Tgt m) : ‖tgtVec m x‖ = 1 := by
  have h := Metric.mem_sphere.mp x.2
  rw [dist_eq_norm, sub_zero] at h
  rw [tgtVec, ← (euclTgtIso m).norm_map
    ((euclTgtIso m).symm (x : EuclideanSpace ℝ (Fin (2 * m + 1)))),
    LinearIsometryEquiv.apply_symm_apply]
  exact h

/-- The point of `Tgt m` with prescribed model coordinates, of unit norm. -/
def tgtPt (m : ℕ) (z : CapModel m) (hz : ‖z‖ = 1) : Tgt m :=
  ⟨euclTgtIso m z, by
    rw [Metric.mem_sphere, dist_eq_norm, sub_zero, (euclTgtIso m).norm_map, hz]⟩

lemma tgtHeight_tgtPt (m : ℕ) (z : CapModel m) (hz : ‖z‖ = 1) :
    tgtHeight m (tgtPt m z hz) = z.snd := by
  simp [tgtHeight, tgtPt]

/-- The point of the cap with prescribed model coordinates and height `≥ -1/2`. -/
def capPt (m : ℕ) (z : CapModel m) (hz : ‖z‖ = 1) (hh : -(1 / 2) ≤ z.snd) : capTplus m :=
  ⟨tgtPt m z hz, by
    show tgtHeight m (tgtPt m z hz) ≥ -(1 / 2)
    rw [tgtHeight_tgtPt]
    exact hh⟩

/-! ## The normalized convex combination with the north pole -/

/-- The normalized convex combination, at time `s`, of a point `w` of the model space with the
north pole `(0,1)`. -/
def combPoint (m : ℕ) (w : CapModel m) (s : ℝ) : CapModel m :=
  unitV (s • northVec m + (1 - s) • w)

/-- **The key estimate**: if `w` is a point of the model sphere of height `≥ -1/2`, then the
normalized convex combination of `w` with the north pole is nonzero and again has height `≥ -1/2`;
this is the arithmetic content of the contractibility of the cap. -/
lemma cap_comb_height (m : ℕ) {w : CapModel m} (hw : ‖w‖ = 1) (hp : -(1 / 2) ≤ w.snd)
    {α β : ℝ} (hα : 0 ≤ α) (hβ : 0 ≤ β) (hαβ : α + β = 1) :
    0 < ‖α • northVec m + β • w‖ ∧ -(1 / 2) ≤ (unitV (α • northVec m + β • w)).snd := by
  have hw1 : ‖w.fst‖ ^ 2 + w.snd ^ 2 = 1 := by
    have h := WithLp.prod_norm_sq_eq_of_L2 w
    rw [hw] at h
    simpa [Real.norm_eq_abs, sq_abs] using h.symm
  have h1 : (α • northVec m + β • w).fst = β • w.fst := by simp [northVec]
  have h2 : (α • northVec m + β • w).snd = α + β * w.snd := by simp [northVec]
  have hnorm : ‖α • northVec m + β • w‖ ^ 2 =
      (β * ‖w.fst‖) ^ 2 + (α + β * w.snd) ^ 2 := by
    rw [WithLp.prod_norm_sq_eq_of_L2, h1, h2]
    simp only [norm_smul, Real.norm_of_nonneg hβ, Real.norm_eq_abs, sq_abs]
  have har := cap_arith (α := α) (β := β) (p := w.snd) (r := ‖w.fst‖) hα hβ hαβ hw1 hp
  have hD : ‖α • northVec m + β • w‖ =
      Real.sqrt ((β * ‖w.fst‖) ^ 2 + (α + β * w.snd) ^ 2) := by
    rw [← Real.sqrt_sq (norm_nonneg (α • northVec m + β • w)), hnorm]
  refine ⟨?_, ?_⟩
  · rw [hD]
    exact Real.sqrt_pos_of_pos har.1
  · have hsnd : (unitV (α • northVec m + β • w)).snd =
        ‖α • northVec m + β • w‖⁻¹ * (α + β * w.snd) := by
      show (‖α • northVec m + β • w‖⁻¹ • (α • northVec m + β • w)).snd =
        ‖α • northVec m + β • w‖⁻¹ * (α + β * w.snd)
      rw [WithLp.smul_snd, h2, smul_eq_mul]
    rw [hsnd, hD, le_inv_mul_iff₀ (Real.sqrt_pos_of_pos har.1)]
    linarith [har.2]

lemma combPoint_spec (m : ℕ) {w : CapModel m} (hw : ‖w‖ = 1) (hp : -(1 / 2) ≤ w.snd)
    {s : ℝ} (h0 : 0 ≤ s) (h1 : s ≤ 1) :
    0 < ‖s • northVec m + (1 - s) • w‖ ∧ -(1 / 2) ≤ (combPoint m w s).snd := by
  have h := cap_comb_height (m := m) (w := w) hw hp (α := s) (β := 1 - s) h0 (by linarith)
    (by ring)
  simpa [combPoint] using h

lemma combPoint_norm (m : ℕ) {w : CapModel m} (hw : ‖w‖ = 1) (hp : -(1 / 2) ≤ w.snd)
    {s : ℝ} (h0 : 0 ≤ s) (h1 : s ≤ 1) : ‖combPoint m w s‖ = 1 := by
  have hne : s • northVec m + (1 - s) • w ≠ 0 :=
    norm_ne_zero_iff.mp (ne_of_gt (combPoint_spec m hw hp h0 h1).1)
  simpa [combPoint] using norm_unitV hne

lemma combPoint_zero (m : ℕ) {w : CapModel m} (hw : ‖w‖ = 1) : combPoint m w 0 = w := by
  show unitV (0 • northVec m + (1 - 0) • w) = w
  simp [unitV, hw]

lemma combPoint_one (m : ℕ) (w : CapModel m) : combPoint m w 1 = northVec m := by
  show unitV (1 • northVec m + (1 - 1) • w) = northVec m
  simp [unitV, norm_northVec m]

/-! ## The contraction map on the cap -/

/-- The model coordinates of a point of the cap. -/
def capVec (m : ℕ) (p : unitInterval × capTplus m) : CapModel m :=
  tgtVec m (p.2 : Tgt m)

/-- The model point of the contraction at time `p.1`. -/
def combVec (m : ℕ) (p : unitInterval × capTplus m) : CapModel m :=
  combPoint m (capVec m p) (p.1 : ℝ)

lemma norm_capVec (m : ℕ) (p : unitInterval × capTplus m) : ‖capVec m p‖ = 1 :=
  norm_tgtVec m (p.2 : Tgt m)

lemma snd_capVec (m : ℕ) (p : unitInterval × capTplus m) : -(1 / 2) ≤ (capVec m p).snd := by
  have h : -(1 / 2) ≤ tgtHeight m (p.2 : Tgt m) := (p.2 : capTplus m).2
  show -(1 / 2) ≤ (tgtVec m (p.2 : Tgt m)).snd
  rwa [tgtVec_snd]

lemma combVec_spec (m : ℕ) (p : unitInterval × capTplus m) :
    0 < ‖(p.1 : ℝ) • northVec m + (1 - (p.1 : ℝ)) • capVec m p‖ ∧
      -(1 / 2) ≤ (combVec m p).snd := by
  have h := combPoint_spec (m := m) (w := capVec m p) (norm_capVec m p) (snd_capVec m p)
    (s := (p.1 : ℝ)) (unitInterval.nonneg p.1) (unitInterval.le_one p.1)
  simpa [combVec] using h

lemma combVec_norm (m : ℕ) (p : unitInterval × capTplus m) : ‖combVec m p‖ = 1 := by
  have hne : (p.1 : ℝ) • northVec m + (1 - (p.1 : ℝ)) • capVec m p ≠ 0 :=
    norm_ne_zero_iff.mp (ne_of_gt (combVec_spec m p).1)
  simpa [combVec, combPoint] using norm_unitV hne

/-- The point of the cap at time `p.1` of the contraction towards the north pole. -/
def combPt (m : ℕ) (p : unitInterval × capTplus m) : capTplus m :=
  capPt m (combVec m p) (combVec_norm m p) (combVec_spec m p).2

/-- v4.34: instance search for this times out on `WithLp 2 (Eu m × ℝ)`; supply it directly. -/
instance capModel_continuousSMul (m : ℕ) : ContinuousSMul ℝ (CapModel m) :=
  IsBoundedSMul.continuousSMul

lemma continuous_unitV_comp (m : ℕ) {X : Type*} [TopologicalSpace X] {f : X → CapModel m}
    (hf : Continuous f) (hne : ∀ x, f x ≠ 0) : Continuous fun x => unitV (f x) := by
  have h : (fun x => unitV (f x)) = fun x => ‖f x‖⁻¹ • f x := by
    funext x
    simp only [unitV]
  rw [h]
  exact (hf.norm.inv₀ (fun x => norm_ne_zero_iff.mpr (hne x))).smul hf

lemma continuous_capVec (m : ℕ) : Continuous (capVec m) := by
  have h2 : Continuous fun p : unitInterval × capTplus m =>
      (euclTgtIso m).symm (((p.2 : capTplus m) : Tgt m) :
        EuclideanSpace ℝ (Fin (2 * m + 1))) :=
    (euclTgtIso m).symm.continuous.comp
      (continuous_subtype_val.comp (continuous_subtype_val.comp continuous_snd))
  show Continuous fun p : unitInterval × capTplus m =>
    (euclTgtIso m).symm (((p.2 : capTplus m) : Tgt m) : EuclideanSpace ℝ (Fin (2 * m + 1)))
  exact h2

lemma continuous_combVec (m : ℕ) : Continuous (combVec m) := by
  have hs : Continuous fun p : unitInterval × capTplus m => (p.1 : ℝ) :=
    continuous_subtype_val.comp continuous_fst
  have hz : Continuous fun p : unitInterval × capTplus m =>
      (p.1 : ℝ) • northVec m + (1 - (p.1 : ℝ)) • capVec m p :=
    (hs.smul continuous_const).add ((continuous_const.sub hs).smul (continuous_capVec m))
  have hne : ∀ p : unitInterval × capTplus m,
      (p.1 : ℝ) • northVec m + (1 - (p.1 : ℝ)) • capVec m p ≠ 0 :=
    fun p => norm_ne_zero_iff.mp (ne_of_gt (combVec_spec m p).1)
  have h := continuous_unitV_comp (m := m) hz hne
  show Continuous fun p : unitInterval × capTplus m =>
    unitV ((p.1 : ℝ) • northVec m + (1 - (p.1 : ℝ)) • capVec m p)
  exact h

lemma continuous_combPt (m : ℕ) : Continuous (combPt m) := by
  have hcont : Continuous fun p : unitInterval × capTplus m => euclTgtIso m (combVec m p) :=
    (euclTgtIso m).continuous.comp (continuous_combVec m)
  have hmem : ∀ p : unitInterval × capTplus m,
      euclTgtIso m (combVec m p) ∈
        Metric.sphere (0 : EuclideanSpace ℝ (Fin (2 * m + 1))) 1 := by
    intro p
    rw [Metric.mem_sphere, dist_eq_norm, sub_zero, (euclTgtIso m).norm_map]
    exact combVec_norm m p
  have hcap : ∀ p : unitInterval × capTplus m,
      (⟨euclTgtIso m (combVec m p), hmem p⟩ : Tgt m) ∈ capTplus m := by
    intro p
    show tgtHeight m (tgtPt m (combVec m p) (combVec_norm m p)) ≥ -(1 / 2)
    rw [tgtHeight_tgtPt]
    exact (combVec_spec m p).2
  exact Continuous.subtype_mk (Continuous.subtype_mk hcont hmem) hcap

lemma combVec_zero (m : ℕ) (x : capTplus m) :
    combVec m ((0 : unitInterval), x) = capVec m ((0 : unitInterval), x) := by
  have h0 : ((0 : unitInterval) : ℝ) = 0 := rfl
  have hw : ‖capVec m ((0 : unitInterval), x)‖ = 1 := norm_capVec m _
  show combPoint m (capVec m ((0 : unitInterval), x)) ((0 : unitInterval) : ℝ) =
    capVec m ((0 : unitInterval), x)
  rw [h0, combPoint_zero m hw]

lemma combVec_one (m : ℕ) (x : capTplus m) : combVec m ((1 : unitInterval), x) = northVec m := by
  have h1 : ((1 : unitInterval) : ℝ) = 1 := rfl
  show combPoint m (capVec m ((1 : unitInterval), x)) ((1 : unitInterval) : ℝ) = northVec m
  rw [h1, combPoint_one m]

lemma combPt_zero (m : ℕ) (x : capTplus m) : combPt m ((0 : unitInterval), x) = x := by
  apply Subtype.ext
  apply Subtype.ext
  show euclTgtIso m (combVec m ((0 : unitInterval), x)) =
    (((x : capTplus m) : Tgt m) : EuclideanSpace ℝ (Fin (2 * m + 1)))
  rw [combVec_zero m x]
  show euclTgtIso m (tgtVec m (x : Tgt m)) =
    (((x : capTplus m) : Tgt m) : EuclideanSpace ℝ (Fin (2 * m + 1)))
  simp [tgtVec]

lemma combPt_one (m : ℕ) (x : capTplus m) :
    combPt m ((1 : unitInterval), x) = northCap m := by
  apply Subtype.ext
  apply Subtype.ext
  show euclTgtIso m (combVec m ((1 : unitInterval), x)) = euclTgtIso m (northVec m)
  rw [combVec_one m x]

/-! ## The two homotopies -/

/-- **Step 1**: the cap contracts to its north pole. -/
def contractNorth (m : ℕ) : ContinuousMap.Homotopy (ContinuousMap.id (capTplus m))
    (ContinuousMap.const (capTplus m) (northCap m)) where
  toFun := combPt m
  continuous_toFun := continuous_combPt m
  map_zero_left := by
    intro x
    rw [combPt_zero m x]
    rfl
  map_one_left := by
    intro x
    rw [combPt_one m x]
    rfl

/-- **Step 2**: the north pole is joined to `t0` inside the cap (a homotopy between the two
constant maps `const northPt` and `const t0`). -/
def contractT0 (m : ℕ) (t0 : Tgt m) (ht0 : t0 ∈ capTplus m) :
    ContinuousMap.Homotopy (ContinuousMap.const (capTplus m) (northCap m))
      (ContinuousMap.const (capTplus m) (⟨t0, ht0⟩ : capTplus m)) where
  toFun p := combPt m (unitInterval.symm p.1, ⟨t0, ht0⟩)
  continuous_toFun := (continuous_combPt m).comp
    ((unitInterval.continuous_symm.comp continuous_fst).prodMk continuous_const)
  map_zero_left := by
    intro x
    show combPt m (unitInterval.symm (0 : unitInterval), (⟨t0, ht0⟩ : capTplus m)) =
      northCap m
    rw [unitInterval.symm_zero]
    exact combPt_one m ⟨t0, ht0⟩
  map_one_left := by
    intro x
    show combPt m (unitInterval.symm (1 : unitInterval), (⟨t0, ht0⟩ : capTplus m)) =
      (⟨t0, ht0⟩ : capTplus m)
    rw [unitInterval.symm_one]
    exact combPt_zero m ⟨t0, ht0⟩

/-! ## The contraction of the cap to `t0` -/

/-- The closed cap `capTplus m = {tgtHeight ≥ -1/2}` of `Tgt m = S^{2m}` is contractible to any of
its points, by an explicit homotopy staying inside the cap: there is a continuous
`H : capTplus m × [0,1] → capTplus m` with `H (x,0) = x` and `H (x,1) = t0`. -/
theorem capTplus_contract (m : ℕ) (t0 : Tgt m) (ht0 : t0 ∈ capTplus m) :
    ∃ H : C(capTplus m × unitInterval, capTplus m),
      (∀ x, H (x, 0) = x) ∧ ∀ x, H (x, 1) = ⟨t0, ht0⟩ := by
  let Hcm : C(capTplus m × unitInterval, capTplus m) :=
    (((contractNorth m).trans (contractT0 m t0 ht0)) :
        C(unitInterval × capTplus m, capTplus m)).comp
      (⟨Prod.swap, continuous_swap⟩ :
        C(capTplus m × unitInterval, unitInterval × capTplus m))
  refine ⟨Hcm, ?_, ?_⟩
  · intro x
    simp [Hcm, ContinuousMap.comp_apply, ContinuousMap.id_apply]
  · intro x
    simp [Hcm, ContinuousMap.comp_apply]

end

end Work.KT
