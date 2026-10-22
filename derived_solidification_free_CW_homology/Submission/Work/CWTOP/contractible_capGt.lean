import Mathlib
import Submission.Work.CWTOP.Closed
import Submission.Work.CWTOP.CapDefs

/-!
# The cap `-1 < y 0` of the model sphere is contractible

The model sphere `modelSphere n ⊆ Fin (n + 1) → ℝ` is the unit sphere for the sup norm, hence the
boundary of the cube `[-1,1]^{n+1}`.  The cap `capGt n = {y // -1 < y 0}` is the complement of the
single point `-pole n`.  The straight line from a point `y` of the cap to the pole `pole n` never
meets the closed ray of the antipode `-pole n`, so normalising it (in the norm of
`Fin (n+1) → ℝ`) gives a well defined continuous deformation of the cap to the pole; this proves
`ContractibleSpace (capGt n)`.

The key pointwise input is `interpVec_add_norm_pos`: for `t ∈ [0,1]` and `y` in the cap,
`((1 - t) • y + t • pole) 0 + ‖(1 - t) • y + t • pole‖ > 0`, which says exactly that
`(1 - t) • y + t • pole` is never a nonpositive multiple of `pole` (in particular it is never `0`).
-/

open Set Metric Topology
open scoped unitInterval

noncomputable section

namespace Work.CWTOP

/-! ## §1 The pole as a point of the cap -/

/-- The pole, viewed as a point of the cap. -/
def poleCap (n : ℕ) : capGt n :=
  ⟨⟨pole n, pole_mem_modelSphere n⟩, by
    show -1 < (pole n : Fin (n + 1) → ℝ) 0
    rw [pole_zero]
    norm_num⟩

lemma capVec_poleCap (n : ℕ) : capVec (poleCap n) = pole n := rfl

/-! ## §2 The key pointwise inequality -/

/-- For `t ∈ [0,1]` and `y` in the cap, the point `(1 - t) • y + t • pole` of the straight line
from `y` to the pole is never on the closed ray of the antipode: its `0`-th coordinate plus its
norm is positive. -/
theorem interpVec_add_norm_pos (n : ℕ) (t : ℝ) (y : capGt n) (ht0 : 0 ≤ t) (ht1 : t ≤ 1) :
    0 < interpVec t y 0 + ‖interpVec t y‖ := by
  -- an index at which the norm of `capVec y` is attained
  obtain ⟨i, hi⟩ := Set.mem_range.mp (IsGreatest.pi_norm (capVec y)).1
  have hyi : |capVec y i| = 1 := by
    rw [Real.norm_eq_abs, capVec_norm y] at hi
    exact hi
  rcases eq_or_ne i 0 with rfl | hi0
  · -- the norm is attained at the `0`-th coordinate, so `y` is the pole
    have hy0 : capVec y 0 = 1 := by
      rcases le_or_gt (capVec y 0) 0 with h | h
      · rw [abs_of_nonpos h] at hyi
        linarith [capVec_coord y]
      · rw [abs_of_pos h] at hyi
        exact hyi
    have hv0 : interpVec t y 0 = 1 := by
      rw [interpVec_apply_zero, hy0]
      ring
    rw [hv0]
    linarith [norm_nonneg (interpVec t y)]
  · -- otherwise the `i`-th coordinate of `y` has modulus one, with `i ≠ 0`
    have hvi : interpVec t y i = (1 - t) * capVec y i := interpVec_apply_of_ne_zero t y hi0
    have habs : |interpVec t y i| = 1 - t := by
      rw [hvi, abs_mul, hyi, mul_one, abs_of_nonneg (sub_nonneg.mpr ht1)]
    have hle : |interpVec t y i| ≤ ‖interpVec t y‖ := by
      have h := norm_le_pi_norm (interpVec t y) i
      rwa [Real.norm_eq_abs] at h
    -- `(interpVec t y) 0 + |(interpVec t y) i| = (1 - t) * (y 0 + 1) + t`
    have hsum : interpVec t y 0 + |interpVec t y i| = (1 - t) * (capVec y 0 + 1) + t := by
      rw [interpVec_apply_zero, habs]
      ring
    have hA : 0 ≤ (1 - t) * (capVec y 0 + 1) :=
      mul_nonneg (by linarith) (by linarith [capVec_coord y])
    have hAt : 0 < (1 - t) * (capVec y 0 + 1) + t := by
      rcases lt_or_eq_of_le ht0 with h | h
      · linarith
      · rw [← h]
        simp only [sub_zero, one_mul, add_zero]
        linarith [capVec_coord y]
    linarith [hsum, hle, hAt]

lemma interpVec_ne_zero (n : ℕ) (t : ℝ) (y : capGt n) (ht0 : 0 ≤ t) (ht1 : t ≤ 1) :
    interpVec t y ≠ 0 := by
  intro h
  have hpos := interpVec_add_norm_pos n t y ht0 ht1
  rw [h] at hpos
  simp at hpos

lemma interpVec_norm_pos (n : ℕ) (t : ℝ) (y : capGt n) (ht0 : 0 ≤ t) (ht1 : t ≤ 1) :
    0 < ‖interpVec t y‖ :=
  norm_pos_iff.mpr (interpVec_ne_zero n t y ht0 ht1)

/-- The normalised straight-line point lies on the model sphere. -/
lemma normalized_mem_modelSphere (n : ℕ) (t : ℝ) (y : capGt n) (ht0 : 0 ≤ t) (ht1 : t ≤ 1) :
    (‖interpVec t y‖)⁻¹ • interpVec t y ∈ modelSphere n := by
  rw [mem_modelSphere, norm_smul, Real.norm_eq_abs,
    abs_of_nonneg (inv_nonneg.mpr (norm_nonneg _)),
    inv_mul_cancel₀ (ne_of_gt (interpVec_norm_pos n t y ht0 ht1))]

/-- The normalised straight-line point still satisfies `-1 <` its `0`-th coordinate. -/
lemma normalized_coord_gt (n : ℕ) (t : ℝ) (y : capGt n) (ht0 : 0 ≤ t) (ht1 : t ≤ 1) :
    -1 < ((‖interpVec t y‖)⁻¹ • interpVec t y) 0 := by
  have hpos := interpVec_add_norm_pos n t y ht0 ht1
  have hnpos := interpVec_norm_pos n t y ht0 ht1
  have hv : -‖interpVec t y‖ < interpVec t y 0 := by linarith
  have hmul := mul_lt_mul_of_pos_left hv (inv_pos.mpr hnpos)
  have h1 : (‖interpVec t y‖)⁻¹ * (-‖interpVec t y‖) = -1 := by
    rw [mul_neg, inv_mul_cancel₀ (ne_of_gt hnpos)]
  rw [h1] at hmul
  simpa [Pi.smul_apply, smul_eq_mul] using hmul

/-! ## §3 The deformation and its continuity -/

/-- The underlying vector of the deformation of the cap to the pole. -/
def capDeformationVec (n : ℕ) (q : unitInterval × capGt n) : Fin (n + 1) → ℝ :=
  (‖interpFun n q‖)⁻¹ • interpFun n q

lemma continuous_interpFin (n : ℕ) :
    Continuous fun q : unitInterval × capGt n => interpFun n q := by
  have ht : Continuous fun q : unitInterval × capGt n => ((q.1 : unitInterval) : ℝ) :=
    continuous_subtype_val.comp continuous_fst
  have hy : Continuous fun q : unitInterval × capGt n => capVec q.2 :=
    (continuous_subtype_val.comp continuous_subtype_val).comp continuous_snd
  have h1 : Continuous fun q : unitInterval × capGt n => (1 - (q.1 : ℝ)) • capVec q.2 :=
    (continuous_const.sub ht).smul hy
  have h2 : Continuous fun q : unitInterval × capGt n => (q.1 : ℝ) • pole n :=
    ht.smul continuous_const
  exact h1.add h2

lemma continuous_capDeformationVec (n : ℕ) : Continuous (capDeformationVec n) := by
  have hfun := continuous_interpFin n
  have hinv : Continuous fun q : unitInterval × capGt n => (‖interpFun n q‖)⁻¹ :=
    Continuous.inv₀ (continuous_norm.comp hfun)
      (fun q => ne_of_gt (norm_pos_iff.mpr
        (interpVec_ne_zero n (q.1 : ℝ) q.2 q.1.2.1 q.1.2.2)))
  exact hinv.smul hfun

/-- The deformation of the cap to the pole: straight line to the pole, normalised to the sphere. -/
def capDeformation (n : ℕ) : C(unitInterval × capGt n, capGt n) where
  toFun q :=
    ⟨⟨capDeformationVec n q,
        normalized_mem_modelSphere n (q.1 : ℝ) q.2 q.1.2.1 q.1.2.2⟩,
      normalized_coord_gt n (q.1 : ℝ) q.2 q.1.2.1 q.1.2.2⟩
  continuous_toFun := by
    apply Continuous.subtype_mk
    apply Continuous.subtype_mk
    exact continuous_capDeformationVec n

lemma capDeformationVec_zero (n : ℕ) (y : capGt n) :
    capDeformationVec n (0, y) = capVec y := by
  have h0 : interpFun n (0, y) = capVec y := by
    simp [interpFun, interpVec, Set.Icc.coe_zero]
  simp only [capDeformationVec, h0, capVec_norm, inv_one, one_smul]

lemma capDeformationVec_one (n : ℕ) (y : capGt n) :
    capDeformationVec n (1, y) = pole n := by
  have h1 : interpFun n (1, y) = pole n := by
    simp [interpFun, interpVec, Set.Icc.coe_one]
  simp only [capDeformationVec, h1, norm_pole, inv_one, one_smul]

/-! ## §4 The homotopy and contractibility -/

/-- The straight-line deformation of the cap to the pole. -/
def capHomotopy (n : ℕ) :
    ContinuousMap.Homotopy (ContinuousMap.id (capGt n))
      (ContinuousMap.const (capGt n) (poleCap n)) where
  toContinuousMap := capDeformation n
  map_zero_left y := by
    apply Subtype.ext
    apply Subtype.ext
    exact capDeformationVec_zero n y
  map_one_left y := by
    apply Subtype.ext
    apply Subtype.ext
    exact capDeformationVec_one n y

theorem contractible_capGt (n : ℕ) :
    ContractibleSpace {y : Work.CWTOP.modelSphere n // -1 < y.1 0} := by
  have h : ContractibleSpace (capGt n) :=
    (contractible_iff_id_nullhomotopic (capGt n)).mpr ⟨poleCap n, ⟨capHomotopy n⟩⟩
  exact h

end Work.CWTOP
