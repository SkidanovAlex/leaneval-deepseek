import Mathlib
import Submission.Work.Thom.Cohomology
import Submission.Work.Thom.discFullA

-- Lean v4.35.0-rc3: restore v4.34 instance-unification transparency (port).
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
set_option synthInstance.maxHeartbeats 400000

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 1000000

/-!
# The inclusion of the punctured closed ball of radius `ρ` in the punctured space

For `ρ > 0` and `n : ℕ`, the inclusion of pairs

`(D_ρ, D_ρ ∖ {0}) ⟶ (ℝⁿ, ℝⁿ ∖ {0})`,  `D_ρ = {v : ℝⁿ | ‖v‖ ≤ ρ}`,

is a homotopy equivalence of pairs: the radial projection `v ↦ ρ (max ρ ‖v‖)⁻¹ • v` onto the closed
ball of radius `ρ` is a homotopy inverse, it fixes `D_ρ` pointwise and it maps `ℝⁿ ∖ {0}` to
`D_ρ ∖ {0}`.  Consequently (`Work.Thom.EuclCleanInfra.bijective_relCohMap_of_homotopyEquiv`) the
induced pullback on relative cohomology

`Hⁿ(ℝⁿ, ℝⁿ∖{0}; ℤ) ⟶ Hⁿ(D_ρ, D_ρ∖{0}; ℤ)`

is bijective in every degree — here in the degree `n` equal to the dimension, which is the only
degree in which the two groups are nonzero.  This is the last geometric input identifying the
"punctured ball" model of the Thom pair of the trivial rank-`n` bundle with the "punctured
Euclidean space" model.

The construction follows `Submission/Work/Thom/discFullA.lean` (the case `ρ = 1`, where the
boundary is the *sphere* rather than the punctured ball) and
`Submission/Work/Thom/spherePuncturedA.lean` (the relative version), with `1` replaced by `ρ` and
`(max 1 ‖v‖)⁻¹` by `ρ (max ρ ‖v‖)⁻¹`.
-/

namespace Work.ThomBordism

noncomputable section

/-! ## The radial coefficient and the radial projection onto the closed ball of radius `ρ` -/

/-- The **radial coefficient** `ρ (max ρ ‖v‖)⁻¹`: it is `1` on the closed ball of radius `ρ` and
`ρ / ‖v‖` outside it.  (It is the analogue of `Work.Thom.DiscFull.clampCoeff` for the radius `ρ`.) -/
def clampCoeffB (n : ℕ) (ρ : ℝ) (v : EuclideanSpace ℝ (Fin n)) : ℝ := ρ * (max ρ ‖v‖)⁻¹

theorem clampCoeffB_pos {n : ℕ} {ρ : ℝ} (hρ : 0 < ρ) (v : EuclideanSpace ℝ (Fin n)) :
    0 < clampCoeffB n ρ v :=
  mul_pos hρ (inv_pos.mpr (lt_of_lt_of_le hρ (le_max_left ρ ‖v‖)))

theorem clampCoeffB_nonneg {n : ℕ} {ρ : ℝ} (hρ : 0 < ρ) (v : EuclideanSpace ℝ (Fin n)) :
    0 ≤ clampCoeffB n ρ v := (clampCoeffB_pos hρ v).le

theorem clampCoeffB_eq_one_of_norm_le {n : ℕ} {ρ : ℝ} (hρ : 0 < ρ)
    {v : EuclideanSpace ℝ (Fin n)} (h : ‖v‖ ≤ ρ) : clampCoeffB n ρ v = 1 := by
  rw [clampCoeffB, max_eq_left h, mul_inv_cancel₀ hρ.ne']

/-- The radial coefficient does not increase the norm beyond `ρ`. -/
theorem clampCoeffB_mul_norm_le {n : ℕ} {ρ : ℝ} (hρ : 0 < ρ) (v : EuclideanSpace ℝ (Fin n)) :
    clampCoeffB n ρ v * ‖v‖ ≤ ρ := by
  rw [clampCoeffB]
  rcases le_total ‖v‖ ρ with h | h
  · rw [max_eq_left h, mul_inv_cancel₀ hρ.ne', one_mul]
    exact h
  · rw [max_eq_right h]
    have hv : (0 : ℝ) < ‖v‖ := lt_of_lt_of_le hρ h
    rw [mul_assoc, inv_mul_cancel₀ (ne_of_gt hv), mul_one]

/-- The **radial projection** `v ↦ ρ (max ρ ‖v‖)⁻¹ • v` onto the closed ball of radius `ρ`. -/
def clampPointB (n : ℕ) (ρ : ℝ) (v : EuclideanSpace ℝ (Fin n)) :
    EuclideanSpace ℝ (Fin n) := clampCoeffB n ρ v • v

theorem norm_clampPointB_le {n : ℕ} {ρ : ℝ} (hρ : 0 < ρ) (v : EuclideanSpace ℝ (Fin n)) :
    ‖clampPointB n ρ v‖ ≤ ρ := by
  rw [clampPointB, norm_smul, Real.norm_eq_abs, abs_of_nonneg (clampCoeffB_nonneg hρ v)]
  exact clampCoeffB_mul_norm_le hρ v

/-- On the closed ball of radius `ρ` the radial projection is the identity. -/
theorem clampPointB_eq_self_of_norm_le {n : ℕ} {ρ : ℝ} (hρ : 0 < ρ)
    {v : EuclideanSpace ℝ (Fin n)} (h : ‖v‖ ≤ ρ) : clampPointB n ρ v = v := by
  rw [clampPointB, clampCoeffB_eq_one_of_norm_le hρ h, one_smul]

/-- The radial projection vanishes only at the origin. -/
theorem clampPointB_ne_zero {n : ℕ} {ρ : ℝ} (hρ : 0 < ρ)
    {v : EuclideanSpace ℝ (Fin n)} (hv : v ≠ 0) : clampPointB n ρ v ≠ 0 :=
  smul_ne_zero (ne_of_gt (clampCoeffB_pos hρ v)) hv

theorem continuous_clampCoeffB {n : ℕ} {ρ : ℝ} (hρ : 0 < ρ) :
    Continuous (clampCoeffB n ρ) :=
  continuous_const.mul ((continuous_const.max continuous_norm).inv₀
    (fun v => ne_of_gt (lt_of_lt_of_le hρ (le_max_left ρ ‖v‖))))

theorem continuous_clampPointB {n : ℕ} {ρ : ℝ} (hρ : 0 < ρ) :
    Continuous (clampPointB n ρ) := (continuous_clampCoeffB hρ).smul continuous_id

/-- The coefficient of the straight-line homotopy from the radial projection to the identity is
positive, at every time `t ∈ [0,1]` and at every nonzero vector. -/
theorem homCoeff_pos {n : ℕ} {ρ : ℝ} (hρ : 0 < ρ) (t : ℝ) (ht0 : 0 ≤ t) (ht1 : t ≤ 1)
    (v : EuclideanSpace ℝ (Fin n)) : 0 < (1 - t) * clampCoeffB n ρ v + t := by
  rcases eq_or_lt_of_le ht1 with h | h
  · rw [h]; norm_num
  · have hc := clampCoeffB_pos hρ v
    have h1 : 0 < 1 - t := by linarith
    linarith [mul_pos h1 hc]

/-! ## The radial retraction of `ℝⁿ` onto the closed ball of radius `ρ` -/

/-- The radial projection as a map into the closed ball of radius `ρ`. -/
def clampB {n : ℕ} {ρ : ℝ} (hρ : 0 < ρ) (v : EuclideanSpace ℝ (Fin n)) :
    ↥{v : EuclideanSpace ℝ (Fin n) | ‖v‖ ≤ ρ} :=
  ⟨clampPointB n ρ v, norm_clampPointB_le hρ v⟩

/-- The inclusion of the closed ball of radius `ρ` in `ℝⁿ`. -/
def ballIncl (n : ℕ) (ρ : ℝ) :
    C(↥{v : EuclideanSpace ℝ (Fin n) | ‖v‖ ≤ ρ}, EuclideanSpace ℝ (Fin n)) :=
  ⟨Subtype.val, continuous_subtype_val⟩

/-- The radial retraction of `ℝⁿ` onto the closed ball of radius `ρ`. -/
def ballRetract {n : ℕ} {ρ : ℝ} (hρ : 0 < ρ) :
    C(EuclideanSpace ℝ (Fin n), ↥{v : EuclideanSpace ℝ (Fin n) | ‖v‖ ≤ ρ}) :=
  ⟨clampB hρ, (continuous_clampPointB hρ).subtype_mk (norm_clampPointB_le hρ)⟩

/-- The linear interpolation of the radial scaling, at time `t`:
`v ↦ ((1-t) ρ (max ρ ‖v‖)⁻¹ + t) • v`.  At `t = 0` this is the radial retraction and at `t = 1`
the identity of `ℝⁿ`. -/
def ballHomotopyMap {n : ℕ} {ρ : ℝ} (hρ : 0 < ρ) :
    C(unitInterval × EuclideanSpace ℝ (Fin n), EuclideanSpace ℝ (Fin n)) where
  toFun x := ((1 - (x.1 : ℝ)) * clampCoeffB n ρ x.2 + (x.1 : ℝ)) • x.2
  continuous_toFun := by
    have ht : Continuous fun x : unitInterval × EuclideanSpace ℝ (Fin n) => (x.1 : ℝ) :=
      continuous_subtype_val.comp continuous_fst
    have hv : Continuous fun x : unitInterval × EuclideanSpace ℝ (Fin n) => x.2 := continuous_snd
    have hc : Continuous fun x : unitInterval × EuclideanSpace ℝ (Fin n) => clampCoeffB n ρ x.2 :=
      (continuous_clampCoeffB hρ).comp hv
    exact (((continuous_const.sub ht).mul hc).add ht).smul hv

/-- **The inclusion of the closed ball of radius `ρ` in `ℝⁿ` is a homotopy equivalence**, with
homotopy inverse the radial projection, the homotopy being the linear interpolation of the radial
scaling. -/
def ballHomotopyEquiv {n : ℕ} {ρ : ℝ} (hρ : 0 < ρ) :
    ContinuousMap.HomotopyEquiv (↥{v : EuclideanSpace ℝ (Fin n) | ‖v‖ ≤ ρ})
      (EuclideanSpace ℝ (Fin n)) where
  toFun := ballIncl n ρ
  invFun := ballRetract hρ
  left_inv := by
    have heq : (ballRetract hρ).comp (ballIncl n ρ)
        = ContinuousMap.id ↥{v : EuclideanSpace ℝ (Fin n) | ‖v‖ ≤ ρ} := by
      apply ContinuousMap.ext
      intro q
      apply Subtype.ext
      exact clampPointB_eq_self_of_norm_le hρ q.2
    rw [heq]
  right_inv := by
    refine ⟨ContinuousMap.Homotopy.mk (ballHomotopyMap hρ) ?_ ?_⟩
    · intro p
      show ((1 - ((0 : unitInterval) : ℝ)) * clampCoeffB n ρ p + ((0 : unitInterval) : ℝ)) • p
        = clampPointB n ρ p
      rw [show ((0 : unitInterval) : ℝ) = 0 from rfl]
      simp [clampPointB]
    · intro p
      show ((1 - ((1 : unitInterval) : ℝ)) * clampCoeffB n ρ p + ((1 : unitInterval) : ℝ)) • p
        = p
      rw [show ((1 : unitInterval) : ℝ) = 1 from rfl]
      simp

/-! ## The punctured ball -/

/-- The inclusion of the punctured closed ball of radius `ρ` in the punctured space, as a map of
the *subtypes*: it is the restriction of `ballIncl` to the complements of the origin. -/
def punctBallIncl (n : ℕ) (ρ : ℝ) :
    C(↥{v : ↥{v : EuclideanSpace ℝ (Fin n) | ‖v‖ ≤ ρ} |
        (v : EuclideanSpace ℝ (Fin n)) ≠ 0},
      ↥({0}ᶜ : Set (EuclideanSpace ℝ (Fin n)))) :=
  ⟨fun v => ⟨(v : EuclideanSpace ℝ (Fin n)), v.2⟩,
    (continuous_subtype_val.comp continuous_subtype_val).subtype_mk (fun v => v.2)⟩

/-- The radial retraction of the punctured space onto the punctured closed ball of radius `ρ`. -/
def punctBallRetract {n : ℕ} {ρ : ℝ} (hρ : 0 < ρ) :
    C(↥({0}ᶜ : Set (EuclideanSpace ℝ (Fin n))),
      ↥{v : ↥{v : EuclideanSpace ℝ (Fin n) | ‖v‖ ≤ ρ} |
        (v : EuclideanSpace ℝ (Fin n)) ≠ 0}) where
  toFun v := ⟨clampB hρ v, by
    show ((clampB hρ v : ↥{v : EuclideanSpace ℝ (Fin n) | ‖v‖ ≤ ρ}) :
        EuclideanSpace ℝ (Fin n)) ≠ 0
    exact clampPointB_ne_zero hρ (Set.mem_compl_iff _ _ |>.mp v.2)⟩
  continuous_toFun := by
    have h1 : Continuous fun v : ↥({0}ᶜ : Set (EuclideanSpace ℝ (Fin n))) =>
        (clampB hρ v : ↥{v : EuclideanSpace ℝ (Fin n) | ‖v‖ ≤ ρ}) :=
      ((continuous_clampPointB hρ).comp continuous_subtype_val).subtype_mk
        (fun v => norm_clampPointB_le hρ (v : EuclideanSpace ℝ (Fin n)))
    exact h1.subtype_mk (fun v => by
      show clampPointB n ρ (v : EuclideanSpace ℝ (Fin n)) ≠ 0
      exact clampPointB_ne_zero hρ (Set.mem_compl_iff _ _ |>.mp v.2))

/-- The straight-line homotopy from the radial retraction of the punctured space to the identity,
which stays in the punctured space because the coefficient
`(1-t) ρ (max ρ ‖v‖)⁻¹ + t` is positive for `t ∈ [0,1]` and `v ≠ 0`. -/
def punctBallHomotopyMap {n : ℕ} {ρ : ℝ} (hρ : 0 < ρ) :
    C(unitInterval × ↥({0}ᶜ : Set (EuclideanSpace ℝ (Fin n))),
      ↥({0}ᶜ : Set (EuclideanSpace ℝ (Fin n)))) where
  toFun x := ⟨((1 - (x.1 : ℝ)) * clampCoeffB n ρ (x.2 : EuclideanSpace ℝ (Fin n))
      + (x.1 : ℝ)) • (x.2 : EuclideanSpace ℝ (Fin n)), by
    exact Set.mem_compl_iff _ _ |>.mpr
      (smul_ne_zero
        (ne_of_gt (homCoeff_pos hρ (x.1 : ℝ) x.1.2.1 x.1.2.2 (x.2 : EuclideanSpace ℝ (Fin n))))
        (Set.mem_compl_iff _ _ |>.mp x.2.2))⟩
  continuous_toFun := by
    have ht : Continuous fun x : unitInterval × ↥({0}ᶜ : Set (EuclideanSpace ℝ (Fin n))) =>
        (x.1 : ℝ) := continuous_subtype_val.comp continuous_fst
    have hv : Continuous fun x : unitInterval × ↥({0}ᶜ : Set (EuclideanSpace ℝ (Fin n))) =>
        (x.2 : EuclideanSpace ℝ (Fin n)) := continuous_subtype_val.comp continuous_snd
    have hc : Continuous fun x : unitInterval × ↥({0}ᶜ : Set (EuclideanSpace ℝ (Fin n))) =>
        clampCoeffB n ρ (x.2 : EuclideanSpace ℝ (Fin n)) := (continuous_clampCoeffB hρ).comp hv
    have hmain : Continuous fun x : unitInterval × ↥({0}ᶜ : Set (EuclideanSpace ℝ (Fin n))) =>
        ((1 - (x.1 : ℝ)) * clampCoeffB n ρ (x.2 : EuclideanSpace ℝ (Fin n)) + (x.1 : ℝ))
          • (x.2 : EuclideanSpace ℝ (Fin n)) :=
      (((continuous_const.sub ht).mul hc).add ht).smul hv
    exact hmain.subtype_mk (fun x => Set.mem_compl_iff _ _ |>.mpr
      (smul_ne_zero
        (ne_of_gt (homCoeff_pos hρ (x.1 : ℝ) x.1.2.1 x.1.2.2 (x.2 : EuclideanSpace ℝ (Fin n))))
        (Set.mem_compl_iff _ _ |>.mp x.2.2)))

/-- **The inclusion of the punctured closed ball of radius `ρ` in the punctured space is a homotopy
equivalence**, with homotopy inverse the radial projection and the linear interpolation of the
radial scaling as homotopy. -/
def punctBallHomotopyEquiv {n : ℕ} {ρ : ℝ} (hρ : 0 < ρ) :
    ContinuousMap.HomotopyEquiv
      (↥{v : ↥{v : EuclideanSpace ℝ (Fin n) | ‖v‖ ≤ ρ} |
        (v : EuclideanSpace ℝ (Fin n)) ≠ 0})
      (↥({0}ᶜ : Set (EuclideanSpace ℝ (Fin n)))) where
  toFun := punctBallIncl n ρ
  invFun := punctBallRetract hρ
  left_inv := by
    have heq : (punctBallRetract hρ).comp (punctBallIncl n ρ)
        = ContinuousMap.id (↥{v : ↥{v : EuclideanSpace ℝ (Fin n) | ‖v‖ ≤ ρ} |
            (v : EuclideanSpace ℝ (Fin n)) ≠ 0}) := by
      apply ContinuousMap.ext
      intro q
      apply Subtype.ext
      apply Subtype.ext
      exact clampPointB_eq_self_of_norm_le hρ q.1.2
    rw [heq]
  right_inv := by
    refine ⟨ContinuousMap.Homotopy.mk (punctBallHomotopyMap hρ) ?_ ?_⟩
    · intro v
      apply Subtype.ext
      show ((1 - ((0 : unitInterval) : ℝ)) * clampCoeffB n ρ (v : EuclideanSpace ℝ (Fin n))
          + ((0 : unitInterval) : ℝ)) • (v : EuclideanSpace ℝ (Fin n))
        = clampPointB n ρ (v : EuclideanSpace ℝ (Fin n))
      rw [show ((0 : unitInterval) : ℝ) = 0 from rfl]
      simp [clampPointB]
    · intro v
      apply Subtype.ext
      show ((1 - ((1 : unitInterval) : ℝ)) * clampCoeffB n ρ (v : EuclideanSpace ℝ (Fin n))
          + ((1 : unitInterval) : ℝ)) • (v : EuclideanSpace ℝ (Fin n))
        = (v : EuclideanSpace ℝ (Fin n))
      rw [show ((1 : unitInterval) : ℝ) = 1 from rfl]
      simp

/-! ## The induced map on relative cohomology -/

/-- **The inclusion of the punctured closed ball of radius `ρ` in the punctured space induces a
bijection on relative cohomology** in degree `n`.  This is
`Work.Thom.EuclCleanInfra.bijective_relCohMap_of_homotopyEquiv` applied to the two homotopy
equivalences of pairs constructed above. -/
theorem punctBallIncl_bijective {n : ℕ} {ρ : ℝ} (hρ : 0 < ρ) :
    Function.Bijective ((Work.Thom.relCohMap
      (⟨Subtype.val, continuous_subtype_val⟩ :
        C(↥{v : EuclideanSpace ℝ (Fin n) | ‖v‖ ≤ ρ}, EuclideanSpace ℝ (Fin n)))
      {v : ↥{v : EuclideanSpace ℝ (Fin n) | ‖v‖ ≤ ρ} |
        (v : EuclideanSpace ℝ (Fin n)) ≠ 0}
      ({0}ᶜ : Set (EuclideanSpace ℝ (Fin n)))
      (fun v hv => hv) ℤ n).hom) := by
  exact Work.Thom.EuclCleanInfra.bijective_relCohMap_of_homotopyEquiv
    {v : ↥{v : EuclideanSpace ℝ (Fin n) | ‖v‖ ≤ ρ} |
      (v : EuclideanSpace ℝ (Fin n)) ≠ 0}
    ({0}ᶜ : Set (EuclideanSpace ℝ (Fin n)))
    (⟨Subtype.val, continuous_subtype_val⟩ :
      C(↥{v : EuclideanSpace ℝ (Fin n) | ‖v‖ ≤ ρ}, EuclideanSpace ℝ (Fin n)))
    (fun v hv => hv)
    (ballHomotopyEquiv hρ) rfl (punctBallHomotopyEquiv hρ) (fun q => rfl) n

end

end Work.ThomBordism
