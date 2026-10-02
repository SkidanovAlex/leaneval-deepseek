import Mathlib
import Submission.Work.RatHurewicz.Cofibre.Maps

-- Lean v4.35.0-rc3: restore v4.34 instance-unification transparency (port).
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false

/-!
# Shrinking the height of a point of the half-open cone

For `s t : I` put `shrinkPt s t = (1-s)*t`; it is `≤ t`, hence it keeps the height inside
`{h < 1/2}`.  Descending `(y,s) ↦ [y, shrinkPt s (height y)]` along the restricted quotient map of
the half-open cone gives `coneShrinkC : ↥{h<1/2} → C(I, ↥{h<1/2})`: the homotopy that shrinks the
half-open cone onto its base.
-/

open scoped Topology unitInterval

namespace Work.RatHurewicz

noncomputable section

variable {E F : Type} [TopologicalSpace E] [TopologicalSpace F]

/-- `(1-s)*t` as an element of the unit interval. -/
def shrinkPt (s t : unitInterval) : unitInterval :=
  ⟨(1 - (s : ℝ)) * (t : ℝ), by
    constructor <;> nlinarith [s.2.1, s.2.2, t.2.1, t.2.2]⟩

/-- The same, as a continuous map. -/
def shrinkPtC : C(unitInterval × unitInterval, unitInterval) where
  toFun p := shrinkPt p.1 p.2
  continuous_toFun :=
    Continuous.subtype_mk (by fun_prop) (fun p => by
      constructor <;> nlinarith [p.1.2.1, p.1.2.2, p.2.2.1, p.2.2.2])

@[simp]
theorem shrinkPtC_apply (p : unitInterval × unitInterval) : shrinkPtC p = shrinkPt p.1 p.2 := rfl

@[simp]
theorem shrinkPt_zero (t : unitInterval) : shrinkPt 0 t = t := by
  apply Subtype.ext; simp [shrinkPt]

@[simp]
theorem shrinkPt_one (t : unitInterval) : shrinkPt 1 t = 0 := by
  apply Subtype.ext; simp [shrinkPt]

@[simp]
theorem shrinkPt_right_zero (s : unitInterval) : shrinkPt s 0 = 0 := by
  apply Subtype.ext; simp [shrinkPt]

theorem shrinkPt_le (s t : unitInterval) : (shrinkPt s t : ℝ) ≤ (t : ℝ) := by
  have hs : (1 : ℝ) - (s : ℝ) ≤ 1 := by linarith [s.2.1]
  have ht : (0 : ℝ) ≤ (t : ℝ) := t.2.1
  have h := mul_le_mul_of_nonneg_right hs ht
  simpa [shrinkPt] using h

theorem shrinkPt_lt_half (s : unitInterval) {t : unitInterval} (h : t < cofibreHalf) :
    shrinkPt s t < cofibreHalf :=
  lt_of_le_of_lt (shrinkPt_le s t) h

/-! ## The shrink map on the half-open cone -/

/-- The raw shrink map, on the preimage of the half-open cone in `F × I`. -/
def coneShrinkRaw :
    C(↥(coneMk (F := F) ⁻¹' coneLtHalfSet (F := F)) × unitInterval,
      ↥(coneLtHalfSet (F := F))) where
  toFun q :=
    ⟨coneMk (F := F) (q.1.1.1, shrinkPt q.2 q.1.1.2), by
      show coneHeight (coneMk (F := F) (q.1.1.1, shrinkPt q.2 q.1.1.2)) < cofibreHalf
      rw [coneHeight_coneMk]
      exact shrinkPt_lt_half q.2
        (by have h : coneHeight (coneMk (F := F) q.1.1) < cofibreHalf := q.1.2; rwa [coneHeight_coneMk] at h)⟩
  continuous_toFun :=
    Continuous.subtype_mk
      (continuous_quotient_mk'.comp (Continuous.prodMk
        (continuous_fst.comp (continuous_subtype_val.comp continuous_fst))
        (shrinkPtC.continuous.comp (continuous_snd.prodMk
          (continuous_snd.comp (continuous_subtype_val.comp continuous_fst))))))
      (fun q => by
        show coneHeight (coneMk (F := F) (q.1.1.1, shrinkPt q.2 q.1.1.2)) < cofibreHalf
        rw [coneHeight_coneMk]
        exact shrinkPt_lt_half q.2
          (by have h : coneHeight (coneMk (F := F) q.1.1) < cofibreHalf := q.1.2; rwa [coneHeight_coneMk] at h))

theorem coneShrinkRaw_apply (p : ↥(coneMk (F := F) ⁻¹' coneLtHalfSet (F := F)))
    (s : unitInterval) :
    coneShrinkRaw (F := F) (p, s) =
      ⟨coneMk (F := F) (p.1.1, shrinkPt s p.1.2), by
        show coneHeight (coneMk (F := F) (p.1.1, shrinkPt s p.1.2)) < cofibreHalf
        rw [coneHeight_coneMk]
        exact shrinkPt_lt_half s
          (by have h : coneHeight (coneMk (F := F) p.1) < cofibreHalf := p.2; rwa [coneHeight_coneMk] at h)⟩ := rfl

/-- The curried shrink map, as a continuous map into the function space. -/
def coneShrinkCurried :
    C(↥(coneMk (F := F) ⁻¹' coneLtHalfSet (F := F)),
      C(unitInterval, ↥(coneLtHalfSet (F := F)))) where
  toFun p := ⟨fun s => coneShrinkRaw (F := F) (p, s),
    (coneShrinkRaw (F := F)).continuous.comp (continuous_const.prodMk continuous_id)⟩
  continuous_toFun := ContinuousMap.continuous_of_continuous_uncurry _
    (coneShrinkRaw (F := F)).continuous

@[simp]
theorem coneShrinkCurried_apply (p : ↥(coneMk (F := F) ⁻¹' coneLtHalfSet (F := F)))
    (s : unitInterval) :
    (coneShrinkCurried (F := F) p) s = coneShrinkRaw (F := F) (p, s) := rfl

/-- The shrink map is constant on the fibres of the restricted quotient map: on the half-open cone
two points are related only when they are equal. -/
theorem coneShrinkCurried_factors :
    Function.FactorsThrough (coneShrinkCurried (F := F)) (coneRestrictMk (F := F)) := by
  intro a b hab
  have h : coneMk (F := F) a.1 = coneMk (F := F) b.1 := congrArg Subtype.val hab
  have hrel : (Work.Stems.coneSetoid F).r a.1 b.1 := Quotient.eq''.mp h
  have hab' : a = b := by
    apply Subtype.ext
    rcases hrel with h' | ⟨h1, h2⟩
    · exact h'
    · exfalso
      have ha : coneHeight (coneMk (F := F) a.1) < cofibreHalf := a.2
      rw [coneHeight_coneMk] at ha
      rw [h1] at ha
      have : ((1 : unitInterval) : ℝ) < ((cofibreHalf : unitInterval) : ℝ) := ha
      norm_num [cofibreHalf] at this
  subst hab'
  rfl

/-- **The shrink map on the half-open cone.** -/
def coneShrinkC :
    C(↥(coneLtHalfSet (F := F)), C(unitInterval, ↥(coneLtHalfSet (F := F)))) :=
  Topology.IsQuotientMap.lift (isQuotientMap_coneRestrictMk (F := F))
    (coneShrinkCurried (F := F)) (coneShrinkCurried_factors (F := F))

/-- Every point of the half-open cone is the image of a point of `F × I`. -/
theorem exists_coneRestrictMk_eq (y : ↥(coneLtHalfSet (F := F))) :
    ∃ p : ↥(coneMk (F := F) ⁻¹' coneLtHalfSet (F := F)), coneRestrictMk (F := F) p = y := by
  refine ⟨⟨Quotient.out y.1, ?_⟩, Subtype.ext ?_⟩
  · show coneMk (F := F) (Quotient.out y.1) ∈ coneLtHalfSet (F := F)
    rw [show coneMk (F := F) (Quotient.out y.1) = y.1 from Quotient.out_eq y.1]
    exact y.2
  · show coneMk (F := F) (Quotient.out y.1) = y.1
    exact Quotient.out_eq y.1

@[simp]
theorem coneRestrictMk_val (p : ↥(coneMk (F := F) ⁻¹' coneLtHalfSet (F := F))) :
    ((coneRestrictMk (F := F) p : ↥(coneLtHalfSet (F := F)))).1 = coneMk (F := F) p.1 := rfl

theorem coneShrinkC_apply (p : ↥(coneMk (F := F) ⁻¹' coneLtHalfSet (F := F)))
    (s : unitInterval) :
    coneShrinkC (F := F) (coneRestrictMk (F := F) p) s = coneShrinkRaw (F := F) (p, s) := by
  have h := Topology.IsQuotientMap.lift_comp (isQuotientMap_coneRestrictMk (F := F))
    (coneShrinkCurried (F := F)) (coneShrinkCurried_factors (F := F))
  have h3 := congrFun (congrArg (fun k : C(↥(coneMk (F := F) ⁻¹' coneLtHalfSet (F := F)),
      C(unitInterval, ↥(coneLtHalfSet (F := F)))) =>
        (⇑k : ↥(coneMk (F := F) ⁻¹' coneLtHalfSet (F := F)) →
          C(unitInterval, ↥(coneLtHalfSet (F := F))))) h) p
  exact congrFun (congrArg (fun k : C(unitInterval, ↥(coneLtHalfSet (F := F))) =>
    (⇑k : unitInterval → ↥(coneLtHalfSet (F := F)))) h3) s

/-- The underlying cone point of the raw shrink map. -/
theorem coneShrinkRaw_apply_val (p : ↥(coneMk (F := F) ⁻¹' coneLtHalfSet (F := F)))
    (s : unitInterval) :
    (coneShrinkRaw (F := F) (p, s)).1 = coneMk (F := F) (p.1.1, shrinkPt s p.1.2) := rfl

/-- The underlying cone point of the shrunk point. -/
theorem coneShrinkC_apply_val (p : ↥(coneMk (F := F) ⁻¹' coneLtHalfSet (F := F)))
    (s : unitInterval) :
    (coneShrinkC (F := F) (coneRestrictMk (F := F) p) s).1 =
      coneMk (F := F) (p.1.1, shrinkPt s p.1.2) := by
  rw [coneShrinkC_apply, coneShrinkRaw_apply_val]

/-- The height of the shrunk point, in the representative form. -/
theorem coneHeight_coneShrinkC_restrictMk (p : ↥(coneMk (F := F) ⁻¹' coneLtHalfSet (F := F)))
    (s : unitInterval) :
    coneHeight ((coneShrinkC (F := F) (coneRestrictMk (F := F) p) s).1) = shrinkPt s p.1.2 := by
  rw [coneShrinkC_apply_val, coneHeight_coneMk]

theorem coneHeight_coneShrinkC_restrictMk_le (p : ↥(coneMk (F := F) ⁻¹' coneLtHalfSet (F := F)))
    (s : unitInterval) :
    (coneHeight ((coneShrinkC (F := F) (coneRestrictMk (F := F) p) s).1) : ℝ) ≤ (p.1.2 : ℝ) := by
  rw [coneHeight_coneShrinkC_restrictMk]
  exact shrinkPt_le s p.1.2

theorem coneShrinkC_zero_restrictMk (p : ↥(coneMk (F := F) ⁻¹' coneLtHalfSet (F := F))) :
    coneShrinkC (F := F) (coneRestrictMk (F := F) p) 0 = coneRestrictMk (F := F) p := by
  apply Subtype.ext
  rw [coneShrinkC_apply_val, coneRestrictMk_val, shrinkPt_zero]

/-- At time `1` the shrunk cone point is the base point of its representative. -/
theorem coneShrinkC_one_restrictMk (p : ↥(coneMk (F := F) ⁻¹' coneLtHalfSet (F := F))) :
    (coneShrinkC (F := F) (coneRestrictMk (F := F) p) 1).1 = Work.Stems.coneIncl p.1.1 := by
  rw [coneShrinkC_apply_val, shrinkPt_one]
  rfl

/-- The shrink map fixes the base points of the half-open cone. -/
theorem coneShrinkC_base (z : F) (s : unitInterval) :
    (coneShrinkC (F := F)
      ⟨Work.Stems.coneIncl z,
        by
        show coneHeight (Work.Stems.coneIncl z) < cofibreHalf
        rw [coneHeight_coneIncl]; exact cofibreHalf_pos⟩ s).1 = Work.Stems.coneIncl z := by
  obtain ⟨p, hp⟩ := exists_coneRestrictMk_eq (F := F)
    ⟨Work.Stems.coneIncl z, by
        show coneHeight (Work.Stems.coneIncl z) < cofibreHalf
        rw [coneHeight_coneIncl]; exact cofibreHalf_pos⟩
  have hcone : coneMk (F := F) p.1 = Work.Stems.coneIncl z := by
    have h2 := congrArg (fun y : ↥(coneLtHalfSet (F := F)) => y.1) hp
    rw [coneRestrictMk_val] at h2
    exact h2
  have hp1 : p.1 = (z, 0) := by
    rcases (Quotient.eq''.mp hcone : (Work.Stems.coneSetoid F).r p.1 (z, 0)) with h | ⟨h1, h2⟩
    · exact h
    · exfalso
      have hlt : coneHeight (coneMk (F := F) p.1) < cofibreHalf := p.2
      rw [coneHeight_coneMk] at hlt
      rw [h1] at hlt
      have : ((1 : unitInterval) : ℝ) < ((cofibreHalf : unitInterval) : ℝ) := hlt
      norm_num [cofibreHalf] at this
  rw [← hp, coneShrinkC_apply_val, hp1, shrinkPt_right_zero]
  rfl

theorem coneShrinkC_zero (y : ↥(coneLtHalfSet (F := F))) : coneShrinkC (F := F) y 0 = y := by
  obtain ⟨p, rfl⟩ := exists_coneRestrictMk_eq (F := F) y
  exact coneShrinkC_zero_restrictMk (F := F) p

end

end Work.RatHurewicz
