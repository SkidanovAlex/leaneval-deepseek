import Mathlib
import Submission.Work.Drive.ProjectiveTopology

/-!
# `S³ → ℝP³` is a covering map

`Work.Drive.projOfUnitSphere` (`Submission/Work/Drive/ProjectiveTopology.lean`) is the map sending a
unit vector of `ℝ⁴` to the line it spans, i.e. the quotient map `S³ → ℝP³ = S³/{±1}` of the
antipodal involution.  Here we prove that it *is* a covering map.

The proof runs through the general machinery of `Topology/Covering/Quotient.lean`: we exhibit the
antipodal action of `ZMod 2` on the unit sphere and show that `projOfUnitSphere` is a *quotient
covering map* for it, so that `IsAddQuotientCoveringMap.isCoveringMap` applies.  Concretely we need

* `IsQuotientMap projOfUnitSphere`: verified through `Topology.isQuotientMap_iff_isClosed`, using
  that `S³` is compact and `ℝP³` is Hausdorff, so that `projOfUnitSphere` is a closed map;
* the fibres of `projOfUnitSphere` are exactly the antipodal pairs, which is
  `Work.Drive.sphere_quotient_projective` (the fibre of a unit vector is `{v, -v}`);
* transversality of the action: a small ball around `v ∈ S³` is disjoint from its image under the
  antipodal map, because `‖v‖ = 1` forces `dist v (-v) = 2`.
-/

namespace Work.Drive

open scoped LinearAlgebra.Projectivization

noncomputable section

/-- The antipodal point of a point of the unit sphere. -/
def negSphere {n : ℕ} (v : unitSphere n) : unitSphere n :=
  ⟨-v.1, by simp [norm_coe_unitSphere v]⟩

@[simp]
lemma negSphere_coe {n : ℕ} (v : unitSphere n) : (negSphere v).1 = -v.1 := rfl

@[simp]
lemma negSphere_negSphere {n : ℕ} (v : unitSphere n) : negSphere (negSphere v) = v :=
  Subtype.ext (by simp)

lemma continuous_negSphere {n : ℕ} : Continuous (negSphere (n := n)) :=
  Continuous.subtype_mk (continuous_neg.comp continuous_subtype_val) _

/-! ### The antipodal action of `ZMod 2` on the unit sphere -/

instance instVAddZMod2UnitSphere {n : ℕ} : VAdd (ZMod 2) (unitSphere n) where
  vadd k v := if k = 0 then v else negSphere v

lemma zmod2_vadd_eq {n : ℕ} (k : ZMod 2) (v : unitSphere n) :
    k +ᵥ v = (if k = 0 then v else negSphere v) := rfl

lemma zmod2_eq_zero_or_one : ∀ k : ZMod 2, k = 0 ∨ k = 1 := by decide

lemma zmod2_one_add_one : ((1 : ZMod 2) + 1) = 0 := by decide

lemma zmod2_one_ne_zero : (1 : ZMod 2) ≠ 0 := by decide

instance instAddActionZMod2UnitSphere {n : ℕ} : AddAction (ZMod 2) (unitSphere n) where
  zero_vadd v := by rw [zmod2_vadd_eq]; simp
  add_vadd a b v := by
    rcases zmod2_eq_zero_or_one a with rfl | rfl <;>
      rcases zmod2_eq_zero_or_one b with rfl | rfl <;>
        simp [zmod2_vadd_eq, zmod2_one_add_one]

instance instContinuousConstVAddZMod2UnitSphere {n : ℕ} :
    ContinuousConstVAdd (ZMod 2) (unitSphere n) where
  continuous_const_vadd k := by
    rcases zmod2_eq_zero_or_one k with rfl | rfl
    · rw [show (fun v : unitSphere n => (0 : ZMod 2) +ᵥ v) = id from
        funext fun v => by rw [zmod2_vadd_eq]; simp]
      exact continuous_id
    · rw [show (fun v : unitSphere n => (1 : ZMod 2) +ᵥ v) = negSphere from
        funext fun v => by rw [zmod2_vadd_eq]; simp]
      exact continuous_negSphere

/-! ### The fibres of `projOfUnitSphere` -/

/-- Two unit vectors represent the same point of `ℝP³` exactly when they are equal or antipodal.
This is the fibre computation `Work.Drive.sphere_quotient_projective` for the map
`projOfUnitSphere`. -/
lemma projOfUnitSphere_eq_iffSphere (a b : unitSphere 3) :
    projOfUnitSphere a = projOfUnitSphere b ↔ a = b ∨ a = negSphere b := by
  rw [projOfUnitSphere_eq a, projOfUnitSphere_eq b,
      sphere_quotient_projective.2 a.1 b.1 (norm_coe_unitSphere a) (norm_coe_unitSphere b)]
  constructor
  · rintro (h | h)
    · exact Or.inl (Subtype.ext h.symm)
    · refine Or.inr (Subtype.ext ?_)
      rw [negSphere_coe, h, neg_neg]
  · rintro (h | h)
    · exact Or.inl (congrArg Subtype.val h).symm
    · refine Or.inr ?_
      have ha : a.1 = -b.1 := by rw [h]; rfl
      rw [ha, neg_neg]

/-- The fibres of `projOfUnitSphere` are exactly the orbits of the antipodal `ZMod 2`-action. -/
lemma projOfUnitSphere_eq_iff_mem_orbit (a b : unitSphere 3) :
    projOfUnitSphere a = projOfUnitSphere b ↔ a ∈ AddAction.orbit (ZMod 2) b := by
  rw [AddAction.mem_orbit_iff, projOfUnitSphere_eq_iffSphere]
  constructor
  · rintro (h | h)
    · exact ⟨0, by rw [zmod2_vadd_eq]; simp [h]⟩
    · refine ⟨1, ?_⟩
      rw [zmod2_vadd_eq]
      simp only [zmod2_one_ne_zero, if_false]
      exact h.symm
  · rintro ⟨g, hg⟩
    rcases zmod2_eq_zero_or_one g with rfl | rfl
    · left
      rw [zmod2_vadd_eq] at hg
      simpa using hg.symm
    · right
      rw [zmod2_vadd_eq] at hg
      simp only [zmod2_one_ne_zero, if_false] at hg
      exact hg.symm

/-! ### `projOfUnitSphere` is a quotient map -/

/-- `S³ → ℝP³` is a quotient map: it is continuous and surjective, and as a continuous map from the
compact space `S³` to the Hausdorff space `ℝP³` it is closed, so that the topology of `ℝP³` is the
coinduced one. -/
lemma isQuotientMap_projOfUnitSphere :
    Topology.IsQuotientMap (projOfUnitSphere (n := 3)) := by
  rw [Topology.isQuotientMap_iff_isClosed]
  refine ⟨surjective_projOfUnitSphere, fun s => ⟨fun hs => hs.preimage continuous_projOfUnitSphere,
    fun hs => ?_⟩⟩
  have himg : IsCompact (projOfUnitSphere (n := 3) '' (projOfUnitSphere (n := 3) ⁻¹' s)) :=
    hs.isCompact.image continuous_projOfUnitSphere
  have : IsClosed (projOfUnitSphere (n := 3) '' (projOfUnitSphere (n := 3) ⁻¹' s)) :=
    himg.isClosed
  rwa [Set.image_preimage_eq s surjective_projOfUnitSphere] at this

/-! ### Transversality of the action -/

/-- A ball of radius `1` around a unit vector is disjoint from its antipodal image: if `x` lies in
the ball and `-x` does too, the triangle inequality gives `dist x (-x) < 2`, while `‖x‖ = 1` forces
`dist x (-x) = 2`. -/
lemma disjoint_ball_negSphere (a : unitSphere 3) :
    ∃ U ∈ nhds a, ∀ g : ZMod 2, ((fun x => g +ᵥ x) '' U ∩ U).Nonempty → g = 0 := by
  refine ⟨Metric.ball a 1, Metric.ball_mem_nhds a one_pos, ?_⟩
  intro g hg
  rcases zmod2_eq_zero_or_one g with rfl | rfl
  · rfl
  · exfalso
    obtain ⟨y, ⟨x, hxU, hxy⟩, hyU⟩ := hg
    have hx' : dist x a < 1 := Metric.mem_ball.mp hxU
    have hy' : dist y a < 1 := Metric.mem_ball.mp hyU
    have hyx : y = negSphere x := by simpa [zmod2_vadd_eq, zmod2_one_ne_zero] using hxy.symm
    have h3 : dist x (negSphere x) < 2 := by
      calc dist x (negSphere x) = dist x y := by rw [hyx]
        _ ≤ dist x a + dist a y := dist_triangle x a y
        _ < 1 + 1 := by
              rw [dist_comm a y]
              exact add_lt_add hx' hy'
        _ = 2 := by norm_num
    have h4 : dist x (negSphere x) = 2 := by
      rw [Subtype.dist_eq, negSphere_coe, dist_eq_norm]
      have h2 : x.1 - -x.1 = (2 : ℝ) • x.1 := by module
      rw [h2, norm_smul, Real.norm_eq_abs, abs_of_nonneg (by norm_num : (0:ℝ) ≤ 2),
        norm_coe_unitSphere x]
      norm_num
    linarith

/-! ### The covering map -/

/-- `projOfUnitSphere` is a quotient covering map for the antipodal `ZMod 2`-action. -/
lemma isAddQuotientCoveringMap_projOfUnitSphere :
    IsAddQuotientCoveringMap (projOfUnitSphere (n := 3)) (ZMod 2) :=
  IsAddQuotientCoveringMap.mk isQuotientMap_projOfUnitSphere
    instContinuousConstVAddZMod2UnitSphere
    (fun {a b} => projOfUnitSphere_eq_iff_mem_orbit a b)
    disjoint_ball_negSphere

theorem isCoveringMap_projOfUnitSphere :
    IsCoveringMap (Work.Drive.projOfUnitSphere (n := 3)) :=
  isAddQuotientCoveringMap_projOfUnitSphere.isCoveringMap

end

end Work.Drive
