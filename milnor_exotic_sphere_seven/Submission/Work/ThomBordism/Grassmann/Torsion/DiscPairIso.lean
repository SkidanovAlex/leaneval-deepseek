import Submission.Work.ThomBordism.Grassmann.Torsion.RadialDefs
import Submission.Work.ThomBordism.Grassmann.Torsion.ExcisionCompat
import Submission.Work.Thom.ATools
import Submission.Work.ThomBordism.Grassmann.relCohMap_pairHomotopy
import Submission.Work.ThomBordism.Grassmann.relCohomology_iso_of_tripleVanishing
import Submission.Work.Cohomology.relCohomology_univ_vanishing

-- Lean v4.35.0-rc3: restore v4.34 instance-unification transparency (port).
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
set_option synthInstance.maxHeartbeats 400000

set_option autoImplicit false
set_option maxHeartbeats 3000000
set_option backward.isDefEq.respectTransparency false

/-!
# The punctured disc pair and the disc pair

Two homotopy equivalences of pairs on the total space `E` of the tautological bundle:

* `puncturedDiscPairIso` — `(D, D∖0) ≃ (E, E∖0)` where `D = {fibN < 2}`: the radial deformation
  `p ↦ (max 1 (fibN p))⁻¹ • p` retracts `E` onto `D` (and `E∖0` onto `D∖0`), so the inclusion of
  pairs induces an isomorphism of relative cohomology;
* `discPairIso` — inside `D`, the annulus `{1 < fibN < 2}` can be replaced by the punctured disc
  `{0 < fibN < 2}` (the inclusion `{1 < fibN < 2} ↪ {0 < fibN < 2}` is a homotopy equivalence, and
  `relCohomology_iso_of_tripleVanishing` lets a pair be shrunk when the difference is acyclic).

The acyclicity needed for the second statement is `annPairAcyclic`, proved here from the same
pair-homotopy tool: `(↥{0 < fibN < 2}, {1 < fibN < 2})` is homotopy equivalent, as a pair, to
`(↥{1 < fibN < 2}, ⊤)`, whose relative cohomology vanishes by
`Work.Cohomology.relCohomology_univ_vanishing`.
-/

open scoped Topology
open CategoryTheory

namespace Work.ThomBordism.Grassmann.Torsion

open Work.ThomBordism.Grassmann

noncomputable section

variable {k m : ℕ}

/-! ## The retraction homotopies -/

/-! ## `puncturedDiscPairIso`: `(D, D∖0) ≃ (E, E∖0)` -/

theorem fibN_radPt_lt_two (k m : ℕ) (p : TM k m) : fibN k m (radPt k m p) < 2 := by
  rw [fibN_radPt]
  exact lt_of_le_of_lt (min_le_right _ _) (by norm_num)

/-- The deformation of the disc `D = {fibN < 2}` towards the origin (the underlying map). -/
def discHomFun (k m : ℕ) (z : ↥unitInterval × DiscT k m) : DiscT k m :=
  ⟨homPt k m ⟨z.1, Subtype.val z.2⟩,
    lt_of_le_of_lt (fibN_homPt_le k m ⟨z.1, Subtype.val z.2⟩) (Subtype.property z.2)⟩

theorem continuous_discHomFun (k m : ℕ) : Continuous (discHomFun k m) :=
  Continuous.subtype_mk (p := fun y : TM k m => y ∈ discSet k m)
    (f := fun z : ↥unitInterval × DiscT k m => homPt k m ⟨z.1, Subtype.val z.2⟩)
    ((continuous_homPt k m).comp
      (continuous_fst.prodMk (continuous_subtype_val.comp continuous_snd)))
    (fun z => lt_of_le_of_lt (fibN_homPt_le k m ⟨z.1, Subtype.val z.2⟩) (Subtype.property z.2))

/-- The deformation of the disc `D = {fibN < 2}` towards the origin, as a map `I × D → D`. -/
noncomputable def discHomMap (k m : ℕ) : C(↥unitInterval × DiscT k m, DiscT k m) :=
  ⟨discHomFun k m, continuous_discHomFun k m⟩

@[simp] theorem discHomMap_apply (k m : ℕ) (z : ↥unitInterval × DiscT k m) :
    discHomMap k m z = discHomFun k m z := rfl

/-- **The punctured disc pair has the relative cohomology of the Thom pair.** -/
theorem puncturedDiscPairIso (k m n : ℕ) :
    Nonempty (Work.Thom.RelCoh ℤ n ↥{p : TM k m | fibN k m p < 2}
        {x : ↥{p : TM k m | fibN k m p < 2} | 0 < fibN k m (x : TM k m)}
      ≃ₗ[ℤ] Work.Thom.OpenThom (tautologicalBundle k m) n) := by
  -- the inclusion of pairs `(D, D∖0) → (E, E∖0)`
  let F : C(↥{p : TM k m | fibN k m p < 2}, TM k m) :=
    ⟨Subtype.val, continuous_subtype_val⟩
  -- the radial retraction `E → D`
  let G : C(TM k m, ↥{p : TM k m | fibN k m p < 2}) :=
    ⟨fun p => ⟨radPt k m p, fibN_radPt_lt_two k m p⟩,
      (radPt k m).continuous.subtype_mk (fun p => fibN_radPt_lt_two k m p)⟩
  have hF : ∀ x ∈ {x : ↥{p : TM k m | fibN k m p < 2} | 0 < fibN k m (x : TM k m)},
      F x ∈ {p : TM k m | p.2 ≠ 0} := by
    intro x hx
    have h0 : fibN k m (F x) ≠ 0 := ne_of_gt hx
    intro hcon
    exact h0 ((fibN_eq_zero_iff k m (F x)).mpr hcon)
  have hG : ∀ y ∈ {p : TM k m | p.2 ≠ 0},
      G y ∈ {x : ↥{p : TM k m | fibN k m p < 2} | 0 < fibN k m (x : TM k m)} := by
    intro y hy
    have h0 : 0 < fibN k m y := by
      rcases lt_or_eq_of_le (fibN_nonneg k m y) with h | h
      · exact h
      · exact absurd ((fibN_eq_zero_iff k m y).mp h.symm) hy
    exact (fibN_radPt_pos_iff k m y).mpr h0
  -- the deformation on `D`
  let P : (G.comp F).Homotopy (ContinuousMap.id ↥{p : TM k m | fibN k m p < 2}) :=
    { toContinuousMap := discHomMap k m
      map_zero_left := fun x => Subtype.ext (homPt_zero k m (Subtype.val x))
      map_one_left := fun x => Subtype.ext (homPt_one k m (Subtype.val x)) }
  -- the deformation on `E`
  let Q : (F.comp G).Homotopy (ContinuousMap.id (TM k m)) :=
    { toContinuousMap := ⟨homPt k m, continuous_homPt k m⟩
      map_zero_left := fun p => homPt_zero k m p
      map_one_left := fun p => homPt_one k m p }
  have hP : ∀ t x, x ∈ {x : ↥{p : TM k m | fibN k m p < 2} | 0 < fibN k m (x : TM k m)} →
      P (t, x) ∈ {x : ↥{p : TM k m | fibN k m p < 2} | 0 < fibN k m (x : TM k m)} := by
    intro t x hx
    simp only [P, discHomMap_apply, discHomFun]
    exact fibN_homPt_pos k m ⟨t, Subtype.val x⟩ hx
  have hQ : ∀ t y, y ∈ {p : TM k m | p.2 ≠ 0} → Q (t, y) ∈ {p : TM k m | p.2 ≠ 0} := by
    intro t y hy
    have h0 : 0 < fibN k m y := by
      rcases lt_or_eq_of_le (fibN_nonneg k m y) with h | h
      · exact h
      · exact absurd ((fibN_eq_zero_iff k m y).mp h.symm) hy
    have hpos := fibN_homPt_pos k m ⟨t, y⟩ h0
    intro hcon
    exact absurd ((fibN_eq_zero_iff k m (homPt k m ⟨t, y⟩)).mpr hcon) (ne_of_gt hpos)
  have hbij := Work.ThomBordism.Grassmann.relCohMap_pairHomotopy
    {x : ↥{p : TM k m | fibN k m p < 2} | 0 < fibN k m (x : TM k m)}
    {p : TM k m | p.2 ≠ 0} F G hF hG P hP Q hQ n
  exact ⟨(LinearEquiv.ofBijective
    (Work.Thom.relCohMap F {x : ↥{p : TM k m | fibN k m p < 2} | 0 < fibN k m (x : TM k m)}
      {p : TM k m | p.2 ≠ 0} hF ℤ n).hom hbij).symm⟩

/-! ## The annulus coefficient homotopies -/

/-- The annulus, regarded as a subset of the punctured disc. -/
def annToPunct (k m : ℕ) (z : ↥(annSet k m)) : ↥(punctSet k m) :=
  ⟨z.val, ⟨lt_trans zero_lt_one z.property.1, z.property.2⟩⟩

/-- The coefficient of the annulus deformation at time `t`. -/
noncomputable def annHomCoeff (k m : ℕ) (t : ℝ) (p : TM k m) : ℝ := (1 - t) * annCoef k m p + t

theorem continuous_annHomCoeff {S : Set (TM k m)} (hS : ∀ p ∈ S, 0 < fibN k m p) :
    Continuous fun z : ↥(unitInterval) × ↥S => annHomCoeff k m (z.1 : ℝ) z.2.val := by
  have h1 : Continuous fun z : ↥(unitInterval) × ↥S => ((z.1 : ↥unitInterval) : ℝ) :=
    continuous_subtype_val.comp continuous_fst
  have hmid : Continuous fun z : ↥(unitInterval) × ↥S => z.2 := continuous_snd
  have h2 : Continuous fun z : ↥(unitInterval) × ↥S => annCoef k m z.2.val :=
    (continuous_annCoef_subtype hS).comp hmid
  unfold annHomCoeff
  exact ((continuous_const.sub h1).mul h2).add h1

/-- The annulus deformation point of `p`. -/
noncomputable def annHomPt (k m : ℕ) (z : ↥(unitInterval) × ↥(punctSet k m)) : TM k m :=
  ⟨z.2.val.proj, annHomCoeff k m (z.1 : ℝ) z.2.val • z.2.val.snd⟩

theorem fibN_annHomPt (k m : ℕ) (z : ↥(unitInterval) × ↥(punctSet k m)) :
    fibN k m (annHomPt k m z)
      = (1 - (z.1 : ℝ)) * annShift (fibN k m z.2.val) + (z.1 : ℝ) * fibN k m z.2.val := by
  have hpos : 0 < fibN k m z.2.val := z.2.property.1
  have hcoef : 0 ≤ annHomCoeff k m (z.1 : ℝ) z.2.val := by
    unfold annHomCoeff
    have h1 : 0 ≤ 1 - (z.1 : ℝ) := sub_nonneg.mpr (Set.mem_Icc.mp z.1.2).2
    have h2 : 0 ≤ annCoef k m z.2.val := le_of_lt (annCoef_pos hpos z.2.property.2)
    have h3 : 0 ≤ (z.1 : ℝ) := (Set.mem_Icc.mp z.1.2).1
    nlinarith
  rw [annHomPt, fibN_smul k m hcoef]
  have hkey : (annCoef k m z.2.val - (z.1 : ℝ) * annCoef k m z.2.val) * fibN k m z.2.val
      = (1 - (z.1 : ℝ)) * (annCoef k m z.2.val * fibN k m z.2.val) := by ring
  rw [annHomCoeff, add_mul, sub_mul, one_mul, hkey, annCoef_mul_fibN hpos]

theorem fibN_annHomPt_pos (k m : ℕ) (z : ↥(unitInterval) × ↥(punctSet k m)) :
    0 < fibN k m (annHomPt k m z) := by
  rw [fibN_annHomPt]
  have hpos : 0 < fibN k m z.2.val := z.2.property.1
  have hmem := annShift_mem hpos z.2.property.2
  rcases lt_or_eq_of_le (Set.mem_Icc.mp z.1.2).2 with hlt | heq
  · have h1 : 0 < 1 - (z.1 : ℝ) := sub_pos.mpr hlt
    have h2 : 0 ≤ (z.1 : ℝ) := (Set.mem_Icc.mp z.1.2).1
    nlinarith [mul_pos h1 (lt_trans zero_lt_one hmem.1), mul_nonneg h2 (le_of_lt hpos)]
  · rw [heq]
    norm_num
    exact hpos

theorem fibN_annHomPt_lt_two (k m : ℕ) (z : ↥(unitInterval) × ↥(punctSet k m)) :
    fibN k m (annHomPt k m z) < 2 := by
  rw [fibN_annHomPt]
  have hpos : 0 < fibN k m z.2.val := z.2.property.1
  have hmem := annShift_mem hpos z.2.property.2
  rcases lt_or_eq_of_le (Set.mem_Icc.mp z.1.2).2 with hlt | heq
  · have h1' : 0 < 1 - (z.1 : ℝ) := sub_pos.mpr hlt
    have hA := mul_lt_mul_of_pos_left hmem.2 h1'
    have hB := mul_le_mul_of_nonneg_left (le_of_lt z.2.property.2) (Set.mem_Icc.mp z.1.2).1
    linarith
  · rw [heq]
    norm_num
    exact z.2.property.2

theorem fibN_annHomPt_gt_one (k m : ℕ) (z : ↥(unitInterval) × ↥(punctSet k m))
    (h : 1 < fibN k m z.2.val) : 1 < fibN k m (annHomPt k m z) := by
  rw [fibN_annHomPt]
  have hpos : 0 < fibN k m z.2.val := z.2.property.1
  have hmem := annShift_mem hpos z.2.property.2
  rcases lt_or_eq_of_le (Set.mem_Icc.mp z.1.2).2 with hlt | heq
  · have h1' : 0 < 1 - (z.1 : ℝ) := sub_pos.mpr hlt
    have hA := mul_lt_mul_of_pos_left hmem.1 h1'
    have hB := mul_le_mul_of_nonneg_left (le_of_lt h) (Set.mem_Icc.mp z.1.2).1
    linarith
  · rw [heq]
    norm_num
    exact h

/-- The annulus deformation, as a map `I × {1 < fibN < 2} → {1 < fibN < 2}`. -/
def annMapFun (k m : ℕ) (z : ↥unitInterval × ↥(annSet k m)) : ↥(annSet k m) :=
  ⟨annHomPt k m ⟨z.1, annToPunct k m z.2⟩,
    ⟨fibN_annHomPt_gt_one k m ⟨z.1, annToPunct k m z.2⟩ z.2.property.1,
      fibN_annHomPt_lt_two k m ⟨z.1, annToPunct k m z.2⟩⟩⟩

theorem continuous_annMapFun (k m : ℕ) : Continuous (annMapFun k m) :=
  Continuous.subtype_mk (p := fun y : TM k m => y ∈ annSet k m)
    (f := fun z : ↥unitInterval × ↥(annSet k m) => annHomPt k m ⟨z.1, annToPunct k m z.2⟩)
    (Work.Thom.continuous_smul_section (tautologicalBundle k m)
      ⟨fun z : ↥unitInterval × ↥(annSet k m) => z.2.val,
        continuous_subtype_val.comp continuous_snd⟩
      ⟨fun z => annHomCoeff k m (z.1 : ℝ) (Subtype.val z.2),
        continuous_annHomCoeff (S := annSet k m) (fun p hp => lt_trans zero_lt_one hp.1)⟩)
    (fun z => ⟨fibN_annHomPt_gt_one k m ⟨z.1, annToPunct k m z.2⟩ z.2.property.1,
      fibN_annHomPt_lt_two k m ⟨z.1, annToPunct k m z.2⟩⟩)

/-- The annulus deformation as a continuous map. -/
noncomputable def annHomMap (k m : ℕ) : C(↥unitInterval × ↥(annSet k m), ↥(annSet k m)) :=
  ⟨annMapFun k m, continuous_annMapFun k m⟩

@[simp] theorem annHomMap_apply (k m : ℕ) (z : ↥unitInterval × ↥(annSet k m)) :
    annHomMap k m z = annMapFun k m z := rfl

theorem annHomCoeff_zero (k m : ℕ) (p : TM k m) : annHomCoeff k m (0 : ℝ) p = annCoef k m p := by
  unfold annHomCoeff; ring

theorem annHomCoeff_one (k m : ℕ) (p : TM k m) : annHomCoeff k m (1 : ℝ) p = 1 := by
  unfold annHomCoeff; ring

/-! ## The annulus push and the punctured-disc deformation -/

/-- The radial push `{0 < fibN < 2} → {1 < fibN < 2}` (the annulus coefficient rescaling). -/
def punctShiftFun (k m : ℕ) (z : PunctT k m) : ↥(annSet k m) :=
  ⟨⟨z.val.proj, annCoef k m z.val • z.val.snd⟩,
    ⟨by
      have hpos : 0 < fibN k m z.val := z.property.1
      have hcoef : 0 ≤ annCoef k m z.val := le_of_lt (annCoef_pos hpos z.property.2)
      rw [fibN_smul k m hcoef, annCoef_mul_fibN hpos]
      exact (annShift_mem hpos z.property.2).1,
     by
      have hpos : 0 < fibN k m z.val := z.property.1
      have hcoef : 0 ≤ annCoef k m z.val := le_of_lt (annCoef_pos hpos z.property.2)
      rw [fibN_smul k m hcoef, annCoef_mul_fibN hpos]
      exact (annShift_mem hpos z.property.2).2⟩⟩

theorem continuous_punctShiftFun (k m : ℕ) : Continuous (punctShiftFun k m) :=
  Continuous.subtype_mk (p := fun y : TM k m => y ∈ annSet k m)
    (f := fun z : PunctT k m => (⟨z.val.proj, annCoef k m z.val • z.val.snd⟩ : TM k m))
    (Work.Thom.continuous_smul_section (tautologicalBundle k m)
      ⟨fun z : PunctT k m => z.val, continuous_subtype_val⟩
      ⟨fun z => annCoef k m z.val,
        continuous_annCoef_subtype (S := punctSet k m) (fun p hp => hp.1)⟩)
    (fun z => (punctShiftFun k m z).property)

/-- The annulus push as a continuous map. -/
noncomputable def punctShiftMap (k m : ℕ) : C(PunctT k m, ↥(annSet k m)) :=
  ⟨punctShiftFun k m, continuous_punctShiftFun k m⟩

/-- The inclusion of the annulus in the punctured disc, as a continuous map. -/
noncomputable def annToPunctMap (k m : ℕ) : C(↥(annSet k m), PunctT k m) :=
  ContinuousMap.mk (annToPunct k m)
    (Continuous.subtype_mk (p := fun y : TM k m => y ∈ punctSet k m)
      (f := fun y : ↥(annSet k m) => y.val)
      continuous_subtype_val
      (fun y => ⟨lt_trans zero_lt_one y.property.1, y.property.2⟩))

/-- The punctured-disc deformation `I × {0 < fibN < 2} → {0 < fibN < 2}`. -/
def punctMapFun (k m : ℕ) (z : ↥unitInterval × PunctT k m) : PunctT k m :=
  ⟨annHomPt k m z, ⟨fibN_annHomPt_pos k m z, fibN_annHomPt_lt_two k m z⟩⟩

theorem continuous_punctMapFun (k m : ℕ) : Continuous (punctMapFun k m) :=
  Continuous.subtype_mk (p := fun y : TM k m => y ∈ punctSet k m)
    (f := fun z : ↥unitInterval × PunctT k m => annHomPt k m z)
    (Work.Thom.continuous_smul_section (tautologicalBundle k m)
      ⟨fun z : ↥unitInterval × PunctT k m => z.2.val,
        continuous_subtype_val.comp continuous_snd⟩
      ⟨fun z => annHomCoeff k m (z.1 : ℝ) z.2.val,
        continuous_annHomCoeff (S := punctSet k m) (fun p hp => hp.1)⟩)
    (fun z => ⟨fibN_annHomPt_pos k m z, fibN_annHomPt_lt_two k m z⟩)

/-- The punctured-disc deformation as a continuous map. -/
noncomputable def punctHomMap (k m : ℕ) : C(↥unitInterval × PunctT k m, PunctT k m) :=
  ⟨punctMapFun k m, continuous_punctMapFun k m⟩

@[simp] theorem punctHomMap_apply (k m : ℕ) (z : ↥unitInterval × PunctT k m) :
    punctHomMap k m z = punctMapFun k m z := rfl

@[simp] theorem punctShiftMap_apply (k m : ℕ) (z : PunctT k m) :
    punctShiftMap k m z = punctShiftFun k m z := rfl

@[simp] theorem annToPunctMap_apply (k m : ℕ) (y : ↥(annSet k m)) :
    annToPunctMap k m y = annToPunct k m y := rfl

theorem annHomPt_one (k m : ℕ) (z : ↥(punctSet k m)) :
    annHomPt k m ⟨(1 : ↥unitInterval), z⟩ = z.val := by
  show (⟨z.val.proj, annHomCoeff k m (((1 : ↥unitInterval) : ℝ)) z.val • z.val.snd⟩ : TM k m)
    = z.val
  have h1 : annHomCoeff k m ((1 : ↥unitInterval) : ℝ) z.val = 1 := by
    rw [show (((1 : ↥unitInterval) : ℝ)) = 1 from rfl]
    exact annHomCoeff_one k m z.val
  simp only [h1, one_smul]

theorem annHomPt_zero (k m : ℕ) (z : ↥(punctSet k m)) :
    annHomPt k m ⟨(0 : ↥unitInterval), z⟩
      = (⟨z.val.proj, annCoef k m z.val • z.val.snd⟩ : TM k m) := by
  show (⟨z.val.proj, annHomCoeff k m (((0 : ↥unitInterval) : ℝ)) z.val • z.val.snd⟩ : TM k m)
    = (⟨z.val.proj, annCoef k m z.val • z.val.snd⟩ : TM k m)
  have h1 : annHomCoeff k m ((0 : ↥unitInterval) : ℝ) z.val = annCoef k m z.val := by
    rw [show (((0 : ↥unitInterval) : ℝ)) = 0 from rfl]
    exact annHomCoeff_zero k m z.val
  simp only [h1]

/-- **The pair `(↥{0 < fibN < 2}, {1 < fibN < 2})` is acyclic** (its relative cohomology vanishes
in every degree): the annulus is a deformation retract of the punctured disc. -/
theorem annPairAcyclic (k m j : ℕ) :
    Subsingleton (Work.Thom.RelCoh ℤ j (PunctT k m)
      {y : PunctT k m | 1 < fibN k m y.val}) := by
  have hf : ∀ x ∈ {y : PunctT k m | 1 < fibN k m y.val},
      punctShiftMap k m x ∈ (Set.univ : Set ↥(annSet k m)) := fun _ _ => trivial
  have hg : ∀ y ∈ (Set.univ : Set ↥(annSet k m)), annToPunctMap k m y ∈
      {y : PunctT k m | 1 < fibN k m y.val} := fun y _ => y.property.1
  let P' : ((annToPunctMap k m).comp (punctShiftMap k m)).Homotopy (ContinuousMap.id (PunctT k m)) :=
    { toContinuousMap := punctHomMap k m
      map_zero_left := by
        intro z
        refine Subtype.ext ?_
        exact congrArg (fun c : ℝ => (⟨z.val.proj, c • z.val.snd⟩ : TM k m))
          (annHomCoeff_zero k m z.val)
      map_one_left := by
        intro z
        refine Subtype.ext ?_
        show (⟨z.val.proj, annHomCoeff k m ((1 : ↥unitInterval) : ℝ) z.val • z.val.snd⟩ : TM k m)
          = z.val
        have h1 : annHomCoeff k m ((1 : ↥unitInterval) : ℝ) z.val = 1 := by
          rw [show (((1 : ↥unitInterval) : ℝ)) = 1 from rfl]
          exact annHomCoeff_one k m z.val
        simp only [h1, one_smul] }
  let Q' : ((punctShiftMap k m).comp (annToPunctMap k m)).Homotopy (ContinuousMap.id ↥(annSet k m)) :=
    { toContinuousMap := annHomMap k m
      map_zero_left := by
        intro y
        refine Subtype.ext ?_
        show (annHomPt k m ⟨(0 : ↥unitInterval), annToPunct k m y⟩ : TM k m)
          = (⟨y.val.proj, annCoef k m (annToPunct k m y).val • (annToPunct k m y).val.snd⟩ : TM k m)
        exact congrArg (fun c : ℝ =>
          (⟨(annToPunct k m y).val.proj, c • (annToPunct k m y).val.snd⟩ : TM k m))
          (annHomCoeff_zero k m (annToPunct k m y).val)
      map_one_left := by
        intro y
        refine Subtype.ext ?_
        show annHomPt k m ⟨(1 : ↥unitInterval), annToPunct k m y⟩ = (y : TM k m)
        exact annHomPt_one k m (annToPunct k m y) }
  have hP' : ∀ t x, x ∈ {y : PunctT k m | 1 < fibN k m y.val} →
      P' (t, x) ∈ {y : PunctT k m | 1 < fibN k m y.val} := by
    intro t x hx
    show 1 < fibN k m (annHomPt k m ⟨t, x⟩)
    exact fibN_annHomPt_gt_one k m ⟨t, x⟩ hx
  have hQ' : ∀ t y, y ∈ (Set.univ : Set ↥(annSet k m)) → Q' (t, y) ∈ Set.univ :=
    fun _ _ _ => trivial
  have hbij := Work.ThomBordism.Grassmann.relCohMap_pairHomotopy
    {y : PunctT k m | 1 < fibN k m y.val} Set.univ (punctShiftMap k m) (annToPunctMap k m)
    hf hg P' hP' Q' hQ' j
  haveI : Subsingleton (Work.Thom.RelCoh ℤ j (↥(annSet k m)) Set.univ) :=
    Work.Cohomology.relCohomology_univ_vanishing (TopCat.of ↥(annSet k m)) j
  exact ⟨fun a b => by
    obtain ⟨x, rfl⟩ := hbij.2 a
    obtain ⟨y, rfl⟩ := hbij.2 b
    rw [Subsingleton.elim x y]⟩

/-- The punctured disc as a subset of the disc, as a type. -/
abbrev Punct2T (k m : ℕ) : Type := ↥{x : ↥(discSet k m) | 0 < fibN k m x.val}

/-- The canonical identification of the nested subtype `↥{x : ↥(discSet k m) | 0 < fibN k m x.val}`
with the punctured disc. -/
noncomputable def punctFlatHomeo (k m : ℕ) : Punct2T k m ≃ₜ PunctT k m where
  toFun x := ⟨x.val.val, ⟨x.property, x.val.property⟩⟩
  invFun y := ⟨⟨y.val, y.property.2⟩, y.property.1⟩
  left_inv x := Subtype.ext (Subtype.ext rfl)
  right_inv y := Subtype.ext rfl
  continuous_toFun := Continuous.subtype_mk (p := fun y : TM k m => y ∈ punctSet k m)
    (f := fun x : Punct2T k m => (x.val.val : TM k m))
    (continuous_subtype_val.comp continuous_subtype_val)
    (fun x => ⟨x.property, x.val.property⟩)
  continuous_invFun := Continuous.subtype_mk
    (p := fun x : ↥(discSet k m) => 0 < fibN k m x.val)
    (f := fun y : PunctT k m => (⟨y.val, y.property.2⟩ : ↥(discSet k m)))
    (Continuous.subtype_mk (p := fun y : TM k m => fibN k m y < 2)
      (f := fun y : PunctT k m => y.val) continuous_subtype_val (fun y => y.property.2))
    (fun y => y.property.1)

@[simp] theorem punctFlatHomeo_apply (k m : ℕ) (x : Punct2T k m) :
    punctFlatHomeo k m x = ⟨x.val.val, ⟨x.property, x.val.property⟩⟩ := rfl

/-- The nested form of `annPairAcyclic`, in the shape required by the triple-vanishing lemma. -/
theorem annPairAcyclicNested (k m j : ℕ) :
    Subsingleton (Work.Cohomology.relCohomology ℤ (TopCat.of (Punct2T k m))
      ((Subtype.val : Punct2T k m → ↥(discSet k m)) ⁻¹'
        {x : ↥(discSet k m) | 1 < fibN k m x.val}) j) := by
  haveI : Subsingleton (Work.Thom.RelCoh ℤ j (PunctT k m)
      {y : PunctT k m | 1 < fibN k m y.val}) := annPairAcyclic k m j
  have hbij := Work.Thom.bijective_relCohMap_of_homeomorphA
    {x : Punct2T k m | 1 < fibN k m x.val.val}
    {y : PunctT k m | 1 < fibN k m y.val}
    (punctFlatHomeo k m) (fun x => Iff.rfl) ℤ j
  refine ⟨fun a b => ?_⟩
  obtain ⟨x, rfl⟩ := hbij.2 a
  obtain ⟨y, rfl⟩ := hbij.2 b
  rw [Subsingleton.elim x y]

/-- **The disc pair with the annulus as second member has the relative cohomology of the punctured
disc pair**: inside `D = {fibN < 2}`, the annulus `{1 < fibN}` is a deformation retract of the
punctured disc `{0 < fibN}`, so the triple-vanishing lemma applies. -/
theorem discPairIso (k m n : ℕ) :
    Nonempty (Work.Thom.RelCoh ℤ (n + 1) ↥(discSet k m)
        {x : ↥(discSet k m) | 1 < fibN k m x.val}
      ≃ₗ[ℤ] Work.Thom.RelCoh ℤ (n + 1) ↥(discSet k m)
        {x : ↥(discSet k m) | 0 < fibN k m x.val}) := by
  have hsub : {x : ↥(discSet k m) | 1 < fibN k m x.val}
      ⊆ {x : ↥(discSet k m) | 0 < fibN k m x.val} := by
    intro x hx
    show 0 < fibN k m x.val
    exact lt_trans zero_lt_one hx
  obtain ⟨e⟩ := Work.ThomBordism.Grassmann.relCohomology_iso_of_tripleVanishing
    (TopCat.of ↥(discSet k m)) {x : ↥(discSet k m) | 1 < fibN k m x.val}
    {x : ↥(discSet k m) | 0 < fibN k m x.val} hsub
    (fun j => annPairAcyclicNested k m j) n
  exact ⟨e.symm⟩

end

end Work.ThomBordism.Grassmann.Torsion