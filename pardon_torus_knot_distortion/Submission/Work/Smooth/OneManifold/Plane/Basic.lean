import Mathlib
import Submission.Work.Smooth.OneManifold.Bridge

/-!
# Local arcs in the parameter plane

This file collects the elementary facts about `Work.Smooth.SphereJordan.IsLocallyArc` for subsets
of the parameter plane `ℝ × ℝ` (and for `ℝ` itself):

* `isLocallyArc_real` — `ℝ` is locally an arc;
* `isLocallyArc_Ioo`, `isLocallyArc_of_isOpen_real` — an open subset of `ℝ` is locally an arc;
* `isLocallyArc_image_of_homeomorph` — local arcness is a topological property of the *set* (it
  transports along a homeomorphism of the ambient spaces);
* `isLocallyArc_of_eq` — a congruence;
* `isLocallyArc_of_isOpen_cover` — a space covered by open locally-arc pieces is locally arc;
* `isLocallyArc_graph_of_isOpen` — the graph of a continuous function over an open subset of `ℝ`
  is locally an arc (the projection to the first coordinate is a homeomorphism);
* `isLocallyArc_max_zero` — the "corner" `{(a, b) | max a b = 0}`, the union of the two negative
  coordinate half-axes, is locally an arc (it is homeomorphic to `ℝ`).

They are the plane-side vocabulary of the local models of the box norm
(`Submission/Work/Smooth/BoxGeneric/LocalSurface`), used in this chapter to upgrade the local
`IsLocalArc` models of the box-norm level set to the local-`1`-manifold structure
`Work.Smooth.OneManifold.IsLocallyEuclidean`.
-/

open Set

namespace Work.Smooth.OneManifold

noncomputable section

/-- **A subset of the parameter plane is locally an arc**: this is
`Work.Smooth.SphereJordan.IsLocallyArc` for the subspace `P ⊆ ℝ × ℝ`. -/
abbrev IsLocallyArcP (P : Set (ℝ × ℝ)) : Prop := Work.Smooth.SphereJordan.IsLocallyArc ↥P

/-! ## `ℝ` and its open subsets -/

/-- **The real line is locally an arc.** -/
theorem isLocallyArc_real : Work.Smooth.SphereJordan.IsLocallyArc ℝ := by
  intro x
  refine ⟨{ V := Set.Ioo (x - 1) (x + 1)
            isOpen_V := isOpen_Ioo
            mem_V := ⟨by linarith, by linarith⟩
            homeo := homeomorphIooCentre x 1 one_pos
            homeo_zero := Subtype.ext (homeomorphIooCentre_zero x 1 one_pos) }⟩

/-- **An open subset of `ℝ` is locally an arc.** -/
theorem isLocallyArc_of_isOpen_real {A : Set ℝ} (hA : IsOpen A) :
    Work.Smooth.SphereJordan.IsLocallyArc ↥A := by
  intro x
  obtain ⟨ε, hε, hεsub⟩ := Metric.mem_nhds_iff.mp (hA.mem_nhds x.2)
  have hI : Set.Ioo ((x : ℝ) - ε) ((x : ℝ) + ε) ⊆ A := by
    refine fun t ht => hεsub ?_
    rw [Metric.mem_ball, Real.dist_eq, abs_sub_lt_iff]
    exact ⟨by linarith [ht.2], by linarith [ht.1]⟩
  refine ⟨{ V := Subtype.val ⁻¹' Set.Ioo ((x : ℝ) - ε) ((x : ℝ) + ε)
            isOpen_V := isOpen_Ioo.preimage continuous_subtype_val
            mem_V := by
              show (x : ℝ) ∈ Set.Ioo ((x : ℝ) - ε) ((x : ℝ) + ε)
              exact ⟨by linarith, by linarith⟩
            homeo := (homeomorphIooCentre (x : ℝ) ε hε).trans
              (Work.Smooth.SphereJordan.LocalArc.subtypeSubtypeHomeomorph hI)
            homeo_zero := ?_ }⟩
  apply Subtype.ext
  rw [Homeomorph.trans_apply]
  apply Subtype.ext
  exact homeomorphIooCentre_zero (x : ℝ) ε hε

/-- **An open interval is locally an arc.** -/
theorem isLocallyArc_Ioo (a b : ℝ) : Work.Smooth.SphereJordan.IsLocallyArc ↥(Set.Ioo a b) :=
  isLocallyArc_of_isOpen_real isOpen_Ioo

/-! ## Transport and covers -/

/-- **Local arcness transports along a homeomorphism** (the set version of
`Work.Smooth.OneManifold.isLocallyArc_of_homeomorph`): if `e : X ≃ₜ Y` and `A ⊆ X` is locally an
arc then so is `e '' A ⊆ Y`. -/
theorem isLocallyArc_image_of_homeomorph {X Y : Type*} [TopologicalSpace X] [TopologicalSpace Y]
    (e : X ≃ₜ Y) {A : Set X} (h : Work.Smooth.SphereJordan.IsLocallyArc ↥A) :
    Work.Smooth.SphereJordan.IsLocallyArc ↥(e '' A) :=
  isLocallyArc_of_homeomorph (e.image A) h

/-- **A congruence for local arcness.** -/
theorem isLocallyArc_of_eq {X : Type*} [TopologicalSpace X] {A B : Set X} (h : A = B)
    (hA : Work.Smooth.SphereJordan.IsLocallyArc ↥A) :
    Work.Smooth.SphereJordan.IsLocallyArc ↥B :=
  isLocallyArc_of_homeomorph (Homeomorph.setCongr h) hA

/-- **A space covered by open locally-arc pieces is locally arc.** -/
theorem isLocallyArc_of_isOpen_cover {X : Type*} [TopologicalSpace X] {ι : Type*} {U : ι → Set X}
    (hU : ∀ i, IsOpen (U i)) (hcov : ∀ x : X, ∃ i, x ∈ U i)
    (h : ∀ i, Work.Smooth.SphereJordan.IsLocallyArc ↥(U i)) :
    Work.Smooth.SphereJordan.IsLocallyArc X := by
  intro x
  obtain ⟨i, hi⟩ := hcov x
  obtain ⟨c⟩ := h i ⟨x, hi⟩
  have hsub : Subtype.val '' c.V ⊆ U i := by
    rintro y ⟨v, -, rfl⟩
    exact v.2
  have hVopen : IsOpen (Subtype.val '' c.V) :=
    (hU i).isOpenMap_subtype_val c.V c.isOpen_V
  have hEq : c.V = {y : ↥(U i) | (y : X) ∈ Subtype.val '' c.V} := by
    ext y
    exact ⟨fun hy => ⟨y, hy, rfl⟩, fun hy => by
      obtain ⟨v, hv, hve⟩ := hy
      rwa [show y = v from (Subtype.ext hve).symm]⟩
  refine ⟨{ V := Subtype.val '' c.V
            isOpen_V := hVopen
            mem_V := ⟨⟨x, hi⟩, c.mem_V, rfl⟩
            homeo := c.homeo.trans ((Homeomorph.setCongr hEq).trans
              (Work.Smooth.SphereJordan.LocalArc.subtypeSubtypeHomeomorph hsub).symm)
            homeo_zero := ?_ }⟩
  apply Subtype.ext
  show ((c.homeo 0 : c.V) : ↥(U i)) = x
  rw [c.homeo_zero]

/-! ## Graphs of continuous functions -/

/-- **The graph of a continuous function over an open subset of `ℝ` is locally an arc.**

The projection `(x, φ x) ↦ x` is a homeomorphism onto the open set `A`. -/
theorem isLocallyArc_graph_of_isOpen {A : Set ℝ} (hA : IsOpen A) {φ : ℝ → ℝ}
    (hφ : ContinuousOn φ A) :
    IsLocallyArcP {q : ℝ × ℝ | q.1 ∈ A ∧ q.2 = φ q.1} := by
  have hpair : Continuous fun t : ↥A => ((t : ℝ), φ (t : ℝ)) :=
    continuous_subtype_val.prodMk hφ.domRestrict
  let proj : ↥({q : ℝ × ℝ | q.1 ∈ A ∧ q.2 = φ q.1}) → ↥A :=
    fun q => ⟨q.1.1, q.2.1⟩
  let gr : ↥A → ↥({q : ℝ × ℝ | q.1 ∈ A ∧ q.2 = φ q.1}) :=
    fun t => ⟨((t : ℝ), φ (t : ℝ)), t.2, rfl⟩
  have hproj : Continuous proj :=
    Continuous.subtype_mk (continuous_fst.comp continuous_subtype_val) fun q => q.2.1
  have hgr : Continuous gr :=
    Continuous.subtype_mk hpair fun t => ⟨t.2, rfl⟩
  have e : ↥({q : ℝ × ℝ | q.1 ∈ A ∧ q.2 = φ q.1}) ≃ₜ ↥A :=
    { toFun := proj
      invFun := gr
      left_inv := fun q => Subtype.ext (Prod.ext rfl q.2.2.symm)
      right_inv := fun t => Subtype.ext rfl
      continuous_toFun := hproj
      continuous_invFun := hgr }
  exact isLocallyArc_of_homeomorph e.symm (isLocallyArc_of_isOpen_real hA)

/-- The graph of a continuous function over an open interval. -/
theorem isLocallyArc_graph {φ : ℝ → ℝ} {a b : ℝ} (hφ : ContinuousOn φ (Set.Ioo a b)) :
    IsLocallyArcP {q : ℝ × ℝ | q.1 ∈ Set.Ioo a b ∧ q.2 = φ q.1} :=
  isLocallyArc_graph_of_isOpen isOpen_Ioo hφ


/-- **The trace of a locally arc set on an open set is locally arc.** -/
theorem isLocallyArc_inter_of_isOpen {X : Type*} [TopologicalSpace X] {Z U : Set X}
    (hZ : Work.Smooth.SphereJordan.IsLocallyArc ↥Z) (hU : IsOpen U) :
    Work.Smooth.SphereJordan.IsLocallyArc ↥(Z ∩ U) := by
  have h1 : Work.Smooth.SphereJordan.IsLocallyArc ↥(Subtype.val ⁻¹' U : Set ↥Z) :=
    Work.Smooth.SphereJordan.LocalArc.isLocallyArcIsOpen hZ
      (hU.preimage continuous_subtype_val)
  refine isLocallyArc_of_homeomorph ?_ h1
  exact
  { toFun := fun y => ⟨(y.1 : X), y.1.2, y.2⟩
    invFun := fun y => ⟨⟨(y.1 : X), y.2.1⟩, y.2.2⟩
    left_inv := fun y => Subtype.ext rfl
    right_inv := fun y => Subtype.ext rfl
    continuous_toFun :=
      Continuous.subtype_mk (continuous_subtype_val.comp continuous_subtype_val) _
    continuous_invFun :=
      Continuous.subtype_mk (Continuous.subtype_mk continuous_subtype_val _) _ }

/-- **Congruence for local arcness along a homeomorphism of the ambient space.** -/
theorem isLocallyArc_of_image_eq {X Y : Type*} [TopologicalSpace X] [TopologicalSpace Y]
    (e : X ≃ₜ Y) {A : Set X} {B : Set Y} (h : e '' A = B)
    (hA : Work.Smooth.SphereJordan.IsLocallyArc ↥A) :
    Work.Smooth.SphereJordan.IsLocallyArc ↥B :=
  isLocallyArc_of_eq h (isLocallyArc_image_of_homeomorph e hA)


/-- The preimage of a locally arc set under the subtype inclusion is locally arc. -/
theorem isLocallyArc_preimage_subtypeVal {X : Type*} [TopologicalSpace X] {U : Set X} {s : Set X}
    (hs : s ⊆ U) (h : Work.Smooth.SphereJordan.IsLocallyArc ↥s) :
    Work.Smooth.SphereJordan.IsLocallyArc ↥(Subtype.val ⁻¹' s : Set ↥U) :=
  isLocallyArc_of_homeomorph (Work.Smooth.SphereJordan.LocalArc.subtypeSubtypeHomeomorph hs) h

/-- The image of a locally arc set under the subtype inclusion is locally arc. -/
theorem isLocallyArc_subtypeVal_image {X : Type*} [TopologicalSpace X] {U : Set X}
    {s : Set ↥U} (h : Work.Smooth.SphereJordan.IsLocallyArc ↥s) :
    Work.Smooth.SphereJordan.IsLocallyArc ↥(Subtype.val '' s) := by
  have hs : Subtype.val '' s ⊆ U := by rintro z ⟨y, -, rfl⟩; exact y.2
  have heq : {y : ↥U | (y : X) ∈ Subtype.val '' s} = s := by
    ext y
    exact ⟨fun h' => by
        obtain ⟨w, hw, hwe⟩ := h'
        rwa [show y = w from Subtype.ext hwe.symm], fun h' => ⟨y, h', rfl⟩⟩
  exact isLocallyArc_of_homeomorph (Work.Smooth.SphereJordan.LocalArc.subtypeSubtypeHomeomorph hs).symm
    (isLocallyArc_of_eq heq.symm h)


/-- **The coordinate swap of the plane is a homeomorphism.** -/
def prodSwapHomeomorph : ℝ × ℝ ≃ₜ ℝ × ℝ where
  toFun z := (z.2, z.1)
  invFun z := (z.2, z.1)
  left_inv z := rfl
  right_inv z := rfl
  continuous_toFun := continuous_snd.prodMk continuous_fst
  continuous_invFun := continuous_snd.prodMk continuous_fst

/-- **The graph of a continuous function over an open interval, read over the second
coordinate.** -/
theorem isLocallyArc_graph_snd {φ : ℝ → ℝ} {a b : ℝ} (hφ : ContinuousOn φ (Set.Ioo a b)) :
    IsLocallyArcP {q : ℝ × ℝ | q.2 ∈ Set.Ioo a b ∧ q.1 = φ q.2} := by
  have h' : prodSwapHomeomorph '' {q : ℝ × ℝ | q.1 ∈ Set.Ioo a b ∧ q.2 = φ q.1}
      = {q : ℝ × ℝ | q.2 ∈ Set.Ioo a b ∧ q.1 = φ q.2} := by
    ext q
    constructor
    · rintro ⟨z, hz, hzq⟩
      rw [← hzq]
      exact hz
    · intro hq
      refine ⟨(q.2, q.1), hq, ?_⟩
      exact Prod.ext rfl rfl
  exact isLocallyArc_of_image_eq prodSwapHomeomorph h' (isLocallyArc_graph hφ)

/-! ## The corner `{max a b = 0}` -/

/-- The parametrisation `t ↦ (min t 0, -max t 0)` of the union of the two negative coordinate
half-axes. -/
def cornerPt (t : ℝ) : ℝ × ℝ := (min t 0, -max t 0)

theorem cornerPt_max (t : ℝ) : max (cornerPt t).1 (cornerPt t).2 = 0 := by
  rcases le_total t 0 with h | h
  · rw [cornerPt, min_eq_left h, max_eq_right h]
    show max t (-(0 : ℝ)) = 0
    rw [neg_zero]
    exact max_eq_right h
  · rw [cornerPt, min_eq_right h, max_eq_left h]
    show max (0 : ℝ) (-t) = 0
    exact max_eq_left (neg_nonpos.mpr h)

theorem cornerPt_fst_sub_snd (t : ℝ) : (cornerPt t).1 - (cornerPt t).2 = t := by
  rw [cornerPt]
  have := min_add_max t 0
  linarith

/-- **The corner `{(a, b) | max a b = 0}` is locally an arc** (it is homeomorphic to `ℝ`). -/
theorem isLocallyArc_max_zero :
    IsLocallyArcP {q : ℝ × ℝ | max q.1 q.2 = 0} := by
  have e : ℝ ≃ₜ ↥({q : ℝ × ℝ | max q.1 q.2 = 0}) :=
    { toFun := fun t => ⟨cornerPt t, cornerPt_max t⟩
      invFun := fun q => q.1.1 - q.1.2
      left_inv := fun t => cornerPt_fst_sub_snd t
      right_inv := fun q => by
        apply Subtype.ext
        have hq : max (q : ℝ × ℝ).1 (q : ℝ × ℝ).2 = 0 := q.2
        obtain ⟨h1, h2, h3⟩ : (q : ℝ × ℝ).1 ≤ 0 ∧ (q : ℝ × ℝ).2 ≤ 0 ∧
            ((q : ℝ × ℝ).1 = 0 ∨ (q : ℝ × ℝ).2 = 0) := by
          have hle1 : (q : ℝ × ℝ).1 ≤ 0 := le_trans (le_max_left _ _) (le_of_eq hq)
          have hle2 : (q : ℝ × ℝ).2 ≤ 0 := le_trans (le_max_right _ _) (le_of_eq hq)
          refine ⟨hle1, hle2, ?_⟩
          by_contra hc
          rw [not_or] at hc
          obtain ⟨hc1, hc2⟩ := hc
          have hlt : max (q : ℝ × ℝ).1 (q : ℝ × ℝ).2 < 0 :=
            max_lt (lt_of_le_of_ne hle1 hc1) (lt_of_le_of_ne hle2 hc2)
          rw [hq] at hlt
          exact lt_irrefl 0 hlt
        show cornerPt ((q : ℝ × ℝ).1 - (q : ℝ × ℝ).2) = (q : ℝ × ℝ)
        rcases h3 with h3 | h3
        · have h4 : 0 ≤ -(q : ℝ × ℝ).2 := neg_nonneg.mpr h2
          rw [h3, zero_sub, cornerPt, min_eq_right h4, max_eq_left h4, neg_neg]
          exact Prod.ext h3.symm rfl
        · have h4 : (q : ℝ × ℝ).1 ≤ 0 := h1
          rw [h3, sub_zero, cornerPt, min_eq_left h4, max_eq_right h4, neg_zero]
          exact Prod.ext rfl h3.symm
      continuous_toFun :=
        Continuous.subtype_mk (f := cornerPt) (by
          show Continuous fun t : ℝ => (min t 0, -max t 0)
          fun_prop) (fun t => cornerPt_max t)
      continuous_invFun := by
        show Continuous fun q : ↥({q : ℝ × ℝ | max q.1 q.2 = 0}) =>
          (q : ℝ × ℝ).1 - (q : ℝ × ℝ).2
        fun_prop }
  exact isLocallyArc_of_homeomorph e isLocallyArc_real

end

end Work.Smooth.OneManifold
