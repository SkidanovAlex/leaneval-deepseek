import Mathlib
import Submission.Work.OROneRel.unionAmalgamDefs

/-!
# (Finite) Seifert--van Kampen for `2`-complexes, in the `PresentedGroup` setting

This file proves `Work.OROneRel.presentedGroup_union_amalgam`.  The proof is entirely algebraic
(no topology): we exhibit two mutually inverse homomorphisms

* `ugOut : Monoid.PushoutI (UGFamPhi …) →* PresentedGroup (UGRel …)`, the universal map out of the
  amalgam, induced by the two inclusions of the vertex groups, and
* `ugIn : PresentedGroup (UGRel …) →* Monoid.PushoutI (UGFamPhi …)`, which sends a generator `e : E`
  to the class of `e` in the first vertex group if `e ∈ E₁` and to the class in the second vertex
  group otherwise.

For `e ∈ E₁ ∩ E₂` the two branches agree, because both are the image under `Monoid.PushoutI.base`
of the class of `e` in the amalgamating group (`Monoid.PushoutI.of_apply_eq_base`).  This is the
only place where the amalgamating maps are used, and it is exactly what makes `ugIn` kill the
relators coming from `S₂` (whose letters may lie in `E₁`).
-/

set_option autoImplicit false
set_option linter.unusedVariables false

namespace Work.OROneRel

universe u

section Amalgam

variable {E : Type u}
variable (E₁ E₂ : Set E)
variable (S₁ : Set (FreeGroup ↥E₁)) (S₂ : Set (FreeGroup ↥E₂))
variable (S₀ : Set (FreeGroup ↥(E₁ ∩ E₂)))
variable (h₁ : FreeGroup.map (inc₁ E₁ E₂) '' S₀ ⊆ S₁)
variable (h₂ : FreeGroup.map (inc₂ E₁ E₂) '' S₀ ⊆ S₂)

/-! ### The relators of the pieces lie among the relators of the union -/

theorem ugSubset₁ : FreeGroup.map (incVal E₁) '' S₁ ⊆ UGRel E₁ E₂ S₁ S₂ :=
  fun _ hx => Or.inl hx

theorem ugSubset₂ : FreeGroup.map (incVal E₂) '' S₂ ⊆ UGRel E₁ E₂ S₁ S₂ :=
  fun _ hx => Or.inr hx

theorem ugSubset₀ (h₁' : FreeGroup.map (inc₁ E₁ E₂) '' S₀ ⊆ S₁) :
    FreeGroup.map (incVal (E₁ ∩ E₂)) '' S₀ ⊆ UGRel E₁ E₂ S₁ S₂ := by
  rintro y ⟨r, hr, rfl⟩
  refine Or.inl ⟨FreeGroup.map (inc₁ E₁ E₂) r, h₁' ⟨r, hr, rfl⟩, ?_⟩
  have hfun : (fun a : ↥(E₁ ∩ E₂) => incVal E₁ (inc₁ E₁ E₂ a)) = incVal (E₁ ∩ E₂) := by
    funext x
    rfl
  rw [fg_map_map, hfun]

/-! ### The map out of the amalgam -/

/-- The two vertex groups map into the fundamental group of the union. -/
noncomputable def ugLiftF :
    ∀ i : Bool, UGFam E₁ E₂ S₁ S₂ i →* PresentedGroup (UGRel E₁ E₂ S₁ S₂)
  | false => presentedMap (incVal E₁) (ugSubset₁ E₁ E₂ S₁ S₂)
  | true => presentedMap (incVal E₂) (ugSubset₂ E₁ E₂ S₁ S₂)

/-- The two maps out of the vertex groups agree on the amalgamating group. -/
theorem ugLiftF_comp (i : Bool) :
    (ugLiftF E₁ E₂ S₁ S₂ i).comp (UGFamPhi E₁ E₂ S₁ S₂ S₀ h₁ h₂ i) =
      presentedMap (incVal (E₁ ∩ E₂)) (ugSubset₀ E₁ E₂ S₁ S₂ S₀ h₁) := by
  cases i with
  | false =>
    change (presentedMap (incVal E₁) (ugSubset₁ E₁ E₂ S₁ S₂)).comp
        (presentedMap (inc₁ E₁ E₂) h₁) =
      presentedMap (incVal (E₁ ∩ E₂)) (ugSubset₀ E₁ E₂ S₁ S₂ S₀ h₁)
    refine presentedGroup_hom_ext fun x => ?_
    simp only [MonoidHom.comp_apply, presentedMap_of]
    rfl
  | true =>
    change (presentedMap (incVal E₂) (ugSubset₂ E₁ E₂ S₁ S₂)).comp
        (presentedMap (inc₂ E₁ E₂) h₂) =
      presentedMap (incVal (E₁ ∩ E₂)) (ugSubset₀ E₁ E₂ S₁ S₂ S₀ h₁)
    refine presentedGroup_hom_ext fun x => ?_
    simp only [MonoidHom.comp_apply, presentedMap_of]
    rfl

/-- The universal map out of the amalgam into the fundamental group of the union. -/
noncomputable def ugOut :
    Monoid.PushoutI (UGFamPhi E₁ E₂ S₁ S₂ S₀ h₁ h₂) →* PresentedGroup (UGRel E₁ E₂ S₁ S₂) :=
  Monoid.PushoutI.lift (ugLiftF E₁ E₂ S₁ S₂)
    (presentedMap (incVal (E₁ ∩ E₂)) (ugSubset₀ E₁ E₂ S₁ S₂ S₀ h₁))
    (ugLiftF_comp E₁ E₂ S₁ S₂ S₀ h₁ h₂)

theorem ugOut_of_false (g : PresentedGroup S₁) :
    ugOut E₁ E₂ S₁ S₂ S₀ h₁ h₂
        (Monoid.PushoutI.of (φ := UGFamPhi E₁ E₂ S₁ S₂ S₀ h₁ h₂) false g) =
      presentedMap (incVal E₁) (ugSubset₁ E₁ E₂ S₁ S₂) g :=
  Monoid.PushoutI.lift_of (ugLiftF E₁ E₂ S₁ S₂)
    (presentedMap (incVal (E₁ ∩ E₂)) (ugSubset₀ E₁ E₂ S₁ S₂ S₀ h₁))
    (ugLiftF_comp E₁ E₂ S₁ S₂ S₀ h₁ h₂) (i := false) g

theorem ugOut_of_true (g : PresentedGroup S₂) :
    ugOut E₁ E₂ S₁ S₂ S₀ h₁ h₂
        (Monoid.PushoutI.of (φ := UGFamPhi E₁ E₂ S₁ S₂ S₀ h₁ h₂) true g) =
      presentedMap (incVal E₂) (ugSubset₂ E₁ E₂ S₁ S₂) g :=
  Monoid.PushoutI.lift_of (ugLiftF E₁ E₂ S₁ S₂)
    (presentedMap (incVal (E₁ ∩ E₂)) (ugSubset₀ E₁ E₂ S₁ S₂ S₀ h₁))
    (ugLiftF_comp E₁ E₂ S₁ S₂ S₀ h₁ h₂) (i := true) g

/-! ### The map into the amalgam -/

/-- A generator of the union is sent to the vertex group containing it (preferring the first). -/
noncomputable def ugThetaFam (hE : ∀ e : E, e ∈ E₁ ∨ e ∈ E₂) :
    E → Monoid.PushoutI (UGFamPhi E₁ E₂ S₁ S₂ S₀ h₁ h₂) := by
  classical
  exact fun e =>
    if h : e ∈ E₁ then
      Monoid.PushoutI.of (φ := UGFamPhi E₁ E₂ S₁ S₂ S₀ h₁ h₂) false (PresentedGroup.of ⟨e, h⟩)
    else
      Monoid.PushoutI.of (φ := UGFamPhi E₁ E₂ S₁ S₂ S₀ h₁ h₂) true
        (PresentedGroup.of ⟨e, (hE e).resolve_left h⟩)

theorem ugThetaFam_of_mem (hE : ∀ e : E, e ∈ E₁ ∨ e ∈ E₂) (e : E) (h : e ∈ E₁) :
    ugThetaFam E₁ E₂ S₁ S₂ S₀ h₁ h₂ hE e =
      Monoid.PushoutI.of (φ := UGFamPhi E₁ E₂ S₁ S₂ S₀ h₁ h₂) false
        (PresentedGroup.of ⟨e, h⟩) := by
  simp only [ugThetaFam, dif_pos h]

theorem ugThetaFam_of_notMem (hE : ∀ e : E, e ∈ E₁ ∨ e ∈ E₂) (e : E) (h : e ∉ E₁) :
    ugThetaFam E₁ E₂ S₁ S₂ S₀ h₁ h₂ hE e =
      Monoid.PushoutI.of (φ := UGFamPhi E₁ E₂ S₁ S₂ S₀ h₁ h₂) true
        (PresentedGroup.of ⟨e, (hE e).resolve_left h⟩) := by
  simp only [ugThetaFam, dif_neg h]

/-- A generator of `E₂` lands in the second vertex group, *even if it also lies in* `E₁`
(this is where `Monoid.PushoutI.of_apply_eq_base` is used). -/
theorem ugThetaFam_incVal₂ (hE : ∀ e : E, e ∈ E₁ ∨ e ∈ E₂) (a : ↥E₂) :
    ugThetaFam E₁ E₂ S₁ S₂ S₀ h₁ h₂ hE (incVal E₂ a) =
      Monoid.PushoutI.of (φ := UGFamPhi E₁ E₂ S₁ S₂ S₀ h₁ h₂) true (PresentedGroup.of a) := by
  change ugThetaFam E₁ E₂ S₁ S₂ S₀ h₁ h₂ hE (a : E) = _
  by_cases h : (a : E) ∈ E₁
  · rw [ugThetaFam_of_mem E₁ E₂ S₁ S₂ S₀ h₁ h₂ hE (a : E) h]
    have key₁ : Monoid.PushoutI.of (φ := UGFamPhi E₁ E₂ S₁ S₂ S₀ h₁ h₂) false
        (PresentedGroup.of (⟨(a : E), h⟩ : ↥E₁)) =
        Monoid.PushoutI.base (UGFamPhi E₁ E₂ S₁ S₂ S₀ h₁ h₂)
          (PresentedGroup.of (⟨(a : E), ⟨h, a.2⟩⟩ : ↥(E₁ ∩ E₂))) := by
      have hφ : (UGFamPhi E₁ E₂ S₁ S₂ S₀ h₁ h₂) false
          (PresentedGroup.of (⟨(a : E), ⟨h, a.2⟩⟩ : ↥(E₁ ∩ E₂))) =
          PresentedGroup.of (⟨(a : E), h⟩ : ↥E₁) := by
        change presentedMap (inc₁ E₁ E₂) h₁
          (PresentedGroup.of (⟨(a : E), ⟨h, a.2⟩⟩ : ↥(E₁ ∩ E₂))) = _
        rw [presentedMap_of]
        rfl
      rw [← hφ]
      exact Monoid.PushoutI.of_apply_eq_base _ false _
    have key₂ : Monoid.PushoutI.of (φ := UGFamPhi E₁ E₂ S₁ S₂ S₀ h₁ h₂) true
        (PresentedGroup.of a) =
        Monoid.PushoutI.base (UGFamPhi E₁ E₂ S₁ S₂ S₀ h₁ h₂)
          (PresentedGroup.of (⟨(a : E), ⟨h, a.2⟩⟩ : ↥(E₁ ∩ E₂))) := by
      have hφ : (UGFamPhi E₁ E₂ S₁ S₂ S₀ h₁ h₂) true
          (PresentedGroup.of (⟨(a : E), ⟨h, a.2⟩⟩ : ↥(E₁ ∩ E₂))) = PresentedGroup.of a := by
        change presentedMap (inc₂ E₁ E₂) h₂
          (PresentedGroup.of (⟨(a : E), ⟨h, a.2⟩⟩ : ↥(E₁ ∩ E₂))) = _
        rw [presentedMap_of]
        rfl
      rw [← hφ]
      exact Monoid.PushoutI.of_apply_eq_base _ true _
    rw [key₁, key₂]
  · rw [ugThetaFam_of_notMem E₁ E₂ S₁ S₂ S₀ h₁ h₂ hE (a : E) h]

/-- The lift of `ugThetaFam` to the free group on the edge set of the union. -/
noncomputable def ugTheta (hE : ∀ e : E, e ∈ E₁ ∨ e ∈ E₂) :
    FreeGroup E →* Monoid.PushoutI (UGFamPhi E₁ E₂ S₁ S₂ S₀ h₁ h₂) :=
  FreeGroup.lift (ugThetaFam E₁ E₂ S₁ S₂ S₀ h₁ h₂ hE)

/-- The first vertex group, composed into the amalgam. -/
noncomputable def ugTheta₁ :
    FreeGroup ↥E₁ →* Monoid.PushoutI (UGFamPhi E₁ E₂ S₁ S₂ S₀ h₁ h₂) :=
  (Monoid.PushoutI.of (φ := UGFamPhi E₁ E₂ S₁ S₂ S₀ h₁ h₂) false).comp (PresentedGroup.mk S₁)

/-- The second vertex group, composed into the amalgam. -/
noncomputable def ugTheta₂ :
    FreeGroup ↥E₂ →* Monoid.PushoutI (UGFamPhi E₁ E₂ S₁ S₂ S₀ h₁ h₂) :=
  (Monoid.PushoutI.of (φ := UGFamPhi E₁ E₂ S₁ S₂ S₀ h₁ h₂) true).comp (PresentedGroup.mk S₂)

theorem ugTheta_comp_map₁ (hE : ∀ e : E, e ∈ E₁ ∨ e ∈ E₂) :
    (ugTheta E₁ E₂ S₁ S₂ S₀ h₁ h₂ hE).comp (FreeGroup.map (incVal E₁)) =
      ugTheta₁ E₁ E₂ S₁ S₂ S₀ h₁ h₂ := by
  refine FreeGroup.ext_hom _ _ fun a => ?_
  rw [MonoidHom.comp_apply, FreeGroup.map.of, ugTheta, FreeGroup.lift_apply_of,
    ugThetaFam_of_mem E₁ E₂ S₁ S₂ S₀ h₁ h₂ hE (incVal E₁ a) a.2]
  rfl

theorem ugTheta_comp_map₂ (hE : ∀ e : E, e ∈ E₁ ∨ e ∈ E₂) :
    (ugTheta E₁ E₂ S₁ S₂ S₀ h₁ h₂ hE).comp (FreeGroup.map (incVal E₂)) =
      ugTheta₂ E₁ E₂ S₁ S₂ S₀ h₁ h₂ := by
  refine FreeGroup.ext_hom _ _ fun a => ?_
  rw [MonoidHom.comp_apply, FreeGroup.map.of, ugTheta, FreeGroup.lift_apply_of,
    ugThetaFam_incVal₂ E₁ E₂ S₁ S₂ S₀ h₁ h₂ hE a]
  rfl

theorem ugTheta₁_relator (r₁ : FreeGroup ↥E₁) (hr₁ : r₁ ∈ S₁) :
    ugTheta₁ E₁ E₂ S₁ S₂ S₀ h₁ h₂ r₁ = 1 := by
  change (Monoid.PushoutI.of (φ := UGFamPhi E₁ E₂ S₁ S₂ S₀ h₁ h₂) false)
    ((PresentedGroup.mk S₁) r₁) = 1
  rw [PresentedGroup.one_of_mem hr₁]
  exact map_one _

theorem ugTheta₂_relator (r₂ : FreeGroup ↥E₂) (hr₂ : r₂ ∈ S₂) :
    ugTheta₂ E₁ E₂ S₁ S₂ S₀ h₁ h₂ r₂ = 1 := by
  change (Monoid.PushoutI.of (φ := UGFamPhi E₁ E₂ S₁ S₂ S₀ h₁ h₂) true)
    ((PresentedGroup.mk S₂) r₂) = 1
  rw [PresentedGroup.one_of_mem hr₂]
  exact map_one _

/-- The relators of the union are killed by `ugTheta`. -/
theorem ugTheta_relator (hE : ∀ e : E, e ∈ E₁ ∨ e ∈ E₂) (r : FreeGroup E)
    (hr : r ∈ UGRel E₁ E₂ S₁ S₂) :
    ugTheta E₁ E₂ S₁ S₂ S₀ h₁ h₂ hE r = 1 := by
  rcases hr with hr | hr
  · obtain ⟨r₁, hr₁, rfl⟩ := hr
    exact (DFunLike.congr_fun (ugTheta_comp_map₁ E₁ E₂ S₁ S₂ S₀ h₁ h₂ hE) r₁).trans
      (ugTheta₁_relator E₁ E₂ S₁ S₂ S₀ h₁ h₂ r₁ hr₁)
  · obtain ⟨r₂, hr₂, rfl⟩ := hr
    exact (DFunLike.congr_fun (ugTheta_comp_map₂ E₁ E₂ S₁ S₂ S₀ h₁ h₂ hE) r₂).trans
      (ugTheta₂_relator E₁ E₂ S₁ S₂ S₀ h₁ h₂ r₂ hr₂)

/-- The induced map from the fundamental group of the union into the amalgam. -/
noncomputable def ugIn (hE : ∀ e : E, e ∈ E₁ ∨ e ∈ E₂) :
    PresentedGroup (UGRel E₁ E₂ S₁ S₂) →* Monoid.PushoutI (UGFamPhi E₁ E₂ S₁ S₂ S₀ h₁ h₂) :=
  PresentedGroup.toGroup (f := ugThetaFam E₁ E₂ S₁ S₂ S₀ h₁ h₂ hE)
    (fun r hr => ugTheta_relator E₁ E₂ S₁ S₂ S₀ h₁ h₂ hE r hr)

theorem ugIn_of (hE : ∀ e : E, e ∈ E₁ ∨ e ∈ E₂) (e : E) :
    ugIn E₁ E₂ S₁ S₂ S₀ h₁ h₂ hE (PresentedGroup.of e) =
      ugThetaFam E₁ E₂ S₁ S₂ S₀ h₁ h₂ hE e :=
  PresentedGroup.toGroup.of _

/-! ### The two round trips -/

theorem ugOut_ugIn (hE : ∀ e : E, e ∈ E₁ ∨ e ∈ E₂) (e : E) :
    ugOut E₁ E₂ S₁ S₂ S₀ h₁ h₂
        (ugIn E₁ E₂ S₁ S₂ S₀ h₁ h₂ hE (PresentedGroup.of e)) = PresentedGroup.of e := by
  rw [ugIn_of]
  by_cases h : e ∈ E₁
  · rw [ugThetaFam_of_mem E₁ E₂ S₁ S₂ S₀ h₁ h₂ hE e h]
    rw [ugOut_of_false, presentedMap_of]
    rfl
  · rw [ugThetaFam_of_notMem E₁ E₂ S₁ S₂ S₀ h₁ h₂ hE e h]
    rw [ugOut_of_true, presentedMap_of]
    rfl

/-- `ugOut ∘ ugIn = id` on the fundamental group of the union, checked on generators. -/
theorem ugOut_comp_ugIn (hE : ∀ e : E, e ∈ E₁ ∨ e ∈ E₂) :
    (ugOut E₁ E₂ S₁ S₂ S₀ h₁ h₂).comp (ugIn E₁ E₂ S₁ S₂ S₀ h₁ h₂ hE) =
      MonoidHom.id (PresentedGroup (UGRel E₁ E₂ S₁ S₂)) := by
  refine presentedGroup_hom_ext fun e => ?_
  show ugOut E₁ E₂ S₁ S₂ S₀ h₁ h₂
      (ugIn E₁ E₂ S₁ S₂ S₀ h₁ h₂ hE (PresentedGroup.of e)) = PresentedGroup.of e
  exact ugOut_ugIn E₁ E₂ S₁ S₂ S₀ h₁ h₂ hE e

/-- `ugIn ∘ ugOut = id` on the amalgam, checked on the two vertex groups. -/
theorem ugIn_comp_ugOut (hE : ∀ e : E, e ∈ E₁ ∨ e ∈ E₂) :
    (ugIn E₁ E₂ S₁ S₂ S₀ h₁ h₂ hE).comp (ugOut E₁ E₂ S₁ S₂ S₀ h₁ h₂) =
      MonoidHom.id (Monoid.PushoutI (UGFamPhi E₁ E₂ S₁ S₂ S₀ h₁ h₂)) := by
  refine Monoid.PushoutI.hom_ext_nonempty (φ := UGFamPhi E₁ E₂ S₁ S₂ S₀ h₁ h₂) fun i => ?_
  cases i with
  | false =>
    refine presentedGroup_hom_ext fun x => ?_
    show ugIn E₁ E₂ S₁ S₂ S₀ h₁ h₂ hE (ugOut E₁ E₂ S₁ S₂ S₀ h₁ h₂
        (Monoid.PushoutI.of (φ := UGFamPhi E₁ E₂ S₁ S₂ S₀ h₁ h₂) false (PresentedGroup.of x))) =
      Monoid.PushoutI.of (φ := UGFamPhi E₁ E₂ S₁ S₂ S₀ h₁ h₂) false (PresentedGroup.of x)
    rw [ugOut_of_false, presentedMap_of]
    rw [ugIn_of, ugThetaFam_of_mem E₁ E₂ S₁ S₂ S₀ h₁ h₂ hE (incVal E₁ x) x.2]
    rfl
  | true =>
    refine presentedGroup_hom_ext fun x => ?_
    show ugIn E₁ E₂ S₁ S₂ S₀ h₁ h₂ hE (ugOut E₁ E₂ S₁ S₂ S₀ h₁ h₂
        (Monoid.PushoutI.of (φ := UGFamPhi E₁ E₂ S₁ S₂ S₀ h₁ h₂) true (PresentedGroup.of x))) =
      Monoid.PushoutI.of (φ := UGFamPhi E₁ E₂ S₁ S₂ S₀ h₁ h₂) true (PresentedGroup.of x)
    rw [ugOut_of_true, presentedMap_of]
    rw [ugIn_of, ugThetaFam_incVal₂ E₁ E₂ S₁ S₂ S₀ h₁ h₂ hE x]

end Amalgam

/-- **(Finite) Seifert--van Kampen for `2`-complexes, in the `PresentedGroup` setting.**

Model a `2`-complex as a type `E` of edges together with a set of relators in `FreeGroup E` (so that
its fundamental group is a `PresentedGroup`; the relators include both the attaching words of the
`2`-cells and the edges of a spanning tree, which is why the statement needs no graph theory:
"connected" and "simply connected" enter only through the choice of the relator sets, and the
relator set of the intersection is assumed to map into both others).

Let `Γ = A ∪ B` have edge sets `E₁`, `E₂` covering `E`; let `S₁`, `S₂` be the relator sets of `A`
and `B`, and `S₀` that of the intersection `A ∩ B`, mapping into `S₁` and `S₂` under the inclusion
of edge sets.  Then

  `π₁(Γ) ≅ π₁(A) ∗_{π₁(A ∩ B)} π₁(B)`.

This is the finite form of the result missing from Mathlib and from this workspace (there is no
`vanKampen` anywhere here); it is the linchpin of the *amalgam* route to the residual case of
`Work.OROneRel.magnusStepCase2`.  Applied to the window domains `D` and `tD` of the `Z`-cover
(whose intersection carries no `2`-cell in the minimal `Z`-domain) it gives
`π₁(D ∪ tD) ≅ π₁(D) ∗_{π₁(D ∩ tD)} π₁(tD)`, and iterating it gives the *line amalgam*
`ker (presentedCohom c u l hc) = ⋯ ∗_A tHt^{-1} ∗_A H ∗_A t^{-1}Ht^{-1} ⋯` with `H = π₁(D)`,
`A = π₁(D ∩ t^{-1}D)`, whose normal form yields Britton's normal form and hence the HNN splitting.

Proof (no topology, and no connectedness hypotheses are needed for the algebra): `Monoid.PushoutI`
gives a map *out of* the amalgam, defined by the two canonical maps `π₁(A) → π₁(Γ)`,
`π₁(B) → π₁(Γ)`, which agree on `π₁(A ∩ B)` because both are induced by the inclusion `E₁ ∩ E₂ → E`;
the inverse `π₁(Γ) →` the amalgam sends a generator `e : E` to the class of `e` in `π₁(A)` if
`e ∈ E₁` and in `π₁(B)` otherwise -- for `e ∈ E₁ ∩ E₂` the two branches agree in the amalgam because
they are the two images of the class of `e` in `π₁(A ∩ B)` (this is `Monoid.PushoutI.of_apply_eq_base`,
so no hypothesis on `S₀` is needed beyond the well-definedness of the two maps).  It kills the
relators of `Γ`: for a relator coming from `S₁` all its letters are edges of `A`, so the chosen branch
is the `A` branch and the relator dies in `π₁(A)` (`presentedMap_of` and `fg_lift_comp_map`); similarly
for `S₂`.  The two composites are the identity on generators, hence everywhere
(`presentedGroup_hom_ext` and `Monoid.PushoutI.hom_ext`). -/
theorem presentedGroup_union_amalgam {E : Type*} (E₁ E₂ : Set E)
    (hE : ∀ e : E, e ∈ E₁ ∨ e ∈ E₂)
    (S₁ : Set (FreeGroup ↥E₁)) (S₂ : Set (FreeGroup ↥E₂)) (S₀ : Set (FreeGroup ↥(E₁ ∩ E₂)))
    (h₁ : FreeGroup.map (Work.OROneRel.inc₁ E₁ E₂) '' S₀ ⊆ S₁)
    (h₂ : FreeGroup.map (Work.OROneRel.inc₂ E₁ E₂) '' S₀ ⊆ S₂) :
    Nonempty (PresentedGroup (Work.OROneRel.UGRel E₁ E₂ S₁ S₂) ≃*
      Monoid.PushoutI (Work.OROneRel.UGFamPhi E₁ E₂ S₁ S₂ S₀ h₁ h₂)) :=
  ⟨MonoidHom.toMulEquiv (ugIn E₁ E₂ S₁ S₂ S₀ h₁ h₂ hE) (ugOut E₁ E₂ S₁ S₂ S₀ h₁ h₂)
    (ugOut_comp_ugIn E₁ E₂ S₁ S₂ S₀ h₁ h₂ hE) (ugIn_comp_ugOut E₁ E₂ S₁ S₂ S₀ h₁ h₂ hE)⟩

end Work.OROneRel
