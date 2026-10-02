import Mathlib
import Submission.Work.Serre.SPC.Setup
import Submission.Work.RatHurewicz.AttachRange.AttachInclInj
import Submission.Work.RatHurewicz.attachIncl_isOpenMap_range

-- Lean v4.35.0-rc3: restore v4.34 instance-unification transparency (port).
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
set_option synthInstance.maxHeartbeats 400000

/-!
# Geometry of one cell attachment

For a map `g : Γ → B`, an attachment `Γ' = attachCells n Γ ι fr` and an extension
`g' : Γ' → B` of `g` (`g' (attachIncl x) = g x`), the inclusion of `Γ` in `Γ'` is a homeomorphism
onto its range, and the pullback of a map `p : E → B` along `g'` restricted to the old part is the
pullback of `p` along `g`.
-/

open CategoryTheory CategoryTheory.Limits
open scoped Topology

set_option backward.isDefEq.respectTransparency false

namespace Work.Serre.SPC

noncomputable section

variable {E B Γ : Type} [TopologicalSpace E] [TopologicalSpace B] [TopologicalSpace Γ]

/-- **The inclusion of `Γ` into the attached space is a homeomorphism onto its range**: it is
injective and inducing. -/
def attachRangeHomeo (n : ℕ) (ι : Type)
    (fr : ι → C(Work.RatHurewicz.cellSphere n, Γ)) :
    Γ ≃ₜ ↥(Set.range fun y : Γ => Work.RatHurewicz.attachIncl n Γ ι fr y) :=
  (Equiv.ofBijective (fun y => (⟨Work.RatHurewicz.attachIncl n Γ ι fr y, ⟨y, rfl⟩⟩ :
      ↥(Set.range fun y : Γ => Work.RatHurewicz.attachIncl n Γ ι fr y)))
    ⟨fun y y' h => Work.RatHurewicz.AttachRange.attachIncl_injective n Γ ι fr
        (Subtype.ext_iff.mp h),
      fun z => by
        obtain ⟨y, hy⟩ := z.2
        exact ⟨y, Subtype.ext hy⟩⟩).toHomeomorphOfContinuousOpen
    (Continuous.subtype_mk (Work.RatHurewicz.attachIncl n Γ ι fr).continuous _)
    (Work.RatHurewicz.isOpenMap_codRestrict_range
      (Work.RatHurewicz.isInducing_attachIncl n Γ ι fr))

/-- The homeomorphism `attachRangeHomeo` is the corestriction of `attachIncl`. -/
@[simp]
theorem attachRangeHomeo_apply (n : ℕ) (ι : Type)
    (fr : ι → C(Work.RatHurewicz.cellSphere n, Γ)) (y : Γ) :
    ((attachRangeHomeo (Γ := Γ) n ι fr y : ↥(Set.range fun y : Γ =>
      Work.RatHurewicz.attachIncl n Γ ι fr y)) : Work.RatHurewicz.attachCells n Γ ι fr)
      = Work.RatHurewicz.attachIncl n Γ ι fr y := rfl

/-- **The pullback over the old part is the old pullback.** -/
def pullbackOldHomeo (p : C(E, B)) (g : C(Γ, B)) (n : ℕ) (ι : Type)
    (fr : ι → C(Work.RatHurewicz.cellSphere n, Γ))
    (g' : C(Work.RatHurewicz.attachCells n Γ ι fr, B))
    (hg' : ∀ x : Γ, g' (Work.RatHurewicz.attachIncl n Γ ι fr x) = g x) :
    Work.StemsB.Pullback g p ≃ₜ
      ↥((Work.StemsB.pullbackFst g' p) ⁻¹'
        (Set.range fun y : Γ => Work.RatHurewicz.attachIncl n Γ ι fr y)) where
  toFun x :=
    ⟨⟨(Work.RatHurewicz.attachIncl n Γ ι fr (Subtype.val x).1, (Subtype.val x).2), by
        rw [hg' (Subtype.val x).1]; exact x.2⟩, ⟨(Subtype.val x).1, rfl⟩⟩
  invFun z :=
    ⟨((attachRangeHomeo (Γ := Γ) n ι fr).symm
        ⟨(Subtype.val (Subtype.val z)).1, z.2⟩, (Subtype.val (Subtype.val z)).2), by
      have h1 : Work.RatHurewicz.attachIncl n Γ ι fr
          ((attachRangeHomeo (Γ := Γ) n ι fr).symm
            ⟨(Subtype.val (Subtype.val z)).1, z.2⟩)
          = (Subtype.val (Subtype.val z)).1 :=
        congrArg Subtype.val (Homeomorph.apply_symm_apply (attachRangeHomeo (Γ := Γ) n ι fr)
          (⟨(Subtype.val (Subtype.val z)).1, z.2⟩ : ↥(Set.range fun y : Γ =>
            Work.RatHurewicz.attachIncl n Γ ι fr y)))
      show g _ = p (Subtype.val (Subtype.val z)).2
      rw [← hg' _, h1]
      exact (Subtype.val z).2⟩
  left_inv x := by
    apply Subtype.ext
    apply Prod.ext
    · show ((attachRangeHomeo (Γ := Γ) n ι fr).symm
        (⟨Work.RatHurewicz.attachIncl n Γ ι fr (Subtype.val x).1, ⟨(Subtype.val x).1, rfl⟩⟩ :
          ↥(Set.range fun y : Γ => Work.RatHurewicz.attachIncl n Γ ι fr y)))
        = (Subtype.val x).1
      exact Work.RatHurewicz.AttachRange.attachIncl_injective n Γ ι fr
        (congrArg Subtype.val (Homeomorph.apply_symm_apply (attachRangeHomeo (Γ := Γ) n ι fr) _))
    · rfl
  right_inv z := by
    apply Subtype.ext
    apply Subtype.ext
    apply Prod.ext
    · show ((attachRangeHomeo (Γ := Γ) n ι fr)
        ((attachRangeHomeo (Γ := Γ) n ι fr).symm
          ⟨(Subtype.val (Subtype.val z)).1, z.2⟩) :
          ↥(Set.range fun y : Γ => Work.RatHurewicz.attachIncl n Γ ι fr y)).1
        = (Subtype.val (Subtype.val z)).1
      rw [Homeomorph.apply_symm_apply]
    · rfl
  continuous_toFun := by fun_prop
  continuous_invFun := by fun_prop

end

end Work.Serre.SPC

namespace Work.Serre.SPC

noncomputable section

variable {E B Γ : Type} [TopologicalSpace E] [TopologicalSpace B] [TopologicalSpace Γ]

/-- The corestriction of `attachIncl` is `attachRangeHomeo` (as a function). -/
theorem attachRangeHomeo_apply_val (n : ℕ) (ι : Type)
    (fr : ι → C(Work.RatHurewicz.cellSphere n, Γ)) (y : Γ) :
    ((attachRangeHomeo (Γ := Γ) n ι fr y : ↥(Set.range fun y : Γ =>
      Work.RatHurewicz.attachIncl n Γ ι fr y)) : Work.RatHurewicz.attachCells n Γ ι fr)
      = Work.RatHurewicz.attachIncl n Γ ι fr y := rfl

/-- The inverse of `attachRangeHomeo`: the point of `Γ` mapping to a point of the range. -/
theorem attachRangeHomeo_symm_apply_val (n : ℕ) (ι : Type)
    (fr : ι → C(Work.RatHurewicz.cellSphere n, Γ))
    (w : ↥(Set.range fun y : Γ => Work.RatHurewicz.attachIncl n Γ ι fr y)) :
    Work.RatHurewicz.attachIncl n Γ ι fr ((attachRangeHomeo (Γ := Γ) n ι fr).symm w)
      = (w : Work.RatHurewicz.attachCells n Γ ι fr) := by
  rw [← attachRangeHomeo_apply_val n ι fr ((attachRangeHomeo (Γ := Γ) n ι fr).symm w)]
  exact congrArg Subtype.val (Homeomorph.apply_symm_apply (attachRangeHomeo (Γ := Γ) n ι fr) w)

/-- The projection formula for the homeomorphism `pullbackOldHomeo`. -/
@[simp]
theorem pullbackOldHomeo_val_fst (p : C(E, B)) (g : C(Γ, B)) (n : ℕ) (ι : Type)
    (fr : ι → C(Work.RatHurewicz.cellSphere n, Γ))
    (g' : C(Work.RatHurewicz.attachCells n Γ ι fr, B))
    (hg' : ∀ x : Γ, g' (Work.RatHurewicz.attachIncl n Γ ι fr x) = g x)
    (x : Work.StemsB.Pullback g p) :
    (Work.StemsB.pullbackFst g' p) ((pullbackOldHomeo p g n ι fr g' hg') x).val
      = Work.RatHurewicz.attachIncl n Γ ι fr (Subtype.val x).1 := rfl

/-- The projection formula for the inverse of the homeomorphism `pullbackOldHomeo`. -/
@[simp]
theorem pullbackOldHomeo_symm_fst (p : C(E, B)) (g : C(Γ, B)) (n : ℕ) (ι : Type)
    (fr : ι → C(Work.RatHurewicz.cellSphere n, Γ))
    (g' : C(Work.RatHurewicz.attachCells n Γ ι fr, B))
    (hg' : ∀ x : Γ, g' (Work.RatHurewicz.attachIncl n Γ ι fr x) = g x)
    (z : ↥((Work.StemsB.pullbackFst g' p) ⁻¹'
      (Set.range fun y : Γ => Work.RatHurewicz.attachIncl n Γ ι fr y))) :
    (Work.StemsB.pullbackFst g p) ((pullbackOldHomeo p g n ι fr g' hg').symm z)
      = (attachRangeHomeo (Γ := Γ) n ι fr).symm
          ⟨(Subtype.val (Subtype.val z)).1, z.2⟩ := rfl

/-- The inclusion of the fibre over the new base point into the old part. -/
def fibreInclOldPart (p : C(E, B)) (g : C(Γ, B)) (n : ℕ) (ι : Type)
    (fr : ι → C(Work.RatHurewicz.cellSphere n, Γ))
    (g' : C(Work.RatHurewicz.attachCells n Γ ι fr, B))
    (hg' : ∀ x : Γ, g' (Work.RatHurewicz.attachIncl n Γ ι fr x) = g x) (γ₀ : Γ)
    (z : ↥((Work.StemsB.pullbackFst g' p) ⁻¹'
      ({Work.RatHurewicz.attachIncl n Γ ι fr γ₀} : Set
        (Work.RatHurewicz.attachCells n Γ ι fr)))) :
    ↥((Work.StemsB.pullbackFst g' p) ⁻¹'
      (Set.range fun y : Γ => Work.RatHurewicz.attachIncl n Γ ι fr y)) :=
  ⟨z.val, Set.mem_range.mpr ⟨γ₀, (Set.mem_singleton_iff.mp (Set.mem_preimage.mp z.2)).symm⟩⟩

@[simp]
theorem fibreInclOldPart_val (p : C(E, B)) (g : C(Γ, B)) (n : ℕ) (ι : Type)
    (fr : ι → C(Work.RatHurewicz.cellSphere n, Γ))
    (g' : C(Work.RatHurewicz.attachCells n Γ ι fr, B))
    (hg' : ∀ x : Γ, g' (Work.RatHurewicz.attachIncl n Γ ι fr x) = g x) (γ₀ : Γ)
    (z : ↥((Work.StemsB.pullbackFst g' p) ⁻¹'
      ({Work.RatHurewicz.attachIncl n Γ ι fr γ₀} : Set
        (Work.RatHurewicz.attachCells n Γ ι fr)))) :
    (fibreInclOldPart p g n ι fr g' hg' γ₀ z).val = z.val := rfl

/-- Continuity of the inclusion of the fibre into the old part. -/
theorem continuous_fibreInclOldPart (p : C(E, B)) (g : C(Γ, B)) (n : ℕ) (ι : Type)
    (fr : ι → C(Work.RatHurewicz.cellSphere n, Γ))
    (g' : C(Work.RatHurewicz.attachCells n Γ ι fr, B))
    (hg' : ∀ x : Γ, g' (Work.RatHurewicz.attachIncl n Γ ι fr x) = g x) (γ₀ : Γ) :
    Continuous (fibreInclOldPart p g n ι fr g' hg' γ₀) := by
  rw [show fibreInclOldPart p g n ι fr g' hg' γ₀
      = fun z => (⟨z.val, Set.mem_range.mpr ⟨γ₀, (Set.mem_singleton_iff.mp
          (Set.mem_preimage.mp z.2)).symm⟩⟩ :
        ↥((Work.StemsB.pullbackFst g' p) ⁻¹'
          (Set.range fun y : Γ => Work.RatHurewicz.attachIncl n Γ ι fr y))) from rfl]
  exact Continuous.subtype_mk continuous_subtype_val _

/-- **The pullback over the base point is the old fibre**: the restriction of
`pullbackOldHomeo` to the fibres. -/
def pullbackOldHomeoA (p : C(E, B)) (g : C(Γ, B)) (n : ℕ) (ι : Type)
    (fr : ι → C(Work.RatHurewicz.cellSphere n, Γ))
    (g' : C(Work.RatHurewicz.attachCells n Γ ι fr, B))
    (hg' : ∀ x : Γ, g' (Work.RatHurewicz.attachIncl n Γ ι fr x) = g x) (γ₀ : Γ) :
    ↥((Work.StemsB.pullbackFst g p) ⁻¹' ({γ₀} : Set Γ)) ≃ₜ
      ↥((Work.StemsB.pullbackFst g' p) ⁻¹'
        ({Work.RatHurewicz.attachIncl n Γ ι fr γ₀} : Set
          (Work.RatHurewicz.attachCells n Γ ι fr))) where
  toFun := fun x =>
    ⟨((pullbackOldHomeo p g n ι fr g' hg') x.val).val, by
      rw [Set.mem_preimage, Set.mem_singleton_iff, pullbackOldHomeo_val_fst]
      exact congrArg (Work.RatHurewicz.attachIncl n Γ ι fr)
        (Set.mem_singleton_iff.mp (Set.mem_preimage.mp x.2))⟩
  invFun := fun z =>
    ⟨(pullbackOldHomeo p g n ι fr g' hg').symm (fibreInclOldPart p g n ι fr g' hg' γ₀ z), by
      rw [Set.mem_preimage, Set.mem_singleton_iff]
      apply Work.RatHurewicz.AttachRange.attachIncl_injective n Γ ι fr
      rw [pullbackOldHomeo_symm_fst, attachRangeHomeo_symm_apply_val]
      exact Set.mem_singleton_iff.mp (Set.mem_preimage.mp z.2)⟩
  left_inv := fun x => by
    apply Subtype.ext
    have h := Homeomorph.symm_apply_apply (pullbackOldHomeo p g n ι fr g' hg') x.val
    convert h using 2
    exact Subtype.ext rfl
  right_inv := fun z => by
    apply Subtype.ext
    dsimp only
    rw [show ((pullbackOldHomeo p g n ι fr g' hg')
        ((pullbackOldHomeo p g n ι fr g' hg').symm
          (fibreInclOldPart p g n ι fr g' hg' γ₀ z))).val
      = (fibreInclOldPart p g n ι fr g' hg' γ₀ z).val from
        congrArg Subtype.val (Homeomorph.apply_symm_apply _ _)]
    exact fibreInclOldPart_val p g n ι fr g' hg' γ₀ z
  continuous_toFun := by
    refine Continuous.subtype_mk ?_ _
    exact continuous_subtype_val.comp
      ((pullbackOldHomeo p g n ι fr g' hg').continuous.comp continuous_subtype_val)
  continuous_invFun := by
    refine Continuous.subtype_mk ?_ _
    exact (pullbackOldHomeo p g n ι fr g' hg').symm.continuous.comp
      (continuous_fibreInclOldPart p g n ι fr g' hg' γ₀)

/-- The homeomorphism between the base points of the old and the new stage. -/
def basePointHomeo (n : ℕ) (ι : Type)
    (fr : ι → C(Work.RatHurewicz.cellSphere n, Γ)) (γ₀ : Γ) :
    ↥({γ₀} : Set Γ) ≃ₜ
      ↥({Work.RatHurewicz.attachIncl n Γ ι fr γ₀} : Set
        (Work.RatHurewicz.attachCells n Γ ι fr)) where
  toFun _ := ⟨Work.RatHurewicz.attachIncl n Γ ι fr γ₀, rfl⟩
  invFun _ := ⟨γ₀, rfl⟩
  left_inv x := Subtype.ext (Set.mem_singleton_iff.mp x.2).symm
  right_inv x := Subtype.ext (Set.mem_singleton_iff.mp x.2).symm
  continuous_toFun := continuous_const
  continuous_invFun := continuous_const

end

end Work.Serre.SPC
