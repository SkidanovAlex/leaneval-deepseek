/-
# Two models of the circle, and the Jordan curve predicate

`Work.Top.IsJordanCurve C` says that `C` is the image of an injective continuous map
`AddCircle (1:ℝ) → ℂ`, whereas the commons Jordan development (`Submission/Commons/Topology/
Jordan/…`) works with curves `Circle → ℂ`.  This file provides the two transports
(`toCircle`, `ofCircle`) between these models, the basic API of `Work.Top.IsJordanCurve`
(compactness, closedness, nonemptiness of the complement), and the equivalence of the two
definitions of "Jordan curve".
-/
import Mathlib
import Submission.Work.Top.Jordan

-- Lean v4.35.0-rc3 / Mathlib 5e0c4e5 made `isDefEq` respect transparency when unifying instances; with it,
-- `ZMod.instField` and `ZMod.commRing` (and `Neg (ZMod p)` via `SubtractionMonoid`) no longer unify, which
-- breaks `ring`/`rw`/module-instance search on `ZMod p`. Restore the v4.34 behaviour for this file.
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false


set_option autoImplicit false

open Set

namespace Work.TopJordan

noncomputable section

/-- The canonical homeomorphism between the additive circle `AddCircle (1:ℝ)` (the model of
`Work.Top.IsJordanCurve`) and `Circle` (the model of the commons Jordan development). -/
def circleHomeo : AddCircle (1 : ℝ) ≃ₜ Circle :=
  AddCircle.homeomorphCircle (T := (1 : ℝ)) one_ne_zero

@[simp] theorem circleHomeo_symm_apply_apply (t : AddCircle (1 : ℝ)) :
    circleHomeo.symm (circleHomeo t) = t :=
  Homeomorph.symm_apply_apply circleHomeo t

@[simp] theorem circleHomeo_apply_symm_apply (z : Circle) :
    circleHomeo (circleHomeo.symm z) = z :=
  Homeomorph.apply_symm_apply circleHomeo z

/-- Transport a curve parametrized by `AddCircle (1:ℝ)` to one parametrized by `Circle`. -/
def toCircle (γ : C(AddCircle (1 : ℝ), ℂ)) : C(Circle, ℂ) :=
  ⟨fun z => γ (circleHomeo.symm z), γ.continuous.comp circleHomeo.continuous_symm⟩

/-- Transport a curve parametrized by `Circle` to one parametrized by `AddCircle (1:ℝ)`. -/
def ofCircle (γ : C(Circle, ℂ)) : C(AddCircle (1 : ℝ), ℂ) :=
  ⟨fun t => γ (circleHomeo t), γ.continuous.comp circleHomeo.continuous⟩

@[simp] theorem toCircle_apply (γ : C(AddCircle (1 : ℝ), ℂ)) (z : Circle) :
    toCircle γ z = γ (circleHomeo.symm z) := rfl

@[simp] theorem ofCircle_apply (γ : C(Circle, ℂ)) (t : AddCircle (1 : ℝ)) :
    ofCircle γ t = γ (circleHomeo t) := rfl

theorem toCircle_injective {γ : C(AddCircle (1 : ℝ), ℂ)} (hγ : Function.Injective γ) :
    Function.Injective (toCircle γ) :=
  fun _ _ h => circleHomeo.symm.injective (hγ h)

theorem ofCircle_injective {γ : C(Circle, ℂ)} (hγ : Function.Injective γ) :
    Function.Injective (ofCircle γ) :=
  fun _ _ h => circleHomeo.injective (hγ h)

theorem range_toCircle (γ : C(AddCircle (1 : ℝ), ℂ)) :
    Set.range (toCircle γ) = Set.range γ := by
  have hcomp : (toCircle γ : Circle → ℂ) = γ ∘ circleHomeo.symm := rfl
  rw [hcomp, Set.range_comp, circleHomeo.symm.surjective.range_eq, Set.image_univ]

theorem range_ofCircle (γ : C(Circle, ℂ)) :
    Set.range (ofCircle γ) = Set.range γ := by
  have hcomp : (ofCircle γ : AddCircle (1 : ℝ) → ℂ) = γ ∘ circleHomeo := rfl
  rw [hcomp, Set.range_comp, circleHomeo.surjective.range_eq, Set.image_univ]

@[simp] theorem toCircle_ofCircle (γ : C(Circle, ℂ)) : toCircle (ofCircle γ) = γ := by
  ext z
  simp [toCircle, ofCircle, circleHomeo]

@[simp] theorem ofCircle_toCircle (γ : C(AddCircle (1 : ℝ), ℂ)) :
    ofCircle (toCircle γ) = γ := by
  ext t
  simp [toCircle, ofCircle, circleHomeo]

/-! ## The Jordan curve predicate -/

/-- A set is a Jordan curve in the sense of `Work.Top` iff it is the image of an injective
continuous map of `Circle`. -/
theorem isJordanCurve_iff_exists_circleMap {C : Set ℂ} :
    Work.Top.IsJordanCurve C ↔
      ∃ γ : C(Circle, ℂ), Function.Injective γ ∧ Set.range γ = C := by
  constructor
  · rintro ⟨γ, hγ, rfl⟩
    exact ⟨toCircle γ, toCircle_injective hγ, range_toCircle γ⟩
  · rintro ⟨γ, hγ, rfl⟩
    exact ⟨ofCircle γ, ofCircle_injective hγ, range_ofCircle γ⟩

/-- The image of an injective continuous map of `Circle` is a Jordan curve. -/
theorem isJordanCurve_range (γ : C(Circle, ℂ)) (hγ : Function.Injective γ) :
    Work.Top.IsJordanCurve (Set.range γ) :=
  isJordanCurve_iff_exists_circleMap.mpr ⟨γ, hγ, rfl⟩

/-- The image of an injective continuous map of `AddCircle (1:ℝ)` is a Jordan curve. -/
theorem isJordanCurve_range_addCircle (γ : C(AddCircle (1 : ℝ), ℂ))
    (hγ : Function.Injective γ) : Work.Top.IsJordanCurve (Set.range γ) :=
  ⟨γ, hγ, rfl⟩

/-- A Jordan curve is compact. -/
theorem isCompact_of_isJordanCurve {C : Set ℂ} (hC : Work.Top.IsJordanCurve C) :
    IsCompact C := by
  obtain ⟨γ, -, rfl⟩ := hC
  exact isCompact_range γ.continuous

/-- A Jordan curve is closed. -/
theorem isClosed_of_isJordanCurve {C : Set ℂ} (hC : Work.Top.IsJordanCurve C) :
    IsClosed C :=
  (isCompact_of_isJordanCurve hC).isClosed

/-- A Jordan curve is nonempty. -/
theorem nonempty_of_isJordanCurve {C : Set ℂ} (hC : Work.Top.IsJordanCurve C) :
    C.Nonempty := by
  obtain ⟨γ, -, rfl⟩ := hC
  exact ⟨γ 0, ⟨0, rfl⟩⟩

/-- The complement of a Jordan curve is open. -/
theorem isOpen_compl_of_isJordanCurve {C : Set ℂ} (hC : Work.Top.IsJordanCurve C) :
    IsOpen Cᶜ :=
  (isClosed_of_isJordanCurve hC).isOpen_compl

/-- A Jordan curve is path connected (it is a continuous image of the circle). -/
theorem isPathConnected_of_isJordanCurve {C : Set ℂ} (hC : Work.Top.IsJordanCurve C) :
    IsPathConnected C := by
  obtain ⟨γ, -, hrange⟩ := isJordanCurve_iff_exists_circleMap.mp hC
  rw [← hrange]
  exact isPathConnected_range γ.continuous

/-- A Jordan curve is invariant under homeomorphisms of the plane. -/
theorem isJordanCurve_image_homeomorph {C : Set ℂ} (f : ℂ ≃ₜ ℂ)
    (hC : Work.Top.IsJordanCurve C) : Work.Top.IsJordanCurve (f '' C) := by
  obtain ⟨γ, hγ, hrange⟩ := hC
  refine ⟨⟨fun z => f (γ z), f.continuous.comp γ.continuous⟩, ?_, ?_⟩
  · intro z w h
    exact hγ (f.injective h)
  · show Set.range (fun z : AddCircle (1 : ℝ) => f (γ z)) = f '' C
    rw [show (fun z : AddCircle (1 : ℝ) => f (γ z)) =
        (f : ℂ → ℂ) ∘ (γ : AddCircle (1 : ℝ) → ℂ) from rfl, Set.range_comp, hrange]

/-- The complement of a Jordan curve is nonempty (a Jordan curve is bounded). -/
theorem compl_nonempty_of_isJordanCurve {C : Set ℂ} (hC : Work.Top.IsJordanCurve C) :
    Cᶜ.Nonempty := by
  obtain ⟨R, hR⟩ := isBounded_iff_forall_norm_le.mp (isCompact_of_isJordanCurve hC).isBounded
  refine ⟨(((max R 0 + 1 : ℝ)) : ℂ), ?_⟩
  simp only [Set.mem_compl_iff]
  intro hmem
  have h1 : ‖(((max R 0 + 1 : ℝ)) : ℂ)‖ ≤ R := hR _ hmem
  rw [Complex.norm_real, Real.norm_eq_abs,
    abs_of_nonneg (by linarith [le_max_right R 0] : (0:ℝ) ≤ max R 0 + 1)] at h1
  linarith [le_max_left R 0]

end

end Work.TopJordan
