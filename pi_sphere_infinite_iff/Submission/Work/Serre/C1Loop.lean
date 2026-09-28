import Submission.Work.Serre.C1SphOne
import Submission.Work.EmbeddedSpheres.exists_parametrization_sph_one

/-!
# C1: loops, the standard parametrization of `S¹`, and generators of `π₁`

This file provides the elementary topological input of the C1 construction:

* `exists_generator_of_mulEquiv_int` — a group isomorphic to `Multiplicative ℤ` has a generator;
* `isQuotientMap_s1ParamCm` — the standard parametrization `[0,1] → S¹` is a quotient map;
* `loopToSphOne` — a loop `γ : [0,1] → X` with `γ 0 = γ 1` descends to a map `S¹ → X`;
* `loopToSphOne_s1ParamCm` — the descent property;
* the induced map on `π₁` sends the class of the parametrization to the class of the loop.
-/

open scoped Topology unitInterval

namespace Work.Serre

noncomputable section

/-- **A generator of a group isomorphic to `Multiplicative ℤ`**: there is `c` such that every
element is a unique integral power of `c`. -/
theorem exists_generator_of_mulEquiv_int {G : Type*} [Group G] (e : G ≃* Multiplicative ℤ) :
    ∃ c : G, ∀ a : G, ∃! m : ℤ, a = c ^ m := by
  refine ⟨e.symm (Multiplicative.ofAdd 1), fun a => ?_⟩
  refine ⟨(e a).toAdd, ?_, ?_⟩
  · have h : e (e.symm (Multiplicative.ofAdd 1) ^ (e a).toAdd) = e a := by
      rw [map_zpow, MulEquiv.apply_symm_apply, ofAdd_one_zpow]
      exact ofAdd_toAdd (e a)
    exact (e.injective h).symm
  · intro m hm
    have h1 : e a = (Multiplicative.ofAdd (1 : ℤ) : Multiplicative ℤ) ^ m := by
      rw [hm, map_zpow, MulEquiv.apply_symm_apply]
    rw [ofAdd_one_zpow] at h1
    exact (congrArg Multiplicative.toAdd h1).symm

/-- The standard parametrization `[0,1] → S¹` is a quotient map (it is a closed surjection from a
compact space onto a Hausdorff space). -/
theorem isClosedMap_s1ParamCm : IsClosedMap ⇑Work.EmbeddedSpheres.s1ParamCm := fun s hs =>
  (hs.isCompact.image Work.EmbeddedSpheres.s1ParamCm.continuous).isClosed

theorem isQuotientMap_s1ParamCm : Topology.IsQuotientMap ⇑Work.EmbeddedSpheres.s1ParamCm :=
  isClosedMap_s1ParamCm.isQuotientMap Work.EmbeddedSpheres.s1ParamCm.continuous
    Work.EmbeddedSpheres.s1ParamCm_surjective

/-- The fibres of the parametrization: two points with the same image are equal or are the two
endpoints. -/
theorem s1ParamCm_fibre {s t : unitInterval} (h : Work.EmbeddedSpheres.s1ParamCm s =
    Work.EmbeddedSpheres.s1ParamCm t) :
    s = t ∨ (s = 0 ∧ t = 1) ∨ (s = 1 ∧ t = 0) :=
  Work.EmbeddedSpheres.s1ParamCm_inj s t h

/-- The key computation of the descent: the chosen lift of `s1ParamCm u` gives back `γ u`. -/
theorem loopToSphOne_fibre {X : Type} [TopologicalSpace X] (γ : C(unitInterval, X))
    (h : γ 0 = γ 1) (u : unitInterval) :
    γ (Classical.choose (Work.EmbeddedSpheres.s1ParamCm_surjective
      (Work.EmbeddedSpheres.s1ParamCm u))) = γ u := by
  have hspec := Classical.choose_spec
    (Work.EmbeddedSpheres.s1ParamCm_surjective (Work.EmbeddedSpheres.s1ParamCm u))
  rcases s1ParamCm_fibre hspec with h1 | ⟨h1, h2⟩ | ⟨h1, h2⟩
  · exact congrArg γ h1
  · rw [h1, h2, h]
  · rw [h1, h2, h]

/-- **The descent of a loop to the circle**: a continuous map `γ : [0,1] → X` with `γ 0 = γ 1`
factors through the standard parametrization of `S¹`. -/
noncomputable def loopToSphOne {X : Type} [TopologicalSpace X] (γ : C(unitInterval, X))
    (h : γ 0 = γ 1) : C(Work.Serre.Sph 1, X) :=
  ⟨fun y => γ (Classical.choose (Work.EmbeddedSpheres.s1ParamCm_surjective y)),
    (isQuotientMap_s1ParamCm.continuous_iff).mpr (by
      have hEq : (fun y => γ (Classical.choose
          (Work.EmbeddedSpheres.s1ParamCm_surjective y))) ∘
            ⇑Work.EmbeddedSpheres.s1ParamCm = ⇑γ := by
        funext u
        exact loopToSphOne_fibre γ h u
      rw [hEq]
      exact γ.continuous)⟩

theorem loopToSphOne_apply {X : Type} [TopologicalSpace X] (γ : C(unitInterval, X))
    (h : γ 0 = γ 1) (u : unitInterval) :
    loopToSphOne γ h (Work.EmbeddedSpheres.s1ParamCm u) = γ u :=
  loopToSphOne_fibre γ h u

/-- The base point of the circle given by the parametrization. -/
def sphOneBase : Work.Serre.Sph 1 := Work.EmbeddedSpheres.s1ParamCm 0

/-- The standard parametrization, as a map on the cube `I¹`. -/
noncomputable def s1ParamCubeCM : C(Fin 1 → unitInterval, Work.Serre.Sph 1) :=
  ⟨fun y => Work.EmbeddedSpheres.s1ParamCm (y 0),
    Work.EmbeddedSpheres.s1ParamCm.continuous.comp (continuous_apply 0)⟩

theorem s1ParamCubeCM_apply (y : Fin 1 → unitInterval) :
    s1ParamCubeCM y = Work.EmbeddedSpheres.s1ParamCm (y 0) := rfl

/-- The parametrization, as a based loop of `S¹` at `sphOneBase` (in the cube model of `π₁`). -/
noncomputable def s1ParamLoop :
    ↥(GenLoop (Fin 1) (Work.Serre.Sph 1) sphOneBase) :=
  ⟨s1ParamCubeCM, fun y hy => by
    obtain ⟨i, hi⟩ := hy
    rw [s1ParamCubeCM_apply]
    have hi' : y 0 = 0 ∨ y 0 = 1 := by
      fin_cases i
      · exact hi
    rcases hi' with h0 | h1
    · rw [h0]; rfl
    · rw [h1]
      exact Work.EmbeddedSpheres.s1ParamCm_zero_eq_one.symm⟩

end

end Work.Serre
