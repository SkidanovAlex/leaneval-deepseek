import Mathlib.Analysis.CStarAlgebra.Classes
import Mathlib.Analysis.Complex.Convex
import Mathlib.NumberTheory.NumberField.Completion.InfinitePlace
import Submission.NK.NUV2.RouteB.RayModulus.Defs
-- PORT435-BEGIN (v4.35 isDefEq respectTransparency compat)
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- PORT435-END

/-!
# Open neighbourhoods of `1` in the units at a complex place generate everything

Let `K` be a number field and `w` a complex infinite place of `K`.  Then the completion
`w.Completion` is (topologically and ring-theoretically) isomorphic to `ℂ`
(`NumberField.InfinitePlace.Completion.isometryEquivComplexOfIsComplex`), so its group of
units is (topologically) isomorphic to `ℂˣ`, which is path connected.

Consequently, if `O` is an *open* subset of `(w.Completion)ˣ` containing `1`, then the subgroup
it generates is open (it contains an open neighbourhood of `1`), hence also closed, and a
clopen non-empty subset of a preconnected space is everything.  This is the local input which
says that at a complex place the congruence (positivity) condition of a ray modulus imposes no
restriction at all.
-/

set_option autoImplicit false
set_option linter.style.haveILetI false

namespace NK.NUV2.RouteB.RayModulus

open NumberField

/-- The units of the completion of `K` at a *complex* infinite place form a preconnected
topological group: the completion is isometric (hence homeomorphic) to `ℂ`, so its units are
homeomorphic to `ℂˣ`, and `ℂˣ` is path connected. -/
theorem preconnectedSpace_units_completion_of_isComplex (K : Type) [Field K] [NumberField K]
    (w : NumberField.InfinitePlace K) (hw : w.IsComplex) :
    PreconnectedSpace (w.Completion)ˣ := by
  -- the ring equivalence `w.Completion ≃+* ℂ` as a multiplicative equivalence
  let e0 : w.Completion ≃* ℂ :=
    (NumberField.InfinitePlace.Completion.ringEquivComplexOfIsComplex hw).toMulEquiv
  -- it induces a homeomorphism between the corresponding groups of units
  let e : (w.Completion)ˣ ≃ₜ ℂˣ :=
    { toFun := Units.mapEquiv e0
      invFun := Units.mapEquiv e0.symm
      left_inv := fun u => (Units.mapEquiv e0).left_inv u
      right_inv := fun u => (Units.mapEquiv e0).right_inv u
      continuous_toFun := by
        apply Units.continuous_map
        have h := (NumberField.InfinitePlace.Completion.isometryEquivComplexOfIsComplex hw).continuous
        convert h using 1
        funext x
        rfl
      continuous_invFun := by
        apply Units.continuous_map
        have h := (NumberField.InfinitePlace.Completion.isometryEquivComplexOfIsComplex hw).symm.continuous
        convert h using 1
        funext x
        rfl }
  haveI : PreconnectedSpace ℂˣ := inferInstance
  refine ⟨?_⟩
  have h : IsPreconnected (Set.range ⇑(e.symm)) := isPreconnected_range e.symm.continuous
  rw [Set.range_eq_univ.mpr e.symm.surjective] at h
  exact h

/-- An open subgroup of a preconnected topological group is the whole group.  (An open subgroup
is closed, and a non-empty clopen subset of a preconnected space is everything.) -/
theorem subgroup_eq_top_of_isOpen_of_preconnected {G : Type*} [Group G] [TopologicalSpace G]
    [SeparatelyContinuousMul G] [PreconnectedSpace G]
    (H : Subgroup G) (hH : IsOpen (H : Set G)) : H = ⊤ := by
  have hclosed : IsClosed (H : Set G) := Subgroup.isClosed_of_isOpen H hH
  have huniv : (H : Set G) = Set.univ :=
    IsClopen.eq_univ ⟨hclosed, hH⟩ ⟨1, H.one_mem⟩
  rw [Subgroup.eq_top_iff']
  intro x
  exact (Set.ext_iff.mp huniv x).mpr trivial

/-- **Every open neighbourhood of `1` in the units at a complex place generates the full group
of units.**  Equivalently, at a complex infinite place the local congruence condition imposed by
a ray modulus is vacuous. -/
theorem complex_closure_of_isOpen_eq_top (K : Type) [Field K] [NumberField K]
    (w : NumberField.InfinitePlace K) (hw : w.IsComplex)
    (O : Set ((w.Completion)ˣ)) (hO : IsOpen O) (h1 : (1 : (w.Completion)ˣ) ∈ O) :
    Subgroup.closure O = ⊤ := by
  haveI : PreconnectedSpace (w.Completion)ˣ :=
    preconnectedSpace_units_completion_of_isComplex K w hw
  -- `1` lies in the interior of `Subgroup.closure O`, since `O` is an open set contained in it
  have hone : (1 : (w.Completion)ˣ) ∈ interior (Subgroup.closure O : Set (w.Completion)ˣ) := by
    have h := interior_mono
      (Subgroup.subset_closure : O ⊆ (Subgroup.closure O : Set (w.Completion)ˣ))
    rw [hO.interior_eq] at h
    exact h h1
  -- hence the subgroup it generates is open
  have hopen : IsOpen (Subgroup.closure O : Set (w.Completion)ˣ) :=
    Subgroup.isOpen_of_one_mem_interior _ hone
  exact subgroup_eq_top_of_isOpen_of_preconnected _ hopen

end NK.NUV2.RouteB.RayModulus
