import Mathlib
import ChallengeDeps
import Submission.OLocalStructure
import Submission.SecantSpace
import Submission.Commons.Topology.PathConnected.isPathConnected_of_isConnected_of_open_pathConnected_nhds

open LeanEval.KnotTheory.Quadrisecant
open Filter
open scoped Real Topology unitInterval

noncomputable section

namespace LeanEval.KnotTheory.Quadrisecant

/-!
# Milestone-2 (iv) / Layer C opener (step 6) — components of `O` are
path-connected, and paths in `O` lift over the ordered double cover

`OLocalStructure.lean` (S93–S95) proved that every trisecant class lies in
an open path-connected neighbourhood of the trisecant set `O` (the class
image of a small strict convex chart cell), and that the connected
components of the subspace `O` are *open*.  This module completes the
topological picture of the components:

1. **generic engine** — imported from the shared commons
   (`Commons.Topology.PathConnected.isPathConnected_of_isConnected_of_open_pathConnected_nhds`,
   fleet-proven L27): in any topological space, a connected set in which
   every point has an open path-connected neighbourhood *inside* the set is
   path-connected;
2. **open path-connected neighbourhoods in the subtype**
   (`exists_open_pathConnected_nhds_in_OSub`): re-exports step (4) into the
   subtype `OSub r = {c // c ∈ trisecantSet r}`;
3. **components are path-connected** (`component_isPathConnected_in_O`):
   an immediate instance of the generic engine — every point of a component
   has such a neighbourhood inside the component by path-connectedness of
   the neighbourhood (`U ⊆ connectedComponent y = connectedComponent c₀`);
4. **paths inside components** (`exists_path_in_component_in_O`): two
   classes in the same component are joined by a path that stays entirely
   inside the component;
5. **path-lifting over the double cover**
   (`exists_lift_orderedData_of_bandPath`, `lift_loop_end_in_fiber`): the
   covering map `mobiusCover : OrderedPairs → OpenMobius`
   (`isCoveringMap_mobiusCover`, SecantSpace) lifts every band path through
   classes of `O` to a path of ordered pairs, given a lift of its source
   class; a *loop* based at `c₀` lifts to an ordered-pair path ending in the
   two-element fibre `{p₀, swapOrdered p₀}` of its base class — the
   monodromy interface that the once/twice-winding analysis of the
   components (Milestone-2 (iv) step 6 remainder, Layer C) consumes.

Everything here is elementary and verified (no axioms, no `sorry`).
-/

/-- The subtype of trisecant classes of a knot (Kuperberg's `O`, as a
topological space with the subspace topology of the open Möbius band). -/
abbrev OSub (r : ℝ → Space) := {c : OpenMobius // c ∈ trisecantSet r}

/-! ## 2. Open path-connected neighbourhoods in the subtype `O` -/

/-- **Open path-connected neighbourhoods in `O` (subtype form).**  Every
trisecant class `c₀ ∈ O` has an open, path-connected neighbourhood in the
subspace `OSub r` (the step-(4) trace neighbourhoods of
`OLocalStructure.exists_open_pathConnected_nhds_in_O`, lifted into the
subtype). -/
lemma exists_open_pathConnected_nhds_in_OSub {r : ℝ → Space} (h : IsSmoothKnot r)
    (hqf : QuadrisecantFree r) (hgp : TorusGeneralPositionTransverse r)
    (c₀ : OSub r) :
    ∃ U : Set (OSub r), IsOpen U ∧ c₀ ∈ U ∧ IsPathConnected U := by
  rcases exists_open_pathConnected_nhds_in_O h hqf hgp (c₀ : OpenMobius) c₀.2 with
    ⟨UO, hUpathO, hc₀UO, hUOsub, W, hWopen, hWeq⟩
  let U : Set (OSub r) := {c : OSub r | (c : OpenMobius) ∈ UO}
  refine ⟨U, ?_, ?_, ?_⟩
  · have heq : U = (fun c : OSub r => (c : OpenMobius)) ⁻¹' W := by
      ext c
      constructor
      · intro hc
        have hw : (c : OpenMobius) ∈ trisecantSet r ∩ W := by
          rw [hWeq]
          exact hc
        exact hw.2
      · intro hc
        dsimp [U]
        rw [← hWeq]
        exact ⟨c.2, hc⟩
    rw [heq]
    exact hWopen.preimage continuous_subtype_val
  · dsimp [U]
    exact hc₀UO
  · simpa [U] using (isPathConnected_lift_trisecant hUOsub hUpathO)

/-! ## 3. Connected components of `O` are path-connected -/

/-- **The connected components of `O` are path-connected.**  Every point of
a component has an open path-connected neighbourhood inside the component
(`exists_open_pathConnected_nhds_in_OSub` + path-connected sets are
connected, so the neighbourhood lies in the component of its point), so the
generic engine applies to the connected component. -/
theorem component_isPathConnected_in_O {r : ℝ → Space} (h : IsSmoothKnot r)
    (hqf : QuadrisecantFree r) (hgp : TorusGeneralPositionTransverse r)
    (c₀ : OSub r) :
    IsPathConnected (connectedComponent c₀) := by
  refine Commons.Topology.PathConnected.isPathConnected_of_isConnected_of_open_pathConnected_nhds
    (s := connectedComponent c₀) isConnected_connectedComponent ?_
  intro y hyC
  rcases exists_open_pathConnected_nhds_in_OSub h hqf hgp y with ⟨U, hUopen, hyU, hUpath⟩
  refine ⟨U, hUopen, hyU, hUpath, ?_⟩
  have hUconn : IsConnected U := hUpath.isConnected
  have hUsub : U ⊆ connectedComponent y := hUconn.subset_connectedComponent hyU
  have heq : connectedComponent c₀ = connectedComponent y := connectedComponent_eq hyC
  simpa [heq] using hUsub

/-- **Paths inside components.**  Two trisecant classes in the same
connected component of `O` are joined by a path that stays entirely inside
the component. -/
theorem exists_path_in_component_in_O {r : ℝ → Space} (h : IsSmoothKnot r)
    (hqf : QuadrisecantFree r) (hgp : TorusGeneralPositionTransverse r)
    {c₀ x y : OSub r} (hx : x ∈ connectedComponent c₀)
    (hy : y ∈ connectedComponent c₀) :
    ∃ γ : Path x y, ∀ t : I, γ t ∈ connectedComponent c₀ := by
  have hpath : IsPathConnected (connectedComponent c₀) :=
    component_isPathConnected_in_O h hqf hgp c₀
  have hjoin : JoinedIn (connectedComponent c₀) x y :=
    (isPathConnected_iff.mp hpath).2 x hx y hy
  exact ⟨hjoin.somePath, hjoin.somePath_mem⟩

/-! ## 4. Path-lifting over the ordered double cover -/

/-- A path between two classes of `O` is a path in the band whose image lies
in the trisecant set; this is its underlying band path. -/
lemma bandPath_continuous {r : ℝ → Space} {c₀ c₁ : OSub r} (γ : Path c₀ c₁) :
    Continuous (fun t : I => (γ t : OpenMobius)) := by
  exact continuous_subtype_val.comp γ.continuous

/-- **Path-lifting over the double cover.**  Given a path `γ` in the
subspace `O` (equivalently a band path through trisecant classes) and a
lift `p₀` of its source class to the ordered double cover, there is a
continuous lift `Γ` of the band path with `Γ 0 = p₀` — the path-lifting
property of the covering map `mobiusCover` (SecantSpace,
`isCoveringMap_mobiusCover`). -/
theorem exists_lift_orderedData_of_bandPath {r : ℝ → Space} {c₀ c₁ : OSub r}
    (γ : Path c₀ c₁) (p₀ : OrderedPairs)
    (hp₀ : mobiusCover p₀ = (c₀ : OpenMobius)) :
    ∃ Γ : C(I, OrderedPairs),
      mobiusCover ∘ Γ = (fun t : I => (γ t : OpenMobius)) ∧ Γ 0 = p₀ := by
  have hγb : Continuous (fun t : I => (γ t : OpenMobius)) := bandPath_continuous γ
  let γB : C(I, OpenMobius) := ⟨fun t : I => (γ t : OpenMobius), hγb⟩
  have hγ₀ : γB 0 = mobiusCover p₀ := by
    dsimp [γB]
    rw [hp₀]
    exact congrArg (fun z : OSub r => (z : OpenMobius)) γ.source
  rcases (isCoveringMap_mobiusCover.exists_path_lifts γB p₀ hγ₀) with ⟨Γ, hΓlifts, hΓ₀⟩
  refine ⟨Γ, ?_, hΓ₀⟩
  simpa [γB, Function.comp_def] using hΓlifts

/-- **Monodromy of a loop at a class.**  A *loop* in `O` based at `c₀`
lifts through the double cover to an ordered-pair path starting at the
chosen representative `p₀` of `c₀` and ending at one of the two
representatives of `c₀` — i.e. at `p₀` (null/even monodromy) or at
`swapOrdered p₀` (the non-trivial/odd monodromy of a once-winding loop).
This is the interface that the once/twice-winding analysis of circular
components of `O` (Milestone-2 (iv) step 6, Layer C) consumes. -/
theorem lift_loop_end_in_fiber {r : ℝ → Space} {c₀ : OSub r} (γ : Path c₀ c₀)
    (p₀ : OrderedPairs) (hp₀ : mobiusCover p₀ = (c₀ : OpenMobius)) :
    ∃ Γ : C(I, OrderedPairs),
      mobiusCover ∘ Γ = (fun t : I => (γ t : OpenMobius)) ∧
        Γ 0 = p₀ ∧ Γ 1 ∈ ({p₀, swapOrdered p₀} : Set OrderedPairs) := by
  rcases exists_lift_orderedData_of_bandPath γ p₀ hp₀ with ⟨Γ, hΓlifts, hΓ₀⟩
  refine ⟨Γ, hΓlifts, hΓ₀, ?_⟩
  have hm : mobiusCover (Γ 1) = mobiusCover p₀ := by
    have h1 : mobiusCover (Γ 1) = (γ 1 : OpenMobius) := by
      have := congrFun hΓlifts (1 : I)
      simpa [Function.comp_def] using this
    rw [h1]
    -- γ 1 = c₀ because γ is a loop
    rw [γ.target]
    exact hp₀.symm
  have hpre : Γ 1 ∈ {q : OrderedPairs | mobiusCover q = mobiusCover p₀} := by
    dsimp
    exact hm
  simpa [mobiusCover_fiber] using hpre
/-! ## 5. Monodromy parity: lifts from the two representatives are swapped -/

/-- The band path underlying a path through classes of `O` (a continuous
map from the unit interval into the open Möbius band whose image consists
of trisecant classes). -/
def bandCMap {r : ℝ → Space} {c₀ c₁ : OSub r} (γ : Path c₀ c₁) : C(I, OpenMobius) :=
  ⟨fun t : I => (γ t : OpenMobius), bandPath_continuous γ⟩

/-- The band path of a loop starts at the chosen representative of the
base class. -/
lemma bandCMap_zero_of_rep {r : ℝ → Space} {c₀ : OSub r} (γ : Path c₀ c₀)
    (p₀ : OrderedPairs) (hp₀ : mobiusCover p₀ = (c₀ : OpenMobius)) :
    bandCMap γ 0 = mobiusCover p₀ := by
  dsimp [bandCMap]
  calc
    ((γ 0 : OSub r) : OpenMobius) = (c₀ : OpenMobius) :=
      congrArg (fun z : OSub r => (z : OpenMobius)) γ.source
    _ = mobiusCover p₀ := hp₀.symm

/-- **Parity of a loop (even/odd).**  A loop in `O` based at the class of
`p₀` lifts to an ordered-pair path starting at `p₀`; its endpoint is
either `p₀` (even/null monodromy) or `swapOrdered p₀` (odd/essential
monodromy).  This is the two-case dichotomy that the once/twice-winding
classification consumes. -/
theorem lift_loop_end_even_or_odd {r : ℝ → Space} {c₀ : OSub r} (γ : Path c₀ c₀)
    (p₀ : OrderedPairs) (hp₀ : mobiusCover p₀ = (c₀ : OpenMobius)) :
    ∃ Γ : C(I, OrderedPairs), mobiusCover ∘ Γ = bandCMap γ ∧ Γ 0 = p₀ ∧
      (Γ 1 = p₀ ∨ Γ 1 = swapOrdered p₀) := by
  rcases lift_loop_end_in_fiber γ p₀ hp₀ with ⟨Γ, hΓl, hΓ₀, hΓ1⟩
  refine ⟨Γ, hΓl, hΓ₀, ?_⟩
  simpa using hΓ1

/-- **The parity is independent of the starting representative.**  Lifting
a loop from the other representative `swapOrdered p₀` of the base class
gives the swap of the lift from `p₀`, so its endpoint is the swap of the
first endpoint — the two fibres of the double cover `{p₀, swapOrdered p₀}`
are exchanged consistently and the even/odd dichotomy above does not depend
on which ordered representative of the base class one starts from. -/
theorem lift_from_swap_ends_swapped {r : ℝ → Space} {c₀ : OSub r} (γ : Path c₀ c₀)
    (p₀ : OrderedPairs) (hp₀ : mobiusCover p₀ = (c₀ : OpenMobius)) :
    ∃ Γ Γs : C(I, OrderedPairs),
      mobiusCover ∘ Γ = bandCMap γ ∧ Γ 0 = p₀ ∧
      mobiusCover ∘ Γs = bandCMap γ ∧ Γs 0 = swapOrdered p₀ ∧
      Γs 1 = swapOrdered (Γ 1) := by
  classical
  rcases exists_lift_orderedData_of_bandPath γ p₀ hp₀ with ⟨Γ, hΓl, hΓ₀⟩
  have hqs : mobiusCover (swapOrdered p₀) = (c₀ : OpenMobius) := by
    rw [mobiusCover_swap, hp₀]
  rcases exists_lift_orderedData_of_bandPath γ (swapOrdered p₀) hqs with ⟨Γs, hΓsl, hΓs₀⟩
  -- the swap of Γ is a lift starting at swapOrdered p₀
  have hΓscont : Continuous (fun t : I => swapOrdered (Γ t)) :=
    continuous_swapOrdered.comp Γ.continuous
  let Γsw : C(I, OrderedPairs) := ⟨fun t : I => swapOrdered (Γ t), hΓscont⟩
  have hΓswl : mobiusCover ∘ Γsw = bandCMap γ := by
    funext t
    change mobiusCover (swapOrdered (Γ t)) = bandCMap γ t
    rw [mobiusCover_swap]
    have hlt := congrFun hΓl t
    change mobiusCover (Γ t) = bandCMap γ t at hlt
    exact hlt
  have hΓsw0 : Γsw 0 = swapOrdered p₀ := by
    dsimp [Γsw]
    rw [hΓ₀]
  -- canonical lifts are unique (eq_liftPath_iff'): Γs and Γsw are both the
  -- lift from swapOrdered p₀
  have hEqs : Γs = isCoveringMap_mobiusCover.liftPath (bandCMap γ) (swapOrdered p₀)
        (bandCMap_zero_of_rep γ (swapOrdered p₀) hqs) := by
    exact (isCoveringMap_mobiusCover.eq_liftPath_iff'
      (γ := bandCMap γ) (e := swapOrdered p₀)
      (γ_0 := bandCMap_zero_of_rep γ (swapOrdered p₀) hqs)).mpr ⟨hΓsl, hΓs₀⟩
  have hEqsw : Γsw = isCoveringMap_mobiusCover.liftPath (bandCMap γ) (swapOrdered p₀)
        (bandCMap_zero_of_rep γ (swapOrdered p₀) hqs) := by
    exact (isCoveringMap_mobiusCover.eq_liftPath_iff'
      (γ := bandCMap γ) (e := swapOrdered p₀)
      (γ_0 := bandCMap_zero_of_rep γ (swapOrdered p₀) hqs)).mpr ⟨hΓswl, hΓsw0⟩
  refine ⟨Γ, ⟨Γs, ⟨hΓl, ⟨hΓ₀, ⟨hΓsl, ⟨hΓs₀, ?_⟩⟩⟩⟩⟩⟩
  calc
    Γs 1 = Γsw 1 := by rw [hEqs, hEqsw]
    _ = swapOrdered (Γ 1) := by
      dsimp [Γsw]

end LeanEval.KnotTheory.Quadrisecant
