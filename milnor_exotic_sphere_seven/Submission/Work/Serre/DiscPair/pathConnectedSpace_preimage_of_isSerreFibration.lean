import Mathlib
import Submission.Work.StemsB.Fibrations
import Submission.Work.Serre.exists_path_pullbackFst

-- Lean v4.35.0-rc3: restore v4.34 instance-unification transparency (port).
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
set_option synthInstance.maxHeartbeats 400000

/-!
# The preimage under a Serre fibration of a path-connected set is path connected

This file proves the `π₀` statement of a Serre fibration in the form in which the DiscPair layer
needs it:

> if `q : E → B` is a Serre fibration, `V ⊆ B` is path connected, `b ∈ V` and the fibre
> `F = q ⁻¹' {b}` is path connected, then `q ⁻¹' V ⊆ E` is path connected.

The mathematics is elementary path lifting, and no relative homotopy theory beyond the lifting
property is required:

* every `a ∈ q ⁻¹' V` is joined *inside* `q ⁻¹' V` to a point of `F`: choose a path in `V` from
  `q a` to `b` (`V` is path connected), lift it with prescribed starting point `a`
  (`exists_liftPath_proj`).  The lift projects onto a path of `V`, hence lies in `q ⁻¹' V`, and its
  endpoint lies over `b`;
* two points of `F` are joined inside `F` (hypothesis), hence inside `q ⁻¹' V`.

Concatenating these three paths gives a path in `q ⁻¹' V` between any two points, so `q ⁻¹' V` is
path connected.  Note that no path connectivity of the whole fibre `q⁻¹{q x}` is assumed: only the
single fibre over `b` is used, together with the fact that every point of the preimage can be
walked to that fibre.

The auxiliary `exists_liftPath_proj` is the path lifting property of a Serre fibration with the
*projection* of the lift exposed (it is the degree-`0` case of the relative homotopy lifting
property `Work.StemsB.exists_lift_rel`); the same statement is proved as
`Work.Serre.exists_liftPath_proj` in `Submission/Work/Serre/zerothHomotopy_fibre_equiv_of_path.lean`,
and is reproduced here so that this file only depends on the lifting property itself.
-/

open scoped Topology unitInterval

namespace Work.Serre.DiscPair

noncomputable section

/-- **Path lifting with prescribed starting point, keeping the projection.**  A path `γ` of the base
with `q e = γ 0` lifts to a path of `E` starting at `e` and projecting onto `γ`.  This is the
degree-`0` case of the relative homotopy lifting property (`Work.StemsB.exists_lift_rel`), with the
projection identity exposed. -/
theorem exists_liftPath_proj {E B : Type} [TopologicalSpace E] [TopologicalSpace B]
    (q : C(E, B)) (hq : Work.StemsB.IsSerreFibration q) (γ : C(unitInterval, B))
    {e : E} (he : q e = γ 0) :
    ∃ w : C(unitInterval, E), w 0 = e ∧ q.comp w = γ := by
  let H : C((Fin 0 → I) × I, B) := ⟨fun z => γ z.2, γ.continuous.comp continuous_snd⟩
  let f : C(Fin 0 → I, E) := ContinuousMap.const (Fin 0 → I) e
  have hf : q.comp f = H.comp (Work.StemsB.zeroIncl 0) := by
    ext z
    show q e = γ 0
    exact he
  let g₀ : C(Work.StemsB.CubeBdry 0 × I, E) := ContinuousMap.const _ e
  have hg : q.comp g₀ = H.comp (Work.StemsB.bdryIncl 0) := by
    ext z
    obtain ⟨i, _⟩ := z.1.2
    exact i.elim0
  have hg0 : ∀ x : Work.StemsB.CubeBdry 0, g₀ (x, 0) = f x.1 := by
    intro x
    obtain ⟨i, _⟩ := x.2
    exact i.elim0
  obtain ⟨G, hGq, hG0, -⟩ := Work.StemsB.exists_lift_rel q hq 0 H f hf g₀ hg hg0
  let z₀ : Fin 0 → I := fun i => i.elim0
  refine ⟨⟨fun t : I => G (z₀, t),
    G.continuous.comp (continuous_const.prodMk continuous_id)⟩, ?_, ?_⟩
  · show G (z₀, 0) = e
    rw [hG0 z₀]
    rfl
  · ext t
    exact congrFun (congrArg DFunLike.coe hGq) (z₀, t)

/-- **The preimage of a path-connected set under a Serre fibration is path connected**, provided
the fibre over one of its points is path connected.

Let `q : E → B` be a Serre fibration, `V ⊆ B` path connected, `b ∈ V` and the fibre
`F = {x : E // q x = b}` path connected.  Then `q ⁻¹' V` is path connected.

Given `x y ∈ q ⁻¹' V`, lift a path of `V` from `q x` to `b` starting at `x`, and a path of `V`
from `q y` to `b` starting at `y`.  This joins `x` inside `q ⁻¹' V` to a point of `F` and `y`
inside `q ⁻¹' V` to a point of `F`, and those two points of `F` are joined inside `F`, hence inside
`q ⁻¹' V`. -/
theorem pathConnectedSpace_preimage_of_isSerreFibration {E B : Type} [TopologicalSpace E]
    [TopologicalSpace B] (q : C(E, B)) (hq : Work.StemsB.IsSerreFibration q)
    {V : Set B} (hV : PathConnectedSpace ↥V) (b : B) (hb : b ∈ V)
    (hF : PathConnectedSpace (Work.StemsB.fibre q b)) :
    PathConnectedSpace ↥(q ⁻¹' V) := by
  classical
  -- the preimage is nonempty: the fibre over `b` is
  have hne : Nonempty ↥(q ⁻¹' V) := by
    obtain ⟨e, he⟩ := hF.nonempty
    exact ⟨⟨e, by show q e ∈ V; rw [he]; exact hb⟩⟩
  refine ⟨hne, fun x y => ?_⟩
  -- every point of `q ⁻¹' V` is joined inside `q ⁻¹' V` to a point of the fibre over `b`
  have key : ∀ a : E, q a ∈ V → ∃ e' : E, q e' = b ∧ JoinedIn (q ⁻¹' V) a e' := by
    intro a ha
    -- a path of `V` from `q a` to `b`, viewed in `B`
    obtain ⟨η⟩ := hV.joined ⟨q a, ha⟩ ⟨b, hb⟩
    let γ : C(unitInterval, B) :=
      (⟨Subtype.val, continuous_subtype_val⟩ : C(↥V, B)).comp η.toContinuousMap
    have hγ0 : q a = γ 0 := by
      show q a = ((η 0 : ↥V) : B)
      exact (congrArg Subtype.val (Path.source η)).symm
    -- lift it, with prescribed starting point `a`
    obtain ⟨w, hw0, hqw⟩ := exists_liftPath_proj q hq γ hγ0
    refine ⟨w 1, ?_, ?_⟩
    · -- the endpoint of the lift lies over `b`
      have h1 : q (w 1) = γ 1 := congrFun (congrArg DFunLike.coe hqw) 1
      rw [h1]
      show ((η 1 : ↥V) : B) = b
      exact congrArg Subtype.val (Path.target η)
    · -- the lift itself is a path of `q ⁻¹' V`
      refine ⟨⟨w, hw0, rfl⟩, fun t => ?_⟩
      show q (w t) ∈ V
      have h1 : q (w t) = γ t := congrFun (congrArg DFunLike.coe hqw) t
      rw [h1]
      exact (η t).2
  obtain ⟨ex, hex, hx'⟩ := key x.1 x.2
  obtain ⟨ey, hey, hy'⟩ := key y.1 y.2
  -- the fibre over `b` sits in `q ⁻¹' V`, since `b ∈ V`
  have hsub : ({b} : Set B) ⊆ V := by
    intro z hz
    rw [Set.mem_singleton_iff] at hz
    rw [hz]; exact hb
  -- two points of the fibre over `b` are joined inside it, hence inside `q ⁻¹' V`
  have hfib : JoinedIn (q ⁻¹' V) ex ey := by
    have hF' : PathConnectedSpace {x : E // q x = b} := hF
    obtain ⟨θ⟩ := hF'.joined ⟨ex, hex⟩ ⟨ey, hey⟩
    refine JoinedIn.mono ?_ (Set.preimage_mono hsub)
    refine ⟨θ.map (continuous_subtype_val : Continuous (Subtype.val : {x : E // q x = b} → E)),
      fun t => ?_⟩
    rw [Set.mem_preimage, Set.mem_singleton_iff]
    exact (θ.toContinuousMap t).2
  -- concatenate the three paths
  have hmain : JoinedIn (q ⁻¹' V) x.1 y.1 := (hx'.trans hfib).trans hy'.symm
  exact JoinedIn.joined_subtype hmain

end

end Work.Serre.DiscPair
