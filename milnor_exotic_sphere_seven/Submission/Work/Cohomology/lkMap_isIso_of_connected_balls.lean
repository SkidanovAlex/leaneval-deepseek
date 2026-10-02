import Mathlib
import Submission.Work.Cohomology.StageSplitDefs
import Submission.Work.Cohomology.lkMap_isIso_of_convex
import Submission.Work.Cohomology.LK_closedBall_union_injective
import Submission.Work.Cohomology.union_ball_chain

-- Lean v4.35.0-rc3: restore v4.34 instance-unification transparency (port).
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
set_option synthInstance.maxHeartbeats 400000

/-!
# The local homology of a connected finite union of closed balls is that of a point

For `T = ⋃_{j : Fin k} closedBall (c j) (r j)` a finite union of closed balls of positive radius
in `ℝ^N` (`N ≥ 1`) whose union is connected, and any point `x ∈ T`, the localization map
`lkMap : LK N T → LK N {x}` is a bijection.

* **Surjectivity** uses that `T` is contained in some closed ball `D`:  the map
  `lkMap : LK N D → LK N {x}` is bijective (`lkMap_isIso_of_convex`), and it factors as
  `lkMap : LK N D → LK N T → LK N {x}`.
* **Injectivity** uses connectedness: a class killed at `x` is killed at the centre of the ball
  containing `x`, and this propagates along a chain of intersecting balls (`union_ball_chain`) to
  the centre of every ball; the product localization is injective
  (`LK_closedBall_union_injective`).
-/

set_option backward.isDefEq.respectTransparency false
set_option linter.unusedVariables false
set_option linter.style.haveILetI false

open Set

namespace Work.Cohomology

noncomputable section

variable {N : ℕ}

/-- `lkMap` only depends on the two sets, not on the proof of the inclusion. -/
private lemma lkMap_congr' {K K' : Set (EuclideanSpace ℝ (Fin N))} (h h' : K ⊆ K') :
    lkMap (N := N) h = lkMap (N := N) h' := by
  rw [Subsingleton.elim h h']

/-- Functoriality of `lkMap` in the form `{y} ⊆ B ⊆ T`. -/
private lemma lkMap_comp_singleton {N : ℕ} {T B : Set (EuclideanSpace ℝ (Fin N))}
    {y : EuclideanSpace ℝ (Fin N)} (h₁ : ({y} : Set (EuclideanSpace ℝ (Fin N))) ⊆ B)
    (h₂ : B ⊆ T) (h : ({y} : Set (EuclideanSpace ℝ (Fin N))) ⊆ T) :
    lkMap (N := N) h = (lkMap (N := N) h₁).comp (lkMap (N := N) h₂) := by
  rw [← lkMap_congr' (h₁.trans h₂) h, lkMap_comp]

/-- The single closed ball localization is injective (a closed ball is convex compact). -/
private lemma lkMap_singleton_closedBall_injective {N : ℕ} (hN : 1 ≤ N) {k : ℕ}
    (c : Fin k → EuclideanSpace ℝ (Fin N)) (r : Fin k → ℝ) (hr : ∀ j, 0 < r j) (j : Fin k)
    {y : EuclideanSpace ℝ (Fin N)} (hy : y ∈ Metric.closedBall (c j) (r j)) :
    Function.Injective (lkMap (N := N)
      (K := ({y} : Set (EuclideanSpace ℝ (Fin N))))
      (K' := Metric.closedBall (c j) (r j))
      (Set.singleton_subset_iff.mpr hy)) :=
  (lkMap_isIso_of_convex hN (isCompact_closedBall (c j) (r j)) (convex_closedBall (c j) (r j))
    ⟨c j, Metric.mem_closedBall_self (le_of_lt (hr j))⟩ hy).1

theorem lkMap_isIso_of_connected_balls {N : ℕ} (hN : 1 ≤ N) {k : ℕ}
    (c : Fin k → EuclideanSpace ℝ (Fin N)) (r : Fin k → ℝ) (hr : ∀ j, 0 < r j)
    (hconn : IsConnected (⋃ j, Metric.closedBall (c j) (r j)))
    (x : EuclideanSpace ℝ (Fin N)) (hx : x ∈ ⋃ j, Metric.closedBall (c j) (r j)) :
    Function.Bijective (Work.Cohomology.lkMap (N := N) (Set.singleton_subset_iff.mpr hx)) := by
  classical
  -- Notation for the union
  have hU : IsConnected (⋃ i ∈ (Finset.univ : Finset (Fin k)), Metric.closedBall (c i) (r i)) := by
    have h : (⋃ i ∈ (Finset.univ : Finset (Fin k)), Metric.closedBall (c i) (r i))
        = (⋃ i, Metric.closedBall (c i) (r i)) := by ext y; simp
    rw [h]; exact hconn
  refine ⟨?hinj, ?hsurj⟩
  case hinj =>
    -- It suffices that a class killed at `x` vanishes.
    rw [Function.Injective]
    intro β₁ β₂ hβ
    have hker : ∀ β : LK N (⋃ i, Metric.closedBall (c i) (r i)),
        lkMap (N := N) (Set.singleton_subset_iff.mpr hx) β = 0 → β = 0 := by
      intro β hβ
      obtain ⟨j0, hj0⟩ := Set.mem_iUnion.mp hx
      let P : Fin k → Prop := fun j => lkMap (N := N)
        (K := Metric.closedBall (c j) (r j)) (K' := ⋃ i, Metric.closedBall (c i) (r i))
        (Set.subset_iUnion (fun i => Metric.closedBall (c i) (r i)) j) β = 0
      -- base case: the ball containing `x`
      have hbase : P j0 := by
        have hcomp := lkMap_comp_singleton (T := ⋃ i, Metric.closedBall (c i) (r i))
          (B := Metric.closedBall (c j0) (r j0)) (y := x)
          (Set.singleton_subset_iff.mpr hj0)
          (Set.subset_iUnion (fun i => Metric.closedBall (c i) (r i)) j0)
          (Set.singleton_subset_iff.mpr hx)
        have h1 : lkMap (N := N) (Set.singleton_subset_iff.mpr hx) β = 0 := hβ
        rw [hcomp, LinearMap.comp_apply] at h1
        exact lkMap_singleton_closedBall_injective hN c r hr j0 hj0 (by rw [h1, map_zero])
      -- propagation step
      have hstep : ∀ {i j : Fin k},
          (Metric.closedBall (c i) (r i) ∩ Metric.closedBall (c j) (r j)).Nonempty → P i → P j := by
        intro i j hij hPi
        obtain ⟨y, hyi, hyj⟩ := hij
        have hyT : y ∈ ⋃ i, Metric.closedBall (c i) (r i) := Set.mem_iUnion.mpr ⟨i, hyi⟩
        have hcomp1 := lkMap_comp_singleton (T := ⋃ i, Metric.closedBall (c i) (r i))
          (B := Metric.closedBall (c i) (r i)) (y := y)
          (Set.singleton_subset_iff.mpr hyi)
          (Set.subset_iUnion (fun i => Metric.closedBall (c i) (r i)) i)
          (Set.singleton_subset_iff.mpr hyT)
        have hmid : lkMap (N := N) (Set.singleton_subset_iff.mpr hyT) β = 0 := by
          rw [hcomp1, LinearMap.comp_apply, hPi, map_zero]
        have hcomp2 := lkMap_comp_singleton (T := ⋃ i, Metric.closedBall (c i) (r i))
          (B := Metric.closedBall (c j) (r j)) (y := y)
          (Set.singleton_subset_iff.mpr hyj)
          (Set.subset_iUnion (fun i => Metric.closedBall (c i) (r i)) j)
          (Set.singleton_subset_iff.mpr hyT)
        rw [hcomp2, LinearMap.comp_apply] at hmid
        exact lkMap_singleton_closedBall_injective hN c r hr j hyj (by rw [hmid, map_zero])
      -- the chain of balls joining `j0` to any `j`
      have hP : ∀ j, P j := by
        intro j
        have hchain := union_ball_chain (s := (Finset.univ : Finset (Fin k)))
          (B := fun i => Metric.closedBall (c i) (r i))
          (fun i _ => Metric.isClosed_closedBall)
          (fun i _ => Metric.isConnected_closedBall (le_of_lt (hr i)))
          hU (Finset.mem_univ j0) (Finset.mem_univ j)
        induction hchain with
        | refl => exact hbase
        | tail _ hbc ih => exact hstep hbc.2.2 ih
      -- apply the product localization injectivity
      refine LK_closedBall_union_injective hN c r hr (fun j => c j)
        (fun j => Metric.mem_closedBall_self (le_of_lt (hr j))) β ?_
      intro j
      have hcomp := lkMap_comp_singleton (T := ⋃ i, Metric.closedBall (c i) (r i))
        (B := Metric.closedBall (c j) (r j)) (y := c j)
        (Set.singleton_subset_iff.mpr (Metric.mem_closedBall_self (le_of_lt (hr j))))
        (Set.subset_iUnion (fun i => Metric.closedBall (c i) (r i)) j)
        (Set.singleton_subset_iff.mpr
          (Set.mem_iUnion.mpr ⟨j, Metric.mem_closedBall_self (le_of_lt (hr j))⟩))
      rw [hcomp, LinearMap.comp_apply, hP j, map_zero]
    have hsub : β₁ - β₂ = 0 := hker (β₁ - β₂) (by rw [map_sub, hβ, sub_self])
    exact sub_eq_zero.mp hsub
  case hsurj =>
    -- `T` is contained in a closed ball `D = closedBall 0 R`, whose localization is bijective
    obtain ⟨R, hR⟩ := (isCompact_iUnion (fun j => isCompact_closedBall (c j) (r j))).isBounded.subset_closedBall (0 : EuclideanSpace ℝ (Fin N))
    have hxD : x ∈ Metric.closedBall (0 : EuclideanSpace ℝ (Fin N)) R := hR hx
    have hR0 : 0 ≤ R := le_trans dist_nonneg (Metric.mem_closedBall.mp hxD)
    have hbij : Function.Bijective (lkMap (N := N) (Set.singleton_subset_iff.mpr hxD)) :=
      lkMap_isIso_of_convex hN (isCompact_closedBall (0 : EuclideanSpace ℝ (Fin N)) R)
        (convex_closedBall _ _) ⟨0, Metric.mem_closedBall_self hR0⟩ hxD
    rw [Function.Surjective]
    intro y
    obtain ⟨z, hz⟩ := hbij.2 y
    refine ⟨lkMap (N := N) (K := ⋃ i, Metric.closedBall (c i) (r i))
        (K' := Metric.closedBall (0 : EuclideanSpace ℝ (Fin N)) R) hR z, ?_⟩
    rw [← LinearMap.comp_apply, ← (lkMap_comp_singleton
      (h₁ := Set.singleton_subset_iff.mpr hx) hR (Set.singleton_subset_iff.mpr hxD))]
    exact hz

end

end Work.Cohomology
