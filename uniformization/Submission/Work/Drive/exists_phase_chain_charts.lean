import Mathlib
import Submission.Work.Drive.cBallDefs
import Submission.Work.Drive.exists_locallyFinite_openCoordinateBall_cover
import Submission.Work.Drive.exists_walk_data

/-!
# The chain of charts to infinity (Hubbard, Chapter 1)

`Work.Drive.exists_phase_chain_charts`: on a connected, second countable, non-compact `ℂ`-charted
surface `X` there are points `a i`, charts `c i` in the maximal atlas and radii `ρ i > 0` such that

* `a 0 = z₀`, the sequence is injective, and `a i ≠ z₀` for `i > 0`;
* `a i, a (i+1)` lie in `(c i).source` with `‖(c i) (a (i+1)) - (c i) (a i)‖ < ρ i`;
* the closure of the `(c i)`-coordinate ball of radius `8 ρ i` about `a i` lies in `(c i).source`;
* the family of those coordinate balls is locally finite.

The point sequence together with the containers comes from `exists_walk_data`; the chart at step `i`
is the chart of the `i`-th container and the radius is the room of `a i` inside that container.  The
local finiteness is the local finiteness of the cover together with the fact that the containers run
to infinity.
-/

open Set Metric Filter
open scoped Topology Manifold

set_option linter.unusedSectionVars false
set_option linter.unusedVariables false

noncomputable section

namespace Work.Drive

variable {X : Type*} [TopologicalSpace X] [T2Space X] [ConnectedSpace X]
  [SecondCountableTopology X] [ChartedSpace ℂ X]
  [IsManifold (modelWithCornersSelf ℂ ℂ) 1 X]

theorem exists_phase_chain_charts {X : Type*} [TopologicalSpace X] [T2Space X] [ConnectedSpace X]
    [SecondCountableTopology X] [ChartedSpace ℂ X]
    [IsManifold (modelWithCornersSelf ℂ ℂ) 1 X]
    (hX : ¬ CompactSpace X) (z₀ : X) :
    ∃ (a : ℕ → X) (c : ℕ → OpenPartialHomeomorph X ℂ) (ρ : ℕ → ℝ),
      (∀ i : ℕ, c i ∈ IsManifold.maximalAtlas (modelWithCornersSelf ℂ ℂ) 1 X) ∧
      a 0 = z₀ ∧ (∀ i : ℕ, 0 < ρ i) ∧
      (∀ i : ℕ, a i ∈ (c i).source ∧ a (i + 1) ∈ (c i).source ∧
        ‖(c i) (a (i + 1)) - (c i) (a i)‖ < ρ i) ∧
      (∀ i : ℕ, closure {x : X | x ∈ (c i).source ∧
        (c i) x ∈ Metric.ball ((c i) (a i)) (8 * ρ i)} ⊆ (c i).source) ∧
      (∀ A : Set X, IsCompact A → {i : ℕ | (A ∩ {x : X | x ∈ (c i).source ∧
        (c i) x ∈ Metric.ball ((c i) (a i)) (8 * ρ i)}).Nonempty}.Finite) ∧
      (∀ i : ℕ, 0 < i → a i ≠ z₀) ∧
      Function.Injective a := by
  classical
  obtain ⟨a, ctr, U, c₀, r₀, ha0, hainj, hr₀pos, hr₀room, hUdef, hUlf, hctr, hmem, hstep⟩ :=
    exists_walk_data (X := X) hX z₀
  -- the coordinate description of the containers
  have hUchar : ∀ n z, z ∈ U n →
      dist ((chartAt ℂ (c₀ n)) z) ((chartAt ℂ (c₀ n)) (c₀ n)) < r₀ n := by
    intro n z hz
    have hz' : z ∈ (chartAt ℂ (c₀ n)).symm '' Metric.ball ((chartAt ℂ (c₀ n)) (c₀ n)) (r₀ n) := by
      rw [hUdef n] at hz; exact hz
    obtain ⟨w, hw, hwz⟩ := hz'
    have hwt : w ∈ (chartAt ℂ (c₀ n)).target :=
      hr₀room n (Metric.ball_subset_closedBall hw)
    have hzw : (chartAt ℂ (c₀ n)) z = w := by
      rw [← hwz, (chartAt ℂ (c₀ n)).right_inv hwt]
    rw [hzw]
    rwa [Metric.mem_ball] at hw
  have hUsrc : ∀ n z, z ∈ U n → z ∈ (chartAt ℂ (c₀ n)).source := by
    intro n z hz
    have hz' : z ∈ (chartAt ℂ (c₀ n)).symm '' Metric.ball ((chartAt ℂ (c₀ n)) (c₀ n)) (r₀ n) := by
      rw [hUdef n] at hz; exact hz
    obtain ⟨w, hw, hwz⟩ := hz'
    have hwt : w ∈ (chartAt ℂ (c₀ n)).target :=
      hr₀room n (Metric.ball_subset_closedBall hw)
    rw [← hwz]
    exact (chartAt ℂ (c₀ n)).map_target hwt
  -- the charts and radii
  let c : ℕ → OpenPartialHomeomorph X ℂ := fun i => chartAt ℂ (c₀ (ctr i))
  let ρ : ℕ → ℝ := fun i => (r₀ (ctr i) - dist ((chartAt ℂ (c₀ (ctr i))) (a i))
      ((chartAt ℂ (c₀ (ctr i))) (c₀ (ctr i)))) / 8
  have hρchar : ∀ i, ρ i = (r₀ (ctr i) - dist ((chartAt ℂ (c₀ (ctr i))) (a i))
      ((chartAt ℂ (c₀ (ctr i))) (c₀ (ctr i)))) / 8 := fun i => rfl
  have hρpos : ∀ i, 0 < ρ i := by
    intro i
    have h := hUchar (ctr i) (a i) (hmem i).1
    rw [hρchar i]
    linarith [hr₀pos (ctr i)]
  -- the closed ball of the statement lies in the chart target
  have hclosed : ∀ i, Metric.closedBall ((c i) (a i)) (8 * ρ i) ⊆ (c i).target := by
    intro i
    have hd := hUchar (ctr i) (a i) (hmem i).1
    have h8 : 8 * ρ i = r₀ (ctr i) - dist ((chartAt ℂ (c₀ (ctr i))) (a i))
        ((chartAt ℂ (c₀ (ctr i))) (c₀ (ctr i))) := by
      rw [hρchar i]; ring
    rw [h8]
    exact subset_trans (closedBall_room_subset (c := chartAt ℂ (c₀ (ctr i)))
      (x := c₀ (ctr i)) (u := a i) hd) (hr₀room (ctr i))
  -- the coordinate balls of the family lie in their container
  have hsub : ∀ i, {x : X | x ∈ (c i).source ∧
      (c i) x ∈ Metric.ball ((c i) (a i)) (8 * ρ i)} ⊆ U (ctr i) := by
    intro i x hx
    have hd := hUchar (ctr i) (a i) (hmem i).1
    have hx2 : dist ((chartAt ℂ (c₀ (ctr i))) x) ((chartAt ℂ (c₀ (ctr i))) (a i)) < 8 * ρ i := by
      have h := hx.2
      rwa [Metric.mem_ball] at h
    have hgoal : dist ((chartAt ℂ (c₀ (ctr i))) x) ((chartAt ℂ (c₀ (ctr i))) (a i)) <
        8 * ((r₀ (ctr i) - dist ((chartAt ℂ (c₀ (ctr i))) (a i))
          ((chartAt ℂ (c₀ (ctr i))) (c₀ (ctr i)))) / 8) := by
      rw [hρchar i] at hx2
      exact hx2
    have hb := ball_eight_subset (c := chartAt ℂ (c₀ (ctr i))) (x := c₀ (ctr i)) (u := a i)
      (r := r₀ (ctr i)) (by rw [Metric.mem_ball]; exact hd)
    have hball : (chartAt ℂ (c₀ (ctr i))) x ∈
        Metric.ball ((chartAt ℂ (c₀ (ctr i))) (a i))
          (8 * ((r₀ (ctr i) - dist ((chartAt ℂ (c₀ (ctr i))) (a i))
            ((chartAt ℂ (c₀ (ctr i))) (c₀ (ctr i)))) / 8)) := by
      rw [Metric.mem_ball]; exact hgoal
    rw [hUdef (ctr i)]
    exact ⟨(chartAt ℂ (c₀ (ctr i))) x, hb hball,
      (chartAt ℂ (c₀ (ctr i))).left_inv hx.1⟩
  refine ⟨a, c, ρ, fun i => IsManifold.chart_mem_maximalAtlas (c₀ (ctr i)), ha0, hρpos, ?_, ?_, ?_,
    ?_, hainj⟩
  · -- the step condition
    intro i
    have h1 : a i ∈ (c i).source := hUsrc (ctr i) (a i) (hmem i).1
    have h2 : a (i + 1) ∈ (c i).source := hUsrc (ctr i) (a (i + 1)) (hmem i).2
    have h3 : dist ((c i) (a (i + 1))) ((c i) (a i)) < ρ i := hstep i
    have h4 : ‖(c i) (a (i + 1)) - (c i) (a i)‖ < ρ i := by
      rw [← dist_eq_norm]; exact h3
    exact ⟨h1, h2, h4⟩
  · -- the closure is in the source
    intro i
    exact closure_cBall_subset_source (c := c i) (x := a i) (r := 8 * ρ i) (hclosed i)
  · -- local finiteness
    intro A hA
    have hN : (({n : ℕ | (U n ∩ A).Nonempty} : Set ℕ)).Finite :=
      hUlf.finite_nonempty_inter_compact hA
    have hctrT : ∀ n : ℕ, {i : ℕ | ctr i = n}.Finite := by
      intro n
      obtain ⟨K, hK⟩ := Filter.tendsto_atTop_atTop.mp hctr (n + 1)
      refine Set.Finite.subset (Set.finite_Iio K) fun i hi => ?_
      by_contra hcon
      have h2 : ctr i = n := hi
      have hKi : K ≤ i := not_lt.mp hcon
      have h1 : n + 1 ≤ ctr i := hK i hKi
      omega
    refine Set.Finite.subset (hN.biUnion fun n _ => hctrT n) ?_
    intro i hi
    have hne : (U (ctr i) ∩ A).Nonempty := by
      obtain ⟨x, hxA, hxS⟩ := hi
      exact ⟨x, hsub i hxS, hxA⟩
    exact Set.mem_biUnion hne rfl
  · -- points with positive index are not the base point
    intro i hi hcon
    have h0 : a i = a 0 := by rw [hcon, ha0]
    exact absurd (hainj h0) (by omega)

end Work.Drive
