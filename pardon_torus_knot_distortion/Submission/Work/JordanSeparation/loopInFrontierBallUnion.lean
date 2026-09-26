import Mathlib
import Submission.Work.Smooth.SphereJordan.planeIndex
import Submission.Work.Smooth.SphereJordan.pos_infDist_componentIn
import Submission.Work.Smooth.SphereJordan.walk_of_preconnected
import Submission.Work.Smooth.SphereJordan.chainFrontierLoop

/-!
# A frontier loop of index `1` for a finite union of equal closed balls

If the origin lies in the *open* union `⋃_{w ∈ P} ball w r` of finitely many balls of equal radius
`r > 0`, then the frontier of the closed union `⋃_{w ∈ P} closedBall w r` contains a closed loop of
index `1`.

The proof restricts to the connected component of `0` in the closed union (a union of balls of the
same radius, whose union of open balls is preconnected), walks over the centres of the balls meeting
that component, and applies the chain statement
`Work.Smooth.SphereJordan.chainFrontierLoop`.

The combinatorial covering-walk input (the overlap graph and its connectedness) is reproduced here
so that this module only depends on `walk_of_preconnected`, `pos_infDist_componentIn` and
`chainFrontierLoop`.
-/

namespace Work.JordanSeparation

open Set

noncomputable section

/-- The **overlap graph** of a finite set `P` of points of `ℂ` with radius `r`: its vertices are
the points of `P`, and two distinct vertices are adjacent when the corresponding closed discs of
radius `r` intersect, i.e. when the distance between the points is at most `2 * r`. -/
def overlapGraph (P : Finset ℂ) (r : ℝ) : SimpleGraph {z : ℂ // z ∈ P} where
  Adj x y := x ≠ y ∧ dist x.1 y.1 ≤ 2 * r
  symm := ⟨fun x y h => ⟨h.1.symm, by simpa [dist_comm] using h.2⟩⟩
  loopless := ⟨fun x h => h.1 rfl⟩

@[simp] lemma overlapGraph_adj {P : Finset ℂ} {r : ℝ} {x y : {z : ℂ // z ∈ P}} :
    (overlapGraph P r).Adj x y ↔ x ≠ y ∧ dist x.1 y.1 ≤ 2 * r := Iff.rfl

/-- Two equal closed discs of radius `r` whose union is preconnected are connected by a chain in the
overlap graph. -/
theorem overlapGraph_preconnected {P : Finset ℂ} {r : ℝ} (hr : 0 < r)
    (hconn : IsPreconnected (⋃ w ∈ P, Metric.closedBall w r)) :
    (overlapGraph P r).Preconnected := by
  classical
  intro x y
  let Reach : {z : ℂ // z ∈ P} → Prop := fun w => (overlapGraph P r).Reachable x w
  have hstepReach : ∀ {w w' : {z : ℂ // z ∈ P}}, Reach w → (overlapGraph P r).Adj w w' →
      Reach w' := fun hw hww' => hw.trans hww'.reachable
  have hxReach : Reach x := SimpleGraph.Reachable.refl x
  have hxT : x ∈ P.attach.filter Reach := by
    rw [Finset.mem_filter]
    exact ⟨Finset.mem_attach P x, hxReach⟩
  set T : Finset {z : ℂ // z ∈ P} := P.attach.filter Reach with hT
  set U : Finset {z : ℂ // z ∈ P} := P.attach.filter (fun w => ¬ Reach w) with hU
  set A : Set ℂ := ⋃ w ∈ T, Metric.closedBall w.1 r with hA
  set B : Set ℂ := ⋃ w ∈ U, Metric.closedBall w.1 r with hB
  have hAcl : IsClosed A := by
    rw [hA]; exact isClosed_biUnion_finset (fun i _ => Metric.isClosed_closedBall)
  have hBcl : IsClosed B := by
    rw [hB]; exact isClosed_biUnion_finset (fun i _ => Metric.isClosed_closedBall)
  have hsub : (⋃ w ∈ P, Metric.closedBall w r) ⊆ A ∪ B := by
    intro z hz
    obtain ⟨w, hwP, hzw⟩ := Set.mem_iUnion₂.mp hz
    let wz : {z : ℂ // z ∈ P} := ⟨w, hwP⟩
    have hmem : wz ∈ P.attach := Finset.mem_attach P wz
    by_cases hR : Reach wz
    · left
      rw [hA]
      exact Set.mem_iUnion₂.mpr ⟨wz, by rw [hT, Finset.mem_filter]; exact ⟨hmem, hR⟩, hzw⟩
    · right
      rw [hB]
      exact Set.mem_iUnion₂.mpr ⟨wz, by rw [hU, Finset.mem_filter]; exact ⟨hmem, hR⟩, hzw⟩
  have hdisj : (⋃ w ∈ P, Metric.closedBall w r) ∩ (A ∩ B) = ∅ := by
    rw [← Set.not_nonempty_iff_eq_empty]
    rintro ⟨z, hzS, hzA, hzB⟩
    rw [hA] at hzA
    rw [hB] at hzB
    obtain ⟨w, hwT, hzw⟩ := Set.mem_iUnion₂.mp hzA
    obtain ⟨w', hwU, hzw'⟩ := Set.mem_iUnion₂.mp hzB
    rw [hT, Finset.mem_filter] at hwT
    rw [hU, Finset.mem_filter] at hwU
    obtain ⟨-, hwReach⟩ := hwT
    obtain ⟨-, hwNotReach⟩ := hwU
    have hdist : dist w.1 w'.1 ≤ 2 * r := by
      have h1 : dist z w.1 ≤ r := Metric.mem_closedBall.mp hzw
      have h2 : dist z w'.1 ≤ r := Metric.mem_closedBall.mp hzw'
      calc dist w.1 w'.1 ≤ dist w.1 z + dist z w'.1 := dist_triangle _ _ _
        _ = dist z w.1 + dist z w'.1 := by rw [dist_comm w.1 z]
        _ ≤ r + r := by linarith
        _ = 2 * r := by ring
    by_cases hww : w = w'
    · exact hwNotReach (hww ▸ hwReach)
    · exact hwNotReach (hstepReach hwReach ⟨hww, hdist⟩)
  have hSsubA : (⋃ w ∈ P, Metric.closedBall w r) ⊆ A := by
    rcases (isPreconnected_iff_subset_of_disjoint_closed.mp hconn) A B hAcl hBcl hsub hdisj with
      h | h
    · exact h
    · exfalso
      have hxS : x.1 ∈ (⋃ w ∈ P, Metric.closedBall w r) :=
        Set.mem_iUnion₂.mpr ⟨x.1, x.2, Metric.mem_closedBall.mpr (by simpa using hr.le)⟩
      have hxA : x.1 ∈ A :=
        Set.mem_iUnion₂.mpr ⟨x, by rw [hT]; exact hxT,
          Metric.mem_closedBall.mpr (by simpa using hr.le)⟩
      have hxB : x.1 ∈ B := h hxS
      have hmem : x.1 ∈ (⋃ w ∈ P, Metric.closedBall w r) ∩ (A ∩ B) := ⟨hxS, hxA, hxB⟩
      rw [hdisj] at hmem
      exact hmem
  have hyS : y.1 ∈ (⋃ w ∈ P, Metric.closedBall w r) :=
    Set.mem_iUnion₂.mpr ⟨y.1, y.2, Metric.mem_closedBall.mpr (by simpa using hr.le)⟩
  have hyA : y.1 ∈ A := hSsubA hyS
  rw [hA] at hyA
  obtain ⟨w, hwT, hyw⟩ := Set.mem_iUnion₂.mp hyA
  rw [hT, Finset.mem_filter] at hwT
  obtain ⟨-, hwReach⟩ := hwT
  have hdist : dist w.1 y.1 ≤ 2 * r := by
    have h : dist y.1 w.1 ≤ r := Metric.mem_closedBall.mp hyw
    rw [dist_comm] at h
    linarith
  by_cases hwy : w = y
  · exact hwy ▸ hwReach
  · exact hwReach.trans (show (overlapGraph P r).Adj w y from ⟨hwy, hdist⟩).reachable

/-- A finite set of centres whose closed discs of radius `r` have preconnected union admits a walk
starting at any prescribed point and visiting every centre, with successive steps of length at most
`2 * r`. -/
theorem exists_walk_covering {P : Finset ℂ} {r : ℝ} (hr : 0 < r) {a : ℂ} (ha : a ∈ P)
    (hconn : IsPreconnected (⋃ w ∈ P, Metric.closedBall w r)) :
    ∃ (n : ℕ) (u : Fin (n + 1) → ℂ), u 0 = a ∧ (∀ i, u i ∈ P) ∧
      (∀ w ∈ P, ∃ i, u i = w) ∧ (∀ i : Fin n, dist (u i.castSucc) (u i.succ) ≤ 2 * r) := by
  obtain ⟨n, u, h0, hsurj, hadj⟩ :=
    Work.Smooth.SphereJordan.walk_of_preconnected (overlapGraph P r) (overlapGraph_preconnected hr hconn) ⟨a, ha⟩
  refine ⟨n, fun i => (u i).1, ?_, ?_, ?_, ?_⟩
  · exact congrArg Subtype.val h0
  · intro i
    exact (u i).2
  · intro w hw
    obtain ⟨i, hi⟩ := hsurj ⟨w, hw⟩
    exact ⟨i, congrArg Subtype.val hi⟩
  · intro i
    exact (hadj i).2

/-- **Conditional assembly.** If the chain statement holds for every walk with steps `≤ 2 * r`, and
every preconnected finite union of equal closed balls admits a covering walk, then the frontier loop
exists in general. -/
theorem loopInFrontierBallUnion_of_chain
    (hchain : ∀ (n : ℕ) (u : Fin (n + 1) → ℂ) (r : ℝ), 0 < r →
      (∀ i : Fin n, dist (u i.castSucc) (u i.succ) ≤ 2 * r) →
      (0 : ℂ) ∈ ⋃ i, Metric.ball (u i) r →
      ∃ c : C(unitInterval, ℂ), (∀ t, c t ∈ frontier (⋃ i, Metric.closedBall (u i) r)) ∧
        c 0 = c 1 ∧ Work.Smooth.SphereJordan.loopIndex c = 1)
    (hwalk : ∀ (Q : Finset ℂ) (r : ℝ), 0 < r → ∀ a ∈ Q,
      IsPreconnected (⋃ w ∈ Q, Metric.closedBall w r) →
      ∃ (n : ℕ) (u : Fin (n + 1) → ℂ), u 0 = a ∧ (∀ i, u i ∈ Q) ∧
        (∀ w ∈ Q, ∃ i, u i = w) ∧ (∀ i : Fin n, dist (u i.castSucc) (u i.succ) ≤ 2 * r))
    {P : Finset ℂ} {r : ℝ} (hr : 0 < r) (h0 : (0 : ℂ) ∈ ⋃ w ∈ P, Metric.ball w r) :
    ∃ c : C(unitInterval, ℂ),
      (∀ t, c t ∈ frontier (⋃ w ∈ P, Metric.closedBall w r)) ∧ c 0 = c 1 ∧
      Work.Smooth.SphereJordan.loopIndex c = 1 := by
  classical
  obtain ⟨a, haP, ha0⟩ := Set.mem_iUnion₂.mp h0
  have ha0c : (0 : ℂ) ∈ Metric.closedBall a r :=
    Metric.mem_closedBall.mpr (Metric.mem_ball.mp ha0).le
  set S : Set ℂ := ⋃ w ∈ P, Metric.closedBall w r with hSdef
  have h0S : (0 : ℂ) ∈ S := hSdef ▸ Set.mem_iUnion₂.mpr ⟨a, haP, ha0c⟩
  have h0C : (0 : ℂ) ∈ connectedComponentIn S 0 := mem_connectedComponentIn h0S
  have hCpre : IsPreconnected (connectedComponentIn S 0) := isPreconnected_connectedComponentIn
  have hCsub : connectedComponentIn S 0 ⊆ S := connectedComponentIn_subset S 0
  have hCcl : IsClosed (connectedComponentIn S 0) := by
    rw [hSdef] at h0S ⊢
    exact Work.Smooth.SphereJordan.isClosed_connectedComponentIn_union h0S
  set Q : Finset ℂ :=
    P.filter (fun w => (connectedComponentIn S 0 ∩ Metric.closedBall w r).Nonempty) with hQdef
  have hQmem : ∀ w, w ∈ Q ↔
      w ∈ P ∧ (connectedComponentIn S 0 ∩ Metric.closedBall w r).Nonempty := by
    intro w; rw [hQdef, Finset.mem_filter]
  have haQ : a ∈ Q := (hQmem a).mpr ⟨haP, ⟨0, h0C, ha0c⟩⟩
  have hballsub : ∀ w ∈ Q, Metric.closedBall w r ⊆ connectedComponentIn S 0 := by
    intro w hw
    obtain ⟨hwp, y, hyC, hyw⟩ := (hQmem w).mp hw
    have hpre : IsPreconnected (Metric.closedBall w r) := (convex_closedBall w r).isPreconnected
    have hsF : Metric.closedBall w r ⊆ S :=
      fun z hz => hSdef ▸ Set.mem_iUnion₂.mpr ⟨w, hwp, hz⟩
    have hsub : Metric.closedBall w r ⊆ connectedComponentIn S y :=
      hpre.subset_connectedComponentIn hyw hsF
    have heq : connectedComponentIn S y = connectedComponentIn S 0 :=
      (connectedComponentIn_eq hyC).symm
    exact fun z hz => heq ▸ hsub hz
  have hunion : (⋃ w ∈ Q, Metric.closedBall w r) = connectedComponentIn S 0 := by
    refine Subset.antisymm ?_ ?_
    · intro z hz
      obtain ⟨w, hwQ, hzw⟩ := Set.mem_iUnion₂.mp hz
      exact hballsub w hwQ hzw
    · intro z hz
      obtain ⟨w, hwP, hzw⟩ := Set.mem_iUnion₂.mp (hCsub hz)
      exact Set.mem_iUnion₂.mpr ⟨w, (hQmem w).mpr ⟨hwP, ⟨z, hz, hzw⟩⟩, hzw⟩
  have hconn : IsPreconnected (⋃ w ∈ Q, Metric.closedBall w r) := hunion ▸ hCpre
  obtain ⟨n, u, hu0, huQ, hucov, hstep⟩ := hwalk Q r hr a haQ hconn
  have h0' : (0 : ℂ) ∈ ⋃ i, Metric.ball (u i) r := by
    obtain ⟨i, hi⟩ := hucov a haQ
    exact Set.mem_iUnion.mpr ⟨i, hi ▸ ha0⟩
  obtain ⟨c, hcfront, hcloop, hidx⟩ := hchain n u r hr hstep h0'
  have hunion' : (⋃ i, Metric.closedBall (u i) r) = connectedComponentIn S 0 := by
    rw [← hunion]
    refine Subset.antisymm ?_ ?_
    · intro z hz
      obtain ⟨i, hzi⟩ := Set.mem_iUnion.mp hz
      exact Set.mem_iUnion₂.mpr ⟨u i, huQ i, hzi⟩
    · intro z hz
      obtain ⟨w, hwQ, hzw⟩ := Set.mem_iUnion₂.mp hz
      obtain ⟨i, hi⟩ := hucov w hwQ
      exact Set.mem_iUnion.mpr ⟨i, hi ▸ hzw⟩
  have hfrontier : frontier (connectedComponentIn S 0) ⊆ frontier S := by
    intro z hz
    have hzC : z ∈ connectedComponentIn S 0 := hCcl.closure_eq ▸ hz.1
    refine ⟨subset_closure (hCsub hzC), ?_⟩
    intro hint
    obtain ⟨ε, hε, hball⟩ := Metric.isOpen_iff.mp isOpen_interior z hint
    have hballsub' : Metric.ball z ε ⊆ connectedComponentIn S z :=
      (convex_ball z ε).isPreconnected.subset_connectedComponentIn (Metric.mem_ball_self hε)
        (fun t ht => interior_subset (hball ht))
    have hcomp : connectedComponentIn S z = connectedComponentIn S 0 :=
      (connectedComponentIn_eq hzC).symm
    rw [hcomp] at hballsub'
    exact hz.2 (interior_maximal hballsub' (Metric.isOpen_ball) (Metric.mem_ball_self hε))
  exact ⟨c, fun t => hfrontier (hunion' ▸ hcfront t), hcloop, hidx⟩

/-- **The frontier loop of a finite union of equal closed balls.**

If the origin lies in the *open* union `⋃_{w ∈ P} ball w r` of finitely many balls of equal radius
`r > 0`, then the frontier of the closed union contains a closed loop of index `1`.  (The loop need
not be simple: the boundary of a union of discs may touch itself.) -/
theorem loopInFrontierBallUnion {P : Finset ℂ} {r : ℝ} (hr : 0 < r)
    (h0 : (0 : ℂ) ∈ ⋃ w ∈ P, Metric.ball w r) :
    ∃ c : C(unitInterval, ℂ), (∀ t, c t ∈ frontier (⋃ w ∈ P, Metric.closedBall w r)) ∧
      c 0 = c 1 ∧ Work.Smooth.SphereJordan.loopIndex c = 1 :=
  loopInFrontierBallUnion_of_chain
    (fun _ _ _ hr' hstep h0' => Work.Smooth.SphereJordan.chainFrontierLoop hr' hstep h0')
    (fun Q r hr' a ha hconn => exists_walk_covering hr' ha hconn)
    hr h0

end

end Work.JordanSeparation
