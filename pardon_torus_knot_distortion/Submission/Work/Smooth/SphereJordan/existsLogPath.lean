import Mathlib
import Submission.Work.Smooth.SphereJordan.planeIndex
import Submission.Work.Smooth.SphereJordan.planeIndexGeom
import Submission.Work.BoxShrink.Pinch.janiszewskiDisjointCompact
import Submission.Work.Smooth.SphereJordan.loopSharedLemmas
import Submission.Work.Smooth.SphereJordan.ballUnionToolkit
import Submission.Work.Smooth.SphereJordan.pos_infDist_componentIn
import Submission.Work.Smooth.SphereJordan.Vendored.frontierCurveOfOpenBallUnionAux
import Submission.Work.Smooth.SphereJordan.jordanLoopIndexOne

namespace Work.Smooth.SphereJordan

open Set

noncomputable section

/-- **The frontier loop of a finite union of equal closed balls.**

If the origin lies in the *open* union `⋃ w ∈ P, ball w r` of finitely many balls of equal radius,
then the frontier of the closed union contains a closed loop of index `1`.  (The loop need not be
simple: the boundary of a union of discs may touch itself.)  This is the single geometric input of
`existsShellLoop`, and hence of `existsLogPath`. -/
theorem loopInFrontierBallUnion {P : Finset ℂ} {r : ℝ} (hr : 0 < r)
    (h0 : (0 : ℂ) ∈ ⋃ w ∈ P, Metric.ball w r) :
    ∃ c : C(unitInterval, ℂ),
      (∀ t, c t ∈ frontier (⋃ w ∈ P, Metric.closedBall w r)) ∧
      c 0 = c 1 ∧ Work.Smooth.SphereJordan.loopIndex c = 1 := by
  -- a Jordan curve in the frontier enclosing `0`
  obtain ⟨γ, hγc, hγper, hγinj, hγrange, hγbdd⟩ :=
    Work.Smooth.SphereJordan.frontierCurveOfOpenBallUnionAux P hr h0
  -- `0` is interior to the union, hence is not on the frontier, hence not on `γ`
  have h0int : (0 : ℂ) ∈ interior (⋃ w ∈ P, Metric.closedBall w r) := by
    obtain ⟨w, hwP, hw⟩ := Set.mem_iUnion₂.mp h0
    refine interior_mono (fun z hz => Set.mem_iUnion₂.mpr ⟨w, hwP, hz⟩) ?_
    exact Metric.ball_subset_interior_closedBall hw
  have h0γ : (0 : ℂ) ∉ Set.range γ := by
    rintro ⟨t, ht⟩
    exact (hγrange ⟨t, rfl⟩).2 (ht ▸ h0int)
  -- a simple closed curve enclosing `0` carries a loop of index `1` on its trace
  obtain ⟨c, hcrange, hcloop, hidx⟩ :=
    Work.Smooth.SphereJordan.jordanLoopIndexOne hγc hγper hγinj h0γ hγbdd
  exact ⟨c, fun t => hγrange (hcrange t), hcloop, hidx⟩

theorem existsShellLoop_of_frontierLoop
    (hfront : ∀ (P : Finset ℂ) (r : ℝ), 0 < r →
      (0 : ℂ) ∈ ⋃ w ∈ P, Metric.ball w r →
      ∃ c : C(unitInterval, ℂ), (∀ t, c t ∈ frontier (⋃ w ∈ P, Metric.closedBall w r)) ∧
        c 0 = c 1 ∧ Work.Smooth.SphereJordan.loopIndex c = 1)
    {K : Set ℂ} (hK : IsCompact K) (h0 : (0 : ℂ) ∈ K) {ε : ℝ} (hε : 0 < ε) :
    ∃ c : C(unitInterval, ℂ), (∀ t, c t ∉ K) ∧ (∀ t, ∃ k ∈ K, dist (c t) k ≤ ε) ∧
      c 0 = c 1 ∧ Work.Smooth.SphereJordan.loopIndex c = 1 := by
  obtain ⟨P, hPK, hcov⟩ := exists_ballUnion_cover hK hε
  have h0mem : (0 : ℂ) ∈ ⋃ w ∈ P, Metric.ball w (ε / 2) := by
    obtain ⟨w, hwP, hw⟩ := Set.mem_iUnion₂.mp (hcov h0)
    exact Set.mem_iUnion₂.mpr ⟨w, hwP, by rw [Metric.mem_ball] at hw ⊢; linarith⟩
  obtain ⟨c, hcrange, hcloop, hidx⟩ := hfront P (ε / 2) (by linarith) h0mem
  obtain ⟨hne, hnear⟩ := frontier_closedBall_union_spec hε hPK hcov
  exact ⟨c, fun t => hne (c t) (hcrange t), fun t => hnear (c t) (hcrange t), hcloop, hidx⟩

/-- **The shell lemma.**  For a compact set `K` containing `0` and any `ε > 0`, there is a closed
loop avoiding `K`, everywhere within `ε` of `K`, of index `1`. -/
theorem existsShellLoop {K : Set ℂ} (hK : IsCompact K) (h0 : (0 : ℂ) ∈ K) {ε : ℝ} (hε : 0 < ε) :
    ∃ c : C(unitInterval, ℂ), (∀ t, c t ∉ K) ∧ (∀ t, ∃ k ∈ K, dist (c t) k ≤ ε)
      ∧ c 0 = c 1 ∧ Work.Smooth.SphereJordan.loopIndex c = 1 :=
  existsShellLoop_of_frontierLoop
    (fun P r hr h0mem => loopInFrontierBallUnion hr h0mem) hK h0 hε

theorem existsLogPath {F : Set ℂ} (hF : IsClosed F) (h0 : (0 : ℂ) ∈ F)
    (hbdd : Bornology.IsBounded (connectedComponentIn F (0 : ℂ))) :
    ∃ Λ : C(unitInterval, ℂ), (∀ t, Complex.exp (Λ t) ∉ F) ∧
      Λ 1 = Λ 0 + 2 * ↑Real.pi * Complex.I := by
  obtain ⟨U, ρ, hUcomp, h0U, hUsubF, hρpos, hgap⟩ := exists_compact_gap hF h0 hbdd
  obtain ⟨c, hcU, hcnear, hcloop, hidx⟩ := existsShellLoop hUcomp h0U (by linarith : (0:ℝ) < ρ/2)
  have hcF : ∀ t, c t ∉ F := by
    intro t hzt
    obtain ⟨k, hkU, hdk⟩ := hcnear t
    by_cases hztU : c t ∈ U
    · exact hcU t hztU
    · have hρle : ρ ≤ dist k (c t) := hgap k hkU (c t) hzt hztU
      rw [dist_comm] at hρle
      linarith [hdk]
  have hc0 : ∀ t, c t ≠ 0 := fun t h => hcU t (h ▸ h0U)
  obtain ⟨Λ, hΛ, -, -⟩ := argChangeLift c hc0
  have hincr : Λ 1 - Λ 0 = 2 * ↑Real.pi * Complex.I := by
    rw [loopIndex_spec c hc0 hcloop Λ hΛ, hidx]
    ring
  refine ⟨Λ, fun t => ?_, ?_⟩
  · rw [hΛ t]; exact hcF t
  · linear_combination hincr


/-! ## Assembly of the general case from the chain case

The general frontier loop follows from the chain version together with the covering walk: restrict
the family to the centres whose ball meets the component `C` of `0`, whose union is then exactly `C`
and preconnected, walk over those centres, apply the chain statement, and use
`frontier C ⊆ frontier S`.
-/

/-- **Conditional assembly.**  If the chain statement holds for every walk with steps `≤ 2 * r`, and
every connected finite union of equal closed balls admits a covering walk, then
`loopInFrontierBallUnion` holds in general. -/
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
    exact isClosed_connectedComponentIn_union h0S
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

end

end Work.Smooth.SphereJordan
