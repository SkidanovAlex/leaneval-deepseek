import Mathlib
import Submission.Work.Smooth.SphereJordan.Vendored.frontierCurveOfOpenBallUnionAux
import Submission.Work.Smooth.SphereJordan.jordanLoopIndexOne

namespace Work.Smooth.SphereJordan

open Set

noncomputable section

/-- The `Finset`-form and `Fin`-form of the union of *open* balls agree. -/
private theorem cfl_iUnion_image_openBall {n : ℕ} (u : Fin (n + 1) → ℂ) (r : ℝ) :
    (⋃ w ∈ (Finset.univ.image u : Finset ℂ), Metric.ball w r)
      = ⋃ i : Fin (n + 1), Metric.ball (u i) r := by
  ext z
  constructor
  · intro hz
    obtain ⟨w, hw, hzw⟩ := Set.mem_iUnion₂.mp hz
    obtain ⟨i, -, rfl⟩ := Finset.mem_image.mp hw
    exact Set.mem_iUnion.mpr ⟨i, hzw⟩
  · intro hz
    obtain ⟨i, hzi⟩ := Set.mem_iUnion.mp hz
    exact Set.mem_iUnion₂.mpr ⟨u i, Finset.mem_image.mpr ⟨i, Finset.mem_univ i, rfl⟩, hzi⟩

/-- The `Finset`-form and `Fin`-form of the union of *closed* balls agree. -/
private theorem cfl_iUnion_image_closedBall {n : ℕ} (u : Fin (n + 1) → ℂ) (r : ℝ) :
    (⋃ w ∈ (Finset.univ.image u : Finset ℂ), Metric.closedBall w r)
      = ⋃ i : Fin (n + 1), Metric.closedBall (u i) r := by
  ext z
  constructor
  · intro hz
    obtain ⟨w, hw, hzw⟩ := Set.mem_iUnion₂.mp hz
    obtain ⟨i, -, rfl⟩ := Finset.mem_image.mp hw
    exact Set.mem_iUnion.mpr ⟨i, hzw⟩
  · intro hz
    obtain ⟨i, hzi⟩ := Set.mem_iUnion.mp hz
    exact Set.mem_iUnion₂.mpr ⟨u i, Finset.mem_image.mpr ⟨i, Finset.mem_univ i, rfl⟩, hzi⟩

/-- `0` lies in the interior of a finite union of equal closed balls one of whose open balls
contains it. -/
private theorem cfl_mem_interior_iUnion {n : ℕ} {u : Fin (n + 1) → ℂ} {r : ℝ}
    (h0 : (0 : ℂ) ∈ ⋃ i, Metric.ball (u i) r) :
    (0 : ℂ) ∈ interior (⋃ i, Metric.closedBall (u i) r) := by
  obtain ⟨k, hk⟩ := Set.mem_iUnion.mp h0
  exact interior_mono (fun z hz => Set.mem_iUnion.mpr ⟨k, hz⟩)
    (Metric.ball_subset_interior_closedBall hk)

/-- `0` is not on the frontier of a finite union of equal closed balls one of whose open balls
contains it. -/
private theorem cfl_zero_notMem_frontier {n : ℕ} {u : Fin (n + 1) → ℂ} {r : ℝ}
    (h0 : (0 : ℂ) ∈ ⋃ i, Metric.ball (u i) r) :
    (0 : ℂ) ∉ frontier (⋃ i, Metric.closedBall (u i) r) := by
  intro hmem
  rw [frontier, Set.mem_sdiff] at hmem
  exact hmem.2 (cfl_mem_interior_iUnion h0)

/-- A Jordan curve lying in the frontier of a finite union of equal closed balls, one of whose open
balls contains the origin, yields a frontier loop of index `1`. -/
private theorem cfl_of_jordan {n : ℕ} {u : Fin (n + 1) → ℂ} {r : ℝ}
    (h0 : (0 : ℂ) ∈ ⋃ i, Metric.ball (u i) r)
    {γ : ℝ → ℂ} (hγ : Continuous γ) (hper : Function.Periodic γ (2 * Real.pi))
    (hinj : Set.InjOn γ (Set.Ico 0 (2 * Real.pi)))
    (hrange : Set.range γ ⊆ frontier (⋃ i, Metric.closedBall (u i) r))
    (hbdd : Bornology.IsBounded (connectedComponentIn (Set.range γ)ᶜ (0 : ℂ))) :
    ∃ c : C(unitInterval, ℂ), (∀ t, c t ∈ frontier (⋃ i, Metric.closedBall (u i) r)) ∧
      c 0 = c 1 ∧ Work.Smooth.SphereJordan.loopIndex c = 1 := by
  have h0not : (0 : ℂ) ∉ Set.range γ := by
    rintro ⟨t, ht⟩
    exact cfl_zero_notMem_frontier h0 (hrange ⟨t, ht⟩)
  obtain ⟨c, hcrange, hcloop, hidx⟩ := jordanLoopIndexOne hγ hper hinj h0not hbdd
  exact ⟨c, fun t => hrange (hcrange t), hcloop, hidx⟩

theorem chainFrontierLoop {n : ℕ} {u : Fin (n + 1) → ℂ} {r : ℝ} (hr : 0 < r)
    (hstep : ∀ i : Fin n, dist (u i.castSucc) (u i.succ) ≤ 2 * r)
    (h0 : (0 : ℂ) ∈ ⋃ i, Metric.ball (u i) r) :
    ∃ c : C(unitInterval, ℂ), (∀ t, c t ∈ frontier (⋃ i, Metric.closedBall (u i) r)) ∧
      c 0 = c 1 ∧ Work.Smooth.SphereJordan.loopIndex c = 1 := by
  set P : Finset ℂ := Finset.univ.image u with hP
  have hclosed : (⋃ w ∈ P, Metric.closedBall w r) = ⋃ i, Metric.closedBall (u i) r := by
    rw [hP]; exact cfl_iUnion_image_closedBall u r
  have hopen : (⋃ w ∈ P, Metric.ball w r) = ⋃ i, Metric.ball (u i) r := by
    rw [hP]; exact cfl_iUnion_image_openBall u r
  have h0' : (0 : ℂ) ∈ ⋃ w ∈ P, Metric.ball w r := by rw [hopen]; exact h0
  obtain ⟨γ, hγc, hγper, hγinj, hγrange, hγbdd⟩ := frontierCurveOfOpenBallUnionAux P hr h0'
  refine cfl_of_jordan h0 hγc hγper hγinj ?_ hγbdd
  intro z hz
  rw [← hclosed]
  exact hγrange hz

end

end Work.Smooth.SphereJordan
