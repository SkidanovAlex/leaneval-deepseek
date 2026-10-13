import Mathlib.Analysis.InnerProductSpace.PiL2
import Submission.Work.SolutionDelivery.Defs
import Submission.Work.SolutionDelivery.Sup.exists_notMem_closedBall_R3
import Submission.Work.SolutionDelivery.Sup.bddAbove_range_ciSup_mem

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

namespace Work.SolutionDelivery.Sup

open Set Metric
open scoped Topology

/-- **The supremum over a closed ball of a jointly continuous family is continuous in the
time parameter.**

If `p ↦ F p.1 p.2` is continuous on `closedBall 0 R ×ˢ Icc a b`, then
`t ↦ ⨆ x ∈ closedBall 0 R, F x t` is continuous on `Icc a b`.

The closed ball is compact (finite-dimensionality of `ℝ³`), so `F` is uniformly continuous on
`closedBall 0 R ×ˢ Icc a b`; around each `t₀` this yields both bounds
`(⨆ x ∈ K, F x t) ≤ (⨆ x ∈ K, F x t₀) + ε` and `(⨆ x ∈ K, F x t₀) ≤ (⨆ x ∈ K, F x t) + ε`.
The `⨆ x ∈ K, ·` notation is the *nested* binder `⨆ x, ⨆ (_ : x ∈ K), ·`: points `x ∉ K`
contribute the junk value `sSup ∅ = 0`, which is where `hR` (so that `K` is a proper subset of
`ℝ³`) enters. -/
theorem continuousOn_ciSup_closedBall {F : Work.SolutionDelivery.R3 → ℝ → ℝ} {R a b : ℝ} (hR : 0 ≤ R)
    (hcont : ContinuousOn (fun p : Work.SolutionDelivery.R3 × ℝ => F p.1 p.2)
      (Metric.closedBall 0 R ×ˢ Set.Icc a b)) :
    ContinuousOn (fun t => ⨆ x ∈ Metric.closedBall 0 R, F x t) (Set.Icc a b) := by
  classical
  let K : Set Work.SolutionDelivery.R3 := Metric.closedBall 0 R
  let I : Set ℝ := Set.Icc a b
  change ContinuousOn (fun t => ⨆ x ∈ K, F x t) I
  have hKc : IsCompact K := isCompact_closedBall 0 R
  have hIc : IsCompact I := isCompact_Icc
  have hcont' : ContinuousOn (fun p : Work.SolutionDelivery.R3 × ℝ => F p.1 p.2) (K ×ˢ I) := hcont
  -- `K` is non-empty since `0 ∈ closedBall 0 R`.
  have hKne : K.Nonempty := by
    refine ⟨0, ?_⟩
    change (0 : Work.SolutionDelivery.R3) ∈ Metric.closedBall 0 R
    rw [Metric.mem_closedBall, dist_self]
    exact hR
  -- the spatial slice `x ↦ F x t` is continuous on `K`.
  have hslice : ∀ t ∈ I, ContinuousOn (fun x : Work.SolutionDelivery.R3 => F x t) K := by
    intro t ht
    have hmap : Set.MapsTo (fun x : Work.SolutionDelivery.R3 => (x, t)) K (K ×ˢ I) :=
      fun x hx => ⟨hx, ht⟩
    have hc : ContinuousOn (fun x : Work.SolutionDelivery.R3 => (x, t)) K :=
      (Continuous.prodMk_left t).continuousOn
    have h := hcont'.comp hc hmap
    simpa only [Function.comp_def] using h
  -- the extended family `x ↦ ⨆ (_ : x ∈ K), F x t` is bounded above.
  have hBdd : ∀ t ∈ I,
      BddAbove (Set.range (fun x : Work.SolutionDelivery.R3 => ⨆ (_ : x ∈ K), F x t)) := by
    intro t ht
    exact bddAbove_range_ciSup_mem hKc (hslice t ht)
  -- a point of `ℝ³` outside `K`; it contributes the junk value `0` to the supremum.
  obtain ⟨x1, hx1⟩ : ∃ x : Work.SolutionDelivery.R3, x ∉ K := by
    obtain ⟨x, hx⟩ := exists_notMem_closedBall_R3 R
    exact ⟨x, hx⟩
  have hg_nonneg : ∀ s ∈ I, 0 ≤ (⨆ x, ⨆ (_ : x ∈ K), F x s) := by
    intro s hs
    have hle := le_ciSup (hBdd s hs) x1
    change (⨆ (_ : x1 ∈ K), F x1 s) ≤ (⨆ x, ⨆ (_ : x ∈ K), F x s) at hle
    rw [ciSup_eq_ite, Real.sSup_empty, dite_eq_right hx1] at hle
    exact hle
  rw [Metric.continuousOn_iff]
  intro t0 ht0 ε hε
  have hε2 : (0:ℝ) < ε / 2 := by linarith
  have hu := Metric.uniformContinuousOn_iff.mp
    ((hKc.prod hIc).uniformContinuousOn_of_continuous hcont')
  obtain ⟨δ, hδpos, hδ⟩ := hu (ε/2) hε2
  refine ⟨δ, hδpos, ?_⟩
  intro t ht hdist
  have hdxy : ∀ x : Work.SolutionDelivery.R3,
      dist ((x, t) : Work.SolutionDelivery.R3 × ℝ) (x, t0) < δ := by
    intro x
    rw [Prod.dist_eq, max_lt_iff]
    exact ⟨by rw [dist_self]; exact hδpos, hdist⟩
  -- uniform control of one slice against the other
  have hclose : ∀ x : Work.SolutionDelivery.R3, x ∈ K → |F x t - F x t0| < ε / 2 := by
    intro x hx
    have h := hδ (x, t) ⟨hx, ht⟩ (x, t0) ⟨hx, ht0⟩ (hdxy x)
    simpa only [Real.dist_eq] using h
  have hupper : (⨆ x, ⨆ (_ : x ∈ K), F x t) ≤ (⨆ x, ⨆ (_ : x ∈ K), F x t0) + ε/2 := by
    refine ciSup_le (fun x => ?_)
    change (⨆ (_ : x ∈ K), F x t) ≤ (⨆ x, ⨆ (_ : x ∈ K), F x t0) + ε/2
    rw [ciSup_eq_ite, Real.sSup_empty]
    by_cases hx : x ∈ K
    · rw [dite_eq_left hx]
      have hle : F x t0 ≤ (⨆ x, ⨆ (_ : x ∈ K), F x t0) := by
        have h := le_ciSup (hBdd t0 ht0) x
        change (⨆ (_ : x ∈ K), F x t0) ≤ _ at h
        rw [ciSup_eq_ite, Real.sSup_empty, dite_eq_left hx] at h
        exact h
      have hlt : F x t - F x t0 < ε/2 := (abs_lt.mp (hclose x hx)).2
      linarith
    · rw [dite_eq_right hx]
      linarith [hg_nonneg t0 ht0]
  have hlower : (⨆ x, ⨆ (_ : x ∈ K), F x t0) ≤ (⨆ x, ⨆ (_ : x ∈ K), F x t) + ε/2 := by
    refine ciSup_le (fun x => ?_)
    change (⨆ (_ : x ∈ K), F x t0) ≤ (⨆ x, ⨆ (_ : x ∈ K), F x t) + ε/2
    rw [ciSup_eq_ite, Real.sSup_empty]
    by_cases hx : x ∈ K
    · rw [dite_eq_left hx]
      have hle : F x t ≤ (⨆ x, ⨆ (_ : x ∈ K), F x t) := by
        have h := le_ciSup (hBdd t ht) x
        change (⨆ (_ : x ∈ K), F x t) ≤ _ at h
        rw [ciSup_eq_ite, Real.sSup_empty, dite_eq_left hx] at h
        exact h
      have hlt : -(ε/2) < F x t - F x t0 := (abs_lt.mp (hclose x hx)).1
      linarith
    · rw [dite_eq_right hx]
      linarith [hg_nonneg t ht]
  rw [Real.dist_eq]
  change |(⨆ x, ⨆ (_ : x ∈ K), F x t) - (⨆ x, ⨆ (_ : x ∈ K), F x t0)| < ε
  have h1 : (⨆ x, ⨆ (_ : x ∈ K), F x t) - (⨆ x, ⨆ (_ : x ∈ K), F x t0) ≤ ε/2 := by linarith
  have h2 : (⨆ x, ⨆ (_ : x ∈ K), F x t0) - (⨆ x, ⨆ (_ : x ∈ K), F x t) ≤ ε/2 := by linarith
  have h3 := abs_sub_le_iff.mpr ⟨h1, h2⟩
  linarith

end Work.SolutionDelivery.Sup
