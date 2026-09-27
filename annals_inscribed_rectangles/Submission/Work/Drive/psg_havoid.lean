import Mathlib
import Submission.Work.Drive.psgFamilyDefs
import Submission.Work.Drive.germHavoidLoop

/-!
# The `havoid` clause of the parity family on the five-box for the `psg` deformation

`Work.Drive.psgLoopFam` / `Work.Drive.psgChainFam` (`Submission/Work/Drive/psgFamilyDefs.lean`) are
the two sides of the L6 family of the germ route along the ramped path from `A` to `B` (of
configurations) and the ramped path from `tA` to `tB` (of angles): the loop side is
`p ↦ Ξ (psgPathL s + τ₁) (coreLoop Q (p 1))` and the chain side is the clamped sweep of the rotated
perturbed sweep chart at the angle `psgAngleClass tA tB s`.

This file discharges the **`havoid` clause** of that family — the statement that a meet of the two
sides cannot occur on the last face `p 4 ∈ {0,1}` of the five-box, i.e. at the level `c` or at the
plane of the sweep:

* `Work.Drive.psg_havoid` — the clause, from the *pointwise-in-the-parameter* `havoid` input `hav`
  (a two-chart statement for every perturbation `a` of norm `< ε₀` and every angle within `δ₀` of `w`)
  plus the two uniformity hypotheses `hconf` (the ramped chart perturbation stays small) and `hang`
  (the ramped angle stays close to `w`).

The proof is a straight instantiation: `p ∈ unitBox 4` gives `u := (p 0, p 1) ∈ unitBox 1` and
`x := (p 2, p 3, p 4) ∈ unitBox 2`, the ramped paths at `s = p 0` supply the two hypotheses of `hav`
(`hconf (p 0)`, `hang (p 0)`), and the equality of the two sides of the family at `p` is
*definitionally* the equality of `hav` at that data (`psgQFam`/`psgPFam` are the perturbed charts and
`famPt`/`famT3` only reindex the chain parameters).
-/

namespace Work.Drive

theorem psg_havoid {m : ℕ}
    (Ξ : EuclideanSpace ℝ (Fin m) → Work.Drive.CappingSpace → Work.Drive.CappingSpace)
    (Q : ℂ → Work.Drive.CappingSpace) (c : ℝ)
    (A B : EuclideanSpace ℝ (Fin m) × EuclideanSpace ℝ (Fin m))
    (w : UnitAddCircle) (tA tB : ℝ) (τ₁ τ₂ : EuclideanSpace ℝ (Fin m)) {ε₀ δ₀ : ℝ}
    (hav : ∀ (a : EuclideanSpace ℝ (Fin m) × EuclideanSpace ℝ (Fin m)) (w' : UnitAddCircle),
      ‖a‖ < ε₀ → dist w' w < δ₀ →
      ∀ (u : EuclideanSpace ℝ (Fin 2)) (x : EuclideanSpace ℝ (Fin 3)),
        u ∈ Submission.Drive.unitBox 1 → x ∈ Submission.Drive.unitBox 2 →
        Work.Drive.coreLoop (Work.Drive.pertChart Ξ Q a.1) (u 1)
          = Work.Drive.clampedSweep c (fun t => 1 - t)
              (Work.Drive.rotPresentation (Work.Drive.pertChart Ξ Q a.2) w') x →
        (x 2 = 0 ∨ x 2 = 1) → False)
    (hconf : ∀ s : ℝ, ‖(Work.Drive.psgPathL A B s + τ₁, Work.Drive.psgPathR A B s + τ₂)‖ < ε₀)
    (hang : ∀ s : ℝ, dist (Work.Drive.psgAngleClass tA tB s) w < δ₀) :
    ∀ p ∈ Submission.Drive.unitBox 4,
      Work.Drive.famLoop (Work.Drive.psgLoopFam Ξ Q A B τ₁) p
        = Work.Drive.famChain (Work.Drive.psgChainFam Ξ Q c A B tA tB τ₂) p →
      (p 4 = 0 ∨ p 4 = 1) → False := by
  intro p hp heq hface
  -- the two box memberships of the `hav` data, read off the five-box coordinate bounds
  have hu : Work.Drive.mk2 (p 0) (p 1) ∈ Submission.Drive.unitBox 1 := by
    intro i
    fin_cases i
    · simpa using hp 0
    · simpa using hp 1
  have hx : Work.Drive.famT3 (p 2) (p 3) (p 4) ∈ Submission.Drive.unitBox 2 := by
    intro i
    fin_cases i
    · simpa using hp 2
    · simpa using hp 3
    · simpa using hp 4
  -- the two sides of the family are, definitionally, `hav`'s two sides at the ramped data
  have hL : Work.Drive.famLoop (Work.Drive.psgLoopFam Ξ Q A B τ₁) p
      = Work.Drive.coreLoop (Work.Drive.pertChart Ξ Q (Work.Drive.psgPathL A B (p 0) + τ₁))
          (Work.Drive.mk2 (p 0) (p 1) 1) := by
    simp only [Work.Drive.famLoop, Work.Drive.psgLoopFam, Work.Drive.chartLoopFam,
      Work.Drive.mk2_apply_zero, Work.Drive.mk2_apply_one]
    congr 1
  have hC : Work.Drive.famChain (Work.Drive.psgChainFam Ξ Q c A B tA tB τ₂) p
      = Work.Drive.clampedSweep c (fun t => 1 - t)
          (Work.Drive.rotPresentation (Work.Drive.pertChart Ξ Q
            (Work.Drive.psgPathR A B (p 0) + τ₂))
            (Work.Drive.psgAngleClass tA tB (p 0)))
          (Work.Drive.famT3 (p 2) (p 3) (p 4)) := by
    simp only [Work.Drive.famChain, Work.Drive.psgChainFam, Work.Drive.sweepFam,
      Work.Drive.famPt_apply_zero]
    congr 1
  have heq' : Work.Drive.coreLoop (Work.Drive.pertChart Ξ Q (Work.Drive.psgPathL A B (p 0) + τ₁))
        (Work.Drive.mk2 (p 0) (p 1) 1)
      = Work.Drive.clampedSweep c (fun t => 1 - t)
          (Work.Drive.rotPresentation (Work.Drive.pertChart Ξ Q
            (Work.Drive.psgPathR A B (p 0) + τ₂))
            (Work.Drive.psgAngleClass tA tB (p 0)))
          (Work.Drive.famT3 (p 2) (p 3) (p 4)) := by
    rw [← hL, ← hC]
    exact heq
  -- the face hypothesis is the `x 2 ∈ {0,1}` hypothesis of `hav`
  have hface' : Work.Drive.famT3 (p 2) (p 3) (p 4) 2 = 0
      ∨ Work.Drive.famT3 (p 2) (p 3) (p 4) 2 = 1 := by
    simpa only [Work.Drive.famT3_apply_two] using hface
  exact hav (Work.Drive.psgPathL A B (p 0) + τ₁, Work.Drive.psgPathR A B (p 0) + τ₂)
    (Work.Drive.psgAngleClass tA tB (p 0)) (hconf (p 0)) (hang (p 0))
    (Work.Drive.mk2 (p 0) (p 1)) (Work.Drive.famT3 (p 2) (p 3) (p 4))
    hu hx heq' hface'

end Work.Drive
