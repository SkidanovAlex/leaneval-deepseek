import Mathlib
import Submission.Work.Drive.Mono.SweepGeom3
import Submission.Work.Drive.Mono.Split
import Submission.Work.Drive.Mono.DichotomyB
import Submission.Work.Drive.Final.AnyEventDefs
import Submission.Work.Drive.Mono.wallSideDefs
import Submission.Work.Drive.Mono.noJumpBelowAt_of_noEventAt
import Submission.Work.Drive.Mono.existsUnique_top_of_two_pieces_of_frontier

/-!
# The wall dichotomy at a level carrying no event

This module isolates `Work.Drive.Mono.wallSide_dichotomy_of_noEvent` (the dichotomy of Pardon at a
level of the window which carries *no* event of the sweep, in the form in which the far side of the
wall need not be carrier-open) from
`Submission/Work/Drive/Mono/noJumpBelowAt_of_anyEventAt.lean`, so that the no-jump at event levels
(`Submission/Work/Drive/Mono/wallSide_ne_bot_of_sweep_bot.lean`) can use it without importing the
target module.
-/

open LeanEval.KnotTheory.PardonDistortion Set

namespace Work.Drive.Mono

noncomputable section

/-- **The wall dichotomy at a level carrying no event**, in the form consumed here: exactly one of
the region and the far side of the wall of the level carries the full winding span. -/
theorem wallSide_dichotomy_of_noEvent
    (p q : ℕ) (hp : 0 < p) (hq : 0 < q) (hc : Nat.Coprime p q)
    (ψ : Submission.Diffeo) (K : Knot)
    (himg : Set.range K.curve = Set.range
      (Work.CoreTopology.ClosedCurve.mapHomeomorph ψ.toHomeomorph
        (Work.CoreTopology.standardCurve p q)).γ)
    (hcl : Work.Drive.CleansDiscsWd (Work.Drive.EpsSphere.torusOf ψ))
    {s u : ℝ} {c : R3} {σ : Equiv.Perm (Fin 3)} {v : R3} {h R : ℝ} {ℓ : R3 →L[ℝ] ℝ}
    {exc : Finset ℝ} {lam0 lam1 : ℝ}
    (hDP : GoodDataPackage3 ψ K s u c σ v h R ℓ exc lam0 lam1 p q)
    {ν : ℝ} (hν : ν ∈ Set.Icc lam0 lam1)
    (hnoev : ¬ ∃ pp : ℝ × ℝ, Work.Drive.Final.IsAnyEvent ψ s c σ u v h ℓ pp ∧
      ℓ (Work.BoxShrink.Pinch.par ψ pp) = ν) :
    (Work.SurgeryInvariance.WindingSpan (Work.Drive.EpsSphere.torusOf ψ)
        (Work.Drive.Final.sweep (Work.Drive.EpsSphere.torusOf ψ) s c σ u v h ℓ ν) = ⊤ ∧
      Work.SurgeryInvariance.WindingSpan (Work.Drive.EpsSphere.torusOf ψ)
        (wallSide (Work.Drive.EpsSphere.torusOf ψ) s c σ u v h ℓ ν) = ⊥) ∨
    (Work.SurgeryInvariance.WindingSpan (Work.Drive.EpsSphere.torusOf ψ)
        (Work.Drive.Final.sweep (Work.Drive.EpsSphere.torusOf ψ) s c σ u v h ℓ ν) = ⊥ ∧
      Work.SurgeryInvariance.WindingSpan (Work.Drive.EpsSphere.torusOf ψ)
        (wallSide (Work.Drive.EpsSphere.torusOf ψ) s c σ u v h ℓ ν) = ⊤) := by
  obtain ⟨n, cs, hsimple, hess, hdisj, hunion⟩ :=
    traceCurvesAt_of_noEventAt_aux p q hp hq hc ψ K himg hcl hDP hν hnoev
  obtain ⟨-, hv1, hℓne, hℓv, -⟩ := hDP.1.tilt
  have hv : v ≠ 0 := by
    intro h0
    rw [h0, norm_zero] at hv1
    exact one_ne_zero hv1.symm
  have hcarrier : Work.Drive.Final.sweep (Work.Drive.EpsSphere.torusOf ψ) s c σ u v h ℓ ν ⊆
      (Work.Drive.EpsSphere.torusOf ψ).carrier := by
    intro y hy
    exact (Work.Drive.Mono.mem_openTiltedSweepRegion_iff.mp hy).1
  refine existsUnique_top_of_two_pieces_of_frontier (P := Work.Drive.EpsSphere.torusOf ψ)
    (X := Work.Drive.Final.sweep (Work.Drive.EpsSphere.torusOf ψ) s c σ u v h ℓ ν)
    (Y := wallSide (Work.Drive.EpsSphere.torusOf ψ) s c σ u v h ℓ ν) hsimple hess hdisj
    hcarrier ?_ Work.Drive.EpsFormSphere.isOpenInCarrier_openTiltedSweepRegion ?_ ?_ ?_
  · exact fun y hy => hy.1
  · -- disjointness: the far side is the complement of the region and the wall
    rw [Set.disjoint_left]
    rintro y hy hy'
    exact hy'.2 (Or.inl hy)
  · -- the cover clause, by construction
    rw [hunion]
    exact carrier_sdiff_wall_eq_union (Work.Drive.EpsSphere.torusOf ψ) s c σ u v h ℓ ν
  · -- the frontier clause: a surface point in the closure of the region but off it is on the wall
    intro z hzc hzcl hznx
    rw [hunion]
    exact ⟨hzc, (mem_frontier_removed_of_mem_closure (P := Work.Drive.EpsSphere.torusOf ψ)
      hv hℓv hℓne hzc hzcl hznx).2⟩




end

end Work.Drive.Mono
