import Mathlib
import Submission.Work.Drive.Mono.eventValue_mem_exc

/-!
# The levels of the events lie in the window

`GoodDataPackage3` carries `TiltData`, which puts the exceptional set `exc` strictly inside the window
(`∀ t ∈ exc, lam0 < t ∧ t < lam1`), and `Work.Drive.Mono.eventValue_mem_exc` shows that the level of
every event of the three types lies in `exc`.  Hence the level of every event lies strictly inside the
window — the hypothesis `hwin` of `Work.Drive.Final.noJumpAtAnyEventCond_of_eventTraceData`, and the
step that produces the "non-exceptional level above the event level" used in the no-jump argument at
an event level.
-/

open LeanEval.KnotTheory.PardonDistortion Set

namespace Work.Drive.Mono

noncomputable section

/-- **The level of an event lies strictly inside the window.** -/
theorem eventValue_mem_window
    {ψ : Submission.Diffeo} {K : LeanEval.KnotTheory.PardonDistortion.Knot} {s u : ℝ}
    {c : LeanEval.KnotTheory.PardonDistortion.R3} {σ : Equiv.Perm (Fin 3)}
    {v : LeanEval.KnotTheory.PardonDistortion.R3} {h R : ℝ}
    {ℓ : LeanEval.KnotTheory.PardonDistortion.R3 →L[ℝ] ℝ} {exc : Finset ℝ} {lam0 lam1 : ℝ}
    {p q : ℕ}
    (hDP : Work.Drive.Mono.GoodDataPackage3 ψ K s u c σ v h R ℓ exc lam0 lam1 p q)
    {pp : ℝ × ℝ} (hev : Work.Drive.Final.IsAnyEvent ψ s c σ u v h ℓ pp) :
    ℓ (Work.BoxShrink.Pinch.par ψ pp) ∈ Set.Icc lam0 lam1 := by
  obtain ⟨-, -, -, -, -, -, -, -, -, _, hexc⟩ := hDP.1.tilt
  have hmem : ℓ (Work.BoxShrink.Pinch.par ψ pp) ∈ (exc : Set ℝ) :=
    eventValue_mem_exc hDP hev
  obtain ⟨h1, h2⟩ := hexc _ hmem
  exact ⟨le_of_lt h1, le_of_lt h2⟩

/-- **The level of an event is strictly below the top of the window.** -/
theorem eventValue_lt_lam1
    {ψ : Submission.Diffeo} {K : LeanEval.KnotTheory.PardonDistortion.Knot} {s u : ℝ}
    {c : LeanEval.KnotTheory.PardonDistortion.R3} {σ : Equiv.Perm (Fin 3)}
    {v : LeanEval.KnotTheory.PardonDistortion.R3} {h R : ℝ}
    {ℓ : LeanEval.KnotTheory.PardonDistortion.R3 →L[ℝ] ℝ} {exc : Finset ℝ} {lam0 lam1 : ℝ}
    {p q : ℕ}
    (hDP : Work.Drive.Mono.GoodDataPackage3 ψ K s u c σ v h R ℓ exc lam0 lam1 p q)
    {pp : ℝ × ℝ} (hev : Work.Drive.Final.IsAnyEvent ψ s c σ u v h ℓ pp) :
    ℓ (Work.BoxShrink.Pinch.par ψ pp) < lam1 := by
  obtain ⟨-, -, -, -, -, -, -, -, -, -, hexc⟩ := hDP.1.tilt
  exact (hexc _ (eventValue_mem_exc hDP hev)).2

/-- **The level of an event is strictly above the bottom of the window.** -/
theorem lam0_lt_eventValue
    {ψ : Submission.Diffeo} {K : LeanEval.KnotTheory.PardonDistortion.Knot} {s u : ℝ}
    {c : LeanEval.KnotTheory.PardonDistortion.R3} {σ : Equiv.Perm (Fin 3)}
    {v : LeanEval.KnotTheory.PardonDistortion.R3} {h R : ℝ}
    {ℓ : LeanEval.KnotTheory.PardonDistortion.R3 →L[ℝ] ℝ} {exc : Finset ℝ} {lam0 lam1 : ℝ}
    {p q : ℕ}
    (hDP : Work.Drive.Mono.GoodDataPackage3 ψ K s u c σ v h R ℓ exc lam0 lam1 p q)
    {pp : ℝ × ℝ} (hev : Work.Drive.Final.IsAnyEvent ψ s c σ u v h ℓ pp) :
    lam0 < ℓ (Work.BoxShrink.Pinch.par ψ pp) := by
  obtain ⟨-, -, -, -, -, -, -, -, -, -, hexc⟩ := hDP.1.tilt
  exact (hexc _ (eventValue_mem_exc hDP hev)).1

end

end Work.Drive.Mono
