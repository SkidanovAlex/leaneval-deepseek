/-
# GATE2 — `CaseIILeak` from the lifted equipotential arc

`Work.GATE2.CaseIILeak` (`Dichotomy2.lean`) is the single residual of the area.  This module
reduces it to **arc-level data**: for a continuous curve `A : C(I, ℂ)` of the `Ψ`-plane running
from a deep real leak point `x*` to the lift `γ₁ s₁`, deep (`Re < -3/2`) along the whole curve, off
`K` (for `A` and for its shifts `A - 1`, `star A + 1/2`, `star (A-1) + 1/2`), in the `1/16384`
window for the two angles `α₁` and `α₂` (on those four legs), and above the `3/4`-floor, one gets
`CaseIILeak c fl.Ψ`.

The proof chains the four reductions built in this area:

* `EXL.lastReal_of_arc` — replace `A` by its terminal segment `B` starting at the **last real
  point** `(x₀ : ℂ)` of `A`, which is what makes the offset-avoidance (W) hold;
* `EXL.exitLoop_of_arcSegment` — the loop `(B − 1) ⋆ γ₁|[s₁−1, s₁] ⋆ (B reversed)` is an `α₁` exit
  loop at `x₀`;
* `EXL.exitLoop_iota_of_arcSegment` — its conjugate is an `α₂` exit loop at `x₀ + 1/2`;
* `deepLeak_of_leak` — `x₀` is a deep real leak point.

Every hypothesis about `A − 1`, `star A + 1/2`, `star (A − 1) + 1/2` is in fact **automatic** on an
equipotential arc: `G (Ψ (w - 1)) = G (Ψ w)/1024` (the potential is constant along `A`) and
`Ψ (star w + 1/2) = g (Ψ w)` with `K c` totally invariant, so the off-`K` conditions of the shifted
legs follow from those of `A`.  They are kept explicit here so that the reduction to the arc is
mechanical.
-/
import Submission.Work.GATE2.Dichotomy2
import Submission.Work.GATE2.EXL.LastReal
import Submission.Work.GATE2.EXL.exitLoop_of_arcSegment
import Submission.Work.GATE2.EXL.exitLoop_iota_of_arcSegment

-- Lean v4.35.0-rc3 / Mathlib 5e0c4e5 made `isDefEq` respect transparency when unifying instances; with it,
-- `ZMod.instField` and `ZMod.commRing` (and `Neg (ZMod p)` via `SubtractionMonoid`) no longer unify, which
-- breaks `ring`/`rw`/module-instance search on `ZMod p`. Restore the v4.34 behaviour for this file.
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false


open Classical Filter Set Metric
open scoped Topology

set_option autoImplicit false
set_option linter.unusedVariables false

noncomputable section

namespace Work.GATE2

open LeanEval.ComplexAnalysis (Mandelbar Tantibar)

/-- **`CaseIILeak` from the lifted equipotential arc.** -/
theorem caseIILeak_of_arc {c : ℂ} {d : Work.EL.RootParabolic c}
    (fl : Work.EL.ParabolicFlower (Work.EL.F c) ((Tantibar c)^[5]) d.z₁)
    (Lray : Work.ELRig.RayCylLift d fl)
    {x₀ s₁ : ℝ} (A : C(unitInterval, ℂ))
    (hA0 : A 0 = ((x₀ : ℝ) : ℂ)) (hA1 : A 1 = Lray.γ₁ s₁)
    (hAre : ∀ r : unitInterval, (A r).re < -(3 / 2 : ℝ))
    (hγim : ∀ s : ℝ, (Lray.γ₁ s).im ≠ 0)
    (hγre : ∀ u ∈ Set.Icc (0 : ℝ) 1, (Lray.γ₁ (s₁ - 1 + u)).re < -(3 / 2 : ℝ))
    (hK : ∀ r : unitInterval, fl.Ψ (A r) ∉ Work.EL.K c)
    (hK1 : ∀ r : unitInterval, fl.Ψ (A r - 1) ∉ Work.EL.K c)
    (hK2 : ∀ r : unitInterval, fl.Ψ (star (A r) + 1 / 2) ∉ Work.EL.K c)
    (hK3 : ∀ r : unitInterval, fl.Ψ (star (A r - 1) + 1 / 2) ∉ Work.EL.K c)
    (hKγ₂ : ∀ u ∈ Set.Icc (0 : ℝ) 1, fl.Ψ (Lray.γ₂ (s₁ - 1 + u)) ∉ Work.EL.K c)
    (hdev : ∀ r : unitInterval,
      |Work.GATE.deviation (Work.Bottcher.varphiCrit c) Work.EL.alpha1 (fl.Ψ (A r))| < 1 / 16384)
    (hdev1 : ∀ r : unitInterval,
      |Work.GATE.deviation (Work.Bottcher.varphiCrit c) Work.EL.alpha1 (fl.Ψ (A r - 1))| <
        1 / 16384)
    (hdev2 : ∀ r : unitInterval,
      |Work.GATE.deviation (Work.Bottcher.varphiCrit c) Work.EL.alpha2
        (fl.Ψ (star (A r) + 1 / 2))| < 1 / 16384)
    (hdev3 : ∀ r : unitInterval,
      |Work.GATE.deviation (Work.Bottcher.varphiCrit c) Work.EL.alpha2
        (fl.Ψ (star (A r - 1) + 1 / 2))| < 1 / 16384)
    (hdevγ₂ : ∀ u ∈ Set.Icc (0 : ℝ) 1,
      |Work.GATE.deviation (Work.Bottcher.varphiCrit c) Work.EL.alpha2
        (fl.Ψ (Lray.γ₂ (s₁ - 1 + u)))| < 1 / 16384)
    (hfloor1 : ∀ r₁ r₂ : unitInterval,
      (3 / 4 : ℝ) * Work.Bottcher.green c (fl.Ψ (A r₁ - 1)) <
        Work.Bottcher.green c (fl.Ψ (A r₂ - 1)))
    (hfloor2 : ∀ r₁ r₂ : unitInterval,
      (3 / 4 : ℝ) * Work.Bottcher.green c (fl.Ψ (A r₁ - 1)) <
        Work.Bottcher.green c (fl.Ψ (A r₂)))
    (hfloorγ₁ : ∀ (r₁ : unitInterval) (u : ℝ), u ∈ Set.Icc (0 : ℝ) 1 →
      (3 / 4 : ℝ) * Work.Bottcher.green c (fl.Ψ (A r₁ - 1)) <
        Work.Bottcher.green c (fl.Ψ (Lray.γ₁ (s₁ - 1 + u))))
    (hfloorι1 : ∀ r₁ r₂ : unitInterval,
      (3 / 4 : ℝ) * Work.Bottcher.green c (fl.Ψ (star (A r₁ - 1) + 1 / 2)) <
        Work.Bottcher.green c (fl.Ψ (star (A r₂ - 1) + 1 / 2)))
    (hfloorι2 : ∀ r₁ r₂ : unitInterval,
      (3 / 4 : ℝ) * Work.Bottcher.green c (fl.Ψ (star (A r₁ - 1) + 1 / 2)) <
        Work.Bottcher.green c (fl.Ψ (star (A r₂) + 1 / 2)))
    (hfloorγ₂ : ∀ (r₁ : unitInterval) (u : ℝ), u ∈ Set.Icc (0 : ℝ) 1 →
      (3 / 4 : ℝ) * Work.Bottcher.green c (fl.Ψ (star (A r₁ - 1) + 1 / 2)) <
        Work.Bottcher.green c (fl.Ψ (Lray.γ₂ (s₁ - 1 + u)))) :
    CaseIILeak c fl.Ψ := by
  have hA0im : (A 0).im = 0 := by rw [hA0]; simp
  have hA1im : (A 1).im ≠ 0 := by rw [hA1]; exact hγim s₁
  obtain ⟨x, B, hB0, hB1, hsgnB, hrange⟩ := Work.GATE2.EXL.lastReal_of_arc hA0im hA1im
  -- transfer every hypothesis from `A` to the terminal segment `B`
  have hBre : ∀ t : unitInterval, (B t).re < -(3 / 2 : ℝ) := by
    intro t; obtain ⟨t', ht'⟩ := hrange t; rw [ht']; exact hAre t'
  have hKB : ∀ t : unitInterval, fl.Ψ (B t) ∉ Work.EL.K c := by
    intro t; obtain ⟨t', ht'⟩ := hrange t; rw [ht']; exact hK t'
  have hK1B : ∀ t : unitInterval, fl.Ψ (B t - 1) ∉ Work.EL.K c := by
    intro t; obtain ⟨t', ht'⟩ := hrange t; rw [ht']; exact hK1 t'
  have hK2B : ∀ t : unitInterval, fl.Ψ (star (B t) + 1 / 2) ∉ Work.EL.K c := by
    intro t; obtain ⟨t', ht'⟩ := hrange t; rw [ht']; exact hK2 t'
  have hK3B : ∀ t : unitInterval, fl.Ψ (star (B t - 1) + 1 / 2) ∉ Work.EL.K c := by
    intro t; obtain ⟨t', ht'⟩ := hrange t; rw [ht']; exact hK3 t'
  have hdevB : ∀ t : unitInterval,
      |Work.GATE.deviation (Work.Bottcher.varphiCrit c) Work.EL.alpha1 (fl.Ψ (B t))| <
        1 / 16384 := by
    intro t; obtain ⟨t', ht'⟩ := hrange t; rw [ht']; exact hdev t'
  have hdev1B : ∀ t : unitInterval,
      |Work.GATE.deviation (Work.Bottcher.varphiCrit c) Work.EL.alpha1 (fl.Ψ (B t - 1))| <
        1 / 16384 := by
    intro t; obtain ⟨t', ht'⟩ := hrange t; rw [ht']; exact hdev1 t'
  have hdev2B : ∀ t : unitInterval,
      |Work.GATE.deviation (Work.Bottcher.varphiCrit c) Work.EL.alpha2
        (fl.Ψ (star (B t) + 1 / 2))| < 1 / 16384 := by
    intro t; obtain ⟨t', ht'⟩ := hrange t; rw [ht']; exact hdev2 t'
  have hdev3B : ∀ t : unitInterval,
      |Work.GATE.deviation (Work.Bottcher.varphiCrit c) Work.EL.alpha2
        (fl.Ψ (star (B t - 1) + 1 / 2))| < 1 / 16384 := by
    intro t; obtain ⟨t', ht'⟩ := hrange t; rw [ht']; exact hdev3 t'
  obtain ⟨tB, htB⟩ : ∃ t' : unitInterval, B 0 = A t' := hrange 0
  have hfloorB : ∀ t : unitInterval,
      (3 / 4 : ℝ) * Work.Bottcher.green c (fl.Ψ (B 0 - 1)) <
        Work.Bottcher.green c (fl.Ψ (B t)) := by
    intro t
    obtain ⟨t', ht'⟩ := hrange t
    have h1 : B 0 - 1 = A tB - 1 := by rw [htB]
    rw [h1, ht']
    exact hfloor2 tB t'
  have hfloorB1 : ∀ t : unitInterval,
      (3 / 4 : ℝ) * Work.Bottcher.green c (fl.Ψ (B 0 - 1)) <
        Work.Bottcher.green c (fl.Ψ (B t - 1)) := by
    intro t
    obtain ⟨t', ht'⟩ := hrange t
    have h1 : B 0 - 1 = A tB - 1 := by rw [htB]
    have h2 : B t - 1 = A t' - 1 := by rw [ht']
    rw [h1, h2]
    exact hfloor1 tB t'
  have hfloorγ₁B : ∀ u ∈ Set.Icc (0 : ℝ) 1,
      (3 / 4 : ℝ) * Work.Bottcher.green c (fl.Ψ (B 0 - 1)) <
        Work.Bottcher.green c (fl.Ψ (Lray.γ₁ (s₁ - 1 + u))) := by
    intro u hu
    have h1 : B 0 - 1 = A tB - 1 := by rw [htB]
    rw [h1]
    exact hfloorγ₁ tB u hu
  have hfloorι1B : ∀ t : unitInterval,
      (3 / 4 : ℝ) * Work.Bottcher.green c (fl.Ψ (star (B 0 - 1) + 1 / 2)) <
        Work.Bottcher.green c (fl.Ψ (star (B t - 1) + 1 / 2)) := by
    intro t
    obtain ⟨t', ht'⟩ := hrange t
    have h1 : star (B 0 - 1) + 1 / 2 = star (A tB - 1) + 1 / 2 := by rw [htB]
    have h2 : star (B t - 1) + 1 / 2 = star (A t' - 1) + 1 / 2 := by rw [ht']
    rw [h1, h2]
    exact hfloorι1 tB t'
  have hfloorι2B : ∀ t : unitInterval,
      (3 / 4 : ℝ) * Work.Bottcher.green c (fl.Ψ (star (B 0 - 1) + 1 / 2)) <
        Work.Bottcher.green c (fl.Ψ (star (B t) + 1 / 2)) := by
    intro t
    obtain ⟨t', ht'⟩ := hrange t
    have h1 : star (B 0 - 1) + 1 / 2 = star (A tB - 1) + 1 / 2 := by rw [htB]
    have h2 : star (B t) + 1 / 2 = star (A t') + 1 / 2 := by rw [ht']
    rw [h1, h2]
    exact hfloorι2 tB t'
  have hfloorγ₂B : ∀ u ∈ Set.Icc (0 : ℝ) 1,
      (3 / 4 : ℝ) * Work.Bottcher.green c (fl.Ψ (star (B 0 - 1) + 1 / 2)) <
        Work.Bottcher.green c (fl.Ψ (Lray.γ₂ (s₁ - 1 + u))) := by
    intro u hu
    have h1 : star (B 0 - 1) + 1 / 2 = star (A tB - 1) + 1 / 2 := by rw [htB]
    rw [h1]
    exact hfloorγ₂ tB u hu
  obtain ⟨r₁, v₁, hr₁, hE₁⟩ :=
    Work.GATE2.EXL.exitLoop_of_arcSegment fl Lray B hB0 (hB1.trans hA1) hBre hγre hsgnB hγim
      hKB hK1B hdevB hdev1B hfloorB hfloorB1 hfloorγ₁B
  obtain ⟨r₂, v₂, hr₂, hE₂⟩ :=
    Work.GATE2.EXL.exitLoop_iota_of_arcSegment fl Lray B hB0 (hB1.trans hA1) hBre hγre hsgnB
      hγim hK2B hK3B hKγ₂ hdev2B hdev3B hdevγ₂ hfloorι2B hfloorι1B hfloorγ₂B
  have hbx : B 0 = ((x : ℝ) : ℂ) := hB0
  have hleak : fl.Ψ ((x : ℝ) : ℂ) ∉ Work.EL.K c := by rw [← hbx]; exact hKB 0
  have hxdeep : x < -(3 / 2 : ℝ) := by
    have h := hBre 0
    rw [hbx] at h
    simpa using h
  exact ⟨x, deepLeak_of_leak (fl := fl) hxdeep hleak,
    ⟨r₁, hr₁, fun r₀ hr v => ⟨Work.GATE2.EXL.ExitLoop.mono_r₀ (Work.GATE2.EXL.ExitLoop.congr_v hE₁.some v) hr.2⟩⟩,
    ⟨r₂, hr₂, fun r₀ hr v => ⟨Work.GATE2.EXL.ExitLoop.mono_r₀ (Work.GATE2.EXL.ExitLoop.congr_v hE₂.some v) hr.2⟩⟩⟩

end Work.GATE2
