/-
# GATE2 — the two branches of the design's dichotomy, and their assembly

* **`Work.GATE2.twoSided_of_realCrossing`** (`RealCrossDrive.lean`) closes the **first** branch
  (the ray lift meets the real axis) completely.
* **`Work.GATE2.EXL.exitLoop_iota_of_curve`** — the `ι`-twin of the general exit loop: if `lam`
  is a compact curve of the `Ψ`-plane from `x₀ - 1` to `x₀` whose **conjugate** `star (lam t) + 1/2`
  satisfies the four conditions (off `K`, the `α₂`-window, the `3/4`-floor, the slit), then there
  is an exit loop at `x₀ + 1/2` for the angle `α₂`.  This is
  `Work.GATE2.EXL.exitLoop_of_curve` applied to the conjugated curve (the slit condition is
  invariant under `star`: `star w ∈ slitAt 0 ↔ w ∈ slitAt 0`).
* **`Work.GATE2.CaseIILeak`** — the *single* residual of the area: in case (ii) (the real axis
  misses both lifts) there is a deep real leak point `xLeak` with both exit-loop families at
  `xLeak` and `xLeak + 1/2`.  By `Work.GATE2.deepLeak_of_leak`, `DeepLeak` only asks for
  `Ψ xLeak ∉ K c₀` with `xLeak < -3/2`; the two families are the output of
  `Work.GATE2.EXL.exitLoop_of_curve` on the lifted equipotential arc (`NOTES_LEAD_mandelbar_gaps3.md`
  §2.2 (b)).
* **`Work.GATE2.twoSided_of_dichotomy`** — `Work.GATE.TwoSided c₀ P.Nm` from the dichotomy's
  disjunction (`Work.GATE2.EXL.exists_real_crossing_or_htail`'s two cases, the first spelled as
  "the lift `gamma_1` has a real point" and the second as `CaseIILeak`).
* **`Work.GATE2.twoSided_of_nest`** — the same, with the dichotomy *derived* from the nest data
  (`nest`, `han`, `hflip`) by `Work.GATE2.EXL.exists_real_crossing_or_htail`; its only residual is
  `CaseIILeak c₀ fl.Ψ`.
-/
import Submission.Work.MandelWire.GATE2n.RealCrossDrive
import Submission.Work.GATE2.EXL.exitLoop_of_curve
import Submission.Work.GATE2.EXL.Dichotomy

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

namespace Work.MandelWire.G2n

open Work.GATE2

open LeanEval.ComplexAnalysis (Mandelbar Tantibar)

namespace EXL

/-- **The `ι`-twin of `exitLoop_of_curve`.**  The exit loop for the angle `α₂` at the centre
`x₀ + 1/2` is the one for the angle `α₂` at the *conjugated* curve `star (lam t) + 1/2`, which runs
from `x₀ - 1/2` to `x₀ + 1/2`.  The slit condition is invariant under `star`, and the `Re`-bound
`< -3/2` for `lam` gives `< -1` for the conjugate. -/
theorem exitLoop_iota_of_curve {c₀ : ℂ} {d : Work.EL.RootParabolic c₀}
    (fl : Work.EL.ParabolicFlower (Work.EL.F c₀) ((Tantibar c₀)^[5]) d.z₁)
    {x₀ : ℝ} (lam : C(unitInterval, ℂ))
    (h0 : lam 0 = ((x₀ - 1 : ℝ) : ℂ)) (h1 : lam 1 = ((x₀ : ℝ) : ℂ))
    (hre : ∀ t : unitInterval, (lam t).re < -(3 / 2 : ℝ))
    (hK : ∀ t : unitInterval, fl.Ψ (star (lam t) + 1 / 2) ∉ Work.EL.K c₀)
    (hwin : ∀ t : unitInterval,
      |Work.GATE.deviation (Work.Bottcher.varphiCrit c₀) Work.EL.alpha2
        (fl.Ψ (star (lam t) + 1 / 2))| < 1 / 16384)
    (hfloor : ∀ t : unitInterval,
      (3 / 4 : ℝ) * Work.Bottcher.green c₀ (fl.Ψ (star (lam 0) + 1 / 2)) <
        Work.Bottcher.green c₀ (fl.Ψ (star (lam t) + 1 / 2)))
    (hslit : ∀ t : unitInterval, lam t - lam 0 ∈ Work.GATE2.slitAt 0) :
    ∃ r₀ v : ℝ, 0 < r₀ ∧
      Nonempty (Work.GATE2.ExitLoop c₀ fl.Ψ (x₀ + 1 / 2) r₀ v Work.EL.alpha2) := by
  have hcont : Continuous (fun t : unitInterval => star (lam t) + 1 / 2) :=
    lam.continuous.star.add continuous_const
  have hstar_slit : ∀ w : ℂ, star w ∈ Work.GATE2.slitAt 0 ↔ w ∈ Work.GATE2.slitAt 0 := by
    intro w
    simp only [Work.GATE2.slitAt]
    constructor
    · intro h hc; exact h ⟨by simpa using hc.1, by simpa using hc.2⟩
    · intro h hc; exact h ⟨by simpa using hc.1, by simpa using hc.2⟩
  refine Work.GATE2.EXL.exitLoop_of_curve (fl := fl) (α := Work.EL.alpha2) (x₀ := x₀ + 1 / 2)
    ⟨fun t : unitInterval => star (lam t) + 1 / 2, hcont⟩ ?_ ?_ ?_ ?_ ?_ ?_ ?_
  · show star (lam 0) + 1 / 2 = (((x₀ + 1 / 2) - 1 : ℝ) : ℂ)
    rw [h0]
    have hs : star (((x₀ - 1 : ℝ)) : ℂ) = (((x₀ - 1 : ℝ)) : ℂ) := by simp
    rw [hs]; push_cast; ring
  · show star (lam 1) + 1 / 2 = (((x₀ + 1 / 2) : ℝ) : ℂ)
    rw [h1]
    have hs : star (((x₀ : ℝ)) : ℂ) = (((x₀ : ℝ)) : ℂ) := by simp
    rw [hs]; push_cast; ring
  · intro t
    show (star (lam t) + 1 / 2).re < -1
    have h := hre t
    have hre' : (star (lam t) + 1 / 2).re = (lam t).re + 1 / 2 := by simp
    rw [hre']; linarith
  · intro t; exact hK t
  · intro t; exact hwin t
  · intro t; exact hfloor t
  · intro t
    show star (lam t) + 1 / 2 - (star (lam 0) + 1 / 2) ∈ Work.GATE2.slitAt 0
    have hsub : star (lam t) + 1 / 2 - (star (lam 0) + 1 / 2) = star (lam t - lam 0) := by
      simp
    rw [hsub]
    exact (hstar_slit (lam t - lam 0)).mpr (hslit t)

end EXL

/-- **The residual of the area**: in case (ii) of the dichotomy (the real axis misses both lifts)
there is a deep real leak point `xLeak` with both exit-loop families — at `xLeak` for the angle
`α₁`, and at `xLeak + 1/2` for the angle `α₂`.  This is what the design's §2.2 (b) produces from the
lifted equipotential arc through the deep equator tail `pairSideNear P0 ∩ pairSideNear (Q n)`. -/
def CaseIILeak (c₀ : ℂ) (Ψ : ℂ → ℂ) : Prop :=
  ∃ xLeak : ℝ, DeepLeak c₀ Ψ xLeak ∧
    (∃ R : ℝ, 0 < R ∧ ∀ r₀ ∈ Set.Ioc (0 : ℝ) R, ∀ v : ℝ,
      Nonempty (ExitLoop c₀ Ψ xLeak r₀ v Work.EL.alpha1)) ∧
    (∃ R : ℝ, 0 < R ∧ ∀ r₀ ∈ Set.Ioc (0 : ℝ) R, ∀ v : ℝ,
      Nonempty (ExitLoop c₀ Ψ (xLeak + 1 / 2) r₀ v Work.EL.alpha2))

/-- **The assembly: `Work.GATE.TwoSided c₀ P.Nm` from the design's dichotomy.**  The first branch
is closed unconditionally (`Work.GATE2.twoSided_of_realCrossing`); the second is the named residual
`Work.GATE2.CaseIILeak`. -/
theorem twoSided_of_dichotomy {c₀ : ℂ} {d : Work.EL.RootParabolic c₀}
    {fl : Work.EL.ParabolicFlower (Work.EL.F c₀) ((Tantibar c₀)^[5]) d.z₁}
    (FF : Work.PARIMPL.FlowerFix d (Work.EL.F c₀) ((Tantibar c₀)^[5]) d.z₁ fl.Pa fl.φa)
    {P : Work.PARIMPL.ParNormal d} {Pa : Set ℂ} {φa Ψ : ℂ → ℂ}
    (nIn : ℕ)
    (trans : ℂ → ℂ)
    (hOpen : IsOpen P.Nm) (hfront : c₀ ∈ frontier P.Nm)
    (hPaeq : Pa = fl.Pa) (hφa_eq : φa = fl.φa) (hΨeq : Ψ = fl.Ψ)
    (hentry₀ : Work.PARIMPL.entryPt P nIn c₀ ∈ Pa)
    (hcrit : (φa (Work.PARIMPL.entryPt P nIn c₀)).im = 0)
    (hSat : SaturatedFlower fl FF)
    {ρc : ℝ} (hρc : 0 < ρc) (hcont : ContinuousOn trans (P.Nm ∩ Metric.ball c₀ ρc))
    {ρh : ℝ} (hρh : 0 < ρh)
    (him : ∀ c ∈ P.Nm ∩ Metric.ball c₀ ρh, (trans c).im = 0)
    (hblowup : ∀ p ∈ frontier P.Nm ∩ Metric.ball c₀ ρh,
      Tendsto (fun c => (trans c).re) (𝓝[P.Nm] p) atBot)
    {ρe : ℝ} (hρe : 0 < ρe)
    (hblow : ∀ b : ℝ, ∃ r : ℝ, 0 < r ∧ ∀ c ∈ P.Nm ∩ Metric.ball c₀ r, (trans c).re ≤ b)
    (hLS : Work.PARIMPL2.LockstepAll c₀ P.Nm trans nIn
      (fun c z => Work.PARIMPL.Ft c z) Pa φa Ψ
      ((φa (Work.PARIMPL.entryPt P nIn c₀)).re - (nIn : ℝ)))
    (hG : Work.PARIMPL.GreenEscapeOpen)
    (Lray : Work.ELRig.RayCylLift d fl)
    (hcase : (∃ s : ℝ, (Lray.γ₁ s).im = 0) ∨ CaseIILeak c₀ fl.Ψ) :
    Work.GATE.TwoSided c₀ P.Nm := by
  rcases hcase with h0 | ⟨xLeak, hDL, hE₁, hE₂⟩
  · exact twoSided_of_realCrossing (d := d) (nIn := nIn) FF trans hOpen hfront hPaeq hφa_eq hΨeq
      hentry₀ hcrit hSat hρc hcont hρh him hblowup hρe hblow hLS hG Lray h0
  · exact twoSided_of_deepLeak (d := d) (nIn := nIn) FF trans hOpen hfront hPaeq hφa_eq hΨeq
      hentry₀ hcrit hSat hρc hcont hρh him hblowup hρe hblow hLS hG hDL hE₁ hE₂

/-- **The same assembly with the dichotomy *derived* from the nest data.**  The hypothesis `hcaseII`
is the only residual: case (i) comes from `Work.GATE2.EXL.exists_real_crossing_or_htail` (whose case
(i) is a real crossing of `Lray` and whose case (ii) is the deep tail in the near side). -/
theorem twoSided_of_nest {c₀ : ℂ} {d : Work.EL.RootParabolic c₀}
    {fl : Work.EL.ParabolicFlower (Work.EL.F c₀) ((Tantibar c₀)^[5]) d.z₁}
    (FF : Work.PARIMPL.FlowerFix d (Work.EL.F c₀) ((Tantibar c₀)^[5]) d.z₁ fl.Pa fl.φa)
    {P : Work.PARIMPL.ParNormal d} {Pa : Set ℂ} {φa Ψ : ℂ → ℂ}
    (nIn : ℕ)
    (trans : ℂ → ℂ)
    (hOpen : IsOpen P.Nm) (hfront : c₀ ∈ frontier P.Nm)
    (hPaeq : Pa = fl.Pa) (hφa_eq : φa = fl.φa) (hΨeq : Ψ = fl.Ψ)
    (hentry₀ : Work.PARIMPL.entryPt P nIn c₀ ∈ Pa)
    (hcrit : (φa (Work.PARIMPL.entryPt P nIn c₀)).im = 0)
    (hSat : SaturatedFlower fl FF)
    {ρc : ℝ} (hρc : 0 < ρc) (hcont : ContinuousOn trans (P.Nm ∩ Metric.ball c₀ ρc))
    {ρh : ℝ} (hρh : 0 < ρh)
    (him : ∀ c ∈ P.Nm ∩ Metric.ball c₀ ρh, (trans c).im = 0)
    (hblowup : ∀ p ∈ frontier P.Nm ∩ Metric.ball c₀ ρh,
      Tendsto (fun c => (trans c).re) (𝓝[P.Nm] p) atBot)
    {ρe : ℝ} (hρe : 0 < ρe)
    (hblow : ∀ b : ℝ, ∃ r : ℝ, 0 < r ∧ ∀ c ∈ P.Nm ∩ Metric.ball c₀ r, (trans c).re ≤ b)
    (hLS : Work.PARIMPL2.LockstepAll c₀ P.Nm trans nIn
      (fun c z => Work.PARIMPL.Ft c z) Pa φa Ψ
      ((φa (Work.PARIMPL.entryPt P nIn c₀)).re - (nIn : ℝ)))
    (hG : Work.PARIMPL.GreenEscapeOpen)
    (nest : Work.EL.Z1Nest d.hN d.z₁ fl.Pa)
    (Lray : Work.ELRig.RayCylLift d fl)
    (han : ∀ n : ℤ, AnalyticOn ℝ (fun s : ℝ => Lray.γ₁ s) (Set.Ioo (n : ℝ) ((n : ℝ) + 1)))
    (hflip : Work.ELRig.FlipHyp fl nest.P0 Lray)
    (hcaseII : CaseIILeak c₀ fl.Ψ) :
    Work.GATE.TwoSided c₀ P.Nm := by
  rcases Work.GATE2.EXL.exists_real_crossing_or_htail d fl nest Lray han hflip with
    ⟨y₀, s, hγ, -⟩ | htail
  · refine twoSided_of_dichotomy (d := d) (nIn := nIn) FF trans hOpen hfront hPaeq hφa_eq hΨeq
      hentry₀ hcrit hSat hρc hcont hρh him hblowup hρe hblow hLS hG Lray (Or.inl ⟨s, ?_⟩)
    rw [hγ]
    simp
  · exact twoSided_of_dichotomy (d := d) (nIn := nIn) FF trans hOpen hfront hPaeq hφa_eq hΨeq
      hentry₀ hcrit hSat hρc hcont hρh him hblowup hρe hblow hLS hG Lray (Or.inr hcaseII)

end Work.MandelWire.G2n
