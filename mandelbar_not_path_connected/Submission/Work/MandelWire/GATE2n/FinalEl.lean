/-
# GATE2 — the endgame drive with the design's dichotomy and the new case-(ii) data

`Work.GATE.TwoSided c₀ P.Nm` from the PARIMPL/PARIMPL2 data, the flower and its saturation
certificate, the nest, the cylinder lift, and the case-(ii) data of
`Work.GATE2.caseIILeak_of_sides`.  The dichotomy is *derived* from the nest data
(`Work.GATE2.EXL.exists_real_crossing_or_htail`), so neither the case-(ii) assumption
`∀ s, (γ₁ s).im ≠ 0` nor the deep-tail hypothesis `∃ R, ∀ x < -R, Ψ x ∈ pairSideNear P0` is a
hypothesis of this theorem: the first branch of the dichotomy is closed by
`Work.GATE2.twoSided_of_realCrossing`, and the second supplies both.
-/
import Submission.Work.GATE2.SidesDrive
import Submission.Work.MandelWire.GATE2n.Dichotomy2
import Submission.Work.GATE2.hleak0_of_rigidity

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
set_option maxHeartbeats 1600000

noncomputable section

namespace Work.MandelWire.G2n

open Work.GATE2

open LeanEval.ComplexAnalysis (Mandelbar Tantibar)

/-- **The endgame from the derived dichotomy and the case-(ii) data.** -/
theorem twoSided_of_el {c₀ : ℂ} {d : Work.EL.RootParabolic c₀}
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
    (nest : Work.EL.Z1Nest d.hN d.z₁ fl.Pa) (Lray : Work.ELRig.RayCylLift d fl)
    (han : ∀ n : ℤ, AnalyticOn ℝ (fun s : ℝ => Lray.γ₁ s) (Set.Ioo (n : ℝ) ((n : ℝ) + 1)))
    (hflip : Work.ELRig.FlipHyp fl nest.P0 Lray)
    (hQa : ∀ n : ℕ, (nest.Q n).a = Work.ELNest.bAng' n)
    (hQb : ∀ n : ℕ, (nest.Q n).b = Work.ELNest.bAng n + 1)
    (hR : 3 / 2 ≤ Lray.R)
    (hPsides : ∀ n : ℕ, (nest.Q (n + 1)).y ∈ Work.EL.pairSideNear nest.P0)
    (hQsides : ∀ n : ℕ, (nest.Q (n + 1)).y ∈ Work.EL.pairSideNear (nest.Q n))
    (hangle : ∀ n : ℕ, ∀ x : ℝ, fl.Ψ ((x : ℝ) : ℂ) ∉ Work.EL.K c₀ →
      fl.Ψ ((x : ℝ) : ℂ) ∈ Work.EL.pairSideNear nest.P0 →
      fl.Ψ ((x : ℝ) : ℂ) ∈ Work.EL.pairSideNear (nest.Q (n + 1)) →
      (∃ θ ∈ Set.Ioo (Work.ELNest.bAng n) Work.EL.alpha1,
          ∃ t : ℝ, 1 < t ∧ fl.Ψ ((x : ℝ) : ℂ) = Work.EL.rayPt d.hN θ t) ∨
        (∃ θ ∈ Set.Ioo (Work.ELNest.bAng n) Work.EL.alpha1,
          ∃ t : ℝ, 1 < t ∧ fl.Ψ (((x + 1 / 2 : ℝ)) : ℂ) = Work.EL.rayPt d.hN θ t))
    (tr : Work.EL.B2Data d.hN d.z₁)
    (hpot : ∀ g : ℝ, 0 < g → ∃ R : ℝ, ∀ w : ℂ, w.re < -R → Work.EL.pot d.hN (fl.Ψ w) < g)
    (hΨsmall : ∀ ε : ℝ, 0 < ε → ∃ R : ℝ, ∀ w : ℂ, w.re < -R → ‖fl.Ψ w - d.z₁‖ < ε)
    (hs₁ : ∃ P₀ : ℝ, 0 < P₀ ∧ ∀ p ∈ Set.Ioo (0 : ℝ) P₀, ∃ s₁ : ℝ, Lray.τ s₁ = Real.exp p ∧
      ∀ u ∈ Set.Icc (0 : ℝ) 1, (Lray.γ₁ (s₁ - 1 + u)).re < -Lray.R) :
    Work.GATE.TwoSided c₀ P.Nm := by
  by_cases hcross : ∃ s : ℝ, (Lray.γ₁ s).im = 0
  · exact twoSided_of_dichotomy (d := d) (nIn := nIn) FF trans hOpen hfront hPaeq hφa_eq hΨeq
      hentry₀ hcrit hSat hρc hcont hρh him hblowup hρe hblow hLS hG Lray (Or.inl hcross)
  · push_neg at hcross
    have htail : ∃ R' : ℝ, ∀ x : ℝ, x < -R' →
        fl.Ψ ((x : ℝ) : ℂ) ∈ Work.EL.pairSideNear nest.P0 := by
      rcases Work.GATE2.EXL.exists_real_crossing_or_htail d fl nest Lray han hflip with
        ⟨y₀, s, hγ, _⟩ | htail
      · exact absurd (hcross s) (by rw [hγ]; simp)
      · exact htail
    exact twoSided_of_dichotomy (d := d) (nIn := nIn) FF trans hOpen hfront hPaeq hφa_eq hΨeq
      hentry₀ hcrit hSat hρc hcont hρh him hblowup hρe hblow hLS hG Lray
      (Or.inr (caseIILeak_of_sides (d := d) fl nest Lray hQa hQb hR hPsides hQsides hangle
        (Work.GATE2.hleak0_of_rigidity (d := d) fl nest htail tr) htail hpot hΨsmall hcross hs₁))

end Work.MandelWire.G2n
