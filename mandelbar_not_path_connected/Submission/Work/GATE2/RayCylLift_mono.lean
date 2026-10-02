import Mathlib
import Submission.Work.GATE2.Inputs
import Submission.Work.ELRig.CylLift

-- Lean v4.35.0-rc3 / Mathlib 5e0c4e5 made `isDefEq` respect transparency when unifying instances; with it,
-- `ZMod.instField` and `ZMod.commRing` (and `Neg (ZMod p)` via `SubtractionMonoid`) no longer unify, which
-- breaks `ring`/`rw`/module-instance search on `ZMod p`. Restore the v4.34 behaviour for this file.
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false


namespace Work.GATE2

open LeanEval.ComplexAnalysis (Tantibar)

/-- **Monotonicity of a `RayCylLift` in the half-plane level `R`.**  Every field of a
`RayCylLift` weakens as `R` grows: the `tailId`, `hzne` and `hinj` fields ask `w.re < -R`, and
`hγtail` only asks `R₀ < R`.  Hence for `R ≤ R'` there is a lift with the *same* curves
`γ₁`, `γ₂` and level map `τ` and with half-plane level `R'`.  In particular a lift of level `R`
gives one of level `max R (3/2)`, which is how the interface choice `3/2 ≤ Lray.R` of the
case-(ii) drive is discharged. -/
theorem RayCylLift_mono {c : ℂ} {d : Work.EL.RootParabolic c}
    {fl : Work.EL.ParabolicFlower (Work.EL.F c) ((Tantibar c)^[5]) d.z₁}
    (L : Work.ELRig.RayCylLift d fl) {R' : ℝ} (hR : L.R ≤ R') :
    ∃ L' : Work.ELRig.RayCylLift d fl,
      L'.γ₁ = L.γ₁ ∧ L'.γ₂ = L.γ₂ ∧ L'.τ = L.τ ∧ L'.R = R' := by
  obtain ⟨R₀, hR₀, hγtail⟩ := L.hγtail
  have hle : -R' ≤ -L.R := neg_le_neg hR
  refine ⟨{ γ₁ := L.γ₁, γ₂ := L.γ₂, τ := L.τ, R := R'
            hτmono := L.hτmono, hτ1 := L.hτ1, hΨ₁ := L.hΨ₁
            cont₁ := L.cont₁, cont₂ := L.cont₂, per₁ := L.per₁, per₂ := L.per₂
            anti := L.anti
            tailId₁ := fun w hw => L.tailId₁ w (lt_of_lt_of_le hw hle)
            tailId₂ := fun w hw => L.tailId₂ w (lt_of_lt_of_le hw hle)
            hzne := fun w hw => L.hzne w (lt_of_lt_of_le hw hle)
            hγtail := ⟨R₀, lt_of_lt_of_le hR₀ hR, hγtail⟩
            hinj := fun w hw w' hw' h => L.hinj (lt_of_lt_of_le hw hle) (lt_of_lt_of_le hw' hle) h },
          rfl, rfl, rfl, rfl⟩

end Work.GATE2
