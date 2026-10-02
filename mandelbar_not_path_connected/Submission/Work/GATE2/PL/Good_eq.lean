import Mathlib
import Submission.Work.GATE2.PL.Defs
import Submission.Work.GATE2.PL.Main
import Submission.Work.GATE2.PL.isCoveringMapOn_tantibar_five
import Submission.Work.GATE2.ExitPathInputs

-- Lean v4.35.0-rc3 / Mathlib 5e0c4e5 made `isDefEq` respect transparency when unifying instances; with it,
-- `ZMod.instField` and `ZMod.commRing` (and `Neg (ZMod p)` via `SubtractionMonoid`) no longer unify, which
-- breaks `ring`/`rw`/module-instance search on `ZMod p`. Restore the v4.34 behaviour for this file.
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false


namespace Work.GATE2.PL

open Set Function Filter
open Classical
open LeanEval.ComplexAnalysis (Tantibar)

noncomputable section

set_option maxHeartbeats 1000000
set_option linter.unusedVariables false
set_option linter.unusedSimpArgs false

/-- `Good` is monotone in the level: a half-step lift on `Dom v X k` restricts to `Dom v X j`
for `j ≤ k`. -/
theorem Good_mono {c₀ : ℂ} {d : Work.EL.RootParabolic c₀}
    {fl : Work.EL.ParabolicFlower (Work.EL.F c₀) (G5 c₀) d.z₁}
    {FF : Work.PARIMPL.FlowerFix d (Work.EL.F c₀) (G5 c₀) d.z₁ fl.Pa fl.φa}
    {v X : ℝ} {j k : ℕ} (hjk : j ≤ k) {ψ : ℂ → ℂ}
    (h : Work.GATE2.PL.Good fl FF v X k ψ) : Work.GATE2.PL.Good fl FF v X j ψ :=
  ⟨fun w hw => h.anti w (Work.GATE2.PL.dom_mono hjk hw), h.far,
    h.cont.mono (Work.GATE2.PL.dom_mono hjk)⟩

/-- **Uniqueness of the half-step lift on a slit domain.**  Let `F = Work.EL.F c₀ = (T_{c₀})^[10]`, `g = Work.GATE2.PL.G5 c₀ = (T_{c₀})^[5]` (an antiholomorphic square root of `F`), `fl` the Leau–Fatou flower of `F` at `d.z₁`, `FF` the associated `FlowerFix`, and `sig w = w̄ + 1/2`.  On the slit domain `Dom v X k = Work.GATE2.PL.slitAt v ∩ {w | X − k/2 < Re w}` the predicate `Work.GATE2.PL.Good fl FF v X k ψ` says that `ψ` is continuous on `Dom v X k`, satisfies `g (ψ w) = ψ (sig w)` there, and is far to the right the inverse of the Fatou coordinate `fl.φa` on the sub-petal `FF.Pg`.

Two such half-step lifts are **equal on `Dom v X k`**, provided the common base map `z ↦ ψ (sig z)` avoids the critical values `critVals = {T_{c₀}^[j] c₀ : 0 ≤ j ≤ 4}` of `g` on `Dom v X k`.

Proof: induction on `k`.  At `k = 0`, `Dom v X 0 ⊆ {Re > X}` where both functions are inverse to the injective `φa` on `Pg` (`fl.φa_fatou.2`).  For the step, both `ψ₁, ψ₂` are continuous lifts, on the simply connected `Dom v X (k+1)`, of the *same* base map `z ↦ ψ₁ (sig z)` (they agree on `Dom v X k` by induction, and `sig '' Dom v X (k+1) ⊆ Dom v X k`), through the covering map `Work.GATE2.PL.isCoveringMapOn_tantibar_five c₀` over `critValsᶜ`; uniqueness of lifts (`IsCoveringMapOn.existsUnique_continuousMap_lifts`) and the basepoint `X + 1` (where both equal the inverse of `φa`) finish.  The pattern of the lift construction is in `Submission/Work/GATE2/PL/Main.lean` (`exists_step_of_avoid`). -/
theorem Good_eq {c₀ : ℂ} {d : Work.EL.RootParabolic c₀}
    {fl : Work.EL.ParabolicFlower (Work.EL.F c₀) (Work.GATE2.PL.G5 c₀) d.z₁}
    {FF : Work.PARIMPL.FlowerFix d (Work.EL.F c₀) (Work.GATE2.PL.G5 c₀) d.z₁ fl.Pa fl.φa}
    {v X : ℝ} (hX : v - 1 / 2 ≤ X) {k : ℕ} {ψ₁ ψ₂ : ℂ → ℂ}
    (h1 : Work.GATE2.PL.Good fl FF v X k ψ₁) (h2 : Work.GATE2.PL.Good fl FF v X k ψ₂)
    (hav : ∀ z : ℂ, z ∈ Work.GATE2.PL.Dom v X k →
      ψ₁ (Work.GATE2.PL.sig z) ∉ Work.GATE2.PL.critVals (c₀ := c₀)) :
    ∀ w ∈ Work.GATE2.PL.Dom v X k, ψ₁ w = ψ₂ w := by
  revert h1 h2 hav
  induction k with
  | zero =>
    intro h1 h2 hav w hw
    have hw' : X < w.re := by
      obtain ⟨-, h⟩ := mem_Dom.mp hw
      simpa using h
    obtain ⟨h1Pg, h1φ⟩ := h1.far w hw'
    obtain ⟨h2Pg, h2φ⟩ := h2.far w hw'
    exact fl.φa_fatou.2 (FF.Pg_sub h1Pg) (FF.Pg_sub h2Pg) (by rw [h1φ, h2φ])
  | succ k ih =>
    intro h1 h2 hav w hw
    -- restrict the two `Good` functions to the smaller level `k`
    have h1k : Good fl FF v X k ψ₁ := Good_mono (Nat.le_succ k) h1
    have h2k : Good fl FF v X k ψ₂ := Good_mono (Nat.le_succ k) h2
    have havk : ∀ z : ℂ, z ∈ Dom v X k → ψ₁ (sig z) ∉ critVals (c₀ := c₀) :=
      fun z hz => hav z (dom_mono (Nat.le_succ k) hz)
    have hagree : ∀ z ∈ Dom v X k, ψ₁ z = ψ₂ z := ih h1k h2k havk
    -- the common base map on the simply connected domain `Dom v X (k+1)`
    have hcontb : ContinuousOn (fun z : ℂ => ψ₁ (sig z)) (Dom v X (k + 1)) :=
      h1.cont.comp continuous_sig.continuousOn
        (fun z hz => dom_mono (Nat.le_succ k) (dom_sig_succ hz))
    haveI hLP : LocallyPathConnectedSpace ↥(Dom v X (k + 1)) :=
      (isOpen_Dom v X (k + 1)).locallyPathConnectedSpace
    haveI hCT : ContractibleSpace ↥(Dom v X (k + 1)) := contractibleSpace_Dom hX (k + 1)
    haveI hSC : SimplyConnectedSpace ↥(Dom v X (k + 1)) := SimplyConnectedSpace.ofContractible _
    have hp : ((X + 1 : ℝ) : ℂ) ∈ Dom v X (k + 1) := mem_Dom_starP hX (k + 1)
    have hre : X < (((X + 1 : ℝ) : ℂ)).re := by
      simp only [Complex.ofReal_re]
      linarith
    let hb : C(↥(Dom v X (k + 1)), ℂ) :=
      ⟨(Dom v X (k + 1)).domRestrict (fun z : ℂ => ψ₁ (sig z)), hcontb.domRestrict⟩
    have hb_val : ∀ a : ↥(Dom v X (k + 1)), hb a = ψ₁ (sig (a : ℂ)) := fun a => rfl
    obtain ⟨F, ⟨hFp, hFg⟩, huniq⟩ :=
      IsCoveringMapOn.existsUnique_continuousMap_lifts (isCoveringMapOn_tantibar_five c₀) hb
        (a₀ := (⟨((X + 1 : ℝ) : ℂ), hp⟩ : ↥(Dom v X (k + 1))))
        (e₀ := ψ₁ ((X + 1 : ℝ) : ℂ))
        (by rw [hb_val _]; exact h1.anti _ hp)
        (fun a => by rw [hb_val a]; exact hav _ a.2)
    -- `ψ₁` restricted to level `k+1` is a lift
    have h1lift : (⟨(Dom v X (k + 1)).domRestrict ψ₁, h1.cont.domRestrict⟩ :
        C(↥(Dom v X (k + 1)), ℂ)) = F := by
      refine huniq _ ⟨rfl, ?_⟩
      funext a
      show G5 c₀ (ψ₁ (a : ℂ)) = hb a
      rw [h1.anti (a : ℂ) a.2, hb_val a]
    -- `ψ₂` restricted to level `k+1` is a lift as well: it agrees with `ψ₁` on `sig '' Dom v X (k+1)`
    -- by the induction hypothesis, and at the basepoint `X + 1` by injectivity of `φa` on `Pg`.
    have h2lift : (⟨(Dom v X (k + 1)).domRestrict ψ₂, h2.cont.domRestrict⟩ :
        C(↥(Dom v X (k + 1)), ℂ)) = F := by
      refine huniq _ ⟨?_, ?_⟩
      · show ψ₂ ((X + 1 : ℝ) : ℂ) = ψ₁ ((X + 1 : ℝ) : ℂ)
        obtain ⟨ha1Pg, ha1φ⟩ := h1.far _ hre
        obtain ⟨ha2Pg, ha2φ⟩ := h2.far _ hre
        exact (fl.φa_fatou.2 (FF.Pg_sub ha1Pg) (FF.Pg_sub ha2Pg) (by rw [ha1φ, ha2φ])).symm
      · funext a
        show G5 c₀ (ψ₂ (a : ℂ)) = hb a
        rw [h2.anti (a : ℂ) a.2, hb_val a]
        exact (hagree _ (dom_sig_succ a.2)).symm
    have h1w : ψ₁ w = F ⟨w, hw⟩ := by
      have hh := congrArg (fun g : C(↥(Dom v X (k + 1)), ℂ) => g ⟨w, hw⟩) h1lift
      simpa only [ContinuousMap.coe_mk, Set.domRestrict_apply] using hh
    have h2w : ψ₂ w = F ⟨w, hw⟩ := by
      have hh := congrArg (fun g : C(↥(Dom v X (k + 1)), ℂ) => g ⟨w, hw⟩) h2lift
      simpa only [ContinuousMap.coe_mk, Set.domRestrict_apply] using hh
    rw [h1w, h2w]

end

end Work.GATE2.PL
