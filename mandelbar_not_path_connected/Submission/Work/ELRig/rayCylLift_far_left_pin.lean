import Mathlib
import Submission.Work.ELRig.CylLift
import Submission.Work.ELRig.exists_rayCylLift

-- Lean v4.35.0-rc3 / Mathlib 5e0c4e5 made `isDefEq` respect transparency when unifying instances; with it,
-- `ZMod.instField` and `ZMod.commRing` (and `Neg (ZMod p)` via `SubtractionMonoid`) no longer unify, which
-- breaks `ring`/`rw`/module-instance search on `ZMod p`. Restore the v4.34 behaviour for this file.
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false


namespace Work.ELRig

/-- The "height" `s ↦ Re (γ₁ s) - s` of the first lift of a `RayCylLift` is `1`-periodic, hence
bounded above.  (Auxiliary form used by `rayCylLift_far_left_pin`.) -/
theorem rayCylLift_height_bdd {c : ℂ} {d : Work.EL.RootParabolic c}
    {fl : Work.EL.ParabolicFlower (Work.EL.F c) ((LeanEval.ComplexAnalysis.Tantibar c)^[5]) d.z₁}
    (L : Work.ELRig.RayCylLift d fl) :
    ∃ M : ℝ, ∀ s : ℝ, (L.γ₁ s).re - s ≤ M := by
  have hper : Function.Periodic (fun s : ℝ => (L.γ₁ s).re - s) 1 := by
    intro s
    show (L.γ₁ (s + 1)).re - (s + 1) = (L.γ₁ s).re - s
    rw [L.per₁ s]
    simp only [Complex.add_re, Complex.one_re]
    ring
  have hcont : Continuous (fun s : ℝ => (L.γ₁ s).re - s) :=
    (Complex.continuous_re.comp L.cont₁).sub continuous_id
  obtain ⟨x, _, hxmax⟩ :=
    isCompact_Icc.exists_isMaxOn (Set.nonempty_Icc.mpr (zero_le_one : (0:ℝ) ≤ 1))
      hcont.continuousOn
  refine ⟨(L.γ₁ x).re - x, fun s => ?_⟩
  have hb : (L.γ₁ (Int.fract s)).re - Int.fract s ≤ (L.γ₁ x).re - x :=
    (isMaxOn_iff.mp hxmax) (Int.fract s) ⟨Int.fract_nonneg s, (Int.fract_lt_one s).le⟩
  have hshift : (L.γ₁ s).re - s = (L.γ₁ (Int.fract s)).re - Int.fract s := by
    have h := hper.int_mul ⌊s⌋ (Int.fract s)
    rw [mul_one, Int.fract_add_floor s] at h
    exact h
  rw [hshift]
  exact hb

/-- **In a far-left half plane the first lift is the inverse repelling image of its own ray point.**

Two facts about an arbitrary `RayCylLift` `L`.  First, the "height" `s ↦ (L.γ₁ s).re - s` is
`1`-periodic (`L.per₁`: `(L.γ₁ (s+1)).re = (L.γ₁ s).re + 1`) and continuous (`L.cont₁`), hence
bounded by some `M ≥ 0`; so for `s ≤ -R - M` one has `(L.γ₁ s).re < -R`.

Second, for such `s` the point `L.γ₁ s` and `Function.invFunOn fl.Ψ {w : ℂ | w.re < -R}
(Work.EL.rayPt d.hN Work.EL.alpha1 (L.τ u))` both lie in the half plane `{w : ℂ | w.re < -R}`
(the second by `Function.invFunOn_mem`, using `L.γ₁ u` as an explicit witness that
`rayPt α₁ (L.τ u) ∈ fl.Ψ '' {w | w.re < -R}`) and have the same `fl.Ψ`-image `rayPt α₁ (L.τ u)`
(`L.hΨ₁` and `Function.invFunOn_eq`); since `{w | w.re < -R} ⊆ {w | w.re < -L.R}` when
`L.R ≤ R`, `L.hinj` makes `fl.Ψ` injective there, so the two points are equal. -/
theorem rayCylLift_far_left_pin {c : ℂ} (d : Work.EL.RootParabolic c)
    (fl : Work.EL.ParabolicFlower (Work.EL.F c) ((LeanEval.ComplexAnalysis.Tantibar c)^[5]) d.z₁)
    (L : Work.ELRig.RayCylLift d fl) {R : ℝ} (hR : L.R ≤ R) :
    ∃ sstar : ℝ, ∀ u : ℝ, u ≤ sstar →
      L.γ₁ u = Function.invFunOn fl.Ψ {w : ℂ | w.re < -R}
        (Work.EL.rayPt d.hN Work.EL.alpha1 (L.τ u)) := by
  obtain ⟨M, hM⟩ := rayCylLift_height_bdd L
  refine ⟨-R - M - 1, fun u hu => ?_⟩
  have hre : (L.γ₁ u).re < -R := by
    have h1 := hM u
    linarith
  have hwit : ∃ w ∈ {w : ℂ | w.re < -R},
      fl.Ψ w = Work.EL.rayPt d.hN Work.EL.alpha1 (L.τ u) :=
    ⟨L.γ₁ u, hre, L.hΨ₁ u⟩
  have hmem : Function.invFunOn fl.Ψ {w : ℂ | w.re < -R}
      (Work.EL.rayPt d.hN Work.EL.alpha1 (L.τ u)) ∈ {w : ℂ | w.re < -R} :=
    Function.invFunOn_mem hwit
  have heq : fl.Ψ (L.γ₁ u) = fl.Ψ (Function.invFunOn fl.Ψ {w : ℂ | w.re < -R}
      (Work.EL.rayPt d.hN Work.EL.alpha1 (L.τ u))) := by
    rw [L.hΨ₁ u, Function.invFunOn_eq hwit]
  exact L.hinj (lt_of_lt_of_le hre (neg_le_neg hR))
    (lt_of_lt_of_le hmem (neg_le_neg hR)) heq

end Work.ELRig
