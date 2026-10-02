import Mathlib
import Submission.Work.ELRig.analyticOn_rayPt_of_analytic

-- Lean v4.35.0-rc3 / Mathlib 5e0c4e5 made `isDefEq` respect transparency when unifying instances; with it,
-- `ZMod.instField` and `ZMod.commRing` (and `Neg (ZMod p)` via `SubtractionMonoid`) no longer unify, which
-- breaks `ring`/`rw`/module-instance search on `ZMod p`. Restore the v4.34 behaviour for this file.
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false


namespace Work.ELRig.RayPtC

open Set

/-- **Complex extension of a dynamic ray parameterisation.**

For a dynamical Nakane datum `hN : Work.EL.DynB c φ` and a Böttcher coordinate `φ` that is
analytic on the escape set, the level-`t` point `Work.EL.rayPt hN θ t` of the dynamic ray of
angle `θ` — a priori only defined for real levels `t > 1` — extends to a holomorphic,
injective function `F` of the complex level on the exterior disc `{z : 1 < ‖z‖}`.

The extension is the composition of the inverse Böttcher coordinate with the fixed rotation
`u ↦ u * exp (2πiθ)`: if `s = exp (2πiθ)` (of modulus `1`) then

`F u = Work.ELRig.invBottcher hN (u * s)`.

`invBottcher hN` is analytic on the exterior disc (`Work.ELRig.analyticAt_invBottcher`, using
`han`), hence so is `F`; multiplication by the unit `s` is injective, and `invBottcher hN` is
injective on the exterior disc because it is a right inverse of `φ`
(`Work.ELRig.invBottcher_spec`).  Finally for real `t > 1` we have
`F t = invBottcher hN (rayPoint θ t) = rayPt hN θ t`
(`Work.ELRig.invBottcher_rayPoint`). -/
theorem rayPt_complex_extension {c : ℂ} {φ : ℂ → ℂ} (hN : Work.EL.DynB c φ)
    (han : AnalyticOnNhd ℂ φ (Work.Bottcher.EscapeSet c)) (θ : ℝ) :
    ∃ F : ℂ → ℂ, DifferentiableOn ℂ F {z : ℂ | 1 < ‖z‖} ∧ Set.InjOn F {z : ℂ | 1 < ‖z‖} ∧
      (∀ t : ℝ, 1 < t → F (t : ℂ) = Work.EL.rayPt hN θ t) := by
  -- the unit complex number carrying the angle
  set s : ℂ := Complex.exp (2 * (Real.pi : ℂ) * (θ : ℂ) * Complex.I) with hs
  have hsnorm : ‖s‖ = 1 := by
    rw [hs, Complex.norm_exp]; simp
  -- multiplication by `s` preserves the modulus, hence the exterior disc
  have hsmul : ∀ u : ℂ, ‖u * s‖ = ‖u‖ := by
    intro u; rw [norm_mul, hsnorm, mul_one]
  have hsne : s ≠ 0 := by
    intro h; rw [h, norm_zero] at hsnorm; linarith
  refine ⟨fun u => Work.ELRig.invBottcher hN (u * s), ?_, ?_, ?_⟩
  · -- holomorphy of the extension
    have hinv : AnalyticOnNhd ℂ (Work.ELRig.invBottcher hN) {w : ℂ | 1 < ‖w‖} :=
      fun w hw => Work.ELRig.analyticAt_invBottcher hN han hw
    have hmul : DifferentiableOn ℂ (fun u : ℂ => u * s) {u : ℂ | 1 < ‖u‖} :=
      (differentiable_id.mul_const s).differentiableOn
    exact hinv.differentiableOn.comp hmul (fun u hu => by
      simp only [Set.mem_ofPred_eq, hsmul u] at *; exact hu)
  · -- injectivity
    have hinj : Set.InjOn (Work.ELRig.invBottcher hN) {w : ℂ | 1 < ‖w‖} := by
      intro w hw w' hw' h
      rw [← (Work.ELRig.invBottcher_spec hN hw).2, ← (Work.ELRig.invBottcher_spec hN hw').2, h]
    intro u hu u' hu' h
    refine mul_right_cancel₀ hsne (hinj ?_ ?_ h)
    · simp only [Set.mem_ofPred_eq, hsmul u] at hu ⊢; exact hu
    · simp only [Set.mem_ofPred_eq, hsmul u'] at hu' ⊢; exact hu'
  · -- agreement with the ray on real levels
    intro t ht
    rw [Work.ELRig.invBottcher_rayPoint hN ht]
    congr 1

end Work.ELRig.RayPtC
