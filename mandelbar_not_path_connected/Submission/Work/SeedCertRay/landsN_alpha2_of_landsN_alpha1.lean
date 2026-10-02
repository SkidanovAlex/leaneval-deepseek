/-
# `landsN_alpha2_of_landsN_alpha1` — `α₂` lands wherever `α₁` does

The angle-doubling map `Work.EL.T θ = Int.fract (-2θ)` of the antiholomorphic quadratic
family sends the first root-portrait angle to the second after five steps,

`T^[5] α₁ = α₂`   (`371/1023 ↦ 281/1023 ↦ 461/1023 ↦ 101/1023 ↦ 821/1023 ↦ 404/1023`),

so on the dynamical side the five-fold iterate `(T_c)^[5]` carries the ray of angle `α₁` to
the ray of angle `α₂`.  Landing is natural under that iterate
(`Work.ELTop.landsN_map`, iterated: `landsN_map_iterate`), and at the characteristic point of
the root portrait the iterate fixes the point (`hg`).  Hence a landing of `R(α₁)` at `z₁`
forces a landing of `R(α₂)` at `z₁`, which is exactly the "`α₂` follows by `T⁵`" step of the
certified-seed argument (`NOTES_LEAD_mandelbar_noncusp.md`, §2.5).
-/
import Mathlib
import Submission.Work.SeedCertRay.Basic

-- Lean v4.35.0-rc3 / Mathlib 5e0c4e5 made `isDefEq` respect transparency when unifying instances; with it,
-- `ZMod.instField` and `ZMod.commRing` (and `Neg (ZMod p)` via `SubtractionMonoid`) no longer unify, which
-- breaks `ring`/`rw`/module-instance search on `ZMod p`. Restore the v4.34 behaviour for this file.
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false


namespace Work.SeedCertRay

open LeanEval.ComplexAnalysis (Tantibar Mandelbar)

/-- **Landing is natural under the iterates of `T_c`.**  If the ray of angle `θ` lands at `y`,
then the ray of angle `T^[n] θ` lands at `(T_c)^[n] y`.  Immediate by induction from
`Work.ELTop.landsN_map`. -/
theorem landsN_map_iterate {c : ℂ} {φ : ℂ → ℂ} (hN : Work.EL.DynB c φ)
    (hφ : Work.ParamRays.IsDynBottcher c φ) (n : ℕ) {θ : ℝ} {y : ℂ}
    (h : Work.EL.LandsN hN θ y) :
    Work.EL.LandsN hN ((Work.EL.T)^[n] θ) ((Tantibar c)^[n] y) := by
  induction n with
  | zero => simpa using h
  | succ n ih =>
    rw [Function.iterate_succ_apply', Function.iterate_succ_apply']
    exact Work.ELTop.landsN_map hN hφ ih

theorem landsN_alpha2_of_landsN_alpha1 {c : ℂ} {φ : ℂ → ℂ} (hN : Work.EL.DynB c φ) (hφ : Work.ParamRays.IsDynBottcher c φ) {z₁ : ℂ} (hg : (LeanEval.ComplexAnalysis.Tantibar c)^[5] z₁ = z₁) (h₁ : Work.EL.LandsN hN Work.EL.alpha1 z₁) : Work.EL.LandsN hN Work.EL.alpha2 z₁ := by
  -- `T^[5] α₁ = α₂`, the arithmetic of the root portrait.
  have hT : (Work.EL.T)^[5] Work.EL.alpha1 = Work.EL.alpha2 := by
    norm_num [Work.EL.T, Work.EL.alpha1, Work.EL.alpha2, Function.iterate_succ_apply',
      Function.iterate_zero, Int.fract]
  -- push the landing along the five-fold iterate.
  have h := landsN_map_iterate hN hφ 5 h₁
  rw [hT, hg] at h
  exact h

end Work.SeedCertRay
