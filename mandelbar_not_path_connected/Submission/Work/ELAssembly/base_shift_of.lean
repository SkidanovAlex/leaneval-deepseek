/-
# `base_shift_of`: the level-`0` pair of the `z₁`-nest sits one `F`-step below `T^[4] z₁`

Certificate C5 of the equator-leak argument: the level-`0` pair of the nest at the parabolic
point `z₁` is a pull-back of the root-portrait pair landing at `f⁴ z₁`, i.e.

    F c ((Qp 0).y) = (Tantibar c)^[4] d.z₁,      F c = (Tantibar c)^[10].

Nothing but the *angles* enters: by `Qp_shift`'s mechanism the point `F c ((Qp 0).y)` is the
landing point of the ray of angle `T^[10] (β₀')`, while `(Tantibar c)^[4] d.z₁` is the landing
point of the ray of angle `T^[4] α₁` (the root portrait propagates along the orbit of `z₁`).
The two angles agree,

    T^[10] (β₀') = fract (1024 · β₀') = fract (821/1023 + 404) = 821/1023,
    T^[4] α₁     = fract (16 · α₁)     = fract (821/1023 + 5)   = 821/1023,

because `1024 · β₀' = 414113/1023 = 404 + 821/1023` and `16 · α₁ = 5936/1023 = 5 + 821/1023`
(`β₀' = 414113/1047552`, `α₁ = 371/1023 = 379904/1047552`).  Landing points being unique
(`landsN_unique`), the two are the same point.
-/
import Mathlib
import Submission.Work.ELAssembly.Chains
import Submission.Work.ELNest.Qp_shift
import Submission.Work.ELNest.T_iterate_bAng

-- Lean v4.35.0-rc3 / Mathlib 5e0c4e5 made `isDefEq` respect transparency when unifying instances; with it,
-- `ZMod.instField` and `ZMod.commRing` (and `Neg (ZMod p)` via `SubtractionMonoid`) no longer unify, which
-- breaks `ring`/`rw`/module-instance search on `ZMod p`. Restore the v4.34 behaviour for this file.
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false


namespace Work.ELAssembly

open LeanEval.ComplexAnalysis (Tantibar)

/-- `Work.EL.F` is the tenth iterate of `Tantibar`, as in `Work.ELNest.F_eq_tantibar`. -/
theorem EL_F_eq_tantibar (c : ℂ) : Work.EL.F c = (Tantibar c)^[10] := by
  rw [Work.EL.F, Work.ELNest.Tsq_eq_comp, ← Function.iterate_mul]

/-- **The base shift of the `z₁`-nest (certificate C5).**  The level-`0` pair of the nest is a
pull-back of the root-portrait pair landing at `T^[4] z₁`. -/
theorem base_shift_of {c : ℂ} (d : Work.EL.RootParabolic c) (N : Work.ELAssembly.NestPairs d) :
    Work.EL.F c ((N.Qp 0).y) = (LeanEval.ComplexAnalysis.Tantibar c)^[4] d.z₁ := by
  have hF_eq : Work.EL.F c = (Tantibar c)^[10] := EL_F_eq_tantibar c
  -- the angle arithmetic: `T^[10] β₀' = T^[4] α₁`
  have h1 : Int.fract ((1024 : ℝ) * Work.ELNest.bAng' 0) = 821 / 1023 := by
    have hb : (1024 : ℝ) * Work.ELNest.bAng' 0 = 821 / 1023 + 404 := by
      rw [Work.ELNest.bAng']
      norm_num [Work.ELNest.alpha2, Work.ELNest.beta0']
    rw [hb, Int.fract_eq_iff]
    exact ⟨by norm_num, by norm_num, 404, by push_cast; ring⟩
  have h2 : Int.fract ((16 : ℝ) * Work.EL.alpha1) = 821 / 1023 := by
    have hb : (16 : ℝ) * Work.EL.alpha1 = 821 / 1023 + 5 := by
      norm_num [Work.EL.alpha1]
    rw [hb, Int.fract_eq_iff]
    exact ⟨by norm_num, by norm_num, 5, by push_cast; ring⟩
  have h4 : Work.EL.T^[4] Work.EL.alpha1 = Int.fract ((16 : ℝ) * Work.EL.alpha1) := by
    have h := Work.ELNest.T_iterate_succ 3 Work.EL.alpha1
    norm_num at h
    exact h
  have hang : Work.EL.T^[10] (Work.ELNest.bAng' 0) = Work.EL.T^[4] Work.EL.alpha1 := by
    rw [Work.ELNest.T_iterate_ten, h1, h4, h2]
  -- the level-`0` pair lands at the ray of angle `β₀'`
  have hQ : Work.EL.LandsN d.hN (Work.ELNest.bAng' 0) ((N.Qp 0).y) := by
    rw [← N.Qpa 0]
    exact (N.Qp 0).lands_a
  -- push it forward by `F = (Tantibar c)^[10]`
  have hpush := Work.ELNest.landsN_iterate d.hN d.bottcher 10 hQ
  rw [hang] at hpush
  rw [← hF_eq] at hpush
  -- the right-hand point is the landing point of the ray of angle `T^[4] α₁`
  have hR : Work.EL.LandsN d.hN Work.EL.alpha1 d.z₁ :=
    (Work.ELTop.landsN_iff_landsAt d.hN d.bottcher Work.EL.alpha1 d.z₁).mpr d.rays.1
  have h4' := Work.ELNest.landsN_iterate d.hN d.bottcher 4 hR
  exact Work.ELNest.landsN_unique hpush h4'

end Work.ELAssembly
