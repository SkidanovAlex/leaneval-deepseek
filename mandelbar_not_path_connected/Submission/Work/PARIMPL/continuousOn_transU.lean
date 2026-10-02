/-
Copyright: subproject `Submission/Work/PARIMPL/` of `mandelbar_not_path_connected`.

# `Work.PARIMPL.continuousOn_transU` — the continuity of the transit coordinate

`Work.PARIMPL.TransitData.cont` (the `TransitData` field of
`Submission/Work/PARIMPL/NOTES.md` §4, carried as the field `cont` of
`Work.PARIMPL.TransitData`) asks for the continuity of the transit coordinate
`transU P n c = −Ũ_c(u_c((F c)^[n] c))` on `P.Nm ∩ ball c₀ ρ₁`.

This file proves it from the two **slit-plane** hypotheses that the design's window argument
supplies:

* `hslit₁`: the Möbius coordinate `m_{a_c}(ζ_c)` of the entry point lies in the slit plane —
  this makes the inner `log` of `𝐞calCoord` a continuous branch **and** excludes its poles
  `ζ_c = ±a_c` (a point of the slit plane is nonzero, and `m_a ζ = 0` iff `ζ = ±a`);
* `hslit₂`: `sinh (a_c·u_c)/a_c` lies in the slit plane — the corresponding statement for the
  outer `log` of `approxEcal`.

Everything else is the continuity furnished by `ParNormal`: `c ↦ a c` on `Nm`
(`ParNormal.continuousOn_a_Nm` — this is the *only* place the implosion side is used, since `a`
has monodromy `−1` around the parabolic locus `Par`), `c ↦ κ c`, `c ↦ m c`, `c ↦ s c` on the
parameter ball, and `c ↦ (F c)^[n] c` (`Work.PARIMPL.continuousOn_entryPt`, which is global).
-/
import Mathlib
import Submission.Work.PARIMPL.Basic
import Submission.Work.PARIMPL.Match
import Submission.Work.PARIMPL.Transit

-- Lean v4.35.0-rc3 / Mathlib 5e0c4e5 made `isDefEq` respect transparency when unifying instances; with it,
-- `ZMod.instField` and `ZMod.commRing` (and `Neg (ZMod p)` via `SubtractionMonoid`) no longer unify, which
-- breaks `ring`/`rw`/module-instance search on `ZMod p`. Restore the v4.34 behaviour for this file.
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false


set_option linter.unusedVariables false

namespace Work.PARIMPL

open Classical Filter Set Metric
open scoped Topology

/-- **Continuity of the transit coordinate.**  On the implosion side intersected with a ball
around the root parameter, the transit coordinate `transU P n c = −Ũ_c(u_c((F c)^[n] c))` is
continuous, provided the two logarithmic arguments of the construction stay on the slit plane
(the branch conditions supplied by the window membership `MatchData.entering`).

Concretely, `transU P n c` is the composite

`c ↦ a c`, `c ↦ κ c`, `c ↦ ζ_c = (z_c − m c)/s c`, `ζ ↦ log (m_{a_c} ζ)/(2a_c)`,
`u ↦ u + πi/a_c`, `u ↦ u + κ c · log (sinh (a_c u)/a_c)`, `x ↦ −x`,

and each step is continuous: the divisions by `a c` and `s c` are legitimate because on `Nm` we
have `a c = i·λ_c` with `λ_c > 0`, while the two `log`s are continuous branches on the slit plane
by `Complex.continuousAt_clog` (`ContinuousOn.clog`). -/
theorem continuousOn_transU {c₀ : ℂ} {d : Work.EL.RootParabolic c₀} (P : Work.PARIMPL.ParNormal d) (n : ℕ) {ρ₁ : ℝ} (hρ₁ : 0 < ρ₁) (hslit₁ : ∀ c ∈ P.Nm ∩ Metric.ball c₀ ρ₁, Work.Implosion.mobius (P.a c) (Work.PARIMPL.chartZeta P c (Work.PARIMPL.entryPt P n c)) ∈ Complex.slitPlane) (hslit₂ : ∀ c ∈ P.Nm ∩ Metric.ball c₀ ρ₁, Complex.sinh (P.a c * Work.PARIMPL.ecalUin P c (Work.PARIMPL.entryPt P n c)) / P.a c ∈ Complex.slitPlane) : ContinuousOn (Work.PARIMPL.transU P n) (P.Nm ∩ Metric.ball c₀ ρ₁) := by
  let s : Set ℂ := P.Nm ∩ Metric.ball c₀ ρ₁
  -- the two monotonicity facts: `Nm ⊆ ball c₀ ρ₀`, and `Nm` carries the continuity of `a`
  have hsNm : s ⊆ P.Nm := fun c hc => hc.1
  have hsball : s ⊆ Metric.ball c₀ P.ρ₀ := fun c hc => hc.1.1
  -- `c ↦ a c` is continuous on `Nm` (and `a c ≠ 0` there, since `a c = i·λ c`, `λ c > 0`)
  have hA : ContinuousOn (fun c => P.a c) s := P.continuousOn_a_Nm.mono hsNm
  have hAne : ∀ c ∈ s, P.a c ≠ 0 := by
    intro c hc
    rw [P.a_of_mem_Nm (hsNm hc)]
    exact mul_ne_zero
      (Complex.ofReal_ne_zero.mpr (ne_of_gt (P.lam_pos_of_mem_Nm (hsNm hc))))
      Complex.I_ne_zero
  -- the continuity fields of the parameter normal form, restricted to `s`
  have hκ : ContinuousOn P.κ s := P.cont_κ.mono hsball
  have hentry : ContinuousOn (fun c => Work.PARIMPL.entryPt P n c) s :=
    (Work.PARIMPL.continuousOn_entryPt P n).mono hsball
  have hm : ContinuousOn P.m s := P.cont_m.mono hsball
  have hsc : ContinuousOn P.s s := P.cont_s.mono hsball
  have hsne : ∀ c ∈ s, P.s c ≠ 0 := fun c hc => P.s_ne c (hsball hc)
  -- the chart coordinate `ζ c = (z c − m c)/s c`
  have hζ : ContinuousOn (fun c => Work.PARIMPL.chartZeta P c (Work.PARIMPL.entryPt P n c)) s := by
    simp only [Work.PARIMPL.chartZeta]
    exact (hentry.sub hm).div hsc hsne
  -- `hslit₁` is nonzero, hence the denominator `ζ c − a c` of the Möbius map does not vanish
  have hden : ∀ c ∈ s, Work.PARIMPL.chartZeta P c (Work.PARIMPL.entryPt P n c) - P.a c ≠ 0 := by
    intro c hc h0
    have hne := Complex.slitPlane_ne_zero (hslit₁ c hc)
    simp only [Work.Implosion.mobius] at hne
    rw [h0, div_zero] at hne
    exact hne rfl
  -- the Möbius coordinate `c ↦ m_{a c}(ζ c)` and its logarithm
  have hmob : ContinuousOn (fun c => Work.Implosion.mobius (P.a c)
      (Work.PARIMPL.chartZeta P c (Work.PARIMPL.entryPt P n c))) s := by
    simp only [Work.Implosion.mobius]
    exact (hζ.add hA).div (hζ.sub hA) hden
  have hlog1 : ContinuousOn (fun c => Complex.log (Work.Implosion.mobius (P.a c)
      (Work.PARIMPL.chartZeta P c (Work.PARIMPL.entryPt P n c)))) s :=
    hmob.clog hslit₁
  -- the Écalle coordinate `u(ζ c) = log (m_{a c} ζ c)/(2 a c)`
  have hEcal : ContinuousOn (fun c => Work.Implosion.ecalCoord (P.a c)
      (Work.PARIMPL.chartZeta P c (Work.PARIMPL.entryPt P n c))) s := by
    simp only [Work.Implosion.ecalCoord]
    exact hlog1.div (continuousOn_const.mul hA)
      (fun c hc => mul_ne_zero two_ne_zero (hAne c hc))
  -- the incoming lift `u_c + πi/a_c`
  have hconst : ContinuousOn (fun _ : ℂ => (Real.pi : ℂ) * Complex.I) s :=
    continuousOn_const.mul continuousOn_const
  have hUin : ContinuousOn (fun c => Work.PARIMPL.ecalUin P c (Work.PARIMPL.entryPt P n c)) s := by
    simp only [Work.PARIMPL.ecalUin, Work.PARIMPL.ecalU]
    exact hEcal.add (hconst.div hA hAne)
  -- the argument `sinh (a c · u c)/a c` of the outer logarithm
  have hSinh : ContinuousOn (fun c => Complex.sinh (P.a c * Work.PARIMPL.ecalUin P c
      (Work.PARIMPL.entryPt P n c)) / P.a c) s :=
    (Complex.continuous_sinh.comp_continuousOn (hA.mul hUin)).div hA hAne
  have hlog2 : ContinuousOn (fun c => Complex.log (Complex.sinh (P.a c *
      Work.PARIMPL.ecalUin P c (Work.PARIMPL.entryPt P n c)) / P.a c)) s :=
    hSinh.clog hslit₂
  -- the approximate coordinate `Ũ_c(u_c z) = u_c z + κ c · log (sinh (a c · u_c z)/a c)`
  have hmain : ContinuousOn (fun c => Work.PARIMPL.approxUin P c (Work.PARIMPL.entryPt P n c)) s := by
    simp only [Work.PARIMPL.approxUin, Work.Implosion.approxEcal]
    exact hUin.add (hκ.mul hlog2)
  -- and the transit coordinate is its negative
  change ContinuousOn (fun c => -Work.PARIMPL.approxUin P c (Work.PARIMPL.entryPt P n c)) s
  exact hmain.neg

end Work.PARIMPL
