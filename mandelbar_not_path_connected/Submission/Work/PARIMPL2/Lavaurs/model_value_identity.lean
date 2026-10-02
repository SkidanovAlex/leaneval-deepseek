import Mathlib
import Submission.Work.PARIMPL2.Lavaurs.Defs

-- Lean v4.35.0-rc3 / Mathlib 5e0c4e5 made `isDefEq` respect transparency when unifying instances; with it,
-- `ZMod.instField` and `ZMod.commRing` (and `Neg (ZMod p)` via `SubtractionMonoid`) no longer unify, which
-- breaks `ring`/`rw`/module-instance search on `ZMod p`. Restore the v4.34 behaviour for this file.
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false


set_option linter.unusedVariables false

namespace Work.PARIMPL2.Lavaurs

/-- **The model value at the limit point `ζ₀`.**  With `ζ₀ = chartZeta P c₀ z = (z − d.z₁)/P.s c₀`
(so `ζ₀ = −1/w0 P z`) and `c ∈ P.Nm`, the branch-free incoming model value

  `M(ζ) = π/λ_c + 1/ζ − κ_c·log(−ζ)`

evaluated at `ζ₀` differs from the model value `π/λ_c − approxCoord κ₀ (w0 P z)` of the incoming
window (`approxCoord κ w = w − κ log w`) exactly by `(κ_c − κ₀)·log(w0 P z)`.

Uses `P.m c₀ = d.z₁` and `P.s c₀ ≠ 0`; the branch identity `log(−ζ₀) = −log(w0 P z)` holds because
`Re (w0 P z) ≥ R ≥ 8 > 0` on `WinG` (so `w0 P z` is in the slit plane), which is why the window
hypothesis is needed. -/
theorem model_value_identity {c₀ : ℂ} {d : Work.EL.RootParabolic c₀}
    (P : Work.PARIMPL.ParNormal d) (R H : ℝ)
    (hH : R ≥ 8 * (H + 1)) {c : ℂ} (hc : c ∈ P.Nm) {z : ℂ}
    (hz : z ∈ Work.PARIMPL2.WinG P R H) :
    ((Real.pi / P.lam c : ℝ) : ℂ) + 1 / Work.PARIMPL.chartZeta P c₀ z
        - P.κ c * Complex.log (-(Work.PARIMPL.chartZeta P c₀ z))
      = ((Real.pi / P.lam c : ℝ) : ℂ)
        - Work.FatouCoord.approxCoord (P.κ c₀) (Work.PARIMPL2.w0 P z)
        + (P.κ c - P.κ c₀) * Complex.log (Work.PARIMPL2.w0 P z) := by
  obtain ⟨hz1, hre, him⟩ := hz
  -- The imaginary bound forces `H ≥ 0`, hence `R ≥ 8 > 0`, so `Re (w0 P z) > 0`.
  have hH0 : 0 ≤ H := le_trans (abs_nonneg _) him
  have hR8 : 8 ≤ R := by linarith [hH, hH0]
  have hw0re : 0 < (Work.PARIMPL2.w0 P z).re := by linarith [hre.1]
  -- `chartZeta P c₀ z = -1/(w0 P z)`.
  have hchart : Work.PARIMPL.chartZeta P c₀ z = -(Work.PARIMPL2.w0 P z)⁻¹ := by
    have hs : P.s c₀ ≠ 0 := P.s_ne c₀ (Metric.mem_ball_self P.hρ₀)
    have hz1' : z - d.z₁ ≠ 0 := sub_ne_zero.mpr hz1
    rw [Work.PARIMPL.chartZeta, P.m₀, Work.PARIMPL2.w0]
    field_simp
  -- `1/(chartZeta P c₀ z) = -(w0 P z)`.
  have hinv : 1 / Work.PARIMPL.chartZeta P c₀ z = -(Work.PARIMPL2.w0 P z) := by
    have hs : P.s c₀ ≠ 0 := P.s_ne c₀ (Metric.mem_ball_self P.hρ₀)
    have hz1' : z - d.z₁ ≠ 0 := sub_ne_zero.mpr hz1
    rw [Work.PARIMPL.chartZeta, P.m₀, Work.PARIMPL2.w0]
    field_simp
  -- The branch identity `log(-ζ₀) = -log(w0 P z)`: `-ζ₀ = (w0 P z)⁻¹` and `w0 P z` is in the
  -- slit plane (`0 < Re (w0 P z)`, so `arg ≠ π`).
  have hlog : Complex.log (-(Work.PARIMPL.chartZeta P c₀ z))
      = -Complex.log (Work.PARIMPL2.w0 P z) := by
    rw [hchart, neg_neg]
    exact Complex.log_inv _ (by
      have hlt : |(Work.PARIMPL2.w0 P z).arg| < Real.pi / 2 :=
        Complex.abs_arg_lt_pi_div_two_iff.mpr (Or.inl hw0re)
      intro hcon
      rw [hcon, abs_of_pos Real.pi_pos] at hlt
      linarith [Real.pi_pos])
  rw [hinv, hlog, Work.FatouCoord.approxCoord]
  ring

end Work.PARIMPL2.Lavaurs
