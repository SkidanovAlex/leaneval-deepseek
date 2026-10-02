import Mathlib
import Submission.Work.FlowerGlue2.Defs
import Submission.Work.FlowerGlue2.parabolicBounds_c0
import Submission.Work.FlowerGlue2.h_c0_differentiableOn
import Submission.Work.FlowerGlue2.isRepellingCoord_transfer
import Submission.Work.FlowerGlue2.exists_rep_inverse_diag
import Submission.Work.FlowerGlue2.repNorm_of_diag_inverse

-- Lean v4.35.0-rc3 / Mathlib 5e0c4e5 made `isDefEq` respect transparency when unifying instances; with it,
-- `ZMod.instField` and `ZMod.commRing` (and `Neg (ZMod p)` via `SubtractionMonoid`) no longer unify, which
-- breaks `ring`/`rw`/module-instance search on `ZMod p`. Restore the v4.34 behaviour for this file.
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false


/-!
# `Work.FlowerGlue2.isRepellingCoord_ref`

The *reference repelling coordinate* of the implosion comparison, in the form the exit step
(`Work.PARIMPL2.Lavaurs.lockstep_complex` and the `L4` assembly) consumes it: a single function
`Ψ₁` with

* `Work.FatouCoord.IsRepellingCoord (Work.PARIMPL.Ft c₀) d.z₁ R₁ Ψ₁` — `Ψ₁` is a repelling
  coordinate at the parabolic point, on the far-left half-plane `{Re < -R₁}`;
* *surjectivity onto the Stolz petal*: every `z` of the petal `Dst P R₂` is the image under
  `Ψ₁` of a point of the deep half-plane `{Re < -R₁ - 2}` (this is the hypothesis `hsurj` of
  `Work.FlowerGlue2.rep_unique_backward`, which identifies `Ψ₁` with the flower's own repelling
  coordinate up to a shift);
* `Work.PARIMPL2.Lavaurs.RepNorm P Ψ₁` — the repelling normalisation bundle `N2` (the
  quantitative preimage of the outgoing window).

## The construction

`Ψ₁` is the *transfer form* of the repelling conjugacy `V` of the germ at `c₀`:
`Ψ₁ w = d.z₁ + P.s c₀ * (-1 / V w)`, where `V w = w + (1 - h₁ c₀) Λ w + Z w` solves
`V (w+1) = wMap f (V w)` with the fine decay `‖Z w‖ ≤ K (1 + log ‖w‖)/‖w‖`
(`Work.FlowerGlue2.exists_conjugacy_Z_fine`).  All three conjuncts are properties of that `V`:

* `IsRepellingCoord`: `Work.FlowerGlue2.isRepellingCoord_transfer`, applied to the chart
  conjugacy `Work.FlowerGlue2.ft_chart_ref`
  (`Ft c₀ (d.z₁ + P.s c₀ ζ) = d.z₁ + P.s c₀ (ζ + ζ² P.h c₀ ζ)`, from `ParNormal.conj` with
  `a c₀ = 0`);
* surjectivity: the inversion of `V` on the Stolz sector, in the *diagonal* form
  `Work.FlowerGlue2.exists_rep_inverse_diag` (the threshold `R₂` is chosen as `2R₁` times the
  absolute threshold of that statement), together with `Work.FlowerGlue2.chart_recovery`
  (`z = d.z₁ - P.s c₀ / w0 P z`);
* `RepNorm`: `Work.FlowerGlue2.repNorm_of_diag_inverse`, the estimate of
  `Work.FlowerGlue2.rep_norm_transfer_stolz` fed by the same diagonal inverse.

The diagonal (rather than half-plane) shape of the inverse is what makes the `RepNorm` conjunct
provable without any hypothesis on the sign of `Re (P.κ c₀)`: `RepNorm` needs the preimage of a
window point of depth `-Re w ∈ [R, R+2]` only at depth `< -R/2`, and the diagonal statement
delivers it with `R₁ := R/2 - 2`.
-/

namespace Work.FlowerGlue2

open Filter Set Metric
open scoped Topology

variable {c₀ : ℂ} {d : Work.EL.RootParabolic c₀}

/-- **The chart conjugacy at the parabolic parameter**, in the form consumed by the transfer
statement: for `‖ζ‖ < P.r`, `Ft c₀ (d.z₁ + P.s c₀·ζ) = d.z₁ + P.s c₀·(ζ + ζ²·h c₀ ζ)`. -/
theorem ft_chart_ref (P : Work.PARIMPL.ParNormal d) {ζ : ℂ} (hζ : ‖ζ‖ < P.r) :
    Work.PARIMPL.Ft c₀ (d.z₁ + P.s c₀ * ζ) = d.z₁ + P.s c₀ * (ζ + ζ ^ 2 * P.h c₀ ζ) := by
  have hmem : c₀ ∈ Metric.ball c₀ P.ρ₀ := Metric.mem_ball_self P.hρ₀
  have ha : P.a c₀ = 0 := by
    have h := P.a_sq c₀ hmem
    rw [P.a2₀] at h
    have h' : P.a c₀ * P.a c₀ = 0 := by simpa [pow_two] using h
    exact mul_self_eq_zero.mp h'
  have hconj := P.conj c₀ hmem ζ (by simpa using hζ)
  rw [P.m₀, ha] at hconj
  rw [show Work.Implosion.normalForm (0 : ℂ) (P.h c₀) ζ = ζ + ζ ^ 2 * P.h c₀ ζ by
        simp [Work.Implosion.normalForm]] at hconj
  exact hconj

/-- **The reference repelling coordinate** `isRepellingCoord_ref`: one function `Ψ₁` which is a
repelling coordinate at `d.z₁`, surjects the deep half-plane onto the Stolz petal `Dst P R₂`,
and satisfies the repelling normalisation `N2`. -/
theorem isRepellingCoord_ref {c₀ : ℂ} {d : Work.EL.RootParabolic c₀} (P : Work.PARIMPL.ParNormal d)
    (hτ : P.h c₀ 0 = 1) :
    ∃ R₁ : ℝ, ∃ Ψ₁ : ℂ → ℂ,
      Work.FatouCoord.IsRepellingCoord (Work.PARIMPL.Ft c₀) d.z₁ R₁ Ψ₁ ∧
      (∃ R₂ : ℝ, ∀ z ∈ Work.FlowerGlue2.Dst P R₂,
        ∃ w' : ℂ, w'.re < -R₁ - 2 ∧ Ψ₁ w' = z) ∧
      Work.PARIMPL2.Lavaurs.RepNorm P Ψ₁ := by
  have hb := parabolicBounds_c0 P hτ (h_c0_differentiableOn P)
  obtain ⟨R₀, hR₀pos, Z, V, hVdiff, hVdef, hVshift, hVinj, hVclose, K, hKpos, hVinv⟩ :=
    exists_rep_inverse_diag hb
  set R₁ : ℝ := max R₀ (max (R₀ + 1) (max 1 (2 / P.r + 1))) with hR₁def
  have hR₁R₀ : R₀ ≤ R₁ := le_max_left _ _
  have hR₁R₀1 : R₀ + 1 ≤ R₁ := le_trans (le_max_left _ _) (le_max_right _ _)
  have hR₁one : 1 ≤ R₁ :=
    le_trans (le_max_left _ _) (le_trans (le_max_right _ _) (le_max_right _ _))
  have h2r : 2 / P.r < R₁ := by
    have h1 : 2 / P.r < 2 / P.r + 1 := by linarith
    have h2 : 2 / P.r + 1 ≤ R₁ :=
      le_trans (le_max_right _ _) (le_trans (le_max_right _ _) (le_max_right _ _))
    linarith
  have hR₁p3 : R₀ - 3 ≤ R₁ := by linarith
  refine ⟨R₁, fun w => d.z₁ + P.s c₀ * (-1 / V w), ?_, ?_, ?_⟩
  · -- `Ψ₁` is a repelling coordinate at `d.z₁`
    exact isRepellingCoord_transfer (P.s_ne c₀ (Metric.mem_ball_self P.hρ₀)) P.hr hR₁one
      hR₁R₀1 h2r (fun ζ hζ => ft_chart_ref P hζ) hVdiff hVshift hVinj hVclose
  · -- the deep half-plane surjects onto the Stolz petal `Dst P R₂`
    refine ⟨max (2 * R₁) R₀, ?_⟩
    intro z hz
    rw [mem_Dst] at hz
    obtain ⟨hz1, hzre, hzim⟩ := hz
    have hmax : max (2 * R₁) R₀ ≤ -((w0 P z).re) := by linarith
    have h2R₁ : 2 * R₁ ≤ -((w0 P z).re) := le_trans (le_max_left _ _) hmax
    have hR₀le : R₀ ≤ -((w0 P z).re) := le_trans (le_max_right _ _) hmax
    obtain ⟨v, hvdeep, hVv, -⟩ := hVinv R₁ (w0 P z) hR₁p3 h2R₁ hR₀le hzim
    refine ⟨v, hvdeep, ?_⟩
    have hz' : z = d.z₁ + P.s c₀ * (-1 / w0 P z) := by
      conv_lhs => rw [chart_recovery (P := P) hz1]
      ring_nf
    change d.z₁ + P.s c₀ * (-1 / V v) = z
    rw [hVv]
    exact hz'.symm
  · -- the repelling normalisation `N2`, fed by the same diagonal inverse
    exact repNorm_of_diag_inverse (V := V) (R₀ := R₀) (K₀ := K) P hτ hR₀pos hKpos hVinv

end Work.FlowerGlue2
