/-
# `Work.PARIMPL.ParSplit.parChartSq`

The final algebraic identity of the parameter normal-form chart: on a small ball around `c₀` the
chart scale `s = parS S c` does not vanish and

  `(s · a)² = Gc`,   `a = parA S c` the chosen square root of `parA2 = σ · ‖Gc‖ · ‖ρ‖²`.

The mathematical content is small, but the degenerate locus matters: `Gc` **vanishes on a real
curve through `c₀`** (the collision locus of the two split fixed points), so the identity
`parLam = σ · Gc/‖Gc‖` of `parLam_eq` is only available off that curve; multiplying the
denominator back gives `parLam · σ · ‖Gc‖ = Gc` *everywhere* (`Gc` also on the curve, where both
sides vanish), and that is the form in which the wall identity is used below.

The three nonvanishing/identity inputs are

* `parH_ne_zero`  : `parH`, hence `parLam = conj parH`, does not vanish near `c₀`
  (at `c₀` it collapses to `G_{c₀}'(z₁)`, a unit complex number);
* `parRho_ne_zero`: `parRho = R_c(m c) = (F c)''(m c)/2 ≠ 0` near `c₀`
  (simplicity of the parabolic fixed point);
* `parLam_sigma_norm_Gc`: the denominator-cleared wall identity `parLam · σ · ‖Gc‖ = Gc`.

Everything else is the elementary algebra

  `s² = parLam / ‖ρ‖²`   (`parU0² = parLam · ρ²/‖ρ‖²` and `s = parU0/parRho`),
  `a² = parA2`           (`realSqrt` really is a square root).

All lemmas below are stated with their own explicit binders, so this module is self-contained
apart from `ParWall` (definitions), `parRho_ne_zero`, `parH_ne_zero` and `parLam_sigma_norm_Gc`.
-/
import Mathlib
import Submission.Work.PARIMPL.ParSplit.ParWall
import Submission.Work.PARIMPL.ParSplit.parLam_eq
import Submission.Work.PARIMPL.ParSplit.parRho_ne_zero
import Submission.Work.PARIMPL.ParSplit.parH_ne_zero
import Submission.Work.PARIMPL.ParSplit.parLam_sigma_norm_Gc

-- Lean v4.35.0-rc3 / Mathlib 5e0c4e5 made `isDefEq` respect transparency when unifying instances; with it,
-- `ZMod.instField` and `ZMod.commRing` (and `Neg (ZMod p)` via `SubtractionMonoid`) no longer unify, which
-- breaks `ring`/`rw`/module-instance search on `ZMod p`. Restore the v4.34 behaviour for this file.
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false


set_option autoImplicit false
set_option linter.unusedVariables false

open Classical Filter Set Metric
open scoped Topology

noncomputable section

namespace Work.PARIMPL.ParSplit

/-! ## Elementary algebra of the chart *-/

/-- `Complex.sqrt` really is a square root (it is `z ^ (2⁻¹ : ℂ)`). -/
theorem chartSqrt_sq (z : ℂ) : (Complex.sqrt z) ^ 2 = z := by
  rw [Complex.sqrt]
  exact Complex.cpow_nat_inv_pow z (by norm_num)

/-- `u₀ ^ 2 = parLam · ρ² / ‖ρ‖²`, by definition of `parU0 = √(parLam · ρ²/‖ρ‖²)`. -/
theorem chart_parU0_sq {c₀ : ℂ} {d : Work.EL.RootParabolic c₀} (S : SplitData d) (c : ℂ) :
    (parU0 S c) ^ 2
      = parLam S c * (parRho S c) ^ 2 / (Complex.ofReal ‖parRho S c‖) ^ 2 := by
  unfold parU0
  exact chartSqrt_sq _

/-- `s ^ 2 = parLam / ‖ρ‖²`, the key cancellation of the chart scale. -/
theorem chart_parS_sq {c₀ : ℂ} {d : Work.EL.RootParabolic c₀} (S : SplitData d) (c : ℂ)
    (hρ : parRho S c ≠ 0) :
    (parS S c) ^ 2 = parLam S c / (Complex.ofReal ‖parRho S c‖) ^ 2 := by
  have hρ2 : (parRho S c) ^ 2 ≠ 0 := pow_ne_zero 2 hρ
  have hn : (Complex.ofReal ‖parRho S c‖ : ℂ) ≠ 0 := by
    rw [Complex.ofReal_ne_zero]; exact norm_ne_zero_iff.mpr hρ
  have hn2 : (Complex.ofReal ‖parRho S c‖ : ℂ) ^ 2 ≠ 0 := pow_ne_zero 2 hn
  rw [parS, div_pow, chart_parU0_sq]
  field_simp

/-- The complex form of `parA2`. -/
theorem chart_parA2_coe {c₀ : ℂ} {d : Work.EL.RootParabolic c₀} (S : SplitData d) (c : ℂ) :
    (parA2 S c : ℂ)
      = (parSigma S c : ℂ) * (‖Gc S c‖ : ℂ) * (Complex.ofReal ‖parRho S c‖) ^ 2 := by
  unfold parA2
  push_cast
  ring

/-- `a ^ 2 = parA2`: the chosen square root of `parA2` (real for `parA2 ≥ 0`, purely imaginary
otherwise) really is one.  No sign hypothesis is needed. -/
theorem chart_parA_sq {c₀ : ℂ} {d : Work.EL.RootParabolic c₀} (S : SplitData d) (c : ℂ) :
    (parA S c) ^ 2 = ((parA2 S c : ℝ) : ℂ) := by
  unfold parA
  exact realSqrt_sq _

/-! ## The two quadratic identities -/

/-- `s² · a2 = Gc`, from `parLam · σ · ‖Gc‖ = Gc` and `s² = parLam/‖ρ‖²`. -/
theorem chart_parS_sq_mul_parA2 {c₀ : ℂ} {d : Work.EL.RootParabolic c₀} (S : SplitData d) (c : ℂ)
    (hρ : parRho S c ≠ 0)
    (hmain : parLam S c * (parSigma S c : ℂ) * (‖Gc S c‖ : ℂ) = Gc S c) :
    (parS S c) ^ 2 * (parA2 S c : ℂ) = Gc S c := by
  have hn : (Complex.ofReal ‖parRho S c‖ : ℂ) ≠ 0 := by
    rw [Complex.ofReal_ne_zero]; exact norm_ne_zero_iff.mpr hρ
  have hn2 : (Complex.ofReal ‖parRho S c‖ : ℂ) ^ 2 ≠ 0 := pow_ne_zero 2 hn
  calc (parS S c) ^ 2 * (parA2 S c : ℂ)
      = (parLam S c / (Complex.ofReal ‖parRho S c‖) ^ 2) * (parA2 S c : ℂ) := by
        rw [chart_parS_sq S c hρ]
    _ = (parLam S c / (Complex.ofReal ‖parRho S c‖) ^ 2)
          * ((parSigma S c : ℂ) * (‖Gc S c‖ : ℂ)
              * (Complex.ofReal ‖parRho S c‖) ^ 2) := by rw [chart_parA2_coe S c]
    _ = (parLam S c * (parSigma S c : ℂ) * (‖Gc S c‖ : ℂ))
          * ((Complex.ofReal ‖parRho S c‖) ^ 2 / (Complex.ofReal ‖parRho S c‖) ^ 2) := by
        ring
    _ = Gc S c * 1 := by rw [hmain, div_self hn2]
    _ = Gc S c := by ring

/-- `(s · a)² = Gc`. -/
theorem chart_parS_mul_parA_sq {c₀ : ℂ} {d : Work.EL.RootParabolic c₀} (S : SplitData d) (c : ℂ)
    (h2 : (parS S c) ^ 2 * (parA2 S c : ℂ) = Gc S c) :
    (parS S c * parA S c) ^ 2 = Gc S c := by
  calc (parS S c * parA S c) ^ 2 = (parS S c) ^ 2 * (parA S c) ^ 2 := by rw [mul_pow]
    _ = (parS S c) ^ 2 * (parA2 S c : ℂ) := by rw [chart_parA_sq]
    _ = Gc S c := h2

/-- `s ≠ 0`, from `parLam ≠ 0` and `parRho ≠ 0`. -/
theorem chart_parS_ne_zero {c₀ : ℂ} {d : Work.EL.RootParabolic c₀} (S : SplitData d) (c : ℂ)
    (hρ : parRho S c ≠ 0) (hlam : parLam S c ≠ 0) : parS S c ≠ 0 := by
  have hn : (Complex.ofReal ‖parRho S c‖ : ℂ) ≠ 0 := by
    rw [Complex.ofReal_ne_zero]; exact norm_ne_zero_iff.mpr hρ
  have hs2 : (parS S c) ^ 2 ≠ 0 := by
    rw [chart_parS_sq S c hρ]
    exact div_ne_zero hlam (pow_ne_zero 2 hn)
  intro h
  exact hs2 (by rw [h]; ring)

/-- `parLam ≠ 0 ⟸ parH ≠ 0` (`parLam = conj parH`). -/
theorem chart_parLam_ne_zero_of_parH {c₀ : ℂ} {d : Work.EL.RootParabolic c₀} {S : SplitData d}
    {c : ℂ} (h : parH S c ≠ 0) : parLam S c ≠ 0 := by
  intro hz
  apply h
  have := congrArg star hz
  simpa [parLam] using this

/-! ## The target -/

theorem parChartSq {c₀ : ℂ} {d : Work.EL.RootParabolic c₀}
    (S : Work.PARIMPL.ParSplit.SplitData d) :
    ∃ ρ' > 0, ρ' ≤ S.ρ ∧ ∀ c ∈ Metric.ball c₀ ρ',
      Work.PARIMPL.ParSplit.parS S c ≠ 0 ∧
      (Work.PARIMPL.ParSplit.parS S c * Work.PARIMPL.ParSplit.parA S c) ^ 2
        = Work.PARIMPL.ParSplit.Gc S c := by
  obtain ⟨ρ₁, hρ₁0, hρ₁ρ, h₁⟩ := parH_ne_zero S
  obtain ⟨ρ₂, hρ₂0, hρ₂ρ, h₂⟩ := parRho_ne_zero S
  obtain ⟨ρ₃, hρ₃0, hρ₃ρ, h₃⟩ := parLam_sigma_norm_Gc S
  have hle₁ : min (min ρ₁ ρ₂) ρ₃ ≤ ρ₁ := le_trans (min_le_left _ _) (min_le_left _ _)
  have hle₂ : min (min ρ₁ ρ₂) ρ₃ ≤ ρ₂ := le_trans (min_le_left _ _) (min_le_right _ _)
  have hle₃ : min (min ρ₁ ρ₂) ρ₃ ≤ ρ₃ := min_le_right _ _
  refine ⟨min (min ρ₁ ρ₂) ρ₃, lt_min (lt_min hρ₁0 hρ₂0) hρ₃0, le_trans hle₁ hρ₁ρ, ?_⟩
  intro c hc
  have hc₁ : c ∈ Metric.ball c₀ ρ₁ := Metric.ball_subset_ball hle₁ hc
  have hc₂ : c ∈ Metric.ball c₀ ρ₂ := Metric.ball_subset_ball hle₂ hc
  have hc₃ : c ∈ Metric.ball c₀ ρ₃ := Metric.ball_subset_ball hle₃ hc
  have hρ : parRho S c ≠ 0 := h₂ c hc₂
  have hlam : parLam S c ≠ 0 := chart_parLam_ne_zero_of_parH (h₁ c hc₁)
  have hmain : parLam S c * (parSigma S c : ℂ) * (‖Gc S c‖ : ℂ) = Gc S c := h₃ c hc₃
  exact ⟨chart_parS_ne_zero S c hρ hlam,
    chart_parS_mul_parA_sq S c (chart_parS_sq_mul_parA2 S c hρ hmain)⟩

end Work.PARIMPL.ParSplit
