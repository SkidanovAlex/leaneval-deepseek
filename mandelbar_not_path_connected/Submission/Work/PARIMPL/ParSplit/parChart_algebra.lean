/-
# `Work.PARIMPL.ParSplit.parChart_algebra`

The *algebra* of the normal-form chart of `ParWall`: with

* `s = parS = parU0 / parRho` the chart scale,
* `a = parA = realSqrt (parA2)` a (real or purely imaginary) square root of
  `parA2 = σ · ‖Gc‖ · ‖parRho‖²`,
* `Gc = (E/2)²` the square of the half-difference of the two split fixed points,
* `σ = parSigma = ±1` the branch sign,

one has, on a ball around `c₀`,

  `s ≠ 0`,   `s² · a2 = Gc`,   `a² = a2`,   `(s · a)² = Gc`,   and  `h 0 = u₀`,

where `h = parHgerm` is the germ of the normal form and `u₀ = parU0` its value at `0`.

The mathematical content is small but the degenerate locus matters: `Gc` *vanishes on a real
curve through `c₀`* (the collision locus of the two split fixed points), so the identity
`parLam = σ · Gc/‖Gc‖` of `parLam_eq` is available only off that curve.  Multiplying the
denominator back gives `parLam · σ · ‖Gc‖ = Gc` *everywhere* (`Gc` also on the curve, where both
sides vanish), and that is exactly the form in which the identity is used below; the identity in
this form is `Work.PARIMPL.ParSplit.parLam_sigma_norm_Gc`.

The two nonvanishing inputs come from sibling modules:
* `parRho_ne_zero` (`parRho_ne_zero.lean`): `parRho = R_c(m c) = (F c)''(m c)/2 ≠ 0` near `c₀`
  (simplicity of the parabolic fixed point),
* `parH_ne_zero` (`parH_ne_zero.lean`): `parH S c₀ = gam S c₀ 1 = (Gpoly c₀)'(z₁) ≠ 0`, because
  `deriv (F c₀) z₁ = 1` forces `(Gpoly c₀)'(z₁) · conj ((Gpoly c₀)'(z₁)) = 1`.

Everything else is the elementary algebra of `Complex.sqrt`, `realSqrt` and the coercions
`ℝ → ℂ`, done in the *degenerate* form in which the wall identities hold: no step divides by
`Gc`, and `parA2` is allowed to have either sign (`realSqrt_sq` holds unconditionally).
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


set_option maxRecDepth 4000
set_option autoImplicit false
set_option linter.unusedVariables false

open Classical Filter Set Metric
open scoped Topology

noncomputable section

namespace Work.PARIMPL.ParSplit

/-! ## Square roots and the sign `σ` -/

/-- `Complex.sqrt` really is a square root (it is `z ^ (2⁻¹ : ℂ)`). -/
theorem sqrt_sq (z : ℂ) : (Complex.sqrt z) ^ 2 = z := by
  rw [Complex.sqrt]
  exact Complex.cpow_nat_inv_pow z (by norm_num)

/-- The branch sign is `±1`. -/
theorem parSigma_sq {c₀ : ℂ} {d : Work.EL.RootParabolic c₀} (S : SplitData d) (c : ℂ) :
    (parSigma S c : ℂ) ^ 2 = 1 := by
  unfold parSigma
  split_ifs <;> norm_num

/-! ## Elementary consequences of the definitions -/

/-- `Rfun S c 0 = parRho S c`: `parRho` is the constant coefficient of `R_c (m c + ·)`. -/
theorem Rfun_zero {c₀ : ℂ} {d : Work.EL.RootParabolic c₀} (S : SplitData d) (c : ℂ) :
    Rfun S c 0 = parRho S c := by
  unfold Rfun parRho
  rw [Finset.sum_eq_single 0]
  · simp
  · intro b _ hb
    rw [zero_pow hb, mul_zero]
  · intro h
    exact absurd (Finset.mem_range.mpr (by norm_num [wallN])) h

/-- `s · ρ = u₀`, i.e. `parS = parU0 / parRho` undone. -/
theorem parS_mul_parRho {c₀ : ℂ} {d : Work.EL.RootParabolic c₀} (S : SplitData d) (c : ℂ)
    (hρ : parRho S c ≠ 0) : parS S c * parRho S c = parU0 S c := by
  unfold parS
  exact div_mul_cancel₀ _ hρ

/-- `u₀ ^ 2 = parLam · ρ² / ‖ρ‖²`. -/
theorem parChart_parU0_sq {c₀ : ℂ} {d : Work.EL.RootParabolic c₀} (S : SplitData d) (c : ℂ) :
    (parU0 S c) ^ 2 = parLam S c * (parRho S c) ^ 2 / (Complex.ofReal ‖parRho S c‖) ^ 2 := by
  unfold parU0
  exact sqrt_sq _

/-- `s ^ 2 = parLam / ‖ρ‖²`, the key cancellation of the chart scale. -/
theorem parS_sq {c₀ : ℂ} {d : Work.EL.RootParabolic c₀} (S : SplitData d) (c : ℂ)
    (hρ : parRho S c ≠ 0) :
    (parS S c) ^ 2 = parLam S c / (Complex.ofReal ‖parRho S c‖) ^ 2 := by
  have hρ2 : (parRho S c) ^ 2 ≠ 0 := pow_ne_zero 2 hρ
  have hn : (Complex.ofReal ‖parRho S c‖ : ℂ) ≠ 0 := by
    rw [Complex.ofReal_ne_zero]; exact norm_ne_zero_iff.mpr hρ
  have hn2 : (Complex.ofReal ‖parRho S c‖ : ℂ) ^ 2 ≠ 0 := pow_ne_zero 2 hn
  rw [parS, div_pow, parChart_parU0_sq]
  field_simp

/-- The complex form of `parA2`. -/
theorem parA2_coe {c₀ : ℂ} {d : Work.EL.RootParabolic c₀} (S : SplitData d) (c : ℂ) :
    (parA2 S c : ℂ)
      = (parSigma S c : ℂ) * (‖Gc S c‖ : ℂ) * (Complex.ofReal ‖parRho S c‖) ^ 2 := by
  rw [parA2, Complex.ofReal_mul, Complex.ofReal_mul, Complex.ofReal_pow]

/-- `a ^ 2 = a2`: the chosen square root of `parA2` (real for `a2 ≥ 0`, purely imaginary
otherwise) really is one.  No sign hypothesis is needed. -/
theorem parA_sq {c₀ : ℂ} {d : Work.EL.RootParabolic c₀} (S : SplitData d) (c : ℂ) :
    (parA S c) ^ 2 = ((parA2 S c : ℝ) : ℂ) := by
  unfold parA
  exact realSqrt_sq _

/-- `h c 0 = u₀ c`: the germ of the normal form at the origin is the chart constant. -/
theorem parHgerm_zero {c₀ : ℂ} {d : Work.EL.RootParabolic c₀} (S : SplitData d) (c : ℂ)
    (hρ : parRho S c ≠ 0) : parHgerm S c 0 = parU0 S c := by
  unfold parHgerm
  rw [mul_zero, Rfun_zero, parS_mul_parRho S c hρ]

/-! ## The two quadratic identities -/

/-- `s² · a2 = Gc`, from `parLam · σ · ‖Gc‖ = Gc` and `s² = parLam/‖ρ‖²`. -/
theorem parS_sq_mul_parA2 {c₀ : ℂ} {d : Work.EL.RootParabolic c₀} (S : SplitData d) (c : ℂ)
    (hρ : parRho S c ≠ 0)
    (hmain : parLam S c * (parSigma S c : ℂ) * (‖Gc S c‖ : ℂ) = Gc S c) :
    (parS S c) ^ 2 * (parA2 S c : ℂ) = Gc S c := by
  have hn : (Complex.ofReal ‖parRho S c‖ : ℂ) ≠ 0 := by
    rw [Complex.ofReal_ne_zero]; exact norm_ne_zero_iff.mpr hρ
  have hn2 : (Complex.ofReal ‖parRho S c‖ : ℂ) ^ 2 ≠ 0 := pow_ne_zero 2 hn
  calc (parS S c) ^ 2 * (parA2 S c : ℂ)
      = (parLam S c / (Complex.ofReal ‖parRho S c‖) ^ 2) * (parA2 S c : ℂ) := by
        rw [parS_sq S c hρ]
    _ = (parLam S c / (Complex.ofReal ‖parRho S c‖) ^ 2)
          * ((parSigma S c : ℂ) * (‖Gc S c‖ : ℂ)
              * (Complex.ofReal ‖parRho S c‖) ^ 2) := by rw [parA2_coe S c]
    _ = (parLam S c * (parSigma S c : ℂ) * (‖Gc S c‖ : ℂ))
          * ((Complex.ofReal ‖parRho S c‖) ^ 2 / (Complex.ofReal ‖parRho S c‖) ^ 2) := by
        ring
    _ = Gc S c * 1 := by rw [hmain, div_self hn2]
    _ = Gc S c := by ring

/-- `(s · a)² = Gc`. -/
theorem parChart_parS_mul_parA_sq {c₀ : ℂ} {d : Work.EL.RootParabolic c₀} (S : SplitData d)
    (c : ℂ) (h2 : (parS S c) ^ 2 * (parA2 S c : ℂ) = Gc S c) :
    (parS S c * parA S c) ^ 2 = Gc S c := by
  calc (parS S c * parA S c) ^ 2 = (parS S c) ^ 2 * (parA S c) ^ 2 := by rw [mul_pow]
    _ = (parS S c) ^ 2 * (parA2 S c : ℂ) := by rw [parA_sq]
    _ = Gc S c := h2

/-- `s ≠ 0`, from `parLam ≠ 0` and `parRho ≠ 0`. -/
theorem parS_ne_zero {c₀ : ℂ} {d : Work.EL.RootParabolic c₀} (S : SplitData d) (c : ℂ)
    (hρ : parRho S c ≠ 0) (hlam : parLam S c ≠ 0) : parS S c ≠ 0 := by
  have hn : (Complex.ofReal ‖parRho S c‖ : ℂ) ≠ 0 := by
    rw [Complex.ofReal_ne_zero]; exact norm_ne_zero_iff.mpr hρ
  have hs2 : (parS S c) ^ 2 ≠ 0 := by
    rw [parS_sq S c hρ]
    exact div_ne_zero hlam (pow_ne_zero 2 hn)
  intro h
  exact hs2 (by rw [h]; ring)

/-- `parLam ≠ 0` whenever `parH ≠ 0` (`parLam = conj (parH)`). -/
theorem parLam_ne_zero_of_parH {c₀ : ℂ} {d : Work.EL.RootParabolic c₀} {S : SplitData d} {c : ℂ}
    (h : parH S c ≠ 0) : parLam S c ≠ 0 := by
  intro hz
  apply h
  have := congrArg star hz
  simpa [parLam] using this

/-- `parLam ≠ 0` on a ball around `c₀`, from `parH_ne_zero`. -/
theorem parLam_ne_zero {c₀ : ℂ} {d : Work.EL.RootParabolic c₀} (S : SplitData d) :
    ∃ ρ' > 0, ρ' ≤ S.ρ ∧ ∀ c ∈ Metric.ball c₀ ρ', parLam S c ≠ 0 := by
  obtain ⟨ρ', hρ'0, hρ'ρ, h⟩ := parH_ne_zero S
  exact ⟨ρ', hρ'0, hρ'ρ, fun c hc => parLam_ne_zero_of_parH (h c hc)⟩

/-! ## The target -/

theorem parChart_algebra {c₀ : ℂ} {d : Work.EL.RootParabolic c₀}
    (S : Work.PARIMPL.ParSplit.SplitData d) :
    ∃ ρ' > 0, ρ' ≤ S.ρ ∧ ∀ c ∈ Metric.ball c₀ ρ',
      Work.PARIMPL.ParSplit.parS S c ≠ 0 ∧
      (Work.PARIMPL.ParSplit.parS S c) ^ 2 * (Work.PARIMPL.ParSplit.parA2 S c : ℂ)
          = Work.PARIMPL.ParSplit.Gc S c ∧
      (Work.PARIMPL.ParSplit.parA S c) ^ 2 = ((Work.PARIMPL.ParSplit.parA2 S c : ℝ) : ℂ) ∧
      (Work.PARIMPL.ParSplit.parS S c * Work.PARIMPL.ParSplit.parA S c) ^ 2
          = Work.PARIMPL.ParSplit.Gc S c ∧
      Work.PARIMPL.ParSplit.parHgerm S c 0 = Work.PARIMPL.ParSplit.parU0 S c := by
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
  have hlam : parLam S c ≠ 0 := parLam_ne_zero_of_parH (h₁ c hc₁)
  have hmain : parLam S c * (parSigma S c : ℂ) * (‖Gc S c‖ : ℂ) = Gc S c := h₃ c hc₃
  have h2 : (parS S c) ^ 2 * (parA2 S c : ℂ) = Gc S c := parS_sq_mul_parA2 S c hρ hmain
  exact ⟨parS_ne_zero S c hρ hlam, h2, parA_sq S c, parChart_parS_mul_parA_sq S c h2,
    parHgerm_zero S c hρ⟩

end Work.PARIMPL.ParSplit
