import Mathlib
import Submission.Work.LinnikAreas.BGTZ

/-!
# The `hHigh` input of AREA 6, from the λ₁-free bound plus the BGTZ-range bound

`Work.LinnikAreas.area6_of_all` needs

`hHigh : ∃ C > 0, ∃ e < 0, ∃ q₀, ∀ (Siegel data), restHighZeroSum χ₁ β₁ (11/2) (3/10) ≤ C·λ₁·𝓛^e`.

The workspace's earlier route supplied it from `Siegel.DHLogFreeHeightCoupled c` (a coupled
`λ₁`-saving log-free density estimate in the height direction) via `siegelRestHighCoupled`; that
estimate is *not* a classical theorem in the unrestricted form (see the discussion in
`Submission/Work/LinnikAreas/BGTZ.lean` and `NOTES_area6_route.md` §8).

This file supplies `hHigh` from the two *honest* pieces:

* `Siegel.RestHighFreeSpec (-3/2)` — the `λ₁`-free bound `restHighZeroSum ≤ C·𝓛^{-3/2}`, which is
  Heath-Brown's Lemma 13.2 argument run against the `λ₁`-free log-free family count
  (`LogFreeFamHeight (5/2) (3/2)`, Jutila + Huxley); and
* `Siegel.RestHighBGTZSpec (-3/2)` — the `λ₁`-saving bound for `λ₁ ≤ 1/10`, which is the same
  count but with the λ-range cut off by the Benli–Goel–Twiss–Zaman repulsion at all heights
  (`Siegel.RepulsionBGTZ`),

split at `λ₁ = 1/10`: for `λ₁ ≥ 1/10` the `λ₁`-free bound is already a multiple of `λ₁`.
-/

open DirichletCharacter Complex
open scoped Classical BigOperators
noncomputable section

namespace Work.LinnikAreas

open Work.LinnikContract

/-- **The `hHigh` input of `area6_of_all`**, from the `λ₁`-free high-zero bound and the
`λ₁`-saving one in the BGTZ range `λ₁ ≤ 1/10`. -/
theorem RestHighCombine (hfree : Siegel.RestHighFreeSpec (-3 / 2))
    (hbgtz : Siegel.RestHighBGTZSpec (-3 / 2)) :
    ∃ C : ℝ, 0 < C ∧ ∃ e : ℝ, e < 0 ∧ ∃ q₀ : ℕ,
      ∀ q : ℕ, q₀ ≤ q → ∀ [NeZero q] (χ₁ : DirichletCharacter ℂ q) (β₁ : ℝ),
        χ₁ ≠ 1 → χ₁ ^ 2 = 1 → β₁ < 1 → zeroMult χ₁ (β₁ : ℂ) ≠ 0 →
        lamOf q (β₁ : ℂ) ≤ 1 / 2 →
        Siegel.restHighZeroSum χ₁ (β₁ : ℂ) (11 / 2) (3 / 10)
          ≤ C * lamOf q (β₁ : ℂ) * (Real.log q) ^ e := by
  obtain ⟨C₁, hC₁pos, q₀₁, h₁⟩ := hfree
  obtain ⟨C₂, hC₂pos, q₀₂, h₂⟩ := hbgtz
  refine ⟨max C₂ (10 * C₁), lt_max_of_lt_left hC₂pos, -3 / 2, by norm_num, max (max q₀₁ q₀₂) 2, ?_⟩
  intro q hq nq χ₁ β₁ hχ hsq hβ hz hlam
  have hq₁ : q₀₁ ≤ q := le_trans (le_trans (le_max_left _ _) (le_max_left _ _)) hq
  have hq₂ : q₀₂ ≤ q := le_trans (le_trans (le_max_right _ _) (le_max_left _ _)) hq
  have hq2 : 2 ≤ q := le_trans (le_max_right _ _) hq
  have hlog : 0 < Real.log q := Real.log_pos (by exact_mod_cast (by omega : 1 < q))
  have hlamnn : 0 ≤ lamOf q (β₁ : ℂ) := by
    rw [lamOf, Complex.ofReal_re]
    exact mul_nonneg (by linarith) hlog.le
  have hpow : 0 ≤ (Real.log q) ^ (-3 / 2 : ℝ) := Real.rpow_nonneg hlog.le _
  by_cases hsmall : lamOf q (β₁ : ℂ) ≤ 1 / 10
  · refine le_trans (h₂ q hq₂ χ₁ β₁ hχ hsq hβ hz hsmall) ?_
    exact mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_right (le_max_left _ _) hlamnn) hpow
  · push_neg at hsmall
    refine le_trans (h₁ q hq₁ χ₁ β₁ hχ hsq hβ hz hlam) ?_
    have hstep : C₁ * (Real.log q) ^ (-3 / 2 : ℝ)
        ≤ (10 * C₁) * lamOf q (β₁ : ℂ) * (Real.log q) ^ (-3 / 2 : ℝ) := by
      have h1 : C₁ ≤ C₁ * (10 * lamOf q (β₁ : ℂ)) := by nlinarith [hC₁pos.le, hsmall.le]
      calc C₁ * (Real.log q) ^ (-3 / 2 : ℝ)
          ≤ (C₁ * (10 * lamOf q (β₁ : ℂ))) * (Real.log q) ^ (-3 / 2 : ℝ) :=
            mul_le_mul_of_nonneg_right h1 hpow
        _ = (10 * C₁) * lamOf q (β₁ : ℂ) * (Real.log q) ^ (-3 / 2 : ℝ) := by ring
    exact le_trans hstep
      (mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_right (le_max_right _ _) hlamnn) hpow)

end Work.LinnikAreas
