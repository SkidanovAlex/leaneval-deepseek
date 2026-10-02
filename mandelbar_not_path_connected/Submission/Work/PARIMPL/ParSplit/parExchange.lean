/-
# `Work.PARIMPL.ParSplit.parExchange`

The sign of the (continuous, real-valued) discriminant `parA2 S c = σ c · ‖G c‖ · ‖ρ c‖²`
determines the *character* of the antiholomorphic square root `gtc c = (T_c)^[5]` of the second
return map on the two split fixed points `S.m c ± S.E c/2`:

* `parA2 S c < 0` (implosion side): `gtc c` **swaps** the two split fixed points, and the chart
  data satisfies `parA S c = parLamReal S c · I`, `parLamReal S c > 0`;
* `parA2 S c > 0` (the other side): `gtc c` **fixes** both split fixed points.

The two statements are stated in the form used by the assembly of the parameter normal form:
the swap/fix alternatives are phrased for the *chart* points `S.m c ± parS S c · parA S c`, which
are the split fixed points up to the labelling (`(parS·parA)² = G`).

Everything is a consequence of `parLam_eq` (the branch-corrected direction `parLam` equals
`σ · dir G`), of `parRho_ne_zero` (so the chart scale `parS` is defined), of
`g_mem_of_split`/`g_mem_of_split_sub` (the images under `gtc` stay in the dynamical disc, so the
swap/fix dichotomy of `SplitData` applies) and of the elementary algebra of the chosen square
roots `realSqrt` and `Complex.sqrt`.
-/
import Mathlib
import Submission.Work.PARIMPL.ParSplit.ParWall
import Submission.Work.PARIMPL.ParSplit.parLam_eq
import Submission.Work.PARIMPL.ParSplit.parRho_ne_zero
import Submission.Work.PARIMPL.ParSplit.swap_fix_open

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

variable {c₀ : ℂ} {d : Work.EL.RootParabolic c₀}

/-! ## The algebraic core: `(parS · parA)² = G` -/

/-- `parU0` is the chosen square root of `parLam · parRho²/‖parRho‖²`. -/
theorem parU0_sq (S : SplitData d) (c : ℂ) :
    (parU0 S c) ^ 2 = parLam S c * (parRho S c) ^ 2 / ((‖parRho S c‖ ^ 2 : ℝ) : ℂ) := by
  unfold parU0
  rw [Complex.sqrt]
  have h := Complex.cpow_nat_inv_pow
    (parLam S c * (parRho S c) ^ 2 / ((‖parRho S c‖ ^ 2 : ℝ) : ℂ)) (n := 2) (by norm_num)
  simpa using h

/-- The square of the branch sign `parSigma` (which takes the values `±1`). -/
theorem parSigma_sq_one (S : SplitData d) (c : ℂ) : (parSigma S c : ℂ) ^ 2 = 1 := by
  unfold parSigma
  split_ifs <;> norm_num

/-- **The chart identity.**  On the ball where `parLam = σ · dir G` and `parRho ≠ 0`, the product
`parS · parA` is a square root of `G = (E/2)²`, i.e. the chart points `m ± parS·parA` are the two
split fixed points. -/
theorem parS_mul_parA_sq (S : SplitData d) (c : ℂ) (hrho : parRho S c ≠ 0)
    (hlam : parLam S c * (‖Gc S c‖ : ℂ) = (parSigma S c : ℂ) * Gc S c) :
    (parS S c * parA S c) ^ 2 = Gc S c := by
  have hs2 : (parS S c) ^ 2 = parLam S c / ((‖parRho S c‖ ^ 2 : ℝ) : ℂ) := by
    unfold parS
    rw [div_pow, parU0_sq S c]
    field_simp
  have hA : (parA S c) ^ 2 = ((parA2 S c : ℝ) : ℂ) := realSqrt_sq _
  have hσ : (parSigma S c : ℂ) ^ 2 = 1 := parSigma_sq_one S c
  have hcast : ((parA2 S c : ℝ) : ℂ)
      = (parSigma S c : ℂ) * (‖Gc S c‖ : ℂ) * ((‖parRho S c‖ ^ 2 : ℝ) : ℂ) := by
    rw [parA2]; push_cast; ring
  have hρn : ((‖parRho S c‖ ^ 2 : ℝ) : ℂ) ≠ 0 := by
    have : ‖parRho S c‖ ^ 2 ≠ 0 := pow_ne_zero _ (norm_ne_zero_iff.mpr hrho)
    exact_mod_cast this
  rw [mul_pow, hs2, hA, hcast]
  rw [show parLam S c / ((‖parRho S c‖ ^ 2 : ℝ) : ℂ)
        * ((parSigma S c : ℂ) * (‖Gc S c‖ : ℂ) * ((‖parRho S c‖ ^ 2 : ℝ) : ℂ))
      = (parLam S c * (‖Gc S c‖ : ℂ)) * (parSigma S c : ℂ) from by field_simp]
  rw [hlam]
  rw [show (parSigma S c : ℂ) * Gc S c * (parSigma S c : ℂ)
      = (parSigma S c : ℂ) ^ 2 * Gc S c from by ring]
  rw [hσ, one_mul]

/-- On the ball of `parLam_eq`, `parLam · ‖Gc‖ = σ · Gc` (both sides vanish at `Gc = 0`). -/
theorem parLam_mul_norm_Gc (S : SplitData d) {ρ₁ : ℝ} (hρ₁ : ρ₁ ≤ S.ρ)
    (hlam : ∀ c ∈ Metric.ball c₀ ρ₁, Gc S c ≠ 0 →
      parLam S c = (parSigma S c : ℂ) * Gc S c / (‖Gc S c‖ : ℂ))
    {c : ℂ} (hc : c ∈ Metric.ball c₀ ρ₁) :
    parLam S c * (‖Gc S c‖ : ℂ) = (parSigma S c : ℂ) * Gc S c := by
  by_cases hG : Gc S c = 0
  · simp [hG]
  · rw [hlam c hc hG]
    have hn : (‖Gc S c‖ : ℂ) ≠ 0 := by
      rw [Complex.ofReal_ne_zero]; exact norm_ne_zero_iff.mpr hG
    field_simp

/-! ## The character of `gtc` from the sign of `parA2` -/

/-- **Negative sign ⟹ swap.**  If `parA2 S c < 0` then `σ c = -1`, i.e. `gtc c` swaps the two
split fixed points. -/
theorem gtc_swap_of_a2_neg (S : SplitData d) (c : ℂ) (ha2 : parA2 S c < 0) :
    gtc c (S.m c + S.E c / 2) = S.m c - S.E c / 2 := by
  by_contra h
  have hσ : parSigma S c = 1 := by rw [parSigma]; exact if_neg h
  have hprod : (0 : ℝ) ≤ ‖Gc S c‖ * ‖parRho S c‖ ^ 2 :=
    mul_nonneg (norm_nonneg _) (sq_nonneg _)
  have hval : parA2 S c = ‖Gc S c‖ * ‖parRho S c‖ ^ 2 := by rw [parA2, hσ]; ring
  linarith

/-- **Positive sign ⟹ fix (at the plus point).**  If `0 < parA2 S c` then `σ c = 1`; the dichotomy
of `SplitData` (which applies because `gtc c (m c + E c/2)` stays in the dynamical disc) then gives
`gtc c (m c + E c/2) = m c + E c/2`. -/
theorem gtc_fix_of_a2_pos (S : SplitData d) (c : ℂ) (hc : c ∈ Metric.ball c₀ S.ρ)
    (hmem : gtc c (S.m c + S.E c / 2) ∈ Metric.ball d.z₁ S.R) (ha2 : 0 < parA2 S c) :
    gtc c (S.m c + S.E c / 2) = S.m c + S.E c / 2 := by
  rcases S.swap_or_fix_of_split hc hmem with h | h
  · exact h
  · exfalso
    have hσ : parSigma S c = -1 := by rw [parSigma]; exact if_pos h
    have hprod : (0 : ℝ) ≤ ‖Gc S c‖ * ‖parRho S c‖ ^ 2 :=
      mul_nonneg (norm_nonneg _) (sq_nonneg _)
    have hval : parA2 S c = -(‖Gc S c‖ * ‖parRho S c‖ ^ 2) := by rw [parA2, hσ]; ring
    linarith

/-- **Fix at the plus point ⟹ fix at the minus point.** -/
theorem gtc_sub_eq_of_fix (S : SplitData d) (c : ℂ) (hc : c ∈ Metric.ball c₀ S.ρ)
    (hmem_sub : gtc c (S.m c - S.E c / 2) ∈ Metric.ball d.z₁ S.R)
    (hadd : gtc c (S.m c + S.E c / 2) = S.m c + S.E c / 2) :
    gtc c (S.m c - S.E c / 2) = S.m c - S.E c / 2 := by
  have hgg : gtc c (gtc c (S.m c - S.E c / 2)) = S.m c - S.E c / 2 := by
    rw [gtc_comp_apply]
    exact S.fixed_sub c hc
  have hfix : Work.EL.F c (gtc c (S.m c - S.E c / 2)) = gtc c (S.m c - S.E c / 2) := by
    have hcomp : gtc c (gtc c (gtc c (S.m c - S.E c / 2)))
        = Work.EL.F c (gtc c (S.m c - S.E c / 2)) := by
      rw [gtc_comp_apply]
    rw [← hcomp, hgg]
  rcases (S.unique c hc (gtc c (S.m c - S.E c / 2)) hmem_sub).mp hfix with h | h
  · rw [h] at hgg
    rw [hadd] at hgg
    rw [h]
    exact hgg
  · exact h

/-! ## `parExchange` -/

theorem parExchange {c₀ : ℂ} {d : Work.EL.RootParabolic c₀}
    (S : Work.PARIMPL.ParSplit.SplitData d) :
    ∃ ρ' > 0, ρ' ≤ S.ρ ∧ ∀ c ∈ Metric.ball c₀ ρ',
      (Work.PARIMPL.ParSplit.parA2 S c < 0 →
          Work.PARIMPL.ParSplit.parA S c = (Work.PARIMPL.ParSplit.parLamReal S c : ℂ) * Complex.I) ∧
      (Work.PARIMPL.ParSplit.parA2 S c < 0 → 0 < Work.PARIMPL.ParSplit.parLamReal S c) ∧
      (Work.PARIMPL.ParSplit.parA2 S c < 0 →
          gtc c (S.m c + Work.PARIMPL.ParSplit.parS S c * Work.PARIMPL.ParSplit.parA S c)
            = S.m c - Work.PARIMPL.ParSplit.parS S c * Work.PARIMPL.ParSplit.parA S c) ∧
      (0 < Work.PARIMPL.ParSplit.parA2 S c →
          gtc c (S.m c + Work.PARIMPL.ParSplit.parS S c * Work.PARIMPL.ParSplit.parA S c)
              = S.m c + Work.PARIMPL.ParSplit.parS S c * Work.PARIMPL.ParSplit.parA S c ∧
          gtc c (S.m c - Work.PARIMPL.ParSplit.parS S c * Work.PARIMPL.ParSplit.parA S c)
              = S.m c - Work.PARIMPL.ParSplit.parS S c * Work.PARIMPL.ParSplit.parA S c) := by
  obtain ⟨ρ₁, hρ₁, hρ₁ρ, hlam⟩ := parLam_eq S
  obtain ⟨ρ₂, hρ₂, hρ₂ρ, hmem⟩ := g_mem_of_split S
  obtain ⟨ρ₃, hρ₃, hρ₃ρ, hmem_sub⟩ := g_mem_of_split_sub S
  obtain ⟨ρ₄, hρ₄, hρ₄ρ, hrho⟩ := parRho_ne_zero S
  let ρ' : ℝ := min (min (min ρ₁ ρ₂) ρ₃) ρ₄
  have hρ'pos : 0 < ρ' := lt_min (lt_min (lt_min hρ₁ hρ₂) hρ₃) hρ₄
  have hρ'ρ : ρ' ≤ S.ρ :=
    le_trans (le_trans (min_le_left _ _) (le_trans (min_le_left _ _) (min_le_left _ _))) hρ₁ρ
  refine ⟨ρ', hρ'pos, hρ'ρ, ?_⟩
  intro c hc
  -- membership in the four balls and in the big one
  have hb1 : ρ' ≤ ρ₁ :=
    le_trans (min_le_left _ _) (le_trans (min_le_left _ _) (min_le_left _ _))
  have hb2 : ρ' ≤ ρ₂ :=
    le_trans (min_le_left _ _) (le_trans (min_le_left _ _) (min_le_right _ _))
  have hb3 : ρ' ≤ ρ₃ := le_trans (min_le_left _ _) (min_le_right _ _)
  have hb4 : ρ' ≤ ρ₄ := min_le_right _ _
  have hc1 : c ∈ Metric.ball c₀ ρ₁ := mem_ball.mpr (lt_of_lt_of_le (mem_ball.mp hc) hb1)
  have hc2 : c ∈ Metric.ball c₀ ρ₂ := mem_ball.mpr (lt_of_lt_of_le (mem_ball.mp hc) hb2)
  have hc3 : c ∈ Metric.ball c₀ ρ₃ := mem_ball.mpr (lt_of_lt_of_le (mem_ball.mp hc) hb3)
  have hc4 : c ∈ Metric.ball c₀ ρ₄ := mem_ball.mpr (lt_of_lt_of_le (mem_ball.mp hc) hb4)
  have hcρ : c ∈ Metric.ball c₀ S.ρ := mem_ball.mpr (lt_of_lt_of_le (mem_ball.mp hc) hρ'ρ)
  have hlam' : parLam S c * (‖Gc S c‖ : ℂ) = (parSigma S c : ℂ) * Gc S c :=
    parLam_mul_norm_Gc S hρ₁ρ hlam hc1
  have hsq : (parS S c * parA S c) ^ 2 = Gc S c :=
    parS_mul_parA_sq S c (hrho c hc4) hlam'
  -- `parS·parA = ± E/2`
  have hsplit : parS S c * parA S c = S.E c / 2 ∨ parS S c * parA S c = -(S.E c / 2) := by
    have h2 : (parS S c * parA S c) ^ 2 - (S.E c / 2) ^ 2 = 0 := by
      rw [hsq]; unfold Gc; ring
    have h3 : (parS S c * parA S c - S.E c / 2) * (parS S c * parA S c + S.E c / 2) = 0 := by
      have : (parS S c * parA S c - S.E c / 2) * (parS S c * parA S c + S.E c / 2)
          = (parS S c * parA S c) ^ 2 - (S.E c / 2) ^ 2 := by ring
      rw [this, h2]
    rcases mul_eq_zero.mp h3 with h | h
    · left; linear_combination h
    · right; linear_combination h
  refine ⟨?_, ?_, ?_, ?_⟩
  · -- clause 1: `parA = parLamReal · I` on the implosion side
    intro ha2
    unfold parA parLamReal realSqrt
    rw [if_neg (not_le.mpr ha2)]
  · -- clause 2: `0 < parLamReal`
    intro ha2
    unfold parLamReal
    apply Real.sqrt_pos.mpr
    rw [norm_pos_iff]
    exact ne_of_lt ha2
  · -- clause 3: swap on the implosion side
    intro ha2
    have hswap : gtc c (S.m c + S.E c / 2) = S.m c - S.E c / 2 := gtc_swap_of_a2_neg S c ha2
    have hswap_q : gtc c (S.m c + -(S.E c / 2)) = S.m c + S.E c / 2 := by
      have h0 : gtc c (gtc c (S.m c + S.E c / 2)) = S.m c + S.E c / 2 := by
        rw [gtc_comp_apply]; exact S.fixed_add c hcρ
      rw [hswap] at h0
      rw [show S.m c - S.E c / 2 = S.m c + -(S.E c / 2) from by ring] at h0
      exact h0
    rcases hsplit with hx | hx
    · rw [hx, hswap]
    · rw [hx]
      simp only [sub_eq_add_neg, neg_neg]
      exact hswap_q
  · -- clause 4: fix on the other side
    intro ha2
    have hfixp : gtc c (S.m c + S.E c / 2) = S.m c + S.E c / 2 :=
      gtc_fix_of_a2_pos S c hcρ (hmem c hc2) ha2
    have hfixq : gtc c (S.m c - S.E c / 2) = S.m c - S.E c / 2 :=
      gtc_sub_eq_of_fix S c hcρ (hmem_sub c hc3) hfixp
    have hfixq' : gtc c (S.m c + -(S.E c / 2)) = S.m c + -(S.E c / 2) := by
      rw [show S.m c - S.E c / 2 = S.m c + -(S.E c / 2) from by ring] at hfixq
      exact hfixq
    constructor
    · rcases hsplit with hx | hx
      · rw [hx, hfixp]
      · rw [hx, hfixq']
    · rcases hsplit with hx | hx
      · rw [hx, hfixq]
      · rw [hx]
        simp only [sub_eq_add_neg, neg_neg]
        exact hfixp

end Work.PARIMPL.ParSplit
