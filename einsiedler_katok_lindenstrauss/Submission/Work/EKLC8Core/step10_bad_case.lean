/-
Step 10 of `ROUTE_LEAD.md` §5, the **bad case** of the H-property case analysis.

Notation (see `ROUTE_LEAD.md` §5 Step 10, and `Basic.lean`): `G` is the displacement matrix
`g̃ = φ_τ g φ_τ⁻¹`, `κ = κ(G) = max(κ_a, κ_u)` with `κ_a = |a₂-a₁| = |G 1 1 - G 0 0|`,
`κ_u = max(√|G 1 0|, |G 2 0|, |G 1 2|)`, and `drift G r` is the max of the three `U_(12)`
entries `|(a₂-a₁)r - G 1 0·r²|`, `|G 1 2·r|`, `|G 2 0·r|` of the sheared displacement
`g̃(r) = u(r) g̃ u(-r)`.  The hypothesis `ρ/κ < |r| ≤ 1/κ` says `q := κ|r|` lies in `(ρ, 1]`.

The claim is the lower bound of EKL's bad case: if the drift is `< ρ²` (that is, `q` is
attained by one of `|(a₂-a₁)r|`, `√|G 1 0|·|r|` in the paper's terminology) then
`|G 1 0| ≥ ρ²κ² = ρ²/κ⁻²`.

Proof.  Since `|G 2 0·r|`, `|G 1 2·r| < ρ²` and `ρ/κ < |r|`, we get
`|G 2 0|, |G 1 2| < ρκ ≤ κ`; together with `|G 1 0| < ρ²κ²` (assumed for contradiction),
which gives `√|G 1 0| < ρκ ≤ κ`, this forces `κ_u(G) < κ`, hence `κ_a(G) = κ`, i.e.
`|a₂ - a₁| = κ`.  Then

  `drift ≥ |(a₂-a₁)r - G 1 0·r²| = |r|·|(a₂-a₁) - G 1 0·r| ≥ |r|·(κ - |G 1 0|·|r|)`

and `|G 1 0|·|r| < ρ²κ²·κ⁻¹ = ρ²κ`, so `drift > |r|·κ(1-ρ²) > ρ·(1-ρ²) ≥ ρ²`
(the last because `ρ ≤ 1/2`), contradicting `drift < ρ²`.
-/
import Mathlib
import Submission.Work.EKLC8Core.Vol

namespace Work.EKLC8Core

theorem step10_bad_case {ρ κ r : ℝ} {G : Matrix (Fin 3) (Fin 3) ℝ}
    (hρ0 : 0 < ρ) (hρ1 : ρ ≤ 1 / 2) (hκ : 0 < κ) (hκκ : kappa G = κ)
    (hr1 : ρ * κ⁻¹ < |r|) (hr2 : |r| ≤ κ⁻¹) (hbad : drift G r < ρ ^ 2) :
    ρ ^ 2 * κ ^ 2 ≤ |G 1 0| := by
  by_contra hcon
  have hconlt : |G 1 0| < ρ ^ 2 * κ ^ 2 := not_le.mp hcon
  have hρκ : 0 < ρ * κ⁻¹ := mul_pos hρ0 (inv_pos.mpr hκ)
  have hrpos : 0 < |r| := lt_trans hρκ hr1
  -- `ρ < κ|r|`, and hence `1/|r| < κ/ρ`.
  have hκr : ρ < κ * |r| := by
    have h1 : κ * (ρ * κ⁻¹) = ρ := by field_simp
    have h2 := mul_lt_mul_of_pos_left hr1 hκ
    rwa [h1] at h2
  have hinv : |r|⁻¹ < κ / ρ := by
    have h := one_div_lt_one_div_of_lt hρκ hr1
    have h2 : 1 / (ρ * κ⁻¹) = κ / ρ := by field_simp
    rw [h2] at h
    have h3 : (1 : ℝ) / |r| = |r|⁻¹ := by rw [div_eq_mul_inv, one_mul]
    rwa [h3] at h
  -- the two "outer" drift entries are `< ρ²`, hence the corresponding matrix entries are
  -- `< ρκ`.
  have hCabs : |G 2 0| * |r| < ρ ^ 2 := by
    have h1 : |G 2 0 * r| ≤ drift G r := by
      simp only [drift]; exact le_max_right _ _
    rw [abs_mul] at h1
    exact lt_of_le_of_lt h1 hbad
  have hBabs : |G 1 2| * |r| < ρ ^ 2 := by
    have h1 : |G 1 2 * r| ≤ drift G r := by
      simp only [drift]; exact le_trans (le_max_right _ _) (le_max_left _ _)
    rw [abs_mul] at h1
    exact lt_of_le_of_lt h1 hbad
  have hρκκ : ρ * κ ≤ κ := by nlinarith
  have hdiv : ρ ^ 2 / |r| < ρ * κ := by
    rw [div_eq_mul_inv]
    calc ρ ^ 2 * |r|⁻¹ < ρ ^ 2 * (κ / ρ) := mul_lt_mul_of_pos_left hinv (pow_pos hρ0 2)
      _ = ρ * κ := by field_simp
  have hC20 : |G 2 0| < ρ * κ :=
    lt_trans ((lt_div_iff₀ hrpos).mpr hCabs) hdiv
  have hC12 : |G 1 2| < ρ * κ :=
    lt_trans ((lt_div_iff₀ hrpos).mpr hBabs) hdiv
  -- `√|G 1 0| < ρκ`
  have hs : Real.sqrt |G 1 0| < ρ * κ := by
    rw [Real.sqrt_lt' (mul_pos hρ0 hκ)]
    calc |G 1 0| < ρ ^ 2 * κ ^ 2 := hconlt
      _ = (ρ * κ) ^ 2 := by ring
  -- All three terms of `κ_u(G)` are `< κ`, so `κ_u(G) < κ` and consequently `κ_a(G) = κ`.
  have hκU : kappaU G < κ := by
    have h20 : |G 2 0| < κ := lt_of_lt_of_le hC20 hρκκ
    have h12 : |G 1 2| < κ := lt_of_lt_of_le hC12 hρκκ
    have hs' : Real.sqrt |G 1 0| < κ := lt_of_lt_of_le hs hρκκ
    simp only [kappaU]
    exact max_lt hs' (max_lt h20 h12)
  have hκA : kappaA G = κ := by
    have hmax : max (kappaA G) (kappaU G) = κ := by rw [← hκκ]; rfl
    rcases le_or_gt (kappaA G) (kappaU G) with h | h
    · rw [max_eq_right h] at hmax
      exact absurd hmax (ne_of_lt hκU)
    · rwa [max_eq_left h.le] at hmax
  have hκAge : |G 1 1 - G 0 0| = κ := hκA
  -- the drift dominates `|r| · (κ - |G 1 0|·|r|)`
  have hchain : |r| * (κ - |G 1 0| * |r|) ≤ drift G r := by
    have hA : |(G 1 1 - G 0 0) * r - G 1 0 * r ^ 2|
        = |r| * |(G 1 1 - G 0 0) - G 1 0 * r| := by
      rw [show (G 1 1 - G 0 0) * r - G 1 0 * r ^ 2
            = r * ((G 1 1 - G 0 0) - G 1 0 * r) by ring, abs_mul]
    have h1 : |G 1 1 - G 0 0| - |G 1 0 * r| ≤ |(G 1 1 - G 0 0) - G 1 0 * r| :=
      abs_sub_abs_le_abs_sub _ _
    rw [abs_mul, hκAge] at h1
    calc |r| * (κ - |G 1 0| * |r|) ≤ |r| * |(G 1 1 - G 0 0) - G 1 0 * r| :=
          mul_le_mul_of_nonneg_left h1 hrpos.le
      _ = |(G 1 1 - G 0 0) * r - G 1 0 * r ^ 2| := hA.symm
      _ ≤ drift G r := by
          simp only [drift]
          exact le_trans (le_max_left _ _) (le_max_left _ _)
  -- `|G 1 0|·|r| < ρ²κ`
  have hG10r : |G 1 0| * |r| < ρ ^ 2 * κ := by
    have h1 : |G 1 0| * |r| ≤ |G 1 0| * κ⁻¹ := mul_le_mul_of_nonneg_left hr2 (abs_nonneg _)
    have h2 : |G 1 0| * κ⁻¹ < ρ ^ 2 * κ ^ 2 * κ⁻¹ :=
      mul_lt_mul_of_pos_right hconlt (inv_pos.mpr hκ)
    have h3 : ρ ^ 2 * κ ^ 2 * κ⁻¹ = ρ ^ 2 * κ := by field_simp
    linarith
  -- hence `drift > ρ²`, the contradiction.
  have hbig : ρ ^ 2 < drift G r := by
    have h1m : (0 : ℝ) < 1 - ρ ^ 2 := by nlinarith [sq_nonneg (ρ - 1 / 2)]
    have h4 : κ * (1 - ρ ^ 2) < κ - |G 1 0| * |r| := by nlinarith
    have hmul : |r| * (κ * (1 - ρ ^ 2)) < |r| * (κ - |G 1 0| * |r|) :=
      mul_lt_mul_of_pos_left h4 hrpos
    have hstep : ρ * (1 - ρ ^ 2) < |r| * (κ * (1 - ρ ^ 2)) := by
      calc ρ * (1 - ρ ^ 2) < (κ * |r|) * (1 - ρ ^ 2) := mul_lt_mul_of_pos_right hκr h1m
        _ = |r| * (κ * (1 - ρ ^ 2)) := by ring
    have h6 : ρ ^ 2 ≤ ρ * (1 - ρ ^ 2) := by nlinarith [sq_nonneg ρ]
    linarith
  exact absurd hbig (not_lt.mpr hbad.le)

end Work.EKLC8Core
