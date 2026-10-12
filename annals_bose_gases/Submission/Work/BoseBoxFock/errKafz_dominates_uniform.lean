import ChallengeDeps
import Mathlib.Algebra.Order.Star.Real
import Mathlib.Analysis.Real.Pi.Bounds
import Submission.Work.BoseBoxFock.EnvFacts
-- PORT435-BEGIN (v4.35 isDefEq respectTransparency compat)
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- PORT435-END

/-!
# `Submission/Work/BoseBoxFock/errKafz_dominates_uniform.lean`

The uniform (in the honest mode family `HM`) form of `Work.BoseBoxFock.errKafz_dominates`:
the environment bundle `EnvFactsAt v h fc fu HM μ C₀` — provided *uniformly* in `HM` —
dominates the five error terms of the §8 model bound by the `R`-assembly error `errKafz`,
with a constant that depends only on `C₀`:

    C := 1 + 2(8π+C₀)(2+C₀) + 40(C₀+1)² + (8π+C₀)C₀ + 8π + (192/π)C₀².

The proof has four independent pieces (all in this file):

* `errKafzT1_le` — `4·cH·(n+1) ≤ 2(8π+C₀)(2+C₀)·μa`, from `n+1 ≤ 2μℓ³+1`, `ℓ⁻³(2μℓ³+1) ≤ (2+C₀)μ`;
* `errKafzT2_le` — the two `√`-terms `≤ 40(C₀+1)²·μa`, from `√M ≤ √(C₀μℓ³)`, `√(n+1) ≤ √(3μℓ³)`
  and the collapse `ℓ⁻³√(C₀μℓ³)√(3μℓ³) = μ√(3C₀)`;
* `errKafzT3_le` — the `(ρ_z−μ)`-term `≤ ((8π+C₀)C₀ + 8π + (192/π)C₀²)·μa`;
* `mu_sq_a_sideAt_cube_sqrt_Kl_inv_cube` + `errKafz_ge` — `errKafz ≥ C·μa`, because the
  bracket of `errKafz` is `≥ K_ℓ⁻³` and `μ²(a v)ℓ³√(μa³)·K_ℓ⁻³ = μ(a v)` exactly.

Nothing in the bound ever sees `HM` except through the index type of the rows that are
universally quantified over the modes.
-/

open scoped Real

namespace Work.BoseBoxFock

set_option linter.unusedVariables false

/-! ## 1. The exact rpow identity `μ² a ℓ³ √(μa³) K_ℓ⁻³ = μa` -/

/-- `fsXp t (-489) · fsXp t (323/2) · fsXp t (9/2) = t⁻¹`: the exponent bookkeeping of
`ℓ³ = (a v)³ t^{-489/323}`, `√t = t^{1/2}`, `K_ℓ⁻³ = t^{9/646}`. -/
lemma errKafzT_fsXp_prod_inv (t : ℝ) (ht : 0 < t) :
    Work.BoseBox.fsXp t (-489) * Work.BoseBox.fsXp t (323 / 2)
      * Work.BoseBox.fsXp t (9 / 2) = t⁻¹ := by
  rw [Work.BoseBox.fsXp_mul ht, Work.BoseBox.fsXp_mul ht]
  rw [show (-489 + 323 / 2 + 9 / 2 : ℝ) = -323 by norm_num]
  rw [Work.BoseBox.fsXp]
  rw [show (-323 : ℝ) / 323 = -1 by norm_num, Real.rpow_neg_one]

/-- `(paramsAt μ A).Kl ^ (-3) = fsXp (μA³) (9/2)`, i.e. `K_ℓ⁻³ = t^{9/646}`. -/
lemma errKafzT_Kl_inv_cube {A μ : ℝ} (hA : 0 < A) (hμ : 0 < μ) :
    (Work.BoseBox.paramsAt μ A).Kl ^ (-(3 : ℝ)) = Work.BoseBox.fsXp (μ * A ^ 3) (9 / 2) := by
  have ht : 0 < μ * A ^ 3 := by positivity
  rw [Work.BoseFixB1.Kl_eq_fsXp]
  rw [Work.BoseBox.fsXp_rpow ht.le]
  norm_num

/-- **`μ² a ℓ³ √(μa³) · K_ℓ⁻³ = μ a`** at `ℓ = sideAt μ a`: the identity that makes the
`K_ℓ⁻³`-slot of `errKafz` worth exactly `C·μa`. -/
lemma mu_sq_a_sideAt_cube_sqrt_Kl_inv_cube {A μ : ℝ} (hA : 0 < A) (hμ : 0 < μ) :
    μ ^ 2 * A * Work.BoseBox.sideAt μ A ^ 3 * Real.sqrt (μ * A ^ 3)
      * (Work.BoseBox.paramsAt μ A).Kl ^ (-(3 : ℝ)) = μ * A := by
  have ht : 0 < μ * A ^ 3 := by positivity
  have hfs : Work.BoseBox.fsXp (μ * A ^ 3) (-489) * Work.BoseBox.fsXp (μ * A ^ 3) (323 / 2)
      * Work.BoseBox.fsXp (μ * A ^ 3) (9 / 2) = (μ * A ^ 3)⁻¹ :=
    errKafzT_fsXp_prod_inv (μ * A ^ 3) ht
  rw [Work.BoseFixB1.sideAt_cube_eq hA hμ, Real.sqrt_eq_rpow, Work.BoseFixB1.half_eq_fsXp,
    errKafzT_Kl_inv_cube hA hμ]
  rw [show μ ^ 2 * A * (A ^ 3 * Work.BoseBox.fsXp (μ * A ^ 3) (-489))
        * Work.BoseBox.fsXp (μ * A ^ 3) (323 / 2) * Work.BoseBox.fsXp (μ * A ^ 3) (9 / 2)
      = μ ^ 2 * A ^ 4 * (Work.BoseBox.fsXp (μ * A ^ 3) (-489)
          * Work.BoseBox.fsXp (μ * A ^ 3) (323 / 2)
          * Work.BoseBox.fsXp (μ * A ^ 3) (9 / 2)) from by ring]
  rw [hfs, show μ ^ 2 * A ^ 4 = (μ * A) * (μ * A ^ 3) from by ring, mul_assoc,
    mul_inv_cancel₀ (show (μ * A ^ 3 : ℝ) ≠ 0 by positivity), mul_one]

/-! ## 2. `errKafz ≥ C·μa` -/

/-- **`errKafz ≥ C·μa`**: the bracket of `errKafz` is at least its `K_ℓ⁻³`-slot, and
`μ²(a v)ℓ³√(μa³)K_ℓ⁻³ = μ(a v)` (`mu_sq_a_sideAt_cube_sqrt_Kl_inv_cube`). -/
lemma errKafz_ge (v : ℝ³ → ℝ) {R μ C : ℝ} (hμ : 0 < μ)
    (hav : 0 < BoseGases.a v) (hC : 0 ≤ C) :
    C * μ * BoseGases.a v ≤ Work.BoseFixR.errKafz v R μ C := by
  have hiden : μ ^ 2 * BoseGases.a v * Work.BoseFixR.ell3 v μ
      * Real.sqrt (Work.BoseFixR.dil v μ)
      * (Work.BoseBox.paramsAt μ (BoseGases.a v)).Kl ^ (-(3 : ℝ)) = μ * BoseGases.a v := by
    simp only [Work.BoseFixR.ell3, Work.BoseFixR.ell, Work.BoseFixR.dil]
    exact mu_sq_a_sideAt_cube_sqrt_Kl_inv_cube hav hμ
  have hbr : (Work.BoseBox.paramsAt μ (BoseGases.a v)).Kl ^ (-(3 : ℝ))
      ≤ ((Work.BoseBox.paramsAt μ (BoseGases.a v)).Kl ^ (-(3 : ℝ)) + Work.BoseFixR.fsX v μ ^ 2
        + (R / BoseGases.a v) ^ 2 * Real.sqrt (Work.BoseFixR.dil v μ)
        + Work.BoseFixR.errExp v μ) := by
    have h2 : 0 ≤ Work.BoseFixR.fsX v μ ^ 2 := sq_nonneg _
    have h3 : 0 ≤ (R / BoseGases.a v) ^ 2 * Real.sqrt (Work.BoseFixR.dil v μ) :=
      mul_nonneg (sq_nonneg _) (Real.sqrt_nonneg _)
    have h4 : 0 ≤ Work.BoseFixR.errExp v μ := by
      rw [Work.BoseFixR.errExp]
      exact Real.rpow_nonneg (by rw [Work.BoseFixR.dil]; positivity) _
    linarith
  have hX : 0 ≤ μ ^ 2 * BoseGases.a v * Work.BoseFixR.ell3 v μ
      * Real.sqrt (Work.BoseFixR.dil v μ) := by
    have h1 : 0 ≤ μ ^ 2 := sq_nonneg μ
    have h2 : 0 ≤ Work.BoseFixR.ell3 v μ := by
      rw [Work.BoseFixR.ell3, Work.BoseFixR.ell]
      exact pow_nonneg (le_of_lt (Work.BoseBox.sideAt_pos hμ hav)) 3
    exact mul_nonneg (mul_nonneg (mul_nonneg h1 hav.le) h2) (Real.sqrt_nonneg _)
  rw [Work.BoseFixR.errKafz]
  calc C * μ * BoseGases.a v
      = C * (μ ^ 2 * BoseGases.a v * Work.BoseFixR.ell3 v μ
          * Real.sqrt (Work.BoseFixR.dil v μ)
          * (Work.BoseBox.paramsAt μ (BoseGases.a v)).Kl ^ (-(3 : ℝ))) := by rw [hiden]; ring
    _ ≤ C * (μ ^ 2 * BoseGases.a v * Work.BoseFixR.ell3 v μ
          * Real.sqrt (Work.BoseFixR.dil v μ)
          * ((Work.BoseBox.paramsAt μ (BoseGases.a v)).Kl ^ (-(3 : ℝ))
            + Work.BoseFixR.fsX v μ ^ 2
            + (R / BoseGases.a v) ^ 2 * Real.sqrt (Work.BoseFixR.dil v μ)
            + Work.BoseFixR.errExp v μ)) := by
        exact mul_le_mul_of_nonneg_left (mul_le_mul_of_nonneg_left hbr hX) hC
    _ = C * μ ^ 2 * BoseGases.a v * Work.BoseFixR.ell3 v μ
          * Real.sqrt (Work.BoseFixR.dil v μ)
          * ((Work.BoseBox.paramsAt μ (BoseGases.a v)).Kl ^ (-(3 : ℝ))
            + Work.BoseFixR.fsX v μ ^ 2
            + (R / BoseGases.a v) ^ 2 * Real.sqrt (Work.BoseFixR.dil v μ)
            + Work.BoseFixR.errExp v μ) := by ring

/-! ## 3. The three arithmetic term bounds -/

/-- `4·cH·(n+1) ≤ 2(8π+C₀)(2+C₀)·μa`. -/
lemma errKafzT1_le {a ℓ μ W0 n C₀ : ℝ} (ha : 0 < a) (hℓ : 0 < ℓ) (hn : 0 ≤ n)
    (hC₀ : 0 ≤ C₀) (hn2 : n ≤ 2 * μ * ℓ ^ 3) (hW00 : 0 ≤ W0) (hW0 : W0 ≤ C₀ * a)
    (hL : ℓ ^ (-(3 : ℝ)) ≤ C₀ * μ) :
    4 * ((1 / 2) * ℓ ^ (-(3 : ℝ)) * (8 * Real.pi * a + W0)) * (n + 1)
    ≤ 2 * (8 * Real.pi + C₀) * (2 + C₀) * (μ * a) := by
  have hLpos : 0 < ℓ ^ (-(3 : ℝ)) := Real.rpow_pos_of_pos hℓ _
  have hLr : ℓ ^ (-(3 : ℝ)) * (μ * ℓ ^ 3) = μ := by
    have h3 : ℓ ^ (-(3 : ℝ)) = (ℓ ^ 3)⁻¹ := by
      rw [Real.rpow_neg hℓ.le]; norm_num
    rw [h3]; field_simp
  have hL2 : ℓ ^ (-(3 : ℝ)) * (2 * (μ * ℓ ^ 3) + 1) ≤ (2 + C₀) * μ := by
    have h : ℓ ^ (-(3 : ℝ)) * (2 * (μ * ℓ ^ 3) + 1) = 2 * μ + ℓ ^ (-(3 : ℝ)) := by
      have h2 : ℓ ^ (-(3 : ℝ)) * (2 * (μ * ℓ ^ 3)) = 2 * μ := by nlinarith [hLr]
      rw [mul_add, mul_one, h2]
    rw [h]; nlinarith
  calc 4 * ((1 / 2) * ℓ ^ (-(3 : ℝ)) * (8 * Real.pi * a + W0)) * (n + 1)
      = 2 * (ℓ ^ (-(3 : ℝ)) * ((8 * Real.pi * a + W0) * (n + 1))) := by ring
    _ ≤ 2 * (ℓ ^ (-(3 : ℝ)) * (((8 * Real.pi + C₀) * a) * (2 * (μ * ℓ ^ 3) + 1))) := by
        gcongr
        · nlinarith
        · linarith
    _ = 2 * ((8 * Real.pi + C₀) * a) * (ℓ ^ (-(3 : ℝ)) * (2 * (μ * ℓ ^ 3) + 1)) := by ring
    _ ≤ 2 * ((8 * Real.pi + C₀) * a) * ((2 + C₀) * μ) := by gcongr
    _ = 2 * (8 * Real.pi + C₀) * (2 + C₀) * (μ * a) := by ring

/-- The two `√`-terms of the model bound are `≤ 40(C₀+1)²·μa`. -/
lemma errKafzT2_le {a ℓ μ M W10 W0 n C₀ : ℝ} (ha : 0 < a) (hℓ : 0 < ℓ) (hμ : 0 < μ)
    (hn : 0 ≤ n) (hC₀ : 0 ≤ C₀) (hbox : 1 ≤ μ * ℓ ^ 3) (hn2 : n ≤ 2 * μ * ℓ ^ 3)
    (hM0 : 0 ≤ M) (hM : M ≤ C₀ * μ * ℓ ^ 3)
    (hW10 : |W10| ≤ C₀ * a) (hW00 : 0 ≤ W0) (hW0 : W0 ≤ C₀ * a)
    (hLr : ℓ ^ (-(3 : ℝ)) * (μ * ℓ ^ 3) = μ) :
    4 * ℓ ^ (-(3 : ℝ)) * (|W10| * Real.sqrt ((48 / Real.pi) * M) + W0 * Real.sqrt M)
        * Real.sqrt (n + 1) ≤ 40 * (C₀ + 1) ^ 2 * (μ * a) := by
  have hr : 0 < μ * ℓ ^ 3 := lt_of_lt_of_le one_pos hbox
  have hMle : M ≤ C₀ * (μ * ℓ ^ 3) := by nlinarith [hM]
  have hsqrtM : Real.sqrt M ≤ Real.sqrt (C₀ * (μ * ℓ ^ 3)) := Real.sqrt_le_sqrt hMle
  have hC0r : 0 ≤ C₀ * (μ * ℓ ^ 3) := by positivity
  have hsqrtn : Real.sqrt (n + 1) ≤ Real.sqrt (3 * (μ * ℓ ^ 3)) :=
    Real.sqrt_le_sqrt (by linarith)
  have hsq : Real.sqrt (C₀ * (μ * ℓ ^ 3)) * Real.sqrt (3 * (μ * ℓ ^ 3))
      = Real.sqrt (3 * C₀) * (μ * ℓ ^ 3) := by
    rw [← Real.sqrt_mul hC0r (3 * (μ * ℓ ^ 3)),
        show C₀ * (μ * ℓ ^ 3) * (3 * (μ * ℓ ^ 3)) = (3 * C₀) * (μ * ℓ ^ 3) ^ 2 by ring,
        Real.sqrt_mul (by positivity : (0 : ℝ) ≤ 3 * C₀), Real.sqrt_sq hr.le]
  have hS4 : Real.sqrt (48 / Real.pi) ≤ 4 := by
    rw [← Real.sqrt_sq (by norm_num : (0 : ℝ) ≤ 4)]
    apply Real.sqrt_le_sqrt
    rw [div_le_iff₀ Real.pi_pos]
    nlinarith [Real.pi_gt_three]
  have h3C : Real.sqrt (3 * C₀) ≤ 2 * (C₀ + 1) := by
    rw [← Real.sqrt_sq (by positivity : (0 : ℝ) ≤ 2 * (C₀ + 1))]
    apply Real.sqrt_le_sqrt
    nlinarith
  have hbr : |W10| * Real.sqrt ((48 / Real.pi) * M) + W0 * Real.sqrt M
      ≤ C₀ * a * (Real.sqrt (48 / Real.pi) + 1) * Real.sqrt (C₀ * (μ * ℓ ^ 3)) := by
    have h1 : |W10| * Real.sqrt ((48 / Real.pi) * M)
        ≤ C₀ * a * Real.sqrt (48 / Real.pi) * Real.sqrt (C₀ * (μ * ℓ ^ 3)) := by
      rw [Real.sqrt_mul (by positivity : (0 : ℝ) ≤ 48 / Real.pi) M]
      calc |W10| * (Real.sqrt (48 / Real.pi) * Real.sqrt M)
          = |W10| * Real.sqrt (48 / Real.pi) * Real.sqrt M := by ring
        _ ≤ C₀ * a * Real.sqrt (48 / Real.pi) * Real.sqrt (C₀ * (μ * ℓ ^ 3)) := by gcongr
    have h2 : W0 * Real.sqrt M ≤ C₀ * a * Real.sqrt (C₀ * (μ * ℓ ^ 3)) := by gcongr
    nlinarith [h1, h2]
  have hS5 : Real.sqrt (48 / Real.pi) + 1 ≤ 5 := by linarith
  have hmain : C₀ * (Real.sqrt (48 / Real.pi) + 1) * Real.sqrt (3 * C₀) ≤ 10 * (C₀ + 1) ^ 2 := by
    have hs1 : C₀ * (Real.sqrt (48 / Real.pi) + 1) * Real.sqrt (3 * C₀)
        ≤ C₀ * 5 * Real.sqrt (3 * C₀) := by
      apply mul_le_mul_of_nonneg_right _ (Real.sqrt_nonneg _)
      exact mul_le_mul_of_nonneg_left hS5 hC₀
    have hs2 : C₀ * 5 * Real.sqrt (3 * C₀) ≤ C₀ * 5 * (2 * (C₀ + 1)) :=
      mul_le_mul_of_nonneg_left h3C (by positivity)
    have hs4 : 10 * C₀ * (C₀ + 1) ≤ 10 * (C₀ + 1) ^ 2 := by nlinarith
    linarith [hs1, hs2, hs4]
  calc 4 * ℓ ^ (-(3 : ℝ)) * (|W10| * Real.sqrt ((48 / Real.pi) * M) + W0 * Real.sqrt M)
        * Real.sqrt (n + 1)
      ≤ 4 * ℓ ^ (-(3 : ℝ)) * (C₀ * a * (Real.sqrt (48 / Real.pi) + 1)
          * Real.sqrt (C₀ * (μ * ℓ ^ 3))) * Real.sqrt (3 * (μ * ℓ ^ 3)) := by gcongr
    _ = 4 * C₀ * a * (Real.sqrt (48 / Real.pi) + 1)
          * (ℓ ^ (-(3 : ℝ))
              * (Real.sqrt (C₀ * (μ * ℓ ^ 3)) * Real.sqrt (3 * (μ * ℓ ^ 3)))) := by ring
    _ = 4 * C₀ * a * (Real.sqrt (48 / Real.pi) + 1) * (Real.sqrt (3 * C₀) * μ) := by
        rw [hsq, show ℓ ^ (-(3 : ℝ)) * (Real.sqrt (3 * C₀) * (μ * ℓ ^ 3))
              = Real.sqrt (3 * C₀) * (ℓ ^ (-(3 : ℝ)) * (μ * ℓ ^ 3)) by ring, hLr]
    _ ≤ 40 * (C₀ + 1) ^ 2 * (μ * a) := by
        have hfac : 0 ≤ 4 * a * μ := by positivity
        calc 4 * C₀ * a * (Real.sqrt (48 / Real.pi) + 1) * (Real.sqrt (3 * C₀) * μ)
            = 4 * a * μ * (C₀ * (Real.sqrt (48 / Real.pi) + 1) * Real.sqrt (3 * C₀)) := by ring
          _ ≤ 4 * a * μ * (10 * (C₀ + 1) ^ 2) := mul_le_mul_of_nonneg_left hmain hfac
          _ = 40 * (C₀ + 1) ^ 2 * (μ * a) := by ring

/-- The `(ρ_z−μ)`-term of the model bound is `≤ ((8π+C₀)C₀ + 8π + (192/π)C₀²)·μa`. -/
lemma errKafzT3_le {a ℓ μ M W10 W0 C₀ : ℝ} (ha : 0 < a) (hℓ : 0 < ℓ) (hμ : 0 < μ)
    (hC₀ : 0 ≤ C₀) (hbox : 1 ≤ μ * ℓ ^ 3)
    (hM0 : 0 ≤ M) (hM : M ≤ C₀ * μ * ℓ ^ 3)
    (hW10 : |W10| ≤ C₀ * a) (hW00 : 0 ≤ W0) (hW0 : W0 ≤ C₀ * a)
    (hL : ℓ ^ (-(3 : ℝ)) ≤ C₀ * μ) (hLr : ℓ ^ (-(3 : ℝ)) * (μ * ℓ ^ 3) = μ) :
    |2 * ((1 / 2) * ℓ ^ (-(3 : ℝ)) * (8 * Real.pi * a + W0)) + μ * (8 * Real.pi * a)|
      + ℓ ^ (-(3 : ℝ)) * (2 * C₀ * a + |W10 + W0|) * ((48 / Real.pi) * M)
    ≤ ((8 * Real.pi + C₀) * C₀ + 8 * Real.pi + (192 / Real.pi) * C₀ ^ 2) * (μ * a) := by
  have hLnn : 0 ≤ ℓ ^ (-(3 : ℝ)) := le_of_lt (Real.rpow_pos_of_pos hℓ _)
  have hA : ℓ ^ (-(3 : ℝ)) * (8 * Real.pi * a + W0) + μ * (8 * Real.pi * a)
      ≤ ((8 * Real.pi + C₀) * C₀ + 8 * Real.pi) * (μ * a) := by
    have hA1 : ℓ ^ (-(3 : ℝ)) * (8 * Real.pi * a + W0)
        ≤ ℓ ^ (-(3 : ℝ)) * ((8 * Real.pi + C₀) * a) := by
      apply mul_le_mul_of_nonneg_left _ hLnn
      nlinarith
    have hA2 : ℓ ^ (-(3 : ℝ)) * ((8 * Real.pi + C₀) * a)
        ≤ (C₀ * μ) * ((8 * Real.pi + C₀) * a) := by
      apply mul_le_mul_of_nonneg_right hL
      positivity
    have hA3 : (C₀ * μ) * ((8 * Real.pi + C₀) * a) = ((8 * Real.pi + C₀) * C₀) * (μ * a) := by
      ring
    nlinarith [hA1, hA2, hA3]
  have hB : ℓ ^ (-(3 : ℝ)) * (2 * C₀ * a + |W10 + W0|) * ((48 / Real.pi) * M)
      ≤ (192 / Real.pi) * C₀ ^ 2 * (μ * a) := by
    have hB0 : |W10 + W0| ≤ 2 * C₀ * a := by
      have hW0abs : |W0| = W0 := abs_of_nonneg hW00
      calc |W10 + W0| ≤ |W10| + |W0| := abs_add_le _ _
        _ ≤ C₀ * a + C₀ * a := by rw [hW0abs]; linarith
        _ = 2 * C₀ * a := by ring
    have hB1 : 2 * C₀ * a + |W10 + W0| ≤ 4 * C₀ * a := by linarith
    have hB2 : ℓ ^ (-(3 : ℝ)) * (2 * C₀ * a + |W10 + W0|) * ((48 / Real.pi) * M)
        ≤ ℓ ^ (-(3 : ℝ)) * (4 * C₀ * a) * ((48 / Real.pi) * M) := by gcongr
    have hB3 : ℓ ^ (-(3 : ℝ)) * (4 * C₀ * a) * ((48 / Real.pi) * M)
        ≤ ℓ ^ (-(3 : ℝ)) * (4 * C₀ * a) * ((48 / Real.pi) * (C₀ * μ * ℓ ^ 3)) := by gcongr
    have hB4 : ℓ ^ (-(3 : ℝ)) * (4 * C₀ * a) * ((48 / Real.pi) * (C₀ * μ * ℓ ^ 3))
        = (192 / Real.pi) * C₀ ^ 2 * (μ * a) := by
      rw [show ℓ ^ (-(3 : ℝ)) * (4 * C₀ * a) * ((48 / Real.pi) * (C₀ * μ * ℓ ^ 3))
            = (4 * C₀ * a * (48 / Real.pi) * C₀) * (ℓ ^ (-(3 : ℝ)) * (μ * ℓ ^ 3)) by ring, hLr]
      ring
    linarith [hB2, hB3, hB4]
  have habs : |2 * ((1 / 2) * ℓ ^ (-(3 : ℝ)) * (8 * Real.pi * a + W0)) + μ * (8 * Real.pi * a)|
      = ℓ ^ (-(3 : ℝ)) * (8 * Real.pi * a + W0) + μ * (8 * Real.pi * a) := by
    rw [show 2 * ((1 / 2) * ℓ ^ (-(3 : ℝ)) * (8 * Real.pi * a + W0))
          = ℓ ^ (-(3 : ℝ)) * (8 * Real.pi * a + W0) by ring]
    exact abs_of_nonneg (by positivity)
  rw [habs]
  linarith

/-- **The five-term arithmetic of `errKafz_dominates_uniform`**, with the explicit
constant `1 + 2(8π+C₀)(2+C₀) + 40(C₀+1)² + (8π+C₀)C₀ + 8π + (192/π)C₀²`. -/
lemma kafz_terms_le {a ℓ μ M W10 W0 n C₀ : ℝ}
    (ha : 0 < a) (hℓ : 0 < ℓ) (hμ : 0 < μ) (hC₀ : 0 ≤ C₀) (hn : 0 ≤ n)
    (hbox : 1 ≤ μ * ℓ ^ 3) (hL : ℓ ^ (-(3 : ℝ)) ≤ C₀ * μ)
    (hM0 : 0 ≤ M) (hM : M ≤ C₀ * μ * ℓ ^ 3)
    (hW10 : |W10| ≤ C₀ * a) (hW00 : 0 ≤ W0) (hW0 : W0 ≤ C₀ * a)
    (hn2 : n ≤ 2 * μ * ℓ ^ 3) :
    4 * ((1 / 2) * ℓ ^ (-(3 : ℝ)) * (8 * Real.pi * a + W0)) * (n + 1)
      + 4 * ℓ ^ (-(3 : ℝ)) * (|W10| * Real.sqrt ((48 / Real.pi) * M) + W0 * Real.sqrt M)
          * Real.sqrt (n + 1)
      + (|2 * ((1 / 2) * ℓ ^ (-(3 : ℝ)) * (8 * Real.pi * a + W0)) + μ * (8 * Real.pi * a)|
          + ℓ ^ (-(3 : ℝ)) * (2 * C₀ * a + |W10 + W0|) * ((48 / Real.pi) * M))
    ≤ (1 + 2 * (8 * Real.pi + C₀) * (2 + C₀) + 40 * (C₀ + 1) ^ 2
        + (8 * Real.pi + C₀) * C₀ + 8 * Real.pi + (192 / Real.pi) * C₀ ^ 2) * μ * a := by
  have hLr : ℓ ^ (-(3 : ℝ)) * (μ * ℓ ^ 3) = μ := by
    have h3 : ℓ ^ (-(3 : ℝ)) = (ℓ ^ 3)⁻¹ := by
      rw [Real.rpow_neg hℓ.le]; norm_num
    rw [h3]; field_simp
  have h1 := errKafzT1_le ha hℓ hn hC₀ hn2 hW00 hW0 hL
  have h2 := errKafzT2_le ha hℓ hμ hn hC₀ hbox hn2 hM0 hM hW10 hW00 hW0 hLr
  have h3 := errKafzT3_le ha hℓ hμ hC₀ hbox hM0 hM hW10 hW00 hW0 hL hLr
  have hμa : 0 ≤ μ * a := by positivity
  nlinarith [h1, h2, h3]

/-! ## 4. `0 < E.bigM` for the honest family -/

/-- `E.bigM = 𝓜 = K_M (μa³)^{-1/4} > 0`. -/
lemma honestFam_bigM_pos (v : ℝ³ → ℝ) (h : Work.UBB.ScatSol v)
    (fc fu : Work.BoseBoxFix.LowCut) (HM : ∀ μ : ℝ, Work.BoseBoxFock.HonestModes v μ)
    {μ : ℝ} (hμ : 0 < μ) (hav : 0 < BoseGases.a v) :
    0 < (HonestBoxFam v h fc fu HM μ).E.bigM := by
  have ht : 0 < μ * BoseGases.a v ^ 3 := by positivity
  show 0 < Work.BoseBox.fsXp (μ * BoseGases.a v ^ 3) (-1)
    * (μ * BoseGases.a v ^ 3) ^ (-(1 / 4 : ℝ))
  exact mul_pos (Work.BoseBox.fsXp_pos ht) (Real.rpow_pos_of_pos ht _)

theorem errKafz_dominates_uniform (v : ℝ³ → ℝ) (h : Work.UBB.ScatSol v) (hv : 0 ≤ v)
    (hv1 : MeasureTheory.MemLp v 1) (hvrad : _root_.BoseGases.IsRadial v) {R : ℝ} (hR : 0 < R)
    (hv_supp : tsupport v ⊆ Metric.ball (0 : ℝ³) R) (hav : 0 < BoseGases.a v)
    (fc fu : Work.BoseBoxFix.LowCut)
    (ε₀ C₀ : ℝ) (hε₀ : 0 < ε₀) (hC₀ : 0 ≤ C₀)
    (hEnv : ∀ (HM : ∀ μ : ℝ, Work.BoseBoxFock.HonestModes v μ) (μ : ℝ),
        Work.BoseBoxFix.Adm v ε₀ μ → EnvFactsAt v h fc fu HM μ C₀) :
    ∃ C : ℝ, 0 ≤ C ∧
      ∀ (HM : ∀ μ : ℝ, Work.BoseBoxFock.HonestModes v μ) (μ : ℝ),
        Work.BoseBoxFix.Adm v ε₀ μ → ∀ n : ℕ,
      (n : ℝ) ≤ 2 * μ * (HonestBoxFam v h fc fu HM μ).E.ell ^ 3 →
      (0 ≤ (HonestBoxFam v h fc fu HM μ).E.bigM)
      ∧ (0 ≤ (48 / Real.pi) * (HonestBoxFam v h fc fu HM μ).E.bigM)
      ∧ (0 ≤ 4 * cHCF (HonestBoxFam v h fc fu HM μ).E (8 * π * BoseGases.a v))
      ∧ (0 ≤ 4 * (HonestBoxFam v h fc fu HM μ).E.ell ^ (-(3 : ℝ))
            * (|(HonestBoxFam v h fc fu HM μ).E.W1 0|
                * Real.sqrt ((48 / Real.pi) * (HonestBoxFam v h fc fu HM μ).E.bigM)
              + (HonestBoxFam v h fc fu HM μ).E.W1omega0
                * Real.sqrt (HonestBoxFam v h fc fu HM μ).E.bigM))
      ∧ (4 * cHCF (HonestBoxFam v h fc fu HM μ).E (8 * π * BoseGases.a v) * ((n : ℝ) + 1)
        + 4 * (HonestBoxFam v h fc fu HM μ).E.ell ^ (-(3 : ℝ))
            * (|(HonestBoxFam v h fc fu HM μ).E.W1 0|
                * Real.sqrt ((48 / Real.pi) * (HonestBoxFam v h fc fu HM μ).E.bigM)
              + (HonestBoxFam v h fc fu HM μ).E.W1omega0
                * Real.sqrt (HonestBoxFam v h fc fu HM μ).E.bigM)
            * Real.sqrt ((n : ℝ) + 1)
        + (|2 * cHCF (HonestBoxFam v h fc fu HM μ).E (8 * π * BoseGases.a v)
              + μ * (8 * π * BoseGases.a v)|
            + (HonestBoxFam v h fc fu HM μ).E.ell ^ (-(3 : ℝ))
              * (2 * C₀ * BoseGases.a v
                  + |(HonestBoxFam v h fc fu HM μ).E.W1 0
                      + (HonestBoxFam v h fc fu HM μ).E.W1omega0|)
              * ((48 / Real.pi) * (HonestBoxFam v h fc fu HM μ).E.bigM)))
        ≤ Work.BoseFixR.errKafz v R μ C := by
  refine ⟨1 + 2 * (8 * π + C₀) * (2 + C₀) + 40 * (C₀ + 1) ^ 2 + (8 * π + C₀) * C₀
    + 8 * π + (192 / π) * C₀ ^ 2, ?_, ?_⟩
  · positivity
  · intro HM μ hAdm n hn
    have hμ : 0 < μ := hAdm.1
    obtain ⟨hell_pos, -, -, hbox, hLin, hMle, hW1le, -, hWω00, hWω0le, -, hcH0, -, -, -, -⟩ :=
      hEnv HM μ hAdm
    have hbigM0 : 0 ≤ (HonestBoxFam v h fc fu HM μ).E.bigM :=
      le_of_lt (honestFam_bigM_pos v h fc fu HM hμ hav)
    have hC : 0 ≤ (1 + 2 * (8 * π + C₀) * (2 + C₀) + 40 * (C₀ + 1) ^ 2 + (8 * π + C₀) * C₀
        + 8 * π + (192 / π) * C₀ ^ 2 : ℝ) := by positivity
    refine ⟨hbigM0, ?_, ?_, ?_, ?_⟩
    · exact mul_nonneg (by positivity) hbigM0
    · exact mul_nonneg (by norm_num) hcH0
    · have hℓ3 : 0 ≤ (HonestBoxFam v h fc fu HM μ).E.ell ^ (-(3 : ℝ)) :=
        Real.rpow_nonneg hell_pos.le _
      have h1 : 0 ≤ |(HonestBoxFam v h fc fu HM μ).E.W1 0|
          * Real.sqrt ((48 / Real.pi) * (HonestBoxFam v h fc fu HM μ).E.bigM) :=
        mul_nonneg (abs_nonneg _) (Real.sqrt_nonneg _)
      have h2 : 0 ≤ (HonestBoxFam v h fc fu HM μ).E.W1omega0
          * Real.sqrt (HonestBoxFam v h fc fu HM μ).E.bigM :=
        mul_nonneg hWω00 (Real.sqrt_nonneg _)
      exact mul_nonneg (mul_nonneg (by norm_num) hℓ3) (add_nonneg h1 h2)
    · have hkey : 4 * cHCF (HonestBoxFam v h fc fu HM μ).E (8 * π * BoseGases.a v)
            * ((n : ℝ) + 1)
          + 4 * (HonestBoxFam v h fc fu HM μ).E.ell ^ (-(3 : ℝ))
              * (|(HonestBoxFam v h fc fu HM μ).E.W1 0|
                  * Real.sqrt ((48 / Real.pi) * (HonestBoxFam v h fc fu HM μ).E.bigM)
                + (HonestBoxFam v h fc fu HM μ).E.W1omega0
                  * Real.sqrt (HonestBoxFam v h fc fu HM μ).E.bigM)
              * Real.sqrt ((n : ℝ) + 1)
          + (|2 * cHCF (HonestBoxFam v h fc fu HM μ).E (8 * π * BoseGases.a v)
                + μ * (8 * π * BoseGases.a v)|
              + (HonestBoxFam v h fc fu HM μ).E.ell ^ (-(3 : ℝ))
                * (2 * C₀ * BoseGases.a v
                    + |(HonestBoxFam v h fc fu HM μ).E.W1 0
                        + (HonestBoxFam v h fc fu HM μ).E.W1omega0|)
                * ((48 / Real.pi) * (HonestBoxFam v h fc fu HM μ).E.bigM))
        ≤ (1 + 2 * (8 * π + C₀) * (2 + C₀) + 40 * (C₀ + 1) ^ 2 + (8 * π + C₀) * C₀
            + 8 * π + (192 / π) * C₀ ^ 2) * μ * BoseGases.a v := by
        simpa only [cHCF, i3F] using
          (kafz_terms_le (a := BoseGases.a v) (ℓ := (HonestBoxFam v h fc fu HM μ).E.ell)
            (μ := μ) (M := (HonestBoxFam v h fc fu HM μ).E.bigM)
            (W10 := (HonestBoxFam v h fc fu HM μ).E.W1 0)
            (W0 := (HonestBoxFam v h fc fu HM μ).E.W1omega0)
            (n := (n : ℝ)) (C₀ := C₀) hav hell_pos hμ hC₀ (Nat.cast_nonneg n) hbox hLin
            hbigM0 hMle (hW1le 0) hWω00 hWω0le hn)
      exact le_trans hkey (errKafz_ge v hμ hav hC)

end Work.BoseBoxFock
