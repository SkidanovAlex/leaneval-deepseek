import Mathlib
import Submission.Work.Defs.Basic

open Filter Asymptotics

namespace Work.Tower.MinkowskiGS.Numeric

/-- The exponent `(2/3)(C_A · ℓ · log ℓ + C_A)` that bounds `log R` from above. -/
private noncomputable def Xexpr (C_A : ℝ) (ℓ : ℕ) : ℝ :=
  (2 / 3) * (C_A * (ℓ : ℝ) * Real.log ℓ + C_A)

private theorem Xexpr_nonneg {C_A : ℝ} (hCA : 0 < C_A) (ℓ : ℕ) : 0 ≤ Xexpr C_A ℓ := by
  have hℓ : (0 : ℝ) ≤ (ℓ : ℝ) * Real.log ℓ := by
    rcases Nat.eq_zero_or_pos ℓ with h0 | hpos
    · simp [h0]
    · have h1 : (1 : ℝ) ≤ (ℓ : ℝ) := by exact_mod_cast hpos
      exact mul_nonneg (by linarith) (Real.log_nonneg h1)
  unfold Xexpr
  nlinarith [mul_nonneg hCA.le hℓ]

/-! ### Little-o facts: `log` is negligible compared to `n²` -/

private theorem log_cast_isLittleO :
    (fun ℓ : ℕ => Real.log (ℓ : ℝ)) =o[atTop] (fun ℓ : ℕ => (ℓ : ℝ)) := by
  simpa [Function.comp_def] using
    Real.isLittleO_log_id_atTop.comp_tendsto (tendsto_natCast_atTop_atTop (R := ℝ))

private theorem id_mul_log_isLittleO :
    (fun ℓ : ℕ => (ℓ : ℝ) * Real.log ℓ) =o[atTop] (fun ℓ : ℕ => (ℓ : ℝ) ^ 2) := by
  have h := log_cast_isLittleO.mul_isBigO (isBigO_refl (fun ℓ : ℕ => (ℓ : ℝ)) atTop)
  exact h.congr (fun ℓ => mul_comm _ _) (fun ℓ => (pow_two _).symm)

private theorem const_isLittleO_sq (c : ℝ) :
    (fun _ : ℕ => c) =o[atTop] (fun ℓ : ℕ => (ℓ : ℝ) ^ 2) := by
  rw [isLittleO_const_left]
  refine Or.inr ?_
  have h : Tendsto (fun ℓ : ℕ => (ℓ : ℝ) ^ 2) atTop atTop :=
    (tendsto_pow_atTop two_ne_zero).comp tendsto_natCast_atTop_atTop
  refine h.congr' (Eventually.of_forall fun ℓ => ?_)
  show (ℓ : ℝ) ^ 2 = ‖(ℓ : ℝ) ^ 2‖
  rw [Real.norm_eq_abs, abs_of_nonneg (sq_nonneg _)]

private theorem Xexpr_isLittleO (C_A : ℝ) :
    (fun ℓ : ℕ => Xexpr C_A ℓ) =o[atTop] (fun ℓ : ℕ => (ℓ : ℝ) ^ 2) := by
  have h1 : (fun ℓ : ℕ => C_A * ((ℓ : ℝ) * Real.log ℓ))
      =o[atTop] (fun ℓ : ℕ => (ℓ : ℝ) ^ 2) := id_mul_log_isLittleO.const_mul_left C_A
  have h2 : (fun _ : ℕ => C_A) =o[atTop] (fun ℓ : ℕ => (ℓ : ℝ) ^ 2) :=
    const_isLittleO_sq C_A
  have h4 := (h1.add h2).const_mul_left (2 / 3 : ℝ)
  refine h4.congr (fun ℓ => ?_) (fun ℓ => rfl)
  unfold Xexpr
  ring

private theorem log_one_add_Xexpr_isLittleO (C_A : ℝ) (hCA : 0 < C_A) :
    (fun ℓ : ℕ => Real.log (1 + Xexpr C_A ℓ)) =o[atTop] (fun ℓ : ℕ => (ℓ : ℝ) ^ 2) := by
  have hO : (fun ℓ : ℕ => Real.log (1 + Xexpr C_A ℓ)) =O[atTop] (fun ℓ : ℕ => Xexpr C_A ℓ) := by
    rw [isBigO_iff]
    refine ⟨1, Eventually.of_forall fun ℓ => ?_⟩
    have hx : (0 : ℝ) ≤ Xexpr C_A ℓ := Xexpr_nonneg hCA ℓ
    have h1 : (0 : ℝ) ≤ Real.log (1 + Xexpr C_A ℓ) := Real.log_nonneg (by linarith)
    have h2 : Real.log (1 + Xexpr C_A ℓ) ≤ Xexpr C_A ℓ := by
      have := Real.log_le_sub_one_of_pos (show (0 : ℝ) < 1 + Xexpr C_A ℓ by linarith)
      linarith
    rw [one_mul, Real.norm_eq_abs, Real.norm_eq_abs, abs_of_nonneg h1, abs_of_nonneg hx]
    exact h2
  exact hO.trans_isLittleO (Xexpr_isLittleO C_A)

/-- The explicit upper bound on `4·dimCl + 8`, as a function of `ℓ`, is `o(ℓ²)`. -/
private theorem B_isLittleO (C_A : ℝ) (hCA : 0 < C_A) (C_M : ℝ) (hCM : 0 < C_M) :
    (fun ℓ : ℕ => 12 * Real.logb 3 (C_M * Real.exp (Xexpr C_A ℓ) * (1 + Xexpr C_A ℓ)) + 8)
      =o[atTop] (fun ℓ : ℕ => (ℓ : ℝ) ^ 2) := by
  have hlog3 : (0 : ℝ) < Real.log 3 := Real.log_pos (by norm_num)
  have heq : ∀ ℓ : ℕ,
      12 * Real.logb 3 (C_M * Real.exp (Xexpr C_A ℓ) * (1 + Xexpr C_A ℓ)) + 8
        = ((12 / Real.log 3) * Real.log C_M + 8)
          + ((12 / Real.log 3) * Xexpr C_A ℓ
              + (12 / Real.log 3) * Real.log (1 + Xexpr C_A ℓ)) := by
    intro ℓ
    have hx : (0 : ℝ) ≤ Xexpr C_A ℓ := Xexpr_nonneg hCA ℓ
    have e1 : Real.log (C_M * Real.exp (Xexpr C_A ℓ) * (1 + Xexpr C_A ℓ))
        = Real.log C_M + Xexpr C_A ℓ + Real.log (1 + Xexpr C_A ℓ) := by
      rw [Real.log_mul (mul_ne_zero (ne_of_gt hCM) (Real.exp_ne_zero _))
            (ne_of_gt (by linarith : (0 : ℝ) < 1 + Xexpr C_A ℓ)),
          Real.log_mul (ne_of_gt hCM) (Real.exp_ne_zero _), Real.log_exp]
    rw [show Real.logb 3 (C_M * Real.exp (Xexpr C_A ℓ) * (1 + Xexpr C_A ℓ))
          = Real.log (C_M * Real.exp (Xexpr C_A ℓ) * (1 + Xexpr C_A ℓ)) / Real.log 3 from rfl,
        e1]
    field_simp [hlog3.ne']
    ring
  have h1 : (fun _ : ℕ => (12 / Real.log 3) * Real.log C_M + 8)
      =o[atTop] (fun ℓ : ℕ => (ℓ : ℝ) ^ 2) := const_isLittleO_sq _
  have h2 : (fun ℓ : ℕ => (12 / Real.log 3) * Xexpr C_A ℓ)
      =o[atTop] (fun ℓ : ℕ => (ℓ : ℝ) ^ 2) := (Xexpr_isLittleO C_A).const_mul_left _
  have h3 : (fun ℓ : ℕ => (12 / Real.log 3) * Real.log (1 + Xexpr C_A ℓ))
      =o[atTop] (fun ℓ : ℕ => (ℓ : ℝ) ^ 2) :=
    (log_one_add_Xexpr_isLittleO C_A hCA).const_mul_left _
  exact (h1.add (h2.add h3)).congr (fun ℓ => (heq ℓ).symm) (fun ℓ => rfl)

/-- For any positive constants `C_A`, `C_M` and all sufficiently large `ℓ`, the
`dimension`-clause bound is dominated by `(ℓ-1)²` minus the `t`-contribution. -/
theorem minkowski_numeric_dimCl_eventually
    (C_A : ℝ) (hCA : 0 < C_A) (C_M : ℝ) (hCM : 0 < C_M) :
    ∃ ℓ₀ : ℕ, 0 < ℓ₀ ∧ ∀ ℓ : ℕ, ℓ₀ ≤ ℓ → ∀ (r : Fin ℓ → ℕ) (R : ℝ) (t : ℕ),
      (∀ i, Nat.Prime (r i)) → (∀ i, r i % 3 = 1) →
      (∑ i, Real.log (r i : ℝ)) ≤ C_A * (ℓ : ℝ) * Real.log ℓ + C_A →
      R = Real.exp ((2 / 3) * ∑ i, Real.log (r i : ℝ)) →
      t = ((ℓ - 1) ^ 2) / 100 →
      (∀ dimCl : ℕ, (dimCl : ℝ) ≤ 3 * Real.logb 3 (C_M * R * (1 + Real.log R)) →
        (((ℓ - 1 : ℕ) : ℝ)) ^ 2 > 4 * ((dimCl : ℝ) + 2 + 3 * (t : ℝ))) := by
  have hB := B_isLittleO C_A hCA C_M hCM
  rw [isLittleO_iff] at hB
  obtain ⟨ℓ₁, hℓ₁⟩ := eventually_atTop.mp (hB (show (0 : ℝ) < 11 / 100 by norm_num))
  refine ⟨max 2 ℓ₁, lt_of_lt_of_le (show (0 : ℕ) < 2 by norm_num) (le_max_left 2 ℓ₁), ?_⟩
  intro ℓ hℓ r R t hprime hmod3 hS hR ht dimCl hdim
  have hℓ2 : 2 ≤ ℓ := le_trans (le_max_left 2 ℓ₁) hℓ
  have hℓ1 : 1 ≤ ℓ := by omega
  -- the little-o bound, at the specific `ℓ`
  have hbound : ‖12 * Real.logb 3 (C_M * Real.exp (Xexpr C_A ℓ) * (1 + Xexpr C_A ℓ)) + 8‖
      ≤ (11 / 100) * ‖(ℓ : ℝ) ^ 2‖ := hℓ₁ ℓ (le_trans (le_max_right 2 ℓ₁) hℓ)
  have hbound' : 12 * Real.logb 3 (C_M * Real.exp (Xexpr C_A ℓ) * (1 + Xexpr C_A ℓ)) + 8
      ≤ (11 / 100) * (ℓ : ℝ) ^ 2 := by
    have h := hbound
    simp only [Real.norm_eq_abs, abs_of_nonneg (sq_nonneg ((ℓ : ℝ)))] at h
    exact le_trans (le_abs_self _) h
  -- basic positivity of the sum of logs
  have hSnn : 0 ≤ ∑ i, Real.log (r i : ℝ) := by
    refine Finset.sum_nonneg fun i _ => ?_
    have hp : 2 ≤ r i := (hprime i).two_le
    exact Real.log_nonneg (by exact_mod_cast (show (1 : ℕ) ≤ r i by omega))
  have hXbound : (2 / 3 : ℝ) * (∑ i, Real.log (r i : ℝ)) ≤ Xexpr C_A ℓ := by
    unfold Xexpr
    linarith [hS]
  have hlogR : Real.log R = (2 / 3 : ℝ) * (∑ i, Real.log (r i : ℝ)) := by
    rw [hR, Real.log_exp]
  have hRle : R ≤ Real.exp (Xexpr C_A ℓ) := by
    rw [hR]
    exact Real.exp_le_exp.mpr hXbound
  have hRpos : 0 < R := by
    rw [hR]; exact Real.exp_pos _
  have h1R : (0 : ℝ) < 1 + Real.log R := by
    rw [hlogR]; linarith [hSnn]
  have hXnn : (0 : ℝ) ≤ Xexpr C_A ℓ := Xexpr_nonneg hCA ℓ
  have harg1 : (0 : ℝ) < C_M * R * (1 + Real.log R) :=
    mul_pos (mul_pos hCM hRpos) h1R
  have hargle : C_M * R * (1 + Real.log R)
      ≤ C_M * Real.exp (Xexpr C_A ℓ) * (1 + Xexpr C_A ℓ) := by
    have hstep : R * (1 + Real.log R) ≤ Real.exp (Xexpr C_A ℓ) * (1 + Xexpr C_A ℓ) :=
      mul_le_mul hRle (by rw [hlogR]; linarith [hXbound]) h1R.le (Real.exp_pos _).le
    calc C_M * R * (1 + Real.log R) = C_M * (R * (1 + Real.log R)) := by ring
      _ ≤ C_M * (Real.exp (Xexpr C_A ℓ) * (1 + Xexpr C_A ℓ)) :=
          mul_le_mul_of_nonneg_left hstep hCM.le
      _ = C_M * Real.exp (Xexpr C_A ℓ) * (1 + Xexpr C_A ℓ) := by ring
  have hlogb_le : Real.logb 3 (C_M * R * (1 + Real.log R))
      ≤ Real.logb 3 (C_M * Real.exp (Xexpr C_A ℓ) * (1 + Xexpr C_A ℓ)) :=
    Real.logb_le_logb_of_le (by norm_num) harg1 hargle
  have hdim4 : 4 * (dimCl : ℝ) + 8
      ≤ 12 * Real.logb 3 (C_M * Real.exp (Xexpr C_A ℓ) * (1 + Xexpr C_A ℓ)) + 8 := by
    linarith [hdim, hlogb_le]
  -- the `t`-term
  have ht_bound : (t : ℝ) ≤ (((ℓ - 1 : ℕ) : ℝ)) ^ 2 / 100 := by
    have h1 : (t : ℝ) = ((((ℓ - 1) ^ 2) / 100 : ℕ) : ℝ) := by rw [ht]
    rw [h1]
    refine le_trans Nat.cast_div_le (le_of_eq ?_)
    rw [Nat.cast_pow]
    norm_num
  -- `ℓ² ≤ 4(ℓ-1)²` for `ℓ ≥ 2`
  have hsq_le : (ℓ : ℝ) ^ 2 ≤ 4 * (((ℓ - 1 : ℕ) : ℝ)) ^ 2 := by
    have hcast : ((ℓ - 1 : ℕ) : ℝ) = (ℓ : ℝ) - 1 := by
      rw [Nat.cast_sub hℓ1, Nat.cast_one]
    rw [hcast]
    have hℓ2' : (2 : ℝ) ≤ (ℓ : ℝ) := by exact_mod_cast hℓ2
    nlinarith [mul_nonneg (show (0 : ℝ) ≤ (ℓ : ℝ) - 2 by linarith)
      (show (0 : ℝ) ≤ 3 * (ℓ : ℝ) - 2 by linarith)]
  have hU : (1 : ℝ) ≤ (((ℓ - 1 : ℕ) : ℝ)) ^ 2 := by
    have h1 : (1 : ℕ) ≤ ℓ - 1 := by omega
    have h2 : (1 : ℝ) ≤ ((ℓ - 1 : ℕ) : ℝ) := by exact_mod_cast h1
    nlinarith [mul_nonneg (show (0 : ℝ) ≤ ((ℓ - 1 : ℕ) : ℝ) - 1 by linarith)
      (show (0 : ℝ) ≤ ((ℓ - 1 : ℕ) : ℝ) + 1 by linarith)]
  linarith [hdim4, hbound', ht_bound, hsq_le, hU]

end Work.Tower.MinkowskiGS.Numeric
