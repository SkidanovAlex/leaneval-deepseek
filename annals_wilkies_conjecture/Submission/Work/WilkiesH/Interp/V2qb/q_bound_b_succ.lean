import Mathlib
import Submission.Work.WilkiesH.Interp.V2Params

set_option autoImplicit false
set_option maxHeartbeats 2000000
noncomputable section
open Classical

namespace Work.WilkiesH.Interp.V2qb

open Work.WilkiesH.Interp

/-! ## Elementary numerical estimates for the `b + 1` bound of `qPoly`

The polynomial `qPoly μ` evaluates (see `qPol_eval`) to

`CCc μ · (1 + D) · (1 + g)^(Ec μ) · (1 + log H)^(Fc μ)`,

and the flatness order is `bV μ g H = EE μ · (g+1)^(AA μ) · (lgNat H)^(BB μ)`.
The following elementary comparisons give `bV + 1 ≤ qPoly` at `(D, g, log H)`. -/

/-- Evaluation of `qPoly μ` at the concrete point `(D, g, log H)`. -/
lemma qPol_eval (μ D g H : ℕ) :
    MvPolynomial.eval ![(D : ℝ), (g : ℝ), Real.log H] (qPoly μ)
      = (CCc μ : ℝ) * (1 + (D : ℝ)) * (1 + (g : ℝ)) ^ (Ec μ) *
          (1 + Real.log H) ^ (Fc μ) := by
  rw [qPoly_eval]
  simp only [Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.cons_val_two,
    Matrix.vecHead, Matrix.vecTail, Function.comp_apply, Fin.succ_zero_eq_one]

/-- `2 · EE μ ≤ CCc μ`, i.e. `2 · (μ+2)^(40(μ+1)^2) ≤ (μ+2)^(100(μ+1)^2)`. -/
lemma two_mul_EE_le_CCc (μ : ℕ) : 2 * EE μ ≤ CCc μ := by
  have hexp : 1 ≤ 60 * (μ + 1) ^ 2 := by
    have h1 : 1 ≤ (μ + 1) ^ 2 := Nat.one_le_pow _ _ (by norm_num)
    calc (1 : ℕ) = 1 * 1 := by ring
      _ ≤ 60 * (μ + 1) ^ 2 := Nat.mul_le_mul (by norm_num) h1
  have hbase : 2 ≤ (μ + 2) ^ (60 * (μ + 1) ^ 2) := by
    calc (2 : ℕ) ≤ μ + 2 := by omega
      _ = (μ + 2) ^ 1 := by ring
      _ ≤ (μ + 2) ^ (60 * (μ + 1) ^ 2) := Nat.pow_le_pow_right (by omega) hexp
  have hsplit : (μ + 2) ^ (100 * (μ + 1) ^ 2)
      = (μ + 2) ^ (40 * (μ + 1) ^ 2) * (μ + 2) ^ (60 * (μ + 1) ^ 2) := by
    rw [← Nat.pow_add]; congr 1; ring
  rw [EE, CCc, hsplit]
  calc 2 * (μ + 2) ^ (40 * (μ + 1) ^ 2)
      = (μ + 2) ^ (40 * (μ + 1) ^ 2) * 2 := Nat.mul_comm _ _
    _ ≤ (μ + 2) ^ (40 * (μ + 1) ^ 2) * (μ + 2) ^ (60 * (μ + 1) ^ 2) :=
        Nat.mul_le_mul_left _ hbase

/-- `AA μ ≤ Ec μ`, i.e. `100(μ+1)^3 ≤ 1000(μ+1)^4`. -/
lemma AA_le_Ec (μ : ℕ) : AA μ ≤ Ec μ := by
  rw [AA, Ec]
  have h34 : (μ + 1) ^ 3 ≤ (μ + 1) ^ 4 := Nat.pow_le_pow_right (by omega) (by norm_num)
  calc 100 * (μ + 1) ^ 3 ≤ 100 * (μ + 1) ^ 4 := Nat.mul_le_mul_left _ h34
    _ ≤ 1000 * (μ + 1) ^ 4 := Nat.mul_le_mul_right _ (by norm_num)

/-- `BB μ ≤ Fc μ`, i.e. `100(μ+1)^3 ≤ 1000(μ+1)^4`. -/
lemma BB_le_Fc (μ : ℕ) : BB μ ≤ Fc μ := by
  rw [BB, Fc]
  have h34 : (μ + 1) ^ 3 ≤ (μ + 1) ^ 4 := Nat.pow_le_pow_right (by omega) (by norm_num)
  calc 100 * (μ + 1) ^ 3 ≤ 100 * (μ + 1) ^ 4 := Nat.mul_le_mul_left _ h34
    _ ≤ 1000 * (μ + 1) ^ 4 := Nat.mul_le_mul_right _ (by norm_num)

/-- `9 · BB μ ≤ Fc μ - BB μ`: the slack in the exponent of `(1 + log H)` absorbs
nine copies of `BB μ`. -/
lemma nine_mul_BB_le (μ : ℕ) : 9 * BB μ ≤ Fc μ - BB μ := by
  rw [BB, Fc]
  have hpow : (μ + 1) ^ 3 ≤ (μ + 1) ^ 4 := Nat.pow_le_pow_right (by omega) (by norm_num)
  have h : 1000 * (μ + 1) ^ 3 ≤ 1000 * (μ + 1) ^ 4 := Nat.mul_le_mul_left _ hpow
  omega

/-- The `H`-part of the bound: `(lgNat H)^(BB μ) ≤ (1 + log H)^(Fc μ)` for `H ≥ 1`. -/
lemma lgNat_pow_le (μ H : ℕ) (hH : 1 ≤ H) :
    ((lgNat H : ℕ) : ℝ) ^ (BB μ) ≤ (1 + Real.log H) ^ (Fc μ) := by
  rcases eq_or_lt_of_le hH with h1 | h2
  · subst h1
    simp [lgNat]
  · have hL : 0 ≤ Real.log (H : ℝ) := log_nat_nonneg H
    have hge2 : (2 : ℝ) ≤ (H : ℝ) := by exact_mod_cast h2
    have hlogge : Real.log 2 ≤ Real.log (H : ℝ) := Real.log_le_log (by norm_num) hge2
    have hhalf : (1 : ℝ) / 2 ≤ Real.log 2 := by
      have := Real.log_two_gt_d9; linarith
    have ha : (3 : ℝ) / 2 ≤ 1 + Real.log (H : ℝ) := by linarith
    have hceil : ((lgNat H : ℕ) : ℝ) ≤ 2 * (1 + Real.log (H : ℝ)) := by
      have hc : (Nat.ceil (Real.log (H : ℝ)) : ℝ) < Real.log (H : ℝ) + 1 :=
        Nat.ceil_lt_add_one hL
      have he : ((lgNat H : ℕ) : ℝ) = (Nat.ceil (Real.log (H : ℝ)) : ℝ) + 1 := by
        simp [lgNat]
      rw [he]; linarith
    have hBBFc : BB μ ≤ Fc μ := BB_le_Fc μ
    have h9 : 9 * BB μ ≤ Fc μ - BB μ := nine_mul_BB_le μ
    have htwo : (2 : ℝ) ^ (BB μ) ≤ (1 + Real.log (H : ℝ)) ^ (Fc μ - BB μ) := by
      calc (2 : ℝ) ^ (BB μ) ≤ (((3 : ℝ) / 2) ^ 9) ^ (BB μ) := by
              apply pow_le_pow_left₀ (by norm_num) _ (BB μ)
              norm_num
        _ = ((3 : ℝ) / 2) ^ (9 * BB μ) := by rw [pow_mul]
        _ ≤ ((3 : ℝ) / 2) ^ (Fc μ - BB μ) := pow_le_pow_right₀ (by norm_num) h9
        _ ≤ (1 + Real.log (H : ℝ)) ^ (Fc μ - BB μ) :=
              pow_le_pow_left₀ (by norm_num) ha (Fc μ - BB μ)
    calc ((lgNat H : ℕ) : ℝ) ^ (BB μ) ≤ (2 * (1 + Real.log (H : ℝ))) ^ (BB μ) :=
            pow_le_pow_left₀ (Nat.cast_nonneg (lgNat H)) hceil (BB μ)
      _ = (2 : ℝ) ^ (BB μ) * (1 + Real.log (H : ℝ)) ^ (BB μ) := by rw [mul_pow]
      _ ≤ (1 + Real.log (H : ℝ)) ^ (Fc μ - BB μ) * (1 + Real.log (H : ℝ)) ^ (BB μ) :=
            mul_le_mul_of_nonneg_right htwo (pow_nonneg (by linarith [log_nat_nonneg H]) _)
      _ = (1 + Real.log (H : ℝ)) ^ (Fc μ - BB μ + BB μ) := by rw [← pow_add]
      _ = (1 + Real.log (H : ℝ)) ^ (Fc μ) := by rw [Nat.sub_add_cancel hBBFc]

-- The `b + 1` bound of the polynomial `q`: `bV + 1 ≤ qPoly` evaluated at `(D,g,log H)`.
-- Ingredients: `qPoly μ` evaluates to `CCc μ * (1+D) * (1+g)^(Ec μ) * (1+log H)^(Fc μ)`
-- (`qPoly_eval`), `bV μ g H + 1 ≤ 2 * bV μ g H` (as `1 ≤ bV`), `CCc μ ≥ 2 * EE μ` (indeed
-- `CCc μ = (μ+2)^(100(μ+1)^2)` and `EE μ = (μ+2)^(40(μ+1)^2)`), `Ec μ ≥ AA μ`, `Fc μ ≥ BB μ`
-- and `lgNat H ≤ log H + 2`; the slack `Fc μ - BB μ` absorbs the factor `2^BB` when `H ≥ 2`.
theorem q_bound_b_succ (μ D g H : ℕ) (hH : 1 ≤ H) :
    ((Work.WilkiesH.Interp.bV μ g H : ℕ) : ℝ) + 1 ≤
      MvPolynomial.eval ![(D : ℝ), (g : ℝ), Real.log H] (Work.WilkiesH.Interp.qPoly μ) := by
  rw [qPol_eval]
  have hb1 : (1 : ℝ) ≤ ((bV μ g H : ℕ) : ℝ) := by exact_mod_cast one_le_bV μ g H
  have hstep : ((bV μ g H : ℕ) : ℝ) + 1 ≤ 2 * ((bV μ g H : ℕ) : ℝ) := by linarith
  have hmain : 2 * ((bV μ g H : ℕ) : ℝ) ≤
      (CCc μ : ℝ) * (1 + (D : ℝ)) * (1 + (g : ℝ)) ^ (Ec μ) *
        (1 + Real.log H) ^ (Fc μ) := by
    have hP : 2 * (EE μ : ℝ) ≤ (CCc μ : ℝ) := by exact_mod_cast two_mul_EE_le_CCc μ
    have hQ : ((g + 1 : ℕ) : ℝ) ^ (AA μ) ≤ (1 + (g : ℝ)) ^ (Ec μ) := by
      have hcast : ((g + 1 : ℕ) : ℝ) = 1 + (g : ℝ) := by push_cast; ring
      rw [hcast]
      exact pow_le_pow_right₀
        (by linarith [show (0 : ℝ) ≤ (g : ℝ) from Nat.cast_nonneg g]) (AA_le_Ec μ)
    have hR : ((lgNat H : ℕ) : ℝ) ^ (BB μ) ≤ (1 + Real.log H) ^ (Fc μ) :=
      lgNat_pow_le μ H hH
    have hbVcast : 2 * ((bV μ g H : ℕ) : ℝ)
        = (2 * (EE μ : ℝ)) * (((g + 1 : ℕ) : ℝ) ^ (AA μ)) *
            (((lgNat H : ℕ) : ℝ) ^ (BB μ)) := by
      simp only [bV]; push_cast; ring
    rw [hbVcast]
    have hg0 : (0 : ℝ) ≤ (g : ℝ) := Nat.cast_nonneg g
    have hD0 : (0 : ℝ) ≤ (D : ℝ) := Nat.cast_nonneg D
    have hD1 : (1 : ℝ) ≤ 1 + (D : ℝ) := by linarith
    have hQnn : (0 : ℝ) ≤ ((g + 1 : ℕ) : ℝ) ^ (AA μ) :=
      pow_nonneg (Nat.cast_nonneg (g + 1)) _
    have hRnn : (0 : ℝ) ≤ ((lgNat H : ℕ) : ℝ) ^ (BB μ) :=
      pow_nonneg (Nat.cast_nonneg (lgNat H)) _
    have hSnn : (0 : ℝ) ≤ (1 + (g : ℝ)) ^ (Ec μ) := pow_nonneg (by linarith) _
    have hTnn : (0 : ℝ) ≤ (1 + Real.log H) ^ (Fc μ) :=
      pow_nonneg (by linarith [log_nat_nonneg H]) _
    have hCCnn : (0 : ℝ) ≤ (CCc μ : ℝ) := Nat.cast_nonneg _
    have hQR : ((g + 1 : ℕ) : ℝ) ^ (AA μ) * ((lgNat H : ℕ) : ℝ) ^ (BB μ)
        ≤ (1 + (g : ℝ)) ^ (Ec μ) * (1 + Real.log H) ^ (Fc μ) :=
      mul_le_mul hQ hR hRnn hSnn
    have hPQ : (2 * (EE μ : ℝ)) *
          ((((g + 1 : ℕ) : ℝ) ^ (AA μ)) * ((lgNat H : ℕ) : ℝ) ^ (BB μ))
        ≤ (CCc μ : ℝ) * ((1 + (g : ℝ)) ^ (Ec μ) * (1 + Real.log H) ^ (Fc μ)) :=
      mul_le_mul hP hQR (mul_nonneg hQnn hRnn) hCCnn
    have hfinal : (CCc μ : ℝ) * ((1 + (g : ℝ)) ^ (Ec μ) * (1 + Real.log H) ^ (Fc μ))
        ≤ (CCc μ : ℝ) * (1 + (D : ℝ)) *
            ((1 + (g : ℝ)) ^ (Ec μ) * (1 + Real.log H) ^ (Fc μ)) := by
      have h : ((1 + (g : ℝ)) ^ (Ec μ) * (1 + Real.log H) ^ (Fc μ))
          ≤ (1 + (D : ℝ)) * ((1 + (g : ℝ)) ^ (Ec μ) * (1 + Real.log H) ^ (Fc μ)) :=
        le_mul_of_one_le_left (mul_nonneg hSnn hTnn) hD1
      calc (CCc μ : ℝ) * ((1 + (g : ℝ)) ^ (Ec μ) * (1 + Real.log H) ^ (Fc μ))
          ≤ (CCc μ : ℝ) *
              ((1 + (D : ℝ)) * ((1 + (g : ℝ)) ^ (Ec μ) * (1 + Real.log H) ^ (Fc μ))) :=
            mul_le_mul_of_nonneg_left h hCCnn
        _ = (CCc μ : ℝ) * (1 + (D : ℝ)) *
              ((1 + (g : ℝ)) ^ (Ec μ) * (1 + Real.log H) ^ (Fc μ)) := by ring
    calc (2 * (EE μ : ℝ)) * ((g + 1 : ℕ) : ℝ) ^ (AA μ) * ((lgNat H : ℕ) : ℝ) ^ (BB μ)
        = (2 * (EE μ : ℝ)) *
            ((((g + 1 : ℕ) : ℝ) ^ (AA μ)) * ((lgNat H : ℕ) : ℝ) ^ (BB μ)) := by ring
      _ ≤ (CCc μ : ℝ) * ((1 + (g : ℝ)) ^ (Ec μ) * (1 + Real.log H) ^ (Fc μ)) := hPQ
      _ ≤ (CCc μ : ℝ) * (1 + (D : ℝ)) *
            ((1 + (g : ℝ)) ^ (Ec μ) * (1 + Real.log H) ^ (Fc μ)) := hfinal
      _ = (CCc μ : ℝ) * (1 + (D : ℝ)) * (1 + (g : ℝ)) ^ (Ec μ) *
            (1 + Real.log H) ^ (Fc μ) := by ring
  linarith

end Work.WilkiesH.Interp.V2qb
