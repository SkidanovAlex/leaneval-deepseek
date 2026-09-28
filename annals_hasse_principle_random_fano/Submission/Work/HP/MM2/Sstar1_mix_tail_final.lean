import Mathlib
import Submission.Work.HP.MM2.Defs
import Submission.Work.HP.MM2.ss1_DeltaXY_gcd_ge_one
import Submission.Work.HP.DeltaXY_gcd_detL
import Submission.Work.HP.bigW_le_pow
import Submission.Work.HP.eNorm_veronese_bounds
import Submission.Work.HP.MDBasic.nonneg_basic
import Submission.Work.HP.MM2.iotaDN_pos
import Submission.Work.HP.EE_lower2
import Submission.Work.HP.Lat.detL_ge_one
import Submission.Work.HP.MDEstimates.veronese_linIndep
import Submission.Work.HP.six_le_NN
import Submission.Work.HP.MM2.NN_ge_two_mul_add_one
import Submission.Work.HP.MM2.mix_tail_arith_final

/-!
# `Sstar1_mix_tail_final`: the arithmetic tail of the `Sstar1` bound

The assembling step of the `𝓢*₁` mixed tail estimate: if `C` is any constant with `8Cι ≥ 2`
(`ι = iotaDN d n`) and `B` is large, then for `B^(5/6) ≤ A ≤ B²` the two "error" terms

`K (1+log A)² A^{(3/4)(N-2)} / ‖ν(x)‖`  and  `K (1+log A)`

are both dominated by `A^{N-2}/(log B · W · ‖ν(x)‖ · log A)`, hence by `C · mixMain/log A`.

The first domination is exactly the arithmetic input `mix_tail_arith_final` (item (i) after
multiplying by `A^{(3/4)(N-2)}`, using `(1+log A)²log A ≤ (1+log A)³`), the second is item (ii)
of `mix_tail_arith_final`.  The passage from `A^{N-2}/(log B·W·‖ν(x)‖·log A)` to
`C · mixMain/log A` uses only `det Γ_{x,y} ≤ ‖ν(x)‖‖ν(y)‖` (`detL_Gam_le_norm`) and
`det Γ_{x,y} > 0`.
-/

set_option autoImplicit false
set_option maxHeartbeats 1000000

noncomputable section

open Filter Finset MeasureTheory

namespace Work.HP.MM2

open Work.HP

attribute [local instance] Classical.propDecidable

/-! ## Helpers -/

/-- A primitive vector is nonzero. -/
private lemma isPrim_ne_zero_sf {ι : Type*} [Fintype ι] {a : ι → ℤ} (h : IsPrim a) : a ≠ 0 := by
  intro h0
  have h1 : Finset.univ.gcd a = 0 := Finset.gcd_eq_zero_iff.mpr (fun i _ => by rw [h0]; rfl)
  rw [IsPrim] at h
  rw [h] at h1
  exact one_ne_zero h1

/-- `LinearIndependent ℤ ![x,y]` forbids `x = y` (the relation `x - y = 0`). -/
private lemma ne_of_linInd {ι : Type*} [Fintype ι] (x y : ι → ℤ)
    (h : LinearIndependent ℤ ![x, y]) : x ≠ y := by
  intro hxy
  have h2 := (Fintype.linearIndependent_iff.mp h) ![1, -1]
  have hsum : (∑ i, (![1, -1] : Fin 2 → ℤ) i • (![x, y] i)) = 0 := by
    simp [Fin.sum_univ_two, hxy]
  have := h2 hsum 0
  simp at this

/-- `LinearIndependent ℤ ![x,y]` forbids `x = -y` (the relation `x + y = 0`). -/
private lemma ne_neg_of_linInd {ι : Type*} [Fintype ι] (x y : ι → ℤ)
    (h : LinearIndependent ℤ ![x, y]) : x ≠ -y := by
  intro hxy
  have h2 := (Fintype.linearIndependent_iff.mp h) ![1, 1]
  have hsum : (∑ i, (![1, 1] : Fin 2 → ℤ) i • (![x, y] i)) = 0 := by
    simp [Fin.sum_univ_two, hxy]
  have := h2 hsum 0
  simp at this

/-- Pure real arithmetic: if `2 ≤ 8Cι` and `D ≤ Ex·Ey` with all quantities positive, then
`2·AN2/(L·W·Ex·LA) ≤ C·(8ι·AN2·Ey/(L·W·D))/LA`.  This is the step
`‖ν(y)‖/det Γ_{x,y} ≥ 1/‖ν(x)‖` followed by `2 ≤ 8Cι`. -/
private lemma mixMain_lower {C ι L W LA Ex Ey D AN2 : ℝ}
    (hι : 0 < ι) (hC8 : 2 ≤ C * 8 * ι)
    (hL : 0 < L) (hW : 0 < W) (hLA : 0 < LA) (hEx : 0 < Ex) (hEy : 0 < Ey)
    (hD : 0 < D) (hDle : D ≤ Ex * Ey) (hAN2 : 0 ≤ AN2) :
    2 * (AN2 / (L * W * Ex * LA)) ≤ C * (8 * ι * AN2 * Ey / (L * W * D)) / LA := by
  have hratio : 1 / Ex ≤ Ey / D := by
    rw [div_le_div_iff₀ hEx hD]
    linarith [hDle]
  have hf : (0 : ℝ) ≤ AN2 / (L * W * LA) := by positivity
  have hkey : 2 * ((1 / Ex) * (AN2 / (L * W * LA)))
      ≤ (C * 8 * ι) * (Ey / D) * (AN2 / (L * W * LA)) := by
    have h1 : (2 : ℝ) * (1 / Ex) ≤ (C * 8 * ι) * (Ey / D) :=
      mul_le_mul hC8 hratio (by positivity) (by positivity)
    have hm := mul_le_mul_of_nonneg_right h1 hf
    convert hm using 1 <;> ring
  have e1 : C * (8 * ι * AN2 * Ey / (L * W * D)) / LA
      = (C * 8 * ι) * (Ey / D) * (AN2 / (L * W * LA)) := by
    field_simp
  have e2 : AN2 / (L * W * Ex * LA) = (1 / Ex) * (AN2 / (L * W * LA)) := by
    field_simp
  rw [e2, e1]
  exact hkey

/-! ## The assembly -/

theorem Sstar1_mix_tail_final (d n : ℕ) [DecidableEq (Work.HP.Mon d n)] (hd : 2 ≤ d) (hdn : d ≤ n)
    (h22 : (d, n) ≠ (2, 2)) (K : ℝ) (hK : 0 < K) :
    ∃ C B₀ : ℝ, 0 < C ∧ ∀ A B : ℝ, B₀ ≤ B → B ^ ((5 : ℝ) / 6) ≤ A → A ≤ B ^ 2 →
      ∀ x y : Fin (n + 1) → ℤ, Work.HP.IsPrim x → Work.HP.IsPrim y →
        LinearIndependent ℤ ![x, y] →
        Work.HP.eNorm x ≤ B ^ (1 / ((n : ℝ) + 1 - d)) →
      K * ((1 + Real.log A) ^ 2 *
            A ^ ((3 : ℝ) / 4 * ((Work.HP.NN d n - 2 : ℕ) : ℝ)) /
            Work.HP.eNorm (Work.HP.veronese d n x) + (1 + Real.log A))
        ≤ C * Work.HP.MM2.mixMain d n A B (x, y) / Real.log A := by
  have hn2 : 2 ≤ n := le_trans hd hdn
  have hN : 2 * d + 1 ≤ NN d n := NN_ge_two_mul_add_one d n hn2
  obtain ⟨Barith, harith⟩ := mix_tail_arith_final d n hd hdn K hK hN
  have hιpos : 0 < iotaDN d n := iotaDN_pos d n hd hdn
  set C : ℝ := max 1 (1 / (4 * iotaDN d n)) with hCdef
  have hC8 : (2 : ℝ) ≤ C * 8 * iotaDN d n := by
    have h1 : (1 / (4 * iotaDN d n)) ≤ C := by rw [hCdef]; exact le_max_right _ _
    have h8 : (0 : ℝ) ≤ 8 := by norm_num
    have hm := mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_right h1 h8) hιpos.le
    have h2 : (1 / (4 * iotaDN d n)) * 8 * iotaDN d n = 2 := by
      field_simp
      norm_num
    linarith [hm, h2]
  refine ⟨C, max Barith 100, ?_, ?_⟩
  · rw [hCdef]; positivity
  intro A B hB hBA hAB2 x y hx hy hxy hnx
  have hBa : Barith ≤ B := le_trans (le_max_left _ _) hB
  have hBge : (100 : ℝ) ≤ B := le_trans (le_max_right _ _) hB
  obtain ⟨hA1, hA2⟩ := harith B hBa A hBA hAB2
  have hA2x := hA2 x hnx
  have hBpos : 0 < B := by linarith
  have hB1 : 1 < B := by linarith
  have hlogBpos : 0 < Real.log B := Real.log_pos hB1
  have hB56pos : 0 < B ^ ((5 : ℝ) / 6) := Real.rpow_pos_of_pos hBpos _
  have hApos : 0 < A := lt_of_lt_of_le hB56pos hBA
  have hlogApos : 0 < Real.log A := by
    have h1 : Real.log (B ^ ((5 : ℝ) / 6)) ≤ Real.log A := Real.log_le_log hB56pos hBA
    rw [Real.log_rpow hBpos] at h1
    nlinarith
  have h1LA : 0 < 1 + Real.log A := by linarith
  have hWpos : 0 < (bigW (wOf B) : ℝ) := by
    have h : (1 : ℝ) ≤ (bigW (wOf B) : ℝ) := by exact_mod_cast one_le_bigW (wOf B)
    linarith
  have hExpos : 0 < eNorm (veronese d n x) :=
    eNorm_pos_iff.mpr (MDEstimates.veronese_ne_zero (isPrim_ne_zero_sf hx))
  have hEypos : 0 < eNorm (veronese d n y) :=
    eNorm_pos_iff.mpr (MDEstimates.veronese_ne_zero (isPrim_ne_zero_sf hy))
  have hD1 : (1 : ℝ) ≤ detL (Gam d n x y) := Lat.detL_ge_one _
  have hDpos : 0 < detL (Gam d n x y) := lt_of_lt_of_le zero_lt_one hD1
  have hDle : detL (Gam d n x y) ≤ eNorm (veronese d n x) * eNorm (veronese d n y) :=
    detL_Gam_le_norm d n hd x y hx hy (ne_of_linInd x y hxy) (ne_neg_of_linInd x y hxy)
  -- (1) `K (1+log A)^2 log A log B W A^{(3/4)(N-2)} ≤ A^{N-2}`
  have hcore1 : K * (1 + Real.log A) ^ 2 * Real.log A * Real.log B * (bigW (wOf B) : ℝ) *
      A ^ ((3 : ℝ) / 4 * ((NN d n - 2 : ℕ) : ℝ)) ≤ A ^ (NN d n - 2) := by
    have hstep : K * (1 + Real.log A) ^ 3 * Real.log B * (bigW (wOf B) : ℝ) *
        A ^ ((3 : ℝ) / 4 * ((NN d n - 2 : ℕ) : ℝ))
        ≤ A ^ (((NN d n - 2 : ℕ) : ℝ) / 4) * A ^ ((3 : ℝ) / 4 * ((NN d n - 2 : ℕ) : ℝ)) :=
      mul_le_mul_of_nonneg_right hA1 (le_of_lt (Real.rpow_pos_of_pos hApos _))
    have hAA : A ^ (((NN d n - 2 : ℕ) : ℝ) / 4) * A ^ ((3 : ℝ) / 4 * ((NN d n - 2 : ℕ) : ℝ))
        = A ^ (NN d n - 2) := by
      rw [← Real.rpow_add hApos, ← Real.rpow_natCast A (NN d n - 2)]
      congr 1
      ring
    have hmono : K * (1 + Real.log A) ^ 2 * Real.log A * Real.log B * (bigW (wOf B) : ℝ) *
        A ^ ((3 : ℝ) / 4 * ((NN d n - 2 : ℕ) : ℝ))
        ≤ K * (1 + Real.log A) ^ 3 * Real.log B * (bigW (wOf B) : ℝ) *
        A ^ ((3 : ℝ) / 4 * ((NN d n - 2 : ℕ) : ℝ)) := by
      have h2 : (1 + Real.log A) ^ 2 * Real.log A ≤ (1 + Real.log A) ^ 3 := by
        nlinarith [hlogApos.le]
      have hn : (0 : ℝ) ≤ K * Real.log B * (bigW (wOf B) : ℝ) *
          A ^ ((3 : ℝ) / 4 * ((NN d n - 2 : ℕ) : ℝ)) := by positivity
      have hm := mul_le_mul_of_nonneg_left h2 hn
      convert hm using 1 <;> ring
    linarith [hstep, hmono, hAA]
  -- (2) `K (1+log A) log A log B W ‖ν(x)‖ ≤ A^{N-2}`
  have hcore2 : K * (1 + Real.log A) * Real.log A * Real.log B * (bigW (wOf B) : ℝ) *
      eNorm (veronese d n x) ≤ A ^ (NN d n - 2) := by
    have h2 : K * (1 + Real.log A) * Real.log A * Real.log B * (bigW (wOf B) : ℝ) *
        eNorm (veronese d n x)
        ≤ K * (1 + Real.log A) ^ 2 * Real.log B * (bigW (wOf B) : ℝ) *
          eNorm (veronese d n x) := by
      have hm : (1 + Real.log A) * Real.log A ≤ (1 + Real.log A) ^ 2 := by
        nlinarith [hlogApos.le]
      have hn : (0 : ℝ) ≤ K * Real.log B * (bigW (wOf B) : ℝ) * eNorm (veronese d n x) := by
        positivity
      have hm2 := mul_le_mul_of_nonneg_left hm hn
      convert hm2 using 1 <;> ring
    linarith [h2, hA2x]
  have hden : (0 : ℝ) < Real.log B * (bigW (wOf B) : ℝ) * eNorm (veronese d n x) * Real.log A := by
    positivity
  have key1 : K * ((1 + Real.log A) ^ 2 * A ^ ((3 : ℝ) / 4 * ((NN d n - 2 : ℕ) : ℝ)) /
      eNorm (veronese d n x))
      ≤ A ^ (NN d n - 2) /
        (Real.log B * (bigW (wOf B) : ℝ) * eNorm (veronese d n x) * Real.log A) := by
    rw [le_div_iff₀ hden]
    have hgoal : K * ((1 + Real.log A) ^ 2 * A ^ ((3 : ℝ) / 4 * ((NN d n - 2 : ℕ) : ℝ)) /
          eNorm (veronese d n x)) *
          (Real.log B * (bigW (wOf B) : ℝ) * eNorm (veronese d n x) * Real.log A)
        = K * (1 + Real.log A) ^ 2 * Real.log A * Real.log B * (bigW (wOf B) : ℝ) *
          A ^ ((3 : ℝ) / 4 * ((NN d n - 2 : ℕ) : ℝ)) := by
      field_simp
    rw [hgoal]
    exact hcore1
  have key2 : K * (1 + Real.log A)
      ≤ A ^ (NN d n - 2) /
        (Real.log B * (bigW (wOf B) : ℝ) * eNorm (veronese d n x) * Real.log A) := by
    rw [le_div_iff₀ hden]
    have hgoal : K * (1 + Real.log A) *
          (Real.log B * (bigW (wOf B) : ℝ) * eNorm (veronese d n x) * Real.log A)
        = K * (1 + Real.log A) * Real.log A * Real.log B * (bigW (wOf B) : ℝ) *
          eNorm (veronese d n x) := by
      ring
    rw [hgoal]
    exact hcore2
  have hRHS : 2 * (A ^ (NN d n - 2) /
      (Real.log B * (bigW (wOf B) : ℝ) * eNorm (veronese d n x) * Real.log A))
      ≤ C * mixMain d n A B (x, y) / Real.log A := by
    simp only [mixMain]
    exact mixMain_lower hιpos hC8 hlogBpos hWpos hlogApos hExpos hEypos hDpos hDle
      (pow_nonneg hApos.le _)
  have hfinal : K * ((1 + Real.log A) ^ 2 * A ^ ((3 : ℝ) / 4 * ((NN d n - 2 : ℕ) : ℝ)) /
        eNorm (veronese d n x)) + K * (1 + Real.log A)
      ≤ 2 * (A ^ (NN d n - 2) /
        (Real.log B * (bigW (wOf B) : ℝ) * eNorm (veronese d n x) * Real.log A)) := by
    linarith [key1, key2]
  have hrw : K * ((1 + Real.log A) ^ 2 * A ^ ((3 : ℝ) / 4 * ((NN d n - 2 : ℕ) : ℝ)) /
        eNorm (veronese d n x) + (1 + Real.log A))
      = K * ((1 + Real.log A) ^ 2 * A ^ ((3 : ℝ) / 4 * ((NN d n - 2 : ℕ) : ℝ)) /
          eNorm (veronese d n x)) + K * (1 + Real.log A) := by ring
  rw [hrw]
  exact le_trans hfinal hRHS

end Work.HP.MM2
