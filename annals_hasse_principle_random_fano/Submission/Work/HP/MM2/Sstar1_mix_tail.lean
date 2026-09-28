import Mathlib
import Submission.Work.HP.MM2.Defs
import Submission.Work.HP.MM2.ss1_S1ball_aux
import Submission.Work.HP.MM2.ss1_sum_Icc_inv_le
import Submission.Work.HP.isPrim_veronese
import Submission.Work.HP.Vero.finrank_latOrth
import Submission.Work.HP.lam_basic
import Submission.Work.HP.six_le_NN
import Submission.Work.HP.MM2.S1ball_degN
import Submission.Work.HP.MM2.Sstar1_mix_tail_final
import Submission.Work.HP.MM2.Sstar1_mix_tail_arith
import Submission.Work.HP.MM2.iotaDN_pos
import Submission.Work.HP.MM2.Sstar1_mix_tail_arith_aux
import Submission.Work.HP.MM2.loc_arith
import Submission.Work.HP.MM2.ss1_DeltaXY_gcd_ge_one
import Submission.Work.HP.DeltaXY_gcd_detL
import Submission.Work.HP.eNorm_veronese_bounds
import Submission.Work.HP.latOrth_count_degenerate
import Submission.Work.HP.bigW_le_pow

set_option autoImplicit false
set_option maxHeartbeats 1000000
noncomputable section

namespace Work.HP.MM2

open Work.HP

attribute [local instance] Classical.propDecidable

/-! ## Auxiliary lemmas for the tail of the Möbius sum -/

/-- `1 ≤ λ_{N-1}(Λ_{ν(x)})` for primitive `x ≠ 0`. -/
private lemma one_le_lamX (d n : ℕ) [DecidableEq (Mon d n)] (hd : 2 ≤ d) (hdn : d ≤ n)
    (x : Fin (n + 1) → ℤ) (hx : IsPrim x) : 1 ≤ lamX d n x := by
  rw [lamX]
  have h0 : veronese d n x ≠ 0 := IsPrim.ne_zero (isPrim_veronese d n (by omega) hx)
  have hrk : rk (latOrth (veronese d n x)) = NN d n - 1 := by
    rw [rk]
    simpa [NN] using Vero.finrank_latOrth (veronese d n x) h0
  have hN : 1 ≤ NN d n - 1 := by
    have := six_le_NN d n hd hdn
    omega
  exact LCD_one_le_lam (latOrth (veronese d n x)) hN (by omega)

/-- The `ℓ`-tail of the Möbius sum, bounded by the improved small-ball estimate.

For `ℓ > A/(Wλ(x))` the radius `A/ℓ` is at most `W λ(x) ≤ μ`, so the small-ball sum is
bounded by the (sharper) `S1ball` bound with `T = A/ℓ`, `μ` as given; summing `1/ℓ` over the
range costs a factor `1 + log A`. -/
private lemma tail_sum_le (d n : ℕ) [DecidableEq (Mon d n)] (hd : 2 ≤ d) (hdn : d ≤ n)
    (K1 : ℝ) (hK1 : 0 ≤ K1)
    (hS1 : ∀ x : Fin (n + 1) → ℤ, IsPrim x → ∀ T μ : ℝ, 1 ≤ T → 1 ≤ μ →
      lamX d n x ≤ μ →
      S1ball d n x T ≤ K1 * ((1 + Real.log T) *
        (T ^ (NN d n - 2) + μ ^ (NN d n - 2)) / eNorm (veronese d n x) + 1))
    (A B : ℝ) (hA1 : 1 ≤ A)
    (x : Fin (n + 1) → ℤ) (hx : IsPrim x)
    (hWlam : (bigW (wOf B) : ℝ) * lamX d n x ≤ A ^ ((3 : ℝ) / 4)) :
    ∑ ℓ ∈ Finset.Icc (⌊A / ((bigW (wOf B) : ℝ) * lamX d n x)⌋₊ + 1) ⌊A⌋₊,
        (1 / (ℓ : ℝ)) * S1ball d n x (A / (ℓ : ℝ))
      ≤ 2 * K1 * ((1 + Real.log A) ^ 2 *
            A ^ ((3 : ℝ) / 4 * ((NN d n - 2 : ℕ) : ℝ)) / eNorm (veronese d n x)
          + (1 + Real.log A)) := by
  classical
  set W : ℝ := (bigW (wOf B) : ℝ) with hW
  set lam : ℝ := lamX d n x with hlam
  set V : ℝ := eNorm (veronese d n x) with hV
  set μ : ℝ := max 1 (W * lam) with hμ
  set L₀ : ℕ := ⌊A / (W * lam)⌋₊ with hL₀
  set M : ℕ := ⌊A⌋₊ with hM
  have hA0 : 0 ≤ A := le_trans zero_le_one hA1
  have hW1 : 1 ≤ W := by rw [hW]; exact_mod_cast one_le_bigW (wOf B)
  have hlam1 : 1 ≤ lam := by rw [hlam]; exact one_le_lamX d n hd hdn x hx
  have hWlam_pos : 0 < W * lam := by positivity
  have hμ1 : 1 ≤ μ := le_max_left _ _
  have hμW : W * lam ≤ μ := le_max_right _ _
  have hlamμ : lam ≤ μ := by
    have h1 : (1 : ℝ) * lam ≤ W * lam := mul_le_mul_of_nonneg_right hW1 (by linarith)
    linarith [hμW, h1]
  have hVpos : 0 < V := by
    rw [hV]
    exact eNorm_pos_of_ne_zero (IsPrim.ne_zero (isPrim_veronese d n (by omega) hx))
  have hstep : ∀ ℓ ∈ Finset.Icc (L₀ + 1) M,
      (1 / (ℓ : ℝ)) * S1ball d n x (A / (ℓ : ℝ))
        ≤ (1 / (ℓ : ℝ)) *
            (K1 * ((1 + Real.log A) * (μ ^ (NN d n - 2) + μ ^ (NN d n - 2)) / V + 1)) := by
    intro ℓ hℓ
    obtain ⟨hℓ1, hℓM⟩ := Finset.mem_Icc.mp hℓ
    have hℓ1' : 1 ≤ ℓ := by omega
    have hℓpos : (0 : ℝ) < (ℓ : ℝ) :=
      by exact_mod_cast (lt_of_lt_of_le Nat.zero_lt_one hℓ1')
    have hℓge : ((L₀ : ℝ) + 1) ≤ (ℓ : ℝ) := by
      have : L₀ + 1 ≤ ℓ := hℓ1
      exact_mod_cast this
    have hL0pos : (0 : ℝ) < (L₀ : ℝ) + 1 := by positivity
    have hT1 : 1 ≤ A / (ℓ : ℝ) := by
      rw [le_div_iff₀ hℓpos]
      calc (1 : ℝ) * (ℓ : ℝ) = (ℓ : ℝ) := one_mul _
        _ ≤ (M : ℝ) := by exact_mod_cast hℓM
        _ ≤ A := by rw [hM]; exact Nat.floor_le hA0
    have hTA : A / (ℓ : ℝ) ≤ A := by
      rw [div_le_iff₀ hℓpos]
      nlinarith [hA0, hℓge]
    have hTle : A / (ℓ : ℝ) ≤ μ := by
      have hfl : A / (W * lam) < (L₀ : ℝ) + 1 := by
        rw [hL₀]; exact Nat.lt_floor_add_one _
      have hmul : A < ((L₀ : ℝ) + 1) * (W * lam) := (div_lt_iff₀ hWlam_pos).mp hfl
      have hlt : A / ((L₀ : ℝ) + 1) < W * lam := by
        rw [div_lt_iff₀ hL0pos]
        linarith [hmul]
      have hone : (1 : ℝ) / (ℓ : ℝ) ≤ 1 / ((L₀ : ℝ) + 1) :=
        one_div_le_one_div_of_le hL0pos hℓge
      have hAle : A / (ℓ : ℝ) ≤ A / ((L₀ : ℝ) + 1) := by
        rw [div_eq_mul_one_div A (ℓ : ℝ), div_eq_mul_one_div A ((L₀ : ℝ) + 1)]
        exact mul_le_mul_of_nonneg_left hone hA0
      linarith [hAle, hlt, hμW]
    have hTpos : 0 < A / (ℓ : ℝ) := lt_of_lt_of_le zero_lt_one hT1
    have hlog : 1 + Real.log (A / (ℓ : ℝ)) ≤ 1 + Real.log A := by
      have h : Real.log (A / (ℓ : ℝ)) ≤ Real.log A := Real.log_le_log hTpos hTA
      linarith
    have hpow : (A / (ℓ : ℝ)) ^ (NN d n - 2) ≤ μ ^ (NN d n - 2) :=
      pow_le_pow_left₀ (le_of_lt hTpos) hTle _
    have hnum : (1 + Real.log (A / (ℓ : ℝ))) *
          ((A / (ℓ : ℝ)) ^ (NN d n - 2) + μ ^ (NN d n - 2))
        ≤ (1 + Real.log A) * (μ ^ (NN d n - 2) + μ ^ (NN d n - 2)) := by
      have h2 : (A / (ℓ : ℝ)) ^ (NN d n - 2) + μ ^ (NN d n - 2)
          ≤ μ ^ (NN d n - 2) + μ ^ (NN d n - 2) := by linarith
      exact mul_le_mul hlog h2 (by positivity) (by have := Real.log_nonneg hA1; linarith)
    have hquot : (1 + Real.log (A / (ℓ : ℝ))) *
          ((A / (ℓ : ℝ)) ^ (NN d n - 2) + μ ^ (NN d n - 2)) / V
        ≤ (1 + Real.log A) * (μ ^ (NN d n - 2) + μ ^ (NN d n - 2)) / V :=
      div_le_div_of_nonneg_right hnum hVpos.le
    have hS1' := hS1 x hx (A / (ℓ : ℝ)) μ hT1 hμ1 hlamμ
    have hbracket : (1 + Real.log (A / (ℓ : ℝ))) *
          ((A / (ℓ : ℝ)) ^ (NN d n - 2) + μ ^ (NN d n - 2)) / V + 1
        ≤ (1 + Real.log A) * (μ ^ (NN d n - 2) + μ ^ (NN d n - 2)) / V + 1 := by
      linarith [hquot]
    have hK1' : S1ball d n x (A / (ℓ : ℝ))
        ≤ K1 * ((1 + Real.log A) * (μ ^ (NN d n - 2) + μ ^ (NN d n - 2)) / V + 1) :=
      le_trans hS1' (mul_le_mul_of_nonneg_left hbracket hK1)
    exact mul_le_mul_of_nonneg_left hK1' (by positivity)
  have hH : ∑ ℓ ∈ Finset.Icc (L₀ + 1) M, (1 / (ℓ : ℝ)) ≤ 1 + Real.log A := by
    have hsub : Finset.Icc (L₀ + 1) M ⊆ Finset.Icc 1 M := by
      intro ℓ hℓ
      obtain ⟨h1, h2⟩ := Finset.mem_Icc.mp hℓ
      exact Finset.mem_Icc.mpr ⟨by omega, h2⟩
    have h1 : ∑ ℓ ∈ Finset.Icc (L₀ + 1) M, (1 / (ℓ : ℝ)) ≤ ∑ ℓ ∈ Finset.Icc 1 M, (1 / (ℓ : ℝ)) :=
      Finset.sum_le_sum_of_subset_of_nonneg hsub (fun ℓ _ _ => by positivity)
    have h2 : ∑ ℓ ∈ Finset.Icc 1 M, (1 / (ℓ : ℝ)) ≤ 1 + Real.log (M : ℝ) := ss1_sum_Icc_inv_le M
    have h3 : (1 : ℝ) + Real.log (M : ℝ) ≤ 1 + Real.log A := by
      have hMA : (M : ℝ) ≤ A := by rw [hM]; exact Nat.floor_le hA0
      by_cases hM0 : M = 0
      · rw [hM0]
        simp only [Nat.cast_zero, Real.log_zero, add_zero]
        exact le_add_of_nonneg_right (Real.log_nonneg hA1)
      · have hMpos : (0 : ℝ) < (M : ℝ) := by
          exact_mod_cast Nat.pos_of_ne_zero hM0
        have := Real.log_le_log hMpos hMA
        linarith
    linarith [h1, h2, h3]
  have hmulsum : ∑ ℓ ∈ Finset.Icc (L₀ + 1) M,
        (1 / (ℓ : ℝ)) * (K1 * ((1 + Real.log A) * (μ ^ (NN d n - 2) + μ ^ (NN d n - 2)) / V + 1))
      = K1 * ((1 + Real.log A) * (μ ^ (NN d n - 2) + μ ^ (NN d n - 2)) / V + 1) *
          ∑ ℓ ∈ Finset.Icc (L₀ + 1) M, (1 / (ℓ : ℝ)) := by
      rw [← Finset.sum_mul]
      exact mul_comm _ _
  have hbracket0 : 0 ≤ K1 * ((1 + Real.log A) * (μ ^ (NN d n - 2) + μ ^ (NN d n - 2)) / V + 1) := by
    have h1 : 0 ≤ (1 + Real.log A) := by
      have := Real.log_nonneg hA1; linarith
    have h2 : 0 ≤ μ ^ (NN d n - 2) + μ ^ (NN d n - 2) := by positivity
    have : 0 ≤ (1 + Real.log A) * (μ ^ (NN d n - 2) + μ ^ (NN d n - 2)) / V :=
      div_nonneg (mul_nonneg h1 h2) hVpos.le
    nlinarith [hK1, this]
  have hμpow : μ ^ (NN d n - 2) ≤ A ^ ((3 : ℝ) / 4 * ((NN d n - 2 : ℕ) : ℝ)) := by
    have hA14 : (1 : ℝ) ≤ A ^ ((3 : ℝ) / 4) := Real.one_le_rpow hA1 (by norm_num)
    have hμle : μ ≤ A ^ ((3 : ℝ) / 4) := max_le hA14 hWlam
    have h1 : μ ^ (NN d n - 2) ≤ (A ^ ((3 : ℝ) / 4)) ^ (NN d n - 2) :=
      pow_le_pow_left₀ (by linarith) hμle _
    have h2 : (A ^ ((3 : ℝ) / 4)) ^ (NN d n - 2)
        = A ^ ((3 : ℝ) / 4 * ((NN d n - 2 : ℕ) : ℝ)) :=
      calc (A ^ ((3 : ℝ) / 4)) ^ (NN d n - 2)
          = (A ^ ((3 : ℝ) / 4)) ^ ((NN d n - 2 : ℕ) : ℝ) :=
            (Real.rpow_natCast _ _).symm
        _ = A ^ ((3 : ℝ) / 4 * ((NN d n - 2 : ℕ) : ℝ)) :=
            (Real.rpow_mul hA0 ((3 : ℝ) / 4) ((NN d n - 2 : ℕ) : ℝ)).symm
    exact h1.trans h2.le
  calc ∑ ℓ ∈ Finset.Icc (L₀ + 1) M, (1 / (ℓ : ℝ)) * S1ball d n x (A / (ℓ : ℝ))
      ≤ ∑ ℓ ∈ Finset.Icc (L₀ + 1) M,
          (1 / (ℓ : ℝ)) * (K1 * ((1 + Real.log A) * (μ ^ (NN d n - 2) + μ ^ (NN d n - 2)) / V + 1)) :=
        Finset.sum_le_sum hstep
    _ = K1 * ((1 + Real.log A) * (μ ^ (NN d n - 2) + μ ^ (NN d n - 2)) / V + 1) *
          ∑ ℓ ∈ Finset.Icc (L₀ + 1) M, (1 / (ℓ : ℝ)) := hmulsum
    _ ≤ K1 * ((1 + Real.log A) * (μ ^ (NN d n - 2) + μ ^ (NN d n - 2)) / V + 1) *
          (1 + Real.log A) := mul_le_mul_of_nonneg_left hH hbracket0
    _ ≤ 2 * K1 * ((1 + Real.log A) ^ 2 *
            A ^ ((3 : ℝ) / 4 * ((NN d n - 2 : ℕ) : ℝ)) / V + (1 + Real.log A)) := by
        have hlog1 : (0 : ℝ) ≤ 1 + Real.log A := by
          have := Real.log_nonneg hA1; linarith
        have hlt1 : K1 * ((1 + Real.log A) * (μ ^ (NN d n - 2) + μ ^ (NN d n - 2)) / V + 1)
              * (1 + Real.log A)
            ≤ K1 * (2 * ((1 + Real.log A) ^ 2 *
                A ^ ((3 : ℝ) / 4 * ((NN d n - 2 : ℕ) : ℝ)) / V)) + 2 * K1 * (1 + Real.log A) := by
          have hpow2 : 0 ≤ A ^ ((3 : ℝ) / 4 * ((NN d n - 2 : ℕ) : ℝ)) := by positivity
          have heq : K1 * ((1 + Real.log A) * (μ ^ (NN d n - 2) + μ ^ (NN d n - 2)) / V + 1)
              * (1 + Real.log A)
              = K1 * (2 * ((1 + Real.log A) ^ 2 * μ ^ (NN d n - 2) / V)) + K1 * (1 + Real.log A) := by
            have hVne : V ≠ 0 := ne_of_gt hVpos
            field_simp
            ring
          rw [heq]
          have hle1 : K1 * (2 * ((1 + Real.log A) ^ 2 * μ ^ (NN d n - 2) / V))
              ≤ K1 * (2 * ((1 + Real.log A) ^ 2 *
                  A ^ ((3 : ℝ) / 4 * ((NN d n - 2 : ℕ) : ℝ)) / V)) := by
            apply mul_le_mul_of_nonneg_left _ hK1
            apply mul_le_mul_of_nonneg_left _ (by norm_num)
            exact div_le_div_of_nonneg_right
              (mul_le_mul_of_nonneg_left hμpow (by positivity)) hVpos.le
          have hle2 : K1 * (1 + Real.log A) ≤ 2 * K1 * (1 + Real.log A) := by
            nlinarith [hK1, hlog1]
          linarith [hle1, hle2]
        linarith [hlt1]
    _ = 2 * K1 * ((1 + Real.log A) ^ 2 *
            A ^ ((3 : ℝ) / 4 * ((NN d n - 2 : ℕ) : ℝ)) / eNorm (veronese d n x)
          + (1 + Real.log A)) := by rw [hV]

/-- `|μ(ℓ)| ≤ 1` for the Möbius function, as a real number. -/
private lemma abs_moebius_cast_le_one_tail (ℓ : ℕ) :
    |((ArithmeticFunction.moebius ℓ : ℤ) : ℝ)| ≤ 1 := by
  rw [← Int.cast_abs]
  exact_mod_cast ArithmeticFunction.abs_moebius_le_one (n := ℓ)

theorem Sstar1_mix_tail (d n : ℕ) [DecidableEq (Work.HP.Mon d n)] (hd : 2 ≤ d) (hdn : d ≤ n)
    (h22 : (d, n) ≠ (2, 2)) :
    ∃ C B₀ : ℝ, 0 < C ∧ ∀ A B : ℝ, B₀ ≤ B → B ^ ((5 : ℝ) / 6) ≤ A → A ≤ B ^ 2 →
      ∀ x y : Fin (n + 1) → ℤ, Work.HP.IsPrim x → Work.HP.IsPrim y →
        LinearIndependent ℤ ![x, y] →
        Work.HP.eNorm x ≤ B ^ (1 / ((n : ℝ) + 1 - d)) →
        (Work.HP.bigW (Work.HP.wOf B) : ℝ) * Work.HP.MM2.lamX d n x ≤ A ^ ((3 : ℝ) / 4) →
      |∑ ℓ ∈ Finset.Icc (⌊A / ((Work.HP.bigW (Work.HP.wOf B) : ℝ) *
            Work.HP.MM2.lamX d n x)⌋₊ + 1) ⌊A⌋₊,
          ((ArithmeticFunction.moebius ℓ : ℝ) / (ℓ : ℝ)) *
            Work.HP.Sk d n 1 (Work.HP.GamMix d n x y (Work.HP.bigW (Work.HP.wOf B) /
                Nat.gcd ℓ (Work.HP.bigW (Work.HP.wOf B))))
              (Work.HP.TmixSet d n y (A / (ℓ : ℝ)) (Real.log B))|
        ≤ C * Work.HP.MM2.mixMain d n A B (x, y) / Real.log A := by
  obtain ⟨K1, hK1pos, hS1⟩ := S1ball_degN d n hd hdn
  obtain ⟨C, Bf, hCpos, hfin⟩ :=
    Sstar1_mix_tail_final d n hd hdn h22 (2 * K1) (by linarith)
  refine ⟨C, max Bf 1, hCpos, ?_⟩
  intro A B hB hA56 hAB2 x y hx hy hLI hNx hWlam
  have hBf : Bf ≤ B := le_trans (le_max_left _ _) hB
  have hB1 : 1 ≤ B := le_trans (le_max_right _ _) hB
  have hA1 : 1 ≤ A := le_trans (Real.one_le_rpow hB1 (by norm_num)) hA56
  have habs : |∑ ℓ ∈ Finset.Icc (⌊A / ((bigW (wOf B) : ℝ) * lamX d n x)⌋₊ + 1) ⌊A⌋₊,
        ((ArithmeticFunction.moebius ℓ : ℝ) / (ℓ : ℝ)) *
          Sk d n 1 (GamMix d n x y ((bigW (wOf B) : ℕ) / Nat.gcd ℓ (bigW (wOf B))))
            (TmixSet d n y (A / (ℓ : ℝ)) (Real.log B))|
      ≤ ∑ ℓ ∈ Finset.Icc (⌊A / ((bigW (wOf B) : ℝ) * lamX d n x)⌋₊ + 1) ⌊A⌋₊,
          (1 / (ℓ : ℝ)) * S1ball d n x (A / (ℓ : ℝ)) := by
    refine le_trans (Finset.abs_sum_le_sum_abs _ _) (Finset.sum_le_sum (fun ℓ hℓ => ?_))
    obtain ⟨hℓ1, -⟩ := Finset.mem_Icc.mp hℓ
    have hℓ1' : 1 ≤ ℓ := by omega
    have hℓpos : (0 : ℝ) < (ℓ : ℝ) := by
      exact_mod_cast (lt_of_lt_of_le Nat.zero_lt_one hℓ1')
    have hSknn : 0 ≤ Sk d n 1
        (GamMix d n x y ((bigW (wOf B) : ℕ) / Nat.gcd ℓ (bigW (wOf B))))
        (TmixSet d n y (A / (ℓ : ℝ)) (Real.log B)) :=
      Sk_nonneg _ _ _
    calc |((ArithmeticFunction.moebius ℓ : ℝ) / (ℓ : ℝ)) *
            Sk d n 1 (GamMix d n x y ((bigW (wOf B) : ℕ) / Nat.gcd ℓ (bigW (wOf B))))
              (TmixSet d n y (A / (ℓ : ℝ)) (Real.log B))|
        = |((ArithmeticFunction.moebius ℓ : ℤ) : ℝ)| / (ℓ : ℝ) *
            Sk d n 1 (GamMix d n x y ((bigW (wOf B) : ℕ) / Nat.gcd ℓ (bigW (wOf B))))
              (TmixSet d n y (A / (ℓ : ℝ)) (Real.log B)) := by
          rw [abs_mul, abs_div, abs_of_pos hℓpos, abs_of_nonneg hSknn]
      _ ≤ (1 / (ℓ : ℝ)) *
            Sk d n 1 (GamMix d n x y ((bigW (wOf B) : ℕ) / Nat.gcd ℓ (bigW (wOf B))))
              (TmixSet d n y (A / (ℓ : ℝ)) (Real.log B)) := by
          refine mul_le_mul_of_nonneg_right ?_ hSknn
          exact div_le_div_of_nonneg_right (abs_moebius_cast_le_one_tail ℓ) hℓpos.le
      _ ≤ (1 / (ℓ : ℝ)) * S1ball d n x (A / (ℓ : ℝ)) := by
          refine mul_le_mul_of_nonneg_left ?_ (by positivity)
          exact ss1_Sk_le_S1ball d n x y ((bigW (wOf B) : ℕ) / Nat.gcd ℓ (bigW (wOf B)))
            (A / (ℓ : ℝ)) (Real.log B)
  have htail := tail_sum_le d n hd hdn K1 hK1pos.le hS1 A B hA1 x hx hWlam
  calc |∑ ℓ ∈ Finset.Icc (⌊A / ((bigW (wOf B) : ℝ) * lamX d n x)⌋₊ + 1) ⌊A⌋₊,
        ((ArithmeticFunction.moebius ℓ : ℝ) / (ℓ : ℝ)) *
          Sk d n 1 (GamMix d n x y ((bigW (wOf B) : ℕ) / Nat.gcd ℓ (bigW (wOf B))))
            (TmixSet d n y (A / (ℓ : ℝ)) (Real.log B))|
      ≤ ∑ ℓ ∈ Finset.Icc (⌊A / ((bigW (wOf B) : ℝ) * lamX d n x)⌋₊ + 1) ⌊A⌋₊,
          (1 / (ℓ : ℝ)) * S1ball d n x (A / (ℓ : ℝ)) := habs
    _ ≤ 2 * K1 * ((1 + Real.log A) ^ 2 *
            A ^ ((3 : ℝ) / 4 * ((NN d n - 2 : ℕ) : ℝ)) / eNorm (veronese d n x)
          + (1 + Real.log A)) := htail
    _ ≤ C * mixMain d n A B (x, y) / Real.log A :=
        hfin A B hBf hA56 hAB2 x y hx hy hLI hNx

end Work.HP.MM2
