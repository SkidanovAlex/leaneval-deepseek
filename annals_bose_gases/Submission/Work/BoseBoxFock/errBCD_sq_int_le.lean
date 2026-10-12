import Mathlib.Analysis.CStarAlgebra.Classes
import Mathlib.Algebra.Order.Ring.Star
import Mathlib.Algebra.Order.Star.Real
import Mathlib.Analysis.Normed.Lp.MeasurableSpace
import Mathlib.MeasureTheory.Integral.Bochner.Set
import Mathlib.MeasureTheory.Measure.Haar.OfBasis
import Submission.Work.BoseBoxFock.K1pairingDefs
-- PORT435-BEGIN (v4.35 isDefEq respectTransparency compat)
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- PORT435-END

/-!
# `Work.BoseBoxFock.errBCD_sq_int_le` — the three `χ̂`-row errors are `L²`-small

The truncation error of the expanded pair kernel `K1exp` against its limit `K1lim` splits into
the four rows `χχ, χ̂, χ̂, χ̂²` (`k1Kernel_decomp`).  This file closes the three `χ̂`-rows: the
functions `k1ErrB`, `k1ErrC` and the constant `k1ErrD` are `L²(boxL (ellH v μ))`-small as the
lattice size `N' → ∞`.  (The remaining `χχ`-row `k1ErrA` is the sibling
`Submission/Work/BoseBoxFock/errA_sq_int_le.lean`, whose convergence is the oscillatory
periodisation statement — the `χ̂`-rows treated here are *absolutely* convergent.)

## Route

The `χ̂`-rows `pinQB`, `pinQC`, `pinQD` split into the generic lattice rows (`k1pinQB_split`,
`k1pinQC_split`, `k1pinQD_split` are *definitional* rewrites of `K1pairingDefs`), and the limit
objects `pinQBl`, `pinQCl`, `pinQDl` are *definitionally* the limit rows `k1RowLim`/`k1RowLimM`
of the weight `k1ChiHatWt`/`k1ChiHatSqWt`.  Hence every error is a sum of two pieces

* `k1RowCut − k1RowLim` for `k1ChiHatWt`/`k1ChiHatSqWt` — the *cut* row against the *limit* row;
* `k1Row − k1RowLim` — the *un-cut* row against the limit row.

Both are small **uniformly in the position variable**:

* `k1RowCut_sub_lim_uniform` bounds `k1RowCut − k1RowLim` by `‖k1Row − k1RowCut‖ + ‖k1Row −
  k1RowLim‖`; the second is `k1Row_tendsto` (proved, uniform in `z`), and the first is
  `k1Row_sub_cut_le` (proved: the cut is inactive on the ball of radius `N/4`, so the difference
  is bounded by the lattice *ball* tail of `‖F‖`) together with `k1BallTail_le` /
  `k1BallTail_mono` (proved: the ball tail of a family with order-`52` decay is arbitrarily
  small, and tails are monotone in the threshold).

The weights `k1ChiHatWt`/`k1ChiHatSqWt` do have order-`52` decay, by the proved majorants
`k1ChiHatWt_majorant`/`k1ChiHatSqWt_majorant` (`Ŵ` is bounded by its `L¹` mass, `χ̂` decays at
order `52`).

Finally a uniform bound `‖f z‖ ≤ K` gives `∫_{boxL ℓ} ‖f z‖² ≤ K²·ℓ³` (`boxL` has volume `ℓ³`),
and `K := √(ε/(ℓ³+1))` makes this `≤ ε`.  No orthogonality of the lattice characters is used.
-/

namespace Work.BoseBoxFock

open MeasureTheory

local notation "E3" => EuclideanSpace ℝ (Fin 3)

set_option maxHeartbeats 1000000
set_option linter.unusedVariables false

/-! ## 1. Summability of the truncated ball tails -/

private lemma summable_trunc_norm {F : (Fin 3 → ℤ) → ℂ} {C : ℝ} (hC0 : 0 ≤ C)
    (hC : ∀ n : Fin 3 → ℤ, ‖F n‖ ≤ C * ((1 + ‖Work.BoseB4.vec n‖ ^ 2) ^ 52)⁻¹) (ρ : ℝ) :
    Summable (fun n : Fin 3 → ℤ => if ρ ≤ ‖latVec n‖ then ‖F n‖ else 0) := by
  refine Summable.of_nonneg_of_le (fun n => ?_) (fun n => ?_)
    ((summable_vec_inv_one_add_norm_sq (k := 52) (by norm_num)).mul_left C)
  · split <;> positivity
  · split
    · exact hC n
    · exact mul_nonneg hC0 (by positivity)

/-! ## 2. Uniform convergence of the cut row to the limit row -/

private lemma k1RowCut_sub_lim_uniform {ℓ : ℝ} (hℓ : 0 < ℓ) (fu : Work.BoseBoxFix.LowCut)
    {F : (Fin 3 → ℤ) → ℂ}
    (hF : ∃ C : ℝ, 0 ≤ C ∧ ∀ n : Fin 3 → ℤ,
      ‖F n‖ ≤ C * ((1 + ‖Work.BoseB4.vec n‖ ^ 2) ^ 52)⁻¹) :
    ∀ ε : ℝ, 0 < ε → ∃ N : ℕ, ∀ N' : ℕ, N ≤ N' → ∀ z : E3,
      ‖k1RowCut ℓ fu N' F z - k1RowLim ℓ F z‖ ≤ ε := by
  intro ε hε
  obtain ⟨N₁, h₁⟩ := k1Row_tendsto hℓ hF (ε / 2) (by linarith)
  obtain ⟨M, hM⟩ := k1BallTail_le (ℓ := ℓ) hℓ hF (ε / 2) (by linarith)
  obtain ⟨C, hC0, hC⟩ := hF
  refine ⟨max (max N₁ 1) (4 * M), fun N' hN' z => ?_⟩
  have hN₁ : N₁ ≤ N' := le_trans (le_trans (le_max_left _ _) (le_max_left _ _)) hN'
  have h1N' : 1 ≤ N' := le_trans (le_trans (le_max_right _ _) (le_max_left _ _)) hN'
  have h4M : 4 * M ≤ N' := le_trans (le_max_right _ _) hN'
  have htailcut : ‖k1Row ℓ N' F z - k1RowCut ℓ fu N' F z‖
      ≤ ∑' n : Fin 3 → ℤ, (if (N' : ℝ) / 4 ≤ ‖latVec n‖ then ‖F n‖ else 0) :=
    k1Row_sub_cut_le hℓ fu h1N' ⟨C, hC0, hC⟩ z
  have hmono : (∑' n : Fin 3 → ℤ, (if (N' : ℝ) / 4 ≤ ‖latVec n‖ then ‖F n‖ else 0))
      ≤ ∑' n : Fin 3 → ℤ, (if (M : ℝ) ≤ ‖latVec n‖ then ‖F n‖ else 0) := by
    refine k1BallTail_mono (F := F) (ρ := (M : ℝ)) (ρ' := (N' : ℝ) / 4) ?_
      (summable_trunc_norm hC0 hC ((N' : ℝ) / 4)) (summable_trunc_norm hC0 hC ((M : ℝ)))
    have h2 : ((4 * M : ℕ) : ℝ) ≤ (N' : ℝ) := by exact_mod_cast h4M
    push_cast at h2
    linarith
  have htail : (∑' n : Fin 3 → ℤ, (if (M : ℝ) ≤ ‖latVec n‖ then ‖F n‖ else 0)) ≤ ε / 2 :=
    hM M le_rfl
  have hcut : ‖k1RowCut ℓ fu N' F z - k1Row ℓ N' F z‖ ≤ ε / 2 := by
    rw [norm_sub_rev]
    exact le_trans htailcut (le_trans hmono htail)
  have hlim : ‖k1Row ℓ N' F z - k1RowLim ℓ F z‖ ≤ ε / 2 := h₁ N' hN₁ z
  calc ‖k1RowCut ℓ fu N' F z - k1RowLim ℓ F z‖
      = ‖(k1RowCut ℓ fu N' F z - k1Row ℓ N' F z) + (k1Row ℓ N' F z - k1RowLim ℓ F z)‖ := by
        congr 1; ring
    _ ≤ ‖k1RowCut ℓ fu N' F z - k1Row ℓ N' F z‖
          + ‖k1Row ℓ N' F z - k1RowLim ℓ F z‖ := norm_add_le _ _
    _ ≤ ε / 2 + ε / 2 := add_le_add hcut hlim
    _ = ε := by ring

/-- The pair row `(cut + row) − (limit + limit)` is uniformly small. -/
private lemma k1pairRow_uniform {ℓ : ℝ} (hℓ : 0 < ℓ) (fu : Work.BoseBoxFix.LowCut)
    {Fa Fb : (Fin 3 → ℤ) → ℂ}
    (hFa : ∃ C : ℝ, 0 ≤ C ∧ ∀ n : Fin 3 → ℤ,
      ‖Fa n‖ ≤ C * ((1 + ‖Work.BoseB4.vec n‖ ^ 2) ^ 52)⁻¹)
    (hFb : ∃ C : ℝ, 0 ≤ C ∧ ∀ n : Fin 3 → ℤ,
      ‖Fb n‖ ≤ C * ((1 + ‖Work.BoseB4.vec n‖ ^ 2) ^ 52)⁻¹) :
    ∀ ε : ℝ, 0 < ε → ∃ N : ℕ, ∀ N' : ℕ, N ≤ N' → ∀ z : E3,
      ‖(k1RowCut ℓ fu N' Fa z + k1Row ℓ N' Fb z)
        - (k1RowLim ℓ Fa z + k1RowLim ℓ Fb z)‖ ≤ ε := by
  intro ε hε
  obtain ⟨Na, ha⟩ := k1RowCut_sub_lim_uniform hℓ fu hFa (ε / 2) (by linarith)
  obtain ⟨Nb, hb⟩ := k1Row_tendsto hℓ hFb (ε / 2) (by linarith)
  refine ⟨max Na Nb, fun N' hN' z => ?_⟩
  have ha' := ha N' (le_trans (le_max_left _ _) hN') z
  have hb' := hb N' (le_trans (le_max_right _ _) hN') z
  calc ‖(k1RowCut ℓ fu N' Fa z + k1Row ℓ N' Fb z)
        - (k1RowLim ℓ Fa z + k1RowLim ℓ Fb z)‖
      = ‖(k1RowCut ℓ fu N' Fa z - k1RowLim ℓ Fa z)
          + (k1Row ℓ N' Fb z - k1RowLim ℓ Fb z)‖ := by
        congr 1; ring
    _ ≤ ‖k1RowCut ℓ fu N' Fa z - k1RowLim ℓ Fa z‖
          + ‖k1Row ℓ N' Fb z - k1RowLim ℓ Fb z‖ := norm_add_le _ _
    _ ≤ ε / 2 + ε / 2 := add_le_add ha' hb'
    _ = ε := by ring

/-! ## 3. The limit kernels are the limit rows of the `χ̂`-weights -/

private lemma pinQBl_eq_k1RowLim (ℓ : ℝ) (W : E3 → ℝ) (w : E3) :
    pinQBl ℓ W w = k1RowLim ℓ (k1ChiHatWt ℓ W) w := rfl

private lemma pinQCl_eq_k1RowLimM (ℓ : ℝ) (W : E3 → ℝ) (y : E3) :
    pinQCl ℓ W y = k1RowLimM ℓ (k1ChiHatWt ℓ W) y := rfl

private lemma pinQDl_eq_k1RowLim_zero (ℓ : ℝ) (W : E3 → ℝ) :
    pinQDl ℓ W = k1RowLim ℓ (k1ChiHatSqWt ℓ W) 0 := by
  rw [pinQDl, k1RowLim]
  refine tsum_congr fun n => ?_
  simp only [k1ChiHatSqWt, latChr, inner_zero_right, Complex.ofReal_zero, mul_zero,
    Complex.exp_zero, mul_one]

/-! ## 4. The three error functions as pair rows -/

private lemma k1ErrB_eq {v : E3 → ℝ} {μ : ℝ} (fu : Work.BoseBoxFix.LowCut) {Wa Wb : E3 → ℝ}
    (hWam : AEStronglyMeasurable Wa volume) (hWab : ∃ C : ℝ, ∀ x, ‖Wa x‖ ≤ C)
    (hWas : HasCompactSupport Wa)
    (hWbm : AEStronglyMeasurable Wb volume) (hWbb : ∃ C : ℝ, ∀ x, ‖Wb x‖ ≤ C)
    (hWbs : HasCompactSupport Wb) (N : ℕ) (w : E3) :
    k1ErrB v μ fu N Wa Wb w
      = (k1RowCut (ellH v μ) fu N (k1ChiHatWt (ellH v μ) Wa) w
          + k1Row (ellH v μ) N (k1ChiHatWt (ellH v μ) Wb) w)
        - (k1RowLim (ellH v μ) (k1ChiHatWt (ellH v μ) Wa) w
          + k1RowLim (ellH v μ) (k1ChiHatWt (ellH v μ) Wb) w) := by
  unfold k1ErrB
  rw [k1pinQB_split fu N w, (limit_rows_add hWam hWab hWas hWbm hWbb hWbs).1 w,
    pinQBl_eq_k1RowLim, pinQBl_eq_k1RowLim]

private lemma k1ErrC_eq {v : E3 → ℝ} {μ : ℝ} (fu : Work.BoseBoxFix.LowCut) {Wa Wb : E3 → ℝ}
    (hWam : AEStronglyMeasurable Wa volume) (hWab : ∃ C : ℝ, ∀ x, ‖Wa x‖ ≤ C)
    (hWas : HasCompactSupport Wa)
    (hWbm : AEStronglyMeasurable Wb volume) (hWbb : ∃ C : ℝ, ∀ x, ‖Wb x‖ ≤ C)
    (hWbs : HasCompactSupport Wb) (N : ℕ) (y : E3) :
    k1ErrC v μ fu N Wa Wb y
      = (k1RowCut (ellH v μ) fu N (k1ChiHatWt (ellH v μ) Wa) (-y)
          + k1Row (ellH v μ) N (k1ChiHatWt (ellH v μ) Wb) (-y))
        - (k1RowLim (ellH v μ) (k1ChiHatWt (ellH v μ) Wa) (-y)
          + k1RowLim (ellH v μ) (k1ChiHatWt (ellH v μ) Wb) (-y)) := by
  unfold k1ErrC
  rw [k1pinQC_split fu N y, (limit_rows_add hWam hWab hWas hWbm hWbb hWbs).2.1 y,
    pinQCl_eq_k1RowLimM, pinQCl_eq_k1RowLimM, k1RowCutM_eq, k1RowM_eq, k1RowLimM_eq,
    k1RowLimM_eq]

private lemma k1ErrD_eq {v : E3 → ℝ} {μ : ℝ} (fu : Work.BoseBoxFix.LowCut) {Wa Wb : E3 → ℝ}
    (hWam : AEStronglyMeasurable Wa volume) (hWab : ∃ C : ℝ, ∀ x, ‖Wa x‖ ≤ C)
    (hWas : HasCompactSupport Wa)
    (hWbm : AEStronglyMeasurable Wb volume) (hWbb : ∃ C : ℝ, ∀ x, ‖Wb x‖ ≤ C)
    (hWbs : HasCompactSupport Wb) (N : ℕ) :
    k1ErrD v μ fu N Wa Wb
      = (k1RowCut (ellH v μ) fu N (k1ChiHatSqWt (ellH v μ) Wa) 0
          + k1Row (ellH v μ) N (k1ChiHatSqWt (ellH v μ) Wb) 0)
        - (k1RowLim (ellH v μ) (k1ChiHatSqWt (ellH v μ) Wa) 0
          + k1RowLim (ellH v μ) (k1ChiHatSqWt (ellH v μ) Wb) 0) := by
  unfold k1ErrD
  rw [k1pinQD_split fu N, (limit_rows_add hWam hWab hWas hWbm hWbb hWbs).2.2.1,
    pinQDl_eq_k1RowLim_zero, pinQDl_eq_k1RowLim_zero]

/-! ## 5. Uniform smallness of the three errors -/

private lemma k1ErrB_uniform {v : E3 → ℝ} {μ : ℝ} (fu : Work.BoseBoxFix.LowCut) {Wa Wb : E3 → ℝ}
    (hWam : AEStronglyMeasurable Wa volume) (hWab : ∃ C : ℝ, ∀ x, ‖Wa x‖ ≤ C)
    (hWas : HasCompactSupport Wa)
    (hWbm : AEStronglyMeasurable Wb volume) (hWbb : ∃ C : ℝ, ∀ x, ‖Wb x‖ ≤ C)
    (hWbs : HasCompactSupport Wb) :
    ∀ ε : ℝ, 0 < ε → ∃ N : ℕ, ∀ N' : ℕ, N ≤ N' → ∀ w : E3,
      ‖k1ErrB v μ fu N' Wa Wb w‖ ≤ ε := by
  intro ε hε
  have hℓ : 0 < ellH v μ := ellH_pos v μ
  obtain ⟨N, hN⟩ := k1pairRow_uniform hℓ fu (k1ChiHatWt_majorant hℓ Wa)
    (k1ChiHatWt_majorant hℓ Wb) ε hε
  refine ⟨N, fun N' hN' w => ?_⟩
  rw [k1ErrB_eq fu hWam hWab hWas hWbm hWbb hWbs N' w]
  exact hN N' hN' w

private lemma k1ErrC_uniform {v : E3 → ℝ} {μ : ℝ} (fu : Work.BoseBoxFix.LowCut) {Wa Wb : E3 → ℝ}
    (hWam : AEStronglyMeasurable Wa volume) (hWab : ∃ C : ℝ, ∀ x, ‖Wa x‖ ≤ C)
    (hWas : HasCompactSupport Wa)
    (hWbm : AEStronglyMeasurable Wb volume) (hWbb : ∃ C : ℝ, ∀ x, ‖Wb x‖ ≤ C)
    (hWbs : HasCompactSupport Wb) :
    ∀ ε : ℝ, 0 < ε → ∃ N : ℕ, ∀ N' : ℕ, N ≤ N' → ∀ y : E3,
      ‖k1ErrC v μ fu N' Wa Wb y‖ ≤ ε := by
  intro ε hε
  have hℓ : 0 < ellH v μ := ellH_pos v μ
  obtain ⟨N, hN⟩ := k1pairRow_uniform hℓ fu (k1ChiHatWt_majorant hℓ Wa)
    (k1ChiHatWt_majorant hℓ Wb) ε hε
  refine ⟨N, fun N' hN' y => ?_⟩
  rw [k1ErrC_eq fu hWam hWab hWas hWbm hWbb hWbs N' y]
  exact hN N' hN' (-y)

private lemma k1ErrD_uniform {v : E3 → ℝ} {μ : ℝ} (fu : Work.BoseBoxFix.LowCut) {Wa Wb : E3 → ℝ}
    (hWam : AEStronglyMeasurable Wa volume) (hWab : ∃ C : ℝ, ∀ x, ‖Wa x‖ ≤ C)
    (hWas : HasCompactSupport Wa)
    (hWbm : AEStronglyMeasurable Wb volume) (hWbb : ∃ C : ℝ, ∀ x, ‖Wb x‖ ≤ C)
    (hWbs : HasCompactSupport Wb) :
    ∀ ε : ℝ, 0 < ε → ∃ N : ℕ, ∀ N' : ℕ, N ≤ N' →
      ‖k1ErrD v μ fu N' Wa Wb‖ ≤ ε := by
  intro ε hε
  have hℓ : 0 < ellH v μ := ellH_pos v μ
  obtain ⟨N, hN⟩ := k1pairRow_uniform hℓ fu (k1ChiHatSqWt_majorant hℓ Wa)
    (k1ChiHatSqWt_majorant hℓ Wb) ε hε
  refine ⟨N, fun N' hN' => ?_⟩
  rw [k1ErrD_eq fu hWam hWab hWas hWbm hWbb hWbs N']
  exact hN N' hN' 0

/-! ## 6. From a uniform bound to the `L²` bound over the box -/

/-- **The trivial `L²` bound over the corpus box.**  If `‖g z‖ ≤ K` pointwise, then
`∫_{boxL ℓ} ‖g z‖² ≤ K²·ℓ³`: the box has volume `ℓ³` and the integrand is dominated by the
constant `K²`; if the integrand is not integrable the Bochner integral is `0`
(`MeasureTheory.integral_undef`) and the inequality is trivial. -/
private lemma boxL_normSq_setIntegral_le {ℓ K : ℝ} (hℓ : 0 < ℓ) (hK : 0 ≤ K)
    {g : E3 → ℂ} (hg : ∀ z, ‖g z‖ ≤ K) :
    (∫ z in Work.BoseK15.corpusBox.boxL ℓ, ‖g z‖ ^ 2) ≤ K ^ 2 * ℓ ^ 3 := by
  have hvol : volume (Work.BoseK15.corpusBox.boxL ℓ) = ENNReal.ofReal (ℓ ^ 3) :=
    Work.BoseB4.BoxData.volume_boxL Work.BoseK15.corpusBox hℓ
  by_cases hInt : Integrable (fun z : E3 => ‖g z‖ ^ 2)
      (volume.restrict (Work.BoseK15.corpusBox.boxL ℓ))
  · have hfin : volume (Work.BoseK15.corpusBox.boxL ℓ) ≠ ⊤ := by
      rw [hvol]; exact ENNReal.ofReal_ne_top
    haveI : IsFiniteMeasure (volume.restrict (Work.BoseK15.corpusBox.boxL ℓ)) :=
      isFiniteMeasure_restrict.mpr hfin
    have hKint : Integrable (fun _ : E3 => K ^ 2)
        (volume.restrict (Work.BoseK15.corpusBox.boxL ℓ)) := integrable_const _
    have hmono := setIntegral_mono_on hInt hKint
      (Work.BoseB4.BoxData.boxL_measurableSet (B := Work.BoseK15.corpusBox) ℓ)
      (fun z _ => pow_le_pow_left₀ (norm_nonneg (g z)) (hg z) 2)
    refine hmono.trans (le_of_eq ?_)
    rw [setIntegral_const, smul_eq_mul]
    rw [show volume.real (Work.BoseK15.corpusBox.boxL ℓ) = ℓ ^ 3 by
      show (volume (Work.BoseK15.corpusBox.boxL ℓ)).toReal = ℓ ^ 3
      rw [hvol, ENNReal.toReal_ofReal (by positivity)]]
    ring
  · rw [integral_undef hInt]
    exact mul_nonneg (pow_nonneg hK 2) (pow_nonneg hℓ.le 3)

/-- The arithmetic of the choice `K = √(ε/(ℓ³+1))`: `K²·ℓ³ ≤ ε`. -/
private lemma sqrt_window_arith {ℓ ε : ℝ} (hℓ : 0 < ℓ) (hε : 0 < ε) :
    (Real.sqrt (ε / (ℓ ^ 3 + 1))) ^ 2 * ℓ ^ 3 ≤ ε := by
  have h1 : 0 < ℓ ^ 3 + 1 := by have := pow_pos hℓ 3; linarith
  have h2 : 0 ≤ ε / (ℓ ^ 3 + 1) := by positivity
  rw [Real.sq_sqrt h2]
  have h3 : ℓ ^ 3 / (ℓ ^ 3 + 1) ≤ 1 := by
    rw [div_le_one h1]; linarith
  calc ε / (ℓ ^ 3 + 1) * ℓ ^ 3 = ε * (ℓ ^ 3 / (ℓ ^ 3 + 1)) := by ring
    _ ≤ ε * 1 := mul_le_mul_of_nonneg_left h3 hε.le
    _ = ε := mul_one _

/-! ## 7. The target -/

theorem errBCD_sq_int_le {v : EuclideanSpace ℝ (Fin 3) → ℝ} {μ : ℝ}
    (fu : Work.BoseBoxFix.LowCut) {Wa Wb : EuclideanSpace ℝ (Fin 3) → ℝ}
    (hWam : MeasureTheory.AEStronglyMeasurable Wa MeasureTheory.volume)
    (hWab : ∃ C : ℝ, ∀ x, ‖Wa x‖ ≤ C) (hWas : HasCompactSupport Wa)
    (hWbm : MeasureTheory.AEStronglyMeasurable Wb MeasureTheory.volume)
    (hWbb : ∃ C : ℝ, ∀ x, ‖Wb x‖ ≤ C) (hWbs : HasCompactSupport Wb) :
    (∀ ε : ℝ, 0 < ε → ∃ N : ℕ, ∀ N' : ℕ, N ≤ N' →
        (∫ z in Work.BoseK15.corpusBox.boxL (Work.BoseBoxFock.ellH v μ),
          ‖Work.BoseBoxFock.k1ErrB v μ fu N' Wa Wb z‖ ^ 2) ≤ ε)
    ∧ (∀ ε : ℝ, 0 < ε → ∃ N : ℕ, ∀ N' : ℕ, N ≤ N' →
        (∫ z in Work.BoseK15.corpusBox.boxL (Work.BoseBoxFock.ellH v μ),
          ‖Work.BoseBoxFock.k1ErrC v μ fu N' Wa Wb z‖ ^ 2) ≤ ε)
    ∧ (∀ ε : ℝ, 0 < ε → ∃ N : ℕ, ∀ N' : ℕ, N ≤ N' →
        (∫ z in Work.BoseK15.corpusBox.boxL (Work.BoseBoxFock.ellH v μ),
          ‖Work.BoseBoxFock.k1ErrD v μ fu N' Wa Wb‖ ^ 2) ≤ ε) := by
  have hℓ : 0 < ellH v μ := ellH_pos v μ
  refine ⟨?_, ?_, ?_⟩
  · intro ε hε
    have hKpos : 0 < Real.sqrt (ε / ((ellH v μ) ^ 3 + 1)) :=
      Real.sqrt_pos.mpr (by positivity)
    obtain ⟨N, hN⟩ := k1ErrB_uniform (v := v) (μ := μ) fu hWam hWab hWas hWbm hWbb hWbs
      _ hKpos
    refine ⟨N, fun N' hN' => ?_⟩
    refine le_trans (boxL_normSq_setIntegral_le hℓ hKpos.le (fun z => hN N' hN' z))
      (sqrt_window_arith hℓ hε)
  · intro ε hε
    have hKpos : 0 < Real.sqrt (ε / ((ellH v μ) ^ 3 + 1)) :=
      Real.sqrt_pos.mpr (by positivity)
    obtain ⟨N, hN⟩ := k1ErrC_uniform (v := v) (μ := μ) fu hWam hWab hWas hWbm hWbb hWbs
      _ hKpos
    refine ⟨N, fun N' hN' => ?_⟩
    refine le_trans (boxL_normSq_setIntegral_le hℓ hKpos.le (fun z => hN N' hN' z))
      (sqrt_window_arith hℓ hε)
  · intro ε hε
    have hKpos : 0 < Real.sqrt (ε / ((ellH v μ) ^ 3 + 1)) :=
      Real.sqrt_pos.mpr (by positivity)
    obtain ⟨N, hN⟩ := k1ErrD_uniform (v := v) (μ := μ) fu hWam hWab hWas hWbm hWbb hWbs
      _ hKpos
    refine ⟨N, fun N' hN' => ?_⟩
    refine le_trans (boxL_normSq_setIntegral_le hℓ hKpos.le
      (g := fun _ : E3 => k1ErrD v μ fu N' Wa Wb) (fun _ => hN N' hN')) ?_
    exact sqrt_window_arith hℓ hε

end Work.BoseBoxFock
