import Mathlib.Analysis.CStarAlgebra.Classes
import Mathlib.Algebra.Order.Ring.Star
import Mathlib.Analysis.Normed.Lp.MeasurableSpace
import Mathlib.MeasureTheory.Function.L1Space.Integrable
import Mathlib.MeasureTheory.Measure.Haar.OfBasis
import Submission.Work.BoseBoxFock.K1dirBDefs
-- PORT435-BEGIN (v4.35 isDefEq respectTransparency compat)
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- PORT435-END

/-!
# `Work.BoseBoxFock.K1dirB.k1ErrD_tendsto` — the `θθ`-row error is uniformly small, from
`L¹` hypotheses alone

The target `Work.BoseBoxFock.k1ErrD v μ fu N Wa Wb` is the difference between the truncated
`θθ`-lattice sum `pinQD v μ N (k1cfun fu Wa Wb (ellH v μ) N)` and its limit
`pinQDl (ellH v μ) (Wa + Wb)`, i.e. the `θθ` row of the truncation error of the expanded pair
kernel `K1exp` against `K1lim` (`k1Kernel_decomp`).

The sibling `Submission/Work/BoseBoxFock/errBCD_sq_int_le.lean` proves the *uniform* smallness of
this error (`k1ErrD_uniform`) under the strong hypotheses that `Wa`, `Wb` are bounded, a.e.
strongly measurable and compactly supported, which are used there only to *linearise the limit
row*: `limit_rows_add` splits `pinQDl ℓ (Wa + Wb)` into `pinQDl ℓ Wa + pinQDl ℓ Wb`, and the
linearity of the Fourier transform `chat` in its kernel needs the two summands to be integrable.

That linearisation, however, needs **only integrability** (`Work.BoseRowsFS.CoulBilin.chat_add`),
and the convergence estimate itself (`k1Row_tendsto` + `k1BallTail_le` + `k1Row_sub_cut_le`) needs
no hypothesis on the weights at all beyond the *decay majorant* of the lattice family — which is
automatic, since `chat W` is dominated by the `L¹` mass `∫|W|`
(`Work.BoseBoxFock.chat_abs_le_uniform`) and `χ̂` decays at order `52`
(`Work.BoseBoxFock.hatChi_decay_52`).

This module therefore reproduces the short chain with the correct hypotheses:

* `chat_add_fun` — additivity of `chat` in the kernel (`Pi.add` spelling);
* `summable_pinQDl`, `pinQDl_add` — the limit row is additive for merely integrable weights;
* `rowLim_zero_eq_pinQDl` — the limit `θθ`-row at the origin is `pinQDl`;
* `k1ErrD_eq_integrable` — the splitting of `k1ErrD` into `(cut row + row) − (lim + lim)`;
* `k1RowCut_sub_lim_uniform`, `k1Row_pair_uniform` — the uniform convergence of one row and of the
  pair row (copies of the private helpers of `errBCD_sq_int_le`, with no regularity hypothesis);
* `k1ErrD_tendsto` — the target.

Everything is `sorry`-free.
-/

noncomputable section

open scoped BigOperators
open MeasureTheory

namespace Work.BoseBoxFock.K1dirB

local notation "E3" => EuclideanSpace ℝ (Fin 3)

set_option maxHeartbeats 1000000
set_option linter.unusedVariables false

/-! ## 1. Additivity of the Fourier transform and of the `θθ`-limit row -/

/-- `chat` is additive in its kernel, in the `W + U` (`Pi.add`) spelling. -/
private lemma chat_add_fun {W U : E3 → ℝ} (hW : MeasureTheory.Integrable W)
    (hU : MeasureTheory.Integrable U) (k : E3) :
    Work.BoseFixR.chat (W + U) k = Work.BoseFixR.chat W k + Work.BoseFixR.chat U k := by
  have h : (W + U : E3 → ℝ) = fun x => W x + U x := rfl
  rw [h]
  exact Work.BoseRowsFS.CoulBilin.chat_add hW hU k

/-- The summand family of `pinQDl` is summable: it is exactly the `k = 2` `χ̂`-weighted lattice
family `k1ChiHatSqWt`, whose decay majorant is `k1ChiHatSqWt_majorant`. -/
private lemma summable_pinQDl {ℓ : ℝ} (hℓ : 0 < ℓ) (W : E3 → ℝ) :
    Summable (fun n : Fin 3 → ℤ => ((Work.BoseFixR.chat W (Work.BoseBoxFock.kmomInt ℓ n) : ℝ) : ℂ)
      * (((Work.BoseK15.corpusBox.hatChi (ℓ • Work.BoseBoxFock.kmomInt ℓ n) : ℝ) : ℂ)) ^ 2) := by
  obtain ⟨C, hC0, hC⟩ := Work.BoseBoxFock.k1ChiHatSqWt_majorant hℓ W
  refine Summable.of_norm_bounded
    ((Work.BoseBoxFock.summable_vec_inv_one_add_norm_sq (k := 52) (by norm_num)).mul_left C)
    (fun n => ?_)
  simpa only [Work.BoseBoxFock.k1ChiHatSqWt] using hC n

/-- **The `θθ`-limit row is additive in the weight**, for merely integrable weights. -/
private lemma pinQDl_add {ℓ : ℝ} (hℓ : 0 < ℓ) {W U : E3 → ℝ}
    (hW : MeasureTheory.Integrable W) (hU : MeasureTheory.Integrable U) :
    Work.BoseBoxFock.pinQDl ℓ (W + U)
      = Work.BoseBoxFock.pinQDl ℓ W + Work.BoseBoxFock.pinQDl ℓ U := by
  have hsumA := summable_pinQDl hℓ W
  have hsumB := summable_pinQDl hℓ U
  have hpt : ∀ n : Fin 3 → ℤ,
      ((Work.BoseFixR.chat (W + U) (Work.BoseBoxFock.kmomInt ℓ n) : ℝ) : ℂ)
        * (((Work.BoseK15.corpusBox.hatChi (ℓ • Work.BoseBoxFock.kmomInt ℓ n) : ℝ) : ℂ)) ^ 2
      = (((Work.BoseFixR.chat W (Work.BoseBoxFock.kmomInt ℓ n) : ℝ) : ℂ)
          * (((Work.BoseK15.corpusBox.hatChi (ℓ • Work.BoseBoxFock.kmomInt ℓ n) : ℝ) : ℂ)) ^ 2)
        + (((Work.BoseFixR.chat U (Work.BoseBoxFock.kmomInt ℓ n) : ℝ) : ℂ)
          * (((Work.BoseK15.corpusBox.hatChi (ℓ • Work.BoseBoxFock.kmomInt ℓ n) : ℝ) : ℂ)) ^ 2) := by
    intro n
    rw [chat_add_fun hW hU (Work.BoseBoxFock.kmomInt ℓ n)]
    push_cast
    ring
  rw [Work.BoseBoxFock.pinQDl]
  rw [show (fun n : Fin 3 → ℤ =>
        ((Work.BoseFixR.chat (W + U) (Work.BoseBoxFock.kmomInt ℓ n) : ℝ) : ℂ)
          * (((Work.BoseK15.corpusBox.hatChi (ℓ • Work.BoseBoxFock.kmomInt ℓ n) : ℝ) : ℂ)) ^ 2)
      = fun n : Fin 3 → ℤ =>
        (((Work.BoseFixR.chat W (Work.BoseBoxFock.kmomInt ℓ n) : ℝ) : ℂ)
            * (((Work.BoseK15.corpusBox.hatChi (ℓ • Work.BoseBoxFock.kmomInt ℓ n) : ℝ) : ℂ)) ^ 2)
          + (((Work.BoseFixR.chat U (Work.BoseBoxFock.kmomInt ℓ n) : ℝ) : ℂ)
            * (((Work.BoseK15.corpusBox.hatChi (ℓ • Work.BoseBoxFock.kmomInt ℓ n) : ℝ) : ℂ)) ^ 2) from
      funext hpt]
  rw [Summable.tsum_add hsumA hsumB]
  rfl

/-- The generic limit row at the origin is `pinQDl` (the lattice character at `z = 0` is `1`). -/
private lemma rowLim_zero_eq_pinQDl (ℓ : ℝ) (W : E3 → ℝ) :
    Work.BoseBoxFock.k1RowLim ℓ (Work.BoseBoxFock.k1ChiHatSqWt ℓ W) 0
      = Work.BoseBoxFock.pinQDl ℓ W := by
  rw [Work.BoseBoxFock.k1RowLim, Work.BoseBoxFock.pinQDl]
  refine tsum_congr fun n => ?_
  simp only [Work.BoseBoxFock.k1ChiHatSqWt, Work.BoseBoxFock.latChr, inner_zero_right,
    Complex.ofReal_zero, mul_zero, Complex.exp_zero, mul_one]

/-! ## 2. The splitting of `k1ErrD` under integrability alone -/

/-- **The `θθ`-row error splits into (cut row + row) − (lim + lim)**, with the limit row
linearised by the additivity `chat (Wa + Wb) = chat Wa + chat Wb` — for merely integrable
weights. -/
private lemma k1ErrD_eq_integrable {v : E3 → ℝ} {μ : ℝ} (fu : Work.BoseBoxFix.LowCut)
    {Wa Wb : E3 → ℝ} (hWai : MeasureTheory.Integrable Wa) (hWbi : MeasureTheory.Integrable Wb)
    (N : ℕ) :
    Work.BoseBoxFock.k1ErrD v μ fu N Wa Wb
      = (Work.BoseBoxFock.k1RowCut (Work.BoseBoxFock.ellH v μ) fu N
            (Work.BoseBoxFock.k1ChiHatSqWt (Work.BoseBoxFock.ellH v μ) Wa) 0
          + Work.BoseBoxFock.k1Row (Work.BoseBoxFock.ellH v μ) N
            (Work.BoseBoxFock.k1ChiHatSqWt (Work.BoseBoxFock.ellH v μ) Wb) 0)
        - (Work.BoseBoxFock.k1RowLim (Work.BoseBoxFock.ellH v μ)
            (Work.BoseBoxFock.k1ChiHatSqWt (Work.BoseBoxFock.ellH v μ) Wa) 0
          + Work.BoseBoxFock.k1RowLim (Work.BoseBoxFock.ellH v μ)
            (Work.BoseBoxFock.k1ChiHatSqWt (Work.BoseBoxFock.ellH v μ) Wb) 0) := by
  unfold Work.BoseBoxFock.k1ErrD
  rw [Work.BoseBoxFock.k1pinQD_split fu N,
    pinQDl_add (Work.BoseBoxFock.ellH_pos v μ) hWai hWbi,
    ← rowLim_zero_eq_pinQDl (Work.BoseBoxFock.ellH v μ) Wa,
    ← rowLim_zero_eq_pinQDl (Work.BoseBoxFock.ellH v μ) Wb]

/-! ## 3. Uniform convergence of a row and of a pair row

These are copies of the private helpers of `Submission/Work/BoseBoxFock/errBCD_sq_int_le.lean`,
whose only hypothesis on the weight is the order-`52` decay majorant of the lattice family. -/

/-- Summability of the truncated ball tail of a family with order-`52` decay. -/
private lemma summable_trunc_norm {F : (Fin 3 → ℤ) → ℂ} {C : ℝ} (hC0 : 0 ≤ C)
    (hC : ∀ n : Fin 3 → ℤ, ‖F n‖ ≤ C * ((1 + ‖Work.BoseB4.vec n‖ ^ 2) ^ 52)⁻¹) (ρ : ℝ) :
    Summable (fun n : Fin 3 → ℤ => if ρ ≤ ‖latVec n‖ then ‖F n‖ else 0) := by
  refine Summable.of_nonneg_of_le (fun n => ?_) (fun n => ?_)
    ((Work.BoseBoxFock.summable_vec_inv_one_add_norm_sq (k := 52) (by norm_num)).mul_left C)
  · split <;> positivity
  · split
    · exact hC n
    · exact mul_nonneg hC0 (by positivity)

/-- **A cut row converges uniformly to its limit row.** -/
private lemma k1RowCut_sub_lim_uniform {ℓ : ℝ} (hℓ : 0 < ℓ) (fu : Work.BoseBoxFix.LowCut)
    {F : (Fin 3 → ℤ) → ℂ}
    (hF : ∃ C : ℝ, 0 ≤ C ∧ ∀ n : Fin 3 → ℤ,
      ‖F n‖ ≤ C * ((1 + ‖Work.BoseB4.vec n‖ ^ 2) ^ 52)⁻¹) :
    ∀ ε : ℝ, 0 < ε → ∃ N : ℕ, ∀ N' : ℕ, N ≤ N' → ∀ z : E3,
      ‖Work.BoseBoxFock.k1RowCut ℓ fu N' F z - Work.BoseBoxFock.k1RowLim ℓ F z‖ ≤ ε := by
  intro ε hε
  obtain ⟨N₁, h₁⟩ := Work.BoseBoxFock.k1Row_tendsto hℓ hF (ε / 2) (by linarith)
  obtain ⟨M, hM⟩ := Work.BoseBoxFock.k1BallTail_le (ℓ := ℓ) hℓ hF (ε / 2) (by linarith)
  obtain ⟨C, hC0, hC⟩ := hF
  refine ⟨max (max N₁ 1) (4 * M), fun N' hN' z => ?_⟩
  have hN₁ : N₁ ≤ N' := le_trans (le_trans (le_max_left _ _) (le_max_left _ _)) hN'
  have h1N' : 1 ≤ N' := le_trans (le_trans (le_max_right _ _) (le_max_left _ _)) hN'
  have h4M : 4 * M ≤ N' := le_trans (le_max_right _ _) hN'
  have htailcut : ‖Work.BoseBoxFock.k1Row ℓ N' F z - Work.BoseBoxFock.k1RowCut ℓ fu N' F z‖
      ≤ ∑' n : Fin 3 → ℤ, (if (N' : ℝ) / 4 ≤ ‖latVec n‖ then ‖F n‖ else 0) :=
    Work.BoseBoxFock.k1Row_sub_cut_le hℓ fu h1N' ⟨C, hC0, hC⟩ z
  have hmono : (∑' n : Fin 3 → ℤ, (if (N' : ℝ) / 4 ≤ ‖latVec n‖ then ‖F n‖ else 0))
      ≤ ∑' n : Fin 3 → ℤ, (if (M : ℝ) ≤ ‖latVec n‖ then ‖F n‖ else 0) := by
    refine Work.BoseBoxFock.k1BallTail_mono (F := F) (ρ := (M : ℝ)) (ρ' := (N' : ℝ) / 4) ?_
      (summable_trunc_norm hC0 hC ((N' : ℝ) / 4)) (summable_trunc_norm hC0 hC ((M : ℝ)))
    have h2 : ((4 * M : ℕ) : ℝ) ≤ (N' : ℝ) := by exact_mod_cast h4M
    push_cast at h2
    linarith
  have htail : (∑' n : Fin 3 → ℤ, (if (M : ℝ) ≤ ‖latVec n‖ then ‖F n‖ else 0)) ≤ ε / 2 :=
    hM M le_rfl
  have hcut : ‖Work.BoseBoxFock.k1RowCut ℓ fu N' F z - Work.BoseBoxFock.k1Row ℓ N' F z‖ ≤ ε / 2 := by
    rw [norm_sub_rev]
    exact le_trans htailcut (le_trans hmono htail)
  have hlim : ‖Work.BoseBoxFock.k1Row ℓ N' F z - Work.BoseBoxFock.k1RowLim ℓ F z‖ ≤ ε / 2 :=
    h₁ N' hN₁ z
  calc ‖Work.BoseBoxFock.k1RowCut ℓ fu N' F z - Work.BoseBoxFock.k1RowLim ℓ F z‖
      = ‖(Work.BoseBoxFock.k1RowCut ℓ fu N' F z - Work.BoseBoxFock.k1Row ℓ N' F z)
          + (Work.BoseBoxFock.k1Row ℓ N' F z - Work.BoseBoxFock.k1RowLim ℓ F z)‖ := by
        congr 1; ring
    _ ≤ ‖Work.BoseBoxFock.k1RowCut ℓ fu N' F z - Work.BoseBoxFock.k1Row ℓ N' F z‖
          + ‖Work.BoseBoxFock.k1Row ℓ N' F z - Work.BoseBoxFock.k1RowLim ℓ F z‖ := norm_add_le _ _
    _ ≤ ε / 2 + ε / 2 := add_le_add hcut hlim
    _ = ε := by ring

/-- **The pair row `(cut + row) − (lim + lim)` is uniformly small.** -/
private lemma k1Row_pair_uniform {ℓ : ℝ} (hℓ : 0 < ℓ) (fu : Work.BoseBoxFix.LowCut)
    {Fa Fb : (Fin 3 → ℤ) → ℂ}
    (hFa : ∃ C : ℝ, 0 ≤ C ∧ ∀ n : Fin 3 → ℤ,
      ‖Fa n‖ ≤ C * ((1 + ‖Work.BoseB4.vec n‖ ^ 2) ^ 52)⁻¹)
    (hFb : ∃ C : ℝ, 0 ≤ C ∧ ∀ n : Fin 3 → ℤ,
      ‖Fb n‖ ≤ C * ((1 + ‖Work.BoseB4.vec n‖ ^ 2) ^ 52)⁻¹) :
    ∀ ε : ℝ, 0 < ε → ∃ N : ℕ, ∀ N' : ℕ, N ≤ N' → ∀ z : E3,
      ‖(Work.BoseBoxFock.k1RowCut ℓ fu N' Fa z + Work.BoseBoxFock.k1Row ℓ N' Fb z)
        - (Work.BoseBoxFock.k1RowLim ℓ Fa z + Work.BoseBoxFock.k1RowLim ℓ Fb z)‖ ≤ ε := by
  intro ε hε
  obtain ⟨Na, ha⟩ := k1RowCut_sub_lim_uniform hℓ fu hFa (ε / 2) (by linarith)
  obtain ⟨Nb, hb⟩ := Work.BoseBoxFock.k1Row_tendsto hℓ hFb (ε / 2) (by linarith)
  refine ⟨max Na Nb, fun N' hN' z => ?_⟩
  have ha' := ha N' (le_trans (le_max_left _ _) hN') z
  have hb' := hb N' (le_trans (le_max_right _ _) hN') z
  calc ‖(Work.BoseBoxFock.k1RowCut ℓ fu N' Fa z + Work.BoseBoxFock.k1Row ℓ N' Fb z)
        - (Work.BoseBoxFock.k1RowLim ℓ Fa z + Work.BoseBoxFock.k1RowLim ℓ Fb z)‖
      = ‖(Work.BoseBoxFock.k1RowCut ℓ fu N' Fa z - Work.BoseBoxFock.k1RowLim ℓ Fa z)
          + (Work.BoseBoxFock.k1Row ℓ N' Fb z - Work.BoseBoxFock.k1RowLim ℓ Fb z)‖ := by
        congr 1; ring
    _ ≤ ‖Work.BoseBoxFock.k1RowCut ℓ fu N' Fa z - Work.BoseBoxFock.k1RowLim ℓ Fa z‖
          + ‖Work.BoseBoxFock.k1Row ℓ N' Fb z - Work.BoseBoxFock.k1RowLim ℓ Fb z‖ := norm_add_le _ _
    _ ≤ ε / 2 + ε / 2 := add_le_add ha' hb'
    _ = ε := by ring

/-! ## 4. The target -/

theorem k1ErrD_tendsto {v : EuclideanSpace ℝ (Fin 3) → ℝ} {μ : ℝ} (fu : Work.BoseBoxFix.LowCut)
    {Wa Wb : EuclideanSpace ℝ (Fin 3) → ℝ} (hWai : MeasureTheory.Integrable Wa)
    (hWbi : MeasureTheory.Integrable Wb) :
    ∀ ε : ℝ, 0 < ε → ∃ N₀ : ℕ, ∀ N : ℕ, N₀ ≤ N →
      ‖Work.BoseBoxFock.k1ErrD v μ fu N Wa Wb‖ ≤ ε := by
  intro ε hε
  have hℓ : 0 < Work.BoseBoxFock.ellH v μ := Work.BoseBoxFock.ellH_pos v μ
  obtain ⟨N, hN⟩ := k1Row_pair_uniform hℓ fu
    (Work.BoseBoxFock.k1ChiHatSqWt_majorant hℓ Wa)
    (Work.BoseBoxFock.k1ChiHatSqWt_majorant hℓ Wb) ε hε
  refine ⟨N, fun N' hN' => ?_⟩
  rw [k1ErrD_eq_integrable fu hWai hWbi N']
  exact hN N' hN' 0

end Work.BoseBoxFock.K1dirB
