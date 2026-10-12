import Mathlib.Analysis.CStarAlgebra.Classes
import Mathlib.LinearAlgebra.Complex.FiniteDimensional
import Mathlib.Algebra.Order.Ring.Star
import Mathlib.Analysis.Normed.Lp.MeasurableSpace
import Mathlib.MeasureTheory.Function.L1Space.Integrable
import Mathlib.MeasureTheory.Measure.Haar.OfBasis
import Submission.Work.BoseBoxFock.K1pairingDefs
-- PORT435-BEGIN (v4.35 isDefEq respectTransparency compat)
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- PORT435-END

/-!
# `Work.BoseBoxFock.K1dirB.k1ErrB_tendsto` — the first `χ̂`-row error is uniformly small

**Statement.**  For every `ε > 0` there is `N₀` with

    ‖k1ErrB v μ fu N Wa Wb w‖ ≤ ε      for all `N ≥ N₀` and all `w : ℝ³`,

where `k1ErrB v μ fu N Wa Wb = pinQB v μ N (k1cfun fu Wa Wb (ellH v μ) N) −
pinQBl (ellH v μ) (Wa + Wb)` is the first `χ̂`-row error of the `K1exp`/`K1lim` comparison
(`Submission.Work.BoseBoxFock.K1pairingDefs`), for **integrable** `Wa`, `Wb`.

## Route

The `χ̂`-sums `pinQB`/`pinQBl` are *absolutely* convergent lattice series, so no oscillation
control is needed.  By `k1pinQB_split` the truncated sum is

    pinQB v μ N (k1cfun fu Wa Wb (ellH v μ) N) w
      = k1RowCut ℓ fu N (k1ChiHatWt ℓ Wa) w + k1Row ℓ N (k1ChiHatWt ℓ Wb) w ,

and `pinQBl ℓ (Wa + Wb)` is the sum of the two limit rows `k1RowLim ℓ (k1ChiHatWt ℓ ·)`,
because `chat` is additive in its kernel on integrable kernels (`chat_add`,
`Work.BoseRowsFS.CoulBilin`).  Hence

    k1ErrB = (k1RowCut − k1RowLim)  [the `Wa`/cut piece]
           + (k1Row    − k1RowLim)  [the `Wb` piece],

and each piece is *uniformly* small in the position variable:

* `k1Row_tendsto` (proved) — the truncated row converges to its `tsum` uniformly;
* `k1Row_sub_cut_le` (proved) — the cut differs from the un-cut row only on the lattice ball of
  radius `N/4`, so `‖k1Row − k1RowCut‖` is bounded by that ball's tail, which is arbitrarily
  small by `k1BallTail_le`/`k1BallTail_mono` (proved).

The weight `k1ChiHatWt ℓ W n = Ŵ(kmomInt ℓ n)·χ̂(ℓ • kmomInt ℓ n)` has order-`52` lattice decay
for **every** `W` (`k1ChiHatWt_majorant`: `|Ŵ|` is bounded by the `L¹` mass `∫|W|`, and `χ̂`
decays at order `52`), which is exactly the majorant the three proved lattice-tail statements
consume.  No boundedness, measurability or compact-support hypothesis on `Wa`, `Wb` is used.

The comparison with the sibling `errBCD_sq_int_le.lean` is worth recording: that file proves the
`L²(boxL (ellH v μ))` version of the same statement under the *stronger* hypotheses
`AEStronglyMeasurable` + bounded + `HasCompactSupport`; here only `Integrable` is assumed and the
conclusion is the *uniform* one.  The single place where the extra hypotheses were used there is
the additivity `pinQBl ℓ (Wa + Wb) = pinQBl ℓ Wa + pinQBl ℓ Wb`, whose only analytic input is
`chat_add` — additive on integrable kernels — so `Integrable` suffices
(`k1ErrBaux_pinQBl_add` below).

**Import note.**  `k1ErrB` and every ingredient of the argument live in
`Submission.Work.BoseBoxFock.K1pairingDefs` (the vocabulary module `K1dirBDefs` only *re-exports*
it); this file imports that module directly, so it does not depend on the ongoing edits of the
`K1dirBDefs` chapter.

This file is complete: every declaration below is proved from the imported corpus lemmas.
-/

noncomputable section

open scoped BigOperators
open MeasureTheory

namespace Work.BoseBoxFock.K1dirB

open Work.BoseBoxFock

local notation "E3" => EuclideanSpace ℝ (Fin 3)

set_option maxHeartbeats 1000000
set_option linter.unusedVariables false

/-! ## 1. Summability of the `χ̂`-weighted lattice families -/

lemma k1ErrBaux_norm_ofReal_complex (r : ℝ) : ‖(r : ℂ)‖ = |r| := RCLike.norm_ofReal r

lemma k1ErrBaux_smul_kmomInt {ℓ : ℝ} (hℓ : ℓ ≠ 0) (n : Fin 3 → ℤ) :
    ℓ • kmomInt ℓ n = Work.BoseB4.vec n := by
  rw [kmomInt, smul_smul, mul_inv_cancel₀ hℓ, one_smul]

lemma k1ErrBaux_norm_exp_I_mul_ofReal (r : ℝ) :
    ‖Complex.exp (Complex.I * (r : ℂ))‖ = 1 := by
  rw [Complex.norm_exp]
  have h : (Complex.I * (r : ℂ)).re = 0 := by simp
  rw [h, Real.exp_zero]

/-- Multiplication by a unimodular phase preserves summability. -/
lemma k1ErrBaux_summable_mul_phase {f : (Fin 3 → ℤ) → ℂ} (hf : Summable f)
    {phase : (Fin 3 → ℤ) → ℂ} (hphase : ∀ n, ‖phase n‖ ≤ 1) :
    Summable (fun n => f n * phase n) := by
  refine Summable.of_norm_bounded hf.norm (fun n => ?_)
  rw [norm_mul]
  exact mul_le_of_le_one_right (norm_nonneg _) (hphase n)

/-- **Summability of the `χ̂`-weighted lattice family.**  For `ℓ > 0`, the family
`n ↦ Ŵ(kmomInt ℓ n)·χ̂(ℓ • kmomInt ℓ n)^k` (`k ≥ 1`) is summable, by the uniform `L¹` bound on
`Ŵ` and the order-`52` decay of `χ̂`. -/
lemma k1ErrBaux_summable_hatChi_core {ℓ : ℝ} (hℓ : 0 < ℓ) (W : E3 → ℝ) (k : ℕ) (hk : 1 ≤ k) :
    Summable (fun n : Fin 3 → ℤ =>
      ((Work.BoseFixR.chat W (kmomInt ℓ n) : ℝ) : ℂ)
        * (((Work.BoseK15.corpusBox.hatChi (ℓ • kmomInt ℓ n) : ℝ) : ℂ)) ^ k) := by
  obtain ⟨B, hB0, hB⟩ := chat_abs_le_uniform (W := W)
  obtain ⟨C, hC0, hC⟩ := hatChi_decay_52
  have h52 : 2 ≤ 52 * k := by omega
  have hsumg : Summable (fun n : Fin 3 → ℤ =>
      (B * C ^ k) * ((1 + ‖Work.BoseB4.vec n‖ ^ 2) ^ (52 * k))⁻¹) :=
    (summable_vec_inv_one_add_norm_sq h52).mul_left (B * C ^ k)
  refine Summable.of_norm_bounded hsumg (fun n => ?_)
  rw [k1ErrBaux_smul_kmomInt (ne_of_gt hℓ) n, norm_mul, norm_pow,
    k1ErrBaux_norm_ofReal_complex, k1ErrBaux_norm_ofReal_complex]
  have h1 : |Work.BoseFixR.chat W (kmomInt ℓ n)|
        * |Work.BoseK15.corpusBox.hatChi (Work.BoseB4.vec n)| ^ k
      ≤ B * (C * ((1 + ‖Work.BoseB4.vec n‖ ^ 2) ^ 52)⁻¹) ^ k :=
    mul_le_mul (hB _) (pow_le_pow_left₀ (abs_nonneg _) (hC _) k)
      (pow_nonneg (abs_nonneg _) k) hB0
  refine le_trans h1 ?_
  have hEq : B * (C * ((1 + ‖Work.BoseB4.vec n‖ ^ 2) ^ 52)⁻¹) ^ k
      = B * C ^ k * ((1 + ‖Work.BoseB4.vec n‖ ^ 2) ^ (52 * k))⁻¹ := by
    rw [mul_pow, inv_pow, ← pow_mul, ← mul_assoc]
  exact le_of_eq hEq

/-- The `pinQBl` summand family of a kernel `W` is summable. -/
lemma k1ErrBaux_summable_bl {ℓ : ℝ} (hℓ : 0 < ℓ) (W : E3 → ℝ) (w : E3) :
    Summable (fun n : Fin 3 → ℤ =>
      ((Work.BoseFixR.chat W (kmomInt ℓ n) : ℝ) : ℂ)
        * ((Work.BoseK15.corpusBox.hatChi (ℓ • kmomInt ℓ n) : ℝ) : ℂ)
        * Complex.exp (Complex.I * ((inner ℝ (kmomInt ℓ n) w : ℝ) : ℂ))) := by
  have h := k1ErrBaux_summable_mul_phase (f := fun n : Fin 3 → ℤ =>
      ((Work.BoseFixR.chat W (kmomInt ℓ n) : ℝ) : ℂ)
        * (((Work.BoseK15.corpusBox.hatChi (ℓ • kmomInt ℓ n) : ℝ) : ℂ)) ^ 1)
    (k1ErrBaux_summable_hatChi_core hℓ W 1 le_rfl) (phase := fun n =>
      Complex.exp (Complex.I * ((inner ℝ (kmomInt ℓ n) w : ℝ) : ℂ)))
    (fun n => le_of_eq (k1ErrBaux_norm_exp_I_mul_ofReal _))
  simpa only [pow_one] using h

/-- `chat` is additive in its kernel, in the `W + U` spelling. -/
lemma k1ErrBaux_chat_add {W U : E3 → ℝ} (hW : MeasureTheory.Integrable W)
    (hU : MeasureTheory.Integrable U) (k : E3) :
    Work.BoseFixR.chat (W + U) k = Work.BoseFixR.chat W k + Work.BoseFixR.chat U k := by
  rw [show (W + U) = fun x => W x + U x from funext fun x => rfl]
  exact Work.BoseRowsFS.CoulBilin.chat_add hW hU k

/-- **Additivity of the first `χ̂`-lattice sum in the weight.**  For `ℓ > 0` and *integrable*
`Wa`, `Wb` (only additivity of `chat` is needed). -/
lemma k1ErrBaux_pinQBl_add {ℓ : ℝ} (hℓ : 0 < ℓ) {Wa Wb : E3 → ℝ}
    (hIa : MeasureTheory.Integrable Wa) (hIb : MeasureTheory.Integrable Wb) (w : E3) :
    pinQBl ℓ (Wa + Wb) w = pinQBl ℓ Wa w + pinQBl ℓ Wb w := by
  have hsumA := k1ErrBaux_summable_bl hℓ Wa w
  have hsumB := k1ErrBaux_summable_bl hℓ Wb w
  have hpt : ∀ n : Fin 3 → ℤ,
      ((Work.BoseFixR.chat (Wa + Wb) (kmomInt ℓ n) : ℝ) : ℂ)
        * ((Work.BoseK15.corpusBox.hatChi (ℓ • kmomInt ℓ n) : ℝ) : ℂ)
        * Complex.exp (Complex.I * ((inner ℝ (kmomInt ℓ n) w : ℝ) : ℂ))
      = (((Work.BoseFixR.chat Wa (kmomInt ℓ n) : ℝ) : ℂ)
          * ((Work.BoseK15.corpusBox.hatChi (ℓ • kmomInt ℓ n) : ℝ) : ℂ)
          * Complex.exp (Complex.I * ((inner ℝ (kmomInt ℓ n) w : ℝ) : ℂ)))
        + (((Work.BoseFixR.chat Wb (kmomInt ℓ n) : ℝ) : ℂ)
          * ((Work.BoseK15.corpusBox.hatChi (ℓ • kmomInt ℓ n) : ℝ) : ℂ)
          * Complex.exp (Complex.I * ((inner ℝ (kmomInt ℓ n) w : ℝ) : ℂ))) := by
    intro n
    rw [k1ErrBaux_chat_add hIa hIb (kmomInt ℓ n)]
    push_cast
    ring
  rw [pinQBl]
  rw [show (fun n : Fin 3 → ℤ =>
        ((Work.BoseFixR.chat (Wa + Wb) (kmomInt ℓ n) : ℝ) : ℂ)
          * ((Work.BoseK15.corpusBox.hatChi (ℓ • kmomInt ℓ n) : ℝ) : ℂ)
          * Complex.exp (Complex.I * ((inner ℝ (kmomInt ℓ n) w : ℝ) : ℂ)))
      = fun n : Fin 3 → ℤ =>
        (((Work.BoseFixR.chat Wa (kmomInt ℓ n) : ℝ) : ℂ)
            * ((Work.BoseK15.corpusBox.hatChi (ℓ • kmomInt ℓ n) : ℝ) : ℂ)
            * Complex.exp (Complex.I * ((inner ℝ (kmomInt ℓ n) w : ℝ) : ℂ)))
          + (((Work.BoseFixR.chat Wb (kmomInt ℓ n) : ℝ) : ℂ)
            * ((Work.BoseK15.corpusBox.hatChi (ℓ • kmomInt ℓ n) : ℝ) : ℂ)
            * Complex.exp (Complex.I * ((inner ℝ (kmomInt ℓ n) w : ℝ) : ℂ))) from
      funext hpt]
  rw [Summable.tsum_add hsumA hsumB]
  rfl

/-- The limit row `pinQBl` is *definitionally* the limit lattice row of the `χ̂`-weight. -/
lemma k1ErrBaux_pinQBl_eq_k1RowLim (ℓ : ℝ) (W : E3 → ℝ) (w : E3) :
    pinQBl ℓ W w = k1RowLim ℓ (k1ChiHatWt ℓ W) w := rfl

/-! ## 2. The lattice tails are uniformly small -/

lemma k1ErrBaux_summable_trunc_norm {F : (Fin 3 → ℤ) → ℂ} {C : ℝ} (hC0 : 0 ≤ C)
    (hC : ∀ n : Fin 3 → ℤ, ‖F n‖ ≤ C * ((1 + ‖Work.BoseB4.vec n‖ ^ 2) ^ 52)⁻¹) (ρ : ℝ) :
    Summable (fun n : Fin 3 → ℤ => if ρ ≤ ‖latVec n‖ then ‖F n‖ else 0) := by
  refine Summable.of_nonneg_of_le (fun n => ?_) (fun n => ?_)
    ((summable_vec_inv_one_add_norm_sq (k := 52) (by norm_num)).mul_left C)
  · split <;> positivity
  · split
    · exact hC n
    · exact mul_nonneg hC0 (by positivity)

/-- The cut row converges to the limit row, uniformly in the position variable. -/
lemma k1ErrBaux_rowCut_sub_lim_uniform {ℓ : ℝ} (hℓ : 0 < ℓ) (fu : Work.BoseBoxFix.LowCut)
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
      (k1ErrBaux_summable_trunc_norm hC0 hC ((N' : ℝ) / 4))
      (k1ErrBaux_summable_trunc_norm hC0 hC ((M : ℝ)))
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
lemma k1ErrBaux_pairRow_uniform {ℓ : ℝ} (hℓ : 0 < ℓ) (fu : Work.BoseBoxFix.LowCut)
    {Fa Fb : (Fin 3 → ℤ) → ℂ}
    (hFa : ∃ C : ℝ, 0 ≤ C ∧ ∀ n : Fin 3 → ℤ,
      ‖Fa n‖ ≤ C * ((1 + ‖Work.BoseB4.vec n‖ ^ 2) ^ 52)⁻¹)
    (hFb : ∃ C : ℝ, 0 ≤ C ∧ ∀ n : Fin 3 → ℤ,
      ‖Fb n‖ ≤ C * ((1 + ‖Work.BoseB4.vec n‖ ^ 2) ^ 52)⁻¹) :
    ∀ ε : ℝ, 0 < ε → ∃ N : ℕ, ∀ N' : ℕ, N ≤ N' → ∀ z : E3,
      ‖(k1RowCut ℓ fu N' Fa z + k1Row ℓ N' Fb z)
        - (k1RowLim ℓ Fa z + k1RowLim ℓ Fb z)‖ ≤ ε := by
  intro ε hε
  obtain ⟨Na, ha⟩ := k1ErrBaux_rowCut_sub_lim_uniform hℓ fu hFa (ε / 2) (by linarith)
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

/-! ## 3. The error as a pair of lattice rows -/

/-- **The first `χ̂`-row error is a pair of lattice rows.**  With `ℓ = ellH v μ`,
`k1ErrB v μ fu N Wa Wb w` is the difference of the truncated pair row and the limit pair row of
the weights `k1ChiHatWt ℓ Wa` (cut) and `k1ChiHatWt ℓ Wb` (un-cut). -/
lemma k1ErrB_eq_rowDiff {v : E3 → ℝ} {μ : ℝ} (fu : Work.BoseBoxFix.LowCut) {Wa Wb : E3 → ℝ}
    (hIa : MeasureTheory.Integrable Wa) (hIb : MeasureTheory.Integrable Wb) (N : ℕ) (w : E3) :
    k1ErrB v μ fu N Wa Wb w
      = (k1RowCut (ellH v μ) fu N (k1ChiHatWt (ellH v μ) Wa) w
          + k1Row (ellH v μ) N (k1ChiHatWt (ellH v μ) Wb) w)
        - (k1RowLim (ellH v μ) (k1ChiHatWt (ellH v μ) Wa) w
          + k1RowLim (ellH v μ) (k1ChiHatWt (ellH v μ) Wb) w) := by
  unfold k1ErrB
  rw [k1pinQB_split fu N w,
    k1ErrBaux_pinQBl_add (ellH_pos v μ) hIa hIb w,
    k1ErrBaux_pinQBl_eq_k1RowLim, k1ErrBaux_pinQBl_eq_k1RowLim]

/-! ## 4. The target -/

theorem k1ErrB_tendsto {v : EuclideanSpace ℝ (Fin 3) → ℝ} {μ : ℝ} (fu : Work.BoseBoxFix.LowCut)
    {Wa Wb : EuclideanSpace ℝ (Fin 3) → ℝ} (hWai : MeasureTheory.Integrable Wa)
    (hWbi : MeasureTheory.Integrable Wb) :
    ∀ ε : ℝ, 0 < ε → ∃ N₀ : ℕ, ∀ N : ℕ, N₀ ≤ N → ∀ w : EuclideanSpace ℝ (Fin 3),
      ‖Work.BoseBoxFock.k1ErrB v μ fu N Wa Wb w‖ ≤ ε := by
  intro ε hε
  have hℓ : 0 < ellH v μ := ellH_pos v μ
  obtain ⟨N, hN⟩ := k1ErrBaux_pairRow_uniform hℓ fu (k1ChiHatWt_majorant hℓ Wa)
    (k1ChiHatWt_majorant hℓ Wb) ε hε
  refine ⟨N, fun N' hN' w => ?_⟩
  rw [k1ErrB_eq_rowDiff fu hWai hWbi N' w]
  exact hN N' hN' w

end Work.BoseBoxFock.K1dirB
