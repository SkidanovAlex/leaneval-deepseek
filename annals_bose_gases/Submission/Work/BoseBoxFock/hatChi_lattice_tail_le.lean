import Mathlib.Algebra.Order.Ring.Star
import Mathlib.Algebra.Order.Star.Real
import Mathlib.Analysis.Normed.Lp.MeasurableSpace
import Mathlib.MeasureTheory.Integral.Bochner.Basic
import Mathlib.MeasureTheory.Measure.Haar.OfBasis
import Submission.Work.BoseB7AK.W1rows.W1hat_abs_le
import Submission.Work.BoseBoxFock.lattice_cubeTail_le
import Submission.Work.BoseBoxFock.summable_vec_inv_one_add_norm_sq
import Submission.Work.BoseK15.ChiReg_corpus
-- PORT435-BEGIN (v4.35 isDefEq respectTransparency compat)
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- PORT435-END

/-!
# `Work.BoseBoxFock.hatChi_lattice_tail_le` — the cube-index lattice tail of `chat W · χ̂`

**Statement.**  For `ℓ > 0` and a bounded `W : ℝ³ → ℝ` vanishing outside the ball of radius `R`,

    ∀ ε > 0, ∃ N, ∀ N' ≥ N,
      Σ'_{n : ℤ³, ∃ i, N' < |n i|} |Ŵ(kmomInt ℓ n)| · |χ̂(ℓ • kmomInt ℓ n)| ≤ ε .

This is the `chat`-form companion of `Work.BoseBoxFock.latTail_cube_le` (which carries
`‖Ŵ(kmomInt ℓ n)‖²` instead): both are truncations of a *summable* lattice family by the
condition that the index leaves the cube `[-N',N']³`, the momentum form used in the §10
far-kernel chapter.

**Proof.**  The two factors are controlled by the two standard inputs:

* `Ŵ` is dominated by its `L¹` mass, uniformly in the momentum,
  `|Ŵ(k)| ≤ ∫|W|` (`Work.BoseB7AK.W1rows.abs_chat_le_integral_abs`, no integrability or
  measurability hypothesis needed), so `B := ∫|W|` is a nonnegative uniform bound for
  `|chat W ·|` (`chat_abs_le_uniform`);
* `χ̂` has order-`52` decay, `|χ̂(p)| ≤ C (1+‖p‖²)^{-52}` (`Work.BoseK15.ChiReg_corpus 52`,
  the corpus `lem:DecaychiHat`), and the lattice series `Σ_n (1+‖vec n‖²)^{-52}` converges
  (`Work.BoseBoxFock.summable_vec_inv_one_add_norm_sq` at `k = 52`; three-dimensionality).

Hence the summand is dominated by the summable majorant
`(B·C)·(1+‖vec n‖²)^{-52}`, and since `ℓ • kmomInt ℓ n = vec n` the abstract cube-tail lemma
`Work.BoseBoxFock.lattice_cubeTail_le` (complements of finite sets of a summable nonnegative
lattice family carry arbitrarily small sums) finishes the proof.

The hypotheses `hWb`, `hWs` are not needed for the argument — it works for every `W`, the
`L¹`-mass bound `∫|W|` always being available (the Bochner integral of a non-integrable function
being `0`) — but the statement is the requested one and they are kept.
-/

noncomputable section

open MeasureTheory

namespace Work.BoseBoxFock

local notation "E3" => EuclideanSpace ℝ (Fin 3)

set_option linter.unusedVariables false

/-- **The uniform `L¹` bound for the Fourier transform.**  `B := ∫|W| ≥ 0` dominates
`|chat W k|` for every momentum `k`. -/
lemma chat_abs_le_uniform {W : E3 → ℝ} :
    ∃ B : ℝ, 0 ≤ B ∧ ∀ k : E3, |Work.BoseFixR.chat W k| ≤ B :=
  ⟨∫ x : E3, |W x|,
    MeasureTheory.integral_nonneg (f := fun x : E3 => |W x|) (fun x => abs_nonneg (W x)),
    fun k => Work.BoseB7AK.W1rows.abs_chat_le_integral_abs k⟩

/-- **The order-`52` decay of the corpus bump `χ̂`**, in the "one over a power" normalisation
used by the lattice majorant: `|χ̂(p)| ≤ C·(1+‖p‖²)^{-52}` with `C ≥ 0`
(`Work.BoseK15.ChiReg_corpus 52`, the corpus `lem:DecaychiHat`). -/
lemma hatChi_decay_52 :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ p : E3,
      |Work.BoseK15.corpusBox.hatChi p| ≤ C * ((1 + ‖p‖ ^ 2) ^ 52)⁻¹ := by
  obtain ⟨C, hC0, hC⟩ := Work.BoseK15.ChiReg_corpus 52
  refine ⟨C, hC0, fun p => ?_⟩
  have hD : (0 : ℝ) < (1 + ‖p‖ ^ 2) ^ 52 := by positivity
  have h1 : |Work.BoseK15.corpusBox.hatChi p| * (1 + ‖p‖ ^ 2) ^ 52
      / (1 + ‖p‖ ^ 2) ^ 52 ≤ C / (1 + ‖p‖ ^ 2) ^ 52 :=
    (div_le_div_iff_of_pos_right hD).mpr (hC.1 p)
  rwa [mul_div_cancel_right₀ _ hD.ne', div_eq_mul_inv] at h1

theorem hatChi_lattice_tail_le {ℓ R : ℝ} (hℓ : 0 < ℓ) {W : EuclideanSpace ℝ (Fin 3) → ℝ}
    (hWb : ∃ C : ℝ, ∀ x, ‖W x‖ ≤ C) (hWs : ∀ x, R < ‖x‖ → W x = 0) :
    ∀ ε : ℝ, 0 < ε → ∃ N : ℕ, ∀ N' : ℕ, N ≤ N' →
      (∑' n : Fin 3 → ℤ, (if ∃ i : Fin 3, N' < |n i| then
        |Work.BoseFixR.chat W (Work.BoseBoxFock.kmomInt ℓ n)|
          * |Work.BoseK15.corpusBox.hatChi (ℓ • Work.BoseBoxFock.kmomInt ℓ n)| else 0)) ≤ ε := by
  -- the two uniform inputs: the `L¹` bound for `chat W`, the decay of `χ̂`
  obtain ⟨B, hB0, hB⟩ := chat_abs_le_uniform (W := W)
  obtain ⟨Cm, hCm0, hCm⟩ := hatChi_decay_52
  -- the summable majorant family
  set g : (Fin 3 → ℤ) → ℝ := fun n =>
    |Work.BoseFixR.chat W (kmomInt ℓ n)| * |Work.BoseK15.corpusBox.hatChi (Work.BoseB4.vec n)|
    with hgdef
  have hgnn : ∀ n : Fin 3 → ℤ, 0 ≤ g n := fun n => mul_nonneg (abs_nonneg _) (abs_nonneg _)
  have hsumm : Summable g := by
    refine Summable.of_nonneg_of_le hgnn (fun n => ?_)
      ((summable_vec_inv_one_add_norm_sq (k := 52) (by norm_num)).mul_left (B * Cm))
    have h1 : |Work.BoseFixR.chat W (kmomInt ℓ n)| ≤ B := hB _
    have h2 : |Work.BoseK15.corpusBox.hatChi (Work.BoseB4.vec n)|
        ≤ Cm * ((1 + ‖Work.BoseB4.vec n‖ ^ 2) ^ 52)⁻¹ := hCm _
    calc g n = |Work.BoseFixR.chat W (kmomInt ℓ n)|
          * |Work.BoseK15.corpusBox.hatChi (Work.BoseB4.vec n)| := rfl
      _ ≤ B * (Cm * ((1 + ‖Work.BoseB4.vec n‖ ^ 2) ^ 52)⁻¹) :=
          mul_le_mul h1 h2 (abs_nonneg _) hB0
      _ = B * Cm * ((1 + ‖Work.BoseB4.vec n‖ ^ 2) ^ 52)⁻¹ := by ring
  intro ε hε
  -- the abstract cube tail of the majorant
  obtain ⟨N, hN⟩ := lattice_cubeTail_le hgnn hsumm ε hε
  refine ⟨N, fun N' hNN' => ?_⟩
  -- `ℓ • kmomInt ℓ n = vec n`: the momentum argument of `χ̂` is the dual-lattice vector
  have hsmul : ∀ n : Fin 3 → ℤ, ℓ • kmomInt ℓ n = Work.BoseB4.vec n := by
    intro n
    rw [kmomInt, smul_smul, mul_inv_cancel₀ hℓ.ne', one_smul]
  simp only [hsmul]
  exact hN N' hNN'

end Work.BoseBoxFock
