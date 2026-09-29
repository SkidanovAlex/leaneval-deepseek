import Mathlib
import Submission.Work.TMC16Core.Defs
import Submission.Work.TMC16Core.Basic.nnDist
import Submission.Work.TMC16Core.Basic.rational_block_prod
import Submission.Work.TMC16Core.Trig.sin_prod_classic
import Submission.Work.TMC16Core.Trig.sum_emod_coprime
import Submission.Work.TMC16Core.Trig.nn_mul_div_emod
import Submission.Work.TMC16Core.Trig.rat_prod_erase_le
import Submission.Work.TMC16Core.Trig.rat_prod_min_removed_v2

set_option linter.unusedVariables false

namespace Work.TMC16Core.Trig

open Finset
open Work.TMC16Core.Basic

/-- **Non-degenerate sharp bound.**  If the removed factor `S (2x + j₁ p/L)` is nonzero, the
product of the remaining `2 |sin (π (2x + k p/L))|` factors is at most `L`.

This is the `2^{L-1}`-multiple of `Trig/rat_prod_erase_le.erase_prod_le_of_pos`, which gives the
corresponding product of `|sin|` factors as at most `L / 2^{L-1}`. -/
lemma rat_prod_erase_sharp_of_pos {L : ℕ} (hL : 0 < L) {p : ℤ}
    (hcop : Nat.Coprime p.natAbs L) (x : ℝ) {j₁ : ℕ} (hj₁ : j₁ ∈ Finset.Icc 1 L)
    (hpos : 0 < S (2 * x + (j₁ : ℝ) * ((p : ℝ) / (L : ℝ)))) :
    ∏ j ∈ (Finset.Icc 1 L).erase j₁,
        (2 * |Real.sin (Real.pi * (2 * x + (j : ℝ) * ((p : ℝ) / (L : ℝ))))|) ≤ (L : ℝ) := by
  have hterm : ∀ k : ℕ,
      |Real.sin (2 * Real.pi * (x + (k : ℝ) * ((p : ℝ) / (2 * (L : ℝ)))))| =
        S (2 * x + (k : ℝ) * ((p : ℝ) / (L : ℝ))) := by
    intro k
    unfold S
    congr 1
    field_simp
  have hE := erase_prod_le_of_pos (q := L) hL hcop x hj₁ hpos
  have hcard : ((Finset.Icc 1 L).erase j₁).card = L - 1 := by
    rw [Finset.card_erase_of_mem hj₁, Nat.card_Icc]
    omega
  have hsplit : ∏ j ∈ (Finset.Icc 1 L).erase j₁,
        (2 * |Real.sin (Real.pi * (2 * x + (j : ℝ) * ((p : ℝ) / (L : ℝ))))|)
      = (2 : ℝ) ^ (L - 1) * ∏ j ∈ (Finset.Icc 1 L).erase j₁,
        S (2 * x + (j : ℝ) * ((p : ℝ) / (L : ℝ))) := by
    rw [show (∏ j ∈ (Finset.Icc 1 L).erase j₁,
        (2 * |Real.sin (Real.pi * (2 * x + (j : ℝ) * ((p : ℝ) / (L : ℝ))))|))
      = ∏ j ∈ (Finset.Icc 1 L).erase j₁,
        ((fun _ : ℕ => (2 : ℝ)) j * S (2 * x + (j : ℝ) * ((p : ℝ) / (L : ℝ)))) from
        Finset.prod_congr rfl (fun j _ => rfl)]
    rw [Finset.prod_mul_distrib, Finset.prod_const, hcard]
  rw [hsplit]
  calc (2 : ℝ) ^ (L - 1) * ∏ j ∈ (Finset.Icc 1 L).erase j₁,
        S (2 * x + (j : ℝ) * ((p : ℝ) / (L : ℝ)))
      = (2 : ℝ) ^ (L - 1) * ∏ j ∈ (Finset.Icc 1 L).erase j₁,
          |Real.sin (2 * Real.pi * (x + (j : ℝ) * ((p : ℝ) / (2 * (L : ℝ)))))| := by
        congr 1
        exact Finset.prod_congr rfl (fun k _ => (hterm k).symm)
    _ ≤ (2 : ℝ) ^ (L - 1) * ((L : ℝ) / (2 : ℝ) ^ (L - 1)) :=
        mul_le_mul_of_nonneg_left hE (by positivity)
    _ = (L : ℝ) := by
        have h2 : (2 : ℝ) ^ (L - 1) ≠ 0 := pow_ne_zero _ (by norm_num)
        field_simp

/-- **The rational block product with the minimal factor removed: sharp upper bound.**
For `p` coprime to `L ≥ 1`, real `x` and `j₁ ∈ {1,…,L}` a minimiser of `j ↦ nn (2x + j·p/L)`,
the product of the remaining `2 |sin (π (2x + j·p/L))|` is at most `L`.

The clean route (already available in this workspace): `Basic.rational_block_prod` gives
`∏_{k=1}^{L} |sin (π (2x + k p/L))| = |sin (2π L x)| · 2 / 2^L`, so (in the non-degenerate case
`0 < |sin (π(2x + j₁ p/L))|`)
`∏_{k≠j₁} 2|sin (π(2x + k p/L))| = |sin (2π L x)| / |sin (π (2x + j₁ p/L))|`, and the Dirichlet
bound `|sin (n t)| ≤ n |sin t|` with `n = L`, `t = π(2x + j₁ p/L)` bounds this by `L`.
(The sharper existing lemma `Trig/rat_prod_erase_le.erase_prod_le_of_pos` states exactly
`∏_{k≠j₁} |sin| ≤ L / 2^{L-1}` under the hypothesis that the removed factor is nonzero — multiply
by `2^{L-1}`.)
In the degenerate case `|sin (π(2x + j₁ p/L))| = 0` one has `2x ≡ -j₁ p/L`, so
`nn (2x + j p/L) = nn ((j - j₁) p / L)` with `j ↦ (j - j₁)·p mod L` a bijection
`{1,…,L}\{j₁} → {1,…,L-1}` (see `Trig/sum_emod_coprime`, `Trig/nn_mul_div_emod`), and the
classical identity `Trig/sin_prod_classic`: `∏_{k=1}^{L-1} sin (π k/L) = L / 2^{L-1}`, giving the
product exactly `L`.  (A alternative closure argument: the product is continuous in `x`, the sharp
bound holds on the dense non-degenerate locus, hence everywhere.) -/
theorem rat_prod_erase_sharp {L : ℕ} (hL : 0 < L) {p : ℤ} (hcop : Nat.Coprime p.natAbs L)
    (x : ℝ) {j₁ : ℕ} (hj₁ : j₁ ∈ Finset.Icc 1 L)
    (hmin : ∀ j ∈ Finset.Icc 1 L,
      Work.TMC16Core.Basic.nn (2 * x + (j : ℝ) * ((p : ℝ) / (L : ℝ))) ≥
        Work.TMC16Core.Basic.nn (2 * x + (j₁ : ℝ) * ((p : ℝ) / (L : ℝ)))) :
    ∏ j ∈ (Finset.Icc 1 L).erase j₁,
        (2 * |Real.sin (Real.pi * (2 * x + (j : ℝ) * ((p : ℝ) / (L : ℝ))))|) ≤ (L : ℝ) := by
  refine le_of_forall_pos_le_add (fun ε hε => ?_)
  have hcont : ContinuousAt (fun y : ℝ => ∏ j ∈ (Finset.Icc 1 L).erase j₁,
      (2 * |Real.sin (Real.pi * (2 * y + (j : ℝ) * ((p : ℝ) / (L : ℝ))))|)) x := by
    apply Continuous.continuousAt
    apply continuous_finsetProd
    intro k hk
    fun_prop
  obtain ⟨δ, hδpos, hδ⟩ := Metric.continuousAt_iff.mp hcont ε hε
  obtain ⟨y, hyx, hybad⟩ := exists_nn_pos_shift ((j₁ : ℝ) * ((p : ℝ) / (L : ℝ))) x δ hδpos
  have hdist : dist y x < δ := by rw [Real.dist_eq]; exact hyx
  have hval := hδ hdist
  rw [Real.dist_eq] at hval
  have hspos : 0 < S (2 * y + (j₁ : ℝ) * ((p : ℝ) / (L : ℝ))) := S_pos_of_not_int _ hybad
  have hFy := rat_prod_erase_sharp_of_pos hL hcop y hj₁ hspos
  have hlt : (∏ j ∈ (Finset.Icc 1 L).erase j₁,
        (2 * |Real.sin (Real.pi * (2 * x + (j : ℝ) * ((p : ℝ) / (L : ℝ))))|))
      < (∏ j ∈ (Finset.Icc 1 L).erase j₁,
        (2 * |Real.sin (Real.pi * (2 * y + (j : ℝ) * ((p : ℝ) / (L : ℝ))))|)) + ε := by
    have h1 := (abs_lt.mp hval).1
    linarith
  linarith

end Work.TMC16Core.Trig
