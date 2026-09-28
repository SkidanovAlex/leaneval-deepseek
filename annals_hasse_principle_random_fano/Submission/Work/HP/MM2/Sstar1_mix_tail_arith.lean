import Mathlib
import Submission.Work.HP.MM2.Defs
import Submission.Work.HP.bigW_le_pow
import Submission.Work.HP.eNorm_veronese_bounds
import Submission.Work.HP.Lat.card_Mon
import Submission.Work.HP.six_le_NN
import Submission.Work.HP.w_arith
import Submission.Work.HP.MM2.Sstar1_mix_tail_arith_aux
import Submission.Work.HP.MM2.mix_tail_arith_final

/-!
# `Sstar1_mix_tail_arith`: the two large-`B` arithmetic inequalities

We must exhibit `B₀` so that, for all `B ≥ B₀`, all `A` with `B^{5/6} ≤ A ≤ B²` and all
`x` with `‖x‖ ≤ B^{1/(n+1-d)}`,

`K (1+log A)^3 log B · W(wOf B) ≤ A^{(N-2)/4}`  and
`K (1+log A)^2 log B · W(wOf B) · ‖ν(x)‖ ≤ A^{N-2}`,  `N = N_{d,n}`.

Both are proved by the sibling lemma `Work.HP.MM2.mix_tail_arith_final`, which states exactly
this conjunction, with the `x`-quantifier extracted from inside the conjunction (legitimate
because the first inequality does not involve `x`).  Its single extra hypothesis
`2d + 1 ≤ N_{d,n}` is supplied here by `Work.HP.MM2.two_mul_add_two_le_NN`
(`N_{d,n} ≥ 2n + 2 ≥ 2d + 2`).

The hypotheses `hd : 2 ≤ d`, `hdn : d ≤ n` and `h22 : (d,n) ≠ (2,2)` are those of the parent
statement; `h22` is not needed by the arithmetic.
-/

namespace Work.HP.MM2

theorem Sstar1_mix_tail_arith (d n : ℕ) [DecidableEq (Work.HP.Mon d n)] (hd : 2 ≤ d) (hdn : d ≤ n)
    (h22 : (d, n) ≠ (2, 2)) (K : ℝ) (hK : 0 < K) :
    ∃ B₀ : ℝ, ∀ B : ℝ, B₀ ≤ B → ∀ A : ℝ, B ^ ((5 : ℝ) / 6) ≤ A → A ≤ B ^ 2 →
      ∀ x : Fin (n + 1) → ℤ, Work.HP.eNorm x ≤ B ^ (1 / ((n : ℝ) + 1 - d)) →
      K * (1 + Real.log A) ^ 3 * Real.log B * (Work.HP.bigW (Work.HP.wOf B) : ℝ)
          ≤ A ^ (((Work.HP.NN d n - 2 : ℕ) : ℝ) / 4) ∧
      K * (1 + Real.log A) ^ 2 * Real.log B * (Work.HP.bigW (Work.HP.wOf B) : ℝ) *
          Work.HP.eNorm (Work.HP.veronese d n x)
          ≤ A ^ (Work.HP.NN d n - 2) := by
  -- The exponent hypothesis of `mix_tail_arith_final`: `2d + 1 ≤ N_{d,n}`.
  have hN : 2 * d + 1 ≤ Work.HP.NN d n := by
    have h := two_mul_add_two_le_NN d n hd hdn
    omega
  obtain ⟨B₀, hB₀⟩ := mix_tail_arith_final d n hd hdn K hK hN
  refine ⟨B₀, fun B hB A hA1 hA2 x hx => ⟨?_, ?_⟩⟩
  · exact (hB₀ B hB A hA1 hA2).1
  · exact (hB₀ B hB A hA1 hA2).2 x hx

end Work.HP.MM2
