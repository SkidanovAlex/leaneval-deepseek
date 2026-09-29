import Mathlib
import Submission.Work.TMC16Core.Core.site
import Submission.Work.TMC16Core.Core.node

namespace Work.TMC16Core.Core

open Work.TMC16Core

/-- **The single-site step with a free decay rate `c`** (the variant of `Core.site_step_gen`
needed by the balanced assembly, cf. `NOTES_remaining_gap.md` §7).

Let `I₁ ∪ I₂` be a family of `K+1` sites whose phases are `ε₁`-uniform, suppose the
continuants at the sites of `I₁` are bounded by `e^{(K+1)(L-εA)}` and that the gap condition
of AJ Lemma 9.3 holds.  If the free rate `c` satisfies `K c ≤ (K+1)(L-εA)`, then some site
`x₁ ∈ I₂` has `‖P_K(θ + x₁ α)‖ ≥ e^{cK}`.

The proof is the non-generation argument of AJ Lemma 9.3: if every site of `I₂` also had
continuant `≤ e^{(K+1)(L-εA)}`, then all the `K+1` phases of `I₁ ∪ I₂` would lie in the
`A`-set, contradicting uniformity — because `Q_K` is too large (`≥ e^{KL}/4`) somewhere
(`pd_fourier_large`).  The threshold `23/32 L` of `Core.site_step_gen` is thus replaced by
the arbitrary level `(K+1)(L-εA)`, which is what frees `c`. -/
theorem site_step_gen_c {α lam L εA ε₁ c : ℝ} {E : ℂ} {θ : ℝ} {K : ℕ}
    {I₁ I₂ : Finset ℤ}
    (hlam : 0 < lam) (hLlog : L = Real.log lam)
    (hε₁ : 0 < ε₁) (hδlt : ε₁ < εA) (hεA : 0 < εA)
    (hgap : 4 * ((K : ℝ) + 1) * Real.exp (L - εA) < Real.exp ((K : ℝ) * (εA - ε₁)))
    (hthr : (K : ℝ) * c ≤ ((K : ℝ) + 1) * (L - εA))
    (hcard : (I₁ ∪ I₂).card = K + 1)
    (huni : Work.TMC16Core.Uniform ε₁
      (fun j : {j : ℤ // j ∈ I₁ ∪ I₂} =>
        θ + (((j : ℤ) : ℝ) + (((K : ℝ) - 1) / 2)) * α))
    (hA : ∀ x ∈ I₁, ‖Work.TMC16Core.pd α lam (θ + (x : ℝ) * α) E (K + 1)‖ ≤
      Real.exp (((K : ℝ) + 1) * (L - εA))) :
    ∃ x₁ ∈ I₂,
      Real.exp (c * (K : ℝ)) ≤ ‖Work.TMC16Core.pd α lam (θ + (x₁ : ℝ) * α) E (K + 1)‖ := by
  -- Suppose every site of `I₂` also lies in the `A`-set.
  by_contra hcon
  push Not at hcon
  -- The polynomial `Q_K` of Chebyshev type: `Q_K(cos 2πx) = pd (x - (K-1)α/2)`.
  obtain ⟨Q, hQdeg, hQ⟩ := Work.TMC16Core.Basic.pd_cheb α lam E K
  -- A point where `Q_K` is as large as `e^{KL}/4`.
  obtain ⟨θ₁, hθ₁⟩ := (Work.TMC16Core.Basic.pd_fourier_large α lam E K).2
  have hθ₀ : Real.exp ((K : ℝ) * L) / 4 ≤
      ‖pd α lam (θ₁ + (((K : ℝ) - 1) / 2) * α - (((K : ℝ) - 1) / 2) * α) E (K + 1)‖ := by
    have hEq : θ₁ + (((K : ℝ) - 1) / 2) * α - (((K : ℝ) - 1) / 2) * α = θ₁ := by ring
    rw [hEq]
    have hpow : |lam| ^ K = Real.exp ((K : ℝ) * L) := by
      rw [abs_of_pos hlam, ← Real.exp_log hlam, Real.exp_nat_mul, hLlog]
    rw [← hpow]
    linarith [Real.exp_pos ((K : ℝ) * L)]
  -- Every phase of the family lies in `A_{K,L-εA}`.
  have hAall : ∀ j : {j : ℤ // j ∈ I₁ ∪ I₂},
      θ + (((j : ℤ) : ℝ) + (((K : ℝ) - 1) / 2)) * α ∈ AkSet α lam E K (L - εA) := by
    intro j
    rcases Finset.mem_union.mp j.2 with hj | hj
    · have h := hA j.val hj
      have heq : θ + (((j : ℤ) : ℝ) + (((K : ℝ) - 1) / 2)) * α - (((K : ℝ) - 1) / 2) * α
          = θ + ((j : ℤ) : ℝ) * α := by ring
      show ‖pd α lam (θ + (((j : ℤ) : ℝ) + (((K : ℝ) - 1) / 2)) * α
          - (((K : ℝ) - 1) / 2) * α) E (K + 1)‖ ≤ Real.exp (((K : ℝ) + 1) * (L - εA))
      rw [heq]; exact h
    · have h := hcon j.val hj
      have heq : θ + (((j : ℤ) : ℝ) + (((K : ℝ) - 1) / 2)) * α - (((K : ℝ) - 1) / 2) * α
          = θ + ((j : ℤ) : ℝ) * α := by ring
      show ‖pd α lam (θ + (((j : ℤ) : ℝ) + (((K : ℝ) - 1) / 2)) * α
          - (((K : ℝ) - 1) / 2) * α) E (K + 1)‖ ≤ Real.exp (((K : ℝ) + 1) * (L - εA))
      rw [heq]
      exact le_trans (le_of_lt h) (Real.exp_le_exp.mpr (by linarith [hthr]))
  -- AJ Lemma 9.3 rules out the uniformity of such a family.
  exact Work.TMC16Core.Basic.lemma_9_3 hQ hQdeg (by rw [Fintype.card_coe]; exact hcard)
    hAall (θ₁ + (((K : ℝ) - 1) / 2) * α) hθ₀ hδlt hgap huni

end Work.TMC16Core.Core
