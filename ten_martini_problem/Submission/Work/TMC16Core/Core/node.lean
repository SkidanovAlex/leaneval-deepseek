import Mathlib
import Submission.Work.TMC16Core.Defs
import Submission.Work.TMC16Core.Basic.lemma_9_3
import Submission.Work.TMC16Core.Basic.pd_cheb
import Submission.Work.TMC16Core.Basic.pd_fourier_large

namespace Work.TMC16Core.Core

open Work.TMC16Core

/-- **The nongenuine step (AJ Lemma 9.3) in the form needed for the localization estimate.**

Suppose a family of `K+1` phases `θ + (x + (K-1)/2)α` indexed by `x ∈ I₁ ∪ I₂` is
`ε₁`-uniform, all phases with `x ∈ I₁` lie in `A_{K,L-εA}`, and `ε₁ < εA` with the gap
condition of Lemma 9.3 holds.  Then some phase with `x ∈ I₂` is *not* in `A_{K,L-εA}`,
i.e. the continuant there is larger than `e^{(K+1)(L-εA)}`.  If in addition
`K·(23/32)L ≤ (K+1)(L-εA)` then the continuant is at least `e^{(23/32)LK}`.

The `A`-set is the set of phases `φ` with `‖P_K(φ)‖ ≤ e^{(K+1)(L-εA)}`; the input
`hA` is what the singularity of `0` produces (Lemma 9.2). -/
theorem node_of_uni {α lam L εA ε₁ : ℝ} {E : ℂ} {θ θ₀ : ℝ} {K : ℕ} {I₁ I₂ : Finset ℤ}
    (hε : ε₁ < εA)
    (hgap : 4 * ((K : ℝ) + 1) * Real.exp (L - εA) < Real.exp ((K : ℝ) * (εA - ε₁)))
    (huni : Uniform ε₁
      (fun j : {j : ℤ // j ∈ I₁ ∪ I₂} => θ + (((j : ℤ) : ℝ) + (((K : ℝ) - 1) / 2)) * α))
    (hcard : (I₁ ∪ I₂).card = K + 1)
    (hA : ∀ x ∈ I₁, ‖pd α lam (θ + (x : ℝ) * α) E (K + 1)‖ ≤
      Real.exp (((K : ℝ) + 1) * (L - εA)))
    (hthreshold : (K : ℝ) * ((23 / 32 : ℝ) * L) ≤ ((K : ℝ) + 1) * (L - εA))
    (hθ₀ : Real.exp ((K : ℝ) * L) / 4 ≤
      ‖pd α lam (θ₀ - (((K : ℝ) - 1) / 2) * α) E (K + 1)‖) :
    ∃ x₁ ∈ I₂, Real.exp ((23 / 32 : ℝ) * L * (K : ℝ)) ≤
      ‖pd α lam (θ + (x₁ : ℝ) * α) E (K + 1)‖ := by
  by_contra hcon
  push Not at hcon
  obtain ⟨Q, hQdeg, hQ⟩ := Work.TMC16Core.Basic.pd_cheb α lam E K
  have hAall : ∀ j : {j : ℤ // j ∈ I₁ ∪ I₂},
      θ + ((j : ℝ) + ((K : ℝ) - 1) / 2) * α ∈ AkSet α lam E K (L - εA) := by
    intro j
    rcases Finset.mem_union.mp j.2 with hj | hj
    · have h := hA j.val hj
      have heq : θ + ((j : ℝ) + ((K : ℝ) - 1) / 2) * α - (((K : ℝ) - 1) / 2) * α
          = θ + (j : ℝ) * α := by ring
      show ‖pd α lam (θ + ((j : ℝ) + ((K : ℝ) - 1) / 2) * α - (((K : ℝ) - 1) / 2) * α)
        E (K + 1)‖ ≤ Real.exp (((K : ℝ) + 1) * (L - εA))
      rw [heq]; exact h
    · have h := hcon j.val hj
      have heq : θ + ((j : ℝ) + ((K : ℝ) - 1) / 2) * α - (((K : ℝ) - 1) / 2) * α
          = θ + (j : ℝ) * α := by ring
      show ‖pd α lam (θ + ((j : ℝ) + ((K : ℝ) - 1) / 2) * α - (((K : ℝ) - 1) / 2) * α)
        E (K + 1)‖ ≤ Real.exp (((K : ℝ) + 1) * (L - εA))
      rw [heq]
      exact le_trans (le_of_lt h) (Real.exp_le_exp.mpr (by linarith [hthreshold]))
  have hnot := Work.TMC16Core.Basic.lemma_9_3 (α := α) (lam := lam) (E := E) (k := K) (L := L)
    (ε := εA) (ε₁ := ε₁) (Q := Q)
    (z := fun j : {j : ℤ // j ∈ I₁ ∪ I₂} =>
      θ + ((j : ℝ) + ((K : ℝ) - 1) / 2) * α)
    hQ hQdeg (by rw [Fintype.card_coe]; exact hcard) hAall θ₀ hθ₀ hε hgap
  exact hnot huni

end Work.TMC16Core.Core
