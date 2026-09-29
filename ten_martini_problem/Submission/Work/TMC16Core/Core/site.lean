import Mathlib
import Submission.Work.TMC16Core.Defs
import Submission.Work.TMC16Core.Basic.pd_fourier_large
import Submission.Work.TMC16Core.Core.windows
import Submission.Work.TMC16Core.Core.ablock
import Submission.Work.TMC16Core.Core.node

/-!
# The single-site localization step (AJ §9)

Given a scale `K ≥ 240`, a site `y` whose balanced window is disjoint from the `A`-window,
the singularity of `0` at rate `L/2`, and the `ε₁`-uniformity of the `K+1` phases
`θ + (x + (K-1)/2)α` for `x ∈ I₁ ∪ I₂`, the continuant is at least `exp((23/32)LK)` at some
site of the balanced window.

This is the assembly of three ingredients: the `A`-window bound (`Ablock_of_sing`, AJ Lemma
9.2), the non-generation lemma (`node_of_uni`, AJ Lemma 9.3) and the Fourier lower bound
`max_θ ‖P_K(θ)‖ ≥ λ^K` (`pd_fourier_large`, from `P_BJ`).
-/

noncomputable section

namespace Work.TMC16Core.Core

open Work.TMC16Core

theorem site_step {α lam L εA ε₁ : ℝ} {E : ℂ} {θ : ℝ} {y : ℤ} {K : ℕ}
    (hlam : 0 < lam) (hLlog : L = Real.log lam) (hL : 0 < L)
    (hε₁ : 0 < ε₁) (hK : 240 ≤ K)
    (hεA : εA ≤ (L / 2) * (3 / 16) - ε₁)
    (hεA' : 0 < εA)
    (hδlt : ε₁ < εA)
    (hgap : 4 * ((K : ℝ) + 1) * Real.exp (L - εA) < Real.exp ((K : ℝ) * (εA - ε₁)))
    (hthr : (K : ℝ) * ((23 / 32 : ℝ) * L) ≤ ((K : ℝ) + 1) * (L - εA))
    (hbd : ∀ n : ℕ, n ≤ K → ∀ ζ : ℝ,
      ‖pd α lam ζ E (n + 1)‖ ≤ Real.exp ((n : ℝ) * (L + ε₁)))
    (hs : IsSingular α lam θ E (L - L / 2) K 0)
    (hdj : -b1316 K + n1 K - 1 < y - b7 K + 3)
    (huni : Uniform ε₁
      (fun j : {j : ℤ // j ∈ I1set K ∪ I2set y K} =>
        θ + (((j : ℤ) : ℝ) + (((K : ℝ) - 1) / 2)) * α)) :
    ∃ x₁ ∈ I2set y K,
      3 * (K : ℤ) ≤ 10 * (y - x₁) ∧ 10 * (y - x₁) ≤ 7 * (K : ℤ) ∧
        (K : ℤ) ≤ 40 * ((x₁ + (K : ℤ) - 1) - y) ∧
        Real.exp ((23 / 32 : ℝ) * L * (K : ℝ)) ≤
          ‖pd α lam (θ + (x₁ : ℝ) * α) E (K + 1)‖ := by
  -- the `A`-window bound
  have hA : ∀ x ∈ I1set K,
      ‖pd α lam (θ + (x : ℝ) * α) E (K + 1)‖ ≤
        Real.exp (((K : ℝ) + 1) * (L - εA)) := by
    intro x hx
    refine le_trans (Ablock_of_sing hL hε₁ hK hbd hs x hx) ?_
    apply Real.exp_le_exp.mpr
    have hK0 : (0:ℝ) ≤ (K:ℝ) := by positivity
    nlinarith [hεA, hK0]
  -- the Fourier point
  obtain ⟨θ₁, hθ₁⟩ := (Work.TMC16Core.Basic.pd_fourier_large α lam (E : ℂ) K).2
  have hθ₀ : Real.exp ((K : ℝ) * L) / 4 ≤
      ‖pd α lam (θ₁ + ((K : ℝ) - 1) / 2 * α - (((K : ℝ) - 1) / 2) * α) E (K + 1)‖ := by
    have hEq : θ₁ + ((K : ℝ) - 1) / 2 * α - (((K : ℝ) - 1) / 2) * α = θ₁ := by ring
    rw [hEq]
    have hpow : |lam| ^ K = Real.exp ((K : ℝ) * L) := by
      rw [abs_of_pos hlam, ← Real.exp_log hlam, Real.exp_nat_mul, hLlog]
    rw [← hpow]
    linarith [Real.exp_pos ((K : ℝ) * L)]
  -- the non-generation step
  have hcard : (I1set K ∪ I2set y K).card = K + 1 := card_union_I1_I2 hK hdj
  obtain ⟨x₁, hx₁, hbig⟩ := node_of_uni (α := α) (lam := lam) (L := L) (εA := εA)
    (ε₁ := ε₁) (E := E) (θ := θ) (K := K) (I₁ := I1set K) (I₂ := I2set y K)
    hδlt hgap huni hcard hA hthr hθ₀
  refine ⟨x₁, hx₁, ?_, ?_, ?_, hbig⟩
  · exact (I2set_balanced hx₁).1
  · exact (I2set_balanced hx₁).2.1
  · exact (I2set_balanced hx₁).2.2

/-- **The single-site step, with the `A`-window bound as a hypothesis.**  Given the `ε₁`-uniformity
of the `K+1` phases of `I₁ ∪ I₂`, an upper bound `e^{(K+1)(L-εA)}` for the continuants at the
sites of `I₁` and the geometry (`I₂ ⊆ I2set y K`), some site of `I₂` satisfies the balanced
conditions of `pd_window` and the exponential lower bound.  The two cases of AJ §9 differ only in
the source of the `A`-bound: the singularity of `0` (Lemma 9.2) or the eigenfunction decay
(Lemma 9.11). -/
theorem site_step_gen {α lam L εA ε₁ : ℝ} {E : ℂ} {θ : ℝ} {K : ℕ} {I₁ I₂ : Finset ℤ} {y : ℤ}
    (hlam : 0 < lam) (hLlog : L = Real.log lam)
    (hε₁ : 0 < ε₁) (hδlt : ε₁ < εA) (hεA : 0 < εA)
    (hgap : 4 * ((K : ℝ) + 1) * Real.exp (L - εA) < Real.exp ((K : ℝ) * (εA - ε₁)))
    (hthr : (K : ℝ) * ((23 / 32 : ℝ) * L) ≤ ((K : ℝ) + 1) * (L - εA))
    (hcard : (I₁ ∪ I₂).card = K + 1)
    (huni : Uniform ε₁
      (fun j : {j : ℤ // j ∈ I₁ ∪ I₂} =>
        θ + (((j : ℤ) : ℝ) + (((K : ℝ) - 1) / 2)) * α))
    (hA : ∀ x ∈ I₁, ‖pd α lam (θ + (x : ℝ) * α) E (K + 1)‖ ≤
      Real.exp (((K : ℝ) + 1) * (L - εA)))
    (hI2 : I₂ ⊆ I2set y K) :
    ∃ x₁ ∈ I₂,
      3 * (K : ℤ) ≤ 10 * (y - x₁) ∧ 10 * (y - x₁) ≤ 7 * (K : ℤ) ∧
        (K : ℤ) ≤ 40 * ((x₁ + (K : ℤ) - 1) - y) ∧
        Real.exp ((23 / 32 : ℝ) * L * (K : ℝ)) ≤
          ‖pd α lam (θ + (x₁ : ℝ) * α) E (K + 1)‖ := by
  obtain ⟨θ₁, hθ₁⟩ := (Work.TMC16Core.Basic.pd_fourier_large α lam (E : ℂ) K).2
  have hθ₀ : Real.exp ((K : ℝ) * L) / 4 ≤
      ‖pd α lam (θ₁ + (((K : ℝ) - 1) / 2) * α - (((K : ℝ) - 1) / 2) * α) E (K + 1)‖ := by
    have hEq : θ₁ + (((K : ℝ) - 1) / 2) * α - (((K : ℝ) - 1) / 2) * α = θ₁ := by ring
    rw [hEq]
    have hpow : |lam| ^ K = Real.exp ((K : ℝ) * L) := by
      rw [abs_of_pos hlam, ← Real.exp_log hlam, Real.exp_nat_mul, hLlog]
    rw [← hpow]
    linarith [Real.exp_pos ((K : ℝ) * L)]
  obtain ⟨x₁, hx₁, hbig⟩ := node_of_uni (α := α) (lam := lam) (L := L) (εA := εA)
    (ε₁ := ε₁) (E := E) (θ := θ) (K := K) (I₁ := I₁) (I₂ := I₂)
    hδlt hgap huni hcard hA hthr hθ₀
  refine ⟨x₁, hx₁, ?_, ?_, ?_, hbig⟩
  · exact (I2set_balanced (hI2 hx₁)).1
  · exact (I2set_balanced (hI2 hx₁)).2.1
  · exact (I2set_balanced (hI2 hx₁)).2.2

end Work.TMC16Core.Core
