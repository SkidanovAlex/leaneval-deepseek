import Mathlib
import Submission.Work.TMC16Core.Defs
import Submission.Work.TMC16Core.Basic.lemma_9_2_win

namespace Work.TMC16Core.Core

theorem nr_ablock {α lam : ℝ} {E : ℂ} {θ L ε₁ εsing δ : ℝ} {K : ℕ} {I₁ : Finset ℤ}
    (hL : 0 < L) (hε₁ : 0 < ε₁) (hε : 0 < εsing) (hεL : εsing ≤ L)
    (hδ1 : 1 / 40 ≤ δ) (hδ2 : δ ≤ 1 / 2)
    (hK : 40 ≤ K) (hKδ : 1 ≤ (K : ℝ) * (δ - 1 / 40))
    (hbd : ∀ n : ℕ, K / 40 ≤ n → n ≤ K → ∀ ζ : ℝ,
      ‖Work.TMC16Core.pd α lam ζ E (n + 1)‖ ≤ Real.exp ((n : ℝ) * (L + ε₁)))
    (hs : Work.TMC16Core.IsSingular α lam θ E (L - εsing) K 0)
    (hsub : ∀ x ∈ I₁, -((1 - δ) * (K : ℝ)) ≤ (x : ℝ) ∧ (x : ℝ) ≤ -(δ * (K : ℝ))) :
    ∀ x ∈ I₁, ‖Work.TMC16Core.pd α lam (θ + (x : ℝ) * α) E (K + 1)‖ ≤
      Real.exp (((K : ℝ) + 1) * (L - εsing * δ + ε₁)) := by
  intro x hx
  obtain ⟨hx1, hx2⟩ := hsub x hx
  have hx1' : (0 : ℤ) - (1 - δ) * (K : ℝ) ≤ (x : ℝ) := by
    simpa using hx1
  have hx2' : (x : ℝ) ≤ (0 : ℤ) - δ * (K : ℝ) := by
    simpa using hx2
  have hk := Work.TMC16Core.Basic.lemma_9_2_win (α := α) (lam := lam) (E := E) (θ := θ)
    (L := L) (ε := εsing) (ε₁ := ε₁) (δ := δ) (k := K) (y := 0)
    (le_of_lt hL) hεL hε hε₁ hδ1 hδ2 hK hKδ hbd hs x hx1' hx2'
  rwa [Work.TMC16Core.mem_AkSet_iff_shift] at hk

end Work.TMC16Core.Core
