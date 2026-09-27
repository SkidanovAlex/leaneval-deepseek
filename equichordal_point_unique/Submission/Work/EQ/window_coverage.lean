import Mathlib
import Submission.Work.EQ.DefsCore
import Submission.Work.EQ.bp_aux
import Submission.Work.EQ.backward_puiseux

namespace Work.EQ

/-- **Pointwise backward-Puiseux coverage of the window of a chain.**

This is `Work.EQ.coverage` (module `Submission/Work/EQ/bp_aux.lean`) applied to the window
`j ↦ (γ s).1 (j - m₁)` of the chain `γ s`, with end map `c w = germC a h (λ ^ n₁ * w)` and
`N = n₁ + m₁`.

Given `s` with `S ≤ s`, a `t` with `t ^ (2 ^ (n₁ + m₁)) = (γ s).2.1 - u`, `t ≠ 0` and
`‖t‖ < rhoFin' a c u R (n₁ + m₁)`, the window is a regular backward `EqRelC`-chain of length
`n₁ + m₁` ending at `c ((γ s).2.1)` (the end is `hfw` at index `n₁`, the pairs come from
`hchain`), so `coverage` produces an admissible sign sequence `σ` with
`(γ s).1 (j - m₁) = branchPt a c u R σ t j` for every `j : Fin (n₁ + m₁ + 1)`.

The work is the index bookkeeping: `(Fin.last (n₁+m₁) : ℕ) = n₁ + m₁`, and for `j : Fin (n₁+m₁)`
sending `Fin.castSucc j ↦ ((j:ℕ):ℤ) - m₁` and `Fin.succ j ↦ (((j:ℕ)+1):ℤ) - m₁` — the latter is
`(((j:ℕ):ℤ) - m₁) + 1`, matching `(hchain s hs).1`. -/
theorem window_coverage {a : ℝ} {h : ℂ → ℂ} {γ : ℝ → ChainData} {S : ℝ} {n₁ m₁ : ℕ} {u : ℂ}
    {R : ℝ} (hR : 0 < R)
    (hc : AnalyticOnNhd ℂ
      (fun w : ℂ => germC a h (((eqLam a : ℝ) : ℂ) ^ n₁ * w)) (Metric.ball u R))
    (hchain : ∀ s : ℝ, S ≤ s → IsChain a h (γ s))
    (hfw : ∀ s : ℝ, S ≤ s → ∀ n : ℕ, n₁ ≤ n →
      (γ s).1 (n : ℤ) = germC a h (((eqLam a : ℝ) : ℂ) ^ n * (γ s).2.1))
    {s : ℝ} (hsS : S ≤ s) {t : ℂ}
    (ht : t ^ (2 ^ (n₁ + m₁)) = (γ s).2.1 - u) (ht0 : t ≠ 0)
    (htρ : ‖t‖ < rhoFin' a
      (fun w : ℂ => germC a h (((eqLam a : ℝ) : ℂ) ^ n₁ * w)) u R (n₁ + m₁)) :
    ∃ σ : Fin (n₁ + m₁) → Bool,
      Adm a (fun w : ℂ => germC a h (((eqLam a : ℝ) : ℂ) ^ n₁ * w)) u R σ ∧
      ∀ j : Fin (n₁ + m₁ + 1),
        (γ s).1 ((((j : ℕ) : ℤ) - (m₁ : ℤ))) =
          branchPt a (fun w : ℂ => germC a h (((eqLam a : ℝ) : ℂ) ^ n₁ * w)) u R σ t j := by
  classical
  -- The window of the chain as a `Fin (n₁+m₁+1)`-family of points.
  set W : Fin (n₁ + m₁ + 1) → ℂ × ℂ :=
    fun j => (γ s).1 ((((j : ℕ) : ℤ) - (m₁ : ℤ))) with hW
  -- The window ends at the end map evaluated at `(γ s).2.1`.
  have hWlast : W (Fin.last (n₁ + m₁))
      = (fun w : ℂ => germC a h (((eqLam a : ℝ) : ℂ) ^ n₁ * w)) ((γ s).2.1) := by
    rw [hW]
    simp only []
    rw [Fin.val_last]
    have hzi : (((n₁ + m₁ : ℕ) : ℤ) - (m₁ : ℤ)) = (n₁ : ℤ) := by push_cast; ring
    rw [hzi]
    exact hfw s hsS n₁ le_rfl
  -- Consecutive window points are regular pairs, read off the chain `γ s`.
  have hWreg : ∀ j : Fin (n₁ + m₁), RegPair a (W (Fin.castSucc j)) (W (Fin.succ j)) := by
    intro j
    rw [hW]
    simp only []
    have h1 := (hchain s hsS).1 (((j : ℕ) : ℤ) - (m₁ : ℤ))
    have hv1 : ((((Fin.castSucc j : Fin (n₁ + m₁ + 1)) : ℕ) : ℤ) - (m₁ : ℤ))
        = ((j : ℕ) : ℤ) - (m₁ : ℤ) := by
      simp [Fin.val_castSucc]
    have hv2 : ((((Fin.succ j : Fin (n₁ + m₁ + 1)) : ℕ) : ℤ) - (m₁ : ℤ))
        = (((j : ℕ) : ℤ) - (m₁ : ℤ)) + 1 := by
      simp [Fin.val_succ]
      ring
    rw [hv1, hv2]
    exact h1
  obtain ⟨σ, hAdm, hPt⟩ := coverage (a := a) (u₀ := u) (R := R) hR
    (c := fun w : ℂ => germC a h (((eqLam a : ℝ) : ℂ) ^ n₁ * w)) hc
    (N := n₁ + m₁) (u := (γ s).2.1) (t := t) ht ht0 htρ W hWlast hWreg
  exact ⟨σ, hAdm, fun j => hPt j⟩

end Work.EQ
