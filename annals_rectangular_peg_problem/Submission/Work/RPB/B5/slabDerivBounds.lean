import Mathlib
import Submission.Work.RPB.B3.UniformInverseAux
import Submission.Work.RPB.B3.positivityExpansion
import Submission.Work.RPB.B3.boundsOnCompactBox

namespace Work.RPB.B5

theorem slabDerivBounds (S : ℝ → ℝ → ℝ → ℝ)
    (hS : ContDiff ℝ 8 (fun z : ℝ × (ℝ × ℝ) => S z.1 z.2.1 z.2.2))
    (hper : ∀ τ t ρ, S τ (t + 2 * Real.pi) ρ = S τ t ρ)
    (hδ : ∀ τ ∈ Set.Icc (0 : ℝ) 1, ∀ t, 0 < deriv (fun ρ => S τ t ρ) 0) :
    ∃ ε₀ : ℝ, 0 < ε₀ ∧ ∃ δ : ℝ, 0 < δ ∧ ∃ M : ℝ, 0 < M ∧
      ∀ τ ∈ Set.Icc (0 : ℝ) 1, ∀ t, ∀ ρ ∈ Set.Icc (-ε₀) ε₀,
        δ ≤ deriv (fun ρ => S τ t ρ) ρ ∧ |deriv (fun ρ => S τ t ρ) ρ| ≤ M := by
  classical
  -- The joint `ρ`-partial derivative, as a function of `(τ, t, ρ)`.
  set g : ℝ × (ℝ × ℝ) → ℝ := fun p => deriv (fun ρ => S p.1 p.2.1 ρ) p.2.2 with hg_def
  have hg : Continuous g := by
    rw [hg_def]
    exact Work.RPB.B3.continuous_deriv_rho S (hS.of_le (by norm_num))
  -- Unfolding lemma.
  have hg_apply : ∀ (τ t ρ : ℝ), g (τ, t, ρ) = deriv (fun s => S τ t s) ρ := by
    intro τ t ρ
    simp only [hg_def]
  -- Step 1: `∂_ρ S > 0` on the slab over one fundamental period `[0, 2π]`.
  obtain ⟨ε₁, hε₁pos, hε₁⟩ :=
    Work.RPB.B3.positivityExpansion (g := g) hg (a := 0) (b := 1) (c := 0) (d := 2 * Real.pi)
      (by norm_num) (by positivity)
      (fun τ hτ t _ => by rw [hg_apply τ t 0]; exact hδ τ hτ t)
  -- Step 2: uniform lower bound `δ` and upper bound `M` on the compact box.
  obtain ⟨δ, hδpos, M, hMpos, hbnd⟩ :=
    Work.RPB.B3.boundsOnCompactBox (g := g) hg (a := 0) (b := 1) (c := 0) (d := 2 * Real.pi)
      (e := ε₁)
      (by
        rintro ⟨τ, t', ρ⟩ ⟨hτ, ht', hρ⟩
        exact hε₁ τ hτ t' ht' ρ hρ)
  refine ⟨ε₁, hε₁pos, δ, hδpos, M, hMpos, ?_⟩
  intro τ hτ t ρ hρ
  -- Reduce an arbitrary `t` to the fundamental period.
  obtain ⟨t₀, ht₀, ht₀eq⟩ := Work.RPB.B3.rpbPeriodReduce S hper τ t
  have hbox : (τ, (t₀, ρ)) ∈
      Set.Icc (0:ℝ) 1 ×ˢ (Set.Icc (0:ℝ) (2 * Real.pi) ×ˢ Set.Icc (-ε₁) ε₁) :=
    ⟨hτ, ht₀, hρ⟩
  have hb := hbnd (τ, (t₀, ρ)) hbox
  have hgeq : g (τ, t, ρ) = g (τ, t₀, ρ) := by
    rw [hg_apply τ t ρ, hg_apply τ t₀ ρ]
    congr 1
    funext s
    exact ht₀eq s
  rw [← hg_apply τ t ρ, hgeq]
  exact hb

end Work.RPB.B5
