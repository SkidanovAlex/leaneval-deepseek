import Mathlib
import Submission.Work.Interfaces.Parabolic
import Submission.Work.Pert.Basic
import Submission.Work.Pert.RBlock
import Submission.Work.Pert.MaxDom
import Submission.Work.Pert.RBlock3

namespace Work.Pert.RBlock5

theorem Rlow_seed_phi_eq {f F τ Φp Ψ : ℂ → ℂ} {Ξ Ξ' : ℝ} {α : ℂ} {Qp' Q : Set ℂ}
    {m : ℕ} {k : ℤ} {d₁ : ℂ} {Df : Set ℂ} {ς : ℂ}
    (hΨinj : Set.InjOn Ψ Q)
    (hQp'sub : Qp' ⊆ Work.Pert.Qp Ξ' α)
    (hinjτ : Set.InjOn τ Qp')
    (hτF : ∀ z ∈ Work.Pert.Qp Ξ' α, τ (F z) = f (τ z))
    (hτper : ∀ z, τ (Work.Pert.Tt α z) = τ z)
    (hA42 : ∀ z ∈ Work.Pert.Qp Ξ' α, Ψ (Work.Pert.Tt α z) = Φp z + d₁)
    (hAbelΦp : ∀ z ∈ Work.Pert.Qp Ξ' α, F z ∈ Work.Pert.Qp Ξ' α → Φp (F z) = Φp z + 1)
    (hςQ : ς ∈ Q) (hTtςQ : Work.Pert.Tt α ς ∈ Q)
    (hwalk : ∀ j : ℕ, j ≤ m → F^[j] ς ∈ Work.Pert.Qp Ξ' α)
    (hFm : F^[m] ς ∈ Qp') :
    Work.Pert.coordP f Df τ Ψ Q
        (Work.Pert.Rlow f Qp' τ Φp (Work.Pert.coordP f Df τ Ψ Q) m k (d₁ + k) (Ψ ς))
      = τ (Work.Pert.Tt α ς) := by
  -- The seed value of `ψ = Ψ ς` is `τ ς`: `Ψ ς` is a level-`0` point of the gate coordinate `Ψ`.
  have hwalk0 : ς ∈ Work.Pert.Qp Ξ' α := hwalk 0 (Nat.zero_le m)
  have hseed : Work.Pert.coordP f Df τ Ψ Q (Ψ ς) = τ ς := by
    rw [Work.Pert.coordP_eq_tauC_of_mem_image hΨinj ⟨ς, hςQ, rfl⟩]
    exact congrArg τ (Work.Pert.invOn_eq hΨinj ⟨ς, hςQ, rfl⟩ hςQ rfl)
  -- The Abel walk identifies the horn coordinate of the level-`m` point with `Φp ς + m`.
  have hPhi := Work.Pert.ParabData.PhiP_invOn_level (Ξ := Ξ') (α := α)
      (Qp' := Qp') hinjτ hwalk hτF hAbelΦp hFm
  -- Hence `Rlow` at the seed returns to the gate, at the deck-shifted gate point `Ψ (Tt α ς)`.
  have hRlow : Work.Pert.Rlow f Qp' τ Φp (Work.Pert.coordP f Df τ Ψ Q) m k (d₁ + k) (Ψ ς)
      = Ψ (Work.Pert.Tt α ς) := by
    simp only [Work.Pert.Rlow]
    rw [hseed, hPhi, hA42 ς hwalk0]
    ring
  -- Evaluate `coordP` at that level-`0` gate point.
  rw [hRlow, Work.Pert.coordP_eq_tauC_of_mem_image hΨinj
    ⟨Work.Pert.Tt α ς, hTtςQ, rfl⟩]
  exact congrArg τ (Work.Pert.invOn_eq hΨinj ⟨Work.Pert.Tt α ς, hTtςQ, rfl⟩ hTtςQ rfl)

end Work.Pert.RBlock5
