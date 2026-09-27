import Mathlib
import Submission.Work.Engulf.Defs
import Submission.Work.Engulf.Tools
import Submission.Work.Engulf.E4alt.Defs2
import Submission.Work.Engulf.Auxi.TameTransfer

open Set Metric PL Finset

namespace Work.Engulf.E4alt

/-- `SmoothChart` transfers along a refinement whose `L`-faces are carried by coarse `L`-faces. -/
theorem smoothChart_of_carrier {n p : ℕ} {M : Type*} [MetricSpace M] {N : ℕ}
    {X : Set M} {Γ Γ₁ : Cx N} {L : Set (E N)} {f g : E N → M} {ψ : CubeChart n M}
    (hgf : EqOn g f L)
    (carrier : ∀ s ∈ Γ₁.faces, simp s ⊆ L → ∃ t ∈ Γ.faces, simp s ⊆ simp t ∧ simp t ⊆ L)
    (hs : SmoothChart p X Γ L f ψ) : SmoothChart p X Γ₁ L g ψ := by
  refine ⟨hs.1, ?_⟩
  intro s hsF hsL y hy hcube
  obtain ⟨t, htF, hst, htL⟩ := carrier s hsF hsL
  rw [hgf (hsL hy)] at hcube
  obtain ⟨δ, hδ, hlin⟩ := hs.2 t htF htL y (hst hy) hcube
  obtain ⟨A, hA⟩ := hlin
  refine ⟨δ, hδ, A, fun z hz => ⟨(hA z ⟨hst hz.1, hz.2⟩).1, ?_⟩⟩
  rw [hgf (hsL hz.1), (hA z ⟨hst hz.1, hz.2⟩).2]

/-- `Tame` transfers along a refinement whose `L`-faces are carried by coarse `L`-faces, when `g`
agrees with `f` on `L`. -/
theorem tame_of_carrier {n p : ℕ} {M : Type*} [MetricSpace M] {N : ℕ}
    {X : Set M} {Γ Γ₁ : Cx N} {L : Set (E N)} {f g : E N → M}
    (hgf : EqOn g f L)
    (carrier : ∀ s ∈ Γ₁.faces, simp s ⊆ L → ∃ t ∈ Γ.faces, simp s ⊆ simp t ∧ simp t ⊆ L)
    (ht : Tame n p X Γ L f) : Tame n p X Γ₁ L g := by
  intro x
  obtain ⟨ψ, hx, hs⟩ := ht x
  exact ⟨ψ, hx, smoothChart_of_carrier hgf carrier hs⟩

theorem tameOfNormData {n p q N : ℕ} {M : Type*} [MetricSpace M] {V X : Set M} {Γ : PL.Cx N}
    {K L : Set (PL.E N)} {f : PL.E N → M} {τ₀ τ₁ : Finset (PL.E N)} {ψ : PL.CubeChart n M}
    {ε : ℝ} (ND : Work.Engulf.Alt.NormData n p q N M V X Γ K L f τ₀ τ₁ ψ ε)
    (H7 : Work.Engulf.L7Hyp n p q V X Γ K L f τ₀ τ₁) :
    Work.Engulf.Tame n p X ND.Γ₁ L ND.g₁ :=
  tame_of_carrier ND.g₁frz ND.carrier H7.cfg.tame

end Work.Engulf.E4alt
