import Mathlib
import Submission.Work.Interfaces.Parabolic
import Submission.Work.L62.lift_section

namespace Work.L62

open Complex Set Metric Filter Topology

/-- **Lifted Lemma 5.3 (sections of the horn map).**  `Bu` is the upper component of the domain
of the lifted horn map `E = d.E` of a germ `g₀ ∈ 𝓕₀`; `hd.v` is a lift of the unique critical value.
If `Y` is open and simply connected and avoids the critical values of `E - β` (i.e.
`ζ + β ≠ v + k` for all `ζ ∈ Y`, `k : ℤ`), then every `x₀ ∈ Bu` with `E x₀ - β = y₀ ∈ Y` is the
value at `y₀` of a holomorphic section `σ : Y → Bu` of `E - β` over `Y`. -/
theorem exists_section_horn {g₀ : ℂ → ℂ} {D : Set ℂ} (d : MandelDim.ParabData g₀ D)
    (hd : MandelDim.HornData d) {β : ℂ}
    {Y : Set ℂ} (hYo : IsOpen Y) (hYsc : SimplyConnectedSpace Y)
    (havoid : ∀ ζ ∈ Y, ∀ k : ℤ, ζ + β ≠ hd.v + k)
    {y₀ : ℂ} (hy₀ : y₀ ∈ Y) {x₀ : ℂ} (hx₀ : x₀ ∈ hd.Bu) (hxy : d.E x₀ - β = y₀) :
    ∃ σ : ℂ → ℂ, DifferentiableOn ℂ σ Y ∧ σ y₀ = x₀ ∧
      (∀ y ∈ Y, σ y ∈ hd.Bu ∧ d.E (σ y) - β = y) := by
  -- `Bu ⊆ DE`, so `d.E = d.Φ ∘ d.φ` is holomorphic on the open set `Bu`
  have hsub : hd.Bu ⊆ d.DE := fun w hw => hd.sub (Or.inl hw)
  have hφdiff : DifferentiableOn ℂ d.φ hd.Bu := d.φ_holo.mono (fun w hw => (hsub hw).1)
  have hE : DifferentiableOn ℂ d.E hd.Bu :=
    d.Φ_holo.comp hφdiff (fun w hw => (hsub hw).2)
  have hp : DifferentiableOn ℂ (fun z => d.E z - β) hd.Bu :=
    hE.sub (differentiableOn_const β)
  -- the covering of the horn map pushes forward along the translation `ζ ↦ ζ - β`
  have hcov : IsCoveringMapOn (fun z : hd.Bu => d.E z - β) Y :=
    (hd.cov_u.homeomorph_comp (Homeomorph.subRight β)).mono
      (fun y hy k => havoid y hy k)
  -- Lemma 5.3 (abstract covering form)
  obtain ⟨σ, hσd, hσ0, hσ⟩ :=
    lift_section hd.Bu_open hp hYo hYsc hcov hy₀ hx₀ hxy
  exact ⟨σ, hσd, hσ0, hσ⟩

end Work.L62
