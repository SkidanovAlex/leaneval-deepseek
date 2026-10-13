import Mathlib

/-!
# Global uniqueness of integral curves of a `C¹` autonomous vector field

If `X : (Fin m → ℝ) → (Fin m → ℝ)` is `C¹` and `γ, δ : ℝ → Fin m → ℝ` are integral curves of `X`
satisfying `γ t₀ = δ t₀`, then `γ = δ`.

The vector field is only locally Lipschitz (a `C¹` map on a finite-dimensional space), so Mathlib's
global uniqueness statement `ODE_solution_unique_univ` (which requires a *global* Lipschitz constant)
does not apply directly. Instead we use the standard clopen argument: the coincidence set
`{t | γ t = δ t}` is closed (continuity) and open (local uniqueness via
`ODE_solution_unique_of_eventually` applied in a Lipschitz neighbourhood of `γ t₀`); since `ℝ` is
preconnected and the set is non-empty, it is all of `ℝ`.
-/

open Filter
open scoped Topology

namespace Work.WilE2

theorem integral_curve_unique_global {m : ℕ} (X : (Fin m → ℝ) → (Fin m → ℝ)) (hX : ContDiff ℝ 1 X)
    {γ δ : ℝ → Fin m → ℝ} (hγ : ∀ t, HasDerivAt γ (X (γ t)) t)
    (hδ : ∀ t, HasDerivAt δ (X (δ t)) t) {t₀ : ℝ} (h : γ t₀ = δ t₀) : γ = δ := by
  -- Local uniqueness: near any point where `γ` and `δ` agree, they agree on a neighbourhood.
  have hloc : ∀ t₁, γ t₁ = δ t₁ → γ =ᶠ[𝓝 t₁] δ := by
    intro t₁ ht₁
    -- `X` is `C¹`, hence Lipschitz on a neighbourhood `s` of `γ t₁`.
    obtain ⟨K, s, hs, hKs⟩ := hX.locallyLipschitz (γ t₁)
    have hγs : ∀ᶠ t in 𝓝 t₁, γ t ∈ s :=
      Filter.eventually_iff.mpr ((hγ t₁).continuousAt.preimage_mem_nhds hs)
    have hδs : ∀ᶠ t in 𝓝 t₁, δ t ∈ s :=
      Filter.eventually_iff.mpr ((hδ t₁).continuousAt.preimage_mem_nhds (by rw [← ht₁]; exact hs))
    exact ODE_solution_unique_of_eventually (v := fun _ => X) (s := fun _ => s) (K := K)
      (Filter.Eventually.of_forall fun _ => hKs)
      ((Filter.Eventually.of_forall hγ).and hγs)
      ((Filter.Eventually.of_forall hδ).and hδs) ht₁
  -- The coincidence set is clopen.
  have hclosed : IsClosed {t : ℝ | γ t = δ t} :=
    isClosed_eq (continuous_iff_continuousAt.mpr fun t => (hγ t).continuousAt)
      (continuous_iff_continuousAt.mpr fun t => (hδ t).continuousAt)
  have hopen : IsOpen {t : ℝ | γ t = δ t} :=
    isOpen_iff_mem_nhds.mpr fun t ht => Filter.eventually_iff.mp (hloc t ht)
  -- `ℝ` is preconnected, so a non-empty clopen set is everything.
  have huniv : {t : ℝ | γ t = δ t} = Set.univ :=
    IsClopen.eq_univ ⟨hclosed, hopen⟩ ⟨t₀, h⟩
  funext t
  have : t ∈ ({t : ℝ | γ t = δ t}) := by rw [huniv]; exact Set.mem_univ t
  exact this

end Work.WilE2
