import Mathlib

namespace Work.Horn.HB

theorem range_lift_eq_pathComponent {E X A : Type*} [TopologicalSpace E] [TopologicalSpace X]
    [TopologicalSpace A] {p : E → X} (hp : IsCoveringMap p) [PathConnectedSpace A] {u : A → X}
    (hu : IsCoveringMap u) {a₀ : A} {e₀ : E} (he : p e₀ = u a₀) {σ : A → E} (hσ : Continuous σ)
    (hσa : σ a₀ = e₀) (hcomp : ∀ a, p (σ a) = u a) :
    Set.range σ = pathComponent e₀ := by
  apply Set.Subset.antisymm
  · -- `σ` is continuous and `A` is path connected, so its range is path connected and
    -- contains `e₀`; hence it lies in the path component of `e₀`.
    exact (isPathConnected_range hσ).subset_pathComponent ⟨a₀, hσa⟩
  · -- Conversely, take `e` in the path component of `e₀` and a path `γ` from `e₀` to `e` in `E`.
    rintro e he
    rw [mem_pathComponent_iff] at he
    obtain ⟨γ⟩ := he
    -- Lift the base path `p ∘ γ` through the covering `u`, starting at `a₀`.
    let γX : C(unitInterval, X) := ⟨fun t => p (γ t), hp.continuous.comp γ.continuous⟩
    have hγX : ∀ t, γX t = p (γ t) := fun t => rfl
    have h0 : γX 0 = u a₀ := by
      show p (γ 0) = u a₀
      rw [show (γ : unitInterval → E) 0 = e₀ from γ.source, he]
    let Γ : C(unitInterval, A) := hu.liftPath γX a₀ h0
    have hΓ0 : Γ 0 = a₀ := hu.liftPath_zero γX a₀ h0
    have hΓ : ∀ t, u (Γ t) = p (γ t) := fun t => by
      have h := congr_fun (hu.liftPath_lifts γX a₀ h0) t
      simpa [hγX] using h
    -- Then `σ ∘ Γ` is a lift of `p ∘ γ` through the covering `p` starting at `e₀`,
    -- so by uniqueness of path lifts it equals `γ`.
    have hcont : Continuous (fun t : unitInterval => σ (Γ t)) := hσ.comp Γ.continuous
    have heq : p ∘ (fun t : unitInterval => σ (Γ t)) = p ∘ (fun t : unitInterval => γ t) := by
      funext t
      show p (σ (Γ t)) = p (γ t)
      rw [hcomp, hΓ t]
    have h0' : (fun t : unitInterval => σ (Γ t)) 0 = (fun t : unitInterval => γ t) 0 := by
      show σ (Γ 0) = γ 0
      rw [hΓ0, hσa]
      exact γ.source.symm
    have hfun := hp.eq_of_comp_eq hcont γ.continuous heq 0 h0'
    exact ⟨Γ 1, by rw [congr_fun hfun 1, show (γ : unitInterval → E) 1 = e from γ.target]⟩

end Work.Horn.HB
