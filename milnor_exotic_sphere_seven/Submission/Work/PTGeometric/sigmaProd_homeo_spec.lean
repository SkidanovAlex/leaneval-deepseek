import Mathlib

-- Lean v4.35.0-rc3: restore v4.34 instance-unification transparency (port).
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false

/-!
# Associativity/regrouping homeomorphism for a nested `Sigma` type

For an index type `ι`, a family `Z : ι → Type*` and `m : ℕ`, the nested sigma type
`Σ k : Fin m, Σ a : ι, Z a` is homeomorphic to the "flattened" type
`Σ p : Fin m × ι, Z p.2`, by the canonical regrouping map
`⟨k, ⟨a, z⟩⟩ ↦ ⟨(k, a), z⟩`.

This is the topological (not merely set-theoretic) form of `Equiv.sigmaAssoc`
combined with `Equiv.sigmaEquivProd`; the proof of continuity is immediate from
`continuous_sigma_iff` and `Continuous.sigma_map`.
-/

namespace Work.PTGeometric

theorem sigmaProd_homeo_spec {m : ℕ} {ι : Type} {Z : ι → Type*} [∀ a, TopologicalSpace (Z a)] :
    ∃ H : (Σ _k : Fin m, Σ a : ι, Z a) ≃ₜ (Σ p : Fin m × ι, Z p.2),
      ∀ u : (Σ _k : Fin m, Σ a : ι, Z a), H u = ⟨(u.1, u.2.1), u.2.2⟩ := by
  refine ⟨{ toFun := fun u => ⟨(u.1, u.2.1), u.2.2⟩
            invFun := fun p => ⟨p.1.1, ⟨p.1.2, p.2⟩⟩
            left_inv := ?_
            right_inv := ?_
            continuous_toFun := ?_
            continuous_invFun := ?_ }, ?_⟩
  · rintro ⟨k, a, z⟩; rfl
  · rintro ⟨⟨k, a⟩, z⟩; rfl
  · rw [continuous_sigma_iff]
    intro k
    exact Continuous.sigma_map (σ := Z) (τ := fun p : Fin m × ι => Z p.2)
      (f₁ := fun a => (k, a)) (f₂ := fun _ => id) (fun a => continuous_id)
  · rw [continuous_sigma_iff]
    intro p
    have h1 : Continuous (fun z : Z p.2 => (⟨p.2, z⟩ : Σ a : ι, Z a)) := continuous_sigmaMk
    have h2 : Continuous (fun y : (Σ a : ι, Z a) => (⟨p.1, y⟩ : Σ k : Fin m, Σ a, Z a)) :=
      continuous_sigmaMk (σ := fun _ : Fin m => (Σ a : ι, Z a)) (i := p.1)
    exact h2.comp h1
  · intro u; rfl

end Work.PTGeometric
