import Mathlib
import Submission.Work.SSGRoute.PTDefs
-- PORT435-BEGIN (v4.35 isDefEq respectTransparency compat)
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- PORT435-END

/-!
# The Shapiro `1`-cocycle transported to the restricted model

`Work.Sha2Lib.shapiroCocycle_mem` builds, from a character `y` of the coefficient subgroup `H`, a
`1`-cocycle of the coinduced module `Rep.coind H.subtype W` over `Γ`.  The unramified detector needs
the same class in the *restricted* model `Rep.res f (Rep.coind S.subtype W)`, where `f : Γ →* Γ'` is
a surjection (in the application: `galRes k K L : Gal(L/k) →* Gal(K/k)`) and `S ≤ Γ'` (in the
application `N = Gal(K/K₁)`), the coefficient subgroup of the coind being `H = f ⁻¹S` (in the
application `Gal(L/K₁)`).

The transport is *not* the naive "compose with `f`": the coind model over `Γ` is
`{φ : Γ → W.V // H-invariant}` while the restricted model is `{ψ : Γ' → W.V // S-invariant}`, and
the two are identified by `ψ = φ ∘ ℓ` for a section `ℓ` of `f`.  The point of this file is that
*the cocycle condition is automatic for such a `ψ`*, because any two lifts of the same element of
`Γ'` differ by an element of `ker f ≤ H` and the Shapiro transversal `c` is invariant under the
left `H`-action (`Work.Sha2Lib.shapiroCocycle_mem`'s `hcoinv`), so the ambiguity in `ℓ` does not
matter.  The only extra requirement is that `ℓ` maps `S` into `H` (this is what makes the
`S`-invariance of `ψ` true, and it is exactly the statement that the decomposition group of the
place lifts into the right subgroup).

Everything is pure group theory and `sorry`-free.
-/

namespace Work.SSGRoute.TPatom

open CategoryTheory

attribute [local instance 10000] Rep.hV2 Rep.hV1

/-- The `Γ`-action on the coinduction `Rep.coind φ W` evaluated pointwise: `(γ • f) g = f (g * γ)`
(local copy of `Work.Sha2Lib.coind_subtype_ρ_apply`). -/
private lemma coind_ρ_apply {Γ Γ' : Type} [Group Γ] [Group Γ'] (φ : Γ →* Γ')
    (W : Rep SSGRoute.PTExt.Coeff Γ)
    (γ : Γ') (x : (Rep.coind φ W).V) (g : Γ') :
    ((((Rep.coind φ W).ρ γ x : (Rep.coind φ W).V) : Γ' → W.V) g)
      = (x : Γ' → W.V) (g * γ) := by
  rw [Representation.coind_apply]
  rfl

/-- **Existence and pointwise formula for the transported Shapiro cocycle.** -/
theorem exists_shapiroCocycle_res {Γ Γ' : Type} [Group Γ] [Group Γ']
    (f : Γ →* Γ') (S : Subgroup Γ') (H : Subgroup Γ) (hH : H.Normal)
    (hker : f.ker ≤ H)
    (ℓ : Γ' → Γ) (hℓ : ∀ g : Γ', f (ℓ g) = g) (hℓH : ∀ n : ↥S, ℓ (n : Γ') ∈ H)
    (W : Rep SSGRoute.PTExt.Coeff ↥S)
    (htriv : ∀ (n : ↥S) (x : W.V), W.ρ n x = x)
    (c : Γ → Γ → ↥H)
    (hcmul : ∀ g γ γ' : Γ,
      ((c g (γ * γ') : ↥H) : Γ) = ((c g γ : ↥H) : Γ) * ((c (g * γ) γ' : ↥H) : Γ))
    (hcoinv : ∀ (g γ : Γ) (n : ↥H), c ((n : Γ) * g) γ = c g γ)
    (y : ↥H →* Multiplicative W.V) :
    ∃ z : Γ → (Rep.res f (Rep.coind S.subtype W)).V,
      z ∈ groupCohomology.cocycles₁ (Rep.res f (Rep.coind S.subtype W)) ∧
      (∀ (γ : Γ) (g : Γ'), (z γ : Γ' → W.V) g = Multiplicative.toAdd (y (c (ℓ g) γ))) := by
  classical
  have hmem : ∀ γ : Γ, (fun g : Γ' => Multiplicative.toAdd (y (c (ℓ g) γ)))
      ∈ (Representation.coindV S.subtype W.ρ) := by
    intro γ
    refine (Representation.mem_coindV (φ := S.subtype) (σ := W.ρ)
      (fun g : Γ' => Multiplicative.toAdd (y (c (ℓ g) γ)))).mpr ?_
    intro n g
    have ha : f (ℓ ((n : Γ') * g)) = (n : Γ') * g := hℓ _
    have hb : f (ℓ (n : Γ') * ℓ g) = (n : Γ') * g := by rw [map_mul, hℓ (n : Γ'), hℓ g]
    have hk : ℓ ((n : Γ') * g) * (ℓ (n : Γ') * ℓ g)⁻¹ ∈ f.ker := by
      rw [MonoidHom.mem_ker, map_mul, map_inv, ha, hb, mul_inv_cancel]
    have hstep1 : c (ℓ ((n : Γ') * g)) γ = c (ℓ (n : Γ') * ℓ g) γ := by
      conv_lhs => rw [show ℓ ((n : Γ') * g)
        = (ℓ ((n : Γ') * g) * (ℓ (n : Γ') * ℓ g)⁻¹) * (ℓ (n : Γ') * ℓ g) by group]
      exact hcoinv _ γ ⟨_, hker hk⟩
    have hstep2 : c (ℓ (n : Γ') * ℓ g) γ = c (ℓ g) γ := hcoinv _ γ ⟨_, hℓH n⟩
    rw [htriv n]
    exact congrArg (fun t => Multiplicative.toAdd (y t)) (hstep1.trans hstep2)
  let z : Γ → (Rep.res f (Rep.coind S.subtype W)).V := fun γ =>
    ⟨fun g : Γ' => Multiplicative.toAdd (y (c (ℓ g) γ)), hmem γ⟩
  have hzval : ∀ (γ : Γ) (g : Γ'), (z γ : Γ' → W.V) g = Multiplicative.toAdd (y (c (ℓ g) γ)) := by
    intro γ g
    dsimp only [z]
  have hact : ∀ (γ δ : Γ) (g : Γ'),
      (((Rep.res f (Rep.coind S.subtype W)).ρ γ (z δ) : (Rep.coind S.subtype W).V) : Γ' → W.V) g
        = Multiplicative.toAdd (y (c (ℓ g * γ) δ)) := by
    intro γ δ g
    rw [Rep.coe_res_obj_ρ', coind_ρ_apply, hzval]
    have h1 : f (ℓ (g * f γ)) = g * f γ := hℓ _
    have h2 : f (ℓ g * γ) = g * f γ := by rw [map_mul, hℓ g]
    have hk : ℓ (g * f γ) * (ℓ g * γ)⁻¹ ∈ f.ker := by
      rw [MonoidHom.mem_ker, map_mul, map_inv, h1, h2, mul_inv_cancel]
    have hstep : c (ℓ (g * f γ)) δ = c (ℓ g * γ) δ := by
      conv_lhs => rw [show ℓ (g * f γ)
        = (ℓ (g * f γ) * (ℓ g * γ)⁻¹) * (ℓ g * γ) by group]
      exact hcoinv _ δ ⟨_, hker hk⟩
    exact congrArg (fun t => Multiplicative.toAdd (y t)) hstep
  refine ⟨z, ?_, hzval⟩
  rw [groupCohomology.mem_cocycles₁_iff]
  intro γ δ
  apply Subtype.ext
  funext g
  rw [Submodule.coe_add, Pi.add_apply]
  rw [hact γ δ g, hzval γ g, hzval (γ * δ) g]
  have hc : c (ℓ g) (γ * δ)
      = c (ℓ g) γ * c (ℓ g * γ) δ := Subtype.ext (hcmul (ℓ g) γ δ)
  rw [hc, map_mul, toAdd_mul, add_comm]

end Work.SSGRoute.TPatom
