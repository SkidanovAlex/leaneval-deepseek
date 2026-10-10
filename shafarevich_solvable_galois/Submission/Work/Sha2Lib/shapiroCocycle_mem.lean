import Mathlib.RepresentationTheory.Coinduced
import Mathlib.RepresentationTheory.Homological.GroupCohomology.LowDegree
import Submission.Work.SSGRoute.PTDefs
-- PORT435-BEGIN (v4.35 isDefEq respectTransparency compat)
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- PORT435-END

namespace Work.Sha2Lib

/-- The `Γ`-action on the coinduction `Rep.coind H.subtype W` evaluated pointwise:
`(γ • f) g = f (g * γ)`. -/
lemma coind_subtype_ρ_apply {Γ : Type} [Group Γ] {H : Subgroup Γ}
    (W : Rep.{0} SSGRoute.PTExt.Coeff ↥H)
    (γ : Γ) (x : (Rep.coind H.subtype W).V) (g : Γ) :
    (((Rep.coind H.subtype W).ρ γ x : (Rep.coind H.subtype W).V) : Γ → W.V) g
      = (x : Γ → W.V) (g * γ) := by
  rw [Representation.coind_apply]; rfl

/-- **The Shapiro `1`-cocycle of a character of a subgroup, in the coinduced model.**

Let `Γ` be a finite group, `H ≤ Γ` a subgroup, `W` a `Rep Coeff H` on which `H` acts trivially.
Let `c : Γ → Γ → ↥H` satisfy the multiplicative telescoping identity
`c g (γ * γ') = c g γ * c (g * γ) γ'`, the unit condition `c g 1 = 1`, and the invariance
`c (n * g) γ = c g γ` under the left `H`-action.  (For a set-theoretic section `s : Γ → Γ` of
`Γ → H \ Γ`, the element `c g γ := ⟨s g * γ * (s (g * γ))⁻¹, _⟩` lies in `H` and satisfies all
three.)

Then for any character `y : ↥H →* Multiplicative W.V`, the function
`z : Γ → (Rep.coind H.subtype W).V`, `z γ := (fun g => y (c g γ))`, is a `1`-cocycle of the
coinduced `Γ`-module `Rep.coind H.subtype W` (whose `Γ`-action is `(γ • f) g = f (g * γ)`). -/
theorem shapiroCocycle_mem {Γ : Type} [Group Γ] [Fintype Γ] {H : Subgroup Γ}
    (W : Rep.{0} SSGRoute.PTExt.Coeff ↥H)
    (htriv : ∀ (n : ↥H) (x : W.V), W.ρ n x = x)
    (c : Γ → Γ → ↥H)
    (hcmul : ∀ g γ γ' : Γ,
      ((c g (γ * γ') : ↥H) : Γ) = ((c g γ : ↥H) : Γ) * ((c (g * γ) γ' : ↥H) : Γ))
    (hcunit : ∀ g : Γ, ((c g 1 : ↥H) : Γ) = 1)
    (hcoinv : ∀ (g γ : Γ) (n : ↥H), c ((n : Γ) * g) γ = c g γ)
    (y : ↥H →* Multiplicative W.V) :
    (fun γ : Γ =>
      (⟨fun g : Γ => Multiplicative.toAdd (y (c g γ)), by
        intro n g
        show Multiplicative.toAdd (y (c ((n : Γ) * g) γ))
          = W.ρ n (Multiplicative.toAdd (y (c g γ)))
        rw [hcoinv g γ n]
        exact (htriv n _).symm⟩ : (Rep.coind H.subtype W).V))
      ∈ groupCohomology.cocycles₁ (Rep.coind H.subtype W) := by
  rw [groupCohomology.mem_cocycles₁_iff]
  intro γ γ'
  apply Subtype.ext
  funext g
  simp only [Submodule.coe_add, Pi.add_apply]
  rw [coind_subtype_ρ_apply]
  have h : c g (γ * γ') = c g γ * c (g * γ) γ' := Subtype.val_injective (hcmul g γ γ')
  rw [h, map_mul, toAdd_mul, add_comm]

end Work.Sha2Lib
