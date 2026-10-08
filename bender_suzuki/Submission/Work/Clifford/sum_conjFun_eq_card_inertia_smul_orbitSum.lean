import Mathlib
import Submission.Work.Clifford.Orbit
import Submission.Work.Clifford.card_charOrbit

-- ftport:v435-opts-begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- ftport:v435-opts-end

/-!
# `Work.Clifford.sum_conjFun_eq_card_inertia_smul_orbitSum`

For a normal subgroup `N ⊴ G` of a finite group `G` and an arbitrary function `θ : N → ℂ`,
summing the conjugates `θ^g = conjFun N g θ` (`θ^g(x) = θ (g x g⁻¹)`) over all `g : G` and
counting multiplicities gives

  `∑_{g : G} θ^g = |I_G(θ)| • orbitSum N θ`,

where `I_G(θ) = inertia N θ = {g : G | θ^g = θ}` is the inertia group of `θ` and
`orbitSum N θ = ∑_{φ ∈ charOrbit N θ} φ` is the sum of the distinct conjugates of `θ`.

This is the "with multiplicity" companion of the orbit–stabiliser statement
(`Work.Clifford.card_charOrbit`): the map `g ↦ θ^g` has image `charOrbit N θ`, and the fibre over
every point of the orbit is a coset of the inertia group, hence has cardinality `|I_G(θ)|`.  No
hypothesis on `θ` is needed: it may be an arbitrary complex-valued function on `N`.

Concretely, the fibre of `φ = θ^h` is `I_G(θ) * h` — indeed
`θ^g = θ^h ↔ g * h⁻¹ ∈ I_G(θ) ↔ g ∈ I_G(θ) * h` (`Work.Clifford.conjFun_eq_conjFun_iff`) — and
the sum of the terms of a fibre is `|I_G(θ)| • φ`.  Summing over the orbit yields the statement.
-/

noncomputable section

set_option linter.unusedSectionVars false

open Classical

namespace Work.Clifford

universe u

variable {G : Type u} [Group G] [Fintype G]
variable {N : Subgroup G} [N.Normal]

/-- The fibre of the map `g ↦ θ^g` over the conjugate `θ^h` of `θ` is a coset of the inertia
group, hence has `Nat.card (inertia N θ)` elements. -/
theorem filter_conjFun_eq_card_inertia (θ : N → ℂ) (h : G) :
    (Finset.univ.filter (fun g : G => conjFun N g θ = conjFun N h θ)).card
      = Nat.card ↥(inertia N θ) := by
  classical
  rw [Nat.card_eq_fintype_card]
  -- the fibre is `I_G(θ) * h`
  have himg : Finset.univ.filter (fun g : G => conjFun N g θ = conjFun N h θ)
      = Finset.image (fun i : ↥(inertia N θ) => (i : G) * h) Finset.univ := by
    ext g
    simp only [Finset.mem_filter, Finset.mem_univ, true_and, Finset.mem_image]
    constructor
    · intro hg
      rw [conjFun_eq_conjFun_iff] at hg
      exact ⟨⟨g * h⁻¹, hg⟩, by group⟩
    · rintro ⟨i, hi⟩
      rw [← hi, conjFun_eq_conjFun_iff]
      show ((i : G) * h) * h⁻¹ ∈ inertia N θ
      rw [mul_inv_cancel_right]
      exact i.2
  rw [himg, Finset.card_image_of_injective _ (fun a b hab => Subtype.ext (mul_right_cancel hab)),
    Finset.card_univ]

/-- Pointwise form of the main identity: at a point `n : N`, the sum of the conjugates of `θ`
is `|I_G(θ)|` times the sum of the members of the orbit. -/
theorem sum_conjFun_apply_eq_card_inertia_mul_orbitSum (θ : N → ℂ) (n : N) :
    ∑ g : G, conjFun N g θ n =
      ∑ φ ∈ charOrbit N θ, (Nat.card ↥(inertia N θ) : ℂ) * φ n := by
  classical
  -- group the sum over `G` by the value of `g ↦ θ^g`
  have hfib : ∑ φ ∈ charOrbit N θ,
        ∑ i ∈ (Finset.univ : Finset G) with conjFun N i θ = φ, φ n
      = ∑ i : G, conjFun N i θ n :=
    Finset.sum_fiberwise_of_maps_to' (s := (Finset.univ : Finset G)) (t := charOrbit N θ)
      (g := fun g : G => conjFun N g θ) (f := fun φ : N → ℂ => φ n)
      (fun i _ => conjFun_mem_charOrbit θ i)
  rw [← hfib]
  refine Finset.sum_congr rfl fun φ hφ => ?_
  -- each fibre contributes `|I_G(θ)| • φ`
  rw [Finset.sum_const]
  obtain ⟨g, hg⟩ := mem_charOrbit.mp hφ
  rw [← hg, filter_conjFun_eq_card_inertia θ g, nsmul_eq_mul]

theorem sum_conjFun_eq_card_inertia_smul_orbitSum {G : Type*} [Group G] [Fintype G]
    {N : Subgroup G} [N.Normal] (θ : N → ℂ) :
    ∑ g : G, Work.Clifford.conjFun N g θ =
      (Nat.card ↥(Work.Clifford.inertia N θ) : ℂ) • Work.Clifford.orbitSum N θ := by
  classical
  funext n
  rw [Finset.sum_apply, Pi.smul_apply, smul_eq_mul, orbitSum_apply]
  rw [sum_conjFun_apply_eq_card_inertia_mul_orbitSum θ n, Finset.mul_sum]

end Work.Clifford
