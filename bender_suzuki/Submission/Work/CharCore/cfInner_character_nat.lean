import Mathlib
import Submission.Work.CharCore.Basic
import Submission.Work.CharCore.irr_orthonormal
import Submission.Work.CharCore.mem_Irr_iff_fdrep
import Submission.Work.CharCore.star_char

-- ftport:v435-opts-begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- ftport:v435-opts-end

/-!
# `Work.CharCore.cfInner_character_nat`

The multiplicity of an irreducible character `χ ∈ Irr G` in the character of an arbitrary
finite dimensional complex representation `ρ` of a finite group `G`,

`cfInner ρ.character χ`,

is a natural number.

## Proof

Pick the irreducible character `χ` as the character of our favourite simple submodule
`N ≤ ℂ[G]` of the regular module (`Work.CharCore.exists_mem_irrSubmodules_of_mem_Irr`), so
`χ = (submoduleRep N).character`.  For a *character of a representation* the complex conjugate
of the value at `g` is the value at `g⁻¹` (`Work.CharCore.star_char`), so

`cfInner ρ.character χ = (Nat.card G)⁻¹ * ∑_g ρ.character g * (submoduleRep N).character g⁻¹`.

Reversing the product inside the sum (`∑_g f g⁻¹ h g = ∑_g f g h g⁻¹`) shows that this is
Mathlib's scalar product `(Nat.card G)⁻¹ * ∑_g σ.character g * ρ.character g⁻¹` for the
irreducible representation `σ = submoduleRep N`, which is the dimension of the space of
`G`-equivariant linear maps `ρ → σ`
(`Representation.card_inv_mul_sum_char_mul_char_eq_finrank`) — a natural number.
-/

noncomputable section

open Classical

namespace Work.CharCore

theorem cfInner_character_nat {G : Type*} [Group G] [Fintype G] {V : Type*} [AddCommGroup V]
    [Module ℂ V] [FiniteDimensional ℂ V] (ρ : Representation ℂ G V) {χ : G → ℂ} (hχ : χ ∈ Irr G) :
    ∃ n : ℕ, cfInner ρ.character χ = n := by
  obtain ⟨N, _, hNχ⟩ := exists_mem_irrSubmodules_of_mem_Irr hχ
  refine ⟨Module.finrank ℂ (ρ.IntertwiningMap (submoduleRep N)), ?_⟩
  rw [cfInner, Fintype.card_eq_nat_card, ← hNχ]
  have h1 : (∑ x : G, ρ.character x * starRingEnd ℂ ((submoduleRep N).character x))
      = ∑ x : G, ρ.character x * (submoduleRep N).character x⁻¹ :=
    Finset.sum_congr rfl fun x _ => by rw [star_char (submoduleRep N) x]
  rw [h1]
  have h2 : (∑ x : G, ρ.character x * (submoduleRep N).character x⁻¹)
      = ∑ x : G, (submoduleRep N).character x * ρ.character x⁻¹ := by
    rw [Finset.sum_congr rfl
      (fun x _ => mul_comm (ρ.character x) ((submoduleRep N).character x⁻¹))]
    rw [← Equiv.sum_comp (Equiv.inv G)
      (fun y => (submoduleRep N).character y * ρ.character y⁻¹)]
    exact Finset.sum_congr rfl fun _ _ => by simp
  rw [h2]
  exact Representation.card_inv_mul_sum_char_mul_char_eq_finrank ρ (submoduleRep N)

end Work.CharCore
