import Mathlib
import Submission.Work.Induction.Defs
import Submission.Work.CharCore.star_char
import Submission.Work.CharCore.irreducible_character_mem_Irr
import Submission.Work.Clifford.CharPair

-- ftport:v435-opts-begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- ftport:v435-opts-end

namespace Work.Induction

open Classical

-- Orthonormality of the irreducible characters `Work.CharCore.Irr G` for the normalised inner
-- product.  Proof route: `χ ∈ Irr G` and `ψ ∈ Irr G` are characters of simple representations
-- (`Work.CharCore.exists_mem_irrSubmodules_of_mem_Irr` gives a simple submodule `N` of the
-- regular module with `χ = (Work.CharCore.submoduleRep N).character`; view it as an `FDRep` via
-- `FDRep.of`), and Mathlib's `FDRep.char_orthonormal` gives
-- `|G|⁻¹ ∑_g V.character g * W.character g⁻¹ = if Nonempty (V ≅ W) then 1 else 0`.
-- Convert `W.character g⁻¹` to `conj (W.character g)` using `Work.CharCore.star_char`, and
-- `Nonempty (V ≅ W) ↔ V.character = W.character` (⇐ because the scalar product is then `1 ≠ 0`).
theorem irr_orthonormal {G : Type*} [Group G] [Fintype G] {χ ψ : G → ℂ}
    (hχ : χ ∈ Work.CharCore.Irr G) (hψ : ψ ∈ Work.CharCore.Irr G) :
    Work.CharCore.cfInner χ ψ = if χ = ψ then 1 else 0 := by
  -- `ψ` is the character of a simple submodule of the regular module, so its values at inverses
  -- are the conjugates of its values.
  obtain ⟨N, _hN, hNψ⟩ := Work.CharCore.exists_mem_irrSubmodules_of_mem_Irr hψ
  have hstar : ∀ x : G, starRingEnd ℂ (ψ x) = ψ x⁻¹ := by
    intro x
    have h := Work.CharCore.star_char (Work.CharCore.submoduleRep N) x
    rwa [hNψ] at h
  -- hence `cfInner χ ψ` is the bilinear pairing `charPair χ ψ`, whose orthonormality is proved
  -- directly from Mathlib's `Representation.char_orthonormal`.
  have h1 : Work.CharCore.cfInner χ ψ = Work.Clifford.charPair χ ψ := by
    have hsum : (∑ x : G, χ x * starRingEnd ℂ (ψ x)) = ∑ x : G, χ x * ψ x⁻¹ :=
      Finset.sum_congr rfl fun x _ => by rw [hstar x]
    rw [Work.CharCore.cfInner_apply, Work.Clifford.charPair_apply, Fintype.card_eq_nat_card, hsum]
  rw [h1]
  exact Work.Clifford.charPair_eq_ite_of_mem_Irr hχ hψ

end Work.Induction
