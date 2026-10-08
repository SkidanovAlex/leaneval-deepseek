import Mathlib
import Submission.Work.Coherence.Defs

-- ftport:v435-opts-begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- ftport:v435-opts-end

/-!
# The degree of an irreducible character is a positive integer

For a finite group `G`, an irreducible complex character `χ` (an element of
`Work.Coherence.Irr G`, i.e. the character of a simple finite-dimensional complex
representation) takes the value `χ 1 = dim V` at the identity, the dimension of the
underlying representation `V`.  Since `V` is simple, it is a non-zero object of
`FDRep ℂ G`, so its dimension is a positive natural number.

The main point of the formalisation is to transfer "simple $\Rightarrow$ non-zero" from the
categorical setting of `FDRep ℂ G` to the underlying type of the representation, which lets us
use `Module.finrank_pos_iff`.
-/

noncomputable section

open Classical

open CategoryTheory CategoryTheory.Limits

namespace Work.Coherence

/-- A representation `V : FDRep ℂ G` whose underlying type is a subsingleton is a zero object.
Equivalently (contrapositively): a non-zero representation has a non-subsingleton underlying type.
This is what allows us to conclude that a *simple* representation has positive dimension. -/
lemma isZero_of_subsingleton_fdrep {G : Type*} [Group G] {V : FDRep ℂ G}
    (h : Subsingleton ↥V.V) : IsZero V := by
  -- The full subcategory inclusion `FGModuleCat ℂ ⥤ ModuleCat ℂ` is fully faithful, and
  -- a subsingleton module is a zero object of `ModuleCat ℂ`.
  have h1 : IsZero (V.V) :=
    IsZero.of_full_of_faithful_of_isZero (ModuleCat.isFG ℂ).ι V.V
      (ModuleCat.isZero_of_subsingleton V.V.obj)
  -- A zero object of `Action` is detected on the underlying morphism, which for `Action`
  -- is computed componentwise.
  rw [IsZero.iff_id_eq_zero]
  apply Action.hom_ext
  rw [Action.id_hom, Action.zero_hom]
  exact (IsZero.iff_id_eq_zero V.V).mp h1

theorem irr_degree_pos {G : Type*} [Group G] [Fintype G] {χ : G → ℂ} (hχ : χ ∈ Irr G) :
    ∃ n : ℕ, 0 < n ∧ χ 1 = (n : ℂ) := by
  rw [mem_Irr] at hχ
  obtain ⟨V, hV, hchar⟩ := hχ
  refine ⟨Module.finrank ℂ ↥V.V, ?_, ?_⟩
  · -- The dimension is positive because `V` is simple, hence non-zero.
    rw [Module.finrank_pos_iff, ← not_subsingleton_iff_nontrivial]
    intro hsub
    exact Simple.not_isZero V (isZero_of_subsingleton_fdrep hsub)
  · -- The character at `1` is the dimension of the representation.
    rw [← hchar]
    exact FDRep.char_one V

end Work.Coherence
