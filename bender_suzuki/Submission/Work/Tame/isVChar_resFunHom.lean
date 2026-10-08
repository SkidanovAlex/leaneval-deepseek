import Mathlib
import Submission.Work.Tame.Defs

-- ftport:v435-opts-begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- ftport:v435-opts-end

namespace Work.Tame

open Classical

/-- Pullback of a virtual character along a group homomorphism: if `f` is a generalized
character of `X` and `φ : H →* X`, then `f ∘ φ` is a generalized character of `H`.  Needed for
`isVChar_tau` (Feit–Thompson, after (9.4)). -/
theorem isVChar_resFunHom {X : Type*} [Group X] [Fintype X] {H : Type*} [Group H] [Fintype H]
    (φ : H →* X) {f : X → ℂ} (hf : CharCore.IsVChar f) :
    CharCore.IsVChar (Induction.resFunHom φ f) := by
  classical
  -- An irreducible character of `X` pulls back to a virtual character of `H`: it is the
  -- character of a simple submodule of `ℂ[X]`, and composing that representation with `φ`
  -- gives a genuine representation of `H` whose character is the pullback; characters of
  -- representations are virtual characters (`CharCore.isChar_character`).
  have hχV : ∀ χ : X → ℂ, χ ∈ CharCore.Irr X →
      CharCore.IsVChar (Induction.resFunHom φ χ) := by
    intro χ hχ
    obtain ⟨N, _hN, hNχ⟩ := CharCore.exists_mem_irrSubmodules_of_mem_Irr hχ
    rw [← hNχ]
    have key : Induction.resFunHom φ (CharCore.submoduleRep N).character
        = (show Representation ℂ H ↥N from (CharCore.submoduleRep N).comp φ).character := rfl
    rw [key]
    exact CharCore.IsChar.toVChar (CharCore.isChar_character _)
  -- The set of `ψ` whose pullback is a virtual character is an additive subgroup of `X → ℂ`
  -- containing `Irr X`, hence contains the closure of `Irr X`.
  let T : AddSubgroup (X → ℂ) :=
    { carrier := {ψ | CharCore.IsVChar (Induction.resFunHom φ ψ)}
      zero_mem' := by
        change CharCore.IsVChar (Induction.resFunHom φ 0)
        rw [Induction.resFunHom_zero]; exact CharCore.IsVChar.zero
      add_mem' := by
        intro f g hf hg
        change CharCore.IsVChar (Induction.resFunHom φ (f + g))
        rw [Induction.resFunHom_add]; exact CharCore.IsVChar.add hf hg
      neg_mem' := by
        intro f hf
        change CharCore.IsVChar (Induction.resFunHom φ (-f))
        rw [Induction.resFunHom_neg]; exact CharCore.IsVChar.neg hf }
  have hle : AddSubgroup.closure ((CharCore.Irr X : Finset (X → ℂ)) : Set (X → ℂ)) ≤ T := by
    rw [AddSubgroup.closure_le]
    intro χ hχ
    exact hχV χ hχ
  exact hle hf

end Work.Tame
