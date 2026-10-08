import Mathlib
import Submission.Work.CharCore.Basic
import Submission.Work.CharCore.isChar_character
import Submission.Work.CharCore.mem_Irr_iff_fdrep

-- ftport:v435-opts-begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- ftport:v435-opts-end

/-!
# `Work.CharCore.isVChar_mul`

Virtual characters are closed under pointwise multiplication.

The mathematical content is that the product of two *irreducible* characters is a genuine
character (hence a virtual one): if `χ` and `ψ` are the characters of the simple representations
`V` and `W`, then `χ * ψ` is the character of the tensor product `V ⊗ W` (`FDRep.char_tensor`),
which is a finite dimensional representation, so its character is a character
(`Work.CharCore.isChar_character`).

The passage from "irreducible times irreducible" to "virtual times virtual" is by additivity:
for a fixed `χ ∈ Irr G`, the set `{g | IsVChar (χ * g)}` is an additive subgroup of `G → ℂ`
containing `Irr G`, hence contains `IsVChar`; iterating the same argument in the second
variable gives the general statement.
-/

noncomputable section

open Classical
open CategoryTheory MonoidalCategory

namespace Work.CharCore

variable {G : Type*} [Group G] [Fintype G]

/-- The product of two irreducible characters is a virtual character: it is the character of
the tensor product of the corresponding simple representations. -/
theorem isVChar_mul_mem_Irr {χ ψ : G → ℂ} (hχ : χ ∈ Irr G) (hψ : ψ ∈ Irr G) :
    IsVChar (χ * ψ) := by
  obtain ⟨V, _hV, hVchar⟩ := (mem_Irr_iff_fdrep χ).mp hχ
  obtain ⟨W, _hW, hWchar⟩ := (mem_Irr_iff_fdrep ψ).mp hψ
  have hchar : ((V ⊗ W).character : G → ℂ) = Representation.character ((V ⊗ W).ρ) := rfl
  rw [← hVchar, ← hWchar, ← FDRep.char_tensor, hchar]
  exact IsChar.toVChar (isChar_character ((V ⊗ W).ρ))

/-- Multiplication on the left by a fixed irreducible character preserves virtual characters. -/
theorem isVChar_mul_of_mem_Irr_left {χ : G → ℂ} (hχ : χ ∈ Irr G) {g : G → ℂ}
    (hg : IsVChar g) : IsVChar (χ * g) := by
  induction hg using AddSubgroup.closure_induction with
  | mem y hy => exact isVChar_mul_mem_Irr hχ hy
  | zero => rw [mul_zero]; exact IsVChar.zero
  | add a b _ _ iha ihb => rw [mul_add]; exact iha.add ihb
  | neg a _ iha => rw [mul_neg]; exact iha.neg

theorem isVChar_mul {G : Type*} [Group G] [Fintype G] {f g : G → ℂ} (hf : IsVChar f)
    (hg : IsVChar g) : IsVChar (f * g) := by
  induction hg using AddSubgroup.closure_induction with
  | mem y hy => rw [mul_comm]; exact isVChar_mul_of_mem_Irr_left hy hf
  | zero => rw [mul_zero]; exact IsVChar.zero
  | add a b _ _ iha ihb => rw [mul_add]; exact iha.add ihb
  | neg a _ iha => rw [mul_neg]; exact iha.neg

end Work.CharCore
