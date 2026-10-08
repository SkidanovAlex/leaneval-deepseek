import Mathlib
import Submission.Work.Clifford.CFun
import Submission.Work.Clifford.char_mem_Irr_of_isSimpleModule
import Submission.Work.CharCore.classFun_eq_zero_of_orthogonal

-- ftport:v435-opts-begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- ftport:v435-opts-end

/-!
# `Work.Clifford.classFun_eq_zero_of_orthogonal`

A class function on a finite group which is orthogonal (for the normalised character inner
product `cfInner`) to every irreducible complex character is zero.

The character-theoretic input is isolated in the companion module
`Submission.Work.Clifford.char_mem_Irr_of_isSimpleModule`: the character of a simple finite
dimensional `ℂ[G]`-module lies in `Work.Clifford.Irr G` (the set of characters of simple
finite dimensional complex representations of `G`).  With that at hand the statement is a
formal consequence of the (equivalent, but phrased with the finite family of simple submodules
of the regular module) result `Work.CharCore.classFun_eq_zero_of_orthogonal`: the two
character sets have the same elements.
-/

noncomputable section

open Classical Finset

namespace Work.Clifford

variable {G : Type*} [Group G] [Fintype G]

/-- Every element of the `Work.CharCore.Irr` family (the characters of the chosen simple
submodules of the regular module) is an irreducible complex character in the sense of
`Work.Clifford.Irr`. -/
theorem charCore_mem_Irr_subset (χ : G → ℂ) (hχ : χ ∈ Work.CharCore.Irr G) : χ ∈ Irr G := by
  obtain ⟨N, hN, hχeq⟩ := (Work.CharCore.mem_Irr_iff_exists χ).mp hχ
  rw [← hχeq]
  haveI := Work.CharCore.isSimpleModule_of_mem_irrSubmodules N hN
  exact char_mem_Irr_of_isSimpleModule N

/-- A class function on a finite group which is orthogonal to every irreducible complex
character is zero. -/
theorem classFun_eq_zero_of_orthogonal {G : Type*} [Group G] [Fintype G] {f : G → ℂ}
    (hf : Work.Clifford.IsClassFun f)
    (h : ∀ χ : G → ℂ, χ ∈ Work.Clifford.Irr G → Work.Clifford.cfInner f χ = 0) : f = 0 := by
  exact Work.CharCore.classFun_eq_zero_of_orthogonal hf
    (fun χ hχ => h χ (charCore_mem_Irr_subset χ hχ))

end Work.Clifford
