import Mathlib
import Submission.Work.CharCore.Basic
import Submission.Work.CharCore.irr_orthonormal
import Submission.Work.CharCore.classFun_eq_sum_irr

-- ftport:v435-opts-begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- ftport:v435-opts-end

/-!
# The dimension of the space of class functions is the number of irreducible characters

The irreducible complex characters `Work.CharCore.Irr G` of a finite group `G` are
(a) linearly independent and (b) span the space of class functions: every class function
`f` is `∑_χ ⟨f, χ⟩ • χ` by `Work.CharCore.classFun_eq_sum_irr`, and conversely every
`χ ∈ Irr G` is a class function.  Hence `classFunSubmodule G` is the span of `Irr G`, and
its dimension over `ℂ` is the cardinality of `Irr G`.

Linear independence is immediate from the orthonormality of `Irr G`
(`Work.CharCore.irr_orthonormal`): applying `⟨-, ψ⟩` to a vanishing linear combination
collapses the sum to the single coefficient of `ψ`.
-/

noncomputable section

open Classical

namespace Work.CharCore

variable {G : Type*} [Group G] [Fintype G]

/-- The set of irreducible complex characters of `G` is linearly independent in the space
of all functions `G → ℂ`.

Indeed, if `∑ χ ∈ Irr G, c χ • χ = 0` then applying `cfInner · ψ` (for `ψ ∈ Irr G`) and
using orthonormality collapses the sum to the single term `c ψ`. -/
theorem irr_linearIndepOn :
    LinearIndepOn ℂ id ((Irr G : Finset (G → ℂ)) : Set (G → ℂ)) := by
  rw [linearIndepOn_finset_iff]
  intro c hc ψ hψ
  have h := congrArg (fun f : G → ℂ => cfInner f ψ) hc
  simp only [id_eq] at h
  rw [cfInner_sum_smul_left, cfInner_zero_left] at h
  have hsingle : (∑ χ ∈ Irr G, c χ * cfInner χ ψ) = c ψ := by
    rw [Finset.sum_eq_single ψ]
    · rw [irr_orthonormal ψ ψ hψ hψ]; simp
    · intro χ hχ hne
      rw [irr_orthonormal χ ψ hχ hψ]; simp [hne]
    · intro hnot; exact absurd hψ hnot
  rw [hsingle] at h
  exact h

/-- The space of class functions on `G` is exactly the span of the irreducible
characters: every class function is a linear combination of them by
`Work.CharCore.classFun_eq_sum_irr`, and every irreducible character is a class function. -/
theorem classFunSubmodule_eq_span_Irr :
    classFunSubmodule G = Submodule.span ℂ ((Irr G : Finset (G → ℂ)) : Set (G → ℂ)) := by
  apply le_antisymm
  · intro f hf
    rw [mem_classFunSubmodule] at hf
    rw [classFun_eq_sum_irr hf]
    exact Submodule.sum_mem _ fun χ hχ => Submodule.smul_mem _ _ (Submodule.subset_span hχ)
  · rw [Submodule.span_le]
    intro χ hχ
    rw [SetLike.mem_coe, mem_classFunSubmodule]
    exact isClassFun_of_mem_Irr hχ

/-- **The dimension of the space of class functions of a finite group is the number of
its irreducible complex characters.** -/
theorem finrank_classFun_eq_card_Irr {G : Type*} [Group G] [Fintype G] :
    Module.finrank ℂ (classFunSubmodule G) = (Irr G).card := by
  rw [classFunSubmodule_eq_span_Irr, finrank_span_finset_eq_card irr_linearIndepOn]

end Work.CharCore
