import Mathlib
import Submission.Work.CharCore.IrrDegreeAux

-- ftport:v435-opts-begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- ftport:v435-opts-end

/-!
# `|G| / dim N = ω_N` for a simple `ℂ[G]`-module `N`

The weighted sum `omegaSum N hN = ∑_C ω_C χ(g_C⁻¹)` of the central characters of the class
sums against the character values at the class representatives is the analytic integer attached
to the simple module `N`.  Here we compute it: it equals `|G| / dim N`, the quotient of the
group order by the degree of `N`.

The proof combines

* `centralChar_classSum_mul_finrank`: `ω_C * dim N = |C| * χ(g_C)`;
* `IsClassFun.sum_eq_sum_conjClasses`: decomposition of a sum over `G` into a sum over
  conjugacy classes for the class function `g ↦ χ g * χ g⁻¹`;
* `sum_char_mul_char_inv_eq_card`: `∑_g χ g * χ g⁻¹ = |G|`.
-/

set_option linter.unusedSectionVars false

noncomputable section

open Classical

namespace Work.CharCore

variable {G : Type*} [Group G] [Fintype G]

/-- The pointwise inverse of a class function is a class function. -/
private theorem isClassFun_comp_inv {χ : G → ℂ} (hχ : IsClassFun χ) :
    IsClassFun (fun g : G => χ g⁻¹) := by
  intro g h
  show χ (h * g * h⁻¹)⁻¹ = χ g⁻¹
  rw [show (h * g * h⁻¹)⁻¹ = h * g⁻¹ * h⁻¹ from by group]
  exact hχ g⁻¹ h

/-- The sum of `|C| χ(g_C) χ(g_C⁻¹)` over the conjugacy classes is `|G|`. -/
private theorem sum_card_conjClass_mul_char_mul_char_inv
    (N : Submodule (groupAlgebra G) (groupAlgebra G))
    (hN : IsSimpleModule (groupAlgebra G) N) :
    (∑ C : ConjClasses G,
        (Fintype.card C.carrier : ℂ) *
          ((submoduleRep N).character (rep C) * (submoduleRep N).character (rep C)⁻¹))
      = (Nat.card G : ℂ) := by
  have hcl : IsClassFun (fun g : G =>
      (submoduleRep N).character g * (submoduleRep N).character g⁻¹) :=
    (isClassFun_character (submoduleRep N)).mul
      (isClassFun_comp_inv (isClassFun_character (submoduleRep N)))
  rw [← IsClassFun.sum_eq_sum_conjClasses hcl]
  exact sum_char_mul_char_inv_eq_card N hN

theorem card_div_finrank_eq_omegaSum {G : Type*} [Group G] [Fintype G]
    (N : Submodule (Work.CharCore.groupAlgebra G) (Work.CharCore.groupAlgebra G))
    (hN : IsSimpleModule (Work.CharCore.groupAlgebra G) N) :
    (Nat.card G : ℂ) / (Module.finrank ℂ N : ℂ) = Work.CharCore.omegaSum N hN := by
  have hnt : Nontrivial N := IsSimpleModule.nontrivial (groupAlgebra G) N
  have hdpos : 0 < Module.finrank ℂ N := Module.finrank_pos_iff.mpr hnt
  have hd : (Module.finrank ℂ N : ℂ) ≠ 0 := by
    exact_mod_cast Nat.pos_iff_ne_zero.mp hdpos
  rw [div_eq_iff hd]
  have key : omegaSum N hN * (Module.finrank ℂ N : ℂ) = (Nat.card G : ℂ) := by
    rw [omegaSum, Finset.sum_mul]
    trans ∑ C : ConjClasses G,
        (Fintype.card C.carrier : ℂ) *
          ((submoduleRep N).character (rep C) * (submoduleRep N).character (rep C)⁻¹)
    · refine Finset.sum_congr rfl fun C _ => ?_
      rw [show (centralChar N hN ⟨conjClassSum C, classSum_mem_center C⟩ *
            (submoduleRep N).character (rep C)⁻¹) * (Module.finrank ℂ N : ℂ)
          = (centralChar N hN ⟨conjClassSum C, classSum_mem_center C⟩ *
              (Module.finrank ℂ N : ℂ)) * (submoduleRep N).character (rep C)⁻¹ from by ring,
        centralChar_classSum_mul_finrank N hN C]
      ring
    · exact sum_card_conjClass_mul_char_mul_char_inv N hN
  rw [key]

end Work.CharCore
