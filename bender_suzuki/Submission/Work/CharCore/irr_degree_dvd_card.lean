import Mathlib
import Submission.Work.CharCore.Basic
import Submission.Work.CharCore.IrrDegreeAux
import Submission.Work.CharCore.card_div_finrank_eq_omegaSum
import Submission.Work.CharCore.dvd_of_isIntegral_rat

-- ftport:v435-opts-begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- ftport:v435-opts-end

namespace Work.CharCore

noncomputable section

open Classical

variable {G : Type*} [Group G] [Fintype G]

/-- The sum `∑_C ω_C χ(g_C⁻¹)` is an algebraic integer: it is a sum of products of algebraic
integers. -/
theorem isIntegral_omegaSum (N : Submodule (groupAlgebra G) (groupAlgebra G))
    (hN : IsSimpleModule (groupAlgebra G) N) : IsIntegral ℤ (omegaSum N hN) := by
  rw [omegaSum]
  refine IsIntegral.sum _ fun C _ => ?_
  exact (isIntegral_centralChar_classSum N hN C).mul
    (Representation.isIntegral_character (submoduleRep N) ((rep C)⁻¹))

end

end Work.CharCore

namespace Work.CharCore

theorem irr_degree_dvd_card {G : Type*} [Group G] [Fintype G] {χ : G → ℂ} (hχ : χ ∈ Irr G) :
    irrDeg χ ∣ Nat.card G := by
  classical
  obtain ⟨N, hNmem, hNχ⟩ := exists_mem_irrSubmodules_of_mem_Irr hχ
  have hN : IsSimpleModule (groupAlgebra G) N := isSimpleModule_of_mem_irrSubmodules N hNmem
  have hdeg : irrDeg χ = Module.finrank ℂ N := irrDeg_eq_finrank hχ hNmem hNχ
  rw [hdeg]
  set d : ℕ := Module.finrank ℂ N with hd
  have hkey : (Nat.card G : ℂ) / (d : ℂ) = omegaSum N hN := by
    rw [hd]
    exact card_div_finrank_eq_omegaSum N hN
  have hintC : IsIntegral ℤ ((Nat.card G : ℂ) / (d : ℂ)) := by
    rw [hkey]
    exact isIntegral_omegaSum N hN
  have hrat : IsIntegral ℤ ((Nat.card G : ℚ) / (d : ℚ)) := by
    rw [← isIntegral_algebraMap_iff (R := ℤ) (A := ℚ) (B := ℂ)
      (x := (Nat.card G : ℚ) / (d : ℚ))]
    convert hintC using 1
    push_cast
    ring
  have hdpos : 0 < d := by
    rw [hd]
    exact Module.finrank_pos_iff.mpr (IsSimpleModule.nontrivial (groupAlgebra G) N)
  exact dvd_of_isIntegral_rat hdpos hrat

end Work.CharCore
