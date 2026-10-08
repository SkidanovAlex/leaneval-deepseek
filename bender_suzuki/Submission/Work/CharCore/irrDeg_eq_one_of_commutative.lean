import Mathlib
import Submission.Work.CharCore.Basic

-- ftport:v435-opts-begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- ftport:v435-opts-end

/-!
# Degrees of irreducible characters of a commutative group

Every irreducible complex character of a finite commutative group has degree `1`.

The proof is the standard one: an irreducible character `χ` is the character of a simple
submodule `N` of the regular module `ℂ[G]`, and `irrDeg χ = finrank ℂ N`.  Since `G` is
commutative the group algebra `ℂ[G]` is commutative, and over an algebraically closed field
any finite-dimensional simple module of a commutative algebra is one-dimensional
(`IsSimpleModule.finrank_eq_one_of_isMulCommutative`).
-/

noncomputable section

open scoped IsMulCommutative

namespace Work.CharCore

theorem irrDeg_eq_one_of_commutative {G : Type*} [Group G] [Fintype G] [IsMulCommutative G]
    {χ : G → ℂ} (hχ : χ ∈ Irr G) : irrDeg χ = 1 := by
  obtain ⟨N, hN, hNχ⟩ := exists_mem_irrSubmodules_of_mem_Irr hχ
  have hS : IsSimpleModule (groupAlgebra G) N := isSimpleModule_of_mem_irrSubmodules N hN
  have hcomm : IsMulCommutative (groupAlgebra G) :=
    IsMulCommutative.of_comm fun a b => mul_comm a b
  rw [irrDeg_eq_finrank hχ hN hNχ]
  exact IsSimpleModule.finrank_eq_one_of_isMulCommutative (groupAlgebra G) N ℂ

end Work.CharCore
