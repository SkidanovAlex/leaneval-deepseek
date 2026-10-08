import Mathlib
import Submission.Work.CharCore.IrrDegreeAux
import Submission.Work.CharCore.Basic

-- ftport:v435-opts-begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- ftport:v435-opts-end

/-!
# The value of `∑_{x,y ∈ C} χ (x * y)`

Let `G` be a finite group, `χ` an irreducible complex character of `G` and `C` a conjugacy class
of `G`.  Writing `C^* = ∑_{x ∈ C} x ∈ ℂ[G]` for the class sum and `g_C` for the chosen
representative of `C`, the target lemma computes

`∑_{x ∈ C} ∑_{y ∈ C} χ (x * y) = (|C| * χ g_C)^2 / χ 1`.

The proof works inside a simple `ℂ[G]`-module `N` affording `χ`.  The class sum acts on `N` as
the scalar `ω = centralChar N hN C^*` (`Work.CharCore.centralChar_spec`), so its square acts as
`ω^2`, and taking traces gives

`∑_{x,y ∈ C} χ (x * y) = tr (C^* C^*) = ω^2 · dim N = ω^2 · χ 1`.

The classical relation `Work.CharCore.centralChar_classSum_mul_finrank`
(`ω · χ 1 = |C| · χ g_C`) then identifies `ω^2 · χ 1` with `(|C| χ g_C)^2 / χ 1`, using
`χ 1 = dim N ≠ 0` for a simple module.
-/

set_option linter.style.haveILetI false

namespace Work.BrauerSuzuki.Characters

open Classical
open Work.CharCore

variable {G : Type*} [Group G] [Fintype G]

/-- The square of a class sum, expanded in the complex group algebra. -/
theorem conjClassSum_mul_self (C : ConjClasses G) :
    conjClassSum C * conjClassSum C
      = ∑ x : C.carrier, ∑ y : C.carrier,
          MonoidAlgebra.single ((x : G) * (y : G)) (1 : ℂ) := by
  rw [Work.CharCore.classSum_eq, Finset.sum_mul]
  refine Finset.sum_congr rfl fun x _ => ?_
  rw [Finset.mul_sum]
  refine Finset.sum_congr rfl fun y _ => ?_
  rw [MonoidAlgebra.single_mul_single, mul_one]

/-- A class sum acts on a simple module as the scalar given by the central character. -/
theorem lsmul_classSum_eq (N : Submodule (groupAlgebra G) (groupAlgebra G))
    (hN : IsSimpleModule (groupAlgebra G) N) (C : ConjClasses G) :
    (Algebra.lsmul ℂ ℂ N) (conjClassSum C)
      = centralChar N hN ⟨conjClassSum C, classSum_mem_center C⟩ • (1 : Module.End ℂ N) := by
  refine LinearMap.ext fun n => ?_
  rw [Algebra.lsmul_apply, LinearMap.smul_apply, Module.End.one_apply]
  exact centralChar_spec N hN ⟨conjClassSum C, classSum_mem_center C⟩ n

/-- The square of a class sum acts on a simple module as the square of the scalar. -/
theorem lsmul_classSum_sq_eq (N : Submodule (groupAlgebra G) (groupAlgebra G))
    (hN : IsSimpleModule (groupAlgebra G) N) (C : ConjClasses G) :
    (Algebra.lsmul ℂ ℂ N) (conjClassSum C * conjClassSum C)
      = (centralChar N hN ⟨conjClassSum C, classSum_mem_center C⟩) ^ 2
          • (1 : Module.End ℂ N) := by
  rw [map_mul, lsmul_classSum_eq N hN C, smul_mul_smul, mul_one, sq]

/-- The trace of the action of the square of a class sum on a simple module is the square of
the central character value times the degree. -/
theorem trace_classSum_sq_eq (N : Submodule (groupAlgebra G) (groupAlgebra G))
    (hN : IsSimpleModule (groupAlgebra G) N) (C : ConjClasses G) :
    (LinearMap.trace ℂ N) ((Algebra.lsmul ℂ ℂ N) (conjClassSum C * conjClassSum C))
      = (centralChar N hN ⟨conjClassSum C, classSum_mem_center C⟩) ^ 2
          * (Module.finrank ℂ N : ℂ) := by
  rw [lsmul_classSum_sq_eq N hN C, map_smul, LinearMap.trace_one, smul_eq_mul]

/-- The trace of the action of the square of a class sum is the double sum of the character
values `χ (x * y)` over the class. -/
theorem trace_classSum_sq_eq_sum (N : Submodule (groupAlgebra G) (groupAlgebra G))
    (C : ConjClasses G) :
    (LinearMap.trace ℂ N) ((Algebra.lsmul ℂ ℂ N) (conjClassSum C * conjClassSum C))
      = ∑ x : C.carrier, ∑ y : C.carrier, (submoduleRep N).character ((x : G) * (y : G)) := by
  rw [conjClassSum_mul_self, map_sum, map_sum]
  refine Finset.sum_congr rfl fun x _ => ?_
  rw [map_sum, map_sum]
  refine Finset.sum_congr rfl fun y _ => ?_
  rfl

theorem sum_sum_char_eq {G : Type*} [Group G] [Fintype G] {χ : G → ℂ}
    (hχ : χ ∈ Work.CharCore.Irr G) (C : ConjClasses G) :
    (∑ x : C.carrier, ∑ y : C.carrier, χ ((x : G) * (y : G)))
      = ((Nat.card C.carrier : ℂ) * χ (Work.CharCore.rep C)) ^ 2 / χ 1 := by
  obtain ⟨N, hN, hNχ⟩ := exists_mem_irrSubmodules_of_mem_Irr hχ
  haveI hNs : IsSimpleModule (groupAlgebra G) N := isSimpleModule_of_mem_irrSubmodules N hN
  have hχ1 : χ 1 = (Module.finrank ℂ N : ℂ) := by
    rw [← hNχ, Representation.char_one]
  have hsum : (∑ x : C.carrier, ∑ y : C.carrier, χ ((x : G) * (y : G)))
      = (centralChar N hNs ⟨conjClassSum C, classSum_mem_center C⟩) ^ 2
          * (Module.finrank ℂ N : ℂ) := by
    rw [← hNχ, ← trace_classSum_sq_eq_sum N C]
    exact trace_classSum_sq_eq N hNs C
  have hcf : centralChar N hNs ⟨conjClassSum C, classSum_mem_center C⟩
        * (Module.finrank ℂ N : ℂ) = (Nat.card C.carrier : ℂ) * χ (rep C) := by
    have h := centralChar_classSum_mul_finrank N hNs C
    rw [hNχ] at h
    rw [← Nat.card_eq_fintype_card] at h
    exact h
  haveI : Nontrivial N := IsSimpleModule.nontrivial (groupAlgebra G) N
  have hfr : (Module.finrank ℂ N : ℂ) ≠ 0 := by
    exact_mod_cast ne_of_gt (Module.finrank_pos (R := ℂ) (M := N))
  rw [hsum, hχ1, ← hcf]
  rw [eq_div_iff hfr]
  ring

end Work.BrauerSuzuki.Characters
