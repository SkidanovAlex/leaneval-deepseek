/-
Copyright (c) 2026. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Gorenstein–Walter formalisation team (area BSW, `Work.BSW`)

# Area BSW: character values at involutions are integers

Bender's §2 counting arguments (as recorded in `Work.BSW.Char.invPairCount_eq_sum_characters`)
evaluate character sums such as `∑_χ χ(t)^k / χ(1)` for an involution `t`, and treat the
individual values `χ(t)` as rational integers.  This file supplies that fact:

  `χ(t) ∈ ℤ` for every irreducible complex character `χ` of a finite group and every
  involution `t ∈ G`.

The proof is the direct eigenvalue argument.  By definition `IsIrreducibleCharacter` produces a
finite-dimensional `ℂ`-representation `ρ` with `χ = ρ.character`; `t * t = 1` gives
`(ρ t) * (ρ t) = 1`, so `ρ t` is annihilated by the squarefree polynomial `X ^ 2 - 1`.  Its
characteristic polynomial splits over `ℂ` and the trace is the sum of its roots, each of which
satisfies `μ ^ 2 = 1`, i.e. `μ = ±1`; a sum of `±1`'s is an integer.
-/
import Mathlib
import Submission.Work.BSW.Char.Setup

namespace Work.BSW.Char

/-- A multiset of complex numbers all of whose elements are `1` or `-1` has an integral sum. -/
theorem exists_int_of_multiset_sum_pm_one (m : Multiset ℂ)
    (hm : ∀ μ ∈ m, μ = 1 ∨ μ = -1) : ∃ n : ℤ, m.sum = (n : ℂ) := by
  induction m using Multiset.induction with
  | empty => exact ⟨0, by simp⟩
  | cons a s ih =>
      have ha : a = 1 ∨ a = -1 := hm a (Multiset.mem_cons_self a s)
      have hs : ∀ μ ∈ s, μ = 1 ∨ μ = -1 := fun μ hμ => hm μ (Multiset.mem_cons_of_mem hμ)
      obtain ⟨n, hn⟩ := ih hs
      rcases ha with rfl | rfl
      · exact ⟨n + 1, by rw [Multiset.sum_cons, hn]; push_cast; ring⟩
      · exact ⟨n - 1, by rw [Multiset.sum_cons, hn]; push_cast; ring⟩

/-- **The trace of an involetive endomorphism is an integer.**  If `T : End ℂ V` is a
finite-dimensional complex endomorphism with `T * T = 1`, then `trace T ∈ ℤ`: the eigenvalues of
`T` all satisfy `μ ^ 2 = 1`, hence are `±1`, and the trace is their sum. -/
theorem exists_int_trace_of_mul_self_eq_one {V : Type} [AddCommGroup V] [Module ℂ V]
    [FiniteDimensional ℂ V] (T : Module.End ℂ V) (hT : T * T = 1) :
    ∃ n : ℤ, LinearMap.trace ℂ V T = (n : ℂ) := by
  have hsplit : T.charpoly.Splits := IsAlgClosed.splits _
  rw [Module.End.trace_eq_sum_roots_charpoly_of_splits hsplit]
  refine exists_int_of_multiset_sum_pm_one _ (fun μ hμ => ?_)
  -- `T` is annihilated by `X ^ 2 - 1`, so every eigenvalue `μ` satisfies `μ ^ 2 = 1`.
  have hpow : T ^ 2 = 1 := by rw [pow_two]; exact hT
  have hroot : T.charpoly.IsRoot μ := (Polynomial.mem_roots T.charpoly_monic.ne_zero).mp hμ
  have h2 : μ ^ 2 = 1 :=
    OddOrder.RepresentationTheory.pow_eq_one_of_isRoot_charpoly_of_pow_eq_one hpow hroot
  -- `μ ^ 2 = 1` in the domain `ℂ` forces `μ = 1` or `μ = -1`.
  rcases mul_eq_zero.mp (show (μ - 1) * (μ + 1) = 0 from by
      have hh : (μ - 1) * (μ + 1) = μ ^ 2 - 1 := by ring
      rw [hh, h2]; ring) with h3 | h3
  · exact Or.inl (sub_eq_zero.mp h3)
  · exact Or.inr (by linear_combination h3)

theorem chi_t_eq_int {G : Type} [Group G] [Fintype G] (t : G) (ht : orderOf t = 2)
    (χ : OddOrder.RepresentationTheory.IrreducibleCharacter G) :
    ∃ n : ℤ, (χ : OddOrder.RepresentationTheory.ClassFunction G ℂ) t = (n : ℂ) := by
  -- Realise `χ` as the character of a finite-dimensional complex representation `ρ`.
  obtain ⟨V, _, _, _, ρ, _, hχ⟩ := χ.isIrreducible
  -- `t` is an involution, so `ρ t` is too, and its trace is an integer.
  have ht2 : t * t = 1 := by
    have h : t ^ orderOf t = 1 := pow_orderOf_eq_one t
    rw [ht] at h
    simpa [pow_two] using h
  have hT : ρ t * ρ t = 1 := by
    rw [← map_mul, ht2, map_one]
  obtain ⟨n, hn⟩ := exists_int_trace_of_mul_self_eq_one (ρ t) hT
  exact ⟨n, by
    have h1 : (χ : OddOrder.RepresentationTheory.ClassFunction G ℂ) t = ρ.character t :=
      congrFun hχ t
    rw [h1]
    simpa [Representation.character] using hn⟩

end Work.BSW.Char
