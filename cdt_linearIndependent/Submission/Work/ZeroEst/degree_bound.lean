import Mathlib
import Submission.Work.ZeroEst.defs

/-!
# A uniform degree bound on a finite-dimensional space of polynomial tuples

If `V ⊆ ℚ[X]^n` is a finite-dimensional `ℚ`-subspace, then the degrees occurring in each
coordinate of the elements of `V` are bounded by a single constant `N`.

This is the elementary linear-algebra input behind the usual "jumps" / degree-filtration
arguments: a finite-dimensional space of polynomials cannot contain polynomials of
arbitrarily large degree.

The proof is the direct one: pick a finite spanning set `S` of `V` (`Module.Finite.fg_top`,
via `FiniteDimensional ℚ V`). Each spanning vector is a tuple of polynomials, so
`N := sup_{x ∈ S} sup_j natDegree (x j)` is finite. The set `T` of vectors of `V` whose every
coordinate has degree `≤ N` is a `ℚ`-submodule of `V` (closed under `0`, `+` and scalar
multiplication by `Polynomial.degree_zero`, `Polynomial.degree_add_le` and
`Polynomial.degree_smul_le`), and it contains `S`; since `V = span S`, it is all of `V`.
-/

namespace Work.ZeroEst

theorem degree_bound {n : ℕ} (V : Submodule ℚ (Fin n →₀ Polynomial ℚ))
    [FiniteDimensional ℚ V] :
    ∃ N : ℕ, ∀ v : Fin n →₀ Polynomial ℚ, v ∈ V → ∀ j : Fin n,
      (v j).degree ≤ (N : WithBot ℕ) := by
  classical
  -- A finite spanning set of the finite-dimensional space `V`.
  obtain ⟨S, hS⟩ := Module.Finite.fg_top (R := ℚ) (M := V)
  -- The candidate bound: the largest `natDegree` of a coordinate of a spanning vector.
  let N : ℕ := S.sup (fun x => (Finset.univ : Finset (Fin n)).sup
    (fun j => (((x : V) : (Fin n →₀ Polynomial ℚ)) j).natDegree))
  refine ⟨N, ?_⟩
  intro v hv j
  -- The submodule of `V` consisting of vectors all of whose coordinates have degree `≤ N`.
  let T : Submodule ℚ V :=
    { carrier := {w : V | ∀ j : Fin n,
        (((w : V) : (Fin n →₀ Polynomial ℚ)) j).degree ≤ (N : WithBot ℕ)}
      zero_mem' := by
        intro j
        rw [Submodule.coe_zero, Finsupp.zero_apply, Polynomial.degree_zero]
        exact bot_le
      add_mem' := by
        intro a b ha hb j
        rw [Submodule.coe_add, Finsupp.add_apply]
        exact le_trans (Polynomial.degree_add_le _ _) (max_le (ha j) (hb j))
      smul_mem' := by
        intro c a ha j
        rw [Submodule.coe_smul, Finsupp.smul_apply]
        exact le_trans (Polynomial.degree_smul_le c _) (ha j) }
  -- Every spanning vector lies in `T`, by definition of `N`.
  have hST : (S : Set V) ⊆ T := by
    intro x hx j
    refine le_trans Polynomial.degree_le_natDegree ?_
    apply WithBot.coe_le_coe.mpr
    exact le_trans
      (Finset.le_sup (s := Finset.univ) (f := fun j =>
          (((x : V) : (Fin n →₀ Polynomial ℚ)) j).natDegree) (Finset.mem_univ j))
      (Finset.le_sup (s := S) (f := fun x => (Finset.univ : Finset (Fin n)).sup
          (fun j => (((x : V) : (Fin n →₀ Polynomial ℚ)) j).natDegree)) hx)
  -- Hence `T` contains `V = span S`.
  have htop : (⊤ : Submodule ℚ V) ≤ T := by
    rw [← hS]
    exact Submodule.span_le.mpr hST
  have hmem : (⟨v, hv⟩ : V) ∈ T := htop Submodule.mem_top
  exact hmem j

end Work.ZeroEst
