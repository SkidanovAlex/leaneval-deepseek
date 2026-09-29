import Mathlib
import Submission.Work.CDcl.xrel_defs
import Submission.Work.CDcl.xrel_linalg_span
import Submission.Work.CDcl.xrel_linalg_clearing

/-!
# Existence of a polynomial relation between five vectors in a `ℚ(x)`-span of four

`xrel_linalg` is the elementary linear-algebra step of the reduction of the pullbacks
`T k = (G^{(k)})∘y` to a single relation in `ℚ⟦x⟧`: five elements `F k ∈ ℚ((x))`, each a
`ℚ(x)`-linear combination of `P, P', Pw, Pw'` plus an additive correction `toL (d k)`, admit a
nontrivial `ℚ[x]`-coefficient combination which is itself the image of a polynomial.

The proof splits into two independent ingredients, proved in the sibling modules:

* `xrel_linalg_span` : five vectors inside the span of four vectors over a field are linearly
  dependent (`∑ k, c k • S k = 0` with `c ≠ 0`);
* `xrel_linalg_clearing` : a finite family of rational functions and one further rational
  function admit a single nonzero common multiplier `A` after which all of them become
  polynomials.

With these, the argument is immediate: the `c k • S k` relation reads
`∑ k, toL (c k) * F k = toL (∑ k, c k * d k)`, and multiplying by `A` (and using
`toL ∘ algebraMap = id`) produces the required polynomial combination.
-/

namespace Work.CDcl

/-- The coercion `ℚ[X] → ℚ(X)` is `algebraMap` (which the goal statements display as `↑`). -/
lemma coePolynomial_eq_algebraMap (p : Polynomial ℚ) :
    (p : RatFunc ℚ) = algebraMap (Polynomial ℚ) (RatFunc ℚ) p := by
  simp only [RatFunc.coePolynomial]

theorem xrel_linalg (F : Fin 5 → LF) (P P' Pw Pw' : LF) (u : Fin 5 → Fin 4 → RatFunc ℚ)
    (d : Fin 5 → RatFunc ℚ)
    (hF : ∀ k, F k = toL (u k 0) * P + toL (u k 1) * P' + toL (u k 2) * Pw + toL (u k 3) * Pw' + toL (d k)) :
    ∃ (Q : Fin 5 → Polynomial ℚ) (r : Polynomial ℚ), Q ≠ 0 ∧
      ∑ k, toL (Q k) * F k = toL r := by
  classical
  -- View `LF = ℚ((x))` as a `ℚ(x)`-vector space through the embedding `toL`.
  letI : Algebra (RatFunc ℚ) LF := toL.toAlgebra
  -- Subtract the additive correction so that `S k` lies in the `ℚ(x)`-span of `P, P', Pw, Pw'`.
  set S : Fin 5 → LF := fun k => F k - toL (d k) with hSdef
  set W : Submodule (RatFunc ℚ) LF :=
    Submodule.span (RatFunc ℚ) (Set.range ![P, P', Pw, Pw']) with hW
  have hP : P ∈ W := by rw [hW]; exact Submodule.subset_span (Set.mem_range_self (0 : Fin 4))
  have hP' : P' ∈ W := by rw [hW]; exact Submodule.subset_span (Set.mem_range_self (1 : Fin 4))
  have hPw : Pw ∈ W := by rw [hW]; exact Submodule.subset_span (Set.mem_range_self (2 : Fin 4))
  have hPw' : Pw' ∈ W := by rw [hW]; exact Submodule.subset_span (Set.mem_range_self (3 : Fin 4))
  have hmem : ∀ k, S k ∈ W := by
    intro k
    have hk : S k = F k - toL (d k) := by simp only [hSdef]
    rw [hk, hF k, add_sub_cancel_right]
    exact Submodule.add_mem W (Submodule.add_mem W (Submodule.add_mem W
      (Submodule.smul_mem W (u k 0) hP) (Submodule.smul_mem W (u k 1) hP'))
      (Submodule.smul_mem W (u k 2) hPw)) (Submodule.smul_mem W (u k 3) hPw')
  -- Five vectors in the span of four: a nontrivial `ℚ(x)`-relation.
  obtain ⟨c, hcne, hcsum⟩ := xrel_linalg_span (g := ![P, P', Pw, Pw']) S (fun k => hW ▸ hmem k)
  have hrel : ∑ k, toL (c k) * S k = 0 := by
    simpa only [RingHom.smul_toAlgebra] using hcsum
  -- Consequently `∑ k, toL (c k) * F k` is the image of a rational function.
  have hkey : ∑ k, toL (c k) * F k = toL (∑ k, c k * d k) := by
    have hFS : ∀ k, F k = S k + toL (d k) := by
      intro k
      have hk : S k = F k - toL (d k) := by simp only [hSdef]
      rw [hk]; abel
    calc ∑ k, toL (c k) * F k
        = ∑ k, (toL (c k) * S k + toL (c k) * toL (d k)) := by
            refine Finset.sum_congr rfl (fun k _ => ?_)
            rw [hFS k, mul_add]
      _ = (∑ k, toL (c k) * S k) + ∑ k, toL (c k) * toL (d k) := Finset.sum_add_distrib
      _ = ∑ k, toL (c k) * toL (d k) := by rw [hrel, zero_add]
      _ = ∑ k, toL (c k * d k) :=
            Finset.sum_congr rfl (fun k _ => (toL_mul (c k) (d k)).symm)
      _ = toL (∑ k, c k * d k) := by rw [map_sum]
  -- Clear denominators in the coefficients `c k` and in the rational function above.
  obtain ⟨A, Q, r, hAne, hQ, hr⟩ := xrel_linalg_clearing c hcne (∑ k, c k * d k)
  refine ⟨Q, r, ?_, ?_⟩
  · -- `Q ≠ 0` because `A ≠ 0` and some `c k ≠ 0`.
    intro hQ0
    obtain ⟨k, hk⟩ : ∃ k, c k ≠ 0 := by
      by_contra h
      push_neg at h
      exact hcne (funext h)
    have hQk : Q k = 0 := congr_fun hQ0 k
    exact (mul_ne_zero hAne hk) (by rw [← hQ k, hQk, map_zero])
  · calc ∑ k, toL (Q k) * F k
        = ∑ k, (toL A * toL (c k)) * F k := by
            refine Finset.sum_congr rfl (fun k _ => ?_)
            rw [coePolynomial_eq_algebraMap, hQ k, toL_mul]
      _ = toL A * ∑ k, toL (c k) * F k := by
            rw [Finset.mul_sum]
            exact Finset.sum_congr rfl (fun k _ => by ring)
      _ = toL A * toL (∑ k, c k * d k) := by rw [hkey]
      _ = toL (A * (∑ k, c k * d k)) := by rw [toL_mul]
      _ = toL r := by rw [← hr, coePolynomial_eq_algebraMap]

end Work.CDcl
