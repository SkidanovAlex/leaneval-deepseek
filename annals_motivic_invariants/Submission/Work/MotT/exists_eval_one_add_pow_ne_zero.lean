import Mathlib
import Submission.Work.MotT.valAux

set_option linter.unusedVariables false -- v435-speed

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

/-!
# `P (1 + π^m) ≠ 0` for all sufficiently large `m`

Let `K` be a field carrying a valuation `v : K → WithZero (Multiplicative ℤ)` (so that the value
group is `ℤ`) and let `π` be a uniformizer, `v π = vOne`, where `vOne = ofAdd (-1)` is the
normalized "order one" element of `ℤᵐ⁰` (`Work.MotT.vOne`; see `Submission/Work/MotT/Defs.lean`).

Then for every nonzero polynomial `P ∈ K[X]` we have `P (1 + π^m) ≠ 0` for all sufficiently
large `m`.

The mathematics is one line: the elements `1 + π^m` are pairwise distinct, because `π` is not a
root of unity (`v (π^k) = vOne^k ≠ 1 = v 1` for `k > 0`), while a nonzero polynomial has only
finitely many roots.  Hence the set of *bad* exponents `m` is finite, and therefore bounded.

This is the "generic point" input of node T7 (`Work.MotT.exists_kleinData_val`): a Klein model is
cut out by Pfaffian equations `P = 0`, and avoiding `1 + π^m` for large `m` produces Klein
parameters `u = 1 + π^m` that are units (cf. `Work.MotT.v_one_add_pow_pi`).
-/

namespace Work.MotT

/-- **Powers of a uniformizer are pairwise distinct.**  If `v π = vOne` then `m ↦ π ^ m` is
injective: if `π ^ m = π ^ n` with `m ≤ n`, then `π ^ (n - m) = 1` (as `π ≠ 0`), while
`v (π ^ (n - m)) = vOne ^ (n - m) = ofAdd (-(n - m)) ≠ 1 = v 1` as soon as `n - m ≠ 0`. -/
theorem pow_injective_of_v_eq_vOne {K : Type} [Field K]
    (v : Valuation K (WithZero (Multiplicative ℤ))) {π : K} (hπ : v π = vOne) :
    Function.Injective (fun m : ℕ => π ^ m) := by
  have hvOne_ne_zero : vOne ≠ (0 : WithZero (Multiplicative ℤ)) := by
    rw [vOne]; exact WithZero.coe_ne_zero
  have hπ_ne : π ≠ 0 := by
    rw [← Valuation.ne_zero_iff v, hπ]; exact hvOne_ne_zero
  intro m n h
  change π ^ m = π ^ n at h
  rcases le_total m n with hmn | hmn
  · have hn : n = m + (n - m) := (Nat.add_sub_cancel' hmn).symm
    rw [hn, pow_add] at h
    have h1 : π ^ (n - m) = 1 := by
      refine mul_left_cancel₀ (pow_ne_zero m hπ_ne) ?_
      simpa using h.symm
    rcases Nat.eq_zero_or_pos (n - m) with h0 | hpos
    · omega
    · exfalso
      have hval : v (π ^ (n - m)) = vOne ^ (n - m) := by rw [Valuation.map_pow, hπ]
      rw [h1, Valuation.map_one] at hval
      have hlt := vOne_pow_lt_one (m := n - m) hpos
      rw [← hval] at hlt
      exact absurd hlt (lt_irrefl 1)
  · have hm : m = n + (m - n) := (Nat.add_sub_cancel' hmn).symm
    rw [hm, pow_add] at h
    have h1 : π ^ (m - n) = 1 := by
      refine mul_left_cancel₀ (pow_ne_zero n hπ_ne) ?_
      simpa using h
    rcases Nat.eq_zero_or_pos (m - n) with h0 | hpos
    · omega
    · exfalso
      have hval : v (π ^ (m - n)) = vOne ^ (m - n) := by rw [Valuation.map_pow, hπ]
      rw [h1, Valuation.map_one] at hval
      have hlt := vOne_pow_lt_one (m := m - n) hpos
      rw [← hval] at hlt
      exact absurd hlt (lt_irrefl 1)

/-- **The target lemma.**  For a nonzero polynomial `P` over a field `K` with a valuation with
value group `ℤ` and a uniformizer `π` (`v π = vOne`), one has `P (1 + π ^ m) ≠ 0` for all
sufficiently large `m`. -/
theorem exists_eval_one_add_pow_ne_zero {K : Type} [Field K]
    (v : Valuation K (WithZero (Multiplicative ℤ))) {π : K}
    (hπ : v π = Work.MotT.vOne) (P : Polynomial K) (hP : P ≠ 0) :
    ∃ M : ℕ, ∀ m : ℕ, M ≤ m → P.eval (1 + π ^ m) ≠ 0 := by
  classical
  have hinj : Function.Injective (fun m : ℕ => (1 : K) + π ^ m) :=
    fun _ _ h => pow_injective_of_v_eq_vOne v hπ (add_left_cancel h)
  -- the roots of `P` form a finite set
  have hTfin : {x : K | P.IsRoot x}.Finite := by
    refine Set.Finite.ofFinset P.roots.toFinset ?_
    intro x
    simp [Multiset.mem_toFinset, Polynomial.mem_roots hP]
  -- hence the bad exponents form a finite set (an injective preimage of a finite set)
  have hSfin : {m : ℕ | P.eval ((1 : K) + π ^ m) = 0}.Finite := by
    have h := Set.Finite.preimage (f := fun m : ℕ => (1 : K) + π ^ m)
      (s := {x : K | P.IsRoot x}) (fun _ _ _ _ hab => hinj hab) hTfin
    simpa [Polynomial.IsRoot] using h
  obtain ⟨M, hM⟩ := hSfin.bddAbove
  exact ⟨M + 1, fun m hm hzero => absurd (hM hzero) (by omega)⟩

end Work.MotT
