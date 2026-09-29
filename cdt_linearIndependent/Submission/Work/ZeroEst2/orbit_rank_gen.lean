import Mathlib
import Submission.Work.ZeroEst2.span_witness

/-!
# `Work.ZeroEst2.orbit_rank_gen` — the rank of a `Λ`-orbit

Let `Λ` be the `ℚ`-linear operator on coefficient vectors `Q : Fin m → ℚ[X]` given by
`(ΛQ)_i = q·Q_i' + Σ_j Q_j · A_{j i}` (the coefficient-level operator realising `θ = q·d/dx`
on combinations `Σ_i Q_i f_i`; see `Work.ZeroEst.Lam`, `Work.ZeroEst.orbit`).  This file
determines the *rank* of the orbit `W k = Λ^k W_0` of a nonzero vector `P`.

**Statement.**  For an arbitrary sequence `W : ℕ → (Fin m → ℚ[X])` with `W 0 ≠ 0` and
`W (k+1) = Λ (W k)` there is an `r` with `1 ≤ r ≤ m` such that the first `r` orbit vectors
`W 0, …, W (r-1)` are `ℚ(x)`-linearly independent and `W r` lies in their `ℚ(x)`-span.

**Proof.**  The `Λ`-recurrence is in fact irrelevant to this statement: it is a pure
finite-dimensional linear-algebra fact about the sequence `v_k := W k ⊗ 1` in the
`m`-dimensional `ℚ(x)`-vector space `ℚ(x)^m`:

* `v_0 ≠ 0` (the coefficient embedding `ℚ[X] ↪ ℚ(x)` is injective and `W 0 = P ≠ 0`), so the
  first vector is nonzero;
* `m+1` vectors of an `m`-dimensional space are dependent, so some `v_k` with `k ≤ m` lies in
  the span of the *preceding* ones (`Work.ZeroEst2.span_witness`);
* let `r` be the *least* index with `v_r ∈ span(v_0, …, v_{r-1})`.  Then `r ≤ m` (some witness
  is `≤ m`) and `r ≥ 1` (`v_0 ≠ 0` rules out `r = 0`), and for every `k < r` the vector `v_k`
  lies outside the span of its predecessors, which forces `v_0, …, v_{r-1}` to be independent
  (otherwise `Work.ZeroEst2.span_witness` applied to the prefix would produce a smaller `k` with
  `v_k ∈ span(v_0, …, v_{k-1})`, contradicting minimality of `r`).
-/

namespace Work.ZeroEst2

open Polynomial

/-- **The rank of a `Λ`-orbit.**  For any sequence `W` of coefficient vectors whose first term
`P` is nonzero and whose successive terms satisfy `W (k+1) = Λ (W k)`, the `ℚ(x)`-rank of the
orbit is attained at some index `r` with `1 ≤ r ≤ m`: the first `r` vectors are `ℚ(x)`-linearly
independent and the next one is a `ℚ(x)`-combination of them. -/
theorem orbit_rank_gen {m : ℕ} (q : Polynomial ℚ) (A : Fin m → Fin m → Polynomial ℚ)
    (P : Fin m → Polynomial ℚ) (hP : P ≠ 0) (W : ℕ → Fin m → Polynomial ℚ)
    (hW0 : W 0 = P)
    (hW : ∀ k : ℕ, W (k + 1) = fun i =>
      q * Polynomial.derivative (W k i) + ∑ j, W k j * A j i) :
    ∃ r : ℕ, 1 ≤ r ∧ r ≤ m ∧
      LinearIndependent (RatFunc ℚ)
        (fun k : Fin r => fun j => algebraMap (Polynomial ℚ) (RatFunc ℚ) (W k j)) ∧
      (fun j => algebraMap (Polynomial ℚ) (RatFunc ℚ) (W r j)) ∈
        Submodule.span (RatFunc ℚ)
          (Set.range fun k : Fin r => fun j =>
            algebraMap (Polynomial ℚ) (RatFunc ℚ) (W k j)) := by
  classical
  -- the orbit of `P` viewed in the `ℚ(x)`-vector space `ℚ(x)^m`
  let v : ℕ → (Fin m → RatFunc ℚ) := fun k j => algebraMap (Polynomial ℚ) (RatFunc ℚ) (W k j)
  -- `v 0 ≠ 0`, since the coefficient embedding `ℚ[X] ↪ ℚ(x)` is injective and `W 0 = P ≠ 0`
  have hv0 : v 0 ≠ 0 := by
    intro h
    have hall : ∀ j, W 0 j = 0 := fun j => by
      have h1 : algebraMap (Polynomial ℚ) (RatFunc ℚ) (W 0 j) = 0 := by
        have hc := congrFun h j
        simpa [v] using hc
      exact RatFunc.algebraMap_injective ℚ (by rw [map_zero]; exact h1)
    apply hP
    rw [← hW0]
    funext j
    exact hall j
  -- the predicate "`v k` lies in the span of its predecessors"
  let p : ℕ → Prop := fun k => v k ∈ Submodule.span (RatFunc ℚ) (Set.range fun i : Fin k => v i)
  -- some `k ≤ m` satisfies it: otherwise `v 0, …, v m` would be `m+1` independent vectors in an
  -- `m`-dimensional space
  have hex : ∃ k, k ≤ m ∧ p k := by
    by_contra hc
    push Not at hc
    have hLI : LinearIndependent (RatFunc ℚ) (fun i : Fin (m+1) => v i) := by
      by_contra h
      obtain ⟨k, hk, hmem⟩ := span_witness v h
      exact hc k (Nat.lt_succ_iff.mp hk) hmem
    have hcard := hLI.fintype_card_le_finrank
    simp only [Fintype.card_fin, Module.finrank_fin_fun] at hcard
    omega
  -- the least such index
  have hex' : ∃ k, p k := hex.imp (fun k hk => hk.2)
  let r := Nat.find hex'
  have hrp : p r := Nat.find_spec hex'
  have hmin : ∀ k < r, ¬ p k := fun k hk => Nat.find_min hex' hk
  have hrle : r ≤ m := by
    obtain ⟨k, hk, hpk⟩ := hex
    by_contra hcon
    exact hmin k (by omega) hpk
  have hr1 : 1 ≤ r := by
    have hne : r ≠ 0 := by
      intro h0
      have h0p : p 0 := h0 ▸ hrp
      have hz : v 0 = 0 := by
        have hh := h0p
        simp only [p] at hh
        simpa using hh
      exact hv0 hz
    omega
  refine ⟨r, hr1, hrle, ?_, ?_⟩
  · -- `v 0, …, v (r-1)` are independent: a dependence would produce a smaller witness
    by_contra h
    obtain ⟨k, hk, hmem⟩ := span_witness v h
    exact hmin k hk hmem
  · -- and `v r` lies in their span, by construction
    exact hrp

end Work.ZeroEst2
