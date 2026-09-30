import Mathlib
import Submission.Work.Pi6.EMM2.K4Kit
set_option backward.isDefEq.respectTransparency false  -- v435port
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false  -- v435port
set_option backward.isDefEq.respectTransparency.types false  -- v435port

namespace Work.Pi6.EMM2.K4F

/-- **The row-`q = 0` bound in total degree 7.**

For a multiplicative Serre spectral sequence `S` of a Serre fibration `p : E → B` (fibre
`F = Fib p e₀`) through degree `N ≥ 8`:

* the base has `H⁰(B) = 𝕜`, `H¹(B) = H²(B) = H³(B) = 0`;
* the fibre has `H⁰(F) = 𝕜`, `H¹(F) = H²(F) = 0` and `dim H⁶(F) ≤ 2`;
* the total space has `H⁷(E) = 0`;

then `dim H⁷(B) ≤ 2`.

The telescoped dimension bound `Work.Pi6.EMM2.finrank_row0_bound` gives
`dim H⁷(B) ≤ dim H⁷(E) + Σ_{r} dim H^{7-(r+2)}(B) · dim H^{r+1}(F)` with `r` running over
`{0,…,5}`.  The total space contributes `0`; the terms `r = 0,…,4` pair a vanishing `H^{r+1}(F)`
(`r ≤ 1`) with a vanishing `H^{7-(r+2)}(B)` (`r ≥ 2`); and the term `r = 5` is
`dim H⁰(B) · dim H⁶(F) = dim H⁶(F) ≤ 2`. -/
theorem sevenBound {E B : Type} [TopologicalSpace E] [TopologicalSpace B] (p : C(E, B))
    (e₀ : E) (N : ℕ) (S : Work.Pi6.CohSS (ZMod 2)) (hS : Work.Pi6.IsSerreMSS S p e₀ N)
    (hN : 8 ≤ N)
    (hBfin : ∀ s : ℕ, s ≤ N → FiniteDimensional (ZMod 2) (Work.Pi6.Coh (ZMod 2) B s))
    (hFfin : ∀ q : ℕ, q ≤ N →
      FiniteDimensional (ZMod 2) (Work.Pi6.Coh (ZMod 2) (Work.Pi6.EMM2.Fib p e₀) q))
    (hB0 : Module.finrank (ZMod 2) (Work.Pi6.Coh (ZMod 2) B 0) = 1)
    (hF0 : Module.finrank (ZMod 2) (Work.Pi6.Coh (ZMod 2) (Work.Pi6.EMM2.Fib p e₀) 0) = 1)
    (hB1 : CategoryTheory.Limits.IsZero (Work.Pi6.Coh (ZMod 2) B 1))
    (hB2 : CategoryTheory.Limits.IsZero (Work.Pi6.Coh (ZMod 2) B 2))
    (hB3 : CategoryTheory.Limits.IsZero (Work.Pi6.Coh (ZMod 2) B 3))
    (hF1 : CategoryTheory.Limits.IsZero (Work.Pi6.Coh (ZMod 2) (Work.Pi6.EMM2.Fib p e₀) 1))
    (hF2 : CategoryTheory.Limits.IsZero (Work.Pi6.Coh (ZMod 2) (Work.Pi6.EMM2.Fib p e₀) 2))
    (hF6 : Module.finrank (ZMod 2) (Work.Pi6.Coh (ZMod 2) (Work.Pi6.EMM2.Fib p e₀) 6) ≤ 2)
    (hE7 : CategoryTheory.Limits.IsZero (Work.Pi6.Coh (ZMod 2) E 7)) :
    Module.finrank (ZMod 2) (Work.Pi6.Coh (ZMod 2) B 7) ≤ 2 := by
  have key := Work.Pi6.EMM2.finrank_row0_bound S p e₀ N hS hBfin hFfin hF0 7 (by omega)
  have hE : Module.finrank (ZMod 2) (Work.Pi6.Coh (ZMod 2) E 7) = 0 :=
    Work.Pi6.EMM2.k4_finrank_eq_zero_of_isZero_cohom hE7
  have hz1 : Module.finrank (ZMod 2) (Work.Pi6.Coh (ZMod 2) B 1) = 0 :=
    Work.Pi6.EMM2.k4_finrank_eq_zero_of_isZero_cohom hB1
  have hz2 : Module.finrank (ZMod 2) (Work.Pi6.Coh (ZMod 2) B 2) = 0 :=
    Work.Pi6.EMM2.k4_finrank_eq_zero_of_isZero_cohom hB2
  have hz3 : Module.finrank (ZMod 2) (Work.Pi6.Coh (ZMod 2) B 3) = 0 :=
    Work.Pi6.EMM2.k4_finrank_eq_zero_of_isZero_cohom hB3
  have hw1 : Module.finrank (ZMod 2) (Work.Pi6.Coh (ZMod 2) (Work.Pi6.EMM2.Fib p e₀) 1) = 0 :=
    Work.Pi6.EMM2.k4_finrank_eq_zero_of_isZero_cohom hF1
  have hw2 : Module.finrank (ZMod 2) (Work.Pi6.Coh (ZMod 2) (Work.Pi6.EMM2.Fib p e₀) 2) = 0 :=
    Work.Pi6.EMM2.k4_finrank_eq_zero_of_isZero_cohom hF2
  have hsum : (∑ r ∈ Finset.range (7 - 1),
      Module.finrank (ZMod 2) (Work.Pi6.Coh (ZMod 2) B (7 - (r + 2))) *
        Module.finrank (ZMod 2)
          (Work.Pi6.Coh (ZMod 2) (Work.Pi6.EMM2.Fib p e₀) (r + 1))) ≤ 2 := by
    rw [show (7 : ℕ) - 1 = 6 from rfl]
    rw [show (6 : ℕ) = 5 + 1 from rfl, Finset.sum_range_succ]
    have hzero : (∑ r ∈ Finset.range 5,
        Module.finrank (ZMod 2) (Work.Pi6.Coh (ZMod 2) B (7 - (r + 2))) *
          Module.finrank (ZMod 2)
            (Work.Pi6.Coh (ZMod 2) (Work.Pi6.EMM2.Fib p e₀) (r + 1))) = 0 := by
      apply Finset.sum_eq_zero
      intro r hr
      rw [Finset.mem_range] at hr
      rcases Nat.lt_or_ge r 2 with h2 | h2
      · interval_cases r
        · simp [hw1]
        · simp [hw2]
      · interval_cases r
        · simp [hz3]
        · simp [hz2]
        · simp [hz1]
    rw [hzero, zero_add]
    rw [hB0, one_mul]
    exact hF6
  linarith

end Work.Pi6.EMM2.K4F
