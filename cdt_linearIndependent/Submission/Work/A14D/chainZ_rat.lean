import Mathlib
import Submission.Work.A14D.chainZDefs

namespace Work.A14D

open Polynomial

/-!
# The cleared chain computes the iterated class `(dZ)^[k] (1,0)`

`chainZ k = (D_k, A_k, B_k)` is the denominator-cleared form of the recursion
`(u,v) ↦ (ρ(u' − v·R/P), ρ(u + v' − v·P'/P))` (`ρ = rhos = (X−1)²/(X²−2X)`) computing the class
of `∂_y^k` in the `P`-branch module `ℚ(X)e₀ ⊕ ℚ(X)e₁`.  The clearance is exact: the class is
`(A_k/D_k, B_k/D_k)`.

The two private lemmas below are the two components of the *one-step* clearing identity
(`dZ` versus `chainStepZ`), proved by the quotient rule `Submission.CDT.dRat_div`; the theorem is
the resulting induction on `k`.
-/

/-- First component of one cleared step: if `a = d·u` and `b = d·v` in `ℚ(X)` (with `d ≠ 0`) then
the first coordinate of `dZ (u,v)` is `A'/D'` for the cleared step `chainStepZ d a b`. -/
private lemma chainStepZ_clear_fst (d a b : Polynomial ℚ) (UV : RatFunc ℚ × RatFunc ℚ)
    (hd : algebraMap (Polynomial ℚ) (RatFunc ℚ) d ≠ 0)
    (ha : algebraMap (Polynomial ℚ) (RatFunc ℚ) a = algebraMap (Polynomial ℚ) (RatFunc ℚ) d * UV.1)
    (hb : algebraMap (Polynomial ℚ) (RatFunc ℚ) b = algebraMap (Polynomial ℚ) (RatFunc ℚ) d * UV.2) :
    algebraMap (Polynomial ℚ) (RatFunc ℚ) (chainStepZ d a b).2.1
      = algebraMap (Polynomial ℚ) (RatFunc ℚ) (chainStepZ d a b).1 * (dZ UV).1 := by
  simp only [chainStepZ]
  have hwz : algebraMap (Polynomial ℚ) (RatFunc ℚ) wXq ≠ 0 :=
    RatFunc.algebraMap_ne_zero wXq_ne_zero
  have hpz : algebraMap (Polynomial ℚ) (RatFunc ℚ) pZq ≠ 0 :=
    RatFunc.algebraMap_ne_zero pZq_ne_zero
  have hU : UV.1 = algebraMap (Polynomial ℚ) (RatFunc ℚ) a
      / algebraMap (Polynomial ℚ) (RatFunc ℚ) d := by
    rw [eq_div_iff hd, mul_comm]
    exact ha.symm
  have hV : UV.2 = algebraMap (Polynomial ℚ) (RatFunc ℚ) b
      / algebraMap (Polynomial ℚ) (RatFunc ℚ) d := by
    rw [eq_div_iff hd, mul_comm]
    exact hb.symm
  rw [dZ_fst, hU, hV, Submission.CDT.dRat_div, rhos_eq, RZQ_eq, PZQ_eq]
  simp only [map_mul, map_sub, map_pow]
  field_simp

/-- Second component of one cleared step: if `a = d·u` and `b = d·v` in `ℚ(X)` (with `d ≠ 0`) then
the second coordinate of `dZ (u,v)` is `B'/D'` for the cleared step `chainStepZ d a b`. -/
private lemma chainStepZ_clear_snd (d a b : Polynomial ℚ) (UV : RatFunc ℚ × RatFunc ℚ)
    (hd : algebraMap (Polynomial ℚ) (RatFunc ℚ) d ≠ 0)
    (ha : algebraMap (Polynomial ℚ) (RatFunc ℚ) a = algebraMap (Polynomial ℚ) (RatFunc ℚ) d * UV.1)
    (hb : algebraMap (Polynomial ℚ) (RatFunc ℚ) b = algebraMap (Polynomial ℚ) (RatFunc ℚ) d * UV.2) :
    algebraMap (Polynomial ℚ) (RatFunc ℚ) (chainStepZ d a b).2.2
      = algebraMap (Polynomial ℚ) (RatFunc ℚ) (chainStepZ d a b).1 * (dZ UV).2 := by
  simp only [chainStepZ]
  have hwz : algebraMap (Polynomial ℚ) (RatFunc ℚ) wXq ≠ 0 :=
    RatFunc.algebraMap_ne_zero wXq_ne_zero
  have hpz : algebraMap (Polynomial ℚ) (RatFunc ℚ) pZq ≠ 0 :=
    RatFunc.algebraMap_ne_zero pZq_ne_zero
  have hU : UV.1 = algebraMap (Polynomial ℚ) (RatFunc ℚ) a
      / algebraMap (Polynomial ℚ) (RatFunc ℚ) d := by
    rw [eq_div_iff hd, mul_comm]
    exact ha.symm
  have hV : UV.2 = algebraMap (Polynomial ℚ) (RatFunc ℚ) b
      / algebraMap (Polynomial ℚ) (RatFunc ℚ) d := by
    rw [eq_div_iff hd, mul_comm]
    exact hb.symm
  rw [dZ_snd, hU, hV, Submission.CDT.dRat_div, rhos_eq, PZQ'_eq, PZQ_eq]
  simp only [map_mul, map_sub, map_add, map_pow]
  field_simp
  ring

/-- The cleared chain `(D_k, A_k, B_k)` of `chainZDefs` computes the iterated class
`(dZ)^[k] (1,0)` of `∂_y^k` in the `P`-branch module `ℚ(X)e₀ ⊕ ℚ(X)e₁`. -/
theorem chainZ_rat (k : ℕ) :
    (algebraMap (Polynomial ℚ) (RatFunc ℚ) (Work.A14D.AZpoly k)
        = algebraMap (Polynomial ℚ) (RatFunc ℚ) (Work.A14D.DZpoly k)
          * ((Work.A14D.dZ^[k]) (1, 0)).1) ∧
    (algebraMap (Polynomial ℚ) (RatFunc ℚ) (Work.A14D.BZpoly k)
        = algebraMap (Polynomial ℚ) (RatFunc ℚ) (Work.A14D.DZpoly k)
          * ((Work.A14D.dZ^[k]) (1, 0)).2) := by
  have key : ∀ k : ℕ,
      (algebraMap (Polynomial ℚ) (RatFunc ℚ) (AZpoly k)
          = algebraMap (Polynomial ℚ) (RatFunc ℚ) (DZpoly k) * ((dZ^[k]) (1, 0)).1) ∧
      (algebraMap (Polynomial ℚ) (RatFunc ℚ) (BZpoly k)
          = algebraMap (Polynomial ℚ) (RatFunc ℚ) (DZpoly k) * ((dZ^[k]) (1, 0)).2) := by
    intro k
    induction k with
    | zero => simp
    | succ k ih =>
        obtain ⟨ihA, ihB⟩ := ih
        have hd : algebraMap (Polynomial ℚ) (RatFunc ℚ) (DZpoly k) ≠ 0 :=
          RatFunc.algebraMap_ne_zero (DZpoly_ne_zero k)
        have hstep := chainStepZ_clear_fst (DZpoly k) (AZpoly k) (BZpoly k) ((dZ^[k]) (1, 0))
          hd ihA ihB
        have hstep' := chainStepZ_clear_snd (DZpoly k) (AZpoly k) (BZpoly k) ((dZ^[k]) (1, 0))
          hd ihA ihB
        rw [Function.iterate_succ_apply']
        rw [show AZpoly (k + 1) = (chainStepZ (DZpoly k) (AZpoly k) (BZpoly k)).2.1 from rfl,
            show BZpoly (k + 1) = (chainStepZ (DZpoly k) (AZpoly k) (BZpoly k)).2.2 from rfl,
            show DZpoly (k + 1) = (chainStepZ (DZpoly k) (AZpoly k) (BZpoly k)).1 from rfl]
        exact ⟨hstep, hstep'⟩
  exact key k

end Work.A14D
