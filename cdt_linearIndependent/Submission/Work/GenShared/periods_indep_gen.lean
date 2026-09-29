import Mathlib
import Submission.Work.GenShared.periods_defs
import Submission.Work.GenShared.rreg_Dv
import Submission.Work.GenShared.hasDerivAt_rval
import Submission.Work.GenShared.adjoint_eq_sum
import Submission.Work.GenShared.iterate_derivative_C
import Submission.Work.GenShared.riccati_core
import Submission.Work.GenShared.inN_dv

/-!
# Periods of a solution of an irreducible order-two ODE are independent

Shared generic lemma (`Work.GenShared.periods_indep_gen`) used by both Theorem C (`y1_periods_indep`)
and Theorem A (`ninth_periods_indep`): let `y1` be a nonzero holomorphic solution of the order-two
equation `p₂ y'' + p₁ y' + p₀ y = 0` on a ball `ball x₀ δ` on which `p₂` does not vanish, let
`Jᵢ` be primitives of `rᵢ y1` (`rᵢ = rnᵢ/rdᵢ`, `rdᵢ` nonvanishing on the ball).  Assume the Riccati
equation `p₂(u' + u²) + p₁ u + p₀ = 0` has no solution `u ∈ ℂ(x)` (`hric`) and that the adjoint
equation `(p₂β)'' - (p₁β)' + p₀β = Σ cᵢ rᵢ` has no rational solution with `c ∈ ℂ^k` (`hadj`).
Then `y1, y1', J₁, …, J_k` are linearly independent over the polynomials: any relation
`A y1 + B y1' + Σ Cᵢ Jᵢ = 0` on the ball with polynomial coefficients forces `A = B = Cᵢ = 0`.

The proof is the standard differential-module argument, carried out on the ball itself.  Let
`W̄ = K e₀ ⊕ K e₁ ⊕ ⊕ᵢ K φᵢ` (`K = ℂ(x)`) with connection `∂` (`Dv`: `∂e₀ = e₁`,
`∂e₁ = -(p₀/p₂)e₀ - (p₁/p₂)e₁`, `∂φᵢ = rᵢ e₀`) and evaluation `Wev`.  `N = ker ev` (`InN`) is
`∂`-stable (`inN_dv`), and `N ∩ (Ke₀ ⊕ Ke₁) = 0` (`riccati_core`): if `a y1 + b y1' ≡ 0` with
`b ≠ 0`, then `u = -a/b ∈ ℂ(x)` solves the Riccati equation, contradicting `hric`; if `b = 0` then
`a = 0` by the identity theorem for the holomorphic `y1`.

Now let `n₀ = (A, B, C) ∈ N`.  If `C = 0` we are done by `N ∩ (Ke₀ ⊕ Ke₁) = 0`.  If `C ≠ 0` pick
`m` and a nonzero constant vector `c₀` with `(Cᵢ)^{(m)} = c₀ i` (`iterate_derivative_C`); the third
component of `∂ᵐn₀` evolves by `dRat`, so it equals the constant vector `c₀`, and `∂ᵐn₀ ∈ N`.  Then
`∂(∂ᵐn₀) ∈ N` has vanishing `φ`-part, so `∂(∂ᵐn₀) = 0` by `riccati_core`.  Writing the two
equations of `∂n = 0` and setting `β = b/p₂`, this is exactly the adjoint equation
`(p₂β)'' - (p₁β)' + p₀β = Σ c₀ᵢ rᵢ` (`adjoint_eq_sum`), which `hadj` forbids unless `c₀ = 0` — a
contradiction.
-/

namespace Work.GenShared

open Complex Metric
open Submission.CDT (dRat)

noncomputable section

/-! ## Elementary bookkeeping lemmas -/

/-- `Rval` of a polynomial coefficient. -/
lemma pg_rval_algMap (p : Polynomial ℂ) (z : ℂ) :
    Rval (algebraMap (Polynomial ℂ) (RatFunc ℂ) p) z = p.eval z := by
  simp [Rval, RatFunc.num_algebraMap, RatFunc.denom_algebraMap]

/-- `Rreg` of a polynomial coefficient. -/
lemma pg_rreg_algMap (p : Polynomial ℂ) (z : ℂ) :
    Rreg (algebraMap (Polynomial ℂ) (RatFunc ℂ) p) z := by
  simp [Rreg, RatFunc.denom_algebraMap]

/-- `Rval` of the zero rational function. -/
lemma pg_rval_zero (z : ℂ) : Rval (0 : RatFunc ℂ) z = 0 := by simp [Rval]

/-- The constant rational function `c` is `algebraMap` of `Polynomial.C c`. -/
lemma pg_C_eq_algMap (c : ℂ) :
    (algebraMap ℂ (RatFunc ℂ) c)
      = algebraMap (Polynomial ℂ) (RatFunc ℂ) (Polynomial.C c) :=
  (IsScalarTower.algebraMap_apply ℂ (Polynomial ℂ) (RatFunc ℂ) c).symm

/-- The derivative of a constant rational function vanishes. -/
lemma pg_dRat_const (c : ℂ) : dRat (algebraMap ℂ (RatFunc ℂ) c) = 0 := by
  rw [pg_C_eq_algMap, Submission.CDT.dRat_algebraMap, Polynomial.derivative_C, map_zero]

/-- Iterating the connection `∂` only differentiates the third component. -/
lemma pg_iterate_Dv_third {k : ℕ} (p2 p1 p0 : Polynomial ℂ) (rn rd : Fin k → Polynomial ℂ)
    (m : ℕ) (n : W k) :
    ((fun n : W k => Dv p2 p1 p0 rn rd n)^[m] n).2.2
      = fun i => (dRat^[m]) (n.2.2 i) := by
  have hthird : ∀ x : W k, (Dv p2 p1 p0 rn rd x).2.2 = fun i => dRat (x.2.2 i) :=
    fun x => rfl
  induction m generalizing n with
  | zero => rfl
  | succ m ih =>
      rw [Function.iterate_succ_apply', hthird, ih]
      funext i
      rw [Function.iterate_succ_apply']

/-- The iterated derivative of a polynomial coefficient. -/
lemma pg_dRat_iterate_algMap (p : Polynomial ℂ) (m : ℕ) :
    (dRat^[m]) (algebraMap (Polynomial ℂ) (RatFunc ℂ) p)
      = algebraMap (Polynomial ℂ) (RatFunc ℂ) ((Polynomial.derivative^[m]) p) := by
  induction m generalizing p with
  | zero => simp
  | succ m ih =>
      rw [Function.iterate_succ_apply, Submission.CDT.dRat_algebraMap, ih,
        Function.iterate_succ_apply]

/-! ## The main theorem -/

theorem periods_indep_gen {k : ℕ} (p2 p1 p0 : Polynomial ℂ) (hp2 : p2 ≠ 0)
    (rn rd : Fin k → Polynomial ℂ) (hrd : ∀ i, rd i ≠ 0)
    (hric : ∀ u : RatFunc ℂ,
      algebraMap (Polynomial ℂ) (RatFunc ℂ) p2 * (Submission.CDT.dRat u + u ^ 2)
        + algebraMap (Polynomial ℂ) (RatFunc ℂ) p1 * u
        + algebraMap (Polynomial ℂ) (RatFunc ℂ) p0 ≠ 0)
    (hadj : ∀ (β : RatFunc ℂ) (c : Fin k → ℂ),
      Submission.CDT.dRat (Submission.CDT.dRat (algebraMap (Polynomial ℂ) (RatFunc ℂ) p2 * β))
          - Submission.CDT.dRat (algebraMap (Polynomial ℂ) (RatFunc ℂ) p1 * β)
          + algebraMap (Polynomial ℂ) (RatFunc ℂ) p0 * β
        = ∑ i, (algebraMap ℂ (RatFunc ℂ) (c i)) *
            (algebraMap (Polynomial ℂ) (RatFunc ℂ) (rn i) / algebraMap (Polynomial ℂ) (RatFunc ℂ) (rd i)) →
      β = 0 ∧ c = 0)
    (x0 : ℂ) {δ : ℝ} (hδ : 0 < δ)
    (hp2ne : ∀ z ∈ ball x0 δ, p2.eval z ≠ 0) (hrdne : ∀ i, ∀ z ∈ ball x0 δ, (rd i).eval z ≠ 0)
    (y1 : ℂ → ℂ) (hy1d : DifferentiableOn ℂ y1 (ball x0 δ)) (hy1ne : ∃ z ∈ ball x0 δ, y1 z ≠ 0)
    (hode : ∀ z ∈ ball x0 δ,
      p2.eval z * deriv (deriv y1) z + p1.eval z * deriv y1 z + p0.eval z * y1 z = 0)
    (J : Fin k → ℂ → ℂ) (hJd : ∀ i, DifferentiableOn ℂ (J i) (ball x0 δ))
    (hJderiv : ∀ i, ∀ z ∈ ball x0 δ, HasDerivAt (J i) ((rn i).eval z / (rd i).eval z * y1 z) z)
    (A B : Polynomial ℂ) (C : Fin k → Polynomial ℂ)
    (hrel : ∀ z ∈ ball x0 δ,
      A.eval z * y1 z + B.eval z * deriv y1 z + ∑ i, (C i).eval z * J i z = 0) :
    A = 0 ∧ B = 0 ∧ C = 0 := by
  -- ### The delegated ingredients
  -- `N` is stable under the connection (from `inN_dv`).
  have h_inN_dv : ∀ n : W k, InN x0 δ y1 J n → InN x0 δ y1 J (Dv p2 p1 p0 rn rd n) :=
    fun n hn => inN_dv p2 p1 p0 rn rd x0 hδ hp2ne hrdne y1 hy1d hode J hJd hJderiv hn
  -- `N ∩ (Ke₀ ⊕ Ke₁) = 0` (from `riccati_core`).
  have h_riccati : ∀ a b : RatFunc ℂ,
      (∀ z ∈ ball x0 δ, Rreg a z → Rreg b z →
        Rval a z * y1 z + Rval b z * deriv y1 z = 0) → a = 0 ∧ b = 0 := fun a b hab =>
    riccati_core (k := k) p2 p1 p0 hp2 hric x0 hδ hp2ne y1 hy1d hy1ne hode a b hab
  -- A nonzero polynomial vector eventually has a nonzero constant derivative
  -- (from `iterate_derivative_C`).
  have h_iter : ∀ (C : Fin k → Polynomial ℂ), C ≠ 0 → ∃ m : ℕ, ∃ c : Fin k → ℂ, c ≠ 0 ∧
      ∀ i, (Polynomial.derivative^[m]) (C i) = Polynomial.C (c i) := fun C hC =>
    iterate_derivative_C C hC
  -- ### The relation vector `n₀ = A e₀ + B e₁ + Σ Cᵢ φᵢ`
  set n0 : W k := (algebraMap (Polynomial ℂ) (RatFunc ℂ) A,
      algebraMap (Polynomial ℂ) (RatFunc ℂ) B,
      fun i => algebraMap (Polynomial ℂ) (RatFunc ℂ) (C i)) with hn0
  have hwev0 : ∀ z : ℂ, Wev y1 J n0 z
      = A.eval z * y1 z + B.eval z * deriv y1 z + ∑ i, (C i).eval z * J i z := by
    intro z
    simp only [Wev, hn0, pg_rval_algMap]
  have hn0N : InN x0 δ y1 J n0 := by
    intro z hz _ _ _
    rw [hwev0 z]
    exact hrel z hz
  rcases eq_or_ne C 0 with hC0 | hCne
  · -- ### Case `C = 0`: only the `Ke₀ ⊕ Ke₁` part remains
    have hAB : algebraMap (Polynomial ℂ) (RatFunc ℂ) A = 0 ∧
        algebraMap (Polynomial ℂ) (RatFunc ℂ) B = 0 := by
      refine h_riccati _ _ ?_
      intro z hz ha hb
      have hc : ∀ i, Rreg (n0.2.2 i) z := fun i => by
        simp only [hn0]
        exact pg_rreg_algMap _ z
      simpa [hwev0 z, hC0, pg_rval_algMap] using hn0N z hz ha hb hc
    refine ⟨?_, ?_, hC0⟩
    · by_contra hA
      exact RatFunc.algebraMap_ne_zero hA hAB.1
    · by_contra hB
      exact RatFunc.algebraMap_ne_zero hB hAB.2
  · -- ### Case `C ≠ 0`
    obtain ⟨m, c0, hc0ne, hc0⟩ := h_iter C hCne
    set nm : W k := (fun n : W k => Dv p2 p1 p0 rn rd n)^[m] n0 with hnm
    -- `∂ᵐn₀ ∈ N`
    have hnmN : InN x0 δ y1 J nm := by
      rw [hnm]
      have hiter : ∀ j : ℕ,
          InN x0 δ y1 J ((fun n : W k => Dv p2 p1 p0 rn rd n)^[j] n0) := by
        intro j
        induction j with
        | zero => simpa using hn0N
        | succ j ih =>
            rw [Function.iterate_succ_apply']
            exact h_inN_dv _ ih
      exact hiter m
    -- its `φ`-part is the constant vector `c₀`
    have hcp : nm.2.2 = fun i => algebraMap ℂ (RatFunc ℂ) (c0 i) := by
      have hthird : ((fun n : W k => Dv p2 p1 p0 rn rd n)^[m] n0).2.2
          = fun i => (dRat^[m]) (algebraMap (Polynomial ℂ) (RatFunc ℂ) (C i)) := by
        rw [pg_iterate_Dv_third]
      rw [hnm, hthird]
      funext i
      rw [pg_dRat_iterate_algMap, hc0 i, pg_C_eq_algMap]
    -- so `∂(∂ᵐn₀)` has vanishing `φ`-part, hence lies in `N ∩ (Ke₀ ⊕ Ke₁)`
    have hthird0 : (Dv p2 p1 p0 rn rd nm).2.2 = 0 := by
      funext i
      show dRat (nm.2.2 i) = 0
      rw [hcp]
      simpa using pg_dRat_const (c0 i)
    have hdnmN : InN x0 δ y1 J (Dv p2 p1 p0 rn rd nm) := h_inN_dv nm hnmN
    have hαβ : (Dv p2 p1 p0 rn rd nm).1 = 0 ∧ (Dv p2 p1 p0 rn rd nm).2.1 = 0 := by
      refine h_riccati _ _ ?_
      intro z hz ha hb
      have h := hdnmN z hz ha hb (fun i => by
        rw [congrFun hthird0 i]
        exact rreg_zero)
      have hsum : (∑ x, Rval ((Dv p2 p1 p0 rn rd nm).2.2 x) z * J x z) = 0 := by
        simp [hthird0, pg_rval_zero]
      rw [Wev, hsum, add_zero] at h
      exact h
    have hDv0 : Dv p2 p1 p0 rn rd nm = 0 := Prod.ext hαβ.1 (Prod.ext hαβ.2 hthird0)
    -- the two equations of `∂n = 0`
    have h1 : dRat nm.1
        - (algebraMap (Polynomial ℂ) (RatFunc ℂ) p0
            / algebraMap (Polynomial ℂ) (RatFunc ℂ) p2) * nm.2.1
        + ∑ i, nm.2.2 i * (algebraMap (Polynomial ℂ) (RatFunc ℂ) (rn i)
            / algebraMap (Polynomial ℂ) (RatFunc ℂ) (rd i)) = 0 := by
      have h := congrArg Prod.fst hDv0
      simpa only [Dv, Prod.fst_zero] using h
    have h2 : nm.1 + dRat nm.2.1
        - (algebraMap (Polynomial ℂ) (RatFunc ℂ) p1
            / algebraMap (Polynomial ℂ) (RatFunc ℂ) p2) * nm.2.1 = 0 := by
      have h := congrArg (fun n : W k => n.2.1) hDv0
      simpa only [Dv, Prod.snd_zero, Prod.fst_zero] using h
    -- this is the adjoint equation solved by `β = b/p₂`
    have hadj_input := adjoint_eq_sum p2 p1 p0 rn rd hp2 nm.1 nm.2.1 nm.2.2 h1 h2
    have hgoal : dRat (dRat (algebraMap (Polynomial ℂ) (RatFunc ℂ) p2
            * (nm.2.1 * (algebraMap (Polynomial ℂ) (RatFunc ℂ) p2)⁻¹)))
        - dRat (algebraMap (Polynomial ℂ) (RatFunc ℂ) p1
            * (nm.2.1 * (algebraMap (Polynomial ℂ) (RatFunc ℂ) p2)⁻¹))
        + algebraMap (Polynomial ℂ) (RatFunc ℂ) p0
            * (nm.2.1 * (algebraMap (Polynomial ℂ) (RatFunc ℂ) p2)⁻¹)
      = ∑ i, (algebraMap ℂ (RatFunc ℂ) (c0 i)) *
            (algebraMap (Polynomial ℂ) (RatFunc ℂ) (rn i)
              / algebraMap (Polynomial ℂ) (RatFunc ℂ) (rd i)) := by
      have h := hadj_input
      rw [hcp] at h
      exact h
    exact absurd (hadj _ c0 hgoal).2 hc0ne

end

end Work.GenShared
