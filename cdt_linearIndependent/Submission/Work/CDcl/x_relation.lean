import Mathlib
import Submission.Work.CDcl.setup
import Submission.Work.CDcl.xrel_defs
import Submission.Work.CDcl.xco_ode_P
import Submission.Work.CDcl.xco_ode_Pw_alt
import Submission.Work.CDcl.xco_iter
import Submission.Work.CDcl.xco_norm
import Submission.Work.CDcl.xrel_linalg

namespace Work.CDcl

/-! Guidance from the requester (Area CDCl of `cdt_linearIndependent`):

# An order-4 relation for the pullbacks `T k = (G^{(k)})∘y`

`Submission/Work/CDcl/setup.lean` (imported) defines
`G0 a b ra rb rab r0 = Submission.CDT.sympSym (Submission.CDT.logP a b ra rb rab r0)` and
`T a b ra rb rab r0 k = ((PowerSeries.derivative (R := ℚ))^[k] G0).subst sympY`, the pullback of the `k`-th
derivative of `G` along `y = x²/(x-1)`.  Also here: `K = RatFunc ℚ`, `xK = x`, `phiK = x/(x-1)`,
`yK`, `rhoK = (x-1)²/(x(x-2)) = dx/dy`, and the paper's ODE data `p2K, p1K, p0K` (`P₂,P₁,P₀`),
`alphaK = -P₁/P₂`, `betaK = -P₀/P₂`, `gammaK = p/P₂`, plus the φ-pullbacks `Q2K,Q1K,Q0K` and
`alphaKt, betaKt, gammaKt`.

What is asked: a *nontrivial* ℚ[x]-linear relation among the five pullbacks `T 0,…,T 4`:
`Σ_{k<5} P k · T k = r` with `P : Fin 5 → ℚ[x]` not identically zero and `r ∈ ℚ[x]`.

Route (do NOT compute the paper's operator `LL`; only its existence is needed):
1. `P := logP a b ra rb rab r0` satisfies the order-2 inhomogeneous ODE `M(P) = p` with
   `M = P₂∂² + P₁∂ + P₀` and `p ∈ ℚ[x]` — this is `Submission.CDT.logP_ode` (with `logPAODE`,
   `RaFam/RbFam/RabFam`); equivalently `P'' = αK·P' + βK·P + γK` after clearing by `P₂`.
   Its φ-pullback `Pw := P.subst sympPhi` satisfies `Pw'' = alphaKt·Pw' + betaKt·Pw + gammaKt`
   (the tilde data is the pullback operator: `M^w(g) = (M(g∘φ))∘φ`, so `M^w(Pw) = (M(P))∘φ`;
   prove it with the chain rule `PowerSeries.derivative_subst` or by direct substitution).
2. Let `A f := ρ·(derivative-in-x f)`; `S := G.subst sympY = P + Pw` and `A^k S = T k` (chain rule
   plus `ρ·(derivative sympY) = 1`).  Define in `K` the recurrences
   `a₀ = 1, b₀ = 0, a_{k+1} = ρ(a_k' + b_k·β), b_{k+1} = ρ(a_k + b_k' + b_k·α)`
   (`'` = `Submission.CDT.dRat`) and the tilde versions with `α̃,β̃`, plus
   `d₀ = d̃₀ = 0, d_{k+1} = ρ(d_k' + b_k·γ)`, `d̃_{k+1} = ρ(d̃_k' + b̃_k·γ̃)`.
   Prove by induction (`k ≤ 4`) that `A^k(P) = a_k·P + b_k·P' + d_k` and
   `A^k(Pw) = ã_k·Pw + b̃_k·Pw' + d̃_k`.
   NOTE on where to work: the products involve the rational functions `ρ, a_k, …`, which have poles
   at `x = 0`, so `A^k(P)` is not a power series for `k ≥ 1`.  A good setting is the ring
   `R := PowerSeries K` (power series with coefficients in `K = ℚ(x)`) with the derivation
   `D(Σ aₙxⁿ) = Σ (dRat aₙ)xⁿ + Σ n aₙ x^{n-1}`; then `D` is a derivation with
   `D(C c) = C (dRat c)`, and the reduction induction is the Leibniz rule plus the ODE.  (Or use the
   fraction field of `ℚ[[x]]` / `LaurentSeries ℚ`.)
3. Linear algebra: the five vectors `(a_k, b_k, ã_k, b̃_k) ∈ K^4`, `k ≤ 4`, are `K`-linearly
   dependent (5 vectors in a 4-dimensional space).  Summing step 2 with a nontrivial dependence
   `ν : Fin 5 → K` kills the `P, P', Pw, Pw'` terms and gives `Σ_k ν_k·T k = R` with
   `R = Σ_k ν_k·(d_k + d̃_k) ∈ K`, `ν ≠ 0`.  (This is the whole point: there are only four "bad"
   directions, so five unknowns always suffice; no explicit order-4 operator, no `R₄/R₁₀`, no
   monodromy.)
4. Clear denominators: pick `W ∈ ℚ[x]`, `W ≠ 0`, with `W·ν_k ∈ ℚ[x]` and `W·R ∈ ℚ[x]`; multiplying
   step 3 by `W` gives the claimed relation with `P k := W·ν_k`, `r := W·R`.  Since `P k ∈ ℚ[x]`
   and `T k ∈ ℚ[[x]]`, this is an identity of power series.

You may add helper lemmas above the statement; do not change the statement. -/

theorem x_relation (a b : ℚ) (ra rb rab r0 : ℤ) :
    ∃ (P : Fin 5 → Polynomial ℚ) (r : Polynomial ℚ), P ≠ 0 ∧
      (∑ k : Fin 5, (P k : PowerSeries ℚ) * Work.CDcl.T a b ra rb rab r0 k)
        = (r : PowerSeries ℚ) := by
  let U : Fin 5 → Fin 4 → RatFunc ℚ := fun k i =>
    if i = 0 then (Pseq a b ra rb rab r0 (k : ℕ)).1
    else if i = 1 then (Pseq a b ra rb rab r0 (k : ℕ)).2.1
    else if i = 2 then (Pwseq a b ra rb rab r0 (k : ℕ)).1
    else (Pwseq a b ra rb rab r0 (k : ℕ)).2.1
  let D : Fin 5 → RatFunc ℚ := fun k =>
    (Pseq a b ra rb rab r0 (k : ℕ)).2.2 + (Pwseq a b ra rb rab r0 (k : ℕ)).2.2
  have hF : ∀ k : Fin 5,
      Tfun a b ra rb rab r0 (k : ℕ)
        = toL (U k 0) * Pfun a b ra rb rab r0
          + toL (U k 1) * dL (Pfun a b ra rb rab r0)
          + toL (U k 2) * Pwfun a b ra rb rab r0
          + toL (U k 3) * dL (Pwfun a b ra rb rab r0) + toL (D k) := by
    intro k
    have h := xco_norm a b ra rb rab r0 (k : ℕ)
    have h0 : U k 0 = (Pseq a b ra rb rab r0 (k : ℕ)).1 := rfl
    have h1 : U k 1 = (Pseq a b ra rb rab r0 (k : ℕ)).2.1 := rfl
    have h2 : U k 2 = (Pwseq a b ra rb rab r0 (k : ℕ)).1 := rfl
    have h3 : U k 3 = (Pwseq a b ra rb rab r0 (k : ℕ)).2.1 := rfl
    rw [h0, h1, h2, h3]
    exact h
  obtain ⟨Q, r, hQ, hrel⟩ := xrel_linalg (fun k => Tfun a b ra rb rab r0 (k : ℕ))
    (Pfun a b ra rb rab r0) (dL (Pfun a b ra rb rab r0))
    (Pwfun a b ra rb rab r0) (dL (Pwfun a b ra rb rab r0)) U D hF
  refine ⟨Q, r, hQ, ?_⟩
  apply IsFractionRing.injective (PowerSeries ℚ) LF
  have h1 : algebraMap (PowerSeries ℚ) LF
      (∑ k : Fin 5, (Q k : PowerSeries ℚ) * Work.CDcl.T a b ra rb rab r0 (k : ℕ))
      = ∑ k : Fin 5, toL (Q k) * Tfun a b ra rb rab r0 (k : ℕ) := by
    rw [map_sum]
    refine Finset.sum_congr rfl fun k _ => ?_
    have hQk : algebraMap (PowerSeries ℚ) LF (Q k : PowerSeries ℚ) = toL (Q k) := by
      simp only [RatFunc.coePolynomial, toL_algebraMap]
    have hTk : algebraMap (PowerSeries ℚ) LF (Work.CDcl.T a b ra rb rab r0 (k : ℕ))
        = Tfun a b ra rb rab r0 (k : ℕ) := rfl
    rw [map_mul, hQk, hTk]
  rw [h1, hrel]
  simp only [RatFunc.coePolynomial, toL_algebraMap]

end Work.CDcl
