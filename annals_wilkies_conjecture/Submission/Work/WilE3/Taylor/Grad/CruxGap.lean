import Mathlib
import Submission.Work.WilE3.Defs
import Submission.Work.WilE3.Taylor.Grad.hinge
import Submission.Work.WilE3.Taylor.Grad.arcCrux_of_grad
import Submission.Work.WilE3.Taylor.CaseII.GenGrad

/-!
  annals_wilkies_conjecture, AREA E3 / Taylor / Grad: **the denominator bound** — the single
  remaining mathematical input of Gabrielov's effective Łojasiewicz inequality.

  This module is the *low* half of `Submission/Work/WilE3/Taylor/hasLoj_of_multiplicity.lean`
  (split out of it because the workspace build guard caps a module at 30 KB).  It carries

  * `Work.WilE3.Taylor.arith_denom` — the pure arithmetic of the reduction: on a polar arc with
    `n < m`, the reduced denominator `q = m / gcd (2n) m` of the exponent `2n/m` controls the
    sharp arc bound via `(2q+1)·n ≤ 2q·m`;
  * `Work.WilE3.Taylor.ea_arcCrux_denomBound` — **the remaining gap**, i.e. Gabrielov's bound
    (11)/(13) (Selecta Math. 1 (1995), Theorem 3.1; restated as Lemma 2.3 of the 1998 frontier
    paper): the denominator `q` is bounded by a polynomial in `atomDeg Φ` alone.
-/

set_option autoImplicit false
noncomputable section
open Classical Topology
open WilkiesDesign.E

namespace Work.WilE3.Taylor

variable {k r : ℕ}

/-- **The arithmetic of the denominator bound.**  Let `m, n` be the orders of `Φ ∘ γ` and of a
partial `∂ᵢΦ ∘ γ` along a polar arc, with `n < m` (which holds automatically, by the one-variable
chain rule: `n + a ≤ m` where `a ≥ 1` is the order of `γ - y`).  Write the exponent `2n/m` in
lowest terms as `p/q`; then `q = m / gcd (2n) m`, and `p ≤ 2q - 1` *automatically* (indeed
`g := gcd (2n) m` divides `m` and `2n`, and `2(m-n) = g·(2q - p) ≥ g`).  Hence

   `2q·n = p·m ≤ (2q-1)·m`,

i.e. `n/m ≤ 1 - 1/(2q)`.  Since `q ≤ Q` by the denominator bound, we get `2Q·n ≤ (2Q-1)·m`, and
adding `n ≤ m` gives `(2Q+1)·n ≤ 2Q·m` — the sharp arc crux with `K = 2Q`.

This is the *only* number-theoretic content of the arc crux; the analytic content is entirely in
the denominator bound `ea_arcCrux_denomBound`. -/
theorem arith_denom {m n Q : ℕ} (hm : 0 < m) (hnm : n < m)
    (hQ : m / Nat.gcd (2 * n) m ≤ Q) :
    (2 * Q + 1) * n ≤ 2 * Q * m := by
  have hgpos : 0 < Nat.gcd (2 * n) m :=
    Nat.pos_of_dvd_of_pos (Nat.gcd_dvd_right (2 * n) m) hm
  have hm_eq : (m / Nat.gcd (2 * n) m) * Nat.gcd (2 * n) m = m :=
    Nat.div_mul_cancel (Nat.gcd_dvd_right (2 * n) m)
  have hn_eq : (2 * n / Nat.gcd (2 * n) m) * Nat.gcd (2 * n) m = 2 * n :=
    Nat.div_mul_cancel (Nat.gcd_dvd_left (2 * n) m)
  set q := m / Nat.gcd (2 * n) m with hq
  set p := 2 * n / Nat.gcd (2 * n) m with hp
  set g := Nat.gcd (2 * n) m with hg
  have hqpos : 0 < q := by
    rcases Nat.eq_zero_or_pos q with h | h
    · exfalso
      rw [h, Nat.zero_mul] at hm_eq
      omega
    · exact h
  have hp_lt : p < 2 * q := by
    have h1 : p * g < 2 * q * g := by
      calc p * g = 2 * n := hn_eq
        _ < 2 * m := by omega
        _ = 2 * (q * g) := by rw [hm_eq]
        _ = 2 * q * g := by ring
    exact Nat.lt_of_mul_lt_mul_right h1
  have hp_le : p ≤ 2 * q - 1 := by omega
  have h4 : 2 * q * n ≤ (2 * q - 1) * m := by
    have h2 : 2 * q * n = p * m := by
      calc 2 * q * n = q * (2 * n) := by ring
        _ = q * (p * g) := by rw [hn_eq]
        _ = p * (q * g) := by ring
        _ = p * m := by rw [hm_eq]
    rw [h2]
    exact Nat.mul_le_mul_right m hp_le
  have hkey : n * (2 * Q) ≤ m * (2 * Q - 1) := by
    have hstep : n * (2 * q) * Q ≤ m * (2 * Q - 1) * q := by
      calc n * (2 * q) * Q = 2 * q * n * Q := by ring
        _ ≤ (2 * q - 1) * m * Q := Nat.mul_le_mul_right Q h4
        _ = m * ((2 * q - 1) * Q) := by ring
        _ ≤ m * ((2 * Q - 1) * q) := by
              refine Nat.mul_le_mul_left m ?_
              rw [Nat.sub_mul, Nat.sub_mul, one_mul, one_mul]
              have he : 2 * q * Q = 2 * Q * q := by ring
              rw [he]
              omega
        _ = m * (2 * Q - 1) * q := by ring
    have hcancel := hstep
    rw [show n * (2 * q) * Q = n * (2 * Q) * q by ring] at hcancel
    exact Nat.le_of_mul_le_mul_right hcancel hqpos
  calc (2 * Q + 1) * n = 2 * Q * n + n := by ring
    _ ≤ (2 * Q - 1) * m + m := by
          refine Nat.add_le_add ?_ (Nat.le_of_lt hnm)
          rw [Nat.mul_comm (2 * Q) n, Nat.mul_comm (2 * Q - 1) m]
          exact hkey
    _ = 2 * Q * m := by
          have h1 : 1 ≤ 2 * Q := by omega
          rw [show (2 * Q - 1) * m + m = ((2 * Q - 1) + 1) * m by ring,
            Nat.sub_add_cancel h1]

/- **RETIRED (SESSION 11): the denominator bound.**  The declaration formerly here,
`Work.WilE3.Taylor.ea_arcCrux_denomBound`, asserted that `q := m / Nat.gcd (2 * n) m` is bounded by
`Q.eval (atomDeg Φ)`.  **That statement is FALSE** and is recorded as such in
`Taylor/NOTES_hasLoj_of_multiplicity.md` §10.6: for `k ≤ 2` the hypothesis `PolarLike` is *vacuous*
(`det3` is fully antisymmetrised, so it vanishes whenever two of `i j l : Fin k` coincide, and for
`k ≤ 2` three indices always repeat), so the claim becomes universal for plane curves, and the family
`k = 2`, `Φ = X₀X₁` (`atomDeg Φ = 3`), `γ_a(t) = (t^{a+1}, t^a)` gives `m = 2a+1` with the only
admissible partial orders `a` and `a+1`; both `2a` and `2a+2` are coprime to `m = 2a+1`, so
`q = 2a+1 → ∞` while `atomDeg Φ` stays fixed.  No polynomial `Q` can work. -/

/-- **(DEFICIT): the residual target, in the shape the arc crux consumes it.**

For every format bound `F` there is a format-determined polynomial `K` (∃`K`, *not* a fixed power
`X^(F+1)`) such that every polar arc carries a partial of order `n` with
`(K.eval (atomDeg Φ) + 1) * n ≤ K.eval (atomDeg Φ) * m`, i.e. `n/m ≤ K/(K+1)`.

This is the form consumed by `Work.WilE3.Taylor.ea_arcCrux_gap` (which has the shape `∀ F ∃ K`), and
it is the form in which the statement is *true*: the published effective bounds (Gabrielov 1995,
(17)/(18); 1998, Lemma 2.3) are polynomials in the degrees whose coefficients depend on the format,
and `MultiplicityBound` supplies only an unspecified `M`, so a fixed exponent `F + 1` cannot be
asserted (SESSION 16, message of the project lead).  The `∀ F ∃ K` form is what `ArcCrux` and the
hinge `Grad.ea_grad_of_arcCrux` accept (any monotone polynomial works, and both consumers only need
`K` to come with the classification).

It **does not** pass through the denominator `q`: the identically-vanishing partial along the arc is
the recurring obstruction (NOTES §9.6, §10.3, §10.6), and there is **no** induction on `k`
(SESSION 4's S4-3).

**(SESSION 17)** It is now *proved*, from the effective gradient inequality: the converse of the
hinge `Work.WilE3.Taylor.Grad.ea_grad_of_arcCrux` is
`Work.WilE3.Taylor.Grad.arcCrux_of_grad`, and (GRAD) is available from `MultiplicityBound` by the
replacement route (`Work.WilE3.Taylor.CaseII.ea_grad_of_multiplicity'`, node T5).  So this module
carries no unfinished declaration any more. -/
theorem arcDeficitBound (hMB : Work.WilE3.MultiplicityBound) :
    ∀ F : ℕ, ∃ K : Polynomial ℕ, ∀ (k r : ℕ) (c : EAChain k r) (Φ : EAPoly k r) (y : Fin k → ℝ)
      (γ : ℝ → Fin k → ℝ) (m : ℕ),
      k + r ≤ F → AnalyticAt ℝ γ 0 → γ 0 = y → 0 < m →
      analyticOrderAt (fun t : ℝ => eaEval c Φ (γ t)) 0 = m →
      Work.WilE3.Taylor.Grad.PolarLike c Φ y γ →
      ∃ (i : Fin k) (n : ℕ),
        analyticOrderAt (fun t : ℝ => eaEval c (eaD c i Φ) (γ t)) 0 = n ∧
          (K.eval (atomDeg Φ) + 1) * n ≤ K.eval (atomDeg Φ) * m :=
  Work.WilE3.Taylor.Grad.arcCrux_of_grad
    (Work.WilE3.Taylor.CaseII.ea_grad_of_multiplicity' hMB)

end Work.WilE3.Taylor
