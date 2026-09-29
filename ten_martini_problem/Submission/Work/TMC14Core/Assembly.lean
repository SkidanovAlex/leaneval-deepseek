import Submission.Work.TMC14Core.Chambers

/-!
# TMC14Core: the C14 assembly skeleton

`P_GapBound` (C14) says: inside a spectral interval of `Σ_α` (`α` irrational, `0 < λ ≤ 1`)
and for every `ε > 0`, all sufficiently good rational approximants `p/q` of `α` have a
*flat piece* of `N_{p/q}` in `[c,d]` of length at least `e^{-εq}λ^{q/2}`.

Following ROUTE_LEAD §4 C14, the proof decomposes into

* **(A) `RatIdsFlat`** — off the union spectrum `ratSpec p q lam` of the rational
  approximant, `N_{p/q}` is locally constant (14b);
* **(B) `RatIdsVariation`** — inside the union spectrum, the total variation of `N_{p/q}`
  over an interval is at most `2/q` (14c; `1/q` per band, and at most two bands can be met
  inside the spectrum, the second only through the touching point at `0` for even `q`);
* **(D) `RatGapSize`** — the CEY lower bound for the gaps of the union spectrum of a good
  rational approximant, i.e. 14e (Choi–Elliott–Yui trace identity) + 14f (the upper bound on
  the remaining factors, from C4 + C7 + the block-perturbation estimate).

The gap-finding argument (14d) and the final assembly (14g) are proved here: they use only
`C5` (continuity of `N`) and `C6` (`Σ` consists of points of increase of `N`).
-/

open MeasureTheory Filter Topology Set
open LeanEval.Analysis.TenMartini

noncomputable section

namespace Work.TMC14Core

/-- The union of the spectra of the rational approximant `p/q` (Bloch/Floquet): `E` belongs
to it iff the `q`-step transfer matrix has `|tr| ≤ 2` for some phase. -/
def ratSpec (p : ℤ) (q : ℕ) (lam : ℝ) : Set ℝ :=
  {E | ∃ θ : ℝ, ‖trAq p q lam (E : ℂ) θ‖ ≤ 2}

/-- **(A)** Off `ratSpec p q lam`, the integrated density of states `N_{p/q}` is locally
constant (ROUTE_LEAD 14b). -/
def RatIdsFlat : Prop :=
  ∀ (p : ℤ) (q : ℕ) (lam : ℝ), 0 < lam → ∀ a b : ℝ, a < b →
    (∀ E ∈ Ioo a b, ∀ θ : ℝ, 2 < ‖trAq p q lam (E : ℂ) θ‖) →
    ids ((p : ℝ) / (q : ℝ)) lam a = ids ((p : ℝ) / (q : ℝ)) lam b

/-- **(B)** Inside `ratSpec p q lam`, the variation of `N_{p/q}` over an interval is at most
`2/q'`, where `q' = q / gcd(p, q)` is the denominator of `p/q` in lowest terms (ROUTE_LEAD
14c: one band carries a jump `1/q'`, and at most two bands can be met inside the spectrum).
Note `q'` and not `q`: for a non-reduced fraction `p/q` the spectrum is that of the reduced
one, and the jump per band is `1/q'`. -/
def RatIdsVariation : Prop :=
  ∀ (p : ℤ) (q : ℕ) (lam : ℝ), 0 < lam → 1 ≤ q → ∀ a b : ℝ, a ≤ b →
    (∀ E ∈ Ioo a b, ∃ θ : ℝ, ‖trAq p q lam (E : ℂ) θ‖ ≤ 2) →
    ids ((p : ℝ) / (q : ℝ)) lam b - ids ((p : ℝ) / (q : ℝ)) lam a
      ≤ 2 / ((q / Nat.gcd p.natAbs q : ℕ) : ℝ)

/-- **(D)** The Choi–Elliott–Yui lower bound for the gaps of the rational approximant
(ROUTE_LEAD 14e + 14f).  Hypotheses: `α` irrational, `0 < λ ≤ 1`, a window `[c,d]` **inside
the spectrum `Σ_α`** (so that `C7` gives `L = 0` there, feeding 14f), `ε > 0`.  Conclusion:
there are `δ > 0`, `Q` such that for every `q ≥ Q` and every `p` with `|α - p/q| < δ/q`, every
gap `(a,b)` of `ratSpec p q lam` with `[a,b] ⊆ [c,d]` has length at least `e^{-εq}λ^{q/2}`.
Here "gap" means: `(a,b)` avoids the spectrum and its endpoints belong to it.

The proof needs `P_LEBasics` (14f's locally uniform upper bound on `A_n`) and `P_BJ`
(`L = 0` on `Σ_α`), which is why they are arguments. -/
def RatGapBound : Prop :=
  P_LEBasics → P_BJ →
    ∀ (α lam c d : ℝ), Irrational α → 0 < lam → lam ≤ 1 → c < d → Icc c d ⊆ amoSpec α lam →
    ∀ ε : ℝ, 0 < ε →
      ∃ δ : ℝ, 0 < δ ∧ ∃ Q : ℕ, ∀ (p : ℤ) (q : ℕ), Q ≤ q →
        |α - (p : ℝ) / (q : ℝ)| < δ / (q : ℝ) →
        ∀ a b : ℝ, c ≤ a → a < b → b ≤ d →
          (∀ E ∈ Ioo a b, ∀ θ : ℝ, 2 < ‖trAq p q lam (E : ℂ) θ‖) →
          a ∈ ratSpec p q lam → b ∈ ratSpec p q lam →
          Real.exp (-(ε * (q : ℝ))) * lam ^ ((q : ℝ) / 2) ≤ b - a

/-- **(E)** Arithmetic of the approximation: for irrational `α` and `N`, all rationals with
denominator `< N` stay at distance at least `ρ > 0` from `α` (there are only finitely many
candidates near `α`).  This is what forces the *reduced* denominator `q / gcd(p,q)` of a good
approximant `p/q` to be large, which in turn is what (B) needs. -/
def RatDenomLarge : Prop :=
  ∀ α : ℝ, Irrational α → ∀ N : ℕ, ∃ ρ : ℝ, 0 < ρ ∧ ∀ (p : ℤ) (q : ℕ), 0 < q → q < N →
    ρ ≤ |α - (p : ℝ) / (q : ℝ)|

/-- **(F)** The topology of the rational union spectrum, in the form the assembly uses:
it is closed, and around any point `E` of a window `[c,d]` that is *outside* it there is an
interval `[a',b'] ∋ E` inside the window whose interior avoids the spectrum, whose left end is
either outside the window (`a' < c`) or a spectral point, and whose right end is either `d` or
a spectral point.  (The left/right ends are the infimum/supremum of the off-spectrum piece.) -/
def RatGapEndpoints : Prop :=
  (∀ (p : ℤ) (q : ℕ) (lam : ℝ), IsClosed (ratSpec p q lam)) ∧
  (∀ (p : ℤ) (q : ℕ) (lam c d E : ℝ), E ∉ ratSpec p q lam → c ≤ E → E ≤ d → c < d →
    ∃ a' b' : ℝ, a' ≤ E ∧ E ≤ b' ∧ b' ≤ d ∧
      (∀ y ∈ Ioo a' b', y ∉ ratSpec p q lam) ∧
      (c ≤ a' → a' ∈ ratSpec p q lam) ∧
      (b' < d → b' ∈ ratSpec p q lam))

end Work.TMC14Core
