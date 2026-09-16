import Mathlib
import Submission.DHLCriterion
import Submission.SieveSFunction

open scoped BigOperators Topology
open Finset Filter

set_option maxHeartbeats 1000000

/-!
# The level-of-distribution interface (Polymath8a §2 and §4.2)

This module sets up the interface between the sieve side (the divisor sums of
`Submission.SieveExpansion`/`PairwiseLemma41`) and the analytic
number-theory side (Bombieri--Vinogradov) for the *θ-weighted* sums of
Polymath8a Theorem 3.5.

The quantity that has to be controlled is the discrepancy (P8 (3))

    Δ(f; a (q)) := Σ_{n ∈ [x,2x], n ≡ a (q)} f n − (1/φ(q))·Σ_{n ∈ [x,2x], (n,q)=1} f n,

of the window `[x,2x]`.  In the application `f n = θ(n + h)` for a shift `h`, and
the residue class `a` is the (primitive!) class produced by the CRT from the
sieve congruences `n + h_i ≡ 0 (mod [d_i,d'_i])`, `n ≡ b (W)`.

The Elliott--Halberstam input is recorded as the predicate
`levelOfDistribution ϑ`: for every `A` the sum of the maximal (over primitive
residue classes) discrepancies over the moduli `q ≤ Q ≪ x^ϑ` is
`≪_A x log^{-A} x`.  Theorem 2.3 of Polymath8a (Bombieri--Vinogradov, not yet
formalized) supplies `levelOfDistribution ϑ` for every `ϑ < 1/2`.
-/

namespace Commons.NumberTheory.MaynardSieve

/-- The discrepancy (P8 (3)) of a window function `f` on `[x,2x]` with respect
to the residue class `a (mod q)`:
`Σ_{n ∈ [x,2x], n ≡ a (q)} f n − (1/φ(q))·Σ_{n ∈ [x,2x], (n,q)=1} f n`. -/
noncomputable def disc (f : ℕ → ℝ) (x q a : ℕ) : ℝ :=
  (∑ n ∈ (Finset.Icc x (2 * x)).filter (fun n => n % q = a % q), f n) -
    (1 / ((q.totient : ℕ) : ℝ)) *
      (∑ n ∈ (Finset.Icc x (2 * x)).filter (fun n => n.Coprime q), f n)

/-- The same discrepancy for a *shifted* residue condition: the window variable
is `m = n + h`, and the condition is `m ≡ c (mod q)`. -/
noncomputable def discShift (f : ℕ → ℝ) (x q c h : ℕ) : ℝ :=
  (∑ n ∈ (Finset.Icc x (2 * x)).filter (fun n => (n + h) % q = c % q), f (n + h)) -
    (1 / ((q.totient : ℕ) : ℝ)) *
      (∑ n ∈ (Finset.Icc x (2 * x)).filter (fun n => (n + h).Coprime q), f (n + h))

/-- The maximal discrepancy over the **primitive** residue classes `a (mod q)`,
`sup_{(a,q)=1} |Δ(f; a (q))|`, as a `sSup` of the (nonempty, when `q ≥ 1`) set of
values of `|disc f x q a|` over residues coprime to `q`. -/
noncomputable def discSup (f : ℕ → ℝ) (x q : ℕ) : ℝ :=
  sSup ((fun a : ℕ => |disc f x q a|) '' {a : ℕ | a.Coprime q})

/-! ## The level of distribution in the *shifted-window* form

**Correction (session 18).**  The naive reading of the Elliott--Halberstam input
for the sieve would be `discSup (fun n => thetaNat (n + h)) x q`, i.e. the
discrepancy of the *unshifted window* `[x,2x]` applied to the shifted function
`n ↦ θ(n+h)`.  That statement is **false**: its expected main term
`(1/φ(q))·Σ_{n∈[x,2x],(n,q)=1}θ(n+h)` counts the coprimality of `n` (not of
`n+h`), and for the primitive class `a ≡ -h (mod q)` the *class sum* of `θ(n+h)`
vanishes while the main term is `≈ x/φ(q)` (for `q` prime this makes
`sup_a |disc| ≈ x/q`, whose sum over `q ≤ x^ϑ` is `≫ x`).

The correct object — and the one actually used in Polymath8a §4.2, equation (45)
— is the discrepancy of the *shifted* function `α = 1_{[x+h,2x+h]}·θ` in its
primitive class, i.e. exactly `discShift (fun n => thetaNat n) x q a h`:
this is `Δ(α; a (q))` of P8 (3), whose main term is
`(1/φ(q))·Σ_{(m,q)=1} α(m) = (1/φ(q))·Σ_{(m,q)=1} θ(m)` over the shifted window
`≈ x/φ(q)`, matching the class sum `Σ_{m≡a(q)}θ(m) ≈ x/φ(q)`.  (Recall
`Σ_{(m,q)=1}θ(m) ≈ x`, since `θ` is supported on primes — the coprimality
condition only removes the finitely many primes dividing `q`.) -/

/-- The maximal discrepancy (P8 (3)) over the primitive residue classes of the
*shifted* window `[x+h, 2x+h]`, i.e. of `discShift (fun n => thetaNat n) x q a h`. -/
noncomputable def discSupShift (x q h : ℕ) : ℝ :=
  sSup ((fun a : ℕ => |discShift (fun n => thetaNat n) x q a h|) '' {a : ℕ | a.Coprime q})

/-- **The level of distribution `ϑ` for the primes** in the shifted-window form
consumed by the sieve (Polymath8a Claim 2.2 / Theorem 2.3): for every `A ≥ 1`,
for all sufficiently large `x` and every `Q` with `Q ≤ x^ϑ`,

    Σ_{q ≤ Q} sup_{h ≤ C} sup_{(a,q)=1} |Δ(θ·1_{[x+h,2x+h]}; a (q))| ≤ x·(log x)^{-A},

uniformly in the bounded shifts `h ≤ C` (in the application `h = h_{i₀}` is a
fixed element of an admissible tuple, so all shifts are bounded). -/
def levelOfDistribution (ϑ : ℝ) : Prop :=
  ∀ A : ℝ, 1 ≤ A → ∀ C : ℕ, ∀ᶠ x : ℕ in atTop, ∀ Q : ℕ,
    (Q : ℝ) ≤ (x : ℝ) ^ ϑ →
      (∑ q ∈ Finset.Icc 1 Q,
        (Finset.range (C + 1)).sup' ⟨0, Finset.mem_range.mpr (Nat.succ_pos C)⟩
          (fun h => discSupShift x q h)) ≤
        (x : ℝ) * (Real.log (x : ℝ)) ^ (-A)

/-! ## Elementary decomposition of a window sum along a residue class -/

/-- The discrepancy is exactly the `class sum − expected count` decomposition of
the window sum over a primitive residue class. -/
theorem classSum_eq_expected_add_disc (f : ℕ → ℝ) (x q a : ℕ) :
    (∑ n ∈ (Finset.Icc x (2 * x)).filter (fun n => n % q = a % q), f n) =
      (1 / ((q.totient : ℕ) : ℝ)) *
          (∑ n ∈ (Finset.Icc x (2 * x)).filter (fun n => n.Coprime q), f n) +
        disc f x q a := by
  unfold disc
  ring

/-- Shifted form of the same decomposition. -/
theorem classSum_shift_eq_expected_add_disc (f : ℕ → ℝ) (x q c h : ℕ) :
    (∑ n ∈ (Finset.Icc x (2 * x)).filter (fun n => (n + h) % q = c % q), f (n + h)) =
      (1 / ((q.totient : ℕ) : ℝ)) *
          (∑ n ∈ (Finset.Icc x (2 * x)).filter (fun n => (n + h).Coprime q), f (n + h)) +
        discShift f x q c h := by
  unfold discShift
  ring

/-- The `θ`-weighted `S`-set sum: the object `S̃(d,e)` of P8 (43). -/
noncomputable def thetaSset (N W b : ℕ) {k : ℕ} (H : Fin k → ℕ) (m : Fin k → ℕ)
    (h : ℕ) : ℝ :=
  ∑ n ∈ Sset N W b H m, thetaNat (n + h)

/-- `thetaSset` unfolds to the θ-sum over the `S`-set congruence system. -/
theorem thetaSset_eq_sum_filter (N W b : ℕ) {k : ℕ} (H : Fin k → ℕ) (m : Fin k → ℕ)
    (h : ℕ) :
    thetaSset N W b H m h =
      ∑ n ∈ (Finset.Icc N (2 * N)).filter
        (fun n => n % W = b % W ∧ ∀ i : Fin k, m i ∣ n + H i), thetaNat (n + h) := rfl

/-- If the `S`-set is the shifted residue class modulo `q` (the CRT output of the
sieve congruences), then `S̃` is the θ-sum over that class, and the discrepancy
decomposition applies:
`S̃ = (1/φ(q))·Σ_{(n+h,q)=1} θ(n+h) + Δ`. -/
theorem thetaSset_eq_expected_add_disc {N W b q c : ℕ} {k : ℕ} {H : Fin k → ℕ}
    {m : Fin k → ℕ} {h : ℕ}
    (hset : Sset N W b H m =
      (Finset.Icc N (2 * N)).filter (fun n => (n + h) % q = c % q)) :
    thetaSset N W b H m h =
      (1 / ((q.totient : ℕ) : ℝ)) *
          (∑ n ∈ (Finset.Icc N (2 * N)).filter (fun n => (n + h).Coprime q),
            thetaNat (n + h)) +
        discShift (fun n => thetaNat n) N q c h := by
  rw [thetaSset, hset]
  exact classSum_shift_eq_expected_add_disc (fun n => thetaNat n) N q c h

end Commons.NumberTheory.MaynardSieve
