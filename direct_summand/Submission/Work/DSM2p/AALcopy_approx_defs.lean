-- Redirected copy of `Submission.Work.DSM2p.approx_defs` (imports re-pointed to the `AALvaln` vocabulary layer so that
-- `area_AAL_proved.lean` can import the result without an import cycle).  The original
-- file is untouched; this copy is generated mechanically.
import Submission.Work.DSM2p.AALvaln

/-!
# `approx-defs` — the vocabulary of the Česnavičius–Scholze approximation lemma

This file owns the definitions shared by the pieces of the analytic node
`Work.DSM2p.approx_lem` (Česnavičius–Scholze, *Purity for flat cohomology*, `approx-lem`).

## The objects

Fix `p`, a `CommRing R` with `DSMap.PerfectoidData p R`, `[Fact (¬IsUnit (p:R))]` and
`[IsAdicComplete (Ideal.span {(p:R)}) R]`.  Write

* `Λ = PreTilt R p = Perfection (R ⧸ (p)) p` for the tilt of `R` (Mathlib);
* `𝕎 = WittVector p Λ`, with `θ = WittVector.fontaineTheta R p : 𝕎 →+* R` (Mathlib);
* `[x] = WittVector.teichmuller p x` for the Teichmüller lift of `x : Λ`.

Every `z : 𝕎` has the (convergent) Teichmüller expansion
`z = ∑ j, [z_(j)] * p^j`, where the *tilt digit*

`tiltDigit z j = ((frobeniusEquiv Λ p).symm ^ j) (z.coeff j)  : Λ`

is the `p^j`-th root of the `j`-th Witt coordinate of `z`.  Its `♯`-image `PreTilt.untilt (tiltDigit z j)`
is the `j`-th coefficient of the Teichmüller expansion of `θ z` in `R`:

`θ z = ∑ j, PreTilt.untilt (tiltDigit z j) * (p : R)^j`

(`fontaineTheta_sub_sum_mem` below for the truncated, ideal-theoretic, form).  This is the only route
by which the Witt vectors enter the approximation lemma: everything is phrased in terms of the two
multiplicative maps `PreTilt.untilt` and `tiltDigit`.

`DigitsLe QR z B` ("the digits of `z` are bounded by `B`", `B : R`) is the sup-norm condition of
Česnavičius–Scholze, phrased so that the value group is never named: for every continuous valuation
`v` of the unit ball of `R`, `v` of every tilt digit of `z` is at most `v B`.
-/

set_option linter.unusedSectionVars false

namespace Work.DSM2p

universe u v

variable {p : ℕ} [Fact p.Prime] {R : Type u} [CommRing R] [Fact (¬ IsUnit (p : R))]
    [IsAdicComplete (Ideal.span {(p : R)}) R]

/-- The `j`-th **tilt digit** of a Witt vector `z` over the tilt `Λ = PreTilt R p`: the `p^j`-th root
of the `j`-th Witt coordinate of `z`.  Its `♯`-image is the `j`-th coefficient of the Teichmüller
expansion of `fontaineTheta R p z`. -/
noncomputable def tiltDigit (z : WittVector p (PreTilt R p)) (j : ℕ) : PreTilt R p :=
  ((frobeniusEquiv (PreTilt R p) p).symm ^ j) (z.coeff j)

@[simp]
theorem tiltDigit_zero (z : WittVector p (PreTilt R p)) : tiltDigit z 0 = z.coeff 0 := by
  simp [tiltDigit]

/-- The Teichmüller lift has only its `0`-th tilt digit, namely `x` itself. -/
@[simp]
theorem tiltDigit_teichmuller (x : PreTilt R p) (j : ℕ) :
    tiltDigit (WittVector.teichmuller p x) j = if j = 0 then x else 0 := by
  rcases eq_or_ne j 0 with rfl | hj
  · simp [tiltDigit]
  · rw [if_neg hj]
    simp [tiltDigit, WittVector.teichmuller_coeff_pos p x j (Nat.pos_of_ne_zero hj)]

/-- `DigitsLe QR z B` : every tilt digit of `z` has `v`-value at most `v B` at every continuous
valuation `v` of `R` of the unit ball.  This is the sup-norm bound `|z|_sup ≤ B` of
Česnavičius–Scholze, stated without naming the value group. -/
def DigitsLe (QR : DSMap.PerfectoidData p R) (z : WittVector p (PreTilt R p)) (B : R) : Prop :=
  ∀ (Γ₀ : Type v) [LinearOrderedCommGroupWithZero Γ₀] (v : Valuation R Γ₀),
    IsContinuousValuation (QR.ϖ 0) v → IsUnitBall v Set.univ →
      ∀ j : ℕ, v (PreTilt.untilt (tiltDigit z j)) ≤ v B

/-- **The truncated Teichmüller expansion.**  For every `z : 𝕎` and every `N`, the element
`fontaineTheta R p z` differs from the finite sum `∑_{j ≤ N} ♯(tiltDigit z j) * p^j` by a multiple of
`p^{N+1}`.  (Ideal-theoretic form, obtained from Mathlib's
`WittVector.dvd_sub_sum_teichmuller_iterateFrobeniusEquiv_coeff` by applying `θ`.) -/
theorem fontaineTheta_sub_sum_mem (QR : DSMap.PerfectoidData p R)
    (z : WittVector p (PreTilt R p)) (N : ℕ) :
    WittVector.fontaineTheta R p z -
        ∑ j ≤ N, PreTilt.untilt (tiltDigit z j) * (p : R) ^ j ∈
      Ideal.span {(p : R)} ^ (N + 1) := by
  simp only [tiltDigit]
  obtain ⟨w, hw⟩ := WittVector.dvd_sub_sum_teichmuller_iterateFrobeniusEquiv_coeff z N
  have hsum : WittVector.fontaineTheta R p
      (∑ i ≤ N, WittVector.teichmuller p
        (((frobeniusEquiv (PreTilt R p) p).symm ^ i) (z.coeff i)) *
          (p : WittVector p (PreTilt R p)) ^ i)
      = ∑ j ≤ N,
          PreTilt.untilt (((frobeniusEquiv (PreTilt R p) p).symm ^ j) (z.coeff j)) * (p : R) ^ j := by
    rw [map_sum]
    refine Finset.sum_congr rfl fun i _ => ?_
    rw [map_mul, map_pow, WittVector.fontaineTheta_teichmuller, map_natCast]
  rw [← hsum, ← map_sub]
  have h2 : WittVector.fontaineTheta R p
      (z - ∑ i ≤ N, WittVector.teichmuller p
        (((frobeniusEquiv (PreTilt R p) p).symm ^ i) (z.coeff i)) *
          (p : WittVector p (PreTilt R p)) ^ i)
      = (p : R) ^ (N + 1) * WittVector.fontaineTheta R p w := by
    rw [hw, map_mul, map_pow, map_natCast]
  rw [h2]
  exact Ideal.mul_mem_right _ _ (Ideal.pow_mem_pow (Ideal.mem_span_singleton_self (p : R)) (N + 1))

end Work.DSM2p
