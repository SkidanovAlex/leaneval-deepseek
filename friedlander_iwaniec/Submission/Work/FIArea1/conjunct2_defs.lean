/-
# `Submission.Work.FIArea1.conjunct2_defs` — the auxiliary sets and pair counts of *FI* (5.22)

`conjunct2_le` (`Work.FIArea1.conjunct2_le`) is the second conjunct of *FI* (5.22):

  `Dform Pa f β ≤ Dstar Pa f β + c τ² (M^{3/4}N^{3/4} + Pz^{-1}M^{1/2}N^{3/2})(log(MN))^{516}`.

Its proof splits `Dform - Dstar` into a diagonal and an off-diagonal piece.  The diagonal piece is
bounded by `Work.FIArea1.diagonal_le`; the off-diagonal piece is bounded by the *pure count*
`offdiagPairSum` of the support conditions of a coefficient of (4.13), which is delegated as
`Work.FIArea1.offdiag_polar_count`.  This module only contains the definitions (and their
membership calculus) so that the delegated statements can be written without any decidability
hypotheses.
-/
import Mathlib
import Submission.Work.FITop3.Defs3
import Submission.Work.FITop3.Smooth
import Submission.Work.FITop3.Smooth.sm_props
import Submission.Work.FITop3.Majorant.majorant_props
import Submission.Work.FITop3.Witness.exists_primary_norm
import Submission.Work.FIArea1.Basic

set_option autoImplicit false

namespace Work.FIArea1

open Finset
open scoped BigOperators

attribute [local instance] Classical.propDecidable

noncomputable section

/-- The support conditions of a coefficient of (4.13): the points of the box `boxN Pa`
(`|z|² ≲ N`) lying in the polar box (5.14) at scale `N`, with squarefree norm (forced by the
Möbius factor `μ(|z|²)`) and free of primes `≤ P` (5.8).  Every `z` with `β z ≠ 0` for a
coefficient `β` of `IsBetaCoeff` lies in this set (`beta_ne_zero_structure`). -/
def polarSupp (Pa : Work.FITop.Params) (φ : ℝ) : Finset GaussianInt :=
  (Work.FITop.boxN Pa).filter (fun z =>
    Work.FITop3.InPolarBox Pa φ z ∧ Squarefree (Work.FIPlan.gnorm z)
      ∧ Work.FITop3.NoSmallPrimes Pa z)

/-- Membership in `polarSupp`. -/
lemma mem_polarSupp {Pa : Work.FITop.Params} {φ : ℝ} {z : GaussianInt} :
    z ∈ polarSupp Pa φ ↔ z ∈ Work.FITop.boxN Pa ∧ Work.FITop3.InPolarBox Pa φ z
      ∧ Squarefree (Work.FIPlan.gnorm z) ∧ Work.FITop3.NoSmallPrimes Pa z := by
  simp [polarSupp, and_assoc]

/-- The **off-diagonal non-coprime pair count** of (5.22): the triples `(w, z₁, z₂)` with
`w ∈ boxM Pa`, `z₁ ≠ z₂` both in `polarSupp Pa φ`, the pair `(z₁, z₂)` not coprime in `ℤ[i]`,
counted with multiplicity `Z(Re wz₁)·Z(Re wz₂)` (`Zint`).  This is the count whose estimate
(`≪ (M^{3/4}N^{3/4} + P^{-1}M^{1/2}N^{3/2})(log MN)^{516}`, *FI* pp. 971–972) is the `P^{-1}`
saving of (5.22); it is delegated as `Work.FIArea1.offdiag_polar_count`. -/
def offdiagPairSum (Pa : Work.FITop.Params) (φ : ℝ) : ℝ :=
  ∑ w ∈ Work.FITop.boxM Pa, ∑ z1 ∈ polarSupp Pa φ, ∑ z2 ∈ polarSupp Pa φ,
    (if z1 = z2 ∨ Work.FIPlan.GaussCoprime z1 z2 then 0
     else (Work.FIPlan.Zint (Work.FIPlan.cForm w z1) : ℝ)
          * (Work.FIPlan.Zint (Work.FIPlan.cForm w z2) : ℝ))

/-! ## Route notes for `Work.FIArea1.offdiag_polar_count`

*(These notes are for the prover of `Work.FIArea1.offdiag_polar_count`; nothing below is used by
`conjunct2_le`.)*

The estimate to prove is
`offdiagPairSum Pa φ ≤ c(M^{3/4}N^{3/4} + P^{-1}M^{1/2}N^{3/2})(log(MN))^{516}`.

* Every counted pair `(z₁, z₂)` (both in the polar box, squarefree norm, `(z,Π) = 1`, not coprime)
  shares a *Gaussian* prime `π` with `|π|² = p` a rational prime `> P`
  (`Work.FIArea1.common_prime_of_not_coprime` + `NoSmallPrimes`); squarefreeness of `|z_i|²` forces
  `p ≡ 1 (mod 4)`, `π | z_i` exactly once, and `z_i = π z_i'` with `|z_i'|² ∈ (N/p, 2N/p]`.
* *The naive per-`π` application of the derivation of FI Lemma 5.1 is not enough*: at the reduced
  parameters `(Mp, N/p)` (outer `W = wπ`, inner `z_i'`; the `c_i` range is still
  `|c_i| ≤ 2(MN)^{1/4}` because `|W||z_i'| = |w||z_i|`) it gives only `≪ M^{1/2}N^{3/2}p^{-1}` per
  `π`, and `Σ_{p>P} 1/p` diverges (log log) — that route loses the whole `P^{-1}`.
* *Where the extra `p^{-1}` comes from*: in the substituted variables the pair
  `(z₁', z₂', c₁, c₂)` determines the outer point `W` by the linear system of Lemma 5.1,
  `W = i·(c₁²·conj z₂' - c₂²·conj z₁')/Δ'(z₁',z₂')`; on top of the congruence
  `c₁²z₂' ≡ c₂²z₁' (mod |Δ'|)` (which makes `W ∈ ℤ[i]`) one must impose the *extra* divisibility
  `π | W` (equivalently `w = W/π ∈ ℤ[i]`).  For fixed `(z₁', z₂', c₁)` this is a congruence
  condition on `c₂` modulo `π`, so it cuts the `c₂`-range of length `≈ (MN)^{1/4}` down to
  `≪ (MN)^{1/4}/p + 1`: a factor `p^{-1}`.  Together with the `p^{-1}` inherited from the reduced
  inner scale `N/p` this is the required `p^{-2}` per `π`.
* Summing over `π`: `Σ_{|π|²>P} |π|^{-2} ≤ 2Σ_{p>P} p^{-2} ≤ 4/P`
  (each Gaussian prime `π` has `|π|² = p` or `p²` for a rational prime `p`, and `n ↦ n^{-2}` is
  summable with tail `≤ 2/P`).
* The diagonal (`z₁ = z₂`) term `M^{3/4}N^{3/4}` on the right is *slack* on this side: the sum
  `offdiagPairSum` excludes `z₁ = z₂`.  Hence a crude bound suffices for small `N` (for `N ≤ 4/3`
  there is no `z` with `N < |z|² ≤ (1+θ)N` and a squarefree norm free of primes `≤ P`, so the sum
  vanishes), and any `log` losses in the dyadic summation over `π` are absorbed by
  `(log(MN))^{516}`.

The arithmetic inputs of Lemma 5.1 are already in the workspace:
`Work.FIArea1.lemma22_divisor_splitting` (FI Lemma 2.2, all three assertions) and
`Work.FIArea1.count_line_squares` / `Work.FIArea1.count_annulus` (the one-condition lattice
counts). -/

end

end Work.FIArea1
