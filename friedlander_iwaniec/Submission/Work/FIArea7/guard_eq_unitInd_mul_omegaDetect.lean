/-
# The guard identity: `[4be ∣ |Δ|]` against the unit indicators

The `ω`-detection sum of (17.9),

  `S(z₁,z₂) = Σ_{ω : ZMod Q} [z₁ ≡ ω z₂ (mod Q)]·(ω|e)`,   `Q = 4be`,

is multiplied downstream either by the *pair guard* `[Q ∣ |Δ(z₁,z₂)|]` or by the product of the
two *unit indicators* `unitInd Q z₁ · unitInd Q z₂`.  This file proves the two agree in the §17
situation: on the support of the round-6 coefficient `IsBetaCoeff6`, and for a Gaussian-coprime
pair `(z₁,z₂)`.

Two facts are used, in opposite directions.

* If `Q ∣ |Δ|`, then (17.2)–(17.4) of the paper hold for this pair, so neither `|z₁|²` nor `|z₂|²`
  shares a prime with `Q`: this is `coprime_gnorm_of_dvd_absDelta`, applied once to `(z₁,z₂)` and
  once to the swapped pair `(z₂,z₁)` (legitimate because `|Δ(z₂,z₁)| = |Δ(z₁,z₂)|`).  Hence both
  unit indicators are `1`.

* If `Q ∤ |Δ|`, the detection sum itself vanishes: a class `ω` with `z₁ ≡ ω z₂ (mod Q)`
  forces `Q ∣ Δ(z₁,z₂)` (multiply the two coordinate congruences), hence `Q ∣ |Δ|`, a
  contradiction.  So `S = 0` and both sides are `0`.

Note that neither direction needs the coprimality `(Q, |z₂|²) = 1` that (19.7) carries, and the
first direction needs no positivity of `|Δ|` (the coprime lemmas hold for `|Δ| = 0` as well).
-/
import Mathlib
import Submission.Work.FIArea7.UniChain6
import Submission.Work.FIArea7.Section16Expansion
import Submission.Work.FIArea7.coprime_gnorm_of_dvd_absDelta
import Submission.Work.FIArea7.dvd_delta_iff_exists_omega

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false

open scoped BigOperators

namespace Work.FIArea7

/-- A class `ω (mod Q)` satisfying the two coordinate congruences forces `Q ∣ Δ(z₁,z₂)`: read the
congruences in `ZMod Q`, where `Δ(z₁,z₂) = r₁s₂ − s₁r₂` becomes `ω r₂ s₂ − ω s₂ r₂ = 0`. -/
lemma guard_dvd_Delta_of_omega_congr {Q : ℕ} {z1 z2 : GaussianInt} {ω : ZMod Q}
    (hre : (z1.re : ZMod Q) = ω * (z2.re : ZMod Q))
    (him : (z1.im : ZMod Q) = ω * (z2.im : ZMod Q)) :
    (Q : ℤ) ∣ Work.FIPlan.Delta z1 z2 := by
  apply (ZMod.intCast_zmod_eq_zero_iff_dvd (Work.FIPlan.Delta z1 z2) Q).mp
  rw [Work.FIArea7.Delta_eq]
  push_cast
  rw [hre, him]
  ring

/-- **The detection sum vanishes off the guard.**  If `Q ∤ |Δ(z₁,z₂)|` then no class `ω` can
satisfy `z₁ ≡ ω z₂ (mod Q)`, so the (17.9) inner sum over `ω` is `0`. -/
lemma guard_omegaSum_eq_zero_of_not_dvd {Q e : ℕ} [NeZero Q] (z1 z2 : GaussianInt)
    (h : ¬ Q ∣ Work.FIPlan.absDelta z1 z2) :
    (∑ ω : ZMod Q, (if ((z1.re : ZMod Q) = ω * (z2.re : ZMod Q)) ∧
        ((z1.im : ZMod Q) = ω * (z2.im : ZMod Q))
      then (jacobiSym (ω.val : ℤ) e : ℂ) else 0)) = 0 := by
  refine Finset.sum_eq_zero (fun ω _ => ?_)
  rw [if_neg]
  rintro ⟨hre, him⟩
  apply h
  have hD : (Q : ℤ) ∣ Work.FIPlan.Delta z1 z2 := guard_dvd_Delta_of_omega_congr hre him
  have h2 : ((Q : ℤ)).natAbs ∣ (Work.FIPlan.Delta z1 z2).natAbs := Int.natAbs_dvd_natAbs.mpr hD
  simpa [Work.FIPlan.absDelta, Int.natAbs_natCast] using h2

/-- `Δ(z₂,z₁) = −Δ(z₁,z₂)` (the determinant changes sign under the swap). -/
lemma guard_Delta_swap (z1 z2 : GaussianInt) :
    Work.FIPlan.Delta z2 z1 = -Work.FIPlan.Delta z1 z2 := by
  rw [Work.FIArea7.Delta_eq, Work.FIArea7.Delta_eq]; ring

/-- `|Δ(z₂,z₁)| = |Δ(z₁,z₂)|`: the guard `Q ∣ |Δ|` is symmetric in the pair. -/
lemma guard_absDelta_comm (z1 z2 : GaussianInt) :
    Work.FIPlan.absDelta z2 z1 = Work.FIPlan.absDelta z1 z2 := by
  unfold Work.FIPlan.absDelta
  rw [guard_Delta_swap, Int.natAbs_neg]

/-- **The guard identity**, in the form isolated from the coefficient predicate: for primary,
squarefree-norm, Gaussian-coprime `z₁,z₂` the pair guard `[Q ∣ |Δ|]` and the product of unit
indicators `unitInd Q z₁·unitInd Q z₂` act identically on the (17.9) detection sum. -/
lemma guard_eq_of_primary {Q e : ℕ} [NeZero Q] {z1 z2 : GaussianInt}
    (hP1 : Work.FIPlan.IsPrimary z1) (hP2 : Work.FIPlan.IsPrimary z2)
    (hs1 : Squarefree (Work.FIPlan.gnorm z1)) (hs2 : Squarefree (Work.FIPlan.gnorm z2))
    (hc : IsCoprime z1 z2) :
    (if Q ∣ Work.FIPlan.absDelta z1 z2 then (1 : ℂ) else 0)
        * (∑ ω : ZMod Q,
            (if ((z1.re : ZMod Q) = ω * (z2.re : ZMod Q))
                ∧ ((z1.im : ZMod Q) = ω * (z2.im : ZMod Q))
              then (jacobiSym (ω.val : ℤ) e : ℂ) else 0))
      = Work.FIArea7.unitInd Q z1 * Work.FIArea7.unitInd Q z2
        * (∑ ω : ZMod Q,
            (if ((z1.re : ZMod Q) = ω * (z2.re : ZMod Q))
                ∧ ((z1.im : ZMod Q) = ω * (z2.im : ZMod Q))
              then (jacobiSym (ω.val : ℤ) e : ℂ) else 0)) := by
  have hQpos : 0 < Q := Nat.pos_of_ne_zero (NeZero.ne Q)
  by_cases hdiv : Q ∣ Work.FIPlan.absDelta z1 z2
  · have hcop2 : Nat.Coprime (Work.FIPlan.gnorm z2) Q :=
      Work.FIArea7.coprime_gnorm_of_dvd_absDelta hQpos hP1 hP2 hs1 hs2 hc hdiv
    have hcop1 : Nat.Coprime (Work.FIPlan.gnorm z1) Q :=
      Work.FIArea7.coprime_gnorm_of_dvd_absDelta hQpos hP2 hP1 hs2 hs1 hc.symm
        (by rwa [guard_absDelta_comm])
    have hu1 : Work.FIArea7.unitInd Q z1 = 1 := by rw [Work.FIArea7.unitInd, if_pos hcop1]
    have hu2 : Work.FIArea7.unitInd Q z2 = 1 := by rw [Work.FIArea7.unitInd, if_pos hcop2]
    rw [if_pos hdiv, hu1, hu2]; ring
  · have hS := guard_omegaSum_eq_zero_of_not_dvd (Q := Q) (e := e) z1 z2 hdiv
    rw [if_neg hdiv, hS]; ring

/-- **The guard identity for the §17 coefficient.**  For a round-6 coefficient `β`, on a pair in
its support (so both points are primary with squarefree norm) that is Gaussian-coprime, the pair
guard `[4be ∣ |Δ|]` of (17.9) may be replaced by the product of the unit indicators
`unitInd (4be) z₁·unitInd (4be) z₂` of the character expansion (16.11). -/
theorem guard_eq_unitInd_mul_omegaDetect {Pa : Work.FITop.Params} {φ : ℝ} {z0 : GaussianInt}
    {β : GaussianInt → ℂ} (hβ : Work.FITop4.IsBetaCoeff6 Pa φ z0 β)
    {z1 z2 : GaussianInt} (hz1 : β z1 ≠ 0) (hz2 : β z2 ≠ 0)
    (hc : Work.FIPlan.GaussCoprime z1 z2) (b e : ℕ) [NeZero (4 * b * e)] :
    (if 4 * b * e ∣ Work.FIPlan.absDelta z1 z2 then (1 : ℂ) else 0)
        * (∑ ω : ZMod (4 * b * e),
            (if ((z1.re : ZMod (4 * b * e)) = ω * (z2.re : ZMod (4 * b * e)))
                ∧ ((z1.im : ZMod (4 * b * e)) = ω * (z2.im : ZMod (4 * b * e)))
              then (jacobiSym (ω.val : ℤ) e : ℂ) else 0))
      = Work.FIArea7.unitInd (4 * b * e) z1 * Work.FIArea7.unitInd (4 * b * e) z2
        * (∑ ω : ZMod (4 * b * e),
            (if ((z1.re : ZMod (4 * b * e)) = ω * (z2.re : ZMod (4 * b * e)))
                ∧ ((z1.im : ZMod (4 * b * e)) = ω * (z2.im : ZMod (4 * b * e)))
              then (jacobiSym (ω.val : ℤ) e : ℂ) else 0)) := by
  have hP1 : Work.FIPlan.IsPrimary z1 := (hβ.support hz1).1
  have hP2 : Work.FIPlan.IsPrimary z2 := (hβ.support hz2).1
  have hs1 : Squarefree (Work.FIPlan.gnorm z1) := hβ.squarefree_gnorm hz1
  have hs2 : Squarefree (Work.FIPlan.gnorm z2) := hβ.squarefree_gnorm hz2
  exact guard_eq_of_primary hP1 hP2 hs1 hs2 hc

end Work.FIArea7
