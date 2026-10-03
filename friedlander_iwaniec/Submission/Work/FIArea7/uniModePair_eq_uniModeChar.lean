import Mathlib
import Submission.Work.FIArea7.UniMollify6
import Submission.Work.FIArea7.guard_eq_unitInd_mul_omegaDetect
import Submission.Work.FIArea7.reflSign_separable
import Submission.Work.FIArea7.pull6_mode_pair_eq

namespace Work.FIArea7

attribute [local instance] Classical.propDecidable

/-- **The pair identity, term by term.**  For a single pair `(z₁,z₂)` the inner summand of
`uniModePair` (with the pair guard `4be ∣ |Δ|` and the Kubota power `i^{(s₂-s₁)/2}`) agrees with
the inner summand of `uniModeChar` (with the unit indicators and the coefficient `uniCoeff`).

Three cases.  If `(z₁,z₂)` is not Gaussian-coprime both summands are `0`.  If it is, and
`4be ∣ |Δ|`, this is `Work.FIArea7.pull6_mode_pair_eq`.  If it is but `4be ∤ |Δ|`, the pair
summand is `0` while the detection sum `omegaDetect` vanishes by
`Work.FIArea7.guard_omegaSum_eq_zero_of_not_dvd`, so the character summand is `0` too. -/
private lemma uniModePair_inner_eq {Pa : Work.FITop.Params} {φ : ℝ} {z0 : GaussianInt}
    {β : GaussianInt → ℂ} (hβ : Work.FITop4.IsBetaCoeff6 Pa φ z0 β) (b e : ℕ) (k : ℤ)
    [NeZero (4 * b * e)] (ε : GaussianInt → ℤ)
    (hε : ∀ z1 z2 : GaussianInt, Work.FITop3.InPolarBox Pa φ z1 → Work.FITop3.InPolarBox Pa φ z2 →
        Work.FIArea7.reflSign z1 z2 = ε z1 * ε z2) (z1 z2 : GaussianInt) :
    (if Work.FIPlan.GaussCoprime z1 z2 ∧ 4 * b * e ∣ Work.FIPlan.absDelta z1 z2 then
        (Work.FIArea7.reflSign z1 z2 : ℂ) * Work.FIArea7.omegaDetect (4 * b * e) e z1 z2
          * Complex.I ^ (((z2.re - 1) / 2 : ℤ) - ((z1.re - 1) / 2 : ℤ))
          * (Work.FIArea7.betaPrime β z1 * star (Work.FIArea7.betaPrime β z2))
          * (Work.FIArea7.uniPow z1 k * star (Work.FIArea7.uniPow z2 k))
       else 0)
      = (if Work.FIPlan.GaussCoprime z1 z2 then
          Work.FIArea7.unitInd (4 * b * e) z1 * Work.FIArea7.unitInd (4 * b * e) z2
            * (Work.FIArea7.uniCoeff ε β k z1 * star (Work.FIArea7.uniCoeff ε β k z2))
            * Work.FIArea7.omegaDetect (4 * b * e) e z1 z2
         else 0) := by
  by_cases hc : Work.FIPlan.GaussCoprime z1 z2
  · rw [if_pos hc]
    by_cases hQ : 4 * b * e ∣ Work.FIPlan.absDelta z1 z2
    · rw [if_pos ⟨hc, hQ⟩]
      have hp := Work.FIArea7.pull6_mode_pair_eq hβ b e k ε hε hc hQ
      rwa [← Work.FIArea7.omegaDetect_unfold6 (4 * b * e) e z1 z2] at hp
    · rw [if_neg (fun h => hQ h.2)]
      have h0 : Work.FIArea7.omegaDetect (4 * b * e) e z1 z2 = 0 := by
        rw [Work.FIArea7.omegaDetect_unfold6 (4 * b * e) e z1 z2]
        exact Work.FIArea7.guard_omegaSum_eq_zero_of_not_dvd (Q := 4 * b * e) (e := e) z1 z2 hQ
      rw [h0]; ring
  · rw [if_neg hc, if_neg (fun h => hc h.1)]

/--
**`uniModePair` is `uniModeChar`**: the pair-sum form of a Fourier mode (with the explicit pair
guard `4be ∣ |Δ|`) equals the `unitInd`/`ω`-sum form produced by the §16 character expansion
(at modulus `Q = 4be` and coefficient `c = uniCoeff ε β k`).

The two sums have the same index set, so it suffices to identify the summands pair by pair
(`uniModePair_inner_eq`): both vanish off the Gaussian-coprime pairs; on a coprime pair with
`4be ∣ |Δ|` the identity is `Work.FIArea7.pull6_mode_pair_eq`; on a coprime pair without the guard
the detection sum `omegaDetect` vanishes (`Work.FIArea7.guard_omegaSum_eq_zero_of_not_dvd`).
-/
theorem uniModePair_eq_uniModeChar {Pa : Work.FITop.Params} {φ : ℝ} {z0 : GaussianInt}
    {β : GaussianInt → ℂ} (hβ : Work.FITop4.IsBetaCoeff6 Pa φ z0 β) (b e : ℕ) (k : ℤ)
    [NeZero (4 * b * e)] (ε : GaussianInt → ℤ)
    (hε : ∀ z1 z2 : GaussianInt, Work.FITop3.InPolarBox Pa φ z1 → Work.FITop3.InPolarBox Pa φ z2 →
        Work.FIArea7.reflSign z1 z2 = ε z1 * ε z2) :
    Work.FIArea7.uniModePair Pa b e β k = Work.FIArea7.uniModeChar Pa b e β k ε := by
  unfold Work.FIArea7.uniModePair Work.FIArea7.uniModeChar
  refine Finset.sum_congr rfl (fun z1 _ => Finset.sum_congr rfl (fun z2 _ => ?_))
  exact uniModePair_inner_eq hβ b e k ε hε z1 z2

end Work.FIArea7
