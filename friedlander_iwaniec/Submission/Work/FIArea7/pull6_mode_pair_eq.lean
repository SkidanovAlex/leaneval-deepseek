import Mathlib
import Submission.Work.FIArea7.UniMollify6
import Submission.Work.FIArea7.WBOmega6
import Submission.Work.FIArea7.guard_eq_unitInd_mul_omegaDetect
import Submission.Work.FIArea7.reflSign_separable
import Submission.Work.FIArea7.Section16Expansion

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false

namespace Work.FIArea7

/-- **The power of `i` of the (17.5) insertion is trivial on a fixed class mod `8`.**

For `z₁, z₂` with odd real parts and `z₁ ≡ z₂ (mod 8)` the exponent `(r₂ − 1)/2 − (r₁ − 1)/2` is
divisible by `4`, hence `i^{(r₂−1)/2 − (r₁−1)/2} = 1`.  This is the paper's remark underlying the
insertion of the factor `i^{(r−1)/2}` into (17.5): a non-zero round-6 coefficient is supported on a
single class mod eight (`Work.FITop4.IsBetaCoeff6.sameClass`). -/
private lemma I_zpow_eq_one_of_sameClass8 {z1 z2 : GaussianInt} (h1 : Odd z1.re) (h2 : Odd z2.re)
    (h8 : z1.re ≡ z2.re [ZMOD 8]) :
    Complex.I ^ (((z2.re - 1) / 2 : ℤ) - ((z1.re - 1) / 2 : ℤ)) = 1 := by
  apply Work.FIArea7.I_zpow_eq_one_of_four_dvd
  obtain ⟨k, hk⟩ := h1
  obtain ⟨l, hl⟩ := h2
  have hk' : (z1.re - 1) / 2 = k := by rw [hk]; omega
  have hl' : (z2.re - 1) / 2 = l := by rw [hl]; omega
  rw [hk', hl']
  have hdvd : (8 : ℤ) ∣ z2.re - z1.re := h8.dvd
  rw [hk, hl] at hdvd
  have h2d : (8 : ℤ) ∣ 2 * (l - k) := by
    have e : (2 * l + 1) - (2 * k + 1) = 2 * (l - k) := by ring
    rwa [e] at hdvd
  obtain ⟨c, hc⟩ := h2d
  refine ⟨c, ?_⟩
  have : 2 * (l - k) = 2 * (4 * c) := by rw [hc]; ring
  exact mul_left_cancel₀ (by norm_num : (2 : ℤ) ≠ 0) this

theorem pull6_mode_pair_eq {Pa : Work.FITop.Params} {φ : ℝ} {z0 : GaussianInt}
    {β : GaussianInt → ℂ} (hβ : Work.FITop4.IsBetaCoeff6 Pa φ z0 β) (b e : ℕ)
    [NeZero (4 * b * e)] (k : ℤ) (ε : GaussianInt → ℤ)
    (hε : ∀ z1 z2 : GaussianInt, Work.FITop3.InPolarBox Pa φ z1 → Work.FITop3.InPolarBox Pa φ z2 →
        Work.FIArea7.reflSign z1 z2 = ε z1 * ε z2)
    {z1 z2 : GaussianInt} (hc : Work.FIPlan.GaussCoprime z1 z2)
    (hQ : 4 * b * e ∣ Work.FIPlan.absDelta z1 z2) :
    (Work.FIArea7.reflSign z1 z2 : ℂ) * Work.FIArea7.omegaDetect (4 * b * e) e z1 z2
        * Complex.I ^ (((z2.re - 1) / 2 : ℤ) - ((z1.re - 1) / 2 : ℤ))
        * (Work.FIArea7.betaPrime β z1 * star (Work.FIArea7.betaPrime β z2))
        * (Work.FIArea7.uniPow z1 k * star (Work.FIArea7.uniPow z2 k))
      = Work.FIArea7.unitInd (4 * b * e) z1 * Work.FIArea7.unitInd (4 * b * e) z2
          * (Work.FIArea7.uniCoeff ε β k z1 * star (Work.FIArea7.uniCoeff ε β k z2))
          * (∑ ω : ZMod (4 * b * e),
              (if ((z1.re : ZMod (4 * b * e)) = ω * (z2.re : ZMod (4 * b * e)))
                  ∧ ((z1.im : ZMod (4 * b * e)) = ω * (z2.im : ZMod (4 * b * e)))
                then (jacobiSym (ω.val : ℤ) e : ℂ) else 0)) := by
  -- the two shape lemmas for `uniCoeff`
  have hstar : ∀ z : GaussianInt, star (Work.FIArea7.uniCoeff ε β k z)
      = (ε z : ℂ) * star (Work.FIArea7.betaPrime β z) * star (Work.FIArea7.uniPow z k) := by
    intro z
    rw [Work.FIArea7.uniCoeff, star_mul, star_mul, star_intCast]
    ring
  have hun : ∀ z : GaussianInt, Work.FIArea7.uniCoeff ε β k z
      = (ε z : ℂ) * Work.FIArea7.betaPrime β z * Work.FIArea7.uniPow z k := fun z => rfl
  -- off the support of `β` both sides vanish
  by_cases hz1 : β z1 = 0
  · have hbp1 : Work.FIArea7.betaPrime β z1 = 0 := by rw [Work.FIArea7.betaPrime, hz1, mul_zero]
    have huc1 : Work.FIArea7.uniCoeff ε β k z1 = 0 := by
      rw [Work.FIArea7.uniCoeff, hbp1, mul_zero, zero_mul]
    rw [hbp1, huc1]; ring
  · by_cases hz2 : β z2 = 0
    · have hbp2 : star (Work.FIArea7.betaPrime β z2) = 0 := by
        rw [Work.FIArea7.betaPrime, hz2, mul_zero, star_zero]
      have huc2 : star (Work.FIArea7.uniCoeff ε β k z2) = 0 := by
        rw [Work.FIArea7.uniCoeff, Work.FIArea7.betaPrime, hz2]; simp
      rw [hbp2, huc2]; ring
    · -- on the support: the paper's side conditions hold, and all three correction factors are `1`
      have hb1 : Work.FITop3.InPolarBox Pa φ z1 := hβ.support hz1
      have hb2 : Work.FITop3.InPolarBox Pa φ z2 := hβ.support hz2
      have hP1 : Work.FIPlan.IsPrimary z1 := hb1.1
      have hP2 : Work.FIPlan.IsPrimary z2 := hb2.1
      have hs1 : Squarefree (Work.FIPlan.gnorm z1) := hβ.squarefree_gnorm hz1
      have hs2 : Squarefree (Work.FIPlan.gnorm z2) := hβ.squarefree_gnorm hz2
      have hsc : Work.FITop4.SameClass8 z1 z2 := hβ.sameClass hz1 hz2
      have hre : z1.re ≡ z2.re [ZMOD 8] := (Work.FIArea7.modEq_of_sameClass8 hsc).1
      have hε12 : Work.FIArea7.reflSign z1 z2 = ε z1 * ε z2 := hε z1 z2 hb1 hb2
      have hI : Complex.I ^ (((z2.re - 1) / 2 : ℤ) - ((z1.re - 1) / 2 : ℤ)) = 1 :=
        I_zpow_eq_one_of_sameClass8 hP1.1 hP2.1 hre
      have hQpos : 0 < 4 * b * e := Nat.pos_of_ne_zero (NeZero.ne (4 * b * e))
      have hcop2 : Nat.Coprime (Work.FIPlan.gnorm z2) (4 * b * e) :=
        Work.FIArea7.coprime_gnorm_of_dvd_absDelta hQpos hP1 hP2 hs1 hs2 hc hQ
      have hcop1 : Nat.Coprime (Work.FIPlan.gnorm z1) (4 * b * e) :=
        Work.FIArea7.coprime_gnorm_of_dvd_absDelta hQpos hP2 hP1 hs2 hs1 hc.symm
          (by rwa [Work.FIArea7.guard_absDelta_comm])
      have hu1 : Work.FIArea7.unitInd (4 * b * e) z1 = 1 := by
        rw [Work.FIArea7.unitInd, if_pos hcop1]
      have hu2 : Work.FIArea7.unitInd (4 * b * e) z2 = 1 := by
        rw [Work.FIArea7.unitInd, if_pos hcop2]
      rw [← Work.FIArea7.omegaDetect_unfold6 (4 * b * e) e z1 z2]
      rw [hI, hu1, hu2, hε12, hun z1, hstar z2]
      push_cast
      ring

end Work.FIArea7
