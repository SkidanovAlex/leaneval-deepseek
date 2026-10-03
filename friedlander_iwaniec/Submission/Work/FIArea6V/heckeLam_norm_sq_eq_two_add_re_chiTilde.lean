import Mathlib
import Submission.Work.FIArea5.S16Hecke.heckeLam_localRec
import Submission.Work.FIArea5.S16Hecke.splitPrimaryClass
import Submission.Work.FIArea5.S16Hecke.heckeLam_prime_eq_zero_of_ne_one_mod_four
import Submission.Work.FIArea6Hecke.chiTildeDefs
import Submission.Work.FIArea6HeckeV2.exists_log_heckeFp_le

/-!
# `Work.FIArea6V.heckeLam_norm_sq_eq_two_add_re_chiTilde`

At a split rational prime `p ≡ 1 (mod 4)` with `p ∤ 4d`, the `p`-th Hecke eigenvalue of the
Grössencharacter `ψ_χ(z) = χ(z)(z/|z|)^m` satisfies

  `‖λ_χ(p)‖² = 2 + Re λ_{χ̃}(p)`   with `χ̃(z) = χ(z)/χ(z̄)` and weight `2m`.

This is the local statement that turns the auxiliary character `χ̃` into the square modulus of
`λ_χ(p)`; it is what drives the divergence of `∑ ‖λ_χ(p)‖²/p`.

## Mathematics

`p ≡ 1 (4)` splits in `ℤ[i]`: `splitPrimaryClass` produces the two primary primes `π`, `π'` of
norm `p`, conjugate to each other (`star_eq_of_split_v`).  Writing `A = ψ_χ(π)`, `B = ψ_χ(π')`,

* `λ_χ(p) = A + B` and `λ_{χ̃}(p) = A' + B'` with `A' = ψ_{χ̃}(π)`, `B' = ψ_{χ̃}(π')`;
* `‖A‖ = ‖B‖ = 1` (since `π, π'` are units mod `4d` and have norm `p ∤ 4d`);
* `A' · B = A` and `B' · A = B` (`ψ_χ̃(z)·ψ_χ(z̄) = ψ_χ(z)`, plus `π̄ = π'`).

Then `A' = A/B = A·conj B`, so `‖A + B‖² = ‖A‖² + ‖B‖² + 2 Re(A·conj B) = 2 + 2 Re A'`, while
`B' = conj A'` gives `Re(A' + B') = 2 Re A'`, hence the identity.
-/

set_option autoImplicit false

namespace Work.FIArea6V

open Work.FIPlan
open Work.FIArea5.S16Hecke
open Work.FIArea6Hecke

noncomputable section

/-! ## Elementary Gaussian-integer facts -/

private lemma toComplex_star_v (z : GaussianInt) : (star z).toComplex = star (z.toComplex) := by
  apply Complex.ext <;> simp

private lemma gnorm_star_v (z : GaussianInt) : gnorm (star z) = gnorm z := by
  simp only [gnorm, Zsqrtd.norm_conj]

private lemma isPrimary_star_v {z : GaussianInt} (hz : IsPrimary z) : IsPrimary (star z) := by
  obtain ⟨hodd, heven, hmod⟩ := hz
  refine ⟨?_, ?_, ?_⟩
  · simpa [Zsqrtd.re_star] using hodd
  · simpa [Zsqrtd.im_star] using heven.neg
  · rw [Zsqrtd.im_star, Zsqrtd.re_star]
    have hsym : -(z.re - 1) ≡ z.re - 1 [ZMOD 4] := by
      rw [Int.modEq_iff_dvd]
      obtain ⟨k, hk⟩ := hodd
      exact ⟨k, by rw [hk]; ring⟩
    exact hmod.neg.trans hsym

private lemma gnorm_pos_v {z : GaussianInt} (hz : z ≠ 0) : 0 < gnorm z := by
  rcases Nat.eq_zero_or_pos (gnorm z) with h | h
  · exfalso
    apply hz
    have h2 : ((gnorm z : ℕ) : ℤ) = z.re ^ 2 + z.im ^ 2 := by
      rw [gnorm, Int.natAbs_of_nonneg (Zsqrtd.norm_nonneg (by norm_num : (-1 : ℤ) ≤ 0) z),
        Zsqrtd.norm_def]
      ring
    rw [h] at h2
    norm_num at h2
    have h1 : z.re = 0 := by
      have h1 : z.re ^ 2 = 0 := by nlinarith [sq_nonneg z.re, sq_nonneg z.im]
      exact sq_eq_zero_iff.mp h1
    have h3 : z.im = 0 := by
      have h1 : z.im ^ 2 = 0 := by nlinarith [sq_nonneg z.re, sq_nonneg z.im]
      exact sq_eq_zero_iff.mp h1
    exact Zsqrtd.ext h1 h3
  · exact h

private lemma not_sq_of_prime_v {p : ℕ} (hp : p.Prime) {m : ℤ} (h : m ^ 2 = (p : ℤ)) : False := by
  rw [pow_two] at h
  have h2 : m.natAbs * m.natAbs = p := by
    have := congrArg Int.natAbs h
    rw [Int.natAbs_mul, Int.natAbs_natCast] at this
    exact_mod_cast this
  have hdvd : m.natAbs ∣ p := ⟨m.natAbs, by rw [← h2]⟩
  rcases hp.eq_one_or_self_of_dvd m.natAbs hdvd with h1 | h1
  · rw [h1] at h2; simp at h2; exact hp.ne_one h2.symm
  · rw [h1] at h2
    have : p * p = p * 1 := by rw [h2, mul_one]
    exact hp.ne_one (Nat.mul_left_cancel hp.pos this)

/-- The two primary primes of norm `p ≡ 1 (4)` are conjugate to each other. -/
private lemma star_eq_of_split_v {p : ℕ} (hp : p.Prime)
    {π π' : GaussianInt} (hπ : IsPrimary π)
    (hgπ : gnorm π = p) (_hgπ' : gnorm π' = p)
    (hclass : ∀ ν z, IsPrimary z → gnorm z = p ^ ν → ∃! a, a ≤ ν ∧ z = π ^ a * π' ^ (ν - a)) :
    star π = π' := by
  have hprim : IsPrimary (star π) := isPrimary_star_v hπ
  have hgn : gnorm (star π) = p ^ 1 := by rw [pow_one, gnorm_star_v, hgπ]
  obtain ⟨a, ha, haz⟩ := (hclass 1 (star π) hprim hgn).exists
  interval_cases a
  · simpa using haz
  · exfalso
    have hstar : star π = π := by simpa using haz
    have him : π.im = 0 := by
      have := congrArg Zsqrtd.im hstar
      rw [Zsqrtd.im_star] at this
      linarith
    have hsq : π.re ^ 2 = (p : ℤ) := by
      have h2 : ((gnorm π : ℕ) : ℤ) = π.re ^ 2 + π.im ^ 2 := by
        rw [gnorm, Int.natAbs_of_nonneg (Zsqrtd.norm_nonneg (by norm_num : (-1 : ℤ) ≤ 0) π),
          Zsqrtd.norm_def]
        ring
      rw [hgπ, him] at h2
      simpa using h2.symm
    exact not_sq_of_prime_v hp hsq

/-! ## The unit modulus of `ψ` and the key `ψ_χ̃ · ψ_χ ∘ conj` identity -/

private lemma norm_psi_eq_one_of_isUnit_v {d : ℕ} {chi : GaussianInt → ℂ}
    (hchi : IsCharMod4dStrict d chi) (m : ℤ) {z : GaussianInt} (hz : IsUnitMod4d d z)
    (hz0 : z ≠ 0) : ‖psi chi m z‖ = 1 := by
  rw [psi, norm_mul, norm_zpow, Work.FIArea6HeckeV2.norm_chi_eq_one_of_isUnitMod4d' hchi hz,
    one_mul]
  have hgpos : 0 < (gnorm z : ℝ) := by exact_mod_cast gnorm_pos_v hz0
  have h1 : ‖z.toComplex / (((Real.sqrt (gnorm z : ℝ) : ℝ)) : ℂ)‖ = 1 := by
    rw [norm_div, norm_toComplex]
    rw [show ‖(((Real.sqrt (gnorm z : ℝ) : ℝ)) : ℂ)‖ = Real.sqrt (gnorm z : ℝ) from by
      simp [abs_of_nonneg (Real.sqrt_nonneg _)]]
    exact div_self (ne_of_gt (Real.sqrt_pos_of_pos hgpos))
  rw [h1, one_zpow]

private lemma psi_chiTilde_mul_psi_star_v {d : ℕ} {chi : GaussianInt → ℂ}
    (hchi : IsCharMod4dStrict d chi) (m : ℤ) {z : GaussianInt} (hz : IsUnitMod4d d z)
    (hz0 : z ≠ 0) :
    psi (chiTilde chi) (2 * m) z * psi chi m (star z) = psi chi m z := by
  have hzstar : IsUnitMod4d d (star z) := Work.FIArea6HeckeV2.isUnitMod4d_star' hz
  have hchi_ne : chi (star z) ≠ 0 := by
    have h := Work.FIArea6HeckeV2.norm_chi_eq_one_of_isUnitMod4d' hchi hzstar
    intro hh; rw [hh] at h; simp at h
  have hgpos : 0 < (gnorm z : ℝ) := by exact_mod_cast gnorm_pos_v hz0
  set W : ℂ := z.toComplex / ((Real.sqrt (gnorm z : ℝ) : ℝ) : ℂ) with hW
  have hnormW : ‖W‖ = 1 := by
    rw [hW, norm_div, norm_toComplex]
    rw [show ‖(((Real.sqrt (gnorm z : ℝ) : ℝ)) : ℂ)‖ = Real.sqrt (gnorm z : ℝ) from by
      simp [abs_of_nonneg (Real.sqrt_nonneg _)]]
    exact div_self (ne_of_gt (Real.sqrt_pos_of_pos hgpos))
  have hWstar : W * star W = 1 := by
    have h : W * star W = ((Complex.normSq W : ℝ) : ℂ) := Complex.mul_conj W
    rw [h, Complex.normSq_eq_norm_sq, hnormW]; norm_num
  have hWne : W ≠ 0 := by intro h; rw [h] at hWstar; simp at hWstar
  have hWd : (star z).toComplex / ((Real.sqrt (gnorm (star z) : ℝ) : ℝ) : ℂ) = star W := by
    rw [toComplex_star_v, gnorm_star_v, hW]
    have hd : star (GaussianInt.toComplex z / (((Real.sqrt (gnorm z : ℝ) : ℝ)) : ℂ))
        = star (GaussianInt.toComplex z) / (((Real.sqrt (gnorm z : ℝ) : ℝ)) : ℂ) := by
      rw [← starRingEnd_apply, map_div₀ (starRingEnd ℂ), starRingEnd_apply, Complex.conj_ofReal]
    rw [hd]
  have hWid : W ^ (2 * m) * (star W) ^ m = W ^ m := by
    rw [show 2 * m = m + m by ring, zpow_add₀ hWne, mul_assoc, ← mul_zpow, hWstar]
    simp
  rw [psi, psi, psi, chiTilde]
  rw [hWd]
  calc (chi z / chi (star z)) * W ^ (2 * m) * (chi (star z) * (star W) ^ m)
      = chi z * (W ^ (2 * m) * (star W) ^ m) := by field_simp [hchi_ne]
    _ = chi z * W ^ m := by rw [hWid]

/-! ## The main identity -/

theorem heckeLam_norm_sq_eq_two_add_re_chiTilde {d : ℕ} (hd : 1 ≤ d) {chi : GaussianInt → ℂ}
    (hchi : Work.FIArea5.S16Hecke.IsCharMod4dStrict d chi) (m : ℤ) {p : ℕ} (hp : p.Prime)
    (hp4 : p % 4 = 1) (hpd : ¬ p ∣ 4 * d) :
    ‖Work.FIArea5.S16Hecke.heckeLam chi m p‖ ^ 2
      = 2 + (Work.FIArea5.S16Hecke.heckeLam (Work.FIArea6Hecke.chiTilde chi) (2 * m) p).re := by
  obtain ⟨π, π', hπp, hπp', hgπ, hgπ', -, -, -, hclass⟩ := splitPrimaryClass p hp hp4
  have hstar : star π = π' := star_eq_of_split_v hp hπp hgπ hgπ' hclass
  have hstar' : star π' = π := by rw [← hstar, star_star]
  have hgn0 : gnorm (0 : GaussianInt) = 0 := by simp [gnorm]
  have hπ0 : π ≠ 0 := by
    intro h; rw [h, hgn0] at hgπ; exact hp.ne_zero hgπ.symm
  have hπ'0 : π' ≠ 0 := by
    intro h; rw [h, hgn0] at hgπ'; exact hp.ne_zero hgπ'.symm
  have hπu : IsUnitMod4d d π :=
    Work.FIArea6Hecke.R.isUnitMod4d_of_gnorm_eq_prime_pow hd hp hpd (ν := 1) (by norm_num)
      (by simpa using hgπ)
  have hπ'u : IsUnitMod4d d π' :=
    Work.FIArea6Hecke.R.isUnitMod4d_of_gnorm_eq_prime_pow hd hp hpd (ν := 1) (by norm_num)
      (by simpa using hgπ')
  have hmul : ∀ z w : GaussianInt, chi (z * w) = chi z * chi w := hchi.1.2.1
  have hchi1 : chi 1 = 1 := hchi.1.1
  have htil_mul : ∀ z w : GaussianInt,
      chiTilde chi (z * w) = chiTilde chi z * chiTilde chi w :=
    Work.FIArea6HeckeV2.chiTilde_mul' hchi
  have htil1 : chiTilde chi 1 = 1 := Work.FIArea6HeckeV2.chiTilde_one' hchi
  have hLam : heckeLam chi m p = psi chi m π + psi chi m π' := by
    have h := heckeLam_splitSum chi m p hp.pos hmul hchi1 π π' hπp hπp' hgπ hgπ' hclass 1
    simpa [pow_one, geo_one] using h
  have hLamd : heckeLam (chiTilde chi) (2 * m) p
      = psi (chiTilde chi) (2 * m) π + psi (chiTilde chi) (2 * m) π' := by
    have h := heckeLam_splitSum (chiTilde chi) (2 * m) p hp.pos htil_mul htil1 π π'
      hπp hπp' hgπ hgπ' hclass 1
    simpa [pow_one, geo_one] using h
  have hA1 : ‖psi chi m π‖ = 1 := norm_psi_eq_one_of_isUnit_v hchi m hπu hπ0
  have hB1 : ‖psi chi m π'‖ = 1 := norm_psi_eq_one_of_isUnit_v hchi m hπ'u hπ'0
  have hAn : psi chi m π * star (psi chi m π) = 1 := by
    have h := Complex.mul_conj (psi chi m π)
    rw [Complex.normSq_eq_norm_sq, hA1] at h
    norm_num at h
    exact h
  have hBn : psi chi m π' * star (psi chi m π') = 1 := by
    have h := Complex.mul_conj (psi chi m π')
    rw [Complex.normSq_eq_norm_sq, hB1] at h
    norm_num at h
    exact h
  have hAdB : psi (chiTilde chi) (2 * m) π * psi chi m π' = psi chi m π := by
    have h := psi_chiTilde_mul_psi_star_v hchi m hπu hπ0
    rw [hstar] at h
    exact h
  have hBdA : psi (chiTilde chi) (2 * m) π' * psi chi m π = psi chi m π' := by
    have h := psi_chiTilde_mul_psi_star_v hchi m hπ'u hπ'0
    rw [hstar'] at h
    exact h
  have hAdForm : psi (chiTilde chi) (2 * m) π = psi chi m π * star (psi chi m π') := by
    calc psi (chiTilde chi) (2 * m) π
        = psi (chiTilde chi) (2 * m) π * 1 := (mul_one _).symm
      _ = psi (chiTilde chi) (2 * m) π * (psi chi m π' * star (psi chi m π')) := by rw [hBn]
      _ = (psi (chiTilde chi) (2 * m) π * psi chi m π') * star (psi chi m π') := by ring
      _ = psi chi m π * star (psi chi m π') := by rw [hAdB]
  have hBdForm : psi (chiTilde chi) (2 * m) π' = psi chi m π' * star (psi chi m π) := by
    calc psi (chiTilde chi) (2 * m) π'
        = psi (chiTilde chi) (2 * m) π' * 1 := (mul_one _).symm
      _ = psi (chiTilde chi) (2 * m) π' * (psi chi m π * star (psi chi m π)) := by rw [hAn]
      _ = (psi (chiTilde chi) (2 * m) π' * psi chi m π) * star (psi chi m π) := by ring
      _ = psi chi m π' * star (psi chi m π) := by rw [hBdA]
  have hstarAd : star (psi (chiTilde chi) (2 * m) π) = psi (chiTilde chi) (2 * m) π' := by
    rw [hAdForm, hBdForm, star_mul, star_star]
  have hre : (psi (chiTilde chi) (2 * m) π + psi (chiTilde chi) (2 * m) π').re
      = 2 * (psi (chiTilde chi) (2 * m) π).re := by
    have hca : psi (chiTilde chi) (2 * m) π + star (psi (chiTilde chi) (2 * m) π)
        = ↑(2 * (psi (chiTilde chi) (2 * m) π).re) :=
      Complex.add_conj (psi (chiTilde chi) (2 * m) π)
    rw [← hstarAd, hca]
    exact Complex.ofReal_re _
  have hnorm : ‖psi chi m π + psi chi m π'‖ ^ 2
      = 2 + 2 * (psi (chiTilde chi) (2 * m) π).re := by
    have h := Complex.normSq_add (psi chi m π) (psi chi m π')
    have hAB : Complex.normSq (psi chi m π + psi chi m π')
        = ‖psi chi m π + psi chi m π'‖ ^ 2 := Complex.normSq_eq_norm_sq _
    have hAn' : Complex.normSq (psi chi m π) = 1 := by
      have : Complex.normSq (psi chi m π) = ‖psi chi m π‖ ^ 2 := Complex.normSq_eq_norm_sq _
      rw [this, hA1]; norm_num
    have hBn' : Complex.normSq (psi chi m π') = 1 := by
      have : Complex.normSq (psi chi m π') = ‖psi chi m π'‖ ^ 2 := Complex.normSq_eq_norm_sq _
      rw [this, hB1]; norm_num
    have hconv : psi chi m π * (starRingEnd ℂ) (psi chi m π')
        = psi chi m π * star (psi chi m π') := rfl
    rw [hAB, hAn', hBn'] at h
    rw [hconv] at h
    rw [← hAdForm] at h
    rw [h]
    ring
  rw [hLam, hLamd, hnorm, hre]

end

end Work.FIArea6V
