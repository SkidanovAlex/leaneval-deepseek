/-
# `Submission.Work.FIArea7.KStar_bound` — *FI* (22.4), the bound for the coprimality-restricted
linear form `K*`

*FI* §22 proves, besides (22.3) for `K(N) = Σ∧_{z ∈ B} ψ(z)[wz]` (`Work.FIArea7.KSum_bound`), the
companion bound (22.4) for `K*(N) = Σ∧_{z ∈ B, (z,w)=1} ψ(z)[wz]`, at the cost of a factor `τ(|w|²)`:

  `K*(N) ≪ d(|k|+1)|w|τ(|w|²)N^{3/4} log(|w|N)`.

The reduction (this file) works on the fibres `KInnerStar` of `K*` (over `r = Re z`), uses the
Gaussian Möbius inversion of the coprimality indicator

  `1[(z,w) = 1] = Σ_{e ∣ w} μ(e) 1[e ∣ z]`

(`Work.FIArea7.KStarDivs.gauss_divs_moebius`, summed over the primary divisors of `w`), which turns
each fibre into a sum of `≪ τ(|w|²)` sums over the arithmetic progression `e ∣ r + is`
(`Work.FIArea7.KStarAP.dvd_and_primary_iff_modEq`) whose size is read off from
`Work.FIArea7.KStarAP.ap_char_chi_bound`; the weights `|e|^{-1/2}` are summed by
`Work.FIArea7.KStarDivs.sum_inv_sqrt_sqfree_gaussPrimDivs_le`.
-/
import Mathlib
import Submission.Work.FIArea7.KStarDefs
import Submission.Work.FIArea7.KStarBasic
import Submission.Work.FIArea7.KStarAP.ap_char_chi_bound
import Submission.Work.FIArea7.KStarAP.dvd_and_primary_iff_modEq
import Submission.Work.FIArea7.KStarDivs.gauss_divs_moebius
import Submission.Work.FIArea7.KStarDivs.sum_inv_sqrt_sqfree_gaussPrimDivs_le

set_option autoImplicit false
set_option maxHeartbeats 1600000

namespace Work.FIArea7

open Finset
open scoped BigOperators

attribute [local instance] Classical.propDecidable

noncomputable section

/-! ## Elementary facts about `gnorm` and the primary divisors -/

/-- `|Re z|² ≤ |z|²`. -/
lemma sq_natAbs_re_le_gnorm (z : GaussianInt) : z.re.natAbs ^ 2 ≤ Work.FIPlan.gnorm z := by
  rw [Work.FIPlan.gnorm, GaussianInt.natAbs_norm_eq, pow_two]
  exact Nat.le_add_right _ _

/-- `|Im z|² ≤ |z|²`. -/
lemma sq_natAbs_im_le_gnorm (z : GaussianInt) : z.im.natAbs ^ 2 ≤ Work.FIPlan.gnorm z := by
  rw [Work.FIPlan.gnorm, GaussianInt.natAbs_norm_eq, pow_two]
  exact Nat.le_add_left _ _

/-- `|Re z| ≤ |z|²`. -/
lemma natAbs_re_le_gnorm (z : GaussianInt) : z.re.natAbs ≤ Work.FIPlan.gnorm z := by
  rcases Nat.eq_zero_or_pos z.re.natAbs with h | h
  · omega
  · refine le_trans ?_ (sq_natAbs_re_le_gnorm z)
    calc z.re.natAbs = z.re.natAbs * 1 := (Nat.mul_one _).symm
      _ ≤ z.re.natAbs * z.re.natAbs := Nat.mul_le_mul_left _ h
      _ = z.re.natAbs ^ 2 := (pow_two _).symm

/-- `|Im z| ≤ |z|²`. -/
lemma natAbs_im_le_gnorm (z : GaussianInt) : z.im.natAbs ≤ Work.FIPlan.gnorm z := by
  rcases Nat.eq_zero_or_pos z.im.natAbs with h | h
  · omega
  · refine le_trans ?_ (sq_natAbs_im_le_gnorm z)
    calc z.im.natAbs = z.im.natAbs * 1 := (Nat.mul_one _).symm
      _ ≤ z.im.natAbs * z.im.natAbs := Nat.mul_le_mul_left _ h
      _ = z.im.natAbs ^ 2 := (pow_two _).symm

/-- `|e|² ∣ |w|²` for `e ∣ w`. -/
lemma gnorm_dvd_gnorm_of_dvd {e w : GaussianInt} (h : e ∣ w) :
    Work.FIPlan.gnorm e ∣ Work.FIPlan.gnorm w := by
  obtain ⟨c, rfl⟩ := h
  rw [gnorm_mul]
  exact dvd_mul_right _ _

/-- Membership in `gaussPrimDivs`: the primary divisors of a non-zero `w`. -/
lemma mem_gaussPrimDivs {w e : GaussianInt} (hw : w ≠ 0) :
    e ∈ gaussPrimDivs w ↔ e ∣ w ∧ Work.FIPlan.IsPrimary e := by
  rw [gaussPrimDivs, Finset.mem_filter, Finset.mem_image]
  constructor
  · rintro ⟨⟨p, hp, rfl⟩, h2⟩
    exact h2
  · rintro ⟨hdvd, hprim⟩
    have hw0' : Work.FIPlan.gnorm w ≠ 0 := fun h => hw (gnorm_eq_zero_iff.mp h)
    have hle : Work.FIPlan.gnorm e ≤ Work.FIPlan.gnorm w :=
      Nat.le_of_dvd (Nat.pos_of_ne_zero hw0') (gnorm_dvd_gnorm_of_dvd hdvd)
    have h1 : e.re.natAbs ≤ Work.FIPlan.gnorm w := le_trans (natAbs_re_le_gnorm e) hle
    have h2 : e.im.natAbs ≤ Work.FIPlan.gnorm w := le_trans (natAbs_im_le_gnorm e) hle
    have h1' : |e.re| ≤ ((Work.FIPlan.gnorm w : ℕ) : ℤ) := by
      have hc : ((e.re.natAbs : ℕ) : ℤ) = |e.re| := by
        simpa using Nat.cast_natAbs (α := ℤ) e.re
      have h2 : ((e.re.natAbs : ℕ) : ℤ) ≤ (((Work.FIPlan.gnorm w : ℕ)) : ℤ) := by
        exact_mod_cast h1
      rwa [hc] at h2
    have h2' : |e.im| ≤ ((Work.FIPlan.gnorm w : ℕ) : ℤ) := by
      have hc : ((e.im.natAbs : ℕ) : ℤ) = |e.im| := by
        simpa using Nat.cast_natAbs (α := ℤ) e.im
      have h2 : ((e.im.natAbs : ℕ) : ℤ) ≤ (((Work.FIPlan.gnorm w : ℕ)) : ℤ) := by
        exact_mod_cast h2
      rwa [hc] at h2
    refine ⟨⟨(e.re, e.im), ?_, rfl⟩, hdvd, hprim⟩
    refine Finset.mem_product.mpr ⟨?_, ?_⟩
    · rw [Finset.mem_Icc]; exact (abs_le.mp h1')
    · rw [Finset.mem_Icc]; exact (abs_le.mp h2')

/-- A divisor of a primitive Gaussian integer is primitive. -/
lemma isCoprime_re_im_of_dvd {e w : GaussianInt} (hw : IsCoprime w.re w.im) (h : e ∣ w) :
    IsCoprime e.re e.im := by
  obtain ⟨a, b, hab⟩ := hw
  rw [Int.isCoprime_iff_gcd_eq_one]
  have hge : ((Int.gcd e.re e.im : ℤ) : GaussianInt) ∣ e := by
    obtain ⟨x, hx⟩ := Int.gcd_dvd_left e.re e.im
    obtain ⟨y, hy⟩ := Int.gcd_dvd_right e.re e.im
    refine ⟨(⟨x, y⟩ : GaussianInt), Zsqrtd.ext ?_ ?_⟩
    · have h1 : (((Int.gcd e.re e.im : ℤ) : GaussianInt) * (⟨x, y⟩ : GaussianInt)).re
          = (Int.gcd e.re e.im : ℤ) * x := by simp [Zsqrtd.re_mul]
      rw [h1]; exact hx
    · have h2 : (((Int.gcd e.re e.im : ℤ) : GaussianInt) * (⟨x, y⟩ : GaussianInt)).im
          = (Int.gcd e.re e.im : ℤ) * y := by simp [Zsqrtd.im_mul]
      rw [h2]; exact hy
  have hg_w : ((Int.gcd e.re e.im : ℤ) : GaussianInt) ∣ w := hge.trans h
  obtain ⟨f, hf⟩ := hg_w
  have h1 : (Int.gcd e.re e.im : ℤ) ∣ w.re := by
    refine ⟨f.re, ?_⟩
    rw [hf, Zsqrtd.re_mul]
    simp
  have h2 : (Int.gcd e.re e.im : ℤ) ∣ w.im := by
    refine ⟨f.im, ?_⟩
    rw [hf, Zsqrtd.im_mul]
    simp
  have h3 : (Int.gcd e.re e.im : ℤ) ∣ (1 : ℤ) := by
    have h4 : (Int.gcd e.re e.im : ℤ) ∣ (w.re * a + w.im * b) :=
      dvd_add (h1.mul_right a) (h2.mul_right b)
    rw [show w.re * a + w.im * b = a * w.re + b * w.im by ring, hab] at h4
    exact h4
  exact Nat.dvd_one.mp (Int.ofNat_dvd.mp (by simpa using h3))

/-- The fibre of `K*` vanishes unless `r` is odd. -/
lemma KInnerStar_eq_zero_of_not_odd {Rz : ℤ} {w : GaussianInt} {k : ℤ}
    {chi : GaussianInt → ℂ} {r : ℤ} (hr : ¬ Odd r) : KInnerStar Rz w k chi r = 0 := by
  rw [KInnerStar]
  apply Finset.sum_eq_zero
  intro s _
  rw [if_neg]
  intro hz
  exact hr hz.1.1

/-- The fibre of `K*` is the alternating sum, over the primary divisors `e` of `w`, of the fibre
restricted by the congruence `e ∣ r + is`. -/
lemma KInnerStar_eq_sum_moebius (Rz : ℤ) (w : GaussianInt) (k : ℤ) (chi : GaussianInt → ℂ)
    (r : ℤ) (hw : Work.FIPlan.IsPrimary w) :
    KInnerStar Rz w k chi r =
      ∑ e ∈ gaussPrimDivs w, (UniqueFactorizationMonoid.moebius e : ℂ) *
        (∑ s ∈ Finset.Icc (-Rz) Rz,
          (if Work.FIPlan.IsPrimary (⟨r, s⟩ : GaussianInt) ∧ e ∣ (⟨r, s⟩ : GaussianInt) then
            grossenChar chi k (⟨r, s⟩ : GaussianInt) * JKSym (w * (⟨r, s⟩ : GaussianInt)) else 0)) := by
  have hpoint : ∀ s : ℤ,
      (if Work.FIPlan.IsPrimary (⟨r, s⟩ : GaussianInt) ∧
          Work.FIPlan.GaussCoprime (⟨r, s⟩ : GaussianInt) w then
          grossenChar chi k (⟨r, s⟩ : GaussianInt) * JKSym (w * (⟨r, s⟩ : GaussianInt)) else 0)
        = ∑ e ∈ gaussPrimDivs w, (UniqueFactorizationMonoid.moebius e : ℂ) *
          (if Work.FIPlan.IsPrimary (⟨r, s⟩ : GaussianInt) ∧ e ∣ (⟨r, s⟩ : GaussianInt) then
            grossenChar chi k (⟨r, s⟩ : GaussianInt) * JKSym (w * (⟨r, s⟩ : GaussianInt)) else 0) := by
    intro s
    have hmoeb := Work.FIArea7.KStarDivs.gauss_divs_moebius w (⟨r, s⟩ : GaussianInt) hw
    set P : Prop := Work.FIPlan.IsPrimary (⟨r, s⟩ : GaussianInt) with hP
    set G : ℂ := grossenChar chi k (⟨r, s⟩ : GaussianInt) * JKSym (w * (⟨r, s⟩ : GaussianInt))
      with hG
    have hkey : (∑ e ∈ gaussPrimDivs w, (UniqueFactorizationMonoid.moebius e : ℂ) *
          (if P ∧ e ∣ (⟨r, s⟩ : GaussianInt) then G else 0))
        = (∑ e ∈ gaussPrimDivs w, (UniqueFactorizationMonoid.moebius e : ℂ) *
            (if e ∣ (⟨r, s⟩ : GaussianInt) then (1 : ℂ) else 0)) *
          ((if P then (1 : ℂ) else 0) * G) := by
      rw [Finset.sum_mul]
      apply Finset.sum_congr rfl
      intro e _
      by_cases hp : P <;> by_cases he : e ∣ (⟨r, s⟩ : GaussianInt) <;> simp [hp, he]
    rw [hkey, hmoeb]
    by_cases hp : P <;> by_cases hc : IsCoprime (⟨r, s⟩ : GaussianInt) w <;>
      simp [hp, hc, Work.FIPlan.GaussCoprime, hG]
  rw [KInnerStar]
  rw [show (∑ s ∈ Finset.Icc (-Rz) Rz,
        (if Work.FIPlan.IsPrimary (⟨r, s⟩ : GaussianInt) ∧
            Work.FIPlan.GaussCoprime (⟨r, s⟩ : GaussianInt) w then
          grossenChar chi k (⟨r, s⟩ : GaussianInt) * JKSym (w * (⟨r, s⟩ : GaussianInt)) else 0))
      = ∑ s ∈ Finset.Icc (-Rz) Rz, ∑ e ∈ gaussPrimDivs w,
          (UniqueFactorizationMonoid.moebius e : ℂ) *
          (if Work.FIPlan.IsPrimary (⟨r, s⟩ : GaussianInt) ∧ e ∣ (⟨r, s⟩ : GaussianInt) then
            grossenChar chi k (⟨r, s⟩ : GaussianInt) * JKSym (w * (⟨r, s⟩ : GaussianInt)) else 0)
      from Finset.sum_congr rfl (fun s _ => hpoint s)]
  rw [Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro e _
  rw [← Finset.mul_sum]


/-! ## The fibre bound for good `r` -/

/-- One Möbius term of the fibre: the sum over the progression `e ∣ r + is` inside the box, bounded
by the arithmetic-progression fibre bound `Work.FIArea7.KStarAP.ap_char_chi_bound`. -/
lemma KInnerStar_term_bound_exists :
    ∃ C : ℝ, 0 < C ∧ ∀ (d : ℕ) (hd : 1 ≤ d) (Rz : ℤ) (hRz : 0 ≤ Rz) (w : GaussianInt) (k : ℤ)
      (chi : GaussianInt → ℂ) (r ω : ℤ) (e : GaussianInt),
      Work.FIPlan.IsPrimary w → IsCoprime w.re w.im →
      (∀ z : GaussianInt, ‖chi z‖ ≤ 1) →
      (∀ a b : ℤ, chi (⟨a, b + 4 * (d : ℤ)⟩ : GaussianInt) = chi (⟨a, b⟩ : GaussianInt)) →
      Odd r → r ≠ 0 →
      (ω * w.re ≡ -w.im [ZMOD (((Work.FIPlan.gnorm w : ℕ) : ℤ))]) →
      ((ω ^ 2 + 1) ≡ 0 [ZMOD (((Work.FIPlan.gnorm w : ℕ) : ℤ))]) →
      e ∈ gaussPrimDivs w →
      (∃ p : ℕ, p.Prime ∧ ¬ (p : ℤ) ∣ (4 * (d : ℤ) * (((Work.FIPlan.gnorm w : ℕ) : ℤ))) ∧
        Odd (r.natAbs.factorization p)) →
      ‖∑ s ∈ Finset.Icc (-Rz) Rz,
          (if Work.FIPlan.IsPrimary (⟨r, s⟩ : GaussianInt) ∧ e ∣ (⟨r, s⟩ : GaussianInt) then
            grossenChar chi k (⟨r, s⟩ : GaussianInt) * JKSym (w * (⟨r, s⟩ : GaussianInt)) else 0)‖
        ≤ C * (d : ℝ) * (|(k : ℝ)| + 1)
            * Real.sqrt ((((Work.FIPlan.gnorm w : ℕ)) : ℝ) / (((Work.FIPlan.gnorm e : ℕ)) : ℝ))
            * (Real.sqrt |(r : ℝ)| + 2 * (Rz : ℝ) * (Real.sqrt |(r : ℝ)|)⁻¹)
            * Real.log (2 + (r.natAbs : ℝ) * (((Work.FIPlan.gnorm w : ℕ)) : ℝ)) := by
  obtain ⟨Cap, hCappos, hAP⟩ := Work.FIArea7.KStarAP.ap_char_chi_bound
  refine ⟨Cap, hCappos, ?_⟩
  intro d hd Rz hRz w k chi r ω e hw hcop hchi hchi2 hr hrn hωlin hωsq he hgood
  have hw0 : w ≠ 0 := by
    rintro rfl
    exact (Int.not_odd_zero) (by simpa using hw.1)
  obtain ⟨hdvd, hprim⟩ := (mem_gaussPrimDivs hw0).mp he
  have he0 : e ≠ 0 := by
    rintro rfl
    exact (Int.not_odd_zero) (by simpa using hprim.1)
  have hecop : IsCoprime e.re e.im := isCoprime_re_im_of_dvd hcop hdvd
  have hMq : (((Work.FIPlan.gnorm e : ℕ)) : ℤ) ∣ (((Work.FIPlan.gnorm w : ℕ)) : ℤ) := by
    exact_mod_cast gnorm_dvd_gnorm_of_dvd hdvd
  have heM1 : 1 ≤ ((Work.FIPlan.gnorm e : ℕ) : ℤ) := by
    have h : Work.FIPlan.gnorm e ≠ 0 := fun h => he0 (gnorm_eq_zero_iff.mp h)
    omega
  obtain ⟨c, hc⟩ := Work.FIArea7.KStarAP.dvd_and_primary_iff_modEq e r hecop hprim hr
  have hbase : ∀ s : ℤ,
      Work.FIPlan.IsPrimary (⟨r, s⟩ : GaussianInt) ∧ e ∣ (⟨r, s⟩ : GaussianInt) →
      grossenChar chi k (⟨r, s⟩ : GaussianInt) * JKSym (w * (⟨r, s⟩ : GaussianInt))
        = (JKSym w * Complex.I ^ ((r - 1) / 2 : ℤ) * (jacobiSym ω (Work.FIPlan.gnorm w) : ℂ)) *
          (chi (⟨r, s⟩ : GaussianInt) * gunitC (⟨r, s⟩ : GaussianInt) ^ k *
            (MultEps w (⟨r, s⟩ : GaussianInt) : ℂ) * (jacobiSym s r.natAbs : ℂ) *
            (jacobiSym (s - ω * r) (Work.FIPlan.gnorm w) : ℂ)) := by
    intro s h
    exact Work.FIArea7.term_eq w k chi r s ω hw hcop h.1 hωlin hωsq
  have hsum : (∑ s ∈ Finset.Icc (-Rz) Rz,
        (if Work.FIPlan.IsPrimary (⟨r, s⟩ : GaussianInt) ∧ e ∣ (⟨r, s⟩ : GaussianInt) then
          grossenChar chi k (⟨r, s⟩ : GaussianInt) * JKSym (w * (⟨r, s⟩ : GaussianInt)) else 0))
      = (JKSym w * Complex.I ^ ((r - 1) / 2 : ℤ) * (jacobiSym ω (Work.FIPlan.gnorm w) : ℂ)) *
        (∑ s ∈ (Finset.Icc (-Rz) Rz).filter
            (fun s : ℤ => s ≡ c [ZMOD (4 * (((Work.FIPlan.gnorm e : ℕ) : ℤ)))]),
          chi (⟨r, s⟩ : GaussianInt) * gunitC (⟨r, s⟩ : GaussianInt) ^ k *
            (MultEps w (⟨r, s⟩ : GaussianInt) : ℂ) * (jacobiSym s r.natAbs : ℂ) *
            (jacobiSym (s - ω * r) (Work.FIPlan.gnorm w) : ℂ)) := by
    rw [Finset.mul_sum, Finset.sum_filter]
    apply Finset.sum_congr rfl
    intro s _
    by_cases h : Work.FIPlan.IsPrimary (⟨r, s⟩ : GaussianInt) ∧ e ∣ (⟨r, s⟩ : GaussianInt)
    · have h2 : s ≡ c [ZMOD (4 * (((Work.FIPlan.gnorm e : ℕ) : ℤ)))] :=
        (and_comm.trans (hc s)).mp h
      rw [if_pos h, if_pos h2, hbase s h]
    · have h2 : ¬ (s ≡ c [ZMOD (4 * (((Work.FIPlan.gnorm e : ℕ) : ℤ)))]) :=
        fun hh => h ((and_comm.trans (hc s)).mpr hh)
      rw [if_neg h, if_neg h2]

  have hnormconst : ‖(JKSym w * Complex.I ^ ((r - 1) / 2 : ℤ) *
      (jacobiSym ω (Work.FIPlan.gnorm w) : ℂ))‖ ≤ 1 := by
    rw [norm_mul, norm_mul]
    have h1 : ‖JKSym w‖ ≤ 1 := norm_JKSym_le_one w
    have h2 : ‖Complex.I ^ ((r - 1) / 2 : ℤ)‖ = 1 := by rw [norm_zpow]; simp
    have h3 : ‖(jacobiSym ω (Work.FIPlan.gnorm w) : ℂ)‖ ≤ 1 := by
      rw [Complex.norm_intCast]
      rcases jacobiSym.trichotomy ω (Work.FIPlan.gnorm w) with h | h | h <;> rw [h] <;> norm_num
    calc ‖JKSym w‖ * ‖Complex.I ^ ((r - 1) / 2 : ℤ)‖ *
          ‖(jacobiSym ω (Work.FIPlan.gnorm w) : ℂ)‖
        ≤ (1 * 1) * 1 := mul_le_mul (mul_le_mul h1 (le_of_eq h2) (norm_nonneg _) zero_le_one) h3
            (norm_nonneg _) (by norm_num)
      _ = 1 := by ring
  have hT : (((Rz - (-Rz)).toNat : ℕ) : ℝ) = 2 * (Rz : ℝ) := by
    have h2 : Rz - (-Rz) = 2 * Rz := by ring
    rw [h2]
    have h3 : (((2 * Rz).toNat : ℕ) : ℤ) = 2 * Rz := Int.toNat_of_nonneg (by linarith)
    exact_mod_cast h3
  have happ := hAP d hd w k chi r ω (((Work.FIPlan.gnorm e : ℕ) : ℤ)) c (-Rz) Rz hw hcop hchi hchi2
    hr hrn hωlin hωsq heM1 hMq hgood
  rw [hT] at happ
  rw [hsum, norm_mul]
  refine le_trans (mul_le_mul hnormconst le_rfl (norm_nonneg _) zero_le_one) ?_
  rw [one_mul]
  exact happ

/-- The fibre of `K*` for a good `r`: Möbius expansion, then `≪ τ(|w|²)` terms of weight
`|e|^{-1/2}`. -/
lemma KInnerStar_good_bound_exists :
    ∃ C : ℝ, 0 < C ∧ ∀ (d : ℕ) (hd : 1 ≤ d) (Rz : ℤ) (hRz : 0 ≤ Rz) (w : GaussianInt) (k : ℤ)
      (chi : GaussianInt → ℂ) (r ω : ℤ),
      Work.FIPlan.IsPrimary w → IsCoprime w.re w.im →
      (∀ z : GaussianInt, ‖chi z‖ ≤ 1) →
      (∀ a b : ℤ, chi (⟨a, b + 4 * (d : ℤ)⟩ : GaussianInt) = chi (⟨a, b⟩ : GaussianInt)) →
      Odd r → r ≠ 0 →
      (ω * w.re ≡ -w.im [ZMOD (((Work.FIPlan.gnorm w : ℕ) : ℤ))]) →
      ((ω ^ 2 + 1) ≡ 0 [ZMOD (((Work.FIPlan.gnorm w : ℕ) : ℤ))]) →
      (∃ p : ℕ, p.Prime ∧ ¬ (p : ℤ) ∣ (4 * (d : ℤ) * (((Work.FIPlan.gnorm w : ℕ) : ℤ))) ∧
        Odd (r.natAbs.factorization p)) →
      ‖KInnerStar Rz w k chi r‖
        ≤ C * (d : ℝ) * (|(k : ℝ)| + 1) * Real.sqrt (((Work.FIPlan.gnorm w : ℕ) : ℝ))
            * ((((Work.FIPlan.gnorm w)).divisors).card : ℝ)
            * (Real.sqrt |(r : ℝ)| + 2 * (Rz : ℝ) * (Real.sqrt |(r : ℝ)|)⁻¹)
            * Real.log (2 + (r.natAbs : ℝ) * (((Work.FIPlan.gnorm w : ℕ)) : ℝ)) := by
  obtain ⟨Cterm, hCtermpos, hTerm⟩ := KInnerStar_term_bound_exists
  obtain ⟨Kdiv, hKdivpos, hKdiv⟩ := Work.FIArea7.KStarDivs.sum_inv_sqrt_sqfree_gaussPrimDivs_le
  refine ⟨Cterm * Kdiv, by positivity, ?_⟩
  intro d hd Rz hRz w k chi r ω hw hcop hchi hchi2 hr hrn hωlin hωsq hgood
  have hw0 : w ≠ 0 := by
    rintro rfl
    exact (Int.not_odd_zero) (by simpa using hw.1)
  have hq0 : (0 : ℝ) ≤ (((Work.FIPlan.gnorm w : ℕ)) : ℝ) := by positivity
  have hdecomp := KInnerStar_eq_sum_moebius Rz w k chi r hw
  set Rr : ℝ := Real.sqrt |(r : ℝ)| + 2 * (Rz : ℝ) * (Real.sqrt |(r : ℝ)|)⁻¹ with hRr
  set LL : ℝ := Real.log (2 + (r.natAbs : ℝ) * (((Work.FIPlan.gnorm w : ℕ)) : ℝ)) with hLL
  set Q : ℝ := Real.sqrt (((Work.FIPlan.gnorm w : ℕ)) : ℝ) with hQ
  have hRzR : (0 : ℝ) ≤ (Rz : ℝ) := by exact_mod_cast hRz
  have hRr0 : 0 ≤ Rr := by
    rw [hRr]
    have h1 : (0:ℝ) ≤ Real.sqrt |(r:ℝ)| := Real.sqrt_nonneg _
    have h2 : (0:ℝ) ≤ (Real.sqrt |(r:ℝ)|)⁻¹ := inv_nonneg.mpr h1
    have h3 : (0:ℝ) ≤ 2 * (Rz : ℝ) * (Real.sqrt |(r : ℝ)|)⁻¹ := by positivity
    linarith
  have hLL0 : 0 ≤ LL := by
    rw [hLL]
    apply Real.log_nonneg
    have h1 : (0:ℝ) ≤ (r.natAbs : ℝ) * (((Work.FIPlan.gnorm w : ℕ)) : ℝ) := by positivity
    linarith
  have hQ0 : 0 ≤ Q := by rw [hQ]; exact Real.sqrt_nonneg _
  -- step 1: bound the fibre by the sum of the term bounds
  have hstep : ‖KInnerStar Rz w k chi r‖
      ≤ ∑ e ∈ gaussPrimDivs w, ‖(UniqueFactorizationMonoid.moebius e : ℂ)‖ *
          (Cterm * (d : ℝ) * (|(k : ℝ)| + 1)
            * Real.sqrt ((((Work.FIPlan.gnorm w : ℕ)) : ℝ) / (((Work.FIPlan.gnorm e : ℕ)) : ℝ))
            * Rr * LL) := by
    rw [hdecomp]
    refine le_trans (norm_sum_le _ _) (Finset.sum_le_sum (fun e he => ?_))
    rw [norm_mul]
    refine mul_le_mul_of_nonneg_left ?_ (norm_nonneg _)
    rw [hRr, hLL]
    exact hTerm d hd Rz hRz w k chi r ω e hw hcop hchi hchi2 hr hrn hωlin hωsq he hgood
  -- step 2: factor out the common weight
  have hsplit : (∑ e ∈ gaussPrimDivs w, ‖(UniqueFactorizationMonoid.moebius e : ℂ)‖ *
        (Cterm * (d : ℝ) * (|(k : ℝ)| + 1)
          * Real.sqrt ((((Work.FIPlan.gnorm w : ℕ)) : ℝ) / (((Work.FIPlan.gnorm e : ℕ)) : ℝ))
          * Rr * LL))
      = (Cterm * (d : ℝ) * (|(k : ℝ)| + 1) * Q * Rr * LL) *
        (∑ e ∈ gaussPrimDivs w, ‖(UniqueFactorizationMonoid.moebius e : ℂ)‖ *
          (1 / Real.sqrt ((((Work.FIPlan.gnorm e : ℕ)) : ℝ)))) := by
    rw [Finset.mul_sum]
    apply Finset.sum_congr rfl
    intro e he
    have hsqrt : Real.sqrt ((((Work.FIPlan.gnorm w : ℕ)) : ℝ) /
        (((Work.FIPlan.gnorm e : ℕ)) : ℝ)) = Q / Real.sqrt ((((Work.FIPlan.gnorm e : ℕ)) : ℝ)) := by
      rw [hQ, Real.sqrt_div hq0]
    rw [hsqrt]
    ring
  -- step 3: the Möbius weights
  have hmu : (∑ e ∈ gaussPrimDivs w, ‖(UniqueFactorizationMonoid.moebius e : ℂ)‖ *
        (1 / Real.sqrt ((((Work.FIPlan.gnorm e : ℕ)) : ℝ))))
      ≤ Kdiv * ((((Work.FIPlan.gnorm w)).divisors).card : ℝ) := by
    refine le_trans (Finset.sum_le_sum (fun e he => ?_)) (hKdiv w hw)
    by_cases hs : Squarefree e
    · have h2 : ‖(UniqueFactorizationMonoid.moebius e : ℂ)‖ = 1 := by
        rw [hs.moebius_eq]; simp
      rw [h2, one_mul, if_pos hs]
    · have h1 : (UniqueFactorizationMonoid.moebius e : ℂ) = 0 := by
        rw [UniqueFactorizationMonoid.moebius_of_not_squarefree hs]; simp
      rw [h1, norm_zero, zero_mul, if_neg hs]
  rw [hsplit] at hstep
  refine le_trans hstep ?_
  refine le_trans (mul_le_mul_of_nonneg_left hmu ?_) ?_
  · -- the constant factor is nonneg
    have h1 : (0 : ℝ) ≤ (d : ℝ) := Nat.cast_nonneg _
    have h2 : (0 : ℝ) ≤ |(k : ℝ)| + 1 := by positivity
    exact mul_nonneg (mul_nonneg (mul_nonneg (mul_nonneg (mul_nonneg hCtermpos.le h1) h2) hQ0)
      hRr0) hLL0
  · -- and the final shape
    rw [hQ, hRr, hLL]
    ring_nf
    exact le_of_eq (by ring)


/-! ## *FI* (22.4) -/

end

end Work.FIArea7
