import Mathlib
import Submission.Work.FIArea5.S16Hecke.Basic
import Submission.Work.FIArea5.S16Hecke.Defs
import Submission.Work.FIArea5.S16Hecke.heckeL_inv_halfPlane
import Submission.Work.FIArea5.S16Hecke.heckeLSeries_eulerProduct_hasProd
import Submission.Work.FIArea5.S16Hecke.heckeLam_bound
import Submission.Work.FIArea5.S16Hecke.heckeLam_localRec
import Submission.Work.FIArea5.S16Hecke.splitPrimaryClass
import Submission.Work.FIArea5.S16Hecke.heckeLam_prime_eq_zero_of_ne_one_mod_four
import Submission.Work.FIArea6Hecke.chiTildeDefs
import Submission.Work.FIArea6Hecke.R.chiTrivLocalPrime
import Submission.Work.FIArea6Hecke.heckeLam_prime_norm_le_two_of_split
import Submission.Work.FIArea6HeckeV2.exists_log_heckeFp_le
import Submission.Work.FIArea6HeckeV2.tsum_log_norm_heckeFp
import Submission.Work.FIArea6V.heckeLam_norm_sq_eq_two_add_re_chiTilde
import Submission.Work.FIFinal.CL.FIArea6V.heckeLSeries_chiTilde_lower_bound_near_one
import Submission.Work.FIArea6V.sum_one_mod_four_rpow_lower_bound
import Submission.Commons.NumberTheory.DirichletSeries.omega_series_factor_shifted

set_option autoImplicit false
set_option maxHeartbeats 8000000

namespace Work.FIArea6V

open scoped BigOperators
open Work.FIArea5.S16Hecke
open Work.FIArea6Hecke

noncomputable section

/-- The auxiliary character `χ̃ = χ/(χ∘conj)` is again a strict character modulo `4d`. -/
theorem chiTilde_isCharMod4dStrict' {d : ℕ} {chi : GaussianInt → ℂ}
    (hchi : IsCharMod4dStrict d chi) : IsCharMod4dStrict d (chiTilde chi) := by
  obtain ⟨hchar, hstrict⟩ := hchi
  obtain ⟨h1, hmul, hbd, hper, hvanish⟩ := hchar
  have hstarper : ∀ z w : GaussianInt, (((4 * d : ℕ) : ℤ) : GaussianInt) ∣ (z - w) →
      (((4 * d : ℕ) : ℤ) : GaussianInt) ∣ (star z - star w) := by
    intro z w hzw
    obtain ⟨c, hc⟩ := hzw
    refine ⟨star c, ?_⟩
    have h : star z - star w = star (z - w) := by simp
    rw [h, hc]
    simp
  refine ⟨⟨?_, ?_, ?_, ?_, ?_⟩, ?_⟩
  · simpa using Work.FIArea6HeckeV2.chiTilde_one' ⟨⟨h1, hmul, hbd, hper, hvanish⟩, hstrict⟩
  · intro z w
    exact Work.FIArea6HeckeV2.chiTilde_mul' ⟨⟨h1, hmul, hbd, hper, hvanish⟩, hstrict⟩ z w
  · exact Work.FIArea6HeckeV2.chiTilde_norm_le_one' ⟨⟨h1, hmul, hbd, hper, hvanish⟩, hstrict⟩
  · intro z w hzw
    show chi z / chi (star z) = chi w / chi (star w)
    rw [hper z w hzw, hper (star z) (star w) (hstarper z w hzw)]
  · intro z hz
    show chi z / chi (star z) = 0
    rw [hvanish z hz, zero_div]
  · intro z hz
    show chi z / chi (star z) = 0
    rw [hstrict z hz, zero_div]

/-- Size bound at a rational prime for a strict character. -/
lemma lam_prime_norm_le_two {d : ℕ} {chi : GaussianInt → ℂ}
    (hchi : IsCharMod4dStrict d chi) (m : ℤ) {p : ℕ} (hp : p.Prime) :
    ‖heckeLam chi m p‖ ≤ 2 := by
  by_cases h4 : p % 4 = 1
  · exact Work.FIArea6Hecke.heckeLam_prime_norm_le_two_of_split chi m hchi.1.2.1 hchi.1.1
      hchi.1.2.2.1 hp h4
  · rw [heckeLam_prime_eq_zero_of_ne_one_mod_four hp h4]
    norm_num

/-- Size bound for the real part of the twisted eigenvalue at a rational prime. -/
lemma lamTilde_prime_re_abs_le_two {d : ℕ} {chi : GaussianInt → ℂ}
    (hchi : IsCharMod4dStrict d chi) (m : ℤ) {p : ℕ} (hp : p.Prime) :
    |(heckeLam (chiTilde chi) (2 * m) p).re| ≤ 2 := by
  have h := lam_prime_norm_le_two (chiTilde_isCharMod4dStrict' hchi) (2 * m) hp
  have h2 : |(heckeLam (chiTilde chi) (2 * m) p).re| ≤ ‖heckeLam (chiTilde chi) (2 * m) p‖ :=
    Complex.abs_re_le_norm _
  linarith

/-- The correction from the primes dividing `4d` is bounded. -/
lemma primes_dvd_correction (d : ℕ) (hd : 1 ≤ d) :
    ∃ C : ℝ, 0 < C ∧ ∀ σ : ℝ, 1 ≤ σ →
      (∑' p : Nat.Primes, (if ((p : ℕ) ∣ 4 * d) then (((p : ℕ) : ℝ) ^ (-σ)) else 0)) ≤ C := by
  refine ⟨4 * d, by positivity, ?_⟩
  intro σ hσ
  refine Real.tsum_le_of_sum_le
    (f := fun p : Nat.Primes => (if ((p : ℕ) ∣ 4 * d) then (((p : ℕ) : ℝ) ^ (-σ)) else 0))
    ?_ ?_
  · intro p
    change (0 : ℝ) ≤ (if ((p : ℕ) ∣ 4 * d) then (((p : ℕ) : ℝ) ^ (-σ)) else 0)
    by_cases h : ((p : ℕ) ∣ 4 * d)
    · rw [if_pos h]
      exact Real.rpow_nonneg (by positivity) _
    · rw [if_neg h]
  · intro s
    have h1 : ∀ p ∈ s, (if ((p : ℕ) ∣ 4 * d) then (((p : ℕ) : ℝ) ^ (-σ)) else 0)
        ≤ (if ((p : ℕ) ∣ 4 * d) then (1 : ℝ) else 0) := by
      intro p _
      by_cases hc : ((p : ℕ) ∣ 4 * d)
      · rw [if_pos hc, if_pos hc]
        exact Real.rpow_le_one_of_one_le_of_nonpos
          (by exact_mod_cast (show (1 : ℕ) ≤ (p : ℕ) from p.2.one_le)) (by linarith)
      · rw [if_neg hc, if_neg hc]
    have h2 : ∑ p ∈ s, (if ((p : ℕ) ∣ 4 * d) then (1 : ℝ) else 0)
        = ((s.filter (fun p : Nat.Primes => ((p : ℕ) ∣ 4 * d))).card : ℝ) := by
      rw [Finset.sum_boole]
    have h3 : ((s.filter (fun p : Nat.Primes => ((p : ℕ) ∣ 4 * d))).card : ℝ)
        ≤ (((4 * d).divisors.card : ℕ) : ℝ) := by
      have hcard : (s.filter (fun p : Nat.Primes => ((p : ℕ) ∣ 4 * d))).card
          ≤ (4 * d).divisors.card := by
        refine Finset.card_le_card_of_injOn (fun p : Nat.Primes => (p : ℕ)) ?_ ?_
        · intro p hp
          obtain ⟨-, hdvd⟩ := Finset.mem_filter.mp hp
          exact Nat.mem_divisors.mpr ⟨hdvd, by omega⟩
        · intro a _ b _ hab
          exact Nat.Primes.coe_nat_injective hab
      exact_mod_cast hcard
    calc ∑ p ∈ s, (if ((p : ℕ) ∣ 4 * d) then (((p : ℕ) : ℝ) ^ (-σ)) else 0)
        ≤ ∑ p ∈ s, (if ((p : ℕ) ∣ 4 * d) then (1 : ℝ) else 0) := Finset.sum_le_sum h1
      _ = ((s.filter (fun p : Nat.Primes => ((p : ℕ) ∣ 4 * d))).card : ℝ) := h2
      _ ≤ (((4 * d).divisors.card : ℕ) : ℝ) := h3
      _ ≤ (4 * d : ℝ) := by exact_mod_cast Nat.card_divisors_le_self (4 * d)

/-- The logarithms of the local Euler factors are summable in the half-plane `re s > 1`. -/
private lemma summable_log_norm_heckeFp {chi : GaussianInt → ℂ} {k : ℤ} {s : ℂ} (hs : 1 < s.re)
    (h1 : chi 1 = 1) (hmul : ∀ z w : GaussianInt, chi (z * w) = chi z * chi w)
    (hb : ∀ z : GaussianInt, ‖chi z‖ ≤ 1) :
    Summable (fun p : Nat.Primes => Real.log ‖heckeFp chi k p s‖) := by
  have hs0 : 0 < s.re := by linarith
  have hFG : ∀ p : Nat.Primes, heckeFp chi k p s * heckeGp chi k p s = 1 :=
    fun p => heckeFp_mul_heckeGp chi k p s hmul h1 hb hs0
  have hmaj : Summable (fun p : Nat.Primes => 9 * (((p : ℕ) : ℝ) ^ (-s.re))) :=
    ((Nat.Primes.summable_rpow (r := -s.re)).mpr (by linarith)).mul_left 9
  have hbnd : Summable (fun p : Nat.Primes => ‖heckeGp chi k p s - 1‖) := by
    refine Summable.of_nonneg_of_le (fun p => norm_nonneg _) (fun p => ?_) hmaj
    exact norm_heckeGp_sub_one_le chi k p s hmul hb hs0
  have hGsum : Summable (fun p : Nat.Primes => Real.log ‖1 + (heckeGp chi k p s - 1)‖) :=
    Summable.summable_log_norm_one_add (f := fun p : Nat.Primes => heckeGp chi k p s - 1) hbnd
  have hGsum' : Summable (fun p : Nat.Primes => Real.log ‖heckeGp chi k p s‖) :=
    hGsum.congr (fun p => by
      rw [show (1 : ℂ) + (heckeGp chi k p s - 1) = heckeGp chi k p s by ring])
  refine hGsum'.neg.congr (fun p => ?_)
  have hnorm : ‖heckeFp chi k p s‖ * ‖heckeGp chi k p s‖ = 1 := by
    rw [← norm_mul, hFG p, norm_one]
  have hFi : ‖heckeFp chi k p s‖ = (‖heckeGp chi k p s‖)⁻¹ := eq_inv_of_mul_eq_one_left hnorm
  rw [hFi, Real.log_inv]

/-- The second-moment character sum dominates the logarithm of the twisted `L`-series. -/
lemma log_le_sum_re_chiTilde {d : ℕ} (hd : 1 ≤ d) {chi : GaussianInt → ℂ}
    (hchi : IsCharMod4dStrict d chi) (m : ℤ) :
    ∃ C : ℝ, 0 < C ∧ ∀ σ : ℝ, 1 < σ →
      Real.log ‖heckeLSeries (chiTilde chi) (2 * m) (σ : ℂ)‖ - C
        ≤ ∑' p : Nat.Primes,
            (heckeLam (chiTilde chi) (2 * m) (p : ℕ)).re * (((p : ℕ) : ℝ) ^ (-σ)) := by
  obtain ⟨C₂, hC₂pos, hC₂⟩ := Work.FIArea6HeckeV2.exists_log_heckeFp_le
  refine ⟨C₂ + 1, by positivity, ?_⟩
  intro σ hσ
  have h1 : chiTilde chi 1 = 1 := Work.FIArea6HeckeV2.chiTilde_one' hchi
  have hmul : ∀ z w : GaussianInt, chiTilde chi (z * w) = chiTilde chi z * chiTilde chi w :=
    Work.FIArea6HeckeV2.chiTilde_mul' hchi
  have hb : ∀ z : GaussianInt, ‖chiTilde chi z‖ ≤ 1 :=
    Work.FIArea6HeckeV2.chiTilde_norm_le_one' hchi
  have hs : 1 < ((σ : ℂ)).re := by simpa using hσ
  have hid : (∑' p : Nat.Primes, Real.log ‖heckeFp (chiTilde chi) (2 * m) p (σ : ℂ)‖)
      = Real.log ‖heckeLSeries (chiTilde chi) (2 * m) (σ : ℂ)‖ :=
    Work.FIArea6HeckeV2.tsum_log_norm_heckeFp hs h1 hmul hb
  have hsumm : Summable (fun p : Nat.Primes => Real.log ‖heckeFp (chiTilde chi) (2 * m) p (σ : ℂ)‖) :=
    summable_log_norm_heckeFp hs h1 hmul hb
  have hpt : ∀ p : Nat.Primes, Real.log ‖heckeFp (chiTilde chi) (2 * m) p (σ : ℂ)‖
      ≤ (heckeLam (chiTilde chi) (2 * m) (p : ℕ)).re * (((p : ℕ) : ℝ) ^ (-σ))
        + C₂ * (((p : ℕ) : ℝ) ^ (-2 * σ)) :=
    fun p => hC₂ hd hchi m hσ (p : ℕ) p.2
  have hgA : Summable (fun p : Nat.Primes =>
      (heckeLam (chiTilde chi) (2 * m) (p : ℕ)).re * (((p : ℕ) : ℝ) ^ (-σ))) := by
    refine Summable.of_norm_bounded
      (((Nat.Primes.summable_rpow (r := -σ)).mpr (by linarith)).mul_left 2) (fun p => ?_)
    rw [Real.norm_eq_abs, abs_mul, abs_of_nonneg (Real.rpow_nonneg (by positivity) _)]
    exact mul_le_mul_of_nonneg_right (lamTilde_prime_re_abs_le_two hchi m p.2)
      (Real.rpow_nonneg (by positivity) _)
  have hgB : Summable (fun p : Nat.Primes => C₂ * (((p : ℕ) : ℝ) ^ (-2 * σ))) := by
    refine Summable.of_norm_bounded
      (((Nat.Primes.summable_rpow (r := -σ)).mpr (by linarith)).mul_left C₂) (fun p => ?_)
    rw [Real.norm_eq_abs, abs_mul, abs_of_nonneg hC₂pos.le,
      abs_of_nonneg (Real.rpow_nonneg (by positivity) _)]
    refine mul_le_mul_of_nonneg_left ?_ hC₂pos.le
    have hp1 : (1 : ℝ) ≤ ((p : ℕ) : ℝ) := by
      exact_mod_cast (show (1 : ℕ) ≤ (p : ℕ) from p.2.one_le)
    have hsq' : (((p : ℕ) : ℝ) ^ (-2 * σ)) = ((((p : ℕ) : ℝ) ^ (-σ))) ^ (2 : ℕ) := by
      rw [← Real.rpow_natCast, ← Real.rpow_mul (by positivity)]
      congr 1
      ring
    rw [hsq']
    have hx0 : 0 ≤ (((p : ℕ) : ℝ) ^ (-σ)) := Real.rpow_nonneg (by positivity) _
    have hx1 : (((p : ℕ) : ℝ) ^ (-σ)) ≤ 1 :=
      Real.rpow_le_one_of_one_le_of_nonpos hp1 (by linarith)
    nlinarith
  have hg : Summable (fun p : Nat.Primes =>
      (heckeLam (chiTilde chi) (2 * m) (p : ℕ)).re * (((p : ℕ) : ℝ) ^ (-σ))
        + C₂ * (((p : ℕ) : ℝ) ^ (-2 * σ))) := hgA.add hgB
  have hle := Summable.tsum_le_tsum hpt hsumm hg
  have hsq : (∑' p : Nat.Primes, (((p : ℕ) : ℝ) ^ (-2 * σ))) ≤ 1 := by
    have hsm1 : Summable (fun p : Nat.Primes => (((p : ℕ) : ℝ) ^ (-2 * σ))) :=
      (Nat.Primes.summable_rpow (r := (-2 * σ))).mpr (by linarith)
    have hsm2 : Summable (fun p : Nat.Primes => ((((p : ℕ)) : ℝ))⁻¹ ^ 2) :=
      ((Nat.Primes.summable_rpow (r := (-2 : ℝ))).mpr (by norm_num)).congr (fun p => by
        rw [Real.rpow_neg (by positivity), Real.rpow_two]
        ring)
    have hmain : (∑' p : Nat.Primes, (((p : ℕ) : ℝ) ^ (-2 * σ)))
        ≤ (∑' p : Nat.Primes, ((((p : ℕ)) : ℝ))⁻¹ ^ 2) := by
      refine Summable.tsum_le_tsum (fun p => ?_) hsm1 hsm2
      have hp1 : (1 : ℝ) ≤ ((p : ℕ) : ℝ) := by
        exact_mod_cast (show (1 : ℕ) ≤ (p : ℕ) from p.2.one_le)
      calc (((p : ℕ) : ℝ) ^ (-2 * σ)) ≤ (((p : ℕ) : ℝ) ^ (-2 : ℝ)) :=
            Real.rpow_le_rpow_of_exponent_le hp1 (by linarith)
        _ = ((((p : ℕ)) : ℝ))⁻¹ ^ 2 := by
            rw [Real.rpow_neg (by positivity), Real.rpow_two]
            ring
    linarith [Commons.NumberTheory.DirichletSeries.tsum_primes_inv_sq_le]
  have hB : (∑' p : Nat.Primes, C₂ * (((p : ℕ) : ℝ) ^ (-2 * σ))) ≤ C₂ := by
    rw [tsum_mul_left]
    calc C₂ * (∑' p : Nat.Primes, (((p : ℕ) : ℝ) ^ (-2 * σ))) ≤ C₂ * 1 :=
          mul_le_mul_of_nonneg_left hsq hC₂pos.le
      _ = C₂ := mul_one C₂
  have hAB : (∑' p : Nat.Primes,
        ((heckeLam (chiTilde chi) (2 * m) (p : ℕ)).re * (((p : ℕ) : ℝ) ^ (-σ))
          + C₂ * (((p : ℕ) : ℝ) ^ (-2 * σ))))
      = (∑' p : Nat.Primes, (heckeLam (chiTilde chi) (2 * m) (p : ℕ)).re * (((p : ℕ) : ℝ) ^ (-σ)))
        + (∑' p : Nat.Primes, C₂ * (((p : ℕ) : ℝ) ^ (-2 * σ))) :=
    Summable.tsum_add hgA hgB
  linarith [hle, hid, hAB, hB]

/-! ## Generic helpers for the assembly -/

/-- The summand `p^{-σ}`. -/
private abbrev Pw (σ : ℝ) (p : Nat.Primes) : ℝ := (((p : ℕ) : ℝ) ^ (-σ))

private lemma Pw_nonneg (σ : ℝ) (p : Nat.Primes) : 0 ≤ Pw σ p :=
  Real.rpow_nonneg (by positivity) _

private lemma summable_Pw (σ : ℝ) (hσ : 1 < σ) : Summable (Pw σ) :=
  (Nat.Primes.summable_rpow (r := -σ)).mpr (by linarith)

private lemma summable_indicator {f : Nat.Primes → ℝ} (hf : Summable f) (hfn : ∀ p, 0 ≤ f p)
    (c : Nat.Primes → Prop) [DecidablePred c] :
    Summable (fun p => if c p then f p else 0) := by
  refine Summable.of_norm_bounded hf (fun p => ?_)
  by_cases h : c p
  · rw [if_pos h, Real.norm_eq_abs, abs_of_nonneg (hfn p)]
  · rw [if_neg h, norm_zero]; exact hfn p

/-- Summability of an indicator of a summable (possibly signed) function. -/
private lemma summable_indicator' {f : Nat.Primes → ℝ} (hf : Summable f)
    (c : Nat.Primes → Prop) [DecidablePred c] :
    Summable (fun p => if c p then f p else 0) := by
  refine Summable.of_norm_bounded hf.norm (fun p => ?_)
  by_cases h : c p
  · rw [if_pos h]
  · rw [if_neg h, norm_zero]; exact norm_nonneg _

/-- Splitting a `tsum` of an indicator along a second condition. -/
private lemma tsum_ite_split {f : Nat.Primes → ℝ} (c e : Nat.Primes → Prop)
    [DecidablePred c] [DecidablePred e]
    (h1 : Summable (fun p => if c p ∧ ¬ e p then f p else 0))
    (h2 : Summable (fun p => if c p ∧ e p then f p else 0)) :
    (∑' p, (if c p then f p else 0))
      = (∑' p, (if c p ∧ ¬ e p then f p else 0)) + (∑' p, (if c p ∧ e p then f p else 0)) := by
  rw [← Summable.tsum_add h1 h2]
  refine tsum_congr (fun p => ?_)
  by_cases hc : c p
  · by_cases he : e p <;> simp [hc, he]
  · simp [hc]

/-- Unpacked upper bound for the real part of the twisted eigenvalue. -/
private lemma lamRe_le_two {d : ℕ} {chi : GaussianInt → ℂ} (hchi : IsCharMod4dStrict d chi)
    (m : ℤ) {p : ℕ} (hp : p.Prime) : (heckeLam (chiTilde chi) (2 * m) p).re ≤ 2 :=
  (abs_le.mp (lamTilde_prime_re_abs_le_two hchi m hp)).2

/-- Unpacked lower bound for the real part of the twisted eigenvalue. -/
private lemma neg_two_le_lamRe {d : ℕ} {chi : GaussianInt → ℂ} (hchi : IsCharMod4dStrict d chi)
    (m : ℤ) {p : ℕ} (hp : p.Prime) : -2 ≤ (heckeLam (chiTilde chi) (2 * m) p).re :=
  (abs_le.mp (lamTilde_prime_re_abs_le_two hchi m hp)).1

/-- The twisted eigenvalue vanishes at primes that are not `1` mod `4`. -/
private lemma lamTilde_eq_zero_of_ne_one {chi : GaussianInt → ℂ} (m : ℤ) {p : ℕ}
    (hp : p.Prime) (h4 : p % 4 ≠ 1) : heckeLam (chiTilde chi) (2 * m) p = 0 :=
  heckeLam_prime_eq_zero_of_ne_one_mod_four hp h4

/-- **The first chain**: `Σ_{p ≡ 1(4)} ‖λ(p)‖² p^{-σ}` dominates
`2 Σ_{p≡1(4)} p^{-σ} + Σ_p Re λ̃(p) p^{-σ}` up to an additive constant, uniformly in `σ`. -/
private lemma chain_A {d : ℕ} (hd : 1 ≤ d) {chi : GaussianInt → ℂ}
    (hchi : IsCharMod4dStrict d chi) (m : ℤ) :
    ∃ C : ℝ, 0 < C ∧ ∀ σ : ℝ, 1 < σ →
      2 * (∑' p : Nat.Primes, (if ((p : ℕ) % 4 = 1) then Pw σ p else 0))
        + (∑' p : Nat.Primes, (heckeLam (chiTilde chi) (2 * m) (p : ℕ)).re * Pw σ p) - C
      ≤ ∑' p : Nat.Primes,
          (if ((p : ℕ) % 4 = 1) then ‖heckeLam chi m (p : ℕ)‖ ^ 2 * Pw σ p else 0) := by
  obtain ⟨Cc, hCcpos, hCc⟩ := primes_dvd_correction d hd
  refine ⟨4 * Cc, by linarith, ?_⟩
  intro σ hσ
  have hCc1 : (∑' p : Nat.Primes, (if ((p : ℕ) ∣ 4 * d) then Pw σ p else 0)) ≤ Cc := by
    simpa only [Pw] using hCc σ hσ.le
  have hPw : Summable (Pw σ) := summable_Pw σ hσ
  have hsumX : Summable (fun p : Nat.Primes =>
      (if ((p : ℕ) % 4 = 1 ∧ ¬ ((p : ℕ) ∣ 4 * d)) then Pw σ p else 0)) :=
    summable_indicator hPw (Pw_nonneg σ) _
  have hsumZ : Summable (fun p : Nat.Primes =>
      (if ((p : ℕ) % 4 = 1 ∧ ((p : ℕ) ∣ 4 * d)) then Pw σ p else 0)) :=
    summable_indicator hPw (Pw_nonneg σ) _
  have hsumRe : Summable (fun p : Nat.Primes =>
      (heckeLam (chiTilde chi) (2 * m) (p : ℕ)).re * Pw σ p) := by
    refine Summable.of_norm_bounded (hPw.mul_left 2) (fun p => ?_)
    rw [Real.norm_eq_abs, abs_mul, abs_of_nonneg (Pw_nonneg σ p)]
    exact mul_le_mul_of_nonneg_right (lamTilde_prime_re_abs_le_two hchi m p.2) (Pw_nonneg σ p)
  have hsumY : Summable (fun p : Nat.Primes =>
      (if ((p : ℕ) % 4 = 1 ∧ ¬ ((p : ℕ) ∣ 4 * d))
        then (heckeLam (chiTilde chi) (2 * m) (p : ℕ)).re * Pw σ p else 0)) :=
    summable_indicator' hsumRe _
  have hsumW : Summable (fun p : Nat.Primes =>
      (if ((p : ℕ) % 4 = 1 ∧ ((p : ℕ) ∣ 4 * d))
        then (heckeLam (chiTilde chi) (2 * m) (p : ℕ)).re * Pw σ p else 0)) :=
    summable_indicator' hsumRe _
  have hpt : ∀ p : Nat.Primes,
      (if ((p : ℕ) % 4 = 1) then ‖heckeLam chi m (p : ℕ)‖ ^ 2 * Pw σ p else 0)
        ≥ (if ((p : ℕ) % 4 = 1 ∧ ¬ ((p : ℕ) ∣ 4 * d))
            then (2 + (heckeLam (chiTilde chi) (2 * m) (p : ℕ)).re) * Pw σ p else 0) := by
    intro p
    by_cases h1 : ((p : ℕ) % 4 = 1)
    · by_cases h2 : ((p : ℕ) ∣ 4 * d)
      · rw [if_pos h1, if_neg (by simp [h1, h2])]
        exact mul_nonneg (sq_nonneg _) (Pw_nonneg σ p)
      · rw [if_pos h1, if_pos (by simp [h1, h2]),
          heckeLam_norm_sq_eq_two_add_re_chiTilde hd hchi m p.2 h1 h2]
    · rw [if_neg h1, if_neg (by simp [h1])]
  have hsumR : Summable (fun p : Nat.Primes =>
      (if ((p : ℕ) % 4 = 1 ∧ ¬ ((p : ℕ) ∣ 4 * d))
        then (2 + (heckeLam (chiTilde chi) (2 * m) (p : ℕ)).re) * Pw σ p else 0)) := by
    refine Summable.of_norm_bounded (hPw.mul_left 4) (fun p => ?_)
    by_cases h1 : ((p : ℕ) % 4 = 1 ∧ ¬ ((p : ℕ) ∣ 4 * d))
    · rw [if_pos h1, Real.norm_eq_abs, abs_mul,
        abs_of_nonneg (by linarith [neg_two_le_lamRe hchi m p.2]),
        abs_of_nonneg (Pw_nonneg σ p)]
      have h2 : (2 + (heckeLam (chiTilde chi) (2 * m) (p : ℕ)).re) ≤ 4 := by
        linarith [lamRe_le_two hchi m p.2]
      exact mul_le_mul_of_nonneg_right h2 (Pw_nonneg σ p)
    · rw [if_neg h1, norm_zero]
      exact mul_nonneg (by norm_num) (Pw_nonneg σ p)
  have hsumS : Summable (fun p : Nat.Primes =>
      (if ((p : ℕ) % 4 = 1) then ‖heckeLam chi m (p : ℕ)‖ ^ 2 * Pw σ p else 0)) := by
    refine Summable.of_norm_bounded (hPw.mul_left 4) (fun p => ?_)
    by_cases h1 : ((p : ℕ) % 4 = 1)
    · rw [if_pos h1, Real.norm_eq_abs, abs_mul, abs_of_nonneg (sq_nonneg _),
        abs_of_nonneg (Pw_nonneg σ p)]
      have hb := lam_prime_norm_le_two hchi m p.2
      have h2 : ‖heckeLam chi m (p : ℕ)‖ ^ 2 ≤ 4 := by
        nlinarith [norm_nonneg (heckeLam chi m (p : ℕ))]
      exact mul_le_mul_of_nonneg_right h2 (Pw_nonneg σ p)
    · rw [if_neg h1, norm_zero]
      exact mul_nonneg (by norm_num) (Pw_nonneg σ p)
  have hstep1 := Summable.tsum_le_tsum hpt hsumR hsumS
  have hstep2 : (∑' p : Nat.Primes,
        (if ((p : ℕ) % 4 = 1 ∧ ¬ ((p : ℕ) ∣ 4 * d))
          then (2 + (heckeLam (chiTilde chi) (2 * m) (p : ℕ)).re) * Pw σ p else 0))
      = 2 * (∑' p : Nat.Primes,
          (if ((p : ℕ) % 4 = 1 ∧ ¬ ((p : ℕ) ∣ 4 * d)) then Pw σ p else 0))
        + (∑' p : Nat.Primes,
          (if ((p : ℕ) % 4 = 1 ∧ ¬ ((p : ℕ) ∣ 4 * d))
            then (heckeLam (chiTilde chi) (2 * m) (p : ℕ)).re * Pw σ p else 0)) := by
    rw [← tsum_mul_left (f := fun p : Nat.Primes =>
        (if ((p : ℕ) % 4 = 1 ∧ ¬ ((p : ℕ) ∣ 4 * d)) then Pw σ p else 0)) (a := 2)]
    rw [← Summable.tsum_add (hsumX.mul_left 2) hsumY]
    refine tsum_congr (fun p => ?_)
    by_cases h1 : ((p : ℕ) % 4 = 1 ∧ ¬ ((p : ℕ) ∣ 4 * d))
    · rw [if_pos h1, if_pos h1, if_pos h1]; ring
    · rw [if_neg h1, if_neg h1, if_neg h1]; ring
  have hMsplit : (∑' p : Nat.Primes, (if ((p : ℕ) % 4 = 1) then Pw σ p else 0))
      = (∑' p : Nat.Primes, (if ((p : ℕ) % 4 = 1 ∧ ¬ ((p : ℕ) ∣ 4 * d)) then Pw σ p else 0))
        + (∑' p : Nat.Primes, (if ((p : ℕ) % 4 = 1 ∧ ((p : ℕ) ∣ 4 * d)) then Pw σ p else 0)) :=
    tsum_ite_split (fun p : Nat.Primes => ((p : ℕ) % 4 = 1))
      (fun p : Nat.Primes => ((p : ℕ) ∣ 4 * d)) hsumX hsumZ
  have hAsplit : (∑' p : Nat.Primes, (heckeLam (chiTilde chi) (2 * m) (p : ℕ)).re * Pw σ p)
      = (∑' p : Nat.Primes,
          (if ((p : ℕ) % 4 = 1 ∧ ¬ ((p : ℕ) ∣ 4 * d))
            then (heckeLam (chiTilde chi) (2 * m) (p : ℕ)).re * Pw σ p else 0))
        + (∑' p : Nat.Primes,
          (if ((p : ℕ) % 4 = 1 ∧ ((p : ℕ) ∣ 4 * d))
            then (heckeLam (chiTilde chi) (2 * m) (p : ℕ)).re * Pw σ p else 0)) := by
    have hA0 : (∑' p : Nat.Primes, (heckeLam (chiTilde chi) (2 * m) (p : ℕ)).re * Pw σ p)
        = ∑' p : Nat.Primes,
            (if ((p : ℕ) % 4 = 1) then (heckeLam (chiTilde chi) (2 * m) (p : ℕ)).re * Pw σ p
              else 0) := by
      refine tsum_congr (fun p => ?_)
      by_cases h1 : ((p : ℕ) % 4 = 1)
      · rw [if_pos h1]
      · rw [if_neg h1, lamTilde_eq_zero_of_ne_one m p.2 h1, Complex.zero_re, zero_mul]
    rw [hA0, tsum_ite_split (fun p : Nat.Primes => ((p : ℕ) % 4 = 1))
      (fun p : Nat.Primes => ((p : ℕ) ∣ 4 * d)) hsumY hsumW]
  have hZ : (∑' p : Nat.Primes,
      (if ((p : ℕ) % 4 = 1 ∧ ((p : ℕ) ∣ 4 * d)) then Pw σ p else 0)) ≤ Cc := by
    refine le_trans (Summable.tsum_le_tsum (fun p => ?_) hsumZ
      (summable_indicator hPw (Pw_nonneg σ) _)) hCc1
    by_cases h1 : ((p : ℕ) ∣ 4 * d)
    · by_cases h2 : ((p : ℕ) % 4 = 1)
      · rw [if_pos ⟨h2, h1⟩, if_pos h1]
      · rw [if_neg (by simp [h2]), if_pos h1]
        exact Pw_nonneg σ p
    · rw [if_neg (by simp [h1]), if_neg h1]
  have hW : (∑' p : Nat.Primes,
      (if ((p : ℕ) % 4 = 1 ∧ ((p : ℕ) ∣ 4 * d))
        then (heckeLam (chiTilde chi) (2 * m) (p : ℕ)).re * Pw σ p else 0)) ≤ 2 * Cc := by
    have hsumM : Summable (fun p : Nat.Primes =>
        (if ((p : ℕ) ∣ 4 * d) then (2 : ℝ) * Pw σ p else 0)) :=
      summable_indicator (hPw.mul_left 2) (fun p => mul_nonneg (by norm_num) (Pw_nonneg σ p)) _
    have h1 : (∑' p : Nat.Primes,
          (if ((p : ℕ) % 4 = 1 ∧ ((p : ℕ) ∣ 4 * d))
            then (heckeLam (chiTilde chi) (2 * m) (p : ℕ)).re * Pw σ p else 0))
        ≤ (∑' p : Nat.Primes, (if ((p : ℕ) ∣ 4 * d) then (2 : ℝ) * Pw σ p else 0)) := by
      refine Summable.tsum_le_tsum (fun p => ?_) hsumW hsumM
      by_cases h2 : ((p : ℕ) ∣ 4 * d)
      · by_cases h3 : ((p : ℕ) % 4 = 1)
        · rw [if_pos ⟨h3, h2⟩, if_pos h2]
          exact mul_le_mul_of_nonneg_right (lamRe_le_two hchi m p.2) (Pw_nonneg σ p)
        · rw [if_neg (by simp [h3]), if_pos h2]
          exact mul_nonneg (by norm_num) (Pw_nonneg σ p)
      · rw [if_neg (by simp [h2]), if_neg h2]
    have h2 : (∑' p : Nat.Primes, (if ((p : ℕ) ∣ 4 * d) then (2 : ℝ) * Pw σ p else 0))
        = 2 * (∑' p : Nat.Primes, (if ((p : ℕ) ∣ 4 * d) then Pw σ p else 0)) := by
      rw [← tsum_mul_left]
      refine tsum_congr (fun p => ?_)
      by_cases hh : ((p : ℕ) ∣ 4 * d) <;> simp [hh]
    rw [h2] at h1
    linarith [h1, hCc1]
  set M : ℝ := ∑' p : Nat.Primes, (if ((p : ℕ) % 4 = 1) then Pw σ p else 0) with hM
  set A : ℝ := ∑' p : Nat.Primes, (heckeLam (chiTilde chi) (2 * m) (p : ℕ)).re * Pw σ p with hA
  set S : ℝ := ∑' p : Nat.Primes,
    (if ((p : ℕ) % 4 = 1) then ‖heckeLam chi m (p : ℕ)‖ ^ 2 * Pw σ p else 0) with hS
  set X : ℝ := ∑' p : Nat.Primes,
    (if ((p : ℕ) % 4 = 1 ∧ ¬ ((p : ℕ) ∣ 4 * d)) then Pw σ p else 0) with hXd
  set Y : ℝ := ∑' p : Nat.Primes,
    (if ((p : ℕ) % 4 = 1 ∧ ¬ ((p : ℕ) ∣ 4 * d))
      then (heckeLam (chiTilde chi) (2 * m) (p : ℕ)).re * Pw σ p else 0) with hYd
  set Z : ℝ := ∑' p : Nat.Primes,
    (if ((p : ℕ) % 4 = 1 ∧ ((p : ℕ) ∣ 4 * d)) then Pw σ p else 0) with hZd
  set W : ℝ := ∑' p : Nat.Primes,
    (if ((p : ℕ) % 4 = 1 ∧ ((p : ℕ) ∣ 4 * d))
      then (heckeLam (chiTilde chi) (2 * m) (p : ℕ)).re * Pw σ p else 0) with hWd
  set R : ℝ := ∑' p : Nat.Primes,
    (if ((p : ℕ) % 4 = 1 ∧ ¬ ((p : ℕ) ∣ 4 * d))
      then (2 + (heckeLam (chiTilde chi) (2 * m) (p : ℕ)).re) * Pw σ p else 0) with hRd
  have hR_le : R ≤ S := by rw [hRd, hS]; exact hstep1
  have hR_eq : R = 2 * X + Y := by rw [hRd, hXd, hYd]; exact hstep2
  have hM' : M = X + Z := by rw [hM, hXd, hZd]; exact hMsplit
  have hA' : A = Y + W := by rw [hA, hYd, hWd]; exact hAsplit
  have hZ' : Z ≤ Cc := by rw [hZd]; exact hZ
  have hW' : W ≤ 2 * Cc := by rw [hWd]; exact hW
  linarith [hR_le, hR_eq, hM', hA', hZ', hW']

/-- **Case A**: if `2m = 0` and `χ̃` is trivial on the primary units, the twisted eigenvalue at a
split prime is exactly `2`. -/
private lemma caseA_lamT_eq_two {d : ℕ} (hd : 1 ≤ d) {chi : GaussianInt → ℂ}
    (hchi : IsCharMod4dStrict d chi) {m : ℤ} (hm : 2 * m = 0)
    (htriv : ∀ z : GaussianInt, Work.FIPlan.IsPrimary z → IsUnitMod4d d z → chiTilde chi z = 1)
    {p : ℕ} (hp : p.Prime) (hp4 : p % 4 = 1) (hpd : ¬ p ∣ 4 * d) :
    heckeLam (chiTilde chi) (2 * m) p = 2 := by
  obtain ⟨π, π', hπ, hπ', hgπ, hgπ', -, -, -, hclass⟩ := splitPrimaryClass p hp hp4
  have hmul : ∀ z w : GaussianInt, chiTilde chi (z * w) = chiTilde chi z * chiTilde chi w :=
    Work.FIArea6HeckeV2.chiTilde_mul' hchi
  have h1 : chiTilde chi 1 = 1 := Work.FIArea6HeckeV2.chiTilde_one' hchi
  have h := heckeLam_splitSum (chiTilde chi) (2 * m) p hp.pos hmul h1 π π' hπ hπ' hgπ hgπ' hclass 1
  rw [pow_one, geo_one] at h
  have hπu : IsUnitMod4d d π :=
    Work.FIArea6Hecke.R.isUnitMod4d_of_gnorm_eq_prime_pow (z := π) (ν := 1) hd hp hpd
      (by norm_num) (by rw [hgπ]; norm_num)
  have hπ'u : IsUnitMod4d d π' :=
    Work.FIArea6Hecke.R.isUnitMod4d_of_gnorm_eq_prime_pow (z := π') (ν := 1) hd hp hpd
      (by norm_num) (by rw [hgπ']; norm_num)
  have e1 : psi (chiTilde chi) (2 * m) π = 1 := by
    rw [psi, hm, zpow_zero, mul_one]
    exact htriv π hπ hπu
  have e2 : psi (chiTilde chi) (2 * m) π' = 1 := by
    rw [psi, hm, zpow_zero, mul_one]
    exact htriv π' hπ' hπ'u
  rw [h, e1, e2]
  norm_num

/-- **Case A** (continued): the twisted second moment dominates twice the split-prime sum. -/
private lemma A_ge_2M_of_caseA {d : ℕ} (hd : 1 ≤ d) {chi : GaussianInt → ℂ}
    (hchi : IsCharMod4dStrict d chi) {m : ℤ} (hm : 2 * m = 0)
    (htriv : ∀ z : GaussianInt, Work.FIPlan.IsPrimary z → IsUnitMod4d d z → chiTilde chi z = 1) :
    ∃ C : ℝ, 0 < C ∧ ∀ σ : ℝ, 1 < σ →
      2 * (∑' p : Nat.Primes, (if ((p : ℕ) % 4 = 1) then Pw σ p else 0)) - C
        ≤ ∑' p : Nat.Primes, (heckeLam (chiTilde chi) (2 * m) (p : ℕ)).re * Pw σ p := by
  obtain ⟨Cc, hCcpos, hCc⟩ := primes_dvd_correction d hd
  refine ⟨4 * Cc, by linarith, ?_⟩
  intro σ hσ
  have hCc1 : (∑' p : Nat.Primes, (if ((p : ℕ) ∣ 4 * d) then Pw σ p else 0)) ≤ Cc := by
    simpa only [Pw] using hCc σ hσ.le
  have hPw : Summable (Pw σ) := summable_Pw σ hσ
  have hsumX : Summable (fun p : Nat.Primes =>
      (if ((p : ℕ) % 4 = 1 ∧ ¬ ((p : ℕ) ∣ 4 * d)) then Pw σ p else 0)) :=
    summable_indicator hPw (Pw_nonneg σ) _
  have hsumZ : Summable (fun p : Nat.Primes =>
      (if ((p : ℕ) % 4 = 1 ∧ ((p : ℕ) ∣ 4 * d)) then Pw σ p else 0)) :=
    summable_indicator hPw (Pw_nonneg σ) _
  have hsumRe : Summable (fun p : Nat.Primes =>
      (heckeLam (chiTilde chi) (2 * m) (p : ℕ)).re * Pw σ p) := by
    refine Summable.of_norm_bounded (hPw.mul_left 2) (fun p => ?_)
    rw [Real.norm_eq_abs, abs_mul, abs_of_nonneg (Pw_nonneg σ p)]
    exact mul_le_mul_of_nonneg_right (lamTilde_prime_re_abs_le_two hchi m p.2) (Pw_nonneg σ p)
  have hsumY : Summable (fun p : Nat.Primes =>
      (if ((p : ℕ) % 4 = 1 ∧ ¬ ((p : ℕ) ∣ 4 * d))
        then (heckeLam (chiTilde chi) (2 * m) (p : ℕ)).re * Pw σ p else 0)) :=
    summable_indicator' hsumRe _
  have hsumW : Summable (fun p : Nat.Primes =>
      (if ((p : ℕ) % 4 = 1 ∧ ((p : ℕ) ∣ 4 * d))
        then (heckeLam (chiTilde chi) (2 * m) (p : ℕ)).re * Pw σ p else 0)) :=
    summable_indicator' hsumRe _
  have hAsplit : (∑' p : Nat.Primes, (heckeLam (chiTilde chi) (2 * m) (p : ℕ)).re * Pw σ p)
      = (∑' p : Nat.Primes,
          (if ((p : ℕ) % 4 = 1 ∧ ¬ ((p : ℕ) ∣ 4 * d))
            then (heckeLam (chiTilde chi) (2 * m) (p : ℕ)).re * Pw σ p else 0))
        + (∑' p : Nat.Primes,
          (if ((p : ℕ) % 4 = 1 ∧ ((p : ℕ) ∣ 4 * d))
            then (heckeLam (chiTilde chi) (2 * m) (p : ℕ)).re * Pw σ p else 0)) := by
    have hA0 : (∑' p : Nat.Primes, (heckeLam (chiTilde chi) (2 * m) (p : ℕ)).re * Pw σ p)
        = ∑' p : Nat.Primes,
            (if ((p : ℕ) % 4 = 1) then (heckeLam (chiTilde chi) (2 * m) (p : ℕ)).re * Pw σ p
              else 0) := by
      refine tsum_congr (fun p => ?_)
      by_cases h1 : ((p : ℕ) % 4 = 1)
      · rw [if_pos h1]
      · rw [if_neg h1, lamTilde_eq_zero_of_ne_one m p.2 h1, Complex.zero_re, zero_mul]
    rw [hA0, tsum_ite_split (fun p : Nat.Primes => ((p : ℕ) % 4 = 1))
      (fun p : Nat.Primes => ((p : ℕ) ∣ 4 * d)) hsumY hsumW]
  have hMsplit : (∑' p : Nat.Primes, (if ((p : ℕ) % 4 = 1) then Pw σ p else 0))
      = (∑' p : Nat.Primes, (if ((p : ℕ) % 4 = 1 ∧ ¬ ((p : ℕ) ∣ 4 * d)) then Pw σ p else 0))
        + (∑' p : Nat.Primes, (if ((p : ℕ) % 4 = 1 ∧ ((p : ℕ) ∣ 4 * d)) then Pw σ p else 0)) :=
    tsum_ite_split (fun p : Nat.Primes => ((p : ℕ) % 4 = 1))
      (fun p : Nat.Primes => ((p : ℕ) ∣ 4 * d)) hsumX hsumZ
  have hYeq : (∑' p : Nat.Primes,
        (if ((p : ℕ) % 4 = 1 ∧ ¬ ((p : ℕ) ∣ 4 * d))
          then (heckeLam (chiTilde chi) (2 * m) (p : ℕ)).re * Pw σ p else 0))
      = 2 * (∑' p : Nat.Primes,
        (if ((p : ℕ) % 4 = 1 ∧ ¬ ((p : ℕ) ∣ 4 * d)) then Pw σ p else 0)) := by
    rw [← tsum_mul_left]
    refine tsum_congr (fun p => ?_)
    by_cases h1 : ((p : ℕ) % 4 = 1 ∧ ¬ ((p : ℕ) ∣ 4 * d))
    · rw [if_pos h1, if_pos h1, caseA_lamT_eq_two hd hchi hm htriv p.2 h1.1 h1.2]
      norm_num
    · rw [if_neg h1, if_neg h1]; ring
  have hWge : -(2 * Cc) ≤ (∑' p : Nat.Primes,
      (if ((p : ℕ) % 4 = 1 ∧ ((p : ℕ) ∣ 4 * d))
        then (heckeLam (chiTilde chi) (2 * m) (p : ℕ)).re * Pw σ p else 0)) := by
    have hsumM : Summable (fun p : Nat.Primes =>
        (if ((p : ℕ) ∣ 4 * d) then (-2 : ℝ) * Pw σ p else 0)) :=
      summable_indicator' (hPw.mul_left (-2)) _
    have h1 : (∑' p : Nat.Primes, (if ((p : ℕ) ∣ 4 * d) then (-2 : ℝ) * Pw σ p else 0))
        ≤ (∑' p : Nat.Primes,
          (if ((p : ℕ) % 4 = 1 ∧ ((p : ℕ) ∣ 4 * d))
            then (heckeLam (chiTilde chi) (2 * m) (p : ℕ)).re * Pw σ p else 0)) := by
      refine Summable.tsum_le_tsum (fun p => ?_) hsumM hsumW
      by_cases h2 : ((p : ℕ) ∣ 4 * d)
      · by_cases h3 : ((p : ℕ) % 4 = 1)
        · rw [if_pos h2, if_pos ⟨h3, h2⟩]
          have hb := neg_two_le_lamRe hchi m p.2
          have hp := Pw_nonneg σ p
          nlinarith
        · rw [if_pos h2, if_neg (by simp [h3])]
          have hp := Pw_nonneg σ p
          nlinarith
      · rw [if_neg h2, if_neg (by simp [h2])]
    have h2 : (∑' p : Nat.Primes, (if ((p : ℕ) ∣ 4 * d) then (-2 : ℝ) * Pw σ p else 0))
        = (-2) * (∑' p : Nat.Primes, (if ((p : ℕ) ∣ 4 * d) then Pw σ p else 0)) := by
      rw [← tsum_mul_left]
      refine tsum_congr (fun p => ?_)
      by_cases hh : ((p : ℕ) ∣ 4 * d) <;> simp [hh]
    have h3 : (-2 : ℝ) * (∑' p : Nat.Primes, (if ((p : ℕ) ∣ 4 * d) then Pw σ p else 0))
        ≥ -(2 * Cc) := by
      nlinarith [hCc1]
    linarith
  set M : ℝ := ∑' p : Nat.Primes, (if ((p : ℕ) % 4 = 1) then Pw σ p else 0) with hM
  set A : ℝ := ∑' p : Nat.Primes, (heckeLam (chiTilde chi) (2 * m) (p : ℕ)).re * Pw σ p with hA
  set X : ℝ := ∑' p : Nat.Primes,
    (if ((p : ℕ) % 4 = 1 ∧ ¬ ((p : ℕ) ∣ 4 * d)) then Pw σ p else 0) with hXd
  set Y : ℝ := ∑' p : Nat.Primes,
    (if ((p : ℕ) % 4 = 1 ∧ ¬ ((p : ℕ) ∣ 4 * d))
      then (heckeLam (chiTilde chi) (2 * m) (p : ℕ)).re * Pw σ p else 0) with hYd
  set Z : ℝ := ∑' p : Nat.Primes,
    (if ((p : ℕ) % 4 = 1 ∧ ((p : ℕ) ∣ 4 * d)) then Pw σ p else 0) with hZd
  set W : ℝ := ∑' p : Nat.Primes,
    (if ((p : ℕ) % 4 = 1 ∧ ((p : ℕ) ∣ 4 * d))
      then (heckeLam (chiTilde chi) (2 * m) (p : ℕ)).re * Pw σ p else 0) with hWd
  have hM' : M = X + Z := by rw [hM, hXd, hZd]; exact hMsplit
  have hA' : A = Y + W := by rw [hA, hYd, hWd]; exact hAsplit
  have hY' : Y = 2 * X := by rw [hYd, hXd]; exact hYeq
  have hZle : Z ≤ Cc := by
    rw [hZd]
    refine le_trans (Summable.tsum_le_tsum (fun p => ?_) hsumZ
      (summable_indicator hPw (Pw_nonneg σ) _)) hCc1
    by_cases h1 : ((p : ℕ) ∣ 4 * d)
    · by_cases h2 : ((p : ℕ) % 4 = 1)
      · rw [if_pos ⟨h2, h1⟩, if_pos h1]
      · rw [if_neg (by simp [h2]), if_pos h1]
        exact Pw_nonneg σ p
    · rw [if_neg (by simp [h1]), if_neg h1]
  have hW'' : -(2 * Cc) ≤ W := by rw [hWd]; exact hWge
  linarith [hM', hA', hY', hW'', hZle]

/-- The main analytic bound, given the split-prime lower bound. -/
private theorem main_bound_of {d : ℕ} (hd : 1 ≤ d) {chi : GaussianInt → ℂ}
    (hchi : IsCharMod4dStrict d chi) (m : ℤ)
    (hMbound : ∃ C : ℝ, 0 < C ∧ ∀ σ : ℝ, 1 < σ → σ ≤ 2 →
      (1 / 256) * Real.log (1 / (σ - 1)) - C
        ≤ ∑' p : Nat.Primes, (if ((p : ℕ) % 4 = 1) then Pw σ p else 0)) :
    ∃ K : ℝ, 0 < K ∧ ∀ σ : ℝ, 1 < σ → σ ≤ 2 →
      (1 / 128) * Real.log (1 / (σ - 1)) - K
        ≤ ∑' p : Nat.Primes,
            (if ((p : ℕ) % 4 = 1) then ‖heckeLam chi m (p : ℕ)‖ ^ 2 * Pw σ p else 0) := by
  obtain ⟨Cm, hCmpos, hCm⟩ := hMbound
  obtain ⟨C1, hC1pos, hC1⟩ := chain_A hd hchi m
  obtain ⟨C2, hC2pos, hC2⟩ := log_le_sum_re_chiTilde hd hchi m
  by_cases hcase : (2 * m = 0 ∧ ∀ z : GaussianInt,
      Work.FIPlan.IsPrimary z → IsUnitMod4d d z → chiTilde chi z = 1)
  · obtain ⟨C3, hC3pos, hC3⟩ := A_ge_2M_of_caseA (m := m) hd hchi hcase.1 hcase.2
    refine ⟨4 * Cm + C3 + C1 + 1, by linarith, ?_⟩
    intro σ hσ1 hσ2
    have h1 := hC1 σ hσ1
    have h2 := hC3 σ hσ1
    have h3 := hCm σ hσ1 hσ2
    have hTnn : 0 ≤ Real.log (1 / (σ - 1)) := by
      apply Real.log_nonneg
      rw [le_div_iff₀ (by linarith)]
      linarith
    linarith
  · obtain ⟨c, δ, hcpos, hδpos, hc⟩ :=
      heckeLSeries_chiTilde_lower_bound_near_one hd hchi (chiTilde_isCharMod4dStrict' hchi) m hcase
    refine ⟨max (2 * Cm - Real.log c + C2 + C1 + 1) ((1 / 128) * |Real.log (1 / δ)| + 1),
      ?_, ?_⟩
    · exact lt_of_lt_of_le (by
        have h := abs_nonneg (Real.log (1 / δ))
        linarith) (le_max_right _ _)
    · intro σ hσ1 hσ2
      have h1 := hC1 σ hσ1
      have h2 := hC2 σ hσ1
      have hSnn : 0 ≤ ∑' p : Nat.Primes,
          (if ((p : ℕ) % 4 = 1) then ‖heckeLam chi m (p : ℕ)‖ ^ 2 * Pw σ p else 0) :=
        tsum_nonneg (fun p => by
          by_cases h1 : ((p : ℕ) % 4 = 1)
          · rw [if_pos h1]; exact mul_nonneg (sq_nonneg _) (Pw_nonneg σ p)
          · rw [if_neg h1])
      by_cases hσδ : σ < 1 + δ
      · have hc' := hc σ hσ1 hσδ
        have hlog : Real.log c ≤ Real.log ‖heckeLSeries (chiTilde chi) (2 * m) (σ : ℂ)‖ :=
          Real.log_le_log hcpos hc'
        have hM' := hCm σ hσ1 hσ2
        have hK' : 2 * Cm - Real.log c + C2 + C1 + 1
            ≤ max (2 * Cm - Real.log c + C2 + C1 + 1) ((1 / 128) * |Real.log (1 / δ)| + 1) :=
          le_max_left _ _
        linarith
      · push_neg at hσδ
        have hle : 1 / (σ - 1) ≤ 1 / δ := one_div_le_one_div_of_le hδpos (by linarith)
        have hT : Real.log (1 / (σ - 1)) ≤ |Real.log (1 / δ)| :=
          le_trans (Real.log_le_log (by apply one_div_pos.mpr; linarith) hle) (le_abs_self _)
        have hK' : (1 / 128) * |Real.log (1 / δ)| + 1
            ≤ max (2 * Cm - Real.log c + C2 + C1 + 1) ((1 / 128) * |Real.log (1 / δ)| + 1) :=
          le_max_right _ _
        linarith

/-- **The target lemma.** -/
theorem heckeLam_sq_prime_recip_divergence {d : ℕ} (hd : 1 ≤ d) (chi : GaussianInt → ℂ)
    (hchi : Work.FIArea5.S16Hecke.IsCharMod4dStrict d chi) (m : ℤ) :
    ¬ Summable (fun n : ℕ =>
      if n.Prime ∧ n % 4 = 1 then ‖Work.FIArea5.S16Hecke.heckeLam chi m n‖ ^ 2 / (n : ℝ)
        else 0) := by
  intro hsum
  obtain ⟨K, hKpos, hK⟩ := main_bound_of hd hchi m sum_one_mod_four_rpow_lower_bound
  set f : ℕ → ℝ := fun n =>
    (if n.Prime ∧ n % 4 = 1 then ‖heckeLam chi m n‖ ^ 2 / (n : ℝ) else 0) with hf
  have hfnn : ∀ n, 0 ≤ f n := by
    intro n
    change 0 ≤ (if n.Prime ∧ n % 4 = 1 then ‖heckeLam chi m n‖ ^ 2 / (n : ℝ) else 0)
    by_cases h : (n.Prime ∧ n % 4 = 1)
    · rw [if_pos h]; exact div_nonneg (sq_nonneg _) (Nat.cast_nonneg n)
    · rw [if_neg h]
  have hsub : Summable (fun p : Nat.Primes => f ↑p) := hsum.subtype (fun n => n.Prime)
  have hS0 : (∑' p : Nat.Primes, f ↑p) ≤ ∑' n : ℕ, f n :=
    Summable.tsum_subtype_le f {n : ℕ | n.Prime} hfnn hsum
  set S0 : ℝ := (∑' p : Nat.Primes, f ↑p) with hS0d
  have hS0nn : 0 ≤ S0 := by
    rw [hS0d]; exact tsum_nonneg (fun p => hfnn ↑p)
  set σ : ℝ := 1 + Real.exp (-(512 * (S0 + K + 1))) with hσd
  have hσ1 : 1 < σ := by
    rw [hσd]
    have := Real.exp_pos (-(512 * (S0 + K + 1)))
    linarith
  have hσ2 : σ ≤ 2 := by
    rw [hσd]
    have h1 : Real.exp (-(512 * (S0 + K + 1))) ≤ 1 := by
      rw [Real.exp_le_one_iff]
      nlinarith [hS0nn, hKpos]
    linarith
  have hkey := hK σ hσ1 hσ2
  have hlog : Real.log (1 / (σ - 1)) = 512 * (S0 + K + 1) := by
    have h1 : σ - 1 = Real.exp (-(512 * (S0 + K + 1))) := by rw [hσd]; ring
    rw [h1, one_div, Real.log_inv, Real.log_exp]
    ring
  have hbridge : (∑' p : Nat.Primes,
        (if ((p : ℕ) % 4 = 1) then ‖heckeLam chi m (p : ℕ)‖ ^ 2 * Pw σ p else 0))
      = ∑' p : Nat.Primes, f ↑p * Pw (σ - 1) p := by
    refine tsum_congr (fun p => ?_)
    change (if ((p : ℕ) % 4 = 1) then ‖heckeLam chi m (p : ℕ)‖ ^ 2 * Pw σ p else 0)
      = (if (p : ℕ).Prime ∧ (p : ℕ) % 4 = 1
          then ‖heckeLam chi m (p : ℕ)‖ ^ 2 / ((p : ℕ) : ℝ) else 0) * Pw (σ - 1) p
    by_cases h41 : ((p : ℕ) % 4 = 1)
    · rw [if_pos h41, if_pos ⟨p.2, h41⟩]
      have hppos : (0 : ℝ) < ((p : ℕ) : ℝ) := by
        exact_mod_cast (show (0 : ℕ) < (p : ℕ) from p.2.pos)
      have hsplit : ((p : ℕ) : ℝ) ^ (-σ) = ((p : ℕ) : ℝ)⁻¹ * ((p : ℕ) : ℝ) ^ (-(σ - 1)) := by
        rw [show (-σ : ℝ) = -1 + (-(σ - 1)) by ring, Real.rpow_add hppos, Real.rpow_neg_one]
      rw [Pw, Pw, hsplit, div_eq_mul_inv]
      ring
    · rw [if_neg h41, if_neg (fun hh => h41 hh.2)]
      ring
  have hle1 : (∑' p : Nat.Primes, f ↑p * Pw (σ - 1) p) ≤ ∑' p : Nat.Primes, f ↑p := by
    refine Summable.tsum_le_tsum (fun p => ?_) ?_ hsub
    · have h1 : Pw (σ - 1) p ≤ 1 := by
        rw [Pw]
        exact Real.rpow_le_one_of_one_le_of_nonpos
          (by exact_mod_cast (show (1 : ℕ) ≤ (p : ℕ) from p.2.one_le)) (by linarith)
      nlinarith [hfnn ↑p, Pw_nonneg (σ - 1) p]
    · refine Summable.of_norm_bounded hsub (fun p => ?_)
      rw [Real.norm_eq_abs, abs_mul, abs_of_nonneg (hfnn ↑p),
        abs_of_nonneg (Pw_nonneg (σ - 1) p)]
      have h1 : Pw (σ - 1) p ≤ 1 := by
        rw [Pw]
        exact Real.rpow_le_one_of_one_le_of_nonpos
          (by exact_mod_cast (show (1 : ℕ) ≤ (p : ℕ) from p.2.one_le)) (by linarith)
      nlinarith [hfnn ↑p, Pw_nonneg (σ - 1) p]
  rw [hbridge] at hkey
  have hkey2 : (1 / 128) * Real.log (1 / (σ - 1)) - K ≤ S0 := by
    rw [hS0d]; linarith [hkey, hle1]
  linarith [hkey2, hlog, hS0nn, hKpos]

end

end Work.FIArea6V
