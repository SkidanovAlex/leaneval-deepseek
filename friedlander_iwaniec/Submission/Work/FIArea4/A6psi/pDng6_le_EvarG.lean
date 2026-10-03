import Mathlib
import Submission.Work.FIArea4.A6psi.Dng6Defs
import Submission.Work.FIArea4.A6psi.ratioSym_scalePt_factor
import Submission.Work.FIArea4.A6psi.Diag6Self
import Submission.Work.FIArea4.A6psi.S15pDng6_eq_sum_stratumE_sub_diag6

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false

namespace Work.FIArea4.A6psi

open Finset
open scoped BigOperators
open Work.FIArea4.S15red

attribute [local instance] Classical.propDecidable

noncomputable section

/-! ## 1. The round-6 counterpart of the frozen `(15.2)` factorisation

The frozen (§15) factorisation `Work.FIArea4.S15red.SSE.ssFactor` writes the `(d,e)`-stratum
summand of the pair sum as `ssConst · ssFac · (ssArrA · ssArrB)`, its content being the
factorisation `(r₁r₂+s₁s₂|d) = (e²+a²|d')·(s₁|e)(s₂|e)(r₁|d')(r₂|d')` of the Jacobi symbol on the
class `s ≡ a r (mod 4d')`.  For the *round-6* symbol `(z₂/z₁|d)` the same computation gives the
**square** `ssFac²` (one copy of `(e²+a²|d')` is the class factor, the other is the twist
`(|z₁|²|d)`), which is
`Work.FIArea4.A6psi.ratioSym_scalePt_factor`. -/

/-- **The round-6 term against the frozen term**: on the `(d,e)`-stratum the round-6 summand is the
frozen summand multiplied by the class factor `ssFac`. -/
private lemma ssTerm6_eq_ssFac_mul (X j d e : ℕ) (he : 1 ≤ e) (hd : 1 ≤ d) (hed : e ∣ d)
    (u t : ℝ) (ℓ : ℤ) (β : GaussianInt → ℂ) (w1 w2 : GaussianInt)
    (hc1 : Nat.Coprime w1.re.natAbs (d / e)) (hc2 : Nat.Coprime w2.re.natAbs (d / e))
    (hprim : Nat.Coprime ((e : ℤ) * w1.re).natAbs (2 * w1.im.natAbs))
    (h4 : 4 * (d / e) ∣ Work.FIPlan.absDelta w1 w2) :
    ssTerm6 X j d u t ℓ (Work.FIArea4.scalePt e w1) (Work.FIArea4.scalePt e w2)
      = Work.FIArea4.S15red.SSE.ssFac e (d / e)
          ((w1.im : ZMod (4 * (d / e))) * ((w1.re : ZMod (4 * (d / e))))⁻¹)
        * Work.FIArea4.S15red.SSE.ssTerm X j d u t ℓ
            (Work.FIArea4.scalePt e w1) (Work.FIArea4.scalePt e w2) := by
  have hd' : 1 ≤ d / e := by
    have h0 : 0 < d / e := Nat.div_pos (Nat.le_of_dvd (by omega) hed) (by omega)
    omega
  have hde : e * (d / e) = d := Nat.mul_div_cancel' hed
  have hA := ratioSym_scalePt_factor e (d / e) he hd' w1 w2 hc1 hc2 hprim h4
  rw [hde] at hA
  simp only [ssTerm6, Work.FIArea4.S15red.SSE.ssTerm, Work.FIArea4.S15red.SSE.ssFac]
  rw [hA]
  push_cast
  ring

/-- **The pointwise factorisation of the round-6 `(d,e)`-stratum summand.** -/
private lemma ssFactor6 (X j d e : ℕ) (he : 1 ≤ e) (hd : 1 ≤ d) (hed : e ∣ d)
    (u t : ℝ) (ℓ : ℤ) (β : GaussianInt → ℂ)
    (hβ : ∀ z : GaussianInt, β z ≠ 0 → Nat.Coprime z.re.natAbs (2 * z.im.natAbs))
    {w1 w2 : GaussianInt} (hb1 : β (Work.FIArea4.scalePt e w1) ≠ 0)
    (hb2 : β (Work.FIArea4.scalePt e w2) ≠ 0)
    (hc1 : Nat.Coprime w1.re.natAbs (d / e)) (hc2 : Nat.Coprime w2.re.natAbs (d / e))
    (h4 : 4 * (d / e) ∣ Work.FIPlan.absDelta w1 w2) :
    β (Work.FIArea4.scalePt e w1) * star (β (Work.FIArea4.scalePt e w2))
        * ssTerm6 X j d u t ℓ (Work.FIArea4.scalePt e w1) (Work.FIArea4.scalePt e w2)
      = Work.FIArea4.S15red.SSE.ssConst X j d t
          * (Work.FIArea4.S15red.SSE.ssFac e (d / e)
              ((w1.im : ZMod (4 * (d / e))) * ((w1.re : ZMod (4 * (d / e))))⁻¹)) ^ 2
          * (Work.FIArea4.S15red.SSE.ssArrA e (d / e) β u t ℓ w1
              * Work.FIArea4.S15red.SSE.ssArrB e (d / e) β u t ℓ w2) := by
  have hprim : Nat.Coprime ((e : ℤ) * w1.re).natAbs (2 * w1.im.natAbs) := by
    simpa [Work.FIArea4.scalePt_re, Work.FIArea4.scalePt_im]
      using hβ (Work.FIArea4.scalePt e w1) hb1
  have hterm := ssTerm6_eq_ssFac_mul X j d e he hd hed u t ℓ β w1 w2 hc1 hc2 hprim h4
  have hf := Work.FIArea4.S15red.SSE.ssFactor X j d e he hd hed u t ℓ β hβ hb1 hb2 hc1 hc2 h4
  calc β (Work.FIArea4.scalePt e w1) * star (β (Work.FIArea4.scalePt e w2))
          * ssTerm6 X j d u t ℓ (Work.FIArea4.scalePt e w1) (Work.FIArea4.scalePt e w2)
      = β (Work.FIArea4.scalePt e w1) * star (β (Work.FIArea4.scalePt e w2))
          * (Work.FIArea4.S15red.SSE.ssFac e (d / e)
              ((w1.im : ZMod (4 * (d / e))) * ((w1.re : ZMod (4 * (d / e))))⁻¹)
            * Work.FIArea4.S15red.SSE.ssTerm X j d u t ℓ
                (Work.FIArea4.scalePt e w1) (Work.FIArea4.scalePt e w2)) := by rw [hterm]
    _ = Work.FIArea4.S15red.SSE.ssFac e (d / e)
          ((w1.im : ZMod (4 * (d / e))) * ((w1.re : ZMod (4 * (d / e))))⁻¹)
        * (β (Work.FIArea4.scalePt e w1) * star (β (Work.FIArea4.scalePt e w2))
            * Work.FIArea4.S15red.SSE.ssTerm X j d u t ℓ
                (Work.FIArea4.scalePt e w1) (Work.FIArea4.scalePt e w2)) := by ring
    _ = Work.FIArea4.S15red.SSE.ssFac e (d / e)
          ((w1.im : ZMod (4 * (d / e))) * ((w1.re : ZMod (4 * (d / e))))⁻¹)
        * (Work.FIArea4.S15red.SSE.ssConst X j d t
            * Work.FIArea4.S15red.SSE.ssFac e (d / e)
                ((w1.im : ZMod (4 * (d / e))) * ((w1.re : ZMod (4 * (d / e))))⁻¹)
            * (Work.FIArea4.S15red.SSE.ssArrA e (d / e) β u t ℓ w1
                * Work.FIArea4.S15red.SSE.ssArrB e (d / e) β u t ℓ w2)) := by rw [hf]
    _ = Work.FIArea4.S15red.SSE.ssConst X j d t
          * (Work.FIArea4.S15red.SSE.ssFac e (d / e)
              ((w1.im : ZMod (4 * (d / e))) * ((w1.re : ZMod (4 * (d / e))))⁻¹)) ^ 2
          * (Work.FIArea4.S15red.SSE.ssArrA e (d / e) β u t ℓ w1
              * Work.FIArea4.S15red.SSE.ssArrB e (d / e) β u t ℓ w2) := by ring


/-- **The pointwise identity of the round-6 stratum summand with its class factorisation.** -/
private lemma ssPoint6 (Pa : Work.FITop.Params) (X j d e : ℕ) (φ : ℝ) (β : GaussianInt → ℂ)
    (ℓ : ℤ) (u t : ℝ) (hβ : Work.FIArea4.IsPrimBoxCoeff Pa φ β)
    (he : 1 ≤ e) (hd : 1 ≤ d) (hed : e ∣ d) (w1 w2 : GaussianInt) :
    (if Nat.Coprime w1.re.natAbs (d / e) ∧ 4 * (d / e) ∣ Work.FIPlan.absDelta w1 w2 then
        (β (Work.FIArea4.scalePt e w1) * star (β (Work.FIArea4.scalePt e w2)))
          * ssTerm6 X j d u t ℓ (Work.FIArea4.scalePt e w1) (Work.FIArea4.scalePt e w2) else 0)
      = (if (Work.FIPlan.Delta w1 w2 : ZMod (4 * (d / e))) = 0 then
          (Work.FIArea4.S15red.SSE.ssConst X j d t * (Work.FIArea4.S15red.SSE.ssFac e (d / e)
              ((w1.im : ZMod (4 * (d / e))) * ((w1.re : ZMod (4 * (d / e))))⁻¹)) ^ 2)
            * (Work.FIArea4.S15red.SSE.ssU Pa e (d / e) β u t ℓ w1
                * star (Work.FIArea4.S15red.SSE.ssV Pa e (d / e) β u t ℓ w2)) else 0) := by
  classical
  by_cases hcond : Nat.Coprime w1.re.natAbs (d / e) ∧ 4 * (d / e) ∣ Work.FIPlan.absDelta w1 w2
  · rw [if_pos hcond,
      if_pos (Work.FIArea4.S15red.SSE.delta_zmod_eq_zero_of_dvd_absDelta hcond.2)]
    by_cases hb1 : β (Work.FIArea4.scalePt e w1) = 0
    · have hz : Work.FIArea4.S15red.SSE.ssU Pa e (d / e) β u t ℓ w1 = 0 := by
        rw [Work.FIArea4.S15red.SSE.ssU]
        split_ifs with hc4
        · rw [Work.FIArea4.S15red.SSE.S15strU_eq', hb1]; simp
        · rfl
      simp only [hb1, zero_mul, mul_zero, hz]
    by_cases hb2 : β (Work.FIArea4.scalePt e w2) = 0
    · have hz : Work.FIArea4.S15red.SSE.ssV Pa e (d / e) β u t ℓ w2 = 0 := by
        rw [Work.FIArea4.S15red.SSE.ssV]
        split_ifs with hc4
        · rw [Work.FIArea4.S15red.SSE.S15strV_eq', hb2]; simp
        · rfl
      simp only [hb2, star_zero, zero_mul, mul_zero, hz]
    · have hodd1 := Work.FIArea4.S15red.SSE.odd_re_of_prim (e := e)
        (fun z hz => Work.FIArea4.IsPrimBoxCoeff.coprime hβ hz) hb1
      have hodd2 := Work.FIArea4.S15red.SSE.odd_re_of_prim (e := e)
        (fun z hz => Work.FIArea4.IsPrimBoxCoeff.coprime hβ hz) hb2
      have hc2 : Nat.Coprime w2.re.natAbs (d / e) := by
        have hD : (d : ℤ) ∣ Work.FIPlan.Delta (Work.FIArea4.scalePt e w1)
            (Work.FIArea4.scalePt e w2) := by
          have h4d : 4 * d ∣ Work.FIPlan.absDelta (Work.FIArea4.scalePt e w1)
              (Work.FIArea4.scalePt e w2) := by
            rw [Work.FIArea4.S15red.SSE.absDelta_scalePt]
            exact (Work.FIArea4.S15red.SSE.four_mul_dvd_iff he hed).mpr hcond.2
          have hd1 : d ∣ Work.FIPlan.absDelta (Work.FIArea4.scalePt e w1)
              (Work.FIArea4.scalePt e w2) := dvd_trans (dvd_mul_left d 4) h4d
          have h2 : (d : ℤ) ∣ ((Work.FIPlan.absDelta (Work.FIArea4.scalePt e w1)
              (Work.FIArea4.scalePt e w2) : ℕ) : ℤ) := by exact_mod_cast hd1
          rw [Work.FIPlan.absDelta] at h2
          exact (Int.dvd_natAbs).mp h2
        have hg := Work.FIArea4.S15red.gcd_re_eq_of_delta
          (Work.FIArea4.IsPrimBoxCoeff.coprime hβ hb1)
          (Work.FIArea4.IsPrimBoxCoeff.coprime hβ hb2) hD
        have hg2 : Nat.gcd d (Work.FIArea4.scalePt e w2).re.natAbs = e := by
          rw [← hg, Work.FIArea4.scalePt_re]
          exact Work.FIArea4.S15red.SSE.gcd_scalePt_of_coprime hed hcond.1
        have hgw : Nat.gcd d ((e : ℤ) * w2.re).natAbs = e := by
          have h1 : Nat.gcd d ((e : ℤ) * w2.re).natAbs
              = Nat.gcd d (Work.FIArea4.scalePt e w2).re.natAbs := by
            rw [Work.FIArea4.scalePt_re]
          rw [h1, hg2]
        exact Work.FIArea4.S15red.SSE.coprime_of_gcd_scalePt he hed hgw
      rw [Work.FIArea4.S15red.SSE.ssU_eq_ssArrA hodd1 hcond.1,
        Work.FIArea4.S15red.SSE.ssV_eq_ssArrB hodd2 hc2]
      exact ssFactor6 X j d e he hd hed u t ℓ β
        (fun z hz => Work.FIArea4.IsPrimBoxCoeff.coprime hβ hz) hb1 hb2 hcond.1 hc2 hcond.2
  · rw [if_neg hcond]
    by_cases hΔ0 : (Work.FIPlan.Delta w1 w2 : ZMod (4 * (d / e))) = 0
    · rw [if_pos hΔ0]
      have h4 : 4 * (d / e) ∣ Work.FIPlan.absDelta w1 w2 := by
        have h1 : ((4 * (d / e) : ℕ) : ℤ) ∣ Work.FIPlan.Delta w1 w2 :=
          (ZMod.intCast_zmod_eq_zero_iff_dvd (Work.FIPlan.Delta w1 w2) (4 * (d / e))).mp hΔ0
        have h2 : ((4 * (d / e) : ℕ) : ℤ)
            ∣ (((Work.FIPlan.Delta w1 w2).natAbs : ℕ) : ℤ) := Int.dvd_natAbs.mpr h1
        have h3 : 4 * (d / e) ∣ (Work.FIPlan.Delta w1 w2).natAbs := by exact_mod_cast h2
        rwa [Work.FIPlan.absDelta]
      have hnc : ¬ Nat.Coprime w1.re.natAbs (d / e) := fun hc => hcond ⟨hc, h4⟩
      have hnotcop : ¬ Nat.Coprime w1.re.natAbs (4 * (d / e)) := fun hc4 =>
        hnc (hc4.coprime_dvd_right (dvd_mul_left (d / e) 4))
      have hz : Work.FIArea4.S15red.SSE.ssU Pa e (d / e) β u t ℓ w1 = 0 := by
        rw [Work.FIArea4.S15red.SSE.ssU, if_neg hnotcop]
      simp only [hz, zero_mul, mul_zero]
    · rw [if_neg hΔ0]

/-- **The pointwise identity of the `w`-side round-6 stratum summand with its class form.** -/
private lemma ssW6_eq_ssT6 (Pa : Work.FITop.Params) (X j d e : ℕ) (φ : ℝ) (β : GaussianInt → ℂ)
    (ℓ : ℤ) (u t : ℝ) (hβ : Work.FIArea4.IsPrimBoxCoeff Pa φ β)
    (hX : X < d) (he : 1 ≤ e) (hd : 1 ≤ d) (hed : e ∣ d) (w1 w2 : GaussianInt) :
    ssW6 X j d e β u t ℓ w1 w2 = ssT6 Pa X j d e β u t ℓ w1 w2 := by
  have hp := ssPoint6 Pa X j d e φ β ℓ u t hβ he hd hed w1 w2
  have hC : (Nat.gcd d (Work.FIArea4.scalePt e w1).re.natAbs = e ∧ X < d
        ∧ 4 * d ∣ Work.FIPlan.absDelta (Work.FIArea4.scalePt e w1) (Work.FIArea4.scalePt e w2))
      ↔ (Nat.Coprime w1.re.natAbs (d / e) ∧ 4 * (d / e) ∣ Work.FIPlan.absDelta w1 w2) := by
    have h1 : Nat.gcd d (Work.FIArea4.scalePt e w1).re.natAbs = e
        ↔ Nat.Coprime w1.re.natAbs (d / e) := by
      rw [Work.FIArea4.scalePt_re]
      exact ⟨fun h => Work.FIArea4.S15red.SSE.coprime_of_gcd_scalePt he hed h,
        fun h => Work.FIArea4.S15red.SSE.gcd_scalePt_of_coprime hed h⟩
    have h2 : 4 * d ∣ Work.FIPlan.absDelta (Work.FIArea4.scalePt e w1)
          (Work.FIArea4.scalePt e w2)
        ↔ 4 * (d / e) ∣ Work.FIPlan.absDelta w1 w2 := by
      rw [Work.FIArea4.S15red.SSE.absDelta_scalePt]
      exact Work.FIArea4.S15red.SSE.four_mul_dvd_iff he hed
    rw [h1, h2]
    constructor
    · rintro ⟨ha, -, hb⟩; exact ⟨ha, hb⟩
    · rintro ⟨ha, hb⟩; exact ⟨ha, hX, hb⟩
  simp only [ssW6, ssT6]
  rw [if_congr hC rfl rfl]
  exact hp

end

/-- **The `e`-stratum of the round-6 per-modulus §15 sum, bounded by the stratum variances.** -/
theorem stratumSumE6_le_EvarG (Pa : Work.FITop.Params) (X j d e : ℕ) (φ : ℝ)
    (β : GaussianInt → ℂ) (ℓ : ℤ) (u t : ℝ) (hβ : Work.FIArea4.IsPrimBoxCoeff Pa φ β)
    (hd : 1 ≤ d) (he : e ∈ d.divisors) :
    ‖stratumSumE6 Pa X j d β ℓ u t e‖ ≤
      2 * (Real.sqrt (Work.FIArea4.EvarG (Work.FITop.radN Pa) (4 * (d / e))
            (Work.FIArea4.S15strU β u t ℓ e))
        * Real.sqrt (Work.FIArea4.EvarG (Work.FITop.radN Pa) (4 * (d / e))
            (Work.FIArea4.S15strV β u t ℓ e))) := by
  classical
  have he1 : 1 ≤ e := Work.FIArea4.S15red.SSE.one_le_of_mem_divisors he
  have hed : e ∣ d := Work.FIArea4.S15red.SSE.dvd_of_mem_divisors he
  have hd0 : d ≠ 0 := (Nat.mem_divisors.mp he).2
  have hdpos : 0 < d := Nat.pos_of_ne_zero hd0
  by_cases hX : X < d
  · set S : ℂ := ∑ z1 ∈ Work.FITop.boxN Pa, ∑ z2 ∈ Work.FITop.boxN Pa,
        ssZ6 X j d e β u t ℓ z1 z2 with hSdef
    set T : ℂ := ∑ w1 ∈ Work.FITop.boxN Pa, ∑ w2 ∈ Work.FITop.boxN Pa,
        ssT6 Pa X j d e β u t ℓ w1 w2 with hTdef
    have hSU : stratumSumE6 Pa X j d β ℓ u t e = 2 * S := by
      rw [hSdef]
      unfold stratumSumE6
      simp only [ssZ6]
      rw [Finset.mul_sum]
      refine Finset.sum_congr rfl (fun z1 _ => ?_)
      rw [Finset.mul_sum]
      refine Finset.sum_congr rfl (fun z2 _ => ?_)
      rw [summand_eq6]
      split_ifs <;> ring
    have hST : S = T := by
      rw [hSdef, hTdef]
      set A : Finset GaussianInt := (Work.FITop.boxN Pa).filter (fun z => (e : ℤ) ∣ z.re) with hAdef
      set W : Finset GaussianInt := (Work.FITop.boxN Pa).filter
          (fun w => Work.FIArea4.scalePt e w ∈ Work.FITop.boxN Pa) with hWdef
      have hB : (∑ z1 ∈ Work.FITop.boxN Pa, ∑ z2 ∈ Work.FITop.boxN Pa,
            ssZ6 X j d e β u t ℓ z1 z2)
          = ∑ z1 ∈ A, ∑ z2 ∈ A, ssZ6 X j d e β u t ℓ z1 z2 := by
        rw [hAdef]
        have h1 : (∑ z1 ∈ Work.FITop.boxN Pa, ∑ z2 ∈ Work.FITop.boxN Pa,
              ssZ6 X j d e β u t ℓ z1 z2)
            = ∑ z1 ∈ (Work.FITop.boxN Pa).filter (fun z => (e : ℤ) ∣ z.re),
                ∑ z2 ∈ Work.FITop.boxN Pa, ssZ6 X j d e β u t ℓ z1 z2 :=
          (Finset.sum_subset (Finset.filter_subset
            (p := fun z => (e : ℤ) ∣ z.re) (Work.FITop.boxN Pa))
            (fun z1 hz1 hnot => Finset.sum_eq_zero (fun z2 _ => by
              rw [ssZ6, if_neg]
              rintro ⟨hg, -, -⟩
              exact hnot (Finset.mem_filter.mpr
                ⟨hz1, Work.FIArea4.S15red.SSE.dvd_re_of_gcd_eq hg⟩)))).symm
        rw [h1]
        refine Finset.sum_congr rfl (fun z1 hz1 => ?_)
        refine (Finset.sum_subset (f := fun z2 => ssZ6 X j d e β u t ℓ z1 z2)
          (Finset.filter_subset (fun z => (e : ℤ) ∣ z.re) (Work.FITop.boxN Pa)) ?_).symm
        intro z2 hz2 hnot
        rw [ssZ6]
        by_cases hc : Nat.gcd d z1.re.natAbs = e ∧ X < d ∧ 4 * d ∣ Work.FIPlan.absDelta z1 z2
        · rw [if_pos hc]
          by_cases hb1 : β z1 = 0
          · rw [hb1]; simp
          by_cases hb2 : β z2 = 0
          · rw [hb2]; simp
          exfalso
          have hΔ : (d : ℤ) ∣ Work.FIPlan.Delta z1 z2 := by
            have h1 : d ∣ Work.FIPlan.absDelta z1 z2 := dvd_trans (dvd_mul_left d 4) hc.2.2
            have h2 : (d : ℤ) ∣ ((Work.FIPlan.absDelta z1 z2 : ℕ) : ℤ) := by exact_mod_cast h1
            rw [Work.FIPlan.absDelta] at h2
            exact (Int.dvd_natAbs).mp h2
          have hg := Work.FIArea4.S15red.gcd_re_eq_of_delta
            (Work.FIArea4.IsPrimBoxCoeff.coprime hβ hb1)
            (Work.FIArea4.IsPrimBoxCoeff.coprime hβ hb2) hΔ
          have hg2 : Nat.gcd d z2.re.natAbs = e := by rw [← hg]; exact hc.1
          exact hnot (Finset.mem_filter.mpr
            ⟨hz2, Work.FIArea4.S15red.SSE.dvd_re_of_gcd_eq hg2⟩)
        · rw [if_neg hc]
      have hCD : (∑ z1 ∈ A, ∑ z2 ∈ A, ssZ6 X j d e β u t ℓ z1 z2)
          = ∑ w1 ∈ Work.FITop.boxN Pa, ∑ w2 ∈ Work.FITop.boxN Pa,
              ssW6 X j d e β u t ℓ w1 w2 := by
        have h1 : (∑ z1 ∈ A, ∑ z2 ∈ A, ssZ6 X j d e β u t ℓ z1 z2)
            = ∑ w1 ∈ W, ∑ w2 ∈ W, ssW6 X j d e β u t ℓ w1 w2 := by
          rw [hAdef, hWdef, Work.FIArea4.S15red.SSE.sum_image_A_eq_sum_W Pa e he1]
          refine Finset.sum_congr rfl (fun w1 _ => ?_)
          rw [Work.FIArea4.S15red.SSE.sum_image_A_eq_sum_W Pa e he1]
          refine Finset.sum_congr rfl (fun w2 _ => ?_)
          simp only [ssZ6, ssW6]
        have h2 : (∑ w1 ∈ W, ∑ w2 ∈ W, ssW6 X j d e β u t ℓ w1 w2)
            = ∑ w1 ∈ Work.FITop.boxN Pa, ∑ w2 ∈ Work.FITop.boxN Pa,
                ssW6 X j d e β u t ℓ w1 w2 := by
          rw [hWdef]
          have h0 : ∀ w1 ∈ Work.FITop.boxN Pa, w1 ∉ (Work.FITop.boxN Pa).filter
              (fun w => Work.FIArea4.scalePt e w ∈ Work.FITop.boxN Pa) →
              ∀ w2, ssW6 X j d e β u t ℓ w1 w2 = 0 := by
            intro w1 hw1 hw1not w2
            have hnb : Work.FIArea4.scalePt e w1 ∉ Work.FITop.boxN Pa := fun hmem =>
              hw1not (Finset.mem_filter.mpr ⟨hw1, hmem⟩)
            have hb : β (Work.FIArea4.scalePt e w1) = 0 :=
              Work.FIArea4.S15red.SSE.eq_zero_of_not_mem_boxN Pa
                (Work.FIArea4.IsPrimBoxCoeff.toBoxCoeff hβ) hnb
            rw [ssW6]
            by_cases hc : Nat.gcd d (Work.FIArea4.scalePt e w1).re.natAbs = e ∧ X < d
                ∧ 4 * d ∣ Work.FIPlan.absDelta (Work.FIArea4.scalePt e w1)
                    (Work.FIArea4.scalePt e w2)
            · rw [if_pos hc, hb]; simp
            · rw [if_neg hc]
          have h0' : ∀ w2 ∈ Work.FITop.boxN Pa, w2 ∉ (Work.FITop.boxN Pa).filter
              (fun w => Work.FIArea4.scalePt e w ∈ Work.FITop.boxN Pa) →
              ∀ w1, ssW6 X j d e β u t ℓ w1 w2 = 0 := by
            intro w2 hw2 hw2not w1
            have hnb : Work.FIArea4.scalePt e w2 ∉ Work.FITop.boxN Pa := fun hmem =>
              hw2not (Finset.mem_filter.mpr ⟨hw2, hmem⟩)
            have hb : β (Work.FIArea4.scalePt e w2) = 0 :=
              Work.FIArea4.S15red.SSE.eq_zero_of_not_mem_boxN Pa
                (Work.FIArea4.IsPrimBoxCoeff.toBoxCoeff hβ) hnb
            rw [ssW6]
            by_cases hc : Nat.gcd d (Work.FIArea4.scalePt e w1).re.natAbs = e ∧ X < d
                ∧ 4 * d ∣ Work.FIPlan.absDelta (Work.FIArea4.scalePt e w1)
                    (Work.FIArea4.scalePt e w2)
            · rw [if_pos hc, hb]; simp
            · rw [if_neg hc]
          rw [(Finset.sum_subset (Finset.filter_subset _ _) (fun w1 hw1 hnot =>
            Finset.sum_eq_zero (fun w2 _ => h0 w1 hw1 hnot w2))).symm]
          refine Finset.sum_congr rfl (fun w1 _ => ?_)
          rw [(Finset.sum_subset (Finset.filter_subset _ _) (fun w2 hw2 hnot =>
            h0' w2 hw2 hnot w1)).symm]
        exact h1.trans h2
      have hE : (∑ w1 ∈ Work.FITop.boxN Pa, ∑ w2 ∈ Work.FITop.boxN Pa,
            ssW6 X j d e β u t ℓ w1 w2)
          = ∑ w1 ∈ Work.FITop.boxN Pa, ∑ w2 ∈ Work.FITop.boxN Pa,
              ssT6 Pa X j d e β u t ℓ w1 w2 := by
        refine Finset.sum_congr rfl (fun w1 _ => Finset.sum_congr rfl (fun w2 _ => ?_))
        exact ssW6_eq_ssT6 Pa X j d e φ β ℓ u t hβ hX he1 hd hed w1 w2
      rw [hB, hCD, hE]
    have hm1 : 1 ≤ 4 * (d / e) := by
      have hd'1 : 0 < d / e := Nat.div_pos (Nat.le_of_dvd hdpos hed)
        (lt_of_lt_of_le Nat.zero_lt_one he1)
      omega
    have hu : ∀ z : GaussianInt, Work.FIArea4.S15red.SSE.ssU Pa e (d / e) β u t ℓ z ≠ 0 →
        Nat.Coprime z.re.natAbs (4 * (d / e)) := by
      intro z hz
      by_contra hc
      exact hz (by rw [Work.FIArea4.S15red.SSE.ssU, if_neg hc])
    have hv : ∀ z : GaussianInt, Work.FIArea4.S15red.SSE.ssV Pa e (d / e) β u t ℓ z ≠ 0 →
        Nat.Coprime z.re.natAbs (4 * (d / e)) := by
      intro z hz
      by_contra hc
      exact hz (by rw [Work.FIArea4.S15red.SSE.ssV, if_neg hc])
    have hF : ∀ a : ZMod (4 * (d / e)),
        ‖Work.FIArea4.S15red.SSE.ssConst X j d t
            * (Work.FIArea4.S15red.SSE.ssFac e (d / e) a) ^ 2‖ ≤ 1 := by
      intro a
      have h1 := Work.FIArea4.S15red.SSE.norm_ssConst_le_one X j d hd t
      have h2 := Work.FIArea4.S15red.SSE.norm_ssFac_le_one e (d / e) a
      have h3 : ‖Work.FIArea4.S15red.SSE.ssFac e (d / e) a‖ ^ 2 ≤ 1 := by
        nlinarith [norm_nonneg (Work.FIArea4.S15red.SSE.ssFac e (d / e) a)]
      rw [norm_mul, norm_pow]
      calc ‖Work.FIArea4.S15red.SSE.ssConst X j d t‖
            * ‖Work.FIArea4.S15red.SSE.ssFac e (d / e) a‖ ^ 2
          ≤ 1 * 1 := mul_le_mul h1 h3 (by positivity) (by norm_num)
        _ = 1 := by ring
    have hCS : ‖T‖ ≤ Real.sqrt (Work.FIArea4.S15red.StrCS.csEvG (Work.FITop.radN Pa)
          (4 * (d / e)) (Work.FIArea4.S15red.SSE.ssU Pa e (d / e) β u t ℓ))
        * Real.sqrt (Work.FIArea4.S15red.StrCS.csEvG (Work.FITop.radN Pa) (4 * (d / e))
          (Work.FIArea4.S15red.SSE.ssV Pa e (d / e) β u t ℓ)) := by
      rw [hTdef]
      exact Work.FIArea4.S15red.StrCS.csPairSum_le (Work.FITop.radN Pa) (4 * (d / e)) hm1
        (Work.FIArea4.S15red.SSE.ssU Pa e (d / e) β u t ℓ)
        (Work.FIArea4.S15red.SSE.ssV Pa e (d / e) β u t ℓ)
        (fun c => Work.FIArea4.S15red.SSE.ssConst X j d t
          * (Work.FIArea4.S15red.SSE.ssFac e (d / e) c) ^ 2) hF hu hv
    have hEvU : Work.FIArea4.S15red.StrCS.csEvG (Work.FITop.radN Pa) (4 * (d / e))
          (Work.FIArea4.S15red.SSE.ssU Pa e (d / e) β u t ℓ)
        = Work.FIArea4.EvarG (Work.FITop.radN Pa) (4 * (d / e))
            (Work.FIArea4.S15strU β u t ℓ e) := by
      rw [Work.FIArea4.S15red.SSE.csEvG_congr (R := Work.FITop.radN Pa) (m := 4 * (d / e))
        (u := Work.FIArea4.S15red.SSE.ssU Pa e (d / e) β u t ℓ)
        (u' := fun z => Work.FIArea4.S15strU β u t ℓ e z
          * Work.FIArea4.jwG (4 * (d / e)) z.re)
        (fun z hz => by rw [Work.FIArea4.S15red.SSE.ssU, if_pos hz])]
      exact (Work.FIArea4.S15red.StrCS.EvarG_eq_csEvG (Work.FITop.radN Pa) (4 * (d / e))
        (Work.FIArea4.S15strU β u t ℓ e)).symm
    have hEvV : Work.FIArea4.S15red.StrCS.csEvG (Work.FITop.radN Pa) (4 * (d / e))
          (Work.FIArea4.S15red.SSE.ssV Pa e (d / e) β u t ℓ)
        = Work.FIArea4.EvarG (Work.FITop.radN Pa) (4 * (d / e))
            (Work.FIArea4.S15strV β u t ℓ e) := by
      rw [Work.FIArea4.S15red.SSE.csEvG_congr (R := Work.FITop.radN Pa) (m := 4 * (d / e))
        (u := Work.FIArea4.S15red.SSE.ssV Pa e (d / e) β u t ℓ)
        (u' := fun z => Work.FIArea4.S15strV β u t ℓ e z
          * Work.FIArea4.jwG (4 * (d / e)) z.re)
        (fun z hz => by rw [Work.FIArea4.S15red.SSE.ssV, if_pos hz])]
      exact (Work.FIArea4.S15red.StrCS.EvarG_eq_csEvG (Work.FITop.radN Pa) (4 * (d / e))
        (Work.FIArea4.S15strV β u t ℓ e)).symm
    rw [hSU, hST, norm_mul, show ‖(2 : ℂ)‖ = 2 by norm_num]
    refine le_trans (mul_le_mul_of_nonneg_left hCS (by norm_num)) ?_
    rw [hEvU, hEvV]
  · have hzero : stratumSumE6 Pa X j d β ℓ u t e = 0 := by
      unfold stratumSumE6
      refine Finset.sum_eq_zero (fun z1 _ => Finset.sum_eq_zero (fun z2 _ => ?_))
      rw [if_neg]
      rintro ⟨-, hXd, -⟩
      exact absurd hXd hX
    rw [hzero, norm_zero]
    positivity

/-- **The per-modulus round-6 §15 bound** (the target `pDng6_le_EvarG`). -/
theorem pDng6_le_EvarG (Pa : Work.FITop.Params) (X j d : ℕ) (φ : ℝ) (β : GaussianInt → ℂ)
    (ℓ : ℤ) (u t : ℝ) (hβ : Work.FIArea4.IsPrimBoxCoeff Pa φ β) (hd : 1 ≤ d) :
    ‖Work.FIArea4.A6psi.S15pDng6 Pa X j d β ℓ u t‖
      ≤ 2 * (∑ e ∈ d.divisors,
          Real.sqrt (Work.FIArea4.EvarG (Work.FITop.radN Pa) (4 * (d / e))
              (Work.FIArea4.S15strU β u t ℓ e))
          * Real.sqrt (Work.FIArea4.EvarG (Work.FITop.radN Pa) (4 * (d / e))
              (Work.FIArea4.S15strV β u t ℓ e)))
        + 2 * ∑ z ∈ Work.FITop.boxN Pa, ‖β z‖ ^ 2 := by
  have hsum : ‖∑ e ∈ d.divisors, stratumSumE6 Pa X j d β ℓ u t e‖
      ≤ ∑ e ∈ d.divisors, 2 * (Real.sqrt (Work.FIArea4.EvarG (Work.FITop.radN Pa)
            (4 * (d / e)) (Work.FIArea4.S15strU β u t ℓ e))
          * Real.sqrt (Work.FIArea4.EvarG (Work.FITop.radN Pa) (4 * (d / e))
            (Work.FIArea4.S15strV β u t ℓ e))) :=
    le_trans (norm_sum_le _ _)
      (Finset.sum_le_sum (fun e he => stratumSumE6_le_EvarG Pa X j d e φ β ℓ u t hβ hd he))
  calc ‖Work.FIArea4.A6psi.S15pDng6 Pa X j d β ℓ u t‖
      = ‖(∑ e ∈ d.divisors, stratumSumE6 Pa X j d β ℓ u t e)
          - diagSum6 Pa X j d β ℓ u t‖ := by
        rw [S15pDng6_eq_sum_stratumE_sub_diag6 Pa X j d β ℓ u t hd]
    _ ≤ ‖∑ e ∈ d.divisors, stratumSumE6 Pa X j d β ℓ u t e‖
          + ‖diagSum6 Pa X j d β ℓ u t‖ := norm_sub_le _ _
    _ ≤ (∑ e ∈ d.divisors, 2 * (Real.sqrt (Work.FIArea4.EvarG (Work.FITop.radN Pa)
            (4 * (d / e)) (Work.FIArea4.S15strU β u t ℓ e))
          * Real.sqrt (Work.FIArea4.EvarG (Work.FITop.radN Pa) (4 * (d / e))
            (Work.FIArea4.S15strV β u t ℓ e))))
        + 2 * ∑ z ∈ Work.FITop.boxN Pa, ‖β z‖ ^ 2 :=
        add_le_add hsum (Diag6.diagSum6_le Pa X j d φ β ℓ u t hβ)
    _ = 2 * (∑ e ∈ d.divisors,
          Real.sqrt (Work.FIArea4.EvarG (Work.FITop.radN Pa) (4 * (d / e))
              (Work.FIArea4.S15strU β u t ℓ e))
          * Real.sqrt (Work.FIArea4.EvarG (Work.FITop.radN Pa) (4 * (d / e))
              (Work.FIArea4.S15strV β u t ℓ e)))
        + 2 * ∑ z ∈ Work.FITop.boxN Pa, ‖β z‖ ^ 2 := by
        simp only [Finset.mul_sum]

end Work.FIArea4.A6psi
