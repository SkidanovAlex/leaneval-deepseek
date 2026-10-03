import Mathlib
import Submission.Work.FIArea6Hecke.R.heckeStripLogDerivConductor
import Submission.Work.FIFinal.CL.FIArea6Hecke.R.heckeZFRrealAxisClean
import Submission.Work.FIArea6Hecke.R.heckeCompletionImprimitive
import Submission.Work.FIArea6Hecke.R.m_eq_zero_of_selfDual
import Submission.Work.FIArea6Hecke.R.noCompletion_of_primaryTrivial
import Submission.Work.FIArea6Hecke.R.exists_realCharacter_agreeing_on_primary

set_option autoImplicit false
set_option maxHeartbeats 1600000

namespace Work.FIArea6Hecke.R

open scoped BigOperators
open Work.FIPlan

noncomputable section

/-! ## 0. Elementary facts about the units modulo `4d`

`IsUnitMod4d d z` means `z` is invertible modulo `4d` in `ℤ[i]`.  Such elements are odd
(`¬ (1+i) ∣ z`), nonzero, and the property is invariant under multiplication by a unit of `ℤ[i]`
(in particular under passage to the primary associate `Work.FIArea4.primAssoc`). -/

lemma zrs_unitMod4d_odd {d : ℕ} {z : GaussianInt}
    (hz : Work.FIArea5.S16Hecke.IsUnitMod4d d z) : Odd (gnorm z) :=
  Work.FIArea5.S16Hecke.isOddG_gnorm_odd z
    (fun h => Work.FIArea5.S16Hecke.not_isUnitMod4d_of_oneAddI_dvd h hz)

lemma zrs_unitMod4d_ne_zero {d : ℕ} {z : GaussianInt}
    (hz : Work.FIArea5.S16Hecke.IsUnitMod4d d z) : z ≠ 0 :=
  ne_zero_of_odd_gnorm (zrs_unitMod4d_odd hz)

lemma zrs_isUnitMod4d_mul_unit {d : ℕ} {z : GaussianInt}
    (hz : Work.FIArea5.S16Hecke.IsUnitMod4d d z) (u : GaussianIntˣ) :
    Work.FIArea5.S16Hecke.IsUnitMod4d d ((u : GaussianInt) * z) := by
  obtain ⟨w, hw⟩ := hz
  refine ⟨((u⁻¹ : GaussianIntˣ) : GaussianInt) * w, ?_⟩
  have h : (u : GaussianInt) * z * (((u⁻¹ : GaussianIntˣ) : GaussianInt) * w) = z * w := by
    rw [show (u : GaussianInt) * z * (((u⁻¹ : GaussianIntˣ) : GaussianInt) * w)
          = ((u : GaussianInt) * ((u⁻¹ : GaussianIntˣ) : GaussianInt)) * (z * w) by ring,
      ← Units.val_mul, mul_inv_cancel u, Units.val_one, one_mul]
  rw [h]; exact hw

lemma zrs_isUnitMod4d_primAssoc {d : ℕ} {z : GaussianInt}
    (hz : Work.FIArea5.S16Hecke.IsUnitMod4d d z) :
    Work.FIArea5.S16Hecke.IsUnitMod4d d (Work.FIArea4.primAssoc z) := by
  obtain ⟨u, hu⟩ := Work.FIArea4.primAssoc_associated (z := z)
    (zrs_unitMod4d_ne_zero hz) (zrs_unitMod4d_odd hz)
  obtain ⟨w, hw⟩ := hz
  refine ⟨(u : GaussianInt) * w, ?_⟩
  have h : Work.FIArea4.primAssoc z * ((u : GaussianInt) * w) = z * w := by
    rw [← mul_assoc, hu]
  rw [h]; exact hw

/-! ## 1. The transfer character

For an odd `z` the primary associate `Work.FIArea4.primAssoc z` is the unique primary element
associated to `z`.  We define the *transfer* of `chi` by evaluating `chi` at the primary associate
of a unit modulo `4d` (and `0` off the units). -/

/-- The transfer `χ'(z) = χ(primAssoc z)` for `z` a unit modulo `4d`, and `χ'(z) = 0` otherwise. -/
def zrsPrimChar (d : ℕ) (chi : GaussianInt → ℂ) (z : GaussianInt) : ℂ := by
  classical
  exact if _ : Work.FIArea5.S16Hecke.IsUnitMod4d d z then chi (Work.FIArea4.primAssoc z) else 0

lemma zrsPrimChar_of_unit {d : ℕ} {chi : GaussianInt → ℂ} {z : GaussianInt}
    (h : Work.FIArea5.S16Hecke.IsUnitMod4d d z) :
    zrsPrimChar d chi z = chi (Work.FIArea4.primAssoc z) := by
  rw [zrsPrimChar]
  exact dif_pos h

lemma zrsPrimChar_of_not_unit {d : ℕ} {chi : GaussianInt → ℂ} {z : GaussianInt}
    (h : ¬ Work.FIArea5.S16Hecke.IsUnitMod4d d z) : zrsPrimChar d chi z = 0 := by
  rw [zrsPrimChar]
  exact dif_neg h

/-! ### 1.1 Parity: a multiple of `4d` has real and imaginary parts divisible by `4` -/

lemma zrs_four_dvd_re_im {d : ℕ} {x : GaussianInt}
    (h : Work.FIArea6Hecke.fourDZFR d ∣ x) : (4 : ℤ) ∣ x.re ∧ (4 : ℤ) ∣ x.im := by
  obtain ⟨hre, him⟩ := (Zsqrtd.intCast_dvd (((4 * d : ℕ) : ℤ)) x).mp h
  have h4 : (4 : ℤ) ∣ (((4 * d : ℕ) : ℤ)) := ⟨(d : ℤ), by push_cast; ring⟩
  exact ⟨dvd_trans h4 hre, dvd_trans h4 him⟩

/-- An odd integer is not divisible by `4`. -/
lemma zrs_not_four_dvd_odd {n : ℤ} (h : Odd n) : ¬ (4 : ℤ) ∣ n := by
  obtain ⟨k, hk⟩ := h
  rintro ⟨m, hm⟩
  omega

lemma zrs_re_sub_mul_I (A B : GaussianInt) :
    (A - B * (⟨0, 1⟩ : GaussianInt)).re = A.re + B.im := by
  rw [Zsqrtd.re_sub, Zsqrtd.re_mul]
  simp

lemma zrs_re_sub_mul_negI (A B : GaussianInt) :
    (A - B * (⟨0, -1⟩ : GaussianInt)).re = A.re - B.im := by
  rw [Zsqrtd.re_sub, Zsqrtd.re_mul]
  simp

/-! ### 1.2 Multiplicativity, bound, periodicity, reality and agreement -/

lemma zrsPrimChar_mul {d : ℕ} {chi : GaussianInt → ℂ}
    (hmul : ∀ z w : GaussianInt, chi (z * w) = chi z * chi w) :
    ∀ z w : GaussianInt, zrsPrimChar d chi (z * w)
      = zrsPrimChar d chi z * zrsPrimChar d chi w := by
  intro z w
  by_cases hz : Work.FIArea5.S16Hecke.IsUnitMod4d d z
  · by_cases hw : Work.FIArea5.S16Hecke.IsUnitMod4d d w
    · rw [zrsPrimChar_of_unit (Work.FIArea6Hecke.isUnitMod4d_mul_iff.mpr ⟨hz, hw⟩),
        zrsPrimChar_of_unit hz, zrsPrimChar_of_unit hw,
        primAssoc_mul_odd (zrs_unitMod4d_odd hz) (zrs_unitMod4d_odd hw), hmul]
    · rw [zrsPrimChar_of_not_unit (fun h => hw (Work.FIArea6Hecke.isUnitMod4d_mul_iff.mp h).2),
        zrsPrimChar_of_unit hz, zrsPrimChar_of_not_unit hw, mul_zero]
  · rw [zrsPrimChar_of_not_unit (fun h => hz (Work.FIArea6Hecke.isUnitMod4d_mul_iff.mp h).1),
      zrsPrimChar_of_not_unit hz, zero_mul]

lemma zrsPrimChar_norm_le_one {d : ℕ} {chi : GaussianInt → ℂ}
    (hb : ∀ z : GaussianInt, ‖chi z‖ ≤ 1) (z : GaussianInt) :
    ‖zrsPrimChar d chi z‖ ≤ 1 := by
  by_cases hz : Work.FIArea5.S16Hecke.IsUnitMod4d d z
  · rw [zrsPrimChar_of_unit hz]; exact hb _
  · rw [zrsPrimChar_of_not_unit hz]; simp

lemma zrsPrimChar_periodic {d : ℕ} (hd : 1 ≤ d) {chi : GaussianInt → ℂ}
    (hchi : Work.FIArea5.S16Hecke.IsCharMod4dStrict d chi) :
    ∀ z w : GaussianInt, Work.FIArea6Hecke.fourDZFR d ∣ (z - w) →
      zrsPrimChar d chi z = zrsPrimChar d chi w := by
  intro z w hzw
  by_cases hz : Work.FIArea5.S16Hecke.IsUnitMod4d d z
  · have hw : Work.FIArea5.S16Hecke.IsUnitMod4d d w :=
      (Work.FIArea6Hecke.isUnitMod4d_congr' hzw).mp hz
    rw [zrsPrimChar_of_unit hz, zrsPrimChar_of_unit hw]
    have hzodd := zrs_unitMod4d_odd hz
    have hwodd := zrs_unitMod4d_odd hw
    obtain ⟨u, hu⟩ := Work.FIArea4.primAssoc_associated (z := z)
      (zrs_unitMod4d_ne_zero hz) hzodd
    obtain ⟨v, hv⟩ := Work.FIArea4.primAssoc_associated (z := w)
      (zrs_unitMod4d_ne_zero hw) hwodd
    set A := Work.FIArea4.primAssoc z with hA
    set B := Work.FIArea4.primAssoc w with hB
    have hAp : IsPrimary A :=
      Work.FIArea4.primAssoc_primary (zrs_unitMod4d_ne_zero hz) hzodd
    have hBp : IsPrimary B :=
      Work.FIArea4.primAssoc_primary (zrs_unitMod4d_ne_zero hw) hwodd
    have hu1 : ((u⁻¹ : GaussianIntˣ) : GaussianInt) * (u : GaussianInt) = 1 := by
      rw [← Units.val_mul, inv_mul_cancel, Units.val_one]
    have hdiv : Work.FIArea6Hecke.fourDZFR d ∣
        A - B * ((v * u⁻¹ : GaussianIntˣ) : GaussianInt) := by
      have h1 : Work.FIArea6Hecke.fourDZFR d ∣
          ((u⁻¹ : GaussianIntˣ) : GaussianInt) * (z - w) := dvd_mul_of_dvd_right hzw _
      have heq : ((u⁻¹ : GaussianIntˣ) : GaussianInt) * (z - w)
          = A - B * ((v * u⁻¹ : GaussianIntˣ) : GaussianInt) := by
        rw [← hu, ← hv, Units.val_mul]
        rw [show ((u⁻¹ : GaussianIntˣ) : GaussianInt)
              * (A * (u : GaussianInt) - B * (v : GaussianInt))
            = (((u⁻¹ : GaussianIntˣ) : GaussianInt) * (u : GaussianInt)) * A
              - B * ((v : GaussianInt) * ((u⁻¹ : GaussianIntˣ) : GaussianInt)) by ring]
        rw [hu1, one_mul]
      rwa [heq] at h1
    have hcases := (Commons.NumberTheory.GaussianInt.units_classification
      ((v * u⁻¹ : GaussianIntˣ) : GaussianInt)).mp (v * u⁻¹).isUnit
    rcases hcases with hT | hT | hT | hT
    · -- `T = 1`: `A ≡ B (4d)`, so `chi A = chi B` by periodicity of `chi`
      have hAB : Work.FIArea6Hecke.fourDZFR d ∣ (A - B) := by
        rw [hT] at hdiv; simpa using hdiv
      exact hchi.1.2.2.2.1 A B hAB
    · -- `T = -1`: `A ≡ -B (4d)` is impossible for primary `A, B`
      exfalso
      have hAB : Work.FIArea6Hecke.fourDZFR d ∣ (A + B) := by
        rw [hT] at hdiv; convert hdiv using 1; ring
      obtain ⟨hre4, him4⟩ := zrs_four_dvd_re_im hAB
      have hre : (A.re + B.re) ≡ 0 [ZMOD 4] := by
        have := hre4
        rw [Zsqrtd.re_add] at this
        exact Int.modEq_zero_iff_dvd.mpr this
      have him : (A.im + B.im) ≡ 0 [ZMOD 4] := by
        have := him4
        rw [Zsqrtd.im_add] at this
        exact Int.modEq_zero_iff_dvd.mpr this
      have hkey : (A.im + B.im) ≡ A.re + B.re - 2 [ZMOD 4] := by
        have h := (hAp.2.2).add hBp.2.2
        convert h using 1 <;> ring
      have hbad : (0 : ℤ) ≡ -2 [ZMOD 4] := by
        calc (0 : ℤ) ≡ A.im + B.im [ZMOD 4] := him.symm
          _ ≡ A.re + B.re - 2 [ZMOD 4] := hkey
          _ ≡ 0 - 2 [ZMOD 4] := hre.sub (Int.ModEq.refl 2)
          _ = -2 := by ring
      have hdvd : (4 : ℤ) ∣ 2 := by
        have h4 : (4 : ℤ) ∣ -2 := Int.modEq_zero_iff_dvd.mp hbad.symm
        exact dvd_neg.mp h4
      exact absurd hdvd (by norm_num)
    · -- `T = i`: `(A - iB).re` is odd but divisible by `4`
      exfalso
      have hre : (4 : ℤ) ∣ (A - B * (⟨0, 1⟩ : GaussianInt)).re := by
        have h := (zrs_four_dvd_re_im hdiv).1
        rwa [hT] at h
      have hodd : Odd (A - B * (⟨0, 1⟩ : GaussianInt)).re := by
        rw [zrs_re_sub_mul_I]
        obtain ⟨k, hk⟩ := hAp.1
        obtain ⟨l, hl⟩ := hBp.2.1
        exact ⟨k + l, by omega⟩
      exact absurd hre (zrs_not_four_dvd_odd hodd)
    · -- `T = -i`: `(A + iB).re` is odd but divisible by `4`
      exfalso
      have hre : (4 : ℤ) ∣ (A - B * (⟨0, -1⟩ : GaussianInt)).re := by
        have h := (zrs_four_dvd_re_im hdiv).1
        rwa [hT] at h
      have hodd : Odd (A - B * (⟨0, -1⟩ : GaussianInt)).re := by
        rw [zrs_re_sub_mul_negI]
        obtain ⟨k, hk⟩ := hAp.1
        obtain ⟨l, hl⟩ := hBp.2.1
        refine ⟨k - l, ?_⟩
        omega
      exact absurd hre (zrs_not_four_dvd_odd hodd)
  · have hw : ¬ Work.FIArea5.S16Hecke.IsUnitMod4d d w :=
      fun h => hz ((Work.FIArea6Hecke.isUnitMod4d_congr' hzw).mpr h)
    rw [zrsPrimChar_of_not_unit hz, zrsPrimChar_of_not_unit hw]

lemma zrsPrimChar_real {d : ℕ} {chi : GaussianInt → ℂ}
    (hsd : Work.FIArea6Hecke.R.SelfDual d chi 0) :
    ∀ z : GaussianInt, star (zrsPrimChar d chi z) = zrsPrimChar d chi z := by
  intro z
  by_cases hz : Work.FIArea5.S16Hecke.IsUnitMod4d d z
  · rw [zrsPrimChar_of_unit hz]
    have hzodd := zrs_unitMod4d_odd hz
    have hAp : IsPrimary (Work.FIArea4.primAssoc z) :=
      Work.FIArea4.primAssoc_primary (zrs_unitMod4d_ne_zero hz) hzodd
    have hAu := zrs_isUnitMod4d_primAssoc hz
    have hsq := hsd (Work.FIArea4.primAssoc z) hAp hAu
    have hpsi : Work.FIArea5.S16Hecke.psi chi 0 (Work.FIArea4.primAssoc z)
        = chi (Work.FIArea4.primAssoc z) := by
      simp [Work.FIArea5.S16Hecke.psi]
    rw [hpsi] at hsq
    rcases sq_eq_one_iff.mp hsq with h | h <;> rw [h] <;> simp
  · rw [zrsPrimChar_of_not_unit hz]; simp

lemma zrsPrimChar_agree {d : ℕ} {chi : GaussianInt → ℂ}
    (hchi : Work.FIArea5.S16Hecke.IsCharMod4dStrict d chi) :
    ∀ z : GaussianInt, IsPrimary z → zrsPrimChar d chi z = chi z := by
  intro z hz
  by_cases hu : Work.FIArea5.S16Hecke.IsUnitMod4d d z
  · rw [zrsPrimChar_of_unit hu, Work.FIArea4.primAssoc_eq_self hz]
  · rw [zrsPrimChar_of_not_unit hu, hchi.2 z hu]

lemma zrsPrimChar_heckeLSeries {d : ℕ} {chi : GaussianInt → ℂ}
    (hchi : Work.FIArea5.S16Hecke.IsCharMod4dStrict d chi) :
    Work.FIArea5.S16Hecke.heckeLSeries (zrsPrimChar d chi) 0
      = Work.FIArea5.S16Hecke.heckeLSeries chi 0 :=
  (Work.FIArea6Hecke.R.heckeLSeries_eq_of_primary_agree (k := 0)
    (fun z hz => (zrsPrimChar_agree hchi z hz).symm)).symm

/-! ## 2. The transfer theorem

A self-dual strict character pair `(chi, m)` is equivalent to a *real* strict character `chi'` with
the same Hecke eigenvalues. -/

theorem zfrRealAxisSd_transfer {d : ℕ} {chi : GaussianInt → ℂ} {m : ℤ}
    (hd : 1 ≤ d) (hchi : Work.FIArea5.S16Hecke.IsCharMod4dStrict d chi)
    (hsd : Work.FIArea6Hecke.R.SelfDual d chi m) :
    ∃ chi' : GaussianInt → ℂ,
      Work.FIArea5.S16Hecke.IsCharMod4dStrict d chi' ∧
      (∀ z : GaussianInt, star (chi' z) = chi' z) ∧
      (∀ z : GaussianInt, IsPrimary z → chi' z = chi z) ∧
      Work.FIArea5.S16Hecke.heckeLSeries chi' 0 = Work.FIArea5.S16Hecke.heckeLSeries chi m := by
  classical
  have hm : m = 0 := Work.FIArea6Hecke.R.m_eq_zero_of_selfDual hd hchi hsd
  subst hm
  refine ⟨zrsPrimChar d chi, ⟨⟨?_, ?_, ?_, ?_, ?_⟩, ?_⟩, ?_, ?_, ?_⟩
  · rw [zrsPrimChar_of_unit (Work.FIArea6Hecke.isUnitMod4d_one d),
      Work.FIArea4.primAssoc_eq_self Work.FIArea5.S16Hecke.isPrimary_one]
    exact hchi.1.1
  · exact zrsPrimChar_mul hchi.1.2.1
  · exact zrsPrimChar_norm_le_one hchi.1.2.2.1
  · exact zrsPrimChar_periodic hd hchi
  · intro z hz
    exact zrsPrimChar_of_not_unit (Work.FIArea6Hecke.not_isUnitMod4d_of_dvd hd hz)
  · intro z hz
    exact zrsPrimChar_of_not_unit hz
  · exact zrsPrimChar_real hsd
  · exact zrsPrimChar_agree hchi
  · exact zrsPrimChar_heckeLSeries hchi

/-- **Lemma 16.1 (Landau--Siegel) on the real axis, for self-dual pairs** (*FI* (16.21)): the
statement `Work.FIArea6Hecke.R.ZFRrealAxisSd ε` of `R/heckeStripLogDerivConductor` — the standard
`ZFRStatementDefs.ZFRrealAxis ε` with `PsiReal` replaced by the (correct, weaker) self-duality
condition `SelfDual` (real Hecke eigenvalues).

Reduce to the already proved `heckeZFRrealAxisClean ε hε hε4` (which covers the `PsiReal` case):
given a self-dual admissible datum `(d, chi, m, Lam)` on the real axis, use
`Work.FIArea6Hecke.R.zfrRealAxisSd_transfer hd hchi hsd` to obtain a real-valued strict
`chi'` with `heckeLSeries chi' 0 = heckeLSeries chi m` (the same Hecke eigenvalues); produce an
entire completion `Lam'` of `(d, chi', 0)` (`heckeCompletionImprimitive`), apply
`heckeZFRrealAxisClean ε hε hε4` to it, and transport the conclusion back: on the half-plane where
both are given, `Lam` and `Lam'` agree with `heckeArch d m · L(chi,m)` resp.
`heckeArch d 0 · L(chi',0)`, and the two `L`-series coincide, so
`Lval d m Lam s = 0 ↔ Lval d 0 Lam' s = 0`.  The non-triviality hypothesis `hne` needed by
`heckeCompletionImprimitive` is forced: a pole of `L(chi',0)` at `s = 1` would make `Lam'`
non-entire, while `Lam = heckeArch d m · L(chi,m)` is entire by hypothesis. -/
theorem zfrRealAxisSd (ε : ℝ) (hε : 0 < ε) (hε4 : ε ≤ 1 / 4) :
    Work.FIArea6Hecke.R.ZFRrealAxisSd ε := by
  obtain ⟨c, hc, hclean⟩ := heckeZFRrealAxisClean ε hε hε4
  refine ⟨c, hc, ?_⟩
  intro d chi m Lam hd hchi hAn hagr hsd s hsim hs1 hs2
  have hm : m = 0 := m_eq_zero_of_selfDual hd hchi hsd
  subst hm
  obtain ⟨chi', hchi', hreal', hagree, hLser⟩ := zfrRealAxisSd_transfer hd hchi hsd
  have hne : ∃ z : GaussianInt, IsPrimary z ∧
      Work.FIArea5.S16Hecke.IsUnitMod4d d z ∧ Work.FIArea5.S16Hecke.psi chi' 0 z ≠ 1 := by
    by_contra hcon
    push_neg at hcon
    refine (noCompletion_of_primaryTrivial d chi 0 hd hchi ?_) ⟨Lam, hAn, ?_⟩
    · intro z hz hu
      have h2 : chi' z = 1 := by
        have h := hcon z hz hu
        simpa [Work.FIArea5.S16Hecke.psi] using h
      calc Work.FIArea5.S16Hecke.psi chi 0 z = chi z := by
            simp [Work.FIArea5.S16Hecke.psi]
        _ = chi' z := (hagree z hz).symm
        _ = 1 := h2
    · intro t ht
      exact hagr t (by simpa using ht)
  obtain ⟨Lam', hAn', hagr'⟩ := heckeCompletionImprimitive d chi' 0 hd hchi' hne
  have hEq : Lam = Lam' :=
    Work.FIArea6Hecke.eq_of_agrees_right Lam' Lam hAn' hAn (fun t ht => by
      rw [hagr t (by simpa using ht), hagr' t (by simpa using ht), congrFun hLser t])
  have hfin : Work.FIArea6Hecke.Lval d 0 Lam' s ≠ 0 :=
    hclean d chi' 0 Lam' hd hchi' hAn' hagr'
      (Work.FIArea6Hecke.R.psiReal_zero_iff.mpr hreal') s hsim hs1 hs2
  rw [← hEq] at hfin
  exact hfin

end

end Work.FIArea6Hecke.R
