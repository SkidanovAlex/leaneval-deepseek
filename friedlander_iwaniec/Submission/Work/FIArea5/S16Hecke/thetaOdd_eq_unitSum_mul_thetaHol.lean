import Mathlib
import Submission.Work.FIArea5.S16Hecke.Defs
import Submission.Work.FIArea5.S16Hecke.ThetaDefs
import Submission.Work.FIArea5.S16Hecke.primaryAux
import Submission.Commons.NumberTheory.GaussianInt.primary_associate_exists_unique
import Submission.Commons.NumberTheory.GaussianInt.units_classification

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false

set_option autoImplicit false

namespace Work.FIArea5.S16Hecke

open Finset
open scoped BigOperators
open Work.FIPlan

attribute [local instance] Classical.propDecidable

noncomputable section

/-! ## The summands of `thetaOdd` and `thetaHol`, and the per-unit pieces -/

/-- The summand of `thetaOdd`: `χ(z) z^m e^{-πu|z|²}` on odd `z`, `0` otherwise. -/
private def TF (chi : GaussianInt → ℂ) (m : ℕ) (u : ℝ) (z : GaussianInt) : ℂ := by
  classical
  exact if isOddG z then
    chi z * (z.toComplex) ^ m * Complex.exp (-Real.pi * u * (gnorm z : ℝ)) else 0

/-- The summand of `thetaHol`: `χ(z) z^m e^{-πu|z|²}` on primary `z`, `0` otherwise. -/
private def TH (chi : GaussianInt → ℂ) (m : ℕ) (u : ℝ) (z : GaussianInt) : ℂ := by
  classical
  exact if IsPrimary z then
    chi z * (z.toComplex) ^ m * Complex.exp (-Real.pi * u * (gnorm z : ℝ)) else 0

/-- The contribution of the unit `a` to `thetaOdd`: the summand restricted to the `a`-translate
of the primary coset. -/
private def TU (chi : GaussianInt → ℂ) (m : ℕ) (u : ℝ) (a z : GaussianInt) : ℂ := by
  classical
  exact if (∃ p : GaussianInt, IsPrimary p ∧ z = a * p) then TF chi m u z else 0

/-- `thetaOdd` is the sum of `TF`. -/
private lemma thetaOdd_eq_tsum_TF (chi : GaussianInt → ℂ) (m : ℕ) (u : ℝ) :
    thetaOdd chi m u = ∑' z : GaussianInt, TF chi m u z := rfl

/-- `thetaHol` is the sum of `TH`. -/
private lemma thetaHol_eq_tsum_TH (chi : GaussianInt → ℂ) (m : ℕ) (u : ℝ) :
    thetaHol chi m u = ∑' z : GaussianInt, TH chi m u z := rfl

/-- If `χ` is multiplicative and `χ 1 = 0` then `χ` vanishes identically. -/
private lemma chi_eq_zero_of_chi_one_eq_zero (chi : GaussianInt → ℂ)
    (hmul : ∀ z w : GaussianInt, chi (z * w) = chi z * chi w) (h1 : chi 1 = 0) (z : GaussianInt) :
    chi z = 0 := by
  have h : chi (z * 1) = chi z * chi 1 := hmul z 1
  rw [mul_one, h1, mul_zero] at h
  exact h

/-! ## `1+i` divides `z` iff `|z|²` is even -/

private lemma gnorm_int_eq (z : GaussianInt) : ((gnorm z : ℕ) : ℤ) = z.re ^ 2 + z.im ^ 2 := by
  rw [gnorm, Int.natAbs_of_nonneg (Zsqrtd.norm_nonneg (by norm_num : (-1 : ℤ) ≤ 0) z),
    Zsqrtd.norm_def]
  ring

private lemma gnorm_oneAddI : gnorm oneAddI = 2 := by
  rw [gnorm, oneAddI]
  decide

private lemma oneAddI_mul_coords (a b : ℤ) :
    oneAddI * (⟨a, b⟩ : GaussianInt) = ⟨a - b, a + b⟩ := by
  ext <;> simp [oneAddI, Zsqrtd.re_mul, Zsqrtd.im_mul] <;> ring

private lemma even_gnorm_of_oneAddI_dvd {z : GaussianInt} (h : oneAddI ∣ z) : Even (gnorm z) := by
  obtain ⟨w, rfl⟩ := h
  rw [gnorm_mul, gnorm_oneAddI]
  exact even_two.mul_right (gnorm w)

private lemma oneAddI_dvd_of_even_gnorm {z : GaussianInt} (h : Even (gnorm z)) : oneAddI ∣ z := by
  have hz : Even ((gnorm z : ℕ) : ℤ) := by
    obtain ⟨k, hk⟩ := h
    exact ⟨(k : ℤ), by rw [hk]; push_cast; ring⟩
  rw [gnorm_int_eq z] at hz
  have hsq_re : Even (z.re ^ 2) ↔ Even z.re := by rw [pow_two, Int.even_mul]; tauto
  have hsq_im : Even (z.im ^ 2) ↔ Even z.im := by rw [pow_two, Int.even_mul]; tauto
  have hpar : Even z.re ↔ Even z.im := by
    have h3 := Int.even_add.mp hz
    rwa [hsq_re, hsq_im] at h3
  have h2 : Even (z.re + z.im) := Int.even_add.mpr hpar
  have hl : Even (z.im - z.re) := by
    have h4 : Even ((z.re + z.im) - 2 * z.re) := Even.sub h2 (even_two.mul_right z.re)
    have h5 : (z.re + z.im) - 2 * z.re = z.im - z.re := by ring
    rwa [h5] at h4
  obtain ⟨k, hk⟩ := h2
  obtain ⟨l, hl⟩ := hl
  refine ⟨⟨k, l⟩, ?_⟩
  rw [oneAddI_mul_coords]
  ext
  · show z.re = k - l
    omega
  · show z.im = k + l
    omega

private lemma oneAddI_dvd_iff (z : GaussianInt) : oneAddI ∣ z ↔ Even (gnorm z) :=
  ⟨even_gnorm_of_oneAddI_dvd, oneAddI_dvd_of_even_gnorm⟩

private lemma isOddG_iff (z : GaussianInt) : isOddG z ↔ Odd (gnorm z) := by
  rw [isOddG, oneAddI_dvd_iff, Nat.not_even_iff_odd]

private lemma isPrimary_isOddG {z : GaussianInt} (hz : IsPrimary z) : isOddG z :=
  (isOddG_iff z).mpr (isPrimary_odd_gnorm hz)

/-! ## The units `{1, -1, i, -i}` -/

private lemma mem_units4_iff {u : GaussianInt} :
    u ∈ units4 ↔ u = 1 ∨ u = -1 ∨ u = (⟨0, 1⟩ : GaussianInt) ∨ u = (⟨0, -1⟩ : GaussianInt) := by
  simp [units4]

private lemma gnorm_of_mem_units4 {u : GaussianInt} (hu : u ∈ units4) : gnorm u = 1 := by
  rw [mem_units4_iff] at hu
  rcases hu with h | h | h | h <;> (rw [h]; decide)

private lemma isUnit_of_mem_units4 {u : GaussianInt} (hu : u ∈ units4) : IsUnit u :=
  (Commons.NumberTheory.GaussianInt.units_classification u).mpr (by
    rw [mem_units4_iff] at hu
    rcases hu with h | h | h | h
    · exact Or.inl h
    · exact Or.inr (Or.inl h)
    · exact Or.inr (Or.inr (Or.inl h))
    · exact Or.inr (Or.inr (Or.inr h)))

private lemma exists_inv_of_mem_units4 {u : GaussianInt} (hu : u ∈ units4) :
    ∃ v : GaussianInt, v * u = 1 ∧ u * v = 1 := by
  obtain ⟨v, hv⟩ := isUnit_iff_exists_inv'.mp (isUnit_of_mem_units4 hu)
  exact ⟨v, hv, by rw [mul_comm]; exact hv⟩

private lemma isOddG_mul_iff {a : GaussianInt} (ha : a ∈ units4) (z : GaussianInt) :
    isOddG (a * z) ↔ isOddG z := by
  rw [isOddG_iff, isOddG_iff, gnorm_mul, gnorm_of_mem_units4 ha, one_mul]

/-- Multiplication by a unit, as an equivalence of `ℤ[i]`. -/
private def mulUnitEquiv (a b : GaussianInt) (hab : a * b = 1) (hba : b * a = 1) :
    GaussianInt ≃ GaussianInt where
  toFun z := a * z
  invFun z := b * z
  left_inv z := by show b * (a * z) = z; rw [← mul_assoc, hba, one_mul]
  right_inv z := by show a * (b * z) = z; rw [← mul_assoc, hab, one_mul]

/-! ## Decomposition of the odd elements -/

private lemma odd_decomp_exists {z : GaussianInt} (hz : isOddG z) :
    ∃ a ∈ units4, ∃ p : GaussianInt, IsPrimary p ∧ z = a * p := by
  have hodd : Odd z.norm.natAbs := (isOddG_iff z).mp hz
  have hz0 : z ≠ 0 := by
    rintro rfl
    simp only [Zsqrtd.norm_def, Zsqrtd.re_zero, Zsqrtd.im_zero, mul_zero, sub_zero,
      Int.natAbs_zero] at hodd
    exact Nat.not_odd_zero hodd
  obtain ⟨w, hwP, -⟩ :=
    Commons.NumberTheory.GaussianInt.primary_associate_exists_unique hz0 hodd
  obtain ⟨ε, hε⟩ := hwP.1
  refine ⟨(↑ε : GaussianInt), ?_, w, ⟨hwP.2.1, hwP.2.2.1, ?_⟩, ?_⟩
  · rw [mem_units4_iff]
    rcases (Commons.NumberTheory.GaussianInt.units_classification (↑ε : GaussianInt)).mp
      (Units.isUnit ε) with h | h | h | h
    · exact Or.inl h
    · exact Or.inr (Or.inl h)
    · exact Or.inr (Or.inr (Or.inl h))
    · exact Or.inr (Or.inr (Or.inr h))
  · exact (ZMod.intCast_eq_intCast_iff w.im (w.re - 1) 4).mp (by push_cast; exact hwP.2.2.2)
  · rw [mul_comm]
    exact hε.symm

private lemma odd_decomp_unique {a₁ a₂ p₁ p₂ : GaussianInt}
    (ha₁ : a₁ ∈ units4) (ha₂ : a₂ ∈ units4) (hp₁ : IsPrimary p₁) (hp₂ : IsPrimary p₂)
    (h : a₁ * p₁ = a₂ * p₂) : a₁ = a₂ := by
  obtain ⟨b, hba, hab⟩ := exists_inv_of_mem_units4 ha₂
  have hp₂' : p₂ = (b * a₁) * p₁ := by
    have h' : b * (a₁ * p₁) = b * (a₂ * p₂) := by rw [h]
    have h₁ : b * (a₁ * p₁) = (b * a₁) * p₁ := (mul_assoc b a₁ p₁).symm
    have h₂ : b * (a₂ * p₂) = p₂ := by rw [← mul_assoc, hba, one_mul]
    rw [h₁, h₂] at h'
    exact h'.symm
  have hunit : IsUnit (b * a₁) :=
    IsUnit.mul (isUnit_iff_exists_inv'.mpr ⟨a₂, hab⟩) (isUnit_of_mem_units4 ha₁)
  have hprim : IsPrimary (b * a₁) := by
    have hbap₁ : IsPrimary (p₁ * (b * a₁)) := by
      have : p₁ * (b * a₁) = p₂ := by rw [mul_comm, hp₂']
      rw [this]; exact hp₂
    exact isPrimary_of_isPrimary_mul_right hp₁ hbap₁
  have hone : b * a₁ = 1 := isPrimary_unit hprim hunit
  calc a₁ = 1 * a₁ := (one_mul a₁).symm
    _ = (a₂ * b) * a₁ := by rw [hab]
    _ = a₂ * (b * a₁) := by rw [mul_assoc]
    _ = a₂ * 1 := by rw [hone]
    _ = a₂ := mul_one a₂

/-! ## The indicator sum -/

private lemma isOddG_of_eq_mul_unit {a z p : GaussianInt} (ha : a ∈ units4) (hp : IsPrimary p)
    (hzp : z = a * p) : isOddG z := by
  rw [hzp, isOddG_mul_iff ha]
  exact isPrimary_isOddG hp

private lemma sum_indicator (z : GaussianInt) :
    ∑ a ∈ units4, (if (∃ p : GaussianInt, IsPrimary p ∧ z = a * p) then (1 : ℂ) else 0)
      = if isOddG z then 1 else 0 := by
  classical
  by_cases hz : isOddG z
  · obtain ⟨a₀, ha₀, p₀, hp₀, hzp⟩ := odd_decomp_exists hz
    have hcond0 : ∃ p : GaussianInt, IsPrimary p ∧ z = a₀ * p := ⟨p₀, hp₀, hzp⟩
    rw [if_pos hz]
    refine Eq.trans (Finset.sum_eq_single a₀ ?_ ?_) ?_
    · intro b hb hba
      rw [if_neg]
      rintro ⟨p, hp, hbp⟩
      exact hba (odd_decomp_unique hb ha₀ hp hp₀ (hbp.symm.trans hzp))
    · intro hnot
      exact absurd ha₀ hnot
    · rw [if_pos hcond0]
  · rw [if_neg hz]
    refine Finset.sum_eq_zero (fun a ha => ?_)
    rw [if_neg]
    rintro ⟨p, hp, hap⟩
    exact hz (isOddG_of_eq_mul_unit ha hp hap)

private lemma TF_eq_sum_TU (chi : GaussianInt → ℂ) (m : ℕ) (u : ℝ) (z : GaussianInt) :
    TF chi m u z = ∑ a ∈ units4, TU chi m u a z := by
  classical
  have h1 : ∀ a ∈ units4, TU chi m u a z
      = (if (∃ p : GaussianInt, IsPrimary p ∧ z = a * p) then (1 : ℂ) else 0) * TF chi m u z := by
    intro a ha
    unfold TU
    by_cases hc : ∃ p : GaussianInt, IsPrimary p ∧ z = a * p
    · rw [if_pos hc, if_pos hc, one_mul]
    · rw [if_neg hc, if_neg hc, zero_mul]
  rw [Finset.sum_congr rfl h1, ← Finset.sum_mul, sum_indicator]
  by_cases hz : isOddG z
  · rw [if_pos hz, one_mul]
  · rw [if_neg hz, zero_mul]
    unfold TF; rw [if_neg hz]

/-! ## The per-unit summand equals a constant times the primary summand -/

private lemma TF_mul_unit_eq (chi : GaussianInt → ℂ) (m : ℕ) (u : ℝ)
    (hmul : ∀ z w : GaussianInt, chi (z * w) = chi z * chi w) {a : GaussianInt}
    (ha : a ∈ units4) {w : GaussianInt} (hw : IsPrimary w) :
    TF chi m u (a * w) = chi a * (a.toComplex) ^ m * TH chi m u w := by
  have hodd : isOddG (a * w) := (isOddG_mul_iff ha w).mpr (isPrimary_isOddG hw)
  have hgn : gnorm (a * w) = gnorm w := by rw [gnorm_mul, gnorm_of_mem_units4 ha, one_mul]
  unfold TF TH
  rw [if_pos hodd, if_pos hw, hmul a w, hgn, GaussianInt.toComplex_mul, mul_pow]
  ring

private lemma TU_mul_unit (chi : GaussianInt → ℂ) (m : ℕ) (u : ℝ)
    (hmul : ∀ z w : GaussianInt, chi (z * w) = chi z * chi w) {a : GaussianInt}
    (ha : a ∈ units4) (w : GaussianInt) :
    TU chi m u a (a * w) = chi a * (a.toComplex) ^ m * TH chi m u w := by
  classical
  by_cases hw : IsPrimary w
  · have hcond : ∃ p : GaussianInt, IsPrimary p ∧ a * w = a * p := ⟨w, hw, rfl⟩
    rw [TU, if_pos hcond]
    exact TF_mul_unit_eq chi m u hmul ha hw
  · have hcond : ¬ ∃ p : GaussianInt, IsPrimary p ∧ a * w = a * p := by
      rintro ⟨p, hp, hap⟩
      have hane : a ≠ 0 := (isUnit_of_mem_units4 ha).ne_zero
      have hwp : w = p := mul_left_cancel₀ hane hap
      rw [← hwp] at hp
      exact hw hp
    rw [TU, if_neg hcond, TH, if_neg hw, mul_zero]

private lemma tsum_TU (chi : GaussianInt → ℂ) (m : ℕ) (u : ℝ)
    (hmul : ∀ z w : GaussianInt, chi (z * w) = chi z * chi w) {a : GaussianInt}
    (ha : a ∈ units4) :
    ∑' z : GaussianInt, TU chi m u a z
      = chi a * (a.toComplex) ^ m * ∑' z : GaussianInt, TH chi m u z := by
  obtain ⟨b, hba, hab⟩ := exists_inv_of_mem_units4 ha
  have h1 : ∑' z : GaussianInt, TU chi m u a z = ∑' w : GaussianInt, TU chi m u a (a * w) :=
    (Equiv.tsum_eq (mulUnitEquiv a b hab hba) (fun z => TU chi m u a z)).symm
  rw [h1, show (fun w => TU chi m u a (a * w))
      = (fun w => chi a * (a.toComplex) ^ m * TH chi m u w) from
    funext (fun w => TU_mul_unit chi m u hmul ha w)]
  rw [tsum_mul_left]

private lemma summable_TU (chi : GaussianInt → ℂ) (m : ℕ) (u : ℝ)
    (hmul : ∀ z w : GaussianInt, chi (z * w) = chi z * chi w) {a : GaussianInt}
    (ha : a ∈ units4) (hsum : Summable (fun z : GaussianInt => TH chi m u z)) :
    Summable (fun z : GaussianInt => TU chi m u a z) := by
  obtain ⟨b, hba, hab⟩ := exists_inv_of_mem_units4 ha
  refine (Equiv.summable_iff (mulUnitEquiv a b hab hba)).mp ?_
  change Summable (fun w => TU chi m u a (a * w))
  rw [show (fun w => TU chi m u a (a * w))
      = (fun w => chi a * (a.toComplex) ^ m * TH chi m u w) from
    funext (fun w => TU_mul_unit chi m u hmul ha w)]
  exact hsum.mul_left _

/-! ## The main identity -/

theorem thetaOdd_eq_unitSum_mul_thetaHol (chi : GaussianInt → ℂ) (m : ℕ)
    (hmul : ∀ z w : GaussianInt, chi (z * w) = chi z * chi w) (u : ℝ) :
    thetaOdd chi m u = unitSum chi m * thetaHol chi m u := by
  classical
  rw [thetaOdd_eq_tsum_TF, thetaHol_eq_tsum_TH]
  rw [tsum_congr (fun z => TF_eq_sum_TU chi m u z)]
  by_cases hsum : Summable (fun z : GaussianInt => TH chi m u z)
  · have hTUsum : ∀ a ∈ units4, Summable (fun z => TU chi m u a z) :=
      fun a ha => summable_TU chi m u hmul ha hsum
    rw [Summable.tsum_finsetSum hTUsum]
    rw [Finset.sum_congr rfl (fun a ha => tsum_TU chi m u hmul ha)]
    rw [← Finset.sum_mul]
    rfl
  · have hT0 : (∑' z : GaussianInt, TH chi m u z) = 0 := tsum_eq_zero_of_not_summable hsum
    rw [hT0, mul_zero]
    apply tsum_eq_zero_of_not_summable
    intro hFs
    have hTFsum : Summable (fun z : GaussianInt => TF chi m u z) :=
      hFs.congr (fun z => (TF_eq_sum_TU chi m u z).symm)
    have hTHsum : Summable (fun z : GaussianInt => TH chi m u z) := by
      by_cases hzeros : ∀ a ∈ units4, chi a * (a.toComplex) ^ m = 0
      · have hchi1 : chi 1 = 0 := by
          have h := hzeros 1 (by rw [mem_units4_iff]; exact Or.inl rfl)
          simpa using h
        refine summable_zero.congr (fun z => ?_)
        unfold TH
        by_cases hz : IsPrimary z
        · rw [if_pos hz, chi_eq_zero_of_chi_one_eq_zero chi hmul hchi1 z, zero_mul, zero_mul]
        · rw [if_neg hz]
      · simp only [not_forall] at hzeros
        obtain ⟨a, ha, ha0⟩ := hzeros
        have hTUa : Summable (fun z => TU chi m u a z) := by
          refine Summable.of_norm_bounded
            (f := fun z => TU chi m u a z) (g := fun z => ‖TF chi m u z‖)
            hTFsum.norm (fun z => ?_)
          unfold TU
          by_cases hc : ∃ p : GaussianInt, IsPrimary p ∧ z = a * p
          · rw [if_pos hc]
          · rw [if_neg hc, norm_zero]; exact norm_nonneg _
        obtain ⟨b, hba, hab⟩ := exists_inv_of_mem_units4 ha
        have hcs : Summable (fun w => chi a * (a.toComplex) ^ m * TH chi m u w) := by
          rw [← show (fun w => TU chi m u a (a * w))
              = (fun w => chi a * (a.toComplex) ^ m * TH chi m u w) from
            funext (fun w => TU_mul_unit chi m u hmul ha w)]
          exact (Equiv.summable_iff (mulUnitEquiv a b hab hba)).mpr hTUa
        refine (hcs.mul_left ((chi a * (a.toComplex) ^ m)⁻¹)).congr (fun z => ?_)
        rw [← mul_assoc, inv_mul_cancel₀ ha0, one_mul]
    exact hsum hTHsum

end

end Work.FIArea5.S16Hecke
