import Mathlib
import Submission.Work.FIArea5.S16Hecke.Defs
import Submission.Work.FIArea5.S16Hecke.ThetaDefs
import Submission.Work.FIArea5.S16Hecke.primaryAux
import Submission.Work.FIArea5.S16Hecke.Basic
import Submission.Work.FIArea6Hecke.R.summable_primary_chi_div_gnorm_cpow
import Submission.Commons.NumberTheory.GaussianInt.primary_associate_exists_unique
import Submission.Commons.NumberTheory.GaussianInt.units_classification

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false

set_option autoImplicit false
set_option linter.unusedVariables false

namespace Work.FIArea6Hecke.R

open Finset
open scoped BigOperators
open Work.FIPlan
open Work.FIArea5.S16Hecke

noncomputable section

attribute [local instance] Classical.propDecidable

/-! ## Summability of the weighted `ψ`-series

For `re s > 1` the series `Σ_z ψ(z)·|z|^{-2s}` is absolutely convergent: the spherical factor
`(z/|z|)^m` has modulus `1` and `‖χ‖ ≤ 1`, while `Σ_z |z|^{-2σ}` converges for `σ > 1`. -/

lemma summable_psi_gnorm_cpow (chi : GaussianInt → ℂ) (m : ℤ)
    (hbd : ∀ z : GaussianInt, ‖chi z‖ ≤ 1) {s : ℂ} (hs : 1 < s.re) :
    Summable (fun z : GaussianInt => psi chi m z * (((gnorm z : ℕ) : ℂ) ^ (-s))) := by
  have hs0 : s ≠ 0 := by rintro rfl; norm_num at hs
  have hsre : (-s.re) ≠ 0 := by rintro h; rw [neg_eq_zero] at h; linarith
  have hnorm : ∀ z : GaussianInt,
      ‖(((gnorm z : ℕ)) : ℂ) ^ (-s)‖ = ((gnorm z : ℕ) : ℝ)^(-s.re) := by
    intro z
    rcases eq_or_ne (gnorm z) 0 with h | h
    · rw [h]; simp only [Nat.cast_zero]
      rw [Complex.zero_cpow (neg_ne_zero.mpr hs0), norm_zero, Real.zero_rpow hsre]
    · rw [show (((gnorm z : ℕ) : ℂ)) = (((gnorm z : ℕ) : ℝ) : ℂ) by simp]
      exact Complex.norm_cpow_eq_rpow_re_of_pos (Nat.cast_pos.mpr (Nat.pos_of_ne_zero h)) (-s)
  refine Summable.of_norm_bounded (summable_gnorm_rpow_neg hs) (fun z => ?_)
  rw [norm_mul, hnorm z]
  calc ‖psi chi m z‖ * ((gnorm z : ℕ) : ℝ) ^ (-s.re)
      ≤ 1 * ((gnorm z : ℕ) : ℝ) ^ (-s.re) :=
        mul_le_mul_of_nonneg_right (norm_psi_le_one chi m hbd z) (by positivity)
    _ = ((gnorm z : ℕ) : ℝ) ^ (-s.re) := one_mul _

/-! ## The four units and the decomposition of the odd elements -/

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

/-! ## The per-unit decomposition of the weighted series -/

/-- The summand of the odd sum: `ψ(z)(|z|²)^{-s}` on odd `z`, `0` otherwise. -/
private def TF (chi : GaussianInt → ℂ) (m : ℤ) (s : ℂ) : GaussianInt → ℂ :=
  fun z => if isOddG z then psi chi m z * (((gnorm z : ℕ) : ℂ) ^ (-s)) else 0

/-- The summand of the primary sum: `ψ(z)(|z|²)^{-s}` on primary `z`, `0` otherwise. -/
private def TH (chi : GaussianInt → ℂ) (m : ℤ) (s : ℂ) : GaussianInt → ℂ :=
  fun z => if IsPrimary z then psi chi m z * (((gnorm z : ℕ) : ℂ) ^ (-s)) else 0

/-- The contribution of the unit `a`: the summand restricted to the `a`-translate of the primary
coset. -/
private def TU (chi : GaussianInt → ℂ) (m : ℤ) (s : ℂ) (a : GaussianInt) :
    GaussianInt → ℂ :=
  fun z => if (∃ p : GaussianInt, IsPrimary p ∧ z = a * p) then TF chi m s z else 0

/-- The spherical unit `z/|z|` at a unit is the unit itself. -/
private lemma psi_unit_eq (chi : GaussianInt → ℂ) (m : ℤ) {a : GaussianInt}
    (ha : a ∈ units4) : psi chi m a = chi a * (a.toComplex) ^ m := by
  rw [psi, gnorm_of_mem_units4 ha]
  simp

private lemma TF_eq_sum_TU (chi : GaussianInt → ℂ) (m : ℤ) (s : ℂ) (z : GaussianInt) :
    TF chi m s z = ∑ a ∈ units4, TU chi m s a z := by
  classical
  have h1 : ∀ a ∈ units4, TU chi m s a z
      = (if (∃ p : GaussianInt, IsPrimary p ∧ z = a * p) then (1 : ℂ) else 0) * TF chi m s z := by
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

private lemma TF_mul_unit_eq (chi : GaussianInt → ℂ) (m : ℤ) (s : ℂ)
    (hmul : ∀ z w : GaussianInt, chi (z * w) = chi z * chi w) {a : GaussianInt}
    (ha : a ∈ units4) {w : GaussianInt} (hw : IsPrimary w) :
    TF chi m s (a * w) = chi a * (a.toComplex) ^ m * TH chi m s w := by
  have hodd : isOddG (a * w) := (isOddG_mul_iff ha w).mpr (isPrimary_isOddG hw)
  have hgn : gnorm (a * w) = gnorm w := by rw [gnorm_mul, gnorm_of_mem_units4 ha, one_mul]
  unfold TF TH
  rw [if_pos hodd, if_pos hw, hgn, psi_mul chi m hmul a w, psi_unit_eq chi m ha]
  ring

private lemma TU_mul_unit (chi : GaussianInt → ℂ) (m : ℤ) (s : ℂ)
    (hmul : ∀ z w : GaussianInt, chi (z * w) = chi z * chi w) {a : GaussianInt}
    (ha : a ∈ units4) (w : GaussianInt) :
    TU chi m s a (a * w) = chi a * (a.toComplex) ^ m * TH chi m s w := by
  classical
  by_cases hw : IsPrimary w
  · have hcond : ∃ p : GaussianInt, IsPrimary p ∧ a * w = a * p := ⟨w, hw, rfl⟩
    rw [TU, if_pos hcond]
    exact TF_mul_unit_eq chi m s hmul ha hw
  · have hcond : ¬ ∃ p : GaussianInt, IsPrimary p ∧ a * w = a * p := by
      rintro ⟨p, hp, hap⟩
      have hane : a ≠ 0 := (isUnit_of_mem_units4 ha).ne_zero
      have hwp : w = p := mul_left_cancel₀ hane hap
      rw [← hwp] at hp
      exact hw hp
    rw [TU, if_neg hcond, TH, if_neg hw, mul_zero]

private lemma tsum_TU (chi : GaussianInt → ℂ) (m : ℤ) (s : ℂ)
    (hmul : ∀ z w : GaussianInt, chi (z * w) = chi z * chi w) {a : GaussianInt}
    (ha : a ∈ units4) :
    ∑' z : GaussianInt, TU chi m s a z
      = chi a * (a.toComplex) ^ m * ∑' z : GaussianInt, TH chi m s z := by
  obtain ⟨b, hba, hab⟩ := exists_inv_of_mem_units4 ha
  have h1 : ∑' z : GaussianInt, TU chi m s a z
      = ∑' w : GaussianInt, TU chi m s a (a * w) :=
    (Equiv.tsum_eq (mulUnitEquiv a b hab hba) (fun z => TU chi m s a z)).symm
  rw [h1, show (fun w => TU chi m s a (a * w))
      = (fun w => chi a * (a.toComplex) ^ m * TH chi m s w) from
    funext (fun w => TU_mul_unit chi m s hmul ha w)]
  rw [tsum_mul_left]

private lemma summable_TU (chi : GaussianInt → ℂ) (m : ℤ) (s : ℂ)
    (hmul : ∀ z w : GaussianInt, chi (z * w) = chi z * chi w) {a : GaussianInt}
    (ha : a ∈ units4) (hsum : Summable (TH chi m s)) :
    Summable (TU chi m s a) := by
  obtain ⟨b, hba, hab⟩ := exists_inv_of_mem_units4 ha
  refine (Equiv.summable_iff (mulUnitEquiv a b hab hba)).mp ?_
  change Summable (fun w => TU chi m s a (a * w))
  rw [show (fun w => TU chi m s a (a * w))
      = (fun w => chi a * (a.toComplex) ^ m * TH chi m s w) from
    funext (fun w => TU_mul_unit chi m s hmul ha w)]
  exact hsum.mul_left _

/-- **The odd part of the weighted lattice series is `Σ_{ε ∈ μ₄} χ(ε)ε^m` times the primary
part.**  Every odd `z` is `a·p` with a unique unit `a` and primary `p`; together with
`ψ(a·p) = χ(a)a^m ψ(p)` and `|a·p| = |p|` this gives the regrouping. -/
private lemma oddDecompUnitSum_local (chi : GaussianInt → ℂ) (m : ℤ) (s : ℂ)
    (hmul : ∀ z w : GaussianInt, chi (z * w) = chi z * chi w)
    (hTHsum : Summable (TH chi m s)) :
    (∑' z : GaussianInt, TF chi m s z)
      = (∑ a ∈ units4, chi a * (a.toComplex) ^ m) * (∑' z : GaussianInt, TH chi m s z) := by
  classical
  rw [tsum_congr (fun z => TF_eq_sum_TU chi m s z)]
  have hTUsum : ∀ a ∈ units4, Summable (TU chi m s a) :=
    fun a ha => summable_TU chi m s hmul ha hTHsum
  rw [Summable.tsum_finsetSum hTUsum]
  rw [Finset.sum_congr rfl (fun a ha => tsum_TU chi m s hmul ha)]
  rw [← Finset.sum_mul]

/-! ## The primary lattice sum is the Hecke `L`-series -/

/-- **The primary-twisted weighted lattice sum is the Hecke `L`-series.**  Grouping the lattice sum
by the norm `n = |z|²` and using that the primary elements of norm `n` contribute the Hecke
eigenvalue `λ(n) = Σ_{|z|²=n, z primary} ψ(z)` gives `Σ_{z primary} ψ(z)|z|^{-2s} = Σ_n λ(n)n^{-s}`,
which is `LSeries (heckeLam chi m) s = heckeLSeries chi m s`. -/
theorem primaryTsum_eq_heckeLSeries (chi : GaussianInt → ℂ) (m : ℤ)
    (hbd : ∀ z : GaussianInt, ‖chi z‖ ≤ 1) {s : ℂ} (hs : 1 < s.re) :
    (∑' z : GaussianInt, TH chi m s z) = heckeLSeries chi m s := by
  classical
  have hfall : Summable (fun z : GaussianInt => psi chi m z * (((gnorm z : ℕ) : ℂ) ^ (-s))) :=
    summable_psi_gnorm_cpow chi m hbd hs
  have hfsum : Summable (fun z : GaussianInt => TH chi m s z) := by
    refine Summable.of_norm_bounded hfall.norm (fun z => ?_)
    unfold TH
    by_cases hz : IsPrimary z
    · rw [if_pos hz]
    · rw [if_neg hz, norm_zero]; positivity
  rw [← (hfsum.hasSum.tsum_fiberwise (gnorm : GaussianInt → ℕ)).tsum_eq]
  have hfib : ∀ n : ℕ,
      (∑' z : ↑(gnorm ⁻¹' ({n} : Set ℕ)), TH chi m s ↑z)
        = heckeLam chi m n * (n : ℂ) ^ (-s) := by
    intro n
    rw [_root_.tsum_subtype (gnorm ⁻¹' ({n} : Set ℕ)) (TH chi m s)]
    have hstep1 : (∑' z : GaussianInt, (gnorm ⁻¹' {n}).indicator (TH chi m s) z)
        = ∑' z : GaussianInt,
            (if IsPrimary z ∧ gnorm z = n then
              psi chi m z * (((gnorm z : ℕ) : ℂ) ^ (-s)) else 0) := by
      refine tsum_congr (fun z => ?_)
      rw [Set.indicator_apply]
      simp only [Set.mem_preimage, Set.mem_singleton_iff]
      unfold TH
      by_cases hp : IsPrimary z <;> by_cases hgn : gnorm z = n <;> simp [hp, hgn]
    rw [hstep1]
    set S : Finset GaussianInt := (gBox (n : ℤ)).filter (fun z => IsPrimary z ∧ gnorm z = n)
      with hS
    have hbound0 : ∀ z ∉ S,
        (if IsPrimary z ∧ gnorm z = n then
          psi chi m z * (((gnorm z : ℕ) : ℂ) ^ (-s)) else 0) = 0 := by
      intro z hz
      rw [if_neg]
      intro h
      apply hz
      rw [hS, Finset.mem_filter]
      refine ⟨?_, h⟩
      have hn : 0 < n := by
        have h1 := one_le_gnorm_of_isPrimary z h.1
        omega
      exact mem_gBox_of_gnorm_le (R := (n : ℤ)) (by exact_mod_cast hn) (by rw [h.2])
    rw [tsum_eq_sum (s := S) hbound0]
    have hSval : ∀ z ∈ S, IsPrimary z ∧ gnorm z = n := by
      intro z hz; rw [hS, Finset.mem_filter] at hz; exact hz.2
    trans ∑ z ∈ S, psi chi m z * (((n : ℕ)) : ℂ) ^ (-s)
    · refine Finset.sum_congr rfl (fun z hz => ?_)
      rw [if_pos (hSval z hz), (hSval z hz).2]
    rw [← Finset.sum_mul]
    congr 1
  rw [tsum_congr hfib]
  unfold heckeLSeries
  rw [LSeries_def₀ (heckeLam_zero chi m) s]
  refine tsum_congr (fun n => ?_)
  rw [div_eq_mul_inv, Complex.cpow_neg]

/-! ## The target -/

theorem oddPartLattice (chi : GaussianInt → ℂ) (m : ℤ)
    (h1 : chi 1 = 1) (hmul : ∀ z w : GaussianInt, chi (z * w) = chi z * chi w)
    (hbd : ∀ z : GaussianInt, ‖chi z‖ ≤ 1)
    [DecidablePred Work.FIArea5.S16Hecke.isOddG] :
    ∀ s : ℂ, 1 < s.re →
      tsum (fun z : GaussianInt =>
        if Work.FIArea5.S16Hecke.isOddG z then
          Work.FIArea5.S16Hecke.psi chi m z * (((Work.FIPlan.gnorm z : ℕ) : ℂ) ^ (-s))
        else 0)
        = (∑ ε ∈ Work.FIArea5.S16Hecke.units4, chi ε * (ε.toComplex) ^ m) *
            Work.FIArea5.S16Hecke.heckeLSeries chi m s := by
  intro s hs
  have hfall : Summable (fun z : GaussianInt =>
      psi chi m z * (((gnorm z : ℕ) : ℂ) ^ (-s))) :=
    summable_psi_gnorm_cpow chi m hbd hs
  have hTHsum : Summable (TH chi m s) := by
    refine Summable.of_norm_bounded hfall.norm (fun z => ?_)
    unfold TH
    by_cases hz : IsPrimary z
    · rw [if_pos hz]
    · rw [if_neg hz, norm_zero]; positivity
  have hTF : (tsum (fun z : GaussianInt =>
        if Work.FIArea5.S16Hecke.isOddG z then
          Work.FIArea5.S16Hecke.psi chi m z * (((Work.FIPlan.gnorm z : ℕ) : ℂ) ^ (-s))
        else 0)) = (∑' z : GaussianInt, TF chi m s z) := by
    refine tsum_congr (fun z => ?_)
    unfold TF
    by_cases h : Work.FIArea5.S16Hecke.isOddG z
    · rw [if_pos h, if_pos h]
    · rw [if_neg h, if_neg h]
  rw [hTF, oddDecompUnitSum_local chi m s hmul hTHsum]
  have hprimary : (∑' z : GaussianInt, TH chi m s z) = heckeLSeries chi m s :=
    primaryTsum_eq_heckeLSeries chi m hbd hs
  rw [hprimary]

end

end Work.FIArea6Hecke.R
