import Mathlib
import Submission.Work.HP.MMDefs
import Submission.Work.HP.MobDefs
import Submission.Work.HP.MobScaleVec

set_option autoImplicit false
noncomputable section
open Finset

namespace Work.HP

variable {ι : Type*}

private lemma abs_coord_le_eNorm_aux [Fintype ι] (a : ι → ℤ) (i : ι) : |(a i : ℝ)| ≤ eNorm a := by
  have h : ((a i : ℝ)) ^ 2 ≤ ∑ j, ((a j : ℝ)) ^ 2 :=
    Finset.single_le_sum (f := fun j => ((a j : ℝ)) ^ 2) (fun j _ => sq_nonneg _)
      (Finset.mem_univ i)
  calc |(a i : ℝ)| = Real.sqrt (((a i : ℝ)) ^ 2) := (Real.sqrt_sq_eq_abs _).symm
    _ ≤ Real.sqrt (∑ j, ((a j : ℝ)) ^ 2) := Real.sqrt_le_sqrt h
    _ = eNorm a := rfl

private lemma one_le_eNorm_aux [Fintype ι] {a : ι → ℤ} (ha : a ≠ 0) : 1 ≤ eNorm a := by
  obtain ⟨i, hi⟩ : ∃ i, a i ≠ 0 := by
    by_contra h; push_neg at h; exact ha (funext h)
  have h1 : (1 : ℝ) ≤ |(a i : ℝ)| := by
    have : (1 : ℤ) ≤ |a i| := Int.one_le_abs hi
    exact_mod_cast this
  exact le_trans h1 (abs_coord_le_eNorm_aux a i)

private lemma le_eNorm_of_dvd_aux [Fintype ι] {a : ι → ℤ} {ℓ : ℕ} (hℓ : 1 ≤ ℓ) {i : ι}
    (hdvd : (ℓ : ℤ) ∣ a i) (hi : a i ≠ 0) : (ℓ : ℝ) ≤ eNorm a := by
  obtain ⟨c, hc⟩ := hdvd
  have hc0 : c ≠ 0 := by rintro rfl; rw [mul_zero] at hc; exact hi hc
  have h1 : |(a i : ℝ)| = (ℓ : ℝ) * |(c : ℝ)| := by
    rw [hc]; push_cast; rw [abs_mul, abs_of_nonneg (by positivity : (0 : ℝ) ≤ (ℓ : ℝ))]
  have h2 : (1 : ℝ) ≤ |(c : ℝ)| := by
    have : (1 : ℤ) ≤ |c| := Int.one_le_abs hc0
    exact_mod_cast this
  calc (ℓ : ℝ) = (ℓ : ℝ) * 1 := (mul_one _).symm
    _ ≤ (ℓ : ℝ) * |(c : ℝ)| := mul_le_mul_of_nonneg_left h2 (by positivity)
    _ = |(a i : ℝ)| := h1.symm
    _ ≤ eNorm a := abs_coord_le_eNorm_aux a i

private lemma finset_gcd_nonneg {ι : Type*} [DecidableEq ι] (s : Finset ι) (f : ι → ℤ) :
    0 ≤ s.gcd f := by
  induction s using Finset.induction with
  | empty => simp
  | insert a s ha ih =>
      rw [Finset.gcd_insert]
      exact Int.gcd_nonneg _ _

private lemma moebius_sum_divisors (m : ℕ) :
    (∑ d ∈ m.divisors, (ArithmeticFunction.moebius d : ℤ)) = if m = 1 then 1 else 0 := by
  rw [← ArithmeticFunction.coe_mul_zeta_apply (f := ArithmeticFunction.moebius) (x := m),
    ArithmeticFunction.moebius_mul_coe_zeta, ArithmeticFunction.one_apply]

private lemma moebius_sum_divisors_R (m : ℕ) :
    (∑ d ∈ m.divisors, (ArithmeticFunction.moebius d : ℝ)) = if m = 1 then 1 else 0 := by
  have h := ArithmeticFunction.coe_mul_zeta_apply (R := ℝ)
      (f := (ArithmeticFunction.moebius : ArithmeticFunction ℝ)) (x := m)
  rw [ArithmeticFunction.coe_moebius_mul_coe_zeta (R := ℝ), ArithmeticFunction.one_apply] at h
  exact h.symm

private lemma isPrim_ne_zero_L [Fintype ι] {a : ι → ℤ} (h : IsPrim a) : a ≠ 0 := by
  intro h0
  have h1 : Finset.univ.gcd a = 0 :=
    Finset.gcd_eq_zero_iff.mpr (fun i _ => by rw [h0]; rfl)
  rw [IsPrim] at h
  rw [h] at h1
  exact one_ne_zero h1

private lemma dvd_all_iff_dvd_gcd [Fintype ι] (a : ι → ℤ) (ℓ : ℕ) :
    (∀ i, (ℓ : ℤ) ∣ a i) ↔ ((ℓ : ℤ) ∣ Finset.univ.gcd a) := by
  constructor
  · intro h
    exact Finset.dvd_gcd (fun i _ => h i)
  · intro h i
    exact h.trans (Finset.gcd_dvd (Finset.mem_univ i))

private lemma filter_Icc_eq_divisors [Fintype ι] [DecidableEq ι] (a : ι → ℤ) (M : ℕ) (ha : a ≠ 0)
    (hM : ∀ ℓ : ℕ, 1 ≤ ℓ → (∀ i, (ℓ : ℤ) ∣ a i) → ℓ ≤ M) :
    (Finset.Icc 1 M).filter (fun (ℓ : ℕ) => ∀ i, (ℓ : ℤ) ∣ a i)
      = (Finset.univ.gcd a).natAbs.divisors := by
  have hg0 : Finset.univ.gcd a ≠ 0 := by
    intro h
    exact ha (funext (fun i => Finset.gcd_eq_zero_iff.mp h i (Finset.mem_univ i)))
  have hgn : (Finset.univ.gcd a).natAbs ≠ 0 := Int.natAbs_ne_zero.mpr hg0
  apply Finset.ext
  intro ℓ
  rw [Finset.mem_filter, Finset.mem_Icc, Nat.mem_divisors]
  constructor
  · rintro ⟨⟨h1, h2⟩, h3⟩
    exact ⟨Int.natAbs_dvd_natAbs.mpr ((dvd_all_iff_dvd_gcd a ℓ).mp h3), hgn⟩
  · rintro ⟨h1, -⟩
    have h2 : ∀ i, (ℓ : ℤ) ∣ a i := (dvd_all_iff_dvd_gcd a ℓ).mpr (Int.natAbs_dvd_natAbs.mp h1)
    have hℓ0 : ℓ ≠ 0 := by
      rintro rfl
      rw [zero_dvd_iff] at h1
      exact hgn h1
    exact ⟨⟨Nat.one_le_iff_ne_zero.mpr hℓ0, hM ℓ (Nat.one_le_iff_ne_zero.mpr hℓ0) h2⟩, h2⟩

private lemma sum_mu_filter_Icc_dvd [Fintype ι] [DecidableEq ι] (a : ι → ℤ) (M : ℕ) (ha : a ≠ 0)
    (hM : ∀ ℓ : ℕ, 1 ≤ ℓ → (∀ i, (ℓ : ℤ) ∣ a i) → ℓ ≤ M) :
    (∑ ℓ ∈ (Finset.Icc 1 M).filter (fun (ℓ : ℕ) => ∀ i, (ℓ : ℤ) ∣ a i),
        (ArithmeticFunction.moebius ℓ : ℝ)) = if Finset.univ.gcd a = 1 then 1 else 0 := by
  rw [filter_Icc_eq_divisors a M ha hM, moebius_sum_divisors_R]
  have hg : 0 ≤ Finset.univ.gcd a := finset_gcd_nonneg _ _
  by_cases h : Finset.univ.gcd a = 1
  · have h1 : (Finset.univ.gcd a).natAbs = 1 := by rw [h]; rfl
    rw [h1, if_pos rfl, if_pos h]
  · have h1 : (Finset.univ.gcd a).natAbs ≠ 1 := by
      intro h2
      rcases (Int.natAbs_eq_iff.mp h2) with h3 | h3
      · exact h h3
      · rw [h3] at hg; norm_num at hg
    rw [if_neg h1, if_neg h]

private lemma pow_mul_invpw (a b : ℝ) (k : ℕ) (ha : a ≠ 0) :
    a ^ k * (1 / (a * b) ^ k) = 1 / b ^ k := by
  have h : a ^ k ≠ 0 := pow_ne_zero k ha
  rw [one_div, one_div, mul_pow, mul_inv_rev, ← mul_assoc, mul_comm (a ^ k) ((b ^ k)⁻¹),
    mul_assoc, mul_inv_cancel₀ h, mul_one]

private lemma mem_image_scaleVec_iff [Fintype ι] [DecidableEq ι] (A : ℝ) (hA : 1 ≤ A)
    (a : ι → ℤ) (haA : eNorm a ≤ A) (ℓ : ℕ) (hℓ : 1 ≤ ℓ) :
    (a ∈ (Fintype.piFinset (fun _ : ι => Finset.Icc (-(⌈A⌉₊ : ℤ)) (⌈A⌉₊ : ℤ))).image
        (scaleVec ℓ)) ↔ (∀ i, (ℓ : ℤ) ∣ a i) := by
  constructor
  · intro hmem i
    rw [Finset.mem_image] at hmem
    obtain ⟨b, -, hb⟩ := hmem
    exact ⟨b i, by rw [← hb]; rfl⟩
  · intro hdvd
    refine Finset.mem_image.mpr ⟨fun i => a i / (ℓ : ℤ), ?_, ?_⟩
    · rw [Fintype.mem_piFinset]
      intro i
      rw [Finset.mem_Icc]
      have hℓz : (0 : ℤ) < (ℓ : ℤ) := by exact_mod_cast hℓ
      have hcancel : (ℓ : ℤ) * (a i / (ℓ : ℤ)) = a i := Int.mul_ediv_cancel' (hdvd i)
      have hb_le : |a i / (ℓ : ℤ)| ≤ |a i| := by
        have h1 : (ℓ : ℤ) * |a i / (ℓ : ℤ)| = |a i| := by
          have habs : |a i| = |(ℓ : ℤ) * (a i / (ℓ : ℤ))| := by
            conv_lhs => rw [← hcancel]
          rw [habs, abs_mul, abs_of_nonneg hℓz.le]
        have h2 : 0 ≤ |a i / (ℓ : ℤ)| := abs_nonneg _
        have h3 : (1 : ℤ) ≤ (ℓ : ℤ) := by exact_mod_cast hℓ
        nlinarith
      have hK : |(a i : ℝ)| ≤ (⌈A⌉₊ : ℝ) :=
        le_trans (le_trans (abs_coord_le_eNorm_aux a i) haA) (Nat.le_ceil A)
      have hKz : |a i| ≤ (⌈A⌉₊ : ℤ) := by exact_mod_cast hK
      have hfin : |a i / (ℓ : ℤ)| ≤ (⌈A⌉₊ : ℤ) := le_trans hb_le hKz
      exact ⟨by linarith [neg_abs_le (a i / (ℓ : ℤ))],
             by linarith [le_abs_self (a i / (ℓ : ℤ))]⟩
    · funext i
      simp only [scaleVec]
      exact Int.mul_ediv_cancel' (hdvd i)

theorem Sstar_moebius_abstract [Fintype ι] [DecidableEq ι]
    (k : ℕ) (A : ℝ) (hA : 1 ≤ A)
    (L R : Set (ι → ℤ)) (L' R' : ℕ → Set (ι → ℤ))
    (hL' : ∀ ℓ, 1 ≤ ℓ → ∀ b, (b ∈ L' ℓ ↔ scaleVec ℓ b ∈ L))
    (hR' : ∀ ℓ, 1 ≤ ℓ → ∀ b, (b ∈ R' ℓ ↔ scaleVec ℓ b ∈ R))
    (hR : ∀ a ∈ R, eNorm a ≤ A) :
    (∑ᶠ a ∈ {a | a ∈ L ∧ IsPrim a ∧ a ∈ R}, 1 / eNorm a ^ k)
      = ∑ ℓ ∈ Finset.Icc 1 ⌊A⌋₊, ((ArithmeticFunction.moebius ℓ : ℝ) / (ℓ : ℝ) ^ k) *
          (∑ᶠ b ∈ {b | b ∈ L' ℓ ∧ b ≠ 0 ∧ b ∈ R' ℓ}, 1 / eNorm b ^ k) := by
  classical
  obtain ⟨hscale_norm, -, -, hscale_zero, hscale_inj⟩ := MobScaleVec (ι := ι)
  have hK1 : 1 ≤ ⌈A⌉₊ := Nat.ceil_pos.mpr (by linarith)
  have hKK : ⌈A⌉₊ ≤ ⌈A⌉₊ * ⌈A⌉₊ := Nat.le_mul_of_pos_right _ hK1
  have hMK : ⌊A⌋₊ ≤ ⌈A⌉₊ := Nat.floor_le_ceil A
  have hKcast : (⌈A⌉₊ : ℤ) ≤ ((⌈A⌉₊ * ⌈A⌉₊ : ℕ) : ℤ) := by exact_mod_cast hKK
  set Box : Finset (ι → ℤ) :=
    Fintype.piFinset (fun _ : ι => Finset.Icc (-(⌈A⌉₊ : ℤ)) (⌈A⌉₊ : ℤ)) with hBoxdef
  set Big : Finset (ι → ℤ) :=
    Fintype.piFinset (fun _ : ι => Finset.Icc (-((⌈A⌉₊ * ⌈A⌉₊ : ℕ) : ℤ))
      ((⌈A⌉₊ * ⌈A⌉₊ : ℕ) : ℤ)) with hBigdef
  have mem_Box : ∀ a : ι → ℤ, eNorm a ≤ A → a ∈ Box := by
    intro a ha
    rw [hBoxdef, Fintype.mem_piFinset]
    intro i
    rw [Finset.mem_Icc]
    have h1 : |(a i : ℝ)| ≤ (⌈A⌉₊ : ℝ) :=
      le_trans (le_trans (abs_coord_le_eNorm_aux a i) ha) (Nat.le_ceil A)
    have h2 := abs_le.mp h1
    exact ⟨by exact_mod_cast h2.1, by exact_mod_cast h2.2⟩
  have mem_Big : ∀ a : ι → ℤ, eNorm a ≤ A → a ∈ Big := by
    intro a ha
    rw [hBigdef, Fintype.mem_piFinset]
    intro i
    rw [Finset.mem_Icc]
    have h1 : |(a i : ℝ)| ≤ ((⌈A⌉₊ * ⌈A⌉₊ : ℕ) : ℝ) := by
      refine le_trans (le_trans (abs_coord_le_eNorm_aux a i) ha) ?_
      exact le_trans (Nat.le_ceil A) (by exact_mod_cast hKK)
    have h2 := abs_le.mp h1
    exact ⟨by exact_mod_cast h2.1, by exact_mod_cast h2.2⟩
  have image_sub_Big : ∀ ℓ ∈ Finset.Icc 1 ⌊A⌋₊, Box.image (scaleVec ℓ) ⊆ Big := by
    intro ℓ hl a ha
    rw [Finset.mem_image] at ha
    obtain ⟨b, hb, rfl⟩ := ha
    rw [hBoxdef, Fintype.mem_piFinset] at hb
    rw [hBigdef, Fintype.mem_piFinset]
    intro i
    change (ℓ : ℤ) * b i ∈ Finset.Icc (-((⌈A⌉₊ * ⌈A⌉₊ : ℕ) : ℤ)) ((⌈A⌉₊ * ⌈A⌉₊ : ℕ) : ℤ)
    rw [Finset.mem_Icc]
    have hbi : b i ∈ Finset.Icc (-(⌈A⌉₊ : ℤ)) (⌈A⌉₊ : ℤ) := hb i
    rw [Finset.mem_Icc] at hbi
    have hlM : ℓ ≤ ⌊A⌋₊ := (Finset.mem_Icc.mp hl).2
    have hℓK : (ℓ : ℤ) ≤ (⌈A⌉₊ : ℤ) := by
      have : ℓ ≤ ⌈A⌉₊ := le_trans hlM hMK
      exact_mod_cast this
    have hℓnn : (0 : ℤ) ≤ (ℓ : ℤ) := Int.natCast_nonneg ℓ
    have habs : |(ℓ : ℤ) * b i| ≤ ((⌈A⌉₊ * ⌈A⌉₊ : ℕ) : ℤ) := by
      rw [abs_mul, abs_of_nonneg hℓnn]
      have hbabs : |b i| ≤ (⌈A⌉₊ : ℤ) := abs_le.mpr hbi
      have hml := mul_le_mul hℓK hbabs (abs_nonneg (b i)) (by positivity)
      calc (ℓ : ℤ) * |b i| ≤ (⌈A⌉₊ : ℤ) * (⌈A⌉₊ : ℤ) := hml
        _ = ((⌈A⌉₊ * ⌈A⌉₊ : ℕ) : ℤ) := by push_cast; ring
    constructor
    · have := neg_abs_le ((ℓ : ℤ) * b i); linarith
    · have := le_abs_self ((ℓ : ℤ) * b i); linarith
  have LHS_eq : (∑ᶠ a ∈ {a | a ∈ L ∧ IsPrim a ∧ a ∈ R}, 1 / eNorm a ^ k)
      = ∑ a ∈ Big, (if a ∈ L ∧ IsPrim a ∧ a ∈ R then 1 / eNorm a ^ k else 0) := by
    rw [finsum_mem_def]
    rw [finsum_eq_finsetSum_of_support_subset (s := Big)]
    · apply Finset.sum_congr rfl
      intro a _
      simp only [Set.indicator_apply, Set.mem_setOf_eq]
    · intro a ha
      simp only [Function.mem_support] at ha
      have hmem : a ∈ {a : ι → ℤ | a ∈ L ∧ IsPrim a ∧ a ∈ R} := by
        by_contra hcon
        exact ha (Set.indicator_of_notMem hcon _)
      exact mem_Big a (hR a hmem.2.2)
  have RHS_eq : (∑ ℓ ∈ Finset.Icc 1 ⌊A⌋₊, ((ArithmeticFunction.moebius ℓ : ℝ) / (ℓ : ℝ) ^ k) *
          (∑ᶠ b ∈ {b | b ∈ L' ℓ ∧ b ≠ 0 ∧ b ∈ R' ℓ}, 1 / eNorm b ^ k))
      = ∑ a ∈ Big, (if a ∈ L ∧ IsPrim a ∧ a ∈ R then 1 / eNorm a ^ k else 0) := by
    calc
      (∑ ℓ ∈ Finset.Icc 1 ⌊A⌋₊, ((ArithmeticFunction.moebius ℓ : ℝ) / (ℓ : ℝ) ^ k) *
          (∑ᶠ b ∈ {b | b ∈ L' ℓ ∧ b ≠ 0 ∧ b ∈ R' ℓ}, 1 / eNorm b ^ k))
          = ∑ ℓ ∈ Finset.Icc 1 ⌊A⌋₊, ∑ a ∈ Big,
              (if a ∈ Box.image (scaleVec ℓ) then (ArithmeticFunction.moebius ℓ : ℝ) *
                (if a ∈ L ∧ a ≠ 0 ∧ a ∈ R then 1 / eNorm a ^ k else 0) else 0) := by
            apply Finset.sum_congr rfl
            intro ℓ hl
            have hl1 : 1 ≤ ℓ := (Finset.mem_Icc.mp hl).1
            have hA1 : (∑ᶠ b ∈ {b | b ∈ L' ℓ ∧ b ≠ 0 ∧ b ∈ R' ℓ}, 1 / eNorm b ^ k)
                = ∑ b ∈ Box, (if b ∈ L' ℓ ∧ b ≠ 0 ∧ b ∈ R' ℓ then 1 / eNorm b ^ k else 0) := by
              rw [finsum_mem_def]
              rw [finsum_eq_finsetSum_of_support_subset (s := Box)]
              · apply Finset.sum_congr rfl
                intro b _
                simp only [Set.indicator_apply, Set.mem_setOf_eq]
              · intro b hb
                simp only [Function.mem_support] at hb
                have hbmem : b ∈ {b : ι → ℤ | b ∈ L' ℓ ∧ b ≠ 0 ∧ b ∈ R' ℓ} := by
                  by_contra hcon
                  exact hb (Set.indicator_of_notMem hcon _)
                refine mem_Box b ?_
                have h1 : scaleVec ℓ b ∈ R := (hR' ℓ hl1 b).mp hbmem.2.2
                have h2 : eNorm (scaleVec ℓ b) ≤ A := hR _ h1
                rw [hscale_norm] at h2
                have hb0 : 0 ≤ eNorm b := Real.sqrt_nonneg _
                have hℓ1 : (1 : ℝ) ≤ (ℓ : ℝ) := by exact_mod_cast hl1
                nlinarith
            have hA2 : (∑ b ∈ Box, (if b ∈ L' ℓ ∧ b ≠ 0 ∧ b ∈ R' ℓ then 1 / eNorm b ^ k else 0))
                = ∑ b ∈ Box, (if scaleVec ℓ b ∈ L ∧ scaleVec ℓ b ≠ 0 ∧ scaleVec ℓ b ∈ R then
                    1 / eNorm b ^ k else 0) := by
              apply Finset.sum_congr rfl
              intro b _
              have hiff : (b ∈ L' ℓ ∧ b ≠ 0 ∧ b ∈ R' ℓ) ↔
                  (scaleVec ℓ b ∈ L ∧ scaleVec ℓ b ≠ 0 ∧ scaleVec ℓ b ∈ R) := by
                rw [hL' ℓ hl1 b, hR' ℓ hl1 b]
                constructor
                · rintro ⟨h1, h2, h3⟩
                  refine ⟨h1, ?_, h3⟩
                  intro hc
                  rcases (hscale_zero ℓ b).mp hc with h | h
                  · omega
                  · exact h2 h
                · rintro ⟨h1, h2, h3⟩
                  refine ⟨h1, ?_, h3⟩
                  intro hc
                  exact h2 (by rw [hc]; exact (hscale_zero ℓ 0).mpr (Or.inr rfl))
              by_cases h : b ∈ L' ℓ ∧ b ≠ 0 ∧ b ∈ R' ℓ
              · rw [if_pos h, if_pos (hiff.mp h)]
              · rw [if_neg h, if_neg (fun hc => h (hiff.mpr hc))]
            have hA3 : (∑ b ∈ Box, (if scaleVec ℓ b ∈ L ∧ scaleVec ℓ b ≠ 0 ∧ scaleVec ℓ b ∈ R then
                    1 / eNorm b ^ k else 0))
                = (ℓ : ℝ) ^ k * ∑ a ∈ Box.image (scaleVec ℓ),
                    (if a ∈ L ∧ a ≠ 0 ∧ a ∈ R then 1 / eNorm a ^ k else 0) := by
              rw [Finset.mul_sum]
              rw [Finset.sum_image (f := fun a : ι → ℤ => (ℓ : ℝ) ^ k *
                    (if a ∈ L ∧ a ≠ 0 ∧ a ∈ R then 1 / eNorm a ^ k else 0))
                    (g := scaleVec ℓ) (fun a _ b _ hab => hscale_inj ℓ a b hl1 hab)]
              apply Finset.sum_congr rfl
              intro b _
              by_cases hC : scaleVec ℓ b ∈ L ∧ scaleVec ℓ b ≠ 0 ∧ scaleVec ℓ b ∈ R
              · rw [if_pos hC, if_pos hC]
                rw [hscale_norm]
                exact (pow_mul_invpw (ℓ : ℝ) (eNorm b) k (by positivity)).symm
              · rw [if_neg hC, if_neg hC, mul_zero]
            calc ((ArithmeticFunction.moebius ℓ : ℝ) / (ℓ : ℝ) ^ k) *
                  (∑ᶠ b ∈ {b | b ∈ L' ℓ ∧ b ≠ 0 ∧ b ∈ R' ℓ}, 1 / eNorm b ^ k)
                = ((ArithmeticFunction.moebius ℓ : ℝ) / (ℓ : ℝ) ^ k) *
                  ((ℓ : ℝ) ^ k * ∑ a ∈ Box.image (scaleVec ℓ),
                    (if a ∈ L ∧ a ≠ 0 ∧ a ∈ R then 1 / eNorm a ^ k else 0)) := by
                    rw [hA1, hA2, hA3]
              _ = (ArithmeticFunction.moebius ℓ : ℝ) * ∑ a ∈ Box.image (scaleVec ℓ),
                    (if a ∈ L ∧ a ≠ 0 ∧ a ∈ R then 1 / eNorm a ^ k else 0) := by
                    have hℓ0 : (ℓ : ℝ) ^ k ≠ 0 := pow_ne_zero k (by positivity)
                    field_simp
              _ = ∑ a ∈ Box.image (scaleVec ℓ), (ArithmeticFunction.moebius ℓ : ℝ) *
                    (if a ∈ L ∧ a ≠ 0 ∧ a ∈ R then 1 / eNorm a ^ k else 0) := by
                    rw [Finset.mul_sum]
              _ = ∑ a ∈ Big, (if a ∈ Box.image (scaleVec ℓ) then (ArithmeticFunction.moebius ℓ : ℝ) *
                    (if a ∈ L ∧ a ≠ 0 ∧ a ∈ R then 1 / eNorm a ^ k else 0) else 0) := by
                    rw [← Finset.sum_filter]
                    congr 1
                    rw [Finset.filter_mem_eq_inter, Finset.inter_eq_right.mpr (image_sub_Big ℓ hl)]
      _ = ∑ a ∈ Big, ∑ ℓ ∈ Finset.Icc 1 ⌊A⌋₊,
              (if a ∈ Box.image (scaleVec ℓ) then (ArithmeticFunction.moebius ℓ : ℝ) *
                (if a ∈ L ∧ a ≠ 0 ∧ a ∈ R then 1 / eNorm a ^ k else 0) else 0) :=
            Finset.sum_comm
      _ = ∑ a ∈ Big, (∑ ℓ ∈ (Finset.Icc 1 ⌊A⌋₊).filter (fun ℓ => a ∈ Box.image (scaleVec ℓ)),
              (ArithmeticFunction.moebius ℓ : ℝ)) *
              (if a ∈ L ∧ a ≠ 0 ∧ a ∈ R then 1 / eNorm a ^ k else 0) := by
            apply Finset.sum_congr rfl
            intro a _
            rw [Finset.sum_mul]
            rw [Finset.sum_filter (p := fun ℓ => a ∈ Box.image (scaleVec ℓ))
                  (f := fun ℓ => (ArithmeticFunction.moebius ℓ : ℝ) *
                    (if a ∈ L ∧ a ≠ 0 ∧ a ∈ R then 1 / eNorm a ^ k else 0))]
      _ = ∑ a ∈ Big, (if a ∈ L ∧ IsPrim a ∧ a ∈ R then 1 / eNorm a ^ k else 0) := by
            apply Finset.sum_congr rfl
            intro a _
            by_cases hC : a ∈ L ∧ a ≠ 0 ∧ a ∈ R
            · have hEq : (Finset.Icc 1 ⌊A⌋₊).filter (fun ℓ => a ∈ Box.image (scaleVec ℓ))
                  = (Finset.Icc 1 ⌊A⌋₊).filter (fun (ℓ : ℕ) => ∀ i, (ℓ : ℤ) ∣ a i) := by
                apply Finset.filter_congr
                intro ℓ hl
                have hl1 : 1 ≤ ℓ := (Finset.mem_Icc.mp hl).1
                rw [hBoxdef]
                exact mem_image_scaleVec_iff A hA a (hR a hC.2.2) ℓ hl1
              rw [hEq]
              have hMhyp : ∀ ℓ : ℕ, 1 ≤ ℓ → (∀ i, (ℓ : ℤ) ∣ a i) → ℓ ≤ ⌊A⌋₊ := by
                intro ℓ hl1 hdvd
                obtain ⟨i, hi⟩ : ∃ i, a i ≠ 0 := by
                  by_contra h
                  simp only [not_exists, not_not] at h
                  exact hC.2.1 (funext h)
                exact Nat.le_floor (le_trans (le_eNorm_of_dvd_aux hl1 (hdvd i) hi) (hR a hC.2.2))
              rw [sum_mu_filter_Icc_dvd a ⌊A⌋₊ hC.2.1 hMhyp, if_pos hC]
              by_cases hP : Finset.univ.gcd a = 1
              · rw [if_pos hP, if_pos ⟨hC.1, hP, hC.2.2⟩, one_mul]
              · rw [if_neg hP, if_neg (fun h => hP h.2.1), zero_mul]
            · rw [if_neg hC, if_neg (fun h => hC ⟨h.1, isPrim_ne_zero_L h.2.1, h.2.2⟩), mul_zero]
  rw [LHS_eq, RHS_eq]

/-! ## Scaling of the lattices and regions appearing in `SstarMobiusLoc` -/

private lemma int_dvd_mul_iff_div_gcd_dvd (Q ℓ : ℕ) (x : ℤ) (hℓ : 1 ≤ ℓ) :
    (Q : ℤ) ∣ (ℓ : ℤ) * x ↔ ((Q / Nat.gcd ℓ Q : ℕ) : ℤ) ∣ x := by
  have hg0 : 0 < Nat.gcd ℓ Q := Nat.gcd_pos_of_pos_left Q (by omega)
  have hgne : ((Nat.gcd ℓ Q : ℕ) : ℤ) ≠ 0 := by exact_mod_cast (Nat.pos_iff_ne_zero.mp hg0)
  have hQ : ((Nat.gcd ℓ Q : ℕ) : ℤ) * ((Q / Nat.gcd ℓ Q : ℕ) : ℤ) = (Q : ℤ) := by
    rw [← Nat.cast_mul, Nat.mul_div_cancel' (Nat.gcd_dvd_right ℓ Q)]
  have hl : ((Nat.gcd ℓ Q : ℕ) : ℤ) * ((ℓ / Nat.gcd ℓ Q : ℕ) : ℤ) = (ℓ : ℤ) := by
    rw [← Nat.cast_mul, Nat.mul_div_cancel' (Nat.gcd_dvd_left ℓ Q)]
  have hcop : IsCoprime ((Q / Nat.gcd ℓ Q : ℕ) : ℤ) ((ℓ / Nat.gcd ℓ Q : ℕ) : ℤ) :=
    (Nat.coprime_div_gcd_div_gcd hg0).isCoprime.symm
  constructor
  · intro h
    rw [← hQ, ← hl, mul_assoc] at h
    exact hcop.dvd_of_dvd_mul_left ((mul_dvd_mul_iff_left hgne).mp h)
  · intro h
    rw [← hQ, ← hl, mul_assoc]
    exact mul_dvd_mul_left _ (dvd_mul_of_dvd_right h _)

private lemma mem_latMod_iff_L {ι : Type*} [Fintype ι] (c : ι → ℤ) (Q : ℕ) (a : ι → ℤ) :
    a ∈ latMod c Q ↔ (Q : ℤ) ∣ Fintype.linearCombination ℤ c a := by
  rw [latMod, Submodule.mem_comap, Submodule.mem_span_singleton]
  constructor
  · rintro ⟨k, hk⟩
    exact ⟨k, by rw [← hk]; ring⟩
  · rintro ⟨k, hk⟩
    exact ⟨k, by rw [hk]; ring⟩

private lemma latMod_scaleVec_iff {ι : Type*} [Fintype ι] (c : ι → ℤ) (Q ℓ : ℕ)
    (hℓ : 1 ≤ ℓ) (a : ι → ℤ) :
    (scaleVec ℓ a ∈ latMod c Q ↔ a ∈ latMod c (Q / Nat.gcd ℓ Q)) := by
  have hscale : Fintype.linearCombination ℤ c (scaleVec ℓ a)
      = (ℓ : ℤ) * Fintype.linearCombination ℤ c a := by
    simp only [Fintype.linearCombination_apply, scaleVec, smul_eq_mul]
    rw [Finset.mul_sum]
    apply Finset.sum_congr rfl
    intro i _
    ring
  rw [mem_latMod_iff_L, mem_latMod_iff_L, hscale]
  exact int_dvd_mul_iff_div_gcd_dvd Q ℓ (Fintype.linearCombination ℤ c a) hℓ

private lemma gamLoc_scaleVec_iff (d n : ℕ) [DecidableEq (Mon d n)] (x y : Fin (n + 1) → ℤ)
    (Q ℓ : ℕ) (hℓ : 1 ≤ ℓ) (a : Mon d n → ℤ) :
    (scaleVec ℓ a ∈ GamLoc d n x y Q ↔ a ∈ GamLoc d n x y (Q / Nat.gcd ℓ Q)) := by
  simp only [GamLoc, Submodule.mem_inf]
  rw [latMod_scaleVec_iff (veronese d n x) Q ℓ hℓ a,
      latMod_scaleVec_iff (veronese d n y) Q ℓ hℓ a]

private lemma tlocSet_scaleVec_iff (d n : ℕ) (x y : Fin (n + 1) → ℤ) (A α : ℝ) (ℓ : ℕ)
    (hℓ : 1 ≤ ℓ) (a : Mon d n → ℤ) :
    (a ∈ TlocSet d n x y (A / (ℓ : ℝ)) α ↔ scaleVec ℓ a ∈ TlocSet d n x y A α) := by
  obtain ⟨hscale_norm, hscale_toR, hCgam_smul, -, -⟩ := MobScaleVec (ι := Mon d n)
  have hℓ0 : (0 : ℝ) < (ℓ : ℝ) := by exact_mod_cast hℓ
  simp only [TlocSet, Set.mem_ofPred_eq]
  rw [hscale_norm, hscale_toR,
    hCgam_smul (toR (veronese d n x)) (toR a) α (ℓ : ℝ) hℓ0,
    hCgam_smul (toR (veronese d n y)) (toR a) α (ℓ : ℝ) hℓ0]
  constructor
  · rintro ⟨h1, h2, h3⟩
    exact ⟨by rw [le_div_iff₀ hℓ0] at h1; linarith, h2, h3⟩
  · rintro ⟨h1, h2, h3⟩
    exact ⟨by rw [le_div_iff₀ hℓ0]; linarith, h2, h3⟩

theorem SstarMobiusLoc (d n : ℕ) [DecidableEq (Mon d n)] (x y : Fin (n + 1) → ℤ)
    (k : ℕ) (A α : ℝ) (Q : ℕ) (hQ : 1 ≤ Q) (hA : 1 ≤ A) :
    Sstar d n k (GamLoc d n x y Q) (TlocSet d n x y A α) =
      ∑ ℓ ∈ Finset.Icc 1 ⌊A⌋₊,
        ((ArithmeticFunction.moebius ℓ : ℝ) / (ℓ : ℝ) ^ k) *
          Sk d n k (GamLoc d n x y (Q / Nat.gcd ℓ Q)) (TlocSet d n x y (A / ℓ) α) := by
  simp only [Sstar, Sk]
  exact Sstar_moebius_abstract (ι := Mon d n) k A hA (↑(GamLoc d n x y Q))
    (TlocSet d n x y A α) (fun ℓ => ↑(GamLoc d n x y (Q / Nat.gcd ℓ Q)))
    (fun ℓ => TlocSet d n x y (A / (ℓ : ℝ)) α)
    (fun ℓ hℓ b => (gamLoc_scaleVec_iff d n x y Q ℓ hℓ b).symm)
    (fun ℓ hℓ b => tlocSet_scaleVec_iff d n x y A α ℓ hℓ b)
    (fun a ha => ha.1)

end Work.HP
