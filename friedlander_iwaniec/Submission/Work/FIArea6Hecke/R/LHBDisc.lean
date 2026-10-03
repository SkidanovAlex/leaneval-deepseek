import Mathlib
import Submission.Work.FIArea6Hecke.R.DiscDefs
import Submission.Work.FIArea6Hecke.R.sum_eq_classSum
import Submission.Work.FIArea6Hecke.R.classCount_eq_shiftCount
import Submission.Commons.NumberTheory.Diophantine.lattice_disk_count_bound
import Submission.Work.FIArea6Hecke.R.classCount_discrepancy_sqrt
import Submission.Work.FIArea6Hecke.R.discSum_trivial_bound
import Submission.Work.FIPlan.Interface
import Submission.Work.FIArea5.S16Hecke.ThetaDefs
import Submission.Work.FIArea6Hecke.R.HeckeDiscRed
import Submission.Work.FIArea5.S16Hecke.primaryAux

namespace Work.FIArea6Hecke.R

open Finset
open scoped BigOperators

attribute [local instance] Classical.propDecidable

noncomputable section

/-! ## Coordinatewise reduction modulo `n` -/

/-- Coordinatewise reduction of a Gaussian integer modulo `n`. -/
def redModD (n : ℤ) (z : GaussianInt) : GaussianInt := ⟨z.re % n, z.im % n⟩

lemma redModD_re_nonneg {n : ℤ} (hn : 0 < n) (z : GaussianInt) : 0 ≤ (redModD n z).re :=
  Int.emod_nonneg _ hn.ne'

lemma redModD_re_lt {n : ℤ} (hn : 0 < n) (z : GaussianInt) : (redModD n z).re < n :=
  Int.emod_lt_of_pos _ hn

lemma redModD_im_nonneg {n : ℤ} (hn : 0 < n) (z : GaussianInt) : 0 ≤ (redModD n z).im :=
  Int.emod_nonneg _ hn.ne'

lemma redModD_im_lt {n : ℤ} (hn : 0 < n) (z : GaussianInt) : (redModD n z).im < n :=
  Int.emod_lt_of_pos _ hn

lemma sub_redModD_re (n : ℤ) (z : GaussianInt) : z.re - (redModD n z).re = n * (z.re / n) := by
  have h := Int.emod_add_mul_ediv z.re n
  simp only [redModD]
  linarith

lemma sub_redModD_im (n : ℤ) (z : GaussianInt) : z.im - (redModD n z).im = n * (z.im / n) := by
  have h := Int.emod_add_mul_ediv z.im n
  simp only [redModD]
  linarith

lemma intCast_mul_re (n : ℤ) (k : GaussianInt) : ((n : GaussianInt) * k).re = n * k.re := by
  obtain ⟨a, b⟩ := k
  simp

lemma intCast_mul_im (n : ℤ) (k : GaussianInt) : ((n : GaussianInt) * k).im = n * k.im := by
  obtain ⟨a, b⟩ := k
  simp

lemma dvd_sub_redModD (n : ℤ) (z : GaussianInt) :
    (n : GaussianInt) ∣ (z - redModD n z) := by
  refine ⟨⟨z.re / n, z.im / n⟩, ?_⟩
  ext
  · rw [Zsqrtd.re_sub, intCast_mul_re, sub_redModD_re]
  · rw [Zsqrtd.im_sub, intCast_mul_im, sub_redModD_im]

lemma dvd_redModD_sub (n : ℤ) (z : GaussianInt) :
    (n : GaussianInt) ∣ (redModD n z - z) := by
  rw [show redModD n z - z = -(z - redModD n z) by ring]
  exact dvd_neg.mpr (dvd_sub_redModD n z)

lemma redModD_eq_self {n : ℤ} (_hn : 0 < n) {z : GaussianInt}
    (h1 : 0 ≤ z.re) (h2 : z.re < n) (h3 : 0 ≤ z.im) (h4 : z.im < n) : redModD n z = z := by
  ext
  · exact Int.emod_eq_of_lt h1 h2
  · exact Int.emod_eq_of_lt h3 h4

lemma isPrimary_redModD {n : ℤ} (hn : 0 < n) (h4d : (4 : ℤ) ∣ n) (z : GaussianInt) :
    Work.FIPlan.IsPrimary (redModD n z) ↔ Work.FIPlan.IsPrimary z := by
  have hre : z.re = (redModD n z).re + n * (z.re / n) := by
    have h := sub_redModD_re n z; linarith
  have him : z.im = (redModD n z).im + n * (z.im / n) := by
    have h := sub_redModD_im n z; linarith
  have hne : Even n := by obtain ⟨k, hk⟩ := h4d; exact ⟨2 * k, by omega⟩
  have hodd : Odd z.re ↔ Odd (redModD n z).re := by
    rw [hre]
    exact ⟨fun h => by simpa using h.sub_even (hne.mul_right (z.re / n)),
           fun h => h.add_even (hne.mul_right (z.re / n))⟩
  have heven : Even z.im ↔ Even (redModD n z).im := by
    rw [him]
    exact ⟨fun h => by simpa using h.sub (hne.mul_right (z.im / n)),
           fun h => h.add (hne.mul_right (z.im / n))⟩
  have h1 : z.im ≡ (redModD n z).im [ZMOD 4] := by
    rw [him]
    simpa using Int.ModEq.add (Int.ModEq.refl (redModD n z).im)
      (Int.modEq_zero_iff_dvd.mpr (dvd_mul_of_dvd_left h4d (z.im / n)))
  have h2 : z.re - 1 ≡ (redModD n z).re - 1 [ZMOD 4] := by
    rw [hre, show (redModD n z).re + n * (z.re / n) - 1
        = ((redModD n z).re - 1) + n * (z.re / n) by ring]
    simpa using Int.ModEq.add (Int.ModEq.refl ((redModD n z).re - 1))
      (Int.modEq_zero_iff_dvd.mpr (dvd_mul_of_dvd_left h4d (z.re / n)))
  have hmod : (z.im ≡ z.re - 1 [ZMOD 4]) ↔
      ((redModD n z).im ≡ (redModD n z).re - 1 [ZMOD 4]) := by
    constructor
    · intro h; exact h1.symm.trans (h.trans h2)
    · intro h; exact h1.trans (h.trans h2.symm)
  rw [Work.FIPlan.IsPrimary, Work.FIPlan.IsPrimary, hodd, heven, hmod]

lemma mem_gsBox_iffD {N : ℕ} {z : GaussianInt} :
    z ∈ gsBox N ↔ 0 ≤ z.re ∧ z.re < (N : ℤ) ∧ 0 ≤ z.im ∧ z.im < (N : ℤ) := by
  rw [gsBox, Finset.mem_image]
  constructor
  · rintro ⟨p, hp, hpz⟩
    rw [Finset.product_eq_sprod, Finset.mem_product, Finset.mem_range, Finset.mem_range] at hp
    obtain ⟨hp1, hp2⟩ := hp
    rw [← hpz]
    refine ⟨?_, ?_, ?_, ?_⟩
    · show (0 : ℤ) ≤ (p.1 : ℤ); exact Int.natCast_nonneg _
    · show (p.1 : ℤ) < (N : ℤ); exact_mod_cast hp1
    · show (0 : ℤ) ≤ (p.2 : ℤ); exact Int.natCast_nonneg _
    · show (p.2 : ℤ) < (N : ℤ); exact_mod_cast hp2
  · rintro ⟨h1, h2, h3, h4⟩
    refine ⟨(z.re.toNat, z.im.toNat), ?_, ?_⟩
    · rw [Finset.product_eq_sprod, Finset.mem_product, Finset.mem_range, Finset.mem_range]
      exact ⟨by omega, by omega⟩
    · ext <;> simp [h1, h3]

lemma redModD_mem_gsBox {N : ℕ} (hN : 0 < N) (z : GaussianInt) :
    redModD (N : ℤ) z ∈ gsBox N := by
  rw [mem_gsBox_iffD]
  have hN' : (0 : ℤ) < (N : ℤ) := by exact_mod_cast hN
  exact ⟨redModD_re_nonneg hN' z, redModD_re_lt hN' z, redModD_im_nonneg hN' z,
    redModD_im_lt hN' z⟩

lemma chi_redModD {d : ℕ} {chi : GaussianInt → ℂ}
    (hchi : Work.FIArea5.S16Hecke.IsCharMod4dStrict d chi) (z : GaussianInt) :
    chi (redModD (((4 * d : ℕ) : ℤ)) z) = chi z :=
  hchi.1.2.2.2.1 _ _ (by simpa using dvd_redModD_sub (((4 * d : ℕ) : ℤ)) z)

lemma isUnitMod4d_redModD {d : ℕ} (z : GaussianInt) :
    Work.FIArea5.S16Hecke.IsUnitMod4d d (redModD (((4 * d : ℕ) : ℤ)) z) ↔
    Work.FIArea5.S16Hecke.IsUnitMod4d d z := by
  have hz1 : ((((4 * d : ℕ) : ℤ)) : GaussianInt) ∣ (z - redModD (((4 * d : ℕ) : ℤ)) z) :=
    dvd_sub_redModD _ z
  have hz2 : ((((4 * d : ℕ) : ℤ)) : GaussianInt) ∣ (redModD (((4 * d : ℕ) : ℤ)) z - z) :=
    dvd_redModD_sub _ z
  constructor
  · rintro ⟨w, hw⟩
    refine ⟨w, ?_⟩
    rw [show z * w - 1 = (redModD (((4 * d : ℕ) : ℤ)) z * w - 1)
        + (z - redModD (((4 * d : ℕ) : ℤ)) z) * w by ring]
    exact dvd_add hw (dvd_mul_of_dvd_left hz1 w)
  · rintro ⟨w, hw⟩
    refine ⟨w, ?_⟩
    rw [show redModD (((4 * d : ℕ) : ℤ)) z * w - 1 = (z * w - 1)
        + (redModD (((4 * d : ℕ) : ℤ)) z - z) * w by ring]
    exact dvd_add hw (dvd_mul_of_dvd_left hz2 w)

lemma isUnitMod4d_one' (d : ℕ) : Work.FIArea5.S16Hecke.IsUnitMod4d d (1 : GaussianInt) :=
  ⟨1, by rw [one_mul, sub_self]; exact dvd_zero _⟩

theorem PsetSumZero {d : ℕ} (hd : 1 ≤ d) {chi : GaussianInt → ℂ}
    (hchi : Work.FIArea5.S16Hecke.IsCharMod4dStrict d chi) {u : GaussianInt}
    (hup : Work.FIPlan.IsPrimary u) (huu : Work.FIArea5.S16Hecke.IsUnitMod4d d u)
    (huc : chi u ≠ 1) : ∑ p ∈ Pset d, chi p = 0 := by
  classical
  set n : ℤ := ((4 * d : ℕ) : ℤ) with hn
  have hn4 : n = 4 * (d : ℤ) := by rw [hn]; push_cast; ring
  have hn0 : 0 < n := by omega
  have h4 : (4 : ℤ) ∣ n := ⟨(d : ℤ), by omega⟩
  set φ : GaussianInt → GaussianInt := fun p => redModD n (u * p) with hφdef
  have hφmem : ∀ p ∈ Pset d, φ p ∈ Pset d := by
    intro p hp
    obtain ⟨hpbox, hpprim⟩ := Finset.mem_filter.mp (by simpa [Pset] using hp)
    rw [Pset, Finset.mem_filter]
    refine ⟨?_, ?_⟩
    · rw [hφdef]; exact redModD_mem_gsBox (by omega) (u * p)
    · rw [hφdef, isPrimary_redModD hn0 h4]
      exact Work.FIArea5.S16Hecke.isPrimary_mul hup hpprim
  have hφinj : ∀ p ∈ Pset d, ∀ q ∈ Pset d, φ p = φ q → p = q := by
    intro p hp q hq heq
    have hpbox : 0 ≤ p.re ∧ p.re < n ∧ 0 ≤ p.im ∧ p.im < n := by
      have h := (Finset.mem_filter.mp (by simpa [Pset] using hp)).1
      rwa [mem_gsBox_iffD] at h
    have hqbox : 0 ≤ q.re ∧ q.re < n ∧ 0 ≤ q.im ∧ q.im < n := by
      have h := (Finset.mem_filter.mp (by simpa [Pset] using hq)).1
      rwa [mem_gsBox_iffD] at h
    have hdvd1 : (n : GaussianInt) ∣ (u * (p - q)) := by
      have ha := dvd_sub_redModD n (u * p)
      have hb := dvd_redModD_sub n (u * q)
      have heq' : redModD n (u * p) = redModD n (u * q) := heq
      rw [show u * (p - q) = (u * p - redModD n (u * p)) + (redModD n (u * q) - u * q) by
        rw [heq']; ring]
      exact dvd_add ha hb
    obtain ⟨w, hw⟩ := huu
    have hdvd2 : (n : GaussianInt) ∣ (p - q) := by
      have h : p - q = w * (u * (p - q)) - (p - q) * (u * w - 1) := by ring
      rw [h]
      exact dvd_sub (dvd_mul_of_dvd_right hdvd1 w) (dvd_mul_of_dvd_right hw (p - q))
    obtain ⟨k, hk⟩ := hdvd2
    have hre : p.re = q.re := by
      have h2 : p.re - q.re = n * k.re := by
        have h := congrArg Zsqrtd.re hk
        rw [Zsqrtd.re_sub, intCast_mul_re] at h
        exact h
      have hmod : p.re % n = q.re % n :=
        Int.modEq_iff_dvd.mpr ⟨-k.re, by linarith [h2]⟩
      have h1 : p.re % n = p.re := Int.emod_eq_of_lt hpbox.1 hpbox.2.1
      have h2' : q.re % n = q.re := Int.emod_eq_of_lt hqbox.1 hqbox.2.1
      linarith [hmod, h1, h2']
    have him : p.im = q.im := by
      have h2 : p.im - q.im = n * k.im := by
        have h := congrArg Zsqrtd.im hk
        rw [Zsqrtd.im_sub, intCast_mul_im] at h
        exact h
      have hmod : p.im % n = q.im % n :=
        Int.modEq_iff_dvd.mpr ⟨-k.im, by linarith [h2]⟩
      have h1 : p.im % n = p.im := Int.emod_eq_of_lt hpbox.2.2.1 hpbox.2.2.2
      have h2' : q.im % n = q.im := Int.emod_eq_of_lt hqbox.2.2.1 hqbox.2.2.2
      linarith [hmod, h1, h2']
    ext <;> assumption
  have himg : (Pset d).image φ = Pset d := by
    apply Finset.eq_of_subset_of_card_le
    · rintro z hz
      rw [Finset.mem_image] at hz
      obtain ⟨p, hp, rfl⟩ := hz
      exact hφmem p hp
    · rw [Finset.card_image_of_injOn (fun a ha b hb hab => hφinj a ha b hb hab)]
  have hsum1 : (∑ p ∈ Pset d, chi p) = ∑ p ∈ Pset d, chi (φ p) := by
    conv_lhs => rw [← himg]
    rw [Finset.sum_image (fun a ha b hb hab => hφinj a ha b hb hab)]
  have hsum2 : (∑ p ∈ Pset d, chi (φ p)) = chi u * ∑ p ∈ Pset d, chi p := by
    rw [Finset.mul_sum]
    refine Finset.sum_congr rfl (fun p hp => ?_)
    rw [hφdef]
    simp only
    rw [chi_redModD hchi, hchi.1.2.1]
  have hS : (∑ p ∈ Pset d, chi p) = chi u * ∑ p ∈ Pset d, chi p := hsum1.trans hsum2
  have hS' : (1 - chi u) * (∑ p ∈ Pset d, chi p) = 0 := by linear_combination hS
  rcases mul_eq_zero.mp hS' with h | h
  · exact absurd (sub_eq_zero.mp h) huc.symm
  · exact h

theorem discSum_mean0_bound :
    ∃ C : ℝ, 0 < C ∧ ∀ (d : ℕ) (hd : 1 ≤ d) (chi : GaussianInt → ℂ),
      Work.FIArea5.S16Hecke.IsCharMod4dStrict d chi →
      (∑ p ∈ Pset d, chi p) = 0 →
      ∀ X : ℝ, 1 ≤ X → ‖discSum X chi‖ ≤ C * (d : ℝ) * Real.sqrt X := by
  classical
  obtain ⟨C₁, hC₁pos, hC₁⟩ := classCount_discrepancy_sqrt
  obtain ⟨C₂, hC₂pos, hC₂⟩ := discSum_trivial_bound
  refine ⟨4 * C₁ + 4 * C₂ + 1, by positivity, ?_⟩
  intro d hd chi hchi hmeanP X hX
  have hchi1 : ∀ z : GaussianInt, ‖chi z‖ ≤ 1 := hchi.1.2.2.1
  have hd0 : (0 : ℝ) < (d : ℝ) := by exact_mod_cast hd
  have hsqrtX0 : 0 ≤ Real.sqrt X := Real.sqrt_nonneg X
  have hPcard : ((Pset d).card : ℝ) ≤ 16 * (d : ℝ) ^ 2 := by
    have h1 : (Pset d).card ≤ (gsBox (4 * d)).card :=
      Finset.card_le_card (Finset.filter_subset _ _)
    have h2 : (gsBox (4 * d)).card ≤ (4 * d) * (4 * d) := by
      refine le_trans (Finset.card_image_le) ?_
      simp [Finset.card_product]
    have h3 : ((4 * d) * (4 * d) : ℕ) = 16 * d ^ 2 := by ring
    have h4 : (Pset d).card ≤ 16 * d ^ 2 := by
      calc (Pset d).card ≤ (gsBox (4 * d)).card := h1
        _ ≤ (4 * d) * (4 * d) := h2
        _ = 16 * d ^ 2 := h3
    calc ((Pset d).card : ℝ) ≤ ((16 * d ^ 2 : ℕ) : ℝ) := by exact_mod_cast h4
      _ = 16 * (d : ℝ) ^ 2 := by push_cast; ring
  by_cases hXbig : 16 * (d : ℝ) ^ 2 ≤ X
  · set A : ℝ := Real.pi * (X / (16 * (d : ℝ) ^ 2)) with hA
    have hsplit : (∑ p ∈ Pset d, chi p * ((classCount d p X : ℕ) : ℂ))
        = ∑ p ∈ Pset d, chi p * ((((classCount d p X : ℝ) - A : ℝ)) : ℂ) := by
      have hzero : (∑ p ∈ Pset d, chi p * ((A : ℝ) : ℂ)) = 0 := by
        rw [← Finset.sum_mul, hmeanP, zero_mul]
      have hexp : ∀ p : GaussianInt, chi p * ((classCount d p X : ℕ) : ℂ)
          = chi p * ((((classCount d p X : ℝ) - A : ℝ)) : ℂ) + chi p * ((A : ℝ) : ℂ) := by
        intro p
        have hc : ((classCount d p X : ℕ) : ℂ)
            = ((((classCount d p X : ℝ) - A : ℝ)) : ℂ) + ((A : ℝ) : ℂ) := by
          push_cast
          ring
        rw [hc]; ring
      calc (∑ p ∈ Pset d, chi p * ((classCount d p X : ℕ) : ℂ))
          = ∑ p ∈ Pset d, (chi p * ((((classCount d p X : ℝ) - A : ℝ)) : ℂ)
              + chi p * ((A : ℝ) : ℂ)) := Finset.sum_congr rfl (fun p _ => hexp p)
        _ = (∑ p ∈ Pset d, chi p * ((((classCount d p X : ℝ) - A : ℝ)) : ℂ))
              + (∑ p ∈ Pset d, chi p * ((A : ℝ) : ℂ)) := Finset.sum_add_distrib
        _ = ∑ p ∈ Pset d, chi p * ((((classCount d p X : ℝ) - A : ℝ)) : ℂ) := by
              rw [hzero, add_zero]
    rw [sum_eq_classSum hd hchi hX, hsplit]
    have hbound : ‖∑ p ∈ Pset d, chi p * ((((classCount d p X : ℝ) - A : ℝ)) : ℂ)‖
        ≤ 4 * C₁ * (d : ℝ) * Real.sqrt X := by
      calc ‖∑ p ∈ Pset d, chi p * ((((classCount d p X : ℝ) - A : ℝ)) : ℂ)‖
          ≤ ∑ p ∈ Pset d, ‖chi p * ((((classCount d p X : ℝ) - A : ℝ)) : ℂ)‖ := norm_sum_le _ _
        _ ≤ ∑ _p ∈ Pset d, C₁ * (Real.sqrt X / (4 * (d : ℝ))) := by
            refine Finset.sum_le_sum (fun p _ => ?_)
            rw [norm_mul, Complex.norm_real, Real.norm_eq_abs]
            calc ‖chi p‖ * |(classCount d p X : ℝ) - A|
                ≤ 1 * (C₁ * (Real.sqrt X / (4 * (d : ℝ)))) := by
                  refine mul_le_mul (hchi1 p) ?_ (abs_nonneg _) (by norm_num)
                  rw [hA]
                  exact hC₁ d hd p X hXbig
              _ = C₁ * (Real.sqrt X / (4 * (d : ℝ))) := by ring
        _ = ((Pset d).card : ℝ) * (C₁ * (Real.sqrt X / (4 * (d : ℝ)))) := by
            rw [Finset.sum_const, nsmul_eq_mul]
        _ ≤ (16 * (d : ℝ) ^ 2) * (C₁ * (Real.sqrt X / (4 * (d : ℝ)))) :=
            mul_le_mul_of_nonneg_right hPcard (by positivity)
        _ = 4 * C₁ * (d : ℝ) * Real.sqrt X := by
            field_simp
            ring
    have hdX : (0 : ℝ) ≤ (d : ℝ) * Real.sqrt X := mul_nonneg hd0.le hsqrtX0
    calc ‖∑ p ∈ Pset d, chi p * ((((classCount d p X : ℝ) - A : ℝ)) : ℂ)‖
        ≤ 4 * C₁ * (d : ℝ) * Real.sqrt X := hbound
      _ = 4 * C₁ * ((d : ℝ) * Real.sqrt X) := by ring
      _ ≤ (4 * C₁ + 4 * C₂ + 1) * ((d : ℝ) * Real.sqrt X) :=
          mul_le_mul_of_nonneg_right (by linarith [hC₂pos]) hdX
      _ = (4 * C₁ + 4 * C₂ + 1) * (d : ℝ) * Real.sqrt X := by ring
  · have hXlt : X < 16 * (d : ℝ) ^ 2 := not_le.mp hXbig
    have hX0 : (0 : ℝ) ≤ X := by linarith
    have htriv : ‖discSum X chi‖ ≤ C₂ * X := hC₂ chi hchi1 X hX
    have hsqrtX_le : Real.sqrt X ≤ 4 * (d : ℝ) := by
      have h : X ≤ (4 * (d : ℝ)) ^ 2 := by nlinarith [hXlt]
      calc Real.sqrt X ≤ Real.sqrt ((4 * (d : ℝ)) ^ 2) := Real.sqrt_le_sqrt h
        _ = 4 * (d : ℝ) := Real.sqrt_sq (by positivity)
    have hXle : X ≤ 4 * (d : ℝ) * Real.sqrt X := by
      calc X = Real.sqrt X * Real.sqrt X := (Real.mul_self_sqrt hX0).symm
        _ ≤ (4 * (d : ℝ)) * Real.sqrt X := mul_le_mul_of_nonneg_right hsqrtX_le hsqrtX0
    have hdX : (0 : ℝ) ≤ (d : ℝ) * Real.sqrt X := mul_nonneg hd0.le hsqrtX0
    calc ‖discSum X chi‖ ≤ C₂ * X := htriv
      _ ≤ C₂ * (4 * (d : ℝ) * Real.sqrt X) := mul_le_mul_of_nonneg_left hXle hC₂pos.le
      _ = 4 * C₂ * ((d : ℝ) * Real.sqrt X) := by ring
      _ ≤ (4 * C₁ + 4 * C₂ + 1) * ((d : ℝ) * Real.sqrt X) :=
          mul_le_mul_of_nonneg_right (by linarith [hC₁pos]) hdX
      _ = (4 * C₁ + 4 * C₂ + 1) * (d : ℝ) * Real.sqrt X := by ring

/-- **Mean-zero primary disc sum: square-root cancellation.**  For a strict character `χ` of
modulus `4d` which is nontrivial on the primary units mod `4d`, the primary disc sum
`discSum X chi = ∑_{z primary, |z|² ≤ X} χ(z)` (the `DiscDefs.discSum`, a sum over `gBox ⌈X⌉₊`)
satisfies `‖discSum X chi‖ ≤ C d √X` for all `X ≥ 1`, with `C` an absolute constant.

Proof route (inputs already in the workspace):

1. The nontriviality on the primary units forces `∑_{p ∈ Pset d} chi p = 0`.  This is
   `Pset_sum_eq_zero`, proved in `Submission/Work/FIArea6Hecke/R/heckeDiscSum_bound.lean` — but that
   file does NOT compile (duplicate declaration `mem_gsBox_iff` clashing with
   `R/hmean_eq_Pset_sum.lean`; and it imports the sorry-containing `discDiscrepancy_saving`), so
   reproduce it here together with its private helpers (`redMod`, `redMod_mem_gsBox`,
   `isPrimary_redMod`, `dvd_sub_redMod`, `dvd_redMod_sub`, `chi_redMod`, `isUnitMod4d_redMod`,
   `mem_gsBox_iff`, ...) under fresh names.
2. `sum_eq_classSum hd hchi hX` writes `discSum X chi = ∑_{p ∈ Pset d} chi p * classCount d p X`
   (note `discSum` here is the `DiscDefs` sum over `gBox ⌈X⌉₊`).  Since `∑_p chi p = 0`, splitting
   `classCount d p X = π R² + (classCount d p X - π R²)` with `R = √X/(4d)` kills the main term.
3. `classCount d p X = πR² + O(R)` uniformly in `p`: `classCount_eq_shiftCount` plus
   `Commons.NumberTheory.Diophantine.lattice_disk_count_bound` (the file
   `R/classCount_discrepancy_sqrt.lean` does not compile — a `Real.sqrt_sq` typo at line 30 — so
   reproduce its argument here).  With `#(Pset d) ≤ 16 d²` this gives
   `‖discSum X chi‖ ≤ C' · 16 d² · √X/(4d) = 4 C' d √X` for `X ≥ 16 d²`.
4. For `X ≤ 16 d²` (i.e. `√X ≤ 4d`): `‖discSum X chi‖ ≤ #{z ∈ gBox ⌈X⌉₊ : gnorm z ≤ X} ≤ 9X`
   (the disc of radius `√X` has `≤ (2√X+1)² ≤ 9X` lattice points), and `X = √X·√X ≤ 4d√X`, so
   `‖discSum X chi‖ ≤ 36 d √X`. -/
theorem LHBDisc :
    ∃ C : ℝ, 0 < C ∧
      ∀ (d : ℕ) (hd : 1 ≤ d) (chi : GaussianInt → ℂ),
        Work.FIArea5.S16Hecke.IsCharMod4dStrict d chi →
        (∃ z : GaussianInt, Work.FIPlan.IsPrimary z ∧
          Work.FIArea5.S16Hecke.IsUnitMod4d d z ∧ chi z ≠ 1) →
        ∀ X : ℝ, 1 ≤ X →
          ‖Work.FIArea6Hecke.R.discSum X chi‖ ≤ C * (d : ℝ) * Real.sqrt X := by
  obtain ⟨C, hCpos, hC⟩ := discSum_mean0_bound
  refine ⟨C, hCpos, ?_⟩
  intro d hd chi hchi hntriv X hX
  obtain ⟨z, hzp, hzu, hzc⟩ := hntriv
  exact hC d hd chi hchi (PsetSumZero hd hchi hzp hzu hzc) X hX

end

end Work.FIArea6Hecke.R
