import Mathlib
import Submission.Work.FIArea7.KSDefs
import Submission.Work.FIArea7.KInner_bound
import Submission.Work.FIArea7.twoChar_pv_dilated
import Submission.Work.FIArea7.jacobiSym_dilation
import Submission.Work.FIArea7.multEps_step
import Submission.Work.FIArea7.sector_diff_le
import Submission.Work.FIArea7.exists_omega

open Finset
namespace Work.FIArea7

lemma Icc_filter_le (X Y t : ℤ) :
    (Finset.Icc X Y).filter (fun u => u ≤ t) = Finset.Icc X (min Y t) := by
  ext u; simp only [Finset.mem_filter, Finset.mem_Icc]; omega

lemma Icc_filter_lt (X Y t : ℤ) :
    (Finset.Icc X Y).filter (fun u => ¬ (u ≤ t)) = Finset.Icc (max X (t+1)) Y := by
  ext u; simp only [Finset.mem_filter, Finset.mem_Icc]; omega

lemma toNat_sub_le_card_Icc (X Y : ℤ) : (Y - X).toNat ≤ (Finset.Icc X Y).card := by
  rw [Int.card_Icc]; exact Int.toNat_le_toNat (by omega)

lemma odd_gnorm_of_isPrimary (w : GaussianInt) (hw : Work.FIPlan.IsPrimary w) :
    Odd (Work.FIPlan.gnorm w) := by
  have hodd : Odd (w.re ^ 2 + w.im ^ 2) := by
    obtain ⟨a, ha⟩ := hw.1
    obtain ⟨b, hb⟩ := hw.2.1
    refine ⟨2*a^2 + 2*a + 2*b^2, ?_⟩
    rw [ha, hb]; ring
  have hcast : ((Work.FIPlan.gnorm w : ℕ) : ℤ) = w.re ^ 2 + w.im ^ 2 := norm_eq w
  have hoddZ : Odd ((Work.FIPlan.gnorm w : ℕ) : ℤ) := by rw [hcast]; exact hodd
  exact_mod_cast hoddZ

lemma norm_gunitC (z : GaussianInt) (hz : z ≠ 0) : ‖gunitC z‖ = 1 := by
  rw [gunitC, norm_div, Complex.norm_real, Real.norm_of_nonneg (norm_nonneg (z : ℂ))]
  have hzc : (z : ℂ) ≠ 0 := fun hh => hz (GaussianInt.toComplex_injective (by simpa using hh))
  exact div_self (ne_of_gt (norm_pos_iff.mpr hzc))

lemma norm_gunitC_zpow (z : GaussianInt) (hz : z ≠ 0) (k : ℤ) : ‖gunitC z ^ k‖ = 1 := by
  rw [norm_zpow, norm_gunitC z hz, one_zpow]

end Work.FIArea7

namespace Work.FIArea7

lemma single_class_bound
    (C0 : ℝ) (hC0 : 0 < C0)
    (h2char : ∀ (m₁ m₂ : ℕ) (hm₁ : Odd m₁) (hm₂ : Odd m₂) (hcop : Nat.Coprime m₁ m₂)
      (hgood : ∃ p : ℕ, p.Prime ∧ Odd (m₁.factorization p))
      (c₁ c₂ X Y : ℤ) (φ : ℤ → ℂ) (M D : ℝ),
      (∀ u : ℤ, ‖φ u‖ ≤ M) → (∀ u : ℤ, ‖φ (u + 1) - φ u‖ ≤ D) →
      ‖∑ u ∈ Finset.Icc X Y, (jacobiSym (u + c₁) m₁ : ℂ) * (jacobiSym (u + c₂) m₂ : ℂ) * φ u‖
        ≤ C0 * (M + ((Y - X).toNat : ℝ) * D) * Real.sqrt ((m₁ : ℝ) * (m₂ : ℝ))
            * (Real.log (2 + (m₁ : ℝ) * (m₂ : ℝ)) + 1))
    (w : GaussianInt) (k Az r c : ℤ) (m₁ m₂ : ℕ) (c₁ c₂ X Y : ℤ)
    (hr : r ≠ 0) (hm₁ : Odd m₁) (hm₂ : Odd m₂) (hcop : Nat.Coprime m₁ m₂)
    (hgood : ∃ p : ℕ, p.Prime ∧ Odd (m₁.factorization p)) :
    ‖∑ u ∈ Finset.Icc X Y, gunitC (⟨r, c + Az * u⟩ : GaussianInt) ^ k
        * (MultEps w (⟨r, c + Az * u⟩ : GaussianInt) : ℂ)
        * (jacobiSym (u + c₁) m₁ : ℂ) * (jacobiSym (u + c₂) m₂ : ℂ)‖
      ≤ C0 * (2 + 2 * ((Y - X).toNat : ℝ) * (|(k : ℝ)| * 2 * |(Az : ℝ)| / |(r : ℝ)|))
          * Real.sqrt ((m₁ : ℝ) * (m₂ : ℝ)) * (Real.log (2 + (m₁ : ℝ) * (m₂ : ℝ)) + 1) := by
  set D : ℝ := |(k : ℝ)| * 2 * |(Az : ℝ)| / |(r : ℝ)| with hDdef
  obtain ⟨t, ht⟩ := multEps_step w r c Az
  set ε₁ : ℤ := MultEps w (⟨r, c + Az * t⟩ : GaussianInt) with hε₁
  set ε₂ : ℤ := MultEps w (⟨r, c + Az * (t + 1)⟩ : GaussianInt) with hε₂
  have hnormε₁ : ‖(ε₁ : ℂ)‖ = 1 := by
    rw [hε₁]
    rcases multEps_eq_pm_one w (⟨r, c + Az * t⟩ : GaussianInt) with h | h <;> rw [h] <;> simp
  have hnormε₂ : ‖(ε₂ : ℂ)‖ = 1 := by
    rw [hε₂]
    rcases multEps_eq_pm_one w (⟨r, c + Az * (t + 1)⟩ : GaussianInt) with h | h <;> rw [h] <;> simp
  have hzr : ∀ u : ℤ, (⟨r, c + Az * u⟩ : GaussianInt) ≠ 0 := by
    intro u h; exact hr (by simpa using congrArg Zsqrtd.re h)
  have hφ₁norm : ∀ u : ℤ, ‖gunitC (⟨r, c + Az * u⟩ : GaussianInt) ^ k * (ε₁ : ℂ)‖ ≤ (1:ℝ) := by
    intro u; rw [norm_mul, norm_gunitC_zpow _ (hzr u) k, hnormε₁, mul_one]
  have hφ₁diff : ∀ u : ℤ,
      ‖gunitC (⟨r, c + Az * (u+1)⟩ : GaussianInt) ^ k * (ε₁ : ℂ)
        - gunitC (⟨r, c + Az * u⟩ : GaussianInt) ^ k * (ε₁ : ℂ)‖ ≤ D := by
    intro u
    have hsd := sector_diff_le r c Az k hr u
    rw [show gunitC (⟨r, c + Az * (u+1)⟩ : GaussianInt) ^ k * (ε₁ : ℂ)
          - gunitC (⟨r, c + Az * u⟩ : GaussianInt) ^ k * (ε₁ : ℂ)
        = (ε₁ : ℂ) * (gunitC (⟨r, c + Az * (u+1)⟩ : GaussianInt) ^ k
            - gunitC (⟨r, c + Az * u⟩ : GaussianInt) ^ k) by ring,
      norm_mul, hnormε₁, one_mul]
    refine le_trans hsd ?_
    rw [hDdef]; ring_nf; norm_num
  have hφ₂norm : ∀ u : ℤ, ‖gunitC (⟨r, c + Az * u⟩ : GaussianInt) ^ k * (ε₂ : ℂ)‖ ≤ (1:ℝ) := by
    intro u; rw [norm_mul, norm_gunitC_zpow _ (hzr u) k, hnormε₂, mul_one]
  have hφ₂diff : ∀ u : ℤ,
      ‖gunitC (⟨r, c + Az * (u+1)⟩ : GaussianInt) ^ k * (ε₂ : ℂ)
        - gunitC (⟨r, c + Az * u⟩ : GaussianInt) ^ k * (ε₂ : ℂ)‖ ≤ D := by
    intro u
    have hsd := sector_diff_le r c Az k hr u
    rw [show gunitC (⟨r, c + Az * (u+1)⟩ : GaussianInt) ^ k * (ε₂ : ℂ)
          - gunitC (⟨r, c + Az * u⟩ : GaussianInt) ^ k * (ε₂ : ℂ)
        = (ε₂ : ℂ) * (gunitC (⟨r, c + Az * (u+1)⟩ : GaussianInt) ^ k
            - gunitC (⟨r, c + Az * u⟩ : GaussianInt) ^ k) by ring,
      norm_mul, hnormε₂, one_mul]
    refine le_trans hsd ?_
    rw [hDdef]; ring_nf; norm_num
  have hb1 := h2char m₁ m₂ hm₁ hm₂ hcop hgood c₁ c₂ X (min Y t)
      (fun u => gunitC (⟨r, c + Az * u⟩ : GaussianInt) ^ k * (ε₁ : ℂ)) 1 D
      hφ₁norm hφ₁diff
  have hb2 := h2char m₁ m₂ hm₁ hm₂ hcop hgood c₁ c₂ (max X (t+1)) Y
      (fun u => gunitC (⟨r, c + Az * u⟩ : GaussianInt) ^ k * (ε₂ : ℂ)) 1 D
      hφ₂norm hφ₂diff
  have e1 : ∑ u ∈ (Finset.Icc X Y).filter (fun u => u ≤ t),
        gunitC (⟨r, c + Az * u⟩ : GaussianInt) ^ k
          * (MultEps w (⟨r, c + Az * u⟩ : GaussianInt) : ℂ)
          * (jacobiSym (u + c₁) m₁ : ℂ) * (jacobiSym (u + c₂) m₂ : ℂ)
      = ∑ u ∈ Finset.Icc X (min Y t),
          (jacobiSym (u + c₁) m₁ : ℂ) * (jacobiSym (u + c₂) m₂ : ℂ)
            * (gunitC (⟨r, c + Az * u⟩ : GaussianInt) ^ k * (ε₁ : ℂ)) := by
    rw [Icc_filter_le X Y t]
    apply Finset.sum_congr rfl
    intro u hu
    have hut : u ≤ t := (Finset.mem_Icc.mp hu).2.trans (min_le_right _ _)
    have hε : MultEps w (⟨r, c + Az * u⟩ : GaussianInt) = ε₁ := by
      rw [hε₁]; exact ht u t (Or.inl ⟨hut, le_refl t⟩)
    rw [hε]; ring
  have e2 : ∑ u ∈ (Finset.Icc X Y).filter (fun u => ¬ u ≤ t),
        gunitC (⟨r, c + Az * u⟩ : GaussianInt) ^ k
          * (MultEps w (⟨r, c + Az * u⟩ : GaussianInt) : ℂ)
          * (jacobiSym (u + c₁) m₁ : ℂ) * (jacobiSym (u + c₂) m₂ : ℂ)
      = ∑ u ∈ Finset.Icc (max X (t+1)) Y,
          (jacobiSym (u + c₁) m₁ : ℂ) * (jacobiSym (u + c₂) m₂ : ℂ)
            * (gunitC (⟨r, c + Az * u⟩ : GaussianInt) ^ k * (ε₂ : ℂ)) := by
    rw [Icc_filter_lt X Y t]
    apply Finset.sum_congr rfl
    intro u hu
    have hut : t < u := by have := (Finset.mem_Icc.mp hu).1; omega
    have hε : MultEps w (⟨r, c + Az * u⟩ : GaussianInt) = ε₂ := by
      rw [hε₂]; exact ht u (t+1) (Or.inr ⟨hut, by omega⟩)
    rw [hε]; ring
  have h1len : ((min Y t - X).toNat : ℝ) ≤ ((Y - X).toNat : ℝ) := by
    have : (min Y t - X).toNat ≤ (Y - X).toNat := Int.toNat_le_toNat (by omega)
    exact_mod_cast this
  have h2len : ((Y - max X (t+1)).toNat : ℝ) ≤ ((Y - X).toNat : ℝ) := by
    have : (Y - max X (t+1)).toNat ≤ (Y - X).toNat := Int.toNat_le_toNat (by omega)
    exact_mod_cast this
  have hDnn : 0 ≤ D := by rw [hDdef]; positivity
  have hSnn : 0 ≤ Real.sqrt ((m₁ : ℝ) * (m₂ : ℝ))
      * (Real.log (2 + (m₁ : ℝ) * (m₂ : ℝ)) + 1) := by
    apply mul_nonneg (Real.sqrt_nonneg _)
    have : (1:ℝ) ≤ 2 + (m₁:ℝ)*(m₂:ℝ) := by
      have h1 := Nat.cast_nonneg (α := ℝ) m₁
      have h2 := Nat.cast_nonneg (α := ℝ) m₂
      nlinarith [mul_nonneg h1 h2]
    linarith [Real.log_nonneg this]
  rw [← Finset.sum_filter_add_sum_filter_not (Finset.Icc X Y) (fun u => u ≤ t)
      (fun u => gunitC (⟨r, c + Az * u⟩ : GaussianInt) ^ k
        * (MultEps w (⟨r, c + Az * u⟩ : GaussianInt) : ℂ)
        * (jacobiSym (u + c₁) m₁ : ℂ) * (jacobiSym (u + c₂) m₂ : ℂ))]
  rw [e1, e2]
  calc ‖(∑ u ∈ Finset.Icc X (min Y t),
          (jacobiSym (u + c₁) m₁ : ℂ) * (jacobiSym (u + c₂) m₂ : ℂ)
            * (gunitC (⟨r, c + Az * u⟩ : GaussianInt) ^ k * (ε₁ : ℂ)))
        + (∑ u ∈ Finset.Icc (max X (t+1)) Y,
          (jacobiSym (u + c₁) m₁ : ℂ) * (jacobiSym (u + c₂) m₂ : ℂ)
            * (gunitC (⟨r, c + Az * u⟩ : GaussianInt) ^ k * (ε₂ : ℂ)))‖
      ≤ ‖∑ u ∈ Finset.Icc X (min Y t),
          (jacobiSym (u + c₁) m₁ : ℂ) * (jacobiSym (u + c₂) m₂ : ℂ)
            * (gunitC (⟨r, c + Az * u⟩ : GaussianInt) ^ k * (ε₁ : ℂ))‖
        + ‖∑ u ∈ Finset.Icc (max X (t+1)) Y,
          (jacobiSym (u + c₁) m₁ : ℂ) * (jacobiSym (u + c₂) m₂ : ℂ)
            * (gunitC (⟨r, c + Az * u⟩ : GaussianInt) ^ k * (ε₂ : ℂ))‖ := norm_add_le _ _
    _ ≤ C0 * (1 + ((min Y t - X).toNat : ℝ) * D) * Real.sqrt ((m₁ : ℝ) * (m₂ : ℝ))
          * (Real.log (2 + (m₁ : ℝ) * (m₂ : ℝ)) + 1)
        + C0 * (1 + ((Y - max X (t+1)).toNat : ℝ) * D) * Real.sqrt ((m₁ : ℝ) * (m₂ : ℝ))
          * (Real.log (2 + (m₁ : ℝ) * (m₂ : ℝ)) + 1) := add_le_add hb1 hb2
    _ ≤ C0 * (2 + 2 * ((Y - X).toNat : ℝ) * D) * Real.sqrt ((m₁ : ℝ) * (m₂ : ℝ))
          * (Real.log (2 + (m₁ : ℝ) * (m₂ : ℝ)) + 1) := by
        have ha1 : 1 + ((min Y t - X).toNat : ℝ) * D ≤ 1 + ((Y - X).toNat : ℝ) * D := by
          have := mul_le_mul_of_nonneg_right h1len hDnn; linarith
        have ha2 : 1 + ((Y - max X (t+1)).toNat : ℝ) * D ≤ 1 + ((Y - X).toNat : ℝ) * D := by
          have := mul_le_mul_of_nonneg_right h2len hDnn; linarith
        have hb1' : C0 * (1 + ((min Y t - X).toNat : ℝ) * D)
            ≤ C0 * (1 + ((Y - X).toNat : ℝ) * D) := mul_le_mul_of_nonneg_left ha1 hC0.le
        have hb2' : C0 * (1 + ((Y - max X (t+1)).toNat : ℝ) * D)
            ≤ C0 * (1 + ((Y - X).toNat : ℝ) * D) := mul_le_mul_of_nonneg_left ha2 hC0.le
        have hb1'' := mul_le_mul_of_nonneg_right hb1' hSnn
        have hb2'' := mul_le_mul_of_nonneg_right hb2' hSnn
        have hkey : C0 * (1 + ((Y - X).toNat : ℝ) * D) * (Real.sqrt ((m₁ : ℝ) * (m₂ : ℝ))
              * (Real.log (2 + (m₁ : ℝ) * (m₂ : ℝ)) + 1))
            + C0 * (1 + ((Y - X).toNat : ℝ) * D) * (Real.sqrt ((m₁ : ℝ) * (m₂ : ℝ))
              * (Real.log (2 + (m₁ : ℝ) * (m₂ : ℝ)) + 1))
            = C0 * (2 + 2 * ((Y - X).toNat : ℝ) * D) * Real.sqrt ((m₁ : ℝ) * (m₂ : ℝ))
              * (Real.log (2 + (m₁ : ℝ) * (m₂ : ℝ)) + 1) := by ring
        have hb1''' : C0 * (1 + ((min Y t - X).toNat : ℝ) * D) * Real.sqrt ((m₁ : ℝ) * (m₂ : ℝ))
              * (Real.log (2 + (m₁ : ℝ) * (m₂ : ℝ)) + 1)
            = C0 * (1 + ((min Y t - X).toNat : ℝ) * D) * (Real.sqrt ((m₁ : ℝ) * (m₂ : ℝ))
              * (Real.log (2 + (m₁ : ℝ) * (m₂ : ℝ)) + 1)) := by ring
        have hb2''' : C0 * (1 + ((Y - max X (t+1)).toNat : ℝ) * D) * Real.sqrt ((m₁ : ℝ) * (m₂ : ℝ))
              * (Real.log (2 + (m₁ : ℝ) * (m₂ : ℝ)) + 1)
            = C0 * (1 + ((Y - max X (t+1)).toNat : ℝ) * D) * (Real.sqrt ((m₁ : ℝ) * (m₂ : ℝ))
              * (Real.log (2 + (m₁ : ℝ) * (m₂ : ℝ)) + 1)) := by ring
        rw [hb1''', hb2''']
        linarith [hb1'', hb2'', hkey]
    _ = C0 * (2 + 2 * ((Y - X).toNat : ℝ) * (|(k : ℝ)| * 2 * |(Az : ℝ)| / |(r : ℝ)|))
          * Real.sqrt ((m₁ : ℝ) * (m₂ : ℝ)) * (Real.log (2 + (m₁ : ℝ) * (m₂ : ℝ)) + 1) := by
        rw [hDdef]

end Work.FIArea7

namespace Work.FIArea7

end Work.FIArea7

namespace Work.FIArea7

end Work.FIArea7
