import Mathlib
import Submission.Commons.Analysis.HardyLittlewood.forward_maximal_z
import Submission.Commons.Analysis.HardyLittlewood.maximal_lp_of_finsupp

namespace Commons.Analysis.HardyLittlewood
open MeasureTheory Filter Finset
open scoped BigOperators ENNReal Topology
open Classical

private lemma ofReal_iSup_eq {ι : Sort*} (f : ι → ℝ) (hf_nn : ∀ i, 0 ≤ f i)
    (hf_bdd : BddAbove (Set.range f)) :
    ENNReal.ofReal (⨆ i, f i) = ⨆ i, ENNReal.ofReal (f i) := by
  refine le_antisymm ?_ (iSup_le fun i => ENNReal.ofReal_le_ofReal (le_ciSup hf_bdd i))
  by_cases hS : (⨆ i, ENNReal.ofReal (f i)) = ⊤
  · rw [hS]; exact le_top
  · rw [ENNReal.ofReal_le_iff_le_toReal hS]
    rw [ENNReal.toReal_iSup (fun i => ENNReal.ofReal_ne_top)]
    simp only [ENNReal.toReal_ofReal (hf_nn _)]
    exact le_rfl

private noncomputable def Mplus (h : ℤ → ℝ) (x : ℤ) : ℝ :=
  ⨆ N : ℕ, (N : ℝ)⁻¹ * ∑ j ∈ Finset.range N, h (x + (j : ℤ))

private noncomputable def Mminus (h : ℤ → ℝ) (x : ℤ) : ℝ :=
  ⨆ N : ℕ, (N : ℝ)⁻¹ * ∑ j ∈ Finset.range N, h (x - (j : ℤ))

private noncomputable def Mtwo (h : ℤ → ℝ) (x : ℤ) : ℝ :=
  ⨆ (p : {p : ℤ × ℤ // p.1 ≤ x ∧ x ≤ p.2}),
    (((p.1.2 - p.1.1 + 1 : ℤ) : ℝ))⁻¹ * ∑ k ∈ Finset.Icc p.1.1 p.1.2, h k

private lemma finset_sum_le_total {h : ℤ → ℝ} (hnn : ∀ x, 0 ≤ h x) {s : Finset ℤ}
    (hs : ∀ n, n ∉ s → h n = 0) (u : Finset ℤ) :
    ∑ k ∈ u, h k ≤ ∑ k ∈ s, h k := by
  rw [← Finset.sum_subset (s₁ := u ∩ s) (s₂ := u) Finset.inter_subset_left
    (fun k hku hkns => hs k (fun hks => hkns (Finset.mem_inter.mpr ⟨hku, hks⟩)))]
  exact Finset.sum_le_sum_of_subset_of_nonneg Finset.inter_subset_right (fun i _ _ => hnn i)

private lemma sum_window_le_total {h : ℤ → ℝ} (hnn : ∀ x, 0 ≤ h x) {s : Finset ℤ}
    (hs : ∀ n, n ∉ s → h n = 0) (x : ℤ) (N : ℕ) :
    ∑ j ∈ Finset.range N, h (x + (j : ℤ)) ≤ ∑ k ∈ s, h k := by
  classical
  set T := (Finset.range N).image (fun j : ℕ => x + (j : ℤ)) with hT
  have hinj : Function.Injective (fun j : ℕ => x + (j : ℤ)) := by
    intro a b hab; simp only at hab; omega
  have h1 : ∑ j ∈ Finset.range N, h (x + (j:ℤ)) = ∑ k ∈ T, h k := by
    rw [hT, Finset.sum_image (fun a _ b _ hab => hinj hab)]
  rw [h1]
  exact finset_sum_le_total hnn hs T

private lemma sum_window_le_total_sub {h : ℤ → ℝ} (hnn : ∀ x, 0 ≤ h x) {s : Finset ℤ}
    (hs : ∀ n, n ∉ s → h n = 0) (x : ℤ) (N : ℕ) :
    ∑ j ∈ Finset.range N, h (x - (j : ℤ)) ≤ ∑ k ∈ s, h k := by
  classical
  set T := (Finset.range N).image (fun j : ℕ => x - (j : ℤ)) with hT
  have hinj : Function.Injective (fun j : ℕ => x - (j : ℤ)) := by
    intro a b hab; simp only at hab; omega
  have h1 : ∑ j ∈ Finset.range N, h (x - (j:ℤ)) = ∑ k ∈ T, h k := by
    rw [hT, Finset.sum_image (fun a _ b _ hab => hinj hab)]
  rw [h1]
  exact finset_sum_le_total hnn hs T

private lemma bddAbove_Mplus {h : ℤ → ℝ} (hnn : ∀ x, 0 ≤ h x) {s : Finset ℤ}
    (hs : ∀ n, n ∉ s → h n = 0) (x : ℤ) :
    BddAbove (Set.range (fun N : ℕ => (N : ℝ)⁻¹ * ∑ j ∈ Finset.range N, h (x + (j : ℤ)))) := by
  refine ⟨∑ k ∈ s, h k, ?_⟩
  rintro y ⟨N, rfl⟩
  have htot : 0 ≤ ∑ k ∈ s, h k := Finset.sum_nonneg (fun k _ => hnn k)
  rcases Nat.eq_zero_or_pos N with hN | hN
  · subst hN; simp only [Nat.cast_zero, inv_zero, zero_mul, Finset.range_zero,
      Finset.sum_empty]; exact htot
  · have hinv : (N : ℝ)⁻¹ ≤ 1 := by
      rw [inv_le_one₀ (by exact_mod_cast hN)]; exact_mod_cast hN
    have hsum : 0 ≤ ∑ j ∈ Finset.range N, h (x + (j : ℤ)) := Finset.sum_nonneg (fun j _ => hnn _)
    calc (N : ℝ)⁻¹ * ∑ j ∈ Finset.range N, h (x + (j : ℤ))
        ≤ 1 * ∑ j ∈ Finset.range N, h (x + (j : ℤ)) := mul_le_mul_of_nonneg_right hinv hsum
      _ = ∑ j ∈ Finset.range N, h (x + (j : ℤ)) := one_mul _
      _ ≤ ∑ k ∈ s, h k := sum_window_le_total hnn hs x N

private lemma bddAbove_Mminus {h : ℤ → ℝ} (hnn : ∀ x, 0 ≤ h x) {s : Finset ℤ}
    (hs : ∀ n, n ∉ s → h n = 0) (x : ℤ) :
    BddAbove (Set.range (fun N : ℕ => (N : ℝ)⁻¹ * ∑ j ∈ Finset.range N, h (x - (j : ℤ)))) := by
  refine ⟨∑ k ∈ s, h k, ?_⟩
  rintro y ⟨N, rfl⟩
  have htot : 0 ≤ ∑ k ∈ s, h k := Finset.sum_nonneg (fun k _ => hnn k)
  rcases Nat.eq_zero_or_pos N with hN | hN
  · subst hN; simp only [Nat.cast_zero, inv_zero, zero_mul, Finset.range_zero,
      Finset.sum_empty]; exact htot
  · have hinv : (N : ℝ)⁻¹ ≤ 1 := by
      rw [inv_le_one₀ (by exact_mod_cast hN)]; exact_mod_cast hN
    have hsum : 0 ≤ ∑ j ∈ Finset.range N, h (x - (j : ℤ)) := Finset.sum_nonneg (fun j _ => hnn _)
    calc (N : ℝ)⁻¹ * ∑ j ∈ Finset.range N, h (x - (j : ℤ))
        ≤ 1 * ∑ j ∈ Finset.range N, h (x - (j : ℤ)) := mul_le_mul_of_nonneg_right hinv hsum
      _ = ∑ j ∈ Finset.range N, h (x - (j : ℤ)) := one_mul _
      _ ≤ ∑ k ∈ s, h k := sum_window_le_total_sub hnn hs x N

private lemma sum_range_sub_eq_sum_Icc (h : ℤ → ℝ) {a x : ℤ} (hax : a ≤ x) :
    ∑ j ∈ Finset.range ((x - a + 1).toNat), h (x - (j:ℤ)) = ∑ k ∈ Finset.Icc a x, h k := by
  have hN : (((x - a + 1).toNat : ℤ)) = x - a + 1 := Int.toNat_of_nonneg (by omega)
  have himg : (Finset.range ((x - a + 1).toNat)).image (fun j : ℕ => x - (j : ℤ))
      = Finset.Icc a x := by
    ext k
    simp only [Finset.mem_image, Finset.mem_range, Finset.mem_Icc]
    constructor
    · rintro ⟨j, hj, rfl⟩
      have hjN : (j:ℤ) < x - a + 1 := by rw [← hN, Int.ofNat_lt]; exact hj
      constructor <;> omega
    · intro hk
      refine ⟨(x - k).toNat, ?_, ?_⟩
      · rw [Int.toNat_lt (by omega)]; rw [hN]; omega
      · rw [Int.toNat_of_nonneg (by omega)]; ring
  rw [← himg, Finset.sum_image]
  intro p _ q _ hpq
  simp only at hpq
  omega

private lemma sum_range_add_eq_sum_Icc (h : ℤ → ℝ) {x b : ℤ} (hxb : x ≤ b) :
    ∑ j ∈ Finset.range ((b - x + 1).toNat), h (x + (j:ℤ)) = ∑ k ∈ Finset.Icc x b, h k := by
  have hN : (((b - x + 1).toNat : ℤ)) = b - x + 1 := Int.toNat_of_nonneg (by omega)
  have himg : (Finset.range ((b - x + 1).toNat)).image (fun j : ℕ => x + (j : ℤ))
      = Finset.Icc x b := by
    ext k
    simp only [Finset.mem_image, Finset.mem_range, Finset.mem_Icc]
    constructor
    · rintro ⟨j, hj, rfl⟩
      have hjN : (j:ℤ) < b - x + 1 := by rw [← hN, Int.ofNat_lt]; exact hj
      constructor <;> omega
    · intro hk
      refine ⟨(k - x).toNat, ?_, ?_⟩
      · rw [Int.toNat_lt (by omega)]; rw [hN]; omega
      · rw [Int.toNat_of_nonneg (by omega)]; ring
  rw [← himg, Finset.sum_image]
  intro p _ q _ hpq
  simp only at hpq
  omega

private lemma Mplus_nonneg {h : ℤ → ℝ} (hnn : ∀ x, 0 ≤ h x) {s : Finset ℤ}
    (hs : ∀ n, n ∉ s → h n = 0) (x : ℤ) : 0 ≤ Mplus h x := by
  have := le_ciSup (bddAbove_Mplus hnn hs x) 0
  simpa [Mplus] using this

private lemma Mminus_nonneg {h : ℤ → ℝ} (hnn : ∀ x, 0 ≤ h x) {s : Finset ℤ}
    (hs : ∀ n, n ∉ s → h n = 0) (x : ℤ) : 0 ≤ Mminus h x := by
  have := le_ciSup (bddAbove_Mminus hnn hs x) 0
  simpa [Mminus] using this

private lemma sum_window_le_total_ltop {h : ℤ → ℝ} (hnn : ∀ x, 0 ≤ h x) {s : Finset ℤ}
    (hs : ∀ n, n ∉ s → h n = 0) (x : ℤ)
    (p : {p : ℤ × ℤ // p.1 ≤ x ∧ x ≤ p.2}) :
    (((p.1.2 - p.1.1 + 1 : ℤ) : ℝ))⁻¹ * ∑ k ∈ Finset.Icc p.1.1 p.1.2, h k
      ≤ ∑ k ∈ s, h k := by
  have hcoef : (((p.1.2 - p.1.1 + 1 : ℤ) : ℝ))⁻¹ ≤ 1 := by
    have hle : (1:ℤ) ≤ p.1.2 - p.1.1 + 1 := by
      have : p.1.1 ≤ p.1.2 := le_trans p.2.1 p.2.2
      omega
    have h1 : (1:ℝ) ≤ ((p.1.2 - p.1.1 + 1 : ℤ) : ℝ) := by exact_mod_cast hle
    rw [inv_le_one₀ (by linarith)]; linarith
  have hsum : ∑ k ∈ Finset.Icc p.1.1 p.1.2, h k ≤ ∑ k ∈ s, h k :=
    finset_sum_le_total hnn hs _
  have hnn' : 0 ≤ ∑ k ∈ Finset.Icc p.1.1 p.1.2, h k := Finset.sum_nonneg (fun k _ => hnn k)
  calc (((p.1.2 - p.1.1 + 1 : ℤ) : ℝ))⁻¹ * ∑ k ∈ Finset.Icc p.1.1 p.1.2, h k
      ≤ 1 * ∑ k ∈ Finset.Icc p.1.1 p.1.2, h k := mul_le_mul_of_nonneg_right hcoef hnn'
    _ = ∑ k ∈ Finset.Icc p.1.1 p.1.2, h k := one_mul _
    _ ≤ ∑ k ∈ s, h k := hsum

private lemma Mtwo_bddAbove {h : ℤ → ℝ} (hnn : ∀ x, 0 ≤ h x) {s : Finset ℤ}
    (hs : ∀ n, n ∉ s → h n = 0) (x : ℤ) :
    BddAbove (Set.range (fun p : {p : ℤ × ℤ // p.1 ≤ x ∧ x ≤ p.2} =>
      (((p.1.2 - p.1.1 + 1 : ℤ) : ℝ))⁻¹ * ∑ k ∈ Finset.Icc p.1.1 p.1.2, h k)) := by
  refine ⟨∑ k ∈ s, h k, ?_⟩
  rintro y ⟨p, rfl⟩
  exact sum_window_le_total_ltop hnn hs x p

private lemma Mtwo_le {h : ℤ → ℝ} (hnn : ∀ x, 0 ≤ h x) {s : Finset ℤ}
    (hs : ∀ n, n ∉ s → h n = 0) (x : ℤ) :
    Mtwo h x ≤ Mplus h x + Mminus h x := by
  haveI : Nonempty {p : ℤ × ℤ // p.1 ≤ x ∧ x ≤ p.2} := ⟨⟨(x,x), le_refl x, le_refl x⟩⟩
  apply ciSup_le
  intro p
  obtain ⟨⟨a, b⟩, hab⟩ := p
  obtain ⟨hax, hxb⟩ := hab
  set A : ℕ := (x - a + 1).toNat with hA
  set B : ℕ := (b - x + 1).toNat with hB
  have hAz : (A : ℤ) = x - a + 1 := Int.toNat_of_nonneg (by omega)
  have hBz : (B : ℤ) = b - x + 1 := Int.toNat_of_nonneg (by omega)
  have hA1 : 1 ≤ A := by omega
  have hB1 : 1 ≤ B := by omega
  have hAr : (1:ℝ) ≤ (A:ℝ) := by exact_mod_cast hA1
  have hBr : (1:ℝ) ≤ (B:ℝ) := by exact_mod_cast hB1
  have hAnn : (0:ℝ) < (A:ℝ) := by linarith
  have hBnn : (0:ℝ) < (B:ℝ) := by linarith
  have hU : ∑ k ∈ Finset.Icc a x, h k ≤ (A:ℝ) * Mminus h x := by
    have hle : (A:ℝ)⁻¹ * ∑ j ∈ Finset.range A, h (x - (j:ℤ)) ≤ Mminus h x := by
      rw [Mminus]; exact le_ciSup (bddAbove_Mminus hnn hs x) A
    rw [sum_range_sub_eq_sum_Icc h hax] at hle
    rwa [inv_mul_le_iff₀ hAnn] at hle
  have hV : ∑ k ∈ Finset.Icc (x+1) b, h k ≤ (B:ℝ) * Mplus h x := by
    have hle : (B:ℝ)⁻¹ * ∑ j ∈ Finset.range B, h (x + (j:ℤ)) ≤ Mplus h x := by
      rw [Mplus]; exact le_ciSup (bddAbove_Mplus hnn hs x) B
    rw [sum_range_add_eq_sum_Icc h hxb] at hle
    rw [inv_mul_le_iff₀ hBnn] at hle
    calc ∑ k ∈ Finset.Icc (x+1) b, h k ≤ ∑ k ∈ Finset.Icc x b, h k :=
          Finset.sum_le_sum_of_subset_of_nonneg
            (by intro k hk; simp only [Finset.mem_Icc] at hk ⊢; omega)
            (fun i _ _ => hnn i)
      _ ≤ (B:ℝ) * Mplus h x := hle
  have hdisj : Disjoint (Finset.Icc a x) (Finset.Icc (x+1) b) := by
    rw [Finset.disjoint_left]; intro k hk1 hk2
    simp only [Finset.mem_Icc] at hk1 hk2; omega
  have hsplit : ∑ k ∈ Finset.Icc a b, h k
      ≤ ∑ k ∈ Finset.Icc a x, h k + ∑ k ∈ Finset.Icc (x+1) b, h k := by
    rw [← Finset.sum_union hdisj]
    refine Finset.sum_le_sum_of_subset_of_nonneg ?_ (fun i _ _ => hnn i)
    intro k hk
    simp only [Finset.mem_union, Finset.mem_Icc] at hk ⊢
    by_cases h : k ≤ x
    · exact Or.inl ⟨hk.1, h⟩
    · exact Or.inr ⟨by omega, hk.2⟩
  have hAeq : ((b - a + 1 : ℤ) : ℝ) = (A:ℝ) + (B:ℝ) - 1 := by
    have : (b - a + 1 : ℤ) = (A:ℤ) + (B:ℤ) - 1 := by rw [hAz, hBz]; ring
    rw [this]; push_cast; ring
  have hpos : (0:ℝ) < ((b - a + 1 : ℤ) : ℝ) := by rw [hAeq]; linarith
  rw [inv_mul_le_iff₀ hpos, hAeq]
  have hu := Mminus_nonneg hnn hs x
  have hv := Mplus_nonneg hnn hs x
  calc ∑ k ∈ Finset.Icc a b, h k
      ≤ ∑ k ∈ Finset.Icc a x, h k + ∑ k ∈ Finset.Icc (x+1) b, h k := hsplit
    _ ≤ (A:ℝ) * Mminus h x + (B:ℝ) * Mplus h x := add_le_add hU hV
    _ ≤ ((A:ℝ) + (B:ℝ) - 1) * (Mplus h x + Mminus h x) := by nlinarith [hu, hv, hAr, hBr]


private lemma ofReal_Mplus {h : ℤ → ℝ} (hnn : ∀ x, 0 ≤ h x) {s : Finset ℤ}
    (hs : ∀ n, n ∉ s → h n = 0) (x : ℤ) :
    ENNReal.ofReal (Mplus h x)
      = ⨆ N : ℕ, ‖((N : ℝ))⁻¹ * ∑ j ∈ Finset.range N, h (x + (j : ℤ))‖ₑ := by
  rw [Mplus,
    ofReal_iSup_eq (fun N : ℕ => (N : ℝ)⁻¹ * ∑ j ∈ Finset.range N, h (x + (j : ℤ)))
      (fun N => mul_nonneg (inv_nonneg.mpr (Nat.cast_nonneg N)) (Finset.sum_nonneg (fun j _ => hnn _)))
      (bddAbove_Mplus hnn hs x)]
  apply iSup_congr; intro N
  rw [Real.enorm_eq_ofReal_abs, abs_of_nonneg]
  exact mul_nonneg (inv_nonneg.mpr (Nat.cast_nonneg N)) (Finset.sum_nonneg (fun j _ => hnn _))

private lemma lintegral_count_neg (F : ℤ → ℝ≥0∞) :
    ∫⁻ x, F (-x) ∂Measure.count = ∫⁻ x, F x ∂Measure.count := by
  rw [MeasureTheory.lintegral_count, MeasureTheory.lintegral_count]
  exact Equiv.tsum_eq (Equiv.neg ℤ) F

private lemma integral_Mplus_le {p : ℝ} (hp : 1 < p) {C : ℝ}
    (hFwd : ∀ (g : ℤ → ℝ), (∃ s : Finset ℤ, ∀ n, n ∉ s → g n = 0) →
      ∫⁻ x, (⨆ N : ℕ, ‖((N : ℝ))⁻¹ * ∑ j ∈ Finset.range N, g (x + j)‖ₑ) ^ p ∂Measure.count
        ≤ ENNReal.ofReal (C ^ p) * ∫⁻ x, ‖g x‖ₑ ^ p ∂Measure.count)
    {h : ℤ → ℝ} (hnn : ∀ x, 0 ≤ h x) {s : Finset ℤ} (hs : ∀ n, n ∉ s → h n = 0) :
    ∫⁻ x, ENNReal.ofReal ((Mplus h x) ^ p) ∂Measure.count
      ≤ ENNReal.ofReal (C ^ p) * ∫⁻ x, ENNReal.ofReal ((h x) ^ p) ∂Measure.count := by
  have hp0 : (0:ℝ) ≤ p := by linarith
  calc ∫⁻ x, ENNReal.ofReal ((Mplus h x) ^ p) ∂Measure.count
      = ∫⁻ x, (ENNReal.ofReal (Mplus h x)) ^ p ∂Measure.count := by
          apply lintegral_congr; intro x
          rw [ENNReal.ofReal_rpow_of_nonneg (Mplus_nonneg hnn hs x) hp0]
    _ = ∫⁻ x, (⨆ N : ℕ, ‖((N : ℝ))⁻¹ * ∑ j ∈ Finset.range N, h (x + j)‖ₑ) ^ p
          ∂Measure.count := by
          apply lintegral_congr; intro x
          rw [ofReal_Mplus hnn hs x]
    _ ≤ ENNReal.ofReal (C ^ p) * ∫⁻ x, ‖h x‖ₑ ^ p ∂Measure.count := hFwd h ⟨s, hs⟩
    _ = ENNReal.ofReal (C ^ p) * ∫⁻ x, ENNReal.ofReal ((h x) ^ p) ∂Measure.count := by
          congr 1
          apply lintegral_congr; intro x
          rw [Real.enorm_eq_ofReal_abs, abs_of_nonneg (hnn x),
            ← ENNReal.ofReal_rpow_of_nonneg (hnn x) hp0]

private lemma integral_Mminus_le {p : ℝ} (hp : 1 < p) {C : ℝ}
    (hFwd : ∀ (g : ℤ → ℝ), (∃ s : Finset ℤ, ∀ n, n ∉ s → g n = 0) →
      ∫⁻ x, (⨆ N : ℕ, ‖((N : ℝ))⁻¹ * ∑ j ∈ Finset.range N, g (x + j)‖ₑ) ^ p ∂Measure.count
        ≤ ENNReal.ofReal (C ^ p) * ∫⁻ x, ‖g x‖ₑ ^ p ∂Measure.count)
    {h : ℤ → ℝ} (hnn : ∀ x, 0 ≤ h x) {s : Finset ℤ} (hs : ∀ n, n ∉ s → h n = 0) :
    ∫⁻ x, ENNReal.ofReal ((Mminus h x) ^ p) ∂Measure.count
      ≤ ENNReal.ofReal (C ^ p) * ∫⁻ x, ENNReal.ofReal ((h x) ^ p) ∂Measure.count := by
  have hkey : ∀ x, Mminus h x = Mplus (fun k : ℤ => h (-k)) (-x) := by
    intro x
    simp only [Mminus, Mplus]
    apply iSup_congr; intro N
    congr 1
    apply Finset.sum_congr rfl; intro j _
    congr 1
    ring
  have hnn' : ∀ k, 0 ≤ (fun k : ℤ => h (-k)) k := fun k => hnn (-k)
  obtain ⟨s', hs'⟩ : ∃ s' : Finset ℤ, ∀ n, n ∉ s' → (fun k : ℤ => h (-k)) n = 0 :=
    ⟨s.image (fun k : ℤ => -k), fun n hn => hs (-n)
      (fun hns => hn (Finset.mem_image.mpr ⟨-n, hns, by ring⟩))⟩
  have hbp := integral_Mplus_le hp hFwd hnn' hs'
  calc ∫⁻ x, ENNReal.ofReal ((Mminus h x) ^ p) ∂Measure.count
      = ∫⁻ x, ENNReal.ofReal ((Mplus (fun k : ℤ => h (-k)) (-x)) ^ p) ∂Measure.count := by
          apply lintegral_congr; intro x; rw [hkey x]
    _ = ∫⁻ y, ENNReal.ofReal ((Mplus (fun k : ℤ => h (-k)) y) ^ p) ∂Measure.count :=
          lintegral_count_neg (fun y : ℤ => ENNReal.ofReal ((Mplus (fun k : ℤ => h (-k)) y) ^ p))
    _ ≤ ENNReal.ofReal (C ^ p)
          * ∫⁻ y, ENNReal.ofReal (((fun k : ℤ => h (-k)) y) ^ p) ∂Measure.count := hbp
    _ = ENNReal.ofReal (C ^ p) * ∫⁻ x, ENNReal.ofReal ((h x) ^ p) ∂Measure.count := by
          congr 1
          exact lintegral_count_neg (fun x : ℤ => ENNReal.ofReal ((h x) ^ p))


private lemma Mtwo_nonneg {h : ℤ → ℝ} (hnn : ∀ x, 0 ≤ h x) {s : Finset ℤ}
    (hs : ∀ n, n ∉ s → h n = 0) (x : ℤ) : 0 ≤ Mtwo h x := by
  have h0 : 0 ≤ ((((x - x + 1 : ℤ) : ℝ))⁻¹ * ∑ k ∈ Finset.Icc x x, h k) := by
    rw [Finset.Icc_self, Finset.sum_singleton]
    have hc : (((x - x + 1 : ℤ) : ℝ))⁻¹ = 1 := by norm_num
    rw [hc, one_mul]; exact hnn x
  exact le_ciSup_of_le (Mtwo_bddAbove hnn hs x) ⟨(x,x), le_refl x, le_refl x⟩ h0

private lemma const_aux {p C : ℝ} (hC : 0 ≤ C) :
    2 ^ (p - 1) * (C ^ p + C ^ p) = (2 * C) ^ p := by
  have h1 : (2:ℝ)^(p-1) * 2 = 2^p := by
    have h := Real.rpow_add (show (0:ℝ) < 2 by norm_num) (p-1) 1
    rw [Real.rpow_one] at h
    rw [← h, show p - 1 + 1 = p by ring]
  rw [show C^p + C^p = 2*C^p by ring, ← mul_assoc, h1, Real.mul_rpow (by norm_num) hC]

private lemma integral_Mtwo_le {p : ℝ} (hp : 1 < p) {C : ℝ} (hC : 0 < C)
    (hFwd : ∀ (g : ℤ → ℝ), (∃ s : Finset ℤ, ∀ n, n ∉ s → g n = 0) →
      ∫⁻ x, (⨆ N : ℕ, ‖((N : ℝ))⁻¹ * ∑ j ∈ Finset.range N, g (x + j)‖ₑ) ^ p ∂Measure.count
        ≤ ENNReal.ofReal (C ^ p) * ∫⁻ x, ‖g x‖ₑ ^ p ∂Measure.count)
    {h : ℤ → ℝ} (hnn : ∀ x, 0 ≤ h x) {s : Finset ℤ} (hs : ∀ n, n ∉ s → h n = 0) :
    ∫⁻ x, ENNReal.ofReal ((Mtwo h x) ^ p) ∂Measure.count
      ≤ ENNReal.ofReal ((2 * C) ^ p) * ∫⁻ x, ENNReal.ofReal ((h x) ^ p) ∂Measure.count := by
  have hp0 : (0:ℝ) ≤ p := by linarith
  have hp1 : (1:ℝ) ≤ p := hp.le
  have hIplus := integral_Mplus_le hp hFwd hnn hs
  have hIminus := integral_Mminus_le hp hFwd hnn hs
  have hpoint : ∀ x, ENNReal.ofReal ((Mtwo h x) ^ p)
      ≤ ENNReal.ofReal (2 ^ (p-1))
        * (ENNReal.ofReal ((Mplus h x) ^ p) + ENNReal.ofReal ((Mminus h x) ^ p)) := by
    intro x
    have hM2 := Mtwo_nonneg hnn hs x
    have hMp := Mplus_nonneg hnn hs x
    have hMm := Mminus_nonneg hnn hs x
    calc ENNReal.ofReal ((Mtwo h x) ^ p)
        = (ENNReal.ofReal (Mtwo h x)) ^ p := (ENNReal.ofReal_rpow_of_nonneg hM2 hp0).symm
      _ ≤ (ENNReal.ofReal (Mplus h x + Mminus h x)) ^ p :=
            ENNReal.rpow_le_rpow (ENNReal.ofReal_le_ofReal (Mtwo_le hnn hs x)) hp0
      _ = (ENNReal.ofReal (Mplus h x) + ENNReal.ofReal (Mminus h x)) ^ p := by
            rw [ENNReal.ofReal_add hMp hMm]
      _ ≤ ENNReal.ofReal (2 ^ (p-1))
            * ((ENNReal.ofReal (Mplus h x)) ^ p + (ENNReal.ofReal (Mminus h x)) ^ p) := by
            have hpow : ((2:ℝ≥0∞) ^ (p-1)) = ENNReal.ofReal (2 ^ (p-1)) := by
              rw [show (2:ℝ≥0∞) = ENNReal.ofReal 2 by norm_num,
                ENNReal.ofReal_rpow_of_nonneg (by norm_num) (by linarith : (0:ℝ) ≤ p-1)]
            rw [← hpow]
            exact ENNReal.rpow_add_le_mul_rpow_add_rpow _ _ hp1
      _ = ENNReal.ofReal (2 ^ (p-1))
            * (ENNReal.ofReal ((Mplus h x) ^ p) + ENNReal.ofReal ((Mminus h x) ^ p)) := by
            rw [ENNReal.ofReal_rpow_of_nonneg hMp hp0, ENNReal.ofReal_rpow_of_nonneg hMm hp0]
  have hmeas1 : Measurable (fun x : ℤ => ENNReal.ofReal ((Mplus h x) ^ p)) := measurable_of_countable _
  have hmeas2 : Measurable (fun x : ℤ => ENNReal.ofReal ((Mminus h x) ^ p)) := measurable_of_countable _
  have hAB : ENNReal.ofReal (2 ^ (p-1)) * ENNReal.ofReal (C ^ p)
      = ENNReal.ofReal (2 ^ (p-1) * C ^ p) :=
    (ENNReal.ofReal_mul (by positivity)).symm
  have hAB2 : ENNReal.ofReal (2 ^ (p-1)) * ENNReal.ofReal (C ^ p) * 2
      = ENNReal.ofReal ((2 * C) ^ p) := by
    rw [hAB, show (2:ℝ≥0∞) = ENNReal.ofReal 2 by norm_num,
      (ENNReal.ofReal_mul (by positivity)).symm]
    congr 1
    rw [show (2:ℝ)^(p-1) * C^p * 2 = 2^(p-1) * (C^p + C^p) by ring, const_aux hC.le]
  calc ∫⁻ x, ENNReal.ofReal ((Mtwo h x) ^ p) ∂Measure.count
      ≤ ∫⁻ x, ENNReal.ofReal (2 ^ (p-1))
          * (ENNReal.ofReal ((Mplus h x) ^ p) + ENNReal.ofReal ((Mminus h x) ^ p))
          ∂Measure.count := lintegral_mono hpoint
    _ = ENNReal.ofReal (2 ^ (p-1))
          * (∫⁻ x, ENNReal.ofReal ((Mplus h x) ^ p) ∂Measure.count
             + ∫⁻ x, ENNReal.ofReal ((Mminus h x) ^ p) ∂Measure.count) := by
          rw [lintegral_const_mul (f := fun x : ℤ =>
                ENNReal.ofReal ((Mplus h x) ^ p) + ENNReal.ofReal ((Mminus h x) ^ p))
                (ENNReal.ofReal (2 ^ (p-1))) (hmeas1.add hmeas2)]
          rw [lintegral_add_left hmeas1]
    _ ≤ ENNReal.ofReal (2 ^ (p-1))
          * (ENNReal.ofReal (C ^ p) * ∫⁻ x, ENNReal.ofReal ((h x) ^ p) ∂Measure.count
             + ENNReal.ofReal (C ^ p) * ∫⁻ x, ENNReal.ofReal ((h x) ^ p) ∂Measure.count) :=
          mul_le_mul_of_nonneg_left (add_le_add hIplus hIminus) (by positivity)
    _ = ENNReal.ofReal ((2 * C) ^ p) * ∫⁻ x, ENNReal.ofReal ((h x) ^ p) ∂Measure.count := by
          rw [show ENNReal.ofReal (2 ^ (p-1))
                * (ENNReal.ofReal (C ^ p) * ∫⁻ x, ENNReal.ofReal ((h x) ^ p) ∂Measure.count
                   + ENNReal.ofReal (C ^ p) * ∫⁻ x, ENNReal.ofReal ((h x) ^ p) ∂Measure.count)
              = (ENNReal.ofReal (2 ^ (p-1)) * ENNReal.ofReal (C ^ p) * 2)
                * ∫⁻ x, ENNReal.ofReal ((h x) ^ p) ∂Measure.count by ring,
              hAB2]


private lemma integral_target_finsupp {p : ℝ} (hp : 1 < p) {C : ℝ} (hC : 0 < C)
    (hFwd : ∀ (g : ℤ → ℝ), (∃ s : Finset ℤ, ∀ n, n ∉ s → g n = 0) →
      ∫⁻ x, (⨆ N : ℕ, ‖((N : ℝ))⁻¹ * ∑ j ∈ Finset.range N, g (x + j)‖ₑ) ^ p ∂Measure.count
        ≤ ENNReal.ofReal (C ^ p) * ∫⁻ x, ‖g x‖ₑ ^ p ∂Measure.count) :
    ∃ C' : ℝ, 0 < C' ∧ ∀ (g : ℤ → ℝ), (∃ s : Finset ℤ, ∀ n, n ∉ s → g n = 0) →
      ∫⁻ x, (⨆ (a : ℤ) (b : ℤ) (_ : a ≤ x ∧ x ≤ b),
            ((b - a + 1).toNat : ℝ≥0∞)⁻¹ * ∑ k ∈ Finset.Icc a b, ‖g k‖ₑ) ^ p ∂Measure.count
        ≤ ENNReal.ofReal (C' ^ p) * ∫⁻ x, ‖g x‖ₑ ^ p ∂Measure.count := by
  refine ⟨2*C, by positivity, ?_⟩
  intro g ⟨s, hs⟩
  have hp0 : (0:ℝ) ≤ p := by linarith
  set h : ℤ → ℝ := fun k => |g k| with hh
  have hnn : ∀ x, 0 ≤ h x := fun x => abs_nonneg _
  have hs' : ∀ n, n ∉ s → h n = 0 := fun n hn => by simp only [hh]; rw [hs n hn, abs_zero]
  have hpoint : ∀ x, (⨆ (a : ℤ) (b : ℤ) (_ : a ≤ x ∧ x ≤ b),
        ((b - a + 1).toNat : ℝ≥0∞)⁻¹ * ∑ k ∈ Finset.Icc a b, ‖g k‖ₑ)
        ≤ ENNReal.ofReal (Mtwo h x) := by
    intro x
    apply iSup_le; intro a
    apply iSup_le; intro b
    apply iSup_le; intro hab
    have hab' : a ≤ b := le_trans hab.1 hab.2
    have hcoefnn : (0:ℝ) ≤ (((b - a + 1 : ℤ) : ℝ))⁻¹ := by
      apply inv_nonneg.mpr
      have : (0:ℤ) ≤ b - a + 1 := by omega
      exact_mod_cast this
    have hterm : ((b - a + 1).toNat : ℝ≥0∞)⁻¹ * ∑ k ∈ Finset.Icc a b, ‖g k‖ₑ
        = ENNReal.ofReal (((b - a + 1 : ℤ) : ℝ)⁻¹ * ∑ k ∈ Finset.Icc a b, h k) := by
      have hcoef : (((b - a + 1).toNat : ℝ≥0∞))⁻¹
          = ENNReal.ofReal (((b - a + 1 : ℤ) : ℝ)⁻¹) := by
        have h2 : (((b - a + 1).toNat : ℤ)) = b - a + 1 :=
          Int.toNat_of_nonneg (show (0:ℤ) ≤ b - a + 1 by omega)
        have h1 : ((b - a + 1 : ℤ) : ℝ) = ((b - a + 1).toNat : ℝ) := by
          have h3 := congrArg (fun z : ℤ => (z : ℝ)) h2
          push_cast at h3 ⊢
          exact h3.symm
        have hnpos : (0:ℝ) < ((b - a + 1).toNat : ℝ) := by
          have : (1:ℕ) ≤ (b - a + 1).toNat := by omega
          exact_mod_cast this
        rw [h1, ENNReal.ofReal_inv_of_pos hnpos, ENNReal.ofReal_natCast]
      have hsum : ∑ k ∈ Finset.Icc a b, ‖g k‖ₑ = ENNReal.ofReal (∑ k ∈ Finset.Icc a b, h k) := by
        rw [ENNReal.ofReal_sum_of_nonneg (fun k _ => hnn k)]
        apply Finset.sum_congr rfl; intro k _
        simp only [Real.enorm_eq_ofReal_abs, hh]
      rw [hcoef, hsum, ← ENNReal.ofReal_mul hcoefnn]
    rw [hterm]
    exact ENNReal.ofReal_le_ofReal (le_ciSup (Mtwo_bddAbove hnn hs' x) ⟨(a,b), hab⟩)
  calc ∫⁻ x, (⨆ (a : ℤ) (b : ℤ) (_ : a ≤ x ∧ x ≤ b),
            ((b - a + 1).toNat : ℝ≥0∞)⁻¹ * ∑ k ∈ Finset.Icc a b, ‖g k‖ₑ) ^ p ∂Measure.count
      ≤ ∫⁻ x, (ENNReal.ofReal (Mtwo h x)) ^ p ∂Measure.count := by
          apply lintegral_mono; intro x
          exact ENNReal.rpow_le_rpow (hpoint x) hp0
    _ = ∫⁻ x, ENNReal.ofReal ((Mtwo h x) ^ p) ∂Measure.count := by
          apply lintegral_congr; intro x
          rw [ENNReal.ofReal_rpow_of_nonneg (Mtwo_nonneg hnn hs' x) hp0]
    _ ≤ ENNReal.ofReal ((2 * C) ^ p) * ∫⁻ x, ENNReal.ofReal ((h x) ^ p) ∂Measure.count :=
          integral_Mtwo_le hp hC hFwd hnn hs'
    _ = ENNReal.ofReal ((2 * C) ^ p) * ∫⁻ x, ‖g x‖ₑ ^ p ∂Measure.count := by
          congr 1; apply lintegral_congr; intro x
          rw [hh, Real.enorm_eq_ofReal_abs,
            ← ENNReal.ofReal_rpow_of_nonneg (abs_nonneg (g x)) hp0]


/-- **Discrete two-sided Hardy--Littlewood maximal inequality on `ℤ`** (`p > 1`),
with respect to counting measure: the two-sided maximal function over integer intervals
containing `x` satisfies an `ℓ^p` bound with respect to counting measure. -/
theorem discrete_maximal_lp {p : ℝ} (hp : 1 < p) :
    ∃ C : ℝ, 0 < C ∧ ∀ (g : ℤ → ℝ),
      ∫⁻ x, (⨆ (a : ℤ) (b : ℤ) (_ : a ≤ x ∧ x ≤ b),
          ((b - a + 1).toNat : ℝ≥0∞)⁻¹ * ∑ k ∈ Finset.Icc a b, ‖g k‖ₑ) ^ p ∂Measure.count
        ≤ ENNReal.ofReal (C ^ p) * ∫⁻ x, ‖g x‖ₑ ^ p ∂Measure.count := by
  obtain ⟨C0, hC0, hFwd⟩ := forward_maximal_z hp
  obtain ⟨C1, hC1, hfin⟩ := integral_target_finsupp hp hC0 hFwd
  exact ⟨C1, hC1, maximal_lp_of_finsupp hp hC1 hfin⟩

end Commons.Analysis.HardyLittlewood
