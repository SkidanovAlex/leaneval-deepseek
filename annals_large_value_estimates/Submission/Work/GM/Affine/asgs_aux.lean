import Mathlib
import Submission.Work.GM.Affine.fine_setup
import Submission.Work.GM.Affine.smoothed_properties
import Submission.Work.GM.Affine.cauchy_base

/-!
# Elementary counting and square-sum helpers for `affineSum_sq_ge_smoothed`

These are the "combinatorial" inputs of the lower bound
`(1/64) M₂² ∫ f̃² ≤ ∫ (affineSum K M₁ M₂ M₃ f̃)²` on the range `M₃ < 1`, `M₁, M₂ ≥ 1/2`:

* the summation ranges `R1 M₁`, `R2 M₂`, `R3 K M₃` are non-empty and carry enough mass
  (`Σ_{m₁∈R1} 1/|m₁| ≥ 1/2`, `Σ_{m₂∈R2} m₂ ≥ M₂²/2`, `1 ≤ #(R3 K M₃)`);
* `(Σ a)² ≥ Σ a²` for non-negative finite families.

Everything here is an elementary estimate about floors and finite sums.
-/

open Finset MeasureTheory

set_option autoImplicit false

namespace Work.GM.Affine

noncomputable section

/-- `(Σ a)² ≥ Σ a²` for a finite family of non-negative reals. -/
lemma asgs_sq_sum_ge_sum_sq {ι : Type*} (s : Finset ι) {f : ι → ℝ} (hnn : ∀ i ∈ s, 0 ≤ f i) :
    ∑ i ∈ s, f i ^ 2 ≤ (∑ i ∈ s, f i) ^ 2 := by
  rw [sq, Finset.sum_mul_sum]
  refine Finset.sum_le_sum fun i hi => ?_
  rw [sq]
  exact Finset.single_le_sum (fun j hj => mul_nonneg (hnn i hi) (hnn j hj)) hi

/-- For `M ≥ 1/2` the number of integers in `(M, 2M]` is at least `M/2`. -/
lemma asgs_floor_diff_ge {M : ℝ} (hM : (1:ℝ)/2 ≤ M) :
    M/2 ≤ (((⌊2*M⌋ : ℤ) : ℝ) - ((⌊M⌋ : ℤ) : ℝ)) := by
  have h2floor : 2 * ⌊M⌋ ≤ ⌊2 * M⌋ := by
    have h : ((2 * ⌊M⌋ : ℤ) : ℝ) ≤ 2 * M := by
      push_cast
      linarith [Int.floor_le M]
    exact Int.le_floor.mpr h
  rcases le_or_gt 2 M with h2 | h2
  · have ha : 2*M - 1 ≤ ((⌊2*M⌋ : ℤ) : ℝ) := by
      have h := Int.lt_floor_add_one (2*M)
      linarith
    have hb : ((⌊M⌋ : ℤ) : ℝ) ≤ M := Int.floor_le M
    linarith
  · have hge1 : (1:ℤ) ≤ ⌊2*M⌋ - ⌊M⌋ := by
      rcases le_or_gt 1 ⌊M⌋ with hj | hj
      · omega
      · have hj0 : ⌊M⌋ = 0 := by
          have h00 : (0:ℤ) ≤ ⌊M⌋ := Int.le_floor.mpr (by push_cast; linarith)
          omega
        have hi : (1:ℤ) ≤ ⌊2*M⌋ := Int.le_floor.mpr (by push_cast; linarith)
        omega
    have h1 : (1:ℝ) ≤ (((⌊2*M⌋ : ℤ) : ℝ) - ((⌊M⌋ : ℤ) : ℝ)) := by
      have hcast : ((⌊2*M⌋ - ⌊M⌋ : ℤ) : ℝ) ≥ 1 := by exact_mod_cast hge1
      push_cast at hcast
      linarith
    linarith

/-- The cardinality of the integer interval `(M, 2M]`. -/
lemma asgs_card_Icc_floor {M : ℝ} (hM : 0 ≤ M) :
    ((Finset.Icc (⌊M⌋ + 1) ⌊2 * M⌋).card : ℝ)
      = (((⌊2*M⌋ : ℤ) : ℝ) - ((⌊M⌋ : ℤ) : ℝ)) := by
  have hcard : (Finset.Icc (⌊M⌋ + 1) ⌊2 * M⌋).card = (⌊2*M⌋ + 1 - (⌊M⌋ + 1)).toNat :=
    Int.card_Icc _ _
  have hnat : (⌊2*M⌋ + 1 - (⌊M⌋ + 1) : ℤ).toNat = (⌊2*M⌋ - ⌊M⌋ : ℤ).toNat := by congr 1; ring
  rw [hcard, hnat]
  have hle : ⌊M⌋ ≤ ⌊2*M⌋ := by
    have h : ((2 * ⌊M⌋ : ℤ) : ℝ) ≤ 2 * M := by
      push_cast
      linarith [Int.floor_le M]
    have h2 : (2 * ⌊M⌋ : ℤ) ≤ ⌊2 * M⌋ := Int.le_floor.mpr h
    have h3 : (0:ℤ) ≤ ⌊M⌋ := Int.le_floor.mpr (by push_cast; linarith)
    omega
  have h : (↑((⌊2*M⌋ - ⌊M⌋ : ℤ).toNat) : ℤ) = ⌊2*M⌋ - ⌊M⌋ := Int.toNat_sub_of_le hle
  have h2 : ((↑((⌊2*M⌋ - ⌊M⌋ : ℤ).toNat) : ℤ) : ℝ) = ((⌊2*M⌋ - ⌊M⌋ : ℤ) : ℝ) := by rw [h]
  push_cast at h2
  exact h2

/-- For `M ≥ 1/2` the range `R2 M` has at least `M/2` elements. -/
lemma asgs_card_R2_ge {M : ℝ} (hM : (1:ℝ)/2 ≤ M) : M/2 ≤ ((R2 M).card : ℝ) := by
  have hsub : Finset.Icc (⌊M⌋ + 1) ⌊2 * M⌋ ⊆ R2 M := by
    intro m hm
    rw [Finset.mem_Icc] at hm
    rw [R2, Finset.mem_filter, Finset.mem_Icc]
    refine ⟨⟨?_, hm.2⟩, ?_⟩
    · have : (0:ℤ) ≤ ⌊M⌋ := Int.le_floor.mpr (by push_cast; linarith)
      omega
    · have hlt : M < ((⌊M⌋ + 1 : ℤ) : ℝ) := by
        have h := Int.lt_floor_add_one M
        push_cast at h ⊢
        linarith
      have hle : ((⌊M⌋ + 1 : ℤ) : ℝ) ≤ (m : ℝ) := by exact_mod_cast hm.1
      linarith
  have hcard : ((Finset.Icc (⌊M⌋ + 1) ⌊2 * M⌋).card : ℝ) ≤ ((R2 M).card : ℝ) := by
    exact_mod_cast Finset.card_le_card hsub
  rw [asgs_card_Icc_floor (by linarith)] at hcard
  linarith [asgs_floor_diff_ge hM]

/-- For `M ≥ 1/2` the range `R1 M` has at least `M` elements. -/
lemma asgs_card_R1_ge {M : ℝ} (hM : (1:ℝ)/2 ≤ M) : M ≤ ((R1 M).card : ℝ) := by
  have hMpos : 0 < M := by linarith
  have h01M : (0:ℤ) ≤ ⌊M⌋ := Int.le_floor.mpr (by push_cast; linarith)
  have h02M : (0:ℤ) ≤ ⌊2*M⌋ := by
    have h : (1:ℤ) ≤ ⌊2*M⌋ := Int.le_floor.mpr (by push_cast; linarith)
    omega
  have hlt : M < ((⌊M⌋ + 1 : ℤ) : ℝ) := by
    have h := Int.lt_floor_add_one M
    push_cast at h ⊢
    linarith
  set P : Finset ℤ := Finset.Icc (⌊M⌋ + 1) ⌊2 * M⌋ with hP
  set N : Finset ℤ := P.image (fun m : ℤ => -m) with hN
  have hPsub : P ⊆ R1 M := by
    intro m hm
    rw [hP, Finset.mem_Icc] at hm
    rw [R1, Finset.mem_filter, Finset.mem_Icc]
    have hmpos : (0:ℝ) < (m:ℝ) := by
      have : (0:ℤ) < m := by omega
      exact_mod_cast this
    refine ⟨⟨?_, hm.2⟩, ?_⟩
    · omega
    · rw [abs_of_pos hmpos]
      have : ((⌊M⌋ + 1 : ℤ) : ℝ) ≤ (m:ℝ) := by exact_mod_cast hm.1
      linarith
  have hNsub : N ⊆ R1 M := by
    intro m hm
    rw [hN, Finset.mem_image] at hm
    obtain ⟨k, hk, rfl⟩ := hm
    rw [hP, Finset.mem_Icc] at hk
    rw [R1, Finset.mem_filter, Finset.mem_Icc]
    have hkpos : (0:ℝ) < (k:ℝ) := by
      have : (0:ℤ) < k := by omega
      exact_mod_cast this
    refine ⟨⟨?_, ?_⟩, ?_⟩
    · omega
    · omega
    · rw [show (((-k : ℤ)) : ℝ) = -(k:ℝ) by push_cast; ring, abs_neg, abs_of_pos hkpos]
      have : ((⌊M⌋ + 1 : ℤ) : ℝ) ≤ (k:ℝ) := by exact_mod_cast hk.1
      linarith
  have hdisj : Disjoint P N := by
    rw [Finset.disjoint_left]
    intro m hmP hmN
    rw [hN, Finset.mem_image] at hmN
    obtain ⟨k, hk, hkm⟩ := hmN
    rw [hP, Finset.mem_Icc] at hmP
    rw [hP, Finset.mem_Icc] at hk
    omega
  have hcard : (P ∪ N).card ≤ (R1 M).card := Finset.card_le_card (Finset.union_subset hPsub hNsub)
  have hcard2 : (P ∪ N).card = P.card + P.card := by
    rw [Finset.card_union_of_disjoint hdisj, hN,
      Finset.card_image_of_injective _ (fun a b h => by omega)]
  have hPcard : M/2 ≤ (P.card : ℝ) := by
    rw [hP, asgs_card_Icc_floor (by linarith)]
    exact asgs_floor_diff_ge hM
  have hthis : ((P ∪ N).card : ℝ) ≤ ((R1 M).card : ℝ) := by exact_mod_cast hcard
  rw [hcard2] at hthis
  push_cast at hthis
  linarith

/-- For `M ≥ 1/2` the sum of the elements of `R2 M` is at least `M²/2`. -/
lemma asgs_sum_R2_ge {M : ℝ} (hM : (1:ℝ)/2 ≤ M) : M^2/2 ≤ ∑ m ∈ R2 M, (m:ℝ) := by
  have hpt : ∀ m ∈ R2 M, M ≤ (m:ℝ) := fun m hm => (Finset.mem_filter.mp hm).2.le
  have h1 : ((R2 M).card : ℝ) * M ≤ ∑ m ∈ R2 M, (m:ℝ) := by
    have h := Finset.card_nsmul_le_sum (R2 M) (fun m : ℤ => (m:ℝ)) M hpt
    simpa [nsmul_eq_mul] using h
  have h2 : M/2 ≤ ((R2 M).card : ℝ) := asgs_card_R2_ge hM
  nlinarith [h1, h2, sq_nonneg M]

/-- For `M ≥ 1/2` the sum of `1/|m|` over `R1 M` is at least `1/2`. -/
lemma asgs_sum_R1_inv_ge {M : ℝ} (hM : (1:ℝ)/2 ≤ M) : 1/2 ≤ ∑ m ∈ R1 M, 1/|(m:ℝ)| := by
  have hMpos : 0 < M := by linarith
  have hpt : ∀ m ∈ R1 M, 1/(2*M) ≤ 1/|(m:ℝ)| := by
    intro m hm
    rw [R1, Finset.mem_filter, Finset.mem_Icc] at hm
    have hmle : (m:ℝ) ≤ ((⌊2*M⌋ : ℤ) : ℝ) := by exact_mod_cast hm.1.2
    have hmge : -(((⌊2*M⌋ : ℤ)) : ℝ) ≤ (m:ℝ) := by exact_mod_cast hm.1.1
    have h2M : ((⌊2*M⌋ : ℤ) : ℝ) ≤ 2*M := Int.floor_le (2*M)
    have h2Mpos : (0:ℝ) < 2*M := by linarith
    have hle : |(m:ℝ)| ≤ 2*M := by
      rw [abs_le]
      constructor <;> linarith
    exact one_div_le_one_div_of_le (lt_trans hMpos hm.2) hle
  have h1 : ((R1 M).card : ℝ) * (1/(2*M)) ≤ ∑ m ∈ R1 M, 1/|(m:ℝ)| := by
    have h := Finset.card_nsmul_le_sum (R1 M) (fun m : ℤ => 1/|(m:ℝ)|) (1/(2*M)) hpt
    simpa [nsmul_eq_mul] using h
  have h2 : M ≤ ((R1 M).card : ℝ) := asgs_card_R1_ge hM
  have h3 : M * (1/(2*M)) ≤ ((R1 M).card : ℝ) * (1/(2*M)) := by
    apply mul_le_mul_of_nonneg_right h2; positivity
  have h4 : M * (1/(2*M)) = 1/2 := by field_simp
  linarith

/-- The `m₃`-range is non-empty as soon as `K M₃ > 0`. -/
lemma asgs_card_R3_ge {K M₃ : ℝ} (hK : 0 < K) (hM₃ : 0 < M₃) : 1 ≤ (R3 K M₃).card := by
  have h0 : (0:ℤ) ≤ ⌊K*M₃⌋ := Int.le_floor.mpr (by push_cast; positivity)
  have hmem : (0:ℤ) ∈ R3 K M₃ := by
    rw [R3, Finset.mem_Icc]
    constructor <;> omega
  have := Finset.card_pos.mpr ⟨0, hmem⟩
  omega

end

end Work.GM.Affine
