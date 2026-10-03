import Mathlib
import Submission.Work.FIArea7.P231.ReducedDefs

set_option autoImplicit false

namespace Work.FIArea7.P231

open Finset
open scoped BigOperators

noncomputable section

/-- Reindex a single sum over `Icc 1 M` along the `c`-smooth decomposition `m = a·m'`:
`smooth part × c-free part`. -/
lemma sum_Icc_reindex_smooth {c M : ℕ} (hc : 1 ≤ c) (G : ℕ → ℂ) :
    (∑ m ∈ Finset.Icc 1 M, G m)
      = ∑ a ∈ (Finset.Icc 1 M).filter (IsSmooth c),
          ∑ m' ∈ (Finset.Icc 1 M).filter (fun m' => a * m' ≤ M ∧ Nat.Coprime m' c),
            G (a * m') := by
  have hbij : (∑ m ∈ Finset.Icc 1 M, G m)
      = ∑ p ∈ (((Finset.Icc 1 M).filter (IsSmooth c)).product (Finset.Icc 1 M)).filter
            (fun p => p.1 * p.2 ≤ M ∧ Nat.Coprime p.2 c),
          G (p.1 * p.2) := by
    refine Finset.sum_bij' (fun a _ => (cSm c a, cCp c a)) (fun p _ => p.1 * p.2)
      ?_ ?_ ?_ ?_ ?_
    · intro a ha
      obtain ⟨ha1, haM⟩ := Finset.mem_Icc.mp ha
      have ha0 : a ≠ 0 := by omega
      refine Finset.mem_filter.mpr ⟨Finset.mem_product.mpr ⟨?_, ?_⟩, ?_⟩
      · refine Finset.mem_filter.mpr ⟨Finset.mem_Icc.mpr ⟨?_, ?_⟩, cSm_smooth c a⟩
        · exact Nat.one_le_iff_ne_zero.mpr (cSm_pos ha0).ne'
        · exact le_trans (cSm_le ha0) haM
      · refine Finset.mem_Icc.mpr ⟨?_, ?_⟩
        · exact Nat.one_le_iff_ne_zero.mpr (cCp_ne_zero ha0)
        · exact le_trans (Nat.le_of_dvd (by omega) (cCp_dvd c a)) haM
      · exact ⟨by rw [cSm_mul_cCp ha0]; exact haM, cCp_coprime ha0⟩
    · intro p hp
      obtain ⟨hp1, hp2, hpc⟩ := Finset.mem_filter.mp hp
      obtain ⟨hpa, hpm⟩ := Finset.mem_product.mp hp1
      obtain ⟨ha1, haM⟩ := Finset.mem_Icc.mp (Finset.mem_filter.mp hpa).1
      obtain ⟨hm1, hmM⟩ := Finset.mem_Icc.mp hpm
      exact Finset.mem_Icc.mpr
        ⟨Nat.one_le_iff_ne_zero.mpr (Nat.mul_ne_zero (by omega) (by omega)), hp2⟩
    · intro a ha
      obtain ⟨ha1, haM⟩ := Finset.mem_Icc.mp ha
      exact cSm_mul_cCp (by omega)
    · intro p hp
      obtain ⟨hp1, hp2, hpc⟩ := Finset.mem_filter.mp hp
      obtain ⟨hpa, hpm⟩ := Finset.mem_product.mp hp1
      obtain ⟨_, haS⟩ := Finset.mem_filter.mp hpa
      obtain ⟨ha1, haM⟩ := Finset.mem_Icc.mp (Finset.mem_filter.mp hpa).1
      obtain ⟨hm1, hmM⟩ := Finset.mem_Icc.mp hpm
      have hp20 : p.2 ≠ 0 := by omega
      exact Prod.ext (cSm_mul_of_smooth_coprime hc haS hpc hp20)
        (cCp_mul_of_smooth_coprime hc haS hpc hp20)
    · intro a ha
      obtain ⟨ha1, haM⟩ := Finset.mem_Icc.mp ha
      rw [cSm_mul_cCp (by omega)]
  calc (∑ m ∈ Finset.Icc 1 M, G m)
      = ∑ p ∈ (((Finset.Icc 1 M).filter (IsSmooth c)).product (Finset.Icc 1 M)).filter
            (fun p => p.1 * p.2 ≤ M ∧ Nat.Coprime p.2 c), G (p.1 * p.2) := hbij
    _ = ∑ p ∈ ((Finset.Icc 1 M).filter (IsSmooth c)).product (Finset.Icc 1 M),
            (if p.1 * p.2 ≤ M ∧ Nat.Coprime p.2 c then G (p.1 * p.2) else 0) := by
          rw [Finset.sum_filter]
    _ = ∑ a ∈ (Finset.Icc 1 M).filter (IsSmooth c), ∑ b ∈ Finset.Icc 1 M,
            (if a * b ≤ M ∧ Nat.Coprime b c then G (a * b) else 0) := by
          exact Finset.sum_product ((Finset.Icc 1 M).filter (IsSmooth c)) (Finset.Icc 1 M) _
    _ = ∑ a ∈ (Finset.Icc 1 M).filter (IsSmooth c),
            ∑ b ∈ (Finset.Icc 1 M).filter (fun b => a * b ≤ M ∧ Nat.Coprime b c),
              G (a * b) := by
          refine Finset.sum_congr rfl (fun a ha => ?_)
          rw [Finset.sum_filter]

/-- The `a·m' ≤ M ∧ (m',c)=1` filter agrees with the range `Icc 1 (M/a)` restricted to `(·,c)=1`. -/
lemma filter_mul_le_eq {c M a : ℕ} (ha : 1 ≤ a) :
    (Finset.Icc 1 M).filter (fun m' => a * m' ≤ M ∧ Nat.Coprime m' c)
      = (Finset.Icc 1 (M / a)).filter (fun m' => Nat.Coprime m' c) := by
  have ha0 : 0 < a := by omega
  ext m'
  simp only [Finset.mem_filter, Finset.mem_Icc]
  constructor
  · rintro ⟨⟨h1, h2⟩, h3, h4⟩
    refine ⟨⟨h1, (Nat.le_div_iff_mul_le ha0).mpr ?_⟩, h4⟩
    rwa [Nat.mul_comm m' a]
  · rintro ⟨⟨h1, h2⟩, h4⟩
    exact ⟨⟨h1, le_trans h2 (Nat.div_le_self M a)⟩,
      by simpa [Nat.mul_comm] using (Nat.le_div_iff_mul_le ha0).mp h2, h4⟩

end

end Work.FIArea7.P231

namespace Work.FIArea7.P231

open Finset
open scoped BigOperators

noncomputable section

/-- One-variable reindexing, "indicator" form: the inner sum runs over `Icc 1 (M/a)`. -/
lemma sum_Icc_reindex_smooth' {c M : ℕ} (hc : 1 ≤ c) (G : ℕ → ℂ) :
    (∑ m ∈ Finset.Icc 1 M, G m)
      = ∑ a ∈ (Finset.Icc 1 M).filter (IsSmooth c),
          ∑ m' ∈ Finset.Icc 1 (M / a), (if Nat.Coprime m' c then G (a * m') else 0) := by
  rw [sum_Icc_reindex_smooth hc G]
  refine Finset.sum_congr rfl (fun a ha => ?_)
  rw [filter_mul_le_eq (Finset.mem_Icc.mp (Finset.mem_filter.mp ha).1).1, Finset.sum_filter]

/-- Push a constant `if` inside a sum. -/
lemma sum_ite_const {p : Prop} [Decidable p] {ι : Type*} (s : Finset ι) (f : ι → ℂ) :
    (if p then ∑ i ∈ s, f i else 0) = ∑ i ∈ s, (if p then f i else 0) := by
  by_cases hp : p <;> simp [hp]

/-- Two-variable reindexing along the `c`-smooth decomposition. -/
lemma sum_Icc_Icc_reindex_smooth {c M N : ℕ} (hc : 1 ≤ c) (F : ℕ → ℕ → ℂ) :
    (∑ m ∈ Finset.Icc 1 M, ∑ n ∈ Finset.Icc 1 N, F m n)
      = ∑ a ∈ (Finset.Icc 1 M).filter (IsSmooth c),
          ∑ m' ∈ Finset.Icc 1 (M / a),
            ∑ b ∈ (Finset.Icc 1 N).filter (IsSmooth c),
              ∑ n' ∈ Finset.Icc 1 (N / b),
                (if Nat.Coprime n' c then
                  (if Nat.Coprime m' c then F (a * m') (b * n') else 0) else 0) := by
  rw [sum_Icc_reindex_smooth' hc (fun m => ∑ n ∈ Finset.Icc 1 N, F m n)]
  refine Finset.sum_congr rfl (fun a ha => Finset.sum_congr rfl (fun m' hm' => ?_))
  rw [sum_ite_const (p := Nat.Coprime m' c) (Finset.Icc 1 N) (fun n => F (a * m') n)]
  exact sum_Icc_reindex_smooth' (M := N) hc (fun n => if Nat.Coprime m' c then F (a * m') n else 0)

end

end Work.FIArea7.P231
