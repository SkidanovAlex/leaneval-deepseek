import Mathlib
import Submission.Work.GM.S3.prop101_defs

namespace Work.GM.S3

open Finset

/-!
# The reflection `(m₁,m₂,m₃) ↦ (-m₁,-m₂,-m₃)` and the two halves of `Bsum`

`Bsum` is the triple sum `Σ_{m₁ ∈ idx1 M₁} Σ_{m₂ ∈ idxM M} Σ_{m₃ ∈ idxM M} R̃(a₂(m,v))²`.
The change of variables `m ↦ -m` in all three indices preserves `arg2`, permutes the index
sets `idx1 M₁`, `idxM M` (both symmetric under negation) and exchanges the two halves
`m₂ < 0` and `m₂ > 0` of `idxM M`; since `|m₂| > M ≥ 1` there is no `m₂ = 0`.  Hence the two
halves are equal and `Bsum = 2 * BsumPos`.

The main combinatorial statement is `sum_triple_reflect`, stated for an arbitrary summand
invariant under the reflection.
-/

/-- `idx1 M₁` is invariant under `m ↦ -m`. -/
lemma neg_mem_idx1 {M₁ : ℝ} {m : ℤ} (h : m ∈ idx1 M₁) : -m ∈ idx1 M₁ := by
  simp only [idx1, Finset.mem_filter, Finset.mem_Icc] at h ⊢
  obtain ⟨⟨h1, h2⟩, h3⟩ := h
  refine ⟨⟨by omega, by omega⟩, ?_⟩
  simpa using h3

/-- `idxM M` is invariant under `m ↦ -m`. -/
lemma neg_mem_idxM {M : ℝ} {m : ℤ} (h : m ∈ idxM M) : -m ∈ idxM M := by
  simp only [idxM, Finset.mem_filter, Finset.mem_Icc] at h ⊢
  obtain ⟨⟨h1, h2⟩, h3⟩ := h
  refine ⟨⟨by omega, by omega⟩, ?_⟩
  simpa using h3

/-- Reindexing a sum over `idx1 M₁` by `m ↦ -m`. -/
lemma sum_neg_idx1 (M₁ : ℝ) (g : ℤ → ℝ) :
    ∑ m ∈ idx1 M₁, g (-m) = ∑ m ∈ idx1 M₁, g m := by
  refine Finset.sum_nbij' (fun m : ℤ => -m) (fun m : ℤ => -m) ?_ ?_ ?_ ?_ ?_
  · intro a ha; exact neg_mem_idx1 ha
  · intro a ha; exact neg_mem_idx1 ha
  · intro a ha; simp
  · intro a ha; simp
  · intro a ha; simp

/-- Reindexing a sum over `idxM M` by `m ↦ -m`. -/
lemma sum_neg_idxM (M : ℝ) (g : ℤ → ℝ) :
    ∑ m ∈ idxM M, g (-m) = ∑ m ∈ idxM M, g m := by
  refine Finset.sum_nbij' (fun m : ℤ => -m) (fun m : ℤ => -m) ?_ ?_ ?_ ?_ ?_
  · intro a ha; exact neg_mem_idxM ha
  · intro a ha; exact neg_mem_idxM ha
  · intro a ha; simp
  · intro a ha; simp
  · intro a ha; simp

/-- For `0 ≤ M`, the positive part of `idxM M` is exactly `idxMpos M`. -/
lemma mem_idxMpos_iff {M : ℝ} (hM : 0 ≤ M) {m : ℤ} :
    m ∈ idxMpos M ↔ m ∈ idxM M ∧ 0 < m := by
  have hf : (0 : ℤ) ≤ ⌊2 * M⌋ := Int.floor_nonneg.mpr (by linarith)
  simp only [idxMpos, idxM, Finset.mem_filter, Finset.mem_Icc]
  constructor
  · rintro ⟨⟨h1, h2⟩, h3⟩
    have hpos : (0 : ℤ) < m := by omega
    refine ⟨⟨⟨by omega, h2⟩, ?_⟩, hpos⟩
    have : |(m : ℝ)| = (m : ℝ) := abs_of_pos (by exact_mod_cast hpos)
    rw [this]; exact h3
  · rintro ⟨⟨⟨h1, h2⟩, h3⟩, h4⟩
    have hcast : (0 : ℝ) < (m : ℝ) := by exact_mod_cast h4
    refine ⟨⟨by omega, h2⟩, ?_⟩
    rwa [abs_of_pos hcast] at h3

/-- For `0 ≤ M`, the negative part of `idxM M` is the image of `idxMpos M` under `m ↦ -m`. -/
lemma neg_mem_idxMpos_iff {M : ℝ} (hM : 0 ≤ M) {m : ℤ} :
    -m ∈ idxMpos M ↔ m ∈ idxM M ∧ m < 0 := by
  have hf : (0 : ℤ) ≤ ⌊2 * M⌋ := Int.floor_nonneg.mpr (by linarith)
  simp only [idxMpos, idxM, Finset.mem_filter, Finset.mem_Icc, Int.cast_neg]
  constructor
  · rintro ⟨⟨h1, h2⟩, h3⟩
    have hneg : m < 0 := by omega
    refine ⟨⟨⟨by omega, by omega⟩, ?_⟩, hneg⟩
    have : |(m : ℝ)| = -(m : ℝ) := abs_of_neg (by exact_mod_cast hneg)
    rw [this]; exact h3
  · rintro ⟨⟨⟨h1, h2⟩, h3⟩, h4⟩
    have hcast : (m : ℝ) < 0 := by exact_mod_cast h4
    refine ⟨⟨by omega, by omega⟩, ?_⟩
    rwa [abs_of_neg hcast] at h3

/-- For `0 ≤ M`, `(idxM M).filter (0 < ·) = idxMpos M`. -/
lemma filter_pos_idxM_eq_idxMpos {M : ℝ} (hM : 0 ≤ M) :
    (idxM M).filter (fun m : ℤ => 0 < m) = idxMpos M := by
  ext m
  simp only [Finset.mem_filter]
  exact (mem_idxMpos_iff hM).symm

/-- Reindexing the negative part of `idxM M` by `m ↦ -m`: it becomes `idxMpos M`. -/
lemma sum_neg_idxMneg {M : ℝ} (hM : 0 ≤ M) (g : ℤ → ℝ) :
    ∑ m ∈ (idxM M).filter (fun m : ℤ => m < 0), g (-m) = ∑ m ∈ idxMpos M, g m := by
  refine Finset.sum_equiv (Equiv.neg ℤ) ?_ ?_
  · intro m
    simp only [Finset.mem_filter]
    exact (neg_mem_idxMpos_iff hM).symm
  · intro m hm
    rfl

/-- An element of `idxM M` is nonzero when `M > 0` (since `M < |m|`). -/
lemma ne_zero_of_mem_idxM {M : ℝ} {m : ℤ} (hm : m ∈ idxM M) (hM : 0 < M) : m ≠ 0 := by
  simp only [idxM, Finset.mem_filter, Finset.mem_Icc] at hm
  rintro rfl
  simp at hm
  linarith [hm.2]

/-- For `M > 0` the two ways of writing the "non-positive" part of `idxM M` agree. -/
lemma filter_lt_zero_eq_filter_not_pos {M : ℝ} (hM : 0 < M) :
    (idxM M).filter (fun m : ℤ => m < 0) = (idxM M).filter (fun m : ℤ => ¬ 0 < m) := by
  apply Finset.filter_congr
  intro m hm
  have hne := ne_zero_of_mem_idxM hm hM
  omega

/-- Splitting the `m₂`-sum of `Σ_{m₁ ∈ idx1 M₁} Σ_{m₂ ∈ idxM M} Σ_{m₃ ∈ idxM M}` into its
positive (`idxMpos M`) and negative (`m₂ < 0`) parts.  Uses `M > 0`, so that `m₂ ≠ 0`. -/
lemma sum_triple_split (M₁ M : ℝ) (F : ℤ → ℤ → ℤ → ℝ) (hM : 0 < M) :
    (∑ m₁ ∈ idx1 M₁, ∑ m₂ ∈ idxM M, ∑ m₃ ∈ idxM M, F m₁ m₂ m₃)
      = (∑ m₁ ∈ idx1 M₁, ∑ m₂ ∈ idxMpos M, ∑ m₃ ∈ idxM M, F m₁ m₂ m₃)
      + (∑ m₁ ∈ idx1 M₁, ∑ m₂ ∈ (idxM M).filter (fun m => m < 0),
          ∑ m₃ ∈ idxM M, F m₁ m₂ m₃) := by
  have hM0 : 0 ≤ M := le_of_lt hM
  rw [← Finset.sum_add_distrib]
  apply Finset.sum_congr rfl
  intro m₁ _
  rw [← Finset.sum_filter_add_sum_filter_not (idxM M) (fun m : ℤ => 0 < m)
        (fun m₂ => ∑ m₃ ∈ idxM M, F m₁ m₂ m₃)]
  rw [filter_pos_idxM_eq_idxMpos hM0, ← filter_lt_zero_eq_filter_not_pos hM]

/-- The `m₂ < 0` half of a triple sum with a reflection-invariant summand equals its `m₂ > 0`
half.  The reflection `(m₁,m₂,m₃) ↦ (-m₁,-m₂,-m₃)` maps `idx1 M₁ × (idxM M ∩ {m₂ < 0}) × idxM M`
bijectively onto `idx1 M₁ × idxMpos M × idxM M`. -/
lemma sum_triple_neg_eq_pos (M₁ M : ℝ) (F : ℤ → ℤ → ℤ → ℝ)
    (hF : ∀ m₁ m₂ m₃ : ℤ, F (-m₁) (-m₂) (-m₃) = F m₁ m₂ m₃) (hM : 1 ≤ M) :
    (∑ m₁ ∈ idx1 M₁, ∑ m₂ ∈ (idxM M).filter (fun m => m < 0), ∑ m₃ ∈ idxM M, F m₁ m₂ m₃)
      = (∑ m₁ ∈ idx1 M₁, ∑ m₂ ∈ idxMpos M, ∑ m₃ ∈ idxM M, F m₁ m₂ m₃) := by
  have hM0 : 0 ≤ M := by linarith
  -- reflect `m₃`
  have h1 : (∑ m₁ ∈ idx1 M₁, ∑ m₂ ∈ (idxM M).filter (fun m => m < 0), ∑ m₃ ∈ idxM M, F m₁ m₂ m₃)
      = (∑ m₁ ∈ idx1 M₁, ∑ m₂ ∈ (idxM M).filter (fun m => m < 0),
          ∑ m₃ ∈ idxM M, F m₁ m₂ (-m₃)) := by
    apply Finset.sum_congr rfl
    intro m₁ _
    apply Finset.sum_congr rfl
    intro m₂ _
    exact (sum_neg_idxM M (fun m₃ => F m₁ m₂ m₃)).symm
  -- reflect `m₁`
  have h2 : (∑ m₁ ∈ idx1 M₁, ∑ m₂ ∈ (idxM M).filter (fun m => m < 0), ∑ m₃ ∈ idxM M, F m₁ m₂ (-m₃))
      = (∑ m₁ ∈ idx1 M₁, ∑ m₂ ∈ (idxM M).filter (fun m => m < 0),
          ∑ m₃ ∈ idxM M, F (-m₁) m₂ (-m₃)) :=
    (sum_neg_idx1 M₁ (fun m₁ =>
      ∑ m₂ ∈ (idxM M).filter (fun m => m < 0), ∑ m₃ ∈ idxM M, F m₁ m₂ (-m₃))).symm
  -- reflect `m₂`: the negative part of `idxM M` is the reflection of `idxMpos M`
  have h3 : (∑ m₁ ∈ idx1 M₁, ∑ m₂ ∈ (idxM M).filter (fun m => m < 0), ∑ m₃ ∈ idxM M, F (-m₁) m₂ (-m₃))
      = (∑ m₁ ∈ idx1 M₁, ∑ m₂ ∈ idxMpos M, ∑ m₃ ∈ idxM M, F (-m₁) (-m₂) (-m₃)) := by
    apply Finset.sum_congr rfl
    intro m₁ _
    simpa using sum_neg_idxMneg hM0 (fun m₂ => ∑ m₃ ∈ idxM M, F (-m₁) (-m₂) (-m₃))
  have h4 : (∑ m₁ ∈ idx1 M₁, ∑ m₂ ∈ idxMpos M, ∑ m₃ ∈ idxM M, F (-m₁) (-m₂) (-m₃))
      = (∑ m₁ ∈ idx1 M₁, ∑ m₂ ∈ idxMpos M, ∑ m₃ ∈ idxM M, F m₁ m₂ m₃) := by
    apply Finset.sum_congr rfl
    intro m₁ _
    apply Finset.sum_congr rfl
    intro m₂ _
    apply Finset.sum_congr rfl
    intro m₃ _
    exact hF m₁ m₂ m₃
  exact h1.trans (h2.trans (h3.trans h4))

/-- For a summand invariant under `(m₁,m₂,m₃) ↦ (-m₁,-m₂,-m₃)`, the triple sum over
`idx1 M₁ × idxM M × idxM M` is twice the sum over `idx1 M₁ × idxMpos M × idxM M`. -/
lemma sum_triple_reflect (M₁ M : ℝ) (F : ℤ → ℤ → ℤ → ℝ)
    (hF : ∀ m₁ m₂ m₃ : ℤ, F (-m₁) (-m₂) (-m₃) = F m₁ m₂ m₃) (hM : 1 ≤ M) :
    (∑ m₁ ∈ idx1 M₁, ∑ m₂ ∈ idxM M, ∑ m₃ ∈ idxM M, F m₁ m₂ m₃)
      = 2 * (∑ m₁ ∈ idx1 M₁, ∑ m₂ ∈ idxMpos M, ∑ m₃ ∈ idxM M, F m₁ m₂ m₃) := by
  have hs := sum_triple_split M₁ M F (by linarith)
  have hn := sum_triple_neg_eq_pos M₁ M F hF hM
  rw [hs, hn]
  ring

/-- The reflection of the three summation indices preserves `arg2`. -/
lemma arg2_neg (m₁ m₂ m₃ : ℤ) (v : ℝ) :
    arg2 (-m₁) (-m₂) (-m₃) v = arg2 m₁ m₂ m₃ v := by
  simp only [arg2, Int.cast_neg]
  ring

/-- The `m₂ < 0` half of `Bsum` equals its `m₂ > 0` half (`BsumPos`): the reflection
`(m₁,m₂,m₃) ↦ (-m₁,-m₂,-m₃)` is a bijection from `idx1 M₁ × (idxM M ∩ {m₂ < 0}) × idxM M` onto
`idx1 M₁ × idxMpos M × idxM M` preserving `arg2`, while `idx1 M₁` and `idxM M` are symmetric under
`m ↦ -m`.  Requires `1 ≤ M` (so that `m₂ ∈ idxM M` with `m₂ > 0` iff `m₂ ∈ idxMpos M`; sufficient
in fact is `0 < M`). -/
theorem bsum_reflect (N : ℕ) (W : Finset ℝ) (B M₁ M : ℝ) (ψ₁ ψ₂ : ℝ → ℝ)
    (hM : 1 ≤ M) (v : ℝ) :
    Work.GM.S3.Bsum N W B M₁ M ψ₁ ψ₂ v = 2 * Work.GM.S3.BsumPos N W B M₁ M ψ₁ ψ₂ v := by
  have hF : ∀ m₁ m₂ m₃ : ℤ,
      Rtilde W N B ψ₁ ψ₂ (arg2 (-m₁) (-m₂) (-m₃) v) ^ 2
        = Rtilde W N B ψ₁ ψ₂ (arg2 m₁ m₂ m₃ v) ^ 2 := by
    intro m₁ m₂ m₃
    rw [arg2_neg m₁ m₂ m₃ v]
  simpa only [Bsum, BsumPos] using
    sum_triple_reflect M₁ M (fun m₁ m₂ m₃ : ℤ => Rtilde W N B ψ₁ ψ₂ (arg2 m₁ m₂ m₃ v) ^ 2) hF hM

end Work.GM.S3
