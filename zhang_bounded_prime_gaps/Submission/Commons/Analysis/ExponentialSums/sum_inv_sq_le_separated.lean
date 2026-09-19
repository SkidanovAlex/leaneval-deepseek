import Mathlib.Algebra.Ring.IsFormallyReal
import Mathlib.NumberTheory.ZetaValues

namespace Commons.Analysis.ExponentialSums

open scoped BigOperators

/-- Partial sums of `∑_{n ≥ 1} 1/n²` are bounded by the value `π²/6` of the whole series. -/
private lemma sum_range_inv_sq_add_one_le (n : ℕ) :
    ∑ i ∈ Finset.range n, (1 : ℝ) / (((i : ℕ) : ℝ) + 1) ^ 2 ≤ Real.pi ^ 2 / 6 := by
  have hs : Summable (fun j : ℕ => (1 : ℝ) / (j : ℝ) ^ 2) := hasSum_zeta_two.summable
  have himg : ∑ k ∈ (Finset.range n).image (fun i : ℕ => i + 1), (1 : ℝ) / (k : ℝ) ^ 2
      = ∑ i ∈ Finset.range n, (1 : ℝ) / (((i : ℕ) : ℝ) + 1) ^ 2 := by
    rw [Finset.sum_image]
    · refine Finset.sum_congr rfl ?_
      intro i _
      rw [Nat.cast_add, Nat.cast_one]
    · intro a _ b _ hab
      exact Nat.add_right_cancel hab
  calc ∑ i ∈ Finset.range n, (1 : ℝ) / (((i : ℕ) : ℝ) + 1) ^ 2
      = ∑ k ∈ (Finset.range n).image (fun i : ℕ => i + 1), (1 : ℝ) / (k : ℝ) ^ 2 := himg.symm
    _ ≤ ∑ k ∈ Finset.range (n + 1), (1 : ℝ) / (k : ℝ) ^ 2 := by
        refine Finset.sum_le_sum_of_subset_of_nonneg ?_ ?_
        · intro x hx
          simp only [Finset.mem_image, Finset.mem_range] at hx ⊢
          obtain ⟨i, hi, rfl⟩ := hx
          exact Nat.succ_lt_succ hi
        · intro k _ _
          positivity
    _ ≤ ∑' k : ℕ, (1 : ℝ) / (k : ℝ) ^ 2 :=
        hs.sum_le_tsum _ (fun k _ => by positivity)
    _ = Real.pi ^ 2 / 6 := hasSum_zeta_two.tsum_eq

/-- One-sided version: a finite set of reals that are all at least `δ` and pairwise
`δ`-separated has reciprocal-square sum at most `π²/(6δ²)`, the value approached by the
one-sided lattice `δ, 2δ, 3δ, ...`. -/
private lemma sum_inv_sq_le_of_pos {B : Finset ℝ} {δ : ℝ} (hδ : 0 < δ)
    (h0 : ∀ b ∈ B, δ ≤ b) (hsep : ∀ b ∈ B, ∀ c ∈ B, b ≠ c → δ ≤ |b - c|) :
    ∑ b ∈ B, (1 : ℝ) / b ^ 2 ≤ Real.pi ^ 2 / (6 * δ ^ 2) := by
  have hsum_eq :
      ∑ b ∈ B, (1 : ℝ) / b ^ 2
        = ∑ i : Fin B.card, (1 : ℝ) / ((B.orderEmbOfFin rfl) i) ^ 2 := by
    conv_lhs => rw [← Finset.map_orderEmbOfFin_univ B (rfl : B.card = B.card)]
    rw [Finset.sum_map]
    rfl
  rw [hsum_eq]
  -- the `i`-th smallest element of `B` is at least `(i+1)·δ`
  have hkey : ∀ (i : ℕ) (hi : i < B.card),
      ((i : ℝ) + 1) * δ ≤ (B.orderEmbOfFin rfl) ⟨i, hi⟩ := by
    intro i
    induction i with
    | zero =>
        intro hi
        have hmem : (B.orderEmbOfFin rfl) ⟨0, hi⟩ ∈ B := Finset.orderEmbOfFin_mem B rfl _
        have := h0 _ hmem
        simpa using this
    | succ i ih =>
        intro hi
        have hilt : i < B.card := Nat.lt_of_succ_lt hi
        have hrec := ih hilt
        have hmem1 : (B.orderEmbOfFin rfl) ⟨i, hilt⟩ ∈ B := Finset.orderEmbOfFin_mem B rfl _
        have hmem2 : (B.orderEmbOfFin rfl) ⟨i + 1, hi⟩ ∈ B := Finset.orderEmbOfFin_mem B rfl _
        have hlt : (⟨i, hilt⟩ : Fin B.card) < ⟨i + 1, hi⟩ :=
          Fin.mk_lt_mk.mpr (Nat.lt_succ_self i)
        have hlt' : (B.orderEmbOfFin rfl) ⟨i, hilt⟩ < (B.orderEmbOfFin rfl) ⟨i + 1, hi⟩ :=
          (OrderEmbedding.lt_iff_lt (B.orderEmbOfFin rfl)).mpr hlt
        have hsp := hsep _ hmem1 _ hmem2 (ne_of_lt hlt')
        have hsp' : δ ≤ (B.orderEmbOfFin rfl) ⟨i + 1, hi⟩ - (B.orderEmbOfFin rfl) ⟨i, hilt⟩ := by
          rw [abs_of_neg (by linarith)] at hsp
          linarith
        have hcast : ((↑(i + 1) : ℝ) + 1) * δ = ((↑i : ℝ) + 1) * δ + δ := by
          push_cast; ring
        rw [hcast]
        linarith
  calc ∑ i : Fin B.card, (1 : ℝ) / ((B.orderEmbOfFin rfl) i) ^ 2
      ≤ ∑ i : Fin B.card, (1 : ℝ) / ((((i : ℕ) : ℝ) + 1) * δ) ^ 2 := by
        refine Finset.sum_le_sum ?_
        intro i _
        have hk := hkey i.val i.isLt
        have hpos : 0 < (((i : ℕ) : ℝ) + 1) * δ := by positivity
        have hle : (((i : ℕ) : ℝ) + 1) * δ ≤ (B.orderEmbOfFin rfl) i := by
          simpa using hk
        have hsq : ((((i : ℕ) : ℝ) + 1) * δ) ^ 2 ≤ ((B.orderEmbOfFin rfl) i) ^ 2 :=
          pow_le_pow_left₀ (le_of_lt hpos) hle 2
        exact one_div_le_one_div_of_le (pow_pos hpos 2) hsq
    _ = (1 / δ ^ 2) * ∑ i : Fin B.card, (1 : ℝ) / (((i : ℕ) : ℝ) + 1) ^ 2 := by
        rw [Finset.mul_sum]
        refine Finset.sum_congr rfl ?_
        intro i _
        have hk : (((i : ℕ) : ℝ) + 1) ≠ 0 := by positivity
        have hd : δ ≠ 0 := ne_of_gt hδ
        field_simp
    _ ≤ (1 / δ ^ 2) * (Real.pi ^ 2 / 6) := by
        refine mul_le_mul_of_nonneg_left ?_ (by positivity)
        rw [Fin.sum_univ_eq_sum_range (fun k : ℕ => (1 : ℝ) / (((k : ℕ) : ℝ) + 1) ^ 2) B.card]
        exact sum_range_inv_sq_add_one_le B.card
    _ = Real.pi ^ 2 / (6 * δ ^ 2) := by
        have hd2 : δ ^ 2 ≠ 0 := pow_ne_zero 2 (ne_of_gt hδ)
        field_simp

/-- For a finite set `A` of nonzero reals, each of modulus at least `δ`, and pairwise
`δ`-separated, the sum of reciprocal squares is at most `π²/(3δ²)` (the value attained by the
two-sided lattice `±δ, ±2δ, ...`). -/
theorem sum_inv_sq_le_separated {A : Finset ℝ} {δ : ℝ} (hδ : 0 < δ)
    (h0 : ∀ a ∈ A, δ ≤ |a|) (hsep : ∀ a ∈ A, ∀ b ∈ A, a ≠ b → δ ≤ |a - b|) :
    ∑ a ∈ A, (1 : ℝ) / a ^ 2 ≤ Real.pi ^ 2 / (3 * δ ^ 2) := by
  set P := A.filter (fun a => 0 < a) with hP
  set N := A.filter (fun a => a < 0) with hN
  have hAN : A = P ∪ N := by
    ext a
    simp only [hP, hN, Finset.mem_union, Finset.mem_filter]
    constructor
    · intro ha
      have ha0 : a ≠ 0 := by
        intro h
        have := h0 a ha
        rw [h, abs_zero] at this
        linarith
      rcases lt_or_gt_of_ne ha0 with h | h
      · exact Or.inr ⟨ha, h⟩
      · exact Or.inl ⟨ha, h⟩
    · rintro (⟨ha, _⟩ | ⟨ha, _⟩) <;> exact ha
  have hdisj : Disjoint P N := by
    rw [Finset.disjoint_left]
    intro a haP haN
    rw [hP, Finset.mem_filter] at haP
    rw [hN, Finset.mem_filter] at haN
    linarith [haP.2, haN.2]
  have hPbound : ∑ a ∈ P, (1 : ℝ) / a ^ 2 ≤ Real.pi ^ 2 / (6 * δ ^ 2) := by
    refine sum_inv_sq_le_of_pos hδ ?_ ?_
    · intro b hb
      rw [hP, Finset.mem_filter] at hb
      have hb0 : 0 < b := hb.2
      have h' := h0 b hb.1
      rwa [abs_of_pos hb0] at h'
    · intro b hb c hc hne
      rw [hP, Finset.mem_filter] at hb hc
      exact hsep b hb.1 c hc.1 hne
  set M := N.image (fun a => -a) with hM
  have hMbound : ∑ c ∈ M, (1 : ℝ) / c ^ 2 ≤ Real.pi ^ 2 / (6 * δ ^ 2) := by
    refine sum_inv_sq_le_of_pos hδ ?_ ?_
    · intro c hc
      rw [hM, Finset.mem_image] at hc
      obtain ⟨a, haN, rfl⟩ := hc
      rw [hN, Finset.mem_filter] at haN
      have h' := h0 a haN.1
      rw [abs_of_neg haN.2] at h'
      exact h'
    · intro c1 hc1 c2 hc2 hne
      rw [hM, Finset.mem_image] at hc1 hc2
      obtain ⟨a1, ha1, rfl⟩ := hc1
      obtain ⟨a2, ha2, rfl⟩ := hc2
      rw [hN, Finset.mem_filter] at ha1 ha2
      have hne' : a1 ≠ a2 := by rintro rfl; exact hne rfl
      have h := hsep a1 ha1.1 a2 ha2.1 hne'
      have heq : |(-a1) - (-a2)| = |a1 - a2| := by
        rw [show (-a1) - (-a2) = -(a1 - a2) by ring, abs_neg]
      rw [heq]
      exact h
  have hNbound : ∑ a ∈ N, (1 : ℝ) / a ^ 2 ≤ Real.pi ^ 2 / (6 * δ ^ 2) := by
    have hinj : Set.InjOn (fun a : ℝ => -a) ↑N := by
      intro a _ b _ h
      have : -a = -b := h
      linarith
    have h1 : ∑ c ∈ M, (1 : ℝ) / c ^ 2 = ∑ a ∈ N, (1 : ℝ) / (-a) ^ 2 := by
      rw [hM]
      exact Finset.sum_image hinj
    have h2 : ∑ a ∈ N, (1 : ℝ) / (-a) ^ 2 = ∑ a ∈ N, (1 : ℝ) / a ^ 2 := by
      refine Finset.sum_congr rfl ?_
      intro a _
      ring_nf
    rw [← h2, ← h1]
    exact hMbound
  rw [hAN, Finset.sum_union hdisj]
  have htwo : Real.pi ^ 2 / (6 * δ ^ 2) + Real.pi ^ 2 / (6 * δ ^ 2)
      = Real.pi ^ 2 / (3 * δ ^ 2) := by
    have hd2 : δ ^ 2 ≠ 0 := pow_ne_zero 2 (ne_of_gt hδ)
    field_simp
    ring
  linarith [hPbound, hNbound, htwo]

end Commons.Analysis.ExponentialSums