import Mathlib
import Submission.Commons.Analysis.Asymptotics.geom_sum_range_le

open Finset

/-
# A lacunary finite-sum bound

This file proves `Commons.Analysis.Sum.lacunary_finset_sum_inv_le`: for a finite set `D` of
positive reals that is `Λ`-lacunary (`Λ * M ≤ N` whenever `M < N` in `D`), the sum of
`(A * N ^ d)⁻¹` over those `N ∈ D` with `X < A * N ^ d` is at most
`(1 - (Λ ^ d)⁻¹)⁻¹ * X⁻¹`.

The key point is that the reciprocals decay geometrically along the lacunary set: if
`M < N` then `Λ * M ≤ N`, so `(A * N ^ d)⁻¹ ≤ (Λ ^ d)⁻¹ * (A * M ^ d)⁻¹`.  Hence the sum
is bounded by the geometric series beginning at the smallest admissible element, which is
`> (X / A) ^ (1/d)` and therefore contributes at most `X⁻¹`.

The proof enumerates the relevant finite set in increasing order via `Finset.orderEmbOfFin`
and applies the elementary geometric-decay estimate `sum_range_le_of_geometric`.
-/

namespace Commons.Analysis.Sum

/-- Geometric decay estimate for a sequence `u` with `u (n + 1) ≤ r * u n`, `0 ≤ r < 1` and
`0 ≤ u 0`: the partial sums up to `N` are bounded by `u 0 / (1 - r)`. -/
theorem sum_range_le_of_geometric {r : ℝ} (hr0 : 0 ≤ r) (hr1 : r < 1) {u : ℕ → ℝ}
    (hu0 : 0 ≤ u 0) (hrec : ∀ n, u (n + 1) ≤ r * u n) (N : ℕ) :
    ∑ n ∈ Finset.range N, u n ≤ u 0 * (1 - r)⁻¹ := by
  have hpow : ∀ n, u n ≤ r ^ n * u 0 := by
    intro n
    induction n with
    | zero => simp
    | succ k ih =>
      calc u (k + 1) ≤ r * u k := hrec k
        _ ≤ r * (r ^ k * u 0) := by
              apply mul_le_mul_of_nonneg_left ih hr0
        _ = r ^ (k + 1) * u 0 := by rw [pow_succ']; ring
  calc ∑ n ∈ Finset.range N, u n ≤ ∑ n ∈ Finset.range N, r ^ n * u 0 :=
        Finset.sum_le_sum (fun n _ => hpow n)
    _ = (∑ n ∈ Finset.range N, r ^ n) * u 0 := by rw [Finset.sum_mul]
    _ ≤ (1 - r)⁻¹ * u 0 := by
        apply mul_le_mul_of_nonneg_right _ hu0
        have h := Commons.Analysis.Asymptotics.geom_sum_range_le hr0 hr1 N
        rwa [one_div] at h
    _ = u 0 * (1 - r)⁻¹ := by ring

/-- Finite lacunary sum bound relative to a lower-bound element: if `S ⊆ D` is nonempty with
`m ∈ S` and `m ≤ N` for all `N ∈ S`, then `∑_{N ∈ S} (A * N ^ d)⁻¹ ≤ (1 - (Λ ^ d)⁻¹)⁻¹ * (A * m ^ d)⁻¹`. -/
theorem lacunary_finset_sum_le_min {Λ : ℝ} (hΛ : 1 < Λ) (d : ℕ) (hd : 1 ≤ d) (A : ℝ) (hA : 0 < A)
    (D : Finset ℝ) (hpos : ∀ N ∈ D, 0 < N)
    (hlac : ∀ M ∈ D, ∀ N ∈ D, M < N → Λ * M ≤ N)
    (S : Finset ℝ) (hSD : S ⊆ D) (hS : S.Nonempty)
    {m : ℝ} (hmS : m ∈ S) (hmin : ∀ N ∈ S, m ≤ N) :
    ∑ N ∈ S, (A * N ^ d)⁻¹ ≤ (1 - (Λ ^ d)⁻¹)⁻¹ * (A * m ^ d)⁻¹ := by
  have hΛpos : 0 < Λ := lt_trans zero_lt_one hΛ
  have hd0 : d ≠ 0 := by omega
  have hld1 : 1 < Λ ^ d := one_lt_pow₀ hΛ hd0
  set r : ℝ := (Λ ^ d)⁻¹ with hr
  have hr0 : 0 ≤ r := by rw [hr]; positivity
  have hr1 : r < 1 := by rw [hr]; exact inv_lt_one_of_one_lt₀ hld1
  have hkpos : 0 < S.card := Finset.card_pos.mpr hS
  let f := S.orderEmbOfFin rfl
  set u : ℕ → ℝ := (fun n => if h : n < S.card then (A * (f ⟨n, h⟩) ^ d)⁻¹ else 0) with hu
  have hu_pos : ∀ n (hn : n < S.card), u n = (A * (f ⟨n, hn⟩) ^ d)⁻¹ := by
    intro n hn; rw [hu]; exact dif_pos hn
  have hu_neg : ∀ n, ¬ (n < S.card) → u n = 0 := by
    intro n hn; rw [hu]; exact dif_neg hn
  have hm_pos : 0 < m := hpos m (hSD hmS)
  have hfpos : ∀ (n : ℕ) (hn : n < S.card), 0 < f ⟨n, hn⟩ :=
    fun n hn => hpos _ (hSD (Finset.orderEmbOfFin_mem S rfl ⟨n, hn⟩))
  have hrec : ∀ n, u (n + 1) ≤ r * u n := by
    intro n
    rcases lt_or_ge (n + 1) S.card with hlt | hge
    · have hn : n < S.card := by omega
      have hm1 : f ⟨n, hn⟩ ∈ S := Finset.orderEmbOfFin_mem S rfl ⟨n, hn⟩
      have hm2 : f ⟨n + 1, hlt⟩ ∈ S := Finset.orderEmbOfFin_mem S rfl ⟨n + 1, hlt⟩
      have hindex : (⟨n, hn⟩ : Fin S.card) < ⟨n + 1, hlt⟩ := by simp [Fin.lt_def]
      have hstrict : f ⟨n, hn⟩ < f ⟨n + 1, hlt⟩ := f.strictMono hindex
      have hlac' : Λ * f ⟨n, hn⟩ ≤ f ⟨n + 1, hlt⟩ := hlac _ (hSD hm1) _ (hSD hm2) hstrict
      have hp1 : 0 < f ⟨n, hn⟩ := hpos _ (hSD hm1)
      have hp2 : 0 < f ⟨n + 1, hlt⟩ := hpos _ (hSD hm2)
      have hpowle : (Λ * f ⟨n, hn⟩) ^ d ≤ (f ⟨n + 1, hlt⟩) ^ d :=
        pow_le_pow_left₀ (le_of_lt (mul_pos hΛpos hp1)) hlac' d
      have h1 : Λ ^ d * (f ⟨n, hn⟩) ^ d ≤ (f ⟨n + 1, hlt⟩) ^ d := by
        calc Λ ^ d * (f ⟨n, hn⟩) ^ d = (Λ * f ⟨n, hn⟩) ^ d := by rw [mul_pow]
          _ ≤ (f ⟨n + 1, hlt⟩) ^ d := hpowle
      have h2 : A * Λ ^ d * (f ⟨n, hn⟩) ^ d ≤ A * (f ⟨n + 1, hlt⟩) ^ d := by
        calc A * Λ ^ d * (f ⟨n, hn⟩) ^ d = A * (Λ ^ d * (f ⟨n, hn⟩) ^ d) := by ring
          _ ≤ A * (f ⟨n + 1, hlt⟩) ^ d := mul_le_mul_of_nonneg_left h1 (le_of_lt hA)
      have ha : 0 < A * Λ ^ d * (f ⟨n, hn⟩) ^ d :=
        mul_pos (mul_pos hA (pow_pos hΛpos d)) (pow_pos (hfpos n hn) d)
      have hb : 0 < A * (f ⟨n + 1, hlt⟩) ^ d :=
        mul_pos hA (pow_pos (hfpos (n + 1) hlt) d)
      have h3 : (A * (f ⟨n + 1, hlt⟩) ^ d)⁻¹ ≤ (A * Λ ^ d * (f ⟨n, hn⟩) ^ d)⁻¹ :=
        (inv_le_inv₀ hb ha).mpr h2
      have h4 : (A * Λ ^ d * (f ⟨n, hn⟩) ^ d)⁻¹ = r * (A * (f ⟨n, hn⟩) ^ d)⁻¹ := by
        rw [hr, show A * Λ ^ d * (f ⟨n, hn⟩) ^ d
              = Λ ^ d * (A * (f ⟨n, hn⟩) ^ d) by ring, mul_inv]
      calc u (n + 1) = (A * (f ⟨n + 1, hlt⟩) ^ d)⁻¹ := hu_pos (n + 1) hlt
        _ ≤ (A * Λ ^ d * (f ⟨n, hn⟩) ^ d)⁻¹ := h3
        _ = r * (A * (f ⟨n, hn⟩) ^ d)⁻¹ := h4
        _ = r * u n := by rw [hu_pos n hn]
    · have hu_n1 : u (n + 1) = 0 := hu_neg (n + 1) (by omega)
      have hun_nonneg : 0 ≤ u n := by
        by_cases hn : n < S.card
        · rw [hu_pos n hn]
          exact inv_nonneg.mpr (le_of_lt (mul_pos hA (pow_pos (hfpos n hn) d)))
        · rw [hu_neg n hn]
      rw [hu_n1]
      exact mul_nonneg hr0 hun_nonneg
  have hu0_nonneg : 0 ≤ u 0 := by
    rw [hu_pos 0 hkpos]
    exact inv_nonneg.mpr (le_of_lt (mul_pos hA (pow_pos (hfpos 0 hkpos) d)))
  have hsum_le := sum_range_le_of_geometric hr0 hr1 hu0_nonneg hrec S.card
  have hsum_eq : ∑ N ∈ S, (A * N ^ d)⁻¹ = ∑ n ∈ Finset.range S.card, u n := by
    rw [Finset.sum_range]
    conv_lhs => rw [← Finset.image_orderEmbOfFin_univ S rfl]
    rw [Finset.sum_image]
    · apply Finset.sum_congr rfl
      intro i _
      have hgi : u ↑i = (A * (f i) ^ d)⁻¹ := by
        rw [hu]; exact dif_pos i.isLt
      rw [← hgi]
    · intro x _ y _ hxy; exact f.injective hxy
  rw [hsum_eq]
  have hu0_eq : u 0 = (A * (f ⟨0, hkpos⟩) ^ d)⁻¹ := hu_pos 0 hkpos
  have hle_m : (A * (f ⟨0, hkpos⟩) ^ d)⁻¹ ≤ (A * m ^ d)⁻¹ := by
    have hfm : f ⟨0, hkpos⟩ ∈ S := Finset.orderEmbOfFin_mem S rfl _
    have hle : m ≤ f ⟨0, hkpos⟩ := hmin _ hfm
    have ha : 0 < A * m ^ d := mul_pos hA (pow_pos hm_pos d)
    have hb : 0 < A * (f ⟨0, hkpos⟩) ^ d := mul_pos hA (pow_pos (hfpos 0 hkpos) d)
    have h2 : A * m ^ d ≤ A * (f ⟨0, hkpos⟩) ^ d :=
      mul_le_mul_of_nonneg_left (pow_le_pow_left₀ (le_of_lt hm_pos) hle d) (le_of_lt hA)
    exact (inv_le_inv₀ hb ha).mpr h2
  have h1mr : 0 ≤ (1 - r)⁻¹ := inv_nonneg.mpr (by linarith [hr1])
  calc ∑ n ∈ Finset.range S.card, u n ≤ u 0 * (1 - r)⁻¹ := hsum_le
    _ = (A * (f ⟨0, hkpos⟩) ^ d)⁻¹ * (1 - r)⁻¹ := by rw [hu0_eq]
    _ ≤ (A * m ^ d)⁻¹ * (1 - r)⁻¹ := mul_le_mul_of_nonneg_right hle_m h1mr
    _ = (1 - (Λ ^ d)⁻¹)⁻¹ * (A * m ^ d)⁻¹ := by rw [hr]; ring


theorem lacunary_finset_sum_inv_le
    {Λ : ℝ} (hΛ : 1 < Λ) (d : ℕ) (hd : 1 ≤ d) (A : ℝ) (hA : 0 < A)
    (D : Finset ℝ) (hpos : ∀ N ∈ D, 0 < N)
    (hlac : ∀ M ∈ D, ∀ N ∈ D, M < N → Λ * M ≤ N)
    (X : ℝ) (hX : 0 < X) :
    ∑ N ∈ D.filter (fun N => X < A * N ^ d), (A * N ^ d)⁻¹
      ≤ (1 - (Λ ^ d)⁻¹)⁻¹ * X⁻¹ := by
  set S : Finset ℝ := D.filter (fun N => X < A * N ^ d) with hSdef
  have hSD : S ⊆ D := by
    intro N hN; rw [hSdef] at hN; exact (Finset.mem_filter.mp hN).1
  have hld1 : 1 < Λ ^ d := one_lt_pow₀ hΛ (by omega)
  have hRpos : 0 < (1 - (Λ ^ d)⁻¹)⁻¹ :=
    inv_pos.mpr (by have h := inv_lt_one_of_one_lt₀ hld1; linarith)
  by_cases hS : S.Nonempty
  · set m : ℝ := S.min' hS with hmdef
    have hminmem : m ∈ S := by rw [hmdef]; exact Finset.min'_mem S hS
    have hminle : ∀ N ∈ S, m ≤ N := by
      intro N hN
      have h1 : S.min' hS ≤ S.min' ⟨N, hN⟩ := le_of_eq (congrArg (fun H => S.min' H) (Subsingleton.elim hS ⟨N, hN⟩))
      exact le_trans h1 (Finset.min'_le S N hN)
    have haux := lacunary_finset_sum_le_min hΛ d hd A hA D hpos hlac S hSD hS hminmem hminle
    have hmem' : m ∈ D.filter (fun N => X < A * N ^ d) := by rw [← hSdef]; exact hminmem
    have hfilt : X < A * m ^ d := (Finset.mem_filter.mp hmem').2
    have hminpos : 0 < m := hpos _ (hSD hminmem)
    have hmp : 0 < A * m ^ d := mul_pos hA (pow_pos hminpos d)
    have hlt : (A * m ^ d)⁻¹ < X⁻¹ := (inv_lt_inv₀ hmp hX).mpr hfilt
    calc ∑ N ∈ S, (A * N ^ d)⁻¹
        ≤ (1 - (Λ ^ d)⁻¹)⁻¹ * (A * m ^ d)⁻¹ := haux
      _ ≤ (1 - (Λ ^ d)⁻¹)⁻¹ * X⁻¹ := le_of_lt (mul_lt_mul_of_pos_left hlt hRpos)
  · have hempty : S = ∅ := Finset.not_nonempty_iff_eq_empty.mp hS
    rw [hempty, Finset.sum_empty]
    exact mul_nonneg hRpos.le (inv_nonneg.mpr hX.le)

end Commons.Analysis.Sum
