import Mathlib
import Submission.Commons.Analysis.Series.tail_inv_sq_le
import Submission.Commons.Analysis.Series.tail_inv_sq_summable

set_option linter.unusedVariables false

namespace Work.FIArea7

open scoped BigOperators Topology
open Filter

/-! ### Reciprocal-square sums over the integers

The tail bound `∑_{|k| ≥ N} 1/k² ≤ 4/N` for finite sets of integers with `|k| ≥ N`. Each of
the two sides `k > 0` and `k < 0` is an injective image of a set of naturals `≥ N`, and
`∑_{n ≥ N} 1/n² ≤ 2/(2N-1)`. -/

private lemma natAbs_injOn_pos (P : Finset ℤ) (hP : ∀ k ∈ P, 0 < k) :
    Set.InjOn (fun k : ℤ => k.natAbs) (P : Set ℤ) := by
  intro a ha b hb hab
  simp only [Finset.mem_coe] at ha hb
  rw [Int.natAbs_eq_natAbs_iff] at hab
  rcases hab with h | h
  · exact h
  · exfalso
    have ha' : 0 < a := hP a ha
    rw [h] at ha'
    have hb' : 0 < b := hP b hb
    omega

private lemma natAbs_injOn_neg (Q : Finset ℤ) (hQ : ∀ k ∈ Q, k < 0) :
    Set.InjOn (fun k : ℤ => k.natAbs) (Q : Set ℤ) := by
  intro a ha b hb hab
  simp only [Finset.mem_coe] at ha hb
  rw [Int.natAbs_eq_natAbs_iff] at hab
  rcases hab with h | h
  · exact h
  · exfalso
    have ha' : a < 0 := hQ a ha
    rw [h] at ha'
    have hb' : b < 0 := hQ b hb
    omega

private lemma sum_inv_sq_le_tsum_tail (N : ℕ) (A : Finset ℕ) (hA : ∀ a ∈ A, N ≤ a) :
    ∑ a ∈ A, (1 : ℝ) / (a : ℝ) ^ 2
      ≤ ∑' n : ℕ, (if N ≤ n then (1 : ℝ) / (n : ℝ) ^ 2 else 0) := by
  calc ∑ a ∈ A, (1 : ℝ) / (a : ℝ) ^ 2
      = ∑ a ∈ A, (if N ≤ a then (1 : ℝ) / (a : ℝ) ^ 2 else 0) :=
        Finset.sum_congr rfl (fun a ha => by rw [if_pos (hA a ha)])
    _ ≤ ∑' n : ℕ, (if N ≤ n then (1 : ℝ) / (n : ℝ) ^ 2 else 0) :=
        Summable.sum_le_tsum A (fun n _ => by split <;> positivity)
          (Commons.Analysis.Series.tail_inv_sq_summable N)

/-- Sum of `1/k²` over a finite set of integers whose absolute values are injective and
`≥ K+1` is at most `2/(2K+1)`. -/
private lemma sum_inv_sq_le_of_inj (K : ℕ) (P : Finset ℤ)
    (hinj : Set.InjOn (fun k : ℤ => k.natAbs) (P : Set ℤ))
    (hP : ∀ k ∈ P, K + 1 ≤ k.natAbs) :
    ∑ k ∈ P, (1 : ℝ) / (k : ℝ) ^ 2 ≤ 2 / (2 * (K : ℝ) + 1) := by
  have hcast : ∀ k : ℤ, (1 : ℝ) / (k : ℝ) ^ 2 = (1 : ℝ) / (((k.natAbs : ℕ) : ℝ)) ^ 2 := by
    intro k
    rw [show (((k.natAbs : ℕ) : ℝ)) = |(k : ℝ)| by rw [← Int.cast_abs]; norm_num, sq_abs]
  calc ∑ k ∈ P, (1 : ℝ) / (k : ℝ) ^ 2
      = ∑ k ∈ P, (1 : ℝ) / (((k.natAbs : ℕ) : ℝ)) ^ 2 :=
        Finset.sum_congr rfl (fun k _ => hcast k)
    _ = ∑ n ∈ P.image (fun k : ℤ => k.natAbs), (1 : ℝ) / (n : ℝ) ^ 2 :=
        (Finset.sum_image (f := fun n : ℕ => (1 : ℝ) / (n : ℝ) ^ 2)
          (g := fun k : ℤ => k.natAbs) hinj).symm
    _ ≤ ∑' n : ℕ, (if K + 1 ≤ n then (1 : ℝ) / (n : ℝ) ^ 2 else 0) :=
        sum_inv_sq_le_tsum_tail (K + 1) _ (fun n hn => by
          obtain ⟨k, hk, rfl⟩ := Finset.mem_image.mp hn
          exact hP k hk)
    _ ≤ 2 / (2 * (K : ℝ) + 1) := by
        have h := Commons.Analysis.Series.tail_inv_sq_le (K + 1) (by omega)
        have hc : (2 : ℝ) * (((K + 1 : ℕ)) : ℝ) - 1 = 2 * (K : ℝ) + 1 := by push_cast; ring
        rwa [hc] at h

/-- For a finite set `T` of integers all of absolute value at least `K + 1`, the sum of `1/k²`
over `T` is at most `4/(K+1)`. -/
private lemma sum_inv_sq_int_le {K : ℕ} (T : Finset ℤ)
    (hT : ∀ k ∈ T, (K : ℝ) + 1 ≤ |(k : ℝ)|) :
    ∑ k ∈ T, (1 : ℝ) / (k : ℝ) ^ 2 ≤ 4 / ((K : ℝ) + 1) := by
  have hcastabs : ∀ k : ℤ, (((k.natAbs : ℕ) : ℝ)) = |(k : ℝ)| := by
    intro k; rw [← Int.cast_abs]; norm_num
  have hnat : ∀ k ∈ T, K + 1 ≤ k.natAbs := by
    intro k hk
    have h := hT k hk
    rw [← hcastabs k] at h
    exact_mod_cast h
  have hP : ∑ k ∈ T.filter (fun k : ℤ => 0 < k), (1 : ℝ) / (k : ℝ) ^ 2
      ≤ 2 / (2 * (K : ℝ) + 1) :=
    sum_inv_sq_le_of_inj K _
      (natAbs_injOn_pos _ (fun k hk => (Finset.mem_filter.mp hk).2))
      (fun k hk => hnat k (Finset.mem_filter.mp hk).1)
  have hQ : ∑ k ∈ T.filter (fun k : ℤ => ¬ 0 < k), (1 : ℝ) / (k : ℝ) ^ 2
      ≤ 2 / (2 * (K : ℝ) + 1) := by
    refine sum_inv_sq_le_of_inj K _ ?_
      (fun k hk => hnat k (Finset.mem_filter.mp hk).1)
    refine natAbs_injOn_neg _ (fun k hk => ?_)
    rw [Finset.mem_filter] at hk
    obtain ⟨hkT, hknot⟩ := hk
    have hne : k ≠ 0 := by
      intro h0
      have h := hT k hkT
      rw [h0] at h
      simp at h
      have : (0 : ℝ) ≤ (K : ℝ) := by positivity
      linarith
    omega
  rw [← Finset.sum_filter_add_sum_filter_not T (fun k : ℤ => 0 < k)
        (fun k => (1 : ℝ) / (k : ℝ) ^ 2)]
  calc ∑ k ∈ T.filter (fun k : ℤ => 0 < k), (1 : ℝ) / (k : ℝ) ^ 2
        + ∑ k ∈ T.filter (fun k : ℤ => ¬ 0 < k), (1 : ℝ) / (k : ℝ) ^ 2
      ≤ 2 / (2 * (K : ℝ) + 1) + 2 / (2 * (K : ℝ) + 1) := add_le_add hP hQ
    _ = 4 / (2 * (K : ℝ) + 1) := by ring
    _ ≤ 4 / ((K : ℝ) + 1) := by
        rw [div_le_div_iff₀ (by positivity) (by positivity)]
        nlinarith

/-! ### The intervals `Icc (-N) N` are a cofinal family of finite subsets of `ℤ` -/

private lemma tendsto_Icc_int_atTop :
    Tendsto (fun N : ℕ => Finset.Icc (-(N : ℤ)) (N : ℤ)) atTop atTop := by
  apply Monotone.tendsto_atTop_atTop
  · intro N M hNM
    exact Finset.Icc_subset_Icc (by omega) (by omega)
  · intro b
    refine ⟨b.sup (fun k => k.natAbs), ?_⟩
    intro k hk
    rw [Finset.mem_Icc]
    have h1 : k.natAbs ≤ b.sup (fun k => k.natAbs) :=
      Finset.le_sup (f := fun k : ℤ => k.natAbs) hk
    have h1z : (k.natAbs : ℤ) ≤ ((b.sup (fun k => k.natAbs) : ℕ) : ℤ) := by
      exact_mod_cast h1
    constructor
    · have := Int.le_natAbs (a := -k)
      rw [Int.natAbs_neg] at this
      linarith
    · have := Int.le_natAbs (a := k)
      linarith

/-! ### The main truncation bound -/

theorem truncLeOfCoeffBounds {ĉ : ℤ → ℂ} {s u : ℂ} {R : ℕ} {M : ℝ} {K : ℕ}
    (hM : 0 ≤ M) (hu : ‖u‖ = 1)
    (h1 : ∀ k : ℤ, k ≠ 0 → ‖ĉ k‖ ≤ M / |(k : ℝ)|)
    (h2 : ∀ k : ℤ, k ≠ 0 → ‖ĉ k‖ ≤ 3 * M * (R : ℝ) / (2 * (k : ℝ) ^ 2))
    (hsum : HasSum (fun k : ℤ => ĉ k * u ^ k) s) :
    ‖s - ∑ k ∈ Finset.Icc (-(K : ℤ)) (K : ℤ), ĉ k * u ^ k‖
      ≤ (20 * M + 1) * (R : ℝ) / ((K : ℝ) + 1) := by
  set A : Finset ℤ := Finset.Icc (-(K : ℤ)) (K : ℤ) with hA
  set g : ℕ → Finset ℤ := fun N => Finset.Icc (-(N : ℤ)) (N : ℤ) with hg
  have hmain : ∀ N : ℕ, K ≤ N →
      ‖(∑ k ∈ g N, ĉ k * u ^ k) - ∑ k ∈ A, ĉ k * u ^ k‖
        ≤ (20 * M + 1) * (R : ℝ) / ((K : ℝ) + 1) := by
    intro N hNK
    have hAG : A ⊆ g N := by
      rw [hA, hg]; exact Finset.Icc_subset_Icc (by omega) (by omega)
    have hsub : (∑ k ∈ g N, ĉ k * u ^ k) - ∑ k ∈ A, ĉ k * u ^ k
        = ∑ k ∈ g N \ A, ĉ k * u ^ k := by
      have h := Finset.sum_sdiff (f := fun k : ℤ => ĉ k * u ^ k) hAG
      rw [← h]; ring
    have hterm : ∀ k ∈ g N \ A,
        ‖ĉ k * u ^ k‖ ≤ (3 * M * (R : ℝ) / 2) * (1 / (k : ℝ) ^ 2) := by
      intro k hk
      rw [Finset.mem_sdiff] at hk
      obtain ⟨hkg, hkA⟩ := hk
      rw [hA, Finset.mem_Icc] at hkA
      have hkA' : k < -(K : ℤ) ∨ (K : ℤ) < k := by
        by_contra h
        rw [not_or] at h
        exact hkA (by omega)
      have hkne : k ≠ 0 := by rcases hkA' with h | h <;> omega
      have hnormu : ‖u ^ k‖ = 1 := by simp [norm_zpow, hu]
      rw [norm_mul, hnormu, mul_one]
      have hk2 : (k : ℝ) ≠ 0 := by exact_mod_cast hkne
      calc ‖ĉ k‖ ≤ 3 * M * (R : ℝ) / (2 * (k : ℝ) ^ 2) := h2 k hkne
        _ = (3 * M * (R : ℝ) / 2) * (1 / (k : ℝ) ^ 2) := by field_simp
    have hkle : ∀ k ∈ g N \ A, (K : ℝ) + 1 ≤ |(k : ℝ)| := by
      intro k hk
      rw [Finset.mem_sdiff] at hk
      obtain ⟨hkg, hkA⟩ := hk
      rw [hA, Finset.mem_Icc] at hkA
      have hkA' : k < -(K : ℤ) ∨ (K : ℤ) < k := by
        by_contra h
        rw [not_or] at h
        exact hkA (by omega)
      rcases hkA' with h | h
      · have h2' : (K : ℝ) + 1 ≤ -(k : ℝ) := by
          have h1' : ((K : ℤ) + 1) ≤ -k := by omega
          have := (Int.cast_le (R := ℝ)).mpr h1'
          push_cast at this
          linarith
        exact le_trans h2' (neg_le_abs _)
      · have h2' : (K : ℝ) + 1 ≤ (k : ℝ) := by
          have h1' : ((K : ℤ) + 1) ≤ k := by omega
          have := (Int.cast_le (R := ℝ)).mpr h1'
          push_cast at this
          linarith
        exact le_trans h2' (le_abs_self _)
    have hsum_le : ∑ k ∈ g N \ A, ‖ĉ k * u ^ k‖
        ≤ (3 * M * (R : ℝ) / 2) * (4 / ((K : ℝ) + 1)) := by
      calc ∑ k ∈ g N \ A, ‖ĉ k * u ^ k‖
          ≤ ∑ k ∈ g N \ A, (3 * M * (R : ℝ) / 2) * (1 / (k : ℝ) ^ 2) :=
              Finset.sum_le_sum hterm
        _ = (3 * M * (R : ℝ) / 2) * ∑ k ∈ g N \ A, 1 / (k : ℝ) ^ 2 := by
              rw [Finset.mul_sum]
        _ ≤ (3 * M * (R : ℝ) / 2) * (4 / ((K : ℝ) + 1)) := by
              apply mul_le_mul_of_nonneg_left _ (by positivity)
              exact sum_inv_sq_int_le _ hkle
    calc ‖(∑ k ∈ g N, ĉ k * u ^ k) - ∑ k ∈ A, ĉ k * u ^ k‖
        = ‖∑ k ∈ g N \ A, ĉ k * u ^ k‖ := by rw [hsub]
      _ ≤ ∑ k ∈ g N \ A, ‖ĉ k * u ^ k‖ := norm_sum_le _ _
      _ ≤ (3 * M * (R : ℝ) / 2) * (4 / ((K : ℝ) + 1)) := hsum_le
      _ = 6 * M * (R : ℝ) / ((K : ℝ) + 1) := by field_simp; ring
      _ ≤ (20 * M + 1) * (R : ℝ) / ((K : ℝ) + 1) := by
            apply div_le_div_of_nonneg_right _ (by positivity)
            exact mul_le_mul_of_nonneg_right (by linarith) (by positivity)
  have hft : ∀ᶠ N in atTop, ‖(∑ k ∈ g N, ĉ k * u ^ k) - ∑ k ∈ A, ĉ k * u ^ k‖
      ≤ (20 * M + 1) * (R : ℝ) / ((K : ℝ) + 1) := by
    rw [eventually_atTop]; exact ⟨K, hmain⟩
  have hcof : Tendsto g atTop atTop := by
    rw [hg]; exact tendsto_Icc_int_atTop
  have hcomp : Tendsto (fun N => ∑ k ∈ g N, ĉ k * u ^ k) atTop (𝓝 s) :=
    hsum.comp hcof
  have hlim : Tendsto (fun N => ‖(∑ k ∈ g N, ĉ k * u ^ k) - ∑ k ∈ A, ĉ k * u ^ k‖) atTop
      (𝓝 ‖s - ∑ k ∈ A, ĉ k * u ^ k‖) :=
    (hcomp.sub tendsto_const_nhds).norm
  exact le_of_tendsto hlim hft

end Work.FIArea7
