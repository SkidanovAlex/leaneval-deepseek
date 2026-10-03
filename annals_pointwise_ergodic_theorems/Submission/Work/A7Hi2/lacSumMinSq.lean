/-
# A lacunary absorption bound at integral scales (local copy)

This is a verbatim copy of `Work.KMTAreas.A7Hi.lacSumMin` (the `≤ 4` bound
`∑_{n ∈ U} min (σ n · d) ((σ n · d)²)⁻¹ ≤ 4` for a `2`-lacunary integral scale family),
with the declarations renamed (suffix `Sq`).  It is used by `Work.A7Hi2.symDiffR_overlap`.

The copy is necessary because `Work.KMTAreas.A7Hi.lacSumMin` is declared *twice* in the
workspace (here and in `Work.KMTAreas.A7Hi.DilVar`), so the two modules cannot be imported into
the same environment.
-/
import Mathlib
import Submission.Commons.Analysis.Sum.lacunary_finset_sum_le

set_option autoImplicit false
set_option maxHeartbeats 1000000

namespace Work.A7Hi2

open Finset

/-- Doubling implies growth by powers of two: `2 ^ k * σ m ≤ σ (m + k)`. -/
lemma two_pow_mul_le_of_doublingSq {σ : ℕ → ℕ} (hσ2 : ∀ n, 2 * σ n ≤ σ (n + 1)) :
    ∀ k m : ℕ, 2 ^ k * σ m ≤ σ (m + k) := by
  intro k
  induction k with
  | zero => intro m; simp
  | succ k ih =>
      intro m
      calc 2 ^ (k + 1) * σ m = 2 ^ k * 2 * σ m := by rw [pow_succ]
        _ = 2 * (2 ^ k * σ m) := by ring
        _ ≤ 2 * σ (m + k) := Nat.mul_le_mul_left 2 (ih m)
        _ ≤ σ (m + k + 1) := hσ2 (m + k)
        _ = σ (m + (k + 1)) := by rw [Nat.add_assoc]

/-- A doubling `ℕ`-sequence with `1 ≤ σ n` is strictly increasing. -/
lemma strictMono_sigmaSq {σ : ℕ → ℕ} (hσ1 : ∀ n, 1 ≤ σ n)
    (hσ2 : ∀ n, 2 * σ n ≤ σ (n + 1)) : StrictMono σ := by
  intro a b hab
  obtain ⟨k, rfl⟩ : ∃ k, b = a + (k + 1) := ⟨b - a - 1, by omega⟩
  have h := two_pow_mul_le_of_doublingSq hσ2 (k + 1) a
  have hk : 2 ≤ 2 ^ (k + 1) := by
    calc (2 : ℕ) = 2 ^ 1 := by norm_num
      _ ≤ 2 ^ (k + 1) := Nat.pow_le_pow_right (by norm_num) (by omega)
  have h2 : 2 * σ a ≤ σ (a + (k + 1)) :=
    le_trans (Nat.mul_le_mul_right _ hk) h
  have h3 := hσ1 a
  omega

/-- For `1 ≤ t` one has `(t ^ 2)⁻¹ ≤ t⁻¹`. -/
lemma inv_sq_le_inv_of_one_leSq {t : ℝ} (h : 1 ≤ t) : (t ^ 2)⁻¹ ≤ t⁻¹ := by
  have ht : 0 < t := lt_of_lt_of_le one_pos h
  have h2 : t ≤ t ^ 2 := by nlinarith
  exact (inv_le_inv₀ (pow_pos ht 2) ht).mpr h2

/-- Transfer of a filtered sum along the (injective) scale map `n ↦ (σ n : ℝ)`. -/
lemma sum_image_filterSq {σ : ℕ → ℕ} {U : Finset ℕ}
    (hinj : Set.InjOn (fun n => (σ n : ℝ)) ↑U)
    (P : ℝ → Prop) [DecidablePred P] (g : ℝ → ℝ) :
    ∑ n ∈ U.filter (fun n => P ((σ n : ℝ))), g ((σ n : ℝ))
      = ∑ N ∈ (U.image (fun n => (σ n : ℝ))).filter P, g N := by
  have hInj : Set.InjOn (fun n => (σ n : ℝ)) ↑(U.filter (fun n => P ((σ n : ℝ)))) := by
    intro x hx y hy hxy
    exact hinj (Finset.mem_filter.mp hx).1 (Finset.mem_filter.mp hy).1 hxy
  rw [Finset.filter_image, Finset.sum_image hInj]

/-- The lacunary absorption bound: for a `2`-lacunary sequence `σ` with `1 ≤ σ n`, any `d ≥ 0`
and any finite `U`,
`∑_{n ∈ U} min (σ n · d) ((σ n · d) ^ 2)⁻¹ ≤ 4`. -/
theorem lacSumMinSq {σ : ℕ → ℕ} (hσ1 : ∀ n, 1 ≤ σ n) (hσ2 : ∀ n, 2 * σ n ≤ σ (n + 1))
    (d : ℝ) (hd : 0 ≤ d) (U : Finset ℕ) :
    ∑ n ∈ U, min ((σ n : ℝ) * d) (((σ n : ℝ) * d) ^ 2)⁻¹ ≤ 4 := by
  classical
  rcases eq_or_lt_of_le hd with hd0 | hdpos
  · rw [← hd0]
    simp
  have hmono : StrictMono σ := strictMono_sigmaSq hσ1 hσ2
  have hinj : Set.InjOn (fun n => (σ n : ℝ)) ↑U := by
    intro x _ y _ hxy
    exact hmono.injective (Nat.cast_injective hxy)
  have hDpos : ∀ N ∈ U.image (fun n => (σ n : ℝ)), 0 < N := by
    intro N hN
    obtain ⟨n, _, rfl⟩ := Finset.mem_image.mp hN
    have h1 : (1 : ℝ) ≤ (σ n : ℝ) := by exact_mod_cast hσ1 n
    linarith
  have hDlac : ∀ M ∈ U.image (fun n => (σ n : ℝ)),
      ∀ N ∈ U.image (fun n => (σ n : ℝ)), M < N → 2 * M ≤ N := by
    intro M hM N hN hMN
    obtain ⟨i, _, rfl⟩ := Finset.mem_image.mp hM
    obtain ⟨j, _, rfl⟩ := Finset.mem_image.mp hN
    have hne : i ≠ j := by
      rintro rfl
      exact lt_irrefl _ hMN
    rcases lt_or_gt_of_ne hne with hij | hji
    · have hle : 2 * σ i ≤ σ j := by
        have h := two_pow_mul_le_of_doublingSq hσ2 (j - i) i
        rw [Nat.add_sub_of_le (le_of_lt hij)] at h
        have hk : 2 ≤ 2 ^ (j - i) := by
          calc (2 : ℕ) = 2 ^ 1 := by norm_num
            _ ≤ 2 ^ (j - i) := Nat.pow_le_pow_right (by norm_num) (by omega)
        exact le_trans (Nat.mul_le_mul_right _ hk) h
      exact_mod_cast hle
    · exfalso
      have hji' : (σ j : ℝ) < (σ i : ℝ) := by exact_mod_cast hmono hji
      linarith
  have hsmall : ∑ N ∈ (U.image (fun n => (σ n : ℝ))).filter (fun N => N * d ≤ 1),
      N * d ≤ 2 := by
    have h := Commons.Analysis.Sum.lacunary_finset_sum_le (Λ := (2 : ℝ)) (by norm_num) 1 le_rfl
      d hdpos (U.image (fun n => (σ n : ℝ))) hDpos hDlac 1 (by norm_num)
    have hfil : (U.image (fun n => (σ n : ℝ))).filter (fun N => d * N ^ 1 ≤ 1)
        = (U.image (fun n => (σ n : ℝ))).filter (fun N => N * d ≤ 1) := by
      apply Finset.filter_congr
      intro N _
      simp [pow_one, mul_comm]
    calc ∑ N ∈ (U.image (fun n => (σ n : ℝ))).filter (fun N => N * d ≤ 1), N * d
        = ∑ N ∈ (U.image (fun n => (σ n : ℝ))).filter (fun N => d * N ^ 1 ≤ 1), d * N ^ 1 := by
          rw [← hfil]
          exact Finset.sum_congr rfl (fun N _ => by simp [pow_one, mul_comm])
      _ ≤ (1 - ((2 : ℝ) ^ 1)⁻¹)⁻¹ * 1 := h
      _ = 2 := by norm_num
  have hbig : ∑ N ∈ (U.image (fun n => (σ n : ℝ))).filter (fun N => 1 < N * d),
      (N * d)⁻¹ ≤ 2 := by
    have h := Commons.Analysis.Sum.lacunary_finset_sum_inv_le (Λ := (2 : ℝ)) (by norm_num) 1 le_rfl
      d hdpos (U.image (fun n => (σ n : ℝ))) hDpos hDlac 1 (by norm_num)
    have hfil : (U.image (fun n => (σ n : ℝ))).filter (fun N => 1 < d * N ^ 1)
        = (U.image (fun n => (σ n : ℝ))).filter (fun N => 1 < N * d) := by
      apply Finset.filter_congr
      intro N _
      simp [pow_one, mul_comm]
    calc ∑ N ∈ (U.image (fun n => (σ n : ℝ))).filter (fun N => 1 < N * d), (N * d)⁻¹
        = ∑ N ∈ (U.image (fun n => (σ n : ℝ))).filter (fun N => 1 < d * N ^ 1),
            (d * N ^ 1)⁻¹ := by
          rw [← hfil]
          exact Finset.sum_congr rfl (fun N _ => by simp [pow_one, mul_comm])
      _ ≤ (1 - ((2 : ℝ) ^ 1)⁻¹)⁻¹ * 1⁻¹ := h
      _ = 2 := by norm_num
  have hsplit := Finset.sum_filter_add_sum_filter_not U (fun n => (σ n : ℝ) * d ≤ 1)
    (fun n => min ((σ n : ℝ) * d) (((σ n : ℝ) * d) ^ 2)⁻¹)
  rw [← hsplit]
  have hA : ∑ n ∈ U.filter (fun n => (σ n : ℝ) * d ≤ 1),
      min ((σ n : ℝ) * d) (((σ n : ℝ) * d) ^ 2)⁻¹ ≤ 2 := by
    calc ∑ n ∈ U.filter (fun n => (σ n : ℝ) * d ≤ 1),
          min ((σ n : ℝ) * d) (((σ n : ℝ) * d) ^ 2)⁻¹
        ≤ ∑ n ∈ U.filter (fun n => (σ n : ℝ) * d ≤ 1), (σ n : ℝ) * d :=
          Finset.sum_le_sum (fun n _ => min_le_left _ _)
      _ = ∑ N ∈ (U.image (fun n => (σ n : ℝ))).filter (fun N => N * d ≤ 1), N * d :=
          sum_image_filterSq hinj (fun N => N * d ≤ 1) (fun N => N * d)
      _ ≤ 2 := hsmall
  have hB : ∑ n ∈ U.filter (fun n => ¬ ((σ n : ℝ) * d ≤ 1)),
      min ((σ n : ℝ) * d) (((σ n : ℝ) * d) ^ 2)⁻¹ ≤ 2 := by
    rw [show U.filter (fun n => ¬ ((σ n : ℝ) * d ≤ 1))
        = U.filter (fun n => 1 < (σ n : ℝ) * d) from
      Finset.filter_congr (fun n _ => not_le)]
    calc ∑ n ∈ U.filter (fun n => 1 < (σ n : ℝ) * d),
          min ((σ n : ℝ) * d) (((σ n : ℝ) * d) ^ 2)⁻¹
        ≤ ∑ n ∈ U.filter (fun n => 1 < (σ n : ℝ) * d), (((σ n : ℝ) * d) ^ 2)⁻¹ :=
          Finset.sum_le_sum (fun n _ => min_le_right _ _)
      _ ≤ ∑ n ∈ U.filter (fun n => 1 < (σ n : ℝ) * d), (((σ n : ℝ) * d))⁻¹ := by
          apply Finset.sum_le_sum
          intro n hn
          exact inv_sq_le_inv_of_one_leSq (le_of_lt (Finset.mem_filter.mp hn).2)
      _ = ∑ N ∈ (U.image (fun n => (σ n : ℝ))).filter (fun N => 1 < N * d), (N * d)⁻¹ :=
          sum_image_filterSq hinj (fun N => 1 < N * d) (fun N => (N * d)⁻¹)
      _ ≤ 2 := hbig
  linarith



end Work.A7Hi2
