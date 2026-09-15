import Mathlib
import Submission.Commons.Analysis.Fourier.tsum_bracket_lattice_le
import Submission.Commons.Analysis.TSum.summable_pi_prod

open scoped BigOperators

namespace Commons.Analysis.Fourier

/-- If `|δ| ≤ 1` then the shifted square `(δ + 2k)²` dominates `k²` for every integer `k`. -/
private lemma sq_le_sq_shift (δ : ℝ) (hδ : |δ| ≤ 1) (k : ℤ) :
    (k : ℝ) ^ 2 ≤ (δ + 2 * (k : ℝ)) ^ 2 := by
  rcases eq_or_ne k 0 with hk | hk
  · subst hk
    push_cast
    nlinarith [sq_nonneg δ]
  · have hkabs : (1 : ℝ) ≤ |(k : ℝ)| := by
      have h := Int.one_le_abs hk
      calc (1 : ℝ) ≤ ((|k| : ℤ) : ℝ) := by exact_mod_cast h
        _ = |(k : ℝ)| := by rw [Int.cast_abs]
    have htri : |(k : ℝ)| ≤ |δ + 2 * (k : ℝ)| := by
      have h1 : |(2 : ℝ) * (k : ℝ)| - |δ| ≤ |(2 : ℝ) * (k : ℝ) + δ| := by
        have h := abs_sub_abs_le_abs_sub ((2 : ℝ) * (k : ℝ)) (-δ)
        simpa [sub_neg_eq_add] using h
      have h2 : |(k : ℝ)| ≤ |(2 : ℝ) * (k : ℝ)| - |δ| := by
        have hmul : |(2 : ℝ) * (k : ℝ)| = 2 * |(k : ℝ)| := by
          rw [abs_mul]; norm_num
        rw [hmul]; linarith
      calc |(k : ℝ)| ≤ |(2 : ℝ) * (k : ℝ) + δ| := le_trans h2 h1
        _ = |δ + 2 * (k : ℝ)| := by rw [add_comm]
    exact (sq_le_sq).mpr htri

/-- One-dimensional comparison: a shifted term is dominated by the unshifted lattice term. -/
private lemma one_add_sq_inv_le (δ : ℝ) (hδ : |δ| ≤ 1) (k : ℤ) :
    (1 + (δ + 2 * (k : ℝ)) ^ 2)⁻¹ ≤ (1 + (k : ℝ) ^ 2)⁻¹ := by
  have hsq := sq_le_sq_shift δ hδ k
  exact (inv_le_inv₀ (by positivity) (by positivity)).mpr (by linarith [hsq])

/-- The one-dimensional lattice series `∑_{m ∈ ℤ} (1 + m²)⁻¹` is summable. -/
theorem summable_one_add_sq_int :
    Summable (fun m : ℤ => (1 + (m : ℝ) ^ 2)⁻¹) := by
  have hu : Summable (fun m : ℤ => 1 / (m : ℝ) ^ 2) :=
    (Real.summable_one_div_int_pow (p := 2)).mpr (by norm_num)
  have he : Summable (fun m : ℤ => if m = 0 then (1 : ℝ) else 0) := by
    refine summable_of_ne_finset_zero (s := {0}) ?_
    intro b hb
    rw [Finset.mem_singleton] at hb
    rw [if_neg hb]
  refine Summable.of_nonneg_of_le (fun m => by positivity) (fun m => ?_) (he.add hu)
  by_cases hm : m = 0
  · subst hm
    norm_num
  · have hx : 0 < (m : ℝ) ^ 2 := by
      have : (m : ℝ) ≠ 0 := by exact_mod_cast hm
      positivity
    have hle : (1 + (m : ℝ) ^ 2)⁻¹ ≤ 1 / (m : ℝ) ^ 2 := by
      rw [inv_eq_one_div]
      exact one_div_le_one_div_of_le hx (by linarith)
    simpa [hm] using hle

/-- The one-dimensional shifted lattice series `∑_{n ∈ ℤ} (1 + (t + 2n)²)⁻¹` is summable. -/
theorem summable_one_add_sq_shift (t : ℝ) :
    Summable (fun n : ℤ => (1 + (t + 2 * (n : ℝ)) ^ 2)⁻¹) := by
  refine summable_of_sum_le (c := ∑' m : ℤ, (1 + (m : ℝ) ^ 2)⁻¹) (fun n => by positivity) ?_
  intro u
  have hA : Summable (fun m : ℤ => (1 + (m : ℝ) ^ 2)⁻¹) := summable_one_add_sq_int
  set j : ℤ := ⌊(1 / 2 - t / 2 : ℝ)⌋ with hj
  have hδ : |t + 2 * (j : ℝ)| ≤ 1 := by
    have h1 : (j : ℝ) ≤ 1 / 2 - t / 2 := by rw [hj]; exact Int.floor_le _
    have h2 : 1 / 2 - t / 2 < (j : ℝ) + 1 := by rw [hj]; exact Int.lt_floor_add_one _
    rw [abs_le]
    constructor <;> linarith
  have hterm : ∀ n : ℤ,
      (1 + (t + 2 * (n : ℝ)) ^ 2)⁻¹ ≤ (1 + ((n - j : ℤ) : ℝ) ^ 2)⁻¹ := by
    intro n
    have hcast : (((n - j : ℤ)) : ℝ) = (n : ℝ) - (j : ℝ) := by push_cast; ring
    have h := one_add_sq_inv_le (t + 2 * (j : ℝ)) hδ (n - j)
    have hrepr : (t + 2 * (j : ℝ)) + 2 * (((n - j : ℤ)) : ℝ) = t + 2 * (n : ℝ) := by
      rw [hcast]; ring
    rw [← hrepr]
    exact h
  calc ∑ n ∈ u, (1 + (t + 2 * (n : ℝ)) ^ 2)⁻¹
      ≤ ∑ n ∈ u, (1 + ((n - j : ℤ) : ℝ) ^ 2)⁻¹ :=
        Finset.sum_le_sum (fun n _ => hterm n)
    _ = ∑ m ∈ u.image (fun n : ℤ => n - j), (1 + (m : ℝ) ^ 2)⁻¹ :=
        (Finset.sum_image (f := fun m : ℤ => (1 + (m : ℝ) ^ 2)⁻¹)
          (g := fun n : ℤ => n - j) (s := u) (by
            intro a _ b _ hab
            have h := congrArg (fun z : ℤ => z + j) hab
            simpa using h)).symm
    _ ≤ ∑' m : ℤ, (1 + (m : ℝ) ^ 2)⁻¹ :=
        hA.sum_le_tsum _ (fun m _ => by positivity)

/-- Pointwise bound of the `d`-bracket by the product of the one-dimensional brackets. -/
theorem bracket_le_prod {ι : Type*} [Fintype ι] (v : ι → ℝ) :
    (1 + ‖v‖ ^ 2) ^ (-(Fintype.card ι : ℝ)) ≤ ∏ i, (1 + (v i) ^ 2)⁻¹ := by
  have hBpos : (0 : ℝ) < 1 + ‖v‖ ^ 2 := by positivity
  have hcoord : ∀ i, (v i) ^ 2 ≤ ‖v‖ ^ 2 := by
    intro i
    have h : |v i| ≤ ‖v‖ := by
      simpa [Real.norm_eq_abs] using norm_le_pi_norm v i
    calc (v i) ^ 2 = |v i| ^ 2 := by rw [sq_abs]
      _ ≤ ‖v‖ ^ 2 := pow_le_pow_left₀ (abs_nonneg _) h 2
  have hprod_le : ∏ i, (1 + (v i) ^ 2) ≤ (1 + ‖v‖ ^ 2) ^ (Fintype.card ι) := by
    calc ∏ i, (1 + (v i) ^ 2) ≤ ∏ _i : ι, (1 + ‖v‖ ^ 2) := by
          apply Finset.prod_le_prod
          · intro i _; positivity
          · intro i _; linarith [hcoord i]
      _ = (1 + ‖v‖ ^ 2) ^ (Fintype.card ι) := by
          rw [Finset.prod_const, Finset.card_univ]
  have hprodpos : 0 < ∏ i, (1 + (v i) ^ 2) :=
    Finset.prod_pos (fun i _ => by positivity)
  rw [Real.rpow_neg (le_of_lt hBpos) (Fintype.card ι : ℝ), Real.rpow_natCast,
      Finset.prod_inv_distrib]
  exact (inv_le_inv₀ (by positivity) hprodpos).mpr hprod_le

/-- The `d`-dimensional bracket lattice family is summable for every shift `η`. -/
theorem summable_bracket (d : ℕ) (η : EuclideanSpace ℝ (Fin d)) :
    Summable (fun ℓ : Fin d → ℤ =>
      (1 + ‖η + (fun i : Fin d => 2 * (ℓ i : ℝ))‖ ^ 2) ^ (-(d : ℝ))) := by
  have hprod : Summable (fun ℓ : Fin d → ℤ =>
      ∏ i, (1 + (η i + 2 * (ℓ i : ℝ)) ^ 2)⁻¹) :=
    Commons.Analysis.TSum.summable_pi_prod_nonneg (fun (i : Fin d) (m : ℤ) => (1 + (η i + 2 * (m : ℝ)) ^ 2)⁻¹)
      (fun i m => by positivity) (fun i => summable_one_add_sq_shift (η i))
  refine Summable.of_nonneg_of_le (fun ℓ => by positivity) (fun ℓ => ?_) hprod
  set v : Fin d → ℝ := η + (fun i : Fin d => 2 * (ℓ i : ℝ)) with hv
  have hveq : ∀ i, v i = η i + 2 * (ℓ i : ℝ) := by intro i; simp [hv]
  calc (1 + ‖η + (fun i : Fin d => 2 * (ℓ i : ℝ))‖ ^ 2) ^ (-(d : ℝ))
      = (1 + ‖v‖ ^ 2) ^ (-(Fintype.card (Fin d) : ℝ)) := by rw [hv, Fintype.card_fin]
    _ ≤ ∏ i, (1 + (v i) ^ 2)⁻¹ := bracket_le_prod v
    _ = ∏ i, (1 + (η i + 2 * (ℓ i : ℝ)) ^ 2)⁻¹ :=
        Finset.prod_congr rfl (fun i _ => by rw [hveq i])

theorem finset_bracket_lattice_le (d : ℕ) :
    ∃ C : ℝ, 0 < C ∧ ∀ (η : EuclideanSpace ℝ (Fin d)) (s : Finset (Fin d → ℤ)),
      (∑ ℓ ∈ s, (1 + ‖η + (fun i : Fin d => 2 * (ℓ i : ℝ))‖ ^ 2) ^ (-(d : ℝ))) ≤ C := by
  obtain ⟨C, hCpos, hCbound⟩ := tsum_bracket_lattice_le d
  refine ⟨C, hCpos, ?_⟩
  intro η s
  have hs : Summable (fun ℓ : Fin d → ℤ =>
      (1 + ‖η + (fun i : Fin d => 2 * (ℓ i : ℝ))‖ ^ 2) ^ (-(d : ℝ))) :=
    summable_bracket d η
  calc (∑ ℓ ∈ s, (1 + ‖η + (fun i : Fin d => 2 * (ℓ i : ℝ))‖ ^ 2) ^ (-(d : ℝ)))
      ≤ ∑' ℓ : Fin d → ℤ, (1 + ‖η + (fun i : Fin d => 2 * (ℓ i : ℝ))‖ ^ 2) ^ (-(d : ℝ)) :=
        hs.sum_le_tsum s (fun _ _ => by positivity)
    _ ≤ C := hCbound η

end Commons.Analysis.Fourier
