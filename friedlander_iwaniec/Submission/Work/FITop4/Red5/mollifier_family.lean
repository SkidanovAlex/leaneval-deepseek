/-
# `Submission.Work.FITop4.Red5.mollifier_family`

The simultaneous existence of the radial mollifier pieces `(a_i, p_i)` and the angular mollifier
pieces `(φ_k, q_k)` used in the Friedlander–Iwaniec reduction, with

* the support and partition of unity properties of §4 (the `p_i` partition `(N, 2N]` up to the two
  boundary strips `(N, N + θN/2]` and `(2N - 2θN, 2N]`),
* the derivative bounds (4.14), (5.12) with the absolute constants `cMoll j`,
* the angular normalisation `q_k(0) = 0` needed to make the coefficients vanish at the origin.

The radial half is `radial_pieces_flat` (the flat radial partition, already supported inside
`(N, 2N]`), reindexed from a `Finset` of pieces to a `Fin`-indexed family; the angular half is the
tent partition of `angular_partition_le`, strengthened by `q_k(0) = 0`.
-/
import Mathlib
import Submission.Work.FITop4.Red5.assembly_helpers
import Submission.Work.FITop4.Red5.angular_partition_le

set_option autoImplicit false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace Work.FITop4.Red5

open Finset
open scoped BigOperators
open Work.FITop4.Bump4

attribute [local instance] Classical.propDecidable

noncomputable section

/-! ## 1. The tent bump vanishes at the origin -/

/-- `tent W 0 = 0`: both clamped steps vanish at (or below) the origin. -/
lemma tent_zero (W : ℝ) : tent W 0 = 0 := by
  unfold tent
  rw [zero_div, show (0 : ℝ) - 1 = -1 by norm_num,
    quinticStep_eq_zero_of_nonpos _ le_rfl,
    quinticStep_eq_zero_of_nonpos _ (by norm_num : (-1 : ℝ) ≤ 0)]
  ring

/-! ## 2. The angular partition with `q_k(0) = 0` -/

/-- The angular partition of unity of §5, with the additional normalisation `q_k(0) = 0`. -/
theorem angular_partition_le0 (θ : ℝ) (hθ0 : 0 < θ) (hθ1 : θ ≤ 1 / 4) :
    ∃ (K : ℕ) (φ : Fin K → ℝ) (q : Fin K → ℝ → ℝ),
      (∀ k, ContDiff ℝ 2 (q k)) ∧
      (∀ k α, 0 ≤ q k α) ∧ (∀ k α, q k α ≤ 1) ∧
      (∀ k, q k 0 = 0) ∧
      (∀ k α, q k α ≠ 0 → 0 ≤ α ∧ α ≤ 2 * Real.pi * θ) ∧
      (∀ α, -Real.pi ≤ α → α ≤ Real.pi → (∑ k, q k (α - φ k)) = 1) ∧
      (∀ k j, j ≤ 2 → ∀ α,
        |iteratedDeriv j (q k) α| ≤ cMoll j * θ ^ (-(j : ℝ))) ∧
      ((K : ℝ) ≤ 4 / θ + 4) := by
  have hWpos : 0 < Real.pi * θ := by positivity
  refine ⟨Nat.ceil (2 / θ) + 1,
    (fun k => -(Real.pi * (1 + θ)) + ((k : ℕ) : ℝ) * (Real.pi * θ)),
    (fun _ x => tent (Real.pi * θ) x), ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · intro k; exact tent_contDiff _
  · intro k α; exact tent_nonneg _ _
  · intro k α; exact tent_le_one _ _
  · intro k; exact tent_zero _
  · intro k α h
    obtain ⟨h1, h2⟩ := tent_support (Real.pi * θ) hWpos h
    exact ⟨h1, h2.trans (le_of_eq (by ring))⟩
  · intro α hlo hhi
    set t : ℝ := (α + Real.pi + Real.pi * θ) / (Real.pi * θ) with ht
    rw [Fin.sum_univ_eq_sum_range
      (fun i => tent (Real.pi * θ) (α - (-(Real.pi * (1 + θ)) + (i : ℝ) * (Real.pi * θ))))]
    have hterm : ∀ i : ℕ, tent (Real.pi * θ) (α - (-(Real.pi * (1 + θ)) + (i : ℝ) * (Real.pi * θ)))
        = (fun m : ℕ => quinticStep (t - m)) i - (fun m : ℕ => quinticStep (t - m)) (i + 1) := by
      intro i
      unfold tent
      have h1 : (α - (-(Real.pi * (1 + θ)) + (i : ℝ) * (Real.pi * θ))) / (Real.pi * θ) = t - i := by
        rw [ht]; field_simp; ring
      have h2 : (α - (-(Real.pi * (1 + θ)) + (i : ℝ) * (Real.pi * θ))) / (Real.pi * θ) - 1
          = t - (i + 1) := by
        rw [ht]; push_cast; field_simp; ring
      rw [h2, h1]
      simp only [Nat.cast_add, Nat.cast_one]
    rw [Finset.sum_congr rfl (fun i _ => hterm i)]
    have htel := sum_range_telescope (fun m : ℕ => quinticStep (t - m)) (Nat.ceil (2 / θ) + 1)
    rw [htel]
    have ht1 : 1 ≤ t := by
      rw [ht, le_div_iff₀ hWpos]
      nlinarith [Real.pi_pos, hlo]
    have htK : t - ((Nat.ceil (2 / θ) + 1 : ℕ) : ℝ) ≤ 0 := by
      have hceil : (2 : ℝ) / θ ≤ (Nat.ceil (2 / θ) : ℝ) := Nat.le_ceil _
      have htle : t ≤ 2 / θ + 1 := by
        rw [ht, div_le_iff₀ hWpos]
        have he : (2 / θ + 1) * (Real.pi * θ) = 2 * Real.pi + Real.pi * θ := by field_simp
        rw [he]; linarith
      push_cast
      linarith
    have h0 : t - ((0 : ℕ) : ℝ) = t := by norm_num
    rw [h0, quinticStep_eq_one_of_one_le _ ht1, quinticStep_eq_zero_of_nonpos _ htK]
    ring
  · intro k j hj α
    interval_cases j
    · rw [iteratedDeriv_zero, cMoll_zero, abs_of_nonneg (tent_nonneg _ α)]
      simp only [Nat.cast_zero, neg_zero, Real.rpow_zero, mul_one]
      exact tent_le_one _ α
    · calc |iteratedDeriv 1 (tent (Real.pi * θ)) α| ≤ 4 / (Real.pi * θ) :=
            abs_iteratedDeriv_one_tent_le _ hWpos α
        _ ≤ cMoll 1 * θ ^ (-((1 : ℕ) : ℝ)) := by
            have h4pi : (4 : ℝ) / Real.pi ≤ 1024 := by
              rw [div_le_iff₀ Real.pi_pos]; nlinarith [Real.pi_gt_three]
            calc (4 : ℝ) / (Real.pi * θ) = (4 / Real.pi) * (1 / θ) := by field_simp
              _ ≤ 1024 * (1 / θ) := mul_le_mul_of_nonneg_right h4pi (by positivity)
              _ = cMoll 1 * θ ^ (-((1 : ℕ) : ℝ)) := by
                    rw [cMoll_one]; norm_num [Real.rpow_neg_one]
    · calc |iteratedDeriv 2 (tent (Real.pi * θ)) α| ≤ 12 / (Real.pi * θ) ^ 2 :=
            abs_iteratedDeriv_two_tent_le _ hWpos α
        _ ≤ cMoll 2 * θ ^ (-((2 : ℕ) : ℝ)) := by
            have h12pi : (12 : ℝ) / Real.pi ^ 2 ≤ (2 : ℝ) ^ 20 := by
              rw [div_le_iff₀ (by positivity : (0 : ℝ) < Real.pi ^ 2)]
              nlinarith [Real.pi_gt_three, sq_nonneg (Real.pi - 3)]
            have hrpow : θ ^ (-((2 : ℕ) : ℝ)) = 1 / θ ^ 2 := by
              rw [show -(((2 : ℕ)) : ℝ) = -(2 : ℝ) by norm_num, Real.rpow_neg hθ0.le 2,
                  show ((2 : ℝ)) = ((2 : ℕ) : ℝ) by norm_num, Real.rpow_natCast, inv_eq_one_div]
            calc (12 : ℝ) / (Real.pi * θ) ^ 2 = ((12 / Real.pi ^ 2)) * (1 / θ ^ 2) := by field_simp
              _ ≤ (2 : ℝ) ^ 20 * (1 / θ ^ 2) := mul_le_mul_of_nonneg_right h12pi (by positivity)
              _ = cMoll 2 * θ ^ (-((2 : ℕ) : ℝ)) := by rw [cMoll_two, hrpow]
  · have hceil : ((Nat.ceil (2 / θ) : ℕ) : ℝ) ≤ 2 / θ + 1 :=
      le_of_lt (Nat.ceil_lt_add_one (by positivity))
    have h2θ : (2 : ℝ) / θ ≤ 4 / θ := div_le_div_of_nonneg_right (by norm_num) hθ0.le
    push_cast
    linarith

/-! ## 3. Reindexing a `Finset`-supported family along `Fin s.card` -/

/-- A sum over `Fin s.card` of the values of `g` on `s`, ordered by `s.orderIsoOfFin`, is the
`Finset`-sum over `s`. -/
lemma sum_fin_orderIsoOfFin {α : Type*} [LinearOrder α] (s : Finset α) (g : α → ℝ) :
    (∑ i : Fin s.card, g (((s.orderIsoOfFin rfl) i : ↥s) : α)) = ∑ x ∈ s, g x := by
  rw [← Finset.sum_attach s g, Finset.attach_eq_univ]
  exact Equiv.sum_comp (s.orderIsoOfFin rfl).toEquiv (fun x : ↥s => g (x : α))

/-! ## 4. The mollifier family -/

/-- **The mollifier family of the Friedlander–Iwaniec reduction.** -/
theorem mollifier_family (N : ℕ) (θ : ℝ) (hN : 1 ≤ N) (hθ0 : 0 < θ) (hθ1 : θ ≤ 1 / 4) :
    ∃ (K K' : ℕ) (a : Fin K → ℝ) (p : Fin K → ℝ → ℝ) (φ : Fin K' → ℝ) (q : Fin K' → ℝ → ℝ),
      (∀ i, (N : ℝ) ≤ a i ∧ a i ≤ 2 * (N : ℝ)) ∧
      (∀ i, ContDiff ℝ 2 (p i)) ∧ (∀ k, ContDiff ℝ 2 (q k)) ∧
      (∀ i u, 0 ≤ p i u) ∧ (∀ i u, p i u ≤ 1) ∧
      (∀ i u, p i u ≠ 0 → a i < u ∧ u ≤ (1 + θ) * a i) ∧
      (∀ i u, p i u ≠ 0 → u ≤ 2 * (N : ℝ)) ∧
      (∀ u, (N : ℝ) < u → u ≤ 2 * (N : ℝ) → (∑ i, p i u) ≤ 1) ∧
      (∀ u, (N : ℝ) + θ * (N : ℝ) / 2 < u → u ≤ 2 * (N : ℝ) - 2 * θ * (N : ℝ) →
          (∑ i, p i u) = 1) ∧
      (∀ i j, j ≤ 2 → ∀ u, |iteratedDeriv j (p i) u| ≤ cMoll j * (θ * a i) ^ (-(j : ℝ))) ∧
      (∀ k α, 0 ≤ q k α) ∧ (∀ k α, q k α ≤ 1) ∧ (∀ k, q k 0 = 0) ∧
      (∀ k α, q k α ≠ 0 → 0 ≤ α ∧ α ≤ 2 * Real.pi * θ) ∧
      (∀ α, -Real.pi ≤ α → α ≤ Real.pi → (∑ k, q k (α - φ k)) = 1) ∧
      (∀ k j, j ≤ 2 → ∀ α, |iteratedDeriv j (q k) α| ≤ cMoll j * θ ^ (-(j : ℝ))) ∧
      ((K : ℝ) ≤ 4 / θ + 4) ∧ ((K' : ℝ) ≤ 4 / θ + 4) := by
  obtain ⟨K₀, a₀, P, R, hcd, hp0, hp1, hsup, ha, hle2N, hsum_le, hsum_eq, hder, hcard⟩ :=
    radial_pieces_flat N θ hN hθ0 hθ1
  obtain ⟨K', φ, q, hqcd, hq0, hq1, hq0z, hqsup, hang, hqd, hK'⟩ :=
    angular_partition_le0 θ hθ0 hθ1
  refine ⟨R.card, K', (fun i => a₀ ((R.orderIsoOfFin rfl i).val)),
    (fun i => P ((R.orderIsoOfFin rfl i).val)), φ, q,
    ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · intro i; exact ha _ (R.orderIsoOfFin rfl i).2
  · intro i; exact hcd _ (R.orderIsoOfFin rfl i).2
  · exact hqcd
  · intro i u; exact hp0 _ (R.orderIsoOfFin rfl i).2 u
  · intro i u; exact hp1 _ (R.orderIsoOfFin rfl i).2 u
  · intro i u; exact hsup _ (R.orderIsoOfFin rfl i).2 u
  · intro i u; exact hle2N _ (R.orderIsoOfFin rfl i).2 u
  · intro u hu1 hu2
    rw [sum_fin_orderIsoOfFin R (fun x => P x u)]
    exact hsum_le u hu1 hu2
  · intro u hu1 hu2
    rw [sum_fin_orderIsoOfFin R (fun x => P x u)]
    exact hsum_eq u hu1 hu2
  · intro i j hj u; exact hder _ (R.orderIsoOfFin rfl i).2 j hj u
  · exact hq0
  · exact hq1
  · exact hq0z
  · exact hqsup
  · exact hang
  · exact hqd
  · exact hcard
  · exact hK'

end

end Work.FITop4.Red5
