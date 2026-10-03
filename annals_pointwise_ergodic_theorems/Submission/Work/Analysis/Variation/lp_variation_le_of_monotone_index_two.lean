/-
Two-dimensional analogue of `lp_variation_le_of_monotone_index`: the `ℓ^r` variation of a
sequence indexed by a componentwise monotone path in `ℕ × ℕ`.
-/
import Mathlib
import Submission.Work.Analysis.Variation.Minkowski

set_option autoImplicit false

open scoped BigOperators ENNReal
open Finset

namespace Work.Analysis.Variation

/-- **Two-dimensional `ℓ^r` variation of a componentwise monotone-indexed sequence.**  Let
`p₁, p₂ : Fin (J+1) → ℕ` be monotone with `p₁ j < n₁`, `p₂ j < n₂` for all `j`, and let
`f : ℕ → ℕ → ℂ`.  Then for `r ≥ 1`
`(∑_{j < J} ‖f (p₁ (j+1)) (p₂ (j+1)) - f (p₁ j) (p₂ j)‖^r)^{1/r}
  ≤ 2 (∑_{q ∈ range n₁ × range n₂} ‖f q.1 q.2‖^r)^{1/r}`.
Proof as in the one-dimensional case `lp_variation_le_of_monotone_index`: on the jump set
`T = {j | (p₁ j, p₂ j) ≠ (p₁ (j+1), p₂ (j+1))}` the maps `j ↦ (p₁ j, p₂ j)` and
`j ↦ (p₁ (j+1), p₂ (j+1))` are injective, hence both `∑_{j∈T}‖f (p₁ j) (p₂ j)‖^r` and
`∑_{j∈T} ‖f (p₁ (j+1)) (p₂ (j+1))‖^r` are bounded by the `ℓ^r` norm over the grid; then apply
`Work.Analysis.Variation.add_rpow_sum_le` to split the differences. -/
theorem lp_variation_le_of_monotone_index_two {r : ℝ} (hr : 1 ≤ r) {n₁ n₂ J : ℕ}
    (f : ℕ → ℕ → ℂ) (p₁ p₂ : Fin (J + 1) → ℕ) (h₁ : Monotone p₁) (h₂ : Monotone p₂)
    (hn₁ : ∀ j, p₁ j < n₁) (hn₂ : ∀ j, p₂ j < n₂) :
    (∑ j : Fin J, ‖f (p₁ j.succ) (p₂ j.succ) - f (p₁ j.castSucc) (p₂ j.castSucc)‖ₑ ^ r)
        ^ (1 / r)
      ≤ 2 * (∑ q ∈ (Finset.range n₁).product (Finset.range n₂), ‖f q.1 q.2‖ₑ ^ r)
          ^ (1 / r) := by
  classical
  have hr0 : (0 : ℝ) < r := lt_of_lt_of_le zero_lt_one hr
  have h1r : (0 : ℝ) < 1 / r := div_pos zero_lt_one hr0
  -- the set of jump positions
  set T : Finset (Fin J) := Finset.univ.filter
    (fun j => (p₁ j.castSucc, p₂ j.castSucc) ≠ (p₁ j.succ, p₂ j.succ)) with hT
  have hTmem : ∀ j ∈ T, (p₁ j.castSucc, p₂ j.castSucc) ≠ (p₁ j.succ, p₂ j.succ) := by
    intro j hj
    simp only [hT, Finset.mem_filter, Finset.mem_univ, true_and] at hj
    exact hj
  have hle₁ : ∀ j : Fin J, p₁ j.castSucc ≤ p₁ j.succ := fun j => h₁ (Fin.castSucc_le_succ j)
  have hle₂ : ∀ j : Fin J, p₂ j.castSucc ≤ p₂ j.succ := fun j => h₂ (Fin.castSucc_le_succ j)
  -- on `T`, the two endpoint maps are injective
  have key₁ : ∀ j j' : Fin J, j < j' → j ∈ T → j' ∈ T →
      (p₁ j.castSucc, p₂ j.castSucc) ≠ (p₁ j'.castSucc, p₂ j'.castSucc) := by
    intro j j' hlt hj hj' heq
    have h2₁ : p₁ j.succ ≤ p₁ j'.castSucc := h₁ (Fin.succ_le_castSucc_iff.mpr hlt)
    have h2₂ : p₂ j.succ ≤ p₂ j'.castSucc := h₂ (Fin.succ_le_castSucc_iff.mpr hlt)
    have e₁ : p₁ j.castSucc = p₁ j'.castSucc := congrArg Prod.fst heq
    have e₂ : p₂ j.castSucc = p₂ j'.castSucc := congrArg Prod.snd heq
    have h₁' : p₁ j.succ = p₁ j.castSucc := le_antisymm (by rw [e₁]; exact h2₁) (hle₁ j)
    have h₂' : p₂ j.succ = p₂ j.castSucc := le_antisymm (by rw [e₂]; exact h2₂) (hle₂ j)
    exact hTmem j hj (Prod.ext h₁'.symm h₂'.symm)
  have key₂ : ∀ j j' : Fin J, j < j' → j ∈ T → j' ∈ T →
      (p₁ j.succ, p₂ j.succ) ≠ (p₁ j'.succ, p₂ j'.succ) := by
    intro j j' hlt hj hj' heq
    have h2₁ : p₁ j.succ ≤ p₁ j'.castSucc := h₁ (Fin.succ_le_castSucc_iff.mpr hlt)
    have h2₂ : p₂ j.succ ≤ p₂ j'.castSucc := h₂ (Fin.succ_le_castSucc_iff.mpr hlt)
    have e₁ : p₁ j.succ = p₁ j'.succ := congrArg Prod.fst heq
    have e₂ : p₂ j.succ = p₂ j'.succ := congrArg Prod.snd heq
    have h₁' : p₁ j'.castSucc = p₁ j'.succ := le_antisymm (hle₁ j') (by rw [← e₁]; exact h2₁)
    have h₂' : p₂ j'.castSucc = p₂ j'.succ := le_antisymm (hle₂ j') (by rw [← e₂]; exact h2₂)
    exact hTmem j' hj' (Prod.ext h₁' h₂')
  -- off `T` the successive differences vanish
  have hzero : ∀ j : Fin J, (p₁ j.castSucc, p₂ j.castSucc) = (p₁ j.succ, p₂ j.succ) →
      ‖f (p₁ j.succ) (p₂ j.succ) - f (p₁ j.castSucc) (p₂ j.castSucc)‖ₑ ^ r = 0 := by
    intro j hj
    have e₁ : p₁ j.castSucc = p₁ j.succ := congrArg Prod.fst hj
    have e₂ : p₂ j.castSucc = p₂ j.succ := congrArg Prod.snd hj
    rw [← e₁, ← e₂, sub_self, enorm_zero, ENNReal.zero_rpow_of_pos hr0]
  have hsumT : ∑ j : Fin J, ‖f (p₁ j.succ) (p₂ j.succ) - f (p₁ j.castSucc) (p₂ j.castSucc)‖ₑ ^ r
      = ∑ j ∈ T, ‖f (p₁ j.succ) (p₂ j.succ) - f (p₁ j.castSucc) (p₂ j.castSucc)‖ₑ ^ r := by
    rw [hT]
    refine (Finset.sum_filter_of_ne ?_).symm
    intro j _ hj0
    by_contra hne
    exact hj0 (hzero j hne)
  -- triangle inequality, termwise on `T`
  have hterm : ∀ j ∈ T, ‖f (p₁ j.succ) (p₂ j.succ) - f (p₁ j.castSucc) (p₂ j.castSucc)‖ₑ ^ r
      ≤ (‖f (p₁ j.succ) (p₂ j.succ)‖ₑ + ‖f (p₁ j.castSucc) (p₂ j.castSucc)‖ₑ) ^ r := fun j _ =>
    ENNReal.rpow_le_rpow enorm_sub_le hr0.le
  -- both extremal sums over `T` are bounded by the `ℓ^r` norm over the grid
  have hbound : ∀ (g₁ g₂ : Fin J → ℕ),
      (∀ j j' : Fin J, j < j' → j ∈ T → j' ∈ T → (g₁ j, g₂ j) ≠ (g₁ j', g₂ j')) →
      (∀ j ∈ T, g₁ j < n₁) → (∀ j ∈ T, g₂ j < n₂) →
      (∑ j ∈ T, ‖f (g₁ j) (g₂ j)‖ₑ ^ r) ^ (1 / r)
        ≤ (∑ q ∈ (Finset.range n₁).product (Finset.range n₂), ‖f q.1 q.2‖ₑ ^ r)
          ^ (1 / r) := by
    intro g₁ g₂ hinj hn1 hn2
    have hinj' : Set.InjOn (fun j => (g₁ j, g₂ j)) ↑T := by
      intro a ha b hb hab
      have ha' := Finset.mem_coe.mp ha
      have hb' := Finset.mem_coe.mp hb
      by_contra hne
      rcases lt_or_gt_of_ne hne with hlt | hlt
      · exact absurd hab (hinj a b hlt ha' hb')
      · exact absurd hab.symm (hinj b a hlt hb' ha')
    have himg : T.image (fun j => (g₁ j, g₂ j)) ⊆ (Finset.range n₁).product (Finset.range n₂) := by
      intro q hq
      obtain ⟨j, hj, rfl⟩ := Finset.mem_image.mp hq
      exact Finset.mem_product.mpr ⟨Finset.mem_range.mpr (hn1 j hj),
        Finset.mem_range.mpr (hn2 j hj)⟩
    calc (∑ j ∈ T, ‖f (g₁ j) (g₂ j)‖ₑ ^ r) ^ (1 / r)
        = (∑ q ∈ T.image (fun j => (g₁ j, g₂ j)), ‖f q.1 q.2‖ₑ ^ r) ^ (1 / r) := by
          rw [Finset.sum_image hinj']
      _ ≤ (∑ q ∈ (Finset.range n₁).product (Finset.range n₂), ‖f q.1 q.2‖ₑ ^ r) ^ (1 / r) :=
          ENNReal.rpow_le_rpow (Finset.sum_le_sum_of_subset himg) h1r.le
  have hA := hbound (fun j => p₁ j.succ) (fun j => p₂ j.succ)
    (fun j j' hlt hj hj' => key₂ j j' hlt hj hj')
    (fun j _ => hn₁ j.succ) (fun j _ => hn₂ j.succ)
  have hB := hbound (fun j => p₁ j.castSucc) (fun j => p₂ j.castSucc)
    (fun j j' hlt hj hj' => key₁ j j' hlt hj hj')
    (fun j _ => hn₁ j.castSucc) (fun j _ => hn₂ j.castSucc)
  calc (∑ j : Fin J, ‖f (p₁ j.succ) (p₂ j.succ) - f (p₁ j.castSucc) (p₂ j.castSucc)‖ₑ ^ r)
          ^ (1 / r)
      = (∑ j ∈ T, ‖f (p₁ j.succ) (p₂ j.succ) - f (p₁ j.castSucc) (p₂ j.castSucc)‖ₑ ^ r)
          ^ (1 / r) := by rw [hsumT]
    _ ≤ (∑ j ∈ T, (‖f (p₁ j.succ) (p₂ j.succ)‖ₑ + ‖f (p₁ j.castSucc) (p₂ j.castSucc)‖ₑ) ^ r)
          ^ (1 / r) := ENNReal.rpow_le_rpow (Finset.sum_le_sum hterm) h1r.le
    _ ≤ (∑ j ∈ T, ‖f (p₁ j.succ) (p₂ j.succ)‖ₑ ^ r) ^ (1 / r)
        + (∑ j ∈ T, ‖f (p₁ j.castSucc) (p₂ j.castSucc)‖ₑ ^ r) ^ (1 / r) :=
        add_rpow_sum_le hr T (fun j => ‖f (p₁ j.succ) (p₂ j.succ)‖ₑ)
          (fun j => ‖f (p₁ j.castSucc) (p₂ j.castSucc)‖ₑ)
    _ ≤ (∑ q ∈ (Finset.range n₁).product (Finset.range n₂), ‖f q.1 q.2‖ₑ ^ r) ^ (1 / r)
        + (∑ q ∈ (Finset.range n₁).product (Finset.range n₂), ‖f q.1 q.2‖ₑ ^ r) ^ (1 / r) :=
        add_le_add hA hB
    _ = 2 * (∑ q ∈ (Finset.range n₁).product (Finset.range n₂), ‖f q.1 q.2‖ₑ ^ r) ^ (1 / r) :=
        (two_mul _).symm

end Work.Analysis.Variation
