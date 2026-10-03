import Mathlib
import Submission.Work.Analysis.Variation.Minkowski

namespace Work.Analysis.Variation

/-- **`ℓ^r` variation of a monotone-indexed sequence.**  Let `p : Fin (J+1) → ℕ` be monotone with
`p j < n` for all `j` and `f : ℕ → ℂ`.  Then for `r ≥ 1` the `ℓ^r` norm of the successive
differences of `(f (p j))_j` is at most twice the `ℓ^r` norm of `f` on `range n`:
`(∑_{j < J} ‖f (p (j+1)) - f (p j)‖^r)^{1/r} ≤ 2 (∑_{x < n} ‖f x‖^r)^{1/r}` (all norms in
`ℝ≥0∞`).  This replaces "the values `f (p j)` are distinct" when `p` is only monotone: on the set
`T = {j | p j ≠ p (j+1)}` of jump positions both `j ↦ p j` and `j ↦ p (j+1)` are *injective*
(if `j < j'` are in `T` then `p j < p j'` and `p (j+1) < p (j'+1)`, since `p j < p (j+1) ≤ p j'`),
so `∑_{j ∈ T} ‖f (p j)‖^r` and `∑_{j ∈ T} ‖f (p (j+1))‖^r` are both bounded by
`∑_{x < n} ‖f x‖^r` (`Finset.sum_image` plus `Finset.sum_le_sum_of_subset_of_nonneg`); the
Minkowski inequality `Work.Analysis.Variation.rpow_sum_sum_le` then splits the differences and the
sum over `j ∉ T` is zero. -/
theorem lp_variation_le_of_monotone_index {r : ℝ} (hr : 1 ≤ r) {n J : ℕ} (f : ℕ → ℂ)
    (p : Fin (J + 1) → ℕ) (hp : Monotone p) (hpn : ∀ j, p j < n) :
    (∑ j : Fin J, ‖f (p j.succ) - f (p j.castSucc)‖ₑ ^ r) ^ (1 / r)
      ≤ 2 * (∑ x ∈ Finset.range n, ‖f x‖ₑ ^ r) ^ (1 / r) := by
  classical
  -- `r > 0`, hence `1/r > 0`: the exponents of all `rpow`-monotonicity applications below.
  have hr0 : (0 : ℝ) < r := lt_of_lt_of_le zero_lt_one hr
  have h1r : (0 : ℝ) < 1 / r := div_pos zero_lt_one hr0
  -- the set of jump positions.
  set T : Finset (Fin J) := Finset.univ.filter (fun j => p j.castSucc ≠ p j.succ) with hT
  have hTmem : ∀ j ∈ T, p j.castSucc ≠ p j.succ := by
    intro j hj
    simp only [hT, Finset.mem_filter, Finset.mem_univ, true_and] at hj
    exact hj
  have hcs_le : ∀ j : Fin J, p j.castSucc ≤ p j.succ := fun j => hp (Fin.castSucc_le_succ j)
  -- on `T`, both `j ↦ p j.castSucc` and `j ↦ p j.succ` are strictly increasing.
  have key : ∀ j j' : Fin J, j < j' → j ∈ T → j' ∈ T →
      p j.castSucc < p j'.castSucc ∧ p j.succ < p j'.succ := by
    intro j j' hlt hj hj'
    have h2 : p j.succ ≤ p j'.castSucc := hp (Fin.succ_le_castSucc_iff.mpr hlt)
    exact ⟨lt_of_lt_of_le (lt_of_le_of_ne (hcs_le j) (hTmem j hj)) h2,
      lt_of_le_of_lt h2 (lt_of_le_of_ne (hcs_le j') (hTmem j' hj'))⟩
  -- off `T` the successive differences vanish.
  have hzero : ∀ j : Fin J, p j.castSucc = p j.succ →
      ‖f (p j.succ) - f (p j.castSucc)‖ₑ ^ r = 0 := by
    intro j hj
    rw [← hj, sub_self, enorm_zero, ENNReal.zero_rpow_of_pos hr0]
  have hsumT : ∑ j : Fin J, ‖f (p j.succ) - f (p j.castSucc)‖ₑ ^ r
      = ∑ j ∈ T, ‖f (p j.succ) - f (p j.castSucc)‖ₑ ^ r := by
    rw [hT]
    refine (Finset.sum_filter_of_ne ?_).symm
    intro j _ hj0
    by_contra hne
    exact hj0 (hzero j hne)
  -- triangle inequality, termwise on `T`.
  have hterm : ∀ j ∈ T, ‖f (p j.succ) - f (p j.castSucc)‖ₑ ^ r
      ≤ (‖f (p j.succ)‖ₑ + ‖f (p j.castSucc)‖ₑ) ^ r := fun j _ =>
    ENNReal.rpow_le_rpow enorm_sub_le hr0.le
  -- both extremal sums over `T` are bounded by the `ℓ^r` norm of `f` on `range n`.
  have hbound : ∀ (g : Fin J → ℕ),
      (∀ j j' : Fin J, j < j' → j ∈ T → j' ∈ T → g j < g j') → (∀ j ∈ T, g j < n) →
      (∑ j ∈ T, ‖f (g j)‖ₑ ^ r) ^ (1 / r)
        ≤ (∑ x ∈ Finset.range n, ‖f x‖ₑ ^ r) ^ (1 / r) := by
    intro g hmono hn
    have hinj : Set.InjOn g ↑T := by
      intro a ha b hb hab
      have ha' := Finset.mem_coe.mp ha
      have hb' := Finset.mem_coe.mp hb
      by_contra hne
      rcases lt_or_gt_of_ne hne with hlt | hlt
      · exact absurd hab (ne_of_lt (hmono a b hlt ha' hb'))
      · exact absurd hab.symm (ne_of_lt (hmono b a hlt hb' ha'))
    have himg : T.image g ⊆ Finset.range n := by
      intro x hx
      obtain ⟨j, hj, rfl⟩ := Finset.mem_image.mp hx
      exact Finset.mem_range.mpr (hn j hj)
    calc (∑ j ∈ T, ‖f (g j)‖ₑ ^ r) ^ (1 / r)
        = (∑ x ∈ T.image g, ‖f x‖ₑ ^ r) ^ (1 / r) := by rw [Finset.sum_image hinj]
      _ ≤ (∑ x ∈ Finset.range n, ‖f x‖ₑ ^ r) ^ (1 / r) :=
          ENNReal.rpow_le_rpow (Finset.sum_le_sum_of_subset himg) h1r.le
  have hA := hbound (fun j => p j.succ) (fun j j' hlt hj hj' => (key j j' hlt hj hj').2)
    (fun j _ => hpn j.succ)
  have hB := hbound (fun j => p j.castSucc) (fun j j' hlt hj hj' => (key j j' hlt hj hj').1)
    (fun j _ => hpn j.castSucc)
  calc (∑ j : Fin J, ‖f (p j.succ) - f (p j.castSucc)‖ₑ ^ r) ^ (1 / r)
      = (∑ j ∈ T, ‖f (p j.succ) - f (p j.castSucc)‖ₑ ^ r) ^ (1 / r) := by rw [hsumT]
    _ ≤ (∑ j ∈ T, (‖f (p j.succ)‖ₑ + ‖f (p j.castSucc)‖ₑ) ^ r) ^ (1 / r) :=
        ENNReal.rpow_le_rpow (Finset.sum_le_sum hterm) h1r.le
    _ ≤ (∑ j ∈ T, ‖f (p j.succ)‖ₑ ^ r) ^ (1 / r)
        + (∑ j ∈ T, ‖f (p j.castSucc)‖ₑ ^ r) ^ (1 / r) :=
        add_rpow_sum_le hr T (fun j => ‖f (p j.succ)‖ₑ) (fun j => ‖f (p j.castSucc)‖ₑ)
    _ ≤ (∑ x ∈ Finset.range n, ‖f x‖ₑ ^ r) ^ (1 / r)
        + (∑ x ∈ Finset.range n, ‖f x‖ₑ ^ r) ^ (1 / r) := add_le_add hA hB
    _ = 2 * (∑ x ∈ Finset.range n, ‖f x‖ₑ ^ r) ^ (1 / r) := (two_mul _).symm

end Work.Analysis.Variation
