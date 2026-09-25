import Mathlib
import Submission.Work.BourgainPlan.Oscillation.lacunary_defs
import Submission.Work.BourgainPlan.Oscillation.lacunary_truncated_maximal_l2

/-!
# Elementary helpers for the `ρ`-lacunary cut family `θ ↦ 1_{θ ≤ s ρ^{-i}}`

The oscillation estimate `oscZ_cut_shift` needs the *maximal* inequality for the family of sharp
frequency cuts `1_{(0, s ρ^{-i}]}`, `i ∈ ℕ`, with the radius `s > 0` arbitrary but the constant
independent of `s`.  The aligned (unshifted) family `1_{(0, ρ^{-i}]}` is covered by
`lacunary_truncated_maximal_l2`; the point of this file is the two elementary facts that let one
move the *shift* `s` onto the lattice and pay for the resulting "gap" operators by disjointness:

* `exists_zpow_le_lt`: every `s > 0` is trapped by two consecutive powers of `ρ`, i.e. there is
  `k : ℤ` with `ρ ^ k ≤ s < ρ ^ (k + 1)`;
* `tsum_ioc_zpow_le`: the lacunary annuli `(ρ ^ n, ρ ^ (n + 1)]` attached to distinct integers `n`
  are pairwise disjoint, which makes the *sum* of the `θ`-energies of the gaps summable.

Also `cut_indicator_ae`, which identifies the one-sided cut `1_{θ ≤ c}` with the symmetric cut
`1_{|θ| ≤ c}` almost everywhere for the reference measure `mu01` (a fact needed to feed
`lacunary_truncated_maximal_l2`, whose cuts are written with `|·|`, into the one-sided setting of
the statement).
-/

namespace Work.BourgainPlan.Oscillation

open Finset MeasureTheory
open scoped BigOperators ENNReal

noncomputable section

/-- **Snapping to the `ρ`-lattice.**  For `ρ > 1` and `s > 0` there is `k : ℤ` with
`ρ ^ k ≤ s < ρ ^ (k + 1)`. -/
lemma exists_zpow_le_lt (ρ : ℝ) (hρ : 1 < ρ) (s : ℝ) (hs : 0 < s) :
    ∃ k : ℤ, ρ ^ k ≤ s ∧ s < ρ ^ (k + 1) := by
  have hρ0 : 0 < ρ := by linarith
  have hne : ρ ≠ 1 := by linarith
  refine ⟨⌊Real.logb ρ s⌋, ?_, ?_⟩
  · rw [← Real.rpow_intCast ρ ⌊Real.logb ρ s⌋]
    calc ρ ^ (((⌊Real.logb ρ s⌋ : ℤ)) : ℝ) ≤ ρ ^ (Real.logb ρ s) :=
          (Real.rpow_le_rpow_left_iff hρ).mpr (Int.floor_le _)
      _ = s := Real.rpow_logb hρ0 hne hs
  · rw [← Real.rpow_intCast ρ (⌊Real.logb ρ s⌋ + 1)]
    calc s = ρ ^ (Real.logb ρ s) := (Real.rpow_logb hρ0 hne hs).symm
      _ < ρ ^ (((⌊Real.logb ρ s⌋ : ℤ) : ℝ) + 1) :=
          (Real.rpow_lt_rpow_left_iff hρ).mpr (Int.lt_floor_add_one _)
      _ = ρ ^ (((⌊Real.logb ρ s⌋ + 1 : ℤ)) : ℝ) := by
          congr 1; push_cast; ring

/-- The one-sided frequency cut `1_{θ ≤ c}` agrees with the symmetric cut `1_{|θ| ≤ c}` almost
everywhere for `mu01` (whose underlying set is `(0, 1]`). -/
lemma cut_indicator_ae (ρ : ℝ) (i : ℕ) :
    (fun θ : ℝ => (if |θ| ≤ Lacunary.cc ρ i then (1 : ℂ) else 0))
      =ᵐ[Lacunary.mu01] (fun θ : ℝ => (if θ ≤ Lacunary.cc ρ i then (1 : ℂ) else 0)) := by
  filter_upwards [MeasureTheory.ae_restrict_mem (μ := volume) measurableSet_Ioc] with θ hθ
  rw [abs_of_pos hθ.1]

/-- The lacunary annuli `(ρ ^ n, ρ ^ (n + 1)]` of *distinct* integers `n` are pairwise
disjoint. -/
lemma pairwiseDisjoint_ioc_zpow {ρ : ℝ} (hρ : 1 < ρ) (n : ℕ → ℤ) (hn : Function.Injective n) :
    Pairwise (Function.onFun Disjoint fun i : ℕ => Set.Ioc (ρ ^ (n i)) (ρ ^ (n i + 1))) := by
  intro i j hij
  rw [Function.onFun, Set.disjoint_left]
  intro θ h1 h2
  rw [Set.mem_Ioc] at h1 h2
  have hne : n i ≠ n j := fun h => hij (hn h)
  rcases lt_or_gt_of_ne hne with h | h
  · have hle : ρ ^ (n i + 1) ≤ ρ ^ (n j) :=
      zpow_le_zpow_right₀ (le_of_lt hρ) (by omega)
    linarith [h1.2, h2.1]
  · have hle : ρ ^ (n j + 1) ≤ ρ ^ (n i) :=
      zpow_le_zpow_right₀ (le_of_lt hρ) (by omega)
    linarith [h1.1, h2.2]

/-- **The disjoint annuli sum.**  The sum of the `θ`-energies of any family of lacunary annuli
`(ρ ^ (n i), ρ ^ (n i + 1)]` indexed by *distinct* integers `n i` is at most the total energy on
`(0, ∞)`. -/
lemma tsum_ioc_zpow_le {ρ : ℝ} (hρ : 1 < ρ) (n : ℕ → ℤ) (hn : Function.Injective n)
    (f : ℝ → ℝ≥0∞) :
    ∑' i : ℕ, ∫⁻ θ in Set.Ioc (ρ ^ (n i)) (ρ ^ (n i + 1)), f θ ≤ ∫⁻ θ in Set.Ioi (0 : ℝ), f θ := by
  rw [← lintegral_iUnion
    (fun i => measurableSet_Ioc) (pairwiseDisjoint_ioc_zpow hρ n hn) f]
  refine lintegral_mono_set ?_
  intro θ hθ
  rw [Set.mem_iUnion] at hθ
  obtain ⟨i, hi⟩ := hθ
  rw [Set.mem_Ioc] at hi
  exact lt_trans (zpow_pos (by linarith : (0:ℝ) < ρ) _) hi.1

end

end Work.BourgainPlan.Oscillation
