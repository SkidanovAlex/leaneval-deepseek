import Mathlib
import Submission.Work.EKLRelCross.PeriodDefs

/-!
# Test functions for separating measures carried by a root subgroup

This file sets up the definitions used in
`Work.EKLRelCross.exists_separating_periodFuns`.

For fixed `i ≠ j` we consider the one-parameter root subgroup
`φ : ℝ → SL₃(ℝ)`, `φ t = u_ij(t) = 1 + t E_ij`, its coordinate functional
`c : SL₃(ℝ) → ℝ`, `c g = g i j` (so that `c ∘ φ = id`), and a family of
"tent" functions on `ℝ` which increase pointwise to the indicator of an open
interval.
-/

namespace Work.EKLRelCross

open MeasureTheory Filter Topology Set
open scoped ENNReal

noncomputable section

open Work.EKLContract

/-! ## The coordinate functional on the root subgroup -/

theorem uij_coeff {i j : Fin 3} (hij : i ≠ j) (t : ℝ) :
    (uij hij t : Matrix (Fin 3) (Fin 3) ℝ) i j = t := by
  rw [uij, Matrix.SpecialLinearGroup.transvection_coe]
  simp [hij]

theorem uij_injective {i j : Fin 3} (hij : i ≠ j) :
    Function.Injective fun t : ℝ => uij hij t := by
  intro a b hab
  have h : (uij hij a : Matrix (Fin 3) (Fin 3) ℝ) i j
      = (uij hij b : Matrix (Fin 3) (Fin 3) ℝ) i j :=
    congrArg (fun g : SL3 => (g : Matrix (Fin 3) (Fin 3) ℝ) i j) hab
  rwa [uij_coeff, uij_coeff] at h

theorem continuous_coeff {i j : Fin 3} :
    Continuous fun g : SL3 => (g : Matrix (Fin 3) (Fin 3) ℝ) i j := by
  fun_prop

/-! ## Tent functions -/

/-- The tent function on the interval `[a,b]`, of steepness `n`.  It is `0` outside
`[a,b]`, equals `1` in the middle of `(a,b)` (for large `n`), and increases pointwise
to the indicator of `Ioo a b` as `n → ∞`. -/
def tentFun (a b : ℝ) (n : ℕ) : ℝ → ℝ :=
  fun t => max 0 (min 1 (min ((n : ℝ) * (t - a)) ((n : ℝ) * (b - t))))

theorem tentFun_apply (a b : ℝ) (n : ℕ) (t : ℝ) :
    tentFun a b n t = max 0 (min 1 (min ((n : ℝ) * (t - a)) ((n : ℝ) * (b - t)))) :=
  rfl

theorem continuous_tentFun (a b : ℝ) (n : ℕ) : Continuous (tentFun a b n) := by
  unfold tentFun
  fun_prop

theorem tentFun_nonneg (a b : ℝ) (n : ℕ) (t : ℝ) : 0 ≤ tentFun a b n t := le_max_left _ _

theorem tentFun_le_one (a b : ℝ) (n : ℕ) (t : ℝ) : tentFun a b n t ≤ 1 :=
  max_le zero_le_one (le_trans (min_le_left _ _) le_rfl)

theorem support_tentFun_subset (a b : ℝ) (n : ℕ) :
    Function.support (tentFun a b n) ⊆ Set.Icc a b := by
  intro t ht
  by_contra h
  rw [Set.mem_Icc, not_and_or, not_le, not_le] at h
  rcases h with h | h
  · have h1 : (n : ℝ) * (t - a) ≤ 0 :=
      mul_nonpos_of_nonneg_of_nonpos (Nat.cast_nonneg n) (by linarith)
    have h2 : min ((n : ℝ) * (t - a)) ((n : ℝ) * (b - t)) ≤ 0 := le_trans (min_le_left _ _) h1
    have h3 : min 1 (min ((n : ℝ) * (t - a)) ((n : ℝ) * (b - t))) ≤ 0 :=
      le_trans (min_le_right _ _) h2
    exact ht (max_eq_left h3)
  · have h1 : (n : ℝ) * (b - t) ≤ 0 :=
      mul_nonpos_of_nonneg_of_nonpos (Nat.cast_nonneg n) (by linarith)
    have h2 : min ((n : ℝ) * (t - a)) ((n : ℝ) * (b - t)) ≤ 0 :=
      le_trans (min_le_right _ _) h1
    have h3 : min 1 (min ((n : ℝ) * (t - a)) ((n : ℝ) * (b - t))) ≤ 0 :=
      le_trans (min_le_right _ _) h2
    exact ht (max_eq_left h3)

/-- The tent as a compactly supported continuous function. -/
def tent (a b : ℝ) (n : ℕ) : CompactlySupportedContinuousMap ℝ ℝ :=
  ⟨⟨tentFun a b n, continuous_tentFun a b n⟩,
    HasCompactSupport.of_support_subset_isCompact isCompact_Icc (support_tentFun_subset a b n)⟩

@[simp] theorem tent_apply (a b : ℝ) (n : ℕ) (t : ℝ) : tent a b n t = tentFun a b n t := rfl

/-! ## Lifting functions on `ℝ` to `SL₃(ℝ)` along the root subgroup -/

/-- Every compactly supported continuous function on `ℝ` is the restriction to `u_ij(ℝ)`
of a compactly supported continuous function on `SL₃(ℝ)`. -/
theorem exists_lift_uij {i j : Fin 3} (hij : i ≠ j)
    (f : CompactlySupportedContinuousMap ℝ ℝ) :
    ∃ G : CompactlySupportedContinuousMap SL3 ℝ,
      ∀ t : ℝ, G (uij hij t) = f t := by
  set c : SL3 → ℝ := fun g => (g : Matrix (Fin 3) (Fin 3) ℝ) i j with hc
  have hcφ : ∀ t, c (uij hij t) = t := fun t => by
    simp only [hc]; exact uij_coeff hij t
  have hcont_c : Continuous c := by simp only [hc]; exact continuous_coeff
  have hK : IsCompact ((fun t => uij hij t) '' tsupport (f : ℝ → ℝ)) :=
    f.hasCompactSupport.isCompact.image (Work.EKLC7.continuous_uij hij)
  obtain ⟨ψ, hψ1, hψc, -, hψ01⟩ :=
    exists_continuousMap_one_of_isCompact_subset_isOpen hK isOpen_univ (subset_univ _)
  have hcont : Continuous (fun g : SL3 => ψ g * f (c g)) :=
    ψ.continuous.mul (f.continuous.comp hcont_c)
  have hcs : HasCompactSupport (fun g : SL3 => ψ g * f (c g)) := by
    apply HasCompactSupport.of_support_subset_isCompact hψc
    intro g hg
    exact subset_tsupport ψ (fun h => hg (show ψ g * f (c g) = 0 by rw [h, zero_mul]))
  refine ⟨⟨⟨fun g => ψ g * f (c g), hcont⟩, hcs⟩, ?_⟩
  intro t
  change ψ (uij hij t) * f (c (uij hij t)) = f t
  rw [hcφ t]
  by_cases hft : f t = 0
  · rw [hft, mul_zero]
  · have ht : t ∈ tsupport (f : ℝ → ℝ) := subset_tsupport _ hft
    have hmem : uij hij t ∈ (fun t => uij hij t) '' tsupport (f : ℝ → ℝ) := ⟨t, ht, rfl⟩
    rw [hψ1 hmem, Pi.one_apply, one_mul]

end

end Work.EKLRelCross
