import Mathlib
import Submission.Work.BW.prod_formula_log
import Submission.Work.BW.LiouvilleAux.posLog_sub_one_infinite
import Submission.Work.BW.LiouvilleAux.posLog_sub_one_finite
import Submission.Work.BW.LiouvilleAux.posLog_hasFiniteSupport
import Submission.Work.BW.LiouvilleAux.sum_mult_erase
import Submission.Work.BW.LiouvilleAux.finsum_log_le_posLog
import Submission.Work.BW.LiouvilleAux.product_formula_isolate

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false

/-!
# The Liouville bound at a single place

This file isolates the "local" step of BW's Liouville-type estimate (BW, p. 25–26, the
estimates (4)–(7) of the proof of their Lemma 3): for `a : K` with `a ≠ 1` and an embedding
`φ : K →+* ℂ` with associated infinite place `v₀`, one has

  `mult(v₀) · log |φ (a-1)| ≥ -(h(a) + (d - mult(v₀)) · log 2)`,  `d = [K : ℚ]`.

The proof is the standard one: the logarithmic product formula expresses the term at `v₀`
as minus the contributions of all other places; each of those is bounded above by the
corresponding `log⁺`-term, which loses `log 2` at every archimedean place (and nothing at
nonarchimedean places). Summing gives `h(a-1) - mult(v₀) log⁺|a-1|_{v₀} ≤ h(a) + (d - mult v₀) log 2`.

The intermediate estimates are provided by the modules under
`Submission.Work.BW.LiouvilleAux`.
-/

namespace Work.BW

open NumberField

/-- **Local height bound for `a - 1`.** For `a ≠ 0, 1` and an infinite place `v₀`, the sum of
the (weighted) `log⁺`-contributions of `a - 1` over all places other than `v₀` is at most
`h(a) + (d - mult v₀) log 2`. This is the "step 4–6" content of BW's Lemma 3, before the
product formula is used to isolate the term at `v₀`. -/
theorem local_height_bound {K : Type*} [Field K] [NumberField K] [DecidableEq (InfinitePlace K)]
    (v₀ : InfinitePlace K) (a : K) (ha0 : a ≠ 0) (ha1 : a ≠ 1) :
    (∑ v ∈ Finset.univ.erase v₀, (v.mult : ℝ) * Real.posLog (v (a - 1))) +
      ∑ᶠ v : FinitePlace K, Real.posLog (v (a - 1)) ≤
      Height.logHeight₁ a + ((Module.finrank ℚ K : ℝ) - (v₀.mult : ℝ)) * Real.log 2 := by
  have hx1 : a - 1 ≠ 0 := sub_ne_zero.mpr ha1
  rw [NumberField.logHeight₁_eq a]
  -- Archimedean part: bound each term at a place `v ≠ v₀`.
  have hA : (∑ v ∈ Finset.univ.erase v₀, (v.mult : ℝ) * Real.posLog (v (a - 1)))
      ≤ (∑ v : InfinitePlace K, (v.mult : ℝ) * Real.posLog (v a)) +
        ((Module.finrank ℚ K : ℝ) - (v₀.mult : ℝ)) * Real.log 2 := by
    have hpt : ∀ v ∈ Finset.univ.erase v₀,
        (v.mult : ℝ) * Real.posLog (v (a - 1)) ≤
          (v.mult : ℝ) * Real.posLog (v a) + (v.mult : ℝ) * Real.log 2 := by
      intro v _
      have h := LiouvilleAux.posLog_sub_one_infinite v a
      have hm : (0:ℝ) ≤ (v.mult : ℝ) := by positivity
      have h2 := mul_le_mul_of_nonneg_left h hm
      linarith [h2]
    calc (∑ v ∈ Finset.univ.erase v₀, (v.mult : ℝ) * Real.posLog (v (a - 1)))
        ≤ ∑ v ∈ Finset.univ.erase v₀,
            ((v.mult : ℝ) * Real.posLog (v a) + (v.mult : ℝ) * Real.log 2) :=
          Finset.sum_le_sum hpt
      _ = (∑ v ∈ Finset.univ.erase v₀, (v.mult : ℝ) * Real.posLog (v a)) +
            ((Module.finrank ℚ K : ℝ) - (v₀.mult : ℝ)) * Real.log 2 := by
          rw [Finset.sum_add_distrib, ← Finset.sum_mul, LiouvilleAux.sum_mult_erase v₀]
      _ ≤ (∑ v : InfinitePlace K, (v.mult : ℝ) * Real.posLog (v a)) +
            ((Module.finrank ℚ K : ℝ) - (v₀.mult : ℝ)) * Real.log 2 := by
          have hsub : ∑ v ∈ Finset.univ.erase v₀, (v.mult : ℝ) * Real.posLog (v a)
              ≤ ∑ v : InfinitePlace K, (v.mult : ℝ) * Real.posLog (v a) :=
            Finset.sum_le_sum_of_subset_of_nonneg (Finset.erase_subset _ _)
              (fun v _ _ => mul_nonneg (Nat.cast_nonneg _) Real.posLog_nonneg)
          linarith
  -- Nonarchimedean part: no loss.
  have hB : (∑ᶠ v : FinitePlace K, Real.posLog (v (a - 1)))
      ≤ (∑ᶠ v : FinitePlace K, Real.posLog (v a)) :=
    finsum_le_finsum (LiouvilleAux.posLog_hasFiniteSupport (a - 1) hx1)
      (LiouvilleAux.posLog_hasFiniteSupport a ha0)
      (fun v => LiouvilleAux.posLog_sub_one_finite v a)
  linarith

/-- **Liouville bound at a single place.** For `a ≠ 1` in a number field `K` and `φ : K →+* ℂ`
with associated infinite place `v₀`,
`mult(v₀) · log |φ (a-1)| ≥ -(h(a) + (d - mult v₀) log 2)`, where `h = Height.logHeight₁` is
the relative logarithmic height and `d = [K : ℚ]`. -/
theorem liouville_place {K : Type*} [Field K] [NumberField K] (φ : K →+* ℂ) (a : K) (ha : a ≠ 1) :
    ((NumberField.InfinitePlace.mk φ).mult : ℝ) * Real.log ‖φ (a - 1)‖ ≥
      -(Height.logHeight₁ a +
        ((Module.finrank ℚ K : ℝ) - ((NumberField.InfinitePlace.mk φ).mult : ℝ)) * Real.log 2) := by
  classical
  rcases eq_or_ne a 0 with h0 | ha0
  · -- `a = 0`: then `φ (a - 1) = -1` and `h(0) = 0`, so the claim reduces to `mult v₀ ≤ d`.
    subst h0
    have hphi : φ (0 - 1) = -1 := by rw [zero_sub, map_neg, map_one]
    rw [hphi, norm_neg, norm_one, Real.log_one, mul_zero, Height.logHeight₁_zero]
    have hm : ((NumberField.InfinitePlace.mk φ).mult : ℝ) ≤ (Module.finrank ℚ K : ℝ) := by
      have h : (NumberField.InfinitePlace.mk φ).mult ≤ Module.finrank ℚ K := by
        rw [← InfinitePlace.sum_mult_eq]
        exact Finset.single_le_sum (fun w _ => Nat.zero_le _) (Finset.mem_univ _)
      exact_mod_cast h
    have hlog2 : (0:ℝ) ≤ Real.log 2 := Real.log_nonneg (by norm_num)
    have : (0:ℝ) ≤
        ((Module.finrank ℚ K : ℝ) - ((NumberField.InfinitePlace.mk φ).mult : ℝ)) * Real.log 2 :=
      mul_nonneg (by linarith) hlog2
    linarith
  · -- `a ≠ 0`: use the product formula to isolate the term at `v₀`, then bound the rest.
    set v₀ := NumberField.InfinitePlace.mk φ with hv₀
    have hx0 : a - 1 ≠ 0 := sub_ne_zero.mpr ha
    have hlogeq : Real.log (v₀ (a - 1)) = Real.log ‖φ (a - 1)‖ := by
      rw [hv₀, InfinitePlace.apply]
    rw [← hlogeq]
    have hiso := LiouvilleAux.product_formula_isolate v₀ hx0
    have hlb := local_height_bound v₀ a ha0 ha
    -- `log ≤ log⁺` termwise on the archimedean places `≠ v₀`.
    have hA : (∑ v ∈ Finset.univ.erase v₀, (v.mult : ℝ) * Real.log (v (a - 1)))
        ≤ ∑ v ∈ Finset.univ.erase v₀, (v.mult : ℝ) * Real.posLog (v (a - 1)) := by
      apply Finset.sum_le_sum
      intro v _
      exact mul_le_mul_of_nonneg_left (by simp [Real.posLog]) (Nat.cast_nonneg _)
    have hB := LiouvilleAux.finsum_log_le_posLog hx0
    have hAB : (∑ v ∈ Finset.univ.erase v₀, (v.mult : ℝ) * Real.log (v (a - 1))) +
        (∑ᶠ v : FinitePlace K, Real.log (v (a - 1))) ≤
        Height.logHeight₁ a + ((Module.finrank ℚ K : ℝ) - (v₀.mult : ℝ)) * Real.log 2 :=
      le_trans (add_le_add hA hB) hlb
    rw [hiso]
    linarith

end Work.BW
