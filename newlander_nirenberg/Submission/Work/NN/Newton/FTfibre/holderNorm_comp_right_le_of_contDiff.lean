/-
Copyright: none.  Part of the `Newlander-Nirenberg` formalisation project.

# The `C^{k,α}` norm of `u ∘ Φ` over an arbitrary domain, in terms of `u` on a neighbourhood

Let `Φ : E →L[ℝ] F` be a continuous linear map and `u : F → ℂ` a globally `C^k` function.
The target lemma bounds the `C^{k,α}` norm of `z ↦ u (Φ z)` over a set `Ω ⊆ E` (open, in the
sense of the hypothesis `hΩ : ∀ x ∈ Ω, Ω ∈ nhds x`) by the `C^{k,α}` norm of `u` over any set
`t ⊆ F` that is a neighbourhood of `Φ x` for every `x ∈ Ω`, with constant
`max 1 (‖Φ‖ ^ (k + α))`.

The proof is a reduction to the "open set" situation, where the previously established
right-composition estimates (`Work.NN.Final.iterDerivNorm_comp_right_le` and
`Work.NN.Newton.FTfibre.holderSeminorm_comp_right_le_of_nonneg`) apply verbatim:

* `hΩ` says exactly that `Ω` is open, and `ht` says that `Φ x ∈ interior t` for `x ∈ Ω`, so
  `Ω ⊆ Φ ⁻¹' interior t` and both are open; `Work.CR.Flat.holderNorm_mono_set` moves the norm
  from `Ω` up to `Φ ⁻¹' interior t`;
* `Work.NN.Final.holderNorm_le_of_subset_interior` moves the norm of `u` down from `t` to
  `interior t` (at a point of the interior, both within-derivatives agree with the global one);
* on `Φ ⁻¹' interior t` the chain rule of `Work.NN.Final.holderNorm_comp_linear` gives, for each
  `i ≤ k`, the factors `‖Φ‖ ^ i` for the `i`-th derivative and `‖Φ‖ ^ (i + α)` for its Hölder
  seminorm, both bounded by `max 1 (‖Φ‖ ^ (k + α))` since `α ≥ 0`.

The Hölder-seminorm half of the estimate is only available in the literature form
`Work.NN.Final.holderSeminorm_comp_right_le` for `0 < α`; the case `α = 0` needed here (where the
Hölder denominator is `1`, so no strict positivity of the exponent is available) is supplied by
`Work.NN.Newton.FTfibre.holderSeminorm_comp_right_le_of_nonneg`, proved separately.
-/
import Mathlib
import Submission.Work.CR.Flat.Holder
import Submission.Work.NN.Final.holderNorm_comp_linear
import Submission.Work.NN.Final.holderNorm_le_of_subset_interior
import Submission.Work.NN.Newton.FTfibre.holderSeminorm_comp_right_le_of_nonneg

noncomputable section

open scoped NNReal ENNReal
open Set

namespace Work.NN.Newton.FTfibre

theorem holderNorm_comp_right_le_of_contDiff
    {E F : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    [NormedAddCommGroup F] [NormedSpace ℝ F]
    (Φ : E →L[ℝ] F) (k : ℕ) {α : ℝ} (hα : 0 ≤ α) {u : F → ℂ} (hu : ContDiff ℝ k u)
    {Ω : Set E} {t : Set F} (hΩ : ∀ x ∈ Ω, Ω ∈ nhds x) (ht : ∀ x ∈ Ω, t ∈ nhds (Φ x)) :
    Work.CR.Flat.holderNorm k α (fun z => u (Φ z)) Ω
      ≤ ENNReal.ofReal (max 1 (‖Φ‖ ^ ((k : ℝ) + α))) * Work.CR.Flat.holderNorm k α u t := by
  have hΩopen : IsOpen Ω := isOpen_iff_mem_nhds.mpr hΩ
  have hsopen : IsOpen (interior t) := isOpen_interior
  have hpre : IsOpen (Φ ⁻¹' interior t) := hsopen.preimage Φ.continuous
  have hsub : Ω ⊆ Φ ⁻¹' interior t := fun x hx => mem_interior_iff_mem_nhds.mpr (ht x hx)
  -- move the left-hand norm up to `Φ ⁻¹' interior t`, and the right-hand norm down to
  -- `interior t`
  have hmono : Work.CR.Flat.holderNorm k α (fun z => u (Φ z)) Ω
      ≤ Work.CR.Flat.holderNorm k α (fun z => u (Φ z)) (Φ ⁻¹' interior t) :=
    Work.CR.Flat.holderNorm_mono_set hpre hΩopen hsub k α _
  have hL1 : Work.CR.Flat.holderNorm k α u (interior t) ≤ Work.CR.Flat.holderNorm k α u t :=
    Work.NN.Final.holderNorm_le_of_subset_interior isOpen_interior Subset.rfl k α u
  refine le_trans hmono (le_trans ?_ (mul_le_mul_of_nonneg_left hL1 bot_le))
  -- now bound term by term on the open set `interior t`
  rw [Work.CR.Flat.holderNorm, Work.CR.Flat.holderNorm, Finset.mul_sum]
  refine Finset.sum_le_sum fun i hi => ?_
  have hik : i ≤ k := Nat.lt_succ_iff.mp (Finset.mem_range.mp hi)
  have hik' : (i : WithTop ℕ∞) ≤ (k : WithTop ℕ∞) := by exact_mod_cast hik
  have hfac1 : ENNReal.ofReal (‖Φ‖ ^ i) ≤ ENNReal.ofReal (max 1 (‖Φ‖ ^ ((k : ℝ) + α))) :=
    ENNReal.ofReal_le_ofReal (Work.NN.Final.rpow_nat_pow_le_max (norm_nonneg Φ) hα hik)
  have hfac2 : ENNReal.ofReal (‖Φ‖ ^ ((i : ℝ) + α))
      ≤ ENNReal.ofReal (max 1 (‖Φ‖ ^ ((k : ℝ) + α))) :=
    ENNReal.ofReal_le_ofReal (Work.NN.Final.rpow_add_le_max (norm_nonneg Φ) hα hik)
  rw [mul_add]
  refine add_le_add ?_ ?_
  · exact le_trans
      (Work.NN.Final.iterDerivNorm_comp_right_le Φ i (k : WithTop ℕ∞) hu.contDiffOn
        isOpen_interior.uniqueDiffOn hpre.uniqueDiffOn hik')
      (mul_le_mul_left hfac1 _)
  · exact le_trans
      (holderSeminorm_comp_right_le_of_nonneg Φ i (k : WithTop ℕ∞) hα hu.contDiffOn
        isOpen_interior.uniqueDiffOn hpre.uniqueDiffOn hik')
      (mul_le_mul_left hfac2 _)

end Work.NN.Newton.FTfibre
