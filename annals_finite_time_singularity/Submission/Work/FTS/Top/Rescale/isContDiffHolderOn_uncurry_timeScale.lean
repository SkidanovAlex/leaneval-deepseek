import Mathlib.Analysis.Calculus.ContDiff.Defs
import Mathlib.Analysis.InnerProductSpace.PiL2
import Mathlib.Topology.MetricSpace.Holder
import Submission.Work.FTS.Top.Rescale.Defs
import Submission.Work.FTS.Top.Rescale.CompCLM.Base

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

open Set Filter
open scoped Topology ENNReal

namespace Work.FTS.Top.Rescale

/-!
# The strip `C^{1,α}` class is preserved by the time rescaling

`(timeScale c u).uncurry z = c • u.uncurry (timeCLM c z)` for `z : R3 × ℝ`, where
`timeCLM c (x,t) = (x, c*t)` is a continuous linear map.  So the target below is a special case of
the generic reparametrisation lemma `isContDiffHolderOn_comp_clm` proved in this file:
`IsContDiffHolderOn` is stable under postcomposition with a continuous linear map `A` on the values
and precomposition with a continuous linear map `Φ` on the variables carrying the new set `s` into
the old set `t`.

The four blocks of the original route are:

* `contDiffOn_comp_clm` (in `CompCLM.Base`) — the `C¹` block, `ContDiffOn.comp` with the smooth `Φ`
  followed by `ContDiffOn` of the continuous linear map `A`;
* `fderivWithin_comp_clm` (in `CompCLM.Base`) — the within-derivative formula
  `fderivWithin ℝ (fun z => A (g (Φ z))) s z = A ∘L (fderivWithin ℝ g t (Φ z) ∘L Φ)`, obtained
  from the within chain rule (`HasFDerivWithinAt.comp`, twice) together with
  `HasFDerivWithinAt.fderivWithin`; the hypothesis "`s` is uniquely differentiable within at each
  of its points" (`huniq`) is exactly what pins the within-derivative down;
* `isBoundedFunOn_fderivWithin_comp_clm` (below) — the boundedness block, from
  `‖A ∘L (D ∘L Φ)‖ ≤ ‖A‖ * ‖D‖ * ‖Φ‖` and the boundedness of `fderivWithin ℝ g t` on `t`;
* `holderOn_fderivWithin_comp_clm` (below) — the Hölder block, from
  `dist (Φ z) (Φ w) ≤ ‖Φ‖ * dist z w` and the Hölder bound for that derivative, with the exponent
  `α`.

Nothing from `Submission.Work.SolutionDelivery.*` is imported.
-/

/-- **From the norm form to `HolderOnWith`.**  The Hölder block below produces a norm inequality;
`HolderOn` is defined through `HolderOnWith`, which is stated in `edist` coordinates.  Since `edist`
on a (pseudo)metric space is `ENNReal.ofReal` of the distance, this is `ENNReal.ofReal` applied to
the hypothesis, together with `ENNReal.ofReal_mul` and `ENNReal.ofReal_rpow_of_nonneg`. -/
theorem holderOnWith_of_norm_le {X Y : Type*} [PseudoMetricSpace X] [NormedAddCommGroup Y]
    {C r : NNReal} {f : X → Y} {s : Set X}
    (h : ∀ x ∈ s, ∀ y ∈ s, ‖f x - f y‖ ≤ (C : ℝ) * dist x y ^ (r : ℝ)) :
    HolderOnWith C r f s := by
  intro x hx y hy
  rw [edist_dist, edist_dist, dist_eq_norm]
  calc ENNReal.ofReal ‖f x - f y‖
      ≤ ENNReal.ofReal ((C : ℝ) * dist x y ^ (r : ℝ)) := ENNReal.ofReal_le_ofReal (h x hx y hy)
    _ = ENNReal.ofReal (C : ℝ) * ENNReal.ofReal (dist x y ^ (r : ℝ)) :=
        ENNReal.ofReal_mul (by positivity)
    _ = ↑C * ENNReal.ofReal (dist x y) ^ (r : ℝ) := by
        rw [ENNReal.ofReal_rpow_of_nonneg dist_nonneg (by positivity), ENNReal.ofReal_coe_nnreal]

/-- **The boundedness block.**  If `fderivWithin ℝ g t` is bounded on `t`, then the
within-derivative of `z ↦ A (g (Φ z))` is bounded on `s`.

Indeed, on `s` that derivative is `A ∘L (D (Φ z) ∘L Φ)` with `‖D (Φ z)‖ ≤ R'`, so it is bounded by
`2 * (‖A‖ * R' * ‖Φ‖)`. -/
theorem isBoundedFunOn_fderivWithin_comp_clm {s t : Set (R3 × ℝ)}
    {g : R3 × ℝ → R3}
    (A : R3 →L[ℝ] R3)
    (Φ : (R3 × ℝ) →L[ℝ] (R3 × ℝ))
    (hΦ : MapsTo Φ s t) (huniq : ∀ z ∈ s, UniqueDiffWithinAt ℝ s z)
    (hg : DifferentiableOn ℝ g t)
    (hbdd : IsBoundedFunOn (fderivWithin ℝ g t) t) :
    IsBoundedFunOn (fderivWithin ℝ (fun z => A (g (Φ z))) s) s := by
  obtain ⟨R, hR⟩ :=
    (Metric.isBounded_iff_subset_closedBall (0 : (R3 × ℝ) →L[ℝ] R3)).1 hbdd
  set R' := max R 0 with hR'def
  have hR'0 : 0 ≤ R' := le_max_right _ _
  refine (Metric.isBounded_iff_subset_closedBall (0 : (R3 × ℝ) →L[ℝ] R3)).2
    ⟨2 * (‖A‖ * R' * ‖Φ‖), ?_⟩
  rintro x ⟨z, hz, rfl⟩
  have hD : ‖fderivWithin ℝ g t (Φ z)‖ ≤ R' := by
    have hmem := hR ⟨Φ z, hΦ hz, rfl⟩
    rw [Metric.mem_closedBall, dist_eq_norm, sub_zero] at hmem
    exact le_trans hmem (le_max_left _ _)
  rw [Metric.mem_closedBall, dist_eq_norm, sub_zero,
    fderivWithin_comp_clm A Φ hΦ huniq hg z hz]
  have hstep : ‖A ∘L (fderivWithin ℝ g t (Φ z) ∘L Φ)‖ ≤ ‖A‖ * R' * ‖Φ‖ := by
    calc ‖A ∘L (fderivWithin ℝ g t (Φ z) ∘L Φ)‖
        ≤ ‖A‖ * ‖fderivWithin ℝ g t (Φ z) ∘L Φ‖ := ContinuousLinearMap.opNorm_comp_le A _
      _ ≤ ‖A‖ * (‖fderivWithin ℝ g t (Φ z)‖ * ‖Φ‖) :=
          mul_le_mul_of_nonneg_left (ContinuousLinearMap.opNorm_comp_le _ Φ) (norm_nonneg _)
      _ ≤ ‖A‖ * (R' * ‖Φ‖) :=
          mul_le_mul_of_nonneg_left (mul_le_mul_of_nonneg_right hD (norm_nonneg _)) (norm_nonneg _)
      _ = ‖A‖ * R' * ‖Φ‖ := by ring
  have hnn : 0 ≤ ‖A‖ * R' * ‖Φ‖ :=
    mul_nonneg (mul_nonneg (norm_nonneg _) hR'0) (norm_nonneg _)
  linarith [hstep, hnn]

/-- **The Hölder block.**  If the within-derivative of `g` is `α`-Hölder on `t`, then so is the
within-derivative of `z ↦ A (g (Φ z))` on `s`, with constant `‖A‖ * ‖Φ‖ * C * ‖Φ‖ ^ α`. -/
theorem holderOn_fderivWithin_comp_clm {α : NNReal} {s t : Set (R3 × ℝ)}
    {g : R3 × ℝ → R3}
    (A : R3 →L[ℝ] R3)
    (Φ : (R3 × ℝ) →L[ℝ] (R3 × ℝ))
    (hΦ : MapsTo Φ s t) (huniq : ∀ z ∈ s, UniqueDiffWithinAt ℝ s z)
    (hg : DifferentiableOn ℝ g t)
    (hholder : HolderOn α (fderivWithin ℝ g t) t) :
    HolderOn α (fderivWithin ℝ (fun z => A (g (Φ z))) s) s := by
  obtain ⟨C, hC⟩ := hholder
  refine ⟨Real.toNNReal (‖A‖ * ‖Φ‖ * (C : ℝ) * ‖Φ‖ ^ (α : ℝ)), ?_⟩
  apply holderOnWith_of_norm_le
  intro x hx y hy
  rw [Real.coe_toNNReal _ (by positivity)]
  rw [fderivWithin_comp_clm A Φ hΦ huniq hg x hx, fderivWithin_comp_clm A Φ hΦ huniq hg y hy]
  set X := fderivWithin ℝ g t (Φ x) with hX
  set Y := fderivWithin ℝ g t (Φ y) with hY
  have hbound : ‖X - Y‖ ≤ (C : ℝ) * dist (Φ x) (Φ y) ^ (α : ℝ) := by
    have h := norm_le_of_holderOnWith hC (Φ x) (hΦ hx) (Φ y) (hΦ hy)
    rwa [← hX, ← hY] at h
  have hdist : dist (Φ x) (Φ y) ≤ ‖Φ‖ * dist x y := by
    rw [dist_eq_norm, dist_eq_norm]
    calc ‖Φ x - Φ y‖ = ‖Φ (x - y)‖ := by rw [map_sub]
      _ ≤ ‖Φ‖ * ‖x - y‖ := ContinuousLinearMap.le_opNorm Φ (x - y)
  have hdistα : dist (Φ x) (Φ y) ^ (α : ℝ) ≤ ‖Φ‖ ^ (α : ℝ) * dist x y ^ (α : ℝ) := by
    calc dist (Φ x) (Φ y) ^ (α : ℝ)
        ≤ (‖Φ‖ * dist x y) ^ (α : ℝ) := Real.rpow_le_rpow dist_nonneg hdist (by positivity)
      _ = ‖Φ‖ ^ (α : ℝ) * dist x y ^ (α : ℝ) := Real.mul_rpow (norm_nonneg _) dist_nonneg
  have hsub : A ∘L X ∘L Φ - A ∘L Y ∘L Φ = A ∘L (X - Y) ∘L Φ := by
    apply ContinuousLinearMap.ext
    intro v
    simp
  rw [hsub]
  calc ‖A ∘L (X - Y) ∘L Φ‖
      ≤ ‖A ∘L (X - Y)‖ * ‖Φ‖ := ContinuousLinearMap.opNorm_comp_le (A ∘L (X - Y)) Φ
    _ ≤ (‖A‖ * ‖X - Y‖) * ‖Φ‖ :=
        mul_le_mul_of_nonneg_right (ContinuousLinearMap.opNorm_comp_le A (X - Y)) (norm_nonneg _)
    _ ≤ (‖A‖ * ((C : ℝ) * dist (Φ x) (Φ y) ^ (α : ℝ))) * ‖Φ‖ :=
        mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_left hbound (norm_nonneg _)) (norm_nonneg _)
    _ ≤ (‖A‖ * ((C : ℝ) * (‖Φ‖ ^ (α : ℝ) * dist x y ^ (α : ℝ)))) * ‖Φ‖ :=
        mul_le_mul_of_nonneg_right
          (mul_le_mul_of_nonneg_left (mul_le_mul_of_nonneg_left hdistα C.coe_nonneg) (norm_nonneg _))
          (norm_nonneg _)
    _ = (‖A‖ * ‖Φ‖ * (C : ℝ) * ‖Φ‖ ^ (α : ℝ)) * dist x y ^ (α : ℝ) := by ring

/-- **The reparametrisation lemma**: `IsContDiffHolderOn` is stable under postcomposition with a
continuous linear map `A` and precomposition with a continuous linear map `Φ` carrying `s` into
`t`. -/
theorem isContDiffHolderOn_comp_clm {α : NNReal} {s t : Set (R3 × ℝ)}
    {g : R3 × ℝ → R3}
    (A : R3 →L[ℝ] R3)
    (Φ : (R3 × ℝ) →L[ℝ] (R3 × ℝ))
    (hΦ : MapsTo Φ s t) (huniq : ∀ z ∈ s, UniqueDiffWithinAt ℝ s z)
    (h : IsContDiffHolderOn ℝ α g t) :
    IsContDiffHolderOn ℝ α (fun z => A (g (Φ z))) s :=
  ⟨contDiffOn_comp_clm A Φ hΦ h.1,
   isBoundedFunOn_fderivWithin_comp_clm A Φ hΦ huniq (h.1.differentiableOn (by norm_num)) h.2.1,
   holderOn_fderivWithin_comp_clm A Φ hΦ huniq (h.1.differentiableOn (by norm_num)) h.2.2⟩

/-
The strip `C^{1,α}` class is preserved by the time rescaling.

`(timeScale c u).uncurry z = c • u.uncurry (timeCLM c z)` for `z : R3 × ℝ`, where
`timeCLM c (x,t) = (x, c*t)` is a continuous linear map (`Work.FTS.Top.timeCLM`; the identity is
`Work.FTS.Top.timeScale_uncurry`).  So this is a reparametrisation result for `IsContDiffHolderOn`.

IMPORTANT: prove it self-containedly in this file.  Do NOT import `Submission.Work.SolutionDelivery.*`
(that subtree is on the lead's drop list and is not a supported dependency); you may read
`Submission/Work/SolutionDelivery/Scaling/isContDiffHolderOn_rescale.lean` for technique only.

Structure of the proof:

* the `C¹` block: `ContDiffOn.comp` with the smooth `timeCLM c`, then `ContDiffOn.const_smul`;
* for `s` uniquely differentiable within at each of its points, the within chain rule gives, for
  `z ∈ s`, `fderivWithin ℝ (fun z => A (g (Φ z))) s z = A ∘L (fderivWithin ℝ g t (Φ z) ∘L Φ)` for
  `A = smulCLM c` and `Φ = timeCLM c` (use `HasFDerivWithinAt.comp` twice, then
  `HasFDerivWithinAt.fderivWithin`);
* boundedness block: `‖A ∘L (D ∘L Φ)‖ ≤ ‖A‖ * ‖D‖ * ‖Φ‖` and boundedness of `fderivWithin ℝ g t`
  on `t`; Holder block: `dist (Φ z) (Φ w) ≤ ‖Φ‖ * dist z w` and the Holder bound for that
  derivative, with the exponent `α`.

Useful: `ContinuousLinearMap.contDiff`, `ContinuousLinearMap.opNorm_comp_le`,
`ContinuousLinearMap.le_opNorm`, `Real.mul_rpow`, `Real.rpow_le_rpow`, `dist_nonneg`,
`ContinuousLinearMap.norm_smul_le`.  The statement holds for every `c`, including `c = 0`
(where `timeScale 0 u = 0`).  Namespace `Work.FTS.Top`.
-/
theorem isContDiffHolderOn_uncurry_timeScale {α : NNReal} {c : ℝ}
    {s t : Set (Work.FTS.Top.R3 × ℝ)} {u : Work.FTS.Top.R3 → ℝ → Work.FTS.Top.R3}
    (hΦ : Set.MapsTo (Work.FTS.Top.timeCLM c) s t)
    (huniq : ∀ z ∈ s, UniqueDiffWithinAt ℝ s z)
    (h : IsContDiffHolderOn ℝ α u.uncurry t) :
    IsContDiffHolderOn ℝ α (Work.FTS.Top.timeScale c u).uncurry s := by
  have hmain := isContDiffHolderOn_comp_clm (Work.FTS.Top.smulCLM c) (Work.FTS.Top.timeCLM c)
    hΦ huniq h
  simpa only [Work.FTS.Top.timeScale_uncurry] using hmain

end Work.FTS.Top.Rescale
