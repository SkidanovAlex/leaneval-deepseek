import Mathlib
import Submission.Work.EKLC6Core.coboundary_integral

/-!
# `EKLC6Core.lintegral_ofReal_sub_comp_le`

One-sided "mean zero" of a coboundary `u ∘ T - u` for a potential `u` that need not be
integrable: `∫⁻ ofReal (u x - u (T x)) ≤ ∫⁻ ofReal (u (T x) - u x)` for every measure preserving
`T` on a probability space.

The proof clips `u` to `[-N, N]`; the clipped coboundary `u_N ∘ T - u_N` is bounded, hence
integrable, and has integral `0` by measure preservation, so its positive part and the positive
part of its negative have equal integrals.  Since `u_N (T x) - u_N x ≤ (u (T x) - u x)⁺`, this
bounds each term of the approximating family by `∫⁻ ofReal (u (T x) - u x)`; Fatou's lemma then
transfers the bound to the limit.
-/

open MeasureTheory Filter
open scoped ENNReal Topology

set_option linter.unusedVariables false

namespace Work.EKLC6Core

/-- `ekTrunc M` is monotone. -/
private lemma ekTrunc_mono (M : ℝ) : Monotone (ekTrunc M) := by
  intro a b hab
  simp only [ekTrunc]
  exact max_le_max le_rfl (min_le_min le_rfl hab)

/-- The difference of two clips is at most the positive part of the difference. -/
private lemma ekTrunc_sub_le_max (M t s : ℝ) : ekTrunc M t - ekTrunc M s ≤ max (t - s) 0 := by
  by_cases h : t ≤ s
  · have h1 : ekTrunc M t ≤ ekTrunc M s := ekTrunc_mono M h
    have h2 : max (t - s) 0 = 0 := max_eq_right (by linarith)
    linarith
  · have ht : s < t := not_le.mp h
    have h2 : max (t - s) 0 = t - s := max_eq_left (by linarith)
    have h3 : |t - s| = t - s := abs_of_nonneg (by linarith)
    have h4 : ekTrunc M t - ekTrunc M s ≤ |t - s| := (abs_le.mp (ekTrunc_abs_lipschitz M t s)).2
    linarith

/-- The positive part of a real number minus the positive part of its negative is the number. -/
private lemma max_sub_max_neg (a : ℝ) : max a 0 - max (-a) 0 = a := by
  rcases le_total 0 a with h | h
  · rw [max_eq_left h, max_eq_right (by linarith)]; ring
  · rw [max_eq_right h, max_eq_left (by linarith)]; ring

/-- One-sided "mean zero" of a coboundary for a possibly *non-integrable* potential `u`.

Let `T` be measure preserving on a probability space `(X, μ)` and `u : X → ℝ` measurable.
If the positive part of the forward increment is integrable
(`∫⁻ x, ENNReal.ofReal (u (T x) - u x) ∂μ < ⊤`) then the backward increment has no larger
lintegral: `∫⁻ x, ofReal (u x - u (T x)) ≤ ∫⁻ x, ofReal (u (T x) - u x)`.

Suggested proof: put `g := fun x => u (T x) - u x`.  Fix `N : ℕ` and set
`u_N := fun x => ekTrunc N (u x)` (`ekTrunc` and `ekTrunc_abs_lipschitz` are in
`Submission.Work.EKLC6Core.coboundary_integral`; or define your own `clamp`).
Key pointwise inequality (provable by `max_sub_max_le_max`): for all reals `a b`,
`ekTrunc N a - ekTrunc N b ≤ max (a - b) 0`.  Hence `(u_N (T x) - u_N x) ≤ max (g x) 0` and
also `(u_N x - u_N (T x)) ≤ max (-g x) 0`.  Since `u_N` is bounded and measurable it is
integrable on the probability space, `∫ u_N (T ·) = ∫ u_N` (use `integral_map` with `hT.map_eq`,
as in `coboundary_integral`), so `∫ (u_N (T ·) - u_N) = 0`, giving
`∫ (u_N (T ·) - u_N)⁺ = ∫ (u_N - u_N (T ·))⁺`.
Then `∫⁻ x, ofReal (u_N (T x) - u_N x) → ∫⁻ x, ofReal (u (T x) - u x)` by
`tendsto_lintegral_of_dominated_convergence` with bound `fun x => ENNReal.ofReal (u (T x) - u x)`
(finite lintegral is the hypothesis), and Fatou (`lintegral_liminf_le'`) applied to
`fun N x => ENNReal.ofReal ((u_N x - u_N (T x))⁺)` finishes. -/
theorem lintegral_ofReal_sub_comp_le {X : Type*} [MeasurableSpace X]
    {μ : MeasureTheory.Measure X} [MeasureTheory.IsProbabilityMeasure μ] {T : X → X}
    (hT : MeasureTheory.MeasurePreserving T μ μ) {u : X → ℝ} (hu : Measurable u)
    (hfin : ∫⁻ x, ENNReal.ofReal (u (T x) - u x) ∂μ < ⊤) :
    ∫⁻ x, ENNReal.ofReal (u x - u (T x)) ∂μ ≤
      ∫⁻ x, ENNReal.ofReal (u (T x) - u x) ∂μ := by
  classical
  -- The truncations of `u` along the orbit converge pointwise to `u`.
  have htrunc_tendsto : ∀ y : X, Tendsto (fun N : ℕ => ekTrunc (N : ℝ) (u y)) atTop (𝓝 (u y)) := by
    intro y
    have hev : (fun N : ℕ => ekTrunc (N : ℝ) (u y)) =ᶠ[atTop] (fun _ => u y) := by
      obtain ⟨N₀, hN₀⟩ := exists_nat_gt |u y|
      filter_upwards [eventually_ge_atTop N₀] with N hN
      have hNy : |u y| ≤ (N : ℝ) := le_trans (le_of_lt hN₀) (by exact_mod_cast hN)
      show max (-(N : ℝ)) (min (N : ℝ) (u y)) = u y
      rw [min_eq_right (le_trans (le_abs_self (u y)) hNy),
        max_eq_right (le_trans (neg_le_neg hNy) (neg_abs_le (u y)))]
    exact Tendsto.congr' hev.symm tendsto_const_nhds
  -- The approximating family: the backward increment of the `N`-th truncation.
  set G : ℕ → X → ℝ≥0∞ :=
    fun N x => ENNReal.ofReal (max (ekTrunc (N : ℝ) (u x) - ekTrunc (N : ℝ) (u (T x))) 0)
    with hG
  -- Each term of the family is bounded by the lintegral of the forward increment.
  have key : ∀ N : ℕ, ∫⁻ x, G N x ∂μ ≤ ∫⁻ x, ENNReal.ofReal (u (T x) - u x) ∂μ := by
    intro N
    simp only [hG]
    have hv_meas : Measurable (fun x : X => ekTrunc (N : ℝ) (u x)) :=
      (ekTrunc_cont _).measurable.comp hu
    have hw_meas : Measurable (fun x : X => ekTrunc (N : ℝ) (u (T x))) :=
      (ekTrunc_cont _).measurable.comp (hu.comp hT.measurable)
    have hv_int : Integrable (fun x : X => ekTrunc (N : ℝ) (u x)) μ :=
      Integrable.of_bound hv_meas.aestronglyMeasurable (N : ℝ)
        (ae_of_all _ (fun x => by
          rw [Real.norm_eq_abs]
          exact ekTrunc_abs_le _ (Nat.cast_nonneg N) (u x)))
    have hw_int : Integrable (fun x : X => ekTrunc (N : ℝ) (u (T x))) μ :=
      Integrable.of_bound hw_meas.aestronglyMeasurable (N : ℝ)
        (ae_of_all _ (fun x => by
          rw [Real.norm_eq_abs]
          exact ekTrunc_abs_le _ (Nat.cast_nonneg N) (u (T x))))
    -- The clipped coboundaries have integral `0`.
    have hcomp : ∫ x, ekTrunc (N : ℝ) (u (T x)) ∂μ = ∫ x, ekTrunc (N : ℝ) (u x) ∂μ := by
      have h1 : ∫ y, ekTrunc (N : ℝ) (u y) ∂(Measure.map T μ)
          = ∫ x, ekTrunc (N : ℝ) (u (T x)) ∂μ :=
        integral_map hT.aemeasurable (by rw [hT.map_eq]; exact hv_meas.aestronglyMeasurable)
      rw [← h1, hT.map_eq]
    set F : X → ℝ := fun x => ekTrunc (N : ℝ) (u (T x)) - ekTrunc (N : ℝ) (u x) with hF
    have hF_int : Integrable F μ := by rw [hF]; exact hw_int.sub hv_int
    have hF_zero : ∫ x, F x ∂μ = 0 := by
      rw [hF, integral_sub hw_int hv_int, hcomp, sub_self]
    -- Hence the positive parts of `F` and of `-F` have equal integrals.
    have hsplit : ∫ x, max (F x) 0 ∂μ = ∫ x, max (-F x) 0 ∂μ := by
      have h1 : ∫ x, max (F x) 0 ∂μ - ∫ x, max (-F x) 0 ∂μ
          = ∫ x, (max (F x) 0 - max (-F x) 0) ∂μ :=
        (integral_sub hF_int.pos_part hF_int.neg_part).symm
      have h3 : ∫ x, (max (F x) 0 - max (-F x) 0) ∂μ = ∫ x, F x ∂μ := by
        apply integral_congr_ae
        filter_upwards with x
        exact max_sub_max_neg (F x)
      linarith
    have hFpos_int : Integrable (fun x => max (F x) 0) μ := hF_int.pos_part
    have hFneg_int : Integrable (fun x => max (-F x) 0) μ := hF_int.neg_part
    have hFpos_nn : 0 ≤ᵐ[μ] (fun x => max (F x) 0) := ae_of_all _ (fun x => le_max_right _ _)
    have hFneg_nn : 0 ≤ᵐ[μ] (fun x => max (-F x) 0) := ae_of_all _ (fun x => le_max_right _ _)
    -- Pointwise comparison with the (positive part of the) forward increment.
    have hdom : ∀ x, max (F x) 0 ≤ max (u (T x) - u x) 0 := by
      intro x
      have h := ekTrunc_sub_le_max (N : ℝ) (u (T x)) (u x)
      exact max_le h (le_max_right _ _)
    calc ∫⁻ x, ENNReal.ofReal (max (ekTrunc (N : ℝ) (u x) - ekTrunc (N : ℝ) (u (T x))) 0) ∂μ
        = ∫⁻ x, ENNReal.ofReal (max (-F x) 0) ∂μ := by
          apply lintegral_congr
          intro x
          have hneg : -F x = ekTrunc (N : ℝ) (u x) - ekTrunc (N : ℝ) (u (T x)) := by
            simp only [hF]; ring
          rw [hneg]
      _ = ENNReal.ofReal (∫ x, max (-F x) 0 ∂μ) :=
          (ofReal_integral_eq_lintegral_ofReal hFneg_int hFneg_nn).symm
      _ = ENNReal.ofReal (∫ x, max (F x) 0 ∂μ) := congrArg ENNReal.ofReal hsplit.symm
      _ = ∫⁻ x, ENNReal.ofReal (max (F x) 0) ∂μ :=
          ofReal_integral_eq_lintegral_ofReal hFpos_int hFpos_nn
      _ ≤ ∫⁻ x, ENNReal.ofReal (max (u (T x) - u x) 0) ∂μ :=
          lintegral_mono (fun x => ENNReal.ofReal_le_ofReal (hdom x))
      _ = ∫⁻ x, ENNReal.ofReal (u (T x) - u x) ∂μ := by
          apply lintegral_congr
          intro x
          rw [ENNReal.ofReal_max]
          simp
  have hG_meas : ∀ N, AEMeasurable (G N) μ := by
    intro N
    have h1 : Measurable (fun x : X => ekTrunc (N : ℝ) (u x)) :=
      (ekTrunc_cont _).measurable.comp hu
    have h2 : Measurable (fun x : X => ekTrunc (N : ℝ) (u (T x))) :=
      (ekTrunc_cont _).measurable.comp (hu.comp hT.measurable)
    exact (ENNReal.continuous_ofReal.measurable.comp
      ((h1.sub h2).max measurable_const)).aemeasurable
  -- Fatou's lemma.
  have hfatou : ∫⁻ x, Filter.liminf (fun N => G N x) atTop ∂μ
      ≤ Filter.liminf (fun N : ℕ => ∫⁻ x, G N x ∂μ) atTop :=
    lintegral_liminf_le' hG_meas
  have hlim : ∀ᵐ x ∂μ,
      Filter.liminf (fun N => G N x) atTop = ENNReal.ofReal (max (u x - u (T x)) 0) := by
    refine Filter.Eventually.of_forall (fun x => ?_)
    have h1 : Tendsto (fun N : ℕ => ekTrunc (N : ℝ) (u x) - ekTrunc (N : ℝ) (u (T x))) atTop
        (𝓝 (u x - u (T x))) := (htrunc_tendsto x).sub (htrunc_tendsto (T x))
    have h2 : Continuous (fun r : ℝ => ENNReal.ofReal (max r 0)) :=
      ENNReal.continuous_ofReal.comp (continuous_id.max continuous_const)
    have h3 : Tendsto (fun N : ℕ =>
        ENNReal.ofReal (max (ekTrunc (N : ℝ) (u x) - ekTrunc (N : ℝ) (u (T x))) 0))
        atTop (𝓝 (ENNReal.ofReal (max (u x - u (T x)) 0))) :=
      (h2.tendsto _).comp h1
    have h4 : Tendsto (fun N => G N x) atTop
        (𝓝 (ENNReal.ofReal (max (u x - u (T x)) 0))) := by
      simpa only [hG] using h3
    exact h4.liminf_eq
  have hliminf_le : Filter.liminf (fun N : ℕ => ∫⁻ x, G N x ∂μ) atTop
      ≤ ∫⁻ x, ENNReal.ofReal (u (T x) - u x) ∂μ := by
    refine Filter.liminf_le_of_le ⟨0, Filter.Eventually.of_forall (fun _ => zero_le)⟩ ?_
    intro b hb
    obtain ⟨N, hN⟩ := hb.exists
    exact le_trans hN (key N)
  calc ∫⁻ x, ENNReal.ofReal (u x - u (T x)) ∂μ
      = ∫⁻ x, ENNReal.ofReal (max (u x - u (T x)) 0) ∂μ := by
        apply lintegral_congr
        intro x
        rw [ENNReal.ofReal_max]
        simp
    _ = ∫⁻ x, Filter.liminf (fun N => G N x) atTop ∂μ := (lintegral_congr_ae hlim).symm
    _ ≤ Filter.liminf (fun N : ℕ => ∫⁻ x, G N x ∂μ) atTop := hfatou
    _ ≤ ∫⁻ x, ENNReal.ofReal (u (T x) - u x) ∂μ := hliminf_le

end Work.EKLC6Core
