import Mathlib
import Submission.Work.EKLC6Core.Basic

/-!
# `EKLC6Core.coboundary_integral`

If `φ` preserves a probability measure `μ` and `D = Ψ ∘ φ - Ψ` almost everywhere, with `D`
integrable, then `∫ D ∂μ = 0`.  The point of the lemma is that `Ψ` itself is only assumed
`AEStronglyMeasurable`, not integrable: the identity is obtained by clipping `Ψ` to `[-n,n]`
(each clipped coboundary has integral `0` by measure preservation) and applying dominated
convergence, the dominating function being `‖D‖` thanks to the `1`-Lipschitz property of the
clipping map.
-/

namespace Work.EKLC6Core

open MeasureTheory Filter
open scoped Topology

/-- Clipping a real number to the interval `[-M, M]`. -/
def ekTrunc (M : ℝ) : ℝ → ℝ := fun t => max (-M) (min M t)

lemma ekTrunc_cont (M : ℝ) : Continuous (ekTrunc M) :=
  continuous_const.max (continuous_const.min continuous_id)

/-- Clipping is `1`-Lipschitz. -/
lemma ekTrunc_abs_lipschitz (M a b : ℝ) : |ekTrunc M a - ekTrunc M b| ≤ |a - b| := by
  have h1 : |ekTrunc M a - ekTrunc M b| ≤ |min M a - min M b| := by
    have h := abs_max_sub_max_le_abs (min M a) (min M b) (-M)
    simpa [ekTrunc, max_comm] using h
  have h2 : |min M a - min M b| ≤ |a - b| := by
    have h := abs_min_sub_min_le_max a M b M
    simpa [min_comm] using h
  exact h1.trans h2

lemma ekTrunc_abs_le (M : ℝ) (hM : 0 ≤ M) (t : ℝ) : |ekTrunc M t| ≤ M :=
  abs_le.mpr ⟨le_max_left _ _, max_le (neg_le_self hM) (min_le_left _ _)⟩

theorem coboundary_integral {X : Type*} [MeasurableSpace X] {μ : MeasureTheory.Measure X}
    [MeasureTheory.IsProbabilityMeasure μ] {φ : X → X}
    (hφ : MeasureTheory.MeasurePreserving φ μ μ)
    {Ψ : X → ℝ} (hΨ : MeasureTheory.AEStronglyMeasurable Ψ μ) {D : X → ℝ}
    (hD : MeasureTheory.Integrable D μ)
    (hdec : ∀ᵐ x ∂μ, D x = Ψ (φ x) - Ψ x) :
    ∫ x, D x ∂μ = 0 := by
  -- Integrals of functions on `X` are invariant under the measure preserving map `φ`.
  have hcomp : ∀ g : X → ℝ, AEStronglyMeasurable g μ → ∫ x, g (φ x) ∂μ = ∫ x, g x ∂μ := by
    intro g hg
    have hg' : AEStronglyMeasurable g (Measure.map φ μ) := by
      rw [hφ.map_eq]; exact hg
    have h1 : ∫ y, g y ∂(Measure.map φ μ) = ∫ x, g (φ x) ∂μ :=
      integral_map hφ.aemeasurable hg'
    rw [← h1, hφ.map_eq]
  -- Truncated versions of `Ψ` are bounded, hence integrable.
  have htrunc_meas : ∀ n : ℕ, AEStronglyMeasurable (fun x => ekTrunc (n : ℝ) (Ψ x)) μ :=
    fun n => (ekTrunc_cont (n : ℝ)).comp_aestronglyMeasurable hΨ
  have htruncφ_meas : ∀ n : ℕ,
      AEStronglyMeasurable (fun x => ekTrunc (n : ℝ) (Ψ (φ x))) μ :=
    fun n => (ekTrunc_cont (n : ℝ)).comp_aestronglyMeasurable (hΨ.comp_measurePreserving hφ)
  have htrunc_int : ∀ n : ℕ, Integrable (fun x => ekTrunc (n : ℝ) (Ψ x)) μ := by
    intro n
    refine Integrable.of_bound (htrunc_meas n) (n : ℝ) ?_
    filter_upwards with x
    exact ekTrunc_abs_le (n : ℝ) (Nat.cast_nonneg n) (Ψ x)
  have htruncφ_int : ∀ n : ℕ, Integrable (fun x => ekTrunc (n : ℝ) (Ψ (φ x))) μ := by
    intro n
    refine Integrable.of_bound (htruncφ_meas n) (n : ℝ) ?_
    filter_upwards with x
    exact ekTrunc_abs_le (n : ℝ) (Nat.cast_nonneg n) (Ψ (φ x))
  -- The approximating coboundaries.
  set F : ℕ → X → ℝ :=
    fun n x => ekTrunc (n : ℝ) (Ψ (φ x)) - ekTrunc (n : ℝ) (Ψ x) with hF
  have hF_meas : ∀ n, AEStronglyMeasurable (F n) μ := by
    intro n
    show AEStronglyMeasurable
      (fun x => ekTrunc (n : ℝ) (Ψ (φ x)) - ekTrunc (n : ℝ) (Ψ x)) μ
    exact (htruncφ_meas n).sub (htrunc_meas n)
  have hF_zero : ∀ n, ∫ x, F n x ∂μ = 0 := by
    intro n
    have h1 : ∫ x, ekTrunc (n : ℝ) (Ψ (φ x)) ∂μ = ∫ x, ekTrunc (n : ℝ) (Ψ x) ∂μ :=
      hcomp (fun x => ekTrunc (n : ℝ) (Ψ x)) (htrunc_meas n)
    have h2 := integral_sub (htruncφ_int n) (htrunc_int n)
    show ∫ x, ekTrunc (n : ℝ) (Ψ (φ x)) - ekTrunc (n : ℝ) (Ψ x) ∂μ = 0
    rw [h2, h1, sub_self]
  -- Domination by `‖D‖`.
  have hbound : ∀ n : ℕ, ∀ᵐ x ∂μ, ‖F n x‖ ≤ ‖D x‖ := by
    intro n
    filter_upwards [hdec] with x hx
    simp only [Real.norm_eq_abs]
    show |ekTrunc (n : ℝ) (Ψ (φ x)) - ekTrunc (n : ℝ) (Ψ x)| ≤ |D x|
    rw [hx]
    exact ekTrunc_abs_lipschitz (n : ℝ) (Ψ (φ x)) (Ψ x)
  -- Pointwise convergence of the truncations.
  have hTendsto : ∀ y : X, Tendsto (fun n : ℕ => ekTrunc (n : ℝ) (Ψ y)) atTop (𝓝 (Ψ y)) := by
    intro y
    have hev : (fun n : ℕ => ekTrunc (n : ℝ) (Ψ y)) =ᶠ[atTop] (fun _ => Ψ y) := by
      obtain ⟨N, hN⟩ := exists_nat_gt |Ψ y|
      filter_upwards [eventually_ge_atTop N] with n hn
      have hny : |Ψ y| ≤ (n : ℝ) := le_trans (le_of_lt hN) (by exact_mod_cast hn)
      show max (-(n : ℝ)) (min (n : ℝ) (Ψ y)) = Ψ y
      rw [min_eq_right (le_trans (le_abs_self _) hny),
        max_eq_right (le_trans (neg_le_neg hny) (neg_abs_le _))]
    exact Filter.Tendsto.congr' hev.symm tendsto_const_nhds
  have hlim : ∀ᵐ x ∂μ, Tendsto (fun n => F n x) atTop (𝓝 (D x)) := by
    filter_upwards [hdec] with x hx
    rw [hx]
    exact (hTendsto (φ x)).sub (hTendsto x)
  -- Dominated convergence.
  have hDCT := tendsto_integral_of_dominated_convergence (F := F) (f := D)
    (fun x => ‖D x‖) hF_meas hD.norm hbound hlim
  have h0 : (fun n : ℕ => ∫ x, F n x ∂μ) = fun _ => (0 : ℝ) := funext hF_zero
  rw [h0] at hDCT
  exact tendsto_nhds_unique hDCT (tendsto_const_nhds (x := (0 : ℝ)))

end Work.EKLC6Core
