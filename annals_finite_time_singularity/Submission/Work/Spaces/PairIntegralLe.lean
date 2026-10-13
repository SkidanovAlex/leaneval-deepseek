import Mathlib.Algebra.Order.Star.Real
import Mathlib.MeasureTheory.Integral.Bochner.Basic
import Mathlib.MeasureTheory.Integral.IntegrableOn
import Mathlib.MeasureTheory.Measure.Haar.OfBasis
import Submission.Work.Spaces.ProductTools

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

namespace Work.Spaces

open MeasureTheory Set Filter

/-! ## Two tools for the totalised integral, and the slice AM–GM bound -/

/-- Two-case monotonicity of the (totalised) Bochner integral: if `g` is integrable and
nonnegative a.e. and `f ≤ g` a.e., then `∫ f ≤ ∫ g`.

If `f` is not integrable its Bochner integral is `0` (`integral_undef`), so the bound is
`0 ≤ ∫ g`, which holds because `g ≥ 0` a.e. (`integral_nonneg_of_ae`); otherwise the usual
`integral_mono_ae` applies.  This is exactly the step needed when the integrand carries no
measurability hypothesis. -/
theorem integral_le_integral_of_ae_le_of_nonneg {α : Type*} [MeasurableSpace α] {μ : Measure α}
    {f g : α → ℝ} (hgi : Integrable g μ) (hg : 0 ≤ᵐ[μ] g) (h : f ≤ᵐ[μ] g) :
    ∫ a, f a ∂μ ≤ ∫ a, g a ∂μ := by
  by_cases hfi : Integrable f μ
  · exact integral_mono_ae hfi hgi h
  · rw [integral_undef hfi]
    exact integral_nonneg_of_ae hg

/-- The arithmetic–geometric mean inequality `|a| · |b| ≤ (a² + b²)/2`. -/
theorem abs_mul_abs_le_half_add_sq (a b : ℝ) : |a| * |b| ≤ (a ^ 2 + b ^ 2) / 2 := by
  nlinarith [sq_nonneg (|a| - |b|), sq_abs a, sq_abs b]

/-- **Slice AM–GM bound.**  For `z` in the domain, if `(W z)² ≤ 1` then the `θ`-slice of
`W² F Ψ` is bounded by the `θ`-slice of `(F² + Ψ²)/2`, using only that the two slices of
`F²` resp. `Ψ²` are integrable (`L2Mem.1`): when the slice of `W² F Ψ` is not integrable its
Bochner integral is `0`, otherwise the pointwise AM–GM bound `|W² F Ψ| ≤ (F² + Ψ²)/2`
integrates. -/
theorem slice_pair_le {F Ψ : ℝ → ℝ → ℝ} (hF : L2Mem F) (hΨ : L2Mem Ψ) {W : ℝ → ℝ}
    (hW : ∀ z, (W z) ^ 2 ≤ 1) {z : ℝ} (hz : z ∈ Iz) :
    (∫ θ in Iθ, (W z) ^ 2 * F z θ * Ψ z θ)
      ≤ ∫ θ in Iθ, ((F z θ) ^ 2 + (Ψ z θ) ^ 2) / 2 := by
  have hInt : IntegrableOn (fun θ => ((F z θ) ^ 2 + (Ψ z θ) ^ 2) / 2) Iθ :=
    ((hF.1 z hz).add (hΨ.1 z hz)).div_const 2
  refine integral_le_integral_of_ae_le_of_nonneg hInt
    (Filter.Eventually.of_forall fun θ =>
      div_nonneg (add_nonneg (sq_nonneg _) (sq_nonneg _)) (by norm_num))
    (ae_restrict_of_forall_mem (show MeasurableSet Iθ from measurableSet_Icc) fun θ hθ => ?_)
  -- the pointwise AM–GM bound, with `(W z)² ≤ 1` absorbing one of the two factors
  have hW2 : |(W z) ^ 2| ≤ 1 := by
    rw [abs_of_nonneg (sq_nonneg _)]; exact hW z
  have hb : |(W z) ^ 2 * F z θ * Ψ z θ| ≤ ((F z θ) ^ 2 + (Ψ z θ) ^ 2) / 2 := by
    calc |(W z) ^ 2 * F z θ * Ψ z θ|
        = |(W z) ^ 2| * |F z θ| * |Ψ z θ| := by rw [abs_mul, abs_mul]
      _ ≤ 1 * |F z θ| * |Ψ z θ| :=
          mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_right hW2 (abs_nonneg _)) (abs_nonneg _)
      _ = |F z θ| * |Ψ z θ| := by ring
      _ ≤ ((F z θ) ^ 2 + (Ψ z θ) ^ 2) / 2 := abs_mul_abs_le_half_add_sq _ _
  exact le_trans (le_abs_self _) hb

/-- **AM–GM bound for the source pairing** (`dz dθ` on `[0,∞) × [0,π/2]`).

If `F` and `Ψ` are square-integrable in the iterated honest sense (`Work.Spaces.L2Mem`) and
`W` is bounded by `1`, then the iterated integral of `W² F Ψ` is bounded by the mean of the two
squared `L²`-norms.

The point of the statement is that NO measurability or integrability hypothesis on `F`, `Ψ` is
imposed beyond `L2Mem`, so the proof must handle the totalised (junk) values: if the relevant
Bochner integral is not honest it is `0` and the estimate is trivial, and otherwise the usual
AM–GM argument applies.

Route.  Fix first `z ∈ Iz` and let `s z θ = (W z)^2 * F z θ * Ψ z θ`,
`s' z θ = ((F z θ)^2 + (Ψ z θ)^2)/2` (so `0 ≤ s'` and, since `(W z)^2 ≤ 1`,
`|s z θ| ≤ s' z θ` by AM–GM).  `s' z ·` is integrable on `Iθ` because both slice integrals of
`F²` and `Ψ²` are (`L2Mem.1`), so:
* either `¬ IntegrableOn (s z ·) Iθ`, and then `∫ θ in Iθ, s z θ = 0 ≤ ∫ θ in Iθ, s' z θ`
  (`MeasureTheory.integral_undef`, and `MeasureTheory.integral_nonneg` for the right-hand side);
* or `s z ·` is integrable, and `∫ θ in Iθ, s z θ ≤ ∫ θ in Iθ, |s z θ| ≤ ∫ θ in Iθ, s' z θ`
  (`MeasureTheory.abs_integral_le_integral_abs` and `MeasureTheory.integral_mono`).
Let `h z := ∫ θ in Iθ, s z θ` and `H z := ∫ θ in Iθ, s' z θ ≥ 0`; the previous paragraph gives
`h z ≤ H z` for every `z ∈ Iz`, and `H` is integrable on `Iz` by `L2Mem.2` and the linearity of
the integral.  Applying the same two-case argument at the outer level gives
`∫ z in Iz, h z ≤ ∫ z in Iz, H z`, and `∫ z in Iz, H z = (L2Sq F + L2Sq Ψ)/2` by
`MeasureTheory.integral_add` and `MeasureTheory.integral_const_mul`. -/
theorem PairIntegralLe {F Ψ : ℝ → ℝ → ℝ} (hF : L2Mem F) (hΨ : L2Mem Ψ) {W : ℝ → ℝ}
    (hW : ∀ z, (W z) ^ 2 ≤ 1) :
    (∫ z in Iz, ∫ θ in Iθ, (W z) ^ 2 * F z θ * Ψ z θ) ≤ (L2Sq F + L2Sq Ψ) / 2 := by
  -- the mean-integrand slice of the right-hand side splits into the two squared slices
  have hsliceId : ∀ z ∈ Iz,
      (∫ θ in Iθ, ((F z θ) ^ 2 + (Ψ z θ) ^ 2) / 2)
        = ((∫ θ in Iθ, (F z θ) ^ 2) + (∫ θ in Iθ, (Ψ z θ) ^ 2)) / 2 := by
    intro z hz
    rw [integral_div, integral_add (hF.1 z hz) (hΨ.1 z hz)]
  have hH_eq : (fun z => ∫ θ in Iθ, ((F z θ) ^ 2 + (Ψ z θ) ^ 2) / 2)
      =ᵐ[volume.restrict Iz]
        (fun z => ((∫ θ in Iθ, (F z θ) ^ 2) + (∫ θ in Iθ, (Ψ z θ) ^ 2)) / 2) :=
    ae_restrict_of_forall_mem (show MeasurableSet Iz from measurableSet_Ici) hsliceId
  -- the right-hand side is an honest integral (`L2Mem.2` and linearity)
  have hHint : Integrable (fun z => ∫ θ in Iθ, ((F z θ) ^ 2 + (Ψ z θ) ^ 2) / 2)
      (volume.restrict Iz) :=
    ((hF.2.add hΨ.2).div_const 2).congr hH_eq.symm
  have hHnonneg : 0 ≤ᵐ[volume.restrict Iz]
      (fun z => ∫ θ in Iθ, ((F z θ) ^ 2 + (Ψ z θ) ^ 2) / 2) :=
    Filter.Eventually.of_forall fun z =>
      integral_nonneg fun θ =>
        div_nonneg (add_nonneg (sq_nonneg _) (sq_nonneg _)) (by norm_num)
  -- the pointwise-in-`z` slice estimate
  have hle : (fun z => ∫ θ in Iθ, (W z) ^ 2 * F z θ * Ψ z θ)
      ≤ᵐ[volume.restrict Iz] (fun z => ∫ θ in Iθ, ((F z θ) ^ 2 + (Ψ z θ) ^ 2) / 2) :=
    ae_restrict_of_forall_mem (show MeasurableSet Iz from measurableSet_Ici)
      fun z hz => slice_pair_le hF hΨ hW hz
  have hmain := integral_le_integral_of_ae_le_of_nonneg hHint hHnonneg hle
  have hcompute : (∫ z in Iz, ∫ θ in Iθ, ((F z θ) ^ 2 + (Ψ z θ) ^ 2) / 2)
      = (L2Sq F + L2Sq Ψ) / 2 := by
    rw [integral_congr_ae hH_eq, integral_div, integral_add hF.2 hΨ.2]
    rfl
  exact hmain.trans hcompute.le

end Work.Spaces
