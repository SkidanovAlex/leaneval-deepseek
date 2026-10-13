/-
Copyright: work module for the Elgindi finite-time singularity project.

# Almost every angular slice of an honest solution is a nice slice

For `Hon α F Ψ` (the level-`0` `η`-weighted hypothesis class of `Honest/Basic.lean`) and for
almost every `z > 0` (with respect to `volume` restricted to `(0,∞)`):

* the slice `θ ↦ Ψ z θ` tends to `0` at `θ → 0⁺` (`HonSliceLeftTendsto`);
* the slice tends to `0` at `θ → (π/2)⁻`;
* the square of the (one-variable) derivative of the slice is integrable on `Iθ`.

The second and third conjuncts in fact hold for **every** `z > 0`; only the first one — the
vanishing of the trace at `θ = 0`, i.e. `lim_{θ→0⁺} Ψ z θ = 0` — is available merely almost
everywhere (`Hon` prescribes `Ψ z 0 = 0` as a *punctual value* and controls the sub-interval
`N z = ∫_θ ∂_z²Ψ(z,θ) sinθcos²θ` only a.e.; see `NOTES_HonSecondMoment.md`).

## Route

* **Right endpoint.**  For every `z > 0` the slice `u = Ψ z ·` satisfies the three hypotheses of
  the general slice lemma `Work.FTS.EllipticEst.remov.SourceBound.sliceTendstoRight`: `C²` on the
  open interval, `∫_θ (u'')²σ < ∞` and `∫_θ (Lzero1 u)²σ < ∞` with `σ = sin(2θ)^{-η}`, and
  `∫_θ u² < ∞`.
  * `∫_θ u² < ∞` is `integrableOn_sq_psi'` (`HonSliceFinite`);
  * `∫_θ (u'')²σ < ∞` is the slicewise reading of `h.memB` (`integrableOn_pthIter2_sEta_of_HkMem`,
    `Endpt.sliceBdd_of_hmB`);
  * `∫_θ (Lzero1 u)²σ < ∞` follows from the equation `Lzero1 u = α²z²u'' + F(z,·) + α(5+α)z u'`
    on the open interval together with `h.memB`, `h.memF` and the `σ`-weighted `L²`-finiteness of
    `∂_zΨ(z,·)` (`integrableOn_zpz_sigma'`, `HonSliceFinite`).

* **Third conjunct.**  `∫_θ (∂_θΨ(z,·))² < ∞` is `integrableOn_sq_pth'` (`HonSliceFinite`), and
  `pth Ψ z θ` is by definition the derivative of the one-variable slice.
-/
import Mathlib.Algebra.Order.Star.Real
import Mathlib.Algebra.Ring.IsFormallyReal
import Mathlib.Analysis.Calculus.ContDiff.Defs
import Mathlib.Analysis.Calculus.FDeriv.Measurable
import Mathlib.MeasureTheory.Integral.Bochner.Basic
import Mathlib.MeasureTheory.Integral.IntegrableOn
import Mathlib.MeasureTheory.Measure.Haar.OfBasis
import Submission.Work.FTS.EllipticEst.Honest.Basic
import Submission.Work.FTS.EllipticEst.StraightDefs
import Submission.Work.FTS.EllipticEst.Honest.HonSliceFinite
import Submission.Work.FTS.EllipticEst.Honest.HonSliceLeftTendsto
import Submission.Work.FTS.EllipticEst.remov.SourceBound.sliceTendstoRight
import Submission.Work.FTS.EllipticEst.Endpt.sliceBdd_of_hmB

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

namespace Work.FTS.EllipticEst.Honest

set_option autoImplicit false
set_option maxHeartbeats 1000000

/-! ## The `σ`-weighted square of a slice is integrable, from level-`0` honesty -/

/-- **`∫_θ g(z,θ)² sin(2θ)^{-η} < ∞` from `HkMem α 0 g`.**  At level `0` the `H^k`-integrand is
the single square `(g z θ · w z / sin(2θ)^{η/2})²`, which equals `(w z)² · g z θ² · σ θ` on `Iθ`;
dividing by the non-zero constant `(w z)²` gives the claim. -/
theorem sq_mul_sEta_integrableOn_of_HkMem {α : ℝ} {g : ℝ → ℝ → ℝ}
    (hmem : Work.Spaces.HkMem α 0 g) {z : ℝ} (hz : 0 < z) :
    MeasureTheory.IntegrableOn (fun θ => (g z θ) ^ 2 * Work.FTS.EllipticEst.sEta θ)
      Work.Spaces.Iθ := by
  have hzI : z ∈ Work.Spaces.Iz := by rw [Work.Spaces.Iz]; exact le_of_lt hz
  have hw : (Work.Spaces.w z) ^ 2 ≠ 0 := by
    have h : Work.Spaces.w z ≠ 0 := by rw [Work.Spaces.w]; positivity
    exact pow_ne_zero 2 h
  refine ((hmem.1 z hzI).const_mul (((Work.Spaces.w z) ^ 2)⁻¹)).congr ?_
  filter_upwards [MeasureTheory.ae_restrict_mem measurableSet_Icc] with θ hθ
  rw [HkIntegrand_zero_eq α g z θ, sq_profile_eq g z θ (sin_two_nonneg_of_mem_Iθ hθ)]
  rw [show ((Work.Spaces.w z) ^ 2)⁻¹
        * ((g z θ) ^ 2 * (Work.Spaces.w z) ^ 2 * Real.sin (2 * θ) ^ (-Work.Spaces.eta))
      = ((Work.Spaces.w z) ^ 2)⁻¹ * (Work.Spaces.w z) ^ 2
        * ((g z θ) ^ 2 * Real.sin (2 * θ) ^ (-Work.Spaces.eta)) from by ring,
    inv_mul_cancel₀ hw, one_mul]
  rfl

/-! ## The `σ`-weighted square of `Lzero1` of a slice, from the equation -/

/-- **`∫_θ (Lzero1 (Ψ z ·))² σ < ∞` for honest data.**  On the open angular interval the equation
reads `Lzero1 (Ψ z ·) = F(z,·) + α²z² ∂_z²Ψ(z,·) + α(5+α)z ∂_zΨ(z,·)`, so the claim follows from
the three slice integrabilities `h.memF`, `h.memB` and `integrableOn_zpz_sigma'`. -/
theorem Lzero1_sq_mul_sEta_integrableOn {α : ℝ} {F Ψ : ℝ → ℝ → ℝ} (h : Hon α F Ψ) {z : ℝ}
    (hz : 0 < z) :
    MeasureTheory.IntegrableOn
      (fun θ => (Work.FTS.EllipticEst.Lzero1 (fun t => Ψ z t) θ) ^ 2
        * Work.FTS.EllipticEst.sEta θ) Work.Spaces.Iθ := by
  -- the three integrable pieces of the right-hand side of the equation
  have hAσ : MeasureTheory.IntegrableOn
      (fun θ => (Work.Spaces.pzIter 2 Ψ z θ) ^ 2 * Work.FTS.EllipticEst.sEta θ)
      Work.Spaces.Iθ := by
    have hzA : MeasureTheory.IntegrableOn
        (fun θ => ((z ^ 2) * Work.Spaces.pzIter 2 Ψ z θ) ^ 2
          * Work.FTS.EllipticEst.sEta θ) Work.Spaces.Iθ :=
      sq_mul_sEta_integrableOn_of_HkMem (g := fun z θ => z ^ 2 * Work.Spaces.pzIter 2 Ψ z θ)
        h.memA hz
    have hz2 : (z ^ 2) ^ 2 ≠ 0 := pow_ne_zero 2 (pow_ne_zero 2 (ne_of_gt hz))
    refine ((hzA.const_mul (((z ^ 2) ^ 2)⁻¹))).congr ?_
    filter_upwards with θ
    rw [show ((z ^ 2) ^ 2)⁻¹
          * (((z ^ 2) * Work.Spaces.pzIter 2 Ψ z θ) ^ 2 * Work.FTS.EllipticEst.sEta θ)
        = ((z ^ 2) ^ 2)⁻¹ * (z ^ 2) ^ 2
          * ((Work.Spaces.pzIter 2 Ψ z θ) ^ 2 * Work.FTS.EllipticEst.sEta θ) from by ring,
      inv_mul_cancel₀ hz2, one_mul]
  have hUσ : MeasureTheory.IntegrableOn
      (fun θ => (Work.Spaces.pz Ψ z θ) ^ 2 * Work.FTS.EllipticEst.sEta θ)
      Work.Spaces.Iθ := integrableOn_zpz_sigma' h hz
  have hFσ : MeasureTheory.IntegrableOn
      (fun θ => (F z θ) ^ 2 * Work.FTS.EllipticEst.sEta θ) Work.Spaces.Iθ :=
    sq_mul_sEta_integrableOn_of_HkMem h.memF hz
  -- the integrable dominator, with the coefficients of the equation absorbed
  have hdom : MeasureTheory.IntegrableOn
      (fun θ => (5 * (α ^ 2 * z ^ 2) ^ 2)
            * ((Work.Spaces.pzIter 2 Ψ z θ) ^ 2 * Work.FTS.EllipticEst.sEta θ)
          + (5 * (α * (5 + α) * z) ^ 2)
            * ((Work.Spaces.pz Ψ z θ) ^ 2 * Work.FTS.EllipticEst.sEta θ)
          + 5 * ((F z θ) ^ 2 * Work.FTS.EllipticEst.sEta θ)) Work.Spaces.Iθ :=
    ((hAσ.const_mul (5 * (α ^ 2 * z ^ 2) ^ 2)).add
      (hUσ.const_mul (5 * (α * (5 + α) * z) ^ 2))).add (hFσ.const_mul 5)
  -- a.e. strong measurability of the integrand
  have haesm : MeasureTheory.AEStronglyMeasurable
      (fun θ => (Work.FTS.EllipticEst.Lzero1 (fun t => Ψ z t) θ) ^ 2
        * Work.FTS.EllipticEst.sEta θ) (MeasureTheory.volume.restrict Work.Spaces.Iθ) := by
    have h3' : MeasureTheory.AEStronglyMeasurable (fun θ => Ψ z θ)
        (MeasureTheory.volume.restrict Work.Spaces.Iθ) :=
      Work.Spaces.aesm_slice_of_continuousOn_Qd (fun p : ℝ × ℝ => Ψ p.1 p.2)
        (Work.FTS.EllipticEst.smoothOpen_of_forall h.sm).continuousOn hz
    have hLu : MeasureTheory.AEStronglyMeasurable
        (fun θ => Work.FTS.EllipticEst.Lzero1 (fun t => Ψ z t) θ)
        (MeasureTheory.volume.restrict Work.Spaces.Iθ) := by
      show MeasureTheory.AEStronglyMeasurable (fun θ : ℝ =>
        -(deriv (fun t => deriv (fun θ' => Ψ z θ') t) θ)
          + deriv (fun t => Real.tan t * Ψ z t) θ - 6 * Ψ z θ) _
      exact (((measurable_deriv (fun t => deriv (fun θ' => Ψ z θ') t)).neg.aestronglyMeasurable).add
        ((measurable_deriv (fun t => Real.tan t * Ψ z t)).aestronglyMeasurable)).sub
        (h3'.const_mul 6)
    exact (hLu.pow 2).mul aesm_sEta'
  refine MeasureTheory.Integrable.mono' hdom haesm ?_
  filter_upwards [ae_mem_Ioo_Iθ'] with θ hθ
  have hσ : 0 ≤ Work.FTS.EllipticEst.sEta θ := sEta_nonneg_Ioo hθ
  have hkey : Work.FTS.EllipticEst.Lzero1 (fun t => Ψ z t) θ
      = F z θ + (α ^ 2 * z ^ 2) * Work.Spaces.pzIter 2 Ψ z θ
        + (α * (5 + α) * z) * Work.Spaces.pz Ψ z θ := by
    have hb := h.eq z hz θ hθ.1 hθ.2
    rw [Work.Elliptic.bslOp_apply] at hb
    have hL : Work.Elliptic.Lzero Ψ z θ = F z θ + α ^ 2 * z ^ 2 * Work.Spaces.pzIter 2 Ψ z θ
        + (α * (5 + α) * z) * Work.Spaces.pz Ψ z θ := by linarith [hb]
    rw [show Work.FTS.EllipticEst.Lzero1 (fun t => Ψ z t) θ
      = Work.Elliptic.Lzero Ψ z θ from rfl, hL]
  have h5 : (F z θ + (α ^ 2 * z ^ 2) * Work.Spaces.pzIter 2 Ψ z θ
        + (α * (5 + α) * z) * Work.Spaces.pz Ψ z θ) ^ 2
      ≤ 5 * ((F z θ) ^ 2 + ((α ^ 2 * z ^ 2) * Work.Spaces.pzIter 2 Ψ z θ) ^ 2
        + ((α * (5 + α) * z) * Work.Spaces.pz Ψ z θ) ^ 2) := by
    have hsq := sq_sum_five_le' (F z θ) ((α ^ 2 * z ^ 2) * Work.Spaces.pzIter 2 Ψ z θ)
      ((α * (5 + α) * z) * Work.Spaces.pz Ψ z θ) 0 0
    nlinarith [hsq]
  rw [Real.norm_of_nonneg (mul_nonneg (sq_nonneg _) hσ), hkey]
  calc (F z θ + (α ^ 2 * z ^ 2) * Work.Spaces.pzIter 2 Ψ z θ
          + (α * (5 + α) * z) * Work.Spaces.pz Ψ z θ) ^ 2 * Work.FTS.EllipticEst.sEta θ
      ≤ 5 * ((F z θ) ^ 2 + ((α ^ 2 * z ^ 2) * Work.Spaces.pzIter 2 Ψ z θ) ^ 2
          + ((α * (5 + α) * z) * Work.Spaces.pz Ψ z θ) ^ 2) * Work.FTS.EllipticEst.sEta θ :=
        mul_le_mul_of_nonneg_right h5 hσ
    _ = (5 * (α ^ 2 * z ^ 2) ^ 2)
            * ((Work.Spaces.pzIter 2 Ψ z θ) ^ 2 * Work.FTS.EllipticEst.sEta θ)
          + (5 * (α * (5 + α) * z) ^ 2)
            * ((Work.Spaces.pz Ψ z θ) ^ 2 * Work.FTS.EllipticEst.sEta θ)
          + 5 * ((F z θ) ^ 2 * Work.FTS.EllipticEst.sEta θ) := by ring

/-! ## The three conjuncts -/

theorem HonSliceAeYc (α : ℝ) (F Ψ : ℝ → ℝ → ℝ)
    (h : Work.FTS.EllipticEst.Honest.Hon α F Ψ) :
    ∀ᵐ z ∂(MeasureTheory.volume.restrict (Set.Ioi 0)),
      Filter.Tendsto (fun θ : ℝ => Ψ z θ) (nhdsWithin 0 (Set.Ioi 0)) (nhds 0) ∧
      Filter.Tendsto (fun θ : ℝ => Ψ z θ)
        (nhdsWithin (Real.pi / 2) (Set.Iio (Real.pi / 2))) (nhds 0) ∧
      MeasureTheory.IntegrableOn (fun θ : ℝ => (deriv (fun t : ℝ => Ψ z t) θ) ^ 2)
        Work.Spaces.Iθ := by
  have hsm : ∀ n : ℕ, ContDiffOn ℝ n (Function.uncurry Ψ)
      (Set.Ioi 0 ×ˢ Set.Ioo 0 (Real.pi / 2)) := h.sm
  -- ## the right endpoint, for every `z > 0`
  have hright : ∀ z : ℝ, 0 < z → Filter.Tendsto (fun θ : ℝ => Ψ z θ)
      (nhdsWithin (Real.pi / 2) (Set.Iio (Real.pi / 2))) (nhds 0) := by
    intro z hz
    refine Work.FTS.EllipticEst.remov.SourceBound.sliceTendstoRight (fun θ => Ψ z θ) ?_ ?_ ?_
      (integrableOn_sq_psi' h hz)
    · exact Work.FTS.EllipticEst.Endpt.contDiffOn_slice_of_strip hsm hz 2
    · -- `∫_θ (u'')² σ < ∞`, with `u''` written as the iterated `deriv`
      refine (Work.FTS.EllipticEst.Endpt.integrableOn_pthIter2_sEta_of_HkMem h.memB hz).congr ?_
      refine Filter.Eventually.of_forall (fun θ => ?_)
      show Work.Spaces.pthIter 2 Ψ z θ ^ 2 * Work.FTS.EllipticEst.sEta θ
        = (deriv (fun t => deriv (fun θ' => Ψ z θ') t) θ) ^ 2 * Work.FTS.EllipticEst.sEta θ
      rw [show Work.Spaces.pthIter 2 Ψ z θ
        = deriv (fun t => deriv (fun θ' => Ψ z θ') t) θ from rfl]
    · exact Lzero1_sq_mul_sEta_integrableOn h hz
  -- ## the third conjunct, for every `z > 0`
  have hderiv : ∀ z : ℝ, 0 < z → MeasureTheory.IntegrableOn
      (fun θ : ℝ => (deriv (fun t : ℝ => Ψ z t) θ) ^ 2) Work.Spaces.Iθ := by
    intro z hz
    simpa only [Work.Spaces.pth] using integrableOn_sq_pth' h hz
  -- ## the left endpoint, almost everywhere
  have hleft := HonSliceLeftTendsto α F Ψ h
  filter_upwards [hleft, MeasureTheory.ae_restrict_mem measurableSet_Ioi] with z hzl hz
  exact ⟨hzl, hright z hz, hderiv z hz⟩

end Work.FTS.EllipticEst.Honest
