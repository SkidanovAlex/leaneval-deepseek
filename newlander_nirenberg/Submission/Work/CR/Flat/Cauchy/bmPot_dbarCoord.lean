/-
Copyright: none.  Part of the `Newlander-Nirenberg` formalisation project.

# Differentiating the Bochner–Martinelli potential

`bmPot f z = Σ_k ∫ x, bmKernel k x * f k (z + x)` is (up to the change of variable `x ↦ -x`)
minus a sum of convolutions `bmKernel k ⋆[mul ℝ ℂ, volume] f k`, see
`bmPotential_eq_neg_conv` / `bmPotential_eq_bmPot`.  Since the `f k` are `C¹` with compact
support, Mathlib's `HasCompactSupport.hasFDerivAt_convolution_right` differentiates each
convolution, and the `∂̄`-derivative of the potential is obtained by evaluating the resulting
`(ℂⁿ →L[ℝ] ℂ)`-valued convolution against the two tangent vectors `e_j` and `i·e_j`, using
`dbarCoordPhi` and `convolution_precompR_apply`.
-/
import Mathlib
import Submission.Work.CR.Flat.Cauchy.bmSetup
import Submission.Work.CR.Flat.Cauchy.bmPotential_contDiff_one
import Submission.Work.CR.Flat.Polydisc.dbarCoord_comm

noncomputable section

open scoped NNReal ENNReal Convolution Topology
open MeasureTheory Set Filter

namespace Work.CR.Flat.Cauchy

/-! ## Elementary supporting lemmas -/

/-- A function that vanishes outside the closed ball of radius `R` has compact support. -/
lemma bmPotDbar_hasCompactSupport_of_norm {n : ℕ} {R : ℝ} {g : (Fin n → ℂ) → ℂ}
    (h : ∀ x, R ≤ ‖x‖ → g x = 0) : HasCompactSupport g := by
  refine IsCompact.of_isClosed_subset (isCompact_closedBall (0 : Fin n → ℂ) R)
    (isClosed_tsupport g) ?_
  rw [tsupport]
  refine closure_minimal ?_ Metric.isClosed_closedBall
  intro x hx
  rw [Metric.mem_closedBall, dist_eq_norm, sub_zero]
  exact le_of_lt (lt_of_not_ge fun hle => hx (h x hle))

/-- The Fréchet derivative of a compactly supported function again has compact support. -/
lemma bmPotDbar_hasCompactSupport_fderiv {n : ℕ} {g : (Fin n → ℂ) → ℂ}
    (hg : HasCompactSupport g) : HasCompactSupport (fderiv ℝ g) := by
  refine IsCompact.of_isClosed_subset hg (isClosed_tsupport _) ?_
  rw [tsupport]
  refine closure_minimal ?_ (isClosed_tsupport g)
  intro x hx
  by_contra hxmem
  have hnb : (tsupport g)ᶜ ∈ 𝓝 x := (isClosed_tsupport g).isOpen_compl.mem_nhds hxmem
  have hzero : fderiv ℝ g x = 0 := by
    have heq : g =ᶠ[𝓝 x] (fun _ : Fin n → ℂ => (0 : ℂ)) := by
      filter_upwards [hnb] with y hy
      have hy' : y ∉ Function.support g := fun hgy => hy (subset_tsupport g hgy)
      simpa only [Function.mem_support, ne_eq, not_not] using hy'
    rw [heq.fderiv_eq, fderiv_const_apply]
  have hxne : fderiv ℝ g x ≠ 0 := by
    simpa only [Function.mem_support, ne_eq] using hx
  exact absurd hzero hxne

/-- `dbarCoordPhi j` is complex homogeneous: it commutes with the map `b ↦ a * b`. -/
lemma bmPotDbar_dbarCoordPhi_comp {n : ℕ} (j : Fin n) (a : ℂ) (b : (Fin n → ℂ) →L[ℝ] ℂ) :
    Work.CR.Flat.Polydisc.dbarCoordPhi j ((ContinuousLinearMap.mul ℝ ℂ a).comp b)
      = a * Work.CR.Flat.Polydisc.dbarCoordPhi j b := by
  simp only [Work.CR.Flat.Polydisc.dbarCoordPhi, ContinuousLinearMap.comp_apply, add_apply,
    ContinuousLinearMap.apply_apply, ContinuousLinearMap.mul_apply']
  ring

/-- The same identity for the convolution kernel `L.precompR` attached to multiplication. -/
lemma bmPotDbar_dbarCoordPhi_precompR {n : ℕ} (j : Fin n) (a : ℂ)
    (b : (Fin n → ℂ) →L[ℝ] ℂ) :
    Work.CR.Flat.Polydisc.dbarCoordPhi j
        ((ContinuousLinearMap.precompR (Fin n → ℂ) (ContinuousLinearMap.mul ℝ ℂ)) a b)
      = a * Work.CR.Flat.Polydisc.dbarCoordPhi j b := by
  rw [ContinuousLinearMap.precompR_apply, ContinuousLinearMap.compL_apply]
  exact bmPotDbar_dbarCoordPhi_comp j a b

/-- The change of variable `t ↦ -t` together with the oddness of the Bochner–Martinelli
kernel `bmKernel k (-t) = -bmKernel k t`. -/
lemma bmPotDbar_integral_flip {n : ℕ} (k : Fin n) (φ : (Fin n → ℂ) → ℂ) (z : Fin n → ℂ) :
    ∫ t, bmKernel k t * φ (z - t) = - ∫ x, bmKernel k x * φ (z + x) := by
  rw [← MeasureTheory.integral_neg_eq_self
    (fun t : Fin n → ℂ => bmKernel k t * φ (z - t)) volume]
  have h : (fun x : Fin n → ℂ => bmKernel k (-x) * φ (z - -x))
      = fun x => -(bmKernel k x * φ (z + x)) := by
    funext x
    rw [bmKernel_neg, neg_mul, sub_neg_eq_add]
  rw [h, MeasureTheory.integral_neg]

/-! ## The main theorem -/

/-- **Differentiating the Bochner–Martinelli potential.**  If the components `f k` are `C¹` and
vanish outside the closed ball of radius `R > 0` about the origin, then the potential
`bmPot f z = Σ_k ∫ x, bmKernel k x * f k (z + x)` is real differentiable in `z` and
`dbarCoord j (bmPot f) z = Σ_k ∫ x, bmKernel k x * dbarCoord j (f k) (z + x)`:
the `∂̄`-derivative may be taken under the integral sign, the singular integral being absolutely
convergent because `f k` is compactly supported.

Useful ingredients: `bmPotential_eq_bmPot` and `bmPotential_eq_neg_conv`
(`Submission/Work/CR/Flat/Cauchy/bmPotential_contDiff_one.lean`) rewrite `bmPotential f` as a sum
of convolutions `-Σ_k (bmKernel k ⋆[ContinuousLinearMap.mul ℝ ℂ, volume] f k)`, and
`HasCompactSupport.hasFDerivAt_convolution_right` (Mathlib) gives the derivative as
`bmKernel k ⋆[ContinuousLinearMap.mul ℝ ℂ |>.precompR _, volume] fderiv ℝ (f k)`, with
`convolution_precompR_apply` extracting the value on a vector.  `locallyIntegrable_bmKernel`,
`norm_bmKernel_le`, `hasCompactSupport_of_halfPolydisc` and `bmKernel_neg` from that file are also
useful (they give integrability and the sign change under `x ↦ -x`). -/
theorem bmPot_dbarCoord {n : ℕ} (hn : 0 < n) {f : Fin n → (Fin n → ℂ) → ℂ}
    (hf : ∀ k, ContDiff ℝ 1 (f k)) {R : ℝ} (hR : 0 < R)
    (hsupp : ∀ k : Fin n, ∀ x : Fin n → ℂ, R ≤ ‖x‖ → f k x = 0) (j : Fin n) (z : Fin n → ℂ) :
    dbarCoord j (bmPot f) z = ∑ k, ∫ x, bmKernel k x * dbarCoord j (f k) (z + x) := by
  have _hR := hR
  obtain hcs : ∀ k, HasCompactSupport (f k) := fun k => bmPotDbar_hasCompactSupport_of_norm (hsupp k)
  have hcs' : ∀ k, HasCompactSupport (fderiv ℝ (f k)) :=
    fun k => bmPotDbar_hasCompactSupport_fderiv (hcs k)
  have hcont' : ∀ k, Continuous (fderiv ℝ (f k)) :=
    fun k => (hf k).continuous_fderiv (by simp)
  -- `bmPot` is minus a sum of convolutions
  have hbmPot : bmPot f =
      fun w => -∑ k, (bmKernel k ⋆[ContinuousLinearMap.mul ℝ ℂ, volume] f k) w := by
    funext w
    rw [← bmPotential_eq_bmPot f w]
    exact congrFun (bmPotential_eq_neg_conv f) w
  -- the derivative of the potential
  have hderiv : HasFDerivAt (bmPot f)
      (-∑ k, (bmKernel k ⋆[ContinuousLinearMap.precompR (Fin n → ℂ) (ContinuousLinearMap.mul ℝ ℂ),
                volume] fderiv ℝ (f k)) z) z := by
    rw [hbmPot]
    refine HasFDerivAt.neg ?_
    have hsum : HasFDerivAt
        (fun w => ∑ k, (bmKernel k ⋆[ContinuousLinearMap.mul ℝ ℂ, volume] f k) w)
        (∑ k, (bmKernel k ⋆[ContinuousLinearMap.precompR (Fin n → ℂ)
          (ContinuousLinearMap.mul ℝ ℂ), volume] fderiv ℝ (f k)) z) z := by
      have h := HasFDerivAt.sum (u := Finset.univ) fun k _ =>
        HasCompactSupport.hasFDerivAt_convolution_right (ContinuousLinearMap.mul ℝ ℂ)
          (hcs k) (locallyIntegrable_bmKernel hn k) (hf k) z
      have hfun : (∑ k, (bmKernel k ⋆[ContinuousLinearMap.mul ℝ ℂ, volume] f k))
          = fun w => ∑ k, (bmKernel k ⋆[ContinuousLinearMap.mul ℝ ℂ, volume] f k) w := by
        funext w
        rw [Finset.sum_apply]
      rw [hfun] at h
      exact h
    exact hsum
  -- the `∂̄`-derivative of a single convolution
  have hval : ∀ k, Polydisc.dbarCoordPhi j ((bmKernel k ⋆[
        ContinuousLinearMap.precompR (Fin n → ℂ) (ContinuousLinearMap.mul ℝ ℂ), volume]
        fderiv ℝ (f k)) z) = -∫ x, bmKernel k x * dbarCoord j (f k) (z + x) := by
    intro k
    have hInt : MeasureTheory.ConvolutionExistsAt (bmKernel k) (fderiv ℝ (f k)) z
        (ContinuousLinearMap.precompR (Fin n → ℂ) (ContinuousLinearMap.mul ℝ ℂ)) volume :=
      HasCompactSupport.convolutionExists_right
        (ContinuousLinearMap.precompR (Fin n → ℂ) (ContinuousLinearMap.mul ℝ ℂ))
        (hcs' k) (locallyIntegrable_bmKernel hn k) (hcont' k) z
    rw [MeasureTheory.convolution_def]
    rw [← ContinuousLinearMap.integral_comp_comm (Polydisc.dbarCoordPhi j) hInt]
    have hcongr : (∫ t, Polydisc.dbarCoordPhi j
          ((ContinuousLinearMap.precompR (Fin n → ℂ) (ContinuousLinearMap.mul ℝ ℂ))
            (bmKernel k t) (fderiv ℝ (f k) (z - t))))
        = ∫ t, bmKernel k t * dbarCoord j (f k) (z - t) := by
      refine MeasureTheory.integral_congr_ae (Eventually.of_forall fun t => ?_)
      simp only [Polydisc.dbarCoord_eq_comp, bmPotDbar_dbarCoordPhi_precompR,
        Function.comp_apply]
    rw [hcongr]
    exact bmPotDbar_integral_flip k (dbarCoord j (f k)) z
  -- assemble
  have hcomp : dbarCoord j (bmPot f) z = Polydisc.dbarCoordPhi j (fderiv ℝ (bmPot f) z) := by
    simpa only [Function.comp_apply] using congrFun (Polydisc.dbarCoord_eq_comp j (bmPot f)) z
  rw [hcomp, hderiv.fderiv]
  simp only [map_neg, map_sum, hval, Finset.sum_neg_distrib, neg_neg]

end Work.CR.Flat.Cauchy
