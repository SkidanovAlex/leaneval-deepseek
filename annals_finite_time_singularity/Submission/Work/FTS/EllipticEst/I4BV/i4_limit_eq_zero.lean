/-
Work module for `Work.FTS.EllipticEst.I4BV.i4_limit_eq_zero`.

# The limit of `cos²θ · ψ'(θ)` at `π/2` vanishes

If `ψ : ℝ → ℝ` is `C²` on `(0, π/2)`, its weighted square
`θ ↦ ψ θ² · sin(2θ)^{-η}` (`η = 99/100`) is integrable on `(0, π/2)`, and
`cos²θ · ψ'(θ)` has a limit `L` as `θ → (π/2)⁻`, then `L = 0`.

The mathematics: suppose `L > 0`.  Then `cos²θ ψ'(θ) > L/2` for `θ` close to `π/2`, so
`ψ'(θ) > (L/2)/cos²θ ≥ (L/2)/(π/2-θ)²` (using `cos θ ≤ π/2 - θ`).  The monotonicity of
`ψ(θ) - a/(b-θ) - (a/2)/(π/2-θ)`-type comparison (its derivative is
`ψ' - (a/2)/(π/2-θ)² ≥ 0` for the version used here) gives `ψ(θ) ≥ (L/4)/(π/2-θ)` on a right
neighbourhood, hence `ψ(θ)² ≥ (L/4)²/(π/2-θ)²` there; since `sin(2θ)^{-η} ≥ 1`, this
contradicts the integrability of `ψ²·sin(2θ)^{-η}` because `t ↦ t^{-2}` is not integrable at
`0`.  The case `L < 0` is the same applied to `-ψ`.

The two ingredients are:

* `exists_ge_div_of_deriv_ge` (monotonicity + a derivative lower bound gives a pointwise
  lower bound of the order `a/(b-θ)`);
* `not_integrableOn_inv_sq_right` (from
  `Submission.Work.FTS.EllipticEst.I4BV.not_integrableOn_inv_sq_right`), the divergence of
  `θ ↦ c/(b-θ)²` at the right endpoint.
-/
import Mathlib.Algebra.Order.Star.Real
import Mathlib.Algebra.Ring.IsFormallyReal
import Mathlib.Analysis.Calculus.ContDiff.Operations
import Mathlib.Analysis.Calculus.Deriv.Inv
import Mathlib.Analysis.Calculus.Deriv.MeanValue
import Mathlib.Analysis.LocallyConvex.AbsConvexOpen
import Mathlib.MeasureTheory.Integral.IntegrableOn
import Mathlib.MeasureTheory.Measure.Haar.OfBasis
import Mathlib.Order.CompletePartialOrder
import Submission.Work.FTS.EllipticEst.I4BV.Defs
import Submission.Work.FTS.EllipticEst.I4BV.not_integrableOn_inv_sq_right

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

noncomputable section

open scoped Real Topology
open MeasureTheory Set Filter

namespace Work.FTS.EllipticEst.I4BV

/-! ## Two elementary calculus helpers -/

/-- The derivative of `s ↦ a/(b - s)` away from `b`. -/
private lemma hasDerivAt_rat (a b : ℝ) {x : ℝ} (hx : x ≠ b) :
    HasDerivAt (fun s : ℝ => a / (b - s)) (a / (b - x) ^ 2) x := by
  have hxb : b - x ≠ 0 := sub_ne_zero.mpr (Ne.symm hx)
  have h1 : HasDerivAt (fun s : ℝ => b - s) (-1) x := by
    simpa using (hasDerivAt_id (𝕜 := ℝ) x).const_sub b
  have h2 : HasDerivAt (fun s : ℝ => (b - s)⁻¹) (-(-1) / (b - x) ^ 2) x := h1.inv hxb
  have h3 : HasDerivAt (fun s : ℝ => a * (b - s)⁻¹) (a * (-(-1) / (b - x) ^ 2)) x :=
    h2.const_mul a
  have hone : a * (-(-1) / (b - x) ^ 2) = a / (b - x) ^ 2 := by
    rw [neg_neg, one_div, div_eq_mul_inv]
  rw [hone] at h3
  have hfun : (fun s : ℝ => a * (b - s)⁻¹) = (fun s : ℝ => a / (b - s)) := by
    funext s; rw [div_eq_mul_inv]
  rw [hfun] at h3
  exact h3

/-- The value of the derivative of `s ↦ a/(b - s)` away from `b`. -/
private lemma deriv_rat (a b : ℝ) {x : ℝ} (hx : x ≠ b) :
    deriv (fun s : ℝ => a / (b - s)) x = a / (b - x) ^ 2 :=
  (hasDerivAt_rat a b hx).deriv

/-! ## Growth from a derivative lower bound -/

/-- If `ψ` is `C¹` on `(b-ε, b)` and `ψ' θ ≥ a/(b-θ)²` there (`a > 0`), then `ψ` grows at
least like `(a/2)/(b-θ)` as `θ → b⁻`.  Indeed `g θ = ψ θ - a/(b-θ)` has
`g' = ψ' - a/(b-θ)² ≥ 0`, so `g` is nondecreasing. -/
private theorem exists_ge_div_of_deriv_ge {ψ : ℝ → ℝ} {a b ε : ℝ} (ha : 0 < a) (hε : 0 < ε)
    (hsm : ContDiffOn ℝ 1 ψ (Set.Ioo (b - ε) b))
    (hbound : ∀ θ ∈ Set.Ioo (b - ε) b, a / (b - θ) ^ 2 ≤ deriv ψ θ) :
    ∃ δ : ℝ, 0 < δ ∧ δ ≤ ε ∧ ∀ θ ∈ Set.Ioo (b - δ) b, a / 2 / (b - θ) ≤ ψ θ := by
  set θ₀ : ℝ := b - ε / 2 with hθ₀
  have hθ₀mem : θ₀ ∈ Set.Ioo (b - ε) b :=
    ⟨by rw [hθ₀]; linarith, by rw [hθ₀]; linarith⟩
  have hdiffOn : DifferentiableOn ℝ ψ (Set.Ioo (b - ε) b) := hsm.differentiableOn (by norm_num)
  -- `g θ = ψ θ - a/(b-θ)` is nondecreasing on `[θ₀, θ]`.
  have hmono : ∀ θ ∈ Set.Ioo θ₀ b, ψ θ₀ - a / (b - θ₀) ≤ ψ θ - a / (b - θ) := by
    intro θ hθ
    have hsub : Set.Icc θ₀ θ ⊆ Set.Ioo (b - ε) b := fun s hs =>
      ⟨by linarith [hs.1, hθ₀mem.1], by linarith [hs.2, hθ.2]⟩
    have hlt : ∀ s ∈ Set.Icc θ₀ θ, s < b := fun s hs => lt_of_le_of_lt hs.2 hθ.2
    have hmon : MonotoneOn (fun s : ℝ => ψ s - a / (b - s)) (Set.Icc θ₀ θ) := by
      refine monotoneOn_of_deriv_nonneg (convex_Icc θ₀ θ) ?_ ?_ ?_
      · refine ContinuousOn.sub (hsm.continuousOn.mono hsub) ?_
        refine ContinuousOn.div continuousOn_const
          (continuousOn_const.sub continuousOn_id) ?_
        intro s hs
        exact ne_of_gt (sub_pos.mpr (hlt s hs))
      · rw [interior_Icc]
        refine DifferentiableOn.sub (hdiffOn.mono ?_) ?_
        · intro s hs
          exact ⟨by linarith [hs.1, hθ₀mem.1], by linarith [hs.2, hθ.2]⟩
        · refine DifferentiableOn.div (differentiableOn_const a)
            ((differentiableOn_const b).sub differentiableOn_id) ?_
          intro s hs
          exact ne_of_gt (sub_pos.mpr (lt_trans hs.2 hθ.2))
      · intro x hx
        rw [interior_Icc] at hx
        have hxmem : x ∈ Set.Ioo (b - ε) b :=
          ⟨by linarith [hx.1, hθ₀mem.1], by linarith [hx.2, hθ.2]⟩
        have hxb : x ≠ b := ne_of_lt (lt_trans hx.2 hθ.2)
        have hdψ : DifferentiableAt ℝ ψ x :=
          hdiffOn.differentiableAt (isOpen_Ioo.mem_nhds hxmem)
        have hdrat : DifferentiableAt ℝ (fun s : ℝ => a / (b - s)) x :=
          (hasDerivAt_rat a b hxb).differentiableAt
        have hdv : deriv (fun s : ℝ => ψ s - a / (b - s)) x
            = deriv ψ x - a / (b - x) ^ 2 := by
          change deriv (ψ - fun s : ℝ => a / (b - s)) x = deriv ψ x - a / (b - x) ^ 2
          rw [deriv_sub hdψ hdrat, deriv_rat a b hxb]
        rw [hdv]
        linarith [hbound x hxmem]
    have h' := hmon (Set.left_mem_Icc.mpr hθ.1.le) (Set.right_mem_Icc.mpr hθ.1.le) hθ.1.le
    simpa using h'
  -- The constant `K = ψ θ₀ - a/(b-θ₀)` and the choice of `δ`.
  set K : ℝ := ψ θ₀ - a / (b - θ₀) with hK
  set δ : ℝ := min (ε / 2) (a / 2 / (|K| + 1)) with hδ
  have hδleL : δ ≤ ε / 2 := by rw [hδ]; exact min_le_left _ _
  have hδleR : δ ≤ a / 2 / (|K| + 1) := by rw [hδ]; exact min_le_right _ _
  have hδpos : 0 < δ := by
    rw [hδ]
    exact lt_min (by linarith) (div_pos (by linarith) (by positivity))
  refine ⟨δ, hδpos, le_trans hδleL (by linarith), ?_⟩
  intro θ hθ
  have hθb : θ < b := hθ.2
  have hbθ : 0 < b - θ := sub_pos.mpr hθb
  have hθgt : θ₀ < θ := by
    rw [hθ₀]
    linarith [hθ.1, hδleL]
  have h1 : K ≤ ψ θ - a / (b - θ) := by
    have h := hmono θ ⟨hθgt, hθb⟩
    simpa [hK] using h
  have hbθA : b - θ < a / 2 / (|K| + 1) := lt_of_lt_of_le (by linarith [hθ.1]) hδleR
  have hKle : |K| * (b - θ) ≤ a / 2 := by
    have h1' : |K| * (b - θ) ≤ |K| * (a / 2 / (|K| + 1)) :=
      mul_le_mul_of_nonneg_left hbθA.le (abs_nonneg K)
    have h2' : |K| * (a / 2 / (|K| + 1)) = |K| * (a / 2) / (|K| + 1) := by ring
    have h3' : |K| * (a / 2) / (|K| + 1) ≤ a / 2 := by
      rw [div_le_iff₀ (by positivity : (0 : ℝ) < |K| + 1)]
      nlinarith [abs_nonneg K, ha]
    linarith
  have hKl : -K ≤ a / 2 / (b - θ) := by
    have h1' : |K| ≤ a / 2 / (b - θ) := by
      rw [le_div_iff₀ hbθ]
      exact hKle
    linarith [neg_le_abs K]
  have hZX : a / (b - θ) - a / 2 / (b - θ) = a / 2 / (b - θ) := by
    have ht : b - θ ≠ 0 := ne_of_gt hbθ
    field_simp
    ring
  have h3 : a / (b - θ) + K ≤ ψ θ := by linarith
  have h4 : a / 2 / (b - θ) ≤ a / (b - θ) + K := by linarith
  linarith

/-! ## Non-integrability of `ψ²` from the derivative lower bound -/

private theorem not_integrableOn_sq_of_deriv_ge' {ψ : ℝ → ℝ} {a b ε : ℝ} (ha : 0 < a)
    (hε : 0 < ε) (hsm : ContDiffOn ℝ 1 ψ (Set.Ioo (b - ε) b))
    (hbound : ∀ θ ∈ Set.Ioo (b - ε) b, a / (b - θ) ^ 2 ≤ deriv ψ θ) :
    ¬ MeasureTheory.IntegrableOn (fun θ => ψ θ ^ 2) (Set.Ioo (b - ε) b) := by
  obtain ⟨δ, hδpos, hδε, hlow⟩ := exists_ge_div_of_deriv_ge ha hε hsm hbound
  have hsub : Set.Ioo (b - δ) b ⊆ Set.Ioo (b - ε) b := fun θ hθ =>
    ⟨by linarith [hθ.1, hδε], hθ.2⟩
  have hc : 0 < (a / 2) ^ 2 := by positivity
  have hnot := not_integrableOn_inv_sq_right (c := (a / 2) ^ 2) (b := b) (ε := δ) hc hδpos
  intro hint
  refine hnot ?_
  have hint' : MeasureTheory.IntegrableOn (fun θ => ψ θ ^ 2) (Set.Ioo (b - δ) b) :=
    hint.mono_set hsub
  refine MeasureTheory.Integrable.mono' hint' ?_ ?_
  · have hcont : ContinuousOn (fun θ : ℝ => (a / 2) ^ 2 / (b - θ) ^ 2) (Set.Ioo (b - δ) b) := by
      refine ContinuousOn.div continuousOn_const
        ((continuousOn_const.sub continuousOn_id).pow 2) ?_
      intro θ hθ
      exact pow_ne_zero 2 (ne_of_gt (sub_pos.mpr hθ.2))
    exact hcont.aestronglyMeasurable measurableSet_Ioo
  · filter_upwards [MeasureTheory.ae_restrict_mem measurableSet_Ioo] with θ hθ
    have hbθ : 0 < b - θ := sub_pos.mpr hθ.2
    have hle := hlow θ hθ
    have hnonneg : 0 ≤ a / 2 / (b - θ) := div_nonneg (by linarith) hbθ.le
    have hsq : (a / 2 / (b - θ)) ^ 2 ≤ ψ θ ^ 2 := pow_le_pow_left₀ hnonneg hle 2
    rw [Real.norm_of_nonneg (div_nonneg (sq_nonneg _) (sq_nonneg _))]
    rw [div_pow] at hsq
    exact hsq

/-! ## The main lemma -/

/-- **The `I₄` limit vanishes.**  See the module docstring. -/
theorem i4_limit_eq_zero (ψ : ℝ → ℝ) (L : ℝ)
    (hsm : ContDiffOn ℝ 2 ψ (Set.Ioo 0 (Real.pi / 2)))
    (hA : MeasureTheory.IntegrableOn
      (fun θ => ψ θ ^ 2 * (Real.sin (2 * θ)) ^ (-(99 / 100 : ℝ)))
      (Set.Ioo 0 (Real.pi / 2)))
    (hL : Filter.Tendsto (fun θ => (Real.cos θ) ^ 2 * deriv ψ θ)
      (nhdsWithin (Real.pi / 2) (Set.Iio (Real.pi / 2))) (nhds L)) :
    L = 0 := by
  by_contra hLne
  have hpi2 : (0 : ℝ) < Real.pi / 2 := by linarith [Real.pi_pos]
  have hpi4 : (0 : ℝ) < Real.pi / 4 := by linarith [Real.pi_pos]
  -- The angular weight is at least `1` on the open interval.
  have hσ1 : ∀ θ ∈ Set.Ioo (0 : ℝ) (Real.pi / 2),
      1 ≤ (Real.sin (2 * θ)) ^ (-(99 / 100 : ℝ)) := by
    intro θ hθ
    simpa only [s4] using one_le_s4 hθ
  -- The contradiction engine: `ψ²` is never integrable on a right neighbourhood of `π/2`,
  -- while `hA` forces it to be.
  have hcontra : ∀ δ : ℝ, 0 < δ → δ < Real.pi / 2 →
      ¬ MeasureTheory.IntegrableOn (fun θ => ψ θ ^ 2)
        (Set.Ioo (Real.pi / 2 - δ) (Real.pi / 2)) → False := by
    intro δ hδpos hδlt hnot
    have hsub : Set.Ioo (Real.pi / 2 - δ) (Real.pi / 2) ⊆ Set.Ioo 0 (Real.pi / 2) :=
      fun θ hθ => ⟨by linarith [hθ.1, hδlt], hθ.2⟩
    have hA' : MeasureTheory.IntegrableOn
        (fun θ => ψ θ ^ 2 * (Real.sin (2 * θ)) ^ (-(99 / 100 : ℝ)))
        (Set.Ioo (Real.pi / 2 - δ) (Real.pi / 2)) := hA.mono_set hsub
    have haesm : MeasureTheory.AEStronglyMeasurable (fun θ => ψ θ ^ 2)
        ((MeasureTheory.volume : MeasureTheory.Measure ℝ).restrict
          (Set.Ioo (Real.pi / 2 - δ) (Real.pi / 2))) := by
      have hc : ContinuousOn (fun θ : ℝ => ψ θ ^ 2)
          (Set.Ioo (Real.pi / 2 - δ) (Real.pi / 2)) :=
        (hsm.continuousOn.mono hsub).pow 2
      exact hc.aestronglyMeasurable measurableSet_Ioo
    have hint : MeasureTheory.IntegrableOn (fun θ => ψ θ ^ 2)
        (Set.Ioo (Real.pi / 2 - δ) (Real.pi / 2)) := by
      refine MeasureTheory.Integrable.mono' hA' haesm ?_
      filter_upwards [MeasureTheory.ae_restrict_mem measurableSet_Ioo] with θ hθ
      have hθI := hsub hθ
      rw [Real.norm_of_nonneg (sq_nonneg (ψ θ))]
      exact le_mul_of_one_le_right (sq_nonneg (ψ θ)) (hσ1 θ hθI)
    exact hnot hint
  rcases lt_or_gt_of_ne hLne with hneg | hpos
  · -- Case `L < 0`: apply the engine to `-ψ`.
    have hev : ∀ᶠ x in nhdsWithin (Real.pi / 2) (Set.Iio (Real.pi / 2)),
        (Real.cos x) ^ 2 * deriv ψ x < L / 2 :=
      hL.eventually (Iio_mem_nhds (show L < L / 2 by linarith))
    obtain ⟨b, hb, hbsub⟩ := mem_nhdsLT_iff_exists_Ioo_subset.mp hev
    have hblt : b < Real.pi / 2 := hb
    set δ : ℝ := min (Real.pi / 2 - b) (Real.pi / 4) with hδdef
    have hδpos : 0 < δ := lt_min (by linarith) hpi4
    have hδlt : δ < Real.pi / 2 :=
      lt_of_le_of_lt (min_le_right _ _) (by linarith [Real.pi_pos])
    have hδleb : δ ≤ Real.pi / 2 - b := min_le_left _ _
    have hsub1 : Set.Ioo (Real.pi / 2 - δ) (Real.pi / 2) ⊆ Set.Ioo b (Real.pi / 2) :=
      fun θ hθ => ⟨by linarith [hθ.1, hδleb], hθ.2⟩
    have hkey : ∀ θ ∈ Set.Ioo (Real.pi / 2 - δ) (Real.pi / 2),
        (-L) / 2 / (Real.pi / 2 - θ) ^ 2 ≤ deriv (fun θ => -ψ θ) θ := by
      intro θ hθ
      have hθI : θ ∈ Set.Ioo (0 : ℝ) (Real.pi / 2) := ⟨by linarith [hθ.1, hδlt], hθ.2⟩
      have hlt : (Real.cos θ) ^ 2 * deriv ψ θ < L / 2 := hbsub (hsub1 hθ)
      have hcospos : 0 < Real.cos θ :=
        Real.cos_pos_of_mem_Ioo ⟨by linarith [hθI.1, Real.pi_pos], hθI.2⟩
      have hcossqpos : 0 < (Real.cos θ) ^ 2 := pow_pos hcospos 2
      have h1 : deriv ψ θ < L / 2 / (Real.cos θ) ^ 2 := by
        rw [lt_div_iff₀ hcossqpos]
        exact lt_of_eq_of_lt (mul_comm (deriv ψ θ) ((Real.cos θ) ^ 2)) hlt
      have hcle : Real.cos θ ≤ Real.pi / 2 - θ := cos_le_lin hθI
      have hcossqle : (Real.cos θ) ^ 2 ≤ (Real.pi / 2 - θ) ^ 2 :=
        pow_le_pow_left₀ hcospos.le hcle 2
      have h2 : (-L) / 2 / (Real.pi / 2 - θ) ^ 2 ≤ (-L) / 2 / (Real.cos θ) ^ 2 :=
        div_le_div_of_nonneg_left (by linarith) hcossqpos hcossqle
      have h4 : (-L) / 2 / (Real.cos θ) ^ 2 = -(L / 2 / (Real.cos θ) ^ 2) := by ring
      have h5 : (-L) / 2 / (Real.pi / 2 - θ) ^ 2 ≤ -(L / 2 / (Real.cos θ) ^ 2) := by
        rw [← h4]; exact h2
      have hder : deriv (fun θ => -ψ θ) θ = -deriv ψ θ := by
        have hd : DifferentiableAt ℝ ψ θ :=
          (hsm.differentiableOn (by norm_num)).differentiableAt (isOpen_Ioo.mem_nhds hθI)
        exact hd.hasDerivAt.neg.deriv
      rw [hder]
      linarith
    have hsm1 : ContDiffOn ℝ 1 ψ (Set.Ioo (Real.pi / 2 - δ) (Real.pi / 2)) :=
      (hsm.of_le (by norm_num)).mono (fun θ hθ => ⟨by linarith [hθ.1, hδlt], hθ.2⟩)
    have hnot := not_integrableOn_sq_of_deriv_ge'
      (show (0 : ℝ) < (-L) / 2 by linarith) hδpos hsm1.neg hkey
    have hnot' : ¬ MeasureTheory.IntegrableOn (fun θ => ψ θ ^ 2)
        (Set.Ioo (Real.pi / 2 - δ) (Real.pi / 2)) := by
      rw [show (fun θ : ℝ => (-ψ θ) ^ 2) = (fun θ => ψ θ ^ 2) from
        funext (fun θ => neg_sq (ψ θ))] at hnot
      exact hnot
    exact hcontra δ hδpos hδlt hnot'
  · -- Case `L > 0`.
    have hev : ∀ᶠ x in nhdsWithin (Real.pi / 2) (Set.Iio (Real.pi / 2)),
        L / 2 < (Real.cos x) ^ 2 * deriv ψ x :=
      hL.eventually (Ioi_mem_nhds (show L / 2 < L by linarith))
    obtain ⟨b, hb, hbsub⟩ := mem_nhdsLT_iff_exists_Ioo_subset.mp hev
    have hblt : b < Real.pi / 2 := hb
    set δ : ℝ := min (Real.pi / 2 - b) (Real.pi / 4) with hδdef
    have hδpos : 0 < δ := lt_min (by linarith) hpi4
    have hδlt : δ < Real.pi / 2 :=
      lt_of_le_of_lt (min_le_right _ _) (by linarith [Real.pi_pos])
    have hδleb : δ ≤ Real.pi / 2 - b := min_le_left _ _
    have hsub1 : Set.Ioo (Real.pi / 2 - δ) (Real.pi / 2) ⊆ Set.Ioo b (Real.pi / 2) :=
      fun θ hθ => ⟨by linarith [hθ.1, hδleb], hθ.2⟩
    have hkey : ∀ θ ∈ Set.Ioo (Real.pi / 2 - δ) (Real.pi / 2),
        L / 2 / (Real.pi / 2 - θ) ^ 2 ≤ deriv ψ θ := by
      intro θ hθ
      have hθI : θ ∈ Set.Ioo (0 : ℝ) (Real.pi / 2) := ⟨by linarith [hθ.1, hδlt], hθ.2⟩
      have hgt : L / 2 < (Real.cos θ) ^ 2 * deriv ψ θ := hbsub (hsub1 hθ)
      have hcospos : 0 < Real.cos θ :=
        Real.cos_pos_of_mem_Ioo ⟨by linarith [hθI.1, Real.pi_pos], hθI.2⟩
      have hcossqpos : 0 < (Real.cos θ) ^ 2 := pow_pos hcospos 2
      have h1 : L / 2 / (Real.cos θ) ^ 2 < deriv ψ θ := by
        rw [div_lt_iff₀ hcossqpos]
        exact lt_of_lt_of_eq hgt (mul_comm ((Real.cos θ) ^ 2) (deriv ψ θ))
      have hcle : Real.cos θ ≤ Real.pi / 2 - θ := cos_le_lin hθI
      have hcossqle : (Real.cos θ) ^ 2 ≤ (Real.pi / 2 - θ) ^ 2 :=
        pow_le_pow_left₀ hcospos.le hcle 2
      have h2 : L / 2 / (Real.pi / 2 - θ) ^ 2 ≤ L / 2 / (Real.cos θ) ^ 2 :=
        div_le_div_of_nonneg_left (by linarith) hcossqpos hcossqle
      exact le_trans h2 h1.le
    have hsm1 : ContDiffOn ℝ 1 ψ (Set.Ioo (Real.pi / 2 - δ) (Real.pi / 2)) :=
      (hsm.of_le (by norm_num)).mono (fun θ hθ => ⟨by linarith [hθ.1, hδlt], hθ.2⟩)
    have hnot := not_integrableOn_sq_of_deriv_ge'
      (show (0 : ℝ) < L / 2 by linarith) hδpos hsm1 hkey
    exact hcontra δ hδpos hδlt hnot

end Work.FTS.EllipticEst.I4BV
