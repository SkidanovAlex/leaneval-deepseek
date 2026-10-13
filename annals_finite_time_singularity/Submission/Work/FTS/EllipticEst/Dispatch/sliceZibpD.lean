/-
Copyright: work module for the Elgindi finite-time singularity project.

# The per-angle radial integration by parts of the truncated energy identity

For a datum `AeData α u G` of the almost-everywhere class and a `C²` cutoff `χ` with compact
support in `(0,∞)`, the two one-dimensional integration-by-parts identities of the energy
identity hold *slice by slice* in `θ` (`θ ∈ (0,π/2)` is the region where the `z`-slice of `u` is
smooth on `(0,∞)`):

`∫_z (χ w²)(z) z² ∂_z²u(z,θ) u(z,θ) dz = (1/2) ∫_z (z²χw²)''(z) u(z,θ)² dz
                                          − ∫_z (χw²)(z) (z ∂_zu(z,θ))² dz`,

`∫_z (χ w²)(z) z ∂_zu(z,θ) u(z,θ) dz = −(1/2) ∫_z (z χw²)'(z) u(z,θ)² dz`.

They are the instantiations of `Work.FTS.EllipticEst.remov.ibpZZ` and `...ibpZ` at the weight
`Wcut χ = χ · w²` and the slice `z ↦ u z θ`; the compact support of `χ` supplies both the
integrability of the (finitely many) product integrands and the vanishing of the boundary terms.
-/
import Mathlib.Algebra.Ring.IsFormallyReal
import Mathlib.Analysis.Calculus.ContDiff.Deriv
import Mathlib.Analysis.Calculus.ContDiff.Operations
import Mathlib.MeasureTheory.Integral.Bochner.Basic
import Mathlib.MeasureTheory.Integral.IntegrableOn
import Mathlib.MeasureTheory.Measure.Haar.OfBasis
import Mathlib.Order.CompletePartialOrder
import Submission.Work.FTS.EllipticEst.Dispatch.aeFirstEnergyDTools
import Submission.Work.FTS.EllipticEst.remov.ibpZZ
import Submission.Work.FTS.EllipticEst.remov.ibpZ
import Submission.Work.FTS.EllipticEst.integrableOn_Ioi_of_tail_zero

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

noncomputable section

open scoped Real Topology
open MeasureTheory Set Filter

namespace Work.FTS.EllipticEst.Dispatch

set_option autoImplicit false
set_option linter.unusedVariables false

/-! ## Three elementary consequences of a compactly supported tail -/

/-- A function on `(0,∞)` which is continuous there and vanishes off a compact interval
`[δ,b] ⊆ (0,∞)` is integrable. -/
theorem integrableOn_Ioi_of_support_subset_Icc {f : ℝ → ℝ} {δ b : ℝ} (hδ : 0 < δ)
    (hcont : ContinuousOn f (Set.Ioi 0)) (hsupp : ∀ z, z ∉ Set.Icc δ b → f z = 0) :
    MeasureTheory.IntegrableOn f (Set.Ioi 0) := by
  obtain ⟨C, hC⟩ := IsCompact.exists_bound_of_continuousOn isCompact_Icc
    (hcont.mono (fun z hz => lt_of_lt_of_le hδ hz.1))
  refine Work.FTS.EllipticEst.integrableOn_Ioi_of_tail_zero (f := f) (b := max δ b)
    (M := max C 0) (hcont.aestronglyMeasurable measurableSet_Ioi)
    (fun z hz => ?_) (fun z hz hz' => ?_)
  · by_cases h : z ∈ Set.Icc δ b
    · exact le_trans (hC z h) (le_max_left _ _)
    · rw [hsupp z h, norm_zero]; exact le_max_right _ _
  · exact hsupp z (fun hc => absurd hc.2
      (not_le.mpr (lt_of_le_of_lt (le_max_right δ b) hz')))

/-- A function vanishing off a compact interval `[δ,b] ⊆ (0,∞)` tends to `0` at `0⁺`. -/
theorem tendsto_nhdsGT_zero_of_support_subset_Icc {f : ℝ → ℝ} {δ b : ℝ} (hδ : 0 < δ)
    (hsupp : ∀ z, z ∉ Set.Icc δ b → f z = 0) :
    Filter.Tendsto f (nhdsWithin (0 : ℝ) (Set.Ioi 0)) (nhds 0) := by
  have hmem : Set.Ioo (0 : ℝ) δ ∈ nhdsWithin (0 : ℝ) (Set.Ioi 0) :=
    (nhdsGT_basis 0).mem_iff.mpr ⟨δ, hδ, subset_rfl⟩
  refine Filter.Tendsto.congr' (Filter.EventuallyEq.symm ?_) tendsto_const_nhds
  filter_upwards [hmem] with x hx
  exact hsupp x (fun hc => absurd hc.1 (not_le.mpr hx.2))

/-- A function vanishing off a compact interval tends to `0` at `+∞`. -/
theorem tendsto_atTop_zero_of_support_subset_Icc {f : ℝ → ℝ} {δ b : ℝ}
    (hsupp : ∀ z, z ∉ Set.Icc δ b → f z = 0) :
    Filter.Tendsto f Filter.atTop (nhds 0) := by
  refine Filter.Tendsto.congr' (Filter.EventuallyEq.symm ?_) tendsto_const_nhds
  filter_upwards [Filter.eventually_gt_atTop (max δ b)] with x hx
  exact hsupp x (fun hc => absurd hc.2
    (not_le.mpr (lt_of_le_of_lt (le_max_right δ b) hx)))

/-- A compactly supported function vanishes past some point. -/
theorem hasCompactSupport_eventually_zero {χ : ℝ → ℝ} (hcpt : HasCompactSupport χ) :
    ∃ b : ℝ, ∀ z : ℝ, b ≤ z → χ z = 0 := by
  obtain ⟨C, hC⟩ := hcpt.isCompact.isBounded.subset_closedBall (0 : ℝ)
  refine ⟨max (C + 1) 0, fun z hz => ?_⟩
  by_contra h
  have hmem : z ∈ tsupport χ := subset_tsupport χ (Function.mem_support.mpr h)
  have h1 := hC hmem
  rw [Metric.mem_closedBall, Real.dist_eq, sub_zero] at h1
  have hz0 : 0 ≤ z := le_trans (le_max_right (C + 1) 0) hz
  rw [abs_of_nonneg hz0] at h1
  linarith [le_max_left (C + 1) 0]

/-- The derivative of a function supported in `[δ,b]` vanishes off `[δ,b]`. -/
theorem deriv_eq_zero_off {f : ℝ → ℝ} {δ b : ℝ}
    (hsupp : ∀ z, z ∉ Set.Icc δ b → f z = 0) :
    ∀ z, z ∉ Set.Icc δ b → deriv f z = 0 := by
  intro z hz
  have hnb : f =ᶠ[𝓝 z] (fun _ => (0 : ℝ)) := by
    rcases not_and_or.mp hz with h | h
    · have hzδ : z < δ := not_le.mp h
      filter_upwards [Metric.ball_mem_nhds z (sub_pos.mpr hzδ)] with y hy
      refine hsupp y (fun hc => ?_)
      rw [Metric.mem_ball, Real.dist_eq] at hy
      exact absurd hc.1 (not_le.mpr (by linarith [(abs_lt.mp hy).2]))
    · have hzb : b < z := not_le.mp h
      filter_upwards [Metric.ball_mem_nhds z (sub_pos.mpr hzb)] with y hy
      refine hsupp y (fun hc => ?_)
      rw [Metric.mem_ball, Real.dist_eq] at hy
      exact absurd hc.2 (not_le.mpr (by linarith [neg_lt.mp (abs_lt.mp hy).1]))
  rw [hnb.deriv_eq]
  simp

/-- The second derivative of a function supported in `[δ,b]` vanishes off `[δ,b]`. -/
theorem deriv_deriv_eq_zero_off {f : ℝ → ℝ} {δ b : ℝ}
    (hsupp : ∀ z, z ∉ Set.Icc δ b → f z = 0) :
    ∀ z, z ∉ Set.Icc δ b → deriv (deriv f) z = 0 :=
  deriv_eq_zero_off (deriv_eq_zero_off hsupp)

/-! ## The two radial integrations by parts, sliced in `θ` -/

theorem sliceZibpD_general : ∀ (u : ℝ → ℝ → ℝ),
    (∀ n : ℕ, ContDiffOn ℝ n (Function.uncurry u)
      (Set.Ioi 0 ×ˢ Set.Ioo 0 (Real.pi / 2))) →
    ∀ (χ : ℝ → ℝ), ContDiff ℝ 2 χ → HasCompactSupport χ →
      (∃ δ : ℝ, 0 < δ ∧ ∀ z : ℝ, z ≤ δ → χ z = 0) →
      ∀ θ ∈ Set.Ioo (0 : ℝ) (Real.pi / 2),
        ((∫ z in Set.Ioi 0, Wcut χ z * z ^ 2 * Work.Spaces.pzIter 2 u z θ * u z θ)
            = (1 / 2) * (∫ z in Set.Ioi 0,
                  deriv (deriv (fun z => z ^ 2 * Wcut χ z)) z * (u z θ) ^ 2)
              - (∫ z in Set.Ioi 0, Wcut χ z * (z * Work.Spaces.pz u z θ) ^ 2))
        ∧ ((∫ z in Set.Ioi 0, Wcut χ z * (z * Work.Spaces.pz u z θ) * u z θ)
            = -(1 / 2) * (∫ z in Set.Ioi 0,
                deriv (fun z => z * Wcut χ z) z * (u z θ) ^ 2)) := by
  intro u hsm χ hχsm hχcpt hχ0 θ hθ
  obtain ⟨δ, hδpos, hχδ⟩ := hχ0
  obtain ⟨b, hb⟩ := hasCompactSupport_eventually_zero hχcpt
  -- the weight vanishes off `[δ, b]`
  have hsuppW : ∀ z, z ∉ Set.Icc δ b → Wcut χ z = 0 := by
    intro z hz
    have hχz : χ z = 0 := by
      rcases not_and_or.mp hz with h | h
      · exact hχδ z (le_of_lt (not_le.mp h))
      · exact hb z (le_of_lt (not_le.mp h))
    simp only [Wcut, hχz, zero_mul]
  set φ : ℝ → ℝ := fun z => u z θ with hφdef
  have hφsm : ContDiffOn ℝ 2 φ (Set.Ioi 0) := by
    have hSO : Work.FTS.EllipticEst.SmoothOpen u :=
      Work.FTS.EllipticEst.smoothOpen_of_forall hsm
    have h := contDiffOn_iff_forall_nat_le.mp (hSO.curry_z hθ) 2 le_top
    rw [hφdef]
    exact h
  have hσsm : ContDiffOn ℝ 2 (Wcut χ) (Set.Ioi 0) := by
    have hw : (fun z : ℝ => (Work.Spaces.w z) ^ 2)
        = fun z : ℝ => ((1 + z) ^ 2 / z ^ 2) ^ 2 := by
      funext z; rw [Work.Spaces.w]
    have hw2 : ContDiffOn ℝ 2 (fun z : ℝ => (Work.Spaces.w z) ^ 2) (Set.Ioi 0) := by
      rw [hw]
      have h1 : ContDiffOn ℝ 2 (fun z : ℝ => (1 + z) ^ 2 / z ^ 2) (Set.Ioi 0) := by
        refine ContDiffOn.div ?_ ?_ ?_
        · fun_prop
        · fun_prop
        · intro z hz; exact pow_ne_zero 2 (ne_of_gt hz)
      exact h1.pow 2
    exact ContDiffOn.mul hχsm.contDiffOn hw2
  -- continuity of the slices and their derivatives
  have hφc : ContinuousOn φ (Set.Ioi 0) := hφsm.continuousOn
  have hφd : ContinuousOn (fun z => deriv φ z) (Set.Ioi 0) :=
    (hφsm.deriv_of_isOpen (m := 1) isOpen_Ioi (by norm_num)).continuousOn
  have hφdd : ContinuousOn (fun z => deriv (deriv φ) z) (Set.Ioi 0) :=
    ((hφsm.deriv_of_isOpen (m := 1) isOpen_Ioi (by norm_num)).deriv_of_isOpen (m := 0)
      isOpen_Ioi (by norm_num)).continuousOn
  have hσc : ContinuousOn (Wcut χ) (Set.Ioi 0) := hσsm.continuousOn
  have hσz : ContDiffOn ℝ 2 (fun z => z ^ 2 * Wcut χ z) (Set.Ioi 0) :=
    (contDiffOn_id.pow 2).mul hσsm
  have hσzd : ContinuousOn (fun z => deriv (fun z => z ^ 2 * Wcut χ z) z) (Set.Ioi 0) :=
    (hσz.deriv_of_isOpen (m := 1) isOpen_Ioi (by norm_num)).continuousOn
  have hσzdd : ContinuousOn (fun z => deriv (deriv (fun z => z ^ 2 * Wcut χ z)) z)
      (Set.Ioi 0) :=
    ((hσz.deriv_of_isOpen (m := 1) isOpen_Ioi (by norm_num)).deriv_of_isOpen (m := 0)
      isOpen_Ioi (by norm_num)).continuousOn
  have hσz1 : ContDiffOn ℝ 2 (fun z => z * Wcut χ z) (Set.Ioi 0) :=
    contDiffOn_id.mul hσsm
  have hσz1d : ContinuousOn (fun z => deriv (fun z => z * Wcut χ z) z) (Set.Ioi 0) :=
    (hσz1.deriv_of_isOpen (m := 1) isOpen_Ioi (by norm_num)).continuousOn
  -- the slice derivatives, in `pz`-form
  have hpz : ∀ z : ℝ, Work.Spaces.pz u z θ = deriv φ z := fun z => rfl
  have hpz2 : ∀ z : ℝ, Work.Spaces.pzIter 2 u z θ = deriv (deriv φ) z := by
    intro z
    simp only [Work.Spaces.pzIter_succ, Work.Spaces.pzIter_zero, Work.Spaces.pz, hφdef]
  -- ## the integrability side conditions
  have hsuppZ2 : ∀ z, z ∉ Set.Icc δ b → (fun z => z ^ 2 * Wcut χ z) z = 0 :=
    fun z hz => by
      change z ^ 2 * Wcut χ z = 0
      rw [hsuppW z hz]; ring
  have hsuppZ1 : ∀ z, z ∉ Set.Icc δ b → (fun z => z * Wcut χ z) z = 0 :=
    fun z hz => by
      change z * Wcut χ z = 0
      rw [hsuppW z hz]; ring
  have hdZ2 : ∀ z, z ∉ Set.Icc δ b → deriv (fun z => z ^ 2 * Wcut χ z) z = 0 :=
    deriv_eq_zero_off hsuppZ2
  have hdZ2' : ∀ z, z ∉ Set.Icc δ b →
      deriv (deriv (fun z => z ^ 2 * Wcut χ z)) z = 0 :=
    deriv_deriv_eq_zero_off hsuppZ2
  have hdZ1 : ∀ z, z ∉ Set.Icc δ b → deriv (fun z => z * Wcut χ z) z = 0 :=
    deriv_eq_zero_off hsuppZ1
  have hi1 : MeasureTheory.IntegrableOn
      (fun z => z ^ 2 * Wcut χ z * φ z * deriv (deriv φ) z) (Set.Ioi 0) :=
    integrableOn_Ioi_of_support_subset_Icc hδpos
      (((continuousOn_id.pow 2).mul hσc).mul hφc |>.mul hφdd)
      (fun z hz => by rw [hsuppW z hz]; ring)
  have hi2 : MeasureTheory.IntegrableOn
      (fun z => deriv (fun z => z ^ 2 * Wcut χ z) z * φ z * deriv φ z) (Set.Ioi 0) :=
    integrableOn_Ioi_of_support_subset_Icc hδpos
      ((hσzd.mul hφc).mul hφd)
      (fun z hz => by rw [hdZ2 z hz]; ring)
  have hi3 : MeasureTheory.IntegrableOn
      (fun z => Wcut χ z * (z * deriv φ z) ^ 2) (Set.Ioi 0) :=
    integrableOn_Ioi_of_support_subset_Icc hδpos
      (hσc.mul ((continuousOn_id.mul hφd).pow 2))
      (fun z hz => by rw [hsuppW z hz]; ring)
  have hi4 : MeasureTheory.IntegrableOn
      (fun z => deriv (deriv (fun z => z ^ 2 * Wcut χ z)) z * (φ z) ^ 2) (Set.Ioi 0) :=
    integrableOn_Ioi_of_support_subset_Icc hδpos
      (hσzdd.mul (hφc.pow 2))
      (fun z hz => by rw [hdZ2' z hz]; ring)
  have hj1 : MeasureTheory.IntegrableOn
      (fun z => z * Wcut χ z * φ z * deriv φ z) (Set.Ioi 0) :=
    integrableOn_Ioi_of_support_subset_Icc hδpos
      (((continuousOn_id.mul hσc).mul hφc).mul hφd)
      (fun z hz => by rw [hsuppW z hz]; ring)
  have hj2 : MeasureTheory.IntegrableOn
      (fun z => deriv (fun z => z * Wcut χ z) z * (φ z) ^ 2) (Set.Ioi 0) :=
    integrableOn_Ioi_of_support_subset_Icc hδpos
      (hσz1d.mul (hφc.pow 2))
      (fun z hz => by rw [hdZ1 z hz]; ring)
  -- ## the boundary terms
  have hbd1 : Filter.Tendsto (fun z => z ^ 2 * Wcut χ z * φ z * deriv φ z)
      (nhdsWithin (0 : ℝ) (Set.Ioi 0)) (nhds 0) :=
    tendsto_nhdsGT_zero_of_support_subset_Icc hδpos
      (fun z hz => by rw [hsuppW z hz]; ring)
  have hbT1 : Filter.Tendsto (fun z => z ^ 2 * Wcut χ z * φ z * deriv φ z)
      Filter.atTop (nhds 0) :=
    tendsto_atTop_zero_of_support_subset_Icc (fun z hz => by rw [hsuppW z hz]; ring)
  have hbd2 : Filter.Tendsto
      (fun z => deriv (fun z => z ^ 2 * Wcut χ z) z * (φ z) ^ 2)
      (nhdsWithin (0 : ℝ) (Set.Ioi 0)) (nhds 0) :=
    tendsto_nhdsGT_zero_of_support_subset_Icc hδpos
      (fun z hz => by rw [hdZ2 z hz]; ring)
  have hbT2 : Filter.Tendsto (fun z => deriv (fun z => z ^ 2 * Wcut χ z) z * (φ z) ^ 2)
      Filter.atTop (nhds 0) :=
    tendsto_atTop_zero_of_support_subset_Icc (fun z hz => by rw [hdZ2 z hz]; ring)
  have hjd1 : Filter.Tendsto (fun z => z * Wcut χ z * (φ z) ^ 2)
      (nhdsWithin (0 : ℝ) (Set.Ioi 0)) (nhds 0) :=
    tendsto_nhdsGT_zero_of_support_subset_Icc hδpos
      (fun z hz => by rw [hsuppW z hz]; ring)
  have hjT1 : Filter.Tendsto (fun z => z * Wcut χ z * (φ z) ^ 2)
      Filter.atTop (nhds 0) :=
    tendsto_atTop_zero_of_support_subset_Icc (fun z hz => by rw [hsuppW z hz]; ring)
  -- ## the two identities of `remov`
  have hZZ := Work.FTS.EllipticEst.remov.ibpZZ (Wcut χ) φ hσsm hφsm hi1 hi2 hi3 hi4
    hbd1 hbT1 hbd2 hbT2
  have hZ := Work.FTS.EllipticEst.remov.ibpZ (Wcut χ) φ hσsm hφsm hj1 hj2 hjd1 hjT1
  constructor
  · -- the first identity, converted to the `pz`-form of the statement
    have e1 : (∫ z in Set.Ioi 0, Wcut χ z * z ^ 2 * Work.Spaces.pzIter 2 u z θ * u z θ)
        = ∫ z in Set.Ioi 0, Wcut χ z * z ^ 2 * deriv (deriv φ) z * φ z := by
      refine MeasureTheory.integral_congr_ae (Filter.Eventually.of_forall fun z => ?_)
      simp only [hpz2 z, hφdef]
    have e2 : (∫ z in Set.Ioi 0, Wcut χ z * (z * Work.Spaces.pz u z θ) ^ 2)
        = ∫ z in Set.Ioi 0, Wcut χ z * (z * deriv φ z) ^ 2 := by
      refine MeasureTheory.integral_congr_ae (Filter.Eventually.of_forall fun z => ?_)
      simp only [hpz z]
    have e3 : (∫ z in Set.Ioi 0, deriv (deriv (fun z => z ^ 2 * Wcut χ z)) z * (u z θ) ^ 2)
        = ∫ z in Set.Ioi 0, deriv (deriv (fun z => z ^ 2 * Wcut χ z)) z * (φ z) ^ 2 := by
      refine MeasureTheory.integral_congr_ae (Filter.Eventually.of_forall fun z => ?_)
      simp only [hφdef]
    rw [e1, e2, e3, hZZ]
  · have e1 : (∫ z in Set.Ioi 0, Wcut χ z * (z * Work.Spaces.pz u z θ) * u z θ)
        = ∫ z in Set.Ioi 0, Wcut χ z * (z * deriv φ z) * φ z := by
      refine MeasureTheory.integral_congr_ae (Filter.Eventually.of_forall fun z => ?_)
      simp only [hpz z, hφdef]
    have e2 : (∫ z in Set.Ioi 0, deriv (fun z => z * Wcut χ z) z * (u z θ) ^ 2)
        = ∫ z in Set.Ioi 0, deriv (fun z => z * Wcut χ z) z * (φ z) ^ 2 := by
      refine MeasureTheory.integral_congr_ae (Filter.Eventually.of_forall fun z => ?_)
      simp only [hφdef]
    rw [e1, e2, hZ]

end Work.FTS.EllipticEst.Dispatch
