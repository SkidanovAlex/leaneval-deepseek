/-
Work module for the Elgindi finite-time-singularity project.

# The sharp `σ`-weighted Hardy inequality on the open slice `(0, π/2)`

`sharpHardyOpenAux` proves, for `f` of class `C²` on the open interval `(0, π/2)` whose weighted
energies are finite,

  `(1+η)² ∫_{Iθ} f² sin(2θ)^{-(2+η)} ≤ ∫_{Iθ} (f')² sin(2θ)^{-η}`,

together with the integrability of `θ ↦ f θ² sin(2θ)^{-(2+η)}` on `Iθ`.  This is the sharp
Hardy inequality that the angular Agmon estimate `sliceAgmonOpenCore` needs; the constant
`(1+η)²` is sharp and cannot be improved.

The proof uses the completed-square identity `Work.FTS.EllipticEst.AeStepOneAux.HardyBdd.primPointwise`

  `(1+η)² f² sin(2θ)^{-(2+η)} ≤ (f')² sin(2θ)^{-η} - (hbDeriv f) θ`   on `(0, π/2)`,

where `hbDeriv f` is the explicit derivative of the flux
`hbPrim f θ = 2·hbA·cos(2θ)·f θ²·sin(2θ)^{-(1+η)}` (`hbA = (1+η)/2`).  Integrating over a
sub-interval `(a,b) ⊂ (0,π/2)` and applying the fundamental theorem of calculus gives

  `(1+η)² ∫_a^b f² sin(2θ)^{-(2+η)} ≤ ∫_a^b (f')² sin(2θ)^{-η} - hbPrim f b + hbPrim f a`.

The flux vanishes at both endpoints because
`hbPrim f θ = 2·hbA·cos(2θ)·(f θ² sin(2θ)^{-(1+η)})` and the last factor tends to `0` there by
hypothesis.  Letting `(a,b)` run over `(gapDelta n, π/2 - gapDelta n)` and using the
absolute-continuity/Monotone-convergence lemma `SliceAgmonAux.integrableOn_Ioo_of_le` gives both
the integrability of the singular weight and the sharp inequality.
-/
import Mathlib.Algebra.Order.Star.Real
import Mathlib.Analysis.LocallyConvex.AbsConvexOpen
import Mathlib.Analysis.Real.Pi.Bounds
import Mathlib.MeasureTheory.Integral.IntervalIntegral.FundThmCalculus
import Mathlib.Order.CompletePartialOrder
import Submission.Work.Spaces.Defs
import Submission.Work.FTS.EllipticEst.ThetaPoincareDefs
import Submission.Work.FTS.EllipticEst.Honest.Gap9Open
import Submission.Work.FTS.EllipticEst.AeStepOneAux.HardyBddDefs
import Submission.Work.FTS.EllipticEst.AeStepOneAux.HardyBdd.primDeriv
import Submission.Work.FTS.EllipticEst.AeStepOneAux.HardyBdd.primPointwise
import Submission.Work.EllipticEst.Core.i0Aux.SliceAgmonOpen.Defs
import Submission.Work.EllipticEst.Core.i0Aux.SliceAgmonOpen.tendsto_subinterval
import Submission.Work.EllipticEst.Core.i0Aux.SliceAgmonAux.integrableOn_Ioo_of_le

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

noncomputable section

open scoped Real Topology
open MeasureTheory Set Filter

namespace Work.EllipticEst.Core.i0Aux.SliceAgmonAux

open Work.FTS.EllipticEst.Honest (gapDelta gapDelta_pos)
open Work.FTS.EllipticEst.AeStepOneAux (hbA hbA_nonneg hbPrim hbDeriv hbPrim_def)
open Work.FTS.EllipticEst.AeStepOneAux.HardyBdd (primPointwise hbPrim_hasDerivAt)

/-- `gapDelta n = 1/(n+2) ≤ 1/2`. -/
private theorem gD_le_half (n : ℕ) : gapDelta n ≤ 1 / 2 := by
  rw [gapDelta]
  apply one_div_le_one_div_of_le (by norm_num : (0 : ℝ) < 2)
  have hn : (0 : ℝ) ≤ (n : ℝ) := Nat.cast_nonneg n
  linarith

/-- `gapDelta n → 0`. -/
private theorem gD_tendsto : Filter.Tendsto gapDelta Filter.atTop (nhds 0) := by
  have h : Filter.Tendsto (fun n : ℕ => ((n : ℝ) + 2)⁻¹) Filter.atTop (nhds 0) :=
    tendsto_inv_atTop_zero.comp
      (tendsto_atTop_add_const_right atTop (2 : ℝ) tendsto_natCast_atTop_atTop)
  have hfun : (fun n : ℕ => ((n : ℝ) + 2)⁻¹) = gapDelta := by
    funext n
    simp [gapDelta, one_div]
  rw [hfun] at h
  exact h

/-- `gapDelta n < π/2 - gapDelta n`. -/
private theorem gD_lt_gap (n : ℕ) : gapDelta n < Real.pi / 2 - gapDelta n := by
  have h1 := gD_le_half n
  have h2 : (1 : ℝ) < Real.pi / 2 := by linarith [Real.pi_gt_three]
  linarith

/-- The gap interval sits inside `(0, π/2)`. -/
private theorem gD_subset (n : ℕ) :
    Set.Ioo (gapDelta n) (Real.pi / 2 - gapDelta n) ⊆ Set.Ioo (0 : ℝ) (Real.pi / 2) :=
  fun x hx => ⟨lt_trans (gapDelta_pos n) hx.1,
    lt_trans hx.2 (by linarith [gapDelta_pos n])⟩

/-- `gapDelta n → 0⁺`. -/
private theorem tendsto_gD_within : Filter.Tendsto gapDelta Filter.atTop
    (nhdsWithin (0 : ℝ) (Set.Ioi 0)) := by
  rw [tendsto_nhdsWithin_iff]
  exact ⟨gD_tendsto, Eventually.of_forall (fun n => gapDelta_pos n)⟩

/-- `π/2 - gapDelta n → (π/2)⁻`. -/
private theorem tendsto_sub_gD_within :
    Filter.Tendsto (fun n : ℕ => Real.pi / 2 - gapDelta n) Filter.atTop
      (nhdsWithin (Real.pi / 2) (Set.Iio (Real.pi / 2))) := by
  rw [tendsto_nhdsWithin_iff]
  refine ⟨?_, Eventually.of_forall (fun n => by
    simp only [Set.mem_Iio]; linarith [gapDelta_pos n])⟩
  have h : Filter.Tendsto (fun n : ℕ => Real.pi / 2 - gapDelta n) Filter.atTop
      (nhds (Real.pi / 2 - 0)) := tendsto_const_nhds.sub gD_tendsto
  simpa using h

/-- **The sharp `σ`-weighted Hardy inequality** on the open interval, with the integrability of
the singular weight. -/
theorem sharpHardyOpenAux {f : ℝ → ℝ} (hf : ContDiffOn ℝ 2 f (Set.Ioo 0 (Real.pi / 2)))
    (hrate0 : Filter.Tendsto
      (fun θ : ℝ => (f θ) ^ 2 * (Real.sin (2 * θ)) ^ (-(1 + Work.Spaces.eta)))
      (nhdsWithin (0 : ℝ) (Set.Ioi 0)) (nhds 0))
    (hrate1 : Filter.Tendsto
      (fun θ : ℝ => (f θ) ^ 2 * (Real.sin (2 * θ)) ^ (-(1 + Work.Spaces.eta)))
      (nhdsWithin (Real.pi / 2) (Set.Iio (Real.pi / 2))) (nhds 0))
    (hA : MeasureTheory.IntegrableOn
      (fun θ : ℝ => (deriv f θ) ^ 2 * Work.FTS.EllipticEst.thEta θ) Work.Spaces.Iθ) :
    MeasureTheory.IntegrableOn
        (fun θ : ℝ => (f θ) ^ 2 * (Real.sin (2 * θ)) ^ (-(2 + Work.Spaces.eta)))
        Work.Spaces.Iθ
      ∧ (1 + Work.Spaces.eta) ^ 2
            * (∫ θ in Work.Spaces.Iθ,
                (f θ) ^ 2 * (Real.sin (2 * θ)) ^ (-(2 + Work.Spaces.eta)))
        ≤ (∫ θ in Work.Spaces.Iθ, (deriv f θ) ^ 2 * Work.FTS.EllipticEst.thEta θ) := by
  have hpi2 : (0 : ℝ) < Real.pi / 2 := by positivity
  have h1eta : (0 : ℝ) < 1 + Work.Spaces.eta := by linarith [Work.Spaces.eta_pos]
  have hcoef : (0 : ℝ) < (1 + Work.Spaces.eta) ^ 2 := pow_pos h1eta 2
  have hf1 : ContDiffOn ℝ 1 f (Set.Ioo 0 (Real.pi / 2)) := hf.of_le (by norm_num)
  have hT : Set.Ioo (0 : ℝ) (Real.pi / 2) ⊆ Work.Spaces.Iθ :=
    fun x hx => ⟨le_of_lt hx.1, le_of_lt hx.2⟩
  have hAoo : MeasureTheory.IntegrableOn
      (fun θ : ℝ => (deriv f θ) ^ 2 * Work.FTS.EllipticEst.thEta θ)
      (Set.Ioo 0 (Real.pi / 2)) := hA.mono_set hT
  -- ## standing facts about the integrand
  have hsinT : ContinuousOn (fun x : ℝ => Real.sin (2 * x)) (Set.Ioo 0 (Real.pi / 2)) :=
    (Real.continuous_sin.comp (continuous_const.mul continuous_id)).continuousOn
  have hg : ContinuousOn
      (fun x : ℝ => (f x) ^ 2 * (Real.sin (2 * x)) ^ (-(2 + Work.Spaces.eta)))
      (Set.Ioo 0 (Real.pi / 2)) :=
    (hf.continuousOn.pow 2).mul
      (hsinT.rpow_const (fun x hx => Or.inl (ne_of_gt (sin_two_pos hx))))
  have hnn : ∀ x ∈ Set.Ioo (0 : ℝ) (Real.pi / 2),
      0 ≤ (f x) ^ 2 * (Real.sin (2 * x)) ^ (-(2 + Work.Spaces.eta)) :=
    fun x hx => mul_nonneg (sq_nonneg _)
      (Real.rpow_nonneg (le_of_lt (sin_two_pos hx)) _)
  -- ## the pointwise inequality
  have hpt : ∀ θ ∈ Set.Ioo (0 : ℝ) (Real.pi / 2),
      (1 + Work.Spaces.eta) ^ 2 * ((f θ) ^ 2 * (Real.sin (2 * θ)) ^ (-(2 + Work.Spaces.eta)))
        ≤ (deriv f θ) ^ 2 * Work.FTS.EllipticEst.thEta θ - hbDeriv f θ :=
    fun θ hθ => primPointwise hf1 θ hθ
  -- ## the flux tends to `0` at both endpoints
  have hbp0 : Filter.Tendsto (hbPrim f) (nhdsWithin (0 : ℝ) (Set.Ioi 0)) (nhds 0) := by
    have hc : Filter.Tendsto
        (fun θ : ℝ => (2 * hbA) * ((f θ) ^ 2 * (Real.sin (2 * θ)) ^ (-(1 + Work.Spaces.eta))))
        (nhdsWithin (0 : ℝ) (Set.Ioi 0)) (nhds 0) := by
      simpa using hrate0.const_mul (2 * hbA)
    refine tendsto_zero_iff_norm_tendsto_zero.mpr ?_
    refine squeeze_zero' (Eventually.of_forall (fun θ => norm_nonneg _)) ?_ hc
    filter_upwards [Ioo_mem_nhdsGT hpi2] with θ hθ
    rw [Real.norm_eq_abs]
    have hs : 0 < Real.sin (2 * θ) :=
      Real.sin_pos_of_pos_of_lt_pi (by linarith [hθ.1]) (by linarith [hθ.2, Real.pi_pos])
    have hsnn : 0 ≤ (Real.sin (2 * θ)) ^ (-(1 + Work.Spaces.eta)) := Real.rpow_nonneg hs.le _
    have h2a : (0 : ℝ) ≤ 2 * hbA := by linarith [hbA_nonneg]
    have hrepr : |hbPrim f θ| = 2 * hbA * |Real.cos (2 * θ)| * (f θ) ^ 2
        * (Real.sin (2 * θ)) ^ (-(1 + Work.Spaces.eta)) := by
      rw [hbPrim_def, abs_mul, abs_mul, abs_mul, abs_of_nonneg h2a,
        abs_of_nonneg (sq_nonneg (f θ)), abs_of_nonneg hsnn]
    calc |hbPrim f θ|
        = 2 * hbA * |Real.cos (2 * θ)| * (f θ) ^ 2
            * (Real.sin (2 * θ)) ^ (-(1 + Work.Spaces.eta)) := hrepr
      _ ≤ 2 * hbA * 1 * (f θ) ^ 2 * (Real.sin (2 * θ)) ^ (-(1 + Work.Spaces.eta)) := by
          refine mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_right ?_ (sq_nonneg _)) hsnn
          exact mul_le_mul_of_nonneg_left (Real.abs_cos_le_one (2 * θ)) h2a
      _ = (2 * hbA) * ((f θ) ^ 2 * (Real.sin (2 * θ)) ^ (-(1 + Work.Spaces.eta))) := by ring
  have hbp1 : Filter.Tendsto (hbPrim f) (nhdsWithin (Real.pi / 2) (Set.Iio (Real.pi / 2)))
      (nhds 0) := by
    have hc : Filter.Tendsto
        (fun θ : ℝ => (2 * hbA) * ((f θ) ^ 2 * (Real.sin (2 * θ)) ^ (-(1 + Work.Spaces.eta))))
        (nhdsWithin (Real.pi / 2) (Set.Iio (Real.pi / 2))) (nhds 0) := by
      simpa using hrate1.const_mul (2 * hbA)
    refine tendsto_zero_iff_norm_tendsto_zero.mpr ?_
    refine squeeze_zero' (Eventually.of_forall (fun θ => norm_nonneg _)) ?_ hc
    filter_upwards [Ioo_mem_nhdsLT hpi2] with θ hθ
    rw [Real.norm_eq_abs]
    have hs : 0 < Real.sin (2 * θ) :=
      Real.sin_pos_of_pos_of_lt_pi (by linarith [hθ.1]) (by linarith [hθ.2, Real.pi_pos])
    have hsnn : 0 ≤ (Real.sin (2 * θ)) ^ (-(1 + Work.Spaces.eta)) := Real.rpow_nonneg hs.le _
    have h2a : (0 : ℝ) ≤ 2 * hbA := by linarith [hbA_nonneg]
    have hrepr : |hbPrim f θ| = 2 * hbA * |Real.cos (2 * θ)| * (f θ) ^ 2
        * (Real.sin (2 * θ)) ^ (-(1 + Work.Spaces.eta)) := by
      rw [hbPrim_def, abs_mul, abs_mul, abs_mul, abs_of_nonneg h2a,
        abs_of_nonneg (sq_nonneg (f θ)), abs_of_nonneg hsnn]
    calc |hbPrim f θ|
        = 2 * hbA * |Real.cos (2 * θ)| * (f θ) ^ 2
            * (Real.sin (2 * θ)) ^ (-(1 + Work.Spaces.eta)) := hrepr
      _ ≤ 2 * hbA * 1 * (f θ) ^ 2 * (Real.sin (2 * θ)) ^ (-(1 + Work.Spaces.eta)) := by
          refine mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_right ?_ (sq_nonneg _)) hsnn
          exact mul_le_mul_of_nonneg_left (Real.abs_cos_le_one (2 * θ)) h2a
      _ = (2 * hbA) * ((f θ) ^ 2 * (Real.sin (2 * θ)) ^ (-(1 + Work.Spaces.eta))) := by ring
  -- ## the sub-interval estimate
  have hbound : ∀ n : ℕ,
      (1 + Work.Spaces.eta) ^ 2
        * (∫ x in Set.Ioo (gapDelta n) (Real.pi / 2 - gapDelta n),
            (f x) ^ 2 * (Real.sin (2 * x)) ^ (-(2 + Work.Spaces.eta)))
      ≤ (∫ x in Set.Ioo (gapDelta n) (Real.pi / 2 - gapDelta n),
            (deriv f x) ^ 2 * Work.FTS.EllipticEst.thEta x)
        - hbPrim f (Real.pi / 2 - gapDelta n) + hbPrim f (gapDelta n) := by
    intro n
    have hle : gapDelta n ≤ Real.pi / 2 - gapDelta n := le_of_lt (gD_lt_gap n)
    have hmem : ∀ x ∈ Set.Icc (gapDelta n) (Real.pi / 2 - gapDelta n),
        x ∈ Set.Ioo (0 : ℝ) (Real.pi / 2) := fun x hx =>
      ⟨lt_of_lt_of_le (gapDelta_pos n) hx.1,
        lt_of_le_of_lt hx.2 (by linarith [gapDelta_pos n])⟩
    have hcontn : ContinuousOn
        (fun x : ℝ => (f x) ^ 2 * (Real.sin (2 * x)) ^ (-(2 + Work.Spaces.eta)))
        (Set.Icc (gapDelta n) (Real.pi / 2 - gapDelta n)) :=
      ((hf.continuousOn.mono hmem).pow 2).mul
        ((hsinT.mono hmem).rpow_const
          (fun x hx => Or.inl (ne_of_gt (sin_two_pos (hmem x hx)))))
    have hcontD : ContinuousOn (hbDeriv f)
        (Set.Icc (gapDelta n) (Real.pi / 2 - gapDelta n)) := by
      have hsin : ContinuousOn (fun x : ℝ => Real.sin (2 * x))
          (Set.Icc (gapDelta n) (Real.pi / 2 - gapDelta n)) :=
        (Real.continuous_sin.comp (continuous_const.mul continuous_id)).continuousOn
      have hcos : ContinuousOn (fun x : ℝ => Real.cos (2 * x))
          (Set.Icc (gapDelta n) (Real.pi / 2 - gapDelta n)) :=
        (Real.continuous_cos.comp (continuous_const.mul continuous_id)).continuousOn
      have hff : ContinuousOn f (Set.Icc (gapDelta n) (Real.pi / 2 - gapDelta n)) :=
        hf.continuousOn.mono hmem
      have hdd : ContinuousOn (deriv f)
          (Set.Icc (gapDelta n) (Real.pi / 2 - gapDelta n)) :=
        (hf.continuousOn_deriv_of_isOpen isOpen_Ioo (by norm_num)).mono hmem
      have hs1 : ContinuousOn (fun x : ℝ => (Real.sin (2 * x)) ^ (-(1 + Work.Spaces.eta)))
          (Set.Icc (gapDelta n) (Real.pi / 2 - gapDelta n)) :=
        hsin.rpow_const (fun x hx => Or.inl (ne_of_gt (sin_two_pos (hmem x hx))))
      have hs2 : ContinuousOn (fun x : ℝ => (Real.sin (2 * x)) ^ (-(2 + Work.Spaces.eta)))
          (Set.Icc (gapDelta n) (Real.pi / 2 - gapDelta n)) :=
        hsin.rpow_const (fun x hx => Or.inl (ne_of_gt (sin_two_pos (hmem x hx))))
      have hA1 : ContinuousOn (fun x : ℝ => -4 * hbA * Real.sin (2 * x) * (f x) ^ 2
          * (Real.sin (2 * x)) ^ (-(1 + Work.Spaces.eta)))
          (Set.Icc (gapDelta n) (Real.pi / 2 - gapDelta n)) :=
        (((continuousOn_const.mul hsin).mul (hff.pow 2)).mul hs1)
      have hA2 : ContinuousOn (fun x : ℝ => 4 * hbA * Real.cos (2 * x) * (f x) * deriv f x
          * (Real.sin (2 * x)) ^ (-(1 + Work.Spaces.eta)))
          (Set.Icc (gapDelta n) (Real.pi / 2 - gapDelta n)) :=
        (((continuousOn_const.mul hcos).mul hff).mul hdd).mul hs1
      have hA3pos : ContinuousOn (fun x : ℝ => 4 * hbA * (1 + Work.Spaces.eta)
          * (Real.cos (2 * x)) ^ 2 * (f x) ^ 2
          * (Real.sin (2 * x)) ^ (-(2 + Work.Spaces.eta)))
          (Set.Icc (gapDelta n) (Real.pi / 2 - gapDelta n)) :=
        (((continuousOn_const.mul (hcos.pow 2)).mul (hff.pow 2)).mul hs2)
      have hA3 : ContinuousOn (fun x : ℝ => -(4 * hbA * (1 + Work.Spaces.eta)
          * (Real.cos (2 * x)) ^ 2 * (f x) ^ 2
          * (Real.sin (2 * x)) ^ (-(2 + Work.Spaces.eta))))
          (Set.Icc (gapDelta n) (Real.pi / 2 - gapDelta n)) := hA3pos.neg
      exact (hA1.add hA2).add hA3
    have hIg : MeasureTheory.IntegrableOn
        (fun x : ℝ => (f x) ^ 2 * (Real.sin (2 * x)) ^ (-(2 + Work.Spaces.eta)))
        (Set.Ioo (gapDelta n) (Real.pi / 2 - gapDelta n)) :=
      hcontn.integrableOn_Icc.mono_set Set.Ioo_subset_Icc_self
    have hIA : MeasureTheory.IntegrableOn
        (fun x : ℝ => (deriv f x) ^ 2 * Work.FTS.EllipticEst.thEta x)
        (Set.Ioo (gapDelta n) (Real.pi / 2 - gapDelta n)) :=
      hAoo.mono_set (gD_subset n)
    have hID : MeasureTheory.IntegrableOn (hbDeriv f)
        (Set.Ioo (gapDelta n) (Real.pi / 2 - gapDelta n)) :=
      hcontD.integrableOn_Icc.mono_set Set.Ioo_subset_Icc_self
    have hmono := MeasureTheory.setIntegral_mono_on
      (hf := hIg.const_mul ((1 + Work.Spaces.eta) ^ 2))
      (hg := hIA.sub hID) measurableSet_Ioo (fun x hx => hpt x (gD_subset n hx))
    have e1 : (∫ x in Set.Ioo (gapDelta n) (Real.pi / 2 - gapDelta n),
          (1 + Work.Spaces.eta) ^ 2
            * ((f x) ^ 2 * (Real.sin (2 * x)) ^ (-(2 + Work.Spaces.eta))))
        = (1 + Work.Spaces.eta) ^ 2
          * (∫ x in Set.Ioo (gapDelta n) (Real.pi / 2 - gapDelta n),
              (f x) ^ 2 * (Real.sin (2 * x)) ^ (-(2 + Work.Spaces.eta))) :=
      MeasureTheory.integral_const_mul _ _
    have e2 : (∫ x in Set.Ioo (gapDelta n) (Real.pi / 2 - gapDelta n),
          ((fun x : ℝ => (deriv f x) ^ 2 * Work.FTS.EllipticEst.thEta x) - hbDeriv f) x)
        = (∫ x in Set.Ioo (gapDelta n) (Real.pi / 2 - gapDelta n),
            (deriv f x) ^ 2 * Work.FTS.EllipticEst.thEta x)
          - (∫ x in Set.Ioo (gapDelta n) (Real.pi / 2 - gapDelta n), hbDeriv f x) :=
      MeasureTheory.integral_sub hIA hID
    have e3 : (∫ x in Set.Ioo (gapDelta n) (Real.pi / 2 - gapDelta n), hbDeriv f x)
        = hbPrim f (Real.pi / 2 - gapDelta n) - hbPrim f (gapDelta n) := by
      have hder : ∀ θ ∈ Set.uIcc (gapDelta n) (Real.pi / 2 - gapDelta n),
          HasDerivAt (hbPrim f) (hbDeriv f θ) θ := by
        intro θ hθ
        rw [Set.uIcc_of_le hle, Set.mem_Icc] at hθ
        exact hbPrim_hasDerivAt hf1 θ (hmem θ hθ)
      have hint : IntervalIntegrable (hbDeriv f) MeasureTheory.volume
          (gapDelta n) (Real.pi / 2 - gapDelta n) :=
        hcontD.intervalIntegrable_of_Icc hle
      have h1 : (∫ x in (gapDelta n)..(Real.pi / 2 - gapDelta n), hbDeriv f x)
          = hbPrim f (Real.pi / 2 - gapDelta n) - hbPrim f (gapDelta n) :=
        intervalIntegral.integral_eq_sub_of_hasDerivAt hder hint
      rw [intervalIntegral.integral_of_le hle, MeasureTheory.integral_Ioc_eq_integral_Ioo] at h1
      exact h1
    rw [e1, e2, e3] at hmono
    linarith [hmono]
  -- ## the limit of the sub-interval majorants
  have hL0 : Filter.Tendsto
      (fun n : ℕ => ∫ x in Set.Ioo (gapDelta n) (Real.pi / 2 - gapDelta n),
        (deriv f x) ^ 2 * Work.FTS.EllipticEst.thEta x)
      Filter.atTop
      (nhds (∫ x in Set.Ioo 0 (Real.pi / 2),
        (deriv f x) ^ 2 * Work.FTS.EllipticEst.thEta x)) :=
    SliceAgmonOpen.tendsto_subinterval hAoo tendsto_gD_within tendsto_sub_gD_within
      (Eventually.of_forall (fun n => gD_lt_gap n))
  have hLmain : Filter.Tendsto
      (fun n : ℕ => (∫ x in Set.Ioo (gapDelta n) (Real.pi / 2 - gapDelta n),
            (deriv f x) ^ 2 * Work.FTS.EllipticEst.thEta x)
          - hbPrim f (Real.pi / 2 - gapDelta n) + hbPrim f (gapDelta n))
      Filter.atTop
      (nhds (∫ x in Set.Ioo 0 (Real.pi / 2),
        (deriv f x) ^ 2 * Work.FTS.EllipticEst.thEta x)) := by
    have h := (hL0.sub (hbp1.comp tendsto_sub_gD_within)).add (hbp0.comp tendsto_gD_within)
    simpa using h
  have hL : Filter.Tendsto
      (fun n : ℕ => ((∫ x in Set.Ioo (gapDelta n) (Real.pi / 2 - gapDelta n),
            (deriv f x) ^ 2 * Work.FTS.EllipticEst.thEta x)
          - hbPrim f (Real.pi / 2 - gapDelta n) + hbPrim f (gapDelta n))
        / (1 + Work.Spaces.eta) ^ 2)
      Filter.atTop
      (nhds ((∫ x in Set.Ioo 0 (Real.pi / 2),
        (deriv f x) ^ 2 * Work.FTS.EllipticEst.thEta x) / (1 + Work.Spaces.eta) ^ 2)) := by
    have h := hLmain.mul_const ((1 + Work.Spaces.eta) ^ 2)⁻¹
    simpa [div_eq_mul_inv] using h
  -- ## the monotone-convergence step
  have hkey := integrableOn_Ioo_of_le (g := fun x : ℝ =>
        (f x) ^ 2 * (Real.sin (2 * x)) ^ (-(2 + Work.Spaces.eta)))
      (u := gapDelta) (v := fun n : ℕ => Real.pi / 2 - gapDelta n)
      (L := fun n : ℕ => ((∫ x in Set.Ioo (gapDelta n) (Real.pi / 2 - gapDelta n),
            (deriv f x) ^ 2 * Work.FTS.EllipticEst.thEta x)
          - hbPrim f (Real.pi / 2 - gapDelta n) + hbPrim f (gapDelta n))
        / (1 + Work.Spaces.eta) ^ 2)
      (C := (∫ x in Set.Ioo 0 (Real.pi / 2),
        (deriv f x) ^ 2 * Work.FTS.EllipticEst.thEta x) / (1 + Work.Spaces.eta) ^ 2)
      hg hnn tendsto_gD_within tendsto_sub_gD_within
      (Eventually.of_forall (fun n => gD_lt_gap n)) hL
      (fun n => by
        rw [le_div_iff₀ hcoef]
        calc (∫ x in Set.Ioo (gapDelta n) (Real.pi / 2 - gapDelta n),
              (f x) ^ 2 * (Real.sin (2 * x)) ^ (-(2 + Work.Spaces.eta)))
              * (1 + Work.Spaces.eta) ^ 2
            = (1 + Work.Spaces.eta) ^ 2
              * (∫ x in Set.Ioo (gapDelta n) (Real.pi / 2 - gapDelta n),
                  (f x) ^ 2 * (Real.sin (2 * x)) ^ (-(2 + Work.Spaces.eta))) := by ring
          _ ≤ (∫ x in Set.Ioo (gapDelta n) (Real.pi / 2 - gapDelta n),
                (deriv f x) ^ 2 * Work.FTS.EllipticEst.thEta x)
              - hbPrim f (Real.pi / 2 - gapDelta n) + hbPrim f (gapDelta n) := hbound n)
  -- ## converting back to `Iθ`
  have hcancel : (1 + Work.Spaces.eta) ^ 2
      * ((∫ x in Set.Ioo 0 (Real.pi / 2),
          (deriv f x) ^ 2 * Work.FTS.EllipticEst.thEta x) / (1 + Work.Spaces.eta) ^ 2)
      = (∫ x in Set.Ioo 0 (Real.pi / 2),
          (deriv f x) ^ 2 * Work.FTS.EllipticEst.thEta x) := by
    rw [mul_comm ((1 + Work.Spaces.eta) ^ 2)
      ((∫ x in Set.Ioo 0 (Real.pi / 2),
          (deriv f x) ^ 2 * Work.FTS.EllipticEst.thEta x) / (1 + Work.Spaces.eta) ^ 2)]
    exact div_mul_cancel₀ _ (ne_of_gt hcoef)
  have hmain : (1 + Work.Spaces.eta) ^ 2
      * (∫ x in Set.Ioo 0 (Real.pi / 2),
          (f x) ^ 2 * (Real.sin (2 * x)) ^ (-(2 + Work.Spaces.eta)))
      ≤ (∫ x in Set.Ioo 0 (Real.pi / 2),
          (deriv f x) ^ 2 * Work.FTS.EllipticEst.thEta x) := by
    have h := mul_le_mul_of_nonneg_left hkey.2 (le_of_lt hcoef)
    linarith [h, hcancel.le, hcancel.ge]
  have hIθint : MeasureTheory.IntegrableOn
      (fun x : ℝ => (f x) ^ 2 * (Real.sin (2 * x)) ^ (-(2 + Work.Spaces.eta)))
      Work.Spaces.Iθ :=
    hkey.1.mono_set_ae (by
      filter_upwards [MeasureTheory.Ioo_ae_eq_Icc (a := (0 : ℝ)) (b := Real.pi / 2)]
        with x hx
      intro hxI
      exact hx.mpr hxI)
  have hIθg : (∫ x in Work.Spaces.Iθ,
        (f x) ^ 2 * (Real.sin (2 * x)) ^ (-(2 + Work.Spaces.eta)))
      = (∫ x in Set.Ioo 0 (Real.pi / 2),
          (f x) ^ 2 * (Real.sin (2 * x)) ^ (-(2 + Work.Spaces.eta))) :=
    (MeasureTheory.setIntegral_congr_set MeasureTheory.Ioo_ae_eq_Icc).symm
  have hIθA : (∫ x in Work.Spaces.Iθ,
        (deriv f x) ^ 2 * Work.FTS.EllipticEst.thEta x)
      = (∫ x in Set.Ioo 0 (Real.pi / 2),
          (deriv f x) ^ 2 * Work.FTS.EllipticEst.thEta x) :=
    (MeasureTheory.setIntegral_congr_set MeasureTheory.Ioo_ae_eq_Icc).symm
  exact ⟨hIθint, by rw [hIθg, hIθA]; exact hmain⟩

end Work.EllipticEst.Core.i0Aux.SliceAgmonAux
