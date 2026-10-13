/-
Copyright: work module for the Elgindi finite-time singularity project.

# The endpoint-value reproducing formula for the test function `etaT`

`etaT t x = x (1 - x/t)^3` is the test function used for the endpoint-value estimate.  This file
proves the two-integration-by-parts reproducing formula

  `lim_{x → 0⁺} f x = ∫_0^t η_t f'' - ∫_0^t η_t'' f`

for `f` of class `C²` on a neighbourhood of `(0,t)` with `f` and `f''` integrable on `(0,t)`, `f'`
bounded on `(0,t)`.  The proof integrates by parts on `[ε,t]` (where `η_t(t) = η_t'(t) = 0` and
`η_t(0) = 0`, `η_t'(0) = 1`) and lets `ε ↓ 0`.
-/
import Mathlib.Analysis.Calculus.ContDiff.Deriv
import Mathlib.Analysis.LocallyConvex.AbsConvexOpen
import Mathlib.MeasureTheory.Integral.IntervalIntegral.IntegrationByParts
import Mathlib.Order.CompletePartialOrder
import Mathlib.Order.Interval.Basic
import Submission.Work.EllipticEst.Core.i0Aux.EndpointDefs
import Submission.Work.EllipticEst.Core.i0Aux.EndpointValues.etaTBasic

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

namespace Work.EllipticEst.Core.i0Aux.EndpointValues

open scoped Topology Interval
open Filter Set MeasureTheory

set_option autoImplicit false
-- `haveI` is genuinely needed below (to register `NeBot l` for `tendsto_nhds_unique`)
set_option linter.style.haveILetI false

/-- The set integral over `Ioo a b` is the interval integral over `a..b`. -/
theorem setIntegral_Ioo_eq_intervalIntegral (g : ℝ → ℝ) {a b : ℝ} (h : a ≤ b) :
    ∫ x in Ioo a b, g x = ∫ x in a..b, g x := by
  rw [setIntegral_congr_set (Ioo_ae_eq_Ioc (a := a) (b := b)),
    ← intervalIntegral.integral_of_le h]

/-- The interval integral over `ε..t` tends to the one over `0..t` as `ε ↓ 0`. -/
theorem tendsto_intervalIntegral_left (g : ℝ → ℝ) (t : ℝ) (ht : 0 < t)
    (hg : IntegrableOn g (Ioo 0 t)) :
    Tendsto (fun ε : ℝ => ∫ x in ε..t, g x) (nhdsWithin 0 (Ioi 0))
      (𝓝 (∫ x in (0 : ℝ)..t, g x)) := by
  have h_int : IntegrableOn g (uIcc 0 t) := by
    rw [uIcc_of_le ht.le]
    exact hg.congr_set_ae Ioo_ae_eq_Icc.symm
  have hcont : ContinuousOn (fun x : ℝ => ∫ s in x..t, g s) (uIcc 0 t) :=
    intervalIntegral.continuousOn_primitive_interval_left h_int
  have hmem : uIcc (0 : ℝ) t ∈ 𝓝[Ioi (0 : ℝ)] 0 := by
    rw [uIcc_of_le ht.le, mem_nhdsWithin_iff_exists_mem_nhds_inter]
    exact ⟨Iio t, isOpen_Iio.mem_nhds ht,
      fun x hx => ⟨le_of_lt hx.2, le_of_lt hx.1⟩⟩
  have hle : 𝓝[Ioi (0 : ℝ)] 0 ≤ 𝓝[uIcc (0 : ℝ) t] 0 := nhdsWithin_le_iff.mpr hmem
  exact (hcont.continuousWithinAt left_mem_uIcc).mono_left hle

/-- The two-integration-by-parts identity on `[ε,t]`, `0 < ε < t`. -/
theorem ibpEtaTEpsilon (f : ℝ → ℝ) (t ε : ℝ)
    (ht : 0 < t) (hta : t < Real.pi / 2) (hε : 0 < ε) (hεt : ε < t)
    (hf : ContDiffOn ℝ 2 f (Ioo 0 (Real.pi / 2))) :
    etaT' t ε * f ε
      = (∫ x in ε..t, etaT t x * deriv (deriv f) x)
        - (∫ x in ε..t, etaT'' t x * f x)
        + etaT t ε * deriv f ε := by
  have hsub : uIcc ε t ⊆ Ioo 0 (Real.pi / 2) := by
    rw [uIcc_of_le hεt.le]
    intro x hx
    exact ⟨lt_of_lt_of_le hε hx.1, lt_of_le_of_lt hx.2 hta⟩
  have hm1 : ContDiffOn ℝ 1 (deriv f) (Ioo 0 (Real.pi / 2)) :=
    hf.deriv_of_isOpen isOpen_Ioo (by norm_num)
  have hdη : ∀ x ∈ uIcc ε t, HasDerivAt (etaT t) (etaT' t x) x :=
    fun x _ => etaT_hasDerivAt t x
  have hdη' : ∀ x ∈ uIcc ε t, HasDerivAt (etaT' t) (etaT'' t x) x :=
    fun x _ => etaT'_hasDerivAt t x
  have hdf : ∀ x ∈ uIcc ε t, HasDerivAt f (deriv f x) x := fun x hx =>
    ((hf.contDiffAt (isOpen_Ioo.mem_nhds (hsub hx))).differentiableAt
      (by decide)).hasDerivAt
  have hdf' : ∀ x ∈ uIcc ε t, HasDerivAt (deriv f) (deriv (deriv f) x) x := fun x hx =>
    ((hm1.contDiffAt (isOpen_Ioo.mem_nhds (hsub hx))).differentiableAt
      (by decide)).hasDerivAt
  have hcont_df : ContinuousOn (deriv f) (uIcc ε t) :=
    (hf.continuousOn_deriv_of_isOpen isOpen_Ioo (by norm_num)).mono hsub
  have hcont_df' : ContinuousOn (deriv (deriv f)) (uIcc ε t) :=
    (hm1.continuousOn_deriv_of_isOpen isOpen_Ioo le_rfl).mono hsub
  have hint_df : IntervalIntegrable (deriv f) volume ε t := hcont_df.intervalIntegrable
  have hint_df' : IntervalIntegrable (deriv (deriv f)) volume ε t := hcont_df'.intervalIntegrable
  have hint_η' : IntervalIntegrable (etaT' t) volume ε t :=
    (continuous_etaT' t).continuousOn.intervalIntegrable
  have hint_η'' : IntervalIntegrable (etaT'' t) volume ε t :=
    (continuous_etaT'' t).continuousOn.intervalIntegrable
  have h₁ : ∫ x in ε..t, etaT t x * deriv (deriv f) x
      = etaT t t * deriv f t - etaT t ε * deriv f ε - ∫ x in ε..t, etaT' t x * deriv f x :=
    intervalIntegral.integral_mul_deriv_eq_deriv_mul hdη hdf' hint_η' hint_df'
  have h₂ : ∫ x in ε..t, etaT' t x * deriv f x
      = etaT' t t * f t - etaT' t ε * f ε - ∫ x in ε..t, etaT'' t x * f x :=
    intervalIntegral.integral_mul_deriv_eq_deriv_mul hdη' hdf hint_η'' hint_df
  rw [h₁, h₂, etaT_at_t t ht.ne', etaT'_at_t t ht.ne']
  ring

theorem twoIbpEtaT (f : ℝ → ℝ) (F t : ℝ)
    (ht : 0 < t) (hta : t < Real.pi / 2)
    (hf : ContDiffOn ℝ 2 f (Set.Ioo 0 (Real.pi / 2)))
    (hlim : Filter.Tendsto f (nhdsWithin (0 : ℝ) (Set.Ioi 0)) (nhds F))
    (hbdd : ∃ M, ∀ x ∈ Set.Ioo 0 t, |deriv f x| ≤ M)
    (h1 : MeasureTheory.IntegrableOn (fun x : ℝ => f x) (Set.Ioo 0 t))
    (h2 : MeasureTheory.IntegrableOn (fun x : ℝ => deriv (deriv f) x) (Set.Ioo 0 t)) :
    F = (∫ x in Set.Ioo 0 t, Work.EllipticEst.Core.i0Aux.etaT t x * deriv (deriv f) x)
      - ∫ x in Set.Ioo 0 t, Work.EllipticEst.Core.i0Aux.etaT'' t x * f x := by
  set l : Filter ℝ := nhdsWithin (0 : ℝ) (Ioi 0) with hl
  -- the two products are integrable on `(0,t)`
  have hintA : IntegrableOn (fun x : ℝ => etaT t x * deriv (deriv f) x) (Ioo 0 t) :=
    ((h2.congr_set_ae Ioo_ae_eq_Icc.symm).continuousOn_mul
      ((continuous_etaT t).continuousOn (s := Icc 0 t)) isCompact_Icc).mono_set Ioo_subset_Icc_self
  have hintB : IntegrableOn (fun x : ℝ => etaT'' t x * f x) (Ioo 0 t) :=
    ((h1.congr_set_ae Ioo_ae_eq_Icc.symm).continuousOn_mul
      ((continuous_etaT'' t).continuousOn (s := Icc 0 t)) isCompact_Icc).mono_set
      Ioo_subset_Icc_self
  -- `(0,t)` is an eventual neighbourhood of `0` for the one-sided filter
  have hev : ∀ᶠ ε : ℝ in l, ε ∈ Ioo 0 t := by
    rw [hl]
    filter_upwards [self_mem_nhdsWithin, nhdsWithin_le_nhds (isOpen_Iio.mem_nhds ht)]
      with ε hε hεt
    exact ⟨hε, hεt⟩
  -- the three limits of the right-hand side
  have hlimA : Tendsto (fun ε : ℝ => ∫ x in ε..t, etaT t x * deriv (deriv f) x) l
      (𝓝 (∫ x in (0 : ℝ)..t, etaT t x * deriv (deriv f) x)) :=
    tendsto_intervalIntegral_left _ t ht hintA
  have hlimB : Tendsto (fun ε : ℝ => ∫ x in ε..t, etaT'' t x * f x) l
      (𝓝 (∫ x in (0 : ℝ)..t, etaT'' t x * f x)) :=
    tendsto_intervalIntegral_left _ t ht hintB
  have hlimC : Tendsto (fun ε : ℝ => etaT t ε * deriv f ε) l (𝓝 0) := by
    have hη : Tendsto (fun ε : ℝ => etaT t ε) l (𝓝 0) := by
      have h0 := ((continuous_etaT t).continuousAt (x := 0)).tendsto
      rw [etaT_zero t] at h0
      exact h0.mono_left nhdsWithin_le_nhds
    refine hη.zero_mul_isBoundedUnder_le ?_
    obtain ⟨M, hM⟩ := hbdd
    exact ⟨M, hev.mono fun ε hε => by simpa [Real.norm_eq_abs] using hM ε hε⟩
  -- the limit of the left-hand side
  have hlimE : Tendsto (fun ε : ℝ => etaT' t ε * f ε) l (𝓝 F) := by
    have hderiv : Tendsto (fun ε : ℝ => etaT' t ε) l (𝓝 1) := by
      have h0 := ((continuous_etaT' t).continuousAt (x := 0)).tendsto
      rw [etaT'_zero t] at h0
      exact h0.mono_left nhdsWithin_le_nhds
    simpa [mul_comm] using hlim.mul hderiv
  -- the two sides agree eventually
  have heq : (fun ε : ℝ => etaT' t ε * f ε) =ᶠ[l]
      (fun ε : ℝ => (∫ x in ε..t, etaT t x * deriv (deriv f) x)
        - (∫ x in ε..t, etaT'' t x * f x) + etaT t ε * deriv f ε) := by
    filter_upwards [hev] with ε hε
    exact ibpEtaTEpsilon f t ε ht hta hε.1 hε.2 hf
  have hNeBot : NeBot l := by
    rw [hl, nhdsWithin_neBot]
    intro u hu
    rcases Metric.mem_nhds_iff.mp hu with ⟨δ, hδ, hsub⟩
    exact ⟨δ / 2,
      hsub (by
        rw [Metric.mem_ball, Real.dist_eq, sub_zero, abs_of_pos (half_pos hδ)]
        linarith),
      half_pos hδ⟩
  haveI := hNeBot
  have hR : Tendsto (fun ε : ℝ => (∫ x in ε..t, etaT t x * deriv (deriv f) x)
      - (∫ x in ε..t, etaT'' t x * f x) + etaT t ε * deriv f ε) l
      (𝓝 ((∫ x in (0 : ℝ)..t, etaT t x * deriv (deriv f) x)
        - (∫ x in (0 : ℝ)..t, etaT'' t x * f x) + 0)) := (hlimA.sub hlimB).add hlimC
  have huniq := tendsto_nhds_unique hlimE (hR.congr' heq.symm)
  rw [huniq]
  rw [setIntegral_Ioo_eq_intervalIntegral (fun x => etaT t x * deriv (deriv f) x) ht.le,
    setIntegral_Ioo_eq_intervalIntegral (fun x => etaT'' t x * f x) ht.le]
  ring

end Work.EllipticEst.Core.i0Aux.EndpointValues
