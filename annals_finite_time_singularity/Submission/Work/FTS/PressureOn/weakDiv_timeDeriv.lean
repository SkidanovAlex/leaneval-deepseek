import Mathlib.Algebra.Ring.IsFormallyReal
import Mathlib.Analysis.Calculus.ContDiff.Defs
import Mathlib.Analysis.Calculus.ContDiff.Operations
import Mathlib.Analysis.Calculus.Deriv.Basic
import Mathlib.Analysis.Calculus.Deriv.Slope
import Mathlib.Analysis.Calculus.FDeriv.Mul
import Mathlib.Analysis.Calculus.Gradient.Basic
import Mathlib.Analysis.LocallyConvex.AbsConvexOpen
import Mathlib.Analysis.Normed.Lp.MeasurableSpace
import Mathlib.LinearAlgebra.FreeModule.PID
import Mathlib.LinearAlgebra.Trace
import Mathlib.MeasureTheory.Function.L1Space.Integrable
import Mathlib.MeasureTheory.Function.SpecialFunctions.Inner
import Mathlib.MeasureTheory.Function.StronglyMeasurable.Inner
import Mathlib.MeasureTheory.Group.Integral
import Mathlib.MeasureTheory.Integral.Bochner.Basic
import Mathlib.MeasureTheory.Integral.Bochner.ContinuousLinearMap
import Mathlib.MeasureTheory.Integral.DominatedConvergence
import Mathlib.MeasureTheory.Measure.Haar.OfBasis
import Mathlib.RingTheory.Flat.TorsionFree
import Mathlib.RingTheory.SimpleRing.Principal
import Mathlib.Topology.UniformSpace.Uniformizable
import Submission.Work.FTS.PressureOn.integral_div_eq_zero_of_hasFDerivAt
import Submission.Work.FTS.PressureOn.weakCurl.int2_integrable
import Submission.Work.FTS.StrongEps.E4R3.Apriori4Proofs.TransferDeriv.conv_shift_sq_integral_le
-- ===== merged: Submission.Work.FTS.PressureOn.PoissonAux.integrable_smul_newtonGrad =====
section

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

open MeasureTheory Set Metric
open scoped Topology

namespace Work.FTS.PressureOn.PoissonAux

/-- The pointwise size of the Newtonian gradient kernel: `‖∇N z‖ = (4π)⁻¹‖z‖⁻²`, valid also at
`z = 0` (where both sides vanish, using the convention `0⁻¹ = 0`). -/
private lemma newtonGrad_norm_eq (z : Work.FTS.PressureOn.R3) :
    ‖Work.FTS.PressureOn.newtonGrad z‖ = (4 * Real.pi)⁻¹ * (‖z‖ ^ 2)⁻¹ := by
  rw [Work.FTS.PressureOn.norm_newtonGrad]
  have hcore : (‖z‖ ^ 3)⁻¹ * ‖z‖ = (‖z‖ ^ 2)⁻¹ := by
    rcases eq_or_ne (‖z‖ : ℝ) 0 with h | h
    · rw [h]; norm_num
    · rw [show ‖z‖ ^ 3 = ‖z‖ ^ 2 * ‖z‖ by ring, mul_inv, mul_assoc, inv_mul_cancel₀ h, mul_one]
  calc (4 * Real.pi)⁻¹ * (‖z‖ ^ 3)⁻¹ * ‖z‖
      = (4 * Real.pi)⁻¹ * ((‖z‖ ^ 3)⁻¹ * ‖z‖) := by ring
    _ = (4 * Real.pi)⁻¹ * (‖z‖ ^ 2)⁻¹ := by rw [hcore]

theorem integrable_smul_newtonGrad {ψ : Work.FTS.PressureOn.R3 → ℝ} (hψ : Continuous ψ)
    (hψcs : HasCompactSupport ψ) (y : Work.FTS.PressureOn.R3) :
    MeasureTheory.Integrable (fun x : Work.FTS.PressureOn.R3 =>
      ψ x • Work.FTS.PressureOn.newtonGrad (x - y)) := by
  -- `ψ` is bounded and supported in a closed ball.
  obtain ⟨R, _hRpos, hR⟩ := hψcs.isCompact.isBounded.exists_pos_norm_le
  obtain ⟨C, hC⟩ := hψcs.exists_bound_of_continuous hψ
  have hCnn : 0 ≤ C := (norm_nonneg (ψ 0)).trans (hC 0)
  have hK : 0 ≤ (4 * Real.pi)⁻¹ := by positivity
  -- The elementary majorant is `‖x - y‖⁻²` on the ball of radius `R + ‖y‖` about `y`.
  have hbase : MeasureTheory.Integrable (fun z : Work.FTS.PressureOn.R3 =>
      (‖z‖ ^ 2)⁻¹ * (closedBall (0 : Work.FTS.PressureOn.R3) (R + ‖y‖)).indicator
        (fun _ => (1 : ℝ)) z) :=
    Work.FTS.PressureOn.integrable_inv_normSq_indicator_closedBall (R + ‖y‖)
  have hmp : MeasureTheory.MeasurePreserving (fun x : Work.FTS.PressureOn.R3 => x + (-y))
      MeasureTheory.volume MeasureTheory.volume :=
    MeasureTheory.measurePreserving_add_right MeasureTheory.volume (-y)
  have htrans := hmp.integrable_comp_of_integrable hbase
  have hmaj : MeasureTheory.Integrable (fun x : Work.FTS.PressureOn.R3 =>
      (4 * Real.pi)⁻¹ * C * ((‖x - y‖ ^ 2)⁻¹ *
        (closedBall (0 : Work.FTS.PressureOn.R3) (R + ‖y‖)).indicator
          (fun _ => (1 : ℝ)) (x - y))) := by
    have h := htrans.const_mul ((4 * Real.pi)⁻¹ * C)
    simpa only [Function.comp_apply, sub_eq_add_neg] using h
  refine hmaj.mono' ?_ ?_
  · -- measurability: `newtonGrad` is Borel (a rescaling of `z ↦ z` by `‖z‖⁻³`)
    have hng : Measurable (Work.FTS.PressureOn.newtonGrad :
        Work.FTS.PressureOn.R3 → Work.FTS.PressureOn.R3) := by
      change Measurable (fun z : Work.FTS.PressureOn.R3 =>
        -((4 * Real.pi)⁻¹ * (‖z‖ ^ (3 : ℕ))⁻¹) • z)
      measurability
    exact (hψ.measurable.smul (hng.comp (measurable_id.sub measurable_const))).aestronglyMeasurable
  · -- the pointwise comparison with the majorant
    filter_upwards with x
    by_cases hx : x ∈ closedBall (0 : Work.FTS.PressureOn.R3) R
    · have hxS : x - y ∈ closedBall (0 : Work.FTS.PressureOn.R3) (R + ‖y‖) := by
        rw [mem_closedBall, dist_zero_right] at hx ⊢
        calc ‖x - y‖ ≤ ‖x‖ + ‖y‖ := norm_sub_le x y
          _ ≤ R + ‖y‖ := by linarith
      rw [Set.indicator_of_mem hxS, mul_one, norm_smul]
      calc ‖ψ x‖ * ‖Work.FTS.PressureOn.newtonGrad (x - y)‖
          ≤ C * ((4 * Real.pi)⁻¹ * (‖x - y‖ ^ 2)⁻¹) :=
            mul_le_mul (hC x) (le_of_eq (newtonGrad_norm_eq _)) (norm_nonneg _) hCnn
        _ = (4 * Real.pi)⁻¹ * C * (‖x - y‖ ^ 2)⁻¹ := by ring
    · -- off the supporting ball `ψ` vanishes identically, and the majorant is nonnegative
      have hxts : x ∉ tsupport ψ := fun hmem => hx (by
        rw [mem_closedBall, dist_zero_right]
        exact hR x hmem)
      have hψx : ψ x = 0 := image_eq_zero_of_notMem_tsupport hxts
      rw [hψx, zero_smul, norm_zero]
      exact mul_nonneg (mul_nonneg hK hCnn) (mul_nonneg (by positivity)
        (Set.indicator_nonneg (fun _ _ => zero_le_one) _))

end Work.FTS.PressureOn.PoissonAux
end
-- ===== merged: Submission.Work.FTS.PressureOn.Weyl.const_eq_zero_of_decay =====
section

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

namespace Work.FTS.PressureOn.Weyl

open Filter MeasureTheory Set
open scoped Topology

local notation "R3" => Work.FTS.PressureOn.R3

/-! ## Auxiliary facts about the divergence and translations -/

/-- The divergence commutes with translations: `div (V (· - t)) x = div V (x - t)`. -/
private lemma div_comp_sub (V : R3 → R3) (t x : R3) :
    FiniteTimeSingularity.div (fun y => V (y - t)) x = FiniteTimeSingularity.div V (x - t) := by
  simp only [FiniteTimeSingularity.div]
  rw [fderiv_comp_sub]

/-- Off the topological support of `V`, the divergence of `V` vanishes: `V` is *locally* zero
there, hence so is its Fréchet derivative, hence so is the trace. -/
private lemma div_eq_zero_of_notMem_tsupport {V : R3 → R3} {x : R3} (hx : x ∉ tsupport V) :
    FiniteTimeSingularity.div V x = 0 := by
  have hopen : IsOpen (tsupport V)ᶜ := (isClosed_tsupport V).isOpen_compl
  have h2 : V =ᶠ[𝓝 x] 0 := by
    filter_upwards [hopen.mem_nhds hx] with y hy
    exact image_eq_zero_of_notMem_tsupport hy
  rw [FiniteTimeSingularity.div, h2.fderiv_eq]
  simp

/-- The divergence of a smooth field is continuous. -/
private lemma continuous_div (V : R3 → R3) (hV : ∀ n : ℕ, ContDiff ℝ n V) :
    Continuous (fun x => FiniteTimeSingularity.div V x) := by
  rw [funext (Work.FTS.PressureOn.div_eq_sum_single V)]
  fun_prop

/-- The divergence of a compactly supported field is compactly supported. -/
private lemma hasCompactSupport_div_prv {V : R3 → R3} (hV : HasCompactSupport V) :
    HasCompactSupport (fun x => FiniteTimeSingularity.div V x) := by
  refine HasCompactSupport.intro (K := tsupport V) hV (fun x hx => ?_)
  exact div_eq_zero_of_notMem_tsupport hx

/-! ## The main lemma -/

theorem const_eq_zero_of_decay
    (q : Work.FTS.PressureOn.R3 → ℝ)
    (Φ : Work.FTS.PressureOn.R3 → Work.FTS.PressureOn.R3)
    (hq : Continuous q) (hΦ : Continuous Φ)
    (hq0 : Filter.Tendsto q (Filter.cocompact Work.FTS.PressureOn.R3) (nhds 0))
    (hΦ0 : Filter.Tendsto Φ (Filter.cocompact Work.FTS.PressureOn.R3) (nhds 0))
    (c : Work.FTS.PressureOn.R3)
    (hc : ∀ ψ : Work.FTS.PressureOn.R3 → Work.FTS.PressureOn.R3,
      (∀ n : ℕ, ContDiff ℝ n ψ) → HasCompactSupport ψ →
      (∫ x, inner ℝ (Φ x) (ψ x)) + ∫ x, q x * FiniteTimeSingularity.div ψ x
        = inner ℝ c (∫ x, ψ x)) :
    c = 0 := by
  obtain ⟨φ, hφ, hφc, hφint⟩ := exists_smooth_compactSupport_integral_ne_zero
  -- the smooth compactly supported "bump" and the family of its translates, smeared onto `c`
  have hφt_cs : ∀ t : R3, HasCompactSupport (fun x : R3 => φ (x - t)) := fun t =>
    hφc.comp_homeomorph (Homeomorph.addRight (-t))
  have hcs : ∀ t : R3, HasCompactSupport (fun x : R3 => φ (x - t) • c) := fun t =>
    HasCompactSupport.intro (K := tsupport (fun x : R3 => φ (x - t))) (hφt_cs t)
      (fun x hx => by simp [image_eq_zero_of_notMem_tsupport hx])
  have hsmooth : ∀ t : R3, ∀ n : ℕ, ContDiff ℝ n (fun x : R3 => φ (x - t) • c) := fun t n =>
    ((hφ n).comp (contDiff_id.sub (contDiff_const (c := t)))).smul_const c
  have hψt_int : ∀ t : R3, (∫ x, φ (x - t) • c) = (∫ x, φ x) • c := by
    intro t
    rw [integral_smul_const (fun x => φ (x - t)) c, MeasureTheory.integral_sub_right_eq_self φ t]
  set K0 : ℝ := ∫ x, φ x with hK0def
  have hK0 : K0 ≠ 0 := by rw [hK0def]; exact hφint
  -- the weak identity evaluated on the translated tests
  have key : ∀ t : R3,
      inner ℝ c (K0 • c) = (∫ x, inner ℝ (Φ x) (φ (x - t) • c))
        + ∫ x, q x * FiniteTimeSingularity.div (fun y => φ (y - t) • c) x := by
    intro t
    have h := (hc (fun y => φ (y - t) • c) (hsmooth t) (hcs t)).symm
    rw [hψt_int t] at h
    exact h
  -- the two integral terms tend to `0` at infinity
  have hlim1 : Filter.Tendsto (fun t : R3 => ∫ x, inner ℝ (Φ x) (φ (x - t) • c))
      (Filter.cocompact R3) (nhds 0) := by
    have hcf : Continuous fun x : R3 => inner ℝ (Φ x) c :=
      Continuous.inner (𝕜 := ℝ) hΦ continuous_const
    have hcf0 : Filter.Tendsto (fun x : R3 => inner ℝ (Φ x) c) (Filter.cocompact R3) (nhds 0) := by
      have h := Filter.Tendsto.inner (𝕜 := ℝ) hΦ0
        (tendsto_const_nhds : Filter.Tendsto (fun _ : R3 => c) (Filter.cocompact R3) (nhds c))
      simpa using h
    have hmain := tendsto_integral_mul_shift (fun x : R3 => inner ℝ (Φ x) c) φ
      hcf hcf0 (hφ 0).continuous hφc
    refine Filter.Tendsto.congr' (Filter.Eventually.of_forall fun t => ?_) hmain
    exact MeasureTheory.integral_congr_ae (Filter.Eventually.of_forall fun x => by
      show inner ℝ (Φ x) c * φ (x - t) = inner ℝ (Φ x) (φ (x - t) • c)
      rw [real_inner_smul_right]; ring)
  have hlim2 : Filter.Tendsto
      (fun t : R3 => ∫ x, q x * FiniteTimeSingularity.div (fun y => φ (y - t) • c) x)
      (Filter.cocompact R3) (nhds 0) := by
    have hψ0c : HasCompactSupport (fun z : R3 => φ z • c) :=
      HasCompactSupport.intro (K := tsupport φ) hφc
        (fun x hx => by simp [image_eq_zero_of_notMem_tsupport hx])
    have hGcont : Continuous fun y : R3 => FiniteTimeSingularity.div (fun z => φ z • c) y :=
      continuous_div _ (fun n => (hφ n).smul_const c)
    have hGcs : HasCompactSupport fun y : R3 => FiniteTimeSingularity.div (fun z => φ z • c) y :=
      hasCompactSupport_div_prv hψ0c
    have hmain := tendsto_integral_mul_shift q
      (fun y : R3 => FiniteTimeSingularity.div (fun z => φ z • c) y) hq hq0 hGcont hGcs
    refine Filter.Tendsto.congr' (Filter.Eventually.of_forall fun t => ?_) hmain
    exact MeasureTheory.integral_congr_ae (Filter.Eventually.of_forall fun x => by
      show q x * FiniteTimeSingularity.div (fun z => φ z • c) (x - t)
        = q x * FiniteTimeSingularity.div (fun y => φ (y - t) • c) x
      rw [div_comp_sub (fun z => φ z • c) t x])
  -- conclusion
  have hlimsum : Filter.Tendsto
      (fun t : R3 => (∫ x, inner ℝ (Φ x) (φ (x - t) • c))
        + ∫ x, q x * FiniteTimeSingularity.div (fun y => φ (y - t) • c) x)
      (Filter.cocompact R3) (nhds 0) := by
    simpa using hlim1.add hlim2
  have hconst0 : Filter.Tendsto (fun _ : R3 => inner ℝ c (K0 • c))
      (Filter.cocompact R3) (nhds 0) :=
    Filter.Tendsto.congr' (Filter.Eventually.of_forall fun t => (key t).symm) hlimsum
  have hconst1 : Filter.Tendsto (fun _ : R3 => inner ℝ c (K0 • c))
      (Filter.cocompact R3) (nhds (inner ℝ c (K0 • c))) := tendsto_const_nhds
  have hzero : inner ℝ c (K0 • c) = 0 := (tendsto_nhds_unique hconst0 hconst1).symm
  rw [real_inner_smul_right, real_inner_self_eq_norm_sq] at hzero
  rcases mul_eq_zero.mp hzero with h | h
  · exact absurd h hK0
  · exact norm_eq_zero.mp ((pow_eq_zero_iff (by norm_num : (2 : ℕ) ≠ 0)).mp h)

end Work.FTS.PressureOn.Weyl
end
-- ===== merged: Submission.Work.FTS.PressureOn.hasDerivAt_pressurePotential_time_of_continuous =====
section

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

open FiniteTimeSingularity Set MeasureTheory Metric Filter
open scoped Topology

set_option autoImplicit false

namespace Work.FTS.PressureOn

/-- `∇Nfund` is Borel measurable (it is `(4π)⁻¹‖z‖⁻³ • z`). -/
theorem measurable_nablaNfund : Measurable (nablaNfund : R3 → R3) := by
  have h1 : Measurable fun z : R3 => ((4 * Real.pi)⁻¹ * (‖z‖ ^ (3 : ℕ))⁻¹ : ℝ) :=
    measurable_const.mul ((continuous_norm.pow 3).measurable.inv)
  have h2 : Measurable fun z : R3 => z := measurable_id
  exact h1.smul h2

/-- The slice integrand `y ↦ ⟪∇Nfund (x - y), f y s⟫` is a.e. strongly measurable as soon as `f`
is jointly continuous. -/
theorem aestronglyMeasurable_kernel_inner {f : R3 → ℝ → R3}
    (hcont : Continuous fun p : R3 × ℝ => f p.1 p.2) (x : R3) (s : ℝ) :
    AEStronglyMeasurable (fun y => inner ℝ (nablaNfund (x - y)) (f y s)) volume := by
  have hk : Measurable fun y : R3 => nablaNfund (x - y) :=
    measurable_nablaNfund.comp ((continuous_const.sub continuous_id)).measurable
  have hf : Measurable fun y : R3 => f y s :=
    (hcont.comp (continuous_id.prodMk continuous_const)).measurable
  exact (hk.inner hf).aemeasurable.aestronglyMeasurable

/-- **The missing integrability, from joint continuity.**  If `f` is jointly continuous and its
slices are supported in a fixed ball, then the slices are integrable against the kernel `∇Nfund`. -/
theorem integrable_kernel_inner_of_continuous {f : R3 → ℝ → R3} {x : R3} {t : ℝ}
    (hcont : Continuous fun p : R3 × ℝ => f p.1 p.2)
    (hsupp : ∃ R, ∀ s ∈ Set.Ioo (t - 1) (t + 1), ∀ y, f y s ≠ 0 → ‖y‖ ≤ R) :
    ∀ s ∈ Set.Ioo (t - 1) (t + 1),
      Integrable (fun y => inner ℝ (nablaNfund (x - y)) (f y s)) volume := by
  obtain ⟨R, hR⟩ := hsupp
  -- a uniform bound for `‖f y s‖` on the compact `closedBall 0 R × Icc (t-1) (t+1)`
  have hK : IsCompact (closedBall (0 : R3) R ×ˢ Icc (t - 1) (t + 1)) :=
    (isCompact_closedBall (0 : R3) R).prod isCompact_Icc
  obtain ⟨B, hB⟩ := (hK.image hcont).isBounded.exists_norm_le
  have hB' : ∀ y ∈ closedBall (0 : R3) R, ∀ s ∈ Icc (t - 1) (t + 1), ‖f y s‖ ≤ B := by
    intro y hy s hs
    exact hB _ (Set.mem_image_of_mem (fun p : R3 × ℝ => f p.1 p.2) (show (y, s) ∈
      closedBall (0 : R3) R ×ˢ Icc (t - 1) (t + 1) from ⟨hy, hs⟩))
  intro s hsS
  have hsI : s ∈ Icc (t - 1) (t + 1) := ⟨hsS.1.le, hsS.2.le⟩
  refine Integrable.mono' (integrable_indicator_kernelWeight (R := R) (C := B) x)
    (aestronglyMeasurable_kernel_inner hcont x s) ?_
  refine ae_of_all _ (fun y => ?_)
  by_cases hy : y ∈ closedBall (0 : R3) R
  · have hby : (closedBall (0 : R3) R).indicator (fun y => B * ‖nablaNfund (x - y)‖) y
        = B * ‖nablaNfund (x - y)‖ := Set.indicator_of_mem hy _
    rw [hby]
    calc ‖inner ℝ (nablaNfund (x - y)) (f y s)‖
        ≤ ‖nablaNfund (x - y)‖ * ‖f y s‖ := norm_inner_le_norm _ _
      _ ≤ ‖nablaNfund (x - y)‖ * B :=
          mul_le_mul_of_nonneg_left (hB' y hy s hsI) (norm_nonneg _)
      _ = B * ‖nablaNfund (x - y)‖ := by ring
  · have hy' : R < ‖y‖ := by
      rw [mem_closedBall, dist_eq_norm, sub_zero] at hy
      exact not_le.mp hy
    have hfs : f y s = 0 := by
      by_contra hne
      exact not_le.mpr hy' (hR s hsS y hne)
    have hby : (closedBall (0 : R3) R).indicator (fun y => B * ‖nablaNfund (x - y)‖) y = 0 :=
      Set.indicator_of_notMem hy _
    rw [hby, hfs, inner_zero_right, norm_zero]

/-- **The requested lemma, with the regularity hypothesis that makes it true**: `f` jointly
continuous and supported in a fixed ball (uniformly in time near `t`).  Both extra hypotheses are
automatic for the Lamb vector of a compactly supported physical solution, and *one* of them is
genuinely necessary -- see `refute_hasDerivAt_pressurePotential_time.lean`. -/
theorem hasDerivAt_pressurePotential_time_of_continuous {f : R3 → ℝ → R3} {x : R3} {t : ℝ}
    (hcont : Continuous fun p : R3 × ℝ => f p.1 p.2)
    (hsupp : ∃ R, ∀ s ∈ Set.Ioo (t - 1) (t + 1), ∀ y, f y s ≠ 0 → ‖y‖ ≤ R)
    (hlip : ∃ C, ∀ y, ∀ s ∈ Set.Ioo (t - 1) (t + 1), ‖f y s - f y t‖ ≤ C * |s - t|)
    (hderiv : ∀ y, HasDerivAt (f y) (FiniteTimeSingularity.timeDeriv f y t) t) :
    HasDerivAt (fun s => pressurePotential (f · s) x)
      (-∫ y, inner ℝ (nablaNfund (x - y)) (FiniteTimeSingularity.timeDeriv f y t)) t :=
  hasDerivAt_pressurePotential_time_of_integrable hsupp hlip hderiv
    (integrable_kernel_inner_of_continuous hcont hsupp)

end Work.FTS.PressureOn
end
-- ===== merged: Submission.Work.FTS.PressureOn.weakDiv_timeDeriv =====
section

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

/-!
# `weakDiv_timeDeriv` — the divergence-free condition survives time differentiation

For a velocity field `u` whose spatial slices `u · s` are `C¹` and divergence-free for `s ≥ t` close
to `t`, and which has a one-sided time derivative `∂ₜu(·,t)` at `t` with a Lipschitz-in-time
domination, the pairing of `∂ₜu(·,t)` against the gradient of a compactly supported smooth test
function `φ` vanishes:

`∫ x, ⟪∂ₜu(x,t), ∇φ(x)⟫ = 0`.

The proof has two halves:

* the **integration by parts** half, resting on the divergence theorem in `ℝ³` for a compactly
  supported `C¹` field (`integral_div_eq_zero_of_hasFDerivAt`).  Applied to `φ • v` it gives the
  identity `∫ ⟪∇φ, v⟫ = -∫ (div v) φ`; with `div v = 0` the slice pairing
  `s ↦ ∫ x, ⟪u(x,s), ∇φ(x)⟫` vanishes identically on `[t, t+ε)`
  (`integral_inner_gradient_eq_zero` below);
* the **differentiation under the integral sign** half (`tendsto_integral_slope_self` below), a
  fixed-filter dominated convergence theorem: as `s ↓ t` the integrals of the slopes
  `(s - t)⁻¹ • (u x s - u x t)` converge to the integral of `∂ₜu(·,t)`.

The slopes are the difference quotients of the slice pairing, which is eventually `0`; hence the
limit — the pairing of `∂ₜu(·,t)` against `∇φ` — is `0`.
-/

open MeasureTheory Filter Set Topology
open FiniteTimeSingularity

namespace Work.FTS.PressureOn

set_option maxHeartbeats 4000000

/-- **The divergence of a scalar multiple of a divergence-free field.**  The product rule for the
trace of the Jacobian, `div (φ • v) x = φ x * div v x + (fderiv ℝ φ x) (v x)`, combined with the
identification of `fderiv ℝ φ x (v x)` with `⟪∇φ x, v x⟫`. -/
lemma div_smul_eq_inner_gradient (φ : R3 → ℝ) (v : R3 → R3) (x : R3)
    (hφ : DifferentiableAt ℝ φ x) (hv : DifferentiableAt ℝ v x) (hdiv : div v = 0) :
    div (φ • v) x = inner ℝ (gradient φ x) (v x) := by
  have hsmul := fderiv_smul (𝕜 := ℝ) hφ hv
  have htrace : div (φ • v) x = φ x * div v x + fderiv ℝ φ x (v x) := by
    rw [div, div, hsmul]
    rw [ContinuousLinearMap.toLinearMap_add, ContinuousLinearMap.toLinearMap_smul,
      ContinuousLinearMap.coe_smulRight]
    rw [map_add, map_smul, LinearMap.trace_smulRight, ContinuousLinearMap.coe_coe]
    ring
  rw [htrace, hdiv, Pi.zero_apply, mul_zero, zero_add, ← inner_gradient_left]

/-- An inner product whose **left** factor is compactly supported is compactly supported. -/
lemma hasCompactSupport_inner_left (w : R3 → R3) (hwcs : HasCompactSupport w) (g : R3 → R3) :
    HasCompactSupport (fun x => inner ℝ (w x) (g x)) := by
  refine HasCompactSupport.of_support_subset_isCompact hwcs ?_
  intro x hx
  rw [Function.mem_support] at hx
  exact subset_tsupport _ (by
    rw [Function.mem_support]
    intro h0
    exact hx (by simp [h0]))

/-- An inner product whose **right** factor is compactly supported is compactly supported. -/
lemma hasCompactSupport_inner_right (w : R3 → R3) (hwcs : HasCompactSupport w) (g : R3 → R3) :
    HasCompactSupport (fun x => inner ℝ (g x) (w x)) := by
  refine HasCompactSupport.of_support_subset_isCompact hwcs ?_
  intro x hx
  rw [Function.mem_support] at hx
  exact subset_tsupport _ (by
    rw [Function.mem_support]
    intro h0
    exact hx (by simp [h0]))

/-- **Integration by parts / weak divergence**: for a `C¹` divergence-free field `v` and a compactly
supported smooth test function `φ`, `∫ x, ⟪v x, ∇φ x⟫ = 0`.

Proof: put `G := φ • v`.  Then `G` is `C¹` with compact support, `div G = ⟪∇φ, v⟫`, and the
divergence theorem gives `∫ div G = 0`. -/
lemma integral_inner_gradient_eq_zero {v : R3 → R3} {φ : R3 → ℝ}
    (hv : ContDiff ℝ 1 v) (hdiv : div v = 0)
    (hφ : ∀ n : ℕ, ContDiff ℝ n φ) (hφcs : HasCompactSupport φ) :
    ∫ x, inner ℝ (v x) (gradient φ x) = 0 := by
  have hφ1 : ContDiff ℝ 1 φ := hφ 1
  have hφd : Differentiable ℝ φ := hφ1.differentiable (by norm_num)
  have hvd : Differentiable ℝ v := hv.differentiable (by norm_num)
  have hgradcont : Continuous (fun x => gradient φ x) := by
    have h : Continuous fun x => (InnerProductSpace.toDual ℝ R3).symm (fderiv ℝ φ x) :=
      (InnerProductSpace.toDual ℝ R3).symm.continuous.comp (hφ1.continuous_fderiv (by norm_num))
    simpa [gradient, Function.comp_def] using h
  have hgradcs : HasCompactSupport (fun x => gradient φ x) := by
    have h := (hφcs.fderiv ℝ).comp_left
      (g := fun L : R3 →L[ℝ] ℝ => (InnerProductSpace.toDual ℝ R3).symm L) (by simp)
    simpa [gradient, Function.comp_def] using h
  have hGcs : HasCompactSupport (φ • v) := hφcs.smul_right
  have hGcont : Continuous (φ • v) := hφ1.continuous.smul hv.continuous
  have hGdiff : ∀ x, HasFDerivAt (φ • v) (fderiv ℝ (φ • v) x) x := fun x =>
    (hφd.differentiableAt.smul hvd.differentiableAt).hasFDerivAt
  have hdivG : div (φ • v) = fun x => inner ℝ (gradient φ x) (v x) := by
    funext x
    exact div_smul_eq_inner_gradient φ v x hφd.differentiableAt hvd.differentiableAt hdiv
  have hGint : Integrable (div (φ • v)) := by
    rw [hdivG]
    exact (hgradcont.inner hv.continuous).integrable_of_hasCompactSupport
      (hasCompactSupport_inner_left _ hgradcs v)
  have h0 := integral_div_eq_zero_of_hasFDerivAt (φ • v) hGcs hGcont hGdiff hGint
  have hthis : (∫ x, inner ℝ (gradient φ x) (v x)) = 0 := by simpa [hdivG] using h0
  rw [← hthis]
  refine integral_congr_ae ?_
  filter_upwards with x
  rw [real_inner_comm (v x) (gradient φ x)]

/-- **Differentiation under the integral sign from the right.**  For a field `u` with

* a one-sided time derivative `∂ₜu(·,t)` at `t` (`hderiv`),
* a Lipschitz-in-time domination at `t` (`hlip`),
* slices continuous along `s ↓ t` (`hu`),

and a continuous compactly supported weight `w`, the integrals of the slopes `(s - t)⁻¹ • (u·s - u·t)`
against `w` converge, as `s ↓ t`, to the integral of `∂ₜu(·,t)` against `w`.

The proof is the dominated convergence theorem along the filter `𝓝[>] t`, with dominating function
`C ‖w‖` (the Lipschitz constant times the weight).  The measurability of the `t`-slice — the only
delicate point, since `u · t` is only known to be the pointwise limit of the continuous slices
`u · (t + η/(n+2))` — is obtained from that limit. -/
lemma tendsto_integral_slope_self {u : R3 → ℝ → R3} {t : ℝ} {w : R3 → R3}
    (hwcont : Continuous w) (hwcs : HasCompactSupport w)
    (hu : Filter.Eventually (fun s => Continuous (fun x => u x s)) (nhdsWithin t (Set.Ioi t)))
    (hderiv : ∀ x, HasDerivWithinAt (u x) (timeDeriv u x t) (Set.Ici t) t)
    (hlip : ∃ C, ∀ x, ∀ s ∈ Set.Ioo (t - 1) (t + 1), ‖u x s - u x t‖ ≤ C * |s - t|) :
    Filter.Tendsto (fun s => ∫ x, inner ℝ ((s - t)⁻¹ • (u x s - u x t)) (w x))
      (nhdsWithin t (Set.Ioi t)) (nhds (∫ x, inner ℝ (timeDeriv u x t) (w x))) := by
  obtain ⟨C, hC⟩ := hlip
  -- The `t`-slice is a.e. strongly measurable: it is the pointwise limit of the continuous slices
  -- `u · (t + η/(n+2))` along the right neighbourhood given by `hu`.
  have hmeas_t : AEStronglyMeasurable (fun x => u x t) volume := by
    rw [Filter.eventually_iff, Metric.mem_nhdsWithin_iff] at hu
    obtain ⟨δ, hδpos, hδ⟩ := hu
    set η : ℝ := min δ 1 with hη
    have hηpos : 0 < η := lt_min hδpos zero_lt_one
    have hηδ : η ≤ δ := min_le_left _ _
    have hη1 : η ≤ 1 := min_le_right _ _
    have hcont_n : ∀ n : ℕ, Continuous (fun x => u x (t + η / ((n : ℝ) + 2))) := by
      intro n
      have hpos : (0 : ℝ) < (n : ℝ) + 2 := by positivity
      have hlt : η / ((n : ℝ) + 2) < η := by
        have h1 : 1 < (n : ℝ) + 2 := by
          have : (0 : ℝ) ≤ (n : ℝ) := Nat.cast_nonneg n
          linarith
        exact div_lt_self hηpos h1
      have hsmall : η / ((n : ℝ) + 2) < δ := lt_of_lt_of_le hlt hηδ
      refine hδ ⟨?_, ?_⟩
      · rw [Metric.mem_ball, Real.dist_eq,
          show t + η / ((n : ℝ) + 2) - t = η / ((n : ℝ) + 2) by ring,
          abs_of_pos (div_pos hηpos hpos)]
        exact hsmall
      · exact lt_add_of_pos_right t (div_pos hηpos hpos)
    refine (measurable_of_tendsto_metrizable (f := fun n x => u x (t + η / ((n : ℝ) + 2)))
      (fun n => (hcont_n n).measurable) ?_).aestronglyMeasurable
    rw [tendsto_pi_nhds]
    intro x
    rw [tendsto_iff_norm_sub_tendsto_zero]
    refine squeeze_zero (f := fun n : ℕ => ‖u x (t + η / ((n : ℝ) + 2)) - u x t‖)
      (g := fun n : ℕ => C * (η / ((n : ℝ) + 2))) (fun n => norm_nonneg _) (fun n => ?_) ?_
    · have hpos : (0 : ℝ) < (n : ℝ) + 2 := by positivity
      have hlt1 : η / ((n : ℝ) + 2) < 1 := by
        rw [div_lt_one hpos]
        have h2 : (2 : ℝ) ≤ (n : ℝ) + 2 := by
          have : (0 : ℝ) ≤ (n : ℝ) := Nat.cast_nonneg n
          linarith
        linarith
      have hmem : (t + η / ((n : ℝ) + 2)) ∈ Set.Ioo (t - 1) (t + 1) := by
        have := div_pos hηpos hpos
        constructor <;> linarith
      calc ‖u x (t + η / ((n : ℝ) + 2)) - u x t‖
          ≤ C * |t + η / ((n : ℝ) + 2) - t| := hC x _ hmem
        _ = C * (η / ((n : ℝ) + 2)) := by
            rw [show t + η / ((n : ℝ) + 2) - t = η / ((n : ℝ) + 2) by ring,
              abs_of_pos (div_pos hηpos hpos)]
    · have hdiv : Tendsto (fun n : ℕ => η / ((n : ℝ) + 2)) atTop (𝓝 0) :=
        tendsto_const_nhds.div_atTop
          (tendsto_atTop_add_const_right atTop 2 tendsto_natCast_atTop_atTop)
      simpa using hdiv.const_mul C
  -- Measurability of the integrands.
  have hmeas : ∀ᶠ s in nhdsWithin t (Set.Ioi t),
      AEStronglyMeasurable (fun x => inner ℝ ((s - t)⁻¹ • (u x s - u x t)) (w x)) volume := by
    filter_upwards [hu] with s hs
    have h1 : (fun x => inner ℝ ((s - t)⁻¹ • (u x s - u x t)) (w x))
        = (fun x => inner ℝ ((s - t)⁻¹ • u x s - (s - t)⁻¹ • u x t) (w x)) := by
      funext x; rw [smul_sub]
    rw [h1]
    exact AEStronglyMeasurable.inner
      ((hs.const_smul ((s - t)⁻¹)).aestronglyMeasurable.sub
        (hmeas_t.const_smul ((s - t)⁻¹))) hwcont.aestronglyMeasurable
  -- Domination by `C ‖w‖`.
  have hbound : ∀ᶠ s in nhdsWithin t (Set.Ioi t),
      ∀ᵐ x ∂volume, ‖inner ℝ ((s - t)⁻¹ • (u x s - u x t)) (w x)‖ ≤ C * ‖w x‖ := by
    rw [Filter.eventually_iff, Metric.mem_nhdsWithin_iff]
    refine ⟨1, one_pos, ?_⟩
    rintro s ⟨hs, hst⟩
    simp only [Set.mem_ofPred_eq]
    have hst' : t < s := hst
    have hsI : s ∈ Set.Ioo (t - 1) (t + 1) := by
      rw [Metric.mem_ball, Real.dist_eq] at hs
      constructor <;> linarith [(abs_lt.mp hs).1, (abs_lt.mp hs).2]
    have h0 : 0 < |s - t| := abs_pos.mpr (by linarith)
    filter_upwards with x
    calc ‖inner ℝ ((s - t)⁻¹ • (u x s - u x t)) (w x)‖
        ≤ ‖(s - t)⁻¹ • (u x s - u x t)‖ * ‖w x‖ := norm_inner_le_norm _ _
      _ = |s - t|⁻¹ * ‖u x s - u x t‖ * ‖w x‖ := by
          rw [norm_smul, Real.norm_eq_abs, abs_inv]
      _ ≤ |s - t|⁻¹ * (C * |s - t|) * ‖w x‖ := by
          gcongr
          exact hC x s hsI
      _ = C * ‖w x‖ := by
          rw [mul_comm C |s - t|, ← mul_assoc, inv_mul_cancel₀ (abs_ne_zero.mpr (by linarith)),
            one_mul]
  -- Pointwise convergence of the slopes to the one-sided time derivative.
  have hpt : ∀ᵐ x ∂volume, Tendsto (fun s => inner ℝ ((s - t)⁻¹ • (u x s - u x t)) (w x))
      (nhdsWithin t (Set.Ioi t)) (nhds (inner ℝ (timeDeriv u x t) (w x))) := by
    refine Filter.Eventually.of_forall (fun x => ?_)
    have hslope : Tendsto (fun s => slope (u x) t s) (nhdsWithin t (Set.Ioi t))
        (nhds (timeDeriv u x t)) := by
      have h := hasDerivWithinAt_iff_tendsto_slope.mp (hderiv x)
      rwa [show Set.Ici t \ {t} = Set.Ioi t from by
        ext y; simp [Set.mem_Ioi, lt_iff_le_and_ne]] at h
    have hc : Tendsto (fun _ : ℝ => w x) (nhdsWithin t (Set.Ioi t)) (nhds (w x)) :=
      tendsto_const_nhds
    have h2 := Filter.Tendsto.inner (𝕜 := ℝ) hslope hc
    simpa [slope, Function.comp_def] using h2
  have hbndint : Integrable (fun x => C * ‖w x‖) volume :=
    (hwcont.norm.integrable_of_hasCompactSupport hwcs.norm).const_mul C
  exact tendsto_integral_filter_of_dominated_convergence (fun x => C * ‖w x‖)
    hmeas hbound hbndint hpt

theorem weakDiv_timeDeriv {u : R3 → ℝ → R3} {t : ℝ} {φ : R3 → ℝ}
    (hφ : ∀ n : ℕ, ContDiff ℝ n φ) (hφcs : HasCompactSupport φ)
    (hnbhd : ∀ᶠ s in nhdsWithin t (Set.Ici t),
      ContDiff ℝ 1 (u · s) ∧ FiniteTimeSingularity.div (u · s) = 0)
    (hderiv : ∀ x, HasDerivWithinAt (u x) (FiniteTimeSingularity.timeDeriv u x t) (Set.Ici t) t)
    (hlip : ∃ C, ∀ x, ∀ s ∈ Set.Ioo (t - 1) (t + 1), ‖u x s - u x t‖ ≤ C * |s - t|) :
    ∫ x, inner ℝ (FiniteTimeSingularity.timeDeriv u x t) (gradient φ x) = 0 := by
  have hgradcont : Continuous (fun x => gradient φ x) := by
    have h : Continuous fun x => (InnerProductSpace.toDual ℝ R3).symm (fderiv ℝ φ x) :=
      (InnerProductSpace.toDual ℝ R3).symm.continuous.comp
        ((hφ 1).continuous_fderiv (by norm_num))
    simpa [gradient, Function.comp_def] using h
  have hgradcs : HasCompactSupport (fun x => gradient φ x) := by
    have h := (hφcs.fderiv ℝ).comp_left
      (g := fun L : R3 →L[ℝ] ℝ => (InnerProductSpace.toDual ℝ R3).symm L) (by simp)
    simpa [gradient, Function.comp_def] using h
  -- The right-neighbourhood on which the slices are `C¹` and divergence-free.
  rw [Filter.eventually_iff, Metric.mem_nhdsWithin_iff] at hnbhd
  obtain ⟨ε, hεpos, hε⟩ := hnbhd
  have hnb : ∀ s, dist s t < ε → t ≤ s →
      ContDiff ℝ 1 (fun x => u x s) ∧ div (fun x => u x s) = 0 :=
    fun s hs hts => hε ⟨hs, hts⟩
  -- The slice pairing vanishes on `[t, t+ε)`.
  have hA0 : ∀ s, t ≤ s → s < t + ε → (∫ x, inner ℝ (u x s) (gradient φ x)) = 0 := by
    intro s hts hs
    have hd : dist s t < ε := by
      rw [Real.dist_eq, abs_of_nonneg (sub_nonneg.mpr hts)]
      linarith
    obtain ⟨hc, hd0⟩ := hnb s hd hts
    exact integral_inner_gradient_eq_zero hc hd0 hφ hφcs
  -- The slices stay continuous along `s ↓ t`.
  have hu : ∀ᶠ s in nhdsWithin t (Set.Ioi t), Continuous (fun x => u x s) := by
    rw [Filter.eventually_iff, Metric.mem_nhdsWithin_iff]
    refine ⟨ε, hεpos, ?_⟩
    rintro s ⟨hs, hst⟩
    exact ((hnb s hs (le_of_lt hst)).1).continuous
  have hlim := tendsto_integral_slope_self hgradcont hgradcs hu hderiv hlip
  -- Rewrite the difference quotients as integrals of the slopes.
  have hquot : ∀ᶠ s in nhdsWithin t (Set.Ioi t),
      (∫ x, inner ℝ ((s - t)⁻¹ • (u x s - u x t)) (gradient φ x))
        = ((∫ x, inner ℝ (u x s) (gradient φ x))
            - (∫ x, inner ℝ (u x t) (gradient φ x))) / (s - t) := by
    rw [Filter.eventually_iff, Metric.mem_nhdsWithin_iff]
    refine ⟨ε, hεpos, ?_⟩
    rintro s ⟨hs, hst⟩
    simp only [Set.mem_ofPred_eq]
    have hts : t ≤ s := le_of_lt hst
    obtain ⟨hc, _⟩ := hnb s hs hts
    have hct : ContDiff ℝ 1 (fun x => u x t) :=
      (hnb t (by rw [dist_self]; exact hεpos) le_rfl).1
    have hIs : Integrable (fun x => inner ℝ (u x s) (gradient φ x)) :=
      (hc.continuous.inner hgradcont).integrable_of_hasCompactSupport
        (hasCompactSupport_inner_right _ hgradcs _)
    have hIt : Integrable (fun x => inner ℝ (u x t) (gradient φ x)) :=
      (hct.continuous.inner hgradcont).integrable_of_hasCompactSupport
        (hasCompactSupport_inner_right _ hgradcs _)
    have hsub : (∫ x, inner ℝ (u x s - u x t) (gradient φ x))
        = (∫ x, inner ℝ (u x s) (gradient φ x))
          - (∫ x, inner ℝ (u x t) (gradient φ x)) := by
      rw [← integral_sub hIs hIt]
      refine integral_congr_ae ?_
      filter_upwards with x
      rw [inner_sub_left]
    have hsmul : (∫ x, inner ℝ ((s - t)⁻¹ • (u x s - u x t)) (gradient φ x))
        = (s - t)⁻¹ * (∫ x, inner ℝ (u x s - u x t) (gradient φ x)) := by
      rw [← integral_const_mul]
      refine integral_congr_ae ?_
      filter_upwards with x
      rw [real_inner_smul_left]
    rw [hsmul, hsub, div_eq_inv_mul]
  -- The difference quotients are eventually zero.
  have hQ0 : ∀ᶠ s in nhdsWithin t (Set.Ioi t),
      ((∫ x, inner ℝ (u x s) (gradient φ x))
        - (∫ x, inner ℝ (u x t) (gradient φ x))) / (s - t) = 0 := by
    rw [Filter.eventually_iff, Metric.mem_nhdsWithin_iff]
    refine ⟨ε, hεpos, ?_⟩
    rintro s ⟨hs, hst⟩
    simp only [Set.mem_ofPred_eq]
    have hts : t ≤ s := le_of_lt hst
    have hd : dist s t < ε := hs
    have hse : s < t + ε := by
      rw [Real.dist_eq, abs_of_nonneg (sub_nonneg.mpr hts)] at hd
      linarith
    have h1 : (∫ x, inner ℝ (u x s) (gradient φ x)) = 0 := hA0 s hts hse
    have h2 : (∫ x, inner ℝ (u x t) (gradient φ x)) = 0 := hA0 t le_rfl (by linarith)
    rw [h1, h2, sub_zero, zero_div]
  have hQlim : Tendsto (fun s => ((∫ x, inner ℝ (u x s) (gradient φ x))
        - (∫ x, inner ℝ (u x t) (gradient φ x))) / (s - t))
      (nhdsWithin t (Set.Ioi t)) (nhds (∫ x, inner ℝ (timeDeriv u x t) (gradient φ x))) :=
    Tendsto.congr' hquot hlim
  have hQzero : Tendsto (fun s => ((∫ x, inner ℝ (u x s) (gradient φ x))
        - (∫ x, inner ℝ (u x t) (gradient φ x))) / (s - t))
      (nhdsWithin t (Set.Ioi t)) (nhds 0) :=
    Tendsto.congr' (hQ0.mono fun s hs => hs.symm) tendsto_const_nhds
  exact tendsto_nhds_unique hQlim hQzero

end Work.FTS.PressureOn
end
