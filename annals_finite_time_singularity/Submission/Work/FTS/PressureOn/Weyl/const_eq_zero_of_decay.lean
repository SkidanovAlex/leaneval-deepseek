import Mathlib.Algebra.Ring.IsFormallyReal
import Mathlib.Analysis.Calculus.ContDiff.Operations
import Mathlib.Analysis.Normed.Lp.MeasurableSpace
import Mathlib.LinearAlgebra.Trace
import Mathlib.MeasureTheory.Group.Integral
import Mathlib.MeasureTheory.Integral.Bochner.ContinuousLinearMap
import Mathlib.MeasureTheory.Measure.Haar.OfBasis
import Mathlib.Topology.UniformSpace.Uniformizable
import Submission.Work.FTS.PressureOn.Defs
import Submission.Work.FTS.PressureOn.integral_div_eq_zero_of_hasFDerivAt
import Submission.Work.FTS.PressureOn.Weyl.exists_smooth_compactSupport_integral_ne_zero
import Submission.Work.FTS.PressureOn.Weyl.tendsto_integral_mul_shift

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
private lemma hasCompactSupport_div {V : R3 → R3} (hV : HasCompactSupport V) :
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
      hasCompactSupport_div hψ0c
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
