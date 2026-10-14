import Mathlib.Algebra.Order.Ring.Star
import Mathlib.Algebra.Order.Star.Real
import Mathlib.Algebra.Ring.IsFormallyReal
import Mathlib.Analysis.Calculus.ContDiff.Comp
import Mathlib.Analysis.Calculus.ContDiff.Defs
import Mathlib.Analysis.Calculus.ContDiff.Deriv
import Mathlib.Analysis.Calculus.ContDiff.Operations
import Mathlib.Analysis.Calculus.Deriv.Add
import Mathlib.Analysis.Calculus.Deriv.Basic
import Mathlib.Analysis.Calculus.Deriv.Inv
import Mathlib.Analysis.Calculus.Deriv.Mul
import Mathlib.Analysis.Calculus.Deriv.Pow
import Mathlib.Analysis.Calculus.Deriv.Prod
import Mathlib.Analysis.Calculus.FDeriv.Symmetric
import Mathlib.Analysis.Calculus.IteratedDeriv.Lemmas
import Mathlib.Analysis.Calculus.ParametricIntegral
import Mathlib.Analysis.Complex.Trigonometric
import Mathlib.Analysis.InnerProductSpace.Basic
import Mathlib.Analysis.LocallyConvex.AbsConvexOpen
import Mathlib.Analysis.Normed.Group.Continuity
import Mathlib.Analysis.Normed.Order.Lattice
import Mathlib.Analysis.Normed.Ring.Basic
import Mathlib.Analysis.ODE.ExistUnique
import Mathlib.Analysis.RCLike.Basic
import Mathlib.Analysis.Real.Pi.Bounds
import Mathlib.Analysis.Real.Sqrt
import Mathlib.Analysis.SpecialFunctions.Integrals.Basic
import Mathlib.Analysis.SpecialFunctions.Pow.Deriv
import Mathlib.Analysis.SpecialFunctions.Pow.Real
import Mathlib.Analysis.SpecialFunctions.Trigonometric.Basic
import Mathlib.Analysis.SpecialFunctions.Trigonometric.Deriv
import Mathlib.MeasureTheory.Function.L2Space
import Mathlib.MeasureTheory.Function.LocallyIntegrable
import Mathlib.MeasureTheory.Function.StronglyMeasurable.AEStronglyMeasurable
import Mathlib.MeasureTheory.Integral.Bochner.Basic
import Mathlib.MeasureTheory.Integral.Bochner.Set
import Mathlib.MeasureTheory.Integral.DominatedConvergence
import Mathlib.MeasureTheory.Integral.IntegrableOn
import Mathlib.MeasureTheory.Integral.IntegralEqImproper
import Mathlib.MeasureTheory.Integral.IntervalIntegral.Basic
import Mathlib.MeasureTheory.Integral.IntervalIntegral.ContDiff
import Mathlib.MeasureTheory.Integral.IntervalIntegral.FundThmCalculus
import Mathlib.MeasureTheory.Integral.MeanInequalities
import Mathlib.MeasureTheory.Integral.Prod
import Mathlib.MeasureTheory.Measure.Haar.OfBasis
import Mathlib.MeasureTheory.Measure.Lebesgue.Basic
import Mathlib.MeasureTheory.Order.Group.Lattice
import Mathlib.Order.CompletePartialOrder
import Mathlib.Order.Interval.Basic
import Mathlib.Topology.Algebra.Module.ModuleTopology
import Mathlib.Topology.Algebra.Ring.Real
import Submission.Work.FTS.PhiStar.Series.Weil.integrableOn_prod_mul
import Submission.Work.Spaces.sq_mul_div_rpow
import Submission.Work.Spaces.thD_reindex
-- ===== merged: Submission.Work.FTS.EllipticEst.integrable_prod_ae =====
section

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

namespace Work.FTS.EllipticEst

theorem integrable_prod_ae {α β : Type*} [MeasurableSpace α] [MeasurableSpace β]
    {μ : MeasureTheory.Measure α} {ν : MeasureTheory.Measure β}
    [MeasureTheory.SFinite μ] [MeasureTheory.SFinite ν] {G : α → β → ℝ}
    (hnn : ∀ᵐ a ∂μ, ∀ᵐ b ∂ν, 0 ≤ G a b)
    (hAE : MeasureTheory.AEStronglyMeasurable (Function.uncurry G) (μ.prod ν))
    (hslice : ∀ᵐ a ∂μ, MeasureTheory.Integrable (fun b => G a b) ν)
    (houter : MeasureTheory.Integrable (fun a => ∫ b, G a b ∂ν) μ) :
    MeasureTheory.Integrable (Function.uncurry G) (μ.prod ν) := by
  -- The converse direction of Fubini for products (`integrable_prod_iff`) asks for
  -- integrability of the *norm* iterated integral `a ↦ ∫ b, ‖G a b‖ ∂ν`. Almost
  -- everywhere nonnegativity makes it agree a.e. with the given signed iterated
  -- integral `a ↦ ∫ b, G a b ∂ν`, so it is integrable by `Integrable.congr`.
  refine (MeasureTheory.integrable_prod_iff hAE).2 ⟨hslice, ?_⟩
  refine houter.congr ?_
  filter_upwards [hnn] with a ha
  refine MeasureTheory.integral_congr_ae (ha.mono fun b hb => ?_)
  simp only [Function.uncurry_apply_pair, Real.norm_of_nonneg hb]

end Work.FTS.EllipticEst
end
-- ===== merged: Submission.Work.FTS.EllipticEst.remov.Ebs.abs_integral_mul_le_sqrt =====
section

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

namespace Work.FTS.EllipticEst.remov.Ebs

open MeasureTheory

/-- Cauchy–Schwarz (Bunyakovsky) in the `L²` form, written with square roots: for real functions
`u`, `v` that are square-integrable on a set `s`,
`|∫_s u v| ≤ √(∫_s u²) · √(∫_s v²)`.

The proof uses Hölder's inequality `MeasureTheory.integral_mul_norm_le_Lp_mul_Lq` with
`p = q = 2`, after bounding `|∫ u v| ≤ ∫ |u| |v|` and replacing `|u|²` by `u²` inside the
integrals. -/
theorem abs_integral_mul_le_sqrt {u v : ℝ → ℝ} {s : Set ℝ}
    (hu : MeasureTheory.MemLp u 2 (MeasureTheory.volume.restrict s))
    (hv : MeasureTheory.MemLp v 2 (MeasureTheory.volume.restrict s)) :
    |∫ x in s, u x * v x| ≤ Real.sqrt (∫ x in s, u x ^ 2) * Real.sqrt (∫ x in s, v x ^ 2) := by
  have h1 : |∫ x in s, u x * v x| ≤ ∫ x in s, |u x| * |v x| := by
    simpa only [Real.norm_eq_abs, abs_mul] using
      (MeasureTheory.norm_integral_le_integral_norm (μ := volume.restrict s)
        (f := fun x => u x * v x))
  have hu2 : MemLp u (ENNReal.ofReal (2 : ℝ)) (volume.restrict s) := by simpa using hu
  have hv2 : MemLp v (ENNReal.ofReal (2 : ℝ)) (volume.restrict s) := by simpa using hv
  have h2 : ∫ x in s, |u x| * |v x| ≤
      (∫ x in s, |u x| ^ (2 : ℝ)) ^ (1 / 2 : ℝ) *
        (∫ x in s, |v x| ^ (2 : ℝ)) ^ (1 / 2 : ℝ) := by
    simpa only [Real.norm_eq_abs] using
      (MeasureTheory.integral_mul_norm_le_Lp_mul_Lq (μ := volume.restrict s)
        (p := 2) (q := 2) (f := u) (g := v) (by norm_num [Real.holderConjugate_iff]) hu2 hv2)
  have hA : (∫ x in s, |u x| ^ (2 : ℝ)) = ∫ x in s, u x ^ 2 :=
    integral_congr_ae (Filter.Eventually.of_forall (fun x => by simpa using sq_abs (u x)))
  have hB : (∫ x in s, |v x| ^ (2 : ℝ)) = ∫ x in s, v x ^ 2 :=
    integral_congr_ae (Filter.Eventually.of_forall (fun x => by simpa using sq_abs (v x)))
  calc |∫ x in s, u x * v x| ≤ ∫ x in s, |u x| * |v x| := h1
    _ ≤ (∫ x in s, |u x| ^ (2 : ℝ)) ^ (1 / 2 : ℝ) *
          (∫ x in s, |v x| ^ (2 : ℝ)) ^ (1 / 2 : ℝ) := h2
    _ = Real.sqrt (∫ x in s, u x ^ 2) * Real.sqrt (∫ x in s, v x ^ 2) := by
        rw [hA, hB, ← Real.sqrt_eq_rpow, ← Real.sqrt_eq_rpow]

end Work.FTS.EllipticEst.remov.Ebs
end
-- ===== merged: Submission.Work.FTS.EllipticEst.remov.coerc.mul_sq_vanishing =====
section

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

namespace Work.FTS.EllipticEst.remov.coerc

/-- If `φ θ = O(θ)` as `θ → 0⁺`, `f²` is integrable near `0` and `φ θ * f θ` has a limit
`d` as `θ → 0⁺`, then `d = 0`.

Indeed, if `d ≠ 0` then `|φ θ * f θ| ≥ |d|/2` and `|φ θ| ≤ C θ` on a small interval
`(0, δ)`, so `(f θ)² ≥ k / θ²` there with `k = d²/(4C²) > 0`.  This contradicts the
integrability of `f²` on `(0, δ)` (via
`Work.FTS.EllipticEst.remov.coerc.inv_sq_lower_sq_not_integrable`). -/
theorem mul_sq_vanishing {f φ : ℝ → ℝ} {C d : ℝ} (hC : 0 < C)
    (hφ : ∀ᶠ θ in nhdsWithin (0 : ℝ) (Set.Ioi 0), |φ θ| ≤ C * θ)
    (hf : MeasureTheory.IntegrableOn (fun θ => (f θ) ^ 2) (Set.Ioo 0 1))
    (hw : Filter.Tendsto (fun θ => φ θ * f θ) (nhdsWithin (0 : ℝ) (Set.Ioi 0)) (nhds d)) :
    d = 0 := by
  by_contra hd
  set k : ℝ := d ^ 2 / (4 * C ^ 2) with hkdef
  have hkpos : 0 < k := by
    rw [hkdef]
    exact div_pos (sq_pos_of_ne_zero hd) (by positivity)
  -- Extract the two eventual bounds as explicit thresholds.
  have hφ' := hφ
  rw [eventually_nhdsWithin_iff] at hφ'
  rw [Metric.eventually_nhds_iff] at hφ'
  obtain ⟨ε₁, hε₁, hε₁'⟩ := hφ'
  have hw1 : ∀ᶠ θ in nhdsWithin (0 : ℝ) (Set.Ioi 0), |d| / 2 < |φ θ * f θ| :=
    hw.abs.eventually (Ioi_mem_nhds (by have := abs_pos.mpr hd; linarith))
  rw [eventually_nhdsWithin_iff] at hw1
  rw [Metric.eventually_nhds_iff] at hw1
  obtain ⟨ε₂, hε₂, hε₂'⟩ := hw1
  set ε : ℝ := min ε₁ (min ε₂ 1) with hεdef
  have hεle₁ : ε ≤ ε₁ := by rw [hεdef]; exact min_le_left _ _
  have hεle₂ : ε ≤ ε₂ := by rw [hεdef]; exact le_trans (min_le_right _ _) (min_le_left _ _)
  have hεle1 : ε ≤ 1 := by rw [hεdef]; exact le_trans (min_le_right _ _) (min_le_right _ _)
  have hεpos : 0 < ε := by rw [hεdef]; exact lt_min hε₁ (lt_min hε₂ one_pos)
  set δ : ℝ := ε / 2 with hδdef
  have hδpos : 0 < δ := by rw [hδdef]; linarith
  have hδltε : δ < ε := by rw [hδdef]; linarith
  have hδle1 : δ ≤ 1 := by rw [hδdef]; linarith
  -- The lower bound for `f²` on `(0, δ)`.
  have hlow : ∀ θ ∈ Set.Ioo (0 : ℝ) δ, k / θ ^ 2 ≤ (f θ) ^ 2 := by
    intro θ hθ
    have hθpos : 0 < θ := hθ.1
    have hθltε : θ < ε := lt_trans hθ.2 hδltε
    have hdist₁ : dist θ 0 < ε₁ := by
      rw [Real.dist_eq, sub_zero, abs_of_pos hθpos]; exact lt_of_lt_of_le hθltε hεle₁
    have hdist₂ : dist θ 0 < ε₂ := by
      rw [Real.dist_eq, sub_zero, abs_of_pos hθpos]; exact lt_of_lt_of_le hθltε hεle₂
    have hφb : |φ θ| ≤ C * θ := hε₁' hdist₁ hθpos
    have hprod : |d| / 2 < |φ θ * f θ| := hε₂' hdist₂ hθpos
    rw [abs_mul] at hprod
    have hd2pos : 0 < |d| / 2 := by have := abs_pos.mpr hd; linarith
    have hmul : 0 < |φ θ| * |f θ| := lt_trans hd2pos hprod
    have habsφ : 0 < |φ θ| := pos_of_mul_pos_left hmul (abs_nonneg _)
    have hCθpos : 0 < C * θ := lt_of_lt_of_le habsφ hφb
    have hstep1 : (|d| / 2) / (C * θ) ≤ (|d| / 2) / |φ θ| :=
      div_le_div_of_nonneg_left (by positivity) habsφ hφb
    have hstep2 : (|d| / 2) / |φ θ| < |f θ| := by
      have h := div_lt_div_of_pos_right hprod habsφ
      rwa [mul_div_cancel_left₀ (|f θ|) (ne_of_gt habsφ)] at h
    have hfz : (|d| / 2) / (C * θ) ≤ |f θ| := le_of_lt (lt_of_le_of_lt hstep1 hstep2)
    have hsq : ((|d| / 2) / (C * θ)) ^ 2 ≤ (f θ) ^ 2 := by
      have h0 : (0 : ℝ) ≤ (|d| / 2) / (C * θ) := div_nonneg (by positivity) hCθpos.le
      have h2 : ((|d| / 2) / (C * θ)) ^ 2 ≤ (|f θ|) ^ 2 := by
        rw [sq, sq]; exact mul_self_le_mul_self h0 hfz
      rwa [sq_abs] at h2
    have hsqeq : ((|d| / 2) / (C * θ)) ^ 2 = k / θ ^ 2 := by
      rw [hkdef]
      have habs : (|d| / 2) ^ 2 = d ^ 2 / 4 := by rw [div_pow, sq_abs]; norm_num
      rw [div_pow, mul_pow, habs, div_div, div_div]
      ring
    rw [← hsqeq]
    exact hsq
  have hfδ : MeasureTheory.IntegrableOn (fun θ => (f θ) ^ 2) (Set.Ioo 0 δ) :=
    hf.mono_set (fun θ hθ => ⟨hθ.1, lt_of_lt_of_le hθ.2 hδle1⟩)
  exact inv_sq_lower_sq_not_integrable hδpos hkpos hfδ hlow

end Work.FTS.EllipticEst.remov.coerc
end
-- ===== merged: Submission.Work.FTS.EllipticEst.remov.interval_integral_sq_le_mul =====
section

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

namespace Work.FTS.EllipticEst.remov

open MeasureTheory

/-- If two real functions agree on the open interval `Ioo a b`, then they are equal almost
everywhere for the Lebesgue measure restricted to `Ioc a b`: the two sets differ only by the
single point `b`. -/
lemma ae_eq_of_eq_on_Ioo {F G : ℝ → ℝ} {a b : ℝ} (h : ∀ x ∈ Set.Ioo a b, F x = G x) :
    F =ᵐ[volume.restrict (Set.Ioc a b)] G := by
  show ∀ᵐ x ∂(volume.restrict (Set.Ioc a b)), F x = G x
  rw [MeasureTheory.ae_restrict_iff' measurableSet_Ioc, MeasureTheory.ae_iff]
  refine MeasureTheory.measure_mono_null ?_ (Real.volume_singleton (a := b))
  intro x hx
  change ¬(x ∈ Set.Ioc a b → F x = G x) at hx
  obtain ⟨hxI, hxne⟩ := not_imp.mp hx
  rw [Set.mem_singleton_iff]
  by_contra hxb
  exact hxne (h x (by
    rw [Set.mem_Ioo]
    exact ⟨(Set.mem_Ioc.mp hxI).1, lt_of_le_of_ne (Set.mem_Ioc.mp hxI).2 hxb⟩))

/-- Weighted Cauchy–Schwarz (Bunyakovsky) inequality for interval integrals: if `σ > 0` on
`(a,b)` and both `f²σ` and `σ⁻¹` are integrable on `(a,b]`, then
`(∫_a^b f)² ≤ (∫_a^b f²σ)(∫_a^b σ⁻¹)`.

No measurability of `f` is assumed: the bound is obtained by writing `|f| = √(f²σ)·√(σ⁻¹)`,
which exhibits `f` as a product of two genuine `L²` functions, and applying Cauchy–Schwarz to
them; the sign of `f` is handled by `‖∫ f‖ ≤ ∫ ‖f‖`. -/
theorem interval_integral_sq_le_mul {f σ : ℝ → ℝ} {a b : ℝ} (hab : a ≤ b)
    (hσ : ∀ s ∈ Set.Ioo a b, 0 < σ s)
    (hf : MeasureTheory.IntegrableOn (fun s => (f s) ^ 2 * σ s) (Set.Ioc a b))
    (hσi : MeasureTheory.IntegrableOn (fun s => (σ s)⁻¹) (Set.Ioc a b)) :
    (∫ s in a..b, f s) ^ 2 ≤ (∫ s in a..b, (f s) ^ 2 * σ s) * (∫ s in a..b, (σ s)⁻¹) := by
  rw [intervalIntegral.integral_of_le hab, intervalIntegral.integral_of_le hab,
    intervalIntegral.integral_of_le hab]
  have haesm_u : AEStronglyMeasurable (fun x : ℝ => Real.sqrt ((f x) ^ 2 * σ x))
      (volume.restrict (Set.Ioc a b)) :=
    Real.continuous_sqrt.comp_aestronglyMeasurable hf.aestronglyMeasurable
  have haesm_v : AEStronglyMeasurable (fun x : ℝ => Real.sqrt ((σ x)⁻¹))
      (volume.restrict (Set.Ioc a b)) :=
    Real.continuous_sqrt.comp_aestronglyMeasurable hσi.aestronglyMeasurable
  have hsq_u : ∀ x ∈ Set.Ioo a b, (f x) ^ 2 * σ x = (Real.sqrt ((f x) ^ 2 * σ x)) ^ 2 :=
    fun x hx => (Real.sq_sqrt (mul_nonneg (sq_nonneg (f x)) (le_of_lt (hσ x hx)))).symm
  have hsq_v : ∀ x ∈ Set.Ioo a b, (σ x)⁻¹ = (Real.sqrt ((σ x)⁻¹)) ^ 2 :=
    fun x hx => (Real.sq_sqrt (inv_nonneg.mpr (le_of_lt (hσ x hx)))).symm
  have hmem_u : MemLp (fun x : ℝ => Real.sqrt ((f x) ^ 2 * σ x)) 2
      (volume.restrict (Set.Ioc a b)) :=
    (memLp_two_iff_integrable_sq haesm_u).mpr (hf.congr (ae_eq_of_eq_on_Ioo hsq_u))
  have hmem_v : MemLp (fun x : ℝ => Real.sqrt ((σ x)⁻¹)) 2 (volume.restrict (Set.Ioc a b)) :=
    (memLp_two_iff_integrable_sq haesm_v).mpr (hσi.congr (ae_eq_of_eq_on_Ioo hsq_v))
  have hI1 : (∫ x in Set.Ioc a b, Real.sqrt ((f x) ^ 2 * σ x) * Real.sqrt ((σ x)⁻¹))
      = ∫ x in Set.Ioc a b, |f x| :=
    integral_congr_ae (ae_eq_of_eq_on_Ioo (fun x hx => by
      have hxpos : 0 < σ x := hσ x hx
      rw [Real.sqrt_mul (sq_nonneg (f x)), Real.sqrt_sq_eq_abs, Real.sqrt_inv, mul_assoc,
        mul_inv_cancel₀ (ne_of_gt (Real.sqrt_pos.mpr hxpos)), mul_one]))
  have hI2 : (∫ x in Set.Ioc a b, (Real.sqrt ((f x) ^ 2 * σ x)) ^ 2)
      = ∫ x in Set.Ioc a b, (f x) ^ 2 * σ x :=
    integral_congr_ae (ae_eq_of_eq_on_Ioo (fun x hx => (hsq_u x hx).symm))
  have hI3 : (∫ x in Set.Ioc a b, (Real.sqrt ((σ x)⁻¹)) ^ 2)
      = ∫ x in Set.Ioc a b, (σ x)⁻¹ :=
    integral_congr_ae (ae_eq_of_eq_on_Ioo (fun x hx => (hsq_v x hx).symm))
  have hcs := Work.Spaces.cs_integral hmem_u hmem_v
  have hle : |∫ x in Set.Ioc a b, f x| ≤ ∫ x in Set.Ioc a b, |f x| := by
    simpa using MeasureTheory.norm_integral_le_integral_norm (fun x : ℝ => f x)
      (μ := volume.restrict (Set.Ioc a b))
  calc
    (∫ x in Set.Ioc a b, f x) ^ 2 = |∫ x in Set.Ioc a b, f x| ^ 2 := (sq_abs _).symm
    _ ≤ (∫ x in Set.Ioc a b, |f x|) ^ 2 := pow_le_pow_left₀ (abs_nonneg _) hle 2
    _ = (∫ x in Set.Ioc a b, Real.sqrt ((f x) ^ 2 * σ x) * Real.sqrt ((σ x)⁻¹)) ^ 2 := by
          rw [hI1]
    _ ≤ (∫ x in Set.Ioc a b, (Real.sqrt ((f x) ^ 2 * σ x)) ^ 2) *
          (∫ x in Set.Ioc a b, (Real.sqrt ((σ x)⁻¹)) ^ 2) := hcs
    _ = (∫ x in Set.Ioc a b, (f x) ^ 2 * σ x) * (∫ x in Set.Ioc a b, (σ x)⁻¹) := by
          rw [hI2, hI3]

end Work.FTS.EllipticEst.remov
end
-- ===== merged: Submission.Work.FTS.H2.Defs =====
section

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

noncomputable section

open scoped Real Topology
open MeasureTheory Set Filter

namespace Work.FTS.H2

set_option autoImplicit false

/-! ## The weights of the flat `ℋ⁴` pairing -/

/-- The weight `w(z)/√(sin(2θ)^η)` carried by the `D_z`-only summands (`i = 0`) of the
`ℋ⁴`-norm (paper (HkNorm): the first sum). -/
def Whz (z θ : ℝ) : ℝ := Spaces.w z / (Real.sin (2 * θ)) ^ (Spaces.eta / 2)

/-- The weight `W = w · w_θ` carried by the summands with at least one `θ`-derivative
(`i ≥ 1`) of the `ℋ⁴`-norm (paper (HkNorm): the second sum). -/
def Wm (α z θ : ℝ) : ℝ := Spaces.Wt α z θ

theorem Whz_eq (z θ : ℝ) : Whz z θ = Spaces.w z / (Real.sin (2 * θ)) ^ (Spaces.eta / 2) :=
  rfl

theorem Wm_eq (α z θ : ℝ) : Wm α z θ = Spaces.Wt α z θ := rfl

/-! ## The flat `ℋ⁴` pairing -/

/-- The integrand of the flat `ℋ⁴` pairing of the paper: the bilinear version of
`Spaces.HkIntegrand α 4`, i.e. the sum over the same finitely many weighted derivatives
of the products `D u · D v` in place of the squares `(D u)²`. -/
def H4PairInt (α : ℝ) (u v : ℝ → ℝ → ℝ) (z θ : ℝ) : ℝ :=
  (∑ i ∈ Finset.range 5,
      (Spaces.DzIter i u z θ * Whz z θ) * (Spaces.DzIter i v z θ * Whz z θ))
    + ∑ i ∈ Finset.range 5, ∑ j ∈ Finset.range 5,
        (if 1 ≤ i ∧ i + j ≤ 4 then
          (Spaces.mixed j i u z θ * Wm α z θ) * (Spaces.mixed j i v z θ * Wm α z θ)
        else 0)


/-! ## Elementary API -/





/-- The squared `ℋ⁴`-norm is the `ℋ⁴`-norm squared. -/
theorem HkNorm_sq (α : ℝ) (u : ℝ → ℝ → ℝ) :
    Spaces.HkNorm α 4 u ^ 2 = Spaces.HkSq α 4 u :=
  Real.sq_sqrt (Spaces.HkSq_nonneg α 4 u)

end Work.FTS.H2
end
end
-- ===== merged: Submission.Work.FTS.H2.RegQDefs =====
section

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

noncomputable section

open scoped Real Topology
open MeasureTheory Set Filter

namespace Work.FTS.H2

set_option autoImplicit false

/-- The supremum of `|g|` over the **open** quadrant `(0,∞) × (0,π/2)` — the `L^∞`-companion of
the interior regularity class `Work.FTS.Nonlin.RegQ`. -/
def supAbsO (g : ℝ → ℝ → ℝ) : ℝ :=
  sSup {y : ℝ | ∃ z : ℝ, 0 < z ∧ ∃ θ : ℝ, 0 < θ ∧ θ < π / 2 ∧ y = |g z θ|}

/-- `supAbsO` is attained at the point `(1,1)` in the sense of being an upper bound. -/
private theorem supAbsO_bddAbove {g : ℝ → ℝ → ℝ} {C : ℝ}
    (h : ∀ z θ, 0 < z → 0 < θ → θ < π / 2 → |g z θ| ≤ C) :
    BddAbove {y : ℝ | ∃ z : ℝ, 0 < z ∧ ∃ θ : ℝ, 0 < θ ∧ θ < π / 2 ∧ y = |g z θ|} :=
  ⟨C, by rintro y ⟨z, hz, θ, hθ, hθ', rfl⟩; exact h z θ hz hθ hθ'⟩

/-- The set defining `supAbsO` is nonempty. -/
private theorem supAbsO_nonempty : (1 : ℝ) < π / 2 := by
  have := Real.pi_gt_three; linarith

/-- Pointwise bound from `supAbsO`, inside the open quadrant. -/
theorem le_supAbsO {g : ℝ → ℝ → ℝ} {z θ C : ℝ} (hz : 0 < z) (hθ : 0 < θ) (hθ' : θ < π / 2)
    (h : ∀ z' θ', 0 < z' → 0 < θ' → θ' < π / 2 → |g z' θ'| ≤ C) : |g z θ| ≤ supAbsO g :=
  le_csSup (supAbsO_bddAbove h) ⟨z, hz, θ, hθ, hθ', rfl⟩

/-- Bound of `supAbsO` by a uniform bound on the open quadrant. -/
theorem supAbsO_le {g : ℝ → ℝ → ℝ} {C : ℝ}
    (h : ∀ z θ, 0 < z → 0 < θ → θ < π / 2 → |g z θ| ≤ C) : supAbsO g ≤ C :=
  csSup_le ⟨|g 1 1|, 1, one_pos, 1, one_pos, supAbsO_nonempty, rfl⟩
    (by rintro y ⟨z, hz, θ, hθ, hθ', rfl⟩; exact h z θ hz hθ hθ')


end Work.FTS.H2
end
end
-- ===== merged: Submission.Work.FTS.H2.T1HardWeightAlg =====
section

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

namespace Work.FTS.H2

/-- `rpow` algebra on a non-negative base, in the "positive half exponent" form used by the
`D_z`-slots: for `a ≥ 0` and arbitrary real `e`,
`(A·(W · a^{-e/2}))² = A²·(W²·a^{-e})`.

At `a = 0` both sides survive Lean's totalised `rpow`: for `e ≠ 0` we have
`0^{-e/2} = 0 = 0^{-e}` (`Real.zero_rpow`), while for `e = 0` both `0^{0}` factors are `1`.
For `a > 0` the identity is `sq_rpow_mul_two` (`(a^{-e/2})² = a^{(-e/2)·2} = a^{-e}`) followed
by `mul_pow`. -/
private lemma sq_mul_rpow_neg_half (A W a e : ℝ) (ha : 0 ≤ a) :
    (A * (W * a ^ (-(e / 2)))) ^ 2 = A ^ 2 * (W ^ 2 * a ^ (-e)) := by
  rcases eq_or_lt_of_le ha with h | h
  · subst h
    by_cases he : e = 0
    · subst he; simp only [neg_zero, zero_div, Real.rpow_zero, mul_one]; ring
    · have h1 : (0 : ℝ) ^ (-(e / 2)) = 0 := Real.zero_rpow (by intro hh; exact he (by linarith))
      have h2 : (0 : ℝ) ^ (-e) = 0 := Real.zero_rpow (neg_ne_zero.mpr he)
      rw [h1, h2]; ring
  · have hsq : (a ^ (-(e / 2))) ^ 2 = a ^ (-e) := by
      rw [← Real.rpow_natCast (a ^ (-(e / 2))) 2, ← Real.rpow_mul (le_of_lt h)]
      congr 1; ring
    rw [mul_pow, mul_pow, hsq]

/-- The same identity in the "division" form used by the goal as stated:
for `a ≥ 0` and arbitrary real `e`, `(A·(W / a^{e/2}))² = A²·(W²·a^{-e})`.
`div_eq_mul_inv` and `Real.rpow_neg` turn the `a^{e/2}` in the denominator into the factor
`a^{-e/2}`, reducing to `sq_mul_rpow_neg_half`. -/
private lemma sq_div_rpow_half (A W a e : ℝ) (ha : 0 ≤ a) :
    (A * (W / a ^ (e / 2))) ^ 2 = A ^ 2 * (W ^ 2 * a ^ (-e)) := by
  rw [div_eq_mul_inv, ← Real.rpow_neg ha (e / 2)]
  exact sq_mul_rpow_neg_half A W a e ha

-- The stated lemma carries `hz : z ∈ Iz` for compatibility with its call sites, although the
-- identity proved below holds for every real `w z`: only the non-negativity of `sin(2θ)` on `Iθ`
-- is used, and both slot weights enter through `sq_div_rpow_half`/`sq_mul_rpow_neg_half`.
set_option linter.unusedVariables false in
/-- The pointwise `rpow` algebra converting the `T1Hard` slot weights into the corresponding
summands of `HkIntegrand`: for `z ∈ Iz` (so `w z = (1+z)²/z² ≥ 0`) and `θ ∈ Iθ` (so
`0 ≤ sin(2θ)`) and arbitrary reals `A`, `B`,
`(w z)²·(A²·sin(2θ)^{-η}) = (A·(w z / sin(2θ)^{η/2}))²`
and `(w z)²·(B²·sin(2θ)^{-γ}) = (B·Wt α z θ)²` (`Wt α z θ = w z·sin(2θ)^{-γ/2}`).
Route: `Real.rpow_mul` (`(s^{-η/2})² = s^{-η}` when `0 ≤ s`), `Real.rpow_neg`, `Real.div_rpow`,
`div_pow`, `inv_pow`, `Real.rpow_nonneg`; the degenerate cases `sin(2θ) = 0` and `w z = 0`
(`z = 0`) are handled by `Real.zero_rpow` and by `0^p = 0` for `p ≠ 0` (note `0^k = 0` for `k`
like `η/2 ≠ 0`); `ring` at the end. -/
theorem T1HardWeightAlg (α : ℝ) (z θ A B : ℝ) (hz : z ∈ Work.Spaces.Iz)
    (hθ : θ ∈ Work.Spaces.Iθ) :
    (Work.Spaces.w z) ^ 2 * (A ^ 2 * (Real.sin (2 * θ)) ^ (-Work.Spaces.eta))
        = (A * (Work.Spaces.w z / (Real.sin (2 * θ)) ^ (Work.Spaces.eta / 2))) ^ 2
      ∧ (Work.Spaces.w z) ^ 2 * (B ^ 2 * (Real.sin (2 * θ)) ^ (-Work.Spaces.gam α))
        = (B * Work.Spaces.Wt α z θ) ^ 2 := by
  -- On `Iθ = [0,π/2]` the base `sin(2θ)` of every `rpow` below is non-negative.
  have ha : 0 ≤ Real.sin (2 * θ) := by
    have h1 : (0 : ℝ) ≤ θ := hθ.1
    have h2 : θ ≤ Real.pi / 2 := hθ.2
    exact Real.sin_nonneg_of_mem_Icc ⟨by linarith, by linarith [Real.pi_pos]⟩
  constructor
  · -- `(w z)²·(A²·s^{-η}) = (A·(w z / s^{η/2}))²`: apply the `rpow` algebra to the right-hand
    -- side and commute the factors.
    rw [sq_div_rpow_half A (Work.Spaces.w z) (Real.sin (2 * θ)) Work.Spaces.eta ha]
    ring
  · -- `(w z)²·(B²·s^{-γ}) = (B·Wt α z θ)²`: unfold `Wt α z θ = w z·s^{-γ/2}` and apply the
    -- `rpow` algebra with `e = γ = gam α`.
    rw [Work.Spaces.Wt, Work.Spaces.wTheta,
      sq_mul_rpow_neg_half B (Work.Spaces.w z) (Real.sin (2 * θ)) (Work.Spaces.gam α) ha]
    ring

end Work.FTS.H2
end
-- ===== merged: Submission.Work.FTS.LocData.integral_sqrt_sin_mul_cos_sq =====
section

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

namespace Work.FTS.LocData

/-- The angular integral `∫_{[0,π/2]} √(sin θ cos²θ) dθ = 2/3`.

On `Iθ` the integrand is `√(sin θ) · cos θ` (with `cos θ ≥ 0`), so the substitution
`u = sin θ` gives `∫_0^1 √u du = 2/3`.  Together with `∫_{Iθ} sin θ cos²θ = 1/3`
(Mathlib's `integral_sin_mul_cos_sq`) this is what the proof of
`3/5 ≤ Work.Spaces.c α` needs. -/
theorem integral_sqrt_sin_mul_cos_sq :
    ∫ θ in Work.Spaces.Iθ, Real.sqrt (Real.sin θ * Real.cos θ ^ 2) = 2 / 3 := by
  -- Step 1: on `Iθ = [0, π/2]` both `sin θ` and `cos θ` are nonnegative, so
  -- `√(sin θ · cos²θ) = √(sin θ) · |cos θ| = √(sin θ) · cos θ`.
  have hpt : ∀ θ ∈ Work.Spaces.Iθ, Real.sqrt (Real.sin θ * Real.cos θ ^ 2)
      = Real.sqrt (Real.sin θ) * Real.cos θ := by
    intro θ hθ
    have h0 : 0 ≤ θ := hθ.1
    have h2 : θ ≤ Real.pi / 2 := hθ.2
    have hsin : 0 ≤ Real.sin θ :=
      Real.sin_nonneg_of_mem_Icc ⟨h0, by linarith [h2, Real.pi_pos]⟩
    have hcos : 0 ≤ Real.cos θ :=
      Real.cos_nonneg_of_neg_pi_div_two_le_of_le (by linarith [h0, Real.pi_pos]) h2
    rw [Real.sqrt_mul hsin (Real.cos θ ^ 2), Real.sqrt_sq_eq_abs, abs_of_nonneg hcos]
  rw [MeasureTheory.setIntegral_congr_fun (s := Work.Spaces.Iθ) measurableSet_Icc hpt]
  -- Step 2: the set integral over `Iθ = Icc 0 (π/2)` is the interval integral over `[0, π/2]`.
  rw [Work.Spaces.Iθ, MeasureTheory.integral_Icc_eq_integral_Ioc,
    ← intervalIntegral.integral_of_le (by positivity : (0 : ℝ) ≤ Real.pi / 2)]
  -- Step 3: the substitution `u = sin θ` turns it into `∫_0^1 √u du`.
  have hcv : ∫ θ in (0 : ℝ)..Real.pi / 2, Real.sqrt (Real.sin θ) * Real.cos θ
      = ∫ x in (0 : ℝ)..1, Real.sqrt x := by
    simpa using intervalIntegral.integral_comp_mul_deriv (a := (0 : ℝ)) (b := Real.pi / 2)
      (f := Real.sin) (f' := Real.cos) (g := Real.sqrt)
      (fun x _ => Real.hasDerivAt_sin x) Real.continuous_cos.continuousOn Real.continuous_sqrt
  -- Step 4: `∫_0^1 √u du = ∫_0^1 u^(1/2) du = (1^(3/2) - 0^(3/2))/(3/2) = 2/3`.
  have hroot : ∫ x in (0 : ℝ)..1, Real.sqrt x = 2 / 3 := by
    rw [show ∫ x in (0 : ℝ)..1, Real.sqrt x = ∫ x in (0 : ℝ)..1, x ^ (1 / 2 : ℝ) from
      intervalIntegral.integral_congr (fun x _ => Real.sqrt_eq_rpow x)]
    rw [integral_rpow (Or.inl (by norm_num : (-1 : ℝ) < 1 / 2))]
    norm_num
  rw [hcv, hroot]

end Work.FTS.LocData

namespace Work.FTS.LocData.Work.FTS.LocData

/-- The same statement, recorded also under the doubly nested name that results from the
requested statement text (which itself carried a `namespace Work.FTS.LocData` line).
Both names are provided so that the lemma can be cited either way. -/
theorem integral_sqrt_sin_mul_cos_sq :
    ∫ θ in Work.Spaces.Iθ, Real.sqrt (Real.sin θ * Real.cos θ ^ 2) = 2 / 3 :=
  _root_.Work.FTS.LocData.integral_sqrt_sin_mul_cos_sq

end Work.FTS.LocData.Work.FTS.LocData
end
-- ===== merged: Submission.Work.FTS.Nonlinear.FstarPkg.sinWeight_le_one =====
section

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

namespace Work.FTS.Nonlinear.FstarPkg

/-- For `0 < α ≤ 1` and `0 ≤ s ≤ 1` the weight `s²·s^{-α/5}/(α+s)` is at most `1`.
The numerator equals `s · s^{1-α/5}`: the second factor is `≤ 1` because `s ≤ 1` and
`1 - α/5 ≥ 0`, so the numerator is `≤ s ≤ α + s`, and the denominator is positive. -/
theorem sinWeight_le_one (α s : ℝ) (hα : 0 < α) (hα1 : α ≤ 1) (hs0 : 0 ≤ s) (hs1 : s ≤ 1) :
    s ^ 2 * s ^ (-(α / 5)) / (α + s) ≤ 1 := by
  have hden : 0 < α + s := by linarith
  rcases eq_or_lt_of_le hs0 with h | hs
  · -- `s = 0`: the numerator vanishes.
    subst h
    norm_num
  · -- `0 < s`: merge the two real powers.
    have h1 : s * s ^ (-(α / 5)) = s ^ (1 - α / 5) := by
      have hh : s ^ (1 : ℝ) * s ^ (-(α / 5)) = s ^ (1 - α / 5) := by
        rw [← Real.rpow_add hs]
        ring_nf
      rwa [Real.rpow_one s] at hh
    have h2 : s ^ 2 * s ^ (-(α / 5)) = s * (s * s ^ (-(α / 5))) := by ring
    rw [div_le_one hden, h2, h1]
    have hb : s ^ (1 - α / 5) ≤ 1 := Real.rpow_le_one hs0 hs1 (by linarith)
    have hmul : s * s ^ (1 - α / 5) ≤ s := by
      calc s * s ^ (1 - α / 5) ≤ s * 1 :=
            mul_le_mul_of_nonneg_left hb (le_of_lt hs)
        _ = s := by ring
    linarith

end Work.FTS.Nonlinear.FstarPkg
end
-- ===== merged: Submission.Work.FTS.Nonlinear.Pieces.rl1Pieces.PggTools.angE_w_le_HkSq =====
section

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

/-!
# The weighted `L²`-bound for an angular density dominated a.e. by the `H^k`-integrand

This is the almost-everywhere version of `angE_w_le_HkSq_of_pointwise`: instead of the
pointwise domination `w z * B z θ ^ 2 ≤ HkIntegrand α k f z θ` for all `(z,θ)`, we only
assume it for every `z > 0` and almost every `θ ∈ Iθ`.

The proof is the same as in the pointwise case.  For `z > 0` the weight `w z` is positive, so
`w z * ∫_θ B z θ ^ 2 = ∫_θ w z * B z θ ^ 2`, and the a.e. domination together with the
integrability of `θ ↦ HkIntegrand α k f z θ` (from `HkMem`) gives both the integrability of
the angular slice `θ ↦ B z θ ^ 2` and the pointwise-in-`z` inequality
`w z * ∫_θ B z θ ^ 2 ≤ ∫_θ HkIntegrand α k f z θ`.  The remaining two steps —
measurability of `z ↦ ∫_θ B z θ ^ 2` from the joint measurability `hjn`, and the comparison
of the `z`-integrals over `(0,∞)` and over `Iz = [0,∞)` — are as before; the point `z = 0`
carries no weight (`w 0 = 0`) and `{0}` is null, so the restriction of the hypothesis to
`z > 0` costs nothing.
-/

open scoped Real Topology
open MeasureTheory Set Filter

namespace Work.FTS.Nonlinear.Pieces.rl1Pieces.PggTools

theorem angE_w_le_HkSq {α : ℝ} {k : ℕ} {f B : ℝ → ℝ → ℝ}
    (hmem : Work.Spaces.HkMem α k f)
    (hsl : ∀ z ∈ Work.Spaces.Iz, MeasureTheory.AEStronglyMeasurable (fun θ => B z θ)
      (MeasureTheory.volume.restrict Work.Spaces.Iθ))
    (hjn : MeasureTheory.AEStronglyMeasurable (Function.uncurry B)
      ((MeasureTheory.volume.restrict Work.Spaces.Iz).prod
        (MeasureTheory.volume.restrict Work.Spaces.Iθ)))
    (hpt : ∀ z, 0 < z → ∀ᵐ θ ∂(MeasureTheory.volume.restrict Work.Spaces.Iθ),
      Work.Spaces.w z * (B z θ) ^ 2 ≤ Work.Spaces.HkIntegrand α k f z θ) :
    (∀ z, 0 < z → MeasureTheory.IntegrableOn (fun θ => (B z θ) ^ 2) Work.Spaces.Iθ) ∧
    MeasureTheory.AEStronglyMeasurable
      (fun z => ∫ θ in Work.Spaces.Iθ, (B z θ) ^ 2) (MeasureTheory.volume.restrict (Set.Ioi 0)) ∧
    MeasureTheory.IntegrableOn
      (fun z => Work.Spaces.w z * (∫ θ in Work.Spaces.Iθ, (B z θ) ^ 2)) (Set.Ioi 0) ∧
    (∫ z in Set.Ioi (0 : ℝ), Work.Spaces.w z * (∫ θ in Work.Spaces.Iθ, (B z θ) ^ 2))
      ≤ Work.Spaces.HkSq α k f := by
  have hIz_of_le : ∀ z : ℝ, 0 ≤ z → z ∈ Work.Spaces.Iz := fun z hz => hz
  have hw_pos : ∀ z : ℝ, 0 < z → 0 < Work.Spaces.w z := by
    intro z hz
    rw [Work.Spaces.w]
    exact div_pos (pow_pos (by linarith) 2) (pow_pos hz 2)
  have hw_nonneg : ∀ z : ℝ, 0 ≤ Work.Spaces.w z := by
    intro z
    rw [Work.Spaces.w]
    exact div_nonneg (sq_nonneg _) (sq_nonneg _)
  have hsub : Set.Ioi (0 : ℝ) ⊆ Work.Spaces.Iz := fun z hz => hIz_of_le z (le_of_lt hz)
  -- the pointwise-in-`z` inequality, obtained by pulling the `θ`-independent factor `w z` out
  have key : ∀ z, 0 < z →
      Work.Spaces.w z * (∫ θ in Work.Spaces.Iθ, (B z θ) ^ 2)
        ≤ ∫ θ in Work.Spaces.Iθ, Work.Spaces.HkIntegrand α k f z θ := by
    intro z hz
    have hzIz : z ∈ Work.Spaces.Iz := hIz_of_le z (le_of_lt hz)
    rw [← MeasureTheory.integral_const_mul]
    exact MeasureTheory.integral_mono_of_nonneg
      (ae_of_all _ fun θ => mul_nonneg (hw_nonneg z) (sq_nonneg _))
      (hmem.1 z hzIz)
      (hpt z hz)
  -- each angular slice is square-integrable
  have hB2int : ∀ z, 0 < z →
      MeasureTheory.IntegrableOn (fun θ => (B z θ) ^ 2) Work.Spaces.Iθ := by
    intro z hz
    have hzIz : z ∈ Work.Spaces.Iz := hIz_of_le z (le_of_lt hz)
    have hwz : Work.Spaces.w z ≠ 0 := ne_of_gt (hw_pos z hz)
    have hmeas : MeasureTheory.AEStronglyMeasurable (fun θ => Work.Spaces.w z * (B z θ) ^ 2)
        (MeasureTheory.volume.restrict Work.Spaces.Iθ) :=
      ((hsl z hzIz).pow 2).const_mul _
    have h1 : MeasureTheory.IntegrableOn (fun θ => Work.Spaces.w z * (B z θ) ^ 2) Work.Spaces.Iθ :=
      MeasureTheory.Integrable.mono' (hmem.1 z hzIz) hmeas (by
        filter_upwards [hpt z hz] with θ hθ
        rw [Real.norm_eq_abs, abs_of_nonneg (mul_nonneg (hw_nonneg z) (sq_nonneg _))]
        exact hθ)
    have h2 : MeasureTheory.IntegrableOn
        (fun θ => (Work.Spaces.w z)⁻¹ * (Work.Spaces.w z * (B z θ) ^ 2)) Work.Spaces.Iθ :=
      h1.const_mul _
    have h3 : (fun θ => (Work.Spaces.w z)⁻¹ * (Work.Spaces.w z * (B z θ) ^ 2))
        = fun θ => (B z θ) ^ 2 := by
      funext θ
      rw [inv_mul_cancel_left₀ hwz]
    rwa [h3] at h2
  -- joint measurability of the angular integral
  have hB2measIz : MeasureTheory.AEStronglyMeasurable
      (fun z => ∫ θ in Work.Spaces.Iθ, (B z θ) ^ 2)
      (MeasureTheory.volume.restrict Work.Spaces.Iz) := by
    have huncurry : Function.uncurry (fun z θ => (B z θ) ^ 2)
        = fun p : ℝ × ℝ => (Function.uncurry B p) ^ 2 := by
      funext p; rfl
    have hp : MeasureTheory.AEStronglyMeasurable (fun p : ℝ × ℝ => (Function.uncurry B p) ^ 2)
        ((MeasureTheory.volume.restrict Work.Spaces.Iz).prod
          (MeasureTheory.volume.restrict Work.Spaces.Iθ)) := hjn.pow 2
    have := hp.integral_prod_right'
    simpa [huncurry] using this
  have hB2meas0 : MeasureTheory.AEStronglyMeasurable
      (fun z => ∫ θ in Work.Spaces.Iθ, (B z θ) ^ 2)
      (MeasureTheory.volume.restrict (Set.Ioi 0)) :=
    hB2measIz.mono_measure (MeasureTheory.Measure.restrict_mono hsub le_rfl)
  have hgint : MeasureTheory.IntegrableOn
      (fun z => ∫ θ in Work.Spaces.Iθ, Work.Spaces.HkIntegrand α k f z θ) Work.Spaces.Iz := hmem.2
  have hgint0 : MeasureTheory.IntegrableOn
      (fun z => ∫ θ in Work.Spaces.Iθ, Work.Spaces.HkIntegrand α k f z θ) (Set.Ioi 0) :=
    MeasureTheory.IntegrableOn.mono_set hgint hsub
  have hwmeas : Measurable (fun z : ℝ => Work.Spaces.w z) := by
    unfold Work.Spaces.w
    fun_prop
  -- integrability of the `z`-integrand on `(0,∞)`
  have hFint : MeasureTheory.IntegrableOn
      (fun z => Work.Spaces.w z * (∫ θ in Work.Spaces.Iθ, (B z θ) ^ 2)) (Set.Ioi 0) := by
    refine MeasureTheory.Integrable.mono' hgint0 (hwmeas.aestronglyMeasurable.mul hB2meas0) ?_
    filter_upwards [MeasureTheory.ae_restrict_mem measurableSet_Ioi] with z hz
    rw [Real.norm_eq_abs,
      abs_of_nonneg (mul_nonneg (hw_nonneg z) (MeasureTheory.integral_nonneg fun θ => sq_nonneg _))]
    exact key z hz
  refine ⟨hB2int, hB2meas0, hFint, ?_⟩
  have h1 : ∫ z in Set.Ioi (0 : ℝ), Work.Spaces.w z * (∫ θ in Work.Spaces.Iθ, (B z θ) ^ 2)
      ≤ ∫ z in Set.Ioi (0 : ℝ),
          (∫ θ in Work.Spaces.Iθ, Work.Spaces.HkIntegrand α k f z θ) :=
    MeasureTheory.setIntegral_mono_ae_restrict hFint hgint0 (by
      filter_upwards [MeasureTheory.ae_restrict_mem measurableSet_Ioi] with z hz
      exact key z hz)
  have h2 : ∫ z in Set.Ioi (0 : ℝ), (∫ θ in Work.Spaces.Iθ, Work.Spaces.HkIntegrand α k f z θ)
      ≤ ∫ z in Work.Spaces.Iz, (∫ θ in Work.Spaces.Iθ, Work.Spaces.HkIntegrand α k f z θ) :=
    MeasureTheory.setIntegral_mono_set hgint
      (ae_of_all _ fun z => MeasureTheory.integral_nonneg fun θ =>
        Work.Spaces.HkIntegrand_nonneg α k f z θ)
      (ae_of_all _ fun z hz => hIz_of_le z (le_of_lt hz))
  simpa [Work.Spaces.HkSq] using h1.trans h2

end Work.FTS.Nonlinear.Pieces.rl1Pieces.PggTools
end
-- ===== merged: Submission.Work.FTS.Nonlinear.Pieces.rl1Pieces.PggTools.inner_lintegral_le =====
section

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

noncomputable section
open scoped Real Topology ENNReal
open MeasureTheory Set Filter

namespace Work.FTS.Nonlinear.Pieces.rl1Pieces.PggTools

/-- `K` is bounded by `3` on all of `ℝ` (and on `Iθ` it is nonnegative and `≤ 3`). -/
theorem abs_K_le_three_aux (θ : ℝ) : |Work.Spaces.K θ| ≤ 3 := by
  rw [Work.Spaces.K]
  have h1 : |Real.sin θ| ≤ 1 := abs_le.mpr ⟨Real.neg_one_le_sin θ, Real.sin_le_one θ⟩
  have h2 : |Real.cos θ ^ 2| ≤ 1 := by
    rw [abs_of_nonneg (sq_nonneg _)]
    nlinarith [Real.neg_one_le_cos θ, Real.cos_le_one θ]
  rw [abs_mul, abs_mul, abs_of_nonneg (by norm_num : (0 : ℝ) ≤ 3)]
  calc 3 * |Real.sin θ| * |Real.cos θ ^ 2| ≤ 3 * 1 * 1 :=
        mul_le_mul (mul_le_mul_of_nonneg_left h1 (by norm_num)) h2 (abs_nonneg _) (by norm_num)
    _ = 3 := by norm_num


end Work.FTS.Nonlinear.Pieces.rl1Pieces.PggTools
end
end
-- ===== merged: Submission.Work.FTS.Nonlinear.Pieces.rl1Pieces.PggTools.outer_weight_le =====
section

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

/-!
# The outer weight bound: `∫⁻ (1/z)·Φ^{1/2} ≤ √2 · √(∫ w·Φ)`

This is the radial Cauchy–Schwarz estimate behind the `rl¹`-rows of the nonlinearity: the
singular factor `1/z` of the outer region is split against the weight `w z = (1+z)²/z²`,

```
1/z · √(Φ z) = √(w z · Φ z) · (1+z)⁻¹          (z > 0),
```

so that `√(w z · Φ z)` is square-integrable exactly when `∫ w · Φ < ∞`, while the *second*
factor `(1+z)⁻¹` contributes only the universal constant
`(∫₀^∞ (1+z)⁻²)^{1/2} ≤ √2` (`Work.FTS.H2.InvOneAddSq`).  The proof is Hölder's inequality
in `L²` (`ENNReal.lintegral_mul_le_Lp_mul_Lq` with `p = q = 2`) applied to the two factors,
after converting the `ℝ≥0∞`-integral `∫⁻ ofReal (w·Φ)` of the first factor back into the real
integral `∫ w·Φ`.

The constant `√2` is not optimal (the sharp constant is `1 = (∫₀^∞ (1+z)⁻²)^{1/2}`), but the
statement only needs `√2`, and this is what the available weight lemma provides.
-/

open scoped Real Topology ENNReal
open MeasureTheory Set Filter

namespace Work.FTS.Nonlinear.Pieces.rl1Pieces.PggTools






end Work.FTS.Nonlinear.Pieces.rl1Pieces.PggTools
end
-- ===== merged: Submission.Work.FTS.PhiStar.Radial.radGreenIntended =====
section

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

noncomputable section
open scoped Real Topology
open MeasureTheory Set Filter

namespace Work.FTS.PhiStar.Radial

set_option autoImplicit false

/-- **The intended radial Green's function** (the explicit decaying solution of the mode-`m` Euler
equation `-α²z²a'' - α(5+α)z a' + λ_m a = c`, `λ_m = 2m(2m+5)`).  This is the formula of
`Work.FTS.PhiStar.Radial.radGreen` with the body of the first integral parenthesised; for the
function defined in `Radial/Defs.lean` that parenthesis is missing and the two differ. -/
def radGreenI (α : ℝ) (m : ℕ) (c : ℝ → ℝ) (z : ℝ) : ℝ :=
  1 / (α * (4 * (m : ℝ) + 5)) *
    (z ^ (-(2 * (m : ℝ) + 5) / α) * (∫ t in (0 : ℝ)..z, c t * t ^ ((2 * (m : ℝ) + 5) / α - 1))
      + z ^ (2 * (m : ℝ) / α) * (∫ t in Set.Ioi z, c t * t ^ (-(2 * (m : ℝ) / α) - 1)))

/-! ### Private scaffolding -/

/-- The decaying indicial exponent `s⁻ = -(2m+5)/α`. -/
private def sgN (α : ℝ) (m : ℕ) : ℝ := -(2 * (m : ℝ) + 5) / α
/-- The growing indicial exponent `s⁺ = 2m/α`. -/
private def sgP (α : ℝ) (m : ℕ) : ℝ := 2 * (m : ℝ) / α
/-- The normalising constant `1/(α(4m+5)) = 1/(α²(s⁺-s⁻))`. -/
private def gK (α : ℝ) (m : ℕ) : ℝ := 1 / (α * (4 * (m : ℝ) + 5))
/-- The integrand of the `0..z` integral. -/
private def gf1 (α : ℝ) (m : ℕ) (c : ℝ → ℝ) (t : ℝ) : ℝ :=
  c t * t ^ ((2 * (m : ℝ) + 5) / α - 1)
/-- The integrand of the `Ioi z` integral. -/
private def gf2 (α : ℝ) (m : ℕ) (c : ℝ → ℝ) (t : ℝ) : ℝ :=
  c t * t ^ (-(2 * (m : ℝ) / α) - 1)
/-- The `0..z` integral. -/
private def gA (α : ℝ) (m : ℕ) (c : ℝ → ℝ) (z : ℝ) : ℝ := ∫ t in (0 : ℝ)..z, gf1 α m c t
/-- The `Ioi z` integral. -/
private def gB (α : ℝ) (m : ℕ) (c : ℝ → ℝ) (z : ℝ) : ℝ := ∫ t in Set.Ioi z, gf2 α m c t
/-- The derivative of `radGreenI`. -/
private def gd1 (α : ℝ) (m : ℕ) (c : ℝ → ℝ) (y : ℝ) : ℝ :=
  gK α m * ((sgN α m * y ^ (sgN α m - 1)) * gA α m c y
            + (sgP α m * y ^ (sgP α m - 1)) * gB α m c y)
/-- The second derivative of `radGreenI`. -/
private def gd2 (α : ℝ) (m : ℕ) (c : ℝ → ℝ) (y : ℝ) : ℝ :=
  gK α m * (((sgN α m * ((sgN α m - 1) * y ^ (sgN α m - 2))) * gA α m c y
            + (sgN α m * y ^ (sgN α m - 1)) * gf1 α m c y)
          + ((sgP α m * ((sgP α m - 1) * y ^ (sgP α m - 2))) * gB α m c y
            + (sgP α m * y ^ (sgP α m - 1)) * (-(gf2 α m c y))))

private lemma radGreenI_eq (α : ℝ) (m : ℕ) (c : ℝ → ℝ) :
    radGreenI α m c
      = fun z => gK α m * (z ^ (sgN α m) * gA α m c z + z ^ (sgP α m) * gB α m c z) := by
  funext z
  rfl

/-! ### The main computation -/

theorem radGreenI_solves {α : ℝ} (hα : 0 < α) (m : ℕ) {c : ℝ → ℝ}
    (hc : ContinuousOn c (Set.Ioi 0))
    (h0 : MeasureTheory.IntegrableOn (fun t => c t * t ^ ((2 * (m : ℝ) + 5) / α - 1))
      (Set.Ioo 0 1))
    (h0' : MeasureTheory.IntegrableOn (fun t => c t * t ^ (-(2 * (m : ℝ) / α) - 1))
      (Set.Ioo 0 1))
    (hinf : MeasureTheory.IntegrableOn (fun t => c t * t ^ (-(2 * (m : ℝ) / α) - 1))
      (Set.Ioi 1)) :
    ∀ z, 0 < z →
      -α ^ 2 * z ^ 2 * deriv (deriv (radGreenI α m c)) z
        - α * (5 + α) * z * deriv (radGreenI α m c) z
        + lamR m * radGreenI α m c z = c z := by
  intro z hz
  have hαne : α ≠ 0 := ne_of_gt hα
  have h0i : IntegrableOn (gf1 α m c) (Set.Ioo 0 1) := h0
  have h0i' : IntegrableOn (gf2 α m c) (Set.Ioo 0 1) := h0'
  have hinfi : IntegrableOn (gf2 α m c) (Set.Ioi 1) := hinf
  have hf1c : ContinuousOn (gf1 α m c) (Set.Ioi 0) :=
    hc.mul (continuousOn_id.rpow_const (fun t ht => Or.inl (ne_of_gt ht)))
  have hf2c : ContinuousOn (gf2 α m c) (Set.Ioi 0) :=
    hc.mul (continuousOn_id.rpow_const (fun t ht => Or.inl (ne_of_gt ht)))
  -- Differentiability of the two building blocks, at every `y > 0`.
  have hAall : ∀ y ∈ Set.Ioi (0 : ℝ), HasDerivAt (gA α m c) (gf1 α m c y) y := by
    intro y hy
    have hsm : StronglyMeasurableAtFilter (gf1 α m c) (𝓝 y) volume :=
      ContinuousOn.stronglyMeasurableAtFilter isOpen_Ioi hf1c y hy
    exact intervalIntegral.integral_hasDerivAt_right (a := 0) (b := y)
      (intervalIntegrable_of_Ioi_Ioo hy hf1c h0i) hsm (hf1c.continuousAt (Ioi_mem_nhds hy))
  have hBall : ∀ y ∈ Set.Ioi (0 : ℝ), HasDerivAt (gB α m c) (-(gf2 α m c y)) y := by
    intro y hy
    have hy0 : 0 < y := hy
    exact hasDerivAt_integral_Ioi (a := y / 2) (by linarith)
      (hf2c.mono (fun t ht => by
        have h := ht; simp only [Set.mem_Ioi] at h ⊢; linarith))
      (integrableOn_Ioi_of_Ioi_Ioo (by linarith) hf2c hinfi)
  -- First derivative.
  have hGreen1 : ∀ y ∈ Set.Ioi (0 : ℝ), HasDerivAt (radGreenI α m c) (gd1 α m c y) y := by
    intro y hy
    have hy0 : 0 < y := hy
    have hyne : y ≠ 0 := ne_of_gt hy0
    have hA := hAall y hy
    have hB := hBall y hy
    have hp1 : HasDerivAt (fun t : ℝ => t ^ (sgN α m)) (sgN α m * y ^ (sgN α m - 1)) y :=
      Real.hasDerivAt_rpow_const (Or.inl hyne)
    have hp2 : HasDerivAt (fun t : ℝ => t ^ (sgP α m)) (sgP α m * y ^ (sgP α m - 1)) y :=
      Real.hasDerivAt_rpow_const (Or.inl hyne)
    have hm1 : HasDerivAt (fun t : ℝ => t ^ (sgN α m) * gA α m c t)
        ((sgN α m * y ^ (sgN α m - 1)) * gA α m c y + y ^ (sgN α m) * gf1 α m c y) y :=
      hp1.mul hA
    have hm2 : HasDerivAt (fun t : ℝ => t ^ (sgP α m) * gB α m c t)
        ((sgP α m * y ^ (sgP α m - 1)) * gB α m c y
          + y ^ (sgP α m) * (-(gf2 α m c y))) y :=
      hp2.mul hB
    have h3 : HasDerivAt (fun t : ℝ =>
        gK α m * (t ^ (sgN α m) * gA α m c t + t ^ (sgP α m) * gB α m c t))
        (gK α m * (((sgN α m * y ^ (sgN α m - 1)) * gA α m c y
                      + y ^ (sgN α m) * gf1 α m c y)
                    + ((sgP α m * y ^ (sgP α m - 1)) * gB α m c y
                      + y ^ (sgP α m) * (-(gf2 α m c y))))) y :=
      (hm1.add hm2).const_mul (gK α m)
    have hc1 : y ^ (sgN α m) * gf1 α m c y = c y / y := by
      have he : (2 * (m : ℝ) + 5) / α - 1 = -1 - (-(2 * (m : ℝ) + 5) / α) := by ring
      have hf : gf1 α m c y = c y * y ^ (-1 - sgN α m) := by
        simp only [gf1, sgN]; rw [he]
      calc y ^ (sgN α m) * gf1 α m c y
          = y ^ (sgN α m) * (c y * y ^ (-1 - sgN α m)) := by rw [hf]
        _ = c y * (y ^ (sgN α m) * y ^ (-1 - sgN α m)) := by ring
        _ = c y * y ^ (-(1 : ℝ)) := by
              have hExp : sgN α m + (-1 - sgN α m) = -(1 : ℝ) := by ring
              rw [← Real.rpow_add hy0, hExp]
        _ = c y / y := by rw [Real.rpow_neg_one, div_eq_mul_inv]
    have hc2 : y ^ (sgP α m) * gf2 α m c y = c y / y := by
      have he : -(2 * (m : ℝ) / α) - 1 = -1 - (2 * (m : ℝ) / α) := by ring
      have hf : gf2 α m c y = c y * y ^ (-1 - sgP α m) := by
        simp only [gf2, sgP]; rw [he]
      calc y ^ (sgP α m) * gf2 α m c y
          = y ^ (sgP α m) * (c y * y ^ (-1 - sgP α m)) := by rw [hf]
        _ = c y * (y ^ (sgP α m) * y ^ (-1 - sgP α m)) := by ring
        _ = c y * y ^ (-(1 : ℝ)) := by
              have hExp : sgP α m + (-1 - sgP α m) = -(1 : ℝ) := by ring
              rw [← Real.rpow_add hy0, hExp]
        _ = c y / y := by rw [Real.rpow_neg_one, div_eq_mul_inv]
    have hval : gK α m * (((sgN α m * y ^ (sgN α m - 1)) * gA α m c y
                      + y ^ (sgN α m) * gf1 α m c y)
                    + ((sgP α m * y ^ (sgP α m - 1)) * gB α m c y
                      + y ^ (sgP α m) * (-(gf2 α m c y)))) = gd1 α m c y := by
      simp only [gd1]
      rw [mul_neg, hc1, hc2]
      ring
    rw [radGreenI_eq]
    exact h3.congr_deriv hval
  -- Second derivative.
  have hD1 : HasDerivAt (gd1 α m c) (gd2 α m c z) z := by
    have hzne : z ≠ 0 := ne_of_gt hz
    have hA := hAall z hz
    have hB := hBall z hz
    have hp1 : HasDerivAt (fun t : ℝ => sgN α m * t ^ (sgN α m - 1))
        (sgN α m * ((sgN α m - 1) * z ^ (sgN α m - 2))) z := by
      have h := (Real.hasDerivAt_rpow_const (x := z) (p := sgN α m - 1)
        (Or.inl hzne)).const_mul (sgN α m)
      rwa [show (sgN α m - 1) - 1 = sgN α m - 2 from by ring] at h
    have hp2 : HasDerivAt (fun t : ℝ => sgP α m * t ^ (sgP α m - 1))
        (sgP α m * ((sgP α m - 1) * z ^ (sgP α m - 2))) z := by
      have h := (Real.hasDerivAt_rpow_const (x := z) (p := sgP α m - 1)
        (Or.inl hzne)).const_mul (sgP α m)
      rwa [show (sgP α m - 1) - 1 = sgP α m - 2 from by ring] at h
    have h3 : HasDerivAt (gd1 α m c) (gd2 α m c z) z :=
      ((hp1.mul hA).add (hp2.mul hB)).const_mul (gK α m)
    exact h3
  have hderivEq : deriv (radGreenI α m c) =ᶠ[𝓝 z] gd1 α m c :=
    eventually_of_mem (Ioi_mem_nhds hz) (fun y hy => (hGreen1 y hy).deriv)
  have hdd : deriv (deriv (radGreenI α m c)) z = gd2 α m c z := by
    rw [hderivEq.deriv_eq, hD1.deriv]
  have hd1z : deriv (radGreenI α m c) z = gd1 α m c z := (hGreen1 z hz).deriv
  have hgz : radGreenI α m c z
      = gK α m * (z ^ (sgN α m) * gA α m c z + z ^ (sgP α m) * gB α m c z) :=
    congrFun (radGreenI_eq α m c) z
  rw [hdd, hd1z, hgz]
  -- The `rpow` clearing identities.
  have hzs1 : z * z ^ (sgN α m - 1) = z ^ (sgN α m) := by
    nth_rewrite 1 [← Real.rpow_one z]
    rw [← Real.rpow_add hz]
    congr 1
    ring
  have hzs2 : z ^ 2 * z ^ (sgN α m - 2) = z ^ (sgN α m) := by
    rw [← Real.rpow_two z, ← Real.rpow_add hz]
    congr 1
    ring
  have hzp1 : z * z ^ (sgP α m - 1) = z ^ (sgP α m) := by
    nth_rewrite 1 [← Real.rpow_one z]
    rw [← Real.rpow_add hz]
    congr 1
    ring
  have hzp2 : z ^ 2 * z ^ (sgP α m - 2) = z ^ (sgP α m) := by
    rw [← Real.rpow_two z, ← Real.rpow_add hz]
    congr 1
    ring
  have hc1 : z ^ 2 * z ^ (sgN α m - 1) * gf1 α m c z = c z := by
    have he : (2 * (m : ℝ) + 5) / α - 1 = -1 - (-(2 * (m : ℝ) + 5) / α) := by ring
    have hf : gf1 α m c z = c z * z ^ (-1 - sgN α m) := by
      simp only [gf1, sgN]; rw [he]
    have h2 : z ^ 2 * z ^ (sgN α m - 1) = z ^ (sgN α m + 1) := by
      rw [← Real.rpow_two z, ← Real.rpow_add hz]; congr 1; ring
    have hE : (sgN α m + 1) + (-1 - sgN α m) = 0 := by ring
    have hcomb : z ^ 2 * z ^ (sgN α m - 1) * z ^ (-1 - sgN α m) = 1 := by
      rw [h2, ← Real.rpow_add hz, hE, Real.rpow_zero]
    calc z ^ 2 * z ^ (sgN α m - 1) * gf1 α m c z
        = z ^ 2 * z ^ (sgN α m - 1) * (c z * z ^ (-1 - sgN α m)) := by rw [hf]
      _ = c z * (z ^ 2 * z ^ (sgN α m - 1) * z ^ (-1 - sgN α m)) := by ring
      _ = c z * 1 := by rw [hcomb]
      _ = c z := by ring
  have hc2 : z ^ 2 * z ^ (sgP α m - 1) * gf2 α m c z = c z := by
    have he : -(2 * (m : ℝ) / α) - 1 = -1 - (2 * (m : ℝ) / α) := by ring
    have hf : gf2 α m c z = c z * z ^ (-1 - sgP α m) := by
      simp only [gf2, sgP]; rw [he]
    have h2 : z ^ 2 * z ^ (sgP α m - 1) = z ^ (sgP α m + 1) := by
      rw [← Real.rpow_two z, ← Real.rpow_add hz]; congr 1; ring
    have hE : (sgP α m + 1) + (-1 - sgP α m) = 0 := by ring
    have hcomb : z ^ 2 * z ^ (sgP α m - 1) * z ^ (-1 - sgP α m) = 1 := by
      rw [h2, ← Real.rpow_add hz, hE, Real.rpow_zero]
    calc z ^ 2 * z ^ (sgP α m - 1) * gf2 α m c z
        = z ^ 2 * z ^ (sgP α m - 1) * (c z * z ^ (-1 - sgP α m)) := by rw [hf]
      _ = c z * (z ^ 2 * z ^ (sgP α m - 1) * z ^ (-1 - sgP α m)) := by ring
      _ = c z * 1 := by rw [hcomb]
      _ = c z := by ring
  have hzA1 : z * gd1 α m c z = gK α m * (sgN α m * (z ^ (sgN α m) * gA α m c z)
      + sgP α m * (z ^ (sgP α m) * gB α m c z)) := by
    simp only [gd1]
    linear_combination (gK α m * sgN α m * gA α m c z) * hzs1
      + (gK α m * sgP α m * gB α m c z) * hzp1
  have hzA2 : z ^ 2 * gd2 α m c z
      = gK α m * (sgN α m * (sgN α m - 1) * (z ^ (sgN α m) * gA α m c z)
        + sgP α m * (sgP α m - 1) * (z ^ (sgP α m) * gB α m c z)
        + (sgN α m - sgP α m) * c z) := by
    simp only [gd2]
    linear_combination (gK α m * sgN α m * (sgN α m - 1) * gA α m c z) * hzs2
      + (gK α m * sgP α m * (sgP α m - 1) * gB α m c z) * hzp2
      + (gK α m * sgN α m) * hc1 - (gK α m * sgP α m) * hc2
  have hind1 : -α ^ 2 * sgN α m * (sgN α m - 1) - α * (5 + α) * sgN α m + lamR m = 0 := by
    simp only [sgN, lamR]
    field_simp
    ring
  have hind2 : -α ^ 2 * sgP α m * (sgP α m - 1) - α * (5 + α) * sgP α m + lamR m = 0 := by
    simp only [sgP, lamR]
    field_simp
    ring
  have hK : α ^ 2 * gK α m * (sgP α m - sgN α m) = 1 := by
    simp only [gK, sgP, sgN]
    field_simp
    ring
  linear_combination (-(α ^ 2)) * hzA2 - (α * (5 + α)) * hzA1
    + (gK α m * (z ^ (sgN α m) * gA α m c z)) * hind1
    + (gK α m * (z ^ (sgP α m) * gB α m c z)) * hind2 + (c z) * hK

end Work.FTS.PhiStar.Radial
end
end
-- ===== merged: Submission.Work.FTS.PhiStar.Series.Defs =====
section

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

noncomputable section
open scoped Real Topology BigOperators
open MeasureTheory Set Filter

namespace Work.FTS.PhiStar.Series

set_option autoImplicit false

/-- The `e_m`-coefficient of the slice `F(z,·)` for the self-adjoint weight `cos θ dθ`. -/
def cmode (m : ℕ) (F : ℝ → ℝ → ℝ) (z : ℝ) : ℝ :=
  (∫ θ in (0 : ℝ)..(Real.pi / 2),
      F z θ * Work.FTS.PhiStar.Gegenbauer.eFam m θ * Real.cos θ)
    / (∫ θ in (0 : ℝ)..(Real.pi / 2),
        Work.FTS.PhiStar.Gegenbauer.eFam m θ ^ 2 * Real.cos θ)

/-- The mode-`m` radial coefficient of the solution: the decaying solution of the Euler equation
`-α²z²a'' - α(5+α)z a' + lam m · a = cmode m F`. -/
def acoeff (α : ℝ) (m : ℕ) (F : ℝ → ℝ → ℝ) : ℝ → ℝ :=
  Work.FTS.PhiStar.Radial.radGreen α m (fun t => cmode m F t)

/-- The `N`-th partial sum of the mode series (source `Σ_{m≤N} cmode m F z · e_m`). -/
def psiTrunc (α : ℝ) (F : ℝ → ℝ → ℝ) (N : ℕ) (z θ : ℝ) : ℝ :=
  ∑ m ∈ Finset.range (N + 1),
    acoeff α m F z * Work.FTS.PhiStar.Gegenbauer.eFam m θ

/-- The mode series solution of `bslOp α Ψ = F`. -/
def psiSeries (α : ℝ) (F : ℝ → ℝ → ℝ) (z θ : ℝ) : ℝ :=
  ∑' m : ℕ, acoeff α m F z * Work.FTS.PhiStar.Gegenbauer.eFam m θ

end Work.FTS.PhiStar.Series
end
end
-- ===== merged: Submission.Work.FTS.PhiStar.ThetaTraces =====
section

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

/-!
# `PhiStar.ThetaTraces` — the θ-part of the boundary traces (lead install R6, 2026-10-11)

`cbc/fts_ellnode_ruling.md` §4.2(1), §4.4.  The CptApp chain (`exists_cptQ_approx`) destructures
`BdryTraces α k F` in exactly one place (`Est/hardyShrink_slice`: `(hB 0 s _).2 z hz`): the
θ-limits of `sin(2θ)^{1-γ}·(D_z^s F)²` for `s + 1 ≤ k`, at every `z > 0`.  `ThetaTraces α k F`
is exactly that.  It cannot be derived from `HkMem` (ruling Q1), so it is carried as the last field
`thTr` of `ClassC.ClassC` and of `StrongEps.SoftClass`.

Standalone low-level file (imports only `Spaces.Defs`) so that `ClassC/Defs` can import it without
an import cycle.  `thetaTraces_of_bdryTraces` lives in `PhiStar/ThetaTracesBdry.lean`.
-/

noncomputable section
open scoped Real Topology
open Filter

namespace Work.FTS.PhiStar

/-- θ-traces of the radial iterates of order `s < k` — exactly the part of `BdryTraces α k F`
that the CptApp chain uses (`Est/hardyShrink_slice`: `(hB 0 s _).2 z hz`). -/
def ThetaTraces (α : ℝ) (k : ℕ) (F : ℝ → ℝ → ℝ) : Prop :=
  ∀ s : ℕ, s + 1 ≤ k → ∀ z ∈ Set.Ioi (0 : ℝ),
    Tendsto (fun θ => Real.sin (2 * θ) ^ (1 - Work.Spaces.gam α)
        * (Work.Spaces.mixed s 0 F z θ) ^ 2) (𝓝[>] 0) (𝓝 0) ∧
    Tendsto (fun θ => Real.sin (2 * θ) ^ (1 - Work.Spaces.gam α)
        * (Work.Spaces.mixed s 0 F z θ) ^ 2) (𝓝[<] (π / 2)) (𝓝 0)


end Work.FTS.PhiStar
end
end
-- ===== merged: Submission.Work.FTS.RegPkgGal.R2.hasDerivAt_slice_pth =====
section

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

namespace Work.FTS.RegPkgGal.R2

theorem hasDerivAt_slice_pth {f : ℝ → ℝ → ℝ} {z θ : ℝ}
    (h : ContDiffOn ℝ 1 (Function.uncurry f)
      (Set.prod (Set.Ioi (0:ℝ)) (Set.Ioo (0:ℝ) (Real.pi / 2))))
    (hz : 0 < z) (hθ : θ ∈ Set.Ioo (0:ℝ) (Real.pi / 2)) :
    HasDerivAt (fun s : ℝ => f z s) (Work.Spaces.pth f z θ) θ := by
  -- The angular slice `s ↦ (z, s)` is `C¹` and maps the angular interval into the
  -- product on which `uncurry f` is `C¹`, so the composite `s ↦ f z s` is `C¹`.
  have hslice : ContDiffOn ℝ 1 (fun s : ℝ => (z, s)) (Set.Ioo (0:ℝ) (Real.pi / 2)) := by
    fun_prop
  have hmap : Set.MapsTo (fun s : ℝ => (z, s)) (Set.Ioo (0:ℝ) (Real.pi / 2))
      (Set.prod (Set.Ioi (0:ℝ)) (Set.Ioo (0:ℝ) (Real.pi / 2))) :=
    fun s hs => ⟨hz, hs⟩
  have hcomp : ContDiffOn ℝ 1 (fun s : ℝ => f z s) (Set.Ioo (0:ℝ) (Real.pi / 2)) := by
    have h2 := h.comp hslice hmap
    simpa [Function.comp_def, Function.uncurry] using h2
  -- Hence the slice is differentiable at `θ`, and `deriv` of the slice is exactly
  -- `Work.Spaces.pth f z θ` by definition.
  have hda : DifferentiableAt ℝ (fun s : ℝ => f z s) θ :=
    (hcomp.differentiableOn (by norm_num)).differentiableAt (isOpen_Ioo.mem_nhds hθ)
  simpa [Work.Spaces.pth] using hda.hasDerivAt

end Work.FTS.RegPkgGal.R2
end
-- ===== merged: Submission.Work.FTS.RegPkgGal.R2.hasDerivAt_slice_pz =====
section

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

namespace Work.FTS.RegPkgGal.R2

theorem hasDerivAt_slice_pz {f : ℝ → ℝ → ℝ} {z θ : ℝ}
    (h : ContDiffOn ℝ 1 (Function.uncurry f)
      (Set.prod (Set.Ioi (0:ℝ)) (Set.Ioo (0:ℝ) (Real.pi / 2))))
    (hz : 0 < z) (hθ : θ ∈ Set.Ioo (0:ℝ) (Real.pi / 2)) :
    HasDerivAt (fun s : ℝ => f s θ) (Work.Spaces.pz f z θ) z := by
  -- `pz f z θ` is by definition the derivative of the `z`-slice, so it suffices to
  -- know that the slice is differentiable at `z`.
  rw [Work.Spaces.pz, hasDerivAt_deriv_iff]
  -- the domain `(0,∞) × (0,π/2)` is open, so `ContDiffOn` upgrades to `ContDiffAt`
  have hs : IsOpen (Set.prod (Set.Ioi (0:ℝ)) (Set.Ioo (0:ℝ) (Real.pi / 2))) :=
    isOpen_Ioi.prod isOpen_Ioo
  have hp : (z, θ) ∈ Set.prod (Set.Ioi (0:ℝ)) (Set.Ioo (0:ℝ) (Real.pi / 2)) := ⟨hz, hθ⟩
  have hca : ContDiffAt ℝ 1 (Function.uncurry f) (z, θ) := h.contDiffAt (hs.mem_nhds hp)
  have hd : DifferentiableAt ℝ (Function.uncurry f) (z, θ) :=
    hca.differentiableAt (by norm_num)
  -- compose with the differentiable curve `s ↦ (s, θ)`
  have hcurve : DifferentiableAt ℝ (fun s : ℝ => (s, θ)) z := by fun_prop
  exact hd.comp z hcurve

end Work.FTS.RegPkgGal.R2
end
-- ===== merged: Submission.Work.FTS.RegPkgGal.R2.integrableOn_pth_slice =====
section

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

open scoped Real
open MeasureTheory Set

namespace Work.FTS.RegPkgGal.R2

/-! ## Elementary facts about the angular interval -/

/-- `sin θ cos²θ ≤ sin(2θ)` for `θ ∈ (0, π/2)`: pointwise `cos²θ ≤ cos θ ≤ 2cos θ` and
`sin θ ≥ 0`. -/
lemma sin_mul_cos_sq_le_sin_two {θ : ℝ} (hθ : θ ∈ Set.Ioo (0:ℝ) (Real.pi/2)) :
    Real.sin θ * Real.cos θ ^ 2 ≤ Real.sin (2*θ) := by
  have hs0 : 0 ≤ Real.sin θ :=
    le_of_lt (Real.sin_pos_of_pos_of_lt_pi hθ.1 (by linarith [hθ.2, Real.pi_pos]))
  have hc0 : 0 ≤ Real.cos θ :=
    le_of_lt (Real.cos_pos_of_mem_Ioo ⟨by linarith [hθ.1, Real.pi_pos], hθ.2⟩)
  have hc1 : Real.cos θ ≤ 1 := Real.cos_le_one θ
  have hcs : Real.cos θ ^ 2 ≤ 2 * Real.cos θ := by
    nlinarith [mul_nonneg hc0 (sub_nonneg.mpr hc1), hc0]
  rw [Real.sin_two_mul]
  calc Real.sin θ * Real.cos θ ^ 2 ≤ Real.sin θ * (2 * Real.cos θ) :=
        mul_le_mul_of_nonneg_left hcs hs0
    _ = 2 * Real.sin θ * Real.cos θ := by ring

/-- `sin(2θ) > 0` on the open interval `(0, π/2)`. -/
lemma sin_two_pos_of_mem_Ioo {θ : ℝ} (hθ : θ ∈ Set.Ioo (0:ℝ) (Real.pi/2)) :
    0 < Real.sin (2*θ) :=
  Real.sin_pos_of_pos_of_lt_pi (by linarith [hθ.1]) (by linarith [hθ.2, Real.pi_pos])

/-! ## The explicit integrable majorant -/

/-- **The majorant estimate.**  For `0 < α ≤ 1` and `θ ∈ (0, π/2)`,

  `(sin θ cos²θ)^α / sin(2θ) ≤ (π/4)^{1-α/2} (θ^{-(1-α/2)} + (π/2-θ)^{-(1-α/2)})`. -/
lemma sin_mul_cos_sq_pow_div_le_sin_two {α θ : ℝ} (hα : 0 < α) (hα1 : α ≤ 1)
    (hθ : θ ∈ Set.Ioo (0:ℝ) (Real.pi/2)) :
    (Real.sin θ * Real.cos θ ^ 2)^α / Real.sin (2*θ)
      ≤ (Real.pi/4)^(1-α/2) * (θ^(-(1-α/2)) + (Real.pi/2-θ)^(-(1-α/2))) := by
  have hs : 0 < Real.sin (2*θ) := sin_two_pos_of_mem_Ioo hθ
  have hs1 : Real.sin (2*θ) ≤ 1 := Real.sin_le_one _
  have hs0 : 0 ≤ Real.sin θ :=
    le_of_lt (Real.sin_pos_of_pos_of_lt_pi hθ.1 (by linarith [hθ.2, Real.pi_pos]))
  have hA0 : 0 ≤ Real.sin θ * Real.cos θ ^ 2 := mul_nonneg hs0 (sq_nonneg _)
  have hA : (Real.sin θ * Real.cos θ ^ 2)^α ≤ (Real.sin (2*θ))^α :=
    Real.rpow_le_rpow hA0 (sin_mul_cos_sq_le_sin_two hθ) (le_of_lt hα)
  have h2 : (Real.sin (2*θ))^α / Real.sin (2*θ) = (Real.sin (2*θ))^(α-1) := by
    rw [div_eq_mul_inv, ← Real.rpow_neg_one, ← Real.rpow_add hs]
    congr 1
  have h3 : (Real.sin (2*θ))^(α-1) ≤ (Real.sin (2*θ))^(α/2-1) :=
    Real.rpow_le_rpow_of_exponent_ge hs hs1 (by linarith)
  have h4 : (Real.sin (2*θ))^(α/2-1) = (Real.sin (2*θ))^(-(1-α/2)) := by
    congr 1; ring
  calc (Real.sin θ * Real.cos θ ^ 2)^α / Real.sin (2*θ)
      ≤ (Real.sin (2*θ))^α / Real.sin (2*θ) := div_le_div_of_nonneg_right hA hs.le
    _ = (Real.sin (2*θ))^(α-1) := h2
    _ ≤ (Real.sin (2*θ))^(α/2-1) := h3
    _ = (Real.sin (2*θ))^(-(1-α/2)) := h4
    _ ≤ (Real.pi/4)^(1-α/2) * (θ^(-(1-α/2)) + (Real.pi/2-θ)^(-(1-α/2))) :=
        Work.Spaces.sin_rpow_le_majorant (1-α/2) θ (by linarith) ⟨hθ.1.le, hθ.2.le⟩


/-! ## The pointwise bound on the slice -/

/-- On the open interval, `∂_θ g` is bounded by the weighted derivative divided by `sin(2θ)`. -/
lemma abs_pth_le_div {α Cθ z θ : ℝ} {g : ℝ → ℝ → ℝ}
    (hd : ∀ θ ∈ Work.Spaces.Iθ,
      |Work.Spaces.Dth g z θ| ≤ Cθ * z ^ 2 * (Real.sin θ * Real.cos θ ^ 2) ^ α)
    (hθ : θ ∈ Set.Ioo (0:ℝ) (Real.pi/2)) :
    |Work.Spaces.pth g z θ| ≤ Cθ * z ^ 2 *
      ((Real.sin θ * Real.cos θ ^ 2) ^ α / Real.sin (2*θ)) := by
  have hs : 0 < Real.sin (2*θ) := sin_two_pos_of_mem_Ioo hθ
  have h1 : |Work.Spaces.pth g z θ| = |Work.Spaces.Dth g z θ| / Real.sin (2*θ) := by
    rw [Work.Spaces.Dth, abs_mul, abs_of_pos hs]
    exact (mul_div_cancel_left₀ _ (ne_of_gt hs)).symm
  calc |Work.Spaces.pth g z θ| = |Work.Spaces.Dth g z θ| / Real.sin (2*θ) := h1
    _ ≤ (Cθ * z ^ 2 * (Real.sin θ * Real.cos θ ^ 2) ^ α) / Real.sin (2*θ) :=
        div_le_div_of_nonneg_right (hd θ ⟨hθ.1.le, hθ.2.le⟩) hs.le
    _ = Cθ * z ^ 2 * ((Real.sin θ * Real.cos θ ^ 2) ^ α / Real.sin (2*θ)) := by ring

/-! ## Continuity of the slice -/

/-- The slice `θ ↦ ∂_θ g (z, θ)` is continuous on the open angular interval, by differentiating
the `C¹` function `s ↦ g z s`. -/
lemma continuousOn_pth_slice {g : ℝ → ℝ → ℝ} {z : ℝ} (hz : 0 < z)
    (hsm : ContDiffOn ℝ 1 (Function.uncurry g)
      (Set.prod (Set.Ioi (0:ℝ)) (Set.Ioo (0:ℝ) (Real.pi / 2)))) :
    ContinuousOn (fun θ => Work.Spaces.pth g z θ) (Set.Ioo (0:ℝ) (Real.pi/2)) := by
  have hcomp : ContDiffOn ℝ 1 (fun s : ℝ => g z s) (Set.Ioo (0:ℝ) (Real.pi/2)) := by
    have hslice : ContDiffOn ℝ 1 (fun s : ℝ => (z, s)) (Set.Ioo (0:ℝ) (Real.pi/2)) := by fun_prop
    have hmap : Set.MapsTo (fun s : ℝ => (z, s)) (Set.Ioo (0:ℝ) (Real.pi/2))
        (Set.prod (Set.Ioi (0:ℝ)) (Set.Ioo (0:ℝ) (Real.pi / 2))) := fun s hs => ⟨hz, hs⟩
    have h2 := hsm.comp hslice hmap
    simpa [Function.comp_def, Function.uncurry] using h2
  have h := hcomp.continuousOn_deriv_of_isOpen isOpen_Ioo (by norm_num : (1:WithTop ℕ∞) ≤ 1)
  simpa [Work.Spaces.pth] using h

/-! ## The target -/

theorem integrableOn_pth_slice {α Cθ z : ℝ} (hα : 0 < α) (hα1 : α ≤ 1) (hCθ : 0 ≤ Cθ)
    (hz : 0 < z) {g : ℝ → ℝ → ℝ}
    (hsm : ContDiffOn ℝ 1 (Function.uncurry g)
      (Set.prod (Set.Ioi (0:ℝ)) (Set.Ioo (0:ℝ) (Real.pi / 2))))
    (hd : ∀ θ ∈ Work.Spaces.Iθ,
      |Work.Spaces.Dth g z θ| ≤ Cθ * z ^ 2 * (Real.sin θ * Real.cos θ ^ 2) ^ α) :
    MeasureTheory.IntegrableOn (fun s : ℝ => Work.Spaces.pth g z s)
      (Set.Icc 0 (Real.pi / 2)) MeasureTheory.volume := by
  -- work on the open interval: the two endpoints are null
  have hIoo : MeasureTheory.volume.restrict (Set.Icc (0:ℝ) (Real.pi/2))
      = MeasureTheory.volume.restrict (Set.Ioo (0:ℝ) (Real.pi/2)) :=
    (MeasureTheory.Measure.restrict_congr_set MeasureTheory.Ioo_ae_eq_Icc).symm
  set r : ℝ := 1 - α/2 with hrdef
  have hr0 : 0 < r := by rw [hrdef]; linarith
  have hr1 : r < 1 := by rw [hrdef]; linarith
  have hcz : 0 ≤ Cθ * z^2 := mul_nonneg hCθ (sq_nonneg z)
  -- the integrable majorant `Cθ z² · (π/4)^r (θ^{-r} + (π/2-θ)^{-r})`
  set M : ℝ → ℝ := fun θ => Cθ * z^2 * ((Real.pi/4)^r * (θ^(-r) + (Real.pi/2-θ)^(-r)))
    with hMdef
  have hMaj : MeasureTheory.IntegrableOn M (Set.Icc (0:ℝ) (Real.pi/2)) := by
    have h := (Work.Spaces.integrableOn_majorant_rpow r hr0 hr1).integrable.const_mul (Cθ * z^2)
    rw [hMdef]
    exact h
  refine MeasureTheory.Integrable.mono'
    (f := fun s : ℝ => Work.Spaces.pth g z s) (g := M) ?_ ?_ ?_
  · -- the majorant is integrable (on the open interval, by restriction)
    rw [hIoo]
    exact hMaj.mono_set Set.Ioo_subset_Icc_self
  · -- a.e. strong measurability of the slice
    rw [hIoo]
    exact (continuousOn_pth_slice hz hsm).aestronglyMeasurable measurableSet_Ioo
  · -- the a.e. pointwise bound
    rw [hIoo]
    refine MeasureTheory.ae_restrict_of_forall_mem measurableSet_Ioo (fun θ hθ => ?_)
    rw [Real.norm_eq_abs]
    calc |Work.Spaces.pth g z θ| ≤ Cθ * z ^ 2 *
          ((Real.sin θ * Real.cos θ ^ 2) ^ α / Real.sin (2*θ)) :=
          abs_pth_le_div hd hθ
      _ ≤ M θ := by
          rw [hMdef, hrdef]
          exact mul_le_mul_of_nonneg_left
            (sin_mul_cos_sq_pow_div_le_sin_two hα hα1 hθ) hcz

end Work.FTS.RegPkgGal.R2
end
-- ===== merged: Submission.Work.FTS.RegPkgGal.R7d.ode_box_existence =====
section

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

set_option linter.unusedVariables false

namespace Work.FTS.RegPkgGal.R7d

open Set Metric Filter
open scoped Topology

/-! ## Auxiliary facts

The proof below builds a solution of `ẋ = f(t,x)` on `[0,T]` by a fixed-step Picard iteration over
the windows of a partition of `[0,T]`, gluing the local solutions.  The helpers are (i) the
"singleton" form of the within-derivative (the zeroth window has length `0`), (ii)
Picard–Lindelöf on an arbitrary set `S` that contains the closed ball of radius `a` about the
centre (the box `S` of the statement is *not* a ball, but it contains one, with room given by the
strict inclusions), and (iii) the predicate carried by the `n`-th approximation. -/

/-- The derivative of any function within the singleton `{0}`. -/
private theorem hasDerivWithinAt_singleton_zero {E : Type*} [NormedAddCommGroup E]
    [NormedSpace ℝ E] (g : ℝ → E) (v : E) : HasDerivWithinAt g v ({0} : Set ℝ) 0 := by
  rw [hasDerivWithinAt_iff_tendsto_slope]
  have h : ({0} : Set ℝ) \ {0} = ∅ := by ext x; simp
  rw [h, nhdsWithin_empty]
  exact Filter.tendsto_bot

/-- **Picard–Lindelöf on a set containing a ball about the centre.** If `f` is Lipschitz in `x`
and bounded on `S`, continuous in `t` on `S`, and `S` contains the closed ball of radius `a` about
`x₀`, then `f` is Picard–Lindelöf on the window `[tmin, tmax]` with centre `x₀`, provided
`L * (tmax - tmin) ≤ a`. -/
private theorem isPicardLindelof_of_subset
    {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    {f : ℝ → E → E} {S : Set E} {x₀ : E} {tmin tmax a L K : ℝ}
    (ha : 0 ≤ a) (hL : 0 < L) (hK : 0 ≤ K)
    (hball : Metric.closedBall x₀ a ⊆ S)
    (hlip : ∀ t ∈ Set.Icc tmin tmax, LipschitzOnWith ⟨K, hK⟩ (f t) S)
    (hbdd : ∀ t ∈ Set.Icc tmin tmax, ∀ x ∈ S, ‖f t x‖ ≤ L)
    (htcont : ∀ x ∈ S, ContinuousOn (fun t => f t x) (Set.Icc tmin tmax))
    (htle : tmin ≤ tmax) (htmax : L * max (tmax - tmin) 0 ≤ a) :
    IsPicardLindelof f ⟨tmin, le_rfl, htle⟩ x₀ (Real.toNNReal a) 0 (Real.toNNReal L)
      (Real.toNNReal K) := by
  have hball' : Metric.closedBall x₀ (Real.toNNReal a) ⊆ S := by
    rw [show (Real.toNNReal a : ℝ) = a from Real.coe_toNNReal _ ha]
    exact hball
  refine ⟨?_, ?_, ?_, ?_⟩
  · intro t ht
    rw [show Real.toNNReal K = ⟨K, hK⟩ from Real.toNNReal_of_nonneg hK]
    exact (hlip t ht).mono hball'
  · intro x hx
    exact htcont x (hball' hx)
  · intro t ht x hx
    rw [show (Real.toNNReal L : ℝ) = L from Real.coe_toNNReal _ hL.le]
    exact hbdd t ht x (hball' hx)
  · rw [show (Real.toNNReal L : ℝ) = L from Real.coe_toNNReal _ hL.le,
      show (Real.toNNReal a : ℝ) = a from Real.coe_toNNReal _ ha, NNReal.coe_zero, sub_zero]
    have htv : (⟨tmin, le_rfl, htle⟩ : ↑(Set.Icc tmin tmax)).1 = tmin := rfl
    rw [htv, sub_self]
    exact htmax

/-- The predicate carried by the `n`-th approximation: it solves `ẋ = f(t,x)` on `[0,s]` with
`α 0 = u₀`. -/
private structure IsSol (f : ℝ → ℝ × ℝ → ℝ × ℝ) (u₀ : ℝ × ℝ) (s : ℝ)
    (α : ℝ → ℝ × ℝ) : Prop where
  init : α 0 = u₀
  sol : ∀ t ∈ Set.Icc (0:ℝ) s, HasDerivWithinAt α (f t (α t)) (Set.Icc (0:ℝ) s) t

/-- Picard–Lindelöf with an a priori bound, on a finite time horizon `[0,T]` and on an
axis-parallel box: `f` is Lipschitz in `x` (const `Klip`) and bounded (`L`) on the outer box
`Icc zlo' zhi' ×ˢ Icc θlo' θhi'`, continuous in `t` there, the inner box `Icc zlo zhi ×ˢ Icc θlo θhi`
sits strictly inside the outer one (`zlo' < zlo`, `zhi < zhi'`, `θlo' < θlo`, `θhi < θhi'`), the
starting point `u₀` lies in the inner box, and *every* solution through `u₀` on any `[0,T']` with
`T' ≤ T` stays in the inner box (the a priori estimate). Then a solution exists on all of `[0,T]`.
Intended proof: a finite iteration over windows of length `δ = ε/(2L)` with
`ε = min (zlo-zlo') (zhi'-zhi) (θlo-θlo') (θhi'-θhi)`, each step being Mathlib's
`IsPicardLindelof.exists_eq_forall_mem_Icc_hasDerivWithinAt` with centre `α (nδ)` and radius `ε/2`,
glued by `HasDerivWithinAt.union` (there is a ready-made glue lemma
`Work.FTS.Galerkin.Ode.hasDerivWithinAt_glue` in this workspace, and the sibling proof
`Work.FTS.Galerkin.exists_global_solution_of_bound` does the same iteration for the
`[0,∞)`/ball case and is a good template). -/
theorem ode_box_existence
    (f : ℝ → ℝ × ℝ → ℝ × ℝ) (u₀ : ℝ × ℝ) {T L Klip : ℝ}
    {zlo zhi θlo θhi zlo' zhi' θlo' θhi' : ℝ}
    (hT : 0 ≤ T) (hL : 0 < L) (hKlip : 0 ≤ Klip)
    (hu₀ : u₀.1 ∈ Set.Icc zlo zhi ∧ u₀.2 ∈ Set.Icc θlo θhi)
    (hzi : zlo' < zlo) (hzs : zhi < zhi') (hti : θlo' < θlo) (hts : θhi < θhi')
    (hlip : ∀ t ∈ Set.Icc (0:ℝ) T, LipschitzOnWith ⟨Klip, hKlip⟩ (f t)
      (Set.Icc zlo' zhi' ×ˢ Set.Icc θlo' θhi'))
    (hbdd : ∀ t ∈ Set.Icc (0:ℝ) T, ∀ x ∈ Set.Icc zlo' zhi' ×ˢ Set.Icc θlo' θhi', ‖f t x‖ ≤ L)
    (htcont : ∀ x ∈ Set.Icc zlo' zhi' ×ˢ Set.Icc θlo' θhi',
      ContinuousOn (fun t => f t x) (Set.Icc (0:ℝ) T))
    (htraj : ∀ T' ∈ Set.Icc (0:ℝ) T, ∀ α : ℝ → ℝ × ℝ, α 0 = u₀ →
      (∀ t ∈ Set.Icc (0:ℝ) T', HasDerivWithinAt α (f t (α t)) (Set.Icc (0:ℝ) T') t) →
      ∀ t ∈ Set.Icc (0:ℝ) T', (α t).1 ∈ Set.Icc zlo zhi ∧ (α t).2 ∈ Set.Icc θlo θhi) :
    ∃ α : ℝ → ℝ × ℝ, α 0 = u₀ ∧
      ∀ t ∈ Set.Icc (0:ℝ) T, HasDerivWithinAt α (f t (α t)) (Set.Icc (0:ℝ) T) t := by
  classical
  -- ### The margin `ε` between the inner and the outer box
  obtain ⟨hzi', hzs', hti', hts'⟩ :
      0 < zlo - zlo' ∧ 0 < zhi' - zhi ∧ 0 < θlo - θlo' ∧ 0 < θhi' - θhi :=
    ⟨by linarith, by linarith, by linarith, by linarith⟩
  set ε : ℝ := min (min (zlo - zlo') (zhi' - zhi)) (min (θlo - θlo') (θhi' - θhi)) with hεdef
  have hεpos : 0 < ε := by
    rw [hεdef]; exact lt_min (lt_min hzi' hzs') (lt_min hti' hts')
  have hεle1 : ε ≤ zlo - zlo' := by
    rw [hεdef]; exact le_trans (min_le_left _ _) (min_le_left _ _)
  have hεle2 : ε ≤ zhi' - zhi := by
    rw [hεdef]; exact le_trans (min_le_left _ _) (min_le_right _ _)
  have hεle3 : ε ≤ θlo - θlo' := by
    rw [hεdef]; exact le_trans (min_le_right _ _) (min_le_left _ _)
  have hεle4 : ε ≤ θhi' - θhi := by
    rw [hεdef]; exact le_trans (min_le_right _ _) (min_le_right _ _)
  -- ### The ball of radius `ε` about a point of the inner box lies in the outer box
  have hball : ∀ x ∈ Set.Icc zlo zhi ×ˢ Set.Icc θlo θhi,
      Metric.closedBall x ε ⊆ Set.Icc zlo' zhi' ×ˢ Set.Icc θlo' θhi' := by
    rintro x ⟨hx1, hx2⟩ y hy
    rw [Metric.mem_closedBall, Prod.dist_eq, Real.dist_eq, Real.dist_eq] at hy
    have h1 : -ε ≤ y.1 - x.1 := (abs_le.mp (le_trans (le_max_left _ _) hy)).1
    have h2 : y.1 - x.1 ≤ ε := (abs_le.mp (le_trans (le_max_left _ _) hy)).2
    have h3 : -ε ≤ y.2 - x.2 := (abs_le.mp (le_trans (le_max_right _ _) hy)).1
    have h4 : y.2 - x.2 ≤ ε := (abs_le.mp (le_trans (le_max_right _ _) hy)).2
    rw [Set.mem_Icc] at hx1 hx2
    constructor
    · rw [Set.mem_Icc]; exact ⟨by linarith [hx1.1], by linarith [hx1.2]⟩
    · rw [Set.mem_Icc]; exact ⟨by linarith [hx2.1], by linarith [hx2.2]⟩
  -- ### The number of steps and the step length
  obtain ⟨N, hN⟩ : ∃ N : ℕ, T * L / ε < (N : ℝ) := exists_nat_gt _
  have hNpos : (0:ℝ) < (N:ℝ) :=
    lt_of_le_of_lt (div_nonneg (mul_nonneg hT hL.le) hεpos.le) hN
  have hNne : (N:ℝ) ≠ 0 := hNpos.ne'
  set δ : ℝ := T / N with hδdef
  have hδnn : 0 ≤ δ := by rw [hδdef]; exact div_nonneg hT hNpos.le
  have hNδ : (N:ℝ) * δ = T := by
    rw [hδdef]
    field_simp
  have hNL : T * L ≤ (N:ℝ) * ε := by
    have h2 : (T * L / ε) * ε < (N:ℝ) * ε := mul_lt_mul_of_pos_right hN hεpos
    rw [div_mul_cancel₀ _ hεpos.ne'] at h2
    linarith
  have hLδ : L * δ ≤ ε := by
    have h3 : L * δ = T * L / (N:ℝ) := by rw [hδdef]; ring
    rw [h3, div_le_iff₀ hNpos]
    linarith
  -- ### The induction: a solution on `[0, (min n N) δ]` for every `n`
  have hkey : ∀ n : ℕ, ∃ α : ℝ → ℝ × ℝ,
      IsSol f u₀ (((min n N : ℕ) : ℝ) * δ) α := by
    intro n
    induction n with
    | zero =>
      have h0 : (((min 0 N : ℕ)) : ℝ) * δ = 0 := by
        rw [Nat.min_eq_left (Nat.zero_le N)]; simp
      refine ⟨fun _ => u₀, rfl, ?_⟩
      intro t ht
      rw [h0] at ht ⊢
      rw [Set.Icc_self, Set.mem_singleton_iff] at ht
      rw [Set.Icc_self, ht]
      exact hasDerivWithinAt_singleton_zero _ _
    | succ k ih =>
      by_cases hk : k < N
      · -- ### one Picard step on the window `[kδ, (k+1)δ]`
        have hkmin : min k N = k := Nat.min_eq_left hk.le
        have hk1min : min (k + 1) N = k + 1 := Nat.min_eq_left (Nat.succ_le_of_lt hk)
        rw [hk1min]
        obtain ⟨α, hα0, hαsol⟩ := ih
        rw [hkmin] at hαsol
        set t₀ : ℝ := (k:ℝ) * δ with ht₀def
        have hαsol' : ∀ t ∈ Set.Icc (0:ℝ) t₀,
            HasDerivWithinAt α (f t (α t)) (Set.Icc (0:ℝ) t₀) t := by
          rw [ht₀def]; exact hαsol
        have ht0nn : 0 ≤ t₀ := by rw [ht₀def]; positivity
        have ht0T : t₀ ≤ T := by
          have h1 : (k:ℝ) ≤ (N:ℝ) := by exact_mod_cast hk.le
          calc t₀ = (k:ℝ) * δ := ht₀def
            _ ≤ (N:ℝ) * δ := mul_le_mul_of_nonneg_right h1 hδnn
            _ = T := hNδ
        have hxk : α t₀ ∈ Set.Icc zlo zhi ×ˢ Set.Icc θlo θhi :=
          Set.mem_prod.mpr (htraj t₀ ⟨ht0nn, ht0T⟩ α hα0 hαsol' t₀ ⟨ht0nn, le_rfl⟩)
        have hcast : (((k + 1 : ℕ)) : ℝ) * δ = t₀ + δ := by
          rw [ht₀def]; push_cast; ring
        have hle : t₀ ≤ t₀ + δ := by linarith [hδnn]
        have hwin : Set.Icc t₀ (t₀ + δ) ⊆ Set.Icc (0:ℝ) T := by
          intro t ht
          refine ⟨le_trans ht0nn ht.1, ?_⟩
          have h1 : (((k + 1 : ℕ)) : ℝ) ≤ (N:ℝ) := by
            exact_mod_cast (Nat.succ_le_of_lt hk)
          calc t ≤ t₀ + δ := ht.2
            _ = (((k + 1 : ℕ)) : ℝ) * δ := hcast.symm
            _ ≤ (N:ℝ) * δ := mul_le_mul_of_nonneg_right h1 hδnn
            _ = T := hNδ
        have hpl : IsPicardLindelof f ⟨t₀, le_rfl, hle⟩ (α t₀) (Real.toNNReal ε) 0
            (Real.toNNReal L) (Real.toNNReal Klip) := by
          refine isPicardLindelof_of_subset hεpos.le hL hKlip (hball (α t₀) hxk) ?_ ?_ ?_ hle ?_
          · intro t ht; exact hlip t (hwin ht)
          · intro t ht x hx; exact hbdd t (hwin ht) x hx
          · intro x hx; exact (htcont x hx).mono hwin
          · rw [show t₀ + δ - t₀ = δ from by ring, max_eq_left hδnn]
            exact hLδ
        obtain ⟨γ, hγ0, hγd⟩ := hpl.exists_eq_forall_mem_Icc_hasDerivWithinAt
          (x := α t₀) (hx := Metric.mem_closedBall_self (by simp))
        have hglue : ∀ t ∈ Set.Icc (0:ℝ) (t₀ + δ),
            HasDerivWithinAt (fun y : ℝ => if y ≤ t₀ then α y else γ y)
              (f t (if t ≤ t₀ then α t else γ t)) (Set.Icc (0:ℝ) (t₀ + δ)) t :=
          Work.FTS.Galerkin.Ode.hasDerivWithinAt_glue (f := α) (g := γ) (a := 0) (b := t₀)
            (c := t₀ + δ) ht0nn hle hγ0.symm
            (v := fun x => f x (if x ≤ t₀ then α x else γ x))
            (fun x hxm => by
              have h := hαsol' x hxm
              have hif : (if x ≤ t₀ then α x else γ x) = α x := ite_eq_left hxm.2
              rwa [← hif] at h)
            (fun x hxm => by
              have h := hγd x hxm
              have hif : (if x ≤ t₀ then α x else γ x) = γ x := by
                by_cases hxb : x ≤ t₀
                · rw [ite_eq_left hxb]
                  have hxeq : x = t₀ := le_antisymm hxb hxm.1
                  rw [hxeq]
                  exact hγ0.symm
                · exact ite_eq_right hxb
              rwa [← hif] at h)
        refine ⟨fun y : ℝ => if y ≤ t₀ then α y else γ y, ?_, ?_⟩
        · show (if (0:ℝ) ≤ t₀ then α 0 else γ 0) = u₀
          rw [ite_eq_left ht0nn]
          exact hα0
        · intro t ht
          rw [hcast] at ht ⊢
          exact hglue t ht
      · -- ### beyond `N` steps the interval is already full: keep the approximation
        have hkN : N ≤ k := Nat.le_of_not_lt hk
        have hm1 : min k N = N := Nat.min_eq_right hkN
        have hm2 : min (k + 1) N = N := Nat.min_eq_right (le_trans hkN (Nat.le_succ k))
        rw [hm2]
        obtain ⟨α, hα⟩ := ih
        rw [hm1] at hα
        exact ⟨α, hα⟩
  -- ### The `N`-th approximation is the required global solution
  obtain ⟨α, hα0, hαsol⟩ := hkey N
  rw [Nat.min_self N] at hαsol
  rw [hNδ] at hαsol
  exact ⟨α, hα0, hαsol⟩

end Work.FTS.RegPkgGal.R7d
end
-- ===== merged: Submission.Work.FTS.Regularity.Moduli.fstarLip =====
section

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

namespace Work.FTS.Regularity.Moduli

/-- Algebraic key bound: for `z, z' ≥ 0` the factor `|1 - z z'|` appearing in the
difference `F_*(z) - F_*(z')` is dominated by `(1+z)²(1+z')²`. -/
private lemma abs_one_sub_mul_le {z z' : ℝ} (hz : 0 ≤ z) (hz' : 0 ≤ z') :
    |1 - z * z'| ≤ (1 + z) ^ 2 * (1 + z') ^ 2 := by
  have hzz : 0 ≤ z * z' := mul_nonneg hz hz'
  have hA1 : 1 ≤ (1 + z) * (1 + z') := by nlinarith
  have hmax : |1 - z * z'| ≤ (1 + z) * (1 + z') := by
    by_cases h : z * z' ≤ 1
    · rw [abs_of_nonneg (by linarith : 0 ≤ 1 - z * z')]
      nlinarith
    · rw [abs_of_neg (by linarith : 1 - z * z' < 0)]
      nlinarith
  have hsq : (1 + z) * (1 + z') ≤ ((1 + z) * (1 + z')) ^ 2 := by nlinarith
  calc |1 - z * z'| ≤ (1 + z) * (1 + z') := hmax
    _ ≤ ((1 + z) * (1 + z')) ^ 2 := hsq
    _ = (1 + z) ^ 2 * (1 + z') ^ 2 := by ring

/-- The exact difference of the profile `F_*(z) = 2z/(1+z)²` factors through the
difference `z - z'` with a bounded coefficient. -/
private lemma fstar_sub {z z' : ℝ} (hz : 0 ≤ z) (hz' : 0 ≤ z') :
    Work.FM.Fstar z - Work.FM.Fstar z' =
      2 * (z - z') * (1 - z * z') / ((1 + z) ^ 2 * (1 + z') ^ 2) := by
  have h1 : (1 + z) ^ 2 ≠ 0 := by positivity
  have h2 : (1 + z') ^ 2 ≠ 0 := by positivity
  simp only [Work.FM.Fstar]
  field_simp
  ring

lemma fstarLip {z z' : ℝ} (hz : 0 ≤ z) (hz' : 0 ≤ z') :
    |Work.FM.Fstar z - Work.FM.Fstar z'| ≤ 2 * |z - z'| := by
  rw [fstar_sub hz hz', abs_div, abs_mul, abs_mul,
    abs_of_nonneg (by norm_num : (0 : ℝ) ≤ 2)]
  have hden : 0 < (1 + z) ^ 2 * (1 + z') ^ 2 := by positivity
  rw [abs_of_pos hden, div_le_iff₀ hden]
  have hkey : |1 - z * z'| ≤ (1 + z) ^ 2 * (1 + z') ^ 2 := abs_one_sub_mul_le hz hz'
  have h2 : (0 : ℝ) ≤ 2 * |z - z'| := by positivity
  linarith [mul_le_mul_of_nonneg_left hkey h2]

end Work.FTS.Regularity.Moduli
end
-- ===== merged: Submission.Work.FTS.StrongEps.EpsZero.Bridge.tendsto_pz_zero_of_trace =====
section

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

namespace Work.FTS.StrongEps.EpsZero.Bridge

open Filter

/-- **A radial trace bound forces the radial derivative to vanish at the axis.**  If
`z * (Dz f z θ * w z) ^ 2 → 0` as `z → 0⁺` then `pz f z θ → 0` as `z → 0⁺`.
For `z > 0` one has `Dz f z θ = z * pz f z θ` and `w z = (1+z)^2 / z^2`, hence
`z * (Dz f z θ * w z) ^ 2 = (pz f z θ)^2 * (1+z)^4 / z`; since `z ≤ (1+z)^4` for `z ≥ 0`
this gives `(pz f z θ)^2 ≤ z * (Dz f z θ * w z) ^ 2`, and the claim follows by a squeeze
argument plus the continuity of `Real.sqrt` at `0`. -/
theorem tendsto_pz_zero_of_trace {f : ℝ → ℝ → ℝ} {θ : ℝ}
    (h : Filter.Tendsto (fun z : ℝ => z * (Work.Spaces.Dz f z θ * Work.Spaces.w z) ^ 2)
      (nhdsWithin (0 : ℝ) (Set.Ioi 0)) (nhds (0 : ℝ))) :
    Filter.Tendsto (fun z : ℝ => Work.Spaces.pz f z θ)
      (nhdsWithin (0 : ℝ) (Set.Ioi 0)) (nhds (0 : ℝ)) := by
  refine squeeze_zero_norm'
    (a := fun z : ℝ => Real.sqrt (z * (Work.Spaces.Dz f z θ * Work.Spaces.w z) ^ 2)) ?_ ?_
  · -- For `z > 0` the trace dominates `(pz f z θ)²`, so `|pz f z θ| ≤ √(trace)`.
    filter_upwards [self_mem_nhdsWithin] with z hz
    have hzpos : 0 < z := hz
    have hz0 : z ≠ 0 := ne_of_gt hzpos
    have hkey : z * (z * Work.Spaces.pz f z θ * ((1 + z) ^ 2 / z ^ 2)) ^ 2
        = (Work.Spaces.pz f z θ) ^ 2 * ((1 + z) ^ 4 / z) := by
      field_simp
    have hmain : (Work.Spaces.pz f z θ) ^ 2
        ≤ z * (Work.Spaces.Dz f z θ * Work.Spaces.w z) ^ 2 := by
      simp only [Work.Spaces.Dz, Work.Spaces.w]
      rw [hkey]
      calc (Work.Spaces.pz f z θ) ^ 2
          = (Work.Spaces.pz f z θ) ^ 2 * 1 := by ring
        _ ≤ (Work.Spaces.pz f z θ) ^ 2 * ((1 + z) ^ 4 / z) := by
            refine mul_le_mul_of_nonneg_left ?_ (sq_nonneg _)
            rw [le_div_iff₀ hzpos]
            have hge1 : (1 : ℝ) ≤ 1 + z := by linarith
            have hp : (1 + z) ≤ (1 + z) ^ 4 := by
              simpa using pow_le_pow_right₀ hge1 (show (1 : ℕ) ≤ 4 by norm_num)
            linarith
    simpa only [Real.norm_eq_abs] using Real.abs_le_sqrt hmain
  · -- `√` is continuous at `0`, where it takes the value `0`.
    simpa [Function.comp_def] using (Real.continuous_sqrt.tendsto 0).comp h

end Work.FTS.StrongEps.EpsZero.Bridge
end
-- ===== merged: Submission.Work.FTS.StrongEps.JepsHkMem.integrableOn_sliceIntegral_of_lintegral_lt_top =====
section

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

namespace Work.FTS.StrongEps.JepsHkMem

theorem integrableOn_sliceIntegral_of_lintegral_lt_top {F : ℝ → ℝ → ℝ}
    (hnn : ∀ z θ, 0 ≤ F z θ)
    (hsl : ∀ z ∈ Work.Spaces.Iz, MeasureTheory.IntegrableOn (fun θ => F z θ) Work.Spaces.Iθ)
    (hmeas : MeasureTheory.AEStronglyMeasurable (fun q : ℝ × ℝ => F q.1 q.2)
      ((MeasureTheory.volume.restrict Work.Spaces.Iz).prod
        (MeasureTheory.volume.restrict Work.Spaces.Iθ)))
    (hfin : (∫⁻ z in Work.Spaces.Iz, ∫⁻ θ in Work.Spaces.Iθ, ENNReal.ofReal (F z θ)) < ⊤) :
    MeasureTheory.IntegrableOn (fun z => ∫ θ in Work.Spaces.Iθ, F z θ) Work.Spaces.Iz := by
  have hGfin : MeasureTheory.HasFiniteIntegral (fun q : ℝ × ℝ => F q.1 q.2)
      ((MeasureTheory.volume.restrict Work.Spaces.Iz).prod
        (MeasureTheory.volume.restrict Work.Spaces.Iθ)) := by
    rw [MeasureTheory.hasFiniteIntegral_iff_ofReal
      (Filter.Eventually.of_forall (fun q : ℝ × ℝ => hnn q.1 q.2))]
    have hton := MeasureTheory.lintegral_lintegral
      (μ := MeasureTheory.volume.restrict Work.Spaces.Iz)
      (ν := MeasureTheory.volume.restrict Work.Spaces.Iθ)
      (f := fun z θ => ENNReal.ofReal (F z θ))
      (hmeas.aemeasurable.ennreal_ofReal)
    rw [← hton]
    exact hfin
  have hGint : MeasureTheory.Integrable (fun q : ℝ × ℝ => F q.1 q.2)
      ((MeasureTheory.volume.restrict Work.Spaces.Iz).prod
        (MeasureTheory.volume.restrict Work.Spaces.Iθ)) := ⟨hmeas, hGfin⟩
  have hslice : MeasureTheory.Integrable
      (fun z => ∫ θ, ‖F z θ‖ ∂(MeasureTheory.volume.restrict Work.Spaces.Iθ))
      (MeasureTheory.volume.restrict Work.Spaces.Iz) :=
    hGint.integral_norm_prod_left
  refine hslice.congr ?_
  filter_upwards with z
  exact MeasureTheory.integral_congr_ae
    (Filter.Eventually.of_forall fun θ => Real.norm_of_nonneg (hnn z θ))

end Work.FTS.StrongEps.JepsHkMem
end
-- ===== merged: Submission.Work.FTS.StrongEps.StepFacts.TopSq =====
section

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

noncomputable section

open scoped Real Topology
open MeasureTheory Set Filter

namespace Work.FTS.StrongEps.StepFacts

set_option autoImplicit false

/-- The top-order slots of `HkIntegrand α m f`: the pure `D_z^m`-slot and the mixed slots whose
order `i + j` is exactly `m` (with `i ≥ 1`, as in `HkIntegrand`). -/
def TopSq (α : ℝ) (m : ℕ) (f : ℝ → ℝ → ℝ) (z θ : ℝ) : ℝ :=
  (Work.Spaces.DzIter m f z θ
      * (Work.Spaces.w z / (Real.sin (2 * θ)) ^ (Work.Spaces.eta / 2))) ^ 2
    + ∑ i ∈ Finset.range (m + 1), ∑ j ∈ Finset.range (m + 1),
        if 1 ≤ i ∧ i + j = m then (Work.Spaces.mixed j i f z θ * Work.Spaces.Wt α z θ) ^ 2
        else 0

/-- `TopSq` is a sum of squares, hence nonnegative. -/
theorem TopSq_nonneg (α : ℝ) (m : ℕ) (f : ℝ → ℝ → ℝ) (z θ : ℝ) :
    0 ≤ TopSq α m f z θ := by
  refine add_nonneg (sq_nonneg _) ?_
  exact Finset.sum_nonneg fun i _ => Finset.sum_nonneg fun j _ => by
    split_ifs with h
    · exact sq_nonneg _
    · exact le_refl 0

/-- **The combinatorial splitting of the mixed double sum.**  The mixed part of `HkIntegrand` at
level `m` is the mixed part at level `m - 1` plus the terms of exact order `m`.

The proof compares the two sides pointwise: for natural `i j`,
`[1 ≤ i ∧ i + j ≤ m] = [1 ≤ i ∧ i + j ≤ m - 1] + [1 ≤ i ∧ i + j = m]` as indicator functions,
and the terms with `i = m` or `j = m` in the level-`m-1` indicator already vanish (there
`i + j ≥ m > m - 1`), so the sum over `range (m+1)²` of the level-`m-1` indicator equals the sum
over `range m × range m`. -/
theorem mixed_sum_step (X : ℕ → ℕ → ℝ) (m : ℕ) :
    (∑ i ∈ Finset.range (m + 1), ∑ j ∈ Finset.range (m + 1),
        (if 1 ≤ i ∧ i + j ≤ m then X i j else 0))
      = (∑ i ∈ Finset.range m, ∑ j ∈ Finset.range m,
          (if 1 ≤ i ∧ i + j ≤ m - 1 then X i j else 0))
        + (∑ i ∈ Finset.range (m + 1), ∑ j ∈ Finset.range (m + 1),
            (if 1 ≤ i ∧ i + j = m then X i j else 0)) := by
  -- the pointwise indicator identity
  have hpt : ∀ i j : ℕ,
      (if 1 ≤ i ∧ i + j ≤ m then X i j else 0)
        = (if 1 ≤ i ∧ i + j ≤ m - 1 then X i j else 0)
          + (if 1 ≤ i ∧ i + j = m then X i j else 0) := by
    intro i j
    by_cases h1 : 1 ≤ i
    · by_cases h2 : i + j ≤ m - 1
      · rw [if_pos ⟨h1, by omega⟩, if_pos ⟨h1, h2⟩, if_neg (by omega), add_zero]
      · by_cases h3 : i + j = m
        · rw [if_pos ⟨h1, by omega⟩, if_neg (by omega), if_pos ⟨h1, h3⟩, zero_add]
        · rw [if_neg (by omega), if_neg (by omega), if_neg (by omega), add_zero]
    · rw [if_neg (by tauto), if_neg (by tauto), if_neg (by tauto), add_zero]
  -- the level-`m-1` sum over `range (m+1)²` equals the one over `range m × range m`
  have hshift : (∑ i ∈ Finset.range (m + 1), ∑ j ∈ Finset.range (m + 1),
        (if 1 ≤ i ∧ i + j ≤ m - 1 then X i j else 0))
      = ∑ i ∈ Finset.range m, ∑ j ∈ Finset.range m,
          (if 1 ≤ i ∧ i + j ≤ m - 1 then X i j else 0) := by
    have hinner : ∀ i : ℕ, (∑ j ∈ Finset.range (m + 1),
          (if 1 ≤ i ∧ i + j ≤ m - 1 then X i j else 0))
        = ∑ j ∈ Finset.range m, (if 1 ≤ i ∧ i + j ≤ m - 1 then X i j else 0) := by
      intro i
      refine (Finset.sum_subset (Finset.range_subset_range.mpr (Nat.le_succ m)) ?_).symm
      intro j hj hnj
      rw [Finset.mem_range] at hj hnj
      have : j = m := by omega
      subst this
      exact if_neg (by rintro ⟨h1, h2⟩; omega)
    rw [Finset.sum_congr rfl (fun i _ => hinner i)]
    refine (Finset.sum_subset (Finset.range_subset_range.mpr (Nat.le_succ m)) ?_).symm
    intro i hi hni
    rw [Finset.mem_range] at hi hni
    have : i = m := by omega
    subst this
    refine Finset.sum_eq_zero fun j hj => if_neg ?_
    rintro ⟨h1, h2⟩
    omega
  rw [Finset.sum_congr rfl (fun i _ => Finset.sum_congr rfl (fun j _ => hpt i j))]
  simp only [Finset.sum_add_distrib]
  rw [hshift]

/-- **The level-`m` integrand splits into the level-`(m-1)` integrand and the top slots.** -/
theorem HkIntegrand_le_prev_add_TopSq (α : ℝ) (m : ℕ) (hm : 1 ≤ m) (f : ℝ → ℝ → ℝ)
    (z θ : ℝ) :
    Work.Spaces.HkIntegrand α m f z θ
      ≤ Work.Spaces.HkIntegrand α (m - 1) f z θ + TopSq α m f z θ := by
  have hm' : m - 1 + 1 = m := Nat.sub_add_cancel hm
  -- the pure `D_z` sums
  have hZ : (∑ i ∈ Finset.range (m + 1),
        (Work.Spaces.DzIter i f z θ
          * (Work.Spaces.w z / (Real.sin (2 * θ)) ^ (Work.Spaces.eta / 2))) ^ 2)
      = (∑ i ∈ Finset.range (m - 1 + 1),
          (Work.Spaces.DzIter i f z θ
            * (Work.Spaces.w z / (Real.sin (2 * θ)) ^ (Work.Spaces.eta / 2))) ^ 2)
        + (Work.Spaces.DzIter m f z θ
            * (Work.Spaces.w z / (Real.sin (2 * θ)) ^ (Work.Spaces.eta / 2))) ^ 2 := by
    rw [hm']
    exact Finset.sum_range_succ _ _
  -- the mixed sums
  have hM := mixed_sum_step (fun i j => (Work.Spaces.mixed j i f z θ * Work.Spaces.Wt α z θ) ^ 2)
    m
  have hM' : (∑ i ∈ Finset.range m, ∑ j ∈ Finset.range m,
        (if 1 ≤ i ∧ i + j ≤ m - 1 then
          (Work.Spaces.mixed j i f z θ * Work.Spaces.Wt α z θ) ^ 2 else 0))
      = (∑ i ∈ Finset.range (m - 1 + 1), ∑ j ∈ Finset.range (m - 1 + 1),
        (if 1 ≤ i ∧ i + j ≤ m - 1 then
          (Work.Spaces.mixed j i f z θ * Work.Spaces.Wt α z θ) ^ 2 else 0)) := by
    rw [hm']
  rw [Work.Spaces.HkIntegrand, Work.Spaces.HkIntegrand, TopSq]
  rw [hZ, hM, hM']
  linarith

end Work.FTS.StrongEps.StepFacts
end
end
-- ===== merged: Submission.Work.FTS.StrongPersist.L3Rhs.window_le_slot =====
section

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

namespace Work.FTS.StrongPersist.L3Rhs

open MeasureTheory Set

theorem window_le_slot {v : ℝ → ℝ}
    (hv : MeasureTheory.IntegrableOn (fun x => (v x * Work.Spaces.w x) ^ 2) Work.Spaces.Iz) :
    ∫ x in (1 : ℝ)..2, (v x) ^ 2
      ≤ ∫ x in Work.Spaces.Iz, (v x * Work.Spaces.w x) ^ 2 := by
  -- On `(1,2)` the weight is at least `1`.
  have hw1 : ∀ x ∈ Set.Ioc (1 : ℝ) 2, 1 ≤ Work.Spaces.w x := by
    intro x hx
    have hx0 : 0 < x := lt_of_lt_of_le one_pos hx.1.le
    rw [Work.Spaces.w, one_le_div (pow_pos hx0 2)]
    nlinarith [hx0]
  -- Hence `(v x)² ≤ (v x · w x)²` pointwise there.
  have hpt : ∀ x ∈ Set.Ioc (1 : ℝ) 2, (v x) ^ 2 ≤ (v x * Work.Spaces.w x) ^ 2 := by
    intro x hx
    have hwx : 1 ≤ Work.Spaces.w x := hw1 x hx
    have hw0 : 0 ≤ Work.Spaces.w x := le_trans zero_le_one hwx
    have hle : |v x| ≤ |v x| * Work.Spaces.w x := by
      calc |v x| = |v x| * 1 := (mul_one _).symm
        _ ≤ |v x| * Work.Spaces.w x := by gcongr
    have hsq : (v x) ^ 2 = |v x| ^ 2 := (sq_abs _).symm
    have hsq2 : (v x * Work.Spaces.w x) ^ 2 = (|v x| * Work.Spaces.w x) ^ 2 := by
      rw [← sq_abs (v x * Work.Spaces.w x), abs_mul, abs_of_nonneg hw0]
    rw [hsq, hsq2]
    exact pow_le_pow_left₀ (abs_nonneg _) hle 2
  have hsub : Set.Ioc (1 : ℝ) 2 ⊆ Work.Spaces.Iz := by
    intro x hx
    exact le_trans zero_le_one hx.1.le
  have hinteg : MeasureTheory.IntegrableOn (fun x => (v x * Work.Spaces.w x) ^ 2)
      (Set.Ioc (1 : ℝ) 2) :=
    hv.mono_set hsub
  -- Function domination on the fixed set `(1,2)`.
  have hmono : ∫ x in Set.Ioc (1 : ℝ) 2, (v x) ^ 2
      ≤ ∫ x in Set.Ioc (1 : ℝ) 2, (v x * Work.Spaces.w x) ^ 2 :=
    integral_mono_of_nonneg (ae_of_all _ fun x => sq_nonneg _) hinteg
      ((ae_restrict_iff' measurableSet_Ioc).mpr (ae_of_all _ fun x hx => hpt x hx))
  -- Domain inclusion `(1,2) ⊆ [0,∞)`.
  have hsub2 : ∫ x in Set.Ioc (1 : ℝ) 2, (v x * Work.Spaces.w x) ^ 2
      ≤ ∫ x in Work.Spaces.Iz, (v x * Work.Spaces.w x) ^ 2 :=
    setIntegral_mono_set hv (ae_of_all _ fun x => sq_nonneg _) hsub.eventuallySubset
  rw [intervalIntegral.integral_of_le (by norm_num : (1 : ℝ) ≤ 2)]
  exact le_trans hmono hsub2

end Work.FTS.StrongPersist.L3Rhs
end
-- ===== merged: Submission.Work.FTS.StrongPersist.N6Trans.Hon.TraceAux =====
section

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

noncomputable section
open scoped Real Topology
open MeasureTheory Set Filter

namespace Work.FTS.StrongPersist.N6Trans.Hon

set_option autoImplicit false
/-! ## Elementary algebra of the weight -/

theorem w_sq_eq (z : ℝ) : (Work.Spaces.w z) ^ 2 = (1 + z) ^ 4 / z ^ 4 := by
  have h1 : ((1 + z) ^ 2) ^ 2 = (1 + z) ^ 4 := by rw [← pow_mul]
  have h2 : (z ^ 2) ^ 2 = z ^ 4 := by rw [← pow_mul]
  rw [Work.Spaces.w, div_pow, h1, h2]

theorem one_le_w_sq {z : ℝ} (hz : 0 < z) : 1 ≤ (Work.Spaces.w z) ^ 2 := by
  rw [w_sq_eq, le_div_iff₀ (by positivity)]
  simpa using pow_le_pow_left₀ (le_of_lt hz) (by linarith : z ≤ 1 + z) 4

theorem one_div_zpow_four_le_w_sq {z : ℝ} (hz : 0 < z) : 1 / z ^ 4 ≤ (Work.Spaces.w z) ^ 2 := by
  rw [w_sq_eq, div_le_div_iff_of_pos_right (by positivity)]
  exact one_le_pow₀ (by linarith)

theorem z_mul_w_sq_mul (z v : ℝ) (hz : z ≠ 0) :
    z * (v * Work.Spaces.w z) ^ 2 = (1 + z) ^ 4 * (v ^ 2 / z ^ 3) := by
  rw [mul_pow, w_sq_eq]
  field_simp

theorem z_mul_w_sq_mul' (z v : ℝ) :
    z * (v * Work.Spaces.w z) ^ 2 = (Work.Spaces.w z) ^ 2 * (z * v ^ 2) := by ring

/-! ## Vanishing integrals on shrinking sets -/

/-- The intersection of the shrinking intervals `(0, 1/(n+1))` is empty. -/
theorem iInter_Ioo_one_div_succ_eq_empty :
    (⋂ n : ℕ, Set.Ioo (0 : ℝ) (1 / ((n : ℝ) + 1))) = ∅ := by
  rw [Set.eq_empty_iff_forall_notMem]
  intro x hx
  have hx0 : 0 < x := (Set.mem_iInter.mp hx 0).1
  obtain ⟨n, hn⟩ := exists_nat_one_div_lt hx0
  exact absurd (Set.mem_iInter.mp hx n).2 (not_lt.mpr hn.le)

/-- The intersection of the shrinking tails `(n+1, ∞)` is empty. -/
theorem iInter_Ioi_nat_succ_eq_empty :
    (⋂ n : ℕ, Set.Ioi ((n : ℝ) + 1)) = ∅ := by
  rw [Set.eq_empty_iff_forall_notMem]
  intro x hx
  obtain ⟨n, hn⟩ := exists_nat_gt x
  have h1 : x ∈ Set.Ioi ((n : ℝ) + 1) := Set.mem_iInter.mp hx n
  simp only [Set.mem_Ioi] at h1
  linarith

/-- **Vanishing integrals near `0`.**  For `g` integrable on `(0,1)` and `ε > 0` there is
`δ ∈ (0,1)` with `∫_{(0,δ)} |g| ≤ ε`. -/
theorem exists_setIntegral_Ioo_abs_le {g : ℝ → ℝ} (hg : IntegrableOn g (Set.Ioo (0 : ℝ) 1))
    {ε : ℝ} (hε : 0 < ε) :
    ∃ δ : ℝ, 0 < δ ∧ δ < 1 ∧ ∫ x in Set.Ioo (0 : ℝ) δ, |g x| ≤ ε := by
  have habs : IntegrableOn (fun x => |g x|) (Set.Ioo (0 : ℝ) 1) := Integrable.abs hg
  set s : ℕ → Set ℝ := fun n => Set.Ioo (0 : ℝ) (1 / ((n : ℝ) + 1)) with hs
  have hsm : ∀ n, MeasurableSet (s n) := fun n => measurableSet_Ioo
  have hanti : Antitone s := by
    intro m n hmn x hx
    rw [hs] at hx ⊢
    simp only [Set.mem_Ioo] at hx ⊢
    refine ⟨hx.1, lt_of_lt_of_le hx.2 ?_⟩
    have hmn' : (m : ℝ) + 1 ≤ (n : ℝ) + 1 := by exact_mod_cast Nat.succ_le_succ hmn
    exact one_div_le_one_div_of_le (by positivity) hmn'
  have hint : IntegrableOn (fun x => |g x|) (s 0) := by
    rw [hs]; simpa using habs
  have hlim := Antitone.tendsto_setIntegral hsm hanti hint
  have hz : (∫ x in ⋂ n, s n, |g x|) = 0 := by
    rw [iInter_Ioo_one_div_succ_eq_empty]; simp
  rw [hz] at hlim
  obtain ⟨N, hN⟩ : ∃ N, ∀ b ≥ N, dist (∫ x in s b, |g x|) 0 < ε :=
    Filter.eventually_atTop.1 (hlim (Metric.ball_mem_nhds 0 hε))
  have hNnn : (0 : ℝ) ≤ (N : ℝ) := Nat.cast_nonneg N
  have h1 : ∫ x in s N, |g x| < ε := by
    have h := hN N le_rfl
    rwa [Real.dist_eq, sub_zero,
      abs_of_nonneg (integral_nonneg (fun x => abs_nonneg (g x)))] at h
  have hNle : (1 : ℝ) / ((N : ℝ) + 1) ≤ 1 := by
    rw [div_le_one (by positivity)]
    linarith
  have hN2lt : (1 : ℝ) / ((N : ℝ) + 2) < 1 / ((N : ℝ) + 1) := by
    rw [one_div, one_div, inv_lt_inv₀ (by positivity) (by positivity)]
    linarith
  have hsub : Set.Ioo (0 : ℝ) (1 / ((N : ℝ) + 2)) ⊆ s N := by
    intro x hx
    rw [hs]
    simp only [Set.mem_Ioo] at hx ⊢
    exact ⟨hx.1, lt_of_lt_of_le hx.2 hN2lt.le⟩
  have ht : IntegrableOn (fun x => |g x|) (s N) :=
    IntegrableOn.mono_set habs (fun x hx => ⟨hx.1, lt_of_lt_of_le hx.2 hNle⟩)
  refine ⟨1 / ((N : ℝ) + 2), by positivity, by
      rw [div_lt_one (by positivity)]; linarith, ?_⟩
  exact le_trans (MeasureTheory.setIntegral_mono_set ht
    (Filter.Eventually.of_forall (fun x => abs_nonneg (g x)))
    (Filter.Eventually.of_forall hsub)) h1.le

/-- **Vanishing integrals at `∞`.**  For `g` integrable on `(1,∞)` and `ε > 0` there is
`R > 1` with `∫_{(R,∞)} |g| ≤ ε`. -/
theorem exists_setIntegral_Ioi_abs_le {g : ℝ → ℝ} (hg : IntegrableOn g (Set.Ioi (1 : ℝ)))
    {ε : ℝ} (hε : 0 < ε) :
    ∃ R : ℝ, 1 < R ∧ ∫ x in Set.Ioi R, |g x| ≤ ε := by
  have habs : IntegrableOn (fun x => |g x|) (Set.Ioi (1 : ℝ)) := Integrable.abs hg
  set s : ℕ → Set ℝ := fun n => Set.Ioi ((n : ℝ) + 1) with hs
  have hsm : ∀ n, MeasurableSet (s n) := fun n => measurableSet_Ioi
  have hanti : Antitone s := by
    intro m n hmn x hx
    rw [hs] at hx ⊢
    simp only [Set.mem_Ioi] at hx ⊢
    have h : (m : ℝ) + 1 ≤ (n : ℝ) + 1 := by exact_mod_cast Nat.succ_le_succ hmn
    linarith
  have hint : IntegrableOn (fun x => |g x|) (s 0) := by
    rw [hs]; simpa using habs
  have hlim := Antitone.tendsto_setIntegral hsm hanti hint
  have hz : (∫ x in ⋂ n, s n, |g x|) = 0 := by
    rw [iInter_Ioi_nat_succ_eq_empty]; simp
  rw [hz] at hlim
  obtain ⟨N, hN⟩ : ∃ N, ∀ b ≥ N, dist (∫ x in s b, |g x|) 0 < ε :=
    Filter.eventually_atTop.1 (hlim (Metric.ball_mem_nhds 0 hε))
  have hNnn : (0 : ℝ) ≤ (N : ℝ) := Nat.cast_nonneg N
  have h1 : ∫ x in s N, |g x| < ε := by
    have h := hN N le_rfl
    rwa [Real.dist_eq, sub_zero,
      abs_of_nonneg (integral_nonneg (fun x => abs_nonneg (g x)))] at h
  have hsN : IntegrableOn (fun x => |g x|) (s N) :=
    IntegrableOn.mono_set habs (fun x hx => by
      rw [hs] at hx; simp only [Set.mem_Ioi] at hx ⊢; linarith)
  have hsub : Set.Ioi ((N : ℝ) + 2) ⊆ s N := by
    intro x hx
    rw [hs]
    simp only [Set.mem_Ioi] at hx ⊢
    linarith
  refine ⟨(N : ℝ) + 2, by linarith, ?_⟩
  exact le_trans (MeasureTheory.setIntegral_mono_set hsN
    (Filter.Eventually.of_forall (fun x => abs_nonneg (g x)))
    (Filter.Eventually.of_forall hsub)) h1.le

end Work.FTS.StrongPersist.N6Trans.Hon
end
end
-- ===== merged: Submission.Work.FTS.StrongPersist.N6Trans.L6Flux.zibp_Ioi_of_integrable =====
section

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

noncomputable section

open scoped Real Topology
open MeasureTheory Set Filter

namespace Work.FTS.StrongPersist.N6Trans.L6Flux

set_option autoImplicit false
-- `hMf` is genuinely unused: for `Mf < 0` the pointwise bound is unsatisfiable for `z > 0`,
-- and for `Mf = 0` (`φ ≡ 0`) the general argument below applies unchanged.
set_option linter.unusedVariables false

/-- `𝓝[≥] a` from `𝓝[>] a`: if `F → b` along `𝓝[>] a` and `F a = b`, then `F` tends to `F a`
along `𝓝[≥] a` (i.e. `F` is continuous within `Ici a` at `a`).  Proved through the basis
`Ico a u` of `𝓝[Ici a] a`. -/
private theorem tendsto_Ici_of_tendsto_Ioi {F : ℝ → ℝ} {a b : ℝ}
    (h : Filter.Tendsto F (nhdsWithin a (Set.Ioi a)) (nhds b)) (hb : F a = b) :
    Filter.Tendsto F (nhdsWithin a (Set.Ici a)) (nhds (F a)) := by
  rw [hb]
  intro t ht
  obtain ⟨u, hau, hu⟩ := (nhdsGT_basis a).mem_iff.mp (h ht)
  refine (nhdsGE_basis_Ico a).mem_iff.mpr ⟨u, hau, ?_⟩
  rintro x ⟨hax, hxu⟩
  rcases eq_or_lt_of_le hax with rfl | hlt
  · simp only [Set.mem_preimage]
    rw [hb]
    exact mem_of_mem_nhds ht
  · exact hu ⟨hlt, hxu⟩


end Work.FTS.StrongPersist.N6Trans.L6Flux
end
end
-- ===== merged: Submission.Work.FTS_RXTPieces.Angular.cs_weighted =====
section

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

open MeasureTheory Set

set_option linter.unusedVariables false

namespace Work.FTS_RXTPieces.Angular

/-- `(x ^ a) ^ 2 = x ^ (2 * a)` for `x > 0`. -/
private lemma rpow_sq_of_pos {x : ℝ} (hx : 0 < x) (a : ℝ) : (x ^ a) ^ 2 = x ^ (2 * a) := by
  rw [pow_two, ← Real.rpow_add hx, show a + a = 2 * a by ring]

theorem cs_weighted {γ : ℝ} (hγ : 1 < γ) {g' : ℝ → ℝ}
    (hmes : MeasureTheory.AEStronglyMeasurable g'
      (MeasureTheory.volume.restrict Work.Spaces.Iθ))
    (hint2 : MeasureTheory.IntegrableOn
      (fun θ => g' θ ^ 2 * (Real.sin (2 * θ)) ^ (2 - γ)) Work.Spaces.Iθ)
    (hWv : IntervalIntegrable (fun θ => (Real.sin (2 * θ)) ^ (γ - 2))
      MeasureTheory.volume 0 (Real.pi / 2))
    {a b : ℝ} (ha : 0 < a) (hab : a ≤ b) (hb : b < Real.pi / 2) :
    (∫ x in a..b, |g' x|) ^ 2
      ≤ (∫ θ in Work.Spaces.Iθ, g' θ ^ 2 * (Real.sin (2 * θ)) ^ (2 - γ))
        * (∫ θ in Work.Spaces.Iθ, (Real.sin (2 * θ)) ^ (γ - 2)) := by
  -- Sine is positive on the open interval `(0, π/2)` and nonnegative on `[0, π/2]`.
  have hsinpos : ∀ θ ∈ Set.Ioo (0:ℝ) (Real.pi / 2), 0 < Real.sin (2 * θ) := by
    intro θ hθ
    exact Real.sin_pos_of_pos_of_lt_pi (by linarith [hθ.1]) (by linarith [hθ.2])
  have hsinIoc : ∀ θ ∈ Set.Ioc (0:ℝ) (Real.pi / 2), 0 ≤ Real.sin (2 * θ) := by
    intro θ hθ
    exact Real.sin_nonneg_of_nonneg_of_le_pi (by linarith [hθ.1]) (by linarith [hθ.2])
  -- The interval `(a,b]` sits inside `[0, π/2]` and inside the open interval.
  have hS_T : Set.Ioc a b ⊆ Set.Ioc (0:ℝ) (Real.pi / 2) :=
    fun x hx => ⟨lt_of_lt_of_le ha (le_of_lt hx.1), le_of_lt (lt_of_le_of_lt hx.2 hb)⟩
  have hS_Ioo : Set.Ioc a b ⊆ Set.Ioo (0:ℝ) (Real.pi / 2) :=
    fun x hx => ⟨lt_of_lt_of_le ha (le_of_lt hx.1), lt_of_le_of_lt hx.2 hb⟩
  have hS_Iθ : Set.Ioc a b ⊆ Work.Spaces.Iθ := by
    intro x hx
    rw [Work.Spaces.Iθ, Set.mem_Icc]
    exact ⟨le_of_lt (lt_of_lt_of_le ha (le_of_lt hx.1)), le_of_lt (lt_of_le_of_lt hx.2 hb)⟩
  -- `Iθ` and `(0, π/2]` differ by the null set `{0}`, so they carry the same measure.
  have hnull : MeasureTheory.volume ({(0:ℝ)} : Set ℝ) = 0 :=
    Set.Finite.measure_zero (by simp) MeasureTheory.volume
  have hae0 : ∀ᵐ (x:ℝ), x ∉ ({(0:ℝ)} : Set ℝ) := by
    rw [MeasureTheory.ae_iff]
    simpa only [not_not, Set.ofPred_mem_eq] using hnull
  have hae : Work.Spaces.Iθ =ᵐ[MeasureTheory.volume] Set.Ioc (0:ℝ) (Real.pi / 2) := by
    filter_upwards [hae0] with x hx
    simp only [Work.Spaces.Iθ, Set.mem_Icc, Set.mem_Ioc]
    exact propext ⟨fun h => ⟨lt_of_le_of_ne h.1 (fun h0 => hx h0.symm), h.2⟩,
      fun h => ⟨le_of_lt h.1, h.2⟩⟩
  have hms : MeasureTheory.volume.restrict Work.Spaces.Iθ
      = MeasureTheory.volume.restrict (Set.Ioc (0:ℝ) (Real.pi / 2)) :=
    MeasureTheory.Measure.restrict_congr_set hae
  -- `hint2` transported to the equivalent set `(0, π/2]`.
  have hint2r : MeasureTheory.IntegrableOn
      (fun θ => g' θ ^ 2 * (Real.sin (2 * θ)) ^ (2 - γ)) (Set.Ioc (0:ℝ) (Real.pi / 2)) := by
    change MeasureTheory.Integrable (fun θ => g' θ ^ 2 * (Real.sin (2 * θ)) ^ (2 - γ))
      (MeasureTheory.volume.restrict (Set.Ioc (0:ℝ) (Real.pi / 2)))
    rw [← hms]
    exact hint2
  rw [hms]
  have hWvI : MeasureTheory.IntegrableOn (fun θ => (Real.sin (2 * θ)) ^ (γ - 2))
      (Set.Ioc (0:ℝ) (Real.pi / 2)) := hWv.1
  -- Continuity of the two weights on the open interval, where `sin (2θ) ≠ 0`.
  have hsincont : ContinuousOn (fun θ : ℝ => Real.sin (2 * θ)) (Set.Ioo (0:ℝ) (Real.pi / 2)) :=
    Real.continuous_sin.comp_continuousOn ((continuous_const.mul continuous_id).continuousOn)
  have hwcont : ContinuousOn (fun θ : ℝ => (Real.sin (2 * θ)) ^ ((2 - γ) / 2))
      (Set.Ioo (0:ℝ) (Real.pi / 2)) :=
    hsincont.rpow_const (fun θ hθ => Or.inl (ne_of_gt (hsinpos θ hθ)))
  have hVcont : ContinuousOn (fun θ : ℝ => (Real.sin (2 * θ)) ^ ((γ - 2) / 2))
      (Set.Ioo (0:ℝ) (Real.pi / 2)) :=
    hsincont.rpow_const (fun θ hθ => Or.inl (ne_of_gt (hsinpos θ hθ)))
  -- The three functions of the Cauchy–Schwarz step are a.e. strongly measurable on `(a,b]`.
  have hw_aesm : AEStronglyMeasurable (fun θ : ℝ => (Real.sin (2 * θ)) ^ ((2 - γ) / 2))
      (MeasureTheory.volume.restrict (Set.Ioc a b)) :=
    (hwcont.aestronglyMeasurable measurableSet_Ioo).mono_set hS_Ioo
  have hV_aesm : AEStronglyMeasurable (fun θ : ℝ => (Real.sin (2 * θ)) ^ ((γ - 2) / 2))
      (MeasureTheory.volume.restrict (Set.Ioc a b)) :=
    (hVcont.aestronglyMeasurable measurableSet_Ioo).mono_set hS_Ioo
  have hg_aesm : AEStronglyMeasurable (fun x : ℝ => |g' x|)
      (MeasureTheory.volume.restrict (Set.Ioc a b)) := by
    simpa only [Real.norm_eq_abs] using hmes.norm.mono_set hS_Iθ
  have hu_aesm : AEStronglyMeasurable
      (fun x : ℝ => |g' x| * (Real.sin (2 * x)) ^ ((2 - γ) / 2))
      (MeasureTheory.volume.restrict (Set.Ioc a b)) :=
    hg_aesm.mul hw_aesm
  have hSmeas : MeasurableSet (Set.Ioc a b) := measurableSet_Ioc
  -- The pointwise identities on `(a,b]` (where `sin (2θ) > 0`).
  have hpt1 : ∀ x ∈ Set.Ioc a b, (|g' x| * (Real.sin (2 * x)) ^ ((2 - γ) / 2)) ^ 2
      = g' x ^ 2 * (Real.sin (2 * x)) ^ (2 - γ) := by
    intro x hx
    have hs : 0 < Real.sin (2 * x) := hsinpos x (hS_Ioo hx)
    rw [mul_pow, sq_abs, rpow_sq_of_pos hs, show 2 * ((2 - γ) / 2) = 2 - γ by ring]
  have hu2 : MeasureTheory.Integrable
      (fun x : ℝ => (|g' x| * (Real.sin (2 * x)) ^ ((2 - γ) / 2)) ^ 2)
      (MeasureTheory.volume.restrict (Set.Ioc a b)) :=
    (hint2r.mono_set hS_T).congr_fun (fun x hx => (hpt1 x hx).symm) hSmeas
  have humem : MeasureTheory.MemLp
      (fun x : ℝ => |g' x| * (Real.sin (2 * x)) ^ ((2 - γ) / 2)) 2
      (MeasureTheory.volume.restrict (Set.Ioc a b)) :=
    (MeasureTheory.memLp_two_iff_integrable_sq hu_aesm).mpr hu2
  have hpt2 : ∀ x ∈ Set.Ioc a b, ((Real.sin (2 * x)) ^ ((γ - 2) / 2)) ^ 2
      = (Real.sin (2 * x)) ^ (γ - 2) := by
    intro x hx
    have hs : 0 < Real.sin (2 * x) := hsinpos x (hS_Ioo hx)
    rw [rpow_sq_of_pos hs, show 2 * ((γ - 2) / 2) = γ - 2 by ring]
  have hV2 : MeasureTheory.Integrable
      (fun x : ℝ => ((Real.sin (2 * x)) ^ ((γ - 2) / 2)) ^ 2)
      (MeasureTheory.volume.restrict (Set.Ioc a b)) :=
    (hWvI.mono_set hS_T).congr_fun (fun x hx => (hpt2 x hx).symm) hSmeas
  have hVmem : MeasureTheory.MemLp (fun x : ℝ => (Real.sin (2 * x)) ^ ((γ - 2) / 2)) 2
      (MeasureTheory.volume.restrict (Set.Ioc a b)) :=
    (MeasureTheory.memLp_two_iff_integrable_sq hV_aesm).mpr hV2
  -- Cauchy–Schwarz on `(a,b]`.
  have hcs := Work.Spaces.cs_integral humem hVmem
  have e1 : (∫ x in Set.Ioc a b, (|g' x| * (Real.sin (2 * x)) ^ ((2 - γ) / 2)) ^ 2)
      = (∫ x in Set.Ioc a b, g' x ^ 2 * (Real.sin (2 * x)) ^ (2 - γ)) :=
    MeasureTheory.setIntegral_congr_fun hSmeas hpt1
  have e2 : (∫ x in Set.Ioc a b, ((Real.sin (2 * x)) ^ ((γ - 2) / 2)) ^ 2)
      = (∫ x in Set.Ioc a b, (Real.sin (2 * x)) ^ (γ - 2)) :=
    MeasureTheory.setIntegral_congr_fun hSmeas hpt2
  have hUV : (∫ x in Set.Ioc a b,
        (|g' x| * (Real.sin (2 * x)) ^ ((2 - γ) / 2)) * (Real.sin (2 * x)) ^ ((γ - 2) / 2))
      = (∫ x in Set.Ioc a b, |g' x|) := by
    refine MeasureTheory.setIntegral_congr_fun hSmeas (fun x hx => ?_)
    have hs : 0 < Real.sin (2 * x) := hsinpos x (hS_Ioo hx)
    rw [mul_assoc, ← Real.rpow_add hs, show (2 - γ) / 2 + (γ - 2) / 2 = 0 by ring,
      Real.rpow_zero, mul_one]
  -- Monotonicity of the integral of a nonnegative function for `(a,b] ⊆ (0,π/2]`.
  have hTmeas : MeasurableSet (Set.Ioc (0:ℝ) (Real.pi / 2)) := measurableSet_Ioc
  have h1nn : 0 ≤ᵐ[MeasureTheory.volume.restrict (Set.Ioc (0:ℝ) (Real.pi / 2))]
      (fun θ => g' θ ^ 2 * (Real.sin (2 * θ)) ^ (2 - γ)) :=
    (MeasureTheory.ae_restrict_iff' hTmeas).mpr
      (Filter.Eventually.of_forall (fun x hx =>
        mul_nonneg (sq_nonneg _) (Real.rpow_nonneg (hsinIoc x hx) _)))
  have h2nn : 0 ≤ᵐ[MeasureTheory.volume.restrict (Set.Ioc (0:ℝ) (Real.pi / 2))]
      (fun θ => (Real.sin (2 * θ)) ^ (γ - 2)) :=
    (MeasureTheory.ae_restrict_iff' hTmeas).mpr
      (Filter.Eventually.of_forall (fun x hx => Real.rpow_nonneg (hsinIoc x hx) _))
  have hst : Set.Ioc a b ≤ᵐ[MeasureTheory.volume] Set.Ioc (0:ℝ) (Real.pi / 2) :=
    Filter.Eventually.of_forall (fun x hx => hS_T hx)
  have m1 : (∫ x in Set.Ioc a b, g' x ^ 2 * (Real.sin (2 * x)) ^ (2 - γ))
      ≤ (∫ x in Set.Ioc (0:ℝ) (Real.pi / 2), g' x ^ 2 * (Real.sin (2 * x)) ^ (2 - γ)) :=
    MeasureTheory.setIntegral_mono_set hint2r h1nn hst
  have m2 : (∫ x in Set.Ioc a b, (Real.sin (2 * x)) ^ (γ - 2))
      ≤ (∫ x in Set.Ioc (0:ℝ) (Real.pi / 2), (Real.sin (2 * x)) ^ (γ - 2)) :=
    MeasureTheory.setIntegral_mono_set hWvI h2nn hst
  have hBSnn : 0 ≤ (∫ x in Set.Ioc a b, (Real.sin (2 * x)) ^ (γ - 2)) :=
    MeasureTheory.setIntegral_nonneg hSmeas
      (fun x hx => Real.rpow_nonneg (le_of_lt (hsinpos x (hS_Ioo hx))) _)
  have hAnn : 0 ≤ (∫ x in Set.Ioc (0:ℝ) (Real.pi / 2),
      g' x ^ 2 * (Real.sin (2 * x)) ^ (2 - γ)) :=
    MeasureTheory.setIntegral_nonneg hTmeas (fun x hx =>
      mul_nonneg (sq_nonneg _) (Real.rpow_nonneg (hsinIoc x hx) _))
  calc (∫ x in a..b, |g' x|) ^ 2
      = (∫ x in Set.Ioc a b, |g' x|) ^ 2 := by rw [intervalIntegral.integral_of_le hab]
    _ = (∫ x in Set.Ioc a b,
          (|g' x| * (Real.sin (2 * x)) ^ ((2 - γ) / 2)) * (Real.sin (2 * x)) ^ ((γ - 2) / 2)) ^ 2 := by
          rw [hUV]
    _ ≤ (∫ x in Set.Ioc a b, (|g' x| * (Real.sin (2 * x)) ^ ((2 - γ) / 2)) ^ 2)
        * (∫ x in Set.Ioc a b, ((Real.sin (2 * x)) ^ ((γ - 2) / 2)) ^ 2) := hcs
    _ = (∫ x in Set.Ioc a b, g' x ^ 2 * (Real.sin (2 * x)) ^ (2 - γ))
        * (∫ x in Set.Ioc a b, (Real.sin (2 * x)) ^ (γ - 2)) := by rw [e1, e2]
    _ ≤ (∫ x in Set.Ioc (0:ℝ) (Real.pi / 2), g' x ^ 2 * (Real.sin (2 * x)) ^ (2 - γ))
        * (∫ x in Set.Ioc (0:ℝ) (Real.pi / 2), (Real.sin (2 * x)) ^ (γ - 2)) :=
        mul_le_mul m1 m2 hBSnn hAnn

end Work.FTS_RXTPieces.Angular
end
-- ===== merged: Submission.Work.FTS_RXTPieces.Angular.integral_deriv_eq_sub =====
section

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

/-!
# The fundamental theorem of calculus on a compact sub-interval of `(0, π/2)`

The hypothesis of the main lemma `integral_deriv_eq_sub` provides the derivative of `g` only on
the *open* interval `(0, π/2)`, together with the integrability of `g'^2 · sin(2θ)^{2-γ}`
(with `γ > 1`).

On a compact sub-interval `[a,b] ⊂ (0, π/2)` the angular weight `θ ↦ sin(2θ)^{2-γ}` is bounded
below by a positive constant `c` (`sin_two_rpow_lower_bound`), so the given integrability
yields that `g'` itself is integrable on `[a,b]` (via `integrableOn_sq_of_integrableOn_sq_mul`
and `integrableOn_of_integrableOn_sq`, the latter requiring only that `g'` be a.e. strongly
measurable — here it is a derivative, so `measurable_deriv`/`aestronglyMeasurable_deriv`
apply).  Since `g` is differentiable, hence continuous, on the open interval, the fundamental
theorem of calculus applies in the form
`intervalIntegral.integral_eq_sub_of_hasDerivAt_of_le`.
-/

noncomputable section

open MeasureTheory Set

-- style only: `haveI` is used for a local finite-measure instance below, and the hypothesis
-- `hγ` of the source statement is not needed for the argument (a compact sub-interval of
-- `(0, π/2)` bounds the weight away from `0` for every exponent)
set_option linter.style.haveILetI false
set_option linter.unusedVariables false

namespace Work.FTS_RXTPieces.Angular

/-- On a compact sub-interval `[a,b] ⊂ (0, π/2)` the angular weight `θ ↦ sin(2θ)^{2-γ}` is
bounded below by a positive constant. -/
theorem sin_two_rpow_lower_bound {γ : ℝ} {a b : ℝ} (ha : 0 < a) (hab : a ≤ b)
    (hb : b < Real.pi / 2) :
    ∃ c : ℝ, 0 < c ∧ ∀ θ ∈ Set.Icc a b, c ≤ (Real.sin (2 * θ)) ^ (2 - γ) := by
  have hne : (Set.Icc a b).Nonempty := ⟨a, le_rfl, hab⟩
  have hcont : ContinuousOn (fun θ : ℝ => (Real.sin (2 * θ)) ^ (2 - γ)) (Set.Icc a b) := by
    refine ContinuousOn.rpow_const ?_ ?_
    · exact (Real.continuous_sin.comp (continuous_const.mul continuous_id)).continuousOn
    · intro θ hθ
      left
      apply ne_of_gt
      exact Real.sin_pos_of_pos_of_lt_pi (by linarith [hθ.1, ha]) (by linarith [hθ.2, hb])
  obtain ⟨θ₀, hθ₀, hmin⟩ := isCompact_Icc.exists_isMinOn hne hcont
  refine ⟨(Real.sin (2 * θ₀)) ^ (2 - γ), ?_, fun θ hθ => hmin hθ⟩
  apply Real.rpow_pos_of_pos
  exact Real.sin_pos_of_pos_of_lt_pi (by linarith [hθ₀.1, ha]) (by linarith [hθ₀.2, hb])

/-- If `∫ θ in s, f θ ^ 2 * w θ` is finite and `w ≥ c > 0` on `s`, then `∫ θ in s, f θ ^ 2` is
finite (strong measurability of `f ^ 2` being assumed). -/
theorem integrableOn_sq_of_integrableOn_sq_mul {f w : ℝ → ℝ} {s : Set ℝ} (hs : MeasurableSet s)
    (hmeas : AEStronglyMeasurable (fun θ => f θ ^ 2) (volume.restrict s))
    (h : IntegrableOn (fun θ => f θ ^ 2 * w θ) s volume) {c : ℝ} (hc : 0 < c)
    (hw : ∀ θ ∈ s, c ≤ w θ) :
    IntegrableOn (fun θ => f θ ^ 2) s volume := by
  refine Integrable.mono' (h.const_mul c⁻¹) hmeas ?_
  refine ae_restrict_of_forall_mem hs fun θ hθ => ?_
  have hwc : 1 ≤ c⁻¹ * w θ := by
    have h1 : c⁻¹ * c = 1 := inv_mul_cancel₀ (ne_of_gt hc)
    calc (1 : ℝ) = c⁻¹ * c := h1.symm
      _ ≤ c⁻¹ * w θ := mul_le_mul_of_nonneg_left (hw θ hθ) (le_of_lt (inv_pos.mpr hc))
  calc ‖f θ ^ 2‖ = f θ ^ 2 := by rw [Real.norm_eq_abs, abs_of_nonneg (sq_nonneg _)]
    _ ≤ f θ ^ 2 * (c⁻¹ * w θ) := le_mul_of_one_le_right (sq_nonneg _) hwc
    _ = c⁻¹ * (f θ ^ 2 * w θ) := by ring

/-- On a set of finite measure, a measurable function with integrable square is integrable:
`|f θ| ≤ f θ ^ 2 + 1`, and the constant function `1` is integrable on a finite measure space. -/
theorem integrableOn_of_integrableOn_sq {f : ℝ → ℝ} {s : Set ℝ} (hs : MeasurableSet s)
    (hmeas : AEStronglyMeasurable f (volume.restrict s))
    (h : IntegrableOn (fun θ => f θ ^ 2) s volume) (hfin : volume s ≠ ⊤) :
    IntegrableOn f s volume := by
  haveI : IsFiniteMeasure (volume.restrict s) :=
    ⟨by rw [Measure.restrict_apply_univ]; exact lt_top_iff_ne_top.mpr hfin⟩
  refine Integrable.mono' (h.add (MeasureTheory.integrable_const (1 : ℝ))) hmeas ?_
  refine ae_restrict_of_forall_mem hs fun θ _ => ?_
  have habs : |f θ| ≤ f θ ^ 2 + 1 := by
    rw [abs_le']
    constructor <;> nlinarith [sq_nonneg (f θ + 1), sq_nonneg (f θ - 1)]
  simpa [Pi.add_apply, Real.norm_eq_abs] using habs

/-- **Fundamental theorem of calculus**, on a compact sub-interval of `(0, π/2)`, for a function
whose derivative is known on the *open* interval `(0, π/2)` and whose derivative is
square-integrable against the weight `sin(2θ)^{2-γ}`. -/
theorem integral_deriv_eq_sub {γ : ℝ} (hγ : 1 < γ) {g g' : ℝ → ℝ}
    (hg : ∀ θ ∈ Set.Ioo (0 : ℝ) (Real.pi / 2), HasDerivAt g (g' θ) θ)
    (hint2 : MeasureTheory.IntegrableOn
      (fun θ => g' θ ^ 2 * (Real.sin (2 * θ)) ^ (2 - γ)) Work.Spaces.Iθ)
    {a b : ℝ} (ha : 0 < a) (hab : a ≤ b) (hb : b < Real.pi / 2) :
    ∫ x in a..b, g' x = g b - g a := by
  -- the hypotheses force `g'` to agree with the everywhere-defined `deriv g` on `(a,b)`
  have hderiv_eq : ∀ θ ∈ Set.Ioo (0 : ℝ) (Real.pi / 2), deriv g θ = g' θ :=
    fun θ hθ => (hg θ hθ).deriv
  have hmem : ∀ θ ∈ Set.Ioc a b, θ ∈ Set.Ioo (0 : ℝ) (Real.pi / 2) := by
    intro θ hθ
    rw [Set.mem_Ioc] at hθ
    exact ⟨lt_trans ha hθ.1, lt_of_le_of_lt hθ.2 hb⟩
  -- `g' ^ 2` is a.e. strongly measurable (it is a square of a derivative)
  have hmeas_sq : AEStronglyMeasurable (fun θ => g' θ ^ 2) (volume.restrict (Set.Ioc a b)) := by
    have h1 : AEStronglyMeasurable (fun θ => deriv g θ ^ 2)
        (volume.restrict (Set.Ioc a b)) :=
      (aestronglyMeasurable_deriv g (volume.restrict (Set.Ioc a b))).pow 2
    refine h1.congr (ae_restrict_of_forall_mem measurableSet_Ioc fun θ hθ => ?_)
    show deriv g θ ^ 2 = g' θ ^ 2
    rw [hderiv_eq θ (hmem θ hθ)]
  have hmeas_g' : AEStronglyMeasurable g' (volume.restrict (Set.Ioc a b)) := by
    have h1 : AEStronglyMeasurable (fun θ => deriv g θ) (volume.restrict (Set.Ioc a b)) :=
      aestronglyMeasurable_deriv g _
    refine h1.congr (ae_restrict_of_forall_mem measurableSet_Ioc fun θ hθ => ?_)
    exact hderiv_eq θ (hmem θ hθ)
  -- the compact sub-interval sits inside `Iθ = [0, π/2]`, so the weighted integrability restricts
  have hsub : Set.Ioc a b ⊆ Work.Spaces.Iθ := by
    intro θ hθ
    rw [Set.mem_Ioc] at hθ
    change θ ∈ Set.Icc 0 (Real.pi / 2)
    rw [Set.mem_Icc]
    exact ⟨le_of_lt (lt_trans ha hθ.1), le_of_lt (lt_of_le_of_lt hθ.2 hb)⟩
  -- the weight has a positive lower bound on `[a,b]`, hence `(g')²` is integrable there
  obtain ⟨c, hc, hcw⟩ := sin_two_rpow_lower_bound (γ := γ) ha hab hb
  have hw : ∀ θ ∈ Set.Ioc a b, c ≤ (Real.sin (2 * θ)) ^ (2 - γ) :=
    fun θ hθ => hcw θ (Set.Ioc_subset_Icc_self hθ)
  have hsq_int : IntegrableOn (fun θ => g' θ ^ 2) (Set.Ioc a b) :=
    integrableOn_sq_of_integrableOn_sq_mul measurableSet_Ioc hmeas_sq
      (hint2.mono_set hsub) hc hw
  -- and on the finite measure set `(a,b]` this gives the integrability of `g'` itself
  have hg'_int : IntegrableOn g' (Set.Ioc a b) :=
    integrableOn_of_integrableOn_sq measurableSet_Ioc hmeas_g' hsq_int measure_Ioc_lt_top.ne
  have hint : IntervalIntegrable g' volume a b :=
    (intervalIntegrable_iff_integrableOn_Ioc_of_le hab).mpr hg'_int
  -- `g` is differentiable, hence continuous, on a neighbourhood of `[a,b]`
  have hcont : ContinuousOn g (Set.Icc a b) := by
    have hdiff : DifferentiableOn ℝ g (Set.Ioo 0 (Real.pi / 2)) :=
      fun θ hθ => (hg θ hθ).differentiableAt.differentiableWithinAt
    refine (hdiff.continuousOn).mono ?_
    intro θ hθ
    rw [Set.mem_Icc] at hθ
    exact ⟨lt_of_lt_of_le ha hθ.1, lt_of_le_of_lt hθ.2 hb⟩
  exact intervalIntegral.integral_eq_sub_of_hasDerivAt_of_le hab hcont
    (fun θ hθ => hg θ (hmem θ ⟨hθ.1, le_of_lt hθ.2⟩)) hint

end Work.FTS_RXTPieces.Angular
end
end
-- ===== merged: Submission.Work.FTS_RXTPieces.Angular.meanValue =====
section

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

namespace Work.FTS_RXTPieces.Angular

open MeasureTheory

/-- Mean value inequality for `g²` on `[0,π/2]`: if `g²` is integrable on `Iθ`, then at some
point `t` of the *open* interval the value `g t ^ 2` is at most the average of `g ^ 2`,
i.e. `2 * g t ^ 2 ≤ (4/π) ∫_{Iθ} g ^ 2`.

The proof is by contradiction: if `g ^ 2 > A / (π/2)` everywhere on `(0, π/2)`, where `A` is
the integral of `g ^ 2` over `[0, π/2]`, then `g ^ 2 - A / (π/2)` is a nonnegative function,
positive on the whole open interval, so its integral over `(0, π/2)` is strictly positive;
but the same integral over `[0, π/2]` equals `A - (A / (π/2)) * (π/2) = 0`. -/
theorem meanValue {g : ℝ → ℝ}
    (hint : MeasureTheory.IntegrableOn (fun θ => g θ ^ 2) Work.Spaces.Iθ) :
    ∃ t ∈ Set.Ioo (0 : ℝ) (Real.pi / 2),
      2 * g t ^ 2 ≤ (4 / Real.pi) * (∫ θ in Work.Spaces.Iθ, g θ ^ 2) := by
  by_contra h
  simp only [Work.Spaces.Iθ] at h
  set A : ℝ := ∫ θ in Set.Icc (0 : ℝ) (Real.pi / 2), g θ ^ 2 with hA
  -- if the claim failed, `g ^ 2` exceeds the average `A / (π/2)` everywhere on `(0, π/2)`
  have hpos : ∀ t ∈ Set.Ioo (0 : ℝ) (Real.pi / 2), A / (Real.pi / 2) < g t ^ 2 := by
    intro t ht
    have h1 : (4 / Real.pi) * A < 2 * g t ^ 2 := by
      by_contra hc
      exact h ⟨t, ht, not_lt.mp hc⟩
    have h2 : ((4 / Real.pi) * A) / 2 < g t ^ 2 := by linarith
    have h3 : A / (Real.pi / 2) = ((4 / Real.pi) * A) / 2 := by ring
    linarith
  have hIntG_Icc : MeasureTheory.IntegrableOn (fun θ => g θ ^ 2) (Set.Icc 0 (Real.pi / 2)) := by
    simpa only [Work.Spaces.Iθ] using hint
  have hIntG_Ioo : MeasureTheory.IntegrableOn (fun θ => g θ ^ 2) (Set.Ioo 0 (Real.pi / 2)) :=
    hIntG_Icc.mono_set Set.Ioo_subset_Icc_self
  have hIntC_Ioo : MeasureTheory.IntegrableOn (fun _ : ℝ => A / (Real.pi / 2))
      (Set.Ioo 0 (Real.pi / 2)) :=
    integrableOn_const (μ := volume) (s := Set.Ioo 0 (Real.pi / 2)) (C := A / (Real.pi / 2))
      measure_Ioo_lt_top.ne (by simp)
  have hIntF_Ioo : MeasureTheory.IntegrableOn (fun θ => g θ ^ 2 - A / (Real.pi / 2))
      (Set.Ioo 0 (Real.pi / 2)) :=
    hIntG_Ioo.sub hIntC_Ioo
  have hnn : ∀ᵐ x ∂(volume.restrict (Set.Ioo (0 : ℝ) (Real.pi / 2))),
      (0 : ℝ) ≤ (fun θ => g θ ^ 2 - A / (Real.pi / 2)) x := by
    rw [MeasureTheory.ae_restrict_iff' measurableSet_Ioo]
    filter_upwards with t ht
    have := hpos t ht
    linarith
  have hnonneg : (0 : ℝ → ℝ) ≤ᵐ[volume.restrict (Set.Ioo (0 : ℝ) (Real.pi / 2))]
      (fun θ => g θ ^ 2 - A / (Real.pi / 2)) := hnn
  have hsupp : Set.Ioo (0 : ℝ) (Real.pi / 2) ⊆
      Function.support (fun θ => g θ ^ 2 - A / (Real.pi / 2)) := by
    intro t ht
    rw [Function.mem_support]
    exact ne_of_gt (by have := hpos t ht; linarith)
  have hIntPos : 0 < ∫ θ in Set.Ioo (0 : ℝ) (Real.pi / 2), g θ ^ 2 - A / (Real.pi / 2) := by
    rw [MeasureTheory.setIntegral_pos_iff_support_of_nonneg_ae hnonneg hIntF_Ioo]
    have hset : Function.support (fun θ => g θ ^ 2 - A / (Real.pi / 2)) ∩
        Set.Ioo (0 : ℝ) (Real.pi / 2) = Set.Ioo 0 (Real.pi / 2) :=
      Set.inter_eq_right.mpr hsupp
    rw [hset, Real.volume_Ioo]
    exact ENNReal.ofReal_pos.mpr (by linarith [Real.pi_pos])
  have hIntPosIcc : 0 < ∫ θ in Set.Icc (0 : ℝ) (Real.pi / 2), g θ ^ 2 - A / (Real.pi / 2) := by
    rw [← MeasureTheory.restrict_Ioo_eq_restrict_Icc]
    exact hIntPos
  have hvol : MeasureTheory.volume.real (Set.Icc (0 : ℝ) (Real.pi / 2)) = Real.pi / 2 := by
    have h1 : MeasureTheory.volume (Set.Icc (0 : ℝ) (Real.pi / 2)) = ENNReal.ofReal (Real.pi / 2) := by
      rw [Real.volume_Icc, sub_zero]
    rw [MeasureTheory.Measure.real, h1, ENNReal.toReal_ofReal (by positivity)]
  have hfirst : (∫ θ in Set.Icc (0 : ℝ) (Real.pi / 2), g θ ^ 2) = A := hA.symm
  have hIntC_Icc : MeasureTheory.IntegrableOn (fun _ : ℝ => A / (Real.pi / 2))
      (Set.Icc 0 (Real.pi / 2)) :=
    integrableOn_const (μ := volume) (s := Set.Icc 0 (Real.pi / 2)) (C := A / (Real.pi / 2))
      measure_Icc_lt_top.ne (by simp)
  have hzero : ∫ θ in Set.Icc (0 : ℝ) (Real.pi / 2), g θ ^ 2 - A / (Real.pi / 2) = 0 := by
    rw [MeasureTheory.integral_sub hIntG_Icc hIntC_Icc, MeasureTheory.setIntegral_const, smul_eq_mul,
      hvol, hfirst, mul_div_cancel₀ _ (by positivity : (Real.pi / 2) ≠ 0), sub_self]
  linarith [hIntPosIcc, hzero]

end Work.FTS_RXTPieces.Angular
end
-- ===== merged: Submission.Work.FTS_RXTPieces.noDecayPieces.agmonF_deriv_bnd =====
section

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

namespace Work.FTS_RXTPieces.noDecayPieces

/-- The radial weight `w(z) = (1+z)²/z²` has `z`-derivative `-2(1+z)/z³` away from `z = 0`. -/
private lemma hasDerivAt_w {z : ℝ} (hz : z ≠ 0) :
    HasDerivAt Work.Spaces.w (-2 * (1 + z) / z ^ 3) z := by
  have hnum : HasDerivAt (fun z : ℝ => (1 + z) ^ 2) (2 * (1 + z)) z := by
    convert ((hasDerivAt_id z).const_add 1).pow 2 using 1 <;> (first | rfl | simp)
  have hden : HasDerivAt (fun z : ℝ => z ^ 2) (2 * z) z := by
    convert (hasDerivAt_id z).pow 2 using 1 <;> (first | rfl | simp)
  have hne : z ^ 2 ≠ 0 := pow_ne_zero 2 hz
  have h := hnum.div hden hne
  convert h using 1
  · rfl
  · field_simp
    ring

/-- `|(x-3)/(1+x)| ≤ 3` for `x > 0`. -/
private lemma abs_div_three_le (x : ℝ) (hx : 0 < x) : |(x - 3) / (1 + x)| ≤ 3 := by
  have h1 : (0 : ℝ) < 1 + x := by linarith
  rw [abs_div, abs_of_pos h1, div_le_iff₀ h1, abs_le]
  constructor <;> linarith

/-- The elementary inequality behind the Agmon bound: for `|q| ≤ 3`,
`|2 A B + A² q| ≤ 4 A² + B²`.  Indeed `2|A||B| ≤ A² + B²` and `A²|q| ≤ 3 A²`. -/
private lemma abs_two_mul_add_sq_le (A B q : ℝ) (hq : |q| ≤ 3) :
    |2 * A * B + A ^ 2 * q| ≤ 4 * A ^ 2 + B ^ 2 := by
  have h1 : |2 * A * B + A ^ 2 * q| ≤ 2 * |A| * |B| + |A| ^ 2 * |q| := by
    calc |2 * A * B + A ^ 2 * q| ≤ |2 * A * B| + |A ^ 2 * q| := abs_add_le _ _
      _ = 2 * |A| * |B| + |A| ^ 2 * |q| := by
        rw [abs_mul, abs_mul, abs_mul, abs_pow, abs_of_nonneg (by norm_num : (0 : ℝ) ≤ 2)]
  have h2 : 2 * |A| * |B| ≤ |A| ^ 2 + |B| ^ 2 := by
    have h := two_mul_le_add_sq |A| |B|
    linarith
  have h3 : |A| ^ 2 * |q| ≤ 3 * |A| ^ 2 := by
    have h := mul_le_mul_of_nonneg_right hq (sq_nonneg |A|)
    nlinarith [h]
  calc |2 * A * B + A ^ 2 * q| ≤ 2 * |A| * |B| + |A| ^ 2 * |q| := h1
    _ ≤ (|A| ^ 2 + |B| ^ 2) + 3 * |A| ^ 2 := add_le_add h2 h3
    _ = 4 * A ^ 2 + B ^ 2 := by rw [sq_abs, sq_abs]; ring

theorem agmonF_deriv_bnd {v v' : ℝ → ℝ}
    (hv : ∀ x ∈ Set.Ioi (0 : ℝ), HasDerivAt v (v' x) x) :
    ∀ x ∈ Set.Ioi (0 : ℝ),
      HasDerivAt (fun y : ℝ => y * (v y * Work.Spaces.w y) ^ 2)
        (2 * v x * (x * v' x) * (Work.Spaces.w x) ^ 2
          + (v x) ^ 2 * (Work.Spaces.w x) ^ 2 * ((x - 3) / (1 + x))) x
      ∧ |2 * v x * (x * v' x) * (Work.Spaces.w x) ^ 2
            + (v x) ^ 2 * (Work.Spaces.w x) ^ 2 * ((x - 3) / (1 + x))|
          ≤ 4 * (v x * Work.Spaces.w x) ^ 2 + (x * v' x * Work.Spaces.w x) ^ 2 := by
  intro x hx
  have hx0 : (0 : ℝ) < x := hx
  have hxne : x ≠ 0 := ne_of_gt hx0
  refine ⟨?_, ?_⟩
  · -- the derivative: product rule, chain rule, and `w' = -2(1+x)/x³`
    have hvx : HasDerivAt v (v' x) x := hv x hx
    have hwx : HasDerivAt Work.Spaces.w (-2 * (1 + x) / x ^ 3) x := hasDerivAt_w hxne
    have hmul : HasDerivAt (fun y : ℝ => v y * Work.Spaces.w y)
        (v' x * Work.Spaces.w x + v x * (-2 * (1 + x) / x ^ 3)) x := hvx.mul hwx
    have hsq : HasDerivAt (fun y : ℝ => (v y * Work.Spaces.w y) ^ 2)
        (2 * (v x * Work.Spaces.w x) ^ (2 - 1)
          * (v' x * Work.Spaces.w x + v x * (-2 * (1 + x) / x ^ 3))) x := by
      convert hmul.pow 2 using 1
    have hprod := (hasDerivAt_id x).mul hsq
    refine hprod.congr_deriv ?_
    simp only [id_eq]
    rw [show (2 : ℕ) - 1 = 1 from rfl, pow_one,
      show Work.Spaces.w x = (1 + x) ^ 2 / x ^ 2 from rfl]
    field_simp
    ring
  · -- the bound: triangle inequality, AM–GM, and `|(x-3)/(1+x)| ≤ 3`
    have hq : |(x - 3) / (1 + x)| ≤ 3 := abs_div_three_le x hx0
    have hmain := abs_two_mul_add_sq_le (v x * Work.Spaces.w x) (x * v' x * Work.Spaces.w x)
      ((x - 3) / (1 + x)) hq
    refine le_of_eq_of_le ?_ hmain
    congr 1
    ring

end Work.FTS_RXTPieces.noDecayPieces
end
-- ===== merged: Submission.Work.FTS_RXTPieces.noDecayPieces.sq_le_of_profile_le =====
section

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

namespace Work.FTS_RXTPieces.noDecayPieces

theorem sq_le_of_profile_le {v : ℝ → ℝ} {z K : ℝ} (hz : 0 < z) (hK : 0 ≤ K)
    (h : z * (v z * Work.Spaces.w z) ^ 2 ≤ K) :
    v z ^ 2 ≤ K * (min z 1) ^ 2 := by
  -- `w z = (1+z)²/z²`, so `z * w z ^ 2 = (1+z)⁴ / z³`.
  have hz3 : (0 : ℝ) < z ^ 3 := by positivity
  have hzw : z * (Work.Spaces.w z) ^ 2 = (1 + z) ^ 4 / z ^ 3 := by
    rw [Work.Spaces.w]
    field_simp
  -- The key numeric fact: `1 ≤ (min z 1)² * z * w z ^ 2`, i.e. `z³ ≤ (min z 1)² (1+z)⁴`.
  have hmain : z ^ 3 ≤ (min z 1) ^ 2 * (1 + z) ^ 4 := by
    rcases le_or_gt z 1 with h1 | h1
    · rw [min_eq_left h1]
      have h4 : (1 : ℝ) ≤ (1 + z) ^ 4 := one_le_pow₀ (by linarith) (n := 4)
      have hz2 : (0 : ℝ) ≤ z ^ 2 := sq_nonneg z
      calc z ^ 3 = z ^ 2 * z := by ring
        _ ≤ z ^ 2 * 1 := mul_le_mul_of_nonneg_left h1 hz2
        _ ≤ z ^ 2 * (1 + z) ^ 4 := mul_le_mul_of_nonneg_left h4 hz2
    · rw [min_eq_right h1.le]
      have h43 : z ^ 3 ≤ z ^ 4 := by
        calc z ^ 3 = z ^ 3 * 1 := by ring
          _ ≤ z ^ 3 * z := mul_le_mul_of_nonneg_left h1.le (by positivity)
          _ = z ^ 4 := by ring
      have h44 : z ^ 4 ≤ (1 + z) ^ 4 :=
        pow_le_pow_left₀ (by linarith : (0 : ℝ) ≤ z) (by linarith : z ≤ 1 + z) 4
      linarith
  have hkey : 1 ≤ (min z 1) ^ 2 * (z * (Work.Spaces.w z) ^ 2) := by
    rw [hzw, ← mul_div_assoc, le_div_iff₀ hz3]
    simpa using hmain
  have hstep : (v z) ^ 2 ≤ (v z) ^ 2 * ((min z 1) ^ 2 * (z * (Work.Spaces.w z) ^ 2)) := by
    have := mul_le_mul_of_nonneg_left hkey (sq_nonneg (v z))
    simpa using this
  calc (v z) ^ 2 ≤ (v z) ^ 2 * ((min z 1) ^ 2 * (z * (Work.Spaces.w z) ^ 2)) := hstep
    _ = (min z 1) ^ 2 * (z * (v z * Work.Spaces.w z) ^ 2) := by ring
    _ ≤ (min z 1) ^ 2 * K := mul_le_mul_of_nonneg_left h (sq_nonneg (min z 1))
    _ = K * (min z 1) ^ 2 := by ring

end Work.FTS_RXTPieces.noDecayPieces
end
-- ===== merged: Submission.Work.FTS_RegExport.RXA1w.AgmonZ =====
section

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

/-!
# The weighted radial Agmon inequality

`Work.FTS_RegExport.RXA1w.agmonZ_weight`: for `v : ℝ → ℝ` differentiable on `(0,∞)`, with
`(v w)²` and `(x v' w)²` integrable on `[0,∞)` and `x (v x w(x))² → 0` at `+∞`,

  `(v z)² w(z)² z ≤ 4 ∫_{[0,∞)} (v w)² + ∫_{[0,∞)} (x v' w)²`   for `z > 0`,

where `w(z) = (1+z)²/z²`.  This is the weighted Agmon inequality in the radial variable, the
structurally new ingredient of RX-A1w.
-/

noncomputable section

open scoped Real Topology
open MeasureTheory Set Filter

namespace Work.FTS_RegExport.RXA1w

private lemma continuousOn_w_Ioi : ContinuousOn Work.Spaces.w (Set.Ioi (0 : ℝ)) := by
  have h : (fun y : ℝ => (1 + y) ^ 2 / y ^ 2) = Work.Spaces.w := by
    funext y; rw [Work.Spaces.w]
  rw [← h]
  exact ContinuousOn.div ((continuousOn_const.add continuousOn_id).pow 2)
    (continuousOn_id.pow 2) (fun y hy => pow_ne_zero 2 (ne_of_gt hy))

/-- `(v x · w x)² · x`, the weighted square of a radial slice. -/
private noncomputable def agmonF (v : ℝ → ℝ) (x : ℝ) : ℝ :=
  x * (v x * Work.Spaces.w x) ^ 2

/-- The derivative of `agmonF v` on `(0,∞)`. -/
private noncomputable def agmonF' (v : ℝ → ℝ) (x : ℝ) : ℝ :=
  2 * v x * (x * deriv v x) * (Work.Spaces.w x) ^ 2
    + (v x) ^ 2 * (Work.Spaces.w x) ^ 2 * ((x - 3) / (1 + x))

/-- **Weighted radial Agmon inequality on the half-line.** -/
theorem agmonZ_weight {v : ℝ → ℝ} {z : ℝ} (hz : 0 < z)
    (hderiv : ∀ x ∈ Set.Ioi (0 : ℝ), HasDerivAt v (deriv v x) x)
    (hint1 : MeasureTheory.IntegrableOn (fun x => (v x * Work.Spaces.w x) ^ 2) Work.Spaces.Iz)
    (hint2 : MeasureTheory.IntegrableOn (fun x => (x * deriv v x * Work.Spaces.w x) ^ 2)
      Work.Spaces.Iz)
    (hdec : Filter.Tendsto (fun x => x * (v x * Work.Spaces.w x) ^ 2) Filter.atTop (𝓝 0)) :
    (v z) ^ 2 * (Work.Spaces.w z) ^ 2 * z ≤
      4 * (∫ x in Work.Spaces.Iz, (v x * Work.Spaces.w x) ^ 2)
        + ∫ x in Work.Spaces.Iz, (x * deriv v x * Work.Spaces.w x) ^ 2 := by
  have hvcont : ContinuousOn v (Set.Ioi (0 : ℝ)) := fun x hx =>
    (hderiv x hx).differentiableAt.continuousAt.continuousWithinAt
  have hIz_eq : volume.restrict Work.Spaces.Iz = volume.restrict (Set.Ioi (0 : ℝ)) := by
    rw [Work.Spaces.Iz, MeasureTheory.restrict_Ioi_eq_restrict_Ici]
  have hFderiv : ∀ x ∈ Set.Ioi (0 : ℝ), HasDerivAt (agmonF v) (agmonF' v x) x := by
    intro x hx
    have hx0 : 0 < x := hx
    have hxne : x ≠ 0 := ne_of_gt hx0
    have hev : agmonF v =ᶠ[𝓝 x] fun y : ℝ => (v y) ^ 2 * (1 + y) ^ 4 / y ^ 3 := by
      filter_upwards [isOpen_Ioi.mem_nhds hx0] with y hy
      simp only [agmonF, Work.Spaces.w]
      field_simp
    have hv2 : HasDerivAt (fun y : ℝ => (v y) ^ 2) (2 * v x * deriv v x) x := by
      have h := (hderiv x hx).pow 2
      convert h using 1 <;> ring
    have h1xy : HasDerivAt (fun y : ℝ => 1 + y) 1 x := by
      have h := (hasDerivAt_const x (1 : ℝ)).add (hasDerivAt_id x)
      convert h using 1
      · funext y; simp
      · simp
    have hp : HasDerivAt (fun y : ℝ => (1 + y) ^ 4) (4 * (1 + x) ^ 3) x := by
      have h := h1xy.pow 4
      convert h using 1 <;> ring
    have hden : HasDerivAt (fun y : ℝ => y ^ 3) (3 * x ^ 2) x := by
      have h := (hasDerivAt_id x).pow 3
      convert h using 1
      · funext y; rfl
      · simp
    have hnum : HasDerivAt (fun y : ℝ => (v y) ^ 2 * (1 + y) ^ 4)
        (2 * v x * deriv v x * (1 + x) ^ 4 + (v x) ^ 2 * (4 * (1 + x) ^ 3)) x := by
      have h := hv2.mul hp
      convert h using 1 <;> ring
    have hq := hnum.div hden (pow_ne_zero 3 hxne)
    refine (hev.hasDerivAt_iff).mpr ?_
    convert hq using 1
    rw [agmonF']
    simp only [Work.Spaces.w]
    field_simp <;> ring
  have hF'bound : ∀ x ∈ Work.Spaces.Iz,
      |agmonF' v x| ≤ 4 * (v x * Work.Spaces.w x) ^ 2
        + (x * deriv v x * Work.Spaces.w x) ^ 2 := by
    intro x hx
    have hx0 : 0 ≤ x := hx
    have hb : |(x - 3) / (1 + x)| ≤ 3 := by
      have h1x : (0 : ℝ) < 1 + x := by linarith
      rw [abs_div, abs_of_pos h1x, div_le_iff₀ h1x]
      by_cases h : x ≤ 3
      · rw [abs_of_nonpos (by linarith)]; nlinarith
      · push_neg at h
        rw [abs_of_pos (by linarith)]; nlinarith
    have hkey : agmonF' v x
        = 2 * (v x * Work.Spaces.w x) * (x * deriv v x * Work.Spaces.w x)
          + (v x * Work.Spaces.w x) ^ 2 * ((x - 3) / (1 + x)) := by
      rw [agmonF']; ring
    have hAB : 2 * |(v x * Work.Spaces.w x)| * |(x * deriv v x * Work.Spaces.w x)|
        ≤ (v x * Work.Spaces.w x) ^ 2 + (x * deriv v x * Work.Spaces.w x) ^ 2 := by
      nlinarith [sq_nonneg (|v x * Work.Spaces.w x| - |x * deriv v x * Work.Spaces.w x|),
        sq_abs (v x * Work.Spaces.w x), sq_abs (x * deriv v x * Work.Spaces.w x)]
    have hE1 : |2 * (v x * Work.Spaces.w x) * (x * deriv v x * Work.Spaces.w x)|
        = 2 * |(v x * Work.Spaces.w x)| * |(x * deriv v x * Work.Spaces.w x)| := by
      rw [abs_mul, abs_mul, abs_of_nonneg (by norm_num : (0 : ℝ) ≤ 2)] <;> ring
    have hE2 : |(v x * Work.Spaces.w x) ^ 2 * ((x - 3) / (1 + x))|
        = (v x * Work.Spaces.w x) ^ 2 * |(x - 3) / (1 + x)| := by
      rw [abs_mul, abs_of_nonneg (sq_nonneg _)]
    rw [hkey]
    calc |2 * (v x * Work.Spaces.w x) * (x * deriv v x * Work.Spaces.w x)
            + (v x * Work.Spaces.w x) ^ 2 * ((x - 3) / (1 + x))|
        ≤ |2 * (v x * Work.Spaces.w x) * (x * deriv v x * Work.Spaces.w x)|
            + |(v x * Work.Spaces.w x) ^ 2 * ((x - 3) / (1 + x))| := abs_add_le _ _
      _ = 2 * |(v x * Work.Spaces.w x)| * |(x * deriv v x * Work.Spaces.w x)|
            + (v x * Work.Spaces.w x) ^ 2 * |(x - 3) / (1 + x)| := by rw [hE1, hE2]
      _ ≤ (v x * Work.Spaces.w x) ^ 2 + (x * deriv v x * Work.Spaces.w x) ^ 2
            + (v x * Work.Spaces.w x) ^ 2 * 3 := by
          refine add_le_add hAB ?_
          exact mul_le_mul_of_nonneg_left hb (sq_nonneg _)
      _ = 4 * (v x * Work.Spaces.w x) ^ 2
            + (x * deriv v x * Work.Spaces.w x) ^ 2 := by ring
  have hgint : MeasureTheory.IntegrableOn
      (fun x => 4 * (v x * Work.Spaces.w x) ^ 2
        + (x * deriv v x * Work.Spaces.w x) ^ 2) Work.Spaces.Iz :=
    (hint1.const_mul 4).add hint2
  have haesm : AEStronglyMeasurable (agmonF' v) (volume.restrict Work.Spaces.Iz) := by
    rw [hIz_eq]
    have hdv : AEStronglyMeasurable (deriv v) (volume.restrict (Set.Ioi (0 : ℝ))) :=
      (aestronglyMeasurable_deriv v volume).restrict
    have hvc : AEStronglyMeasurable v (volume.restrict (Set.Ioi (0 : ℝ))) :=
      hvcont.aestronglyMeasurable measurableSet_Ioi
    have hwc : AEStronglyMeasurable (fun x : ℝ => Work.Spaces.w x)
        (volume.restrict (Set.Ioi (0 : ℝ))) :=
      continuousOn_w_Ioi.aestronglyMeasurable measurableSet_Ioi
    have hc3 : AEStronglyMeasurable (fun x : ℝ => (x - 3) / (1 + x))
        (volume.restrict (Set.Ioi (0 : ℝ))) := by
      have h2 : ContinuousOn (fun x : ℝ => 1 + x) (Set.Ioi (0 : ℝ)) :=
        continuousOn_const.add continuousOn_id
      exact ((continuousOn_id.sub continuousOn_const).div h2
        (fun x hx => by have hx0 : 0 < x := hx; exact ne_of_gt (by linarith))).aestronglyMeasurable
        measurableSet_Ioi
    have h1 : AEStronglyMeasurable
        (fun x : ℝ => 2 * v x * (x * deriv v x) * (Work.Spaces.w x) ^ 2)
        (volume.restrict (Set.Ioi (0 : ℝ))) :=
      (((hvc.const_mul 2).mul (aestronglyMeasurable_id.mul hdv)).mul (hwc.pow 2))
    have h2 : AEStronglyMeasurable
        (fun x : ℝ => (v x) ^ 2 * (Work.Spaces.w x) ^ 2 * ((x - 3) / (1 + x)))
        (volume.restrict (Set.Ioi (0 : ℝ))) :=
      (((hvc.pow 2).mul (hwc.pow 2)).mul hc3)
    exact (h1.add h2).congr (Filter.Eventually.of_forall fun x => by
      simp only [agmonF', Pi.add_apply]; try ring)
  have hF'int : MeasureTheory.IntegrableOn (agmonF' v) Work.Spaces.Iz :=
    hgint.mono' haesm (ae_restrict_of_forall_mem measurableSet_Ici fun x hx => by
      rw [Real.norm_eq_abs]; exact hF'bound x hx)
  have hAbsOn : MeasureTheory.IntegrableOn (fun x => |agmonF' v x|) Work.Spaces.Iz :=
    hF'int.abs
  have htail : ∀ X : ℝ, z ≤ X → agmonF v z
      ≤ agmonF v X + ∫ x in Set.Ioi z, |agmonF' v x| := by
    intro X hzX
    have hFcont : ContinuousOn (agmonF v) (Set.Icc z X) := by
      have hv : ContinuousOn v (Set.Icc z X) :=
        hvcont.mono (fun x hx => lt_of_lt_of_le hz hx.1)
      have hw : ContinuousOn Work.Spaces.w (Set.Icc z X) :=
        continuousOn_w_Ioi.mono (fun x hx => lt_of_lt_of_le hz hx.1)
      have h := ((hv.pow 2).mul (hw.pow 2)).mul continuousOn_id
      refine h.congr (fun y _ => ?_)
      simp only [agmonF, Pi.mul_apply, Pi.pow_apply, id_eq]; ring
    have hd : ∀ x ∈ Set.Ioo z X, HasDerivAt (agmonF v) (agmonF' v x) x :=
      fun x hx => hFderiv x (lt_trans hz hx.1)
    have hintv : IntervalIntegrable (agmonF' v) volume z X := by
      rw [intervalIntegrable_iff, Set.uIoc_of_le hzX]
      exact hF'int.mono_set (fun x hx => le_of_lt (lt_trans hz hx.1))
    have hFTC : ∫ x in z..X, agmonF' v x = agmonF v X - agmonF v z :=
      intervalIntegral.integral_eq_sub_of_hasDerivAt_of_le hzX hFcont hd hintv
    have h3abs : |∫ x in z..X, agmonF' v x| ≤ ∫ x in Set.Ioi z, |agmonF' v x| := by
      rw [intervalIntegral.integral_of_le hzX]
      refine le_trans (MeasureTheory.abs_integral_le_integral_abs) ?_
      exact MeasureTheory.setIntegral_mono_set
        (hAbsOn.mono_set (fun x hx => le_of_lt (lt_trans hz hx)))
        (Filter.Eventually.of_forall fun x => abs_nonneg _)
        (Filter.Eventually.of_forall fun x hx => hx.1)
    have h3 : -(∫ x in z..X, agmonF' v x) ≤ ∫ x in Set.Ioi z, |agmonF' v x| :=
      le_trans (neg_le_abs _) h3abs
    linarith [hFTC, h3]
  have hlim : Filter.Tendsto (fun X : ℝ => agmonF v X + ∫ x in Set.Ioi z, |agmonF' v x|)
      Filter.atTop (𝓝 (0 + ∫ x in Set.Ioi z, |agmonF' v x|)) :=
    hdec.add_const _
  have hev2 : ∀ᶠ X in Filter.atTop,
      agmonF v z ≤ agmonF v X + ∫ x in Set.Ioi z, |agmonF' v x| :=
    (Filter.eventually_ge_atTop z).mono htail
  have hmain : agmonF v z ≤ ∫ x in Set.Ioi z, |agmonF' v x| := by
    have := ge_of_tendsto hlim hev2
    simpa using this
  have hmono : ∀ᵐ x ∂(volume.restrict (Set.Ioi z)),
      |agmonF' v x| ≤ 4 * (v x * Work.Spaces.w x) ^ 2
        + (x * deriv v x * Work.Spaces.w x) ^ 2 :=
    ae_restrict_of_forall_mem measurableSet_Ioi fun x hx =>
      hF'bound x (le_of_lt (lt_trans hz hx))
  have hgintz : MeasureTheory.IntegrableOn
      (fun x => 4 * (v x * Work.Spaces.w x) ^ 2
        + (x * deriv v x * Work.Spaces.w x) ^ 2) (Set.Ioi z) :=
    hgint.mono_set (fun x hx => le_of_lt (lt_trans hz hx))
  have habsint : MeasureTheory.IntegrableOn (fun x => |agmonF' v x|) (Set.Ioi z) :=
    hAbsOn.mono_set (fun x hx => le_of_lt (lt_trans hz hx))
  have hle : ∫ x in Set.Ioi z, |agmonF' v x| ≤ ∫ x in Set.Ioi z,
      (4 * (v x * Work.Spaces.w x) ^ 2 + (x * deriv v x * Work.Spaces.w x) ^ 2) :=
    integral_mono_ae habsint hgintz hmono
  have hIz : (∫ x in Set.Ioi z,
        (4 * (v x * Work.Spaces.w x) ^ 2 + (x * deriv v x * Work.Spaces.w x) ^ 2))
      ≤ 4 * (∫ x in Work.Spaces.Iz, (v x * Work.Spaces.w x) ^ 2)
        + ∫ x in Work.Spaces.Iz, (x * deriv v x * Work.Spaces.w x) ^ 2 := by
    have hIa0 : MeasureTheory.IntegrableOn (fun x => 4 * (v x * Work.Spaces.w x) ^ 2)
        Work.Spaces.Iz := hint1.const_mul 4
    have hIa : MeasureTheory.IntegrableOn (fun x => 4 * (v x * Work.Spaces.w x) ^ 2)
        (Set.Ioi z) := hIa0.mono_set (fun x hx => le_of_lt (lt_trans hz hx))
    have hIb : MeasureTheory.IntegrableOn
        (fun x => (x * deriv v x * Work.Spaces.w x) ^ 2) (Set.Ioi z) :=
      hint2.mono_set (fun x hx => le_of_lt (lt_trans hz hx))
    rw [integral_add hIa hIb, integral_const_mul]
    refine add_le_add (mul_le_mul_of_nonneg_left ?_ (by norm_num)) ?_
    · exact MeasureTheory.setIntegral_mono_set hint1
        (Filter.Eventually.of_forall fun x => sq_nonneg _)
        (Filter.Eventually.of_forall fun x hx => le_of_lt (lt_trans hz hx))
    · exact MeasureTheory.setIntegral_mono_set hint2
        (Filter.Eventually.of_forall fun x => sq_nonneg _)
        (Filter.Eventually.of_forall fun x hx => le_of_lt (lt_trans hz hx))
  have hfin : (v z) ^ 2 * (Work.Spaces.w z) ^ 2 * z = agmonF v z := by
    rw [agmonF]; ring
  rw [hfin]
  linarith [hmain, hle, hIz]

end Work.FTS_RegExport.RXA1w
end
end
-- ===== merged: Submission.Work.FTS_RegExport.RXB.tendsto_nhdsGT_zero_of_radial_trace =====
section

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

open scoped Topology
open Filter

namespace Work.FTS_RegExport.RXB

/-- If the radial trace `z · (u z · w z)²` tends to `0` as `z → 0⁺`, then `u z → 0`.
This uses that `w z = (1+z)²/z²`, so `(u z)² = z·(u z·w z)² · z³/(1+z)⁴` and hence
`|u z|` is the square root of a product of two quantities tending to `0`. -/
theorem tendsto_nhdsGT_zero_of_radial_trace {u : ℝ → ℝ}
    (h : Filter.Tendsto (fun z => z * (u z * Work.Spaces.w z) ^ 2)
      (nhdsWithin (0 : ℝ) (Set.Ioi 0)) (nhds 0)) :
    Filter.Tendsto u (nhdsWithin (0 : ℝ) (Set.Ioi 0)) (nhds 0) := by
  -- The auxiliary factor `c z = z³/(1+z)⁴` tends to `0` as `z → 0⁺`.
  have hc : Filter.Tendsto (fun z : ℝ => z ^ 3 / (1 + z) ^ 4) (𝓝[>] (0 : ℝ)) (nhds 0) := by
    have hcont : ContinuousAt (fun z : ℝ => z ^ 3 / (1 + z) ^ 4) 0 :=
      (continuousAt_id.pow 3).div ((continuousAt_const.add continuousAt_id).pow 4) (by norm_num)
    simpa using hcont.tendsto.mono_left nhdsWithin_le_nhds
  -- Hence the product tends to `0`.
  have hbc : Filter.Tendsto (fun z => z * (u z * Work.Spaces.w z) ^ 2 * (z ^ 3 / (1 + z) ^ 4))
      (𝓝[>] (0 : ℝ)) (nhds 0) := by
    simpa using h.mul hc
  -- Continuity of `sqrt` at `0` gives that `sqrt` of the product tends to `0`.
  have hsqrt : Filter.Tendsto
      (fun z => Real.sqrt (z * (u z * Work.Spaces.w z) ^ 2 * (z ^ 3 / (1 + z) ^ 4)))
      (𝓝[>] (0 : ℝ)) (nhds 0) := by
    have hcomp := (Real.continuous_sqrt.continuousAt (x := 0)).tendsto.comp hbc
    rw [Real.sqrt_zero] at hcomp
    exact hcomp
  -- On `(0, ∞)` the quantity under the square root is exactly `(u z)²`.
  have hev : (fun z : ℝ => Real.sqrt (z * (u z * Work.Spaces.w z) ^ 2 * (z ^ 3 / (1 + z) ^ 4)))
      =ᶠ[𝓝[>] (0 : ℝ)] (fun z => |u z|) := by
    refine Filter.eventually_of_mem (U := Set.Ioi 0) self_mem_nhdsWithin ?_
    intro z hz
    have hz' : (0 : ℝ) < z := hz
    have hz0 : z ≠ 0 := ne_of_gt hz'
    have h1z : (1 : ℝ) + z ≠ 0 := by positivity
    have hid : z * (u z * Work.Spaces.w z) ^ 2 * (z ^ 3 / (1 + z) ^ 4) = (u z) ^ 2 := by
      rw [Work.Spaces.w]
      field_simp
    simp only [hid, Real.sqrt_sq_eq_abs]
  have habs : Filter.Tendsto (fun z => |u z|) (𝓝[>] (0 : ℝ)) (nhds 0) := hsqrt.congr' hev
  exact tendsto_zero_iff_norm_tendsto_zero.mpr (by simpa [Real.norm_eq_abs] using habs)

end Work.FTS_RegExport.RXB
end
-- ===== merged: Submission.Work.FTS_RegExport.RXT.AgmonND.Defs =====
section

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

/-!
# The weighted radial Agmon inequality without a decay hypothesis: definitions

This file sets up the objects used in the proof of the *no-decay* weighted radial Agmon
inequality `Work.FTS_RegExport.RXT.Slots.v2_agmonZ_noDecay`, which is the statement of
`Work.FTS_RegExport.RXA1w.agmonZ_weight` with the hypothesis `x (v x w x)² → 0` removed:
that hypothesis is not needed, since integrability of `(v w)²` alone forces
`x (v x w x)²` to take arbitrarily small values along a sequence tending to `∞` (see
`Work.FTS_RegExport.RXT.small_value`), which is all the fundamental-theorem-of-calculus
argument requires.

With `w(x) = (1+x)²/x²` we have `(x (v x w x)²)' = -[4 (v x w x)² + (x v' w)²] + (error)`
with an error of a sign that only helps, so
`z (v z w z)² ≤ ∫_{z}^{∞} [4 (v w)² + (x v' w)²]`.

## Main definitions

* `agmonF v x = x * (v x * w x)²`, the quantity whose derivative is taken;
* `agmonFderiv v v' x = 2 v x (x v' x) w x² + (v x)² w x² ((x-3)/(1+x))`, the pointwise
  derivative of `agmonF v` at `x` (for `v'` a derivative of `v`).
-/

noncomputable section

open scoped Real Topology
open MeasureTheory Set Filter

namespace Work.FTS_RegExport.RXT

/-- The radial weight `w` is continuous on `(0,∞)`. -/
lemma continuousOn_w_Ioi : ContinuousOn Work.Spaces.w (Set.Ioi (0 : ℝ)) := by
  have h : (fun y : ℝ => (1 + y) ^ 2 / y ^ 2) = Work.Spaces.w := by
    funext y; rw [Work.Spaces.w]
  rw [← h]
  exact ContinuousOn.div ((continuousOn_const.add continuousOn_id).pow 2)
    (continuousOn_id.pow 2) (fun y hy => pow_ne_zero 2 (ne_of_gt hy))

/-- `x * (v x * w x)²`, the weighted square of a radial slice. -/
def agmonF (v : ℝ → ℝ) (x : ℝ) : ℝ := x * (v x * Work.Spaces.w x) ^ 2

/-- A formula for the pointwise derivative of `agmonF v` on `(0,∞)`, when `v'` is a
pointwise derivative of `v` there. -/
def agmonFderiv (v v' : ℝ → ℝ) (x : ℝ) : ℝ :=
  2 * v x * (x * v' x) * (Work.Spaces.w x) ^ 2
    + (v x) ^ 2 * (Work.Spaces.w x) ^ 2 * ((x - 3) / (1 + x))

/-- `agmonF v` at a point, in the form appearing in the Agmon inequality. -/
lemma agmonF_eq (v : ℝ → ℝ) (x : ℝ) :
    agmonF v x = (v x) ^ 2 * (Work.Spaces.w x) ^ 2 * x := by
  rw [agmonF]; ring

end Work.FTS_RegExport.RXT
end
end
-- ===== merged: Submission.Work.FTS_RegExport.RXT.contDiffOn_succ_integral_Ioi =====
section

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

/-!
# `Work.FTS_RegExport.RXT.contDiffOn_succ_integral_Ioi`

`z ↦ ∫_r in (z,∞) h r` is `C^{n+1}` on `(0,∞)` for `h` of class `C^n` on `(0,∞)`.

The proof splits on whether `h` is integrable on `(1,∞)`:

* if it is, then (`h` being continuous on `(0,∞)`) it is integrable on `(z,∞)` for every `z > 0`,
  and the fundamental theorem for the tail integral (`Work.FTS.PhiStar.Radial.hasDerivAt_integral_Ioi`)
  gives `HasDerivAt (fun z => ∫_r in (z,∞) h r) (-(h z)) z`; the criterion
  `contDiffOn_succ_iff_deriv_of_isOpen` finishes, using `ContDiffOn ℝ n (fun z => -(h z))`;
* if it is not, then (again by continuity on `(0,∞)`) `h` is integrable on no `(z,∞)`, so the
  integral is the junk value `0` and the function is constant.
-/

namespace Work.FTS_RegExport.RXT

/-- If `h` is continuous on `(0,∞)` and not integrable on `(1,∞)`, then it is integrable on no
half-line `(z,∞)`, `z > 0`: continuity on `(0,∞)` forces integrability on the half-lines to be
independent of `z`. -/
private theorem not_integrableOn_Ioi_of_not_integrableOn_Ioi_one {h : ℝ → ℝ}
    (hcont : ContinuousOn h (Set.Ioi 0)) (h1 : ¬ MeasureTheory.IntegrableOn h (Set.Ioi 1)) :
    ∀ z ∈ Set.Ioi (0 : ℝ), ¬ MeasureTheory.IntegrableOn h (Set.Ioi z) := by
  intro z hz hzint
  rcases le_or_gt z 1 with hz1 | hz1
  · exact h1 (hzint.mono_set (Set.Ioi_subset_Ioi hz1))
  · have hc1 : ContinuousOn h (Set.Icc 1 z) :=
      hcont.mono (fun x hx => lt_of_lt_of_le zero_lt_one hx.1)
    have hJ : MeasureTheory.IntegrableOn h (Set.Ioc 1 z) :=
      (hc1.integrableOn_Icc).mono_set Set.Ioc_subset_Icc_self
    have hU : MeasureTheory.IntegrableOn h (Set.Ioc 1 z ∪ Set.Ioi z) := hJ.union hzint
    exact h1 (hU.mono_set (fun x hx => by
      rcases le_or_gt x z with hxz | hxz
      · exact Or.inl ⟨hx, hxz⟩
      · exact Or.inr hxz))

/-- **Smoothness of the primitive over the half-line.**  For `h` of class `C^n` on `(0,∞)`,
the function `z ↦ ∫_r in (z,∞) h r` is of class `C^{n+1}` on `(0,∞)`.

Two cases: either `h` is integrable on `(a,∞)` for one (hence every) `a > 0`, in which case
`∫_{(z,∞)} h = ∫_{(a,∞)} h - ∫_a^z h` on `z > a` is a constant minus a primitive of `h`; or
`h` is integrable on no `(z,∞)`, `z > 0` (since `h` is locally bounded, once it is integrable
on one half-line it is integrable on all of them), in which case the integral is the junk value
`0` (`MeasureTheory.integral_undef`) and the function is identically zero. -/
theorem contDiffOn_succ_integral_Ioi {n : ℕ} {h : ℝ → ℝ}
    (hc : ContDiffOn ℝ n h (Set.Ioi 0)) :
    ContDiffOn ℝ (n + 1) (fun z => ∫ r in Set.Ioi z, h r) (Set.Ioi 0) := by
  have hcont : ContinuousOn h (Set.Ioi 0) := hc.continuousOn
  by_cases hint : MeasureTheory.IntegrableOn h (Set.Ioi 1)
  · -- integrable case: `F` has derivative `-h`, and `h` is `C^n`
    have hderiv : ∀ z ∈ Set.Ioi (0 : ℝ),
        HasDerivAt (fun u => ∫ t in Set.Ioi u, h t) (-(h z)) z := by
      intro z hz
      have hz2 : (0 : ℝ) < z / 2 := by
        have : (0 : ℝ) < z := hz
        linarith
      exact Work.FTS.PhiStar.Radial.hasDerivAt_integral_Ioi (a := z / 2) (z := z) (by linarith)
        (hcont.mono (fun t ht => lt_trans hz2 ht))
        (Work.FTS.PhiStar.Radial.integrableOn_Ioi_of_Ioi_Ioo hz2 hcont hint)
    rw [contDiffOn_succ_iff_deriv_of_isOpen isOpen_Ioi]
    refine ⟨?_, ?_, ?_⟩
    · exact fun z hz => (hderiv z hz).differentiableAt.differentiableWithinAt
    · intro htop
      exact absurd htop (by simp)
    · exact (hc.neg).congr (fun z hz => (hderiv z hz).deriv)
  · -- junk case: `F` is identically `0` on `(0,∞)`
    have hni := not_integrableOn_Ioi_of_not_integrableOn_Ioi_one hcont hint
    have hzero : ∀ z ∈ Set.Ioi (0 : ℝ), (∫ t in Set.Ioi z, h t) = 0 := by
      intro z hz
      exact MeasureTheory.integral_undef (μ := MeasureTheory.volume.restrict (Set.Ioi z))
        (hni z hz)
    exact ContDiffOn.congr contDiffOn_const (fun z hz => (hzero z hz))

end Work.FTS_RegExport.RXT
end
-- ===== merged: Submission.Work.FTS_RegExport.RXT.continuousAt_integral_Itheta_of_bound =====
section

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

namespace Work.FTS_RegExport.RXT

theorem continuousAt_integral_Itheta_of_bound {G : ℝ → ℝ → ℝ} {φ : ℝ → ℝ} {z₀ K : ℝ}
    (hK : 0 ≤ K) (hφ : ContinuousOn φ Work.Spaces.Iθ)
    (hG_meas : ∀ᶠ z in nhds z₀,
      MeasureTheory.AEStronglyMeasurable (fun θ => G z θ * φ θ)
        (MeasureTheory.volume.restrict (Set.Ioo 0 (Real.pi / 2))))
    (hbound : ∀ᶠ z in nhds z₀,
      ∀ᵐ θ ∂(MeasureTheory.volume.restrict (Set.Ioo 0 (Real.pi / 2))), ‖G z θ‖ ≤ K)
    (hcont : ∀ᵐ θ ∂(MeasureTheory.volume.restrict (Set.Ioo 0 (Real.pi / 2))),
      ContinuousAt (fun z => G z θ) z₀) :
    ContinuousAt (fun z => ∫ θ, G z θ * φ θ
      ∂(MeasureTheory.volume.restrict (Set.Ioo 0 (Real.pi / 2)))) z₀ := by
  -- The interval `(0, π/2)` is of finite measure, so constants are integrable.
  have hfin : MeasureTheory.volume (Set.Ioo (0 : ℝ) (Real.pi / 2)) < ⊤ :=
    lt_of_le_of_lt (MeasureTheory.measure_mono Set.Ioo_subset_Icc_self)
      isCompact_Icc.measure_lt_top
  have hfinI : MeasureTheory.IsFiniteMeasure
      (MeasureTheory.volume.restrict (Set.Ioo (0 : ℝ) (Real.pi / 2))) :=
    ⟨by rw [MeasureTheory.Measure.restrict_apply_univ]; exact hfin⟩
  -- `φ` is bounded on the compact interval `Iθ`.
  obtain ⟨M, hM⟩ := isCompact_Icc.exists_bound_of_continuousOn hφ
  have hφae : ∀ᵐ θ ∂(MeasureTheory.volume.restrict (Set.Ioo (0 : ℝ) (Real.pi / 2))),
      ‖φ θ‖ ≤ M := by
    filter_upwards [MeasureTheory.ae_restrict_mem measurableSet_Ioo] with θ hθ
    exact hM θ ⟨le_of_lt hθ.1, le_of_lt hθ.2⟩
  -- The dominating function, and the a.e. bound by it.
  have hbound' : ∀ᶠ z in nhds z₀,
      ∀ᵐ θ ∂(MeasureTheory.volume.restrict (Set.Ioo (0 : ℝ) (Real.pi / 2))),
        ‖G z θ * φ θ‖ ≤ K * M := by
    filter_upwards [hbound] with z hz
    filter_upwards [hz, hφae] with θ h1 h2
    rw [norm_mul]
    exact mul_le_mul h1 h2 (norm_nonneg _) hK
  -- The a.e. convergence of the slices.
  have hcont' : ∀ᵐ θ ∂(MeasureTheory.volume.restrict (Set.Ioo (0 : ℝ) (Real.pi / 2))),
      ContinuousAt (fun z => G z θ * φ θ) z₀ := by
    filter_upwards [hcont] with θ hθ
    exact hθ.tendsto.mul_const (φ θ)
  have hbint : MeasureTheory.Integrable (fun _ : ℝ => K * M)
      (MeasureTheory.volume.restrict (Set.Ioo (0 : ℝ) (Real.pi / 2))) :=
    MeasureTheory.integrable_const_iff.2 (Or.inr hfinI)
  exact MeasureTheory.continuousAt_of_dominated (F := fun z θ => G z θ * φ θ)
    (x₀ := z₀) (bound := fun _ => K * M) hG_meas hbound' hbint hcont'

end Work.FTS_RegExport.RXT
end
-- ===== merged: Submission.Work.FTS_RegExport.RXT.hasDerivAt_integral_Itheta_of_bound =====
section

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

open MeasureTheory Set Filter

namespace Work.FTS_RegExport.RXT

/-- **Differentiation under the angular integral sign, with an a.e. bound on the derivative.**
If, a.e. in `θ ∈ (0,π/2)`, every `z`-slice `z' ↦ G z' θ * φ θ` is differentiable on the
neighbourhood `(z₀/2, 2 z₀)` of `z₀ > 0` with derivative `G' z θ * φ θ`, and if `‖G' z θ‖`
is a.e. bounded by the constant `K ≥ 0` there, then (given measurability and integrability of
the slice at `z₀`) the parametric integral `z ↦ ∫_θ G z θ * φ θ` is differentiable at `z₀`
with derivative `∫_θ G' z₀ θ * φ θ`.

This is `hasDerivAt_integral_of_dominated_loc_of_deriv_le` with the dominating function
`θ ↦ K * M`, where `M` bounds `‖φ‖` on the compact interval `Iθ` (so the bound is integrable
for the finite measure `volume.restrict (Ioo 0 (π/2))`). -/

theorem hasDerivAt_integral_Itheta_of_bound {G G' : ℝ → ℝ → ℝ} {φ : ℝ → ℝ} {z₀ K : ℝ}
    (hz₀ : 0 < z₀) (hK : 0 ≤ K) (hφ : ContinuousOn φ Work.Spaces.Iθ)
    (hG_meas : ∀ᶠ z in nhds z₀,
      MeasureTheory.AEStronglyMeasurable (fun θ => G z θ * φ θ)
        (MeasureTheory.volume.restrict (Set.Ioo 0 (Real.pi / 2))))
    (hG_int : MeasureTheory.Integrable (fun θ => G z₀ θ * φ θ)
        (MeasureTheory.volume.restrict (Set.Ioo 0 (Real.pi / 2))))
    (hG'_meas : MeasureTheory.AEStronglyMeasurable (fun θ => G' z₀ θ * φ θ)
        (MeasureTheory.volume.restrict (Set.Ioo 0 (Real.pi / 2))))
    (hbound : ∀ᵐ θ ∂(MeasureTheory.volume.restrict (Set.Ioo 0 (Real.pi / 2))),
      ∀ z ∈ Set.Ioo (z₀ / 2) (2 * z₀), ‖G' z θ‖ ≤ K)
    (hderiv : ∀ᵐ θ ∂(MeasureTheory.volume.restrict (Set.Ioo 0 (Real.pi / 2))),
      ∀ z ∈ Set.Ioo (z₀ / 2) (2 * z₀),
        HasDerivAt (fun z' => G z' θ * φ θ) (G' z θ * φ θ) z) :
    HasDerivAt (fun z => ∫ θ, G z θ * φ θ
        ∂(MeasureTheory.volume.restrict (Set.Ioo 0 (Real.pi / 2))))
      (∫ θ, G' z₀ θ * φ θ ∂(MeasureTheory.volume.restrict (Set.Ioo 0 (Real.pi / 2)))) z₀ := by
  -- `‖φ‖` is bounded on the compact interval `Iθ` by some constant `M ≥ 0`
  obtain ⟨M, hM⟩ := isCompact_Icc.exists_bound_of_continuousOn
    (by simpa [Work.Spaces.Iθ] using hφ)
  have hMn : 0 ≤ M := le_trans (norm_nonneg _) (hM 0 ⟨le_refl 0, by linarith [Real.pi_pos]⟩)
  have hphi_ae : ∀ᵐ θ ∂(MeasureTheory.volume.restrict (Set.Ioo 0 (Real.pi / 2))), ‖φ θ‖ ≤ M := by
    rw [MeasureTheory.ae_restrict_iff' measurableSet_Ioo]
    exact Eventually.of_forall fun θ hθ => hM θ ⟨le_of_lt hθ.1, le_of_lt hθ.2⟩
  -- combine the two a.e. bounds: `‖G' z θ * φ θ‖ ≤ K * M`
  have hbound' : ∀ᵐ θ ∂(MeasureTheory.volume.restrict (Set.Ioo 0 (Real.pi / 2))),
      ∀ z ∈ Set.Ioo (z₀ / 2) (2 * z₀), ‖G' z θ * φ θ‖ ≤ K * M := by
    filter_upwards [hbound, hphi_ae] with θ hb hφb z hz
    rw [norm_mul]
    exact mul_le_mul (hb z hz) hφb (norm_nonneg _) hK
  -- the constant bound is integrable for the finite restricted measure
  have hfin : MeasureTheory.IsFiniteMeasure
      (MeasureTheory.volume.restrict (Set.Ioo 0 (Real.pi / 2))) :=
    MeasureTheory.isFiniteMeasure_restrict.mpr
      (by rw [Real.volume_Ioo]; exact ENNReal.ofReal_ne_top)
  have key := hasDerivAt_integral_of_dominated_loc_of_deriv_le
    (μ := MeasureTheory.volume.restrict (Set.Ioo 0 (Real.pi / 2)))
    (F := fun z θ => G z θ * φ θ) (F' := fun z θ => G' z θ * φ θ)
    (bound := fun _ => K * M) (x₀ := z₀) (s := Set.Ioo (z₀ / 2) (2 * z₀))
    (isOpen_Ioo.mem_nhds ⟨by linarith, by linarith⟩) hG_meas hG_int hG'_meas hbound'
    (MeasureTheory.integrable_const_iff.mpr (Or.inr hfin)) hderiv
  exact key.2

end Work.FTS_RegExport.RXT
end
-- ===== merged: Submission.Work.FTS_RegExport.RXT.pzIter_two_bound_of_DzIter_two =====
section

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

namespace Work.FTS_RegExport.RXT

theorem pzIter_two_bound_of_DzIter_two {F : ℝ → ℝ → ℝ} {C z₀ z θ : ℝ}
    (hz₀ : 0 < z₀) (hz : z₀ / 2 < z) (hC : 0 ≤ C)
    (hd : DifferentiableAt ℝ (fun t => Work.Spaces.pzIter 1 F t θ) z)
    (h1 : |Work.Spaces.Dz F z θ| ≤ C) (h2 : |Work.Spaces.DzIter 2 F z θ| ≤ C) :
    |Work.Spaces.pzIter 2 F z θ| ≤ 8 * C / z₀ ^ 2 := by
  have hz0 : 0 < z := by linarith
  have hzsq : 0 < z ^ 2 := pow_pos hz0 2
  -- `∂_z` of the `z`-slice of `pz F` is `pzIter 2 F`
  have hdg : DifferentiableAt ℝ (fun t : ℝ => Work.Spaces.pz F t θ) z := by
    simpa only [Work.Spaces.pzIter_succ, Work.Spaces.pzIter_zero, Work.Spaces.pz] using hd
  -- the one-variable product rule for `t ↦ t * ∂_z F t θ`
  have hderiv : deriv (fun t : ℝ => t * Work.Spaces.pz F t θ) z
      = Work.Spaces.pz F z θ + z * Work.Spaces.pzIter 2 F z θ := by
    have h1' : deriv ((fun t : ℝ => t) * fun t : ℝ => Work.Spaces.pz F t θ) z
        = deriv (fun t : ℝ => t) z * Work.Spaces.pz F z θ
          + z * deriv (fun t : ℝ => Work.Spaces.pz F t θ) z :=
      deriv_mul (c := fun t : ℝ => t) (d := fun t : ℝ => Work.Spaces.pz F t θ)
        differentiableAt_id hdg
    rw [show (fun t : ℝ => t * Work.Spaces.pz F t θ)
          = ((fun t : ℝ => t) * fun t : ℝ => Work.Spaces.pz F t θ) from rfl,
        h1', deriv_id'', one_mul]
    simp only [Work.Spaces.pzIter_succ, Work.Spaces.pzIter_zero, Work.Spaces.pz]
  -- hence `D_z² F = D_z F + z² ∂_z²F` at the point
  have hexp : Work.Spaces.DzIter 2 F z θ
      = Work.Spaces.Dz F z θ + z ^ 2 * Work.Spaces.pzIter 2 F z θ := by
    rw [show Work.Spaces.DzIter 2 F z θ
          = z * deriv (fun t : ℝ => t * Work.Spaces.pz F t θ) z from rfl, hderiv]
    show z * (Work.Spaces.pz F z θ + z * Work.Spaces.pzIter 2 F z θ)
        = z * Work.Spaces.pz F z θ + z ^ 2 * Work.Spaces.pzIter 2 F z θ
    ring
  have hsplit : z ^ 2 * Work.Spaces.pzIter 2 F z θ
      = Work.Spaces.DzIter 2 F z θ - Work.Spaces.Dz F z θ := by linarith
  have hkey0 : |z ^ 2 * Work.Spaces.pzIter 2 F z θ| ≤ 2 * C := by
    rw [hsplit]
    calc |Work.Spaces.DzIter 2 F z θ - Work.Spaces.Dz F z θ|
        ≤ |Work.Spaces.DzIter 2 F z θ| + |Work.Spaces.Dz F z θ| := abs_sub _ _
      _ ≤ C + C := add_le_add h2 h1
      _ = 2 * C := by ring
  have hkey : z ^ 2 * |Work.Spaces.pzIter 2 F z θ| ≤ 2 * C := by
    have h := hkey0
    rwa [abs_mul, abs_of_nonneg (sq_nonneg z)] at h
  have hbound : |Work.Spaces.pzIter 2 F z θ| ≤ 2 * C / z ^ 2 := by
    rw [le_div_iff₀ hzsq]
    simpa [mul_comm] using hkey
  have hstep : (2 * C) / z ^ 2 ≤ (2 * C) / (z₀ ^ 2 / 4) :=
    div_le_div_of_nonneg_left (by linarith) (by positivity) (by nlinarith [hz, hz₀])
  have hcoe : (2 * C) / (z₀ ^ 2 / 4) = 8 * C / z₀ ^ 2 := by
    field_simp
    ring
  calc |Work.Spaces.pzIter 2 F z θ| ≤ 2 * C / z ^ 2 := hbound
    _ ≤ (2 * C) / (z₀ ^ 2 / 4) := hstep
    _ = 8 * C / z₀ ^ 2 := hcoe

end Work.FTS_RegExport.RXT
end
-- ===== merged: Submission.Work.FTS_RegExport.RXT.velPertAux.paramC2 =====
section

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

open scoped Real Topology
open MeasureTheory Set Filter

set_option autoImplicit false

noncomputable section

namespace Work.FTS_RegExport.RXT.velPertAux

/-!
# `paramC2`: `C²`-regularity of the angular parametric integral

`z ↦ ∫_θ F z θ · φ θ` is `C²` on `(0,∞)` when `F` is `C²` on the open quadrant
`(0,∞) × (0,π/2)`, `φ` is continuous on `Iθ = [0,π/2]` and `F`, `D_z F`, `D_z² F` are
bounded by `C` on the open quadrant.

The proof differentiates twice under the integral sign
(`hasDerivAt_integral_of_dominated_loc_of_deriv_le`), the local dominating function being
the constant `C/(z/2) · |φ|_∞`.  In order to avoid a second-order product-rule identity in
`∂_z`, the second derivative is computed for the scaled integrand `D_z F = z ∂_z F` (whose
`z`-derivative is `z ∂_z² F`, bounded by `C/z` because of the hypothesis on `D_z² F`), and
the two parametric integrals are related by `∫_θ D_z F = z ∫_θ ∂_z F`.
-/

/-! ## Elementary calculus helpers -/

/-- The `z`-partial derivative is the Fréchet derivative in the direction `(1,0)`. -/
private theorem pz_eq_fderiv {G : ℝ → ℝ → ℝ} {z θ : ℝ}
    (h : DifferentiableAt ℝ (Function.uncurry G) (z, θ)) :
    Work.Spaces.pz G z θ = fderiv ℝ (Function.uncurry G) (z, θ) (1, 0) := by
  have hcurve : HasDerivAt (fun t : ℝ => (t, θ)) (1, 0) z := by
    simpa using (hasDerivAt_id z).prodMk (hasDerivAt_const z θ)
  exact (h.hasFDerivAt.comp_hasDerivAt z hcurve).deriv

/-- The `z`-slice of a differentiable function of two variables is differentiable. -/
private theorem differentiableAt_slice_left {G : ℝ → ℝ → ℝ} {x θ : ℝ}
    (h : DifferentiableAt ℝ (Function.uncurry G) (x, θ)) :
    DifferentiableAt ℝ (fun x' => G x' θ) x := by
  have hcurve : HasDerivAt (fun t : ℝ => (t, θ)) (1, 0) x := by
    simpa using (hasDerivAt_id x).prodMk (hasDerivAt_const x θ)
  exact (h.hasFDerivAt.comp_hasDerivAt x hcurve).differentiableAt

/-- The `θ`-slice at a positive `z` of a function continuous on the open quadrant is
continuous. -/
private theorem slice_continuousOn {G : ℝ → ℝ → ℝ}
    (h : ContinuousOn (Function.uncurry G) (Set.Ioi 0 ×ˢ Set.Ioo 0 (Real.pi / 2)))
    {x : ℝ} (hx : 0 < x) : ContinuousOn (fun θ => G x θ) (Set.Ioo 0 (Real.pi / 2)) := by
  have hg : ContinuousOn (fun θ : ℝ => (x, θ)) (Set.Ioo 0 (Real.pi / 2)) :=
    (Continuous.prodMk_right x).continuousOn
  have hmap : Set.MapsTo (fun θ : ℝ => (x, θ)) (Set.Ioo 0 (Real.pi / 2))
      (Set.Ioi 0 ×ˢ Set.Ioo 0 (Real.pi / 2)) := fun θ hθ => ⟨hx, hθ⟩
  exact (h.comp hg hmap).congr (fun θ _ => rfl)

/-- The `z`-slice at an interior angle of a function continuous on the open quadrant is
continuous at a positive `x`. -/
private theorem slice_continuousAt {G : ℝ → ℝ → ℝ}
    (h : ContinuousOn (Function.uncurry G) (Set.Ioi 0 ×ˢ Set.Ioo 0 (Real.pi / 2)))
    {x θ : ℝ} (hx : 0 < x) (hθ : θ ∈ Set.Ioo 0 (Real.pi / 2)) :
    ContinuousAt (fun x' => G x' θ) x := by
  have hV : (Set.Ioi 0 ×ˢ Set.Ioo 0 (Real.pi / 2)) ∈ 𝓝 (x, θ) :=
    (isOpen_Ioi.prod isOpen_Ioo).mem_nhds ⟨hx, hθ⟩
  have hcont : ContinuousAt (Function.uncurry G) (x, θ) := h.continuousAt hV
  have hcurve : Filter.Tendsto (fun x' : ℝ => (x', θ)) (𝓝 x) (𝓝 (x, θ)) :=
    (Continuous.prodMk_left θ).continuousAt
  show Filter.Tendsto (fun x' : ℝ => G x' θ) (𝓝 x) (𝓝 (G x θ))
  exact hcont.tendsto.comp hcurve

/-- `∂_z` lowers the order of differentiability on the open quadrant by one. -/
private theorem contDiffOn_uncurry_pz {G : ℝ → ℝ → ℝ} {n : ℕ}
    (h : ContDiffOn ℝ (n + 1) (Function.uncurry G) (Set.Ioi 0 ×ˢ Set.Ioo 0 (Real.pi / 2))) :
    ContDiffOn ℝ n (Function.uncurry (Work.Spaces.pz G))
      (Set.Ioi 0 ×ˢ Set.Ioo 0 (Real.pi / 2)) := by
  have hV : IsOpen (Set.Ioi (0 : ℝ) ×ˢ Set.Ioo 0 (Real.pi / 2)) := isOpen_Ioi.prod isOpen_Ioo
  have hdiff : ∀ p ∈ (Set.Ioi (0 : ℝ) ×ˢ Set.Ioo 0 (Real.pi / 2)),
      DifferentiableAt ℝ (Function.uncurry G) p := fun p hp =>
    (h.differentiableOn (by norm_num)).differentiableAt (hV.mem_nhds hp)
  have hfd : ContDiffOn ℝ n (fun p : ℝ × ℝ => fderiv ℝ (Function.uncurry G) p)
      (Set.Ioi 0 ×ˢ Set.Ioo 0 (Real.pi / 2)) := h.fderiv_of_isOpen hV le_rfl
  have hcomp : ContDiffOn ℝ n
      (fun p : ℝ × ℝ => (fderiv ℝ (Function.uncurry G) p) (1, 0))
      (Set.Ioi 0 ×ˢ Set.Ioo 0 (Real.pi / 2)) := hfd.clm_apply contDiffOn_const
  exact hcomp.congr (fun p hp => pz_eq_fderiv (hdiff p hp))

/-- `D_z` lowers the order of differentiability on the open quadrant by one. -/
private theorem contDiffOn_uncurry_Dz {G : ℝ → ℝ → ℝ} {n : ℕ}
    (h : ContDiffOn ℝ (n + 1) (Function.uncurry G) (Set.Ioi 0 ×ˢ Set.Ioo 0 (Real.pi / 2))) :
    ContDiffOn ℝ n (Function.uncurry (Work.Spaces.Dz G))
      (Set.Ioi 0 ×ˢ Set.Ioo 0 (Real.pi / 2)) := by
  have hpz := contDiffOn_uncurry_pz (n := n) h
  have h1 : ContDiffOn ℝ n (fun p : ℝ × ℝ => p.1)
      (Set.Ioi 0 ×ˢ Set.Ioo 0 (Real.pi / 2)) := contDiff_fst.contDiffOn
  refine (h1.mul hpz).congr (fun p _ => ?_)
  simp only [Function.uncurry, Work.Spaces.Dz]

/-- **Parametric integral with one differentiation.**  If the slices of `G` and of `G'` are
continuous on `(0,π/2)`, `G` is bounded by `Kg` there, `G'` is bounded by `Cg/z`, `φ` is
continuous and bounded by `B` on `Iθ`, and `G'` is the `z`-derivative of `G` pointwise,
then `z ↦ ∫_θ G z θ · φ θ` is `C¹` on `(0,∞)` with derivative `z ↦ ∫_θ G' z θ · φ θ`. -/
private theorem paramIntegral_aux {G G' : ℝ → ℝ → ℝ} {φ : ℝ → ℝ} {B Kg Cg : ℝ}
    (hB0 : 0 ≤ B) (hKg0 : 0 ≤ Kg) (hCg0 : 0 ≤ Cg)
    (hφcont : ContinuousOn φ (Set.Ioo 0 (Real.pi / 2)))
    (hφB : ∀ θ ∈ Work.Spaces.Iθ, |φ θ| ≤ B)
    (hGbd : ∀ z : ℝ, 0 < z → ∀ θ : ℝ, 0 < θ → θ < Real.pi / 2 → |G z θ| ≤ Kg)
    (hG'bd : ∀ z : ℝ, 0 < z → ∀ θ : ℝ, 0 < θ → θ < Real.pi / 2 → |G' z θ| ≤ Cg / z)
    (hGcont : ContinuousOn (Function.uncurry G) (Set.Ioi 0 ×ˢ Set.Ioo 0 (Real.pi / 2)))
    (hG'cont : ContinuousOn (Function.uncurry G') (Set.Ioi 0 ×ˢ Set.Ioo 0 (Real.pi / 2)))
    (hdiff : ∀ x θ : ℝ, 0 < x → 0 < θ → θ < Real.pi / 2 →
      HasDerivAt (fun x' => G x' θ) (G' x θ) x) :
    ContDiffOn ℝ 1 (fun u => ∫ θ in Set.Ioo 0 (Real.pi / 2), G u θ * φ θ) (Set.Ioi 0) ∧
      ∀ z : ℝ, 0 < z →
        HasDerivAt (fun u => ∫ θ in Set.Ioo 0 (Real.pi / 2), G u θ * φ θ)
          (∫ θ in Set.Ioo 0 (Real.pi / 2), G' z θ * φ θ) z := by
  have haesmφ : AEStronglyMeasurable φ (volume.restrict (Set.Ioo 0 (Real.pi / 2))) :=
    hφcont.aestronglyMeasurable measurableSet_Ioo
  have haesmG : ∀ x : ℝ, 0 < x → AEStronglyMeasurable (fun θ => G x θ)
      (volume.restrict (Set.Ioo 0 (Real.pi / 2))) :=
    fun x hx => (slice_continuousOn hGcont hx).aestronglyMeasurable measurableSet_Ioo
  have haesmG' : ∀ x : ℝ, 0 < x → AEStronglyMeasurable (fun θ => G' x θ)
      (volume.restrict (Set.Ioo 0 (Real.pi / 2))) :=
    fun x hx => (slice_continuousOn hG'cont hx).aestronglyMeasurable measurableSet_Ioo
  -- local bound for `G'` on a neighbourhood of a positive point
  have hloc : ∀ z : ℝ, 0 < z → ∀ x ∈ Set.Ioo (z / 2) (2 * z), ∀ θ : ℝ,
      0 < θ → θ < Real.pi / 2 → |G' x θ| ≤ Cg / (z / 2) := by
    intro z hz x hx θ hθ hθ2
    exact le_trans (hG'bd x (by linarith [hx.1]) θ hθ hθ2)
      (div_le_div_of_nonneg_left hCg0 (by linarith) (le_of_lt hx.1))
  -- integrability of the integrands
  have hint : ∀ z : ℝ, 0 < z → Integrable (fun θ => G z θ * φ θ)
      (volume.restrict (Set.Ioo 0 (Real.pi / 2))) := by
    intro z hz
    refine MeasureTheory.Integrable.of_bound ((haesmG z hz).mul haesmφ) (Kg * B) ?_
    filter_upwards [MeasureTheory.ae_restrict_mem measurableSet_Ioo] with θ hθ
    rw [Real.norm_eq_abs, abs_mul]
    exact mul_le_mul (hGbd z hz θ hθ.1 hθ.2) (hφB θ ⟨le_of_lt hθ.1, le_of_lt hθ.2⟩)
      (abs_nonneg _) hKg0
  have hderiv : ∀ z : ℝ, 0 < z → HasDerivAt
      (fun u => ∫ θ in Set.Ioo 0 (Real.pi / 2), G u θ * φ θ)
      (∫ θ in Set.Ioo 0 (Real.pi / 2), G' z θ * φ θ) z := by
    intro z hz
    have hs : Set.Ioo (z / 2) (2 * z) ∈ 𝓝 z := isOpen_Ioo.mem_nhds ⟨by linarith, by linarith⟩
    have hK0 : 0 ≤ Cg / (z / 2) := div_nonneg hCg0 (by linarith)
    have h1 : ∀ᶠ x in 𝓝 z, AEStronglyMeasurable (fun θ => G x θ * φ θ)
        (volume.restrict (Set.Ioo 0 (Real.pi / 2))) := by
      filter_upwards [hs] with x hx
      exact (haesmG x (by linarith [hx.1])).mul haesmφ
    have h2 : Integrable (fun θ => G z θ * φ θ)
        (volume.restrict (Set.Ioo 0 (Real.pi / 2))) := hint z hz
    have h3 : AEStronglyMeasurable (fun θ => G' z θ * φ θ)
        (volume.restrict (Set.Ioo 0 (Real.pi / 2))) := (haesmG' z hz).mul haesmφ
    have h4 : ∀ᵐ a ∂(volume.restrict (Set.Ioo 0 (Real.pi / 2))),
        ∀ x ∈ Set.Ioo (z / 2) (2 * z),
          ‖G' x a * φ a‖ ≤ (fun _ : ℝ => Cg / (z / 2) * B) a := by
      filter_upwards [MeasureTheory.ae_restrict_mem measurableSet_Ioo] with θ hθ
      intro x hx
      rw [Real.norm_eq_abs, abs_mul]
      exact mul_le_mul (hloc z hz x hx θ hθ.1 hθ.2)
        (hφB θ ⟨le_of_lt hθ.1, le_of_lt hθ.2⟩) (abs_nonneg _) hK0
    have h5 : Integrable (fun _ : ℝ => Cg / (z / 2) * B)
        (volume.restrict (Set.Ioo 0 (Real.pi / 2))) :=
      MeasureTheory.integrable_const_iff.mpr (Or.inr inferInstance)
    have h6 : ∀ᵐ a ∂(volume.restrict (Set.Ioo 0 (Real.pi / 2))),
        ∀ x ∈ Set.Ioo (z / 2) (2 * z),
          HasDerivAt (fun x' => G x' a * φ a) (G' x a * φ a) x := by
      filter_upwards [MeasureTheory.ae_restrict_mem measurableSet_Ioo] with θ hθ
      intro x hx
      exact (hdiff x θ (by linarith [hx.1]) hθ.1 hθ.2).mul_const (φ θ)
    exact (hasDerivAt_integral_of_dominated_loc_of_deriv_le
      (μ := volume.restrict (Set.Ioo 0 (Real.pi / 2)))
      (F := fun u θ => G u θ * φ θ) (F' := fun u θ => G' u θ * φ θ)
      (bound := fun _ => Cg / (z / 2) * B) (x₀ := z) (s := Set.Ioo (z / 2) (2 * z))
      hs h1 h2 h3 h4 h5 h6).2
  have hcontderiv : ContinuousOn
      (fun u => ∫ θ in Set.Ioo 0 (Real.pi / 2), G' u θ * φ θ) (Set.Ioi 0) := by
    intro z hz
    have hz0 : 0 < z := by simpa using hz
    have hs : Set.Ioo (z / 2) (2 * z) ∈ 𝓝 z := isOpen_Ioo.mem_nhds ⟨by linarith, by linarith⟩
    have hK0 : 0 ≤ Cg / (z / 2) := div_nonneg hCg0 (by linarith)
    refine (MeasureTheory.continuousAt_of_dominated
      (μ := volume.restrict (Set.Ioo 0 (Real.pi / 2)))
      (F := fun u θ => G' u θ * φ θ) (bound := fun _ => Cg / (z / 2) * B) (x₀ := z)
      ?_ ?_ ?_ ?_).continuousWithinAt
    · filter_upwards [hs] with x hx
      exact (haesmG' x (by linarith [hx.1, hz0])).mul haesmφ
    · filter_upwards [hs] with x hx
      filter_upwards [MeasureTheory.ae_restrict_mem measurableSet_Ioo] with θ hθ
      rw [Real.norm_eq_abs, abs_mul]
      exact mul_le_mul (hloc z hz0 x hx θ hθ.1 hθ.2)
        (hφB θ ⟨le_of_lt hθ.1, le_of_lt hθ.2⟩) (abs_nonneg _) hK0
    · exact MeasureTheory.integrable_const_iff.mpr (Or.inr inferInstance)
    · filter_upwards [MeasureTheory.ae_restrict_mem measurableSet_Ioo] with θ hθ
      exact (slice_continuousAt hG'cont hz0 hθ).mul_const (φ θ)
  refine ⟨?_, hderiv⟩
  refine (contDiffOn_succ_iff_deriv_of_isOpen (n := (0 : WithTop ℕ∞)) isOpen_Ioi).mpr
    ⟨?_, ?_, ?_⟩
  · intro z hz
    exact (hderiv z (by simpa using hz)).differentiableAt.differentiableWithinAt
  · exact fun h => absurd h (by simp)
  · rw [contDiffOn_zero]
    exact hcontderiv.congr (fun z hz => (hderiv z (by simpa using hz)).deriv)

/-! ## The main statement -/

theorem paramC2 {F : ℝ → ℝ → ℝ} {φ : ℝ → ℝ} {C : ℝ}
    (hφ : ContinuousOn φ Work.Spaces.Iθ)
    (hF : ContDiffOn ℝ 2 (Function.uncurry F) (Set.Ioi 0 ×ˢ Set.Ioo 0 (Real.pi / 2)))
    (hb : ∀ z θ : ℝ, 0 < z → 0 < θ → θ < Real.pi / 2 →
      |F z θ| ≤ C ∧ |Work.Spaces.Dz F z θ| ≤ C ∧ |Work.Spaces.DzIter 2 F z θ| ≤ C) :
    ContDiffOn ℝ 2 (fun z => ∫ θ in Work.Spaces.Iθ, F z θ * φ θ) (Set.Ioi 0) := by
  have hpi4 : (0 : ℝ) < Real.pi / 4 := by linarith [Real.pi_pos]
  have hpi42 : Real.pi / 4 < Real.pi / 2 := by linarith [Real.pi_pos]
  have hquarter : Real.pi / 4 ∈ Work.Spaces.Iθ := ⟨le_of_lt hpi4, le_of_lt hpi42⟩
  -- a bound for `φ` on `Iθ`
  obtain ⟨B, hB⟩ := isCompact_Icc.exists_bound_of_continuousOn hφ
  have hB0 : 0 ≤ B := by
    have h := hB (Real.pi / 4) hquarter
    rw [Real.norm_eq_abs] at h
    exact le_trans (abs_nonneg _) h
  have hφB : ∀ θ ∈ Work.Spaces.Iθ, |φ θ| ≤ B := by
    intro θ hθ
    have h := hB θ hθ
    rwa [Real.norm_eq_abs] at h
  have hφcont : ContinuousOn φ (Set.Ioo 0 (Real.pi / 2)) :=
    hφ.mono (fun θ hθ => ⟨le_of_lt hθ.1, le_of_lt hθ.2⟩)
  have hC0 : 0 ≤ C := by
    have h := (hb 1 (Real.pi / 4) one_pos hpi4 hpi42).1
    exact le_trans (abs_nonneg _) h
  have hVopen : IsOpen (Set.Ioi (0 : ℝ) ×ˢ Set.Ioo 0 (Real.pi / 2)) :=
    isOpen_Ioi.prod isOpen_Ioo
  have hquad : ∀ x θ : ℝ, 0 < x → 0 < θ → θ < Real.pi / 2 →
      (x, θ) ∈ (Set.Ioi (0 : ℝ) ×ˢ Set.Ioo 0 (Real.pi / 2)) :=
    fun x θ hx hθ hθ2 => ⟨hx, hθ, hθ2⟩
  -- the pointwise hypotheses
  have hFbd : ∀ z : ℝ, 0 < z → ∀ θ : ℝ, 0 < θ → θ < Real.pi / 2 → |F z θ| ≤ C :=
    fun z hz θ hθ hθ2 => (hb z θ hz hθ hθ2).1
  have hDzFbd : ∀ z : ℝ, 0 < z → ∀ θ : ℝ, 0 < θ → θ < Real.pi / 2 →
      |Work.Spaces.Dz F z θ| ≤ C := fun z hz θ hθ hθ2 => (hb z θ hz hθ hθ2).2.1
  have hDzIterFbd : ∀ z : ℝ, 0 < z → ∀ θ : ℝ, 0 < θ → θ < Real.pi / 2 →
      |Work.Spaces.DzIter 2 F z θ| ≤ C := fun z hz θ hθ hθ2 => (hb z θ hz hθ hθ2).2.2
  have hpzFbd : ∀ z : ℝ, 0 < z → ∀ θ : ℝ, 0 < θ → θ < Real.pi / 2 →
      |Work.Spaces.pz F z θ| ≤ C / z := by
    intro z hz θ hθ hθ2
    have h : z * |Work.Spaces.pz F z θ| ≤ C := by
      have h := hDzFbd z hz θ hθ hθ2
      rw [show Work.Spaces.Dz F z θ = z * Work.Spaces.pz F z θ from rfl, abs_mul,
        abs_of_pos hz] at h
      exact h
    rw [mul_comm] at h
    exact (le_div_iff₀ hz).mpr h
  have hpzDzFbd : ∀ z : ℝ, 0 < z → ∀ θ : ℝ, 0 < θ → θ < Real.pi / 2 →
      |Work.Spaces.pz (Work.Spaces.Dz F) z θ| ≤ C / z := by
    intro z hz θ hθ hθ2
    have h : z * |Work.Spaces.pz (Work.Spaces.Dz F) z θ| ≤ C := by
      have h := hDzIterFbd z hz θ hθ hθ2
      rw [show Work.Spaces.DzIter 2 F z θ
          = z * Work.Spaces.pz (Work.Spaces.Dz F) z θ from rfl, abs_mul, abs_of_pos hz] at h
      exact h
    rw [mul_comm] at h
    exact (le_div_iff₀ hz).mpr h
  -- the joint continuity of the integrands
  have hFcont : ContinuousOn (Function.uncurry F) (Set.Ioi 0 ×ˢ Set.Ioo 0 (Real.pi / 2)) :=
    hF.continuousOn
  have hpzFcont : ContinuousOn (Function.uncurry (Work.Spaces.pz F))
      (Set.Ioi 0 ×ˢ Set.Ioo 0 (Real.pi / 2)) := (contDiffOn_uncurry_pz (n := 1) hF).continuousOn
  have hDzFcont : ContinuousOn (Function.uncurry (Work.Spaces.Dz F))
      (Set.Ioi 0 ×ˢ Set.Ioo 0 (Real.pi / 2)) := (contDiffOn_uncurry_Dz (n := 1) hF).continuousOn
  have hpzDzFcont : ContinuousOn (Function.uncurry (Work.Spaces.pz (Work.Spaces.Dz F)))
      (Set.Ioi 0 ×ˢ Set.Ioo 0 (Real.pi / 2)) :=
    (contDiffOn_uncurry_pz (n := 0) (contDiffOn_uncurry_Dz (n := 1) hF)).continuousOn
  -- pointwise `z`-derivatives
  have hdiffF : ∀ x θ : ℝ, 0 < x → 0 < θ → θ < Real.pi / 2 →
      HasDerivAt (fun x' => F x' θ) (Work.Spaces.pz F x θ) x := by
    intro x θ hx hθ hθ2
    have hd : DifferentiableAt ℝ (Function.uncurry F) (x, θ) :=
      (hF.differentiableOn (by norm_num)).differentiableAt
        (hVopen.mem_nhds (hquad x θ hx hθ hθ2))
    exact (differentiableAt_slice_left hd).hasDerivAt
  have hdiffDz : ∀ x θ : ℝ, 0 < x → 0 < θ → θ < Real.pi / 2 →
      HasDerivAt (fun x' => Work.Spaces.Dz F x' θ)
        (Work.Spaces.pz (Work.Spaces.Dz F) x θ) x := by
    intro x θ hx hθ hθ2
    have hd : DifferentiableAt ℝ (Function.uncurry (Work.Spaces.Dz F)) (x, θ) :=
      ((contDiffOn_uncurry_Dz (n := 1) hF).differentiableOn (by norm_num)).differentiableAt
        (hVopen.mem_nhds (hquad x θ hx hθ hθ2))
    exact (differentiableAt_slice_left hd).hasDerivAt
  -- the two parametric integrals
  have hFaux := paramIntegral_aux (G := F) (G' := Work.Spaces.pz F) (φ := φ)
    (B := B) (Kg := C) (Cg := C) hB0 hC0 hC0 hφcont hφB hFbd hpzFbd
    hFcont hpzFcont hdiffF
  have hDzaux := paramIntegral_aux (G := Work.Spaces.Dz F)
    (G' := Work.Spaces.pz (Work.Spaces.Dz F)) (φ := φ) (B := B) (Kg := C) (Cg := C)
    hB0 hC0 hC0 hφcont hφB hDzFbd hpzDzFbd hDzFcont hpzDzFcont hdiffDz
  -- the scaled integral is `z` times the unscaled one
  have hA'eq : ∀ z : ℝ, 0 < z →
      (∫ θ in Set.Ioo 0 (Real.pi / 2), Work.Spaces.Dz F z θ * φ θ)
        = z * (∫ θ in Set.Ioo 0 (Real.pi / 2), Work.Spaces.pz F z θ * φ θ) := by
    intro z _
    rw [← integral_const_mul z (fun θ => Work.Spaces.pz F z θ * φ θ)]
    refine setIntegral_congr_fun measurableSet_Ioo (fun θ _ => ?_)
    rw [show Work.Spaces.Dz F z θ = z * Work.Spaces.pz F z θ from rfl]
    ring
  -- continuity of the derivative of the scaled integral
  have hB'cont : ContinuousOn
      (fun u => ∫ θ in Set.Ioo 0 (Real.pi / 2),
        Work.Spaces.pz (Work.Spaces.Dz F) u θ * φ θ) (Set.Ioi 0) := by
    have hmp := (contDiffOn_succ_iff_deriv_of_isOpen (𝕜 := ℝ) (n := (0 : WithTop ℕ∞))
      (f := fun u => ∫ θ in Set.Ioo 0 (Real.pi / 2), Work.Spaces.Dz F u θ * φ θ)
      (s := Set.Ioi 0) isOpen_Ioi).mp hDzaux.1
    exact (contDiffOn_zero.mp hmp.2.2).congr
      (fun z hz => (hDzaux.2 z (by simpa using hz)).deriv.symm)
  -- `C¹` for the unscaled integral
  have hAcd : ContDiffOn ℝ 1
      (fun z => ∫ θ in Set.Ioo 0 (Real.pi / 2), Work.Spaces.pz F z θ * φ θ) (Set.Ioi 0) := by
    refine (hDzaux.1.div contDiffOn_id (fun z hz => ne_of_gt (by simpa using hz))).congr
      (fun z hz => ?_)
    have hz0 : 0 < z := by simpa using hz
    have h := hA'eq z hz0
    change (∫ θ in Set.Ioo 0 (Real.pi / 2), Work.Spaces.pz F z θ * φ θ)
      = (∫ θ in Set.Ioo 0 (Real.pi / 2), Work.Spaces.Dz F z θ * φ θ) / z
    rw [h, eq_div_iff (ne_of_gt hz0)]
    ring
  -- `C²` for the parametric integral over `(0,π/2)`
  have hG0cd : ContDiffOn ℝ 2
      (fun z => ∫ θ in Set.Ioo 0 (Real.pi / 2), F z θ * φ θ) (Set.Ioi 0) := by
    refine (contDiffOn_succ_iff_deriv_of_isOpen (𝕜 := ℝ) (n := (1 : WithTop ℕ∞))
      (f := fun z => ∫ θ in Set.Ioo 0 (Real.pi / 2), F z θ * φ θ)
      (s := Set.Ioi 0) isOpen_Ioi).mpr ⟨?_, ?_, ?_⟩
    · intro z hz
      exact (hFaux.2 z (by simpa using hz)).differentiableAt.differentiableWithinAt
    · exact fun h => absurd h (by simp)
    · exact hAcd.congr (fun z hz => (hFaux.2 z (by simpa using hz)).deriv)
  -- transfer from `(0,π/2)` to `[0,π/2]`
  have hnull : volume ({0, Real.pi / 2} : Set ℝ) = 0 := by
    have hset : ({0, Real.pi / 2} : Set ℝ) = {0} ∪ {Real.pi / 2} := by
      ext x
      simp only [Set.mem_insert_iff, Set.mem_singleton_iff, Set.mem_union]
    rw [hset]
    exact measure_union_null (measure_singleton 0) (measure_singleton (Real.pi / 2))
  have hIccdiff : Work.Spaces.Iθ \ Set.Ioo 0 (Real.pi / 2) ⊆ ({0, Real.pi / 2} : Set ℝ) := by
    intro x hx
    obtain ⟨hxI, hxnot⟩ := hx
    simp only [Work.Spaces.Iθ, Set.mem_Icc] at hxI
    rw [Set.mem_Ioo, not_and_or, not_lt, not_lt] at hxnot
    simp only [Set.mem_insert_iff, Set.mem_singleton_iff]
    rcases hxnot with h | h
    · exact Or.inl (le_antisymm h hxI.1)
    · exact Or.inr (le_antisymm hxI.2 h)
  have hIoodiff : Set.Ioo 0 (Real.pi / 2) \ Work.Spaces.Iθ ⊆ ({0, Real.pi / 2} : Set ℝ) := by
    intro x hx
    exact absurd ⟨le_of_lt hx.1.1, le_of_lt hx.1.2⟩ hx.2
  have haeeq : Work.Spaces.Iθ =ᵐ[volume] Set.Ioo 0 (Real.pi / 2) := by
    rw [MeasureTheory.ae_eq_set]
    exact ⟨measure_mono_null hIccdiff hnull, measure_mono_null hIoodiff hnull⟩
  exact hG0cd.congr (fun _ _ => setIntegral_congr_set haeeq)

end Work.FTS_RegExport.RXT.velPertAux
end
end
-- ===== merged: Submission.Work.H2.T1Q.IbpCutoffDefs =====
section

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

noncomputable section

open scoped Real Topology
open MeasureTheory Set Filter

namespace Work.H2.T1Q

/-- The left-hand integrand of `IbpCutoff`: `sin(2θ)^{-q}·(χ θ · hf θ)·(sin(2θ)·hv' θ)·hv θ`. -/
def IbpG (q : ℝ) (χ hf hv : ℝ → ℝ) : ℝ → ℝ :=
  fun θ => (Real.sin (2 * θ)) ^ (-q) * (χ θ * hf θ) * (Real.sin (2 * θ) * deriv hv θ) * hv θ

/-- The right-hand integrand of `IbpCutoff`, without the overall sign:

`sin(2θ)^{-q}·(χ θ·((1/2)·sin(2θ)·hf' θ + (1-q)·cos(2θ)·hf θ) + (1/2)·sin(2θ)·χ' θ·hf θ)·hv θ²`. -/
def IbpK (q : ℝ) (χ hf hv : ℝ → ℝ) : ℝ → ℝ :=
  fun θ => (Real.sin (2 * θ)) ^ (-q)
      * (χ θ * ((1 / 2) * (Real.sin (2 * θ) * deriv hf θ)
            + (1 - q) * Real.cos (2 * θ) * hf θ)
          + (1 / 2) * (Real.sin (2 * θ) * deriv χ θ) * hf θ)
      * (hv θ) ^ 2

/-- The primitive of the angular integration by parts: `(1/2)·sin(2θ)^{1-q}·χ θ·hf θ·hv θ²`. -/
def IbpPrim (q : ℝ) (χ hf hv : ℝ → ℝ) : ℝ → ℝ :=
  fun θ => (1 / 2) * (Real.sin (2 * θ)) ^ (1 - q) * (χ θ * hf θ) * (hv θ) ^ 2

end Work.H2.T1Q
end
end
-- ===== merged: Submission.Work.H2.T1Q.ShrinkInt =====
section

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

namespace Work.H2.T1Q

open MeasureTheory Filter Set
open scoped Topology

/-- The two end-shrinking integrals of an integrable function on `Iθ = [0, π/2]` tend to `0`.

Writing `a n = 1 / (n + 4)`, the first integral is `∫_{(0, a n]} h = F (a n)`, the primitive `F`
of `h`; the second is `∫_{(π/2 - a n, π/2]} h = F (π/2) - F (π/2 - a n)`.  Since `h` is integrable
on `[0, π/2]`, `F` is continuous there, and `a n → 0`, both terms vanish in the limit. -/
theorem ShrinkInt {h : ℝ → ℝ} (hh : MeasureTheory.IntegrableOn h Work.Spaces.Iθ) :
    Filter.Tendsto (fun n : ℕ => (∫ θ in Set.Ioc (0 : ℝ) (1 / ((n : ℝ) + 4)), h θ)
      + ∫ θ in Set.Ioc (Real.pi / 2 - 1 / ((n : ℝ) + 4)) (Real.pi / 2), h θ)
      Filter.atTop (nhds 0) := by
  classical
  have hpi2 : (0 : ℝ) ≤ Real.pi / 2 := by positivity
  have hq4 : (1 : ℝ) / 4 ≤ Real.pi / 2 := by linarith [Real.pi_gt_three]
  have hint : IntegrableOn h (Set.uIcc (0 : ℝ) (Real.pi / 2)) volume := by
    rw [Set.uIcc_of_le hpi2]; exact hh
  have hcont : ContinuousOn (fun t : ℝ => ∫ x in (0 : ℝ)..t, h x)
      (Set.uIcc (0 : ℝ) (Real.pi / 2)) :=
    intervalIntegral.continuousOn_primitive_interval hint
  have hA : Tendsto (fun n : ℕ => (1 : ℝ) / ((n : ℝ) + 4)) atTop (nhds 0) := by
    have hshift : Tendsto (fun n : ℕ => (n : ℝ) + 4) atTop atTop := by
      have h2 := (tendsto_natCast_atTop_atTop (R := ℝ)).comp (Filter.tendsto_add_atTop_nat 4)
      simpa only [Function.comp_def, Nat.cast_add, Nat.cast_ofNat] using h2
    have h1 : Tendsto (fun n : ℕ => ((n : ℝ) + 4)⁻¹) atTop (nhds 0) := hshift.inv_tendsto_atTop
    simpa [one_div] using h1
  have hle_half : ∀ n : ℕ, (1 : ℝ) / ((n : ℝ) + 4) ≤ Real.pi / 2 := by
    intro n
    have hn : (4 : ℝ) ≤ (n : ℝ) + 4 := by
      have : (0:ℝ) ≤ (n:ℝ) := Nat.cast_nonneg n
      linarith
    have h1 : (1 : ℝ) / ((n : ℝ) + 4) ≤ 1 / 4 :=
      one_div_le_one_div_of_le (by norm_num) hn
    linarith
  have hnn : ∀ n : ℕ, (0:ℝ) ≤ (1 : ℝ) / ((n : ℝ) + 4) := by
    intro n; positivity
  have hmemA : ∀ n : ℕ, (1 : ℝ) / ((n : ℝ) + 4) ∈ Set.uIcc (0 : ℝ) (Real.pi / 2) := by
    intro n; rw [Set.uIcc_of_le hpi2]; exact ⟨hnn n, hle_half n⟩
  have hmemB : ∀ n : ℕ, Real.pi / 2 - 1 / ((n : ℝ) + 4) ∈ Set.uIcc (0 : ℝ) (Real.pi / 2) := by
    intro n; rw [Set.uIcc_of_le hpi2]; exact ⟨by linarith [hle_half n], by linarith [hnn n]⟩
  have hFA : Tendsto (fun n : ℕ => ∫ x in (0 : ℝ)..(1 / ((n : ℝ) + 4)), h x) atTop (nhds 0) := by
    have h0 : (0:ℝ) ∈ Set.uIcc (0:ℝ) (Real.pi/2) := Set.left_mem_uIcc
    have hwit : Tendsto (fun n : ℕ => (1 : ℝ) / ((n : ℝ) + 4)) atTop
        (nhdsWithin (0:ℝ) (Set.uIcc (0:ℝ) (Real.pi/2))) :=
      tendsto_nhdsWithin_iff.mpr ⟨hA, Filter.Eventually.of_forall hmemA⟩
    have h' := Filter.Tendsto.comp (hcont.continuousWithinAt h0) hwit
    simpa only [Function.comp_def, intervalIntegral.integral_same] using h'
  have hFB : Tendsto (fun n : ℕ => ∫ x in (0 : ℝ)..(Real.pi / 2 - 1 / ((n : ℝ) + 4)), h x)
      atTop (nhds (∫ x in (0 : ℝ)..(Real.pi / 2), h x)) := by
    have hp : (Real.pi/2) ∈ Set.uIcc (0:ℝ) (Real.pi/2) := Set.right_mem_uIcc
    have hB : Tendsto (fun n : ℕ => Real.pi / 2 - 1 / ((n : ℝ) + 4)) atTop (nhds (Real.pi/2)) := by
      have hh2 := hA.const_sub (Real.pi / 2)
      simpa using hh2
    have hwit : Tendsto (fun n : ℕ => Real.pi / 2 - 1 / ((n : ℝ) + 4)) atTop
        (nhdsWithin (Real.pi/2) (Set.uIcc (0:ℝ) (Real.pi/2))) :=
      tendsto_nhdsWithin_iff.mpr ⟨hB, Filter.Eventually.of_forall hmemB⟩
    have h' := Filter.Tendsto.comp (hcont.continuousWithinAt hp) hwit
    simpa only [Function.comp_def] using h'
  have hmain : Tendsto (fun n : ℕ =>
      (∫ x in (0:ℝ)..(1 / ((n : ℝ) + 4)), h x)
      + ((∫ x in (0:ℝ)..(Real.pi / 2), h x) - ∫ x in (0:ℝ)..(Real.pi / 2 - 1 / ((n : ℝ) + 4)), h x))
      atTop (nhds 0) := by
    have h' := hFA.add (hFB.const_sub (∫ x in (0:ℝ)..(Real.pi / 2), h x))
    simpa using h'
  refine hmain.congr' ?_
  filter_upwards with n
  have hn0 := hnn n
  have hsub : Set.uIcc (0:ℝ) (Real.pi/2 - 1/((n:ℝ)+4)) ⊆ Set.uIcc (0:ℝ) (Real.pi/2) := by
    rw [Set.uIcc_of_le (by linarith [hle_half n] : (0:ℝ) ≤ Real.pi/2 - 1/((n:ℝ)+4)),
      Set.uIcc_of_le hpi2]
    exact Set.Icc_subset_Icc le_rfl (by linarith)
  have hii1 : IntervalIntegrable h volume (0:ℝ) (Real.pi/2) := hint.intervalIntegrable
  have hii2 : IntervalIntegrable h volume (0:ℝ) (Real.pi / 2 - 1/((n:ℝ)+4)) :=
    (hint.mono_set hsub).intervalIntegrable
  have e1 : (∫ x in (0:ℝ)..(1 / ((n : ℝ) + 4)), h x)
      = ∫ θ in Set.Ioc (0:ℝ) (1/((n:ℝ)+4)), h θ := intervalIntegral.integral_of_le hn0
  have e2 : (∫ x in (0:ℝ)..(Real.pi/2), h x) - (∫ x in (0:ℝ)..(Real.pi/2 - 1/((n:ℝ)+4)), h x)
      = ∫ θ in Set.Ioc (Real.pi/2 - 1/((n:ℝ)+4)) (Real.pi/2), h θ := by
    rw [intervalIntegral.integral_interval_sub_left hii1 hii2]
    exact intervalIntegral.integral_of_le (by linarith)
  rw [e1, e2]

end Work.H2.T1Q
end
-- ===== merged: Submission.Work.H2.T1Q.SliceLimit =====
section

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

namespace Work.H2.T1Q

theorem SliceLimit {φ : ℝ → ℝ} {chi : ℕ → ℝ → ℝ} {M : ℝ} {err : ℕ → ℝ}
    (herr : Filter.Tendsto err Filter.atTop (nhds 0))
    (hφint : MeasureTheory.IntegrableOn φ Work.Spaces.Iθ)
    (hchi_meas : ∀ n : ℕ, MeasureTheory.AEStronglyMeasurable (chi n)
      (MeasureTheory.volume.restrict Work.Spaces.Iθ))
    (hchi_le : ∀ (n : ℕ) (θ : ℝ), |chi n θ| ≤ 1)
    (hchi_lim : ∀ᵐ θ ∂(MeasureTheory.volume.restrict Work.Spaces.Iθ),
      Filter.Tendsto (fun n : ℕ => chi n θ) Filter.atTop (nhds 1))
    (hbd : ∀ n : ℕ, |∫ θ in Work.Spaces.Iθ, chi n θ * φ θ| ≤ M + err n) :
    |∫ θ in Work.Spaces.Iθ, φ θ| ≤ M := by
  -- `chi n → 1` a.e. and `|chi n| ≤ 1`, so `∫ chi n · φ → ∫ φ` by dominated
  -- convergence with dominating function `|φ|`.
  have hbound_int : MeasureTheory.Integrable (fun θ => |φ θ|)
      (MeasureTheory.volume.restrict Work.Spaces.Iθ) := hφint.abs
  have hFmeas : ∀ n : ℕ, MeasureTheory.AEStronglyMeasurable
      (fun θ => chi n θ * φ θ) (MeasureTheory.volume.restrict Work.Spaces.Iθ) :=
    fun n => (hchi_meas n).mul hφint.aestronglyMeasurable
  have hb : ∀ n : ℕ, ∀ᵐ θ ∂(MeasureTheory.volume.restrict Work.Spaces.Iθ),
      ‖chi n θ * φ θ‖ ≤ |φ θ| := by
    intro n
    filter_upwards with θ
    rw [Real.norm_eq_abs, abs_mul]
    exact mul_le_of_le_one_left (abs_nonneg _) (hchi_le n θ)
  have hlim_aesm : ∀ᵐ θ ∂(MeasureTheory.volume.restrict Work.Spaces.Iθ),
      Filter.Tendsto (fun n : ℕ => chi n θ * φ θ) Filter.atTop (nhds (φ θ)) := by
    filter_upwards [hchi_lim] with θ hθ
    simpa using hθ.mul_const (φ θ)
  have hconv := MeasureTheory.tendsto_integral_of_dominated_convergence
      (fun θ => |φ θ|) hFmeas hbound_int hb hlim_aesm
  -- Pass to the limit in the bound `|∫ chi n · φ| ≤ M + err n`.
  have h1 : Filter.Tendsto (fun n : ℕ => |∫ θ in Work.Spaces.Iθ, chi n θ * φ θ|) Filter.atTop
      (nhds |∫ θ in Work.Spaces.Iθ, φ θ|) := hconv.abs
  have h2 : Filter.Tendsto (fun n : ℕ => M + err n) Filter.atTop (nhds M) := by
    simpa using (tendsto_const_nhds.add herr)
  exact le_of_tendsto_of_tendsto' h1 h2 (fun n => hbd n)

end Work.H2.T1Q
end
-- ===== merged: Submission.Work.H2W.PsiSlices.contDiffOn_uncurry_dilate =====
section

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

namespace Work.H2W.PsiSlices


end Work.H2W.PsiSlices
end
-- ===== merged: Submission.Work.PhiStar.Honesty.sq_integral_sqrt_mul_le =====
section

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

open MeasureTheory

namespace Work.PhiStar.Honesty

/-- Cauchy–Schwarz for the square roots of two nonnegative integrable functions:
`(∫ √A √B)² ≤ (∫ A)(∫ B)`.  This is the `p = q = 2` Bunyakovsky inequality applied to
`√A` and `√B`, whose squares are `A` and `B` on `s`. -/
theorem sq_integral_sqrt_mul_le {s : Set ℝ} (hs : MeasurableSet s) {A B : ℝ → ℝ}
    (hA : MeasureTheory.IntegrableOn A s) (hB : MeasureTheory.IntegrableOn B s)
    (hAnn : ∀ x ∈ s, 0 ≤ A x) (hBnn : ∀ x ∈ s, 0 ≤ B x) :
    (∫ x in s, Real.sqrt (A x) * Real.sqrt (B x)) ^ 2
      ≤ (∫ x in s, A x) * (∫ x in s, B x) := by
  -- `√A` and `√B` are a.e.-strongly-measurable as continuous images of `A`, `B`.
  have hmeasA : AEStronglyMeasurable (fun x => Real.sqrt (A x)) (volume.restrict s) :=
    Real.continuous_sqrt.comp_aestronglyMeasurable hA.aestronglyMeasurable
  have hmeasB : AEStronglyMeasurable (fun x => Real.sqrt (B x)) (volume.restrict s) :=
    Real.continuous_sqrt.comp_aestronglyMeasurable hB.aestronglyMeasurable
  -- Their squares are `A`, `B` on `s`, hence integrable.
  have hintA : Integrable (fun x => Real.sqrt (A x) ^ 2) (volume.restrict s) :=
    hA.congr_fun (fun x hx => (Real.sq_sqrt (hAnn x hx)).symm) hs
  have hintB : Integrable (fun x => Real.sqrt (B x) ^ 2) (volume.restrict s) :=
    hB.congr_fun (fun x hx => (Real.sq_sqrt (hBnn x hx)).symm) hs
  have hmemA : MemLp (fun x => Real.sqrt (A x)) 2 (volume.restrict s) :=
    (memLp_two_iff_integrable_sq hmeasA).2 hintA
  have hmemB : MemLp (fun x => Real.sqrt (B x)) 2 (volume.restrict s) :=
    (memLp_two_iff_integrable_sq hmeasB).2 hintB
  have hcs := Work.Spaces.cs_integral hmemA hmemB
  have hsqA : (∫ x in s, Real.sqrt (A x) ^ 2) = ∫ x in s, A x :=
    setIntegral_congr_fun hs (fun x hx => Real.sq_sqrt (hAnn x hx))
  have hsqB : (∫ x in s, Real.sqrt (B x) ^ 2) = ∫ x in s, B x :=
    setIntegral_congr_fun hs (fun x hx => Real.sq_sqrt (hBnn x hx))
  rw [hsqA, hsqB] at hcs
  exact hcs

end Work.PhiStar.Honesty
end
-- ===== merged: Submission.Work.R1G.Gam_pi_div_four_lower =====
section

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end
set_option linter.unusedVariables false

namespace Work.R1G



end Work.R1G
end
-- ===== merged: Submission.Work.R1G.HkNorm_const_mul =====
section

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

/-!
# Homogeneity of `HkNorm` in a scalar amplitude

For `c ≥ 0` the weighted `H^k` norm `HkNorm A k` is positively homogeneous of degree one:
`HkNorm A k (fun z θ => c * f z θ) = c * HkNorm A k f`.

Every operator entering the weighted `H^k` integrand (`pz`, `pth`, `Dz`, `Dth`, `DzIter`,
`DthIter`, `mixed`) is linear over the reals, so `HkIntegrand A k` is homogeneous of degree
two in the amplitude and hence so is `HkSq A k` (the Bochner integral is scalar homogeneous
*unconditionally*).  The square root then splits the factor `c²` into `|c| = c`.

No regularity hypothesis on `f` is needed: `deriv` is homogeneous for scalar multiplication
unconditionally (if `f` is not differentiable at a point and `c ≠ 0`, neither is `c * f`), and
the total Bochner integral is homogeneous without any integrability assumption.  In particular
the irrelevant region `z < 0` causes no trouble.
-/

noncomputable section

open scoped Real Topology
open MeasureTheory

namespace Work.R1G

set_option autoImplicit false

/-! ## Unconditional `deriv`-linearity -/

/-- `deriv` is scalar homogeneous **unconditionally**, unlike Mathlib's `deriv_const_mul`,
which needs differentiability: if `f` is not differentiable at `x` then neither is `c * f`
for `c ≠ 0`, so both sides are `0`. -/
private theorem deriv_const_mul_uncond (c x : ℝ) (f : ℝ → ℝ) :
    deriv (fun y => c * f y) x = c * deriv f x := by
  rcases eq_or_ne c 0 with h | h
  · subst h; simp
  · rcases em (DifferentiableAt ℝ f x) with hf | hf
    · exact deriv_const_mul c hf
    · have h2 : ¬ DifferentiableAt ℝ (fun y => c * f y) x := by
        intro hh
        apply hf
        have he : f = fun y => c⁻¹ * (c * f y) := by
          funext y; rw [← mul_assoc, inv_mul_cancel₀ h, one_mul]
        rw [he]
        exact hh.const_mul c⁻¹
      rw [deriv_zero_of_not_differentiableAt hf,
        deriv_zero_of_not_differentiableAt h2, mul_zero]

/-! ## Pointwise linearity of the differential operators -/

private theorem pz_const_mul_prv (c : ℝ) (f : ℝ → ℝ → ℝ) :
    Work.Spaces.pz (fun z θ => c * f z θ) = fun z θ => c * Work.Spaces.pz f z θ := by
  funext z θ
  simp only [Work.Spaces.pz]
  rw [deriv_const_mul_uncond]

private theorem Dz_const_mul_prv (c : ℝ) (g : ℝ → ℝ → ℝ) :
    Work.Spaces.Dz (fun z θ => c * g z θ) = fun z θ => c * Work.Spaces.Dz g z θ := by
  funext z θ
  simp only [Work.Spaces.Dz]
  rw [pz_const_mul_prv]
  ring

private theorem pth_const_mul_prv (c : ℝ) (f : ℝ → ℝ → ℝ) :
    Work.Spaces.pth (fun z θ => c * f z θ) = fun z θ => c * Work.Spaces.pth f z θ := by
  funext z θ
  simp only [Work.Spaces.pth]
  rw [deriv_const_mul_uncond]

private theorem Dth_const_mul_prv (c : ℝ) (g : ℝ → ℝ → ℝ) :
    Work.Spaces.Dth (fun z θ => c * g z θ) = fun z θ => c * Work.Spaces.Dth g z θ := by
  funext z θ
  simp only [Work.Spaces.Dth]
  rw [pth_const_mul_prv]
  ring

private theorem DzIter_const_mul_prv (i : ℕ) (c : ℝ) (f : ℝ → ℝ → ℝ) :
    Work.Spaces.DzIter i (fun z θ => c * f z θ)
      = fun z θ => c * Work.Spaces.DzIter i f z θ := by
  induction i with
  | zero => rfl
  | succ i ih => simp only [Work.Spaces.DzIter_succ, ih, Dz_const_mul_prv]

private theorem DthIter_const_mul_prv (i : ℕ) (c : ℝ) (f : ℝ → ℝ → ℝ) :
    Work.Spaces.DthIter i (fun z θ => c * f z θ)
      = fun z θ => c * Work.Spaces.DthIter i f z θ := by
  induction i with
  | zero => rfl
  | succ i ih => simp only [Work.Spaces.DthIter_succ, ih, Dth_const_mul_prv]

private theorem mixed_const_mul_prv (j i : ℕ) (c : ℝ) (f : ℝ → ℝ → ℝ) :
    Work.Spaces.mixed j i (fun z θ => c * f z θ)
      = fun z θ => c * Work.Spaces.mixed j i f z θ := by
  simp only [Work.Spaces.mixed, DthIter_const_mul_prv, DzIter_const_mul_prv]

/-! ## Homogeneity of the weighted integrand and of `HkSq` -/

/-- The weighted `H^k` integrand is homogeneous of degree two in the amplitude. -/
private theorem HkIntegrand_const_mul_prv (A : ℝ) (k : ℕ) (c : ℝ) (f : ℝ → ℝ → ℝ) :
    Work.Spaces.HkIntegrand A k (fun z θ => c * f z θ)
      = fun z θ => c ^ 2 * Work.Spaces.HkIntegrand A k f z θ := by
  funext z θ
  simp only [Work.Spaces.HkIntegrand, DzIter_const_mul_prv, mixed_const_mul_prv]
  have h1 : (∑ i ∈ Finset.range (k + 1),
        (c * Work.Spaces.DzIter i f z θ
          * (Work.Spaces.w z / (Real.sin (2 * θ)) ^ (Work.Spaces.eta / 2))) ^ 2)
      = c ^ 2 * ∑ i ∈ Finset.range (k + 1),
        (Work.Spaces.DzIter i f z θ
          * (Work.Spaces.w z / (Real.sin (2 * θ)) ^ (Work.Spaces.eta / 2))) ^ 2 := by
    rw [Finset.mul_sum]
    exact Finset.sum_congr rfl fun i _ => by ring
  have h2 : (∑ i ∈ Finset.range (k + 1), ∑ j ∈ Finset.range (k + 1),
        if 1 ≤ i ∧ i + j ≤ k
          then (c * Work.Spaces.mixed j i f z θ * Work.Spaces.Wt A z θ) ^ 2 else 0)
      = c ^ 2 * ∑ i ∈ Finset.range (k + 1), ∑ j ∈ Finset.range (k + 1),
        if 1 ≤ i ∧ i + j ≤ k
          then (Work.Spaces.mixed j i f z θ * Work.Spaces.Wt A z θ) ^ 2 else 0 := by
    rw [Finset.mul_sum]
    refine Finset.sum_congr rfl fun i _ => ?_
    rw [Finset.mul_sum]
    exact Finset.sum_congr rfl fun j _ => by split_ifs with h <;> ring
  rw [h1, h2, mul_add]

/-- `HkSq` is homogeneous of degree two in the amplitude.  Neither integral needs an
integrability hypothesis: `MeasureTheory.integral_const_mul` is unconditional. -/
private theorem HkSq_const_mul (A c : ℝ) (k : ℕ) (f : ℝ → ℝ → ℝ) :
    Work.Spaces.HkSq A k (fun z θ => c * f z θ) = c ^ 2 * Work.Spaces.HkSq A k f := by
  simp only [Work.Spaces.HkSq, HkIntegrand_const_mul_prv]
  simp only [MeasureTheory.integral_const_mul]

/-! ## The requested homogeneity of `HkNorm` -/

theorem HkNorm_const_mul (A c : ℝ) (hc : 0 ≤ c) (k : ℕ) (f : ℝ → ℝ → ℝ) :
    Work.Spaces.HkNorm A k (fun z θ => c * f z θ) = c * Work.Spaces.HkNorm A k f := by
  rw [Work.Spaces.HkNorm, Work.Spaces.HkNorm, HkSq_const_mul A c k f,
    Real.sqrt_mul (sq_nonneg c), Real.sqrt_sq hc]

end Work.R1G
end
end
-- ===== merged: Submission.Work.RPFresh.hasDerivAt_w2z_mul =====
section

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

namespace Work.RPFresh

/-- The derivative of the radial weight `w(z) = (1+z)²/z²`:
`w'(x) = -2(1+x)/x³` for `x ≠ 0`. -/
lemma hasDerivAt_w {x : ℝ} (hx : x ≠ 0) :
    HasDerivAt Work.Spaces.w (-(2 * (1 + x) / x ^ 3)) x := by
  have ha : HasDerivAt (fun z : ℝ => (1 + z) ^ 2) (2 * (1 + x)) x := by
    have h := ((hasDerivAt_const (x : ℝ) (1 : ℝ)).add (hasDerivAt_id x)).pow 2
    convert h using 1
    · ext z; simp
    · simp only [Pi.add_apply, id_eq]; ring
  have hb : HasDerivAt (fun z : ℝ => z ^ 2) (2 * x) x := by
    have h := (hasDerivAt_id x).pow 2
    convert h using 1
    · ext z; simp
    · simp only [id_eq]; ring
  exact (ha.div hb (by positivity)).congr_deriv (by field_simp; ring)

/-- `w(x)² * x` as a function of `x` has derivative `w(x)² * (x-3)/(1+x)`. -/
lemma hasDerivAt_w2_mul_id {x : ℝ} (hx : 0 < x) :
    HasDerivAt (fun z : ℝ => (Work.Spaces.w z) ^ 2 * z)
      ((Work.Spaces.w x) ^ 2 * ((x - 3) / (1 + x))) x := by
  have hxne : x ≠ 0 := ne_of_gt hx
  have hw : HasDerivAt Work.Spaces.w (-(2 * (1 + x) / x ^ 3)) x := hasDerivAt_w hxne
  have hw2 : HasDerivAt (fun z : ℝ => (Work.Spaces.w z) ^ 2)
      (2 * Work.Spaces.w x * (-(2 * (1 + x) / x ^ 3))) x := by
    have h := hw.pow 2
    refine h.congr_deriv ?_
    simp only [Nat.cast_ofNat]
    norm_num
  have hz : HasDerivAt (fun z : ℝ => z) 1 x := hasDerivAt_id x
  have h := hw2.mul hz
  refine h.congr_deriv ?_
  unfold Work.Spaces.w
  field_simp
  ring

theorem hasDerivAt_w2z_mul {f : ℝ → ℝ} {x f' : ℝ} (hx : 0 < x) (hf : HasDerivAt f f' x) :
    HasDerivAt (fun z : ℝ => (Work.Spaces.w z) ^ 2 * z * f z)
      ((Work.Spaces.w x) ^ 2 * (x * f' + ((x - 3) / (1 + x)) * f x)) x := by
  have hmain := hasDerivAt_w2_mul_id hx
  refine (hmain.mul hf).congr_deriv ?_
  ring_nf

end Work.RPFresh
end
-- ===== merged: Submission.Work.RPFresh.integral_sin_two_rpow_le =====
section

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

open scoped Real
open MeasureTheory Set intervalIntegral

namespace Work.RPFresh

/-- For `θ ∈ (0, π/2)`, the `η`-power of `sin(2t)` is integrable on `[0,θ]` against the
majorant `(2t)^η`, and the resulting integral is bounded by `2^η θ^{1+η}/(1+η)`.  This is
the elementary estimate used to control the `sin(2θ)^η` weight near the endpoints
`θ = 0, π/2`; note it only needs `sin x ≤ x` and the monotonicity of `x ↦ x^η` for `η > 0`. -/
theorem integral_sin_two_rpow_le {θ : ℝ} (hθ : θ ∈ Set.Ioo (0:ℝ) (Real.pi/2)) :
    (∫ t in (0:ℝ)..θ, (Real.sin (2*t))^(Work.Spaces.eta))
      ≤ 2^(Work.Spaces.eta) * θ^(1 + Work.Spaces.eta) / (1 + Work.Spaces.eta) := by
  have hη : 0 < Work.Spaces.eta := Work.Spaces.eta_pos
  have h0θ : (0:ℝ) ≤ θ := le_of_lt hθ.1
  -- Pointwise domination `sin(2t)^η ≤ (2t)^η` on `[0,θ]`, hence integral domination.
  have hcont1 : Continuous fun t : ℝ => (Real.sin (2*t))^(Work.Spaces.eta) :=
    (Real.continuous_sin.comp (continuous_const.mul continuous_id)).rpow_const
      (fun x => Or.inr hη.le)
  have hcont2 : Continuous fun t : ℝ => (2*t)^(Work.Spaces.eta) :=
    (continuous_const.mul continuous_id).rpow_const (fun x => Or.inr hη.le)
  have hmono : (∫ t in (0:ℝ)..θ, (Real.sin (2*t))^(Work.Spaces.eta))
      ≤ ∫ t in (0:ℝ)..θ, (2*t)^(Work.Spaces.eta) := by
    apply intervalIntegral.integral_mono_on h0θ (hcont1.intervalIntegrable _ _)
      (hcont2.intervalIntegrable _ _)
    intro x hx
    have hx0 : 0 ≤ x := hx.1
    have hs : Real.sin (2*x) ≤ 2*x := Real.sin_le (by linarith)
    have hsnn : 0 ≤ Real.sin (2*x) := by
      apply Real.sin_nonneg_of_nonneg_of_le_pi <;>
        linarith [hθ.2, Real.pi_pos, hx0, hx.2]
    exact Real.rpow_le_rpow hsnn hs hη.le
  -- Evaluate the majorant integral.
  have hstep : (∫ t in (0:ℝ)..θ, (2*t)^(Work.Spaces.eta))
      = 2^(Work.Spaces.eta) * ∫ t in (0:ℝ)..θ, t^(Work.Spaces.eta) := by
    rw [← intervalIntegral.integral_const_mul (2^(Work.Spaces.eta))
      (fun t => t^(Work.Spaces.eta))]
    apply intervalIntegral.integral_congr
    intro t ht
    have ht0 : 0 ≤ t := by
      have h := ht.1
      rw [min_eq_left h0θ] at h
      exact h
    exact Real.mul_rpow (by norm_num) ht0
  have hrpow : (∫ t in (0:ℝ)..θ, t^(Work.Spaces.eta))
      = θ^(Work.Spaces.eta + 1)/(Work.Spaces.eta + 1) := by
    rw [integral_rpow]
    · rw [Real.zero_rpow (by linarith)]
      ring
    · exact Or.inl (by linarith)
  calc (∫ t in (0:ℝ)..θ, (Real.sin (2*t))^(Work.Spaces.eta))
      ≤ ∫ t in (0:ℝ)..θ, (2*t)^(Work.Spaces.eta) := hmono
    _ = 2^(Work.Spaces.eta) * ∫ t in (0:ℝ)..θ, t^(Work.Spaces.eta) := hstep
    _ = 2^(Work.Spaces.eta) * (θ^(Work.Spaces.eta + 1)/(Work.Spaces.eta + 1)) := by
          rw [hrpow]
    _ = 2^(Work.Spaces.eta) * θ^(1 + Work.Spaces.eta) / (1 + Work.Spaces.eta) := by
          have h1 : (1:ℝ) + Work.Spaces.eta = Work.Spaces.eta + 1 := by ring
          rw [h1]; ring

end Work.RPFresh
end
-- ===== merged: Submission.Work.Spaces.CAux.integrableOn_GamK =====
section

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

namespace Work.Spaces.CAux

open MeasureTheory Set

/-- On `[0,π/2]` the product `Γ(θ)K(θ) = (sin θ · cos²θ)^{α/3} · 3 sin θ cos²θ` is a
continuous function of `θ`, because the base `sin θ · cos²θ` is continuous and
nonnegative there while the exponent `α/3` is nonnegative.  It is therefore
integrable on the compact interval `Iθ`. -/
theorem integrableOn_GamK (α : ℝ) (hα : 0 < α) :
    MeasureTheory.IntegrableOn (fun θ : ℝ => Work.Spaces.Gam α θ * Work.Spaces.K θ) Work.Spaces.Iθ := by
  have hα3 : (0 : ℝ) ≤ α / 3 := by linarith
  have hu : ContinuousOn (fun θ : ℝ => Real.sin θ * Real.cos θ ^ 2) Work.Spaces.Iθ :=
    (Real.continuous_sin.mul (Real.continuous_cos.pow 2)).continuousOn
  have h1 : ContinuousOn (fun θ : ℝ => (Real.sin θ * Real.cos θ ^ 2) ^ (α / 3)) Work.Spaces.Iθ :=
    hu.rpow_const (fun θ _ => Or.inr hα3)
  have hK : ContinuousOn (fun θ : ℝ => 3 * Real.sin θ * Real.cos θ ^ 2) Work.Spaces.Iθ :=
    ((continuous_const.mul Real.continuous_sin).mul (Real.continuous_cos.pow 2)).continuousOn
  have h2 : ContinuousOn
      (fun θ : ℝ => (Real.sin θ * Real.cos θ ^ 2) ^ (α / 3) * (3 * Real.sin θ * Real.cos θ ^ 2))
      Work.Spaces.Iθ :=
    h1.mul hK
  have heq : (fun θ : ℝ => Work.Spaces.Gam α θ * Work.Spaces.K θ)
      = fun θ : ℝ => (Real.sin θ * Real.cos θ ^ 2) ^ (α / 3) * (3 * Real.sin θ * Real.cos θ ^ 2) := by
    funext θ
    simp only [Work.Spaces.Gam, Work.Spaces.K]
  rw [heq]
  exact h2.integrableOn_Icc

end Work.Spaces.CAux
end
-- ===== merged: Submission.Work.Spaces.Gam_bounds =====
section

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

noncomputable section

open scoped Real Topology
open MeasureTheory Set Filter

namespace Work.Spaces

/-!
# Pointwise bounds for the angular weight `Γ(θ)`

`Γ(θ) = (sin θ cos²θ)^{α/3}`.  For `θ ∈ [0,π/2]` the base `u = sin θ cos²θ` lies in
`[0,1]` and the exponent `α/3` is nonnegative, so `Γ` takes values in `[0,1]`.
-/

/-- On the angular interval `Iθ = [0,π/2]`, the base `sin θ cos²θ` lies in `[0,1]`. -/
theorem sin_mul_cos_sq_mem_Icc (θ : ℝ) (hθ : θ ∈ Iθ) :
    0 ≤ Real.sin θ * Real.cos θ ^ 2 ∧ Real.sin θ * Real.cos θ ^ 2 ≤ 1 := by
  have hs0 : 0 ≤ Real.sin θ :=
    Real.sin_nonneg_of_mem_Icc ⟨hθ.1, by linarith [hθ.2, Real.pi_pos]⟩
  refine ⟨mul_nonneg hs0 (by positivity), ?_⟩
  have hs1 : Real.sin θ ≤ 1 := Real.sin_le_one θ
  have hc1 : Real.cos θ ^ 2 ≤ 1 := by
    have h := sq_le_sq' (Real.neg_one_le_cos θ) (Real.cos_le_one θ)
    simpa using h
  have hc0 : (0 : ℝ) ≤ Real.cos θ ^ 2 := by positivity
  simpa using mul_le_mul hs1 hc1 hc0 (by norm_num : (0 : ℝ) ≤ 1)

theorem Gam_bounds (α θ : ℝ) (hα : 0 < α) (hθ : θ ∈ Work.Spaces.Iθ) :
    0 ≤ Work.Spaces.Gam α θ ∧ Work.Spaces.Gam α θ ≤ 1 := by
  have ht0 : 0 ≤ Real.sin θ * Real.cos θ ^ 2 :=
    (sin_mul_cos_sq_mem_Icc θ hθ).1
  have ht1 : Real.sin θ * Real.cos θ ^ 2 ≤ 1 :=
    (sin_mul_cos_sq_mem_Icc θ hθ).2
  have hα3 : 0 ≤ α / 3 := by linarith
  exact ⟨by rw [Gam]; exact Real.rpow_nonneg ht0 _,
    by rw [Gam]; exact Real.rpow_le_one ht0 ht1 hα3⟩

end Work.Spaces
end
end
-- ===== merged: Submission.Work.Spaces.Gam_mul_weight_le =====
section

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

/-!
# The angular weight bound `α Γ(θ) sin(2θ)^{-α/5} / (α + sin(2θ)) ≤ 1`

This is the elementary pointwise estimate on the angular weight
`sin(2θ)^{-α/5} / (α + sin(2θ))` multiplying `Γ` in the `𝒲^{l,∞}`-norms of

T. M. Elgindi, *Finite-time singularity formation for `C^{1,α}` solutions to the
incompressible Euler equations on `ℝ³`*, Annals of Math. 194 (3) 2021.

## Mathematics

Write `s = sin θ`, `c = cos θ` and `A = s c²`, so that on `Iθ = [0, π/2]`
both are nonnegative, `Γ(θ) = A ^ (α/3)` and `sin(2θ) = 2 s c`.

The key pointwise inequality is `A ^ 5 ≤ (sin 2θ) ^ 3`: indeed
`A ^ 5 = (s² c⁷) · (s³ c³) ≤ s³ c³ ≤ 8 s³ c³ = (2 s c) ^ 3`, because
`0 ≤ s, c ≤ 1`.  Raising to the power `α/15 ≥ 0` gives `A ^ (α/3) ≤ (sin 2θ) ^ (α/5)`,
i.e. `Γ(θ) ≤ sin(2θ) ^ (α/5)`.  Multiplying by the nonnegative factor
`sin(2θ)^{-α/5}` and using `x ^ (α/5) * x ^ (-(α/5)) ≤ 1` (equality when
`x > 0`, and `0` when `x = 0`) yields `Γ(θ) sin(2θ)^{-α/5} ≤ 1`, hence
`α Γ(θ) sin(2θ)^{-α/5} ≤ α ≤ α + sin(2θ)`.  Dividing by the positive
denominator `α + sin(2θ)` gives the claim.
-/
open scoped Real

namespace Work.Spaces

theorem Gam_mul_weight_le (α θ : ℝ) (hα : 0 < α) (hθ : θ ∈ Work.Spaces.Iθ) :
    α * Work.Spaces.Gam α θ * (Real.sin (2 * θ)) ^ (-(α / 5)) / (α + Real.sin (2 * θ)) ≤ 1 := by
  obtain ⟨hθ0, hθ1⟩ := hθ
  -- Basic sign/bound facts for `sin θ` and `cos θ` on `Iθ`.
  have hs0 : 0 ≤ Real.sin θ :=
    Real.sin_nonneg_of_mem_Icc ⟨by linarith [Real.pi_pos], by linarith⟩
  have hc0 : 0 ≤ Real.cos θ :=
    Real.cos_nonneg_of_mem_Icc ⟨by linarith [Real.pi_pos], by linarith⟩
  have hs1 : Real.sin θ ≤ 1 := Real.sin_le_one θ
  have hc1 : Real.cos θ ≤ 1 := Real.cos_le_one θ
  -- The angular factor `A = sin θ · cos²θ`, so that `Γ(θ) = A ^ (α/3)`.
  set A : ℝ := Real.sin θ * Real.cos θ ^ 2 with hA
  have hA0 : 0 ≤ A := by rw [hA]; positivity
  have hGamA : Work.Spaces.Gam α θ = A ^ (α / 3) := by
    simp only [Work.Spaces.Gam]
    rw [hA]
  have he0 : 0 ≤ Real.sin (2 * θ) := by
    rw [Real.sin_two_mul]; positivity
  -- The numerical core: `A ^ 5 ≤ sin(2θ) ^ 3`.
  have hA5r : A ^ (5:ℝ) ≤ (Real.sin (2 * θ)) ^ (3:ℝ) := by
    have hm : A ^ 5 ≤ (Real.sin (2 * θ)) ^ 3 := by
      rw [hA, Real.sin_two_mul]
      have h1 : (Real.sin θ) ^ 2 * (Real.cos θ) ^ 7 ≤ 1 := by
        have a : (Real.sin θ) ^ 2 ≤ 1 := pow_le_one₀ (n := 2) hs0 hs1
        have b : (Real.cos θ) ^ 7 ≤ 1 := pow_le_one₀ (n := 7) hc0 hc1
        nlinarith [mul_le_mul a b (pow_nonneg hc0 7) (by norm_num : (0:ℝ) ≤ 1)]
      have hQ : 0 ≤ (Real.sin θ) ^ 3 * (Real.cos θ) ^ 3 := by positivity
      have step : ((Real.sin θ) ^ 2 * (Real.cos θ) ^ 7) * ((Real.sin θ) ^ 3 * (Real.cos θ) ^ 3)
          ≤ 1 * ((Real.sin θ) ^ 3 * (Real.cos θ) ^ 3) :=
        mul_le_mul_of_nonneg_right h1 hQ
      nlinarith [step, hQ, sq_nonneg (Real.sin θ * Real.cos θ)]
    simpa using hm
  -- Raising to the (nonnegative) power `α/15`: `Γ(θ) ≤ sin(2θ) ^ (α/5)`.
  have hGam : Work.Spaces.Gam α θ ≤ (Real.sin (2 * θ)) ^ (α / 5) := by
    have h1 : A ^ (α / 3) = (A ^ (5:ℝ)) ^ (α / 15) := by
      rw [← Real.rpow_mul hA0 5 (α / 15), show (5:ℝ) * (α / 15) = α / 3 by ring]
    have h2 : ((Real.sin (2 * θ)) ^ (3:ℝ)) ^ (α / 15) = (Real.sin (2 * θ)) ^ (α / 5) := by
      rw [← Real.rpow_mul he0 3 (α / 15), show (3:ℝ) * (α / 15) = α / 5 by ring]
    have h3 : (A ^ (5:ℝ)) ^ (α / 15) ≤ ((Real.sin (2 * θ)) ^ (3:ℝ)) ^ (α / 15) :=
      Real.rpow_le_rpow (Real.rpow_nonneg hA0 5) hA5r (by linarith)
    rw [← h1, h2] at h3
    rwa [hGamA]
  -- `Γ(θ) · sin(2θ)^{-α/5} ≤ 1`.
  have hge : Work.Spaces.Gam α θ * (Real.sin (2 * θ)) ^ (-(α / 5)) ≤ 1 := by
    have h1 : Work.Spaces.Gam α θ * (Real.sin (2 * θ)) ^ (-(α / 5))
        ≤ (Real.sin (2 * θ)) ^ (α / 5) * (Real.sin (2 * θ)) ^ (-(α / 5)) :=
      mul_le_mul_of_nonneg_right hGam (Real.rpow_nonneg he0 _)
    have h2 : (Real.sin (2 * θ)) ^ (α / 5) * (Real.sin (2 * θ)) ^ (-(α / 5)) ≤ 1 := by
      rcases eq_or_lt_of_le he0 with h | h
      · rw [← h, Real.zero_rpow (by linarith : α / 5 ≠ 0),
            Real.zero_rpow (by linarith : -(α / 5) ≠ 0)]
        norm_num
      · rw [← Real.rpow_add h (α / 5) (-(α / 5)), show α / 5 + -(α / 5) = 0 by ring,
            Real.rpow_zero]
    linarith
  -- Multiply by `α` and divide by `α + sin(2θ) > 0`.
  have hnum : α * Work.Spaces.Gam α θ * (Real.sin (2 * θ)) ^ (-(α / 5)) ≤ α := by
    have h := mul_le_mul_of_nonneg_left hge (le_of_lt hα)
    rw [mul_one] at h
    linarith [h]
  have hden : 0 < α + Real.sin (2 * θ) := by linarith
  have hfin : α / (α + Real.sin (2 * θ)) ≤ 1 := by
    rw [div_le_one hden]; linarith
  calc α * Work.Spaces.Gam α θ * (Real.sin (2 * θ)) ^ (-(α / 5)) / (α + Real.sin (2 * θ))
      ≤ α / (α + Real.sin (2 * θ)) := div_le_div_of_nonneg_right hnum (le_of_lt hden)
    _ ≤ 1 := hfin

end Work.Spaces
end
-- ===== merged: Submission.Work.Spaces.GoodTermSqBound =====
section

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

open scoped Real Topology
open MeasureTheory Set Filter

namespace Work.Spaces


end Work.Spaces
end
-- ===== merged: Submission.Work.Spaces.H_le_Wt =====
section

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

set_option linter.unusedVariables false

namespace Work.Spaces

/-- The `H^0`-weight `w/ sin(2θ)^{η/2}` is dominated by the `W^{0,∞}`-weight
`W = w · w_θ = w · sin(2θ)^{-γ/2}`: since `η = 99/100 < 1 < γ = 1 + α/10` and
`0 ≤ sin(2θ) ≤ 1` on `[0,π/2]`, the exponent `-η/2` is the larger one, and a base
in `[0,1]` is smaller with the larger exponent. -/
theorem H_le_Wt (α : ℝ) (hα : 0 < α) (z θ : ℝ) (hz : z ∈ Work.Spaces.Iz)
    (hθ : θ ∈ Work.Spaces.Iθ) :
    (Work.Spaces.w z / (Real.sin (2 * θ)) ^ (Work.Spaces.eta / 2)) ^ 2
      ≤ (Work.Spaces.Wt α z θ) ^ 2 := by
  rw [Wt, wTheta]
  -- `w z ≥ 0` always, and `s := sin(2θ) ∈ [0,1]` for `θ ∈ [0,π/2]`.
  have ha : 0 ≤ w z := by rw [w]; exact div_nonneg (sq_nonneg _) (sq_nonneg _)
  have hs0 : 0 ≤ Real.sin (2 * θ) := by
    apply Real.sin_nonneg_of_nonneg_of_le_pi
    · linarith [hθ.1]
    · linarith [hθ.2, Real.pi_pos]
  have hs1 : Real.sin (2 * θ) ≤ 1 := Real.sin_le_one _
  -- Since `-η/2 ≥ -γ/2` and `sin(2θ) ∈ [0,1]`, we have `sin(2θ)^{-η/2} ≤ sin(2θ)^{-γ/2}`.
  have hkey : 1 / (Real.sin (2 * θ)) ^ (eta / 2) ≤ (Real.sin (2 * θ)) ^ (-(gam α / 2)) := by
    have h1 : 1 / (Real.sin (2 * θ)) ^ (eta / 2) = (Real.sin (2 * θ)) ^ (-(eta / 2)) := by
      rw [one_div, ← Real.rpow_neg hs0]
    rw [h1]
    apply Real.rpow_le_rpow_of_exponent_ge_of_imp hs0 hs1
    · have hgam : eta ≤ gam α := by linarith [one_lt_gam hα, eta_lt_one]
      linarith
    · intro _ hy
      exact absurd hy (by norm_num [eta])
  -- Multiply by `w z ≥ 0` and square (both sides are nonnegative).
  calc (w z / (Real.sin (2 * θ)) ^ (eta / 2)) ^ 2
      = (w z * (1 / (Real.sin (2 * θ)) ^ (eta / 2))) ^ 2 := by rw [div_eq_mul_one_div]
    _ ≤ (w z * (Real.sin (2 * θ)) ^ (-(gam α / 2))) ^ 2 := by
        apply pow_le_pow_left₀ _ _ 2
        · exact mul_nonneg ha (div_nonneg zero_le_one (Real.rpow_nonneg hs0 _))
        · exact mul_le_mul_of_nonneg_left hkey ha

end Work.Spaces
end
-- ===== merged: Submission.Work.Spaces.HardyZ =====
section

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

noncomputable section

open scoped Real Topology Interval
open MeasureTheory Set Filter

namespace Work.Spaces

set_option autoImplicit false

/-! ## Smoothness of the `θ`-slice of a `SmoothNbhd` function -/

/-- The `θ`-slice `z ↦ g z θ` of a function smooth on a neighbourhood of the closed
quadrant is smooth on `(-1,∞)`. -/
theorem hardyZ_contDiffOn_slice (g : ℝ → ℝ → ℝ) (hsm : SmoothNbhd g) {θ : ℝ} (hθ : θ ∈ Iθ) :
    ContDiffOn ℝ ⊤ (fun z => g z θ) (Set.Ioi (-1)) := by
  have hθ' : θ ∈ Set.Ioo (-1) (π/2 + 1) := ⟨by linarith [hθ.1], by linarith [hθ.2]⟩
  have hmap : Set.MapsTo (fun z : ℝ => (z, θ)) (Set.Ioi (-1))
      (Set.Ioi (-1) ×ˢ Set.Ioo (-1) (π/2 + 1)) := fun z hz => ⟨hz, hθ'⟩
  exact hsm.comp (contDiffOn_id.prodMk contDiffOn_const) hmap

/-- The slice `z ↦ g z θ` has derivative `pz g z θ` on `(-1,∞)`. -/
theorem hardyZ_hasDerivAt_slice (g : ℝ → ℝ → ℝ) (hsm : SmoothNbhd g) {θ : ℝ} (hθ : θ ∈ Iθ)
    {z : ℝ} (hz : z ∈ Set.Ioi (-1)) : HasDerivAt (fun z => g z θ) (pz g z θ) z := by
  have hd : DifferentiableOn ℝ (fun z => g z θ) (Set.Ioi (-1)) :=
    (hardyZ_contDiffOn_slice g hsm hθ).differentiableOn (by simp)
  exact hd.hasDerivAt (isOpen_Ioi.mem_nhds hz)

/-- The derivative `z ↦ pz g z θ` of the slice is continuous on `(-1,∞)`. -/
theorem hardyZ_continuousOn_pz_slice (g : ℝ → ℝ → ℝ) (hsm : SmoothNbhd g) {θ : ℝ}
    (hθ : θ ∈ Iθ) : ContinuousOn (fun z => pz g z θ) (Set.Ioi (-1)) := by
  have hcd := (hardyZ_contDiffOn_slice g hsm hθ).continuousOn_derivWithin
    (isOpen_Ioi.uniqueDiffOn) le_top
  have : ContinuousOn (fun z => deriv (fun z => g z θ) z) (Set.Ioi (-1)) :=
    hcd.congr (fun x hx => (derivWithin_of_isOpen isOpen_Ioi hx).symm)
  simpa [pz] using this

/-- Elementary membership helper. -/
theorem hardyZ_mem_Ioi (a x : ℝ) (ha : 0 ≤ a) (hx : a ≤ x) : x ∈ Set.Ioi (-1) := by
  simp only [Set.mem_Ioi]; linarith

/-- The fundamental theorem of calculus for the `θ`-slice of a `SmoothNbhd` function:
`∫_a^b ∂_z g(s,θ) ds = g(b,θ) - g(a,θ)`. -/
theorem hardyZ_integral_pz_eq_sub (g : ℝ → ℝ → ℝ) (hsm : SmoothNbhd g) {θ : ℝ} (hθ : θ ∈ Iθ)
    {a b : ℝ} (ha : 0 ≤ a) (hab : a ≤ b) :
    ∫ s in a..b, pz g s θ = g b θ - g a θ := by
  have hderiv : ∀ x ∈ Set.Ioo a b, HasDerivAt (fun z => g z θ) (pz g x θ) x :=
    fun x hx => hardyZ_hasDerivAt_slice g hsm hθ (hardyZ_mem_Ioi a x ha hx.1.le)
  have hcont : ContinuousOn (fun z => g z θ) (Set.Icc a b) :=
    (hardyZ_contDiffOn_slice g hsm hθ).continuousOn.mono
      (fun x hx => hardyZ_mem_Ioi a x ha hx.1)
  have hint : IntervalIntegrable (fun s => pz g s θ) volume a b := by
    refine (hardyZ_continuousOn_pz_slice g hsm hθ).mono (fun x hx => ?_) |>.intervalIntegrable
    rw [Set.uIcc_of_le hab] at hx
    exact hardyZ_mem_Ioi a x ha hx.1
  exact intervalIntegral.integral_eq_sub_of_hasDerivAt_of_le hab hcont hderiv hint

/-! ## Two elementary real-variable lemmas -/

/-- Cauchy–Schwarz (Bunyakovsky) for the interval integral. -/
theorem hardyZ_interval_integral_mul_le_sqrt (a b : ℝ) (hab : a ≤ b) {f g : ℝ → ℝ}
    (hf : ContinuousOn f (Set.uIcc a b)) (hg : ContinuousOn g (Set.uIcc a b)) :
    |∫ x in a..b, f x * g x| ≤
      Real.sqrt (∫ x in a..b, f x ^ 2) * Real.sqrt (∫ x in a..b, g x ^ 2) := by
  have hfI : ContinuousOn f (Set.Icc a b) := by simpa [Set.uIcc_of_le hab] using hf
  have hgI : ContinuousOn g (Set.Icc a b) := by simpa [Set.uIcc_of_le hab] using hg
  have hIoc : MeasurableSet (Set.Ioc a b) := measurableSet_Ioc
  have hsub : Set.Ioc a b ⊆ Set.Icc a b := Set.Ioc_subset_Icc_self
  have h1 : |∫ x in a..b, f x * g x| ≤ ∫ x in a..b, |f x| * |g x| := by
    have h := intervalIntegral.norm_integral_le_integral_norm (μ := volume) hab
      (f := fun x => f x * g x)
    simpa [Real.norm_eq_abs, abs_mul] using h
  have h2 : ∫ x in a..b, |f x| * |g x| = ∫ x in Set.Ioc a b, |f x| * |g x| :=
    intervalIntegral.integral_of_le hab
  have hmf : AEStronglyMeasurable (fun x => |f x|) (volume.restrict (Set.Ioc a b)) :=
    (hfI.abs.mono hsub).aestronglyMeasurable hIoc
  have hmg : AEStronglyMeasurable (fun x => |g x|) (volume.restrict (Set.Ioc a b)) :=
    (hgI.abs.mono hsub).aestronglyMeasurable hIoc
  have hfi : IntegrableOn (fun x => |f x| ^ 2) (Set.Ioc a b) :=
    ((hfI.abs.pow 2).integrableOn_compact isCompact_Icc).mono_set hsub
  have hgi : IntegrableOn (fun x => |g x| ^ 2) (Set.Ioc a b) :=
    ((hgI.abs.pow 2).integrableOn_compact isCompact_Icc).mono_set hsub
  have hLf : MemLp (fun x => |f x|) (ENNReal.ofReal 2) (volume.restrict (Set.Ioc a b)) := by
    rw [show ENNReal.ofReal (2:ℝ) = 2 by norm_num]
    exact (memLp_two_iff_integrable_sq hmf).mpr hfi
  have hLg : MemLp (fun x => |g x|) (ENNReal.ofReal 2) (volume.restrict (Set.Ioc a b)) := by
    rw [show ENNReal.ofReal (2:ℝ) = 2 by norm_num]
    exact (memLp_two_iff_integrable_sq hmg).mpr hgi
  have hH := integral_mul_le_Lp_mul_Lq_of_nonneg (μ := volume.restrict (Set.Ioc a b))
    (p := 2) (q := 2) (by norm_num [Real.holderConjugate_iff])
    (Filter.Eventually.of_forall fun x => abs_nonneg (f x))
    (Filter.Eventually.of_forall fun x => abs_nonneg (g x)) hLf hLg
  have h3f : ∫ x in Set.Ioc a b, |f x| ^ 2 = ∫ x in a..b, f x ^ 2 := by
    rw [intervalIntegral.integral_of_le hab]
    exact setIntegral_congr_fun hIoc (fun x _ => sq_abs (f x))
  have h3g : ∫ x in Set.Ioc a b, |g x| ^ 2 = ∫ x in a..b, g x ^ 2 := by
    rw [intervalIntegral.integral_of_le hab]
    exact setIntegral_congr_fun hIoc (fun x _ => sq_abs (g x))
  calc |∫ x in a..b, f x * g x| ≤ ∫ x in a..b, |f x| * |g x| := h1
    _ = ∫ x in Set.Ioc a b, |f x| * |g x| := h2
    _ ≤ (∫ x in Set.Ioc a b, |f x| ^ 2) ^ (1 / 2 : ℝ) *
          (∫ x in Set.Ioc a b, |g x| ^ 2) ^ (1 / 2 : ℝ) := hH
    _ = Real.sqrt (∫ x in Set.Ioc a b, |f x| ^ 2) *
          Real.sqrt (∫ x in Set.Ioc a b, |g x| ^ 2) := by
        simp only [Real.sqrt_eq_rpow, Real.rpow_two]
    _ = Real.sqrt (∫ x in a..b, f x ^ 2) * Real.sqrt (∫ x in a..b, g x ^ 2) := by
        rw [h3f, h3g]

/-- The weight `ψ(s) = s/(1+s)²` has interval integral of its square at most `1`. -/
theorem hardyZ_integral_psi_sq_le_one {a b : ℝ} (ha : 0 ≤ a) (hab : a ≤ b) :
    ∫ s in a..b, (s / (1 + s) ^ 2) ^ 2 ≤ 1 := by
  have hpt : ∀ x ∈ Set.Icc a b, (x / (1 + x) ^ 2) ^ 2 ≤ 1 / (1 + x) ^ 2 := by
    intro x hx
    have hx0 : 0 ≤ x := le_trans ha hx.1
    have h2 : (0:ℝ) < (1 + x) ^ 2 := by positivity
    rw [div_pow, div_le_div_iff₀ (by positivity) h2]
    have hsq : x ^ 2 ≤ (1 + x) ^ 2 := by nlinarith
    calc x ^ 2 * (1 + x) ^ 2 ≤ (1 + x) ^ 2 * (1 + x) ^ 2 :=
          mul_le_mul_of_nonneg_right hsq h2.le
      _ = 1 * ((1 + x) ^ 2) ^ 2 := by ring
  have hcf : ContinuousOn (fun s : ℝ => (s / (1 + s) ^ 2) ^ 2) (Set.Icc a b) := by
    apply ContinuousOn.pow
    apply ContinuousOn.div
    · exact continuousOn_id
    · exact (continuousOn_const.add continuousOn_id).pow 2
    · intro x hx
      have hx0 : 0 ≤ x := le_trans ha hx.1
      positivity
  have hcg : ContinuousOn (fun s : ℝ => 1 / (1 + s) ^ 2) (Set.Icc a b) := by
    apply ContinuousOn.div
    · exact continuousOn_const
    · exact (continuousOn_const.add continuousOn_id).pow 2
    · intro x hx
      have hx0 : 0 ≤ x := le_trans ha hx.1
      positivity
  have hif : IntervalIntegrable (fun s : ℝ => (s / (1 + s) ^ 2) ^ 2) volume a b := by
    apply ContinuousOn.intervalIntegrable
    rwa [Set.uIcc_of_le hab]
  have hig : IntervalIntegrable (fun s : ℝ => 1 / (1 + s) ^ 2) volume a b := by
    apply ContinuousOn.intervalIntegrable
    rwa [Set.uIcc_of_le hab]
  have hmono : ∫ s in a..b, (s / (1 + s) ^ 2) ^ 2 ≤ ∫ s in a..b, 1 / (1 + s) ^ 2 :=
    intervalIntegral.integral_mono_on hab hif hig hpt
  have hval : ∫ s in a..b, 1 / (1 + s) ^ 2 = (1 + a)⁻¹ - (1 + b)⁻¹ := by
    have hderiv : ∀ x ∈ Set.Ioo a b,
        HasDerivAt (fun s : ℝ => -(1 + s)⁻¹) (1 / (1 + x) ^ 2) x := by
      intro x hx
      have hx0 : 0 ≤ x := le_trans ha hx.1.le
      have hx1 : 0 < 1 + x := by linarith
      have h2 := ((hasDerivAt_id x).const_add (1:ℝ)).inv (ne_of_gt hx1)
      have h3 := h2.neg
      have hfun : (fun s : ℝ => -(1 + s)⁻¹) = -(fun x => 1 + id x)⁻¹ := rfl
      rw [hfun]
      convert h3 using 1
      simp only [id_eq]
      ring
    have hcont : ContinuousOn (fun s : ℝ => -(1 + s)⁻¹) (Set.Icc a b) := by
      apply ContinuousOn.neg
      apply ContinuousOn.inv₀
      · exact continuousOn_const.add continuousOn_id
      · intro x hx
        have hx0 : 0 ≤ x := le_trans ha hx.1
        linarith
    rw [intervalIntegral.integral_eq_sub_of_hasDerivAt_of_le hab hcont hderiv hig]
    ring
  calc ∫ s in a..b, (s / (1 + s) ^ 2) ^ 2 ≤ ∫ s in a..b, 1 / (1 + s) ^ 2 := hmono
    _ = (1 + a)⁻¹ - (1 + b)⁻¹ := hval
    _ ≤ (1 + a)⁻¹ := by
        have : 0 ≤ (1 + b)⁻¹ := by
          rw [inv_nonneg]; linarith
        linarith
    _ ≤ 1 := inv_le_one_of_one_le₀ (by linarith)

/-- Monotonicity of the set integral for `[a,b] ⊆ [0,∞)`. -/
theorem hardyZ_integral_Ioc_le_integral_Iz {f : ℝ → ℝ} {a b : ℝ} (ha : 0 ≤ a) (hab : a ≤ b)
    (hint : IntegrableOn f Iz) (h0 : ∀ x ∈ Iz, 0 ≤ f x) :
    (∫ x in a..b, f x) ≤ ∫ x in Iz, f x := by
  rw [intervalIntegral.integral_of_le hab]
  have h_ae : 0 ≤ᵐ[volume.restrict Iz] f := by
    filter_upwards [MeasureTheory.ae_restrict_mem measurableSet_Ici] with x hx
    exact h0 x hx
  refine setIntegral_mono_set hint h_ae ?_
  exact Filter.Eventually.of_forall (fun x hx => le_trans ha hx.1.le)

/-- The algebraic identity behind the weighted Cauchy–Schwarz step:
`(D_z g · w)(s) · ψ(s) = ∂_s g(s,θ)` for `s > 0`, where `ψ(s) = s/(1+s)²`. -/
theorem hardyZ_mul_w_mul_psi (g : ℝ → ℝ → ℝ) {θ s : ℝ} (hs : 0 < s) :
    (Dz g s θ * w s) * (s / (1 + s) ^ 2) = pz g s θ := by
  have h1 : (1 + s) ≠ 0 := ne_of_gt (by linarith)
  simp only [Dz, w]
  field_simp

/-! ## The Hardy inequality -/

theorem HardyZ (g : ℝ → ℝ → ℝ) (θ : ℝ) (hsm : Work.Spaces.SmoothNbhd g)
    (hθ : θ ∈ Work.Spaces.Iθ) (hdec : Filter.Tendsto (fun z => g z θ) Filter.atTop (nhds 0))
    (hint : MeasureTheory.IntegrableOn
      (fun z => (Work.Spaces.Dz g z θ) ^ 2 * (Work.Spaces.w z) ^ 2) Work.Spaces.Iz) :
    ∀ z ∈ Work.Spaces.Iz, (g z θ) ^ 2 ≤
      ∫ s in Work.Spaces.Iz, (Work.Spaces.Dz g s θ) ^ 2 * (Work.Spaces.w s) ^ 2 := by
  set P : ℝ := ∫ s in Iz, (Dz g s θ) ^ 2 * (w s) ^ 2 with hPdef
  have hPnn : 0 ≤ P := by
    rw [hPdef]
    exact integral_nonneg fun s => mul_nonneg (sq_nonneg _) (sq_nonneg _)
  have hmain : ∀ z, 0 ≤ z → 0 < z → (g z θ) ^ 2 ≤ P := by
    intro z hz hzpos
    have hkey : ∀ B, z ≤ B → |g z θ| ≤ |g B θ| + Real.sqrt P := by
      intro B hzB
      have hFTC : ∫ s in z..B, pz g s θ = g B θ - g z θ :=
        hardyZ_integral_pz_eq_sub g hsm hθ hz hzB
      have hpzc : ContinuousOn (fun s => pz g s θ) (Set.Icc z B) :=
        (hardyZ_continuousOn_pz_slice g hsm hθ).mono
          (fun x hx => hardyZ_mem_Ioi z x hz hx.1)
      have hwc : ContinuousOn w (Set.Icc z B) := by
        unfold w
        apply ContinuousOn.div
        · exact (continuousOn_const.add continuousOn_id).pow 2
        · exact continuousOn_id.pow 2
        · intro x hx
          have hx0 : 0 < x := lt_of_lt_of_le hzpos hx.1
          positivity
      have hcontA : ContinuousOn (fun s => Dz g s θ * w s) (Set.uIcc z B) := by
        rw [Set.uIcc_of_le hzB]
        unfold Dz
        exact (continuousOn_id.mul hpzc).mul hwc
      have hcontψ : ContinuousOn (fun s => s / (1 + s) ^ 2) (Set.uIcc z B) := by
        rw [Set.uIcc_of_le hzB]
        apply ContinuousOn.div
        · exact continuousOn_id
        · exact (continuousOn_const.add continuousOn_id).pow 2
        · intro x hx
          have hx0 : 0 < x := lt_of_lt_of_le hzpos hx.1
          positivity
      have hcs := hardyZ_interval_integral_mul_le_sqrt z B hzB hcontA hcontψ
      have hcongr : ∫ x in z..B, (Dz g x θ * w x) * (x / (1 + x) ^ 2)
          = ∫ x in z..B, pz g x θ := by
        apply intervalIntegral.integral_congr
        intro x hx
        rw [Set.uIcc_of_le hzB] at hx
        exact hardyZ_mul_w_mul_psi g (lt_of_lt_of_le hzpos hx.1)
      have hA2le : ∫ x in z..B, (Dz g x θ * w x) ^ 2 ≤ P := by
        have h1 : ∫ x in z..B, (Dz g x θ * w x) ^ 2
            = ∫ x in z..B, (Dz g x θ) ^ 2 * (w x) ^ 2 := by
          apply intervalIntegral.integral_congr
          intro x _
          ring
        rw [h1, hPdef]
        exact hardyZ_integral_Ioc_le_integral_Iz hz hzB hint
          (fun s _ => mul_nonneg (sq_nonneg _) (sq_nonneg _))
      have hψle : ∫ x in z..B, (x / (1 + x) ^ 2) ^ 2 ≤ 1 :=
        hardyZ_integral_psi_sq_le_one hz hzB
      have hchain : |∫ x in z..B, pz g x θ| ≤ Real.sqrt P := by
        rw [← hcongr]
        calc |∫ x in z..B, (Dz g x θ * w x) * (x / (1 + x) ^ 2)|
            ≤ Real.sqrt (∫ x in z..B, (Dz g x θ * w x) ^ 2) *
                Real.sqrt (∫ x in z..B, (x / (1 + x) ^ 2) ^ 2) := hcs
          _ ≤ Real.sqrt P * Real.sqrt 1 := by
              exact mul_le_mul (Real.sqrt_le_sqrt hA2le) (Real.sqrt_le_sqrt hψle)
                (Real.sqrt_nonneg _) (Real.sqrt_nonneg _)
          _ = Real.sqrt P := by rw [Real.sqrt_one, mul_one]
      have hchain' : |g B θ - g z θ| ≤ Real.sqrt P := by
        rw [← hFTC]
        exact hchain
      have hsplit : g z θ = g B θ - (g B θ - g z θ) := by ring
      calc |g z θ| = |g B θ - (g B θ - g z θ)| := congrArg abs hsplit
        _ ≤ |g B θ| + |g B θ - g z θ| := abs_sub _ _
        _ ≤ |g B θ| + Real.sqrt P := by linarith [hchain']
    have hlim : Filter.Tendsto (fun B => |g B θ| + Real.sqrt P) Filter.atTop
        (nhds (Real.sqrt P)) := by
      have habs : Filter.Tendsto (fun B => |g B θ|) Filter.atTop (nhds 0) := by
        simpa using hdec.abs
      simpa using habs.add_const (Real.sqrt P)
    have hev : ∀ᶠ B in Filter.atTop, |g z θ| ≤ |g B θ| + Real.sqrt P :=
      (eventually_ge_atTop z).mono fun B hB => hkey B hB
    have hle : |g z θ| ≤ Real.sqrt P := ge_of_tendsto hlim hev
    calc (g z θ) ^ 2 = |g z θ| ^ 2 := (sq_abs _).symm
      _ ≤ (Real.sqrt P) ^ 2 := by
          nlinarith [hle, abs_nonneg (g z θ), Real.sqrt_nonneg P]
      _ = P := Real.sq_sqrt hPnn
  intro z hz
  have hz0 : 0 ≤ z := hz
  rcases lt_or_eq_of_le hz0 with hlt | hzero
  · exact hmain z hz0 hlt
  · subst hzero
    have hcont0 : ContinuousAt (fun z => g z θ) 0 :=
      (hardyZ_contDiffOn_slice g hsm hθ).continuousOn.continuousAt
        (isOpen_Ioi.mem_nhds (by simp))
    have hlim2 : Filter.Tendsto (fun z => (g z θ) ^ 2) (𝓝[>] (0:ℝ)) (nhds ((g 0 θ) ^ 2)) := by
      have h := (hcont0.tendsto.mono_left
        (nhdsWithin_le_nhds (s := Set.Ioi (0:ℝ)))).pow 2
      simpa using h
    refine le_of_tendsto hlim2 ?_
    refine Filter.eventually_of_mem (self_mem_nhdsWithin : Set.Ioi (0:ℝ) ∈ 𝓝[>] (0:ℝ)) ?_
    intro z hz'
    exact hmain z (le_of_lt hz') hz'

end Work.Spaces
end
end
-- ===== merged: Submission.Work.Spaces.HkAux =====
section

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

noncomputable section

open scoped Real Topology
open MeasureTheory Set Filter

namespace Work.Spaces

set_option autoImplicit false

/-! ## The open neighbourhood of the quadrant -/

/-- The open neighbourhood `(-1,∞) × (-1,π/2+1)` of the closed quadrant
`[0,∞) × [0,π/2]` on which `SmoothNbhd` demands smoothness. -/
def U : Set (ℝ × ℝ) := Set.Ioi (-1) ×ˢ Set.Ioo (-1) (π/2 + 1)

theorem isOpen_U : IsOpen U := isOpen_Ioi.prod isOpen_Ioo


theorem mem_U {z θ : ℝ} (hz : -1 < z) (hθ₀ : -1 < θ) (hθ₁ : θ < π/2 + 1) : (z, θ) ∈ U :=
  ⟨hz, hθ₀, hθ₁⟩

theorem mem_U_of_dom {z θ : ℝ} (hz : z ∈ Iz) (hθ : θ ∈ Iθ) : (z, θ) ∈ U := by
  refine mem_U ?_ ?_ ?_
  · have : (0 : ℝ) ≤ z := hz
    linarith
  · have : (0 : ℝ) ≤ θ := hθ.1
    linarith
  · have h₁ : θ ≤ π / 2 := hθ.2
    have := Real.pi_pos
    linarith

theorem mem_U_of_box {R z θ : ℝ} (hz : z ∈ Set.Icc 0 R) (hθ : θ ∈ Iθ) : (z, θ) ∈ U :=
  mem_U_of_dom hz.1 hθ

/-! ## The box `[0,R] × [0,π/2]` -/

theorem isCompact_box (R : ℝ) : IsCompact (Set.Icc 0 R ×ˢ Iθ) := by
  rw [Iθ]
  exact isCompact_Icc.prod isCompact_Icc

theorem box_nonempty {R : ℝ} (hR : 0 ≤ R) : (Set.Icc 0 R ×ˢ Iθ).Nonempty :=
  ⟨(0, 0), ⟨⟨le_refl 0, hR⟩, zero_mem_Iθ⟩⟩

/-- The set of values `|H z θ|` for `(z,θ)` in the box `[0,R] × [0,π/2]`. -/
def boxSet (R : ℝ) (H : ℝ → ℝ → ℝ) : Set ℝ := {y : ℝ | ∃ z ∈ Set.Icc 0 R, ∃ θ ∈ Iθ, y = |H z θ|}

/-- The supremum of `|H|` over the box `[0,R] × [0,π/2]`. -/
def boxSup (R : ℝ) (H : ℝ → ℝ → ℝ) : ℝ := sSup (boxSet R H)

theorem bddAbove_boxSup_of_continuousOn {R : ℝ} {H : ℝ → ℝ → ℝ}
    (h : ContinuousOn (Function.uncurry H) (Set.Icc 0 R ×ˢ Iθ)) : BddAbove (boxSet R H) := by
  have hc : ContinuousOn (fun q : ℝ × ℝ => |Function.uncurry H q|) (Set.Icc 0 R ×ˢ Iθ) := h.abs
  refine (isCompact_box R).bddAbove_image hc |>.mono ?_
  rintro y ⟨z, hz, θ, hθ, rfl⟩
  exact ⟨(z, θ), ⟨hz, hθ⟩, rfl⟩

theorem continuousOn_box_of_contDiffOn {R : ℝ} {H : ℝ → ℝ → ℝ}
    (h : ContDiffOn ℝ ⊤ (Function.uncurry H) U) :
    ContinuousOn (Function.uncurry H) (Set.Icc 0 R ×ˢ Iθ) :=
  h.continuousOn.mono fun p hp => mem_U_of_box hp.1 hp.2

theorem le_boxSup {R : ℝ} {H : ℝ → ℝ → ℝ} (hb : BddAbove (boxSet R H))
    {z θ : ℝ} (hz : z ∈ Set.Icc 0 R) (hθ : θ ∈ Iθ) : |H z θ| ≤ boxSup R H :=
  le_csSup hb ⟨z, hz, θ, hθ, rfl⟩

theorem boxSup_nonneg {R : ℝ} {H : ℝ → ℝ → ℝ} (hR : 0 ≤ R) (hb : BddAbove (boxSet R H)) :
    0 ≤ boxSup R H := by
  rcases box_nonempty hR with ⟨p, hp⟩
  exact le_trans (abs_nonneg _) (le_boxSup hb hp.1 hp.2)



theorem supFinite_of_pointwise {H : ℝ → ℝ → ℝ} {C : ℝ}
    (h : ∀ z ∈ Iz, ∀ θ ∈ Iθ, |H z θ| ≤ C) : SupFinite H :=
  ⟨C, fun y hy => by rcases hy with ⟨z, hz, θ, hθ, rfl⟩; exact h z hz θ hθ⟩

end Work.Spaces
end
end
-- ===== merged: Submission.Work.Spaces.SupportZ =====
section

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

noncomputable section

open scoped Real Topology
open MeasureTheory Set Filter

namespace Work.Spaces

set_option autoImplicit false


end Work.Spaces
end
end
-- ===== merged: Submission.Work.Spaces.WlInf_terms =====
section

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

noncomputable section

open scoped Real Topology
open MeasureTheory Set Filter

namespace Work.Spaces

set_option autoImplicit false

/-- The `L^∞`-norm on the domain is nonnegative whenever it is honest. -/
theorem supAbs_nonneg {g : ℝ → ℝ → ℝ} (h : SupFinite g) : 0 ≤ supAbs g :=
  le_trans (abs_nonneg _) (abs_le_supAbs zero_mem_Iz zero_mem_Iθ h)

/-- `D_θ^j f` vanishes identically where `sin(2θ) = 0`, for `j ≥ 1`. -/
theorem DthIter_eq_zero_of_sin_eq_zero (f : ℝ → ℝ → ℝ) (j : ℕ) {θ : ℝ}
    (hθ : Real.sin (2 * θ) = 0) (z : ℝ) : DthIter (j + 1) f z θ = 0 := by
  rw [DthIter_succ]
  simp [Dth, hθ]

/-- `∂_z^k D_θ^j f` vanishes identically where `sin(2θ) = 0` (for `j ≥ 1`). -/
theorem pzIter_DthIter_eq_zero_of_sin_eq_zero (f : ℝ → ℝ → ℝ) (j : ℕ) {θ : ℝ}
    (hθ : Real.sin (2 * θ) = 0) (k : ℕ) :
    ∀ z : ℝ, pzIter k (DthIter (j + 1) f) z θ = 0 := by
  induction k with
  | zero => intro z; exact DthIter_eq_zero_of_sin_eq_zero f j hθ z
  | succ k ih =>
      intro z
      rw [pzIter_succ, pz]
      have : (fun z' => pzIter k (DthIter (j + 1) f) z' θ) = fun _ => (0 : ℝ) := funext ih
      rw [this]
      simp

/-- `D_θ^j f` vanishes on the angular boundary `θ = 0` for `j ≥ 1`. -/
theorem DthIter_apply_zero (f : ℝ → ℝ → ℝ) (j : ℕ) (z : ℝ) : DthIter (j + 1) f z 0 = 0 :=
  DthIter_eq_zero_of_sin_eq_zero f j (by simp) z

/-- `D_θ^j f` vanishes on the angular boundary `θ = π/2` for `j ≥ 1`. -/
theorem DthIter_apply_pi_half (f : ℝ → ℝ → ℝ) (j : ℕ) (z : ℝ) :
    DthIter (j + 1) f z (π / 2) = 0 :=
  DthIter_eq_zero_of_sin_eq_zero f j (by
    rw [show 2 * (π / 2) = π by ring, Real.sin_pi]) z

/-- The first sum inside `WlInf` is nonnegative. -/
theorem wlZSum_nonneg (α : ℝ) (l : ℕ) (f : ℝ → ℝ → ℝ) (hmem : WlInfMem α l f) :
    0 ≤ ∑ k ∈ Finset.range (l + 1), supAbs (fun z θ => (z + 1) ^ k * pzIter k f z θ) :=
  Finset.sum_nonneg fun k hk =>
    supAbs_nonneg (hmem.1 k (Nat.le_of_lt_succ (Finset.mem_range.mp hk)))

/-- The second sum inside `WlInf` is nonnegative. -/
theorem wlThSum_nonneg (α : ℝ) (l : ℕ) (f : ℝ → ℝ → ℝ) (hmem : WlInfMem α l f) :
    0 ≤ ∑ j ∈ Finset.range (l + 1), ∑ k ∈ Finset.range (l + 1),
        if 1 ≤ j ∧ k + j ≤ l then
          supAbs (fun z θ => (z + 1) ^ k * pzIter k (DthIter j f) z θ
            * (Real.sin (2 * θ)) ^ (-(α / 5)) / (α + Real.sin (2 * θ)))
        else 0 := by
  refine Finset.sum_nonneg fun j hj => Finset.sum_nonneg
    (f := fun k => if 1 ≤ j ∧ k + j ≤ l then
        supAbs (fun z θ => (z + 1) ^ k * pzIter k (DthIter j f) z θ
          * (Real.sin (2 * θ)) ^ (-(α / 5)) / (α + Real.sin (2 * θ))) else 0)
    fun k hk => ?_
  by_cases h : 1 ≤ j ∧ k + j ≤ l
  · rw [if_pos h]
    exact supAbs_nonneg (hmem.2 j (Nat.le_of_lt_succ (Finset.mem_range.mp hj))
      k (Nat.le_of_lt_succ (Finset.mem_range.mp hk)) h.1 h.2)
  · rw [if_neg h]

/-- Pointwise bound from the first (radial) sum of the `𝒲^{l,∞}`-norm. -/
theorem WlInf_z_bound (α : ℝ) (l : ℕ) (f : ℝ → ℝ → ℝ) (hmem : WlInfMem α l f)
    (k : ℕ) (hk : k ≤ l) (z θ : ℝ) (hz : z ∈ Iz) (hθ : θ ∈ Iθ) :
    |(z + 1) ^ k * pzIter k f z θ| ≤ WlInf α l f := by
  have hmem' : k ∈ Finset.range (l + 1) := Finset.mem_range.mpr (Nat.lt_succ_of_le hk)
  have h1 : supAbs (fun z θ => (z + 1) ^ k * pzIter k f z θ)
      ≤ ∑ a ∈ Finset.range (l + 1), supAbs (fun z θ => (z + 1) ^ a * pzIter a f z θ) := by
    refine Finset.single_le_sum
      (f := fun a => supAbs (fun z θ => (z + 1) ^ a * pzIter a f z θ)) ?_ hmem'
    intro a ha
    exact supAbs_nonneg (hmem.1 a (Nat.le_of_lt_succ (Finset.mem_range.mp ha)))
  have h2 : |(z + 1) ^ k * pzIter k f z θ|
      ≤ supAbs (fun z θ => (z + 1) ^ k * pzIter k f z θ) :=
    abs_le_supAbs hz hθ (hmem.1 k hk)
  rw [WlInf]
  exact le_trans h2 (le_trans h1 (le_add_of_nonneg_right (wlThSum_nonneg α l f hmem)))

/-- Pointwise bound from the second (angular) sum of the `𝒲^{l,∞}`-norm. -/
theorem WlInf_mixed_bound (α : ℝ) (l : ℕ) (f : ℝ → ℝ → ℝ) (hmem : WlInfMem α l f)
    (j k : ℕ) (hj : 1 ≤ j) (hjk : k + j ≤ l) (z θ : ℝ) (hz : z ∈ Iz) (hθ : θ ∈ Iθ) :
    |(z + 1) ^ k * pzIter k (DthIter j f) z θ
        * (Real.sin (2 * θ)) ^ (-(α / 5)) / (α + Real.sin (2 * θ))| ≤ WlInf α l f := by
  have hj' : j ∈ Finset.range (l + 1) := Finset.mem_range.mpr (by omega)
  have hk' : k ∈ Finset.range (l + 1) := Finset.mem_range.mpr (by omega)
  have h0 : j ≤ l := by omega
  have hmemj := hmem.2 j h0
  have h1 : |(z + 1) ^ k * pzIter k (DthIter j f) z θ
        * (Real.sin (2 * θ)) ^ (-(α / 5)) / (α + Real.sin (2 * θ))|
      ≤ supAbs (fun z θ => (z + 1) ^ k * pzIter k (DthIter j f) z θ
          * (Real.sin (2 * θ)) ^ (-(α / 5)) / (α + Real.sin (2 * θ))) :=
    abs_le_supAbs hz hθ (hmemj k (by omega) hj hjk)
  have hinner : supAbs (fun z θ => (z + 1) ^ k * pzIter k (DthIter j f) z θ
          * (Real.sin (2 * θ)) ^ (-(α / 5)) / (α + Real.sin (2 * θ)))
      ≤ ∑ b ∈ Finset.range (l + 1),
          (if 1 ≤ j ∧ b + j ≤ l then
            supAbs (fun z θ => (z + 1) ^ b * pzIter b (DthIter j f) z θ
              * (Real.sin (2 * θ)) ^ (-(α / 5)) / (α + Real.sin (2 * θ))) else 0) := by
    have hif : (if 1 ≤ j ∧ k + j ≤ l then
        supAbs (fun z θ => (z + 1) ^ k * pzIter k (DthIter j f) z θ
          * (Real.sin (2 * θ)) ^ (-(α / 5)) / (α + Real.sin (2 * θ))) else 0)
        = supAbs (fun z θ => (z + 1) ^ k * pzIter k (DthIter j f) z θ
          * (Real.sin (2 * θ)) ^ (-(α / 5)) / (α + Real.sin (2 * θ))) := if_pos ⟨hj, hjk⟩
    rw [← hif]
    refine Finset.single_le_sum
      (f := fun b => if 1 ≤ j ∧ b + j ≤ l then
          supAbs (fun z θ => (z + 1) ^ b * pzIter b (DthIter j f) z θ
            * (Real.sin (2 * θ)) ^ (-(α / 5)) / (α + Real.sin (2 * θ))) else 0) ?_ hk'
    intro b hb
    by_cases h : 1 ≤ j ∧ b + j ≤ l
    · rw [if_pos h]
      exact supAbs_nonneg (hmemj b (Nat.le_of_lt_succ (Finset.mem_range.mp hb)) h.1 h.2)
    · rw [if_neg h]
  have houter : (∑ b ∈ Finset.range (l + 1),
          (if 1 ≤ j ∧ b + j ≤ l then
            supAbs (fun z θ => (z + 1) ^ b * pzIter b (DthIter j f) z θ
              * (Real.sin (2 * θ)) ^ (-(α / 5)) / (α + Real.sin (2 * θ))) else 0))
      ≤ ∑ a ∈ Finset.range (l + 1), ∑ b ∈ Finset.range (l + 1),
          (if 1 ≤ a ∧ b + a ≤ l then
            supAbs (fun z θ => (z + 1) ^ b * pzIter b (DthIter a f) z θ
              * (Real.sin (2 * θ)) ^ (-(α / 5)) / (α + Real.sin (2 * θ))) else 0) := by
    refine Finset.single_le_sum
      (f := fun a => ∑ b ∈ Finset.range (l + 1),
          (if 1 ≤ a ∧ b + a ≤ l then
            supAbs (fun z θ => (z + 1) ^ b * pzIter b (DthIter a f) z θ
              * (Real.sin (2 * θ)) ^ (-(α / 5)) / (α + Real.sin (2 * θ))) else 0)) ?_ hj'
    intro a ha
    refine Finset.sum_nonneg
      (f := fun b => if 1 ≤ a ∧ b + a ≤ l then
          supAbs (fun z θ => (z + 1) ^ b * pzIter b (DthIter a f) z θ
            * (Real.sin (2 * θ)) ^ (-(α / 5)) / (α + Real.sin (2 * θ))) else 0) ?_
    intro b hb
    by_cases h : 1 ≤ a ∧ b + a ≤ l
    · rw [if_pos h]
      exact supAbs_nonneg (hmem.2 a (Nat.le_of_lt_succ (Finset.mem_range.mp ha))
        b (Nat.le_of_lt_succ (Finset.mem_range.mp hb)) h.1 h.2)
    · rw [if_neg h]
  rw [WlInf]
  exact le_trans h1 (le_trans hinner (le_trans houter (le_add_of_nonneg_left (wlZSum_nonneg α l f hmem))))

/-- Unweighted form of the radial bound: `|∂_z^k f| ≤ |f|_𝒲 (1+z)^{-k}`. -/
theorem pz_sup_bound (α : ℝ) (l : ℕ) (f : ℝ → ℝ → ℝ) (hmem : WlInfMem α l f)
    (k : ℕ) (hk : k ≤ l) (z θ : ℝ) (hz : z ∈ Iz) (hθ : θ ∈ Iθ) :
    |pzIter k f z θ| ≤ WlInf α l f / (z + 1) ^ k := by
  have hz1 : (0 : ℝ) < z + 1 := by
    have hz0 : (0 : ℝ) ≤ z := hz
    linarith
  have hpow : (0 : ℝ) < (z + 1) ^ k := pow_pos hz1 k
  have h1 := WlInf_z_bound α l f hmem k hk z θ hz hθ
  rw [abs_mul, abs_of_pos hpow] at h1
  rw [le_div_iff₀ hpow]
  calc |pzIter k f z θ| * (z + 1) ^ k = (z + 1) ^ k * |pzIter k f z θ| := by ring
    _ ≤ WlInf α l f := h1

/-- Unweighted form of the angular bound:
`|∂_z^k D_θ^j f| ≤ |f|_𝒲 (1+z)^{-k} (α+sin(2θ)) sin(2θ)^{α/5}` for `j ≥ 1`. -/
theorem pz_Dth_sup_bound (α : ℝ) (hα : 0 < α) (l : ℕ) (f : ℝ → ℝ → ℝ) (hmem : WlInfMem α l f)
    (j k : ℕ) (hj : 1 ≤ j) (hjk : k + j ≤ l) (z θ : ℝ) (hz : z ∈ Iz) (hθ : θ ∈ Iθ) :
    |pzIter k (DthIter j f) z θ| ≤ WlInf α l f / (z + 1) ^ k
      * ((α + Real.sin (2 * θ)) * (Real.sin (2 * θ)) ^ (α / 5)) := by
  obtain ⟨j', rfl⟩ : ∃ j', j = j' + 1 := ⟨j - 1, by omega⟩
  have hα5 : (0 : ℝ) < α / 5 := by linarith
  have hz1 : (0 : ℝ) < z + 1 := by
    have hz0 : (0 : ℝ) ≤ z := hz
    linarith
  have hpow : (0 : ℝ) < (z + 1) ^ k := pow_pos hz1 k
  have hsin0 : 0 ≤ Real.sin (2 * θ) := by
    apply Real.sin_nonneg_of_nonneg_of_le_pi
    · linarith [hθ.1]
    · linarith [hθ.2]
  rcases eq_or_lt_of_le hsin0 with hs | hs
  · rw [← hs, Real.zero_rpow (ne_of_gt hα5),
      pzIter_DthIter_eq_zero_of_sin_eq_zero f j' hs.symm k z, abs_zero]
    simp
  · have hθpos : (0 : ℝ) < α + Real.sin (2 * θ) := by linarith
    have hweighted := WlInf_mixed_bound α l f hmem (j' + 1) k (by omega) hjk z θ hz hθ
    rw [abs_div, abs_mul, abs_mul, abs_of_pos hpow,
      abs_of_nonneg (Real.rpow_nonneg hsin0 _), abs_of_pos hθpos] at hweighted
    have hrpow : (Real.sin (2 * θ)) ^ (-(α / 5)) * (Real.sin (2 * θ)) ^ (α / 5) = 1 := by
      rw [← Real.rpow_add hs]
      ring_nf
      simp
    have hstep : (z + 1) ^ k * |pzIter k (DthIter (j' + 1) f) z θ| ≤
        WlInf α l f * ((α + Real.sin (2 * θ)) * (Real.sin (2 * θ)) ^ (α / 5)) := by
      have h2 : (z + 1) ^ k * |pzIter k (DthIter (j' + 1) f) z θ|
          * (Real.sin (2 * θ)) ^ (-(α / 5)) ≤ WlInf α l f * (α + Real.sin (2 * θ)) := by
        rw [div_le_iff₀ hθpos] at hweighted
        exact hweighted
      calc (z + 1) ^ k * |pzIter k (DthIter (j' + 1) f) z θ|
          = ((z + 1) ^ k * |pzIter k (DthIter (j' + 1) f) z θ|
              * (Real.sin (2 * θ)) ^ (-(α / 5))) * (Real.sin (2 * θ)) ^ (α / 5) := by
            rw [mul_assoc, hrpow, mul_one]
        _ ≤ (WlInf α l f * (α + Real.sin (2 * θ))) * (Real.sin (2 * θ)) ^ (α / 5) :=
            mul_le_mul_of_nonneg_right h2 (Real.rpow_nonneg hsin0 _)
        _ = WlInf α l f * ((α + Real.sin (2 * θ)) * (Real.sin (2 * θ)) ^ (α / 5)) := by ring
    have hfinal : |pzIter k (DthIter (j' + 1) f) z θ| ≤
        WlInf α l f * ((α + Real.sin (2 * θ)) * (Real.sin (2 * θ)) ^ (α / 5))
          / (z + 1) ^ k := by
      rw [le_div_iff₀ hpow]
      calc |pzIter k (DthIter (j' + 1) f) z θ| * (z + 1) ^ k
          = (z + 1) ^ k * |pzIter k (DthIter (j' + 1) f) z θ| := by ring
        _ ≤ WlInf α l f * ((α + Real.sin (2 * θ)) * (Real.sin (2 * θ)) ^ (α / 5)) := hstep
    calc |pzIter k (DthIter (j' + 1) f) z θ|
        ≤ WlInf α l f * ((α + Real.sin (2 * θ)) * (Real.sin (2 * θ)) ^ (α / 5))
            / (z + 1) ^ k := hfinal
      _ = WlInf α l f / (z + 1) ^ k
            * ((α + Real.sin (2 * θ)) * (Real.sin (2 * θ)) ^ (α / 5)) := by ring

end Work.Spaces
end
end
-- ===== merged: Submission.Work.Spaces.integral_sin_rpow =====
section

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

noncomputable section

open scoped Real Topology
open MeasureTheory Set Filter

namespace Work.Spaces

set_option autoImplicit false

/-- The angular integral of `sin(2θ)^{γ-2}` over `[0,π/2]` is bounded by `100/(γ-1)`
for `0 < α ≤ 1` (so that `1 < γ ≤ 11/10`, i.e. `γ - 1 = α/10 ≤ 1/10`).

The exponent `γ-2 = -(1 - α/10)` lies in `(-1, -9/10]`, so the integrand has an
integrable singularity at each endpoint `θ = 0` and `θ = π/2`; the sharp value of the
integral is `(√π/2) Γ((γ-1)/2)/Γ(γ/2) ≈ 1/(γ-1)` for `γ → 1⁺`, so the constant `100`
is very generous. -/
theorem integral_sin_rpow (α : ℝ) (hα : 0 < α) (hα1 : α ≤ 1) :
    ∫ θ in Work.Spaces.Iθ, (Real.sin (2 * θ)) ^ (Work.Spaces.gam α - 2)
      ≤ 100 / (Work.Spaces.gam α - 1) := by
  -- The exponent `gam α - 2 = -p` with `p = 1 - α/10 ∈ (0,1)`.
  set p : ℝ := 1 - α / 10 with hpdef
  have hp0 : 0 < p := by simp only [hpdef]; linarith
  have hp1 : p < 1 := by simp only [hpdef]; linarith
  have hexp : Work.Spaces.gam α - 2 = -p := by simp only [hpdef, Work.Spaces.gam]; ring
  have hgam : Work.Spaces.gam α - 1 = 1 - p := by simp only [hpdef, Work.Spaces.gam]; ring
  -- The majorant `G θ = (π/4)^p (θ^{-p} + (π/2-θ)^{-p})`: integrable with integral
  -- `π (1/2)^p / (1-p)`.
  have hGint : Integrable
      (fun θ : ℝ => (Real.pi / 4) ^ p * (θ ^ (-p) + (Real.pi / 2 - θ) ^ (-p)))
      (volume.restrict Work.Spaces.Iθ) := integrableOn_majorant_rpow p hp0 hp1
  have hGval : ∫ θ in Work.Spaces.Iθ,
        ((Real.pi / 4) ^ p * (θ ^ (-p) + (Real.pi / 2 - θ) ^ (-p)))
      = Real.pi * (1 / 2) ^ p / (1 - p) := integral_majorant_rpow p hp0 hp1
  -- The integrand is nonnegative on `Iθ`.
  have hnonneg : 0 ≤ᵐ[volume.restrict Work.Spaces.Iθ]
      (fun θ : ℝ => (Real.sin (2 * θ)) ^ (Work.Spaces.gam α - 2)) := by
    filter_upwards [ae_restrict_mem measurableSet_Icc] with θ hθ
    rw [hexp]
    exact Real.rpow_nonneg (Real.sin_nonneg_of_mem_Icc
      ⟨by linarith [hθ.1], by linarith [hθ.2, Real.pi_pos]⟩) _
  -- The pointwise majorant, valid everywhere on `Iθ`.
  have hle : (fun θ : ℝ => (Real.sin (2 * θ)) ^ (Work.Spaces.gam α - 2)) ≤ᵐ[volume.restrict Work.Spaces.Iθ]
      (fun θ : ℝ => (Real.pi / 4) ^ p * (θ ^ (-p) + (Real.pi / 2 - θ) ^ (-p))) := by
    filter_upwards [ae_restrict_mem measurableSet_Icc] with θ hθ
    rw [hexp]
    exact sin_rpow_le_majorant p θ hp0 hθ
  have hmono := integral_mono_of_nonneg hnonneg hGint hle
  calc ∫ θ in Work.Spaces.Iθ, (Real.sin (2 * θ)) ^ (Work.Spaces.gam α - 2)
      ≤ ∫ θ in Work.Spaces.Iθ, ((Real.pi / 4) ^ p * (θ ^ (-p) + (Real.pi / 2 - θ) ^ (-p))) :=
        hmono
    _ = Real.pi * (1 / 2) ^ p / (1 - p) := hGval
    _ ≤ 100 / (Work.Spaces.gam α - 1) := by
        rw [hgam]
        refine div_le_div_of_nonneg_right ?_ (by linarith : (0 : ℝ) ≤ 1 - p)
        have hhalf : (1 / 2 : ℝ) ^ p ≤ 1 :=
          Real.rpow_le_one (by norm_num) (by norm_num) (le_of_lt hp0)
        have h4 := Real.pi_lt_four
        have hnum : Real.pi * (1 / 2) ^ p ≤ 4 := by
          calc Real.pi * (1 / 2) ^ p ≤ 4 * 1 :=
                mul_le_mul (le_of_lt h4) hhalf (by positivity) (by norm_num)
            _ = 4 := by norm_num
        linarith

end Work.Spaces
end
end
-- ===== merged: Submission.Work.Spaces.mixed_comm =====
section

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

noncomputable section
open scoped Real Topology
open MeasureTheory Set Filter

namespace Work.Spaces

/-! ## The open set on which `SmoothNbhd` is stated

`SmoothNbhd f` says that the uncurried `f` is smooth on an open neighbourhood of the
closed quadrant.  For the commutation of the operators `D_z = z ∂_z` and
`D_θ = sin(2θ) ∂_θ` we only ever need smoothness on that open set, so it is convenient
to give it a name. -/

/-- The open set `(-1,∞) × (-1, π/2+1)` on which `SmoothNbhd` is formulated. -/
def nbhU : Set (ℝ × ℝ) := Set.Ioi (-1) ×ˢ Set.Ioo (-1) (π/2 + 1)

lemma isOpen_nbhU : IsOpen nbhU := isOpen_Ioi.prod isOpen_Ioo

lemma mem_nbhU {z θ : ℝ} (hz : z ∈ Iz) (hθ : θ ∈ Iθ) : (z, θ) ∈ nbhU := by
  rw [Iz, Set.mem_Ici] at hz
  rw [Iθ, Set.mem_Icc] at hθ
  refine Set.mem_prod.mpr ⟨?_, ?_⟩
  · rw [Set.mem_Ioi]; linarith
  · rw [Set.mem_Ioo]; exact ⟨by linarith, by linarith [Real.pi_pos]⟩

/-! ## Slice derivatives and the derivative of the uncurried function

The partial derivative in `z` (at fixed `θ`) of `f : ℝ → ℝ → ℝ` is the derivative of
the slice of `Function.uncurry f`, and it is the first derivative of the uncurried
function in the direction `(1,0)`.  Similarly in `θ`. -/

lemma deriv_slice_fst (F : ℝ × ℝ → ℝ) (z θ : ℝ) (h : DifferentiableAt ℝ F (z,θ)) :
    deriv (fun z' => F (z',θ)) z = fderiv ℝ F (z,θ) (1,0) := by
  have h2 : HasFDerivAt (fun t : ℝ => (t, θ)) (ContinuousLinearMap.inl ℝ ℝ ℝ) z :=
    hasFDerivAt_prodMk_left z θ
  have h3 : HasDerivAt (fun t : ℝ => F (t, θ))
      ((fderiv ℝ F (z,θ)) (ContinuousLinearMap.inl ℝ ℝ ℝ 1)) z :=
    (h.hasFDerivAt.comp z h2).hasDerivAt
  rw [h3.deriv]; simp

lemma deriv_slice_snd (F : ℝ × ℝ → ℝ) (z θ : ℝ) (h : DifferentiableAt ℝ F (z,θ)) :
    deriv (fun θ' => F (z,θ')) θ = fderiv ℝ F (z,θ) (0,1) := by
  have h2 : HasFDerivAt (fun t : ℝ => (z, t)) (ContinuousLinearMap.inr ℝ ℝ ℝ) θ :=
    hasFDerivAt_prodMk_right z θ
  have h3 : HasDerivAt (fun t : ℝ => F (z, t))
      ((fderiv ℝ F (z,θ)) (ContinuousLinearMap.inr ℝ ℝ ℝ 1)) θ :=
    (h.hasFDerivAt.comp θ h2).hasDerivAt
  rw [h3.deriv]; simp

/-- The second mixed slice derivative `∂_z ∂_θ` is the second differential of the
uncurried function evaluated on `((1,0),(0,1))`. -/
lemma deriv_deriv_fst_snd (F : ℝ × ℝ → ℝ) (z θ : ℝ) (h : ContDiffAt ℝ 2 F (z,θ)) :
    deriv (fun z' => deriv (fun θ' => F (z',θ')) θ) z
      = (fderiv ℝ (fderiv ℝ F) (z,θ) (1,0)) (0,1) := by
  have hfd_diff : DifferentiableAt ℝ (fderiv ℝ F) (z,θ) :=
    (ContDiffAt.fderiv_right h (by norm_num : (1:WithTop ℕ∞) + 1 ≤ 2)).differentiableAt (by norm_num)
  have hnd : ∀ᶠ y in 𝓝 (z,θ), DifferentiableAt ℝ F y :=
    (ContDiffAt.eventually h (by decide : (2:WithTop ℕ∞) ≠ ↑(⊤ : ℕ∞))).mono
      (fun y hy => hy.differentiableAt (by norm_num))
  have hslice : ∀ᶠ z' in 𝓝 z, DifferentiableAt ℝ F (z',θ) :=
    (Continuous.prodMk_left θ).continuousAt.eventually hnd
  have hcongr : (fun z' => deriv (fun θ' => F (z',θ')) θ) =ᶠ[𝓝 z]
      (fun z' => fderiv ℝ F (z',θ) (0,1)) := by
    filter_upwards [hslice] with z' hz'
    have h2 : HasFDerivAt (fun t : ℝ => (z', t)) (ContinuousLinearMap.inr ℝ ℝ ℝ) θ :=
      hasFDerivAt_prodMk_right z' θ
    have h3 : HasDerivAt (fun t : ℝ => F (z', t))
        ((fderiv ℝ F (z',θ)) (ContinuousLinearMap.inr ℝ ℝ ℝ 1)) θ :=
      (hz'.hasFDerivAt.comp θ h2).hasDerivAt
    rw [h3.deriv]; simp
  rw [hcongr.deriv_eq]
  let Φ : ℝ × ℝ → ℝ := fun y => fderiv ℝ F y (0,1)
  have hΦ : Φ = (ContinuousLinearMap.apply ℝ ℝ (0,1)) ∘ (fderiv ℝ F) := by
    funext y; simp only [Φ, Function.comp_apply, ContinuousLinearMap.apply_apply]
  have hΦdiff : DifferentiableAt ℝ Φ (z,θ) := by
    rw [hΦ]; exact (ContinuousLinearMap.differentiableAt _).comp _ hfd_diff
  have stepA : deriv (fun z' => Φ (z',θ)) z = fderiv ℝ Φ (z,θ) (1,0) := by
    have h2 : HasFDerivAt (fun t : ℝ => (t, θ)) (ContinuousLinearMap.inl ℝ ℝ ℝ) z :=
      hasFDerivAt_prodMk_left z θ
    have h3 : HasDerivAt (fun t : ℝ => Φ (t, θ))
        ((fderiv ℝ Φ (z,θ)) (ContinuousLinearMap.inl ℝ ℝ ℝ 1)) z := by
      convert (hΦdiff.hasFDerivAt.comp z h2).hasDerivAt using 1
      · ext t; rfl
      · rw [ContinuousLinearMap.comp_apply, ContinuousLinearMap.inl_apply]
    rw [h3.deriv]; simp
  have hΦderiv : fderiv ℝ Φ (z,θ) =
      (ContinuousLinearMap.apply ℝ ℝ (0,1)) ∘SL fderiv ℝ (fderiv ℝ F) (z,θ) := by
    conv_lhs => rw [hΦ]
    rw [fderiv_comp (z,θ) (ContinuousLinearMap.differentiableAt _) hfd_diff]
    rw [ContinuousLinearMap.fderiv]
  rw [stepA, hΦderiv]
  simp [ContinuousLinearMap.comp_apply, ContinuousLinearMap.apply_apply]

/-- The second mixed slice derivative `∂_θ ∂_z` is the second differential of the
uncurried function evaluated on `((0,1),(1,0))`. -/
lemma deriv_deriv_snd_fst (F : ℝ × ℝ → ℝ) (z θ : ℝ) (h : ContDiffAt ℝ 2 F (z,θ)) :
    deriv (fun θ' => deriv (fun z' => F (z',θ')) z) θ
      = (fderiv ℝ (fderiv ℝ F) (z,θ) (0,1)) (1,0) := by
  have hfd_diff : DifferentiableAt ℝ (fderiv ℝ F) (z,θ) :=
    (ContDiffAt.fderiv_right h (by norm_num : (1:WithTop ℕ∞) + 1 ≤ 2)).differentiableAt (by norm_num)
  have hnd : ∀ᶠ y in 𝓝 (z,θ), DifferentiableAt ℝ F y :=
    (ContDiffAt.eventually h (by decide : (2:WithTop ℕ∞) ≠ ↑(⊤ : ℕ∞))).mono
      (fun y hy => hy.differentiableAt (by norm_num))
  have hslice : ∀ᶠ θ' in 𝓝 θ, DifferentiableAt ℝ F (z,θ') :=
    (Continuous.prodMk_right z).continuousAt.eventually hnd
  have hcongr : (fun θ' => deriv (fun z' => F (z',θ')) z) =ᶠ[𝓝 θ]
      (fun θ' => fderiv ℝ F (z,θ') (1,0)) := by
    filter_upwards [hslice] with θ' hθ'
    have h2 : HasFDerivAt (fun t : ℝ => (t, θ')) (ContinuousLinearMap.inl ℝ ℝ ℝ) z :=
      hasFDerivAt_prodMk_left z θ'
    have h3 : HasDerivAt (fun t : ℝ => F (t, θ'))
        ((fderiv ℝ F (z,θ')) (ContinuousLinearMap.inl ℝ ℝ ℝ 1)) z :=
      (hθ'.hasFDerivAt.comp z h2).hasDerivAt
    rw [h3.deriv]; simp
  rw [hcongr.deriv_eq]
  let Φ : ℝ × ℝ → ℝ := fun y => fderiv ℝ F y (1,0)
  have hΦ : Φ = (ContinuousLinearMap.apply ℝ ℝ (1,0)) ∘ (fderiv ℝ F) := by
    funext y; simp only [Φ, Function.comp_apply, ContinuousLinearMap.apply_apply]
  have hΦdiff : DifferentiableAt ℝ Φ (z,θ) := by
    rw [hΦ]; exact (ContinuousLinearMap.differentiableAt _).comp _ hfd_diff
  have stepA : deriv (fun θ' => Φ (z,θ')) θ = fderiv ℝ Φ (z,θ) (0,1) := by
    have h2 : HasFDerivAt (fun t : ℝ => (z, t)) (ContinuousLinearMap.inr ℝ ℝ ℝ) θ :=
      hasFDerivAt_prodMk_right z θ
    have h3 : HasDerivAt (fun t : ℝ => Φ (z, t))
        ((fderiv ℝ Φ (z,θ)) (ContinuousLinearMap.inr ℝ ℝ ℝ 1)) θ := by
      convert (hΦdiff.hasFDerivAt.comp θ h2).hasDerivAt using 1
      · ext t; rfl
      · rw [ContinuousLinearMap.comp_apply, ContinuousLinearMap.inr_apply]
    rw [h3.deriv]; simp
  have hΦderiv : fderiv ℝ Φ (z,θ) =
      (ContinuousLinearMap.apply ℝ ℝ (1,0)) ∘SL fderiv ℝ (fderiv ℝ F) (z,θ) := by
    conv_lhs => rw [hΦ]
    rw [fderiv_comp (z,θ) (ContinuousLinearMap.differentiableAt _) hfd_diff]
    rw [ContinuousLinearMap.fderiv]
  rw [stepA, hΦderiv]
  simp [ContinuousLinearMap.comp_apply, ContinuousLinearMap.apply_apply]

/-! ## Clairaut's theorem for the curvilinear derivatives -/

/-- The two iterated slice derivatives of a `C²` function agree (Clairaut/Schwarz). -/
lemma pz_pth_comm {f : ℝ → ℝ → ℝ} {z θ : ℝ}
    (h : ContDiffAt ℝ 2 (Function.uncurry f) (z,θ)) :
    pz (pth f) z θ = pth (pz f) z θ := by
  have h1 := deriv_deriv_fst_snd (Function.uncurry f) z θ h
  have h2 := deriv_deriv_snd_fst (Function.uncurry f) z θ h
  have hsym := (ContDiffAt.isSymmSndFDerivAt h (by simp : minSmoothness ℝ 2 ≤ 2)).eq (1,0) (0,1)
  change deriv (fun z' => deriv (fun θ' => (Function.uncurry f) (z',θ')) θ) z
      = deriv (fun θ' => deriv (fun z' => (Function.uncurry f) (z',θ')) z) θ
  rw [h1, h2]
  exact hsym

/-- The operators `D_z = z ∂_z` and `D_θ = sin(2θ) ∂_θ` commute at any point where the
function is `C²`. -/
lemma Dz_Dth_comm {f : ℝ → ℝ → ℝ} {z θ : ℝ}
    (h : ContDiffAt ℝ 2 (Function.uncurry f) (z,θ)) :
    Dz (Dth f) z θ = Dth (Dz f) z θ := by
  show z * pz (Dth f) z θ = Real.sin (2*θ) * pth (Dz f) z θ
  have h1 : pz (Dth f) z θ = Real.sin (2*θ) * pz (pth f) z θ := by
    show deriv (fun z' => Real.sin (2*θ) * pth f z' θ) z = Real.sin (2*θ) * pz (pth f) z θ
    rw [deriv_const_mul_field]
    rfl
  have h2 : pth (Dz f) z θ = z * pth (pz f) z θ := by
    show deriv (fun θ' => z * pz f z θ') θ = z * pth (pz f) z θ
    rw [deriv_const_mul_field]
    rfl
  rw [h1, h2, pz_pth_comm h]
  ring

/-! ## `SmoothNbhd` is preserved by `D_z`, `D_θ` and their iterates -/

lemma SmoothNbhd.Dz {f : ℝ → ℝ → ℝ} (h : SmoothNbhd f) : SmoothNbhd (Dz f) := by
  have hfd : ContDiffOn ℝ ⊤ (fderiv ℝ (Function.uncurry f)) nbhU :=
    ContDiffOn.fderiv_of_isOpen h isOpen_nbhU (by simp)
  have hev : ContDiffOn ℝ ⊤ (fun y : ℝ × ℝ => (fderiv ℝ (Function.uncurry f) y) (1,0)) nbhU :=
    hfd.clm_apply contDiffOn_const
  have hfun : ContDiffOn ℝ ⊤ (fun y : ℝ × ℝ =>
      y.1 * (fderiv ℝ (Function.uncurry f) y) (1,0)) nbhU :=
    (contDiff_fst.contDiffOn).mul hev
  refine hfun.congr (fun y hy => ?_)
  have hdiff : DifferentiableAt ℝ (Function.uncurry f) y :=
    (ContDiffOn.contDiffAt h (isOpen_nbhU.mem_nhds hy)).differentiableAt (by norm_num)
  have hderiv : deriv (fun z' => Function.uncurry f (z', y.2)) y.1
      = (fderiv ℝ (Function.uncurry f) y) (1,0) := deriv_slice_fst _ _ _ hdiff
  show y.1 * deriv (fun z' => Function.uncurry f (z', y.2)) y.1
      = y.1 * (fderiv ℝ (Function.uncurry f) y) (1,0)
  rw [hderiv]

lemma SmoothNbhd.Dth {f : ℝ → ℝ → ℝ} (h : SmoothNbhd f) : SmoothNbhd (Dth f) := by
  have hfd : ContDiffOn ℝ ⊤ (fderiv ℝ (Function.uncurry f)) nbhU :=
    ContDiffOn.fderiv_of_isOpen h isOpen_nbhU (by simp)
  have hev : ContDiffOn ℝ ⊤ (fun y : ℝ × ℝ => (fderiv ℝ (Function.uncurry f) y) (0,1)) nbhU :=
    hfd.clm_apply contDiffOn_const
  have hsin : ContDiffOn ℝ ⊤ (fun y : ℝ × ℝ => Real.sin (2 * y.2)) nbhU :=
    (Real.contDiff_sin.comp (contDiff_const.mul contDiff_snd)).contDiffOn
  have hfun : ContDiffOn ℝ ⊤ (fun y : ℝ × ℝ =>
      Real.sin (2*y.2) * (fderiv ℝ (Function.uncurry f) y) (0,1)) nbhU := hsin.mul hev
  refine hfun.congr (fun y hy => ?_)
  have hdiff : DifferentiableAt ℝ (Function.uncurry f) y :=
    (ContDiffOn.contDiffAt h (isOpen_nbhU.mem_nhds hy)).differentiableAt (by norm_num)
  have hderiv : deriv (fun θ' => Function.uncurry f (y.1, θ')) y.2
      = (fderiv ℝ (Function.uncurry f) y) (0,1) := deriv_slice_snd _ _ _ hdiff
  show Real.sin (2*y.2) * deriv (fun θ' => Function.uncurry f (y.1, θ')) y.2
      = Real.sin (2*y.2) * (fderiv ℝ (Function.uncurry f) y) (0,1)
  rw [hderiv]

lemma SmoothNbhd.DzIter {f : ℝ → ℝ → ℝ} (h : SmoothNbhd f) :
    ∀ n : ℕ, SmoothNbhd (DzIter n f)
  | 0 => h
  | n+1 => SmoothNbhd.Dz (SmoothNbhd.DzIter h n)

lemma SmoothNbhd.DthIter {f : ℝ → ℝ → ℝ} (h : SmoothNbhd f) :
    ∀ n : ℕ, SmoothNbhd (DthIter n f)
  | 0 => h
  | n+1 => SmoothNbhd.Dth (SmoothNbhd.DthIter h n)

/-! ## Congruence of `pz`, `pth`, `Dz`, `Dth` under equality on `nbhU` -/

lemma pz_congr {g g' : ℝ → ℝ → ℝ}
    (h : EqOn (Function.uncurry g) (Function.uncurry g') nbhU) {z θ : ℝ}
    (hz : (z,θ) ∈ nbhU) : pz g z θ = pz g' z θ := by
  have hnb : ∀ᶠ z' in 𝓝 z, (z', θ) ∈ nbhU :=
    (Continuous.prodMk_left θ).continuousAt.eventually (isOpen_nbhU.mem_nhds hz)
  have hslice : (fun z' => Function.uncurry g (z',θ)) =ᶠ[𝓝 z]
      (fun z' => Function.uncurry g' (z',θ)) := by
    filter_upwards [hnb] with z' hz'
    exact h hz'
  have := hslice.deriv_eq
  simpa only [pz, Function.uncurry] using this

lemma pth_congr {g g' : ℝ → ℝ → ℝ}
    (h : EqOn (Function.uncurry g) (Function.uncurry g') nbhU) {z θ : ℝ}
    (hz : (z,θ) ∈ nbhU) : pth g z θ = pth g' z θ := by
  have hnb : ∀ᶠ θ' in 𝓝 θ, (z, θ') ∈ nbhU :=
    (Continuous.prodMk_right z).continuousAt.eventually (isOpen_nbhU.mem_nhds hz)
  have hslice : (fun θ' => Function.uncurry g (z,θ')) =ᶠ[𝓝 θ]
      (fun θ' => Function.uncurry g' (z,θ')) := by
    filter_upwards [hnb] with θ' hθ'
    exact h hθ'
  have := hslice.deriv_eq
  simpa only [pth, Function.uncurry] using this

lemma Dz_congr {g g' : ℝ → ℝ → ℝ}
    (h : EqOn (Function.uncurry g) (Function.uncurry g') nbhU) :
    EqOn (Function.uncurry (Dz g)) (Function.uncurry (Dz g')) nbhU := by
  intro y hy
  have hp := pz_congr h hy
  show y.1 * pz g y.1 y.2 = y.1 * pz g' y.1 y.2
  rw [hp]

lemma Dth_congr {g g' : ℝ → ℝ → ℝ}
    (h : EqOn (Function.uncurry g) (Function.uncurry g') nbhU) :
    EqOn (Function.uncurry (Dth g)) (Function.uncurry (Dth g')) nbhU := by
  intro y hy
  have hp := pth_congr h hy
  show Real.sin (2*y.2) * pth g y.1 y.2 = Real.sin (2*y.2) * pth g' y.1 y.2
  rw [hp]

lemma DzIter_congr {g g' : ℝ → ℝ → ℝ}
    (h : EqOn (Function.uncurry g) (Function.uncurry g') nbhU) (j : ℕ) :
    EqOn (Function.uncurry (DzIter j g)) (Function.uncurry (DzIter j g')) nbhU := by
  induction j with
  | zero => exact h
  | succ j ih => exact Dz_congr ih

/-! ## The commutation identities on `nbhU` -/

lemma Dz_Dth_comm_eqOn {f : ℝ → ℝ → ℝ} (h : SmoothNbhd f) :
    EqOn (Function.uncurry (Dz (Dth f))) (Function.uncurry (Dth (Dz f))) nbhU := by
  intro y hy
  exact Dz_Dth_comm ((ContDiffOn.contDiffAt h (isOpen_nbhU.mem_nhds hy)).of_le (by norm_num))

/-- A single `D_θ` can be moved across any iterate of `D_z`. -/
lemma Dth_DzIter_comm_eqOn {f : ℝ → ℝ → ℝ} (h : SmoothNbhd f) (b : ℕ) :
    EqOn (Function.uncurry (Dth (DzIter b f))) (Function.uncurry (DzIter b (Dth f))) nbhU := by
  induction b with
  | zero => intro y hy; rfl
  | succ b ih =>
      intro y hy
      have hc : Dz (Dth (DzIter b f)) y.1 y.2 = Dth (Dz (DzIter b f)) y.1 y.2 :=
        Dz_Dth_comm_eqOn (SmoothNbhd.DzIter h b) hy
      have hpz := pz_congr ih hy
      show Dth (Dz (DzIter b f)) y.1 y.2 = Dz (DzIter b (Dth f)) y.1 y.2
      rw [← hc]
      show y.1 * pz (Dth (DzIter b f)) y.1 y.2 = y.1 * pz (DzIter b (Dth f)) y.1 y.2
      rw [hpz]

/-- The iterates of `D_θ` can be moved across any iterate of `D_z`. -/
lemma DthIter_DzIter_comm_eqOn {f : ℝ → ℝ → ℝ} (h : SmoothNbhd f) (b i : ℕ) :
    EqOn (Function.uncurry (DthIter i (DzIter b f))) (Function.uncurry (DzIter b (DthIter i f))) nbhU := by
  induction i with
  | zero => intro y hy; rfl
  | succ i ih =>
      intro y hy
      have hDth : Dth (DthIter i (DzIter b f)) y.1 y.2 = Dth (DzIter b (DthIter i f)) y.1 y.2 :=
        Dth_congr ih hy
      have hstep : Dth (DzIter b (DthIter i f)) y.1 y.2 = DzIter b (Dth (DthIter i f)) y.1 y.2 :=
        Dth_DzIter_comm_eqOn (SmoothNbhd.DthIter h i) b hy
      show Dth (DthIter i (DzIter b f)) y.1 y.2 = DzIter b (Dth (DthIter i f)) y.1 y.2
      rw [hDth, hstep]

/-! ## Composition of the iterates -/

lemma DthIter_add_right (i a : ℕ) (f : ℝ → ℝ → ℝ) :
    DthIter i (DthIter a f) = DthIter (i + a) f := by
  induction i with
  | zero => simp
  | succ i ih =>
      rw [show (i + 1) + a = (i + a) + 1 from Nat.succ_add i a]
      show Dth (DthIter i (DthIter a f)) = Dth (DthIter (i + a) f)
      rw [ih]

lemma DzIter_add_right (j b : ℕ) (f : ℝ → ℝ → ℝ) :
    DzIter (j + b) f = DzIter j (DzIter b f) := by
  induction j with
  | zero => simp
  | succ j ih =>
      rw [show (j + 1) + b = (j + b) + 1 from Nat.succ_add j b]
      show Dz (DzIter (j + b) f) = Dz (DzIter j (DzIter b f))
      rw [ih]

theorem mixed_comm (g : ℝ → ℝ → ℝ) (hg : Work.Spaces.SmoothNbhd g) (j i b a : ℕ) (z θ : ℝ)
    (hz : z ∈ Work.Spaces.Iz) (hθ : θ ∈ Work.Spaces.Iθ) :
    Work.Spaces.mixed j i (Work.Spaces.mixed b a g) z θ
      = Work.Spaces.mixed (j + b) (i + a) g z θ := by
  have hy : (z, θ) ∈ nbhU := mem_nbhU hz hθ
  have hga : SmoothNbhd (DthIter a g) := SmoothNbhd.DthIter hg a
  have e1 : DzIter j (DthIter i (DzIter b (DthIter a g))) z θ
      = DzIter j (DzIter b (DthIter i (DthIter a g))) z θ :=
    (DzIter_congr (DthIter_DzIter_comm_eqOn hga b i) j) hy
  have e3 : DzIter j (DzIter b (DthIter (i + a) g)) = DzIter (j + b) (DthIter (i + a) g) :=
    (DzIter_add_right j b (DthIter (i + a) g)).symm
  show DzIter j (DthIter i (DzIter b (DthIter a g))) z θ
      = DzIter (j + b) (DthIter (i + a) g) z θ
  rw [e1]
  rw [DthIter_add_right]
  rw [e3]

end Work.Spaces
end
end
-- ===== merged: Submission.Work.Spaces.psi_mw_le =====
section

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

set_option autoImplicit false
set_option linter.unusedVariables false

namespace Work.Spaces

/-- Auxiliary: for `s ∈ [0,1]` and `c ≥ 0`, the product `s^c · s^{-c}` is at most `1`.
This is the algebraic heart of `psi_mw_le`: the "weight" `A = (α+s)·s^{α/5}` and the
"reciprocal weight" `Z = s^{-α/5}/(α+s)` multiply to `s^{α/5}·s^{-α/5} ≤ 1`. -/
theorem rpow_mul_rpow_neg_le_one {s c : ℝ} (hs : 0 ≤ s) (hc : 0 ≤ c) :
    s ^ c * s ^ (-c) ≤ 1 := by
  rcases eq_or_lt_of_le hs with h | h
  · rw [← h]
    rcases eq_or_lt_of_le hc with hc0 | hcpos
    · rw [← hc0]; norm_num
    · rw [Real.zero_rpow (ne_of_gt hcpos), Real.zero_rpow (by linarith : (-c : ℝ) ≠ 0)]
      norm_num
  · rw [← Real.rpow_add h, show c + -c = 0 by ring, Real.rpow_zero]

/-- Auxiliary: for `α ∈ (0,1]` and `s ∈ [0,1]`, `(α+s)·s^{α/5} ≤ 2`. -/
theorem add_mul_rpow_le_two {α s : ℝ} (hα : 0 < α) (hα1 : α ≤ 1) (hs : 0 ≤ s) (hs1 : s ≤ 1) :
    (α + s) * s ^ (α / 5) ≤ 2 := by
  have hα5 : (0:ℝ) < α / 5 := by linarith
  have hB1 : s ^ (α / 5) ≤ 1 := Real.rpow_le_one hs hs1 (le_of_lt hα5)
  have hAs : 0 ≤ α + s := by linarith
  calc (α + s) * s ^ (α / 5) ≤ (α + s) * 1 := mul_le_mul_of_nonneg_left hB1 hAs
    _ ≤ 2 := by linarith

/-- Elgindi's weight estimate for the `W^{l,∞}` product rule: the "middle-factor"
combination `A_a · A_{j-a} · Z` is bounded by the constant `2` uniformly in `0 < α ≤ 1`
and `θ ∈ [0,π/2]`, where `A_k = (α+sin 2θ)·sin(2θ)^{α/5}` for `k ≠ 0` and `A_0 = 1`,
and `Z = sin(2θ)^{-α/5}/(α+sin 2θ)`. -/
theorem psi_mw_le (α : ℝ) (hα : 0 < α) (hα1 : α ≤ 1) (θ : ℝ) (hθ : θ ∈ Work.Spaces.Iθ)
    (a j : ℕ) (ha : a ≤ j) (hj : 1 ≤ j) :
    (if a = 0 then (1 : ℝ) else (α + Real.sin (2 * θ)) * (Real.sin (2 * θ)) ^ (α / 5))
        * (if j - a = 0 then (1 : ℝ) else (α + Real.sin (2 * θ)) * (Real.sin (2 * θ)) ^ (α / 5))
        * ((Real.sin (2 * θ)) ^ (-(α / 5)) / (α + Real.sin (2 * θ))) ≤ 2 := by
  have hθ0 : 0 ≤ θ := hθ.1
  have hθ1 : θ ≤ Real.pi / 2 := hθ.2
  have hs0 : 0 ≤ Real.sin (2 * θ) :=
    Real.sin_nonneg_of_nonneg_of_le_pi (by linarith) (by linarith)
  have hs1 : Real.sin (2 * θ) ≤ 1 := Real.sin_le_one _
  set s : ℝ := Real.sin (2 * θ) with hs
  have hs0' : 0 ≤ s := by rw [hs]; exact hs0
  have hs1' : s ≤ 1 := by rw [hs]; exact hs1
  set A : ℝ := (α + s) * s ^ (α / 5) with hAdef
  set Z : ℝ := s ^ (-(α / 5)) / (α + s) with hZdef
  have hα5 : (0:ℝ) < α / 5 := by linarith
  have hAs : 0 ≤ α + s := by linarith
  have hA0 : 0 ≤ A := by rw [hAdef]; exact mul_nonneg hAs (Real.rpow_nonneg hs0' _)
  have hA2 : A ≤ 2 := by rw [hAdef]; exact add_mul_rpow_le_two hα hα1 hs0' hs1'
  have hBC : s ^ (α / 5) * s ^ (-(α / 5)) ≤ 1 := rpow_mul_rpow_neg_le_one hs0' (le_of_lt hα5)
  have hne : α + s ≠ 0 := by positivity
  have hAZ : A * Z ≤ 1 := by
    have heq : A * Z = s ^ (α / 5) * s ^ (-(α / 5)) := by
      rw [hAdef, hZdef]; field_simp
    rw [heq]; exact hBC
  by_cases ha0 : a = 0
  · rw [ite_eq_left ha0]
    have hja : j - a ≠ 0 := by rw [ha0, Nat.sub_zero]; omega
    rw [ite_eq_right hja]
    nlinarith [hAZ]
  · rw [ite_eq_right ha0]
    by_cases hja : j - a = 0
    · rw [ite_eq_left hja]; nlinarith [hAZ]
    · rw [ite_eq_right hja]; nlinarith [hAZ, hA0, hA2]

end Work.Spaces
end
-- ===== merged: Submission.Work.Spaces.pth_integral =====
section

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

noncomputable section

open scoped Real Topology
open MeasureTheory Set Filter

namespace Work.Spaces

set_option autoImplicit false

/-- **Fundamental theorem of calculus for `∂_θ`.**

If `g` is smooth on an open neighbourhood of the closed quadrant (so in
particular `θ ↦ g z θ` is smooth on an open interval containing `[0, π/2]`)
and `z ≥ 0`, then for every `θ ∈ [0, π/2]` the angular derivative
`s ↦ ∂_θ g z s = pth g z s` is continuous on `[0, θ]` and

`∫_0^θ ∂_θ g z s ds = g z θ - g z 0`.

The smoothness is obtained by restricting the two-variable smoothness of `g` to
the line `z = const` (`ContDiffOn.comp`), after which Mathlib's second
fundamental theorem of calculus for `C^1` functions
(`intervalIntegral.integral_deriv_of_contDiffOn_Icc`) applies on `[0, θ]`. -/
theorem pth_integral (g : ℝ → ℝ → ℝ) (z : ℝ) (hsm : Work.Spaces.SmoothNbhd g) (hz : 0 ≤ z) :
    ∀ θ ∈ Work.Spaces.Iθ,
      (∫ s in (0 : ℝ)..θ, Work.Spaces.pth g z s = g z θ - g z 0) ∧
        ContinuousOn (fun s => Work.Spaces.pth g z s) (Set.Icc 0 θ) := by
  intro θ hθ
  obtain ⟨h0θ, hθpi⟩ := hθ
  -- `z` lies in the open left endpoint `-1` of the radial half-strip
  have hz1 : (-1 : ℝ) < z := by linarith
  -- the one-variable function `θ' ↦ g z θ'` is smooth on an open interval `U`
  -- containing the whole angular range `[0, π/2]`
  have hφU : ContDiffOn ℝ ⊤ (fun t : ℝ => g z t) (Set.Ioo (-1 : ℝ) (π/2 + 1)) := by
    have hp : ContDiffOn ℝ ⊤ (fun t : ℝ => (z, t)) (Set.Ioo (-1 : ℝ) (π/2 + 1)) :=
      contDiffOn_const.prodMk contDiffOn_id
    have h := hsm.comp hp (fun t ht => ⟨hz1, ht⟩)
    simpa [Function.comp_def, Function.uncurry] using h
  -- `[0, θ]` is contained in `U`
  have hsub : Set.Icc (0 : ℝ) θ ⊆ Set.Ioo (-1 : ℝ) (π/2 + 1) := by
    intro t ht
    refine ⟨by linarith [ht.1], ?_⟩
    have := Real.pi_pos
    linarith [ht.2]
  constructor
  · -- second fundamental theorem of calculus on `[0, θ]`
    have h := intervalIntegral.integral_deriv_of_contDiffOn_Icc (a := 0) (b := θ)
      ((hφU.of_le le_top).mono hsub) h0θ
    simpa [Work.Spaces.pth] using h
  · -- continuity of the derivative, from `C^∞` on the open set `U`
    have hcont : ContinuousOn (deriv (fun t : ℝ => g z t)) (Set.Icc 0 θ) :=
      (hφU.continuousOn_deriv_of_isOpen isOpen_Ioo le_top).mono hsub
    simpa [Work.Spaces.pth] using hcont

end Work.Spaces
end
end
-- ===== merged: Submission.Work.Spaces.pz_aux =====
section

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

noncomputable section

open scoped Real Topology ContDiff
open Set Filter

namespace Work.Spaces

set_option autoImplicit false

/-! ## `pzIter` is the iterated derivative of the `z`-slice -/

/-- `pzIter k h z θ` is the `k`-th iterated derivative of the function
`z' ↦ h z' θ` evaluated at `z`. -/
theorem pzIter_eq_iteratedDeriv (k : ℕ) (h : ℝ → ℝ → ℝ) (z θ : ℝ) :
    pzIter k h z θ = iteratedDeriv k (fun z' => h z' θ) z := by
  rw [iteratedDeriv_eq_iterate]
  induction k generalizing z with
  | zero => rfl
  | succ n ih =>
      simp only [pzIter_succ, pz]
      have : (fun z' => pzIter n h z' θ) = deriv^[n] (fun z' => h z' θ) := by
        funext z'; exact ih z'
      rw [this, Function.iterate_succ_apply']

/-- The iterated derivatives of the zero function vanish. -/
theorem iteratedDeriv_zero_fun (n : ℕ) (x : ℝ) :
    iteratedDeriv n (fun _ : ℝ => (0 : ℝ)) x = 0 := by
  induction n generalizing x with
  | zero => rfl
  | succ n ih =>
      rw [iteratedDeriv_succ,
        show iteratedDeriv n (fun _ : ℝ => (0 : ℝ)) = fun _ => 0 from funext ih]
      simp

/-- Iterated derivatives of a finite sum with constant coefficients. -/
theorem iteratedDeriv_sum_const_mul {ι : Type*} (s : Finset ι) (c : ι → ℝ)
    (F : ι → ℝ → ℝ) (n : ℕ) (x : ℝ)
    (h : ∀ i ∈ s, ContDiffAt ℝ (n : ℕ∞) (F i) x) :
    iteratedDeriv n (fun y => ∑ i ∈ s, c i * F i y) x
      = ∑ i ∈ s, c i * iteratedDeriv n (F i) x := by
  have hfun : (fun y => ∑ i ∈ s, c i * F i y) = ∑ i ∈ s, fun y => c i * F i y := by
    funext y
    rw [Finset.sum_apply]
  rw [hfun, iteratedDeriv_sum (f := fun i y => c i * F i y) (I := s) (x := x)
    (fun i hi => contDiffAt_const.mul (h i hi))]
  exact Finset.sum_congr rfl fun i hi => by
    rw [iteratedDeriv_const_mul _ (h i hi)]

/-! ## Smoothness of partial derivatives of a `C^∞` function of two variables -/

/-- The partial `θ`-derivative `(z,θ) ↦ ∂_θ f(z,θ)` of a `C^∞` function of two
variables is again `C^∞`.  (The `deriv` of the `θ`-slice is by definition the
value of `fderiv` on the second basis vector.) -/
theorem contDiffAt_deriv_slice {f : ℝ → ℝ → ℝ} {z θ : ℝ}
    (h : ContDiffAt ℝ ⊤ (Function.uncurry f) (z, θ)) :
    ContDiffAt ℝ ⊤ (fun p : ℝ × ℝ => deriv (fun y => f p.1 y) p.2) (z, θ) := by
  have hinner : ContDiffAt ℝ ⊤ (fun q : (ℝ × ℝ) × ℝ => (q.1.1, q.2)) ((z, θ), θ) :=
    by fun_prop
  have hfun : ContDiffAt ℝ ⊤ (fun q : (ℝ × ℝ) × ℝ => f q.1.1 q.2) ((z, θ), θ) :=
    ContDiffAt.comp (f := fun q : (ℝ × ℝ) × ℝ => (q.1.1, q.2)) ((z, θ), θ) h hinner
  have h1 : ContDiffWithinAt ℝ ⊤ (Function.uncurry (fun p : ℝ × ℝ => fun y : ℝ => f p.1 y))
      (Set.univ ×ˢ Set.univ) ((z, θ), θ) := by
    rw [Set.univ_prod_univ]
    exact hfun.contDiffWithinAt
  have hmain := ContDiffWithinAt.fderivWithin_apply (m := ⊤) (n := ⊤) (s := Set.univ)
    (t := Set.univ) (f := fun p : ℝ × ℝ => fun y : ℝ => f p.1 y)
    (g := fun p : ℝ × ℝ => p.2) (k := fun _ => (1 : ℝ)) (x₀ := (z, θ)) h1
    (by fun_prop) (by fun_prop) uniqueDiffOn_univ (by simp) (by simp) (by simp)
  have h2 : ContDiffWithinAt ℝ ⊤
      (fun p : ℝ × ℝ => deriv (fun y => f p.1 y) p.2) Set.univ (z, θ) := by
    change ContDiffWithinAt ℝ ⊤
      (fun x : ℝ × ℝ => (fderiv ℝ (fun y => f x.1 y) x.2) 1) Set.univ (z, θ)
    simpa only [fderivWithin_univ] using hmain
  exact contDiffWithinAt_univ.mp h2

/-- Restriction of a `C^∞` function of two variables to a horizontal slice is `C^∞`. -/
theorem contDiffAt_slice_left {f : ℝ → ℝ → ℝ} {z θ : ℝ}
    (h : ContDiffAt ℝ ⊤ (Function.uncurry f) (z, θ)) :
    ContDiffAt ℝ ⊤ (fun z' => f z' θ) z := by
  have hlin : ContDiffAt ℝ ⊤ (fun z' : ℝ => (z', θ)) z := by fun_prop
  exact h.comp z hlin


/-! ## Vanishing of `DthIter` at the angular boundary -/

/-- At a point where `sin (2θ) = 0`, every positive iterate of `D_θ` vanishes. -/
theorem DthIter_succ_eq_zero_of_sin_eq_zero (j : ℕ) (h : ℝ → ℝ → ℝ) {z θ : ℝ}
    (hθ : Real.sin (2 * θ) = 0) : DthIter (j + 1) h z θ = 0 := by
  simp [DthIter_succ, Dth, hθ]

/-- At the two angular endpoints `θ = 0` and `θ = π/2` of `Iθ` the factor `sin (2θ)`
of `D_θ` vanishes. -/
theorem sin_two_mul_eq_zero_of_mem_Iθ_of_not_mem_Ioo {θ : ℝ} (hθ : θ ∈ Iθ)
    (h : θ ∉ Ioo 0 (π / 2)) : Real.sin (2 * θ) = 0 := by
  have hcases : θ = 0 ∨ θ = π / 2 := by
    rcases hθ with ⟨h0, h1⟩
    by_cases hle : θ ≤ 0
    · exact Or.inl (le_antisymm hle h0)
    · have hle' : 0 < θ := not_le.mp hle
      refine Or.inr (le_antisymm h1 ?_)
      by_contra hc
      exact absurd ⟨hle', lt_of_not_ge hc⟩ h
  rcases hcases with rfl | rfl
  · simp
  · rw [show 2 * (π / 2) = π by ring, Real.sin_pi]

/-! ## Elementary consequences of `SmoothInt` -/

/-- `SmoothInt` functions are `C^∞` (jointly in both variables) at every point
lying over the open quadrant. -/
theorem SmoothInt.contDiffAt_uncurry {f : ℝ → ℝ → ℝ} (hf : SmoothInt f) {z θ : ℝ}
    (hz : z ∈ Set.Ioi (-1)) (hθ : θ ∈ Ioo 0 (π / 2)) :
    ContDiffAt ℝ ⊤ (Function.uncurry f) (z, θ) := by
  refine hf.1.contDiffAt ?_
  exact (isOpen_Ioi.prod isOpen_Ioo).mem_nhds (by rw [Set.mem_prod]; exact ⟨hz, hθ⟩)

/-- For fixed `z` over the open quadrant, the `θ`-slice of a `SmoothInt` function is
`C^∞` on `(0, π/2)`. -/
theorem SmoothInt.contDiffOn_theta_slice {f : ℝ → ℝ → ℝ} (hf : SmoothInt f) {z : ℝ}
    (hz : z ∈ Set.Ioi (-1)) :
    ContDiffOn ℝ ⊤ (fun θ => f z θ) (Ioo 0 (π / 2)) := by
  rw [isOpen_Ioo.contDiffOn_iff]
  intro θ hθ
  have h1 : ContDiffAt ℝ ⊤ (Function.uncurry f) (z, θ) := hf.contDiffAt_uncurry hz hθ
  have h2 : ContDiffAt ℝ ⊤ (fun θ' : ℝ => (z, θ')) θ := by fun_prop
  exact h1.comp θ h2


end Work.Spaces
end
end
-- ===== merged: Submission.Work.Spaces.sin_two_rpow =====
section

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

noncomputable section

open scoped Real Topology
open MeasureTheory Set Filter

namespace Work.Spaces

set_option autoImplicit false

theorem sin_two_rpow (p : ℝ) (hp : -1 < p) (hp0 : p ≤ 0) :
    MeasureTheory.IntegrableOn (fun θ : ℝ => (Real.sin (2 * θ)) ^ p) Work.Spaces.Iθ ∧
      ∫ θ in Work.Spaces.Iθ, (Real.sin (2 * θ)) ^ p ≤ 100 / (p + 1) := by
  rcases eq_or_lt_of_le hp0 with hp_eq | hp_lt
  · -- The exponent vanishes: the integrand is the constant `1`.
    subst hp_eq
    constructor
    · simpa only [Real.rpow_zero] using
        (MeasureTheory.integrableOn_const (μ := volume) (s := Work.Spaces.Iθ) (C := (1:ℝ))
          (by rw [Work.Spaces.Iθ, Real.volume_Icc]; exact ENNReal.ofReal_ne_top))
    · have hvol : volume.real Work.Spaces.Iθ = Real.pi / 2 := by
        rw [MeasureTheory.measureReal_def, Work.Spaces.Iθ, Real.volume_Icc,
            ENNReal.toReal_ofReal (by linarith [Real.pi_pos])]
        ring
      have hconst : ∫ θ in Work.Spaces.Iθ, (Real.sin (2 * θ)) ^ (0:ℝ)
          = volume.real Work.Spaces.Iθ := by
        simp only [Real.rpow_zero]
        rw [MeasureTheory.setIntegral_const]
        simp
      rw [hconst, hvol]
      norm_num
      linarith [Real.pi_le_four]
  · -- The exponent is negative: dominate by the integrable majorant.
    set q : ℝ := -p with hq
    have hq0 : 0 < q := by rw [hq]; linarith
    have hq1 : q < 1 := by rw [hq]; linarith
    have hpq : p = -q := by rw [hq]; ring
    -- The majorant, its integrability and its integral.
    have hGint : Integrable (fun θ : ℝ => (Real.pi/4)^q * (θ^(-q) + (Real.pi/2 - θ)^(-q)))
        (volume.restrict Work.Spaces.Iθ) := by
      rw [Work.Spaces.Iθ]; exact Work.Spaces.integrableOn_majorant_rpow q hq0 hq1
    have hGval : ∫ θ in Work.Spaces.Iθ, ((Real.pi/4)^q * (θ^(-q) + (Real.pi/2 - θ)^(-q)))
        = Real.pi * (1/2)^q / (1 - q) := by
      rw [Work.Spaces.Iθ]; exact Work.Spaces.integral_majorant_rpow q hq0 hq1
    -- Nonnegativity of the integrand on `Iθ`.
    have hnonneg : 0 ≤ᵐ[volume.restrict Work.Spaces.Iθ] (fun θ : ℝ => (Real.sin (2*θ))^p) := by
      filter_upwards [ae_restrict_mem measurableSet_Icc] with θ hθ
      exact Real.rpow_nonneg
        (Real.sin_nonneg_of_mem_Icc ⟨by linarith [hθ.1], by linarith [hθ.2, Real.pi_pos]⟩) p
    -- The pointwise majorant `sin(2θ)^p ≤ G θ`.
    have hpoint : (fun θ : ℝ => (Real.sin (2*θ))^p) ≤ᵐ[volume.restrict Work.Spaces.Iθ]
        (fun θ : ℝ => (Real.pi/4)^q * (θ^(-q) + (Real.pi/2 - θ)^(-q))) := by
      filter_upwards [ae_restrict_mem measurableSet_Icc] with θ hθ
      rw [hpq]
      exact Work.Spaces.sin_rpow_le_majorant_pi q θ hq0 hθ
    -- Measurability of the integrand (it is `sin ∘ (· * 2)` raised to a constant power).
    have hmeas : AEStronglyMeasurable (fun θ : ℝ => (Real.sin (2*θ))^p)
        (volume.restrict Work.Spaces.Iθ) :=
      (Measurable.pow_const (Real.measurable_sin.comp (measurable_const.mul measurable_id)) p)
        |>.aestronglyMeasurable
    -- Domination of the norms, as required by `Integrable.mono'`.
    have hnorm : ∀ᵐ θ ∂(volume.restrict Work.Spaces.Iθ),
        ‖(Real.sin (2*θ))^p‖ ≤ (Real.pi/4)^q * (θ^(-q) + (Real.pi/2 - θ)^(-q)) := by
      filter_upwards [hpoint, hnonneg] with θ h1 h2
      rw [Real.norm_of_nonneg h2]
      exact h1
    constructor
    · exact hGint.mono' hmeas hnorm
    · calc ∫ θ in Work.Spaces.Iθ, (Real.sin (2*θ))^p
          ≤ ∫ θ in Work.Spaces.Iθ, ((Real.pi/4)^q * (θ^(-q) + (Real.pi/2 - θ)^(-q))) :=
            integral_mono_of_nonneg hnonneg hGint hpoint
        _ = Real.pi * (1/2)^q / (1 - q) := hGval
        _ ≤ 100 / (p + 1) := by
            rw [hpq]
            rw [show -q + 1 = 1 - q by ring]
            have hpi : Real.pi * (1/2:ℝ)^q ≤ 100 := by
              have h1 : (1/2:ℝ)^q ≤ 1 := Real.rpow_le_one (by norm_num) (by norm_num) (le_of_lt hq0)
              have h2 : Real.pi * (1/2:ℝ)^q ≤ Real.pi * 1 :=
                mul_le_mul_of_nonneg_left h1 (le_of_lt Real.pi_pos)
              linarith [Real.pi_le_four]
            exact div_le_div_of_nonneg_right hpi (by linarith)

end Work.Spaces
end
end
