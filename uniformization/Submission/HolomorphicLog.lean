import ChallengeDeps
import Submission.Holomorphic
import Submission.Conjugate
import Submission.Commons.Analysis.Complex.Analytic.exists_analyticAt_log_of_ne_zero

/-!
# Holomorphic functions on a Riemann surface: constant modulus and logarithms

Two facts about holomorphic functions on a connected complex one-manifold `X` which are used in the
construction of the uniformising map:

* `Submission.HolomorphicOnX.exists_eq_const_of_norm_eq` — a holomorphic function on connected `X`
  with constant modulus is constant (maximum modulus principle in a chart, then connectedness).

* `Submission.HolomorphicOnX.exists_log_of_ne_zero` — a **nowhere vanishing** holomorphic function
  on `X` has a holomorphic logarithm, provided `Hom(π₁(X),ℝ) = 0` (the hypothesis of the
  uniformization theorem).  The proof: `log‖f‖` is harmonic on `X` (locally the real part of a
  logarithm of `f`), hence the real part of a global holomorphic function `H` by
  `Submission.exists_holomorphicOnX_re_of_harmonic`; then `f / exp H` has modulus `1`, hence is
  constant, and `c = f / exp H` has a complex logarithm.
-/

open LeanEval.Geometry
open scoped Manifold ContDiff Topology

set_option linter.unusedSectionVars false

noncomputable section

open Filter Set
open Classical

namespace Submission

variable {X : Type*} [TopologicalSpace X] [ChartedSpace ℂ X]
  [IsManifold (modelWithCornersSelf ℂ ℂ) 1 X]

theorem HolomorphicOnXAt.cexp {f : X → ℂ} {x : X} (hf : HolomorphicOnXAt f x) :
    HolomorphicOnXAt (fun y => Complex.exp (f y)) x := by
  rw [HolomorphicOnXAt] at hf ⊢
  exact AnalyticAt.cexp hf

theorem HolomorphicOnX.cexp {f : X → ℂ} {U : Set X} (hf : HolomorphicOnX f U) :
    HolomorphicOnX (fun y => Complex.exp (f y)) U :=
  fun x hx => (hf x hx).cexp

theorem HolomorphicOnXAt.cexp_neg {f : X → ℂ} {x : X} (hf : HolomorphicOnXAt f x) :
    HolomorphicOnXAt (fun y => Complex.exp (-(f y))) x :=
  hf.neg.cexp

end Submission

namespace Submission

/-- In every ball around `w` there is a point whose norm differs from `‖w‖`. -/
theorem exists_norm_ne_of_mem_ball (w : ℂ) {δ : ℝ} (hδ : 0 < δ) :
    ∃ z ∈ Metric.ball w δ, ‖z‖ ≠ ‖w‖ := by
  by_cases hw : w = 0
  · refine ⟨((δ / 2 : ℝ) : ℂ), ?_, ?_⟩
    · rw [Metric.mem_ball, hw, dist_zero_right, Complex.norm_real]
      rw [Real.norm_eq_abs, abs_of_pos (half_pos hδ)]
      linarith
    · rw [hw, norm_zero, Complex.norm_real, Real.norm_eq_abs, abs_of_pos (half_pos hδ)]
      exact ne_of_gt (half_pos hδ)
  · have hwn : 0 < ‖w‖ := norm_pos_iff.mpr hw
    refine ⟨w * (1 + ((δ / (2 * ‖w‖) : ℝ) : ℂ)), ?_, ?_⟩
    · rw [Metric.mem_ball, dist_eq_norm]
      have hsplit : w * (1 + ((δ / (2 * ‖w‖) : ℝ) : ℂ)) - w
          = w * (((δ / (2 * ‖w‖) : ℝ) : ℂ)) := by ring
      rw [hsplit, norm_mul, Complex.norm_real]
      rw [Real.norm_eq_abs, abs_of_pos (div_pos hδ (by positivity))]
      have hmul : ‖w‖ * (δ / (2 * ‖w‖)) = δ / 2 := by field_simp
      rw [hmul]
      linarith
    · have hcast : (1 : ℂ) + ((δ / (2 * ‖w‖) : ℝ) : ℂ)
            = ((1 + δ / (2 * ‖w‖) : ℝ) : ℂ) := by
        push_cast; ring
      have hnorm : ‖w * (1 + ((δ / (2 * ‖w‖) : ℝ) : ℂ))‖
            = ‖w‖ * (1 + δ / (2 * ‖w‖)) := by
        rw [norm_mul, hcast, Complex.norm_real, Real.norm_eq_abs, abs_of_pos (by positivity)]
      rw [hnorm]
      have hmul : ‖w‖ * (1 + δ / (2 * ‖w‖)) = ‖w‖ + δ / 2 := by
        field_simp
      rw [hmul]
      have hpos : 0 < δ / (2 * ‖w‖) := div_pos hδ (by positivity)
      linarith

end Submission

namespace Submission

variable {X : Type*} [TopologicalSpace X] [T2Space X] [ChartedSpace ℂ X]
  [IsManifold (modelWithCornersSelf ℂ ℂ) 1 X]

/-- **Local constancy of a holomorphic function with eventually constant modulus.** -/
theorem HolomorphicOnXAt.eventually_eq_const_of_eventually_norm_eq {f : X → ℂ} {x : X}
    (hf : HolomorphicOnXAt f x) {c : ℝ} (hc : ∀ᶠ y in 𝓝 x, ‖f y‖ = c) :
    ∀ᶠ y in 𝓝 x, f y = f x := by
  set e : OpenPartialHomeomorph X ℂ := chartAt ℂ x with he
  set a : ℂ := e x with ha
  have hsrc : x ∈ e.source := mem_chart_source ℂ x
  have hmem : a ∈ e.target := e.map_source hsrc
  have hsymm : e.symm a = x := e.left_inv hsrc
  have hc' : ∀ᶠ z in 𝓝 a, ‖(f ∘ e.symm) z‖ = c := by
    have hpre : {y : X | ‖f y‖ = c} ∈ 𝓝 x := hc
    have h2 : e.symm ⁻¹' {y : X | ‖f y‖ = c} ∈ 𝓝 a :=
      (e.continuousAt_symm hmem).preimage_mem_nhds (by rw [hsymm]; exact hpre)
    filter_upwards [h2] with z hz
    exact hz
  have hga : AnalyticAt ℂ (f ∘ e.symm) a := hf
  rcases hga.eventually_constant_or_nhds_le_map_nhds with hconst | hopen
  · -- eventually constant at `a`: pull back to `x`
    have hpre : {z : ℂ | (f ∘ e.symm) z = (f ∘ e.symm) a} ∈ 𝓝 a := hconst
    have hnb : e ⁻¹' {z : ℂ | (f ∘ e.symm) z = (f ∘ e.symm) a} ∩ e.source ∈ 𝓝 x :=
      Filter.inter_mem ((e.continuousAt hsrc).preimage_mem_nhds hpre) (e.open_source.mem_nhds hsrc)
    filter_upwards [hnb] with y hy
    have hr : e.symm (e y) = y := e.left_inv hy.2
    calc f y = (f ∘ e.symm) (e y) := by rw [Function.comp_apply, hr]
      _ = (f ∘ e.symm) a := hy.1
      _ = f x := by rw [Function.comp_apply, hsymm]
  · -- open mapping: the image of the modulus-constancy set contains a ball
    exfalso
    have hU : {z : ℂ | ‖(f ∘ e.symm) z‖ = c} ∈ 𝓝 a := hc'
    have hpre : (f ∘ e.symm) ⁻¹' ((f ∘ e.symm) '' {z : ℂ | ‖(f ∘ e.symm) z‖ = c}) ∈ 𝓝 a :=
      Filter.mem_of_superset hU (fun z hz => ⟨z, hz, rfl⟩)
    have himg : (f ∘ e.symm) '' {z : ℂ | ‖(f ∘ e.symm) z‖ = c} ∈ 𝓝 ((f ∘ e.symm) a) := by
      rw [Filter.le_def] at hopen
      exact hopen _ hpre
    obtain ⟨δ, hδ, hδsub⟩ := Metric.mem_nhds_iff.mp himg
    obtain ⟨z, hz, hzne⟩ := exists_norm_ne_of_mem_ball ((f ∘ e.symm) a) hδ
    obtain ⟨z₀, hz₀, hz0eq⟩ := hδsub hz
    have ha_c : ‖(f ∘ e.symm) a‖ = c := hc'.self_of_nhds
    rw [← hz0eq] at hzne
    exact hzne (hz₀.trans ha_c.symm)

end Submission

namespace Submission

variable {X : Type*} [TopologicalSpace X] [T2Space X] [ConnectedSpace X] [ChartedSpace ℂ X]
  [IsManifold (modelWithCornersSelf ℂ ℂ) 1 X]

/-- **A holomorphic function on connected `X` with constant modulus is constant.** -/
theorem HolomorphicOnX.exists_eq_const_of_norm_eq {f : X → ℂ} (hf : HolomorphicOnX f univ)
    (x₀ : X) (hconst : ∀ y : X, ‖f y‖ = ‖f x₀‖) : ∀ y : X, f y = f x₀ := by
  have hcont : Continuous f := hf.continuous
  have hSclosed : IsClosed {y : X | f y = f x₀} := isClosed_eq hcont continuous_const
  have hSopen : IsOpen {y : X | f y = f x₀} := by
    rw [isOpen_iff_mem_nhds]
    intro y hy
    have hev : ∀ᶠ z in 𝓝 y, f z = f y :=
      HolomorphicOnXAt.eventually_eq_const_of_eventually_norm_eq (hf y (mem_univ y))
        (Filter.Eventually.of_forall fun z => (hconst z).trans (hconst y).symm)
    filter_upwards [hev] with z hz
    rw [hz, hy]
  have : (Set.univ : Set X) ⊆ {y : X | f y = f x₀} :=
    isPreconnected_univ.subset_isClopen ⟨hSclosed, hSopen⟩ ⟨x₀, Set.mem_univ x₀, rfl⟩
  intro y
  exact this (Set.mem_univ y)

end Submission

namespace Submission

variable {X : Type*} [TopologicalSpace X] [T2Space X] [ConnectedSpace X] [ChartedSpace ℂ X]
  [IsManifold (modelWithCornersSelf ℂ ℂ) 1 X]

/-- `log ‖f‖` is harmonic on `X` for a nowhere vanishing holomorphic `f`. -/
theorem harmonicOnX_log_norm {f : X → ℂ} (hf : HolomorphicOnX f univ) (hne : ∀ y, f y ≠ 0) :
    HarmonicOnX (fun y => Real.log ‖f y‖) univ := by
  intro x _
  rw [HarmonicOnXAt]
  have hxsrc : x ∈ (chartAt ℂ x).source := mem_chart_source ℂ x
  have hmem : (chartAt ℂ x) x ∈ (chartAt ℂ x).target := (chartAt ℂ x).map_source hxsrc
  have hfx : HolomorphicOnXAt f x := hf x (mem_univ x)
  rw [HolomorphicOnXAt] at hfx
  obtain ⟨ρ, hρ, hsub⟩ := Metric.mem_nhds_iff.mp
    ((chartAt ℂ x).open_target.mem_nhds hmem)
  have hane : f ((chartAt ℂ x).symm ((chartAt ℂ x) x)) ≠ 0 :=
    hne ((chartAt ℂ x).symm ((chartAt ℂ x) x))
  have _hcontne : ∀ᶠ z in nhds ((chartAt ℂ x) x), f ((chartAt ℂ x).symm z) ≠ 0 := by
    have hc : ContinuousAt (fun z => f ((chartAt ℂ x).symm z)) ((chartAt ℂ x) x) :=
      hfx.continuousAt
    exact hc.eventually_ne hane
  have hanaAt : AnalyticAt ℂ (fun z => f ((chartAt ℂ x).symm z)) ((chartAt ℂ x) x) := hfx
  obtain ⟨g, hgana, hgeq⟩ :=
    Commons.Analysis.Complex.Analytic.exists_analyticAt_log_of_ne_zero hanaAt hane
  have heq : (fun y => Real.log ‖f y‖) ∘ (chartAt ℂ x).symm =ᶠ[𝓝 ((chartAt ℂ x) x)]
      fun z => (g z).re := by
    filter_upwards [hgeq] with z hz
    rw [Function.comp_apply, hz, Complex.norm_exp, Real.log_exp]
  exact (InnerProductSpace.harmonicAt_congr_nhds heq).mpr (hgana.harmonicAt_re)

/-- **Every nowhere vanishing holomorphic function on `X` has a holomorphic logarithm**, under the
hypothesis `Hom(π₁(X),ℝ) = 0` of the uniformization theorem. -/
theorem HolomorphicOnX.exists_log_of_ne_zero (x₀ : X)
    [Subsingleton (Additive (FundamentalGroup X x₀) →+ ℝ)]
    {f : X → ℂ} (hf : HolomorphicOnX f univ) (hne : ∀ y, f y ≠ 0) :
    ∃ H : X → ℂ, HolomorphicOnX H univ ∧ ∀ y, f y = Complex.exp (H y) := by
  obtain ⟨G, hGhol, hGre⟩ :=
    exists_holomorphicOnX_re_of_harmonic x₀ (harmonicOnX_log_norm hf hne)
  have hnegG : HolomorphicOnX (fun y : X => -(G y)) univ := fun x hx => (hGhol x hx).neg
  have hexpG : HolomorphicOnX (fun y => Complex.exp (-(G y))) univ := hnegG.cexp
  have hFhol : HolomorphicOnX (fun y => f y * Complex.exp (-(G y))) univ := hf.mul hexpG
  have hFnorm : ∀ y : X, ‖f y * Complex.exp (-(G y))‖ = ‖f x₀ * Complex.exp (-(G x₀))‖ := by
    intro y
    have h1 : ‖Complex.exp (-(G y))‖ = Real.exp (-(G y).re) := Complex.norm_exp _
    have h2 : ‖Complex.exp (-(G x₀))‖ = Real.exp (-(G x₀).re) := Complex.norm_exp _
    have hy : Real.log ‖f y‖ = (G y).re := (hGre y).symm
    have hx : Real.log ‖f x₀‖ = (G x₀).re := (hGre x₀).symm
    have h3 : 0 < ‖f y‖ := norm_pos_iff.mpr (hne y)
    have h4 : 0 < ‖f x₀‖ := norm_pos_iff.mpr (hne x₀)
    have e1 : ‖f y‖ = Real.exp ((G y).re) := by rw [← hy]; exact (Real.exp_log h3).symm
    have e2 : ‖f x₀‖ = Real.exp ((G x₀).re) := by rw [← hx]; exact (Real.exp_log h4).symm
    rw [norm_mul, norm_mul, h1, h2, e1, e2]
    simp only [Complex.neg_re, Real.exp_neg]
    field_simp
  have hFconst : ∀ y : X, f y * Complex.exp (-(G y)) = f x₀ * Complex.exp (-(G x₀)) :=
    hFhol.exists_eq_const_of_norm_eq x₀ hFnorm
  refine ⟨fun y => G y + Complex.log (f x₀ * Complex.exp (-(G x₀))), ?_, ?_⟩
  · exact hGhol.add (holomorphicOnX_const _)
  · intro y
    have hc : f x₀ * Complex.exp (-(G x₀)) ≠ 0 := by
      have hpos : 0 < ‖f x₀ * Complex.exp (-(G x₀))‖ := by
        rw [norm_mul]
        exact mul_pos (norm_pos_iff.mpr (hne x₀)) (norm_pos_iff.mpr (Complex.exp_ne_zero _))
      intro h
      rw [h, norm_zero] at hpos
      exact lt_irrefl (0 : ℝ) hpos
    have hexp : Complex.exp (-(G y)) * Complex.exp (G y) = 1 := by
      rw [← Complex.exp_add, neg_add_cancel, Complex.exp_zero]
    have h1 : f y = (f x₀ * Complex.exp (-(G x₀))) * Complex.exp (G y) := by
      have h := congrArg (fun z : ℂ => z * Complex.exp (G y)) (hFconst y)
      rw [mul_assoc (f y), hexp, mul_one] at h
      exact h
    rw [Complex.exp_add, Complex.exp_log hc]
    calc f y = (f x₀ * Complex.exp (-(G x₀))) * Complex.exp (G y) := h1
      _ = Complex.exp (G y) * (f x₀ * Complex.exp (-(G x₀))) := by rw [mul_comm]

end Submission
