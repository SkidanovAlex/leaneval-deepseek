import Mathlib
import Submission.Work.C17I.defs
import Submission.Work.C17f.differentiableOn_of_hasSum_powSeries
import Submission.Work.C17f.deriv_hasSum_powSeries

/-!
# The chain rule for `Φ = P ∘ φ` at a point of the lens

This file proves `Work.C17I.phi_chain_rule`: if `P` is the analytic function given by the
unlikely series `Σ cₙ zⁿ` on the disc `‖z‖ < x_s`, and `φ z = z/(z-1)` is the Möbius
involution, then at every point `z ≠ 1` of the lens `{z | ‖φ z‖ < x_s}` the composition
`Φ = P ∘ φ` is twice differentiable and

* `Φ' z = P'(φ z) · (-(1/(z-1)²))`,
* `Φ'' z = P''(φ z)/(z-1)⁴ + 2·P'(φ z)/(z-1)³`.

The first identity is the ordinary chain rule; the second is the chain rule applied to
`(P' ∘ φ) · φ'`, using `φ' z = -(1/(z-1)²)` and `φ'' z = 2/(z-1)³`.

The analyticity of `P` and of `P'` on the disc comes from the two `C17f` modules: a pointwise
convergent power series is differentiable on its disc of convergence
(`Work.C17f.differentiableOn_of_hasSum_powSeries`), and the derivative series again converges
pointwise (`Work.C17f.deriv_hasSum_powSeries`).
-/

namespace Work.C17I

open Filter
open scoped Topology

noncomputable section

/-- `φ z = z/(z-1)` has derivative `-(1/(z-1)²)` at every `z ≠ 1`. -/
lemma hasDerivAt_sw (w : ℂ) (hw : w ≠ 1) :
    HasDerivAt (Work.C17I.sw) (-(1 / (w - 1) ^ 2)) w := by
  have h1 : HasDerivAt (fun u : ℂ => u) 1 w := hasDerivAt_id w
  have h2 : HasDerivAt (fun u : ℂ => u - 1) 1 w := h1.sub_const 1
  have h3 : HasDerivAt (fun u : ℂ => (u - 1)⁻¹) (-(1) / (w - 1) ^ 2) w :=
    h2.inv (by simpa using sub_ne_zero.mpr hw)
  have h4 := h1.mul h3
  have hv : (1 * (w - 1)⁻¹ + w * (-(1) / (w - 1) ^ 2)) = -(1 / (w - 1) ^ 2) := by
    rw [one_mul]
    field_simp
    ring
  rw [hv] at h4
  have hfe : Work.C17I.sw = (fun u : ℂ => u) * (fun u : ℂ => (u - 1)⁻¹) := rfl
  rw [hfe]
  exact h4

/-- Away from `1`, the derivative of `φ` is again the rational function `-(1/(z-1)²)`, whose
derivative at `w ≠ 1` is `2/(w-1)³`. -/
lemma hasDerivAt_deriv_sw (w : ℂ) (hw : w ≠ 1) :
    HasDerivAt (deriv Work.C17I.sw) (2 / (w - 1) ^ 3) w := by
  have hw' : w - 1 ≠ 0 := sub_ne_zero.mpr hw
  have hbase : HasDerivAt (fun u : ℂ => -(((u - 1) * (u - 1))⁻¹)) (2 / (w - 1) ^ 3) w := by
    have h2 : HasDerivAt (fun u : ℂ => u - 1) 1 w := (hasDerivAt_id w).sub_const 1
    have h3 : HasDerivAt (fun u : ℂ => (u - 1) * (u - 1)) (2 * (w - 1)) w := by
      have hp := h2.mul h2
      have hv : (1 * (w - 1) + (w - 1) * 1) = 2 * (w - 1) := by ring
      rw [hv] at hp
      have hfe : (fun u : ℂ => (u - 1) * (u - 1))
          = (fun u : ℂ => u - 1) * (fun u : ℂ => u - 1) := rfl
      rw [hfe]
      exact hp
    have h4 : HasDerivAt (fun u : ℂ => ((u - 1) * (u - 1))⁻¹)
        (-(2 * (w - 1)) / ((w - 1) * (w - 1)) ^ 2) w :=
      h3.inv (mul_ne_zero hw' hw')
    have h5 := h4.neg
    have hv : -(-(2 * (w - 1)) / ((w - 1) * (w - 1)) ^ 2) = 2 / (w - 1) ^ 3 := by
      field_simp
    rw [hv] at h5
    exact h5
  refine hbase.congr_of_eventuallyEq ?_
  filter_upwards [isOpen_ne.mem_nhds hw] with u hu
  rw [(hasDerivAt_sw u hu).deriv]
  simp [pow_two, div_eq_mul_inv]

/-- The second-order chain rule for complex functions: if `f` is differentiable at `g z`,
`deriv f` is differentiable at `g z`, `g` and `deriv g` are differentiable at `z`, and
`f ∘ g` is differentiable near `z`, then

`(f ∘ g)'' z = f''(g z)·(g' z)² + f'(g z)·g'' z`. -/
lemma deriv_comp_two {f g : ℂ → ℂ} {z : ℂ}
    (h : ∀ᶠ w in 𝓝 z, DifferentiableAt ℂ f (g w) ∧ DifferentiableAt ℂ g w)
    (hdf : DifferentiableAt ℂ (deriv f) (g z)) (hg : DifferentiableAt ℂ g z)
    (hdg : DifferentiableAt ℂ (deriv g) z) :
    deriv (deriv (f ∘ g)) z =
      deriv (deriv f) (g z) * (deriv g z) ^ 2 + deriv f (g z) * deriv (deriv g) z := by
  have hev : deriv (f ∘ g) =ᶠ[𝓝 z] fun w => deriv f (g w) * deriv g w := by
    filter_upwards [h] with w hw
    exact deriv_comp (x := w) hw.1 hw.2
  rw [Filter.EventuallyEq.deriv_eq hev]
  have hcd : (fun w : ℂ => deriv f (g w) * deriv g w)
      = (fun w : ℂ => deriv f (g w)) * deriv g := rfl
  rw [hcd, deriv_mul (c := fun w => deriv f (g w)) (d := deriv g) (hdf.comp z hg) hdg]
  have hA : deriv (fun w => deriv f (g w)) z = deriv (deriv f) (g z) * deriv g z := by
    have hh := deriv_comp (x := z) hdf hg
    simpa [Function.comp_def] using hh
  rw [hA]
  ring

theorem phi_chain_rule (a b : ℚ) (ra rb rab r0 : ℤ)
    (hconv : ∀ z : ℂ, ‖z‖ < Work.C17.xs a b →
      HasSum (fun n : ℕ => ((PowerSeries.coeff n (Submission.CDT.logP a b ra rb rab r0) : ℚ) : ℂ) * z ^ n)
        (Work.C17.Pfun a b ra rb rab r0 z))
    (z : ℂ) (hz1 : z ≠ 1) (hz : ‖Work.C17I.sw z‖ < Work.C17.xs a b) :
    DifferentiableAt ℂ (Work.C17I.PhiC a b ra rb rab r0) z ∧
    deriv (Work.C17I.PhiC a b ra rb rab r0) z
        = deriv (Work.C17.Pfun a b ra rb rab r0) (Work.C17I.sw z) * (-(1 / (z - 1) ^ 2)) ∧
    DifferentiableAt ℂ (deriv (Work.C17I.PhiC a b ra rb rab r0)) z ∧
    deriv (deriv (Work.C17I.PhiC a b ra rb rab r0)) z
        = deriv (deriv (Work.C17.Pfun a b ra rb rab r0)) (Work.C17I.sw z) / (z - 1) ^ 4
          + 2 * deriv (Work.C17.Pfun a b ra rb rab r0) (Work.C17I.sw z) / (z - 1) ^ 3 := by
  have hmem : Work.C17I.sw z ∈ Metric.ball (0 : ℂ) (Work.C17.xs a b) := by
    simpa [Metric.mem_ball, dist_zero_right] using hz
  -- `P` and `P'` are analytic on the disc of convergence of the unlikely series
  have hdiffOn_f : DifferentiableOn ℂ (Work.C17.Pfun a b ra rb rab r0)
      (Metric.ball 0 (Work.C17.xs a b)) :=
    Work.C17f.differentiableOn_of_hasSum_powSeries hconv
  have hd1 := Work.C17f.deriv_hasSum_powSeries
      (fun n : ℕ => ((PowerSeries.coeff n (Submission.CDT.logP a b ra rb rab r0) : ℚ) : ℂ))
      (Work.C17.xs a b) (Work.C17.Pfun a b ra rb rab r0) hconv
  have hdiffOn_df : DifferentiableOn ℂ (deriv (Work.C17.Pfun a b ra rb rab r0))
      (Metric.ball 0 (Work.C17.xs a b)) :=
    Work.C17f.differentiableOn_of_hasSum_powSeries
      (c := fun n => ((n : ℂ) + 1) *
        ((PowerSeries.coeff (n + 1) (Submission.CDT.logP a b ra rb rab r0) : ℚ) : ℂ))
      (F := deriv (Work.C17.Pfun a b ra rb rab r0)) hd1
  -- the derivatives of `φ`
  have hsw : HasDerivAt (Work.C17I.sw) (-(1 / (z - 1) ^ 2)) z := hasDerivAt_sw z hz1
  have hg_at : DifferentiableAt ℂ (Work.C17I.sw) z := hsw.differentiableAt
  have hdg_at : DifferentiableAt ℂ (deriv (Work.C17I.sw)) z :=
    (hasDerivAt_deriv_sw z hz1).differentiableAt
  have hf_at : DifferentiableAt ℂ (Work.C17.Pfun a b ra rb rab r0) (Work.C17I.sw z) :=
    hdiffOn_f.differentiableAt (Metric.isOpen_ball.mem_nhds hmem)
  have hdf_at : DifferentiableAt ℂ (deriv (Work.C17.Pfun a b ra rb rab r0)) (Work.C17I.sw z) :=
    hdiffOn_df.differentiableAt (Metric.isOpen_ball.mem_nhds hmem)
  -- both ingredients stay analytic in a whole neighbourhood of `z`
  have hEvF : ∀ᶠ w in 𝓝 z,
      DifferentiableAt ℂ (Work.C17.Pfun a b ra rb rab r0) (Work.C17I.sw w) := by
    filter_upwards [hg_at.continuousAt.tendsto.eventually (Metric.isOpen_ball.mem_nhds hmem)]
      with w hw
    exact hdiffOn_f.differentiableAt (Metric.isOpen_ball.mem_nhds hw)
  have hEvG : ∀ᶠ w in 𝓝 z, DifferentiableAt ℂ (Work.C17I.sw) w := by
    filter_upwards [(isOpen_ne (x := (1 : ℂ))).mem_nhds hz1] with w hw
    exact (hasDerivAt_sw w hw).differentiableAt
  have hev : ∀ᶠ w in 𝓝 z, DifferentiableAt ℂ (Work.C17.Pfun a b ra rb rab r0) (Work.C17I.sw w)
      ∧ DifferentiableAt ℂ (Work.C17I.sw) w := hEvF.and hEvG
  have hPhi_eq : Work.C17I.PhiC a b ra rb rab r0
      = Work.C17.Pfun a b ra rb rab r0 ∘ Work.C17I.sw := rfl
  have hev2 : deriv (Work.C17I.PhiC a b ra rb rab r0) =ᶠ[𝓝 z]
      fun w => deriv (Work.C17.Pfun a b ra rb rab r0) (Work.C17I.sw w) * deriv (Work.C17I.sw) w := by
    filter_upwards [hev] with w hw
    rw [hPhi_eq]
    exact deriv_comp (h := Work.C17I.sw) (h₂ := Work.C17.Pfun a b ra rb rab r0) (x := w) hw.1 hw.2
  refine ⟨?_, ?_, ?_, ?_⟩
  · -- `Φ` is differentiable at `z`
    rw [hPhi_eq]
    exact hf_at.comp z hg_at
  · -- first derivative
    rw [hPhi_eq]
    have h := deriv_comp (h := Work.C17I.sw) (h₂ := Work.C17.Pfun a b ra rb rab r0)
      (x := z) hf_at hg_at
    rw [h, hsw.deriv]
  · -- `Φ'` is differentiable at `z`
    exact (hev2.differentiableAt_iff).mpr ((hdf_at.comp z hg_at).mul hdg_at)
  · -- second derivative
    have hkey := deriv_comp_two (f := Work.C17.Pfun a b ra rb rab r0) (g := Work.C17I.sw)
      (z := z) hev hdf_at hg_at hdg_at
    rw [hPhi_eq, hkey, hsw.deriv, (hasDerivAt_deriv_sw z hz1).deriv]
    field_simp

end

end Work.C17I
