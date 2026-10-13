/-
Copyright: work module for the Elgindi finite-time singularity project.

# The integration by parts identity behind the cut-off Agmon estimate

With `ρ = w²` (`Work.Spaces.w z = (1+z)²/z²`), `cutU h ψ = ρ z ψ² (z h')` and
`cutF h ψ = ρ ψ² (z h')² = cutU h ψ · h'` (see `AgmonSlice.CutDefs`), and a cut-off `ψ`
vanishing on `(0,a] ∪ [b,∞)` with `0 < a < b`, we prove

  `∫_0^∞ cutF h ψ = -∫_0^∞ (cutU h ψ)' · h`

together with the integrability of both sides.  Since `ψ` vanishes outside `(a,b)`, both
`cutU h ψ` and `cutU h ψ · h` are compactly supported in `(a,b) ⊂ (0,∞)`, so both boundary
terms of the integration by parts vanish; the identity then follows from
`MeasureTheory.integral_Ioi_mul_deriv_eq_deriv_mul` (integration by parts for improper
integrals over `(a,∞)`) applied to `u = cutU h ψ` and `v = h`.

The integrability is obtained by noticing that both integrands vanish off the compact
interval `[a,b]` and are continuous there.
-/
import Mathlib.Algebra.Ring.IsFormallyReal
import Mathlib.MeasureTheory.Integral.IntegralEqImproper
import Mathlib.Order.CompletePartialOrder
import Submission.Work.FTS.EllipticEst.AgmonSlice.CutDefs
import Submission.Work.Spaces.Defs

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

noncomputable section

open scoped Real Topology
open MeasureTheory Set Filter

namespace Work.FTS.EllipticEst.AgmonFts

theorem cut_IBP (h ψ : ℝ → ℝ) (a b : ℝ) (ha : 0 < a) (hab : a < b)
    (hh : ContDiffOn ℝ 2 h (Set.Ioi 0)) (hψ : ContDiffOn ℝ 2 ψ (Set.Ioi 0))
    (hψsupp : ∀ z : ℝ, 0 < z → z ≤ a ∨ b ≤ z → ψ z = 0) :
    MeasureTheory.IntegrableOn (Work.FTS.EllipticEst.AgmonSlice.cutF h ψ) (Set.Ioi 0) ∧
      MeasureTheory.IntegrableOn
        (fun z => deriv (Work.FTS.EllipticEst.AgmonSlice.cutU h ψ) z * h z) (Set.Ioi 0) ∧
      (∫ z in Set.Ioi (0 : ℝ), Work.FTS.EllipticEst.AgmonSlice.cutF h ψ z)
        = -(∫ z in Set.Ioi (0 : ℝ),
            deriv (Work.FTS.EllipticEst.AgmonSlice.cutU h ψ) z * h z) := by
  -- `[a,b]` sits inside the half-line on which `h` and `ψ` are differentiable
  have hsub : Set.Icc a b ⊆ Set.Ioi (0 : ℝ) := fun x hx => by
    simp only [Set.mem_Ioi]; linarith [hx.1, ha]
  -- a point of `(0,∞) \ [a,b]` lies to the left of `a` or to the right of `b`
  have hsplit : ∀ x : ℝ, x ∈ Set.Ioi (0 : ℝ) \ Set.Icc a b → x < a ∨ b < x := by
    intro x hx
    have h2 := hx.2
    simp only [Set.mem_Icc, not_and_or, not_le] at h2
    exact h2
  -- `ρ = w²` is smooth (hence `C¹`) on `(0,∞)`
  have hrhoCont : ContDiffOn ℝ 1 Work.FTS.EllipticEst.AgmonSlice.cutRho (Set.Ioi 0) := by
    have h1 : ContDiffOn ℝ 1 (fun z : ℝ => (1 + z) ^ 2 / z ^ 2) (Set.Ioi 0) := by
      apply ContDiffOn.div
      · fun_prop
      · fun_prop
      · intro z hz; exact pow_ne_zero 2 (ne_of_gt hz)
    exact h1.pow 2
  -- `cutU h ψ = ρ z ψ² (z h')` is `C¹` on `(0,∞)`
  have hC1 : ContDiffOn ℝ 1 (Work.FTS.EllipticEst.AgmonSlice.cutU h ψ) (Set.Ioi 0) := by
    have hψ1 : ContDiffOn ℝ 1 ψ (Set.Ioi 0) := hψ.of_le (by norm_num)
    have hdh : ContDiffOn ℝ 1 (deriv h) (Set.Ioi 0) :=
      hh.deriv_of_isOpen isOpen_Ioi (by norm_num)
    have h2 : ContDiffOn ℝ 1 (fun z : ℝ => z * deriv h z) (Set.Ioi 0) :=
      contDiffOn_id.mul hdh
    have h3 : ContDiffOn ℝ 1 (fun z : ℝ => ψ z ^ 2) (Set.Ioi 0) := hψ1.pow 2
    exact ((hrhoCont.mul contDiffOn_id).mul h3).mul h2
  have hcdU : ContinuousOn (deriv (Work.FTS.EllipticEst.AgmonSlice.cutU h ψ)) (Set.Icc a b) :=
    (hC1.continuousOn_deriv_of_isOpen isOpen_Ioi (by norm_num)).mono hsub
  have hch : ContinuousOn h (Set.Icc a b) := hh.continuousOn.mono hsub
  have hcdh : ContinuousOn (deriv h) (Set.Icc a b) :=
    (hh.continuousOn_deriv_of_isOpen isOpen_Ioi (by norm_num)).mono hsub
  -- the two integrands vanish off `[a,b]`
  have hvanishF : ∀ z, 0 < z → (z < a ∨ b < z) →
      Work.FTS.EllipticEst.AgmonSlice.cutF h ψ z = 0 := by
    intro z hz hc
    have hψz : ψ z = 0 := by
      rcases hc with h' | h'
      · exact hψsupp z hz (Or.inl (le_of_lt h'))
      · exact hψsupp z hz (Or.inr (le_of_lt h'))
    simp only [Work.FTS.EllipticEst.AgmonSlice.cutF, hψz]; ring
  have hvanishdU : ∀ z, 0 < z → (z < a ∨ b < z) →
      deriv (Work.FTS.EllipticEst.AgmonSlice.cutU h ψ) z = 0 := by
    intro z hz hc
    -- `cutU h ψ` vanishes in a whole neighbourhood of `z`, hence so does its derivative
    have hev : Work.FTS.EllipticEst.AgmonSlice.cutU h ψ =ᶠ[𝓝 z] (fun _ => (0 : ℝ)) := by
      rcases hc with h' | h'
      · filter_upwards
          [isOpen_Ioo.mem_nhds (show z ∈ Set.Ioo 0 a from ⟨hz, h'⟩)] with y hy
        simp only [Work.FTS.EllipticEst.AgmonSlice.cutU,
          hψsupp y hy.1 (Or.inl (le_of_lt hy.2))]
        ring
      · filter_upwards
          [isOpen_Ioo.mem_nhds (show z ∈ Set.Ioo b (z + 1) from ⟨h', by linarith⟩)] with y hy
        simp only [Work.FTS.EllipticEst.AgmonSlice.cutU,
          hψsupp y (by linarith [hy.1]) (Or.inr (le_of_lt hy.1))]
        ring
    rw [hev.deriv_eq]; simp
  -- `cutF h ψ` is continuous on `[a,b]`
  have hcF : ContinuousOn (Work.FTS.EllipticEst.AgmonSlice.cutF h ψ) (Set.Icc a b) := by
    have hrho_c : ContinuousOn Work.FTS.EllipticEst.AgmonSlice.cutRho (Set.Icc a b) :=
      hrhoCont.continuousOn.mono hsub
    have hψ2_c : ContinuousOn (fun z : ℝ => ψ z ^ 2) (Set.Icc a b) :=
      (hψ.continuousOn.mono hsub).pow 2
    have hz2_c : ContinuousOn (fun z : ℝ => (z * deriv h z) ^ 2) (Set.Icc a b) :=
      (continuousOn_id.mul hcdh).pow 2
    exact (hrho_c.mul hψ2_c).mul hz2_c
  -- integrability of the two sides
  have hIntF : MeasureTheory.IntegrableOn (Work.FTS.EllipticEst.AgmonSlice.cutF h ψ)
      (Set.Ioi 0) :=
    (hcF.integrableOn_compact isCompact_Icc).of_forall_sdiff_eq_zero measurableSet_Ioi
      (fun x hx => hvanishF x hx.1 (hsplit x hx))
  have hintUV : MeasureTheory.IntegrableOn
      (fun x => Work.FTS.EllipticEst.AgmonSlice.cutU h ψ x * deriv h x) (Set.Ioi 0) :=
    hIntF.congr_fun (fun x _ => (Work.FTS.EllipticEst.AgmonSlice.cutU_mul_deriv h ψ x).symm)
      measurableSet_Ioi
  have hIntdU : MeasureTheory.IntegrableOn
      (fun x => deriv (Work.FTS.EllipticEst.AgmonSlice.cutU h ψ) x * h x) (Set.Ioi 0) :=
    ((hcdU.mul hch).integrableOn_compact isCompact_Icc).of_forall_sdiff_eq_zero measurableSet_Ioi
      (fun x hx => by rw [Pi.mul_apply, hvanishdU x hx.1 (hsplit x hx), zero_mul])
  refine ⟨hIntF, hIntdU, ?_⟩
  simp only [← Work.FTS.EllipticEst.AgmonSlice.cutU_mul_deriv]
  -- integration by parts on `(0,∞)`; both boundary terms vanish since `ψ` is supported in `[a,b]`
  rw [MeasureTheory.integral_Ioi_mul_deriv_eq_deriv_mul (a := 0) (a' := 0) (b' := 0)
    (u := Work.FTS.EllipticEst.AgmonSlice.cutU h ψ) (v := h)
    (u' := deriv (Work.FTS.EllipticEst.AgmonSlice.cutU h ψ)) (v' := deriv h)
    (fun x hx => ((hC1.differentiableOn (by norm_num)).differentiableAt
        (isOpen_Ioi.mem_nhds hx)).hasDerivAt)
    (fun x hx => ((hh.differentiableOn (by norm_num)).differentiableAt
        (isOpen_Ioi.mem_nhds hx)).hasDerivAt)
    hintUV hIntdU
    (by
      have hev : (fun x => Work.FTS.EllipticEst.AgmonSlice.cutU h ψ x * h x)
          =ᶠ[𝓝[>] (0 : ℝ)] (fun _ => (0 : ℝ)) := by
        filter_upwards [Ioo_mem_nhdsGT ha] with x hx
        simp only [Work.FTS.EllipticEst.AgmonSlice.cutU,
          hψsupp x hx.1 (Or.inl (le_of_lt hx.2))]
        ring
      exact tendsto_const_nhds.congr' hev.symm)
    (by
      have hev : (fun x => Work.FTS.EllipticEst.AgmonSlice.cutU h ψ x * h x)
          =ᶠ[atTop] (fun _ => (0 : ℝ)) := by
        filter_upwards [eventually_ge_atTop b] with x hx
        have hx0 : 0 < x := lt_of_lt_of_le (lt_trans ha hab) hx
        simp only [Work.FTS.EllipticEst.AgmonSlice.cutU, hψsupp x hx0 (Or.inr hx)]
        ring
      exact tendsto_const_nhds.congr' hev.symm)]
  ring

end Work.FTS.EllipticEst.AgmonFts
