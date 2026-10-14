import Mathlib.Algebra.Order.Star.Real
import Mathlib.Algebra.Ring.IsFormallyReal
import Mathlib.Analysis.Calculus.ContDiff.Defs
import Mathlib.Analysis.InnerProductSpace.Basic
import Mathlib.Analysis.LocallyConvex.AbsConvexOpen
import Mathlib.Analysis.SpecialFunctions.Pow.Deriv
import Mathlib.Analysis.SpecialFunctions.Trigonometric.Basic
import Mathlib.MeasureTheory.Integral.Bochner.Basic
import Mathlib.MeasureTheory.Integral.Bochner.Set
import Mathlib.MeasureTheory.Integral.IntegrableOn
import Mathlib.MeasureTheory.Measure.Haar.OfBasis
import Mathlib.Order.CompletePartialOrder
import Mathlib.Topology.Algebra.Module.ModuleTopology
import Submission.Work.FTS.EllipticEst.remov.slice_gprime_ident
import Submission.Work.FTS.H2.hard_sq_prod_z
import Submission.Work.FTS.LocData.bumpZ_eq_zero_of_notMem_Icc
import Submission.Work.FTS.Nonlinear.Pieces.rl1Pieces.PsgEngine
import Submission.Work.FTS.Nonlinear.Pieces.splitsDiff
import Submission.Work.FTS.OpenPkg.C4Factors
import Submission.Work.FTS.OpenPkg.HkMem_add_of_contDiffOn_four
import Submission.Work.FTS.PhiStar.Series.Weil.integrableOn_prod_mul
import Submission.Work.FTS.StrongEps.mixed_Jeps
import Submission.Work.FTS.StrongPersist.N6Trans.OpenTwins.bt_prod_integrable_open
import Submission.Work.FTS_RegExport.C4.Dth_mixed_eq_C4
import Submission.Work.GalerkinFix.RegQ.HkMem_mono_Q
import Submission.Work.Spaces.HkSq_terms
import Submission.Work.Spaces.pz_DthIter_mul_eq
import Submission.Work.Spaces.sin_two_rpow
import Submission.Work.Spaces.sq_mul_div_rpow
-- ===== merged: Submission.Work.FTS.Nonlinear.Pieces.Rl1.EggBound =====
section

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

namespace Work.FTS.Nonlinear.Pieces.Rl1

open MeasureTheory Set Filter
open scoped Real Topology

set_option autoImplicit false
set_option linter.unusedVariables false

/-- `ℋ^k`-membership is closed under multiplication by a constant: the weighted integrand is
`2`-homogeneous (`RowsN0Aux.HkIntegrand_const_mul`), so both conjuncts of `HkMem` follow from the
corresponding ones for `f` by multiplying the integrands with `c²`. -/
theorem HkMem_const_mul_of {α : ℝ} {k : ℕ} (c : ℝ) {f : ℝ → ℝ → ℝ}
    (hf : Work.Spaces.HkMem α k f) :
    Work.Spaces.HkMem α k (fun z θ => c * f z θ) := by
  obtain ⟨h1, h2⟩ := hf
  constructor
  · intro z hz
    have hfun : (fun θ => Work.Spaces.HkIntegrand α k (fun z θ => c * f z θ) z θ)
        = fun θ => c ^ 2 * Work.Spaces.HkIntegrand α k f z θ :=
      funext fun θ =>
        Work.FTS.Nonlinear.Pieces.RowsN0Aux.HkIntegrand_const_mul α k c f z θ
    rw [hfun]
    exact (h1 z hz).const_mul _
  · have hfun : (fun z => ∫ θ in Work.Spaces.Iθ,
          Work.Spaces.HkIntegrand α k (fun z θ => c * f z θ) z θ)
        = fun z => c ^ 2 * ∫ θ in Work.Spaces.Iθ, Work.Spaces.HkIntegrand α k f z θ := by
      funext z
      rw [← MeasureTheory.integral_const_mul]
      exact MeasureTheory.setIntegral_congr_fun measurableSet_Icc
        (fun θ _ => Work.FTS.Nonlinear.Pieces.RowsN0Aux.HkIntegrand_const_mul α k c f z θ)
    rw [hfun]
    exact h2.const_mul _


end Work.FTS.Nonlinear.Pieces.Rl1
end
-- ===== merged: Submission.Work.FTS.OpenPkg.Good =====
section

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

noncomputable section
open scoped Real Topology
open MeasureTheory Set Filter

namespace Work.FTS.OpenPkg

open Work.FTS.Galerkin (Fn)

set_option autoImplicit false
set_option linter.unusedVariables false

/-- A function which is `C^4` on the open quadrant and honest in `ℋ^4`. -/
structure Good (α : ℝ) (f : Fn) : Prop where
  c4 : ContDiffOn ℝ 4 (Function.uncurry f) Q0
  hk : Work.Spaces.HkMem α 4 f

namespace Good

variable {α : ℝ} {f g : Fn}

/-- Sums of good functions are good. -/
theorem add (hf : Good α f) (hg : Good α g) :
    Good α (fun z θ => f z θ + g z θ) :=
  ⟨hf.c4.add hg.c4,
    Work.FTS.OpenPkg.HkMem_add_of_contDiffOn_four hf.c4 hg.c4 hf.hk hg.hk⟩

/-- Constant multiples of good functions are good (the integrand is homogeneous of degree two). -/
theorem const_mul (c : ℝ) (hf : Good α f) : Good α (fun z θ => c * f z θ) := by
  refine ⟨contDiffOn_const.mul hf.c4, ?_⟩
  refine Work.FTS.LocData.HkMem_of_majorant α 4 (f := fun z θ => c * f z θ)
    (M := fun z θ => c ^ 2 * Work.Spaces.HkIntegrand α 4 f z θ)
    (Work.FTS.OpenPkg.continuousOn_HkIntegrand_of_contDiffOn α le_rfl
      (contDiffOn_const.mul hf.c4)) ?_ ?_ ?_
  · intro z hz
    exact (hf.hk.1 z hz).const_mul (c ^ 2)
  · have htarget : IntegrableOn
        (fun z : ℝ => c ^ 2 * ∫ θ in Work.Spaces.Iθ, Work.Spaces.HkIntegrand α 4 f z θ)
        Work.Spaces.Iz := hf.hk.2.const_mul (c ^ 2)
    refine htarget.congr_fun ?_ measurableSet_Ici
    intro z hz
    exact (MeasureTheory.integral_const_mul (c ^ 2)
      (fun θ => Work.Spaces.HkIntegrand α 4 f z θ)).symm
  · intro z hz θ hθ
    rw [Work.FTS.LocData.HkIntegrand_const_mul]

/-- Negation preserves goodness. -/
theorem neg (hf : Good α f) : Good α (fun z θ => -f z θ) := by
  have := hf.const_mul (-1)
  simpa using this

/-- Transfer of goodness along equality on the open quadrant. -/
theorem of_eqOn (hu : Good α f) (h : ∀ z ∈ Set.Ioi (0 : ℝ), ∀ θ ∈ Set.Ioo (0 : ℝ) (π / 2),
    f z θ = g z θ) : Good α g :=
  ⟨hu.c4.congr (fun p hp => (h p.1 hp.1 p.2 hp.2).symm),
    Work.FTS.EllipticEst.Cert.GbarSin.HkMem_congr_Q0 α 4 hu.hk h⟩

/-- Transfer of goodness along an identity valid on the open quadrant. -/
theorem of_eqOn_Qd (hu : Good α f) (h : ∀ z θ, (z, θ) ∈ Work.Construction.Qd → f z θ = g z θ) :
    Good α g :=
  hu.of_eqOn (fun z hz θ hθ => h z θ ⟨hz, hθ⟩)

end Good

/-! ## The two auxiliary blocks -/

/-- `Γ(θ) = (sinθcos²θ)^{α/3}` is smooth on the quadrant. -/
theorem contDiffOn_Gam_Q0 (α : ℝ) (n : ℕ) :
    ContDiffOn ℝ n (fun p : ℝ × ℝ => Work.Spaces.Gam α p.2) Q0 := by
  have hbase : ContDiffOn ℝ n (fun p : ℝ × ℝ => Real.sin p.2 * Real.cos p.2 ^ 2) Q0 :=
    (((Real.contDiff_sin.comp contDiff_snd).mul
      ((Real.contDiff_cos.comp contDiff_snd).pow 2)).contDiffOn).of_le le_top
  have hpos : ∀ p ∈ Q0, 0 < Real.sin p.2 * Real.cos p.2 ^ 2 := by
    intro p hp
    have hs : 0 < Real.sin p.2 := Real.sin_pos_of_pos_of_lt_pi
      (by linarith [Set.mem_Ioo.mp hp.2 |>.1, Real.pi_pos])
      (by linarith [Set.mem_Ioo.mp hp.2 |>.2, Real.pi_pos])
    have hc : 0 < Real.cos p.2 := Real.cos_pos_of_mem_Ioo
      ⟨by linarith [hp.2.1, Real.pi_pos], hp.2.2⟩
    positivity
  simpa only [Work.Spaces.Gam] using
    hbase.rpow_const_of_ne (fun p hp => ne_of_gt (hpos p hp))

/-- `AK α = (Γ(θ)/c α)·2z²/(1+z)³` is smooth on the quadrant. -/
theorem contDiffOn_four_AK (α : ℝ) (hα : 0 < α) (hα1 : α ≤ 1) :
    ContDiffOn ℝ 4 (Function.uncurry (Work.Construction.AK α)) Q0 := by
  have hcne : Work.Spaces.c α ≠ 0 := by
    have h := (Work.Spaces.c_bounds α hα hα1).1
    intro h0; rw [h0] at h; norm_num at h
  have hGam := (contDiffOn_Gam_Q0 α 4).div contDiffOn_const (fun p hp => hcne)
  have hrad : ContDiffOn ℝ 4 (fun p : ℝ × ℝ => 2 * p.1 ^ 2 / (1 + p.1) ^ 3) Q0 :=
    (contDiffOn_const.mul (contDiffOn_fst.pow 2)).div
      ((contDiffOn_const.add contDiffOn_fst).pow 3)
      (fun p hp => pow_ne_zero 3 (ne_of_gt
        (by linarith [Set.mem_Ioi.mp hp.1] : (0 : ℝ) < 1 + p.1)))
  have hfun : (fun p : ℝ × ℝ => (Work.Spaces.Gam α p.2 / Work.Spaces.c α)
      * (2 * p.1 ^ 2 / (1 + p.1) ^ 3)) = Function.uncurry (Work.Construction.AK α) := by
    funext p
    obtain ⟨z, θ⟩ := p
    simp only [Function.uncurry, Work.Construction.AK]
  rw [← hfun]
  exact hGam.mul hrad

end Work.FTS.OpenPkg
end
end
-- ===== merged: Submission.Work.FTS_RegExport.RXT.Sys.hasDerivAt_mixed_theta =====
section

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

namespace Work.FTS_RegExport.RXT.Sys

/-!
# The `θ`-derivative of a mixed slot, at the finite order `C⁴`

For a datum `f` of class `C⁴` on the open quadrant `Q0` the operator `D_θ = sin(2θ) ∂_θ` shifts
the angular index of the mixed derivative `D_z^j D_θ^i f` (`i + j + 1 ≤ 4`, the finite-order
instance of the identity of `Submission/Work/FTS_RegExport/C4/Dth_mixed_eq_C4.lean`).  Since
`D_θ g = sin(2θ) · ∂_θ g` this gives the *plain* `θ`-derivative of the `θ`-slice:

  `HasDerivAt (fun θ' => D_z^jD_θ^i f z θ') (D_z^jD_θ^{i+1} f z θ / sin(2θ)) θ`.

The differentiability of the slice is the finite-order version of
`SmoothOpen.hasDerivAt_thslice`, obtained from `ContDiffOn ℝ 1 (uncurry ·) Q0` by the chain rule
(`Work.Spaces.deriv_slice_snd` identifies the value with `pth`).
-/

/-- For a function `g` which is `C¹` on an open set `V`, the `θ`-slice at an interior point is
differentiable with derivative `pth g z θ` (finite-order companion of
`Work.FTS_RegExport.RXT.hasDerivAt_slice_snd_of_contDiffOn`; stated here so that this file does
not need the heavy `CoercivityFix` import cone). -/
lemma hasDerivAt_slice_snd_of_contDiffOn {g : ℝ → ℝ → ℝ} {V : Set (ℝ × ℝ)}
    (hV : IsOpen V) (h : ContDiffOn ℝ 1 (Function.uncurry g) V)
    {z θ : ℝ} (hz : (z, θ) ∈ V) :
    HasDerivAt (fun θ' => g z θ') (Work.Spaces.pth g z θ) θ := by
  have hd : DifferentiableAt ℝ (Function.uncurry g) (z, θ) :=
    (h.differentiableOn one_ne_zero).differentiableAt (hV.mem_nhds hz)
  have h2 : HasFDerivAt (fun θ' : ℝ => (z, θ')) (ContinuousLinearMap.inr ℝ ℝ ℝ) θ :=
    hasFDerivAt_prodMk_right z θ
  have h3 : HasDerivAt (fun θ' : ℝ => Function.uncurry g (z, θ'))
      ((fderiv ℝ (Function.uncurry g) (z, θ)).comp (ContinuousLinearMap.inr ℝ ℝ ℝ) 1) θ := by
    simpa only [Function.comp_def] using (hd.hasFDerivAt.comp θ h2).hasDerivAt
  have hval : (fderiv ℝ (Function.uncurry g) (z, θ)).comp (ContinuousLinearMap.inr ℝ ℝ ℝ) 1
      = Work.Spaces.pth g z θ := by
    rw [ContinuousLinearMap.comp_apply, ContinuousLinearMap.inr_apply]
    exact (Work.Spaces.deriv_slice_snd (Function.uncurry g) z θ hd).symm
  rw [hval] at h3
  exact h3

theorem hasDerivAt_mixed_theta {f : ℝ → ℝ → ℝ}
    (hf : ContDiffOn ℝ 4 (Function.uncurry f) Work.FTS.EllipticEst.Q0)
    (j i : ℕ) (hji : j + i ≤ 3) {z θ : ℝ} (hz : 0 < z) (hθ : 0 < θ) (hθ' : θ < Real.pi / 2) :
    HasDerivAt (fun θ' => Work.Spaces.mixed j i f z θ')
      (Work.Spaces.mixed j (i + 1) f z θ / Real.sin (2 * θ)) θ := by
  have hmem : (z, θ) ∈ Work.FTS.EllipticEst.Q0 := by
    rw [Work.FTS.EllipticEst.mem_Q0]; exact ⟨hz, hθ, hθ'⟩
  -- `f` is `C^{1 + j + i}`, so `D_θ^i f` is `C^{1+j}` and `D_z^jD_θ^i f` is `C¹`
  have hle : (1 + j) + i ≤ 4 := by omega
  have hDth : ContDiffOn ℝ (↑(1 + j) + ↑i) (Function.uncurry f)
      Work.FTS.EllipticEst.Q0 :=
    hf.of_le (by exact_mod_cast hle)
  have hmid : ContDiffOn ℝ (1 + j) (Function.uncurry (Work.Spaces.DthIter i f))
      Work.FTS.EllipticEst.Q0 :=
    Work.FTS.StrongEps.contDiffOn_uncurry_DthIter_shift
      Work.FTS.EllipticEst.isOpen_Q0 i (1 + j) hDth
  have hmix : ContDiffOn ℝ 1 (Function.uncurry (Work.Spaces.mixed j i f))
      Work.FTS.EllipticEst.Q0 :=
    Work.FTS.StrongEps.contDiffOn_uncurry_DzIter_shift
      Work.FTS.EllipticEst.isOpen_Q0 j 1 hmid
  have hd := hasDerivAt_slice_snd_of_contDiffOn Work.FTS.EllipticEst.isOpen_Q0 hmix hmem
  -- the value of the derivative: `D_θ (D_z^jD_θ^i f) = D_z^jD_θ^{i+1} f`
  have hdth := Work.FTS_RegExport.C4.Dth_mixed_eq_C4 hf j i (by omega) hz ⟨hθ, hθ'⟩
  have hdth' : Real.sin (2 * θ) * Work.Spaces.pth (Work.Spaces.mixed j i f) z θ
      = Work.Spaces.mixed j (i + 1) f z θ := by
    simpa only [Work.Spaces.Dth] using hdth
  have hsin : Real.sin (2 * θ) ≠ 0 := by
    apply ne_of_gt
    exact Real.sin_pos_of_pos_of_lt_pi (by linarith) (by linarith [Real.pi_pos])
  have hval : Work.Spaces.pth (Work.Spaces.mixed j i f) z θ
      = Work.Spaces.mixed j (i + 1) f z θ / Real.sin (2 * θ) := by
    rw [eq_div_iff hsin, mul_comm]
    exact hdth'
  rw [hval] at hd
  exact hd

end Work.FTS_RegExport.RXT.Sys
end
