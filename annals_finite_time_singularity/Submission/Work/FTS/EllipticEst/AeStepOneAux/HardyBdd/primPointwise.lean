import Mathlib.Algebra.Order.Star.Real
import Mathlib.Analysis.InnerProductSpace.Basic
import Mathlib.Analysis.LocallyConvex.AbsConvexOpen
import Mathlib.Analysis.SpecialFunctions.Pow.Deriv
import Mathlib.Topology.Algebra.Module.ModuleTopology
import Submission.Work.FTS.EllipticEst.AeStepOneAux.HardyBddDefs
import Submission.Work.FTS.EllipticEst.H2W.sliceSigmaPointwise

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

namespace Work.FTS.EllipticEst.AeStepOneAux.HardyBdd

/-- The flux `hbPrim f θ = 2·hbA·cos(2θ)·(f θ)²·sin(2θ)^{-(1+η)}` of the weighted Hardy
inequality has, at every interior point `θ ∈ (0, π/2)`, the explicit derivative `hbDeriv f θ`
(see `Submission/Work/FTS/EllipticEst/AeStepOneAux/HardyBddDefs.lean`).  Only
`ContDiffOn ℝ 1 f (Ioo 0 (π/2))` is assumed, so this also holds without any closed-interval
smoothness or integrability hypothesis. -/
theorem hbPrim_hasDerivAt {f : ℝ → ℝ} (hf : ContDiffOn ℝ 1 f (Set.Ioo 0 (Real.pi / 2))) :
    ∀ θ ∈ Set.Ioo 0 (Real.pi / 2), HasDerivAt (hbPrim f) (hbDeriv f θ) θ := by
  intro θ hθ
  have hmem : Set.Ioo (0 : ℝ) (Real.pi / 2) ∈ nhds θ := IsOpen.mem_nhds isOpen_Ioo hθ
  have hfd : DifferentiableAt ℝ f θ := (hf.differentiableOn (by norm_num)).differentiableAt hmem
  have hS : 0 < Real.sin (2 * θ) :=
    Real.sin_pos_of_pos_of_lt_pi (by linarith [hθ.1]) (by linarith [hθ.2])
  have hSne : Real.sin (2 * θ) ≠ 0 := ne_of_gt hS
  have hint : HasDerivAt (fun θ' : ℝ => 2 * θ') 2 θ := by
    simpa using (hasDerivAt_id θ).const_mul 2
  have hsin : HasDerivAt (fun θ' : ℝ => Real.sin (2 * θ')) (2 * Real.cos (2 * θ)) θ := by
    have h := (Real.hasDerivAt_sin (2 * θ)).comp θ hint
    exact h.congr_deriv (by ring)
  have hcos : HasDerivAt (fun θ' : ℝ => Real.cos (2 * θ')) (-2 * Real.sin (2 * θ)) θ := by
    have h := (Real.hasDerivAt_cos (2 * θ)).comp θ hint
    exact h.congr_deriv (by ring)
  have hpow := (Real.hasDerivAt_rpow_const (x := Real.sin (2 * θ))
    (p := -(1 + Work.Spaces.eta)) (Or.inl hSne)).comp θ hsin
  have hf2 : HasDerivAt (fun θ' : ℝ => (f θ') ^ 2) (2 * f θ * deriv f θ) θ := by
    have h := hfd.hasDerivAt.pow 2
    refine h.congr_deriv ?_
    norm_num
  have hmain := (((hasDerivAt_const θ (2 * ((1 + Work.Spaces.eta) / 2))).mul hcos).mul hf2).mul hpow
  refine hmain.congr_deriv ?_
  rw [hbDeriv, hbA]
  simp only [Pi.mul_apply, Function.comp_apply]
  ring_nf

/-- The `deriv` form of `hbPrim_hasDerivAt`. -/
theorem hbPrim_deriv {f : ℝ → ℝ} (hf : ContDiffOn ℝ 1 f (Set.Ioo 0 (Real.pi / 2))) :
    ∀ θ ∈ Set.Ioo 0 (Real.pi / 2), deriv (hbPrim f) θ = hbDeriv f θ :=
  fun θ hθ => (hbPrim_hasDerivAt hf θ hθ).deriv

/-- The pointwise form of the sharp weighted Hardy inequality: on the open interval,
`(1+η)² f² sin(2θ)^{-(2+η)} ≤ (f')² sin(2θ)^{-η} - (hbDeriv f) θ`, where `hbDeriv f` is the
explicit derivative of the flux `hbPrim f` (see
`Submission/Work/FTS/EllipticEst/AeStepOneAux/HardyBddDefs.lean`).  It is the completed-square
identity `Work.FTS.EllipticEst.H2W.sliceSigmaPointwise` with its two nonnegative terms
`(∂_θ(f·sin(2θ)^{-a}))² sin(2θ)^{2a-η}` and `4a(1-a)f²sin(2θ)^{-η}` (`a = (1+η)/2`, so
`2a - η = 1`) dropped.  Only `ContDiffOn ℝ 1 f (Ioo 0 (π/2))` is assumed. -/
theorem primPointwise {f : ℝ → ℝ} (hf : ContDiffOn ℝ 1 f (Set.Ioo 0 (Real.pi / 2))) :
    ∀ θ ∈ Set.Ioo 0 (Real.pi / 2),
      (1 + Work.Spaces.eta) ^ 2 * ((f θ) ^ 2 * (Real.sin (2 * θ)) ^ (-(2 + Work.Spaces.eta)))
        ≤ (deriv f θ) ^ 2 * (Real.sin (2 * θ)) ^ (-(Work.Spaces.eta)) - hbDeriv f θ := by
  intro θ hθ
  have hmem : Set.Ioo (0 : ℝ) (Real.pi / 2) ∈ nhds θ := IsOpen.mem_nhds isOpen_Ioo hθ
  have hfd : DifferentiableAt ℝ f θ := (hf.differentiableOn (by norm_num)).differentiableAt hmem
  have hSpos : 0 < Real.sin (2 * θ) :=
    Real.sin_pos_of_pos_of_lt_pi (by linarith [hθ.1]) (by linarith [hθ.2])
  -- the completed-square identity of `sliceSigmaPointwise`, with the flux derivative evaluated
  have hfluxFun : (fun θ' : ℝ => 2 * ((1 + Work.Spaces.eta) / 2) * Real.cos (2 * θ') * (f θ') ^ 2
      * (Real.sin (2 * θ')) ^ (-(1 + Work.Spaces.eta))) = hbPrim f := rfl
  have hid := Work.FTS.EllipticEst.H2W.sliceSigmaPointwise (u := f) hθ hfd
  rw [hfluxFun, hbPrim_deriv hf θ hθ] at hid
  -- the two terms that are being dropped are nonnegative
  have hsq_nn : 0 ≤ (deriv (fun θ' : ℝ => f θ' * (Real.sin (2 * θ')) ^ (-((1 + Work.Spaces.eta) / 2))) θ) ^ 2
      * (Real.sin (2 * θ)) ^ (2 * ((1 + Work.Spaces.eta) / 2) - Work.Spaces.eta) :=
    mul_nonneg (sq_nonneg _) (le_of_lt (Real.rpow_pos_of_pos hSpos _))
  have hext_nn : 0 ≤ 4 * ((1 + Work.Spaces.eta) / 2) * (1 - (1 + Work.Spaces.eta) / 2) * (f θ) ^ 2
      * (Real.sin (2 * θ)) ^ (-Work.Spaces.eta) := by
    have h1 : 0 ≤ 4 * ((1 + Work.Spaces.eta) / 2) := by linarith [Work.Spaces.eta_pos]
    have h2 : 0 ≤ 1 - (1 + Work.Spaces.eta) / 2 := by linarith [Work.Spaces.eta_lt_one]
    have hU : 0 ≤ (f θ) ^ 2 := sq_nonneg _
    have hS : 0 ≤ (Real.sin (2 * θ)) ^ (-Work.Spaces.eta) := le_of_lt (Real.rpow_pos_of_pos hSpos _)
    exact mul_nonneg (mul_nonneg (mul_nonneg h1 h2) hU) hS
  -- solve the identity for the difference of the two terms on the left
  have hkey : (deriv f θ) ^ 2 * (Real.sin (2 * θ)) ^ (-Work.Spaces.eta) - hbDeriv f θ
      = (deriv (fun θ' : ℝ => f θ' * (Real.sin (2 * θ')) ^ (-((1 + Work.Spaces.eta) / 2))) θ) ^ 2
          * (Real.sin (2 * θ)) ^ (2 * ((1 + Work.Spaces.eta) / 2) - Work.Spaces.eta)
        + 4 * ((1 + Work.Spaces.eta) / 2) * (1 - (1 + Work.Spaces.eta) / 2) * (f θ) ^ 2
          * (Real.sin (2 * θ)) ^ (-Work.Spaces.eta)
        + 4 * ((1 + Work.Spaces.eta) / 2) ^ 2 * (f θ) ^ 2
          * (Real.sin (2 * θ)) ^ (-(2 + Work.Spaces.eta)) := by
    linarith [hid]
  have hcoef : (1 + Work.Spaces.eta) ^ 2 = 4 * ((1 + Work.Spaces.eta) / 2) ^ 2 := by ring
  rw [hcoef, hkey]
  linarith [hsq_nn, hext_nn]

end Work.FTS.EllipticEst.AeStepOneAux.HardyBdd
