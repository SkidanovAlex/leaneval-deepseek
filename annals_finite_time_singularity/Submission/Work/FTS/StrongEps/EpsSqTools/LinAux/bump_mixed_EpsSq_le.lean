import Mathlib.Algebra.Order.Star.Real
import Mathlib.Algebra.Ring.IsFormallyReal
import Mathlib.Analysis.Calculus.ContDiff.Defs
import Mathlib.Analysis.Calculus.ContDiff.Operations
import Mathlib.Analysis.Calculus.Deriv.Abs
import Mathlib.Analysis.Calculus.Deriv.Add
import Mathlib.Analysis.Calculus.Deriv.Mul
import Mathlib.Analysis.InnerProductSpace.Basic
import Mathlib.Analysis.LocallyConvex.AbsConvexOpen
import Mathlib.Analysis.Normed.Ring.Lemmas
import Mathlib.Analysis.Real.Pi.Bounds
import Mathlib.Analysis.SpecialFunctions.Pow.Real
import Mathlib.Analysis.SpecialFunctions.Trigonometric.Arctan
import Mathlib.MeasureTheory.Integral.Bochner.Set
import Mathlib.MeasureTheory.Integral.IntervalIntegral.Basic
import Mathlib.MeasureTheory.Measure.Haar.Unique
import Mathlib.MeasureTheory.Measure.Lebesgue.Basic
import Submission.Work.FTS.EllSol.ClassC
import Submission.Work.FTS.EllipticEst.EllHyp_certificates
import Submission.Work.FTS.EllipticEst.integrableOn_HkIntegrand_terms
import Submission.Work.FTS.EllipticEst.remov.slice_gprime_ident
import Submission.Work.FTS.StrongEps.EpsSqTools.Shift
import Submission.Work.FTS.StrongEps.blocks.L12_Fstar_add_open
import Submission.Work.FTS.StrongPersist.H6Rows.N0pair6bWork.HkMem_mul_of_WlInf6_cd6
import Submission.Work.FTS.StrongPersist.H6Rows.Npair6SupAux.StarSlotPcs.DzdIterBound
import Submission.Work.FTS.StrongPersist.H6Rows.Npair6SupAux.radialSupMul_cd6
import Submission.Work.FTS.StrongPersist.H6Rows.wprod6
import Submission.Work.FTS.StrongPersist.N6Trans.OpenTwins.bt_prod_integrable_open
import Submission.Work.FTS.StrongPersist.SP6.RadialSlot6
import Submission.Work.FTS.StrongPersist.SP6.WlInf6OfFlatW
import Submission.Work.FTS.StrongPersist.Star6
import Submission.Work.FTS.TransportS.t3SlotGuarded
import Submission.Work.FTS_EllLimOK.IsBslSolPos_add
import Submission.Work.FTS_EllLimOK.ProducerH.BoxAux.th2EgBasic
import Submission.Work.FTS_EllLimOK.ThetaJets.ClassC_le
import Submission.Work.FTS_MuLamOK.Defs
import Submission.Work.FTS_MuLipC.RowN.FaSlice
import Submission.Work.FTS_RegExport.RXB.sup_bound_all_alpha
import Submission.Work.FTS_RegExport.RXT.velVanish2Star
import Submission.Work.H2W.weakSliceZContinuousAe
import Submission.Work.H6Pair6Aux.T6Fix.mixed_sinGain_of_pthFlat
import Submission.Work.R1G.vecResid_eq_scalar_smul
import Submission.Work.Spaces.SmoothCompact_HkMem
-- ===== merged: Submission.Work.FTS.EllSol.EllPkgAux.uopPointwiseId =====
section

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

noncomputable section
open scoped Real Topology
open MeasureTheory Set Filter

namespace Work.FTS.EllSol.EllPkgAux

set_option autoImplicit false

/-- **The pointwise identity for `Uop` on the elliptic residual.**  On the open quadrant,

  `Uop α (EllResid α g Ψ) z θ / sin 2θ
     = -3·(ellShift α g Ψ z θ / sin 2θ) - α·(D_z(ellShift α g Ψ) z θ / sin 2θ)
       - (2 Ḡ α g z + (3/4) F_*(g)(z))`,

i.e. the quotient `Uop α Ξ / sin 2θ` of the residual is obtained from the quotient of the
straightened unknown `ellShift α g Ψ` by subtracting the pure radial profile
`2 Gbar α g + (3/4) Fstar g`.  The identity uses the first integral
`α z ∂_z(Gbar α g) = -5 Gbar α g - (3/4) Fstar g` of the `Ḡ`-ODE and the differentiability of
the `z`-slices of `Ψ` (hypothesis `SmoothOpen Ψ`). -/
theorem uopPointwiseId (α : ℝ) (g Ψ : Work.FTS.Galerkin.Fn) (hα : 0 < α) (hα1 : α ≤ 1)
    (hC : Work.FTS.EllSol.ClassC α g) (hΨ : Work.FTS.EllipticEst.SmoothOpen Ψ) :
    ∀ z θ : ℝ, 0 < z → 0 < θ → θ < Real.pi / 2 →
      Work.FTS.EllipticEst.Uop α (Work.Elliptic.EllResid α g Ψ) z θ / Real.sin (2 * θ)
        = -3 * (Work.FTS.EllSol.ellShift α g Ψ z θ / Real.sin (2 * θ))
          - α * (Work.Spaces.Dz (Work.FTS.EllSol.ellShift α g Ψ) z θ / Real.sin (2 * θ))
          - (2 * Work.Elliptic.Gbar α g z + (3 / 4) * Work.Elliptic.Fstar g z) := by
  intro z θ hz hθ hθ2
  have hσ : Real.sin (2 * θ) ≠ 0 :=
    ne_of_gt (Real.sin_pos_of_pos_of_lt_pi (by linarith) (by linarith [hθ2, Real.pi_pos]))
  -- ## The analytic inputs supplied by `ClassC α g`
  have hFsm : ∀ m : ℕ, ContDiffOn ℝ m (Work.Elliptic.Fstar g) (Set.Ioi 0) := hC.fsm
  have hFint : MeasureTheory.IntegrableOn (fun r : ℝ => Work.Elliptic.Fstar g r / r)
      (Set.Ioi 0) :=
    Work.FTS.EllipticEst.FstarDivOpen.fstar_div_integrable_of_smoothOpen α 7 g hC.reg hC.mem
  have hL12 : ∀ z ∈ Set.Ioi (0 : ℝ),
      HasDerivAt (Work.Elliptic.L12 g) (-(3 * Work.Elliptic.Fstar g z / z)) z :=
    Work.FTS.EllipticEst.HasDerivAt_L12_of_Fstar_facts g hFsm hFint
  have hJ : ∀ z ∈ Set.Ioi (0 : ℝ),
      HasDerivAt (fun z' => ∫ s in (0 : ℝ)..z', s ^ ((5 - α) / α) * Work.Elliptic.Fstar g s)
        (z ^ ((5 - α) / α) * Work.Elliptic.Fstar g z) z :=
    Work.FTS.EllipticEst.Cert.Jfun_hasDerivAt_of_Fstar α g hFsm hFint hα hα1
  have hJz : HasDerivAt (Work.Elliptic.Jfun α g)
      (z ^ ((5 - α) / α) * Work.Elliptic.Fstar g z) z := by
    have h := hJ z hz
    have hfun : (fun z' => ∫ s in (0 : ℝ)..z',
        s ^ ((5 - α) / α) * Work.Elliptic.Fstar g s) = Work.Elliptic.Jfun α g := rfl
    rw [hfun] at h
    exact h
  have hGbarDeriv : HasDerivAt (Work.Elliptic.Gbar α g) (Work.Elliptic.DGbar α g z) z :=
    Work.FTS.EllSol.PkgK5.CexK5.hasDerivAt_Gbar_DGbar α g hz hJz
  have hGbar_diff : DifferentiableAt ℝ (Work.Elliptic.Gbar α g) z := hGbarDeriv.differentiableAt
  have hGstar_diff : DifferentiableAt ℝ (Work.Elliptic.Gstar α g) z := by
    have h1 : Work.Elliptic.Gstar α g
        = fun z' : ℝ => (-(1 / (4 * α))) * Work.Elliptic.L12 g z' := rfl
    rw [h1]
    exact (differentiableAt_const _).mul (hL12 z hz).differentiableAt
  have hGsing_diff : DifferentiableAt ℝ (Work.Elliptic.Gsing α g) z := by
    have h1 : Work.Elliptic.Gsing α g
        = Work.Elliptic.Gstar α g + Work.Elliptic.Gbar α g := rfl
    rw [h1]
    exact hGstar_diff.add hGbar_diff
  have hL12diff : DifferentiableAt ℝ (Work.Elliptic.L12 g) z := (hL12 z hz).differentiableAt
  -- ## The derivatives of the two `z`-slices (this is where `SmoothOpen Ψ` enters)
  have hΨslice : HasDerivAt (fun z' : ℝ => Ψ z' θ) (Work.Spaces.pz Ψ z θ) z :=
    hΨ.hasDerivAt_slice ⟨hθ, hθ2⟩ hz
  have hGsingd : HasDerivAt (fun z' : ℝ => Work.Elliptic.Gsing α g z')
      (deriv (Work.Elliptic.Gsing α g) z) z := hGsing_diff.hasDerivAt
  have hXslice : HasDerivAt (fun z' : ℝ => Work.FTS.EllSol.ellShift α g Ψ z' θ)
      (Work.Spaces.pz Ψ z θ + deriv (Work.Elliptic.Gsing α g) z * Real.sin (2 * θ)) z := by
    have h := hΨslice.add (hGsingd.mul_const (Real.sin (2 * θ)))
    have hfun : ((fun z' : ℝ => Ψ z' θ)
        + fun y : ℝ => Work.Elliptic.Gsing α g y * Real.sin (2 * θ))
        = fun z' : ℝ => Work.FTS.EllSol.ellShift α g Ψ z' θ := by
      funext z'
      simp only [Pi.add_apply, Work.FTS.EllSol.ellShift]
    rwa [hfun] at h
  have hΞslice : HasDerivAt (fun z' : ℝ => Work.Elliptic.EllResid α g Ψ z' θ)
      (Work.Spaces.pz Ψ z θ
        - (1 / (4 * α)) * Real.sin (2 * θ) * deriv (Work.Elliptic.L12 g) z) z := by
    have h := hΨslice.sub (hL12diff.hasDerivAt.const_mul ((1 / (4 * α)) * Real.sin (2 * θ)))
    have hfun : ((fun z' : ℝ => Ψ z' θ)
        - fun y : ℝ => (1 / (4 * α)) * Real.sin (2 * θ) * Work.Elliptic.L12 g y)
        = fun z' : ℝ => Work.Elliptic.EllResid α g Ψ z' θ := by
      funext z'
      simp only [Pi.sub_apply, Work.Elliptic.EllResid]
    rwa [hfun] at h
  have hpzX : Work.Spaces.pz (Work.FTS.EllSol.ellShift α g Ψ) z θ
      = Work.Spaces.pz Ψ z θ + deriv (Work.Elliptic.Gsing α g) z * Real.sin (2 * θ) := by
    simpa only [Work.Spaces.pz] using hXslice.deriv
  have hpzΞ : Work.Spaces.pz (Work.Elliptic.EllResid α g Ψ) z θ
      = Work.Spaces.pz Ψ z θ
        - (1 / (4 * α)) * Real.sin (2 * θ) * deriv (Work.Elliptic.L12 g) z := by
    simpa only [Work.Spaces.pz] using hΞslice.deriv
  -- ## `∂_z Ḡ = ∂_z Gsing + (1/4α) ∂_z L₁₂` (`Gsing = Gstar + Ḡ`, `Gstar = -(1/4α) L₁₂`)
  have hGbar_deriv : deriv (Work.Elliptic.Gbar α g) z
      = deriv (Work.Elliptic.Gsing α g) z
        + (1 / (4 * α)) * deriv (Work.Elliptic.L12 g) z := by
    have h := hGsingd.add (hL12diff.hasDerivAt.const_mul (1 / (4 * α)))
    have hfun : (Work.Elliptic.Gsing α g
        + fun y : ℝ => (1 / (4 * α)) * Work.Elliptic.L12 g y) = Work.Elliptic.Gbar α g := by
      funext y
      simp only [Pi.add_apply, Work.Elliptic.Gsing, Work.Elliptic.Gstar]
      ring
    rw [hfun] at h
    exact h.deriv
  -- ## `∂_z(ellShift) = ∂_z(EllResid) + sin 2θ · ∂_z Ḡ`
  have hpz_rel : Work.Spaces.pz (Work.FTS.EllSol.ellShift α g Ψ) z θ
      = Work.Spaces.pz (Work.Elliptic.EllResid α g Ψ) z θ
        + Real.sin (2 * θ) * deriv (Work.Elliptic.Gbar α g) z := by
    rw [hpzX, hpzΞ, hGbar_deriv]
    ring
  -- ## the first integral of the `Ḡ`-ODE: `α z ∂_z Ḡ = -5 Ḡ - (3/4) F_*`
  have hrel := Work.FTS.EllSol.PkgK5.CexK5.Gbar_deriv_rel α g hα hL12
      (fun z hz => (((hFsm 1).differentiableOn (by norm_num)).differentiableAt
        (isOpen_Ioi.mem_nhds hz)).hasDerivAt) hJ z hz
  rw [← hGbarDeriv.deriv] at hrel
  -- ## the unscaled identity
  have hscaled : Work.FTS.EllipticEst.Uop α (Work.Elliptic.EllResid α g Ψ) z θ
      = -3 * Work.FTS.EllSol.ellShift α g Ψ z θ
        - α * Work.Spaces.Dz (Work.FTS.EllSol.ellShift α g Ψ) z θ
        - Real.sin (2 * θ) * (2 * Work.Elliptic.Gbar α g z
            + (3 / 4) * Work.Elliptic.Fstar g z) := by
    have hU : Work.FTS.EllipticEst.Uop α (Work.Elliptic.EllResid α g Ψ) z θ
        = -3 * Work.Elliptic.EllResid α g Ψ z θ
          - α * Work.Spaces.Dz (Work.Elliptic.EllResid α g Ψ) z θ := by
      simp only [Work.FTS.EllipticEst.Uop, Work.Spaces.Dz]
      ring
    have hXeq : Work.FTS.EllSol.ellShift α g Ψ z θ
        = Work.Elliptic.EllResid α g Ψ z θ
          + Work.Elliptic.Gbar α g z * Real.sin (2 * θ) := by
      simp only [Work.FTS.EllSol.ellShift, Work.Elliptic.EllResid, Work.Elliptic.Gsing,
        Work.Elliptic.Gstar]
      ring
    have hDzX : Work.Spaces.Dz (Work.FTS.EllSol.ellShift α g Ψ) z θ
        = Work.Spaces.Dz (Work.Elliptic.EllResid α g Ψ) z θ
          + Real.sin (2 * θ) * z * deriv (Work.Elliptic.Gbar α g) z := by
      simp only [Work.Spaces.Dz, hpz_rel]
      ring
    rw [hU, hDzX, hXeq]
    have hσrel : Real.sin (2 * θ) * (α * (z * deriv (Work.Elliptic.Gbar α g) z))
        = Real.sin (2 * θ) * (-5 * Work.Elliptic.Gbar α g z
            - (3 / 4) * Work.Elliptic.Fstar g z) := by rw [hrel]
    linear_combination hσrel
  -- ## divide by `sin 2θ`
  rw [hscaled]
  field_simp

end Work.FTS.EllSol.EllPkgAux
end
end
-- ===== merged: Submission.Work.FTS.EllSol.PkgK5.uopPointwiseIdentityRefute =====
section

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

noncomputable section

open scoped Real Topology
open MeasureTheory Set Filter

namespace Work.FTS.EllSol.PkgK5

set_option autoImplicit false

/-! ## 0. Elementary facts about the totalised `deriv` -/





/-! ## 1. The algebraic reduction of the requested identity -/



/-! ## 2. The refutation -/


end Work.FTS.EllSol.PkgK5

namespace Work.FTS.EllSol.PkgK5

open scoped Real Topology
open MeasureTheory Set Filter

set_option autoImplicit false

/-- **The repaired identity (proved).**  The requested statement becomes true as soon as the
`z`-slices of `Φg` are differentiable — here supplied by `SmoothOpen Φg`; the shape of the
proof is precisely `D_z X = D_z Ξ + sin 2θ · D_z Ḡ` followed by the tree's proved
`CexK5.Gbar_deriv_rel`.  (`α ≤ 1` is an artefact of
`Cert.Jfun_hasDerivAt_of_Fstar`; the identity itself is true for every `α > 0`.) -/
theorem uopPointwiseIdentity_repaired (α : ℝ) (g Φg : Work.FTS.Galerkin.Fn) (hα : 0 < α)
    (hα1 : α ≤ 1) (hC : Work.FTS.EllSol.ClassC α g)
    (hΦg : Work.FTS.EllipticEst.SmoothOpen Φg) :
    ∀ z θ : ℝ, 0 < z → 0 < θ → θ < Real.pi / 2 →
      Work.FTS.EllipticEst.Uop α (Work.Elliptic.EllResid α g Φg) z θ / Real.sin (2 * θ)
        = -3 * (Work.FTS.EllSol.ellShift α g Φg z θ / Real.sin (2 * θ))
          - α * (Work.Spaces.Dz (Work.FTS.EllSol.ellShift α g Φg) z θ / Real.sin (2 * θ))
          - (2 * Work.Elliptic.Gbar α g z + (3 / 4) * Work.Elliptic.Fstar g z) := by
  intro z θ hz hθ hθ2
  have hσ : Real.sin (2 * θ) ≠ 0 :=
    ne_of_gt (Real.sin_pos_of_pos_of_lt_pi (by linarith) (by linarith [hθ2, Real.pi_pos]))
  -- ## the analytic facts of `ClassC`
  have hFsm : ∀ m : ℕ, ContDiffOn ℝ m (Work.Elliptic.Fstar g) (Set.Ioi 0) := hC.fsm
  have hFint : MeasureTheory.IntegrableOn (fun r : ℝ => Work.Elliptic.Fstar g r / r)
      (Set.Ioi 0) :=
    Work.FTS.EllipticEst.FstarDivOpen.fstar_div_integrable_of_smoothOpen α 7 g hC.reg hC.mem
  have hL12 : ∀ z ∈ Set.Ioi (0 : ℝ),
      HasDerivAt (Work.Elliptic.L12 g) (-(3 * Work.Elliptic.Fstar g z / z)) z :=
    Work.FTS.EllipticEst.HasDerivAt_L12_of_Fstar_facts g hFsm hFint
  have hJ : ∀ z ∈ Set.Ioi (0 : ℝ),
      HasDerivAt (fun z' => ∫ s in (0 : ℝ)..z', s ^ ((5 - α) / α) * Work.Elliptic.Fstar g s)
        (z ^ ((5 - α) / α) * Work.Elliptic.Fstar g z) z :=
    Work.FTS.EllipticEst.Cert.Jfun_hasDerivAt_of_Fstar α g hFsm hFint hα hα1
  have hJz : HasDerivAt (Work.Elliptic.Jfun α g)
      (z ^ ((5 - α) / α) * Work.Elliptic.Fstar g z) z := by
    have h := hJ z hz
    have hfun : (fun z' => ∫ s in (0 : ℝ)..z',
        s ^ ((5 - α) / α) * Work.Elliptic.Fstar g s) = Work.Elliptic.Jfun α g := rfl
    rw [hfun] at h
    exact h
  have hGbarDeriv : HasDerivAt (Work.Elliptic.Gbar α g) (Work.Elliptic.DGbar α g z) z :=
    CexK5.hasDerivAt_Gbar_DGbar α g hz hJz
  have hGbar_diff : DifferentiableAt ℝ (Work.Elliptic.Gbar α g) z := hGbarDeriv.differentiableAt
  have hGstar_diff : DifferentiableAt ℝ (Work.Elliptic.Gstar α g) z := by
    have h1 : Work.Elliptic.Gstar α g
        = fun z' : ℝ => (-(1 / (4 * α))) * Work.Elliptic.L12 g z' := rfl
    rw [h1]
    exact (differentiableAt_const _).mul (hL12 z hz).differentiableAt
  have hGsing_diff : DifferentiableAt ℝ (Work.Elliptic.Gsing α g) z := by
    have h1 : Work.Elliptic.Gsing α g
        = Work.Elliptic.Gstar α g + Work.Elliptic.Gbar α g := rfl
    rw [h1]
    exact hGstar_diff.add hGbar_diff
  have hL12diff : DifferentiableAt ℝ (Work.Elliptic.L12 g) z := (hL12 z hz).differentiableAt
  -- ## the `z`-slice derivatives (this is the step that needs `SmoothOpen Φg`)
  have hΦgs : HasDerivAt (fun z' : ℝ => Φg z' θ) (Work.Spaces.pz Φg z θ) z :=
    hΦg.hasDerivAt_slice ⟨hθ, hθ2⟩ hz
  have hGsingd : HasDerivAt (fun z' : ℝ => Work.Elliptic.Gsing α g z')
      (deriv (Work.Elliptic.Gsing α g) z) z := hGsing_diff.hasDerivAt
  have hXslice : HasDerivAt (fun z' : ℝ => Work.FTS.EllSol.ellShift α g Φg z' θ)
      (Work.Spaces.pz Φg z θ + deriv (Work.Elliptic.Gsing α g) z * Real.sin (2 * θ)) z := by
    have h := hΦgs.add (hGsingd.mul_const (Real.sin (2 * θ)))
    have hfun : ((fun z' : ℝ => Φg z' θ)
        + fun y : ℝ => Work.Elliptic.Gsing α g y * Real.sin (2 * θ))
        = fun z' : ℝ => Work.FTS.EllSol.ellShift α g Φg z' θ := by
      funext z'
      simp only [Pi.add_apply, Work.FTS.EllSol.ellShift]
    rwa [hfun] at h
  have hΞslice : HasDerivAt (fun z' : ℝ => Work.Elliptic.EllResid α g Φg z' θ)
      (Work.Spaces.pz Φg z θ
        - (1 / (4 * α)) * Real.sin (2 * θ) * deriv (Work.Elliptic.L12 g) z) z := by
    have h := hΦgs.sub (hL12diff.hasDerivAt.const_mul ((1 / (4 * α)) * Real.sin (2 * θ)))
    have hfun : ((fun z' : ℝ => Φg z' θ)
        - fun y : ℝ => (1 / (4 * α)) * Real.sin (2 * θ) * Work.Elliptic.L12 g y)
        = fun z' : ℝ => Work.Elliptic.EllResid α g Φg z' θ := by
      funext z'
      simp only [Pi.sub_apply, Work.Elliptic.EllResid]
    rwa [hfun] at h
  have hpzX : Work.Spaces.pz (Work.FTS.EllSol.ellShift α g Φg) z θ
      = Work.Spaces.pz Φg z θ + deriv (Work.Elliptic.Gsing α g) z * Real.sin (2 * θ) := by
    simpa only [Work.Spaces.pz] using hXslice.deriv
  have hpzΞ : Work.Spaces.pz (Work.Elliptic.EllResid α g Φg) z θ
      = Work.Spaces.pz Φg z θ
        - (1 / (4 * α)) * Real.sin (2 * θ) * deriv (Work.Elliptic.L12 g) z := by
    simpa only [Work.Spaces.pz] using hΞslice.deriv
  -- ## `∂_z Ḡ = ∂_z Gsing + (1/(4α))·∂_z L₁₂` (the two singular parts add up to `Ḡ`)
  have hGbar_deriv : deriv (Work.Elliptic.Gbar α g) z
      = deriv (Work.Elliptic.Gsing α g) z
        + (1 / (4 * α)) * deriv (Work.Elliptic.L12 g) z := by
    have h := hGsingd.add (hL12diff.hasDerivAt.const_mul (1 / (4 * α)))
    have hfun : (Work.Elliptic.Gsing α g
        + fun y : ℝ => (1 / (4 * α)) * Work.Elliptic.L12 g y) = Work.Elliptic.Gbar α g := by
      funext y
      simp only [Pi.add_apply, Work.Elliptic.Gsing, Work.Elliptic.Gstar]
      ring
    rw [hfun] at h
    exact h.deriv
  -- ## the key relation between the two `pz`'s
  have hpz_rel : Work.Spaces.pz (Work.FTS.EllSol.ellShift α g Φg) z θ
      = Work.Spaces.pz (Work.Elliptic.EllResid α g Φg) z θ
        + Real.sin (2 * θ) * deriv (Work.Elliptic.Gbar α g) z := by
    rw [hpzX, hpzΞ, hGbar_deriv]
    ring
  -- ## the scaled identity
  have hrel := CexK5.Gbar_deriv_rel α g hα hL12
    (fun z hz => (((hFsm 1).differentiableOn (by norm_num)).differentiableAt
      (isOpen_Ioi.mem_nhds hz)).hasDerivAt) hJ z hz
  rw [← hGbarDeriv.deriv] at hrel
  have hscaled : Work.FTS.EllipticEst.Uop α (Work.Elliptic.EllResid α g Φg) z θ
      = -3 * Work.FTS.EllSol.ellShift α g Φg z θ
        - α * Work.Spaces.Dz (Work.FTS.EllSol.ellShift α g Φg) z θ
        - Real.sin (2 * θ) * (2 * Work.Elliptic.Gbar α g z
            + (3 / 4) * Work.Elliptic.Fstar g z) := by
    have hU : Work.FTS.EllipticEst.Uop α (Work.Elliptic.EllResid α g Φg) z θ
        = -3 * Work.Elliptic.EllResid α g Φg z θ
          - α * Work.Spaces.Dz (Work.Elliptic.EllResid α g Φg) z θ := by
      simp only [Work.FTS.EllipticEst.Uop, Work.Spaces.Dz]
      ring
    have hXeq : Work.FTS.EllSol.ellShift α g Φg z θ
        = Work.Elliptic.EllResid α g Φg z θ
          + Work.Elliptic.Gbar α g z * Real.sin (2 * θ) := by
      simp only [Work.FTS.EllSol.ellShift, Work.Elliptic.EllResid, Work.Elliptic.Gsing,
        Work.Elliptic.Gstar]
      ring
    have hDzX : Work.Spaces.Dz (Work.FTS.EllSol.ellShift α g Φg) z θ
        = Work.Spaces.Dz (Work.Elliptic.EllResid α g Φg) z θ
          + Real.sin (2 * θ) * z * deriv (Work.Elliptic.Gbar α g) z := by
      simp only [Work.Spaces.Dz, hpz_rel]
      ring
    rw [hU, hDzX, hXeq]
    have hσrel : Real.sin (2 * θ) * (α * (z * deriv (Work.Elliptic.Gbar α g) z))
        = Real.sin (2 * θ) * (-5 * Work.Elliptic.Gbar α g z
            - (3 / 4) * Work.Elliptic.Fstar g z) := by rw [hrel]
    linear_combination hσrel
  -- ## divide by `sin 2θ`
  rw [hscaled]
  field_simp

end Work.FTS.EllSol.PkgK5
end
end
-- ===== merged: Submission.Work.FTS.EpsEngine.HkMem_iter_succ =====
section

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

noncomputable section
open scoped Real Topology
open MeasureTheory Set Filter
open Work.FTS.Galerkin (Fn Fam slice)

namespace Work.FTS.EpsEngine

set_option autoImplicit false
set_option linter.unusedVariables false

/-- **(H4)(a), assembled.**  If the increment `∫₀^τ F (slice (Work.FTS.StrongEps.EpsLocalPStar.iter F h₀ n) ·)` is `ℋ^k`-honest with
the norm bound `B·τ` (the conclusion of the repaired interval-integral lemma), then so is the
`(n+1)`-st Picard iterate. -/
theorem HkMem_iter_succ {α B : ℝ} {F : Fn → Fn} {h₀ : Fn} {k : ℕ} {T τ : ℝ} {n : ℕ}
    (hτ : 0 ≤ τ) (hτT : τ ≤ T) (hB : 0 ≤ B)
    (h₀smo : Work.FTS.EllipticEst.SmoothOpen h₀)
    (h₀mem : Work.Spaces.HkMem α k h₀)
    (hIsmo : Work.FTS.EllipticEst.SmoothOpen
      (fun z θ => ∫ s in (0 : ℝ)..τ, F (slice (Work.FTS.StrongEps.EpsLocalPStar.iter F h₀ n) s) z θ))
    (hint : Work.Spaces.HkMem α k
        (fun z θ => ∫ s in (0 : ℝ)..τ, F (slice (Work.FTS.StrongEps.EpsLocalPStar.iter F h₀ n) s) z θ) ∧
      Work.Spaces.HkNorm α k
        (fun z θ => ∫ s in (0 : ℝ)..τ, F (slice (Work.FTS.StrongEps.EpsLocalPStar.iter F h₀ n) s) z θ) ≤ B * τ) :
    Work.Spaces.HkMem α k (slice (Work.FTS.StrongEps.EpsLocalPStar.iter F h₀ (n + 1)) τ) ∧
      Work.Spaces.HkNorm α k (slice (Work.FTS.StrongEps.EpsLocalPStar.iter F h₀ (n + 1)) τ)
        ≤ Work.Spaces.HkNorm α k h₀ + B * τ := by
  have hslice : slice (Work.FTS.StrongEps.EpsLocalPStar.iter F h₀ (n + 1)) τ
      = fun z θ => h₀ z θ + ∫ s in (0 : ℝ)..τ, F (slice (Work.FTS.StrongEps.EpsLocalPStar.iter F h₀ n) s) z θ := by
    funext z θ
    simp only [Work.FTS.Galerkin.slice_apply, Work.FTS.StrongEps.EpsLocalPStar.iter_succ]
  rw [hslice]
  obtain ⟨hmemI, hbdI⟩ := hint
  have h₀c : ∀ m : ℕ, ContDiffOn ℝ m (Function.uncurry h₀) (Set.Ioi 0 ×ˢ Set.Ioo 0 (π / 2)) :=
    (Work.FTS.EllipticEst.smoothOpen_iff_forall _).mp h₀smo
  have hIc : ∀ m : ℕ, ContDiffOn ℝ m
      (Function.uncurry (fun z θ => ∫ s in (0 : ℝ)..τ, F (slice (Work.FTS.StrongEps.EpsLocalPStar.iter F h₀ n) s) z θ))
      (Set.Ioi 0 ×ˢ Set.Ioo 0 (π / 2)) :=
    (Work.FTS.EllipticEst.smoothOpen_iff_forall _).mp hIsmo
  refine ⟨Work.FTS.EllipticEst.HkMem_add_open h₀smo hIsmo h₀mem hmemI, ?_⟩
  refine (Work.FTS.StrongEps.EpsE4Thr.HkNorm_triangle α k h₀c hIc h₀mem hmemI).trans ?_
  exact add_le_add le_rfl hbdI

/-- **(H4)(a) with the interval-integral lemma plugged in.**  The same conclusion as
`HkMem_iter_succ`, with `hint` discharged by `Work.FTS.EpsEngine.HkMem_intervalIntegralPerz` applied
to the family `H s = F (slice (iter F h₀ n) s)`. -/
theorem HkMem_iter_succ_of_data {α B : ℝ} {F : Fn → Fn} {h₀ : Fn} {k : ℕ} {T τ : ℝ} {n : ℕ}
    (hτ : 0 ≤ τ) (hτT : τ ≤ T) (hT : 0 ≤ T) (hB : 0 ≤ B)
    (h₀smo : Work.FTS.EllipticEst.SmoothOpen h₀)
    (h₀mem : Work.Spaces.HkMem α k h₀)
    (hIsmo : Work.FTS.EllipticEst.SmoothOpen
      (fun z θ => ∫ s in (0 : ℝ)..τ, F (slice (Work.FTS.StrongEps.EpsLocalPStar.iter F h₀ n) s) z θ))
    (hHsm : ∀ s ∈ Set.Icc 0 T,
      Work.FTS.EllipticEst.SmoothOpen (F (slice (Work.FTS.StrongEps.EpsLocalPStar.iter F h₀ n) s)))
    (hHmem : ∀ s ∈ Set.Icc 0 T,
      Work.Spaces.HkMem α k (F (slice (Work.FTS.StrongEps.EpsLocalPStar.iter F h₀ n) s)))
    (hHbd : ∀ s ∈ Set.Icc 0 T,
      Work.Spaces.HkNorm α k (F (slice (Work.FTS.StrongEps.EpsLocalPStar.iter F h₀ n) s)) ≤ B)
    (hmeas : ∀ (j i : ℕ), j + i ≤ k → ∀ z θ : ℝ,
      (z, θ) ∈ Work.FTS.EllipticEst.Q0 →
      MeasureTheory.AEStronglyMeasurable
        (fun s : ℝ => Work.Spaces.mixed j i
          (F (slice (Work.FTS.StrongEps.EpsLocalPStar.iter F h₀ n) s)) z θ)
        (MeasureTheory.volume.restrict (Set.Icc (0 : ℝ) T)))
    (hjoint : MeasureTheory.AEStronglyMeasurable
      (fun p : ℝ × ℝ × ℝ => Work.Spaces.HkIntegrand α k
        (F (slice (Work.FTS.StrongEps.EpsLocalPStar.iter F h₀ n) p.1)) p.2.1 p.2.2)
      ((MeasureTheory.volume.restrict (Set.Icc (0 : ℝ) T)).prod
        ((MeasureTheory.volume.restrict Work.Spaces.Iz).prod
          (MeasureTheory.volume.restrict Work.Spaces.Iθ))))
    (hsup : ∀ K : Set (ℝ × ℝ), IsCompact K → K ⊆ Work.FTS.EllipticEst.Q0 →
      ∃ C : ℝ, 0 ≤ C ∧ ∀ s ∈ Set.Icc (0 : ℝ) T, ∀ q ∈ K, ∀ (j i : ℕ), j + i ≤ k →
        |Work.Spaces.mixed j i
          (F (slice (Work.FTS.StrongEps.EpsLocalPStar.iter F h₀ n) s)) q.1 q.2| ≤ C)
    (hperz : ∀ z ∈ Work.Spaces.Iz, ∃ Cz : ℝ, ∀ s ∈ Set.Icc (0 : ℝ) T,
      (∫ θ in Work.Spaces.Iθ, Work.Spaces.HkIntegrand α k
        (F (slice (Work.FTS.StrongEps.EpsLocalPStar.iter F h₀ n) s)) z θ) ≤ Cz) :
    Work.Spaces.HkMem α k (slice (Work.FTS.StrongEps.EpsLocalPStar.iter F h₀ (n + 1)) τ) ∧
      Work.Spaces.HkNorm α k (slice (Work.FTS.StrongEps.EpsLocalPStar.iter F h₀ (n + 1)) τ)
        ≤ Work.Spaces.HkNorm α k h₀ + B * τ := by
  obtain ⟨hmemI, hbdI⟩ :=
    HkMem_intervalIntegralPerz (α := α) (B := B) (k := k) (T := T) (a := 0) (b := τ)
      (H := fun s z θ => F (slice (Work.FTS.StrongEps.EpsLocalPStar.iter F h₀ n) s) z θ)
      hτ hT ⟨le_rfl, hT⟩ ⟨hτ, hτT⟩ hHsm hHmem hHbd hmeas hjoint hsup hperz
  have hbdI' : Work.Spaces.HkNorm α k
      (fun z θ => ∫ s in (0 : ℝ)..τ, F (slice (Work.FTS.StrongEps.EpsLocalPStar.iter F h₀ n) s) z θ)
      ≤ B * τ := by
    simpa only [sub_zero] using hbdI
  exact HkMem_iter_succ (F := F) (h₀ := h₀) (k := k) (T := T) (τ := τ) (n := n)
    hτ hτT hB h₀smo h₀mem hIsmo ⟨hmemI, hbdI'⟩

end Work.FTS.EpsEngine
end
end
-- ===== merged: Submission.Work.FTS.EpsEngine.ThetaFromEpsLeafA.subst_kernel_iter =====
section

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

namespace Work.FTS.EpsEngine.ThetaFromEpsLeafA

open MeasureTheory

/-- The reflection `x ↦ c - x` does not change the Lebesgue `lintegral` on `ℝ`: it is the
composition of the translation `x ↦ x + c` (invariance: `lintegral_add_right_eq_self`) with the
negation `x ↦ -x` (invariance: `lintegral_neg_eq_self`). -/
private lemma lintegral_add_neg_eq_self (F : ℝ → ENNReal) (c : ℝ) :
    (∫⁻ s, F (c + -s)) = ∫⁻ s, F s := by
  rw [MeasureTheory.lintegral_neg_eq_self (fun y => F (c + y))]
  rw [show (∫⁻ s, F (c + s)) = ∫⁻ s, F (s + c) from
    MeasureTheory.lintegral_congr (fun s => by rw [add_comm])]
  exact MeasureTheory.lintegral_add_right_eq_self F c

/-- The two-dimensional form of the previous lemma. -/
private lemma lintegral_prod_neg_sub (F : ℝ → ℝ → ENNReal) (c d : ℝ) :
    (∫⁻ s, ∫⁻ ζ, F (c - s) (d - ζ)) = ∫⁻ s, ∫⁻ ζ, F s ζ := by
  have hinner : ∀ s, (∫⁻ ζ, F (c - s) (d - ζ)) = ∫⁻ ζ, F (c - s) ζ := by
    intro s
    simpa only [sub_eq_add_neg] using lintegral_add_neg_eq_self (fun ζ => F (c - s) ζ) d
  rw [MeasureTheory.lintegral_congr hinner]
  simpa only [sub_eq_add_neg] using lintegral_add_neg_eq_self (fun s => ∫⁻ ζ, F s ζ) c

/-- The angular Jacobian identity behind the log-coordinate substitution: the derivative of
`θ ↦ log tan θ` is `2 / sin (2θ)`, and in the coordinate `ζ = log tan θ` (`θ = arctan (e^ζ)`)
this reads `sin (2 · arctan (e^ζ)) = 2 · kappa ζ`, where `kappa ζ = e^ζ/(1 + e^{2ζ})` is the
derivative of `ζ ↦ arctan (e^ζ)`. -/
private lemma sin_two_arctan_exp (ζ : ℝ) :
    Real.sin (2 * Real.arctan (Real.exp ζ)) = 2 * Work.FTS.StrongEps.HkSqAux.kappa ζ := by
  have hpos : 0 < 1 + (Real.exp ζ) ^ 2 := by positivity
  have hsq : (Real.sqrt (1 + (Real.exp ζ) ^ 2)) ^ 2 = 1 + Real.exp (2 * ζ) := by
    rw [Real.sq_sqrt hpos.le]
    congr 1
    rw [sq, ← Real.exp_add]
    congr 1
    ring
  rw [Real.sin_two_mul, Real.sin_arctan, Real.cos_arctan, Work.FTS.StrongEps.HkSqAux.kappa,
    div_eq_mul_inv, div_eq_mul_inv, ← hsq]
  have hne : Real.sqrt (1 + (Real.exp ζ) ^ 2) ≠ 0 := by positivity
  field_simp

/-- The Jacobian of the log-coordinate substitution `(z, θ) ↦ (log z, log tan θ)` cancels the
weight `2 / (z sin 2θ)` of the quadrant integral. -/
private lemma logJac_mul_weight (s ζ : ℝ) :
    Work.FTS.StrongEps.HkSqAux.logJac s ζ
      * (2 / (Real.exp s * Real.sin (2 * Real.arctan (Real.exp ζ)))) = 1 := by
  rw [Work.FTS.StrongEps.HkSqAux.logJac, sin_two_arctan_exp, div_eq_mul_inv]
  have hk0 : Work.FTS.StrongEps.HkSqAux.kappa ζ ≠ 0 :=
    ne_of_gt (Work.FTS.StrongEps.HkSqAux.kappa_pos ζ)
  have he : Real.exp s ≠ 0 := (Real.exp_pos s).ne'
  field_simp

/-- **The log-coordinate substitution for an arbitrary kernel.** For an arbitrary
`ENNReal`-valued kernel `K` (no measurability or integrability hypothesis) and an arbitrary
`ENNReal`-valued `Ψ`, the iterated integral of `Ψ (zShift z s) (thShift θ ζ)` against `K` over
the plane equals the iterated integral over the quadrant `(0,∞) × (0,π/2)` of `Ψ` against the
reflected kernel `K (log z - log z', log tan θ - log tan θ')`, with the Jacobian weight of the
change of variables `z' = e^s`, `θ' = arctan (e^ζ)` and the measure preserving reflection
`(s, ζ) ↦ (log z - s, log tan θ - ζ)`.

Both sides are `ENNReal`-valued, so no measurability or finiteness hypothesis is required: the
identity is a pure change of variables (the two one-dimensional substitutions
`lintegral_exp_subst_gen`, `lintegral_arctan_exp_subst_gen` and the invariances of the Lebesgue
measure under translation and negation). -/
theorem subst_kernel_iter {K : ℝ × ℝ → ENNReal} {z θ : ℝ} (hz : 0 < z)
    (hθ : θ ∈ Set.Ioo 0 (Real.pi / 2)) (Ψ : ℝ → ℝ → ENNReal) :
    (∫⁻ s, ∫⁻ ζ, K (s, ζ)
        * Ψ (Work.FTS.StrongEps.zShift z s) (Work.FTS.StrongEps.thShift θ ζ))
      = ∫⁻ z' in Set.Ioi 0, ∫⁻ θ' in Set.Ioo 0 (Real.pi / 2),
          K (Real.log z - Real.log z', Real.log (Real.tan θ) - Real.log (Real.tan θ'))
            * Ψ z' θ' * ENNReal.ofReal (2 / (z' * Real.sin (2 * θ'))) := by
  -- **Step 1.** the log-coordinate substitution `z' = e^s`, `θ' = arctan (e^ζ)` applied to the
  -- quadrant integral, with Jacobian `logJac s ζ = e^s · kappa ζ`.
  have hfirst : (∫⁻ z' in Set.Ioi 0, ∫⁻ θ' in Set.Ioo 0 (Real.pi / 2),
          K (Real.log z - Real.log z', Real.log (Real.tan θ) - Real.log (Real.tan θ'))
            * Ψ z' θ' * ENNReal.ofReal (2 / (z' * Real.sin (2 * θ'))))
      = ∫⁻ s, ∫⁻ ζ, ENNReal.ofReal (Work.FTS.StrongEps.HkSqAux.logJac s ζ)
          * (K (Real.log z - Real.log (Real.exp s),
                Real.log (Real.tan θ) - Real.log (Real.tan (Real.arctan (Real.exp ζ))))
              * Ψ (Real.exp s) (Real.arctan (Real.exp ζ))
              * ENNReal.ofReal
                  (2 / (Real.exp s * Real.sin (2 * Real.arctan (Real.exp ζ))))) :=
    Work.FTS.StrongEps.HkSqAux.lintegral_quad_log_subst
      (fun z' θ' => K (Real.log z - Real.log z', Real.log (Real.tan θ) - Real.log (Real.tan θ'))
            * Ψ z' θ' * ENNReal.ofReal (2 / (z' * Real.sin (2 * θ'))))
  -- **Step 2.** the pointwise simplification: `log (e^s) = s`, `log (tan (arctan (e^ζ))) = ζ`
  -- and the Jacobian cancellation.
  have hmiddle : (∫⁻ s, ∫⁻ ζ, ENNReal.ofReal (Work.FTS.StrongEps.HkSqAux.logJac s ζ)
          * (K (Real.log z - Real.log (Real.exp s),
                Real.log (Real.tan θ) - Real.log (Real.tan (Real.arctan (Real.exp ζ))))
              * Ψ (Real.exp s) (Real.arctan (Real.exp ζ))
              * ENNReal.ofReal
                  (2 / (Real.exp s * Real.sin (2 * Real.arctan (Real.exp ζ))))))
      = ∫⁻ s, ∫⁻ ζ, K (Real.log z - s, Real.log (Real.tan θ) - ζ)
            * Ψ (Real.exp s) (Real.arctan (Real.exp ζ)) := by
    refine MeasureTheory.lintegral_congr fun s => MeasureTheory.lintegral_congr fun ζ => ?_
    simp only [Real.log_exp, Real.tan_arctan]
    set X : ENNReal := K (Real.log z - s, Real.log (Real.tan θ) - ζ) with hX
    set P : ENNReal := Ψ (Real.exp s) (Real.arctan (Real.exp ζ)) with hP
    set Y : ENNReal :=
      ENNReal.ofReal (2 / (Real.exp s * Real.sin (2 * Real.arctan (Real.exp ζ)))) with hY
    set Z : ENNReal := ENNReal.ofReal (Work.FTS.StrongEps.HkSqAux.logJac s ζ) with hZ
    have hw : Z * Y = 1 := by
      rw [hZ, hY, ← ENNReal.ofReal_mul (Work.FTS.StrongEps.HkSqAux.logJac_nonneg s ζ),
        logJac_mul_weight, ENNReal.ofReal_one]
    calc Z * (X * P * Y) = (Z * Y) * (X * P) := by ac_rfl
      _ = 1 * (X * P) := by rw [hw]
      _ = X * P := one_mul _
  -- **Step 3.** the measure preserving reflection `(s, ζ) ↦ (log z - s, log tan θ - ζ)`.
  have hlast : (∫⁻ s, ∫⁻ ζ, K (Real.log z - s, Real.log (Real.tan θ) - ζ)
            * Ψ (Real.exp s) (Real.arctan (Real.exp ζ)))
      = ∫⁻ s, ∫⁻ ζ, K (s, ζ)
        * Ψ (Work.FTS.StrongEps.zShift z s) (Work.FTS.StrongEps.thShift θ ζ) := by
    have hF := lintegral_prod_neg_sub
      (fun a b => K (a, b)
        * Ψ (Real.exp (Real.log z - a))
            (Real.arctan (Real.exp (Real.log (Real.tan θ) - b))))
      (Real.log z) (Real.log (Real.tan θ))
    have h1 : ∀ s : ℝ, Real.exp (Real.log z - s) = z * Real.exp (-s) := fun s => by
      rw [Real.exp_sub, Real.exp_log hz, Real.exp_neg, div_eq_mul_inv]
    have h2 : ∀ ζ : ℝ, Real.exp (Real.log (Real.tan θ) - ζ)
        = Real.tan θ * Real.exp (-ζ) := fun ζ => by
      rw [Real.exp_sub,
        Real.exp_log (Real.tan_pos_of_pos_of_lt_pi_div_two hθ.1 hθ.2), Real.exp_neg,
        div_eq_mul_inv]
    calc (∫⁻ s, ∫⁻ ζ, K (Real.log z - s, Real.log (Real.tan θ) - ζ)
            * Ψ (Real.exp s) (Real.arctan (Real.exp ζ)))
        = ∫⁻ s, ∫⁻ ζ, (fun a b => K (a, b)
              * Ψ (Real.exp (Real.log z - a))
                  (Real.arctan (Real.exp (Real.log (Real.tan θ) - b))))
              (Real.log z - s) (Real.log (Real.tan θ) - ζ) := by
          refine MeasureTheory.lintegral_congr fun s =>
            MeasureTheory.lintegral_congr fun ζ => ?_
          simp only
          rw [show Real.log z - (Real.log z - s) = s from by ring,
            show Real.log (Real.tan θ) - (Real.log (Real.tan θ) - ζ) = ζ from by ring]
      _ = ∫⁻ s, ∫⁻ ζ, (fun a b => K (a, b)
              * Ψ (Real.exp (Real.log z - a))
                  (Real.arctan (Real.exp (Real.log (Real.tan θ) - b)))) s ζ := hF
      _ = ∫⁻ s, ∫⁻ ζ, K (s, ζ)
            * Ψ (Work.FTS.StrongEps.zShift z s) (Work.FTS.StrongEps.thShift θ ζ) := by
          refine MeasureTheory.lintegral_congr fun s =>
            MeasureTheory.lintegral_congr fun ζ => ?_
          simp only [Work.FTS.StrongEps.zShift, Work.FTS.StrongEps.thShift]
          rw [h1, h2]
  rw [hfirst, hmiddle, hlast]

end Work.FTS.EpsEngine.ThetaFromEpsLeafA
end
-- ===== merged: Submission.Work.FTS.Open2.Chain2 =====
section

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

noncomputable section
open scoped Real Topology
open MeasureTheory Set Filter

namespace Work.FTS.Open2

open Work.FTS.Nonlin
open Work.FTS.VocabO
open Work.FTS.VocabO2
open Work.FTS.OpenPkg
open Work.FTS.Galerkin (Fn Fam slice galFun galField coeffOf IsSolOn IsGalFam ConvLocUnif
  DenseSpan WeakDetermines IsDynWeakOn ProfileBdd EquicontSpace EquicontTau profileFam RegPkg prof
  galFam GlobalODEExistence IsDynGSolWith dynLin dynRHS)

set_option autoImplicit false
set_option linter.unusedVariables false



end Work.FTS.Open2
end
end
-- ===== merged: Submission.Work.FTS.RegPkgGal.Der.zderiv_N0 =====
section

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

/-!
# `Work.FTS.RegPkgGal.Der.zderiv_N0`

The `z`-derivative bound for the quadratic term `N₀` of the fake-time equation.  The statement is

  `∃ Nc, C1Jet α S Nc (fun z θ τ => N0 (pExp α) (Ftau (pExp α) g τ) (gSlice g τ) z θ)`,

i.e. the composite of the six summands of `N₀` is *jointly* `α`-Hölder with a uniform value bound
(the `Jet` half, which is `Der.jet_N0`) **and** has `z`-slices differentiable on `z > 0` with a
uniform derivative bound.

The two halves are produced by the same calculus: `C1Jet α S N h` bundles a `Jet α S N h` and the
`z`-differentiability bound with the *same* constant `N`.  The closure of `C1Jet` under
`neg`/`add`/`mul`/`const_mul`/`congr` is `Work.FTS.RegPkgGal.C1Jet.*`, proved in the sibling module
`Submission.Work.FTS.RegPkgGal.Der.zderiv_N`; this file uses it and assembles `N₀` from its six
summands.

The one input that is not a hypothesis of the statement is the static profile `F_* = Fstar (pExp α)`
itself: it enters through the perturbation `g(τ) = F(τ) - F_*` (third summand) and through the
constants `L₁₂(F_*)`, `∂_θF_*`, `D_zF_*`.  Its `C1Jet`-data is `c1JetFstar_aux` below (value bound
from `fstar_abs_le_gamma`/`Gamma ≤ 1`, modulus from `fstar_joint_modulus`, `z`-derivative from
`deriv_fstar_z` + `fstarDz_abs_le`).
-/

noncomputable section

set_option autoImplicit false

namespace Work.FTS.RegPkgGal.Der

/-! ## The static profile as a `C1Jet` -/

/-- **The static profile `F_* = Fstar (pExp α)` is a `C1Jet`** with constant `100 + 20·pExp α`:
the value bound `|F_*| ≤ 20Γ ≤ 20 ≤ 100` (`fstar_abs_le_gamma`, `Gamma_le_one`), the joint modulus
`fstar_joint_modulus` (constant `100`, and `F_*` does not depend on `τ`), and the explicit
`z`-derivative `deriv_fstar_z` bounded by `20·pExp α` (`fstarDz_abs_le`). -/
theorem c1JetFstar_aux {α S : ℝ} (hα : 0 < α) (hα13 : α ≤ 1 / 3) :
    Work.FTS.RegPkgGal.C1Jet α S (100 + 20 * Work.FTS.Regularity.pExp α)
      (fun z θ _ => Work.Construction.Fstar (Work.FTS.Regularity.pExp α) z θ) := by
  have hp0 : 0 < Work.FTS.Regularity.pExp α := Work.FTS.Regularity.pExp_pos hα
  have hN0 : 0 ≤ 100 + 20 * Work.FTS.Regularity.pExp α := by linarith
  refine ⟨⟨hN0, ?_, ?_⟩, ?_⟩
  · intro z θ τ hz hθ _
    have h1 := Work.FTS.Regularity.fstar_abs_le_gamma hα hα13 (z := z) (θ := θ) hz hθ
    have hG1 : Work.FTS.Regularity.Gamma α θ ≤ 1 :=
      Work.ConstructionInstance.Gamma_le_one hα.le hθ
    calc |Work.Construction.Fstar (Work.FTS.Regularity.pExp α) z θ|
        ≤ 20 * Work.FTS.Regularity.Gamma α θ := h1
      _ ≤ 20 * 1 := mul_le_mul_of_nonneg_left hG1 (by norm_num)
      _ ≤ 100 + 20 * Work.FTS.Regularity.pExp α := by linarith
  · intro z z' θ θ' τ τ' hz hz' hθ hθ' hτ hτ'
    have h1 := Work.FTS.Regularity.fstar_joint_modulus hα hα13 hz hz' hθ hθ'
    have h2 : (|z - z'| + |θ - θ'|) ^ α ≤ (|z - z'| + |θ - θ'| + |τ - τ'|) ^ α :=
      Real.rpow_le_rpow (by positivity) (by linarith [abs_nonneg (τ - τ')]) hα.le
    calc |Work.Construction.Fstar (Work.FTS.Regularity.pExp α) z θ
            - Work.Construction.Fstar (Work.FTS.Regularity.pExp α) z' θ'|
        ≤ 100 * (|z - z'| + |θ - θ'|) ^ α := h1
      _ ≤ 100 * (|z - z'| + |θ - θ'| + |τ - τ'|) ^ α := mul_le_mul_of_nonneg_left h2 (by norm_num)
      _ ≤ (100 + 20 * Work.FTS.Regularity.pExp α)
            * (|z - z'| + |θ - θ'| + |τ - τ'|) ^ α :=
          mul_le_mul_of_nonneg_right (by linarith)
            (Real.rpow_nonneg (by positivity) α)
  · intro τ hτ θ hθ z hz
    have hzp : 0 < z := hz
    have hz1 : -1 < z := by linarith
    refine ⟨deriv (fun z' => Work.Construction.Fstar (Work.FTS.Regularity.pExp α) z' θ) z, ?_, ?_⟩
    · have hdiff : DifferentiableAt ℝ
          (fun z' => Work.Construction.Fstar (Work.FTS.Regularity.pExp α) z' θ) z := by
        have hfun : (fun z' => Work.Construction.Fstar (Work.FTS.Regularity.pExp α) z' θ)
            = fun z' => (Work.FTS.Regularity.pExp α * (Work.Spaces.Gam (Work.FTS.Regularity.pExp α) θ
                / Work.Spaces.c (Work.FTS.Regularity.pExp α))) * Work.FM.Fstar z' := by
          funext z'
          rw [Work.Construction.Fstar]
        rw [hfun]
        exact ((Work.FM.hasDerivAt_Fstar z hz1).const_mul _).differentiableAt
      exact hdiff.hasDerivAt
    · rw [Work.FTS.Regularity.deriv_fstar_z]
      exact le_trans (Work.FTS.Regularity.fstarDz_abs_le hα hα13 hzp.le hθ)
        (by linarith)

/-! ## The angular coefficient `c₂` as a `C1Jet` -/

/-- `θ ↦ c₂(θ) = cos 2θ - sin²θ` is a `C1Jet` with constant `4`: its `Jet` is `jN0_c2m` and its
`z`-slices are constant. -/
theorem c1JetC2m_aux {α S : ℝ} (hα : 0 < α) (hα1 : α ≤ 1) :
    Work.FTS.RegPkgGal.C1Jet α S 4 (fun z θ _ => Work.Construction.c2m θ) := by
  refine ⟨jN0_c2m (S := S) hα hα1, ?_⟩
  intro τ hτ θ hθ z hz
  exact ⟨0, by simpa using hasDerivAt_const (x := z) (c := Work.Construction.c2m θ),
    by norm_num⟩

theorem zderiv_N0 {α S : ℝ} {g : ℝ → ℝ → ℝ → ℝ} {N₁ N₂ N₃ N₄ N₅ N₆ N₇ : ℝ}
    (hα : 0 < α) (hα13 : α ≤ 1 / 3) (hS : 0 < S)
    (hF : Work.FTS.RegPkgGal.C1Jet α S N₁ (fun z θ τ => Work.Construction.Ftau
      (Work.FTS.Regularity.pExp α) g τ z θ))
    (hDthF : Work.FTS.RegPkgGal.C1Jet α S N₂ (fun z θ τ => Work.Spaces.Dth
      (fun z θ => Work.Construction.Ftau (Work.FTS.Regularity.pExp α) g τ z θ) z θ))
    (hDzF : Work.FTS.RegPkgGal.C1Jet α S N₃ (fun z θ τ => Work.Spaces.Dz
      (fun z θ => Work.Construction.Ftau (Work.FTS.Regularity.pExp α) g τ z θ) z θ))
    (hDzg : Work.FTS.RegPkgGal.C1Jet α S N₃ (fun z θ τ => Work.Spaces.Dz
      (fun z θ => g z θ τ) z θ))
    (hL12g : Work.FTS.RegPkgGal.C1Jet α S N₄ (fun z θ τ => Work.Coercivity.L12f
      (Work.FTS.Regularity.gSlice g τ) z))
    (hL12Fstar : Work.FTS.RegPkgGal.C1Jet α S N₅ (fun z θ τ => Work.Coercivity.L12f
      (fun z θ => Work.Construction.Fstar (Work.FTS.Regularity.pExp α) z θ) z))
    (hDthFstar : Work.FTS.RegPkgGal.C1Jet α S N₆ (fun z θ τ => Work.Spaces.Dth
      (fun z θ => Work.Construction.Fstar (Work.FTS.Regularity.pExp α) z θ) z θ))
    (hDzFstar : Work.FTS.RegPkgGal.C1Jet α S N₇ (fun z θ τ => Work.Spaces.Dz
      (fun z θ => Work.Construction.Fstar (Work.FTS.Regularity.pExp α) z θ) z θ)) :
    ∃ Nc : ℝ, Work.FTS.RegPkgGal.C1Jet α S Nc
      (fun z θ τ => Work.Construction.N0 (Work.FTS.Regularity.pExp α)
        (Work.Construction.Ftau (Work.FTS.Regularity.pExp α) g τ)
        (Work.FTS.Regularity.gSlice g τ) z θ) := by
  have hα1 : α ≤ 1 := by linarith
  -- the static profile and the perturbation `g = F(τ) - F_*`
  have hFst : Work.FTS.RegPkgGal.C1Jet α S (100 + 20 * Work.FTS.Regularity.pExp α)
      (fun z θ _ => Work.Construction.Fstar (Work.FTS.Regularity.pExp α) z θ) :=
    c1JetFstar_aux hα hα13
  have hgs : Work.FTS.RegPkgGal.C1Jet α S (N₁ + (100 + 20 * Work.FTS.Regularity.pExp α))
      (fun z θ τ => g z θ τ) := by
    refine Work.FTS.RegPkgGal.C1Jet.congr
      (Work.FTS.RegPkgGal.C1Jet.add hF (Work.FTS.RegPkgGal.C1Jet.neg hFst)) ?_
    intro z θ τ hz hθ hτ
    simp only [Work.Construction.Ftau]
    ring
  have hc2 : Work.FTS.RegPkgGal.C1Jet α S 4 (fun z θ _ => Work.Construction.c2m θ) :=
    c1JetC2m_aux hα hα1
  -- the eight `C1Jet` slots, in the normalised form used by `N₀`
  have hL12Fst : Work.FTS.RegPkgGal.C1Jet α S N₅ (fun z θ _ =>
      Work.Coercivity.L12f (Work.Construction.Fstar (Work.FTS.Regularity.pExp α)) z) := hL12Fstar
  have hDthFst : Work.FTS.RegPkgGal.C1Jet α S N₆ (fun z θ _ =>
      Work.Spaces.Dth (Work.Construction.Fstar (Work.FTS.Regularity.pExp α)) z θ) := hDthFstar
  have hDzFst : Work.FTS.RegPkgGal.C1Jet α S N₇ (fun z θ _ =>
      Work.Spaces.Dz (Work.Construction.Fstar (Work.FTS.Regularity.pExp α)) z θ) := hDzFstar
  have hL12gs : Work.FTS.RegPkgGal.C1Jet α S N₄ (fun z θ τ =>
      Work.Coercivity.L12f (Work.FTS.Regularity.gSlice g τ) z) := hL12g
  have hDthF' : Work.FTS.RegPkgGal.C1Jet α S N₂ (fun z θ τ =>
      Work.Spaces.Dth (Work.Construction.Ftau (Work.FTS.Regularity.pExp α) g τ) z θ) := hDthF
  have hDzF' : Work.FTS.RegPkgGal.C1Jet α S N₃ (fun z θ τ =>
      Work.Spaces.Dz (Work.Construction.Ftau (Work.FTS.Regularity.pExp α) g τ) z θ) := hDzF
  have hDzgs : Work.FTS.RegPkgGal.C1Jet α S N₃ (fun z θ τ =>
      Work.Spaces.Dz (Work.FTS.Regularity.gSlice g τ) z θ) := hDzg
  -- the six summands of `N₀`
  have hT1 : Work.FTS.RegPkgGal.C1Jet α S _ (fun z θ τ =>
      (3 / (2 * Work.FTS.Regularity.pExp α)) * (Work.Coercivity.L12f
        (Work.Construction.Fstar (Work.FTS.Regularity.pExp α)) z
        * Work.Spaces.Dth (Work.Construction.Fstar (Work.FTS.Regularity.pExp α)) z θ)) :=
    Work.FTS.RegPkgGal.C1Jet.const_mul (c := 3 / (2 * Work.FTS.Regularity.pExp α))
      (Work.FTS.RegPkgGal.C1Jet.mul hL12Fst hDthFst)
  have hT2 : Work.FTS.RegPkgGal.C1Jet α S _ (fun z θ τ =>
      -(Work.Construction.c2m θ * (Work.Coercivity.L12f
        (Work.Construction.Fstar (Work.FTS.Regularity.pExp α)) z
        * Work.Spaces.Dz (Work.Construction.Fstar (Work.FTS.Regularity.pExp α)) z θ))) :=
    Work.FTS.RegPkgGal.C1Jet.neg (Work.FTS.RegPkgGal.C1Jet.mul hc2
      (Work.FTS.RegPkgGal.C1Jet.mul hL12Fst hDzFst))
  have hT3 : Work.FTS.RegPkgGal.C1Jet α S _ (fun z θ τ =>
      (1 / Work.FTS.Regularity.pExp α) * (Work.Coercivity.L12f
        (Work.FTS.Regularity.gSlice g τ) z * g z θ τ)) :=
    Work.FTS.RegPkgGal.C1Jet.const_mul (c := 1 / Work.FTS.Regularity.pExp α)
      (Work.FTS.RegPkgGal.C1Jet.mul hL12gs hgs)
  have hT4 : Work.FTS.RegPkgGal.C1Jet α S _ (fun z θ τ =>
      (3 / (2 * Work.FTS.Regularity.pExp α)) * (Work.Coercivity.L12f
        (Work.FTS.Regularity.gSlice g τ) z
        * Work.Spaces.Dth (Work.Construction.Ftau (Work.FTS.Regularity.pExp α) g τ) z θ)) :=
    Work.FTS.RegPkgGal.C1Jet.const_mul (c := 3 / (2 * Work.FTS.Regularity.pExp α))
      (Work.FTS.RegPkgGal.C1Jet.mul hL12gs hDthF')
  have hT5 : Work.FTS.RegPkgGal.C1Jet α S _ (fun z θ τ =>
      -(Work.Construction.c2m θ * (Work.Coercivity.L12f
        (Work.FTS.Regularity.gSlice g τ) z
        * Work.Spaces.Dz (Work.Construction.Ftau (Work.FTS.Regularity.pExp α) g τ) z θ))) :=
    Work.FTS.RegPkgGal.C1Jet.neg (Work.FTS.RegPkgGal.C1Jet.mul hc2
      (Work.FTS.RegPkgGal.C1Jet.mul hL12gs hDzF'))
  have hT6 : Work.FTS.RegPkgGal.C1Jet α S _ (fun z θ τ =>
      -(Work.Construction.c2m θ * (Work.Coercivity.L12f
        (Work.Construction.Fstar (Work.FTS.Regularity.pExp α)) z
        * Work.Spaces.Dz (Work.FTS.Regularity.gSlice g τ) z θ))) :=
    Work.FTS.RegPkgGal.C1Jet.neg (Work.FTS.RegPkgGal.C1Jet.mul hc2
      (Work.FTS.RegPkgGal.C1Jet.mul hL12Fst hDzgs))
  refine ⟨_, Work.FTS.RegPkgGal.C1Jet.congr
    (Work.FTS.RegPkgGal.C1Jet.add (Work.FTS.RegPkgGal.C1Jet.add
      (Work.FTS.RegPkgGal.C1Jet.add (Work.FTS.RegPkgGal.C1Jet.add
        (Work.FTS.RegPkgGal.C1Jet.add hT1 hT2) hT3) hT4) hT5) hT6) ?_⟩
  intro z θ τ hz hθ hτ
  simp only [Work.Construction.N0, Work.Construction.L12, Work.Coercivity.L12f,
    Work.Spaces.Dth, Work.Construction.s2, Work.FTS.Regularity.gSlice]
  ring

end Work.FTS.RegPkgGal.Der
end
end
-- ===== merged: Submission.Work.FTS.StrongEps.E4R3.N4C.rows.rowsN1 =====
section

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

noncomputable section
open scoped Real Topology
open MeasureTheory Set Filter

namespace Work.FTS.StrongEps.E4R3.N4C.rows

open Work.FTS.Galerkin (Fn)
open Work.FTS.Nonlin (Xn)

set_option autoImplicit false
set_option linter.unusedVariables false

/-! ## Row 8: `N₁^{gg} = 2 ℛ(Φ̃_g) g` -/

theorem rowN1gg (IP : ℝ → Fn → Fn → ℝ)
    {α₂ Ci Ct Ce Cs : ℝ} (hN : Work.FTS.OpenPkg.N4Norm' Ci α₂)
    (hE : N4ExtraH IP α₂ Ct) :
    ∃ K : ℝ, 0 < K ∧ ∀ {α : ℝ} {g Φs Φg : Fn},
      CtxT Cs Ce α₂ α g Φs Φg →
      Xn α (Work.FTS.Nonlin.N1gg α g Φg)
        ≤ K * (α ^ (-(1 / 2 : ℝ)) * Xn α g ^ 2) := by
  obtain ⟨hCi, _⟩ := hN.pos
  have hmax : 0 < max Ce 1 := lt_of_lt_of_le zero_lt_one (le_max_right Ce 1)
  refine ⟨2 * Ci * max Ce 1, mul_pos (mul_pos (by norm_num) hCi) hmax, ?_⟩
  intro α g Φs Φg h
  -- the coefficient `H = ℛ(Φ̃_g)` and the profile
  have hRreg : Work.FTS.VocabO.HQo α 4
      (Work.Construction.Rop α (Work.FTS.Nonlin.PhiTg α g Φg)) := h.hell.R.1
  have hRB : Work.FTS.Nonlin.Xn α
        (Work.Construction.Rop α (Work.FTS.Nonlin.PhiTg α g Φg))
      ≤ Ce * Work.FTS.Nonlin.Xn α g := h.hell.R.2
  have hg4 : Work.FTS.VocabO.HQo α 4 g := h.hqo4
  have hαIoc : α ∈ Set.Ioc 0 α₂ := ⟨h.hα, h.hαα₂⟩
  have hprod := hN.prod α hαIoc (Work.Construction.Rop α (Work.FTS.Nonlin.PhiTg α g Φg)) g
    hRreg hg4
  have hXg : 0 ≤ Work.FTS.Nonlin.Xn α g := Work.Spaces.HkNorm_nonneg α 4 g
  have hA : 0 ≤ α ^ (-(1 / 2 : ℝ)) := Real.rpow_nonneg h.hα.le _
  -- `N₁^{gg}` is `2` times the product
  have heq : Work.FTS.Nonlin.N1gg α g Φg = fun z θ =>
      2 * (Work.Construction.Rop α (Work.FTS.Nonlin.PhiTg α g Φg) z θ * g z θ) := by
    funext z θ
    simp only [Work.FTS.Nonlin.N1gg]
    ring
  rw [heq, Work.FTS.Nonlinear.Pieces.RowsN0Aux.Xn_const_mul,
    abs_of_pos (by norm_num : (0 : ℝ) < 2)]
  have hbound : Work.FTS.Nonlin.Xn α
        (fun z θ => Work.Construction.Rop α (Work.FTS.Nonlin.PhiTg α g Φg) z θ * g z θ)
      ≤ (Ci * max Ce 1) * (α ^ (-(1 / 2 : ℝ)) * Work.FTS.Nonlin.Xn α g ^ 2) := by
    refine le_trans hprod.2 ?_
    have hp : 0 ≤ Ci * α ^ (-(1 / 2 : ℝ)) := mul_nonneg hCi.le hA
    have h1 : Ci * α ^ (-(1 / 2 : ℝ))
          * Work.FTS.Nonlin.Xn α (Work.Construction.Rop α (Work.FTS.Nonlin.PhiTg α g Φg))
          * Work.FTS.Nonlin.Xn α g
        ≤ Ci * α ^ (-(1 / 2 : ℝ)) * (Ce * Work.FTS.Nonlin.Xn α g)
          * Work.FTS.Nonlin.Xn α g :=
      mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_left hRB hp) hXg
    have h2 : Ci * α ^ (-(1 / 2 : ℝ)) * (Ce * Work.FTS.Nonlin.Xn α g)
          * Work.FTS.Nonlin.Xn α g
        ≤ Ci * α ^ (-(1 / 2 : ℝ)) * (max Ce 1 * Work.FTS.Nonlin.Xn α g)
          * Work.FTS.Nonlin.Xn α g :=
      mul_le_mul_of_nonneg_right
        (mul_le_mul_of_nonneg_left
          (mul_le_mul_of_nonneg_right (le_max_left Ce 1) hXg) hp) hXg
    refine le_trans h1 (le_trans h2 ?_)
    have he : Ci * α ^ (-(1 / 2 : ℝ)) * (max Ce 1 * Work.FTS.Nonlin.Xn α g)
          * Work.FTS.Nonlin.Xn α g
        = (Ci * max Ce 1) * (α ^ (-(1 / 2 : ℝ)) * Work.FTS.Nonlin.Xn α g ^ 2) := by
      ring
    rw [he]
  have h2bound := mul_le_mul_of_nonneg_left hbound (by norm_num : (0 : ℝ) ≤ 2)
  have he2 : 2 * ((Ci * max Ce 1) * (α ^ (-(1 / 2 : ℝ)) * Work.FTS.Nonlin.Xn α g ^ 2))
      = (2 * Ci * max Ce 1) * (α ^ (-(1 / 2 : ℝ)) * Work.FTS.Nonlin.Xn α g ^ 2) := by
    ring
  rw [he2] at h2bound
  exact h2bound

/-! ## Row 11: `N₁^{**} = 2 ℛ(Φ̃_*) F_*` -/

theorem rowN1ss (IP : ℝ → Fn → Fn → ℝ)
    {α₂ Ci Ct Ce Cs : ℝ} (hN : Work.FTS.OpenPkg.N4Norm' Ci α₂)
    (hE : N4ExtraH IP α₂ Ct) :
    ∃ K : ℝ, 0 < K ∧ ∀ {α : ℝ} {g Φs Φg : Fn},
      CtxT Cs Ce α₂ α g Φs Φg →
      Xn α (Work.FTS.Nonlin.N1ss α Φs) ≤ K * α ^ 2 := by
  obtain ⟨C, hC, hCb⟩ := Work.FTS.StrongPersist.L3Rhs.N1ssPriced
  refine ⟨C * (1 + |Cs|), mul_pos hC (by positivity), ?_⟩
  intro α g Φs Φg h
  exact (hCb α ⟨h.hα, h.hα1⟩ Cs Φs h.hs).2

/-! ## Rows 9 and 10 (sibling modules `rows/rowN1gs`, `rows/rowN1sg`) -/

/-! ## The row table -/

theorem rowsN1 (IP : ℝ → Work.FTS.Galerkin.Fn → Work.FTS.Galerkin.Fn → ℝ)
    {α₂ Ci Ct Ce Cs : ℝ} (hN : Work.FTS.OpenPkg.N4Norm' Ci α₂)
    (hE : Work.FTS.StrongEps.E4R3.N4C.N4ExtraH IP α₂ Ct) :
    ∃ K : ℝ, 0 < K ∧ ∀ {α : ℝ} {g Φs Φg : Work.FTS.Galerkin.Fn},
      Work.FTS.StrongEps.E4R3.N4C.CtxT Cs Ce α₂ α g Φs Φg →
      Work.FTS.Nonlin.Xn α (Work.FTS.Nonlin.N1gg α g Φg)
          ≤ K * (α ^ (-(1 / 2 : ℝ)) * Work.FTS.Nonlin.Xn α g ^ 2) ∧
      Work.FTS.Nonlin.Xn α (Work.FTS.Nonlin.N1gs α g Φg)
          ≤ K * (Real.sqrt α * Work.FTS.Nonlin.Xn α g) ∧
      Work.FTS.Nonlin.Xn α (Work.FTS.Nonlin.N1sg α Φs g)
          ≤ K * (Real.sqrt α * Work.FTS.Nonlin.Xn α g) ∧
      Work.FTS.Nonlin.Xn α (Work.FTS.Nonlin.N1ss α Φs) ≤ K * α ^ 2 := by
  obtain ⟨K8, hK8, h8⟩ := rowN1gg IP hN hE
  obtain ⟨K9, hK9, h9⟩ := rowN1gs IP hN hE
  obtain ⟨K10, hK10, h10⟩ := rowN1sg IP hN hE
  obtain ⟨K11, hK11, h11⟩ := rowN1ss IP hN hE
  refine ⟨K8 + K9 + K10 + K11 + 1, by linarith, ?_⟩
  intro α g Φs Φg hctx
  have hXg : 0 ≤ Work.FTS.Nonlin.Xn α g := Work.Spaces.HkNorm_nonneg α 4 g
  have hα : 0 < α := hctx.hα
  have e8 : K8 ≤ K8 + K9 + K10 + K11 + 1 := by linarith
  have e9 : K9 ≤ K8 + K9 + K10 + K11 + 1 := by linarith
  have e10 : K10 ≤ K8 + K9 + K10 + K11 + 1 := by linarith
  have e11 : K11 ≤ K8 + K9 + K10 + K11 + 1 := by linarith
  refine ⟨?_, ?_, ?_, ?_⟩
  · refine le_trans (h8 hctx) (mul_le_mul_of_nonneg_right e8 ?_)
    exact mul_nonneg (Real.rpow_nonneg hα.le _) (sq_nonneg _)
  · refine le_trans (h9 hctx) (mul_le_mul_of_nonneg_right e9 ?_)
    exact mul_nonneg (Real.sqrt_nonneg α) hXg
  · refine le_trans (h10 hctx) (mul_le_mul_of_nonneg_right e10 ?_)
    exact mul_nonneg (Real.sqrt_nonneg α) hXg
  · refine le_trans (h11 hctx) (mul_le_mul_of_nonneg_right e11 ?_)
    exact sq_nonneg α

end Work.FTS.StrongEps.E4R3.N4C.rows
end
end
-- ===== merged: Submission.Work.FTS.StrongEps.E4R3.N4C.rows.rowsN4b =====
section

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

namespace Work.FTS.StrongEps.E4R3.N4C.rows

open scoped Real Topology
open MeasureTheory Set Filter

open Work.FTS.Galerkin (Fn)

set_option autoImplicit false
set_option linter.unusedVariables false
set_option maxHeartbeats 1600000

/-! ## The radial coefficient

`-(1/2)·FK(F_*) = -α·hKer`, so all the one-dimensional facts of
`Nonlinear/Pieces/RNP/row22.lean` apply: `hKer` is `C^∞` on `(0,∞)` and the `𝒲^{4,∞}`-norm of
`c·hKer` is at most `200|c|`. -/

/-- `(z,θ) ↦ c·z/(1+z)²` is `C^∞` on the open quadrant. -/
private theorem hKerConst_smoothOpenN4b (c : ℝ) :
    Work.FTS.EllipticEst.SmoothOpen (fun z _ => c * Work.Spaces.hKer z) := by
  refine Work.FTS.NonlinRows.smoothOpen_radial (r := fun z => c * Work.Spaces.hKer z) ?_
  intro n
  have hker : ContDiffOn ℝ n (fun z : ℝ => Work.Spaces.hKer z) (Set.Ioi 0) := by
    simp only [Work.Spaces.hKer_apply]
    refine ContDiffOn.div (n := (n : WithTop ℕ∞)) (s := Set.Ioi 0)
      (contDiffOn_id (𝕜 := ℝ) (s := Set.Ioi 0))
      (((contDiffOn_const (c := (1 : ℝ)) (s := Set.Ioi 0)).add
        (contDiffOn_id (𝕜 := ℝ) (s := Set.Ioi 0))).pow 2) ?_
    intro z hz
    exact pow_ne_zero 2 (by linarith [Set.mem_Ioi.mp hz])
  exact ContDiffOn.const_smul c hker

/-- **Row 22 of the honest §8 table** (pairing bound only): for every honest context,

  `|IP α (N₄^{sg} α g) g| ≤ K·√α·(Xn α g)²`,   `N₄^{sg} α g = -(1/2)·FK(F_*)·D_θ g`.

Constant `K = Ct·(C_W·200) + 1`, with `C_W` the constant of `OpenPkg.WDp_le_WlInf`. -/
theorem rowN4sgHon (IP : ℝ → Fn → Fn → ℝ) {α₂ Ci Ct Cs : ℝ}
    (hN : Work.FTS.OpenPkg.N4Norm' Ci α₂)
    (hE : Work.FTS.StrongEps.E4R3.N4C.N4ExtraH IP α₂ Ct) :
    ∃ K : ℝ, 0 < K ∧ ∀ {α Ce : ℝ} {g Φs Φg : Fn},
      Work.FTS.StrongEps.E4R3.N4C.CtxT Cs Ce α₂ α g Φs Φg →
      |IP α (Work.FTS.Nonlin.N4sg α g) g|
        ≤ K * (Real.sqrt α * Work.FTS.Nonlin.Xn α g ^ 2) := by
  obtain ⟨CW, hCW0, hCW⟩ := Work.FTS.OpenPkg.WDp_le_WlInf
  have hCt0 : 0 < Ct := hE.pos.1
  refine ⟨Ct * (CW * 200) + 1, by positivity, ?_⟩
  intro α Ce g Φs Φg hctx
  have hα : 0 < α := hctx.hα
  have hα1 : α ≤ 1 := hctx.hα1
  have hIoc : α ∈ Set.Ioc 0 α₂ := ⟨hα, hctx.hαα₂⟩
  have hX0 : 0 ≤ Work.FTS.Nonlin.Xn α g := Work.Spaces.HkNorm_nonneg α 4 g
  -- ## the radial coefficient `f = -(1/2)·FK(F_*)`
  set f : Fn := fun z _ => -(1 / 2) * Work.Construction.FK (Work.Construction.Fstar α) z
    with hfdef
  -- `FK(F_*) = α·2z/(1+z)²`, so `f = (-α)·hKer`
  have hcoef : f = fun z _ => (-α) * Work.Spaces.hKer z := by
    funext z θ
    rw [hfdef]
    simp only [Work.FTS.Nonlin.FK_Fstar hα hα1, Work.Spaces.hKer_apply]
    ring
  have hsm_f : Work.FTS.EllipticEst.SmoothOpen f := by
    rw [hcoef]
    exact hKerConst_smoothOpenN4b (-α)
  have hker := Work.FTS.Nonlinear.Pieces.RNP.hKerConstWlInf α (-α)
  have hWmem : Work.Spaces.WlInfMem α 4 f := by
    rw [hcoef]
    exact hker.1
  have hWle : Work.Spaces.WlInf α 4 f ≤ 200 * α := by
    rw [hcoef]
    have h := hker.2
    rw [abs_neg, abs_of_pos hα] at h
    exact h
  -- ## the `D`-sup norm of the coefficient, through `WDp ≤ C_W·WlInf`
  have hWDmem : Work.FTS.VocabO.WDMem 4 f := fun b j hbj =>
    ⟨200 * Work.Spaces.WlInf α 4 f, fun z θ hz hθ1 hθ2 =>
      Work.FTS.OpenPkg.mixed_le_WlInf_200 hα hα1 hsm_f hWmem hbj hz ⟨hθ1, hθ2⟩⟩
  have hWDp : Work.FTS.VocabO.WDp 4 f ≤ CW * (200 * α) :=
    (hCW α f hα hα1 hsm_f hWmem).trans (mul_le_mul_of_nonneg_left hWle hCW0.le)
  -- ## `N₄^{sg}` is the product of the coefficient with `D_θ g`
  have hN4eq : Work.FTS.Nonlin.N4sg α g = fun z θ => f z θ * Work.Spaces.Dth g z θ := by
    funext z θ
    rw [hfdef]
    simp only [Work.FTS.Nonlin.N4sg]
  rw [hN4eq]
  -- ## the transport clause `t4`
  have ht4 := hE.t4 α hIoc f g hsm_f hWDmem hctx.hSmoothOpen hctx.hkMem4 hctx.hkMem5
    hctx.hdecay
  have hXn2 : 0 ≤ Work.FTS.Nonlin.Xn α g ^ 2 := pow_nonneg hX0 2
  have hA0 : 0 ≤ Ct * α ^ (-(1 / 2 : ℝ)) :=
    mul_nonneg hCt0.le (Real.rpow_nonneg hα.le _)
  -- `α^{-1/2}·α = √α`
  have hsqrt : α ^ (-(1 / 2 : ℝ)) * α = Real.sqrt α := by
    have h := (Real.rpow_add hα (-(1 / 2 : ℝ)) (1 : ℝ)).symm
    rw [Real.rpow_one, show -(1 / 2 : ℝ) + 1 = 1 / 2 by norm_num] at h
    rw [h, Real.sqrt_eq_rpow]
  have hchain : |IP α (fun z θ => f z θ * Work.Spaces.Dth g z θ) g|
      ≤ Ct * (CW * 200) * (Real.sqrt α * Work.FTS.Nonlin.Xn α g ^ 2) := by
    refine ht4.trans ?_
    refine (mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_left hWDp hA0) hXn2).trans ?_
    rw [show Ct * α ^ (-(1 / 2 : ℝ)) * (CW * (200 * α)) * Work.FTS.Nonlin.Xn α g ^ 2
        = Ct * (CW * 200) * (α ^ (-(1 / 2 : ℝ)) * α)
          * Work.FTS.Nonlin.Xn α g ^ 2 from by ring, hsqrt]
    exact le_of_eq (by ring)
  refine hchain.trans ?_
  refine mul_le_mul_of_nonneg_right ?_ (mul_nonneg (Real.sqrt_nonneg α) hXn2)
  linarith

theorem rowsN4b (IP : ℝ → Work.FTS.Galerkin.Fn → Work.FTS.Galerkin.Fn → ℝ)
    {α₂ Ci Ct Ce Cs : ℝ} (hN : Work.FTS.OpenPkg.N4Norm' Ci α₂)
    (hE : Work.FTS.StrongEps.E4R3.N4C.N4ExtraH IP α₂ Ct) :
    ∃ K : ℝ, 0 < K ∧ ∀ {α : ℝ} {g Φs Φg : Work.FTS.Galerkin.Fn},
      Work.FTS.StrongEps.E4R3.N4C.CtxT Cs Ce α₂ α g Φs Φg →
      |IP α (Work.FTS.Nonlin.N4sg α g) g| ≤ K * (Real.sqrt α * Work.FTS.Nonlin.Xn α g ^ 2) ∧
      Work.FTS.Nonlin.Xn α (Work.FTS.Nonlin.N4ss α) ≤ K * α ^ 3 := by
  obtain ⟨K1, hK1, h1⟩ := rowN4sgHon IP hN hE
  obtain ⟨K2, hK2, h2⟩ :=
    Work.FTS.StrongEps.E4R3.N4C.rows.N4bRow23.rowN4ssHon IP hN hE
  refine ⟨max K1 K2, lt_of_lt_of_le hK1 (le_max_left K1 K2), ?_⟩
  intro α g Φs Φg hctx
  refine ⟨?_, ?_⟩
  · refine (h1 hctx).trans (mul_le_mul_of_nonneg_right (le_max_left K1 K2) ?_)
    exact mul_nonneg (Real.sqrt_nonneg α) (sq_nonneg _)
  · refine (h2 hctx).trans (mul_le_mul_of_nonneg_right (le_max_right K1 K2) ?_)
    exact pow_nonneg hctx.hα.le 3

end Work.FTS.StrongEps.E4R3.N4C.rows
end
-- ===== merged: Submission.Work.FTS.StrongEps.EpsSqTools.LinAux.bump_mixed_EpsSq_le =====
section

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

noncomputable section

open scoped Real Topology
open MeasureTheory Set Filter

namespace Work.FTS.StrongEps.EpsSqTools.LinAux

set_option autoImplicit false
set_option maxHeartbeats 800000

/-! ## A function supported on the bump box: membership and the uniform bound -/




/-! ## The three levels of `j + i ≤ 1` -/




/-! ## The target -/


end Work.FTS.StrongEps.EpsSqTools.LinAux
end
end
