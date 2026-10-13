import Mathlib.Algebra.Order.Archimedean.Real.Basic
import Mathlib.Order.Filter.Defs
import Submission.Work.FTS.StrongEps.E4R3.Apriori4Proofs.TransferDeriv.Defs
import Submission.Work.FTS.StrongEps.E4R3.Apriori4Proofs.TransferDeriv.JfamPDefectTransfer
import Submission.Work.FTS.StrongEps.EpsE4Thr.HnegCore
import Submission.Work.FTS.StrongEps.EpsE4Thr.HkNorm_epsRHSP_le
import Submission.Work.FTS.StrongEps.epsWP_hkMem4_bnd
import Submission.Work.FTS.StrongEps.epsWP_hkMem4_KW_unif
import Submission.Work.FTS.StrongEps.EpsE4Thr.OpenBarrier
import Submission.Work.FTS.StrongEps.JfamP_norm
import Submission.Work.FTS.StrongEps.L12_Jeps_sub_le4
import Submission.Work.FTS.StrongEps.EpsZeroMode
import Submission.Work.FTS.StrongEps.EpsApprox.HkNorm_Jeps_sub_le
import Submission.Work.FTS.StrongEps.PZeroAux.Pz_l12
import Submission.Work.FTS.StrongEps.PZeroAux.pzNorm_pos
import Submission.Work.FTS.StrongEps.PZeroAux.classC_Pz
import Submission.Work.FTS.StrongEps.PZeroAux.bumpHkNormBound
import Submission.Work.FTS.StrongEps.PZeroAux.PzJepsHkMem
import Submission.Work.FTS.StrongEps.EpsStructP
import Submission.Work.FTS.StrongEps.PZeroScheme
import Submission.Work.FTS.IPGen.IP4Add
import Submission.Work.FTS.StrongPersist.IP6_cs_coeffs
import Submission.Work.FTS.CoercivityFix.Transfer.H1IP_cs_of_mem
import Submission.Work.FTS.GalBasis.cc.L12_add_of_HkMem
import Submission.Work.FTS.EllipticEst.EllHyp_certificates
import Submission.Work.FTS.NonlinRows.NRow10aux.starH_smoothOpen
import Submission.Work.FTS.EllipticEst.HkNorm_const_mul
import Submission.Work.FTS.GalFields.RHS.HkSum

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end
-- NOTE: the statement of `jfamP_defect_bound` below is byte-for-byte the requested one; the
-- import of `TransferDeriv.IP4_transfer_deriv` (a 61 KB module, above the project's per-file
-- build limit) has been replaced by the equivalent transfer estimate
-- `TransferDeriv.JfamPDefectTransfer.IP4_transfer_deriv_local`, assembled from the same proved
-- slot machinery.

namespace Work.FTS.StrongEps.E4R3.Apriori4Proofs.TransferDeriv

open scoped Real Topology
open MeasureTheory Set Filter

open Work.FTS.Galerkin (Fn Fam slice)

set_option autoImplicit false
set_option maxHeartbeats 1600000
set_option linter.unusedVariables false

local notation "IP4" => Work.FTS.CoercivityFix.Assembly.IP4

/-! ## Local algebra of the level-four pairing -/

/-- Symmetry of the level-four pairing (arbitrary coefficients). -/
theorem IP4_symm_local (c₁ c₂ c₁' c₂' c₁'' c₂'' α : ℝ) (f g : Fn) :
    IP4 c₁ c₂ c₁' c₂' c₁'' c₂'' α f g = IP4 c₁ c₂ c₁' c₂' c₁'' c₂'' α g f :=
  Work.FTS.CoercivityFix.Assembly.vc_symm (c₁ := c₁'') (c₂ := c₂'')
    (Work.FTS.CoercivityFix.Assembly.vc_symm (c₁ := c₁') (c₂ := c₂')
      (Work.FTS.CoercivityFix.Assembly.vc_symm (c₁ := c₁) (c₂ := c₂)
        (Work.FTS.CoercivityFix.Assembly.H1IP_comm α))) f g

/-- Cauchy–Schwarz for the level-four pairing on the open class `HQo α 4`. -/
theorem IP4_cs_local (c₁ c₂ c₁' c₂' c₁'' c₂'' : ℝ) :
    ∃ CC : ℝ, 0 ≤ CC ∧ ∀ α ∈ Set.Ioc (0 : ℝ) 1, ∀ f g : Fn,
      Work.FTS.VocabO.HQo α 4 f → Work.FTS.VocabO.HQo α 4 g →
      |IP4 c₁ c₂ c₁' c₂' c₁'' c₂'' α f g| ≤ CC * Work.Spaces.HkNorm α 4 f
        * Work.Spaces.HkNorm α 4 g := by
  refine ⟨(1 + |c₁''| + |c₂''|) * ((1 + |c₁'| + |c₂'|) * ((1 + |c₁| + |c₂|) * 10 ^ 22)),
    by positivity, ?_⟩
  intro α hα f g hf hg
  have hα0 : 0 < α := hα.1
  have hbase : ∀ u v : Fn, Work.FTS.VocabO.HQo α 1 u → Work.FTS.VocabO.HQo α 1 v →
      |Work.Coercivity.H1IP α u v| ≤ 10 ^ 22 * Work.Spaces.HkNorm α 1 u
        * Work.Spaces.HkNorm α 1 v :=
    fun u v hu hv => Work.FTS.CoercivityFix.Transfer.H1IP_cs_of_mem α hα0 u v hu.2 hv.2
  have h1 := Work.FTS.StrongPersist.abs_HkIPStep_le (α := α) hα0 (n := 1)
    (IP := Work.Coercivity.H1IP α) (CC := 10 ^ 22) (c₁ := c₁) (c₂ := c₂)
    (by norm_num) hbase
  have h2 := Work.FTS.StrongPersist.abs_HkIPStep_le (α := α) hα0 (n := 2)
    (IP := Work.Coercivity.HkIPStep c₁ c₂ (Work.Coercivity.H1IP α))
    (CC := (1 + |c₁| + |c₂|) * 10 ^ 22) (c₁ := c₁') (c₂ := c₂') (by positivity) h1
  have h3 := Work.FTS.StrongPersist.abs_HkIPStep_le (α := α) hα0 (n := 3)
    (IP := Work.Coercivity.HkIPStep c₁' c₂'
      (Work.Coercivity.HkIPStep c₁ c₂ (Work.Coercivity.H1IP α)))
    (CC := (1 + |c₁'| + |c₂'|) * ((1 + |c₁| + |c₂|) * 10 ^ 22))
    (c₁ := c₁'') (c₂ := c₂'') (by positivity) h2
  simpa only [Work.FTS.CoercivityFix.Assembly.IP4] using h3 f g hf hg

/-- Additivity of the level-four pairing in its first argument on `HQo α 4`. -/
theorem IP4_add_local (c₁ c₂ c₁' c₂' c₁'' c₂'' α : ℝ) (hα : 0 < α)
    {f₁ f₂ g : Fn}
    (h₁ : Work.FTS.EllipticEst.SmoothOpen f₁) (h₂ : Work.FTS.EllipticEst.SmoothOpen f₂)
    (h₃ : Work.FTS.EllipticEst.SmoothOpen g)
    (m₁ : Work.Spaces.HkMem α 4 f₁) (m₂ : Work.Spaces.HkMem α 4 f₂)
    (m₃ : Work.Spaces.HkMem α 4 g) :
    IP4 c₁ c₂ c₁' c₂' c₁'' c₂'' α (f₁ + f₂) g
      = IP4 c₁ c₂ c₁' c₂' c₁'' c₂'' α f₁ g + IP4 c₁ c₂ c₁' c₂' c₁'' c₂'' α f₂ g :=
  (Work.FTS.IPGen.Comm2o_three α (by linarith)).add f₁ f₂ g h₁ h₂ h₃ m₁ m₂ m₃

/-- Subtracting in the first argument of the level-four pairing. -/
theorem IP4_sub_local (c₁ c₂ c₁' c₂' c₁'' c₂'' α : ℝ) (hα : 0 < α)
    {f₁ f₂ g : Fn}
    (h₁ : Work.FTS.EllipticEst.SmoothOpen f₁) (h₂ : Work.FTS.EllipticEst.SmoothOpen f₂)
    (h₃ : Work.FTS.EllipticEst.SmoothOpen g)
    (m₁ : Work.Spaces.HkMem α 4 f₁) (m₂ : Work.Spaces.HkMem α 4 f₂)
    (m₃ : Work.Spaces.HkMem α 4 g) :
    IP4 c₁ c₂ c₁' c₂' c₁'' c₂'' α (f₁ - f₂) g
      = IP4 c₁ c₂ c₁' c₂' c₁'' c₂'' α f₁ g - IP4 c₁ c₂ c₁' c₂' c₁'' c₂'' α f₂ g := by
  have hsub : f₁ - f₂ + f₂ = f₁ := by
    funext z θ
    simp only [Pi.add_apply, Pi.sub_apply]
    ring
  have h₁' : Work.FTS.EllipticEst.SmoothOpen (f₁ - f₂) :=
    Work.FTS.NonlinRows.smoothOpen_sub h₁ h₂
  have h₂' : Work.FTS.EllipticEst.SmoothOpen (fun z θ => -f₂ z θ) :=
    Work.FTS.StrongEps.smoothOpen_neg_epsWP h₂
  have h₂neg : Work.Spaces.HkMem α 4 (fun z θ => -f₂ z θ) :=
    Work.FTS.StrongEps.hkMem_neg_epsWP m₂
  have m₂' : Work.Spaces.HkMem α 4 (f₁ - f₂) :=
    Work.FTS.EllipticEst.HkMem_add_open h₁ h₂' m₁ h₂neg
  have hadd := IP4_add_local c₁ c₂ c₁' c₂' c₁'' c₂'' α hα h₁' h₂ h₃ m₂' m₂ m₃
  rw [hsub] at hadd
  linarith [hadd]

/-- Congruence of the level-four pairing in its first argument on the open quadrant. -/
theorem IP4_congr_local (c₁ c₂ c₁' c₂' c₁'' c₂'' α : ℝ) (hα : 0 < α) {f f' g : Fn}
    (h : ∀ z θ : ℝ, (z, θ) ∈ Work.Construction.Qd → f z θ = f' z θ) :
    IP4 c₁ c₂ c₁' c₂' c₁'' c₂'' α f g = IP4 c₁ c₂ c₁' c₂' c₁'' c₂'' α f' g :=
  Work.FTS.IPGen.ip4_congr_Qd (α := α) hα h
