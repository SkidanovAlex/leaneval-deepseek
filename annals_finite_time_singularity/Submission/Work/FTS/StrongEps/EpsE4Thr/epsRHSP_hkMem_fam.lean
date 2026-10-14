import Mathlib.Algebra.Order.Archimedean.Real.Basic
import Mathlib.Algebra.Order.Ring.Star
import Mathlib.Basic.Real.Basic
import Mathlib.Order.Filter.Defs
import Mathlib.Tactic.NormNum.Ineq
import Submission.Work.FTS.EllipticEst.EllHyp_certificates
import Submission.Work.FTS.EllipticEst.OpenFTC.absFtcLeIntegralAbsDeriv
import Submission.Work.FTS.GalFields.RHS.HkSum
import Submission.Work.FTS.LocData.ZfarFstar.ZFBase
import Submission.Work.FTS.Nonlinear.Pieces.rl1Pieces.PsgEngine
import Submission.Work.FTS.OpenPkg.WtohWin.Assembly
import Submission.Work.FTS.StrongEps.E4R3.Apriori4Proofs.TransferDeriv.JfamPDefectTransfer
import Submission.Work.FTS.StrongEps.EpsE4Thr.HnegCore
import Submission.Work.FTS.StrongEps.EpsE4Thr.OpenBarrier
import Submission.Work.FTS.StrongEps.EpsLocalPStar.EpsRHSPBdd
import Submission.Work.FTS.StrongEps.EpsRHSPBdd_unif
import Submission.Work.FTS.StrongEps.EpsZeroMode
import Submission.Work.FTS.StrongEps.JfamP_norm
import Submission.Work.FTS.StrongEps.L12_Jeps_sub_le4
import Submission.Work.FTS.StrongEps.PZeroAux.bumpHkNormBound
import Submission.Work.FTS.StrongEps.PZeroAux.softClass_Pz
import Submission.Work.FTS.StrongEps.PZeroScheme
import Submission.Work.FTS.StrongEps.epsWP_hkMem4_KW_unif
import Submission.Work.FTS.StrongEps.wtZ_shift_le
import Submission.Work.FTS.StrongPersist.H6Rows.Npair6BWork.FkAux.fkDzdIterSqLe
import Submission.Work.FTS.StrongPersist.L3Rhs.L3RhsNstarBlock
import Submission.Work.FTS.StrongPersist.N6_prod
import Submission.Work.FTS.TransportS.t3SlotGuarded
import Submission.Work.FTS_RegExport.RXB.sup_bound_all_alpha
import Submission.Work.FTS_RegExport.RXT.Sys.pth_vop_slot_bd
import Submission.Work.H2.T1Q.SliceIntQ
-- ===== merged: Submission.Work.FTS.StrongEps.E4R3.Apriori4Proofs.TransferDeriv.JfamPDefectAlg =====
section

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
end Work.FTS.StrongEps.E4R3.Apriori4Proofs.TransferDeriv
end
-- ===== merged: Submission.Work.FTS.StrongEps.EpsE4Thr.epsRHSP_hkMem_fam =====
section

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

namespace Work.FTS.StrongEps.EpsE4Thr

open Work.FTS.Galerkin (Fn Fam slice)

set_option autoImplicit false

/-- **The strengthened (level-six) form of the family estimate**: along a family `g` satisfying the
standing hypotheses of the projected scheme on `[0,T]`, the scheme's right-hand side
`epsRHSP α ρ ε Φs E g σ` is smooth on the open quadrant and honest in `ℋ⁶` at every fake time
`σ ∈ [0,T]`.

This is `EpsLocalPStar.EpsRHSPBdd` transported from a single profile to the family along
`StrongEps.epsRHSP_eq_slice`: `epsRHSP α ρ ε Φs E g σ = epsRHPSlice α ρ ε Φs E σ (slice g σ)`, and
the class-`C` small-ball data as well as the `ℋ⁶`-size bound required by `EpsRHSPBdd` are exactly
the hypotheses `hC`, `hball`, `hbd` evaluated at `slice g σ`.

`sorry`-free. -/
theorem epsRHSP_smoothOpen_hkMem6_fam {α C₀ Ce Cs B : ℝ} {ρ : ℝ × ℝ → ℝ} {Φs : Work.FTS.Galerkin.Fn} {E : Work.FTS.Galerkin.Fn → Work.FTS.Galerkin.Fn}
    {g : Work.FTS.Galerkin.Fam} {ε T : ℝ}
    (hα : α ∈ Set.Ioc 0 1) (hρ : Work.FTS.StrongEps.IsSmoothKernel ρ) (hε : 0 < ε)
    (hε1 : ε ≤ 1)
    (hEll : ∀ u : Work.FTS.Galerkin.Fn, Work.FTS.ClassC.ClassC α u →
      Work.FTS.VocabO.EllPkgGo α Ce u (E u) ∧ Work.FTS.ClassC.EllPkgK α 6 Ce u (E u))
    (hstar : Work.FTS.VocabO2.StarPkgo2 α Cs Φs)
    (hml : Work.FTS.StrongEps.MuLamOK α C₀ Φs E) (hB : 0 ≤ B)
    (hsm : ∀ s ∈ Set.Icc (0 : ℝ) T, Work.FTS.EllipticEst.SmoothOpen (Work.FTS.Galerkin.slice g s))
    (hmem : ∀ s ∈ Set.Icc (0 : ℝ) T, Work.Spaces.HkMem α 6 (Work.FTS.Galerkin.slice g s))
    (hbd : ∀ s ∈ Set.Icc (0 : ℝ) T, Work.Spaces.HkNorm α 6 (Work.FTS.Galerkin.slice g s) ≤ B)
    (hC : ∀ s ∈ Set.Icc (0 : ℝ) T,
      Work.FTS.ClassC.ClassC α (Work.FTS.StrongEps.Pz (Work.FTS.StrongEps.Jeps ρ ε (Work.FTS.Galerkin.slice g s))))
    (hball : ∀ s ∈ Set.Icc (0 : ℝ) T,
      Work.FTS.Nonlin.Xn α (Work.FTS.StrongEps.Pz (Work.FTS.StrongEps.Jeps ρ ε (Work.FTS.Galerkin.slice g s)))
        ≤ C₀ * α ^ 2) :
    ∀ σ ∈ Set.Icc (0 : ℝ) T,
      Work.FTS.EllipticEst.SmoothOpen (Work.FTS.StrongEps.epsRHSP α ρ ε Φs E g σ)
        ∧ Work.Spaces.HkMem α 6 (Work.FTS.StrongEps.epsRHSP α ρ ε Φs E g σ) := by
  -- the slicewise class-`C` estimate of the scheme's right-hand side
  obtain ⟨_, _, hbdR⟩ :=
    Work.FTS.StrongEps.EpsLocalPStar.EpsRHSPBdd (α := α) (C₀ := C₀) (Ce := Ce) (Cs := Cs)
      (B := B) (ρ := ρ) (Φs := Φs) (E := E) (ε := ε) hα hρ hε hε1 hEll hstar hml hB
  intro σ hσ
  -- the right-hand side of the family at `σ` is the slicewise one at `slice g σ`
  rw [Work.FTS.StrongEps.epsRHSP_eq_slice]
  obtain ⟨hSmo, hMem6, -⟩ :=
    hbdR σ (slice g σ) (hsm σ hσ) (hmem σ hσ) (hbd σ hσ) (hC σ hσ) (hball σ hσ)
  exact ⟨hSmo, hMem6⟩

/-- **`ℋ⁴`-membership of the scheme's right-hand side along a family.**

This is the `ℋ⁴`-membership obligation of the level-four energy estimates of the local existence
scheme.  It is immediate from the stronger level-six form
`epsRHSP_smoothOpen_hkMem6_fam` together with the monotonicity of `HkMem` in the order
(`OpenPkg.HkMem_mono_open`, whose `SmoothOpen` input is the first conjunct of that same estimate):
the `ℋ⁴`-integrand is dominated, term by term, by the `ℋ⁶`-integrand.

`sorry`-free. -/
theorem epsRHSP_hkMem_fam {α C₀ Ce Cs B : ℝ} {ρ : ℝ × ℝ → ℝ} {Φs : Work.FTS.Galerkin.Fn} {E : Work.FTS.Galerkin.Fn → Work.FTS.Galerkin.Fn}
    {g : Work.FTS.Galerkin.Fam} {ε T : ℝ}
    (hα : α ∈ Set.Ioc 0 1) (hρ : Work.FTS.StrongEps.IsSmoothKernel ρ) (hε : 0 < ε)
    (hε1 : ε ≤ 1)
    (hEll : ∀ u : Work.FTS.Galerkin.Fn, Work.FTS.ClassC.ClassC α u →
      Work.FTS.VocabO.EllPkgGo α Ce u (E u) ∧ Work.FTS.ClassC.EllPkgK α 6 Ce u (E u))
    (hstar : Work.FTS.VocabO2.StarPkgo2 α Cs Φs)
    (hml : Work.FTS.StrongEps.MuLamOK α C₀ Φs E) (hB : 0 ≤ B)
    (hsm : ∀ s ∈ Set.Icc (0 : ℝ) T, Work.FTS.EllipticEst.SmoothOpen (Work.FTS.Galerkin.slice g s))
    (hmem : ∀ s ∈ Set.Icc (0 : ℝ) T, Work.Spaces.HkMem α 6 (Work.FTS.Galerkin.slice g s))
    (hbd : ∀ s ∈ Set.Icc (0 : ℝ) T, Work.Spaces.HkNorm α 6 (Work.FTS.Galerkin.slice g s) ≤ B)
    (hC : ∀ s ∈ Set.Icc (0 : ℝ) T,
      Work.FTS.ClassC.ClassC α (Work.FTS.StrongEps.Pz (Work.FTS.StrongEps.Jeps ρ ε (Work.FTS.Galerkin.slice g s))))
    (hball : ∀ s ∈ Set.Icc (0 : ℝ) T,
      Work.FTS.Nonlin.Xn α (Work.FTS.StrongEps.Pz (Work.FTS.StrongEps.Jeps ρ ε (Work.FTS.Galerkin.slice g s)))
        ≤ C₀ * α ^ 2) :
    ∀ σ ∈ Set.Icc (0 : ℝ) T, Work.Spaces.HkMem α 4 (Work.FTS.StrongEps.epsRHSP α ρ ε Φs E g σ) := by
  intro σ hσ
  obtain ⟨hSmo, hMem6⟩ :=
    epsRHSP_smoothOpen_hkMem6_fam (α := α) (C₀ := C₀) (Ce := Ce) (Cs := Cs) (B := B)
      (ρ := ρ) (Φs := Φs) (E := E) (g := g) (ε := ε) (T := T)
      hα hρ hε hε1 hEll hstar hml hB hsm hmem hbd hC hball σ hσ
  -- honesty in `ℋ⁶` descends to `ℋ⁴`, the `ℋ⁴`-integrand being dominated by the `ℋ⁶`-one
  exact Work.FTS.OpenPkg.HkMem_mono_open hSmo 4 (by norm_num) hMem6

end Work.FTS.StrongEps.EpsE4Thr
end
