import Mathlib.Algebra.Order.Ring.Star
import Mathlib.Analysis.Calculus.ContDiff.Operations
import Mathlib.MeasureTheory.Integral.IntegrableOn
import Mathlib.MeasureTheory.Measure.Haar.OfBasis
import Submission.Work.FTS.StrongEps.EpsZero.Pieces
import Submission.Work.FTS.GalBasis.cc.L12_add_of_HkMem
import Submission.Work.FTS.H2.L12densIntegrable
import Submission.Work.FTS.OpenPkg.N4NormExists
import Submission.Work.FTS.GalFields.RHS.Fr_smooth_honest
import Submission.Work.FTS.GalFields.RHS.smoothOpen_N_Ftot_gal
import Submission.Work.FTS.GalFields.RHS.smoothOpen_atoms_of_gal
import Submission.Work.FTS.ClassC.Defs
import Submission.Work.FTS.VocabO2
import Submission.Work.FTS.StrongEps.ClassCRHS.SmoothOpenRHS
import Submission.Work.FTS.IPGen.OpenBasic
import Submission.Work.FTS.NonlinRows.NAux3
import Submission.Work.FTS.EllipticEst.Cert.GbarSin.HkMem_congr_Q0
import Submission.Work.FTS.StrongEps.EpsZero.ClassCHk.LGammaTMem
import Submission.Work.FTS.StrongEps.EpsZero.ClassCHk.N0Mem
import Submission.Work.FTS.StrongEps.EpsZero.ClassCHk.NMem

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

namespace Work.FTS.StrongEps.EpsZero

/-! The statement of `RhsDensIntegrable` mentions `π` in the hypothesis `hzero` (this is the
`π` of `Set.Ioo 0 (π/2)`), and — as requested — it is left free: under Lean's default
`autoImplicit` it is an implicitly bound variable `{π : ℝ}`.  The lakefile sets
`autoImplicit = false`, so we restore the default here rather than touch the statement: the
elaborated type of `RhsDensIntegrable` is then exactly

  `∀ {π : ℝ} {α Ce Cs μ lam : ℝ}, α ∈ Set.Ioc 0 1 → …`,

with the request's text unchanged.  (The `π`-hypothesis is not used in the proof, and the
result is *stronger* than its `π = Real.pi` instance, which is what every caller supplies.) -/
set_option autoImplicit true

theorem RhsDensIntegrable {α Ce Cs μ lam : ℝ} (hα : α ∈ Set.Ioc 0 1) {f : Work.FTS.Galerkin.Fn}
    {E : Work.FTS.Galerkin.Fn → Work.FTS.Galerkin.Fn} {Φs : Work.FTS.Galerkin.Fn}
    (hC : Work.FTS.ClassC.ClassC α f)
    (hzero : ∀ z θ : ℝ, ¬ (0 < z ∧ θ ∈ Set.Ioo 0 (π / 2)) → f z θ = 0)
    (hEll : ∀ u : Work.FTS.Galerkin.Fn, Work.FTS.ClassC.ClassC α u →
      Work.FTS.VocabO.EllPkgGo α Ce u (E u) ∧ Work.FTS.ClassC.EllPkgK α 6 Ce u (E u))
    (hstar : Work.FTS.VocabO2.StarPkgo2 α Cs Φs) :
    MeasureTheory.IntegrableOn (Work.Construction.L12dens (Work.FTS.StrongEps.EpsZero.PLin α f)) (Set.Ioi 0) ∧
    MeasureTheory.IntegrableOn (Work.Construction.L12dens (Work.FTS.StrongEps.EpsZero.PN0 α f)) (Set.Ioi 0) ∧
    MeasureTheory.IntegrableOn (Work.Construction.L12dens (Work.FTS.StrongEps.EpsZero.PN α f (Work.FTS.StrongEps.EpsZero.PPsi E Φs f))) (Set.Ioi 0) ∧
    MeasureTheory.IntegrableOn (Work.Construction.L12dens (Work.FTS.StrongEps.EpsZero.PNs μ lam f)) (Set.Ioi 0) ∧
    MeasureTheory.IntegrableOn (Work.Construction.L12dens (Work.Construction.AK α)) (Set.Ioi 0) ∧
    (∀ z : ℝ, 0 < z → MeasureTheory.IntegrableOn (fun θ : ℝ => Work.Spaces.K θ * Work.FTS.StrongEps.EpsZero.PLin α f z θ / z) Work.Spaces.Iθ) ∧
    (∀ z : ℝ, 0 < z → MeasureTheory.IntegrableOn (fun θ : ℝ => Work.Spaces.K θ * Work.FTS.StrongEps.EpsZero.PN0 α f z θ / z) Work.Spaces.Iθ) ∧
    (∀ z : ℝ, 0 < z → MeasureTheory.IntegrableOn (fun θ : ℝ => Work.Spaces.K θ * Work.FTS.StrongEps.EpsZero.PN α f (Work.FTS.StrongEps.EpsZero.PPsi E Φs f) z θ / z) Work.Spaces.Iθ) ∧
    (∀ z : ℝ, 0 < z → MeasureTheory.IntegrableOn (fun θ : ℝ => Work.Spaces.K θ * Work.FTS.StrongEps.EpsZero.PNs μ lam f z θ / z) Work.Spaces.Iθ) ∧
    (∀ z : ℝ, 0 < z → MeasureTheory.IntegrableOn (fun θ : ℝ => Work.Spaces.K θ * Work.Construction.AK α z θ / z) Work.Spaces.Iθ) := by
  have hα0 : 0 < α := hα.1
  have hα1 : α ≤ 1 := hα.2
  -- the `ℋ⁷`-honesty of the class, and the descent to levels `5` and `4`
  have hmem7 : Work.Spaces.HkMem α 7 f := hC.mem
  have hmem5 : Work.Spaces.HkMem α 5 f :=
    Work.FTS.OpenPkg.HkMem_mono_open hC.reg 5 (by norm_num) hmem7
  have hmem4 : Work.Spaces.HkMem α 4 f :=
    Work.FTS.OpenPkg.HkMem_mono_open hC.reg 4 (by norm_num) hmem7
  have hmem4Dz : Work.Spaces.HkMem α 4 (Work.Spaces.Dz f) :=
    Work.FTS.IPGen.HkMem_Dz_le hC.reg hmem5
  -- the elliptic package for the datum itself, from the uniform witness
  have hE : Work.FTS.VocabO.EllPkgGo α Ce f (E f) := (hEll f hC).1
  -- `C^∞` on the open quadrant of the five summands
  obtain ⟨_, _, hsmLG, hsmN0, hsmN⟩ :=
    Work.FTS.StrongEps.ClassCRHS.SmoothOpenRHS hα0 hα1 hC hE hstar
  have hsmLin : Work.FTS.EllipticEst.SmoothOpen (PLin α f) := hsmLG.neg
  have hsmNs : Work.FTS.EllipticEst.SmoothOpen (PNs μ lam f) :=
    Work.FTS.GalFields.RHS.smoothOpen_Nstar_of hC.reg
  have hsmAK : Work.FTS.EllipticEst.SmoothOpen (Work.Construction.AK α) :=
    Work.FTS.StrongPersist.AK_smoothO α
  -- `ℋ⁴`-honesty of the five summands
  have hmemLin : Work.Spaces.HkMem α 4 (PLin α f) :=
    Work.FTS.LocData.HkMem_neg α 4
      (Work.FTS.StrongEps.EpsZero.ClassCHk.LGammaTMem hα0 hα1 hC hE)
  have hmemN0 : Work.Spaces.HkMem α 4 (PN0 α f) :=
    Work.FTS.StrongEps.EpsZero.ClassCHk.N0Mem hα0 hα1 hC hE
  have hmemN : Work.Spaces.HkMem α 4 (PN α f (PPsi E Φs f)) :=
    Work.FTS.StrongEps.EpsZero.ClassCHk.NMem hα0 hα1 hC hE hstar
  have hmemNs : Work.Spaces.HkMem α 4 (PNs μ lam f) := by
    have h1 : Work.Spaces.HkMem α 4 (fun z θ => (-μ) * f z θ) :=
      Work.FTS.LocData.HkMem_const_mul α 4 (-μ) hmem4
    have h2 : Work.Spaces.HkMem α 4
        (fun z θ => (-(μ + lam + μ * lam)) * Work.Spaces.Dz f z θ) :=
      Work.FTS.LocData.HkMem_const_mul α 4 (-(μ + lam + μ * lam)) hmem4Dz
    have s1 : Work.FTS.EllipticEst.SmoothOpen (fun z θ => (-μ) * f z θ) :=
      Work.FTS.NonlinRows.smoothOpen_const_mul (-μ) hC.reg
    have s2 : Work.FTS.EllipticEst.SmoothOpen
        (fun z θ => (-(μ + lam + μ * lam)) * Work.Spaces.Dz f z θ) :=
      Work.FTS.NonlinRows.smoothOpen_const_mul (-(μ + lam + μ * lam)) hC.reg.Dz
    have hall := Work.FTS.CoercivityFix.Assembly.HkMem_add_open α 4 s1 s2 h1 h2
    refine Work.FTS.EllipticEst.Cert.GbarSin.HkMem_congr_Q0 α 4 hall ?_
    intro z _ θ _
    simp only [Work.Construction.Nstar, Work.Spaces.Dz]
    ring
  have hmemAK : Work.Spaces.HkMem α 4 (Work.Construction.AK α) :=
    Work.FTS.NonlinRows.HkMem_AK α hα0 hα1
  -- the ten integrability clauses, all from the two Cauchy–Schwarz certificates
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact Work.FTS.GalBasis.cc.integrableOn_L12dens_of_SmoothOpen_HkMem hsmLin hmemLin
  · exact Work.FTS.GalBasis.cc.integrableOn_L12dens_of_SmoothOpen_HkMem hsmN0 hmemN0
  · exact Work.FTS.GalBasis.cc.integrableOn_L12dens_of_SmoothOpen_HkMem hsmN hmemN
  · exact Work.FTS.GalBasis.cc.integrableOn_L12dens_of_SmoothOpen_HkMem hsmNs hmemNs
  · exact Work.FTS.GalBasis.cc.integrableOn_L12dens_of_SmoothOpen_HkMem hsmAK hmemAK
  · intro z hz
    exact Work.FTS.GalBasis.cc.integrableOn_slice_of_SmoothOpen_HkMem hsmLin hmemLin hz
  · intro z hz
    exact Work.FTS.GalBasis.cc.integrableOn_slice_of_SmoothOpen_HkMem hsmN0 hmemN0 hz
  · intro z hz
    exact Work.FTS.GalBasis.cc.integrableOn_slice_of_SmoothOpen_HkMem hsmN hmemN hz
  · intro z hz
    exact Work.FTS.GalBasis.cc.integrableOn_slice_of_SmoothOpen_HkMem hsmNs hmemNs hz
  · intro z hz
    exact Work.FTS.GalBasis.cc.integrableOn_slice_of_SmoothOpen_HkMem hsmAK hmemAK hz

end Work.FTS.StrongEps.EpsZero
