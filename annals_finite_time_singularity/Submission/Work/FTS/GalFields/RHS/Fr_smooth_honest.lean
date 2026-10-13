import Mathlib.Algebra.Order.Ring.Star
import Mathlib.Analysis.Calculus.ContDiff.Operations
import Mathlib.Analysis.InnerProductSpace.Basic
import Mathlib.Analysis.SpecialFunctions.Trigonometric.Basic
import Submission.Work.FTS.GalFields.Defs
import Submission.Work.FTS.GalFields.RHS.smoothOpen_atoms_of_gal
import Submission.Work.FTS.OpenPkg.Defs
import Submission.Work.FTS.VocabO2
import Submission.Work.FTS.Nonlinear.Open.Main
import Submission.Work.FTS.EllSol.Assembly
import Submission.Work.FTS.GalFields.Norm.Xn_LGammaT_le

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

/-!
# `RHS/Fr_smooth_honest` — the open-quadrant smoothness and the `ℋ⁴`-honesty of the
dynamic right-hand side `Fr`

`Fr α Φs EllSol g = -𝓛_Γ^T(g) + gRHS(μ,λ,F_*+g, Φ_*+Φ_g, g)` is a finite sum of

* `-𝓛_Γ^T g`,
* `-μ̄·AK α` (a constant times `AK`),
* `N₀ α (F_*+g) g`,
* `N α (F_*+g) (Φ_*+Φ_g)`,
* `N_* μ (lamfun μ) g = -μ·g - (μ+lamfun μ+μ·lamfun μ)·D_z g`,

and every one of these is produced, in this workspace, by

* `smoothOpen_atoms_of_gal` — `C^∞` on the open quadrant `Q₀` of all twelve atoms under
  `GalClass α g` (the honesty of `g`), `StarPkgo2 α Cs Φs`, `EllPkgGo α Ce g Φg`;
* `Norm.Xn_LGammaT_le` — `HkMem α 4 (𝓛_Γ^T g)`;
* `Nonlinear.Open.PiecesHkOpen` — `HkMem α 4` of `AK`, of the blocks `N₀`, `N` and of
  `D_z g` (the `ℋ⁴`-honesty table of the §8 chunks).

The `N_*`-block is the only one not delivered as a package; it is a linear combination of
`g` and `D_z g`, so `LocData.HkMem_const_mul` + `Assembly.HkMem_add_open` +
`HkMem_congr_Q0` give its `ℋ⁴`-honesty from `HkMem α 4 g` and `HkMem α 4 (D_z g)` — no
hypothesis on `μ` (in particular `μ ≠ -1`) is needed, since the statement is only about
*smoothness* and *integrability*, never about a bound in terms of `Xn5`.

The last two conjuncts (the difference with `Fr α Φs EllSol 0`) are the closure of
`SmoothOpen` and of `HkMem α 4` under subtraction, applied to the two instances `g` and `0`
of the first three conjuncts (`GalClass α 0` is `EllSol.galClass_zero`).
-/

namespace Work.FTS.GalFields.RHS

open scoped Real Topology
open MeasureTheory Set Filter

set_option maxHeartbeats 1600000

/-- The modulation constant `μ` of `Fr`, as a function of the data.  This is a pure
abbreviation (it is `Work.Construction.mufunS` applied to the blocks of the right-hand
side); it is introduced only to keep the statements below readable. -/
private noncomputable def MuN (α : ℝ) (Φs : Work.FTS.Galerkin.Fn)
    (EllSol : Work.FTS.Galerkin.Fn → Work.FTS.Galerkin.Fn) (g : Work.FTS.Galerkin.Fn) : ℝ :=
  Work.Construction.mufunS α (Work.Construction.N0 α (Work.Construction.Ftot α g) g)
    (Work.Construction.N α (Work.Construction.Ftot α g)
      (fun z θ => Φs z θ + EllSol g z θ)) g

/-- **The conjunction of the first three conjuncts of `Fr_smooth_honest`**, for an arbitrary
profile `g` of the Galerkin class: `Fr α Φs EllSol g` is `C^∞` on the open quadrant and
honest in `ℋ⁴`.  (The statement of `Fr` unfolds definitionally to the five summands listed
in the module docstring.) -/
private lemma Fr_open_honest {α α₂ Ci Ct Ce Cs : ℝ}
    {IP : ℝ → Work.FTS.Galerkin.Fn → Work.FTS.Galerkin.Fn → ℝ}
    {Φs : Work.FTS.Galerkin.Fn} {EllSol : Work.FTS.Galerkin.Fn → Work.FTS.Galerkin.Fn}
    (hN : Work.FTS.OpenPkg.N4Norm' Ci α₂) (hE : Work.FTS.OpenPkg.N4Extra' IP α₂ Ct)
    (hstar : Work.FTS.VocabO2.StarPkgo2 α Cs Φs)
    (hell : ∀ g : Work.FTS.Galerkin.Fn, Work.FTS.Nonlin.GalClass α g →
      Work.FTS.VocabO.EllPkgGo α Ce g (EllSol g))
    (hα : 0 < α) (hα1 : α ≤ 1) (hαα₂ : α ≤ α₂)
    {g : Work.FTS.Galerkin.Fn} (hgal : Work.FTS.Nonlin.GalClass α g) :
    Work.FTS.EllipticEst.SmoothOpen (Work.FTS.GalFields.Fr α Φs EllSol g) ∧
      Work.Spaces.HkMem α 4 (Work.FTS.GalFields.Fr α Φs EllSol g) := by
  have hsq : Work.FTS.LocData.SmoothQuad g := hgal.reg.1
  have hgS : Work.FTS.EllipticEst.SmoothOpen g :=
    Work.FTS.OpenPkg.smoothOpen_of_smoothQuad hsq
  have hmem6 : Work.Spaces.HkMem α 6 g := hgal.reg.2.1
  have hg4 : Work.Spaces.HkMem α 4 g :=
    Work.FTS.StrongPersist.HkMem_of_le_of_smoothOpen α (by norm_num) hgS hmem6
  have hΦsS : Work.FTS.EllipticEst.SmoothOpen Φs := hstar.smooth
  have hΦgS : Work.FTS.EllipticEst.SmoothOpen (EllSol g) := (hell g hgal).smooth
  -- the twelve `SmoothOpen`-atoms of the right-hand side
  obtain ⟨hL12, hFK, hRopG, hUopG, hVopG, hRopS, hVopS, hLG, hAKs, hN0s, hNs_, hNstars⟩ :=
    smoothOpen_atoms_of_gal hα hα1 hgal hgS hΦsS hΦgS (hell g hgal) hstar
  -- the `ℋ⁴`-honesty table of the §8 chunks
  have hpk : Work.FTS.OpenPkg.PiecesHk α g Φs (EllSol g) :=
    Work.FTS.Nonlinear.Open.PiecesHkOpen IP hN hE hα hα1 hαα₂ hgal hstar (hell g hgal)
  -- `HkMem α 4` of the linear part
  obtain ⟨K, hKpos, hKL⟩ :=
    Work.FTS.GalFields.Norm.Xn_LGammaT_le (Ce := Ce) (Cs := Cs) hN hE
  have hLGT : Work.Spaces.HkMem α 4 (Work.Coercivity.LGammaT α g) :=
    (hKL hα hα1 hαα₂ hgal).1
  -- the two coefficients of the right-hand side
  set mb : ℝ := Work.Construction.mubar (Work.Construction.N0 α (Work.Construction.Ftot α g) g)
      (Work.Construction.N α (Work.Construction.Ftot α g)
        (fun z θ => Φs z θ + EllSol g z θ)) with hmb
  -- `HkMem α 4 (N_* μ (lamfun μ) g)`: a linear combination of `g` and `D_z g`
  have hNs_mem : Work.Spaces.HkMem α 4 (Work.Construction.Nstar (MuN α Φs EllSol g)
      (Work.Construction.lamfun (MuN α Φs EllSol g)) g) := by
    have hμ : Work.Spaces.HkMem α 4 (fun z θ => (-(MuN α Φs EllSol g)) * g z θ) :=
      Work.FTS.LocData.HkMem_const_mul α 4 (-(MuN α Φs EllSol g)) hg4
    have hκ : Work.Spaces.HkMem α 4 (fun z θ =>
        (-(MuN α Φs EllSol g + Work.Construction.lamfun (MuN α Φs EllSol g)
          + MuN α Φs EllSol g * Work.Construction.lamfun (MuN α Φs EllSol g)))
        * Work.Spaces.Dz g z θ) :=
      Work.FTS.LocData.HkMem_const_mul α 4
        (-(MuN α Φs EllSol g + Work.Construction.lamfun (MuN α Φs EllSol g)
          + MuN α Φs EllSol g * Work.Construction.lamfun (MuN α Φs EllSol g))) hpk.pDz
    have hμs : Work.FTS.EllipticEst.SmoothOpen (fun z θ => (-(MuN α Φs EllSol g)) * g z θ) :=
      Work.FTS.NonlinRows.smoothOpen_const_mul (-(MuN α Φs EllSol g)) hgS
    have hκs : Work.FTS.EllipticEst.SmoothOpen (fun z θ =>
        (-(MuN α Φs EllSol g + Work.Construction.lamfun (MuN α Φs EllSol g)
          + MuN α Φs EllSol g * Work.Construction.lamfun (MuN α Φs EllSol g)))
        * Work.Spaces.Dz g z θ) :=
      Work.FTS.NonlinRows.smoothOpen_const_mul _ hgS.Dz
    have hall := Work.FTS.CoercivityFix.Assembly.HkMem_add_open α 4 hμs hκs hμ hκ
    refine Work.FTS.EllipticEst.Cert.GbarSin.HkMem_congr_Q0 α 4 hall ?_
    intro z hz θ hθ
    simp only [Work.Construction.Nstar]
    ring
  -- the smoothness chain
  have s1 : Work.FTS.EllipticEst.SmoothOpen (fun z θ => -(Work.Coercivity.LGammaT α g z θ)) :=
    hLG.neg
  have s2 : Work.FTS.EllipticEst.SmoothOpen
      (fun z θ => (-mb) * Work.Construction.AK α z θ) :=
    Work.FTS.NonlinRows.smoothOpen_const_mul (-mb) hAKs
  have s3 : Work.FTS.EllipticEst.SmoothOpen
      (Work.Construction.N0 α (Work.Construction.Ftot α g) g) := hN0s
  have s4 : Work.FTS.EllipticEst.SmoothOpen (Work.Construction.N α (Work.Construction.Ftot α g)
      (fun z θ => Φs z θ + EllSol g z θ)) := hNs_
  have s5 : Work.FTS.EllipticEst.SmoothOpen (Work.Construction.Nstar (MuN α Φs EllSol g)
      (Work.Construction.lamfun (MuN α Φs EllSol g)) g) := hNstars
  have s23 := Work.FTS.EllipticEst.smoothOpen_add s2 s3
  have s234 := Work.FTS.EllipticEst.smoothOpen_add s23 s4
  have s2345 := Work.FTS.EllipticEst.smoothOpen_add s234 s5
  have stot := Work.FTS.EllipticEst.smoothOpen_add s1 s2345
  -- the honesty chain
  have h1 : Work.Spaces.HkMem α 4 (fun z θ => -(Work.Coercivity.LGammaT α g z θ)) :=
    Work.FTS.NonlinRows.HkMem_neg' α 4 hLGT
  have h2 : Work.Spaces.HkMem α 4 (fun z θ => (-mb) * Work.Construction.AK α z θ) :=
    Work.FTS.LocData.HkMem_const_mul α 4 (-mb) hpk.pAK
  have h3 : Work.Spaces.HkMem α 4 (Work.Construction.N0 α (Work.Construction.Ftot α g) g) :=
    hpk.pN0
  have h4 : Work.Spaces.HkMem α 4 (Work.Construction.N α (Work.Construction.Ftot α g)
      (fun z θ => Φs z θ + EllSol g z θ)) := hpk.pN
  have h23 := Work.FTS.CoercivityFix.Assembly.HkMem_add_open α 4 s2 s3 h2 h3
  have h234 := Work.FTS.CoercivityFix.Assembly.HkMem_add_open α 4 s23 s4 h23 h4
  have h2345 := Work.FTS.CoercivityFix.Assembly.HkMem_add_open α 4 s234 s5 h234 hNs_mem
  have htot := Work.FTS.CoercivityFix.Assembly.HkMem_add_open α 4 s1 s2345 h1 h2345
  exact ⟨stot, htot⟩

theorem Fr_smooth_honest {α α₂ Ci Ct Ce Cs : ℝ} {IP : ℝ → Work.FTS.Galerkin.Fn → Work.FTS.Galerkin.Fn → ℝ}
    {Φs : Work.FTS.Galerkin.Fn} {EllSol : Work.FTS.Galerkin.Fn → Work.FTS.Galerkin.Fn}
    (hN : Work.FTS.OpenPkg.N4Norm' Ci α₂) (hE : Work.FTS.OpenPkg.N4Extra' IP α₂ Ct)
    (hstar : Work.FTS.VocabO2.StarPkgo2 α Cs Φs)
    (hell : ∀ g : Work.FTS.Galerkin.Fn, Work.FTS.Nonlin.GalClass α g →
      Work.FTS.VocabO.EllPkgGo α Ce g (EllSol g))
    (hα : 0 < α) (hα1 : α ≤ 1) (hαα₂ : α ≤ α₂)
    {g : Work.FTS.Galerkin.Fn} (hgal : Work.FTS.Nonlin.GalClass α g) :
    Work.FTS.Nonlin.GalClass α (0 : Work.FTS.Galerkin.Fn) ∧
    Work.FTS.EllipticEst.SmoothOpen (Work.FTS.GalFields.Fr α Φs EllSol g) ∧
    Work.Spaces.HkMem α 4 (Work.FTS.GalFields.Fr α Φs EllSol g) ∧
    Work.FTS.EllipticEst.SmoothOpen
      (fun z θ => Work.FTS.GalFields.Fr α Φs EllSol g z θ
        - Work.FTS.GalFields.Fr α Φs EllSol 0 z θ) ∧
    Work.Spaces.HkMem α 4 (fun z θ => Work.FTS.GalFields.Fr α Φs EllSol g z θ
        - Work.FTS.GalFields.Fr α Φs EllSol 0 z θ) := by
  have hg := Fr_open_honest hN hE hstar hell hα hα1 hαα₂ hgal
  have h0 := Fr_open_honest hN hE hstar hell hα hα1 hαα₂ (g := 0)
    (Work.FTS.EllSol.galClass_zero α)
  refine ⟨Work.FTS.EllSol.galClass_zero α, hg.1, hg.2, ?_, ?_⟩
  · exact Work.FTS.EllipticEst.smoothOpen_sub hg.1 h0.1
  · exact Work.FTS.CoercivityFix.Assembly.HkMem_add_open α 4 hg.1 h0.1.neg hg.2
      (Work.FTS.NonlinRows.HkMem_neg' α 4 h0.2)

end Work.FTS.GalFields.RHS
