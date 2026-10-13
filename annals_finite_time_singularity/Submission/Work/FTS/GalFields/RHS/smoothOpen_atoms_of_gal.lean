/-
# `RHS/smoothOpen_atoms` — the repaired form (with the honesty hypothesis on `g`)

`Submission/Work/FTS/GalFields/RHS/smoothOpen_atoms.lean` asks for the twelve `SmoothOpen`-atoms
of the dynamic right-hand side `Fr` from the *open-quadrant* packages `EllPkgGo α Ce g Φg`,
`StarPkgo2 α Cs Φs` and `SmoothOpen g`.  Two of the twelve conjuncts are **not consequences** of
those hypotheses — they are statements about the *angular moments*

  `FK g z = ∫_θ K(θ)·g z θ dθ`   and   `L₁₂(F_*+g)`, `FK(F_*+g)`

of the datum `g`, and neither package says anything about `g` itself (they constrain `Φg`, `Φs`
and the elliptic residuals `Rop/Uop/Vop (PhiTil α g Φg)` only).  The only route in the tree to the
smoothness of `FK g` identifies it with `-z·∂_z L₁₂(g)` (`OpenPkg.deriv_L12_eq`, consumed by
`NonlinRows.smoothOpen_L12_radial`), which needs exactly

  `LocData.SmoothQuad g`, `Spaces.HkMem α 4 g`, `Construction.L12 g 0 = 0`,

i.e. the `GalClass`-strength honesty of `g` (`Nonlin.GalClass α g`).  See
`NOTES_smoothOpen_FK_of_pkg_FALSE.md`, `NOTES_smoothOpen_N_Ftot_FALSE.md` (both in this directory)
and `StrongPersist/NOTES_L3_lin_FALSE.md` (the same diagnosis, with an explicit family whose
moment has a non-integral exponent `29/2`).

This file proves the **repaired** statement: the same conjunction with the single extra hypothesis

  `(hgal : Work.FTS.Nonlin.GalClass α g)`

— a hypothesis every consumer of this chapter has anyway (`Defs.RHSData`'s `lip` clause begins
`GalClass α g`, `GalClass α g'`; the call site `RHS/lip_clause_of_rows.lean` carries it in its
context).  The twelve conjuncts are assembled from

* the two repaired conjuncts `smoothOpen_FK_of_pkg_gal` and `smoothOpen_N_Ftot_gal`
  (proved in this directory),
* `NonlinRows.smoothOpen_L12_radial`, `hell.R/U/V` (conjuncts 1, 3, 4, 5),
* `NonlinRows.smoothOpen_PhiTs`, `.smoothOpen_Rop`, `.smoothOpen_Vop` (conjuncts 6, 7),
* `smoothOpen_LGammaT_of_L12` (conjunct 8),
* `StrongPersist.AK_smoothO` (conjunct 9),
* `StrongPersist.H6Pair6Aux.SmoothN0` (conjunct 10),
* `smoothOpen_Nstar_of` (conjunct 12).

Everything is `sorry`-free and rests on `[propext, Classical.choice, Quot.sound]`.
-/
import Mathlib.Analysis.Calculus.ContDiff.Defs
import Mathlib.Analysis.InnerProductSpace.Basic
import Submission.Work.FTS.GalFields.Defs
import Submission.Work.FTS.Nonlinear.Defs
import Submission.Work.FTS.EllipticEst.OpenQDefs
import Submission.Work.FTS.NonlinRows.NRow1_7Aux
import Submission.Work.FTS.NonlinRows.smoothOpen_radA
import Submission.Work.FTS.StrongPersist.H6Pair6Aux.SmoothN0
import Submission.Work.FTS.StrongPersist.H6Rows.AK6Row
import Submission.Work.Coercivity.Defs
import Submission.Work.FTS.GalFields.RHS.smoothOpen_LGammaT_of_L12
import Submission.Work.FTS.GalFields.RHS.smoothOpen_FK_of_gal
import Submission.Work.FTS.GalFields.RHS.smoothOpen_N_Ftot_gal

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

namespace Work.FTS.GalFields.RHS

set_option maxHeartbeats 1600000

open Work.FTS.EllipticEst (SmoothOpen)

/-- `N_*` is a linear combination of `g` and `D_z g`, hence `C^∞` on the open quadrant
whenever `g` is. -/
theorem smoothOpen_Nstar_of {μ lam : ℝ} {g : ℝ → ℝ → ℝ} (hg : SmoothOpen g) :
    SmoothOpen (Work.Construction.Nstar μ lam g) := by
  have h1 : SmoothOpen (fun z θ : ℝ => -μ * g z θ) :=
    Work.FTS.NonlinRows.smoothOpen_const_mul (-μ) hg
  have h2 : SmoothOpen (fun z θ : ℝ => (μ + lam + μ * lam) * Work.Spaces.Dz g z θ) :=
    Work.FTS.NonlinRows.smoothOpen_const_mul (μ + lam + μ * lam) hg.Dz
  have h3 : SmoothOpen (fun z θ : ℝ => -μ * g z θ
      - (μ + lam + μ * lam) * Work.Spaces.Dz g z θ) :=
    Work.FTS.NonlinRows.smoothOpen_sub h1 h2
  refine ContDiffOn.congr (f₁ := Function.uncurry (fun z θ : ℝ => -μ * g z θ
      - (μ + lam + μ * lam) * Work.Spaces.Dz g z θ)) h3 ?_
  intro p _
  obtain ⟨z, θ⟩ := p
  simp only [Function.uncurry, Work.Construction.Nstar]

/-- **The repaired form of `smoothOpen_atoms`**: with the honesty hypothesis
`GalClass α g` on the datum (which is what every consumer has), all twelve atoms of the dynamic
right-hand side are `C^∞` on the open quadrant. -/
theorem smoothOpen_atoms_of_gal {α Ce Cs : ℝ} (hα : 0 < α) (hα1 : α ≤ 1)
    {g Φs Φg : Work.FTS.Galerkin.Fn} (hgal : Work.FTS.Nonlin.GalClass α g)
    (hg : Work.FTS.EllipticEst.SmoothOpen g) (hΦs : Work.FTS.EllipticEst.SmoothOpen Φs)
    (hΦg : Work.FTS.EllipticEst.SmoothOpen Φg)
    (hell : Work.FTS.VocabO.EllPkgGo α Ce g Φg) (hstar : Work.FTS.VocabO2.StarPkgo2 α Cs Φs) :
    Work.FTS.EllipticEst.SmoothOpen (fun z _ => Work.Construction.L12 g z) ∧
    Work.FTS.EllipticEst.SmoothOpen (fun z _ => Work.Construction.FK g z) ∧
    Work.FTS.EllipticEst.SmoothOpen
      (Work.Construction.Rop α (Work.FTS.Nonlin.PhiTg α g Φg)) ∧
    Work.FTS.EllipticEst.SmoothOpen (fun z θ => Work.Construction.Uop α
      (Work.FTS.Nonlin.PhiTg α g Φg) z θ / Work.Construction.s2 θ) ∧
    Work.FTS.EllipticEst.SmoothOpen
      (Work.Construction.Vop (Work.FTS.Nonlin.PhiTg α g Φg)) ∧
    Work.FTS.EllipticEst.SmoothOpen
      (Work.Construction.Rop α (Work.FTS.Nonlin.PhiTs α Φs)) ∧
    Work.FTS.EllipticEst.SmoothOpen
      (Work.Construction.Vop (Work.FTS.Nonlin.PhiTs α Φs)) ∧
    Work.FTS.EllipticEst.SmoothOpen
      (Work.Coercivity.LGammaT α g) ∧
    Work.FTS.EllipticEst.SmoothOpen (Work.Construction.AK α) ∧
    Work.FTS.EllipticEst.SmoothOpen
      (Work.Construction.N0 α (Work.Construction.Ftot α g) g) ∧
    Work.FTS.EllipticEst.SmoothOpen (Work.Construction.N α (Work.Construction.Ftot α g)
      (fun z θ => Φs z θ + Φg z θ)) ∧
    Work.FTS.EllipticEst.SmoothOpen
      (Work.Construction.Nstar (Work.Construction.mufunS α
        (Work.Construction.N0 α (Work.Construction.Ftot α g) g)
        (Work.Construction.N α (Work.Construction.Ftot α g)
          (fun z θ => Φs z θ + Φg z θ)) g)
        (Work.Construction.lamfun (Work.Construction.mufunS α
        (Work.Construction.N0 α (Work.Construction.Ftot α g) g)
        (Work.Construction.N α (Work.Construction.Ftot α g)
          (fun z θ => Φs z θ + Φg z θ)) g)) g) := by
  have hL12 : Work.FTS.EllipticEst.SmoothOpen (fun z _ => Work.Construction.L12 g z) :=
    Work.FTS.NonlinRows.smoothOpen_L12_radial hα hΦg hell.V.1.1
  have hFK : Work.FTS.EllipticEst.SmoothOpen (fun z _ => Work.Construction.FK g z) :=
    smoothOpen_FK_of_pkg_gal hα hα1 hgal hg hΦs hΦg hell hstar
  have hRopG : Work.FTS.EllipticEst.SmoothOpen
      (Work.Construction.Rop α (Work.FTS.Nonlin.PhiTg α g Φg)) := hell.R.1.1
  have hUopG : Work.FTS.EllipticEst.SmoothOpen (fun z θ => Work.Construction.Uop α
      (Work.FTS.Nonlin.PhiTg α g Φg) z θ / Work.Construction.s2 θ) := hell.U.1.1
  have hVopG : Work.FTS.EllipticEst.SmoothOpen
      (Work.Construction.Vop (Work.FTS.Nonlin.PhiTg α g Φg)) := hell.V.1.1
  have hPhiTs : Work.FTS.EllipticEst.SmoothOpen (Work.FTS.Nonlin.PhiTs α Φs) :=
    Work.FTS.NonlinRows.smoothOpen_PhiTs hα hα1 hstar.toStarPkgo
  have hRopS : Work.FTS.EllipticEst.SmoothOpen
      (Work.Construction.Rop α (Work.FTS.Nonlin.PhiTs α Φs)) :=
    Work.FTS.NonlinRows.smoothOpen_Rop hPhiTs
  have hVopS : Work.FTS.EllipticEst.SmoothOpen
      (Work.Construction.Vop (Work.FTS.Nonlin.PhiTs α Φs)) :=
    Work.FTS.NonlinRows.smoothOpen_Vop hPhiTs
  have hLG : Work.FTS.EllipticEst.SmoothOpen (Work.Coercivity.LGammaT α g) :=
    smoothOpen_LGammaT_of_L12 hL12 hg
  have hAK : Work.FTS.EllipticEst.SmoothOpen (Work.Construction.AK α) :=
    Work.FTS.StrongPersist.AK_smoothO α
  have hN0 : Work.FTS.EllipticEst.SmoothOpen
      (Work.Construction.N0 α (Work.Construction.Ftot α g) g) :=
    Work.FTS.StrongPersist.H6Pair6Aux.SmoothN0 hα hg hL12
  have hN : Work.FTS.EllipticEst.SmoothOpen (Work.Construction.N α
      (Work.Construction.Ftot α g) (fun z θ => Φs z θ + Φg z θ)) :=
    smoothOpen_N_Ftot_gal hα hα1 hgal hg hΦs hΦg hell hstar
  have hNstar : Work.FTS.EllipticEst.SmoothOpen
      (Work.Construction.Nstar (Work.Construction.mufunS α
        (Work.Construction.N0 α (Work.Construction.Ftot α g) g)
        (Work.Construction.N α (Work.Construction.Ftot α g)
          (fun z θ => Φs z θ + Φg z θ)) g)
        (Work.Construction.lamfun (Work.Construction.mufunS α
        (Work.Construction.N0 α (Work.Construction.Ftot α g) g)
        (Work.Construction.N α (Work.Construction.Ftot α g)
          (fun z θ => Φs z θ + Φg z θ)) g)) g) :=
    smoothOpen_Nstar_of hg
  exact ⟨hL12, hFK, hRopG, hUopG, hVopG, hRopS, hVopS, hLG, hAK, hN0, hN, hNstar⟩

end Work.FTS.GalFields.RHS
