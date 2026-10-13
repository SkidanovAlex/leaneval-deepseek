import Mathlib.Analysis.Calculus.ContDiff.Operations
import Mathlib.Analysis.InnerProductSpace.Basic
import Mathlib.Analysis.SpecialFunctions.Trigonometric.Basic
import Submission.Work.FTS.EpsEngine.EpsClass
import Submission.Work.FTS.EpsEngine.profRHSDiffEpsSq
import Submission.Work.FTS.EllipticEst.OpenQDefs
import Submission.Work.FTS.EpsEngine.BlocksConcrete
import Submission.Work.FTS.StrongEps.ClassCRHS.SmoothOpenRHS
import Submission.Work.FTS.GalFields.RHS.smoothOpen_atoms_of_gal
import Submission.Work.FTS.StrongEps.JepsHkMem.continuousOn_Jeps
import Submission.Work.FTS.StrongEps.BumpDefs
import Submission.Work.FTS.StrongEps.PZero
import Submission.Work.FTS.StrongEps.EpsRLX.MuBlockBase
import Submission.Work.FTS.StrongPersist.H6Pair6Aux.SmoothN0

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

namespace Work.FTS.EpsEngine

open Work.FTS.Galerkin (Fn)

/-- **The pointwise unfolding of `profRHS`**: the pre-mollified right-hand side is the linear part
plus the four blocks `-μ̄·AK α`, `N₀`, `N`, `N_*` of the `g`-equation (`Construction.gRHS`), with
the modulation constants `μ̄ = mubarOf`, `μ = muOf`, `lam = lamfun μ` of the profile.  This is the
form in which the smoothness of `profRHS` is assembled. -/
theorem profRHS_apply_eq (α : ℝ) (Φs : Fn) (E : Fn → Fn) (u : Fn) (z θ : ℝ) :
    Work.FTS.StrongEps.EpsLocalPStar.profRHS α Φs E u z θ
      = Work.FTS.StrongPersist.linPart α u z θ
        + (-(Work.FTS.StrongEps.EpsRLX.mubarOf α Φs E u) * Work.Construction.AK α z θ
          + Work.Construction.N0 α (Work.Construction.Ftot α u) u z θ
          + Work.Construction.N α (Work.Construction.Ftot α u)
              (fun z θ => Φs z θ + E u z θ) z θ
          + Work.Construction.Nstar (Work.FTS.StrongEps.EpsRLX.muOf α Φs E u)
              (Work.Construction.lamfun (Work.FTS.StrongEps.EpsRLX.muOf α Φs E u)) u z θ) := rfl

/-- **`profRHS` is `C^∞` on the open quadrant at every class-`C` profile.**  The analytic inputs
are the open-quadrant smoothness of the profile itself (`ClassC.reg`), the elliptic package of the
profile (`hEll`), the star package of `Φs` (`hstar`) and the smoothness of the four blocks of
`gRHS`; the modulation constants are *numbers*, so no `MuLamOK`/`HkNorm` bound is needed for the
regularity. -/
theorem smoothOpen_profRHS_of_classC {α Ce Cs : ℝ} {Φs : Fn} {E : Fn → Fn} {W : Fn}
    (hα : α ∈ Set.Ioc 0 1)
    (hEll : ∀ u : Fn, Work.FTS.ClassC.ClassC α u →
      Work.FTS.VocabO.EllPkgGo α Ce u (E u) ∧ Work.FTS.ClassC.EllPkgK α 6 Ce u (E u))
    (hstar : Work.FTS.VocabO2.StarPkgo2 α Cs Φs)
    (hW : Work.FTS.ClassC.ClassC α W) :
    Work.FTS.EllipticEst.SmoothOpen (Work.FTS.StrongEps.EpsLocalPStar.profRHS α Φs E W) := by
  have hEllW : Work.FTS.VocabO.EllPkgGo α Ce W (E W) := (hEll W hW).1
  obtain ⟨-, -, hLGsmo, hN0smo, hNsmo⟩ :=
    Work.FTS.StrongEps.ClassCRHS.SmoothOpenRHS hα.1 hα.2 hW hEllW hstar
  -- the linear part `linPart α W = -(L_Γ^T W)`
  have hnegL : Work.FTS.EllipticEst.SmoothOpen (fun z θ => -Work.Coercivity.LGammaT α W z θ) :=
    hLGsmo.neg
  have hLinsmo : Work.FTS.EllipticEst.SmoothOpen (Work.FTS.StrongPersist.linPart α W) := by
    refine Work.FTS.EllipticEst.SmoothOpen.congr hnegL (fun z θ _ _ _ => ?_)
    simp only [Work.FTS.StrongPersist.linPart]
  -- the `-μ̄·AK α` block
  have hAKsmo : Work.FTS.EllipticEst.SmoothOpen (fun z θ =>
      -(Work.FTS.StrongEps.EpsRLX.mubarOf α Φs E W) * Work.Construction.AK α z θ) :=
    Work.FTS.NonlinRows.smoothOpen_const_mul _ (Work.FTS.StrongPersist.AK_smoothO α)
  -- the `N_*` block
  have hNssmo : Work.FTS.EllipticEst.SmoothOpen
      (Work.Construction.Nstar (Work.FTS.StrongEps.EpsRLX.muOf α Φs E W)
        (Work.Construction.lamfun (Work.FTS.StrongEps.EpsRLX.muOf α Φs E W)) W) :=
    Work.FTS.GalFields.RHS.smoothOpen_Nstar_of hW.reg
  -- the nonlinear block `gRHS`
  have hkeysmo : Work.FTS.EllipticEst.SmoothOpen (fun z θ =>
      -(Work.FTS.StrongEps.EpsRLX.mubarOf α Φs E W) * Work.Construction.AK α z θ
        + Work.Construction.N0 α (Work.Construction.Ftot α W) W z θ
        + Work.Construction.N α (Work.Construction.Ftot α W)
            (fun z θ => Φs z θ + E W z θ) z θ
        + Work.Construction.Nstar (Work.FTS.StrongEps.EpsRLX.muOf α Φs E W)
            (Work.Construction.lamfun (Work.FTS.StrongEps.EpsRLX.muOf α Φs E W)) W z θ) :=
    ((hAKsmo.add hN0smo).add hNsmo).add hNssmo
  have hsumsmo : Work.FTS.EllipticEst.SmoothOpen (fun z θ =>
      Work.FTS.StrongPersist.linPart α W z θ
        + (-(Work.FTS.StrongEps.EpsRLX.mubarOf α Φs E W) * Work.Construction.AK α z θ
          + Work.Construction.N0 α (Work.Construction.Ftot α W) W z θ
          + Work.Construction.N α (Work.Construction.Ftot α W)
              (fun z θ => Φs z θ + E W z θ) z θ
          + Work.Construction.Nstar (Work.FTS.StrongEps.EpsRLX.muOf α Φs E W)
              (Work.Construction.lamfun (Work.FTS.StrongEps.EpsRLX.muOf α Φs E W)) W z θ)) :=
    hLinsmo.add hkeysmo
  refine Work.FTS.EllipticEst.SmoothOpen.congr hsumsmo (fun z θ _ _ _ => ?_)
  exact (profRHS_apply_eq α Φs E W z θ).symm

/-- **`Feps` is continuous on the open quadrant and vanishes off it**, at every profile of the
engine's class `EpsClass α ρ ε C₁ B`.  This is the per-profile input of the Carathéodory argument
that produces the local step's `hmeasIter`: the pieces of `profRHS` are continuous on `Q0` because
`w`, `E w` and `Φs` are (`EpsClass.smoothOpen`, `EllPkgGo.smooth`, `StarPkgo2.smooth`), the
`L₁₂`-derivative entering `Theta α (Ftot α w)` is available from `ClassC.mem10` (`HkMem α 10`), and
`Jeps`/`Pz` preserve continuity (the existing `JepsHkMem.continuousOn_Jeps` gives the mollifier part
from continuity of the profile on `Quad`) and vanish off `Q0`. -/
theorem continuousOn_Feps_of_epsClass {α C₁ Ce Cs B : ℝ} {ρ : ℝ × ℝ → ℝ} {Φs : ℝ → ℝ → ℝ}
    {E : (ℝ → ℝ → ℝ) → ℝ → ℝ → ℝ} {ε : ℝ} {w : ℝ → ℝ → ℝ}
    (hα : α ∈ Set.Ioc 0 1) (hρ : Work.FTS.StrongEps.IsSmoothKernel ρ) (hε : 0 < ε) (hε1 : ε ≤ 1)
    (hEll : ∀ u : ℝ → ℝ → ℝ, Work.FTS.ClassC.ClassC α u →
      Work.FTS.VocabO.EllPkgGo α Ce u (E u) ∧ Work.FTS.ClassC.EllPkgK α 6 Ce u (E u))
    (hstar : Work.FTS.VocabO2.StarPkgo2 α Cs Φs)
    (hml : Work.FTS.StrongEps.MuLamOK α C₁ Φs E)
    (hw : Work.FTS.EpsEngine.EpsClass α ρ ε C₁ B w) :
    ContinuousOn (fun q : ℝ × ℝ => Work.FTS.EpsEngine.Feps α ρ ε Φs E w q.1 q.2)
      (Set.Ioi 0 ×ˢ Set.Ioo 0 (Real.pi / 2)) ∧
    (∀ q : ℝ × ℝ, q ∉ Set.Ioi 0 ×ˢ Set.Ioo 0 (Real.pi / 2) →
      Work.FTS.EpsEngine.Feps α ρ ε Φs E w q.1 q.2 = 0) := by
  -- the projected-mollified profile `W = Pz (J_ε w)` and the pre-mollified right-hand side `X`
  set W : Fn := Work.FTS.StrongEps.Pz (Work.FTS.StrongEps.Jeps ρ ε w) with hWdef
  set X : Fn := Work.FTS.StrongEps.EpsLocalPStar.profRHS α Φs E W with hXdef
  have hWcc : Work.FTS.ClassC.ClassC α W := by rw [hWdef]; exact hw.classC
  -- ## `X` is `C^∞` on the open quadrant, hence continuous there
  have hXsmo : Work.FTS.EllipticEst.SmoothOpen X := by
    rw [hXdef]
    exact smoothOpen_profRHS_of_classC hα hEll hstar hWcc
  have hXcont : ContinuousOn (fun q : ℝ × ℝ => X q.1 q.2) Work.FTS.StrongEps.Quad :=
    hXsmo.continuousOn
  -- ## the mollified profile is continuous on the open quadrant
  have hJcont : ContinuousOn (fun q : ℝ × ℝ => Work.FTS.StrongEps.Jeps ρ ε X q.1 q.2)
      Work.FTS.StrongEps.Quad :=
    Work.FTS.StrongEps.JepsHkMem.continuousOn_Jeps hρ.moll hε hXcont
  -- ## the projection `Pz` preserves it
  have hbumpcont : ContinuousOn (fun q : ℝ × ℝ => Work.FTS.StrongEps.bump q.1 q.2)
      Work.FTS.StrongEps.Quad := Work.FTS.StrongEps.smoothOpen_bump.continuousOn
  have hPcont : ContinuousOn (fun q : ℝ × ℝ =>
      Work.FTS.StrongEps.Jeps ρ ε X q.1 q.2
        - (Work.Construction.L12 (Work.FTS.StrongEps.Jeps ρ ε X) 0 / Work.FTS.StrongEps.pzNorm)
            * Work.FTS.StrongEps.bump q.1 q.2) Work.FTS.StrongEps.Quad :=
    hJcont.sub (continuousOn_const.mul hbumpcont)
  -- ## `Jeps` and `Pz` do not see the sets: the definitional unfolding of `Feps`
  have hfun : Work.FTS.EpsEngine.Feps α ρ ε Φs E w
      = Work.FTS.StrongEps.Pz (Work.FTS.StrongEps.Jeps ρ ε X) := by
    unfold Work.FTS.EpsEngine.Feps
    rw [hXdef, hWdef]
  have hPzeq : (fun q : ℝ × ℝ => Work.FTS.StrongEps.Pz (Work.FTS.StrongEps.Jeps ρ ε X) q.1 q.2)
      = fun q : ℝ × ℝ =>
          Work.FTS.StrongEps.Jeps ρ ε X q.1 q.2
            - (Work.Construction.L12 (Work.FTS.StrongEps.Jeps ρ ε X) 0
                / Work.FTS.StrongEps.pzNorm) * Work.FTS.StrongEps.bump q.1 q.2 := by
    funext q
    rw [Work.FTS.StrongEps.Pz_apply]
  refine ⟨?_, ?_⟩
  · rw [hfun, hPzeq]
    exact hPcont
  · intro q hq
    have hq' : ¬ (0 < q.1 ∧ q.2 ∈ Set.Ioo 0 (Real.pi / 2)) :=
      fun h => hq ⟨h.1, h.2⟩
    have hbump0 : Work.FTS.StrongEps.bump q.1 q.2 = 0 := by
      rw [Work.FTS.StrongEps.bump_eq_zero_iff]
      by_cases h1 : 0 < q.1
      · by_cases h2 : q.2 ∈ Set.Ioo 0 (Real.pi / 2)
        · exact absurd ⟨h1, h2⟩ hq'
        · rw [Set.mem_Ioo, not_and_or] at h2
          rcases h2 with h2 | h2
          · exact Or.inr (Or.inr (Or.inl (by linarith [Real.pi_pos])))
          · exact Or.inr (Or.inr (Or.inr (by linarith [Real.pi_pos])))
      · exact Or.inl (by linarith)
    rw [hfun]
    rw [Work.FTS.StrongEps.Pz_apply, Work.FTS.StrongEps.Jeps_eq_zero ρ ε X hq', hbump0]
    ring

end Work.FTS.EpsEngine
