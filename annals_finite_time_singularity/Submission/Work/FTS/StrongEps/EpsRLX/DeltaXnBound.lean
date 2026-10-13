import Mathlib.Algebra.Order.Star.Real
import Mathlib.Analysis.Calculus.ContDiff.Operations
import Mathlib.Analysis.InnerProductSpace.Basic
import Mathlib.Analysis.SpecialFunctions.Trigonometric.Basic
import Submission.Work.FTS.StrongEps.EpsRLX.Defs
import Submission.Work.FTS.StrongEps.EpsRLX.MuBlockClassC
import Submission.Work.FTS.StrongEps.EpsRLX.LGTDiffClassC
import Submission.Work.FTS.StrongEps.EpsRLX.N0DiffClassC
import Submission.Work.FTS.StrongEps.EpsRLX.NDiffClassC
import Submission.Work.FTS.StrongEps.EpsRLX.MuBlockDiffSmoothMem
import Submission.Work.FTS.StrongEps.EpsLocalPStar.EpsRHSXrhs

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

namespace Work.FTS.StrongEps.EpsRLX

open Work.FTS.Galerkin (Fn)

set_option maxHeartbeats 1600000

/-! ## The two telescoping identities for `profRHS`

`profRHS α Φs E w` is, by definition, `linPart α w + gRHS α μ λ (F_* + w) (Φ_s + E w) w` with the
modulation constants of `w`.  Since `muDyn`/`lamDyn` at the constant family `famOf (fun _ => w)`
are `muOf`/`lamfun (muOf)` (`MuBlockBase.muOf_eq_muDyn`, `lamfun_muOf_eq_lamDyn`, both `rfl`), and
`gRHS = -μ̄·AK + N₀ + N + N_*`, the profile `profRHS α Φs E w` splits as

  `linPart α w + (muBlock α Φs E w + N₀ α (F_*+w) w + N α (F_*+w) (Φ_s + E w))`

and its difference at `W₁, W₂` is the sum of the four differences whose `ℋ⁴`-Lipschitz bounds are
`LGTDiffClassC`, `MuBlockClassC`, `N0DiffClassC` and `NDiffClassC`. -/

private theorem profRHS_apply (α : ℝ) (Φs : Fn) (E : Fn → Fn) (w : Fn) (z θ : ℝ) :
    Work.FTS.StrongEps.EpsLocalPStar.profRHS α Φs E w z θ
      = Work.FTS.StrongPersist.linPart α w z θ
        + (-(mubarOf α Φs E w) * Work.Construction.AK α z θ
           + Work.Construction.N0 α (Work.Construction.Ftot α w) w z θ
           + Work.Construction.N α (Work.Construction.Ftot α w)
               (fun z θ => Φs z θ + E w z θ) z θ
           + Work.Construction.Nstar (muOf α Φs E w)
               (Work.Construction.lamfun (muOf α Φs E w)) w z θ) := rfl

private theorem profRHS_sub_eq (α : ℝ) (Φs : Fn) (E : Fn → Fn) (W₁ W₂ : Fn) :
    (fun z θ => Work.FTS.StrongEps.EpsLocalPStar.profRHS α Φs E W₁ z θ
        - Work.FTS.StrongEps.EpsLocalPStar.profRHS α Φs E W₂ z θ)
      = fun z θ => ((Work.FTS.StrongPersist.linPart α W₁ z θ
              - Work.FTS.StrongPersist.linPart α W₂ z θ)
          + (muBlock α Φs E W₁ z θ - muBlock α Φs E W₂ z θ))
          + (Work.Construction.N0 α (Work.Construction.Ftot α W₁) W₁ z θ
              - Work.Construction.N0 α (Work.Construction.Ftot α W₂) W₂ z θ)
          + (Work.Construction.N α (Work.Construction.Ftot α W₁)
                (fun z θ => Φs z θ + E W₁ z θ) z θ
              - Work.Construction.N α (Work.Construction.Ftot α W₂)
                (fun z θ => Φs z θ + E W₂ z θ) z θ) := by
  funext z θ
  simp only [profRHS_apply, muBlock_apply]
  ring


theorem DeltaXnBound {α C₀ Ce Cs : ℝ} {Φs : Work.FTS.Galerkin.Fn}
    {E : Work.FTS.Galerkin.Fn → Work.FTS.Galerkin.Fn}
    (hα : α ∈ Set.Ioc 0 1)
    (hEll : ∀ u : Work.FTS.Galerkin.Fn, Work.FTS.ClassC.ClassC α u →
      Work.FTS.VocabO.EllPkgGo α Ce u (E u) ∧ Work.FTS.ClassC.EllPkgK α 6 Ce u (E u))
    (hstar : Work.FTS.VocabO2.StarPkgo2 α Cs Φs)
    (hml : Work.FTS.StrongEps.MuLamOK α C₀ Φs E) :
    ∃ K : ℝ, 0 < K ∧ ∀ {W₁ W₂ : Work.FTS.Galerkin.Fn},
      Work.FTS.ClassC.ClassC α W₁ → Work.FTS.ClassC.ClassC α W₂ →
      Work.FTS.Nonlin.Xn α W₁ ≤ C₀ * α ^ 2 → Work.FTS.Nonlin.Xn α W₂ ≤ C₀ * α ^ 2 →
      Work.FTS.EllipticEst.SmoothOpen (fun z θ =>
        Work.FTS.StrongEps.EpsLocalPStar.profRHS α Φs E W₁ z θ
          - Work.FTS.StrongEps.EpsLocalPStar.profRHS α Φs E W₂ z θ) ∧
      Work.Spaces.HkMem α 4 (fun z θ =>
        Work.FTS.StrongEps.EpsLocalPStar.profRHS α Φs E W₁ z θ
          - Work.FTS.StrongEps.EpsLocalPStar.profRHS α Φs E W₂ z θ) ∧
      Work.FTS.Nonlin.Xn α (fun z θ =>
        Work.FTS.StrongEps.EpsLocalPStar.profRHS α Φs E W₁ z θ
          - Work.FTS.StrongEps.EpsLocalPStar.profRHS α Φs E W₂ z θ)
        ≤ K * (1 + Work.FTS.GalFields.Xn5 α W₁ + Work.FTS.GalFields.Xn5 α W₂) ^ 2
            * Work.FTS.GalFields.Xn5 α (fun z θ => W₁ z θ - W₂ z θ) := by
  have hα0 : 0 < α := hα.1
  obtain ⟨KL, hKL, hLGT⟩ := LGTDiffClassC (α := α) hα
  obtain ⟨KB, hKB, hMuB⟩ := MuBlockClassC (α := α) (Ce := Ce) (Cs := Cs) (C₀ := C₀)
    (Φs := Φs) (E := E) hα hEll hstar hml
  obtain ⟨K0, hK0, hN0⟩ := N0DiffClassC α hα
  obtain ⟨KN, hKN, hN⟩ := NDiffClassC (α := α) (Ce := Ce) (Cs := Cs) (Φs := Φs) (E := E)
    hα hEll hstar
  refine ⟨20 * (KL + KB + K0 + KN + 1), by linarith, ?_⟩
  intro W₁ W₂ hW₁ hW₂ hX₁ hX₂
  -- ## the four difference pieces
  let A : Fn := fun z θ => Work.FTS.StrongPersist.linPart α W₁ z θ
    - Work.FTS.StrongPersist.linPart α W₂ z θ
  let B : Fn := fun z θ => muBlock α Φs E W₁ z θ - muBlock α Φs E W₂ z θ
  let C : Fn := fun z θ => Work.Construction.N0 α (Work.Construction.Ftot α W₁) W₁ z θ
    - Work.Construction.N0 α (Work.Construction.Ftot α W₂) W₂ z θ
  let D : Fn := fun z θ => Work.Construction.N α (Work.Construction.Ftot α W₁)
        (fun z θ => Φs z θ + E W₁ z θ) z θ
    - Work.Construction.N α (Work.Construction.Ftot α W₂)
        (fun z θ => Φs z θ + E W₂ z θ) z θ
  let AB : Fn := fun z θ => A z θ + B z θ
  let ABC : Fn := fun z θ => A z θ + B z θ + C z θ
  let ABCD : Fn := fun z θ => A z θ + B z θ + C z θ + D z θ
  obtain ⟨hLsm, hLmem, hLxn⟩ := hLGT hW₁ hW₂
  obtain ⟨hBsm, hBmem, hBxn⟩ := hMuB hW₁ hW₂ hX₁ hX₂
  obtain ⟨hCsm, hCmem, hCxn, -⟩ := hN0 hW₁ hW₂
  obtain ⟨hDsm, hDmem, hDxn⟩ := hN hW₁ hW₂
  -- ## the `A`-data
  have hAnegsm : Work.FTS.EllipticEst.SmoothOpen (fun z θ =>
      -(Work.Coercivity.LGammaT α W₁ z θ - Work.Coercivity.LGammaT α W₂ z θ)) := hLsm.neg
  have hAsm : Work.FTS.EllipticEst.SmoothOpen A :=
    smoothOpen_of_eqOn_Qd_cc hAnegsm
      (fun z θ _ _ _ => by simp only [A, Work.FTS.StrongPersist.linPart]; ring)
  have hAnegmem : Work.Spaces.HkMem α 4 (fun z θ =>
      -(Work.Coercivity.LGammaT α W₁ z θ - Work.Coercivity.LGammaT α W₂ z θ)) :=
    Work.FTS.NonlinRows.HkMem_neg' α 4 hLmem
  have hAmem : Work.Spaces.HkMem α 4 A :=
    Work.FTS.EllipticEst.Cert.GbarSin.HkMem_congr_Q0 α 4 hAnegmem
      (fun z _ θ _ => by simp only [A, Work.FTS.StrongPersist.linPart]; ring)
  have hAxn : Work.FTS.Nonlin.Xn α A ≤ KL * Work.FTS.GalFields.Xn5 α
      (fun z θ => W₁ z θ - W₂ z θ) := by
    have h1 : Work.FTS.Nonlin.Xn α A = Work.FTS.Nonlin.Xn α (fun z θ =>
        -(Work.Coercivity.LGammaT α W₁ z θ - Work.Coercivity.LGammaT α W₂ z θ)) :=
      Work.FTS.StrongEps.EComparison.HkNorm_congr_open α 4 (f := A)
        (g := fun z θ => -(Work.Coercivity.LGammaT α W₁ z θ
          - Work.Coercivity.LGammaT α W₂ z θ))
        (fun z θ _ _ _ => by simp only [A, Work.FTS.StrongPersist.linPart]; ring)
    have h2 : Work.FTS.Nonlin.Xn α (fun z θ =>
          -(Work.Coercivity.LGammaT α W₁ z θ - Work.Coercivity.LGammaT α W₂ z θ))
        = Work.FTS.Nonlin.Xn α (fun z θ => Work.Coercivity.LGammaT α W₁ z θ
            - Work.Coercivity.LGammaT α W₂ z θ) :=
      Work.FTS.EllipticEst.HkNorm_neg α 4 (fun z θ => Work.Coercivity.LGammaT α W₁ z θ
        - Work.Coercivity.LGammaT α W₂ z θ)
    rw [h1, h2]
    exact hLxn
  -- ## the sum-level data
  have hABsm : Work.FTS.EllipticEst.SmoothOpen AB :=
    Work.FTS.NonlinRows.smoothOpen_add hAsm hBsm
  have hABmem : Work.Spaces.HkMem α 4 AB :=
    Work.FTS.CoercivityFix.Assembly.HkMem_add_open α 4 hAsm hBsm hAmem hBmem
  have hABxn : Work.FTS.Nonlin.Xn α AB ≤ 2 * (Work.FTS.Nonlin.Xn α A
      + Work.FTS.Nonlin.Xn α B) :=
    Work.FTS.GalFields.RHS.HkNorm_add_le_open α 4 hα0 hAsm hBsm hAmem hBmem
  have hABCsm : Work.FTS.EllipticEst.SmoothOpen ABC :=
    Work.FTS.NonlinRows.smoothOpen_add hABsm hCsm
  have hABCmem : Work.Spaces.HkMem α 4 ABC :=
    Work.FTS.CoercivityFix.Assembly.HkMem_add_open α 4 hABsm hCsm hABmem hCmem
  have hABCxn : Work.FTS.Nonlin.Xn α ABC ≤ 2 * (Work.FTS.Nonlin.Xn α AB
      + Work.FTS.Nonlin.Xn α C) :=
    Work.FTS.GalFields.RHS.HkNorm_add_le_open α 4 hα0 hABsm hCsm hABmem hCmem
  have hABCDsm : Work.FTS.EllipticEst.SmoothOpen ABCD :=
    Work.FTS.NonlinRows.smoothOpen_add hABCsm hDsm
  have hABCDmem : Work.Spaces.HkMem α 4 ABCD :=
    Work.FTS.CoercivityFix.Assembly.HkMem_add_open α 4 hABCsm hDsm hABCmem hDmem
  have hABCDxn : Work.FTS.Nonlin.Xn α ABCD ≤ 2 * (Work.FTS.Nonlin.Xn α ABC
      + Work.FTS.Nonlin.Xn α D) :=
    Work.FTS.GalFields.RHS.HkNorm_add_le_open α 4 hα0 hABCsm hDsm hABCmem hDmem
  -- ## the arithmetic
  have hZs : 0 ≤ Work.FTS.GalFields.Xn5 α (fun z θ => W₁ z θ - W₂ z θ) :=
    Work.Spaces.HkNorm_nonneg α 5 _
  have hPs : (1 : ℝ) ≤ 1 + Work.FTS.GalFields.Xn5 α W₁ + Work.FTS.GalFields.Xn5 α W₂ := by
    have h1 : 0 ≤ Work.FTS.GalFields.Xn5 α W₁ := Work.Spaces.HkNorm_nonneg α 5 W₁
    have h2 : 0 ≤ Work.FTS.GalFields.Xn5 α W₂ := Work.Spaces.HkNorm_nonneg α 5 W₂
    linarith
  have hPsq : (1 : ℝ) ≤ (1 + Work.FTS.GalFields.Xn5 α W₁ + Work.FTS.GalFields.Xn5 α W₂) ^ 2 := by
    nlinarith [hPs]
  have hZT : Work.FTS.GalFields.Xn5 α (fun z θ => W₁ z θ - W₂ z θ)
      ≤ (1 + Work.FTS.GalFields.Xn5 α W₁ + Work.FTS.GalFields.Xn5 α W₂) ^ 2
        * Work.FTS.GalFields.Xn5 α (fun z θ => W₁ z θ - W₂ z θ) := by
    nlinarith [hPsq, hZs]
  have hPT : (1 + Work.FTS.GalFields.Xn5 α W₁ + Work.FTS.GalFields.Xn5 α W₂)
        * Work.FTS.GalFields.Xn5 α (fun z θ => W₁ z θ - W₂ z θ)
      ≤ (1 + Work.FTS.GalFields.Xn5 α W₁ + Work.FTS.GalFields.Xn5 α W₂) ^ 2
        * Work.FTS.GalFields.Xn5 α (fun z θ => W₁ z θ - W₂ z θ) := by
    nlinarith [hPs, hZs]
  have hchain : Work.FTS.Nonlin.Xn α ABCD
      ≤ 8 * Work.FTS.Nonlin.Xn α A + 8 * Work.FTS.Nonlin.Xn α B
        + 4 * Work.FTS.Nonlin.Xn α C + 2 * Work.FTS.Nonlin.Xn α D := by
    linarith [hABCDxn, hABCxn, hABxn]
  have hcomb : 8 * Work.FTS.Nonlin.Xn α A + 8 * Work.FTS.Nonlin.Xn α B
        + 4 * Work.FTS.Nonlin.Xn α C + 2 * Work.FTS.Nonlin.Xn α D
      ≤ 20 * (KL + KB + K0 + KN + 1)
        * (1 + Work.FTS.GalFields.Xn5 α W₁ + Work.FTS.GalFields.Xn5 α W₂) ^ 2
        * Work.FTS.GalFields.Xn5 α (fun z θ => W₁ z θ - W₂ z θ) := by
    nlinarith [hAxn, hBxn, hCxn, hDxn, hZT, hPT, hZs, hPs, hKL, hKB, hK0, hKN]
  have hfinal : Work.FTS.Nonlin.Xn α ABCD
      ≤ 20 * (KL + KB + K0 + KN + 1)
        * (1 + Work.FTS.GalFields.Xn5 α W₁ + Work.FTS.GalFields.Xn5 α W₂) ^ 2
        * Work.FTS.GalFields.Xn5 α (fun z θ => W₁ z θ - W₂ z θ) :=
    le_trans hchain hcomb
  -- ## back to `profRHS`
  have heqfun : ABCD = (fun z θ => Work.FTS.StrongEps.EpsLocalPStar.profRHS α Φs E W₁ z θ
      - Work.FTS.StrongEps.EpsLocalPStar.profRHS α Φs E W₂ z θ) := by
    rw [profRHS_sub_eq α Φs E W₁ W₂]
  refine ⟨?_, ?_, ?_⟩
  · exact smoothOpen_of_eqOn_Qd_cc hABCDsm (fun z θ _ _ _ => congrFun (congrFun heqfun z) θ)
  · exact Work.FTS.EllipticEst.Cert.GbarSin.HkMem_congr_Q0 α 4 hABCDmem
      (fun z _ θ _ => congrFun (congrFun heqfun z) θ)
  · have hcongr := Work.FTS.StrongEps.EComparison.HkNorm_congr_open α 4 (f := ABCD)
      (g := fun z θ => Work.FTS.StrongEps.EpsLocalPStar.profRHS α Φs E W₁ z θ
        - Work.FTS.StrongEps.EpsLocalPStar.profRHS α Φs E W₂ z θ)
      (fun z θ _ _ _ => congrFun (congrFun heqfun z) θ)
    have hXnEq : Work.FTS.Nonlin.Xn α ABCD = Work.FTS.Nonlin.Xn α (fun z θ =>
        Work.FTS.StrongEps.EpsLocalPStar.profRHS α Φs E W₁ z θ
          - Work.FTS.StrongEps.EpsLocalPStar.profRHS α Φs E W₂ z θ) := hcongr
    rw [hXnEq] at hfinal
    exact hfinal

end Work.FTS.StrongEps.EpsRLX
