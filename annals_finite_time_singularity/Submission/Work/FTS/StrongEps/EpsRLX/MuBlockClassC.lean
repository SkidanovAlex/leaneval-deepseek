import Mathlib.Algebra.Order.Star.Real
import Submission.Work.FTS.GalFields.RHS.sharp_muBlock_summand
import Submission.Work.FTS.GalFields.RHS.sharp_modulation_diff
import Submission.Work.FTS.StrongEps.EpsLimitDefs
import Submission.Work.FTS.StrongEps.EpsRLX.Defs
import Submission.Work.FTS.StrongEps.ClassCRHS.SmoothOpenRHS
import Submission.Work.FTS.OpenPkg.Basic
import Submission.Work.FTS.StrongEps.EpsRLX.MuBlockBase
import Submission.Work.FTS.StrongEps.EpsRLX.ModDiffClassC
import Submission.Work.FTS.Nonlinear.Pieces.rowsAux
import Submission.Work.FTS.StrongEps.EpsRLX.MuBlockDiffSmoothMem
import Submission.Work.FTS.StrongEps.EpsRLX.MuBlockXnBound

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

namespace Work.FTS.StrongEps.EpsRLX

open scoped Real Topology
open MeasureTheory Set Filter

set_option autoImplicit false

/-- **The modulation block `-μ̄·AK + N_*` is Lipschitz on the class-`C` small ball of the
`ε`-scheme**, in the sharp (`(1+Xn5 W₁ + Xn5 W₂)²·Xn5(W₁-W₂)`) form of the RHS-difference
estimate of `EpsRHSPLipXProof`.

Write `B(W) := muBlock α Φs E W = -μ̄(W)·AK α + N_* μ(W) (lamfun μ(W)) W`, with the two scalar
modulation constants `μ(W) = muOf α Φs E W`, `μ̄(W) = mubarOf α Φs E W` of
`EpsRLX/MuBlockBase.lean`.  The three conclusions are obtained as follows.

* `SmoothOpen` and `HkMem α 4` of `B(W₁)-B(W₂)`: the sibling `EpsRLX.MuBlockDiffSmoothMem`
  (the block is a *linear* combination `-μ̄·AK - μ·W - (μ+λ+μλ)·D_z W` of `AK α`, `W` and `D_z W`,
  with scalar coefficients, so this is closure under sums, scalar multiples and `D_z`).
* the `Xn`-bound: first `ModDiffClassC` (the `ClassC`-Lipschitz bounds on the modulation
  constants, with constant `Km`), then the sibling `EpsRLX.MuBlockXnBound`, which telescopes the
  difference along `d := W₁ - W₂` using the pointwise identity
  `B(W₁)-B(W₂) = -(μ̄₁-μ̄₂)·AK + μ₁·(D_z d - d) + (μ₁-μ₂)·(D_z W₂ - W₂)` of `MuBlockBase`
  (the two `N_*`-collapses need `|μ| ≤ 1/2`, supplied by `MuLamOK` through
  `MuBlockBase.MuLamOK_muOf`), and bounds the three terms by
  `Km·KAK·(1+X₁+X₂)·X`, `Xn5 d` and `Km·(1+X₁+X₂)·Xn5 W₂·Xn5 d` — all dominated by
  `(1+X₁+X₂)²·Xn5 d`, since `1+X₁+X₂ ≥ 1` and `Xn5 W₂ ≤ 1+X₁+X₂`.

The constant `K = max C 1` merges the constant `C` of the `Xn`-bound with positivity. -/
theorem MuBlockClassC {α Ce Cs C₀ : ℝ} {Φs : Work.FTS.Galerkin.Fn}
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
        Work.FTS.StrongEps.EpsRLX.muBlock α Φs E W₁ z θ
          - Work.FTS.StrongEps.EpsRLX.muBlock α Φs E W₂ z θ) ∧
      Work.Spaces.HkMem α 4 (fun z θ =>
        Work.FTS.StrongEps.EpsRLX.muBlock α Φs E W₁ z θ
          - Work.FTS.StrongEps.EpsRLX.muBlock α Φs E W₂ z θ) ∧
      Work.FTS.Nonlin.Xn α (fun z θ =>
        Work.FTS.StrongEps.EpsRLX.muBlock α Φs E W₁ z θ
          - Work.FTS.StrongEps.EpsRLX.muBlock α Φs E W₂ z θ)
        ≤ K * (1 + Work.FTS.GalFields.Xn5 α W₁ + Work.FTS.GalFields.Xn5 α W₂) ^ 2
            * Work.FTS.GalFields.Xn5 α (fun z θ => W₁ z θ - W₂ z θ) := by
  have hα0 : 0 < α := hα.1
  have hα1 : α ≤ 1 := hα.2
  -- ## the Lipschitz constant of the two modulation constants
  obtain ⟨Km, hKm, hmod⟩ := Work.FTS.StrongEps.EpsRLX.ModDiffClassC (α := α) (Ce := Ce) (Cs := Cs)
    (Φs := Φs) (E := E) hα hEll hstar
  -- ## the universal bound on `|AK α|_{ℋ⁴}`
  obtain ⟨KAK, _hKAK, hAK⟩ := Work.FTS.Nonlinear.Pieces.rak_bound
  -- ## the `Xn`-bound of the difference, with the Lipschitz constant `Km`
  obtain ⟨C, _hC, hXnBd⟩ :=
    Work.FTS.StrongEps.EpsRLX.MuBlockXnBound (α := α) (Km := Km) (KAK := KAK) hα0 hKm.le
  refine ⟨max C 1, lt_of_lt_of_le zero_lt_one (le_max_right _ _), ?_⟩
  intro W₁ W₂ hW₁ hW₂ hX₁ hX₂
  -- ## the small-ball bounds on the two modulation constants
  have hμ₁ : |muOf α Φs E W₁| ≤ 1 / 2 :=
    (Work.FTS.StrongEps.EpsRLX.MuLamOK_muOf (α := α) (C₀ := C₀) (Φs := Φs) (E := E)
      hml hW₁ hX₁).1
  have hμ₂ : |muOf α Φs E W₂| ≤ 1 / 2 :=
    (Work.FTS.StrongEps.EpsRLX.MuLamOK_muOf (α := α) (C₀ := C₀) (Φs := Φs) (E := E)
      hml hW₂ hX₂).1
  -- ## the two Lipschitz bounds on `μ̄` and `μ` (`ModDiffClassC`)
  obtain ⟨hbμ, hbμb⟩ := hmod hW₁ hW₂
  have hbμ' : |muOf α Φs E W₁ - muOf α Φs E W₂|
      ≤ Km * (1 + Work.FTS.GalFields.Xn5 α W₁ + Work.FTS.GalFields.Xn5 α W₂)
          * Work.FTS.GalFields.Xn5 α (fun z θ => W₁ z θ - W₂ z θ) := by
    simpa only [muOf] using hbμ
  have hbμb' : |mubarOf α Φs E W₁ - mubarOf α Φs E W₂|
      ≤ Km * (1 + Work.FTS.GalFields.Xn5 α W₁ + Work.FTS.GalFields.Xn5 α W₂)
          * Work.FTS.GalFields.Xn5 α (fun z θ => W₁ z θ - W₂ z θ) := by
    simpa only [mubarOf] using hbμb
  -- ## the `SmoothOpen`/`HkMem` conjuncts
  obtain ⟨hSM, hMEM⟩ := Work.FTS.StrongEps.EpsRLX.MuBlockDiffSmoothMem (α := α) (Φs := Φs)
    (E := E) (W₁ := W₁) (W₂ := W₂) hα hW₁ hW₂
  refine ⟨hSM, hMEM, ?_⟩
  -- ## the `Xn` conjunct
  have hH0 : 0 ≤ Work.FTS.GalFields.Xn5 α (fun z θ => W₁ z θ - W₂ z θ) :=
    Work.Spaces.HkNorm_nonneg α 5 _
  have hP0 : 0 ≤ (1 + Work.FTS.GalFields.Xn5 α W₁ + Work.FTS.GalFields.Xn5 α W₂) ^ 2 *
      Work.FTS.GalFields.Xn5 α (fun z θ => W₁ z θ - W₂ z θ) :=
    mul_nonneg (sq_nonneg _) hH0
  refine le_trans (hXnBd hW₁ hW₂ hμ₁ hμ₂ hbμb' hbμ' (hAK hα0 hα1)) ?_
  have hle : C ≤ max C 1 := le_max_left _ _
  have hgoal : C * (1 + Work.FTS.GalFields.Xn5 α W₁ + Work.FTS.GalFields.Xn5 α W₂) ^ 2
        * Work.FTS.GalFields.Xn5 α (fun z θ => W₁ z θ - W₂ z θ)
      ≤ max C 1 * (1 + Work.FTS.GalFields.Xn5 α W₁ + Work.FTS.GalFields.Xn5 α W₂) ^ 2
        * Work.FTS.GalFields.Xn5 α (fun z θ => W₁ z θ - W₂ z θ) := by
    nlinarith [hle, hP0, hH0,
      sq_nonneg (1 + Work.FTS.GalFields.Xn5 α W₁ + Work.FTS.GalFields.Xn5 α W₂)]
  exact hgoal

end Work.FTS.StrongEps.EpsRLX
