/-
Copyright: work module for the Elgindi finite-time singularity project.

# `Submission/Work/FTS/StrongEps/EpsE4Thr/HkNorm_epsRHSP_le.lean` — the ε-uniform `ℋ⁴` size of the
scheme's right-hand side, along a family

`EpsLocalPStar.EpsRHSPBdd` (proved) bounds the `ℋ⁴`-size of the projected scheme's right-hand side
by a constant `R` which depends only on `(α, C₀, Ce, Cs, B, ε)` — *not* on the fake time and *not*
on the slice, only on its class-`C` small-ball data and its `ℋ⁶`-size `B`.  Because
`epsRHSP α ρ ε Φs E g σ = epsRHPSlice α ρ ε Φs E σ (slice g σ)` (`epsRHSP_eq_slice`), this is
immediately the *uniform in the fake time* bound along a family, which is the "obligation (c)" of
`NOTES_EpsLocal.md` §4:

  `∃ R > 0, ∀ σ ∈ [0,T], |epsRHSP α ρ ε Φs E g σ|_{ℋ⁴} ≤ R`   (and hence `HkSq α 4 ≤ R²`).

This is the input `hK` (for the derivative family) and the `ℋ⁴`-size control of the level-four
and level-six energy estimates.

Everything here is `sorry`-free.
-/
import Mathlib.Analysis.Real.Sqrt
import Submission.Work.FTS.StrongEps.EpsLocalPStar.EpsRHSPBdd

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

noncomputable section
open scoped Real Topology
open MeasureTheory Set Filter

namespace Work.FTS.StrongEps.EpsE4Thr

open Work.FTS.Galerkin (Fn Fam slice)

set_option autoImplicit false

/-- **The `ℋ⁴`-size of the scheme's right-hand side is bounded uniformly in the fake time.**
This is `EpsLocalPStar.EpsRHSPBdd` transported to the *family* form via
`StrongEps.epsRHSP_eq_slice`. -/
theorem HkNorm_epsRHSP_le {α C₀ Ce Cs B : ℝ} {ρ : ℝ × ℝ → ℝ} {Φs : Fn} {E : Fn → Fn} {g : Fam}
    {ε T : ℝ}
    (hα : α ∈ Set.Ioc 0 1) (hρ : Work.FTS.StrongEps.IsSmoothKernel ρ) (hε : 0 < ε) (hε1 : ε ≤ 1)
    (hEll : ∀ u : Fn, Work.FTS.ClassC.ClassC α u →
      Work.FTS.VocabO.EllPkgGo α Ce u (E u) ∧ Work.FTS.ClassC.EllPkgK α 6 Ce u (E u))
    (hstar : Work.FTS.VocabO2.StarPkgo2 α Cs Φs)
    (hml : Work.FTS.StrongEps.MuLamOK α C₀ Φs E) (hB : 0 ≤ B)
    (hsm : ∀ s ∈ Set.Icc (0 : ℝ) T, Work.FTS.EllipticEst.SmoothOpen (slice g s))
    (hmem : ∀ s ∈ Set.Icc (0 : ℝ) T, Work.Spaces.HkMem α 6 (slice g s))
    (hbd : ∀ s ∈ Set.Icc (0 : ℝ) T, Work.Spaces.HkNorm α 6 (slice g s) ≤ B)
    (hC : ∀ s ∈ Set.Icc (0 : ℝ) T,
      Work.FTS.ClassC.ClassC α (Work.FTS.StrongEps.Pz (Work.FTS.StrongEps.Jeps ρ ε (slice g s))))
    (hball : ∀ s ∈ Set.Icc (0 : ℝ) T,
      Work.FTS.Nonlin.Xn α (Work.FTS.StrongEps.Pz (Work.FTS.StrongEps.Jeps ρ ε (slice g s)))
        ≤ C₀ * α ^ 2) :
    ∃ R : ℝ, 0 < R ∧ ∀ σ ∈ Set.Icc (0 : ℝ) T,
      Work.Spaces.HkNorm α 4 (Work.FTS.StrongEps.epsRHSP α ρ ε Φs E g σ) ≤ R := by
  obtain ⟨R, hR, hbdR⟩ :=
    Work.FTS.StrongEps.EpsLocalPStar.EpsRHSPBdd (α := α) (C₀ := C₀) (Ce := Ce) (Cs := Cs)
      (B := B) (ρ := ρ) (Φs := Φs) (E := E) (ε := ε) hα hρ hε hε1 hEll hstar hml hB
  refine ⟨R, hR, fun σ hσ => ?_⟩
  rw [Work.FTS.StrongEps.epsRHSP_eq_slice]
  exact (hbdR σ (slice g σ) (hsm σ hσ) (hmem σ hσ) (hbd σ hσ) (hC σ hσ) (hball σ hσ)).2.2

/-- The squared form of `HkNorm_epsRHSP_le`: the `ℋ⁴`-*square* of the scheme's right-hand side is
bounded uniformly in the fake time by `R²`. -/
theorem HkSq_epsRHSP_le {α C₀ Ce Cs B : ℝ} {ρ : ℝ × ℝ → ℝ} {Φs : Fn} {E : Fn → Fn} {g : Fam}
    {ε T : ℝ}
    (hα : α ∈ Set.Ioc 0 1) (hρ : Work.FTS.StrongEps.IsSmoothKernel ρ) (hε : 0 < ε) (hε1 : ε ≤ 1)
    (hEll : ∀ u : Fn, Work.FTS.ClassC.ClassC α u →
      Work.FTS.VocabO.EllPkgGo α Ce u (E u) ∧ Work.FTS.ClassC.EllPkgK α 6 Ce u (E u))
    (hstar : Work.FTS.VocabO2.StarPkgo2 α Cs Φs)
    (hml : Work.FTS.StrongEps.MuLamOK α C₀ Φs E) (hB : 0 ≤ B)
    (hsm : ∀ s ∈ Set.Icc (0 : ℝ) T, Work.FTS.EllipticEst.SmoothOpen (slice g s))
    (hmem : ∀ s ∈ Set.Icc (0 : ℝ) T, Work.Spaces.HkMem α 6 (slice g s))
    (hbd : ∀ s ∈ Set.Icc (0 : ℝ) T, Work.Spaces.HkNorm α 6 (slice g s) ≤ B)
    (hC : ∀ s ∈ Set.Icc (0 : ℝ) T,
      Work.FTS.ClassC.ClassC α (Work.FTS.StrongEps.Pz (Work.FTS.StrongEps.Jeps ρ ε (slice g s))))
    (hball : ∀ s ∈ Set.Icc (0 : ℝ) T,
      Work.FTS.Nonlin.Xn α (Work.FTS.StrongEps.Pz (Work.FTS.StrongEps.Jeps ρ ε (slice g s)))
        ≤ C₀ * α ^ 2) :
    ∃ R : ℝ, 0 < R ∧ ∀ σ ∈ Set.Icc (0 : ℝ) T,
      Work.Spaces.HkSq α 4 (Work.FTS.StrongEps.epsRHSP α ρ ε Φs E g σ) ≤ R ^ 2 := by
  obtain ⟨R, hR, hbdR⟩ := HkNorm_epsRHSP_le (α := α) (C₀ := C₀) (Ce := Ce) (Cs := Cs) (B := B)
    (ρ := ρ) (Φs := Φs) (E := E) (g := g) (ε := ε) (T := T)
    hα hρ hε hε1 hEll hstar hml hB hsm hmem hbd hC hball
  refine ⟨R, hR, fun σ hσ => ?_⟩
  have h1 : Work.Spaces.HkSq α 4 (Work.FTS.StrongEps.epsRHSP α ρ ε Φs E g σ)
      = (Work.Spaces.HkNorm α 4 (Work.FTS.StrongEps.epsRHSP α ρ ε Φs E g σ)) ^ 2 := by
    rw [Work.Spaces.HkNorm, Real.sq_sqrt (Work.Spaces.HkSq_nonneg α 4 _)]
  rw [h1]
  exact pow_le_pow_left₀ (Work.Spaces.HkNorm_nonneg α 4 _) (hbdR σ hσ) 2

end Work.FTS.StrongEps.EpsE4Thr
