/-
Copyright: work module for the Elgindi finite-time singularity project.

# `Submission/Work/FTS/StrongEps/EpsLocalPStar/EpsRHSPLipX_Sq.lean`

**The `X`-ball gate of the projected `ε`-scheme.**

The right-hand side `epsRHPSlice α ρ ε Φs E 0 u = Pz (J_ε (profRHS α Φs E (Pz (J_ε u))))` is
bounded in the honest weighted space `X = (EpsMem, EpsSq)` at every profile of the *ball*
`SmoothOpen u ∧ EpsMem α u ∧ EpsSq α u ≤ R ∧ ClassC α (Wp ρ ε u) ∧ Xn α (Wp ρ ε u) ≤ C₀α²`, and is
Lipschitz in `X` with respect to the datum (with `EpsMem α (u-v)` as the honesty hypothesis of the
right-hand side).

This is the `X`-ball form of the sibling gate `EpsLocalPStar.EpsRHSPLipX` (which assumes the strong
`ℋ⁶`-data `HkMem α 6 u` and `HkNorm α 6 u ≤ B` instead): the ball form is what the Picard
iteration of `EpsLocalPStar` can maintain.  The whole `ℋ`-information about the profile is
manufactured from the ball data by the interface module `EpsLocalPStar.XBallFacts`
(`exists_Wp_bound_of_EpsMem`, `HkMem_Jeps_of_ClassC_Wp`, `Wp_sub_eq_of_ClassC`,
`HkSq_Wp_sub_le_of_ClassC`).

The statement is frozen (a colleague consumes `Work.FTS.StrongEps.EpsLocalPStar.EpsRHSPLipX_Sq`
verbatim).  It is discharged as the conjunction of its two clauses:

* the *size half* `ConjOneSq` (below), adapting `EpsRLX.ConjOne`:
  `EpsSq α (Pz (J_ε Φ)) ≤ C_P · EpsSq α (J_ε Φ) ≤ C_P C_J · EpsSq α Φ ≤ C_P C_J R₂`, where the
  profile size needed by `XDataClean`/`ProfRHSEpsData` is `BS = C_W (C_W/ε)⁶ (1+R)` from the ball
  data (`exists_Wp_bound_of_EpsMem`);
* the *Lipschitz half* `ConjTwoSq` (module `EpsLocalPStar.ConjTwoSq`), adapting `EpsRLX.ConjTwo`
  with the same profile size and with `HkSq_Wp_sub_le_of_ClassC` in place of `DeltaData`,

glued with `L := max L₁ L₂`.
-/
import Mathlib.Algebra.Order.Ring.Star
import Mathlib.Analysis.Calculus.ContDiff.Defs
import Mathlib.MeasureTheory.Measure.Haar.OfBasis
import Submission.Work.FTS.StrongEps.EpsLocalPStar.EpsRHSPLipX
import Submission.Work.FTS.StrongEps.EpsLocalPStar.XBallFacts
import Submission.Work.FTS.StrongEps.EpsLocalPStar.ConjTwoSq
import Submission.Work.FTS.StrongEps.EpsRLX.ConjOne
import Submission.Work.FTS.StrongEps.EpsRLX.ConjTwo
import Submission.Work.FTS.StrongEps.EpsSqTools.HkSq_JepsPz_le
import Submission.Work.FTS.StrongEps.EpsRLX.DeltaData
import Submission.Work.FTS.StrongEps.EpsLocalPStar.EpsRHSXrhs

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

namespace Work.FTS.StrongEps.EpsLocalPStar

open scoped Real Topology
open MeasureTheory Set Filter
open Work.FTS.Galerkin (Fn)

set_option autoImplicit false
set_option linter.unusedVariables false
set_option maxHeartbeats 1600000

/-- **The size half of the `X`-ball gate.**  For the parameters of the projected `ε`-scheme there
is a constant `L₁ > 0` such that for every `u` in the ball

  `SmoothOpen u`, `EpsMem α u`, `EpsSq α u ≤ R`, `ClassC α (Wp ρ ε u)`, `Xn α (Wp ρ ε u) ≤ C₀α²`

one has `EpsMem α (epsRHPSlice α ρ ε Φs E 0 u) ∧ EpsSq α (epsRHPSlice α ρ ε Φs E 0 u) ≤ L₁`.

The proof is `EpsRLX.ConjOne` with the datum's `ℋ⁶`-bound replaced by the profile bound
`exists_Wp_bound_of_EpsMem` (at `k = 6`): `W := Wp ρ ε u` is admissible for
`XDataClean`/`ProfRHSEpsData` with the size `BS = C_W (C_W/ε)⁶ (1+R)`. -/
theorem ConjOneSq {α C₀ Ce Cs R : ℝ} {ρ : ℝ × ℝ → ℝ} {Φs : Fn} {E : Fn → Fn} {ε : ℝ}
    (hα : α ∈ Set.Ioc 0 1) (hρ : Work.FTS.StrongEps.IsSmoothKernel ρ) (hε : 0 < ε)
    (hε1 : ε ≤ 1)
    (hEll : ∀ u : Fn, Work.FTS.ClassC.ClassC α u →
      Work.FTS.VocabO.EllPkgGo α Ce u (E u) ∧ Work.FTS.ClassC.EllPkgK α 6 Ce u (E u))
    (hstar : Work.FTS.VocabO2.StarPkgo2 α Cs Φs)
    (hml : Work.FTS.StrongEps.MuLamOK α C₀ Φs E) (hR : 0 ≤ R) :
    ∃ L : ℝ, 0 < L ∧ ∀ u : Fn,
      Work.FTS.EllipticEst.SmoothOpen u → Work.FTS.StrongEps.EpsMem α u →
      Work.FTS.StrongEps.EpsSq α u ≤ R →
      Work.FTS.ClassC.ClassC α (Work.FTS.StrongEps.EpsRLX.Wp ρ ε u) →
      Work.FTS.Nonlin.Xn α (Work.FTS.StrongEps.EpsRLX.Wp ρ ε u) ≤ C₀ * α ^ 2 →
      Work.FTS.StrongEps.EpsMem α (Work.FTS.StrongEps.epsRHPSlice α ρ ε Φs E 0 u) ∧
      Work.FTS.StrongEps.EpsSq α (Work.FTS.StrongEps.epsRHPSlice α ρ ε Φs E 0 u) ≤ L := by
  -- ## the profile size furnished by the ball data
  obtain ⟨CW, hCWpos, hCW⟩ := exists_Wp_bound_of_EpsMem (ρ := ρ) hρ
  set BS : ℝ := CW * (CW / ε) ^ 6 * (1 + R) with hBSdef
  have hBS0 : 0 ≤ BS := by rw [hBSdef]; positivity
  have hW6 : ∀ (u : Fn), Work.FTS.EllipticEst.SmoothOpen u → Work.FTS.StrongEps.EpsMem α u →
      Work.FTS.StrongEps.EpsSq α u ≤ R →
      Work.Spaces.HkNorm α 6 (Work.FTS.StrongEps.EpsRLX.Wp ρ ε u) ≤ BS :=
    fun u hu hmem hEps => by
      rw [hBSdef]
      exact hCW α hα ε ⟨hε, hε1⟩ R hR u hu hmem hEps 6 (by norm_num)
  -- ## the data of the pre-mollified right-hand side, at the enlarged size
  obtain ⟨_, -, hRXdata⟩ :=
    Work.FTS.StrongEps.EpsRLX.XDataClean (α := α) (Ce := Ce) (Cs := Cs) (C₀ := C₀) (B := BS)
      hα hEll hstar hml hBS0
  obtain ⟨R₂, hR₂pos, hR₂⟩ :=
    Work.FTS.StrongEps.EpsRLX.ProfRHSEpsData (α := α) (C₀ := C₀) (Ce := Ce) (Cs := Cs)
      (B := BS) hα hEll hstar hml hBS0
  obtain ⟨CP, hCPpos, hCP⟩ := Work.FTS.StrongEps.EpsRLX.EpsSq_Pz_le
  obtain ⟨CJ, hCJpos, hCJ⟩ := Work.FTS.StrongEps.EpsSqTools.EpsSq_mixed_Jeps_le ρ hρ
  obtain ⟨CM, -, hCM⟩ := Work.FTS.StrongEps.EpsSqTools.EpsSqIter_mixed_Jeps_le6 ρ hρ
  refine ⟨max 1 (CP * CJ * R₂), lt_of_lt_of_le zero_lt_one (le_max_left _ _), ?_⟩
  intro u hu hmem hEps hclu hxnu
  -- ## the profile and the pre-mollified right-hand side
  set W : Fn := Work.FTS.StrongEps.Pz (Work.FTS.StrongEps.Jeps ρ ε u) with hWdef
  set Φ : Fn := profRHS α Φs E W with hΦdef
  have hclW : Work.FTS.ClassC.ClassC α W := hclu
  have hxnW : Work.FTS.Nonlin.Xn α W ≤ C₀ * α ^ 2 := hxnu
  have hWb : Work.Spaces.HkNorm α 6 W ≤ BS := hW6 u hu hmem hEps
  obtain ⟨hXsm, hXmem, -⟩ := hRXdata hclW hxnW hWb
  obtain ⟨hXepsMem, hXepsSq⟩ := hR₂ hclW hxnW hWb
  -- ## the mollified pre-mollified profile
  have hsmΦ : ∀ n : ℕ, ContDiffOn ℝ n (Function.uncurry Φ) Work.FTS.StrongEps.Quad :=
    (Work.FTS.EllipticEst.smoothOpen_iff_forall Φ).mp hXsm
  have hJsm : Work.FTS.EllipticEst.SmoothOpen (Work.FTS.StrongEps.Jeps ρ ε Φ) :=
    Work.FTS.StrongEps.smoothOpen_Jeps ρ hρ hε hsmΦ
  have hJmem : Work.Spaces.HkMem α 4 (Work.FTS.StrongEps.Jeps ρ ε Φ) :=
    Work.FTS.StrongEps.HkMem_Jeps hρ.moll hα hε hsmΦ hXmem
  have hJepsMem : Work.FTS.StrongEps.EpsMem α (Work.FTS.StrongEps.Jeps ρ ε Φ) :=
    (hCM α hα ε hε hε1 Φ hsmΦ hXepsMem).1
  have hJepsSq : Work.FTS.StrongEps.EpsSq α (Work.FTS.StrongEps.Jeps ρ ε Φ)
      ≤ CJ * Work.FTS.StrongEps.EpsSq α Φ := by
    have h := hCJ α hα ε ⟨hε, hε1⟩ Φ hsmΦ hXepsMem 0 0 (by norm_num)
    have h1 : Work.FTS.StrongEps.EpsSq α
        (Work.Spaces.mixed 0 0 (Work.FTS.StrongEps.Jeps ρ ε Φ))
        = Work.FTS.StrongEps.EpsSq α (Work.FTS.StrongEps.Jeps ρ ε Φ) := by
      simp only [Work.Spaces.mixed_zero_left, Work.Spaces.DthIter_zero]
    have h2 : CJ * (CJ / ε) ^ (2 * (0 + 0)) * Work.FTS.StrongEps.EpsSq α Φ
        = CJ * Work.FTS.StrongEps.EpsSq α Φ := by norm_num
    rw [h1, h2] at h
    exact h
  obtain ⟨hPzMem, hPzSq⟩ := hCP α hα (Work.FTS.StrongEps.Jeps ρ ε Φ) hJsm hJmem hJepsMem
  have hslice : Work.FTS.StrongEps.epsRHPSlice α ρ ε Φs E 0 u
      = Work.FTS.StrongEps.Pz (Work.FTS.StrongEps.Jeps ρ ε Φ) := by
    rw [Work.FTS.StrongEps.EpsLocalPStar.epsRHPSlice_eq_profRHS]
  refine ⟨?_, ?_⟩
  · rw [hslice]; exact hPzMem
  · rw [hslice]
    calc Work.FTS.StrongEps.EpsSq α (Work.FTS.StrongEps.Pz (Work.FTS.StrongEps.Jeps ρ ε Φ))
        ≤ CP * Work.FTS.StrongEps.EpsSq α (Work.FTS.StrongEps.Jeps ρ ε Φ) := hPzSq
      _ ≤ CP * (CJ * Work.FTS.StrongEps.EpsSq α Φ) :=
          mul_le_mul_of_nonneg_left hJepsSq hCPpos.le
      _ = CP * CJ * Work.FTS.StrongEps.EpsSq α Φ := by ring
      _ ≤ CP * CJ * R₂ := mul_le_mul_of_nonneg_left hXepsSq (mul_nonneg hCPpos.le hCJpos.le)
      _ ≤ max 1 (CP * CJ * R₂) := le_max_right _ _

theorem EpsRHSPLipX_Sq {α C₀ Ce Cs R : ℝ} {ρ : ℝ × ℝ → ℝ} {Φs : Work.FTS.Galerkin.Fn}
    {E : Work.FTS.Galerkin.Fn → Work.FTS.Galerkin.Fn} {ε : ℝ}
    (hα : α ∈ Set.Ioc 0 1) (hρ : Work.FTS.StrongEps.IsSmoothKernel ρ) (hε : 0 < ε) (hε1 : ε ≤ 1)
    (hEll : ∀ u : Work.FTS.Galerkin.Fn, Work.FTS.ClassC.ClassC α u →
      Work.FTS.VocabO.EllPkgGo α Ce u (E u) ∧ Work.FTS.ClassC.EllPkgK α 6 Ce u (E u))
    (hstar : Work.FTS.VocabO2.StarPkgo2 α Cs Φs)
    (hml : Work.FTS.StrongEps.MuLamOK α C₀ Φs E) (hR : 0 ≤ R) :
    ∃ L : ℝ, 0 < L ∧
      (∀ u : Work.FTS.Galerkin.Fn, Work.FTS.EllipticEst.SmoothOpen u →
        Work.FTS.StrongEps.EpsMem α u →
        Work.FTS.StrongEps.EpsSq α u ≤ R →
        Work.FTS.ClassC.ClassC α (Work.FTS.StrongEps.EpsRLX.Wp ρ ε u) →
        Work.FTS.Nonlin.Xn α (Work.FTS.StrongEps.EpsRLX.Wp ρ ε u) ≤ C₀ * α ^ 2 →
        Work.FTS.StrongEps.EpsMem α (Work.FTS.StrongEps.epsRHPSlice α ρ ε Φs E 0 u) ∧
        Work.FTS.StrongEps.EpsSq α (Work.FTS.StrongEps.epsRHPSlice α ρ ε Φs E 0 u) ≤ L) ∧
      (∀ u v : Work.FTS.Galerkin.Fn, Work.FTS.EllipticEst.SmoothOpen u →
        Work.FTS.EllipticEst.SmoothOpen v →
        Work.FTS.StrongEps.EpsMem α u →
        Work.FTS.StrongEps.EpsSq α u ≤ R →
        Work.FTS.ClassC.ClassC α (Work.FTS.StrongEps.EpsRLX.Wp ρ ε u) →
        Work.FTS.Nonlin.Xn α (Work.FTS.StrongEps.EpsRLX.Wp ρ ε u) ≤ C₀ * α ^ 2 →
        Work.FTS.StrongEps.EpsMem α v → Work.FTS.StrongEps.EpsSq α v ≤ R →
        Work.FTS.ClassC.ClassC α (Work.FTS.StrongEps.EpsRLX.Wp ρ ε v) →
        Work.FTS.Nonlin.Xn α (Work.FTS.StrongEps.EpsRLX.Wp ρ ε v) ≤ C₀ * α ^ 2 →
        Work.FTS.StrongEps.EpsMem α (fun z θ => u z θ - v z θ) →
        Work.FTS.StrongEps.EpsSq α (fun z θ => Work.FTS.StrongEps.epsRHPSlice α ρ ε Φs E 0 u z θ
            - Work.FTS.StrongEps.epsRHPSlice α ρ ε Φs E 0 v z θ)
          ≤ L * Work.FTS.StrongEps.EpsSq α (fun z θ => u z θ - v z θ)) := by
  obtain ⟨L₁, hL₁pos, hL₁⟩ := ConjOneSq (ρ := ρ) (Φs := Φs) (E := E) hα hρ hε hε1 hEll hstar hml hR
  obtain ⟨L₂, hL₂pos, hL₂⟩ := ConjTwoSq (ρ := ρ) (Φs := Φs) (E := E) hα hρ hε hε1 hEll hstar hml hR
  refine ⟨max L₁ L₂, lt_of_lt_of_le hL₁pos (le_max_left L₁ L₂), ?_, ?_⟩
  · intro u hu hmem hEps hcl hxn
    obtain ⟨hmem', hbd⟩ := hL₁ u hu hmem hEps hcl hxn
    exact ⟨hmem', le_trans hbd (le_max_left L₁ L₂)⟩
  · intro u v hu hv hmu hEu hclu hxnu hmv hEv hclv hxnv hmuv
    refine le_trans (hL₂ u v hu hv hmu hEu hclu hxnu hmv hEv hclv hxnv hmuv) ?_
    exact mul_le_mul_of_nonneg_right (le_max_right L₁ L₂)
      (Work.FTS.StrongEps.EpsSq_nonneg α (fun z θ => u z θ - v z θ))

end Work.FTS.StrongEps.EpsLocalPStar
