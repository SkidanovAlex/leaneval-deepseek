/-
Copyright: work module for the Elgindi finite-time singularity project.

# `N0pair6Aux/SmoothPieces` — finite-order smoothness of the pieces of `N₀`

At the bare-`f` interface of `Work.FTS.StrongPersist.H6Rows.N0pair6` the coefficient `L₁₂(f)`
is only `ContDiffOn ℝ 7 (·) (Ioi 0)` (`UopHk.contDiffOn_L12_k` with `HkMem α 7 f`), so the
pieces of `N₀` are only finitely smooth.  This file records the `C⁶` smoothness needed by the
pairing splits (`N0pair6Aux.SlotPairingSplit6`) and the `C⁷` smoothness of their seven-fold sum,
which is what the unfolding `N0pair6Aux.ip4UnfoldSix` needs.  All statements are parametrised by
the order, so one proof serves both.
-/
import Mathlib.Analysis.Calculus.ContDiff.Operations
import Mathlib.Analysis.InnerProductSpace.Basic
import Mathlib.Analysis.SpecialFunctions.Trigonometric.Basic
import Submission.Work.FTS.StrongPersist.Clauses
import Submission.Work.FTS.StrongPersist.H6Pair6Aux.H6N0Aux.N0row_defs
import Submission.Work.FTS.StrongPersist.H6Pair6Aux.SmoothN0
import Submission.Work.FTS.EllipticEst.UopHk.L12_contDiffOn_reg
import Submission.Work.FTS.H2.L12HQ

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

noncomputable section
open scoped Real Topology
open MeasureTheory Set Filter

namespace Work.FTS.StrongPersist.H6Rows.N0pair6Aux

open Work.FTS.StrongPersist.H6Pair6Aux (NA1 NA4 NA5 NA6 NP3 NP4a NP4b NP5a NP5b NP6)

set_option autoImplicit false
set_option linter.unusedVariables false

/-- The open quadrant, in the shape `SmoothOpen`-statements use. -/
abbrev Q0 : Set (ℝ × ℝ) := Work.FTS.EllipticEst.Q0

/-- A radial factor which is `C^k` on `(0,∞)` times a `C^k` function on the open quadrant is
`C^k` on the open quadrant. -/
theorem contDiffOn_radial_mul {k : ℕ} {X : ℝ → ℝ} {ψ : ℝ → ℝ → ℝ}
    (hX : ContDiffOn ℝ k X (Set.Ioi 0))
    (hψ : ContDiffOn ℝ k (Function.uncurry ψ) Q0) :
    ContDiffOn ℝ k (Function.uncurry (fun z θ => X z * ψ z θ)) Q0 := by
  have h : Function.uncurry (fun z θ => X z * ψ z θ)
      = (fun p : ℝ × ℝ => X p.1) * Function.uncurry ψ := by
    funext p; rcases p with ⟨z, θ⟩; rfl
  rw [h]
  exact (hX.comp contDiffOn_fst
    (fun p hp => (Work.FTS.EllipticEst.mem_Q0.mp hp).1)).mul hψ

/-- Multiplication by a constant, for `C^k`-functions on the open quadrant. -/
theorem contDiffOn_const_mul {k : ℕ} (c : ℝ) {F : ℝ × ℝ → ℝ}
    (h : ContDiffOn ℝ k F Q0) : ContDiffOn ℝ k (fun p => c * F p) Q0 :=
  contDiffOn_const.mul h

/-- The `C^k` smoothness of the six `f`-dependent pieces of `N₀`, from the `C^k` smoothness of
the radial factor `L₁₂(f)` (all the other factors are smooth on the open quadrant). -/
theorem N0piecesSmooth {α : ℝ} {f : ℝ → ℝ → ℝ}
    (hsmf : Work.FTS.EllipticEst.SmoothOpen f) {k : ℕ}
    (hLk : ContDiffOn ℝ k (fun z => Work.Construction.L12 f z) (Set.Ioi 0)) :
    ContDiffOn ℝ k (Function.uncurry (NP3 α f)) Q0 ∧
    ContDiffOn ℝ k (Function.uncurry (NP4a α f)) Q0 ∧
    ContDiffOn ℝ k (Function.uncurry (NP4b α f)) Q0 ∧
    ContDiffOn ℝ k (Function.uncurry (NP5a α f)) Q0 ∧
    ContDiffOn ℝ k (Function.uncurry (NP5b α f)) Q0 ∧
    ContDiffOn ℝ k (Function.uncurry (NP6 α f)) Q0 := by
  have hfk : ContDiffOn ℝ k (Function.uncurry (fun z θ => f z θ)) Q0 :=
    (Work.FTS.EllipticEst.smoothOpen_iff_forall f).mp hsmf k
  have hDthk : ContDiffOn ℝ k (Function.uncurry (Work.Spaces.Dth f)) Q0 :=
    (Work.FTS.EllipticEst.smoothOpen_iff_forall (Work.Spaces.Dth f)).mp hsmf.Dth k
  have hDzk : ContDiffOn ℝ k (Function.uncurry (Work.Spaces.Dz f)) Q0 :=
    (Work.FTS.EllipticEst.smoothOpen_iff_forall (Work.Spaces.Dz f)).mp hsmf.Dz k
  have hNA4k : ContDiffOn ℝ k (Function.uncurry (NA4 α)) Q0 :=
    (Work.FTS.EllipticEst.smoothOpen_iff_forall (NA4 α)).mp
      (Work.FTS.StrongPersist.H6Pair6Aux.smoothOpen_NA4 α) k
  have hNA5k : ContDiffOn ℝ k (Function.uncurry (NA5 α)) Q0 :=
    (Work.FTS.EllipticEst.smoothOpen_iff_forall (NA5 α)).mp
      (Work.FTS.StrongPersist.H6Pair6Aux.smoothOpen_NA5 α) k
  have hNA6k : ContDiffOn ℝ k (Function.uncurry (NA6 α)) Q0 :=
    (Work.FTS.EllipticEst.smoothOpen_iff_forall (NA6 α)).mp
      (Work.FTS.StrongPersist.H6Pair6Aux.smoothOpen_NA6 α) k
  have hCk : ContDiffOn ℝ k (Function.uncurry (fun z θ => Work.Construction.c2m θ)) Q0 :=
    (Work.FTS.EllipticEst.smoothOpen_iff_forall
      (fun z θ => Work.Construction.c2m θ)).mp
      (Work.FTS.StrongPersist.H6Pair6Aux.so_snd
        Work.FTS.StrongPersist.H6Pair6Aux.contDiff_c2m) k
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · -- `NP3 = (1/α)·(L₁₂ f · f)`
    refine (contDiffOn_const_mul (1 / α)
      (contDiffOn_radial_mul hLk hfk)).congr (fun p _ => ?_)
    rcases p with ⟨z, θ⟩
    simp only [NP3, Function.uncurry, Pi.mul_apply]
  · -- `NP4a = (3/(2α))·(L₁₂ f · D_θF_*)`
    refine (contDiffOn_const_mul (3 / (2 * α))
      (contDiffOn_radial_mul hLk hNA4k)).congr (fun p _ => ?_)
    rcases p with ⟨z, θ⟩
    simp only [NP4a, Function.uncurry, Pi.mul_apply]
  · -- `NP4b = (3/(2α))·(L₁₂ f · D_θ f)`
    refine (contDiffOn_const_mul (3 / (2 * α))
      (contDiffOn_radial_mul hLk hDthk)).congr (fun p _ => ?_)
    rcases p with ⟨z, θ⟩
    simp only [NP4b, Function.uncurry, Pi.mul_apply]
  · -- `NP5a = (-1)·(L₁₂ f · (c₂ₘ·D_zF_*))`
    refine (contDiffOn_const_mul (-1)
      (contDiffOn_radial_mul hLk hNA5k)).congr (fun p _ => ?_)
    rcases p with ⟨z, θ⟩
    simp only [NP5a, Function.uncurry, Pi.mul_apply]
  · -- `NP5b = (-1)·(c₂ₘ · L₁₂ f · D_z f)`
    have hψ : ContDiffOn ℝ k
        (Function.uncurry (fun z θ => Work.Construction.c2m θ * Work.Spaces.Dz f z θ)) Q0 := by
      have h : Function.uncurry (fun z θ => Work.Construction.c2m θ * Work.Spaces.Dz f z θ)
          = (Function.uncurry (fun z θ => Work.Construction.c2m θ))
            * Function.uncurry (Work.Spaces.Dz f) := by
        funext p; rcases p with ⟨z, θ⟩; rfl
      rw [h]; exact hCk.mul hDzk
    refine (contDiffOn_const_mul (-1)
      (contDiffOn_radial_mul hLk hψ)).congr (fun p _ => ?_)
    rcases p with ⟨z, θ⟩
    simp only [NP5b, Function.uncurry, Pi.mul_apply]
    ring
  · -- `NP6 = (-1)·(c₂ₘ·L₁₂(F_*)·D_z f)`
    have hψ : ContDiffOn ℝ k
        (Function.uncurry (fun z θ => NA6 α z θ * Work.Spaces.Dz f z θ)) Q0 := by
      have h : Function.uncurry (fun z θ => NA6 α z θ * Work.Spaces.Dz f z θ)
          = Function.uncurry (NA6 α) * Function.uncurry (Work.Spaces.Dz f) := by
        funext p; rcases p with ⟨z, θ⟩; rfl
      rw [h]; exact hNA6k.mul hDzk
    refine (contDiffOn_const_mul (-1) hψ).congr (fun p _ => ?_)
    rcases p with ⟨z, θ⟩
    simp only [NP6, Function.uncurry, Pi.mul_apply]

/-- The seven-fold sum `NA1 + NP3 + … + NP6` of the pieces of `N₀`, as a function. -/
def N0Sum (α : ℝ) (f : ℝ → ℝ → ℝ) : ℝ → ℝ → ℝ := fun z θ =>
  NA1 α z θ + NP3 α f z θ + NP4a α f z θ + NP4b α f z θ + NP5a α f z θ
    + NP5b α f z θ + NP6 α f z θ

/-- The `C^k` smoothness of the seven-fold sum of the pieces of `N₀`. -/
theorem N0SumSmooth {α : ℝ} {f : ℝ → ℝ → ℝ}
    (hsmf : Work.FTS.EllipticEst.SmoothOpen f) {k : ℕ}
    (hLk : ContDiffOn ℝ k (fun z => Work.Construction.L12 f z) (Set.Ioi 0)) :
    ContDiffOn ℝ k (Function.uncurry (N0Sum α f)) Q0 := by
  obtain ⟨h3, h4a, h4b, h5a, h5b, h6⟩ := N0piecesSmooth (α := α) hsmf hLk
  have h1 : ContDiffOn ℝ k (Function.uncurry (fun z θ => NA1 α z θ)) Q0 :=
    (Work.FTS.EllipticEst.smoothOpen_iff_forall (fun z θ => NA1 α z θ)).mp
      (Work.FTS.StrongPersist.H6Pair6Aux.smoothOpen_NA1 α) k
  have h13 : ContDiffOn ℝ k (Function.uncurry (fun z θ => NA1 α z θ + NP3 α f z θ)) Q0 := by
    have h : Function.uncurry (fun z θ => NA1 α z θ + NP3 α f z θ)
        = Function.uncurry (fun z θ => NA1 α z θ) + Function.uncurry (NP3 α f) := by
      funext p; rcases p with ⟨z, θ⟩; rfl
    rw [h]; exact h1.add h3
  have h134a : ContDiffOn ℝ k
      (Function.uncurry (fun z θ => NA1 α z θ + NP3 α f z θ + NP4a α f z θ)) Q0 := by
    have h : Function.uncurry (fun z θ => NA1 α z θ + NP3 α f z θ + NP4a α f z θ)
        = Function.uncurry (fun z θ => NA1 α z θ + NP3 α f z θ)
          + Function.uncurry (NP4a α f) := by
      funext p; rcases p with ⟨z, θ⟩; rfl
    rw [h]; exact h13.add h4a
  have h134ab : ContDiffOn ℝ k
      (Function.uncurry (fun z θ => NA1 α z θ + NP3 α f z θ + NP4a α f z θ
        + NP4b α f z θ)) Q0 := by
    have h : Function.uncurry (fun z θ => NA1 α z θ + NP3 α f z θ + NP4a α f z θ
          + NP4b α f z θ)
        = Function.uncurry (fun z θ => NA1 α z θ + NP3 α f z θ + NP4a α f z θ)
          + Function.uncurry (NP4b α f) := by
      funext p; rcases p with ⟨z, θ⟩; rfl
    rw [h]; exact h134a.add h4b
  have h134ab5a : ContDiffOn ℝ k
      (Function.uncurry (fun z θ => NA1 α z θ + NP3 α f z θ + NP4a α f z θ
        + NP4b α f z θ + NP5a α f z θ)) Q0 := by
    have h : Function.uncurry (fun z θ => NA1 α z θ + NP3 α f z θ + NP4a α f z θ
          + NP4b α f z θ + NP5a α f z θ)
        = Function.uncurry (fun z θ => NA1 α z θ + NP3 α f z θ + NP4a α f z θ
            + NP4b α f z θ)
          + Function.uncurry (NP5a α f) := by
      funext p; rcases p with ⟨z, θ⟩; rfl
    rw [h]; exact h134ab.add h5a
  have h134ab5ab : ContDiffOn ℝ k
      (Function.uncurry (fun z θ => NA1 α z θ + NP3 α f z θ + NP4a α f z θ
        + NP4b α f z θ + NP5a α f z θ + NP5b α f z θ)) Q0 := by
    have h : Function.uncurry (fun z θ => NA1 α z θ + NP3 α f z θ + NP4a α f z θ
          + NP4b α f z θ + NP5a α f z θ + NP5b α f z θ)
        = Function.uncurry (fun z θ => NA1 α z θ + NP3 α f z θ + NP4a α f z θ
            + NP4b α f z θ + NP5a α f z θ)
          + Function.uncurry (NP5b α f) := by
      funext p; rcases p with ⟨z, θ⟩; rfl
    rw [h]; exact h134ab5a.add h5b
  have hall : ContDiffOn ℝ k (Function.uncurry (N0Sum α f)) Q0 := by
    have h : Function.uncurry (N0Sum α f)
        = Function.uncurry (fun z θ => NA1 α z θ + NP3 α f z θ + NP4a α f z θ
            + NP4b α f z θ + NP5a α f z θ + NP5b α f z θ)
          + Function.uncurry (NP6 α f) := by
      funext p; rcases p with ⟨z, θ⟩; rfl
    rw [h]; exact h134ab5ab.add h6
  exact hall

end Work.FTS.StrongPersist.H6Rows.N0pair6Aux
