import Mathlib.Analysis.SpecialFunctions.Pow.Real
import Submission.Work.FTS.GalFields.RHS.sharpN0_defs
import Submission.Work.FTS.GalFields.RHS.sharpN0_tof
import Submission.Work.FTS.GalFields.RHS.sharpN0_piecesA

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

namespace Work.FTS.StrongEps.EpsRLX

noncomputable section
open scoped Real Topology
open MeasureTheory Set Filter

open Work.FTS.GalFields.RHS (P1 P2 P3 P4 P5 TOf kA1 kA2 kA3 kA4 kA5)

set_option autoImplicit false
set_option linter.unusedVariables false
set_option maxHeartbeats 1600000

/-- The `ℋ⁴`-honesty, size and smoothness of the pieces `P₁` -- `P₅` of the `N₀`-difference.

`hprod`/`hwprod` are the two product rules of the `ℋ⁴`-calculus (`prod_field`,
`wprod_field_winf`) at the (single) constant `Ci` dominating all the package constants. -/
theorem PiecesAClassC {α Ci : ℝ} {g g' h : ℝ → ℝ → ℝ}
    (hα : 0 < α) (hα1 : α ≤ 1) (hCi : 0 < Ci)
    (hprod : ∀ f g : Work.FTS.Galerkin.Fn, Work.FTS.VocabO.HQo α 4 f →
      Work.FTS.VocabO.HQo α 4 g →
      Work.Spaces.HkMem α 4 (fun z θ => f z θ * g z θ) ∧
      Work.FTS.Nonlin.Xn α (fun z θ => f z θ * g z θ)
        ≤ Ci * α ^ (-(1 / 2 : ℝ)) * Work.FTS.Nonlin.Xn α f * Work.FTS.Nonlin.Xn α g)
    (hwprod : ∀ f g : Work.FTS.Galerkin.Fn, Work.FTS.EllipticEst.SmoothOpen f →
      Work.Spaces.WlInfMem α 4 f → Work.FTS.VocabO.HQo α 4 g →
      Work.Spaces.HkMem α 4 (fun z θ => f z θ * g z θ) ∧
      Work.FTS.Nonlin.Xn α (fun z θ => f z θ * g z θ)
        ≤ Ci * α ^ (-(1 / 2 : ℝ)) * Work.Spaces.WlInf α 4 f * Work.FTS.Nonlin.Xn α g)
    (hgsm : Work.FTS.EllipticEst.SmoothOpen g)
    (hg'sm : Work.FTS.EllipticEst.SmoothOpen g')
    (hhsm : Work.FTS.EllipticEst.SmoothOpen h)
    (hg'mem : Work.Spaces.HkMem α 4 g')
    (hhmem : Work.Spaces.HkMem α 4 h)
    (hLgSm : Work.FTS.EllipticEst.SmoothOpen (fun z _ => Work.Construction.L12 g z))
    (hLhSm : Work.FTS.EllipticEst.SmoothOpen (fun z _ => Work.Construction.L12 h z))
    (hLgMem : Work.Spaces.HkMem α 4 (fun z θ => Work.Construction.L12 g z))
    (hLhMem : Work.Spaces.HkMem α 4 (fun z θ => Work.Construction.L12 h z))
    (hLgXn : Work.FTS.Nonlin.Xn α (fun z θ => Work.Construction.L12 g z)
      ≤ Ci * Work.FTS.Nonlin.Xn α g)
    (hLhXn : Work.FTS.Nonlin.Xn α (fun z θ => Work.Construction.L12 h z)
      ≤ Ci * Work.FTS.GalFields.Xn5 α h)
    (hXg5 : Work.FTS.Nonlin.Xn α g ≤ Work.FTS.GalFields.Xn5 α g)
    (hXh5 : Work.FTS.Nonlin.Xn α h ≤ Work.FTS.GalFields.Xn5 α h)
    (hXg'5 : Work.FTS.Nonlin.Xn α g' ≤ Work.FTS.GalFields.Xn5 α g')
    (hDthhSm : Work.FTS.EllipticEst.SmoothOpen (Work.Spaces.Dth h))
    (hDthhMem : Work.Spaces.HkMem α 4 (Work.Spaces.Dth h))
    (hDthhXn : Work.FTS.Nonlin.Xn α (Work.Spaces.Dth h) ≤ Work.FTS.GalFields.Xn5 α h)
    (hDthg'Sm : Work.FTS.EllipticEst.SmoothOpen (Work.Spaces.Dth g'))
    (hDthg'Mem : Work.Spaces.HkMem α 4 (Work.Spaces.Dth g'))
    (hDthg'Xn : Work.FTS.Nonlin.Xn α (Work.Spaces.Dth g') ≤ Work.FTS.GalFields.Xn5 α g')
    (CF : ℝ) (hCF : 0 < CF)
    (hDthFstarSm : Work.FTS.EllipticEst.SmoothOpen
      (Work.Spaces.Dth (Work.Construction.Fstar α)))
    (hFstarW : Work.Spaces.WlInfMem α 4 (Work.Spaces.Dth (Work.Construction.Fstar α)) ∧
      Work.Spaces.WlInf α 4 (Work.Spaces.Dth (Work.Construction.Fstar α)) ≤ CF * α ^ 2)
    (hZh0 : 0 ≤ Work.FTS.GalFields.Xn5 α h) :
    (Work.Spaces.HkMem α 4 (Work.FTS.GalFields.RHS.P1 α g h) ∧
        Work.FTS.Nonlin.Xn α (Work.FTS.GalFields.RHS.P1 α g h)
          ≤ Work.FTS.GalFields.RHS.kA1 α Ci * Work.FTS.GalFields.RHS.TOf α g g' h)
      ∧ (Work.Spaces.HkMem α 4 (Work.FTS.GalFields.RHS.P2 α g' h) ∧
        Work.FTS.Nonlin.Xn α (Work.FTS.GalFields.RHS.P2 α g' h)
          ≤ Work.FTS.GalFields.RHS.kA2 α Ci * Work.FTS.GalFields.RHS.TOf α g g' h)
      ∧ (Work.Spaces.HkMem α 4 (Work.FTS.GalFields.RHS.P3 α h) ∧
        Work.FTS.Nonlin.Xn α (Work.FTS.GalFields.RHS.P3 α h)
          ≤ Work.FTS.GalFields.RHS.kA3 α Ci CF * Work.FTS.GalFields.RHS.TOf α g g' h)
      ∧ (Work.Spaces.HkMem α 4 (Work.FTS.GalFields.RHS.P4 α g h) ∧
        Work.FTS.Nonlin.Xn α (Work.FTS.GalFields.RHS.P4 α g h)
          ≤ Work.FTS.GalFields.RHS.kA4 α Ci * Work.FTS.GalFields.RHS.TOf α g g' h)
      ∧ (Work.Spaces.HkMem α 4 (Work.FTS.GalFields.RHS.P5 α g' h) ∧
        Work.FTS.Nonlin.Xn α (Work.FTS.GalFields.RHS.P5 α g' h)
          ≤ Work.FTS.GalFields.RHS.kA5 α Ci * Work.FTS.GalFields.RHS.TOf α g g' h)
      ∧ Work.FTS.EllipticEst.SmoothOpen (Work.FTS.GalFields.RHS.P1 α g h)
      ∧ Work.FTS.EllipticEst.SmoothOpen (Work.FTS.GalFields.RHS.P2 α g' h)
      ∧ Work.FTS.EllipticEst.SmoothOpen (Work.FTS.GalFields.RHS.P3 α h)
      ∧ Work.FTS.EllipticEst.SmoothOpen (Work.FTS.GalFields.RHS.P4 α g h)
      ∧ Work.FTS.EllipticEst.SmoothOpen (Work.FTS.GalFields.RHS.P5 α g' h) := by
  have h0g : (0 : ℝ) ≤ Work.FTS.GalFields.Xn5 α g := Work.Spaces.HkNorm_nonneg α 5 g
  have h0g' : (0 : ℝ) ≤ Work.FTS.GalFields.Xn5 α g' := Work.Spaces.HkNorm_nonneg α 5 g'
  -- ## the five pieces: smoothness, honesty, size
  have hs1 : Work.FTS.EllipticEst.SmoothOpen (P1 α g h) := by
    unfold P1
    exact Work.FTS.NonlinRows.smoothOpen_const_mul (1 / α)
      (Work.FTS.NonlinRows.smoothOpen_mul hLgSm hhsm)
  have h1 : Work.Spaces.HkMem α 4 (P1 α g h) ∧
      Work.FTS.Nonlin.Xn α (P1 α g h) ≤ kA1 α Ci * TOf α g g' h := by
    have hp := hprod (fun z θ => Work.Construction.L12 g z) h
      ⟨hLgSm, hLgMem⟩ ⟨hhsm, hhmem⟩
    refine ⟨?_, ?_⟩
    · unfold P1
      exact Work.FTS.LocData.HkMem_const_mul α 4 (1 / α) hp.1
    · unfold P1
      rw [Work.FTS.Nonlinear.Pieces.RowsN0Aux.Xn_const_mul,
        abs_of_nonneg (by positivity : (0 : ℝ) ≤ 1 / α)]
      have hstep : (1 / α) * Work.FTS.Nonlin.Xn α
            (fun z θ => Work.Construction.L12 g z * h z θ)
          ≤ kA1 α Ci * (Work.FTS.Nonlin.Xn α g * Work.FTS.GalFields.Xn5 α h) := by
        rw [kA1]
        calc (1 / α) * Work.FTS.Nonlin.Xn α (fun z θ => Work.Construction.L12 g z * h z θ)
            ≤ (1 / α) * (Ci * α ^ (-(1 / 2 : ℝ))
                * (Ci * Work.FTS.Nonlin.Xn α g) * Work.FTS.GalFields.Xn5 α h) := by
              refine mul_le_mul_of_nonneg_left ?_ (by positivity)
              have hA0 : (0 : ℝ) ≤ Ci * α ^ (-(1 / 2 : ℝ)) := by positivity
              refine le_trans hp.2 ?_
              calc Ci * α ^ (-(1 / 2 : ℝ))
                    * Work.FTS.Nonlin.Xn α (fun z θ => Work.Construction.L12 g z)
                    * Work.FTS.Nonlin.Xn α h
                  ≤ Ci * α ^ (-(1 / 2 : ℝ)) * (Ci * Work.FTS.Nonlin.Xn α g)
                    * Work.FTS.Nonlin.Xn α h :=
                    mul_le_mul (mul_le_mul_of_nonneg_left hLgXn hA0) (le_refl _)
                      (Work.Spaces.HkNorm_nonneg α 4 h)
                      (mul_nonneg hA0 (mul_nonneg (le_of_lt hCi)
                        (Work.Spaces.HkNorm_nonneg α 4 g)))
                _ ≤ Ci * α ^ (-(1 / 2 : ℝ)) * (Ci * Work.FTS.Nonlin.Xn α g)
                    * Work.FTS.GalFields.Xn5 α h :=
                    mul_le_mul_of_nonneg_left hXh5
                      (mul_nonneg hA0 (mul_nonneg (le_of_lt hCi)
                        (Work.Spaces.HkNorm_nonneg α 4 g)))
            _ = (1 / α) * Ci * α ^ (-(1 / 2 : ℝ)) * Ci
                * (Work.FTS.Nonlin.Xn α g * Work.FTS.GalFields.Xn5 α h) := by ring
      refine le_trans hstep ?_
      rw [TOf]
      refine mul_le_mul_of_nonneg_left ?_
        (le_of_lt (show (0 : ℝ) < kA1 α Ci by rw [kA1]; positivity))
      have h1' : Work.FTS.Nonlin.Xn α g ≤ 1 + Work.FTS.GalFields.Xn5 α g
          + Work.FTS.GalFields.Xn5 α g' := by linarith
      nlinarith [mul_le_mul_of_nonneg_right h1' hZh0]
  have hs2 : Work.FTS.EllipticEst.SmoothOpen (P2 α g' h) := by
    unfold P2
    exact Work.FTS.NonlinRows.smoothOpen_const_mul (1 / α)
      (Work.FTS.NonlinRows.smoothOpen_mul hLhSm hg'sm)
  have h2 : Work.Spaces.HkMem α 4 (P2 α g' h) ∧
      Work.FTS.Nonlin.Xn α (P2 α g' h) ≤ kA2 α Ci * TOf α g g' h := by
    have hp := hprod (fun z θ => Work.Construction.L12 h z) g'
      ⟨hLhSm, hLhMem⟩ ⟨hg'sm, hg'mem⟩
    refine ⟨?_, ?_⟩
    · unfold P2
      exact Work.FTS.LocData.HkMem_const_mul α 4 (1 / α) hp.1
    · unfold P2
      rw [Work.FTS.Nonlinear.Pieces.RowsN0Aux.Xn_const_mul,
        abs_of_nonneg (by positivity : (0 : ℝ) ≤ 1 / α)]
      have hstep : (1 / α) * Work.FTS.Nonlin.Xn α
            (fun z θ => Work.Construction.L12 h z * g' z θ)
          ≤ kA2 α Ci * (Work.FTS.GalFields.Xn5 α h * Work.FTS.GalFields.Xn5 α g') := by
        rw [kA2]
        calc (1 / α) * Work.FTS.Nonlin.Xn α (fun z θ => Work.Construction.L12 h z * g' z θ)
            ≤ (1 / α) * (Ci * α ^ (-(1 / 2 : ℝ))
                * (Ci * Work.FTS.GalFields.Xn5 α h) * Work.FTS.GalFields.Xn5 α g') := by
              refine mul_le_mul_of_nonneg_left ?_ (by positivity)
              have hA0 : (0 : ℝ) ≤ Ci * α ^ (-(1 / 2 : ℝ)) := by positivity
              refine le_trans hp.2 ?_
              calc Ci * α ^ (-(1 / 2 : ℝ))
                    * Work.FTS.Nonlin.Xn α (fun z θ => Work.Construction.L12 h z)
                    * Work.FTS.Nonlin.Xn α g'
                  ≤ Ci * α ^ (-(1 / 2 : ℝ)) * (Ci * Work.FTS.GalFields.Xn5 α h)
                    * Work.FTS.Nonlin.Xn α g' :=
                    mul_le_mul (mul_le_mul_of_nonneg_left hLhXn hA0) (le_refl _)
                      (Work.Spaces.HkNorm_nonneg α 4 g') (mul_nonneg hA0 (by positivity))
                _ ≤ Ci * α ^ (-(1 / 2 : ℝ)) * (Ci * Work.FTS.GalFields.Xn5 α h)
                    * Work.FTS.GalFields.Xn5 α g' :=
                    mul_le_mul_of_nonneg_left hXg'5 (mul_nonneg hA0 (by positivity))
            _ = (1 / α) * Ci * α ^ (-(1 / 2 : ℝ)) * Ci
                * (Work.FTS.GalFields.Xn5 α h * Work.FTS.GalFields.Xn5 α g') := by ring
      refine le_trans hstep ?_
      rw [TOf]
      refine mul_le_mul_of_nonneg_left ?_
        (le_of_lt (show (0 : ℝ) < kA2 α Ci by rw [kA2]; positivity))
      have h1' : Work.FTS.GalFields.Xn5 α g' ≤ 1 + Work.FTS.GalFields.Xn5 α g
          + Work.FTS.GalFields.Xn5 α g' := by linarith
      nlinarith [mul_le_mul_of_nonneg_left h1' hZh0]
  have hs3 : Work.FTS.EllipticEst.SmoothOpen (P3 α h) := by
    unfold P3
    exact Work.FTS.NonlinRows.smoothOpen_const_mul (3 / (2 * α))
      (Work.FTS.NonlinRows.smoothOpen_mul hDthFstarSm hLhSm)
  have h3 : Work.Spaces.HkMem α 4 (P3 α h) ∧
      Work.FTS.Nonlin.Xn α (P3 α h) ≤ kA3 α Ci CF * TOf α g g' h := by
    have hw := hwprod (Work.Spaces.Dth (Work.Construction.Fstar α))
      (fun z θ => Work.Construction.L12 h z) hDthFstarSm (hFstarW).1
      ⟨hLhSm, hLhMem⟩
    refine ⟨?_, ?_⟩
    · unfold P3
      exact Work.FTS.LocData.HkMem_const_mul α 4 (3 / (2 * α)) hw.1
    · unfold P3
      rw [Work.FTS.Nonlinear.Pieces.RowsN0Aux.Xn_const_mul,
        abs_of_nonneg (by positivity : (0 : ℝ) ≤ 3 / (2 * α))]
      have hstep : (3 / (2 * α)) * Work.FTS.Nonlin.Xn α
            (fun z θ => Work.Spaces.Dth (Work.Construction.Fstar α) z θ
              * Work.Construction.L12 h z)
          ≤ kA3 α Ci CF * Work.FTS.GalFields.Xn5 α h := by
        rw [kA3]
        calc (3 / (2 * α)) * Work.FTS.Nonlin.Xn α
              (fun z θ => Work.Spaces.Dth (Work.Construction.Fstar α) z θ
                * Work.Construction.L12 h z)
            ≤ (3 / (2 * α)) * (Ci * α ^ (-(1 / 2 : ℝ)) * (CF * α ^ 2)
                * (Ci * Work.FTS.GalFields.Xn5 α h)) := by
              refine mul_le_mul_of_nonneg_left ?_ (by positivity)
              have hA0 : (0 : ℝ) ≤ Ci * α ^ (-(1 / 2 : ℝ)) := by positivity
              refine le_trans hw.2 ?_
              calc Ci * α ^ (-(1 / 2 : ℝ))
                    * Work.Spaces.WlInf α 4 (Work.Spaces.Dth (Work.Construction.Fstar α))
                    * Work.FTS.Nonlin.Xn α (fun z θ => Work.Construction.L12 h z)
                  ≤ Ci * α ^ (-(1 / 2 : ℝ)) * (CF * α ^ 2)
                    * Work.FTS.Nonlin.Xn α (fun z θ => Work.Construction.L12 h z) :=
                    mul_le_mul (mul_le_mul_of_nonneg_left (hFstarW).2 hA0) (le_refl _)
                      (Work.Spaces.HkNorm_nonneg α 4 (fun z θ => Work.Construction.L12 h z))
                      (mul_nonneg hA0 (by positivity))
                _ ≤ Ci * α ^ (-(1 / 2 : ℝ)) * (CF * α ^ 2)
                    * (Ci * Work.FTS.GalFields.Xn5 α h) :=
                    mul_le_mul_of_nonneg_left hLhXn (mul_nonneg hA0 (by positivity))
            _ = (3 / (2 * α)) * (Ci * α ^ (-(1 / 2 : ℝ)) * (CF * α ^ 2) * Ci)
                * Work.FTS.GalFields.Xn5 α h := by ring
      refine le_trans hstep ?_
      rw [TOf]
      refine mul_le_mul_of_nonneg_left ?_
        (le_of_lt (show (0 : ℝ) < kA3 α Ci CF by rw [kA3]; positivity))
      have h1' : (1 : ℝ) ≤ 1 + Work.FTS.GalFields.Xn5 α g
          + Work.FTS.GalFields.Xn5 α g' := by linarith
      simpa using mul_le_mul_of_nonneg_right h1' hZh0
  have hs4 : Work.FTS.EllipticEst.SmoothOpen (P4 α g h) := by
    unfold P4
    exact Work.FTS.NonlinRows.smoothOpen_const_mul (3 / (2 * α))
      (Work.FTS.NonlinRows.smoothOpen_mul hLgSm hDthhSm)
  have h4 : Work.Spaces.HkMem α 4 (P4 α g h) ∧
      Work.FTS.Nonlin.Xn α (P4 α g h) ≤ kA4 α Ci * TOf α g g' h := by
    have hp := hprod (fun z θ => Work.Construction.L12 g z) (Work.Spaces.Dth h)
      ⟨hLgSm, hLgMem⟩ ⟨hDthhSm, hDthhMem⟩
    refine ⟨?_, ?_⟩
    · unfold P4
      exact Work.FTS.LocData.HkMem_const_mul α 4 (3 / (2 * α)) hp.1
    · unfold P4
      rw [Work.FTS.Nonlinear.Pieces.RowsN0Aux.Xn_const_mul,
        abs_of_nonneg (by positivity : (0 : ℝ) ≤ 3 / (2 * α))]
      have hstep : (3 / (2 * α)) * Work.FTS.Nonlin.Xn α
            (fun z θ => Work.Construction.L12 g z * Work.Spaces.Dth h z θ)
          ≤ kA4 α Ci * (Work.FTS.Nonlin.Xn α g * Work.FTS.GalFields.Xn5 α h) := by
        rw [kA4]
        calc (3 / (2 * α)) * Work.FTS.Nonlin.Xn α
              (fun z θ => Work.Construction.L12 g z * Work.Spaces.Dth h z θ)
            ≤ (3 / (2 * α)) * (Ci * α ^ (-(1 / 2 : ℝ))
                * (Ci * Work.FTS.Nonlin.Xn α g) * Work.FTS.GalFields.Xn5 α h) := by
              refine mul_le_mul_of_nonneg_left ?_ (by positivity)
              have hA0 : (0 : ℝ) ≤ Ci * α ^ (-(1 / 2 : ℝ)) := by positivity
              refine le_trans hp.2 ?_
              calc Ci * α ^ (-(1 / 2 : ℝ))
                    * Work.FTS.Nonlin.Xn α (fun z θ => Work.Construction.L12 g z)
                    * Work.FTS.Nonlin.Xn α (Work.Spaces.Dth h)
                  ≤ Ci * α ^ (-(1 / 2 : ℝ)) * (Ci * Work.FTS.Nonlin.Xn α g)
                    * Work.FTS.Nonlin.Xn α (Work.Spaces.Dth h) :=
                    mul_le_mul (mul_le_mul_of_nonneg_left hLgXn hA0) (le_refl _)
                      (Work.Spaces.HkNorm_nonneg α 4 (Work.Spaces.Dth h))
                      (mul_nonneg hA0 (mul_nonneg (le_of_lt hCi)
                        (Work.Spaces.HkNorm_nonneg α 4 g)))
                _ ≤ Ci * α ^ (-(1 / 2 : ℝ)) * (Ci * Work.FTS.Nonlin.Xn α g)
                    * Work.FTS.GalFields.Xn5 α h :=
                    mul_le_mul_of_nonneg_left hDthhXn
                      (mul_nonneg hA0 (mul_nonneg (le_of_lt hCi)
                        (Work.Spaces.HkNorm_nonneg α 4 g)))
            _ = (3 / (2 * α)) * (Ci * α ^ (-(1 / 2 : ℝ)) * Ci)
                * (Work.FTS.Nonlin.Xn α g * Work.FTS.GalFields.Xn5 α h) := by ring
      refine le_trans hstep ?_
      rw [TOf]
      refine mul_le_mul_of_nonneg_left ?_
        (le_of_lt (show (0 : ℝ) < kA4 α Ci by rw [kA4]; positivity))
      have h1' : Work.FTS.Nonlin.Xn α g ≤ 1 + Work.FTS.GalFields.Xn5 α g
          + Work.FTS.GalFields.Xn5 α g' := by linarith
      nlinarith [mul_le_mul_of_nonneg_right h1' hZh0]
  have hs5 : Work.FTS.EllipticEst.SmoothOpen (P5 α g' h) := by
    unfold P5
    exact Work.FTS.NonlinRows.smoothOpen_const_mul (3 / (2 * α))
      (Work.FTS.NonlinRows.smoothOpen_mul hLhSm hDthg'Sm)
  have h5 : Work.Spaces.HkMem α 4 (P5 α g' h) ∧
      Work.FTS.Nonlin.Xn α (P5 α g' h) ≤ kA5 α Ci * TOf α g g' h := by
    have hp := hprod (fun z θ => Work.Construction.L12 h z) (Work.Spaces.Dth g')
      ⟨hLhSm, hLhMem⟩ ⟨hDthg'Sm, hDthg'Mem⟩
    refine ⟨?_, ?_⟩
    · unfold P5
      exact Work.FTS.LocData.HkMem_const_mul α 4 (3 / (2 * α)) hp.1
    · unfold P5
      rw [Work.FTS.Nonlinear.Pieces.RowsN0Aux.Xn_const_mul,
        abs_of_nonneg (by positivity : (0 : ℝ) ≤ 3 / (2 * α))]
      have hstep : (3 / (2 * α)) * Work.FTS.Nonlin.Xn α
            (fun z θ => Work.Construction.L12 h z * Work.Spaces.Dth g' z θ)
          ≤ kA5 α Ci * (Work.FTS.GalFields.Xn5 α h * Work.FTS.GalFields.Xn5 α g') := by
        rw [kA5]
        calc (3 / (2 * α)) * Work.FTS.Nonlin.Xn α
              (fun z θ => Work.Construction.L12 h z * Work.Spaces.Dth g' z θ)
            ≤ (3 / (2 * α)) * (Ci * α ^ (-(1 / 2 : ℝ))
                * (Ci * Work.FTS.GalFields.Xn5 α h) * Work.FTS.GalFields.Xn5 α g') := by
              refine mul_le_mul_of_nonneg_left ?_ (by positivity)
              have hA0 : (0 : ℝ) ≤ Ci * α ^ (-(1 / 2 : ℝ)) := by positivity
              refine le_trans hp.2 ?_
              calc Ci * α ^ (-(1 / 2 : ℝ))
                    * Work.FTS.Nonlin.Xn α (fun z θ => Work.Construction.L12 h z)
                    * Work.FTS.Nonlin.Xn α (Work.Spaces.Dth g')
                  ≤ Ci * α ^ (-(1 / 2 : ℝ)) * (Ci * Work.FTS.GalFields.Xn5 α h)
                    * Work.FTS.Nonlin.Xn α (Work.Spaces.Dth g') :=
                    mul_le_mul (mul_le_mul_of_nonneg_left hLhXn hA0) (le_refl _)
                      (Work.Spaces.HkNorm_nonneg α 4 (Work.Spaces.Dth g'))
                      (mul_nonneg hA0 (by positivity))
                _ ≤ Ci * α ^ (-(1 / 2 : ℝ)) * (Ci * Work.FTS.GalFields.Xn5 α h)
                    * Work.FTS.GalFields.Xn5 α g' :=
                    mul_le_mul_of_nonneg_left hDthg'Xn (mul_nonneg hA0 (by positivity))
            _ = (3 / (2 * α)) * (Ci * α ^ (-(1 / 2 : ℝ)) * Ci)
                * (Work.FTS.GalFields.Xn5 α h * Work.FTS.GalFields.Xn5 α g') := by ring
      refine le_trans hstep ?_
      rw [TOf]
      refine mul_le_mul_of_nonneg_left ?_
        (le_of_lt (show (0 : ℝ) < kA5 α Ci by rw [kA5]; positivity))
      have h1' : Work.FTS.GalFields.Xn5 α g' ≤ 1 + Work.FTS.GalFields.Xn5 α g
          + Work.FTS.GalFields.Xn5 α g' := by linarith
      nlinarith [mul_le_mul_of_nonneg_left h1' hZh0]
  exact ⟨h1, h2, h3, h4, h5, hs1, hs2, hs3, hs4, hs5⟩

end

end Work.FTS.StrongEps.EpsRLX
