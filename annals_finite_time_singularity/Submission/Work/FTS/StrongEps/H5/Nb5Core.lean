/-
# `H5/Nb5Core` — the level-`5` `N`-block from the atomic packages

The transfer half of the level-`5` `N`-block: the twenty pieces `NBlk α w Φs Φg k` are priced by
`H5.Nb5Pieces`, they agree with `N α (Ftot α w) (Φs+Φg)` on the open quadrant (`Rl1.splitOpen`,
via the additivity of `L₁₂` and of the angular moment `FK` over `F_* + w`), and
`HkSumOpenClosure5` then transfers the membership and the norm bound to `N` itself — exactly the
level-four structure of `ClassCRHS.HkMemXnN` on top of `nb_data`.

The atomic packages `HAtoms5Pkg`, `WStar5Pkg`, `WFixed5Pkg`, `HFixed5Pkg` and the slot bound
`SinSqSlot5Pkg` are defined in `H5.Nb5Pkgs`.
-/
import Mathlib.Algebra.Order.Ring.Star
import Mathlib.Analysis.Calculus.FDeriv.Defs
import Mathlib.Analysis.SpecialFunctions.Trigonometric.Basic
import Submission.Work.FTS.StrongEps.H5.Nb5Pkgs
import Submission.Work.FTS.StrongEps.H5.Nb5Pieces
import Submission.Work.FTS.StrongEps.H5.HkSum5
import Submission.Work.FTS.StrongEps.ClassCRHS.HkMemXnNDefs
import Submission.Work.FTS.StrongEps.ClassCRHS.HkMemXnNIdent
import Submission.Work.FTS.StrongEps.ClassCRHS.SmoothOpenRHS
import Submission.Work.FTS.NonlinRows.Rl1.splitOpen
import Submission.Work.FTS.StrongEps.EComparison.EllPkgClsVop
import Submission.Work.FTS.StrongPersist.H6Rows.NZaux.L12AddFstar
import Submission.Work.FTS.StrongPersist.Star6

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

noncomputable section

open scoped Real Topology
open MeasureTheory Set Filter

namespace Work.FTS.StrongEps.H5

open Work.FTS.Galerkin (Fn)

set_option autoImplicit false
set_option maxHeartbeats 1600000
set_option linter.unusedVariables false

/-- **The level-`5` `N`-block data from the atomic packages** (the analogue of
`ClassCRHS.nb_data`): smoothness, `ℋ⁵`-membership and a uniform level-`5` norm bound of each of
the twenty pieces, together with their agreement with `N` on the open quadrant. -/
theorem Nb5_data
    (hH : HAtoms5Pkg) (hWs : WStar5Pkg) (hWf : WFixed5Pkg) (hHf : HFixed5Pkg)
    (hsin5 : SinSqSlot5Pkg)
    (hsmB : ∀ {α : ℝ}, α ∈ Set.Ioc 0 1 → ∀ {Ce Cs6 : ℝ} {Φs w Φg : Fn},
      Work.FTS.ClassC.ClassC α w → Work.FTS.ClassC.EllPkgK α 6 Ce w Φg →
      Work.FTS.StrongPersist.StarPkg6 α Cs6 Φs →
      ∀ k ∈ Finset.range 20,
        Work.FTS.EllipticEst.SmoothOpen (Work.FTS.StrongEps.ClassCRHS.NBlk α w Φs Φg k)) :
    ∀ {α : ℝ}, α ∈ Set.Ioc 0 1 → ∀ {C₀ B Ce Cs6 : ℝ} {Φs : Fn},
      ∃ Kbig : ℝ, 0 < Kbig ∧ ∀ {w Φg : Fn},
        Work.FTS.ClassC.ClassC α w → Work.FTS.Nonlin.Xn α w ≤ C₀ * α ^ 2 →
        Work.Spaces.HkNorm α 6 w ≤ B →
        Work.FTS.ClassC.EllPkgK α 6 Ce w Φg →
        Work.FTS.StrongPersist.StarPkg6 α Cs6 Φs →
        (∀ k ∈ Finset.range 20,
          Work.FTS.EllipticEst.SmoothOpen (Work.FTS.StrongEps.ClassCRHS.NBlk α w Φs Φg k)) ∧
        (∀ k ∈ Finset.range 20,
          Work.Spaces.HkMem α 5 (Work.FTS.StrongEps.ClassCRHS.NBlk α w Φs Φg k) ∧
          Work.Spaces.HkNorm α 5 (Work.FTS.StrongEps.ClassCRHS.NBlk α w Φs Φg k) ≤ Kbig) ∧
        (∀ z θ : ℝ, (z, θ) ∈ Work.Construction.Qd →
          Work.Construction.N α (Work.Construction.Ftot α w) (fun z θ => Φs z θ + Φg z θ) z θ
            = ∑ k ∈ Finset.range 20,
                Work.FTS.StrongEps.ClassCRHS.NBlk α w Φs Φg k z θ) := by
  intro α hαI C₀ B Ce Cs6 Φs
  have hα0 : 0 < α := hαI.1
  obtain ⟨Kbig, hKbig, hpieces⟩ := Nb5_pieces hH hWs hWf hHf hsin5 hαI
    (C₀ := C₀) (B := B) (Ce := Ce) (Cs6 := Cs6) (Φs := Φs)
  refine ⟨Kbig, hKbig, ?_⟩
  intro w Φg hw hXw hX6 hell hstar
  -- ## the split of `N` into the twenty pieces
  have hmem4w : Work.Spaces.HkMem α 4 w :=
    Work.FTS.OpenPkg.HkMem_mono_open hw.reg 4 (by norm_num) hw.mem
  have hLadd : ∀ z : ℝ, 0 < z →
      Work.Construction.L12 (Work.Construction.Ftot α w) z
        = Work.Construction.L12 (Work.Construction.Fstar α) z + Work.Construction.L12 w z :=
    fun z hz => Work.FTS.StrongPersist.H6Rows.NZaux.L12AddFstar hα0 hαI.2 hw.reg hmem4w z hz
  have hFKadd : ∀ z : ℝ, 0 < z →
      Work.Construction.FK (Work.Construction.Ftot α w) z
        = Work.Construction.FK (Work.Construction.Fstar α) z + Work.Construction.FK w z :=
    fun z hz => Work.FTS.GalFields.RHS.FK_add_of_slices
      (a := Work.Construction.Fstar α) (b := w) (ne_of_gt hz)
      (Work.Stability.integrableOn_slice_Fstar α hα0 z)
      (Work.FTS.GalBasis.cc.integrableOn_slice_of_SmoothOpen_HkMem hw.reg hmem4w hz)
  have hL12d : ∀ z : ℝ, 0 < z →
      DifferentiableAt ℝ (fun z' => Work.Construction.L12 w z') z :=
    fun z hz => Work.FTS.StrongEps.EComparison.differentiableAt_L12_of_Vop (ne_of_gt hα0)
      (F := w) (Ψ := Φg) hell.smooth hell.V.1.1 hz
  have hsplit := Work.FTS.NonlinRows.Rl1.splitOpen (α := α) (g := w) (Φs := Φs) (Φg := Φg)
    hα0 hαI.2 hw.reg hstar.smooth hell.smooth hLadd hFKadd hL12d
  refine ⟨hsmB hαI hw hell hstar, hpieces hw hXw hX6 hell hstar, ?_⟩
  intro z θ hzθ
  obtain ⟨hz, hθ0, hθ1⟩ := hzθ
  rw [hsplit z θ ⟨hz, hθ0, hθ1⟩, ← Work.FTS.StrongEps.ClassCRHS.PB_sum_eq α w Φs Φg z θ]
  exact Finset.sum_congr rfl (fun k hk =>
    Work.FTS.StrongEps.ClassCRHS.PB_eq_NBlk hα0 hαI.2 w Φs Φg k hk z θ hz hθ0 hθ1)

/-- **The level-`5` `N`-block from the atomic packages** — the level-`5` analogue of
`ClassCRHS.HkMemXnN`. -/
theorem HkMemXnN5_of_atoms
    (hH : HAtoms5Pkg) (hWs : WStar5Pkg) (hWf : WFixed5Pkg) (hHf : HFixed5Pkg)
    (hsin5 : SinSqSlot5Pkg)
    (hsmB : ∀ {α : ℝ}, α ∈ Set.Ioc 0 1 → ∀ {Ce Cs6 : ℝ} {Φs w Φg : Fn},
      Work.FTS.ClassC.ClassC α w → Work.FTS.ClassC.EllPkgK α 6 Ce w Φg →
      Work.FTS.StrongPersist.StarPkg6 α Cs6 Φs →
      ∀ k ∈ Finset.range 20,
        Work.FTS.EllipticEst.SmoothOpen (Work.FTS.StrongEps.ClassCRHS.NBlk α w Φs Φg k))
    (hsmN : ∀ {α : ℝ}, α ∈ Set.Ioc 0 1 → ∀ {Ce Cs6 : ℝ} {Φs w Φg : Fn},
      Work.FTS.ClassC.ClassC α w → Work.FTS.ClassC.EllPkgK α 6 Ce w Φg →
      Work.FTS.StrongPersist.StarPkg6 α Cs6 Φs →
      Work.FTS.EllipticEst.SmoothOpen (Work.Construction.N α (Work.Construction.Ftot α w)
        (fun z θ => Φs z θ + Φg z θ))) :
    ∀ {α : ℝ}, α ∈ Set.Ioc 0 1 → ∀ {C₀ B Ce Cs6 : ℝ} {Φs : Fn},
      ∃ K : ℝ, 0 < K ∧ ∀ {w Φg : Fn},
        Work.FTS.ClassC.ClassC α w → Work.FTS.Nonlin.Xn α w ≤ C₀ * α ^ 2 →
        Work.Spaces.HkNorm α 6 w ≤ B →
        Work.FTS.ClassC.EllPkgK α 6 Ce w Φg →
        Work.FTS.StrongPersist.StarPkg6 α Cs6 Φs →
        Work.Spaces.HkMem α 5 (Work.Construction.N α (Work.Construction.Ftot α w)
          (fun z θ => Φs z θ + Φg z θ)) ∧
        Work.Spaces.HkNorm α 5 (Work.Construction.N α (Work.Construction.Ftot α w)
          (fun z θ => Φs z θ + Φg z θ)) ≤ K := by
  intro α hαI C₀ B Ce Cs6 Φs
  have hα0 : 0 < α := hαI.1
  obtain ⟨Kbig, hKbig, hdata⟩ := Nb5_data hH hWs hWf hHf hsin5 hsmB hαI (C₀ := C₀) (B := B)
    (Ce := Ce) (Cs6 := Cs6) (Φs := Φs)
  refine ⟨Kbig * (2 ^ 20 * 20) + 1, by positivity, ?_⟩
  intro w Φg hw hXw hX6 hell hstar
  obtain ⟨hsm, hpm, hid⟩ := hdata hw hXw hX6 hell hstar
  have hcont : ContinuousOn (fun p : ℝ × ℝ => Work.Spaces.HkIntegrand α 5
      (Work.Construction.N α (Work.Construction.Ftot α w) (fun z θ => Φs z θ + Φg z θ))
      p.1 p.2) (Set.Ioi 0 ×ˢ Set.Ioo 0 (Real.pi / 2)) :=
    Work.FTS.EllipticEst.SmoothOpen.continuousOn_HkIntegrand
      (hsmN hαI hw hell hstar) α 5
  obtain ⟨hmem, hbnd⟩ := HkSumOpenClosure5 (α := α) hα0 hcont hsm
    (fun k hk => (hpm k hk).1) (fun z θ hz h1 h2 => hid z θ ⟨hz, h1, h2⟩)
  refine ⟨hmem, ?_⟩
  refine le_trans hbnd ?_
  have h1 : Real.sqrt ((2 : ℝ) ^ 20) = 1024 := by
    rw [show (2 : ℝ) ^ 20 = 1024 ^ 2 by norm_num, Real.sqrt_sq (by norm_num)]
  have h2 : ∑ k ∈ Finset.range 20, Work.Spaces.HkNorm α 5
      (Work.FTS.StrongEps.ClassCRHS.NBlk α w Φs Φg k) ≤ 20 * Kbig := by
    refine le_trans (Finset.sum_le_sum (fun k hk => (hpm k hk).2)) ?_
    rw [Finset.sum_const, Finset.card_range, nsmul_eq_mul]
    norm_num
  calc Real.sqrt ((2 : ℝ) ^ 20)
        * ∑ k ∈ Finset.range 20, Work.Spaces.HkNorm α 5
            (Work.FTS.StrongEps.ClassCRHS.NBlk α w Φs Φg k)
      ≤ 1024 * (20 * Kbig) := by
        rw [h1]
        exact mul_le_mul_of_nonneg_left h2 (by norm_num)
    _ ≤ Kbig * (2 ^ 20 * 20) + 1 := by nlinarith [hKbig]

end Work.FTS.StrongEps.H5
