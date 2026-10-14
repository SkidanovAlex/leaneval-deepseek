import Mathlib.Algebra.Order.Ring.Star
import Mathlib.Analysis.Calculus.ContDiff.Defs
import Mathlib.Analysis.InnerProductSpace.Basic
import Mathlib.Analysis.LocallyConvex.AbsConvexOpen
import Mathlib.Analysis.SpecialFunctions.Pow.Real
import Mathlib.MeasureTheory.Function.StronglyMeasurable.AEStronglyMeasurable
import Mathlib.MeasureTheory.Integral.IntervalIntegral.Basic
import Mathlib.MeasureTheory.Measure.Haar.OfBasis
import Mathlib.Topology.Algebra.Module.ModuleTopology
import Submission.Work.FTS.ClassC.RopGen.sliceSecNonposBochner
import Submission.Work.FTS.EllExist.LevelK
import Submission.Work.FTS.EllSol.ClassC
import Submission.Work.FTS.EllSol.EllPkgAux.Slots
import Submission.Work.FTS.EllSol.EllPkgAux.VRSlots
import Submission.Work.FTS.EllSol.ellPkgK6_of_classC
import Submission.Work.FTS.EpsEngine.LocalStepXBall
import Submission.Work.FTS.StrongEps.E5G.Defs
import Submission.Work.FTS.StrongEps.EpsE4Thr.Leaves.FlowBits.hkSqFepsSub_le
import Submission.Work.FTS.StrongEps.EpsHbdd
import Submission.Work.FTS.StrongEps.EpsSqTools.LinAux.LinPartAux
import Submission.Work.FTS.StrongEps.L12Sub4.L12ZeroLog
import Submission.Work.FTS.StrongEps.epsWP_hkMem4_bnd_fam
import Submission.Work.FTS.StrongEps.smoothOpen_epsWP
import Submission.Work.FTS.StrongPersist.H6Rows.N0pair6bWork.HkMem_mul_of_WlInf6_cd6
import Submission.Work.FTS.StrongPersist.H6Rows.Npair6SupAux.radialSupMul_cd6
import Submission.Work.FTS_EllLimOK.ProducerH.BoxAux.th2EgMid
import Submission.Work.FTS_LocDatum3a.Assembly
import Submission.Work.FTS_RegExport.RXB.l12_aux
import Submission.Work.FTS_RegExport.RXVP.NoHdat.velPkgEasy_noHdat
import Submission.Work.FTS_RegExport.Vz7Eslot
import Submission.Work.FTS_RegExport.r1Block.regExport_hVop
-- ===== merged: Submission.Work.FTS.EllSol.ellPkgConj_of_classOk =====
section

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

/-
# `Work.FTS.EllSol.ellPkgConj_of_classOk` — the two elliptic packages at one constant

The statement conjoins the level-`4` package `VocabO.EllPkgGo` (the `ℋ⁴`-package consumed by the
transport/coercivity chapter) and the level-`6` package `EllPkgK 6` (consumed by the level-six
persistence rows), at a *single* constant `Ce` and a *single* range `α ≤ α₀`.

## The assembly

* The level-`4` package over `EllClassOk 7` has exactly the content of
  `Work.FTS.EllSol.ellPkgGo_of_classOk`, namely
  `EllPkgAux.ellPkgGoOfClassOk_of` applied to the four level-`4` slots
  (`ropSlotLe4_cl`, `uopSlotLe4`, `vopSlotLe4_cl`, `vthSlotLe4`).
  It is re-assembled here because the workspace carries several *mutually exclusive* copies of
  shared theory (Lean refuses to import two modules declaring the same name, e.g.
  `Work.EllipticEst.Core.i0Aux.rho` or `Work.FTS.EllipticEst.AngAWeak.Yslice`), and the natural
  providers of the level-`4` and level-`6` packages happen to sit on opposite sides of those
  splits.  Every input is therefore taken from the same side as the level-`6` package
  `ellPkgK6_of_classC`:
  - the interpolation input `EllPkgAux.InterpOpenTraceStmt` (consumed by `uopSlotLe4`) is supplied
    through the verbatim bridge `ClassC.AlphaDzGen.openTraceStmt_of_openTrace` applied to
    `ClassC.RopGen.interpOpenTrace` (the `PkgK5.K5c` copy of the same paper-§7 estimate);
  - the `V^{th}` slot is proved here directly from
    `EllSol.ellVth_transferC_of_pieces_quarter` (in `ClassC/vthQuarter`, together with
    `VthAuxC.certC` and `EllSol.poinC_quarter`), *without* the sibling module
    `ClassC.vthTransfer_classC`, which would pull in the other copy of the level-`4` elliptic
    estimate.
* The level-`6` package is `ellPkgK6_of_classC` verbatim.
* Finally `EllClassOk` is monotone in the level (`8 → 7`, needed by the level-`4` slots) and both
  packages are monotone in their constant, so `Ce := max Ce₄ Ce₆` and `α₀ := min α₄ α₆` serve
  both.
-/

namespace Work.FTS.EllSol

open Work.FTS.Galerkin (Fn)

set_option autoImplicit false

/-! ## Monotonicity of the two packages in the constant

Both packages bound each slot norm by `Ce` times a *nonnegative* datum norm, so raising `Ce`
preserves them.  These are the only two structural facts the assembly needs. -/

/-- `EllPkgK` is monotone in the constant. -/
theorem EllPkgK_mono {α : ℝ} {k : ℕ} {Ce Ce' : ℝ} {g Φg : Fn}
    (h : EllPkgK α k Ce g Φg) (hle : Ce ≤ Ce') : EllPkgK α k Ce' g Φg := by
  obtain ⟨h1, h2, ⟨hRm, hRb⟩, ⟨hUm, hUb⟩, ⟨hVm, hVb⟩⟩ := h
  have hgnn : 0 ≤ Work.Spaces.HkNorm α k g := Work.Spaces.HkNorm_nonneg α k g
  have hmon : ∀ X : ℝ, X ≤ Ce * Work.Spaces.HkNorm α k g →
      X ≤ Ce' * Work.Spaces.HkNorm α k g :=
    fun X hX => le_trans hX (mul_le_mul_of_nonneg_right hle hgnn)
  exact ⟨h1, h2, ⟨hRm, hmon _ hRb⟩, ⟨hUm, hmon _ hUb⟩, ⟨hVm, hmon _ hVb⟩⟩

/-- `VocabO.EllPkgGo` is monotone in the constant (only `0 < α` is needed, to keep the
`α^{-1/2}`-factor nonnegative). -/
theorem EllPkgGo_mono {α Ce Ce' : ℝ} {g Φg : Fn} (hα : 0 < α)
    (h : Work.FTS.VocabO.EllPkgGo α Ce g Φg) (hle : Ce ≤ Ce') :
    Work.FTS.VocabO.EllPkgGo α Ce' g Φg := by
  obtain ⟨h1, h2, ⟨hRm, hRb⟩, ⟨hUm, hUb⟩, ⟨hVm, hVb⟩, hv, ⟨hTm, hTb⟩⟩ := h
  have hgnn : 0 ≤ Work.FTS.Nonlin.Xn α g := Work.Spaces.HkNorm_nonneg α 4 g
  have hαp : 0 ≤ α ^ (-(1 / 2 : ℝ)) := Real.rpow_nonneg hα.le _
  refine ⟨h1, h2, ⟨hRm, ?_⟩, ⟨hUm, ?_⟩, ⟨hVm, ?_⟩, hv, ⟨hTm, ?_⟩⟩
  · exact le_trans hRb (mul_le_mul_of_nonneg_right hle hgnn)
  · exact le_trans hUb (mul_le_mul_of_nonneg_right hle hgnn)
  · exact le_trans hVb (mul_le_mul_of_nonneg_right hle hgnn)
  · refine le_trans hTb ?_
    exact mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_right hle hαp) hgnn

/-- **`EllClassOk` is monotone in the level** (the instance `l = 7`, `K = 8` of
`PkgK5.EllWeakPos_descend`), stated here to keep the assembly self-contained. -/
theorem ellClassOk_eight_seven {α : ℝ} {g Ψ : Fn}
    (h : Work.FTS.EllExist.EllClassOk 8 α g Ψ) :
    Work.FTS.EllExist.EllClassOk 7 α g Ψ :=
  ⟨h.1, h.2.1,
    Work.FTS.EllSol.PkgK5.EllWeakPos_descend (l := 7) (by norm_num) h.2.2⟩

/-! ## The `V^{th}`-slot, on the side of the level-`6` package -/

/-- **The `V^{th}`-slot at level `4` over `EllClassOk 7`**, proved directly from
`ellVth_transferC_of_pieces_quarter` (`ClassC/vthQuarter`) with the two certificate inputs
`VthAuxC.certC` and `EllSol.poinC_quarter`.

This is the content of `EllPkgAux.vthSlotLe4`, but without the sibling import
`ClassC.vthTransfer_classC` (which pulls in the second copy of the level-`4` elliptic estimate,
incompatible with the level-`6` package of this file). -/
theorem vthSlotLe4_clashFree
    (hEst : ∃ C : ℝ, 0 < C ∧ Work.FTS.EllipticEst.TT.EllEstUnif 4 C) :
    ∃ C : ℝ, 0 < C ∧ EllPkgAux.VthSlotLe4 C := by
  obtain ⟨Ce, hCe, h⟩ :=
    Work.FTS.EllSol.ellVth_transferC_of_pieces_quarter hEst
      Work.FTS.EllSol.VthAuxC.certC Work.FTS.EllSol.poinC_quarter
  refine ⟨Ce, hCe, ?_⟩
  intro α g Ψ hα hα4 hC hO
  exact h α g Ψ hα hα4 hC (Work.FTS.StrongGlobal.IsBslSol.toPos hO.1) hO.2.1
    (Work.FTS.EllSol.PkgK5.EllWeakPos_descend (K := 7) (l := 4) (by norm_num) hO.2.2)

/-! ## The level-`4` package -/

/-- **`ellPkgGo_of_classOk`, re-assembled on the side of the level-`6` package.**  Same content
as `Work.FTS.EllSol.ellPkgGo_of_classOk`, with the interpolation input taken through the verbatim
bridge `EllPkgAux.InterpOpenTraceStmt ↦ PkgK5.K5c.InterpOpenTrace`. -/
theorem ellPkgGo_of_classOk_clashFree
    (hEst4 : ∃ C : ℝ, 0 < C ∧ Work.FTS.EllipticEst.TT.EllEstUnif 4 C) :
    ∃ Ce α₀ : ℝ, 0 < Ce ∧ 0 < α₀ ∧
    ∀ (α : ℝ) (g Ψ : Fn), 0 < α → α ≤ α₀ →
      ClassC α g →
      Work.FTS.EllExist.EllClassOk 7 α g Ψ →
      Work.FTS.VocabO.EllPkgGo α Ce g Ψ := by
  have hI : ∃ C : ℝ, 0 < C ∧ Work.FTS.EllSol.EllPkgAux.InterpOpenTraceStmt C :=
    Work.FTS.ClassC.AlphaDzGen.openTraceStmt_of_openTrace
      Work.FTS.ClassC.RopGen.interpOpenTrace
  exact EllPkgAux.ellPkgGoOfClassOk_of
    (EllPkgAux.ropSlotLe4_cl (EllPkgAux.uopSlotLe4 hEst4 hI) (EllPkgAux.vopSlotLe4_cl hEst4))
    (EllPkgAux.uopSlotLe4 hEst4 hI)
    (EllPkgAux.vopSlotLe4_cl hEst4)
    (vthSlotLe4_clashFree hEst4)

/-! ## The conjunction -/

theorem ellPkgConj_of_classOk (hEst4 : ∃ C : ℝ, 0 < C ∧ Work.FTS.EllipticEst.TT.EllEstUnif 4 C) (hEst6 : ∃ C : ℝ, 0 < C ∧ Work.FTS.EllipticEst.TT.EllEstUnif 6 C) :
    ∃ Ce α₀ : ℝ, 0 < Ce ∧ 0 < α₀ ∧
    ∀ (α : ℝ) (g Ψ : Work.FTS.Galerkin.Fn), 0 < α → α ≤ α₀ →
      Work.FTS.EllSol.ClassC α g →
      Work.FTS.EllExist.EllClassOk 8 α g Ψ →
      Work.FTS.VocabO.EllPkgGo α Ce g Ψ ∧ Work.FTS.EllSol.EllPkgK α 6 Ce g Ψ := by
  obtain ⟨CeG, αG, hCeG, hαG, hG⟩ := ellPkgGo_of_classOk_clashFree hEst4
  obtain ⟨CeK, αK, hCeK, hαK, hK⟩ := ellPkgK6_of_classC hEst6
  refine ⟨max CeG CeK, min αG αK, lt_max_of_lt_left hCeG, lt_min hαG hαK, ?_⟩
  intro α g Ψ hα hαm hC hOK8
  have hαG' : α ≤ αG := le_trans hαm (min_le_left _ _)
  have hαK' : α ≤ αK := le_trans hαm (min_le_right _ _)
  exact ⟨EllPkgGo_mono hα (hG α g Ψ hα hαG' hC (ellClassOk_eight_seven hOK8))
      (le_max_left _ _),
    EllPkgK_mono (hK α g Ψ hα hαK' hC hOK8) (le_max_right _ _)⟩

end Work.FTS.EllSol
end
-- ===== merged: Submission.Work.FTS.EpsEngine.Feps_gates_of_xball_curve =====
section

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

namespace Work.FTS.EpsEngine

open MeasureTheory Set Filter
open scoped Real Topology
open Work.FTS.Galerkin (Fn Fam slice)

set_option autoImplicit false
set_option maxHeartbeats 1000000

/-! ## The uniform `ℋ⁶`-bound of the projected slices -/

/-- **The `ℋ⁶`-size of the projected slice `slice (JfamP ρ ε g) s = Pz (J_ε (slice g s))`, from the
`EpsSq`-size of the raw slice.**  There is `CJ > 0` (depending only on the kernel `ρ`) such that for
every `α ∈ (0,1]`, every `ε ∈ (0,1]` and every profile `u` in the `XBall α ρ ε R C₀` invariant,

  `Xn6 α (Pz (J_ε u)) ≤ √(CJ · (CJ/ε)¹² · R)`.

This is the `hb6` slot of the slot-sup gate (`EpsRHSP_slotSup_of_val`): the needed uniform `ℋ⁶`-bound
of the projected slices is *not* the elliptic constant `Ce` of `hEll` but the explicit `R`-dependent
number above.  No sign hypothesis on `R` is needed: for `R < 0` the hypothesis `XBall` is
unsatisfiable, since `0 ≤ EpsSq α u ≤ R` (`EpsSpace.EpsSq_nonneg`). -/
theorem Xn6_JfamP_le_of_XBall {ρ : ℝ × ℝ → ℝ} (hρ : Work.FTS.StrongEps.IsSmoothKernel ρ) :
    ∃ CJ : ℝ, 0 < CJ ∧ ∀ {α ε R C₀ : ℝ}, α ∈ Set.Ioc 0 1 → 0 < ε → ε ≤ 1 →
      ∀ {g : Work.FTS.Galerkin.Fam} {s : ℝ},
        XBall α ρ ε R C₀ (Work.FTS.Galerkin.slice g s) →
        Work.FTS.StrongGlobal.Xn6 α
            (Work.FTS.Galerkin.slice (Work.FTS.StrongEps.JfamP ρ ε g) s)
          ≤ Real.sqrt (CJ * (CJ / ε) ^ (2 * 6) * R) := by
  obtain ⟨CJ, hCJpos, hCJ⟩ := Work.FTS.StrongEps.EpsSqTools.HkSq_JepsPz_le ρ hρ
  refine ⟨CJ, hCJpos, ?_⟩
  intro α ε R C₀ hα hε hε1 g s hX
  have hratio : 0 ≤ CJ / ε := div_nonneg hCJpos.le hε.le
  have hle : Work.Spaces.HkSq α 6
      (Work.FTS.StrongEps.Pz (Work.FTS.StrongEps.Jeps ρ ε (Work.FTS.Galerkin.slice g s)))
      ≤ CJ * (CJ / ε) ^ (2 * 6) * R :=
    le_trans (hCJ α hα ε hε hε1 6 (by norm_num) (Work.FTS.Galerkin.slice g s)
        hX.smoothOpen hX.mem)
      (mul_le_mul_of_nonneg_left hX.sq_le (mul_nonneg hCJpos.le (pow_nonneg hratio _)))
  have hsq : Work.Spaces.HkSq α 6
      (Work.FTS.Galerkin.slice (Work.FTS.StrongEps.JfamP ρ ε g) s)
      ≤ CJ * (CJ / ε) ^ (2 * 6) * R := by
    simpa only [Work.FTS.StrongEps.slice_JfamP] using hle
  exact Real.sqrt_le_sqrt hsq

/-! ## The three gates -/

theorem Feps_gates_of_xball_curve {α C₀ R Ce Cs Lw δ ε : ℝ} {ρ : ℝ × ℝ → ℝ}
    {Φs : Work.FTS.Galerkin.Fn} {E : Work.FTS.Galerkin.Fn → Work.FTS.Galerkin.Fn}
    {g : Work.FTS.Galerkin.Fam}
    (hα : α ∈ Set.Ioc 0 1) (hρ : Work.FTS.StrongEps.IsSmoothKernel ρ) (hε : 0 < ε)
    (hε1 : ε ≤ 1)
    (hEll : ∀ u : Work.FTS.Galerkin.Fn, Work.FTS.ClassC.ClassC α u →
      Work.FTS.VocabO.EllPkgGo α Ce u (E u) ∧ Work.FTS.ClassC.EllPkgK α 6 Ce u (E u))
    (hstar : Work.FTS.VocabO2.StarPkgo2 α Cs Φs)
    (hml : Work.FTS.StrongEps.MuLamOK α C₀ Φs E) (hR : 0 ≤ R) (hLw : 0 ≤ Lw)
    (hP : ∀ s ∈ Set.Icc (0 : ℝ) δ,
      Work.FTS.EpsEngine.XBall α ρ ε R C₀ (Work.FTS.Galerkin.slice g s))
    (hEq : ∀ s ∈ Set.Icc (0 : ℝ) δ, ∀ t ∈ Set.Icc (0 : ℝ) δ,
      Work.FTS.StrongEps.EpsSq α (fun z θ =>
        Work.FTS.Galerkin.slice g s z θ - Work.FTS.Galerkin.slice g t z θ)
        ≤ Lw * (s - t) ^ 2) :
    (∀ (j i : ℕ), j + i ≤ 4 → ∀ z θ : ℝ, (z, θ) ∈ Work.FTS.EllipticEst.Q0 →
        MeasureTheory.AEStronglyMeasurable
          (fun s : ℝ => Work.Spaces.mixed j i
            (Work.FTS.StrongEps.epsRHSP α ρ ε Φs E g s) z θ)
          (MeasureTheory.volume.restrict (Set.Icc (0 : ℝ) δ)))
    ∧ MeasureTheory.AEStronglyMeasurable
        (fun p : ℝ × ℝ × ℝ => Work.Spaces.HkIntegrand α 4
          (Work.FTS.StrongEps.epsRHSP α ρ ε Φs E g p.1) p.2.1 p.2.2)
        ((MeasureTheory.volume.restrict (Set.Icc (0 : ℝ) δ)).prod
          ((MeasureTheory.volume.restrict Work.Spaces.Iz).prod
            (MeasureTheory.volume.restrict Work.Spaces.Iθ)))
    ∧ (∀ K : Set (ℝ × ℝ), IsCompact K → K ⊆ Work.FTS.EllipticEst.Q0 →
        ∃ C : ℝ, 0 ≤ C ∧ ∀ s ∈ Set.Icc (0 : ℝ) δ, ∀ q ∈ K, ∀ (j i : ℕ), j + i ≤ 4 →
          |Work.Spaces.mixed j i (Work.FTS.StrongEps.epsRHSP α ρ ε Φs E g s) q.1 q.2| ≤ C) := by
  refine ⟨?_, ?_, ?_⟩
  · -- ## (meas): the sliced a.e. strong measurability of every jet (the sibling gate, verbatim)
    intro j i hji z θ hQ
    obtain ⟨hz, hθ0, hθ1⟩ := Work.FTS.EllipticEst.mem_Q0.mp hQ
    exact hmeas_slot_epsRHSP_fam_of_gate hα hρ hε hε1 hEll hstar hml hR hLw hP hEq j i hz
      ⟨hθ0, hθ1⟩
  · -- ## (joint): the joint a.e. strong measurability of the `ℋ⁴`-integrand (the sibling gate)
    exact hjoint_HkIntegrand_epsRHSP_fam_of_gate (k := 4) hα hρ hε hε1 hEll hstar hml hR hLw
      hP hEq
  · -- ## (sup): the uniform slot bound on a compact subset of the open quadrant
    intro K hK hKQ
    rcases lt_or_ge δ 0 with hδneg | hδnonneg
    · -- the horizon is empty: the bound is vacuous
      have hemp : Set.Icc (0 : ℝ) δ = ∅ := Set.Icc_eq_empty_of_lt hδneg
      refine ⟨0, le_rfl, ?_⟩
      intro s hs
      rw [hemp] at hs
      exact absurd hs (by simp)
    · -- ## the uniform `ℋ⁶`-bound of the projected slices, from `EpsSq α (slice g s) ≤ R`
      obtain ⟨CJ, _hCJpos, hXn6⟩ := Xn6_JfamP_le_of_XBall (ρ := ρ) hρ
      set B6 : ℝ := Real.sqrt (CJ * (CJ / ε) ^ (2 * 6) * R) with hB6def
      set Ce' : ℝ := max Ce B6 with hCe'def
      have hb6 : ∀ s ∈ Set.Icc (0 : ℝ) δ,
          Work.FTS.StrongGlobal.Xn6 α
            (Work.FTS.Galerkin.slice (Work.FTS.StrongEps.JfamP ρ ε g) s) ≤ Ce' :=
        fun s hs => le_trans (hXn6 hα hε hε1 (hP s hs)) (le_max_right _ _)
      -- ## the elliptic packages at the enlarged constant `Ce'`
      have hEll' : ∀ u : Work.FTS.Galerkin.Fn, Work.FTS.ClassC.ClassC α u →
          Work.FTS.VocabO.EllPkgGo α Ce' u (E u) ∧
            Work.FTS.ClassC.EllPkgK α 6 Ce' u (E u) :=
        fun u hu =>
          ⟨Work.FTS.ClassC.EllPkgGo_mono hα.1 (hEll u hu).1
              (by rw [hCe'def]; exact le_max_left _ _),
           Work.FTS.ClassC.EllPkgK_mono (hEll u hu).2
              (by rw [hCe'def]; exact le_max_left _ _)⟩
      -- ## the class-`C` and ball clauses of the projected slices, from `XBall`
      have hC : ∀ s ∈ Set.Icc (0 : ℝ) δ, Work.FTS.ClassC.ClassC α
          (Work.FTS.Galerkin.slice (Work.FTS.StrongEps.JfamP ρ ε g) s) :=
        fun s hs => (hP s hs).classC
      have hb4 : ∀ s ∈ Set.Icc (0 : ℝ) δ, Work.FTS.Nonlin.Xn α
          (Work.FTS.Galerkin.slice (Work.FTS.StrongEps.JfamP ρ ε g) s) ≤ C₀ * α ^ 2 :=
        fun s hs => (hP s hs).ball
      -- ## the uniform open-quadrant smoothness and `ℋ⁴`-size of `epsWP`
      have hreg : ∀ s ∈ Set.Icc (0 : ℝ) δ,
          Work.FTS.EllipticEst.SmoothOpen (Work.FTS.StrongEps.epsWP α ρ ε Φs E g s) :=
        Work.FTS.StrongEps.smoothOpen_epsWP (α := α) (C₀ := C₀) (Ce := Ce) (Cs := Cs) (ρ := ρ)
          (Φs := Φs) (E := E) (g := g) (ε := ε) hα hEll hstar hC
      obtain ⟨KW, hKW, hn⟩ := Work.FTS.StrongEps.epsWP_hkMem4_bnd_fam
        (α := α) (C₀ := C₀) (Ce := Ce') (Cs := Cs) (T := δ) (ρ := ρ) (Φs := Φs) (E := E)
        (G := fun _ => g) (ε := fun _ => ε) hα hEll' hstar hml
        (fun _ s hs => hC s hs) (fun _ s hs => hb4 s hs) (fun _ s hs => hb6 s hs)
      have hnorm : ∃ KW' : ℝ, 0 ≤ KW' ∧ ∀ s ∈ Set.Icc (0 : ℝ) δ,
          Work.Spaces.HkMem α 4 (Work.FTS.StrongEps.epsWP α ρ ε Φs E g s) ∧
            Work.Spaces.HkNorm α 4 (Work.FTS.StrongEps.epsWP α ρ ε Φs E g s) ≤ KW' :=
        ⟨KW, hKW.le, fun s hs => hn 0 s hs⟩
      -- ## the producer of the slot-sup gate
      obtain ⟨C, hC0, hCb⟩ := EpsRHSP_slotSup_of_val (α := α) (C₀ := C₀) (Ce := Ce')
        (Cs := Cs) (T := δ) (ε := ε) (ρ := ρ) (Φs := Φs) (E := E) (g := g)
        hα hρ hε hε1 hδnonneg hEll' hstar hml hC hb4 hb6 hreg hnorm hK hKQ
      exact ⟨C, hC0, fun s hs q hq j i hji => hCb j i hji s hs q hq⟩

end Work.FTS.EpsEngine
end
-- ===== merged: Submission.Work.FTS.EpsEngine.Feps_intervalIntegrable_pt =====
section

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

noncomputable section

open scoped Real Topology
open MeasureTheory Set Filter
open Work.FTS.Galerkin (Fn slice)

namespace Work.FTS.EpsEngine


end Work.FTS.EpsEngine

end
end
-- ===== merged: Submission.Work.FTS.EpsEngine.HkeepMetric =====
section

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

open Work.FTS.StrongEps.EpsLocalPStar.VolterraAux

noncomputable section
open scoped Real Topology ENNReal
open MeasureTheory Set Filter
open Work.FTS.Galerkin (Fn Fam slice)

namespace Work.FTS.EpsEngine

open Work.FTS.StrongEps
open Work.FTS.StrongEps.EpsLocalPStar
open Work.FTS.StrongEps.EpsSqTools

set_option autoImplicit false

/-- **The `X`-size of a sum.**  If both summands are honest (`EpsMem`, plus a.e. strong
measurability of the weighted profiles for the sum) with sizes `R₀` and `L`, then their sum is
honest with size `2R₀ + 2L` — the AM–GM loss of the triangle inequality for `EpsSq`. -/
theorem EpsMem_EpsSq_add_le {α R₀ R L : ℝ} (hR : 2 * R₀ + 2 * L ≤ R)
    {f g : Fn} (hakf : AK α f) (hakg : AK α g) (hf : EpsMem α f) (hh : EpsSq α f ≤ R₀)
    (hg : EpsMem α g) (hg' : EpsSq α g ≤ L) :
    EpsMem α (fun z θ => f z θ + g z θ) ∧
      EpsSq α (fun z θ => f z θ + g z θ) ≤ R := by
  refine ⟨EpsMem_add hakf hakg hf hg, (EpsSq_add_le_of_mem hf hg).trans ?_⟩
  linarith

/-- **The `X`-size of a Picard slice.**  If the datum has size `R₀` and the increment
`G = ∫₀^τ F (w_s) ds` has size `≤ τ * (τ * B)` (bounded in `epsL2` by `B` along the curve), then
`h₀ + G` is honest of size `R` as soon as `2R₀ + 2 * (τ * (τ * B)) ≤ R`. -/
theorem EpsMem_EpsSq_add_intervalIntegral_le {α τ B R₀ R : ℝ} (hτ : 0 ≤ τ) (hB : 0 ≤ B)
    (hR : 2 * R₀ + 2 * (τ * (τ * B)) ≤ R) {G : ℝ → Fn} {h₀ : Fn}
    (hak : AK α (fun z θ => ∫ s in (0 : ℝ)..τ, G s z θ))
    (hak₀ : AK α h₀) (hh₀ : EpsMem α h₀) (hR₀ : EpsSq α h₀ ≤ R₀)
    (hmeas : AEStronglyMeasurable
      (fun p : ℝ × ℝ × ℝ => G p.1 p.2.1 p.2.2 * epsW α p.2.1 p.2.2)
      ((volume.restrict (Set.uIoc 0 τ)).prod DomM))
    (hbd : ∀ᵐ s ∂(volume.restrict (Set.uIoc 0 τ)), epsL2 α (G s) ≤ ENNReal.ofReal B) :
    EpsMem α (fun z θ => h₀ z θ + ∫ s in (0 : ℝ)..τ, G s z θ) ∧
      EpsSq α (fun z θ => h₀ z θ + ∫ s in (0 : ℝ)..τ, G s z θ) ≤ R := by
  have hG := EpsMem_and_EpsSq_intervalIntegral_le (α := α) (τ := τ) (B := B) hτ hB hmeas hbd
  exact EpsMem_EpsSq_add_le hR hak₀ hak hh₀ hR₀ hG.1 hG.2

end Work.FTS.EpsEngine
end
end
-- ===== merged: Submission.Work.FTS.RegExportIface.Producers =====
section

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

/-!
# `Work.FTS.RegExportIface.Producers` — the OPEN producers of FTS_RegExport (curric-46, 2026-10-10)

One named `theorem … := by sorry` per research item of `cbc/fts_regexport_design.md` §5 as corrected
by `cbc/fts_regexport_design_REVIEW.md` (F2: closed-form coefficients, odd/odd `psiR`, `Θ` on
`z ≤ 0`; F3: `vanish0` in `VelPkg`, RX-A1w, RX-T0). REPAIR 10-11 (`cbc/fts_velpkg_fix.md` + REVIEW):
`VelPkg` is open-θ + `thLip` (axis clause dropped; `thLip` → Hölder `thHol` 10-11, ITEM A of
`cbc/fts_thlip_o1_plans.md`), `r7Block` is fed `edgeExt Vz7`, `Vθ7`,
`edgeExt cs7`; RX-R5 is routed through `Der.R5Parts_of_pieces_F` (product slots,
`FTS_RegExport/RXR5/R5PiecesF.lean`). The deliverable `regExport` (7″) is the
assembly item; `FinalV2.Producers.regPkg7'` is PROVED from it (+ `mu6'` for the clock).

| item | theorem | needs |
|---|---|---|
| RX-A1  | `abs_mixed_le_HkNorm_C4` | — (shared with Final `classC_sup_le`) |
| RX-A1w | `abs_mixed_le_HkNorm_C4_w` | — (same proof, weight kept) |
| RX-A2  | `lim_mixed_bounds` | RX-A1 |
| RX-A2w | `lim_mixed_weighted` | RX-A1w |
| RX-B   | `l12_zero_lim` | — |
| RX-T0  | `dtau_mixed` | — |
| RX-T   | `transport_weighted` | — |
| RX-St1 | `st1Export` | leaf plan `RXT/Leaves.lean` (T1–T5c, S1–S10, X1, S4); RX-B, RX-VP |
| RX-VP  | `velPkg` | RX-A1(w), RX-A2(w); split `velPkgOpen_proved` + `thHol_proved` |
| RX-R7  | `r7Block` | RX-VP |
| RX-Supp| `suppExport` | — (factor of `GalMinConv`'s `hsupp` block) |
| RX-R1  | `r1Block` | RX-A2, RX-St1, RX-R5 |
| RX-R5  | `r5Parts` | RX-St1, RX-A2, RX-VP |
| RX0    | `forall_regPkg_of_parts'` | — (re-proof of `GalMinConv`'s 4 `hRQ` consumers) |
| top    | `regExport` | all of the above + `hsuppOut_gS` + clock |
-/

noncomputable section
open scoped Real Topology NNReal
open Set Filter

namespace Work.FTS.RegExportIface

open Work.FTS.Galerkin (Fn Fam slice IsDynGSolWith)
open Work.FTS.Nonlin (PsiCan)
open Work.FTS.Regularity (pExp Jet)
open Work.FTS.RegPkgGal (extG RegPkg' St1Class R5Parts Avort Bdyn)
open Work.FTS.FinalV2 (gS tauExt LimApprox DynOK' EllLimOK3 Sol)

set_option autoImplicit false

variable {α C₀ Ce Cs : ℝ} {Φs : Fn} {E : Fn →ₗ[ℝ] Fn}












/-- **RX-R1 (research low)**: the R1 block at the sanitised right-Taylor family, from RX-A2
(joint continuity of `g, D_zg` up to `τ = 0`), `St1Class.quad` at `S+1`, the R5 jets + `hRz0`
(for `∂_τg → 0` at `z → 0`) and the `τ = 0` data (`∂_τ⁺g(·,0) = RHS(locG6)`, smooth). -/
theorem r1Block (hα : 0 < α) (hα13 : α ≤ 1 / 3)
    {g : Fam} (hSol : Sol (pExp α) Φs E g) (hOK : DynOK' (pExp α) C₀ Φs E g)
    (hdat : ∃ L β : ℝ, 1 ≤ L ∧ ∀ z θ, g z θ 0 = Work.FTS.LocData6.locG6 (pExp α) L β z θ)
    (hSt1 : ∀ S > 0, St1Class α S (gS α (tauExt g)))
    (H5 : ∀ S > 0, R5Parts α S (gS α (tauExt g)) (psiR α Φs E (tauExt g))) :
    ∀ S > 0, R1Block α S (gS α (tauExt g)) := by
  exact Work.FTS_RegExport.r1Block_proved hα hα13 hSol hOK hdat hSt1 H5


/-- **RX0 (re-proof, research-free).** `GalMinConv` with the four `hRQ` consumers re-proved from
`hIS` + `hmin.c4` (`sup_extG_ext`, `sup2_extG_ext`, `hzmodp_ext`) and from `hSt1.hhθ` (endpoint
continuity); `GalMinAssembly`/`PartsAssembly` re-pointed (new files only). Same output as
`RegPkgGal.forall_regPkg_of_parts`. -/
theorem forall_regPkg_of_parts' {g Φ : Fam} {m : ℝ → ℝ}
    {Vz Vθ cs : ℝ → ℝ → ℝ → ℝ} {a b c : ℝ}
    (H : ∀ S > 0, ∃ Lz7 : ℝ, GalMin' α S g m Vz Vθ cs a b c Lz7)
    (H5 : ∀ S > 0, R5Parts α S g Φ) :
    ∀ S > 0, RegPkg' α S (Avort m) (Bdyn m) (extG g) := by
  exact Work.FTS_RegExport.forall_regPkg_of_parts'_proved H H5

/-- **(7″) THE DELIVERABLE OF FTS_RegExport (assembly item).** Route: `forall_regPkg_of_parts'`
at `g := gS α (tauExt g)`, `Φ := psiR α Φs E (tauExt g)`, `m := maxMu …`, with `GalMin'` from
`r1Block`, `r7Block` (∘ `velPkg`; coefficients `edgeExt Vz7`, `Vθ7`, `edgeExt cs7` — the assembly
is generic in `Vz Vθ cs`, statement unchanged 10-11), `st1Export`, `hIS` from `lim_mixed_bounds` (+ congruence on the
open quadrant), `hHkn` (`HkNorm 4 ≤ Xn`, a.e.-congruence), `hsuppOut_gS`, `RegPkgMin` of the
sanitised family (congruence + `vanish`), the clock (`hclock` + `maxExt`); `R5Parts` from
`r5Parts` (10-11: called with `hdat` and `ClockBd.of_clock hclock`). The producers `velPkg`,
`r7Block`, `st1Export`, `dtau_mixed`, `r5Parts` take `hμ : ClockBd α Φs E g`, supplied here by
`ClockBd.of_clock hclock` (statement unchanged 10-10, 10-11). -/
theorem regExport (hα : 0 < α) (hα13 : α ≤ 1 / 3)
    (hEll : ∀ u : Fn, Work.FTS.ClassC.ClassC (pExp α) u →
      Work.FTS.Final.EllPkgGo (pExp α) Ce u (E u) ∧ Work.FTS.ClassC.EllPkgK (pExp α) 6 Ce u (E u))
    (hEL3 : EllLimOK3 (pExp α) E) (hStar : Work.FTS.Final.StarPkgo2 (pExp α) Cs Φs)
    {g : Fam} (hSol : Sol (pExp α) Φs E g) (hOK : DynOK' (pExp α) C₀ Φs E g)
    (hdat : ∃ L β : ℝ, 1 ≤ L ∧ ∀ z θ, g z θ 0 = Work.FTS.LocData6.locG6 (pExp α) L β z θ)
    (hclock : (∀ τ : ℝ, 0 ≤ τ → |Work.FTS.Galerkin.muDyn (pExp α) (PsiCan Φs E g) g τ| ≤ 1 / 2) ∧
      ContinuousOn (Work.FTS.Galerkin.muDyn (pExp α) (PsiCan Φs E g) g) (Set.Ici 0) ∧
      (∀ S : ℝ, 0 < S → ∃ L : ℝ, 0 ≤ L ∧ ∀ τ ∈ Icc (0 : ℝ) S, ∀ τ' ∈ Icc (0 : ℝ) S,
        |Work.FTS.Galerkin.muDyn (pExp α) (PsiCan Φs E g) g τ
          - Work.FTS.Galerkin.muDyn (pExp α) (PsiCan Φs E g) g τ'| ≤ L * |τ - τ'| ^ α))
    (hcl : Work.FTS_RegExport.ESlotBd α Cs g ⇑E) :
    ∀ S > 0, RegPkg' α S (Avort (Work.FTS.Final.maxMu (pExp α) (PsiCan Φs E g) g))
      (Bdyn (Work.FTS.Final.maxMu (pExp α) (PsiCan Φs E g) g)) (extG (gS α (tauExt g))) := by
  exact Work.FTS_RegExport.regExport_of_ESlotBd hα hα13 hEll hEL3 hStar hSol hOK hdat hclock hcl

end Work.FTS.RegExportIface
end
end
